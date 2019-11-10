open util/time
open util/ordering[Time] as T0

abstract sig User{
	username : one String,
}

sig AuthenticatedUser extends User {
	identityCard : one String,
	fiscalCode : one String
}{
	identityCard != fiscalCode
}

sig MunicipalityAgent extends User {
	municipality : one Municipality
}

sig MunicipalitySupervisor extends User{
	municipality : one Municipality
}

sig Municipality{ }

sig Street{
	area: some Area
}{
	--a street can belong to different areas, but they must be all areas of the same municipality
	no disj a1,a2:Area | a1 in area and a2 in area and a1.municipality != a2.municipality
}

sig Area{ 
	municipality: one Municipality
}{
	some s:Street | this in s.area
}

sig LicensePlate {}

sig Report{
	author: one AuthenticatedUser,
	-- for simplicity the gps position is substituted by a direct association with the Street
	street: one Street,	
	currStatus: one ReportStatus,
	statusHistory: Time -> lone ReportStatus,
	time: one Time,
	licensePlate: one LicensePlate,
	agent: lone MunicipalityAgent
}{
	--the currentStatus is the last status in the statusHistory
	currStatus = {s:ReportStatus | some t1:Time | (t1->s in statusHistory  and no t2:Time | (gt[t2,t1] and (some s2:ReportStatus | t2->s2 in statusHistory)))}
	--a ReportStatus cannot be present more than one time in the history
	no s:ReportStatus | some disj t1,t2:Time | t1->s in statusHistory and t2->s in statusHistory	
	--the state evolution must be consistent with the state diagram (see fig. 2.2)
	no t1,t2:Time, s1,s2:ReportStatus | (gt[t2,t1] and (no t3:Time| gt[t3,t1] and lt[t3,t2] and t3 in statusHistory.ReportStatus) and t1->s1 in statusHistory and t2->s2 in statusHistory and (s2 not in s1.nextStatus))
	WaitingAnalysis in Time.statusHistory
	--the statusHistory cannot start before the report time
	no t:Time | (t in statusHistory.ReportStatus and lt[t,time] )
	--every checked report must have a corresponding agent
	(currStatus = Approved or currStatus = Refused or currStatus = WaitingControl) implies (agent != none)
	--the agent of the report must work for the municipality which the report refers to
	(agent != none) implies agent.municipality = street.area.municipality
	

}

abstract sig ReportStatus {
	nextStatus : set ReportStatus
}
one sig WaitingAnalysis extends ReportStatus{}
{	
	#(nextStatus) = 2 and (WaitingAgent in nextStatus) and (Refused in nextStatus)
}
one sig WaitingAgent extends ReportStatus{}
{
	#(nextStatus) = 3 and (WaitingControl in nextStatus) and (Refused in nextStatus) and (Approved in nextStatus)
}
one sig Approved extends ReportStatus{}
{
	nextStatus = none
}
one sig Refused extends ReportStatus{}
{
	nextStatus = none
}
one sig WaitingControl extends ReportStatus{}
{
	#(nextStatus) = 2 and ( Approved in nextStatus) and (Refused in nextStatus)
}

sig Ticket{
	street: one Street,
	report: lone Report, --not all ticket are issued as a consequence of a SafeStreet report
	time: one Time,
	agent: one MunicipalityAgent,
	licensePlate : one LicensePlate
}

abstract sig StatisticsData{
	startTime : one Time,
	endTime: one Time,
	street: lone Street,
	area: lone Area
}{
	--a statistics must refer to a street or to an area and not both
	(street = none and area != none) or (area = none and street != none)
	gte[endTime,startTime]
}

sig PublicStatisticsData extends StatisticsData {
	num_report : one Int,
	num_tickets: one Int,
	num_accidents: one Int,
	num_park_accidents: one Int
}

sig ReservedStatisticsData extends StatisticsData {
	most_egregious_offender : one LicensePlate
}

abstract sig StatisticsLevel{}

one sig PublicStatistics extends StatisticsLevel {}
one sig ReservedStatistics extends StatisticsLevel{}

sig StatisticsRequest{
	user : one User,
	level : one StatisticsLevel,
	status : one RequestStatus
}

abstract sig RequestStatus{}
one sig RequestAccepted extends RequestStatus{}
one sig RequestRefused extends RequestStatus{}

sig Suggestion{
	street: one Street,
	time: one Time
}

sig Accident{
	street: one Street,
	cause: one AccidentCause,
	time : one Time,
	licensePlate: some LicensePlate
}

abstract sig AccidentCause{}

one sig HighSpeed extends AccidentCause{}
one sig DrugOrAlchol extends AccidentCause{}
one sig BadParkedCar extends AccidentCause{}
one sig Other extends AccidentCause{}

--uniqueness of some identification data

fact noDifferentUsersWithSameIdentityCard{
	no disj u1,u2: AuthenticatedUser | u1.identityCard = u2.identityCard
}

fact noDifferentUsersWithSameUsername{
	no disj u1,u2: User | u1.username = u2.username
}

fact noDifferentUsersWithSameFiscalCode{
	no disj u1,u2: AuthenticatedUser | u1.fiscalCode = u2.fiscalCode
}

--every municipality needs to have at least one agent and one supervisor
fact allMunicipalityHaveOneAgentAndSupervisor{
	all m:Municipality | ( ( some a:MunicipalityAgent | a.municipality = m) and ( some s:MunicipalitySupervisor | s.municipality = m))
 }

--every municipality needs to have at least one street (and so one area, given that every street belongs to at least one 
fact allMunicipalityHaveOneStreet{
	all m:Municipality | ( some s:Street| s.area.municipality = m)
 }

--agents must check reports in order of emission
fact reportAnalysisOrder{
	no r1,r2:Report | gt[r2.time,r1.time] and (r1.currStatus = WaitingAnalysis or r1.currStatus = WaitingAgent ) and (r2.currStatus not in WaitingAgent) and (r2.currStatus not in WaitingAnalysis)
}

--every ticket can be issued only by agents of the city where the violation occured
fact noAgentCanIssueTicketsInAnotherCity{
	no t:Ticket | t.agent.municipality & t.street.area.municipality = none
}

--for every approved report there must be one ticket with corresponding data, referred to that report
--and for every ticket referred to a report, this must be Approved and the data must correspond
fact ticketsForApprovedReports{
	all r:Report |r.currStatus = Approved implies one t:Ticket | ( t.licensePlate = r.licensePlate and t.report =  r and t.agent = r.agent and t.street = r.street)
	all t:Ticket | t.report != none implies one r:Report | (t.report = r and r.licensePlate = r.licensePlate and r.currStatus = Approved and t.agent = r.agent and t.street = r.street)
	all t:Ticket | t.report != none implies gte[t.time, getReportApproveTime[t.report] ]
}

--return the approvation time for a report
fun getReportApproveTime[r:Report] : set Time{
	{t:Time | some s:ReportStatus | ( t->s in r.statusHistory and s=Approved) }
}

--all streets where there have been at least two accidents caused by parking or two approved violation reports must present a suggestion
--here, considering the Time type available, has been used the interval [t.prev,t] to find the events corresponding to a Suggestion at the time t
--clearly this should be a defined interval of time (eg: a month)
fact suggestionForUnsafeStreets{
	all s:Street, t:Time | ( #(getParkAccidentsInStreetAndTime[s,t.prev,t]) >= 2 and #(getApprovedReportsInStreetAndTime[s,t.prev,t]) >= 2 ) iff  (some sg:Suggestion|sg.street=s and sg.time = t)
}

--return the set of Approved Reports of the Street s with time between t1 and t2
fun getApprovedReportsInStreetAndTime[s:Street,t1,t2:Time] : set Report{
	{r:Report | r.street = s and r.currStatus = Approved and gte[r.time,t1] and lte[r.time,t2]}
}

--reserved statistics can only be accessed by Municipality Supervisors
fact statisticsPrivacy{
	all sr:StatisticsRequest | sr.status = RequestAccepted iff ( sr.level = PublicStatistics or (one u:MunicipalitySupervisor | sr.user = u)) 
}

--ensure public statistics values coherence with reports,tickets and accidents data
fact publicStatDataCoherent{
	all psd:PublicStatisticsData |
		((psd.street != none) implies (
			psd.num_report = #(getReportsInStreetAndTime[psd.street,psd.startTime,psd.endTime]) and
			psd.num_tickets = #(getTicketsInStreetAndTime[psd.street,psd.startTime,psd.endTime]) and
			psd.num_accidents = #(getAccidentsInStreetAndTime[psd.street,psd.startTime,psd.endTime]) and
			psd.num_park_accidents = #(getParkAccidentsInStreetAndTime[psd.street,psd.startTime,psd.endTime])
		))
		and
		((psd.area != none) implies(
			psd.num_report = #(getReportsInAreaAndTime[psd.area,psd.startTime,psd.endTime]) and
			psd.num_tickets = #(getTicketsInAreaAndTime[psd.area,psd.startTime,psd.endTime]) and
			psd.num_accidents = #(getAccidentsInAreaAndTime[psd.area,psd.startTime,psd.endTime]) and
			psd.num_park_accidents = #(getParkAccidentsInAreaAndTime[psd.area,psd.startTime,psd.endTime])
		))
}

--return the set of Reports for the Street s between t1 and t2
fun getReportsInStreetAndTime[s:Street, t1, t2:Time]: set Report{
	{r:Report | r.street = s and gte[r.time,t1] and lte[r.time,t2]}
}

--return the set of Tickets for the Street s between t1 and t2
fun getTicketsInStreetAndTime[s:Street, t1, t2:Time]: set Ticket{
	{t:Ticket | t.street = s and gte[t.time,t1] and lte[t.time,t2]}
}

--return the set of Accidents for the Street s between t1 and t2
fun getAccidentsInStreetAndTime[s:Street, t1, t2:Time]: set Accident{
	{a:Accident | a.street = s and gte[a.time,t1] and lte[a.time,t2]}
}

--return the set of Accidents caused by BadParkedCar for the Street s between t1 and t2
fun getParkAccidentsInStreetAndTime[s:Street, t1, t2:Time]: set Accident{
	{a:getAccidentsInStreetAndTime[s,t1,t2]| a.cause = BadParkedCar}
}

--return the set of Reports for the Area a between t1 and t2
fun getReportsInAreaAndTime[a:Area, t1, t2:Time]: set Report{
	{r:Report | a in r.street.area and gte[r.time,t1] and lte[r.time,t2]}
}

--return the set of Tickets for the Area a between t1 and t2
fun getTicketsInAreaAndTime[a:Area, t1, t2:Time]: set Ticket{
	{t:Ticket | a in t.street.area and gte[t.time,t1] and lte[t.time,t2]}
}

--return the set of Accidents for the Area a between t1 and t2
fun getAccidentsInAreaAndTime[a:Area, t1, t2:Time]: set Accident{
	{ac:Accident | a in ac.street.area and gte[a.time,t1] and lte[a.time,t2]}
}

--return the set of Accidents caused by BadParkedCar for the Area a between t1 and t2
fun getParkAccidentsInAreaAndTime[a:Area, t1, t2:Time]: set Accident{
	{ac:getAccidentsInAreaAndTime[a,t1,t2]| ac.cause = BadParkedCar}
}

--ensure reserved statistics values coherence with the tickets data
fact reservedStatDataCoherent{
	all rsd:ReservedStatisticsData | 
		((rsd.street != none) implies (
			let max = #(getTicketsForLPStreetTime[rsd.most_egregious_offender,rsd.street,rsd.startTime,rsd.endTime]) |
			(all lp:LicensePlate | #(getTicketsForLPStreetTime[lp,rsd.street,rsd.startTime,rsd.endTime]) <= max)
		))
		and
		((rsd.area != none) implies (
			let max = #(getTicketsForLPAreaTime[rsd.most_egregious_offender,rsd.area,rsd.startTime,rsd.endTime]) |
			(all lp:LicensePlate | #(getTicketsForLPAreaTime[lp,rsd.area,rsd.startTime,rsd.endTime]) <= max)
		))
	

}

--return the set of Tickets for the LicensePlate lp, on the Street s, between t1 and t2
fun getTicketsForLPStreetTime[lp:LicensePlate,s:Street,t1,t2:Time] : set Ticket{
	{t:Ticket | t.licensePlate = lp and t.street = s and gte[t.time,t1] and lte[t.time,t2]}
}

--return the set of Tickets for the LicensePlate lp, in the Area a, between t1 and t2
fun getTicketsForLPAreaTime[lp:LicensePlate,a:Area,t1,t2:Time] : set Ticket{
	{t:Ticket | t.licensePlate = lp and a in t.street.area and gte[t.time,t1] and lte[t.time,t2]}
}

--reports approved by an agent are less than or equal to the number of tickets issued by that agent
assert approvedReportsAndTicketsByAnAgent{
	all a:MunicipalityAgent | #{r:Report | r.agent = a and r.currStatus = Approved} <= #{t:Ticket | t.agent = a}
}

check approvedReportsAndTicketsByAnAgent for 10

--the number of issued tickets for a street is less than or equal to the number of approved reports for that street
assert approvedReportsAndTicketsForAStreet{
	all s:Street | #{r:Report | r.street = s and r.currStatus = Approved} <= #{t:Ticket | t.street = s}
}


check approvedReportsAndTicketsForAStreet for 10

--approvement of a report
--the previously expessed facts imply the generation of the corresponding ticket and the respect of the status order
pred approveReport[r,r':Report] {
	(r.currStatus = WaitingAgent or r.currStatus = WaitingControl) &&
	r'.author = r.author &&
	r'.street = r.street	&&
	r'.time = r.time &&
	r'.licensePlate = r.licensePlate &&
	r.statusHistory in r'.statusHistory &&
	Approved in Time.(r'.statusHistory)
}

run approveReport for 5 but exactly 10 String, exactly 3 Time, 0 StatisticsRequest, 0 StatisticsData

pred world1{
	#Municipality = 1
	#Street = 1
	#Report = 2
	#Accident = 2
	#Ticket = 2
	#LicensePlate = 2
	#StatisticsRequest = 0
	#PublicStatisticsData = 0
	#ReservedStatisticsData = 0
	some a1,a2:Accident, r1,r2:Report  | a1!=a2 and a1.cause = BadParkedCar and a2.cause = BadParkedCar and r1!=r2 and r1.currStatus = Approved and r2.currStatus = Approved	and a1.time = a2.time and a1.time = r1.time and a1.time = r2.time
}

run world1 for 5 but exactly 5 String, exactly 3 Time

pred world2{
	#Municipality = 1
	#Street = 1
	#Area = 1
	#Report = 2
	#Accident = 1
	#Ticket = 1
	#LicensePlate = 2
	#StatisticsRequest = 1
	#PublicStatisticsData = 1
	#ReservedStatisticsData = 1
	some psd:PublicStatisticsData, t:Ticket,r:Report | t.time = psd.startTime and psd.startTime = r.time
}

run world2 for 5 but exactly 5 String, exactly 2 Time

