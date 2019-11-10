open util/time
open util/ordering[Time] as T0

abstract sig User{
	//useless
	password : one String
 }

sig AuthenticatedUser extends User {
	username : one String,
	reports : set Report,
	identityCard : one String,
	fiscalCode : one String
}

sig MunicipalityAgent extends User {
	//merge as username?
	id : one Int,
	municipality : one Municipality
}

sig MunicipalitySupervisor extends User{
	username : one String,
	municipality : one Municipality
}

//useless
sig Visitor extends User{
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
}

sig LicensePlate {}

sig Report{
	user: one AuthenticatedUser,
	-- for simplicity the gps position is substituted by a direct association with the Street
	street: one Street,	
	currStatus: one ReportStatus,
	statusHistory: Time -> lone ReportStatus,
	time: one Time,
	licensePlate: one LicensePlate,
}{
	--the currentStatus is the last status in the statusHistory
	currStatus = {s:ReportStatus | (some  t1:Time | (t1->s in statusHistory  and no t2:Time | (gt[t2,t1] and (some s2:ReportStatus | t2->s2 in statusHistory))))}
	--a ReportStatus cannot be present more than one time in the history
	no s:ReportStatus | some disj t1,t2:Time | t1->s in statusHistory and t2->s in statusHistory	
	--the state evolution must be consistent with the state diagram (see fig. 2.2)
	no t1,t2:Time, s1,s2:ReportStatus | (gt[t2,t1] and (no t3:Time| gt[t3,t1] and lt[t3,t2] and t3 in statusHistory.ReportStatus) and t1->s1 in statusHistory and t2->s2 in statusHistory and (s2 not in s1.nextStatus))
	WaitingAnalysis in Time.statusHistory

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
	report: lone Report,
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
	(street = none and area != none) or (area = none and street != none)
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

sig Accident{
	street: one Street,
	cause: one AccidentCause,
	time : one Time,
	licensePlate: one LicensePlate
}

abstract sig AccidentCause{}

--one sig HighSpeed extends AccidentCause{}
--one sig DrugOrAlchol extends AccidentCause{}
one sig BadParkedCar extends AccidentCause{}
one sig Other extends AccidentCause{}

sig Suggestion{
	street: one Street,
	time: one Time
}

/** SuggestionType probably to be eliminated (useless)*/
abstract sig SuggestionType{}

sig increaseControls extends SuggestionType{}

sig addParkSlots extends SuggestionType{}

sig addBarriers extends SuggestionType{}

sig modifyParkTime extends SuggestionType{}

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

--uniqueness of some identification data

fact noDifferentUserWithSameIdentityCard{
	no disj u1,u2: AuthenticatedUser | u1.identityCard = u2.identityCard
}

fact noDifferentUserWithSameUsername{
	no disj u1,u2: AuthenticatedUser | u1.username = u2.username and 
	no disj s1,s2 : MunicipalitySupervisor | s1.username = s2.username
}

fact noDifferentUserWithSameFiscalCode{
	no disj u1,u2: AuthenticatedUser | u1.fiscalCode = u2.fiscalCode
}

--every municipality needs to have at least one agent and one supervisor
fact allMunicipalityHaveOneAgentAndSupervisor{
	all m:Municipality | ( ( some a:MunicipalityAgent | a.municipality = m) and ( some s:MunicipalitySupervisor | s.municipality = m))
 }

--agents must check reports in order of emission
fact reportAnalysisOrder{
	no r1,r2:Report | gt[r2.time,r1.time] and (r1.currStatus = WaitingAnalysis or r1.currStatus = WaitingAgent ) and (r2.currStatus not in WaitingAgent) and (r2.currStatus not in WaitingAnalysis)
}

--every ticket can be issued only by agents of the city where the violation occured
fact noAgentCanIssueTicketsInAnotherCity{
	no t:Ticket | t.agent.municipality & t.street.area.municipality = none
}

--for every approved report there must be one ticket for the same license plate, referred to that report
--and for every ticket referred to a report, this must be Approved and the license plate must correspond
fact ticketsForApprovedReports{
	all r:Report |r.currStatus = Approved implies one t:Ticket | ( t.licensePlate = r.licensePlate and t.report =  r)
	all t:Ticket | t.report != none implies one r:Report | (t.report = r and r.licensePlate = r.licensePlate)
}

--all streets where there has been at least two accidents caused by parking or two approved violation reports must present a suggestion
--here, considering the Time type available, has been used the interval [t.prev,t] to find the events corresponding to a Suggestion at the time t
--clearly this should be a defined interval of time (a month)
fact suggestionForUnsafeStreets{
--	all s:Street | ( #(all a:Accident | a.cause = BadParkedCar and a.street=s) >= 2 or #(all r:Report | r.status = Approved and r.street =s)>=2 ) implies (some sg:Suggestion|sg.street=s)
	all s:Street, t:Time | ( #(getParkAccidentsInStreetAndTime[s,t.prev,t]) >= 2 and #(getApprovedReportsInStreetAndTime[s,t.prev,t]) >= 2 ) iff  (some sg:Suggestion|sg.street=s and sg.time = t)
}

fun getApprovedReportsInStreetAndTime[s:Street,t1,t2:Time] : set Report{
	--((Report <: street) :> s).Street  & ((Report <: status) :> Approved).Approved
	{r:Report | r.street = s and r.currStatus = Approved and gte[r.time,t1] and lte[r.time,t2]}
}

--reserved statistics cannot be accessed by normal users
fact statisticsPrivacy{
	all sr:StatisticsRequest | sr.status = RequestAccepted iff ( sr.level = PublicStatistics or (one u:MunicipalityAgent | sr.user = u) or (one u:MunicipalitySupervisor | sr.user = u)) 
}


--ensure public statistics values coerence with reports,tickets and accidents data
fact publicStatDataCoherent{
	all psd:PublicStatisticsData |
		((psd.street != none) implies (
			psd.num_report = #(getReportsInStreetAndTime[psd.street,psd.startTime,psd.endTime]) and
			psd.num_report = #(getTicketsInStreetAndTime[psd.street,psd.startTime,psd.endTime]) and
			psd.num_accidents = #(getAccidentsInStreetAndTime[psd.street,psd.startTime,psd.endTime]) and
			psd.num_park_accidents = #(getParkAccidentsInStreetAndTime[psd.street,psd.startTime,psd.endTime])
		))
		and
		((psd.area != none) implies(
			psd.num_report = #(getReportsInAreaAndTime[psd.area,psd.startTime,psd.endTime]) and
			psd.num_report = #(getTicketsInAreaAndTime[psd.area,psd.startTime,psd.endTime]) and
			psd.num_accidents = #(getAccidentsInAreaAndTime[psd.area,psd.startTime,psd.endTime]) and
			psd.num_park_accidents = #(getParkAccidentsInAreaAndTime[psd.area,psd.startTime,psd.endTime])
		))
}

fun getReportsInStreetAndTime[s:Street, t1, t2:Time]: set Report{
	{r:Report | r.street = s and gte[r.time,t1] and lte[r.time,t2]}
}

fun getTicketsInStreetAndTime[s:Street, t1, t2:Time]: set Ticket{
	{t:Ticket | t.street = s and gte[t.time,t1] and lte[t.time,t2]}
}

fun getAccidentsInStreetAndTime[s:Street, t1, t2:Time]: set Accident{
	{a:Accident | a.street = s and gte[a.time,t1] and lte[a.time,t2]}
}

fun getParkAccidentsInStreetAndTime[s:Street, t1, t2:Time]: set Accident{
	{a:getAccidentsInStreetAndTime[s,t1,t2]| a.cause = BadParkedCar}
}

fun getReportsInAreaAndTime[a:Area, t1, t2:Time]: set Report{
	{r:Report | a in r.street.area and gte[r.time,t1] and lte[r.time,t2]}
}

fun getTicketsInAreaAndTime[a:Area, t1, t2:Time]: set Ticket{
	{t:Ticket | a in t.street.area and gte[t.time,t1] and lte[t.time,t2]}
}

fun getAccidentsInAreaAndTime[a:Area, t1, t2:Time]: set Accident{
	{ac:Accident | a in ac.street.area and gte[a.time,t1] and lte[a.time,t2]}
}

fun getParkAccidentsInAreaAndTime[a:Area, t1, t2:Time]: set Accident{
	{ac:getAccidentsInAreaAndTime[a,t1,t2]| ac.cause = BadParkedCar}
}

--ensure reserved statistics values coerence with the tickets data
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

fun getTicketsForLPStreetTime[lp:LicensePlate,s:Street,t1,t2:Time] : set Ticket{
	{t:Ticket | t.licensePlate = lp and t.street = s and gte[t.time,t1] and lte[t.time,t2]}
}

fun getTicketsForLPAreaTime[lp:LicensePlate,a:Area,t1,t2:Time] : set Ticket{
	{t:Ticket | t.licensePlate = lp and a in t.street.area and gte[t.time,t1] and lte[t.time,t2]}
}

//useless functions (to be eliminated)
/*fun getTicketsInStreetTimeLP[s:Street,t1:Time,t2:Time,lp:LicensePlate] : set Ticket{
	getTicketsForLPAndStreet[lp,s] & getTicketsInStreetAndTime[s,t1,t2]
}

fun getApprovedReportsInStreetTimeLP[s:Street,t1:Time,t2:Time,lp:LicensePlate] : set Ticket {
	getApprovedReportsInStreetAndTime[s,t1,t2] & {r:Report | r.licensePlate = lp}
}*/

--approvement of a report
--the facts imply the generation of the corresponding ticket and the respect of the status order
pred approveReport[r,r':Report] {
	r.currStatus = WaitingAgent &&
	r'.user = r.user &&
	r'.street = r.street	&&
	r'.time = r.time &&
	r'.licensePlate = r.licensePlate &&
	r.statusHistory in r'.statusHistory &&
	Approved in Time.(r'.statusHistory)
}


pred show(){}

--run show for 3 but exactly 10 String, exactly 1 Municipality, exactly 1 Street, exactly 12 Report, exactly 8 Accident, exactly 1 Suggestion, exactly 4 Time
run approveReport for 5 but exactly 10 String
