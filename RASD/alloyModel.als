open util/time

abstract sig User{
	password : one String
 }

sig AuthenticatedUser extends User {
	username : one String,
	reports : set Report,
	identityCard : one String,
	fiscalCode : one String
}

sig MunicipalityAgent extends User {
	id : one Int,
	municipality : one Municipality
}

sig MunicipalitySupervisor extends User{
	username : one String,
	municipality : one Municipality
}

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

sig Visitor extends User{
}

sig Municipality{ }

sig Street{
	area: some Area
}

sig Area{ 
	municipality: one Municipality
}

sig LicensePlate {}

sig Report{
	user: one AuthenticatedUser,
	-- for simplicity the gps position is substituted by a direct association with the Street
	street: one Street,	
	status: one ReportStatus,
	time: one Time,
	licensePlate: one LicensePlate,
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
	#(nextSatus) = 0
}
one sig Refused extends ReportStatus{}
{
	#(nextSatus) = 0
}
one sig WaitingControl extends ReportStatus{}
{
	#(nextStatus) = 2 and ( Approved in nextStatus) and (Refused in nextStatus)
}

sig Ticket{
	street: one Street,
	report: lone Report,
	time: one Time
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

--all streets where there has been at least two accidents caused by parking or two approved violation reports must present a suggestion
--here, considering the Time type available, has been used the interval [t.prev,t] to find the events corresponding to a Suggestion at the time t
--clearly this should be a defined interval of time (a month)
fact suggestionForUnsafeStreets{
--	all s:Street | ( #(all a:Accident | a.cause = BadParkedCar and a.street=s) >= 2 or #(all r:Report | r.status = Approved and r.street =s)>=2 ) implies (some sg:Suggestion|sg.street=s)
	all s:Street, t:Time | ( #(getParkAccidentsInStreetAndTime[s,t.prev,t]) >= 2 and #(getApprovedReportsInStreetAndTime[s,t.prev,t]) >= 2 ) iff  (some sg:Suggestion|sg.street=s and sg.time = t)
}

/*fun getAccidentsByPark3[s:Street] : set Accident{
	((Accident <: street) :> s).Street & ((Accident <: cause) :> BadParkedCar).BadParkedCar
}
fun getAccidentsByPark2[s:Street] : set Accident{
	(Accident <: street).s & (Accident <: cause).BadParkedCar
}*/

fun getApprovedReportsInStreetAndTime[s:Street,t1,t2:Time] : set Report{
	--((Report <: street) :> s).Street  & ((Report <: status) :> Approved).Approved
	{r:Report | r.street = s and r.status = Approved and gte[r.time,t1] and lte[r.time,t2]}
}

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

--reserved statistics cannot be accessed by normal users
fact statisticsPrivacy{
	all sr:StatisticsRequest | sr.status = RequestAccepted iff ( sr.level = PublicStatistics or (one u:MunicipalityAgent | sr.user = u) or (one u:MunicipalitySupervisor | sr.user = u)) 
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
			let max = #(getTicketsForLPAndStreet[rsd.most_egregious_offender,rsd.street]) |
			(all lp:LicensePlate | #(getTicketsForLPAndStreet[lp,rsd.street]) <= max)
		))
		and
		((rsd.area != none) implies (
			let max = #(getTicketsForLPAndArea[rsd.most_egregious_offender,rsd.area]) |
			(all lp:LicensePlate | #(getTicketsForLPAndArea[lp,rsd.area]) <= max)
		))
	

}

fun getTicketsForLPAndStreet[lp:LicensePlate,s:Street] : set Ticket{
	{t:Ticket | t.licensePlate = lp and t.street = s}
}

fun getTicketsForLPAndArea[lp:LicensePlate,a:Area] : set Ticket{
	{t:Ticket | t.licensePlate = lp and a in t.street.area}
}

pred show(){}

run show for 3 but exactly 10 String, exactly 1 Municipality, exactly 1 Street, exactly 12 Report, exactly 8 Accident, exactly 1 Suggestion
