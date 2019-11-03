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

abstract sig ReportStatus {}
one sig WaitingAnalysis extends ReportStatus{}
one sig WaitingAgent extends ReportStatus{}
one sig Approved extends ReportStatus{}
one sig Refused extends ReportStatus{}
one sig WaitingControl extends ReportStatus{}

sig Ticket{
	street: one Street,
	report: lone Report,
	time: one Time
}

sig Accident{
	str: one Street,
	cause: one AccidentCause,
	time : one Time,
	licensePlate: one LicensePlate
}

abstract sig AccidentCause{}

one sig HighSpeed extends AccidentCause{}
one sig DrugOrAlchol extends AccidentCause{}
one sig BadParkedCar extends AccidentCause{}
one sig Other extends AccidentCause{}

sig Suggestion{
	street: one Street
}

--all streets where there has been at least two accidents caused by parking or two approved violation reports must present a suggestion
fact suggestionForUnsafeStreets{
--	all s:Street | ( #(all a:Accident | a.cause = BadParkedCar and a.street=s) >= 2 or #(all r:Report | r.status = Approved and r.street =s)>=2 ) implies (some sg:Suggestion|sg.street=s)
	all s:Street | ( #(getAccidentsByPark[s]) >= 2 or #(getApprovedReport[s]) >= 2 ) implies  (some sg:Suggestion|sg.street=s)
}

fun getAccidentsByPark[s:Street] : set Accident{
	(Accident.str :> s)
}
fun getApprovedReport[s:Street] : set Report{
	(street :> s).Street
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

sig ReservedStatiticsData extends StatisticsData {
	most_egregious_offender : one LicensePlate
}

--ensure public statistics values coerence with reports,tickets and accidents data
/*fact publicStatDataCoherent{
	all psd:PublicStatisticsData |
		((psd.street != none) implies (
			psd.num_report = #(all r:Report | r.street = psd.street and gte[r.time,psd.startTime] and lte[r.time,psd.endTime]) and
			psd.num_report = #(all t:Ticket | t.street = psd.street and gte[t.time,psd.startTime] and lte[t.time,psd.endTime]) and
			psd.num_accidents = #(all a:Accidents | a.street = psd.street and gte[a.time,psd.startTime] and lte[a.time,psd.endTime]) and
			psd.num_parks_accidents = #(all a:Accident | a.street = psd.street and a.cause = BadParkedCard and gte[a.time,psd.startTime] and lte[a.time,psd.endTime])
		))
		and
		((psd.area != none) implies(
			psd.num_report = #(all r:Report | r.street.area in psd.area and gte[r.time,psd.startTime] and lte[r.time,psd.endTime]) and
			psd.num_report = #(all t:Ticket | t.street.area in psd.area and gte[t.time,psd.startTime] and lte[t.time,psd.endTime]) and
			psd.num_accidents = #(all a:Accidents | a.street.area in psd.area and gte[a.time,psd.startTime] and lte[a.time,psd.endTime]) and
			psd.num_parks_accidents = #(all a:Accident | a.street.area in psd.area and a.cause = BadParkedCard and gte[a.time,psd.startTime] and lte[a.time,psd.endTime])
		))
}

--ensure public statistics values coerence with reports,tickets and accidents data
fact reservedStatDataCoherent{
	all rsd:ReservedStatisticsData | 
		(rsd.street != none) implies (
			let max = #(all t:Ticket | t.licensePlate = rsd.most_egregious_offender and t.street = rsd.street) |
			(all lp:LicensePlate | #(all t:Ticket | t.licensePlate = lp and t.street = rsd.street) <= max)
		)

}*/

pred show {}

run show






