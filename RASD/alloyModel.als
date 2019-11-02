abstract sig User{
	password : one String
 }

sig AuthenticatedUser extends User {
	username : one String
	reports : set Report
	identityCard : one String
	fiscalCode : one String
}

sig MunicipalityAgent extends User {
	id : one Int
	municipality : one Municipality
}

sig MunicipalitySupervisor extends User{
	username : one String
	municipality : one Municipality
}

fact noDifferentUserWithSameIdentityCard{
	no  disj u1,u2: AuthenticatedUser | u1.identityCard = u2.identityCard
}

fact noDifferentUserWithSameUsername{
	no  disj u1,u2: AuthenticatedUser | u1.username = u2.username and 
	no disj s1,s2 : MunicipalitySupervisor | s1.username = s2.username
}

fact noDifferentUserWithSameFiscalCode{
	no  disj u1,u2: AuthenticatedUser | u1.fiscalCode = u2.fiscalCode
}

fact allMunicipalityHaveOneAgentAndSupervisor{
	all m:Municipality | ( ( some a:Agent | a.municipality = m) and ( some s:Supervisor | s.municipality = m))
 }

sig Visitor extends User{
}

sig Municipality{ }

sig Street{

}

sig Area{ 

}

sig Report{

}

abstract sig SuggestionType{}

sig increaseControls extends SuggestionType{}

sig addParkSlots extends SuggestionType{}

sig addBarriers extends SuggestionType{}

sig modifyParkTime extends SuggestionType{}

abstract sig Statistics{}

sig 

sig StatisticsRequest{
	user : one User
	type : one Statistics
	status : one RequestStatus
}

abstract sig RequestStatus{}
sig RequestAccepted extends RequestStatus{}
sig RequestRefused extends RequestStatus{}






