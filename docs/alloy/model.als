sig Username, Password {}

abstract sig Person {
	username : one Username,
	password : one Password
}

sig FiscalCode{}

sig User extends Person {
	id : one FiscalCode
}

sig Operator extends Person {}

sig Municipality {}

sig Authority {
	employs : some Operator,
	zone : some Municipality
}

sig Vehicle {
	plate : one LicensePlate
}

sig LicensePlate {}

sig Violation {
	where : one Location,
	vehicle : one Vehicle,
	picture : one Picture
}

sig Picture{}

sig Location {
	belongsTo : one Municipality,
	latitude : one Int,
	longitude : one Int
}{
	latitude > -90 and latitude < 90 and
	longitude > -180 and longitude < 180
}

sig Accident{
	crashWhere : one Location
}

sig SuggestedAction {
	possibleCause : some Violation,
	prevents : some Accident
}

fact noFosterFiscalCode {
	all fisc : FiscalCode | fisc in User.id
}

fact UniqueUsername {
	no disj a, b: Person | (a.username = b.username)
}

fact noFosterPassword {
	all p : Password | p in Person.password
}

fact noFosterUsername {
	all u : Username | u in Person.username
}

fact noFosterOperator {
	all op : Operator | op in Authority.employs
}

fact noFosterMunicipality {
	all mun : Municipality | mun in Authority.zone
}

fact noFosterVehicles {
	all v : Vehicle | v in Violation.vehicle
}

fact noFosterLocation {
	all loc : Location | loc in Violation.where or loc in Accident.crashWhere
}

fact noFosterLicensePlate{
	all lp : LicensePlate | lp in Vehicle.plate
}

fact noFosterPicture{
	all pic : Picture | pic in Violation.picture
}

fact noMultiJobs {
	all disj a, b : Authority | (no op : Operator | 
		op in a.employs and op in b.employs)
}

fact onlyOneAuthorityPerPlace {
	all disj a, b : Authority | (no mun : Municipality | 
		mun in a.zone and mun in b.zone)
}

fact UniqueLicensePlates {
	no disj v1, v2 : Vehicle | v1.plate = v2.plate
}

fact NoDuplicateLocations {
	no disj loc1, loc2 : Location | (loc1.latitude = loc2.latitude) or 
		(loc1.longitude = loc2.longitude)
}

fact UniquePictures {
	no disj v1, v2 : Violation | v1.picture = v2.picture
}

fact UniqueFiscalCode{
	no disj u1, u2 : User | u1.id = u2.id
}	

fun getAuthorityFromOperator[op : Operator]: set Authority {
	employs.op
}

fun getViolationsFromMunicipality[mun : Municipality]: set Violation{
	where.belongsTo.mun
}

fun visibleViolations[op : Operator]: set Violation{
	getViolationsFromMunicipality[getAuthorityFromOperator[op].zone]
}

run show {
	#Operator > 1
	#User > 1
	#Location > 1
	#Violation > 1
} for 4 but 9 Int