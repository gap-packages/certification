SetPackageInfo( rec(
PackageName := "certification",
Version := "0.0.1",
Date := "02/10/2023",
Dependencies := rec(
  GAP := "4.11",
  NeededOtherPackages := [["GAPDoc", "1.5"], ["JSON", "2.0"]],
  SuggestedOtherPackages := [],
  ExternalConditions := []
),
AvailabilityTest := ReturnTrue
));
