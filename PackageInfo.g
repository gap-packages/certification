SetPackageInfo( rec(
PackageName := "certification",
Version := "0.0.1",
Date := "02/10/2023",
Dependencies := rec(
  GAP := "4.12",
  NeededOtherPackages := [["JSON", "2.0"]],
  SuggestedOtherPackages := [],
  ExternalConditions := []
),
TestFile := "tst/testall.g",
AvailabilityTest := ReturnTrue
));
