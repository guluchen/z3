(declare-fun T1_3 () String)
(declare-fun T2_3 () String)
(declare-fun T_1 () String)
(declare-fun var_0xINPUT_8645 () String)
(assert (= T_1 (str.++ T1_3 T2_3)))
(assert (= T2_3 "//3.ig.gmodules.com/gadgets/makeRequest?refresh=3600&url=http%3A%2F%2Fwww.mylisty.net%2FListy%2Fhtml%2FUserManager.action%3Ftype%3Dnew_user%26sid%3D0.3993759937637733&httpMethod=GET&headers=&postData=&authz=&st=&contentType=DOM&numEntries=3&getSummaries=false&signOwner=true&signViewer=true&gadget=http%3A%2F%2Fwww.mylisty.net%2FListy%2Fgadget%2FMyListy.xml&container=ig&bypassSpecCache=0"))
(assert (= T1_3 var_0xINPUT_8645))
(check-sat)
