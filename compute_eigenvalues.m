AttachSpec("~/projects/EichlerShimuraHMF/spec");
AttachSpec("~/projects/CHIMP/CHIMP.spec");
/*
diff --git a/precompute.m b/opt/magma/current/package/Geometry/ModFrmHil/precompute.m
index d5e612f..5689fdf 100644
--- a/precompute.m
+++ b/opt/magma/current/package/Geometry/ModFrmHil/precompute.m
@@ -574,7 +574,6 @@ procedure precompute_tps(OH, P, ridls, record_idx, rows)
   small_prime and:= ramified or
     use_theta select 10*num le #rows/C // would be 1*num if thetas distinguished all orders, and ignoring all overhead
                else h/2*num le #rows/C;
-     small_prime := true; //Edgar hack
   use_theta and:= small_prime; // only the small_prime method involves thetas

   if not assigned OH`RightIdealClasses[record_idx]`rids_narrow_class_junk then
*/
try
    f := LMFDBHMF(label);
    F := BaseField(Parent(f));
    prime := LMFDBIdeal(F, plabel);
    eigenval := Sprint(Eltseq(HeckeEigenvalue(f, prime)));
    print StripWhiteSpace(Join([plabel, eigenval], ":"));
    exit 0;
catch e
    WriteStderr(e);
    exit 1;
end try;
