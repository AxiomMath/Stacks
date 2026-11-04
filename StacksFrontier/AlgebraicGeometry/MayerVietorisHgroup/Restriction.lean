module

public import StacksFrontier.AlgebraicGeometry.MayerVietorisHgroup.AmbientOpen
public import StacksFrontier.AlgebraicGeometry.MayerVietorisHgroup.RestrictCover
public import StacksFrontier.Algebra.Homology.DerivedDeltaOfShortComplexHom

/-!
# Restricting the Mayer--Vietoris sequence to a smaller ambient open

Let `X` be a topological space, `O` a sheaf of rings on `X`, and let `U ⊔ V = W` and
`U' ⊔ V' = W'` be two Mayer--Vietoris covers with `U' ≤ U`, `V' ≤ V` and `W' ≤ W`. The
restriction maps `Hⁿ(W,-) ⟶ Hⁿ(W',-)`, `Hⁿ(U,-) ⊞ Hⁿ(V,-) ⟶ Hⁿ(U',-) ⊞ Hⁿ(V',-)` and
`Hⁿ(U ⊓ V,-) ⟶ Hⁿ(U' ⊓ V',-)` then form a **morphism of the two Mayer--Vietoris long exact
sequences** built by `Stacks.Cohomology.AmbientMayerVietoris.ambientDelta`.

For the two non-connecting maps that is transitivity of restriction. For the **connecting** map
the two Mayer--Vietoris sequences are built from different short complexes of functors, and they
are compared by `CategoryTheory.rightDerivedDelta_comp_of_hom` at the two Mayer--Vietoris short
complexes of sections functors. Here `W'` is an arbitrary open below `W` carrying an arbitrary
cover below the given one.

## Main results

* `Stacks.Cohomology.AmbientMayerVietoris.ambientToCover_comp_biprodMap` and
  `ambientToIntersection_comp_secRestrict`: the two squares exhibiting restriction as a morphism
  of the two Mayer--Vietoris short complexes of sections functors.
* `Stacks.Cohomology.AmbientMayerVietoris.hrestrictNT_comp_ambientDelta`: **the connecting map of
  the Mayer--Vietoris sequence commutes with restriction to a smaller ambient open along a
  smaller cover**, as an identity of natural transformations.
* `Stacks.Cohomology.AmbientMayerVietoris.hrestrict_comp_ambientDelta`: the same square at a
  fixed sheaf of modules, on the cohomology groups.

## Implementation notes

The middle vertical map is `biprod.map` of the two restrictions, which is the only shape in which
the comparison can be stated: the middle term of the derived sequence is the biproduct of the two
cohomology functors, split by `CategoryTheory.Functor.rightDerivedBiprodIso`. The two squares are
checked on the biproduct
summands, and both reduce to `Stacks.Cohomology.AmbientMayerVietoris.secRestrict_comp`, the
transitivity of restriction on sections. The proofs of the four `≤` relations used in the
statements are irrelevant: `secRestrict` depends on a proof of a proposition, so two spellings of
the same inequality give the same map.

## References

* [Stacks Project, Tag 01EB](https://stacks.math.columbia.edu/tag/01EB)
* [Stacks Project, Tag 09MR](https://stacks.math.columbia.edu/tag/09MR)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Category
open Stacks.Cohomology

universe u

namespace Stacks.Cohomology.AmbientMayerVietoris

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-! ### The two squares of sections functors -/

/-- **Restriction commutes with the first map of the Mayer--Vietoris short complex.** Restricting
from `W` to the cover `U, V` and then to the smaller `U', V'` is restricting from `W` to `W'` and
then to `U', V'`, both being the pair of the restrictions `Γ(W,-) ⟶ Γ(U',-)` and
`Γ(W,-) ⟶ Γ(V',-)`. -/
public theorem ambientToCover_comp_biprodMap (W U V W' U' V' : Opens X)
    (hU : U ≤ W) (hV : V ≤ W) (hU' : U' ≤ W') (hV' : V' ≤ W')
    (kU : U' ≤ U) (kV : V' ≤ V) (kW : W' ≤ W) :
    ambientToCover O W U V hU hV ≫ biprod.map (secRestrict O kU) (secRestrict O kV) =
      secRestrict O kW ≫ ambientToCover O W' U' V' hU' hV' := by
  dsimp only [ambientToCover]
  refine biprod.hom_ext _ _ ?_ ?_ <;> simp [secRestrict_comp]

/-- **Restriction commutes with the second map of the Mayer--Vietoris short complex.** On the
`U`-summand both composites are the restriction `Γ(U,-) ⟶ Γ(U' ⊓ V',-)`, and on the `V`-summand
both are minus the restriction `Γ(V,-) ⟶ Γ(U' ⊓ V',-)`. -/
public theorem ambientToIntersection_comp_secRestrict (U V U' V' : Opens X)
    (kU : U' ≤ U) (kV : V' ≤ V) :
    ambientToIntersection O U V ≫ secRestrict O (inf_le_inf kU kV) =
      biprod.map (secRestrict O kU) (secRestrict O kV) ≫ ambientToIntersection O U' V' := by
  dsimp only [ambientToIntersection]
  refine biprod.hom_ext' _ _ ?_ ?_ <;> simp [secRestrict_comp]

/-! ### Restriction on cohomology, and the connecting map -/

section Hgroup

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} O)]

/-- **The Mayer--Vietoris connecting map commutes with restriction to a smaller ambient open
along a smaller cover.** For `U ⊔ V = W` and `U' ⊔ V' = W'` with `U' ≤ U`, `V' ≤ V` and
`W' ≤ W`,

`Hⁿ(U ⊓ V,-) ⟶ Hⁿ(U' ⊓ V',-) ⟶ Hⁿ⁺¹(W',-)`  equals  `Hⁿ(U ⊓ V,-) ⟶ Hⁿ⁺¹(W,-) ⟶ Hⁿ⁺¹(W',-)`,

as natural transformations. Together with
`Stacks.Cohomology.AmbientMayerVietoris.hrestrictNT_comp` on the two non-connecting maps — whose
spellings as restrictions are `ambientFirst_eq` and
`Stacks.Cohomology.AbsoluteMayerVietoris.mvSecond_eq` — this makes restriction a morphism of the
two Mayer--Vietoris long exact sequences. -/
public theorem hrestrictNT_comp_ambientDelta (W U V W' U' V' : Opens X)
    (hU : U ≤ W) (hV : V ≤ W) (hUV : U ⊔ V = W)
    (hU' : U' ≤ W') (hV' : V' ≤ W') (hUV' : U' ⊔ V' = W')
    (kU : U' ≤ U) (kV : V' ≤ V) (kW : W' ≤ W) (n : ℕ) :
    HrestrictNT O (inf_le_inf kU kV) n ≫ ambientDelta O W' U' V' hU' hV' hUV' n =
      ambientDelta O W U V hU hV hUV n ≫ HrestrictNT O kW (n + 1) :=
  CategoryTheory.rightDerivedDelta_comp_of_hom
    (ambientToCover O W U V hU hV) (ambientToIntersection O U V)
    (ambientToCover_comp_ambientToIntersection O W U V hU hV)
    (ambientShortExact_on_injectives O W U V hU hV hUV)
    (ambientToCover O W' U' V' hU' hV') (ambientToIntersection O U' V')
    (ambientToCover_comp_ambientToIntersection O W' U' V' hU' hV')
    (ambientShortExact_on_injectives O W' U' V' hU' hV' hUV')
    (secRestrict O kW) (biprod.map (secRestrict O kU) (secRestrict O kV))
    (secRestrict O (inf_le_inf kU kV))
    (ambientToCover_comp_biprodMap O W U V W' U' V' hU hV hU' hV' kU kV kW)
    (ambientToIntersection_comp_secRestrict O U V U' V' kU kV) n

/-- `Stacks.Cohomology.AmbientMayerVietoris.hrestrictNT_comp_ambientDelta` at a fixed sheaf of
modules, as a square of maps of cohomology groups. -/
public theorem hrestrict_comp_ambientDelta (W U V W' U' V' : Opens X)
    (hU : U ≤ W) (hV : V ≤ W) (hUV : U ⊔ V = W)
    (hU' : U' ≤ W') (hV' : V' ≤ W') (hUV' : U' ⊔ V' = W')
    (kU : U' ≤ U) (kV : V' ≤ V) (kW : W' ≤ W) (n : ℕ) (F : SheafOfModules.{u} O) :
    Hrestrict O (inf_le_inf kU kV) n F ≫ (ambientDelta O W' U' V' hU' hV' hUV' n).app F =
      (ambientDelta O W U V hU hV hUV n).app F ≫ Hrestrict O kW (n + 1) F := by
  simpa only [NatTrans.comp_app, Hrestrict] using NatTrans.congr_app
    (hrestrictNT_comp_ambientDelta O W U V W' U' V' hU hV hUV hU' hV' hUV' kU kV kW n) F

end Hgroup

end Stacks.Cohomology.AmbientMayerVietoris

end
