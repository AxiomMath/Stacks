module

public import StacksFrontier.Homology.HomComplex.RHom.ScalarRestrictionTransport

/-!
# The transported restriction comparison absorbs a prefix of restricted scalars

`Stacks.DerivedHom.BaseChange.scalarRestrictionTransportedIso_hom_app` values the transported
restriction comparison

`τ : U ⋙ E.functor ≅ S.functor ⋙ V`

of the factorization of [stacks 0E1W] at an object of the derived category over `A`. This file
identifies the prefix

`E.functor.map (u ≫ U.map m) ≫ E.functor.map (δ.hom.app N) ≫ E.counitIso.hom.app (V.obj N)`,

a morphism out of `E.functor` of an object over `R`, in which the comparison `δ` appears bare and
its argument `N` is an object over the scalar lift of `A`. Bare `δ` followed by the scalar counit
over `R` is `τ` at the inverse image of `N`, followed by the scalar counit over `A`, and
naturality of `τ` moves the restricted morphism `m` out of `E.functor ∘ U` and into
`V ∘ S.functor`. So the prefix is

`E.functor.map u ≫ τ.hom.app Y₁ ≫ V.map (S.functor.map m ≫ S.counitIso.hom.app N)`,

in which `m` occurs only as its scalar lift `S.functor.map m` followed by a counit.

The abstract content is stated over variable categories, with the value of `τ` taken as a
hypothesis.

No tag is registered and no caveat is lifted. Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open; in particular the
comparison identity `h` is untouched and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.

## Main results

* `CategoryTheory.Functor.map_prod_comp_eq_of_fst_eq` -- an equation of morphisms out of a
  bifunctor with its first argument substituted.
* `CategoryTheory.Equivalence.transportedIso_hom_app_inverse_obj` -- **the identification of bare
  `δ`.**  Over variable categories: the component of the comparison followed by the scalar counit
  over the source ring equals the transported comparison at the inverse image, followed by the
  restriction of the scalar counit over the target ring.
* `CategoryTheory.Equivalence.map_comp_map_comp_delta_hom_app` and `…_comp` -- **the prefix
  identity**, without and with a trailing morphism: the same with a restricted morphism and a
  morphism out of an object of the source category in front, moved across by naturality of the
  transported comparison.
* `Stacks.DerivedHom.BaseChange.functor_map_comp_scalarRestrictionIso_hom_app` and `…_comp` -- the
  prefix identity at the scalar-lift equivalences and
  `Stacks.DerivedHom.BaseChange.scalarRestrictionIso`.

## Implementation notes

The keystone's residual equation is not type-correct at `implicit` transparency, so
`rw` cannot find the pattern of
`Stacks.DerivedHom.BaseChange.functor_map_comp_scalarRestrictionIso_hom_app_comp` even where it
is printed verbatim in the goal. `CategoryTheory.Functor.map_prod_comp_eq_of_fst_eq` makes the
substitution by `refine`, which unifies at default transparency: the residual equation is a
composite out of `StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor` at a pair whose first
entry is the prefix, and that lemma replaces the first entry.

## References

* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe uR uA uM

namespace CategoryTheory.Functor

/-- **An equation of morphisms out of a bifunctor, with its first argument substituted.**

If `a` and `a'` agree then a composite beginning with `G.map (a, b)` may be read with `a'` in place
of `a`. -/
public theorem map_prod_comp_eq_of_fst_eq {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂]
    [Category* D] (G : C₁ × C₂ ⥤ D) {X₁ Y₁ : C₁} {X₂ Y₂ : C₂} {a a' : X₁ ⟶ Y₁} (b : X₂ ⟶ Y₂)
    {W : D} (t : G.obj (Y₁, Y₂) ⟶ W) (rhs : G.obj (X₁, X₂) ⟶ W) (ha : a = a')
    (h : G.map (show (X₁, X₂) ⟶ (Y₁, Y₂) from (a', b)) ≫ t = rhs) :
    G.map (show (X₁, X₂) ⟶ (Y₁, Y₂) from (a, b)) ≫ t = rhs :=
  (congrArg (fun z => G.map (show (X₁, X₂) ⟶ (Y₁, Y₂) from (z, b)) ≫ t) ha).trans h

end CategoryTheory.Functor

namespace CategoryTheory.Equivalence

/-- **The bare comparison followed by the scalar counit is the transported comparison at the
inverse image.**

Let `E : C ≌ C'` and `S : D ≌ D'` be equivalences, `U : D ⥤ C` and `V : D' ⥤ C'` functors and
`δ : S.inverse ⋙ U ≅ V ⋙ E.inverse` a comparison between them, and let `t` be a natural
transformation `U ⋙ E.functor ⟶ S.functor ⋙ V` whose components are the ones
`Stacks.DerivedHom.BaseChange.scalarRestrictionTransportedIso_hom_app` gives, namely the unit of
`S` restricted by `U`, then `δ` at the image under `S.functor`, then the counit of `E`.

Then at an object `N` of `D'` the component of `δ` followed by the counit of `E` is `t` at the
inverse image of `N`, followed by `V` of the counit of `S`. -/
theorem transportedIso_hom_app_inverse_obj {C D C' D' : Type*} [Category* C] [Category* D]
    [Category* C'] [Category* D'] (E : C ≌ C') (S : D ≌ D') (U : D ⥤ C) (V : D' ⥤ C')
    (δ : S.inverse ⋙ U ≅ V ⋙ E.inverse) (t : U ⋙ E.functor ⟶ S.functor ⋙ V)
    (ht : ∀ Y, t.app Y =
      E.functor.map (U.map (S.unitIso.hom.app Y) ≫ δ.hom.app (S.functor.obj Y)) ≫
        E.counitIso.hom.app (V.obj (S.functor.obj Y)))
    (N : D') :
    E.functor.map (δ.hom.app N) ≫ E.counitIso.hom.app (V.obj N) =
      t.app (S.inverse.obj N) ≫ V.map (S.counitIso.hom.app N) := by
  have hcounit : E.counitIso.hom.app (V.obj (S.functor.obj (S.inverse.obj N))) ≫
      V.map (S.counitIso.hom.app N) =
      E.functor.map (E.inverse.map (V.map (S.counitIso.hom.app N))) ≫
        E.counitIso.hom.app (V.obj N) :=
    (E.counitIso.hom.naturality (V.map (S.counitIso.hom.app N))).symm
  have hdelta : U.map (S.inverse.map (S.counitIso.hom.app N)) ≫ δ.hom.app N =
      δ.hom.app (S.functor.obj (S.inverse.obj N)) ≫
        E.inverse.map (V.map (S.counitIso.hom.app N)) :=
    δ.hom.naturality (S.counitIso.hom.app N)
  have hid : U.map (S.unitIso.hom.app (S.inverse.obj N)) ≫
      U.map (S.inverse.map (S.counitIso.hom.app N)) = 𝟙 (U.obj (S.inverse.obj N)) := by
    rw [← U.map_comp, S.unit_inverse_comp N]
    exact U.map_id _
  rw [ht (S.inverse.obj N), Category.assoc, hcounit, ← Category.assoc, ← E.functor.map_comp,
    Category.assoc, ← hdelta, ← Category.assoc, hid]
  simp

/-- **The prefix of restricted scalars absorbed into the transported comparison.**

`CategoryTheory.Equivalence.transportedIso_hom_app_inverse_obj` with a restricted morphism
`U.map m` and a morphism `u` out of an object of `C` composed in front: the whole composite is
`E.functor.map u`, then `t` at `Y₁`, then `V` of the scalar lift `S.functor.map m` followed by
the counit of `S`. -/
theorem map_comp_map_comp_delta_hom_app {C D C' D' : Type*} [Category* C] [Category* D]
    [Category* C'] [Category* D'] (E : C ≌ C') (S : D ≌ D') (U : D ⥤ C) (V : D' ⥤ C')
    (δ : S.inverse ⋙ U ≅ V ⋙ E.inverse) (t : U ⋙ E.functor ⟶ S.functor ⋙ V)
    (ht : ∀ Y, t.app Y =
      E.functor.map (U.map (S.unitIso.hom.app Y) ≫ δ.hom.app (S.functor.obj Y)) ≫
        E.counitIso.hom.app (V.obj (S.functor.obj Y)))
    {X₀ : C} {Y₁ : D} {N : D'} (u : X₀ ⟶ U.obj Y₁) (m : Y₁ ⟶ S.inverse.obj N) :
    E.functor.map (u ≫ U.map m) ≫
        E.functor.map (δ.hom.app N) ≫ E.counitIso.hom.app (V.obj N) =
      E.functor.map u ≫ t.app Y₁ ≫ V.map (S.functor.map m ≫ S.counitIso.hom.app N) := by
  have hnat : E.functor.map (U.map m) ≫ t.app (S.inverse.obj N) =
      t.app Y₁ ≫ V.map (S.functor.map m) := t.naturality m
  have hcore : E.functor.map (U.map m) ≫
      E.functor.map (δ.hom.app N) ≫ E.counitIso.hom.app (V.obj N) =
      t.app Y₁ ≫ V.map (S.functor.map m ≫ S.counitIso.hom.app N) := by
    rw [transportedIso_hom_app_inverse_obj E S U V δ t ht N, ← Category.assoc, hnat,
      Category.assoc, ← V.map_comp]
  rw [E.functor.map_comp, Category.assoc, hcore]

/-- **The prefix identity with a tail.**

`CategoryTheory.Equivalence.map_comp_map_comp_delta_hom_app` with a further morphism `p` composed
on the right, and with the comparison and the counit of `E` bracketed together. -/
theorem map_comp_map_comp_delta_hom_app_comp {C D C' D' : Type*} [Category* C] [Category* D]
    [Category* C'] [Category* D'] (E : C ≌ C') (S : D ≌ D') (U : D ⥤ C) (V : D' ⥤ C')
    (δ : S.inverse ⋙ U ≅ V ⋙ E.inverse) (t : U ⋙ E.functor ⟶ S.functor ⋙ V)
    (ht : ∀ Y, t.app Y =
      E.functor.map (U.map (S.unitIso.hom.app Y) ≫ δ.hom.app (S.functor.obj Y)) ≫
        E.counitIso.hom.app (V.obj (S.functor.obj Y)))
    {X₀ : C} {Y₁ : D} {N : D'} {P : C'} (u : X₀ ⟶ U.obj Y₁) (m : Y₁ ⟶ S.inverse.obj N)
    (p : V.obj N ⟶ P) :
    E.functor.map (u ≫ U.map m) ≫
        (E.functor.map (δ.hom.app N) ≫ E.counitIso.hom.app (V.obj N)) ≫ p =
      (E.functor.map u ≫ t.app Y₁ ≫
        V.map (S.functor.map m ≫ S.counitIso.hom.app N)) ≫ p :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ p) (map_comp_map_comp_delta_hom_app E S U V δ t ht u m))

end CategoryTheory.Equivalence

namespace Stacks.DerivedHom.BaseChange

/-- **The keystone's leading three factors, with the [stacks 0A63] transpose lifted.**

`CategoryTheory.Equivalence.map_comp_map_comp_delta_hom_app` at the two scalar-lift equivalences
and `Stacks.DerivedHom.BaseChange.scalarRestrictionIso`, whose transported form is valued by
`Stacks.DerivedHom.BaseChange.scalarRestrictionTransportedIso_hom_app`.

The left-hand side is a morphism `u` out of an object over `R`, followed by the restriction along
`f` of a morphism `m` landing in the inverse image of an object `N` over the lift of `A`, and then
by the comparison `δ` and the counit of the scalar lift over `R`. The right-hand side has `m`
replaced by its scalar lift `S.functor.map m` followed by the counit of the scalar lift over
`A`. -/
public theorem functor_map_comp_scalarRestrictionIso_hom_app
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM} R
    let S := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA,
      max uR uA uM} A
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse := scalarRestrictionIso.{uR, uA, uM} f
    let τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := E.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    ∀ {X₀ : DerivedCategory (ModuleCat.{max uR uA uM} R)}
      {Y₁ : DerivedCategory (ModuleCat.{max uR uA uM} A)}
      {N : DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A))}
      (u : X₀ ⟶ U.obj Y₁) (m : Y₁ ⟶ S.inverse.obj N),
      E.functor.map (u ≫ U.map m) ≫
          E.functor.map (δ.hom.app N) ≫ E.counitIso.hom.app (V.obj N) =
        E.functor.map u ≫ τ.hom.app Y₁ ≫
          V.map (S.functor.map m ≫ S.counitIso.hom.app N) := by
  intro f' E S U V δ τ X₀ Y₁ N u m
  exact CategoryTheory.Equivalence.map_comp_map_comp_delta_hom_app E S U V δ τ.hom
    (fun Y => scalarRestrictionTransportedIso_hom_app.{uR, uA, uM} f Y) u m

/-- **The keystone's leading three factors with their tail, with the [stacks 0A63] transpose
lifted.**

`Stacks.DerivedHom.BaseChange.functor_map_comp_scalarRestrictionIso_hom_app` with a further
morphism `p` composed on the right and the comparison and the counit of the scalar lift over `R`
bracketed together. -/
public theorem functor_map_comp_scalarRestrictionIso_hom_app_comp
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM} R
    let S := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA,
      max uR uA uM} A
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse := scalarRestrictionIso.{uR, uA, uM} f
    let τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := E.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    ∀ {X₀ : DerivedCategory (ModuleCat.{max uR uA uM} R)}
      {Y₁ : DerivedCategory (ModuleCat.{max uR uA uM} A)}
      {N : DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A))}
      {P : DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))}
      (u : X₀ ⟶ U.obj Y₁) (m : Y₁ ⟶ S.inverse.obj N) (p : V.obj N ⟶ P),
      E.functor.map (u ≫ U.map m) ≫
          (E.functor.map (δ.hom.app N) ≫ E.counitIso.hom.app (V.obj N)) ≫ p =
        (E.functor.map u ≫ τ.hom.app Y₁ ≫
          V.map (S.functor.map m ≫ S.counitIso.hom.app N)) ≫ p := by
  intro f' E S U V δ τ X₀ Y₁ N P u m p
  exact CategoryTheory.Equivalence.map_comp_map_comp_delta_hom_app_comp E S U V δ τ.hom
    (fun Y => scalarRestrictionTransportedIso_hom_app.{uR, uA, uM} f Y) u m p

end Stacks.DerivedHom.BaseChange

end
