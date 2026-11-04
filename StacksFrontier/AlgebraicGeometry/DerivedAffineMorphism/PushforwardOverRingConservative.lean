module

public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.DerivedPushforwardOverPushforwardRing
public import StacksFrontier.Homology.DerivedCategory.IsZero

/-!
# Vanishing and invertibility are the same question for `Φ` and for `Rf_*`

Let `f : X ⟶ S` be a morphism of schemes and let
`Φ : D(𝒪_X) ⥤ D(f_* 𝒪_X)` be the derived direct image over `f_* 𝒪_X` of
`StacksFrontier/AlgebraicGeometry/DerivedAffineMorphism/DerivedPushforwardOverPushforwardRing.lean`,
the functor of [Stacks, Tag 0AVW].  That file identifies `Rf_*` with `Φ` followed by the functor
`D(f_* 𝒪_X) ⥤ D(𝒪_S)` induced by restriction of scalars along `𝒪_S ⟶ f_* 𝒪_X`.  This file draws
the consequence that restriction of scalars loses no information: an object or a morphism of
`D(f_* 𝒪_X)` in the image of `Φ` is zero, or invertible, exactly when the corresponding object or
morphism of `D(𝒪_S)` is.

The input is that restriction of scalars along a map of sheaves of rings is **faithful** — it does
not change the underlying sheaf of abelian groups, which is
`SheafOfModules.restrictScalarsCompToSheaf`, and the forgetful functor to sheaves of abelian
groups is faithful.  A faithful functor between abelian categories reflects monomorphisms and
epimorphisms, hence isomorphisms, and it reflects zero objects; restriction of scalars is also
exact, so the functor it induces on derived categories reflects isomorphisms as well
(`CategoryTheory.Functor.reflectsIsomorphisms_mapDerivedCategory`) and commutes with cohomology.

This is the step "`H^i(Φ(K)) = H^i(Rf_*K)`" of the proof of [Stacks, Tag 0AVW]: it reduces every
vanishing and invertibility question about `Φ` to the same question about `Rf_*`, where the
affine-morphism results of the library — [Stacks, Tag 08D5], [Stacks, Tag 08I8] — apply.  It does
**not** prove that `Φ` is an equivalence; see the implementation notes.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.DerivedAffinePushforward`.

* `isZero_scalarRestriction_obj_iff` — a sheaf of `f_* 𝒪_X`-modules is zero exactly when its
  scalar restriction is.
* `isIso_derivedPushforwardOverRing_map_iff` — `Φα` is invertible exactly when `Rf_*α` is.
* `isZero_homologyFunctor_derivedPushforwardOverRing_iff` — `H^i(ΦE) = 0` exactly when
  `H^i(Rf_*E) = 0`.
* `isZero_derivedPushforwardOverRing_obj_iff` — `ΦE = 0` exactly when `Rf_*E = 0`.
* `reflectsIsomorphisms_derivedPushforwardOverRing` — `Φ` reflects isomorphisms as soon as `Rf_*`
  does.

## Implementation notes

*No `@[stacks 0AVW]` attribute is placed here.*  The tag's first clause is that `Φ` restricts to
an **equivalence** `D_QCoh(𝒪_X) ⥤ D_QCoh(f_* 𝒪_X)` for an affine morphism, and nothing below
constructs a quasi-inverse: the source obtains it as the derived pullback `Lg^*` along the
morphism of ringed spaces `g : (X, 𝒪_X) ⟶ (S, f_* 𝒪_X)`, using that `g` is flat, which is done
in `StacksFrontier/AlgebraicGeometry/DerivedAffineMorphism/FlatOverPushforwardRing.lean`.  What
is below is the half of the source's argument that needs no flatness, and the attribute for the
clause that carries one sits on
`DerivedAffinePushforward.derivedPushforwardOverRingCompRestrictScalarsIso` in the namespace
`Stacks.AlgebraicGeometry`.

*Everything is stated with the derived categories as binders*, matching the file whose results
are used; see its implementation notes for why a model may not be pinned here.

## References

* [Stacks Project, Tag 0AVW](https://stacks.math.columbia.edu/tag/0AVW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe w u

namespace Stacks.AlgebraicGeometry.DerivedAffinePushforward

open Stacks.AlgebraicGeometry.AffineQcohPushforward

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### Restriction of scalars is faithful -/

/-- Restriction of scalars along `𝒪_S ⟶ f_* 𝒪_X` is faithful: composed with the forgetful functor
to sheaves of abelian groups it *is* that forgetful functor, by
`SheafOfModules.restrictScalarsCompToSheaf`, and the latter is faithful. -/
instance scalarRestriction_faithful : (scalarRestriction f).Faithful :=
  Functor.Faithful.of_comp_eq (F := scalarRestriction f)
    (G := SheafOfModules.toSheaf.{u} S.ringCatSheaf)
    (H := SheafOfModules.toSheaf.{u} (pushforwardRing f.base X.ringCatSheaf))
    (SheafOfModules.restrictScalarsCompToSheaf.{u} f.toRingCatSheafHom)

/-- **Restriction of scalars reflects zero objects.**  A sheaf of `f_* 𝒪_X`-modules is a zero
object exactly when the `𝒪_S`-module it restricts to is one. -/
theorem isZero_scalarRestriction_obj_iff
    (M : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) :
    IsZero ((scalarRestriction f).obj M) ↔ IsZero M := by
  rw [IsZero.iff_id_eq_zero, IsZero.iff_id_eq_zero,
    ← (scalarRestriction f).map_id M, CategoryTheory.Functor.map_eq_zero_iff]

/-! ### `Φ` and `Rf_*` answer the same questions -/

section Derived

variable [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)]

/-- **`Φα` is invertible exactly when `Rf_*α` is.**  `Rf_*` is `Φ` followed by the derived
restriction of scalars, and that functor reflects isomorphisms. -/
theorem isIso_derivedPushforwardOverRing_map_iff
    {E F : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)} (α : E ⟶ F) :
    IsIso ((derivedPushforwardOverRing.{w} f).map α) ↔
      IsIso ((AlgebraicGeometry.AnyModel.derivedPushforward.{w} f).map α) := by
  rw [NatIso.isIso_map_iff (derivedPushforwardOverRingCompRestrictScalarsIso.{w} f) α]
  exact (isIso_iff_of_reflects_iso ((derivedPushforwardOverRing.{w} f).map α)
    (scalarRestriction f).mapDerivedCategory).symm

/-- **`H^i(ΦE)` vanishes exactly when `H^i(Rf_*E)` does.**  Restriction of scalars is exact, so it
commutes with cohomology, and it reflects zero objects; under the identification of `Rf_*` with
`Φ` followed by derived restriction of scalars this turns `H^i(Rf_*E)` into the scalar restriction
of `H^i(ΦE)`. -/
theorem isZero_homologyFunctor_derivedPushforwardOverRing_iff
    (E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) i).obj
        ((derivedPushforwardOverRing.{w} f).obj E)) ↔
      IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) i).obj
        ((AlgebraicGeometry.AnyModel.derivedPushforward.{w} f).obj E)) :=
  (isZero_scalarRestriction_obj_iff f _).symm.trans
    (Iso.isZero_iff
      ((((scalarRestriction f).mapDerivedCategoryCompHomologyFunctorIso i).app
            ((derivedPushforwardOverRing.{w} f).obj E)).symm ≪≫
        (DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) i).mapIso
          ((derivedPushforwardOverRingCompRestrictScalarsIso.{w} f).app E).symm))

/-- **`ΦE` is zero exactly when `Rf_*E` is**, both being detected on cohomology. -/
theorem isZero_derivedPushforwardOverRing_obj_iff
    (E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) :
    IsZero ((derivedPushforwardOverRing.{w} f).obj E) ↔
      IsZero ((AlgebraicGeometry.AnyModel.derivedPushforward.{w} f).obj E) := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology,
    DerivedCategory.isZero_iff_forall_isZero_homology]
  exact forall_congr' fun i => isZero_homologyFunctor_derivedPushforwardOverRing_iff.{w} f E i

/-- **`Φ` reflects isomorphisms as soon as `Rf_*` does.**  With
`isIso_derivedPushforwardOverRing_map_iff` the two reflection statements are the same statement. -/
theorem reflectsIsomorphisms_derivedPushforwardOverRing
    (h : (AlgebraicGeometry.AnyModel.derivedPushforward.{w} f).ReflectsIsomorphisms) :
    (derivedPushforwardOverRing.{w} f).ReflectsIsomorphisms where
  reflects α hα :=
    have := (isIso_derivedPushforwardOverRing_map_iff.{w} f α).1 hα
    have := h
    isIso_of_reflects_iso α (AlgebraicGeometry.AnyModel.derivedPushforward.{w} f)

end Derived

end Stacks.AlgebraicGeometry.DerivedAffinePushforward

end
