module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.AlgebraicGeometry.DerivedTilde.Basic

/-!
# The right adjoint of pushforward for a morphism of affine schemes

Let `A → B` be a homomorphism of commutative rings, `Y = Spec A`, `X = Spec B` and
`f : X ⟶ Y` the induced morphism. Derived sheafification identifies `D(A)` with
`D_QCoh(𝒪_Y)` and `D(B)` with `D_QCoh(𝒪_X)`, and under those identifications `Rf_*`
corresponds to restriction of scalars `D(B) ⥤ D(A)`. Consequently a right adjoint of `Rf_*`
corresponds to a right adjoint of restriction of scalars, that is to `RHom_A(B, -)`.

The last step — "consequently" — is what is proved here, and it is formal: a right adjoint is
determined up to canonical isomorphism, so transporting one adjunction along equivalences on
both sides and a commuting square for the left adjoints transports the right adjoints too.

## Main results

* `CategoryTheory.Adjunction.rightAdjointIsoOfSquare` transports an isomorphism of left
  adjoints along equivalences into an isomorphism of right adjoints.
* `CategoryTheory.Adjunction.ofSquare` does the same when no adjunction for the transported
  functor is given: a functor conjugate to a left adjoint is a left adjoint, and its right
  adjoint is the conjugate of the right adjoint.
* `AlgebraicGeometry.derivedTilde_comp_rightAdjointIso` is the affine case: granted that
  derived sheafification is an equivalence on both sides and that the square for the left
  adjoints commutes, the right adjoint of derived pushforward corresponds to the right adjoint
  of derived restriction of scalars.

## Implementation notes

**No `@[stacks 0A9F]` attribute appears below, deliberately.** Tag 0A9F asserts two things
beyond the transport proved here, and both enter the statement below as hypotheses: that derived
sheafification `AlgebraicGeometry.derivedTilde` *is* an equivalence `D(A) ≌ D_QCoh(𝒪_{Spec A})`,
the remaining content of [Stacks, Tag 06Z0], and that derived pushforward along
`Spec B ⟶ Spec A` corresponds to restriction of scalars, [Stacks, Tag 0DJK]. An attribute on a
statement carrying them would report 0A9F as formalized on the strength of the formal step alone.

Both inputs are proved — `AlgebraicGeometry.derivedTilde_isEquivalence` in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalence.lean` and
`AlgebraicGeometry.derivedTildeCompDerivedQuasicoherentPushforwardIso` in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/AffineDerivedPushforward.lean` — and the
tag is placed where they are used to discharge the hypotheses, on
`AlgebraicGeometry.derivedTilde_comp_rightAdjoint_derivedQuasicoherentPushforwardIsoDerivedHom` in
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/AffineRightAdjointDerivedHom.lean`. This
file keeps the hypothesis form, which is the general transport and is what that statement uses.

Everything is stated at the *locally small* derived categories, `ModuleCat.hasDerivedCategory`
and `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which is the model
`AlgebraicGeometry.derivedTilde` is stated at and which is not interchangeable with
`CategoryTheory.HasDerivedCategory.standard`; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/DerivedTilde/Basic.lean`. In particular the right adjoint of
derived restriction of scalars is a hypothesis rather than `Dualizing.derivedHom`, which is
stated at the standard model.

## References

* [Stacks Project, Tag 0A9F](https://stacks.math.columbia.edu/tag/0A9F)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 0DJK](https://stacks.math.columbia.edu/tag/0DJK)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {D : Type u₃} [Category.{v₃} D] {D' : Type u₄} [Category.{v₄} D']

/-- **Right adjoints transported along equivalences.** Let `eR : C ≌ C'` and `eS : D ≌ D'` be
equivalences, let `P : D' ⥤ C'` and `Res : D ⥤ C` be left adjoints of `a` and of `RH`, and
suppose the square of left adjoints commutes: `eS.functor ⋙ P ≅ Res ⋙ eR.functor`. Then the
square of right adjoints commutes: `eR.functor ⋙ a ≅ RH ⋙ eS.functor`.

Only uniqueness of right adjoints is used; the isomorphism is the canonical one between the two
right adjoints of `eS.inverse ⋙ Res`. -/
noncomputable def rightAdjointIsoOfSquare (eR : C ≌ C') (eS : D ≌ D')
    {P : D' ⥤ C'} {a : C' ⥤ D'} (adjP : P ⊣ a)
    {Res : D ⥤ C} {RH : C ⥤ D} (adjRes : Res ⊣ RH)
    (h : eS.functor ⋙ P ≅ Res ⋙ eR.functor) :
    eR.functor ⋙ a ≅ RH ⋙ eS.functor :=
  have leftIso : P ⋙ eR.inverse ≅ eS.inverse ⋙ Res :=
    calc P ⋙ eR.inverse
        ≅ (𝟭 _ ⋙ P) ⋙ eR.inverse :=
          Functor.isoWhiskerRight (Functor.leftUnitor P).symm eR.inverse
      _ ≅ ((eS.inverse ⋙ eS.functor) ⋙ P) ⋙ eR.inverse :=
          Functor.isoWhiskerRight (Functor.isoWhiskerRight eS.counitIso.symm P) eR.inverse
      _ ≅ (eS.inverse ⋙ (eS.functor ⋙ P)) ⋙ eR.inverse :=
          Functor.isoWhiskerRight (Functor.associator eS.inverse eS.functor P) eR.inverse
      _ ≅ (eS.inverse ⋙ (Res ⋙ eR.functor)) ⋙ eR.inverse :=
          Functor.isoWhiskerRight (Functor.isoWhiskerLeft eS.inverse h) eR.inverse
      _ ≅ ((eS.inverse ⋙ Res) ⋙ eR.functor) ⋙ eR.inverse :=
          Functor.isoWhiskerRight (Functor.associator eS.inverse Res eR.functor).symm eR.inverse
      _ ≅ (eS.inverse ⋙ Res) ⋙ (eR.functor ⋙ eR.inverse) :=
          Functor.associator (eS.inverse ⋙ Res) eR.functor eR.inverse
      _ ≅ (eS.inverse ⋙ Res) ⋙ 𝟭 _ :=
          Functor.isoWhiskerLeft (eS.inverse ⋙ Res) eR.unitIso.symm
      _ ≅ eS.inverse ⋙ Res := Functor.rightUnitor _
  rightAdjointUniq ((adjP.comp eR.symm.toAdjunction).ofNatIsoLeft leftIso)
    (eS.symm.toAdjunction.comp adjRes)

/-- **A functor conjugate to a left adjoint is a left adjoint, with the conjugate right adjoint.**
Let `eR : C ≌ C'` and `eS : D ≌ D'` be equivalences, let `Res : D ⥤ C` have a right adjoint `RH`,
and let `P : D' ⥤ C'` be a functor making the square of left adjoints commute,
`eS.functor ⋙ P ≅ Res ⋙ eR.functor`. Then `P` is itself a left adjoint, with right adjoint
`eR.inverse ⋙ RH ⋙ eS.functor`.

The square identifies `P` with the composite `eS.inverse ⋙ Res ⋙ eR.functor` of three left
adjoints, so the adjunction is the composite of the three; transporting it along that isomorphism
leaves the right adjoint unchanged. This complements
`CategoryTheory.Adjunction.rightAdjointIsoOfSquare`, which takes an adjunction `P ⊣ a` as given
and only compares `a` with `RH`: here no adjunction for `P` is assumed, and the conclusion
produces one. -/
noncomputable def ofSquare (eR : C ≌ C') (eS : D ≌ D')
    {P : D' ⥤ C'} {Res : D ⥤ C} {RH : C ⥤ D} (adjRes : Res ⊣ RH)
    (h : eS.functor ⋙ P ≅ Res ⋙ eR.functor) :
    P ⊣ eR.inverse ⋙ RH ⋙ eS.functor :=
  have leftIso : (eS.inverse ⋙ Res) ⋙ eR.functor ≅ P :=
    calc (eS.inverse ⋙ Res) ⋙ eR.functor
        ≅ eS.inverse ⋙ Res ⋙ eR.functor := Functor.associator _ _ _
      _ ≅ eS.inverse ⋙ eS.functor ⋙ P := Functor.isoWhiskerLeft eS.inverse h.symm
      _ ≅ (eS.inverse ⋙ eS.functor) ⋙ P := (Functor.associator _ _ _).symm
      _ ≅ 𝟭 D' ⋙ P := Functor.isoWhiskerRight eS.counitIso P
      _ ≅ P := Functor.leftUnitor P
  ((eS.symm.toAdjunction.comp adjRes).comp eR.toAdjunction).ofNatIsoLeft leftIso

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

/-- **The right adjoint of derived pushforward between affine schemes.** Let `φ : R ⟶ S` be a
homomorphism of commutative rings. Suppose derived sheafification is an equivalence
`D(R) ≌ D_QCoh(𝒪_{Spec R})` and `D(S) ≌ D_QCoh(𝒪_{Spec S})` ([Stacks, Tag 06Z0]), let `P` be a
functor `D_QCoh(𝒪_{Spec S}) ⥤ D_QCoh(𝒪_{Spec R})` with a right adjoint `a` which corresponds
to derived restriction of scalars under those equivalences ([Stacks, Tag 0DJK]), and let `RH`
be a right adjoint of derived restriction of scalars ([Stacks, Tag 0A70]). Then `a`
corresponds to `RH` under the same equivalences.

This is the "hence" of [Stacks, Tag 0A9F]; see the implementation notes of this file for why no
attribute is attached. -/
noncomputable def derivedTilde_comp_rightAdjointIso {R S : CommRingCat.{u}} (φ : R ⟶ S)
    [(derivedTilde R).IsEquivalence] [(derivedTilde S).IsEquivalence]
    {P : (DerivedCategoryB.derivedCategoryB (A := (Spec S).Modules)
        (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory}
    {a : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB (A := (Spec S).Modules)
        (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf)).FullSubcategory}
    (adjP : P ⊣ a)
    (hP : derivedTilde S ⋙ P ≅
      (ModuleCat.restrictScalars.{u} φ.hom).mapDerivedCategory ⋙ derivedTilde R)
    {RH : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S)}
    (adjRes : (ModuleCat.restrictScalars.{u} φ.hom).mapDerivedCategory ⊣ RH) :
    derivedTilde R ⋙ a ≅ RH ⋙ derivedTilde S :=
  Adjunction.rightAdjointIsoOfSquare (derivedTilde R).asEquivalence
    (derivedTilde S).asEquivalence adjP adjRes hP

end AlgebraicGeometry

end
