module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AbelianCechCokernelPassage
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.AbelianModelComparison

/-!
# The abelian action of `i_*ℋ ⁿ_T` through the unbounded model, and the one input it still needs

Let `X` be a scheme, `T ⊆ X` a closed subset and `ℱ`, `𝒢` sheaves of `𝒪_X`-modules.  Two
constructions in this library let `i_*ℋ ⁿ_T` act on a morphism `ψ : ℱ_ab ⟶ 𝒢_ab` of the underlying
sheaves of abelian groups — a morphism which need not be `𝒪_X`-linear, a relative de Rham
differential being the case of interest:

* `Stacks.Perfect.AbelianCechCokernelPassage.supportCohomologyForgetAbMap`, which is the degree-`n`
  cohomology of the right-hand vertical arrow of the derived square of step (ii) of
  [Stacks, Tag 0G85], and is built from
  `Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedEndoForgetComparison` — the comparison
  of [Stacks, Tag 0G74] part (2) in the **unbounded** model, with `i_*` folded in;
* `Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafAbelianMap` and, in the spelling of the
  target of the Gysin map of [Stacks, Tag 0G83],
  `Stacks.Perfect.GysinAbelianSquare.gysinTargetAbelianMap`, built from
  `Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexForgetIso` — the same
  comparison in the **classical** `ℕ`-indexed model.

No declaration relates the two, and that is the only thing between the library and the naturality
of the class map of [Stacks, Tag 0G7Q] in a merely additive morphism; see the implementation notes
of `Stacks.Perfect.AbelianCechCokernelPassage`, whose two final theorems carry the identity as a
hypothesis `hforget` **depending on `ψ`**.

This file removes `ψ` from that hypothesis.  It writes the first action as a conjugation —
`supportCohomologyForgetAbMap_eq` — of the abelian functor `i_*ℋ ⁿ_T` applied to `ψ` by one
explicit isomorphism `endoForgetIsoApp`, namely the unbounded model comparison followed by the
model bridge `Stacks.Cohomology.AbelianModelComparison.abelianModelComponent`; the second action is
already such a conjugation by construction.  Two conjugations of the same map by the same
isomorphism agree, so each consumer of `hforget` is reduced to a single `ψ`-free identity of
isomorphisms, which is exactly the statement recorded as owed in the implementation notes of
`Stacks.Cohomology.AbelianModelComparison`.

## Main definitions

* `singleForgetIso`: **forgetting the module structure commutes with placing a module in degree
  `0`**, read in the derived category: `Φ(ℱ[0]) ≅ (Φℱ)[0]`.  This is the comparison of the
  localizations followed by `HomologicalComplex.singleMapHomologicalComplex`.
* `forgetPushApp`: the unbounded-model side of the comparison at a module — the inverse of
  `Stacks.Perfect.AbelianCechCokernelPassage.forgetDerivedHomology`, then the comparison of
  [Stacks, Tag 0G74] part (2) with `i_*` folded in, then `singleForgetIso`.
* `abelianModelApp`, `endoForgetIsoApp`: the model bridge at the underlying abelian sheaf of a
  module, and the composite of the two — an isomorphism
  `Φ(i_*ℋ ⁿ_T(ℱ)) ≅ i_*ℋ ⁿ_T(Φℱ)` built entirely from the unbounded model.
* `pushIsoApp`: the same kind of isomorphism built from the **classical** model, namely
  `Stacks.Perfect.GysinAbelianSquare.pushforwardLocalCohomologyForgetIso` at a module.

## Main results

* `derivedSingleAb_eq`: `Stacks.Perfect.AbelianCechDerivedSquare.derivedSingleAb` — the morphism
  `ψ` placed in degree `0` in `D(Ab(X))` — is the single functor of abelian sheaves applied to `ψ`,
  conjugated by `singleForgetIso`.  This is the only place where the chain-level definition of that
  morphism is opened up.
* `forgetSupportPushAbMap_eq` and `forgetPush_conj`: the right-hand vertical arrow of the derived
  square, and its degree-`n` cohomology, written as conjugations of the abelian functor applied to
  `ψ`.
* `supportCohomologyForgetAbMap_eq`: **the action of `i_*ℋ ⁿ_T` on `ψ` from the unbounded model is
  the conjugation of `i_*ℋ ⁿ_T(ψ)` by `endoForgetIsoApp`.**  This is the result the file exists
  for, and it carries no hypothesis beyond `hT`.
* `supportCohomologySheafAbelianMap_eq_supportCohomologyForgetAbMap_of_forgetIso`: **the two
  actions agree**, given the `ψ`-free identity
  `endoForgetIsoApp = pushforwardLocalCohomologyForgetIso` in the spelling of [Stacks, Tag 0G7S].
  That identity is proved in
  `StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/SupportedEndoForgetDegreewise.lean`,
  which also records the resulting unconditional statement.
* `forgetIsoSquare_of_forgetIsoApp`,
  `cokernelLastDifToPushforwardAbelianNatural_of_forgetIsoApp` and
  `topCechClassAbelianNatural_of_forgetIsoApp`: the hypothesis `hforget` of
  `Stacks.Perfect.AbelianCechCokernelPassage`, the square of step (ii) of [Stacks, Tag 0G85] above
  the Čech cokernel in the Gysin map's spelling, and the naturality of the class map of
  [Stacks, Tag 0G7Q] — each from the single `ψ`-free identity `forgetIsoApp`.

## Implementation notes

**Carried hypotheses.**  Everything up to and including `supportCohomologyForgetAbMap_eq` carries
exactly a closed subset `T` and a degree `n : ℕ`; no quasi-coherence, and no hypothesis whatsoever
on `ψ`, which is the whole point.  The declarations of the last section carry, in addition, the
quasi-coherence of the two coefficient modules — inherited from
`cokernelLastDifToPushforwardAbelianNatural_of_forgetIsoSquare` of
`Stacks.Perfect.AbelianCechCokernelPassage`
— and the `ψ`-free hypothesis described next.

**The one input this file does not supply.**  The hypothesis of
`supportCohomologySheafAbelianMap_eq_supportCohomologyForgetAbMap_of_forgetIso`, and the hypothesis
`forgetIsoApp` of the last section, say that the isomorphism `endoForgetIsoApp` built from the
unbounded model agrees with the one built from the classical model.  What this file buys is that it
no longer mentions `ψ`: it is an identity between two isomorphisms, naturally the statement that
`Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedEndoForgetComparison` and
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafForgetComparison` are the same comparison
of [Stacks, Tag 0G74] part (2), read on degree-`n` cohomology sheaves.  Both are
`CategoryTheory.Functor.rightDerivedDesc` of their respective transported underived comparisons, so
proving it is a `CategoryTheory.Functor.rightDerived_ext` argument of the same shape as
`Stacks.Cohomology.AbelianSupportedCounitForget.whiskerRight_derivedSupportedSectionsToId`,
followed by the degreewise assembly.  **Both steps are carried out downstream**, not here: the
`rightDerived_ext` argument is
`Stacks.Perfect.SupportedEndoForgetIdentity.endoForgetComparison_eq` and the degreewise assembly is
`Stacks.Perfect.SupportedEndoForgetDegreewise.derivedForgetIdentity`, so both hypotheses of this
file are discharged there for an arbitrary closed subset and degree.

**Why the comparisons are named as values at an object.**  `singleForgetIso`, `forgetPushApp`,
`abelianModelApp`, `endoForgetIsoApp` and `pushIsoApp` are values of natural isomorphisms at an
object, with both ends of their types written as `Functor.obj` applied to an object rather than as
the value of a composite functor.  This is not cosmetic, for the reason recorded in the
implementation notes of `Stacks.Perfect.AbelianCechCokernelPassage`: a term whose type is stated
through a composite functor is type-correct only up to unfolding `CategoryTheory.Functor.comp`, and
in a goal containing one, `rw`, `simp` and `reassoc_of%` all report that they have nothing to do.
`Stacks.Cohomology.AbelianModelComparison.abelianModelComponent` and
`Stacks.Perfect.AbelianCechDerivedSquare.forgetComparison` are both stated at such a type.

**Why `mid_formal`, `conj_map_formal`, `conj_eq_formal` and `square_of_conj_formal` are stated at
an abstract category.**  The composites they reassociate contain the components just described, so
`Category.assoc` and `CategoryTheory.Functor.map_comp` rewrite nothing in them in place.  At a
variable category every rewrite is immediate and `exact` — which works up to default transparency
— instantiates the result.  This is the device of
`Stacks.Perfect.AbelianCechDerivedSquare.square_formal` and
`Stacks.Perfect.AbelianCechCokernelPassage.assoc_formal`, for the same reason.

**Module visibility.**  This module is not listed in the `StacksDraft` umbrella, matching
`Stacks.Perfect.AbelianCechCokernelPassage` and
`Stacks.Cohomology.SupportedComplexes.LocalCohomologySpellingBridge`; consumers import it by name.

**No `@[stacks ...]` attribute is attached to any declaration here**, and nothing here proves
[Stacks, Tag 0G85] or [Stacks, Tag 0G74].

## References

* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7S](https://stacks.math.columbia.edu/tag/0G7S)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Lemma 20.34.6 (Tag 0G72)](https://stacks.math.columbia.edu/tag/0G72)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.AbelianModelComparison (abelianModelComponent
  abelianModelComponent_hom_naturality)
open Stacks.Cohomology.AbelianSupportedCounit (derivedAbelianSupportedPushforward)
open Stacks.Perfect.AbelianCechCokernelPassage (forgetDerivedHomology forgetSupportPushAbMap
  supportCohomologyForgetAbMap
  cokernelLastDifToPushforwardAbelianNatural_of_forgetIsoSquare
  topCechClassAbelianNatural_of_forgetIsoSquare)
open Stacks.Perfect.AbelianCechDerivedSquare (derivedSingleAb forgetComparisonIso singleCplxAb)
open Stacks.Perfect.AbelianFraction (abelianSheaf abHom)
open Stacks.Perfect.CechDerivedSupport (isClosed_equationsClosedSet)
open Stacks.Perfect.CechSupportTransport (supportCohomologyToPushforward)
open Stacks.Perfect.GysinAbelianSquare (abelianLocalCohomologyPushforward gysinTargetAbelianMap
  pushforwardLocalCohomologyForgetIso supportCohomologySheafAbelianMap
  supportCohomologySheafForgetIso)
open Stacks.Perfect.SupportedFraction
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.AbelianSupportedEndoModelBridge

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Formal reassociations -/

/-- Splitting a functor applied to a threefold composite, inside a longer composite, at an
abstract category; stated at a variable category for the reason recorded in the implementation
notes. -/
private lemma mid_formal {C₀ D₀ : Type*} [Category* C₀] [Category* D₀] (Phi : C₀ ⥤ D₀)
    {A B C D : C₀} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) {P Q : D₀}
    (p : P ⟶ Phi.obj A) (q : Phi.obj D ⟶ Q) :
    p ≫ Phi.map (a ≫ b ≫ c) ≫ q =
      p ≫ Phi.map a ≫ Phi.map b ≫ Phi.map c ≫ q := by
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]

/-- A conjugation inside the image of a functor is the image of the conjugation, at an abstract
category: the shape of `forgetPush_conj` below. -/
private lemma conj_map_formal {C₀ D₀ : Type*} [Category* C₀] [Category* D₀] (Phi : C₀ ⥤ D₀)
    {A A' B B' M M' : C₀} (e₁ : A ≅ B) (e₂ : B ≅ M) (e₁' : A' ≅ B') (e₂' : B' ≅ M')
    (m : M ⟶ M') (t : A ⟶ A') (ht : t = e₁.hom ≫ e₂.hom ≫ m ≫ e₂'.inv ≫ e₁'.inv)
    {P P' : D₀} (p : Phi.obj A ≅ P) (p' : Phi.obj A' ≅ P') :
    (p.symm ≪≫ Phi.mapIso e₁ ≪≫ Phi.mapIso e₂).hom ≫ Phi.map m ≫
        (p'.symm ≪≫ Phi.mapIso e₁' ≪≫ Phi.mapIso e₂').inv =
      p.inv ≫ Phi.map t ≫ p'.hom := by
  subst ht
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, CategoryTheory.Functor.map_comp, Category.assoc]

/-- Reading a commuting square as a conjugation, at an abstract category. -/
private lemma conj_of_square {C₀ : Type*} [Category* C₀] {A B A' B' : C₀}
    (e : A ≅ B) (e' : A' ≅ B') (u : B ⟶ B') (v : A ⟶ A')
    (h : v ≫ e'.hom = e.hom ≫ u) : e.hom ≫ u ≫ e'.inv = v := by
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Conjugating by two isomorphisms with the same forward direction gives the same map, at an
abstract category. -/
private lemma conj_eq_formal {C₀ : Type*} [Category* C₀] {A A' B B' : C₀}
    (e f : A ≅ B) (e' f' : A' ≅ B') (u : B ⟶ B')
    (he : e.hom = f.hom) (he' : e'.hom = f'.hom) :
    e.hom ≫ u ≫ e'.inv = f.hom ≫ u ≫ f'.inv := by
  obtain rfl : e = f := Iso.ext he
  obtain rfl : e' = f' := Iso.ext he'
  rfl

/-- The square of `forgetIsoSquare_of_forgetIsoApp` below, at an abstract category: two
conjugations of the same map by isomorphisms which differ by a transport commute with that
transport. -/
private lemma square_of_conj_formal {C₀ : Type*} [Category* C₀] {A A' B B' D D' : C₀}
    (wF : A ≅ B) (wG : A' ≅ B') (pF : D ≅ B) (pG : D' ≅ B') (tF : A ⟶ D) (tG : A' ⟶ D')
    (u : B ⟶ B') (hF : tF ≫ pF.hom = wF.hom) (hG : tG ≫ pG.hom = wG.hom) :
    tF ≫ pF.hom ≫ u ≫ pG.inv = (wF.hom ≫ u ≫ wG.inv) ≫ tG := by
  rw [← Category.assoc, hF, (Iso.eq_comp_inv pG).2 hG]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

variable {X : Scheme.{u}}

/-! ### Forgetting the module structure commutes with placing a module in degree `0` -/

/-- **Forgetting the module structure commutes with placing a module in degree `0`**, read in the
derived categories: `Φ(ℱ[0]) ≅ (Φℱ)[0]`.

It is the comparison `CategoryTheory.Functor.mapDerivedCategoryFactors` identifying the forgetful
functor on derived categories with the forgetful functor applied degreewise, followed by the
localization of `HomologicalComplex.singleMapHomologicalComplex`.  Mathlib's
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor` is the same isomorphism, assembled
differently; this spelling is the one in which `derivedSingleAb_eq` is immediate. -/
def singleForgetIso (H : X.Modules) :
    (abelianSheaf X).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj H) ≅
      (DerivedCategory.singleFunctor
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) 0).obj
        ((abelianSheaf X).obj H) :=
  (abelianSheaf X).mapDerivedCategoryFactors.app
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj H) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (abelianSheaf X)
        (ComplexShape.up ℤ) 0).app H)

/-- **`ψ` placed in degree `0` is the single functor of abelian sheaves applied to `ψ`**,
conjugated by `singleForgetIso`.  This is the only place in the file where the chain-level
definition of `Stacks.Perfect.AbelianCechDerivedSquare.derivedSingleAb` is opened up; everything
else is formal. -/
lemma derivedSingleAb_eq {F G : X.Modules}
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    derivedSingleAb ψ =
      (singleForgetIso F).hom ≫
        (DerivedCategory.singleFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) 0).map (abHom ψ) ≫
        (singleForgetIso G).inv := by
  rw [singleForgetIso, singleForgetIso,
    Stacks.Perfect.AbelianCechDerivedSquare.derivedSingleAb, singleCplxAb]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

/-! ### The abelian action of `i_*ℋ ⁿ_T` through the unbounded model -/

section Unbounded

variable {T : Set X} (hT : IsClosed T) (n : ℕ)

/-- **The unbounded-model side of [Stacks, Tag 0G74] part (2) at a module**: the underlying
abelian sheaf of `i_*ℋ ⁿ_T(ℱ)` is the degree-`n` cohomology of `i_* R𝓗_T^{ab}(Φℱ[0])`.

It is the inverse of `Stacks.Perfect.AbelianCechCokernelPassage.forgetDerivedHomology`, which moves
the forgetful functor past the cohomology of the derived category, then the degree-`n` cohomology
of the comparison `Stacks.Perfect.AbelianCechDerivedSquare.forgetComparison` of
[Stacks, Tag 0G74] part (2) with `i_*` folded in, then `singleForgetIso`. -/
def forgetPushApp (H : X.Modules) :
    (abelianSheaf X).obj (supportCohomologySheaf hT H (n : ℤ)) ≅
      (DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (n : ℤ)).obj
        ((derivedAbelianSupportedPushforward X.toRingedSpace T hT).obj
          ((DerivedCategory.singleFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) 0).obj
            ((abelianSheaf X).obj H))) :=
  (forgetDerivedHomology (supportPushSingle hT H) (n : ℤ)).symm ≪≫
    (DerivedCategory.homologyFunctor
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (n : ℤ)).mapIso
      (forgetComparisonIso hT ((DerivedCategory.singleFunctor X.Modules 0).obj H)) ≪≫
    (DerivedCategory.homologyFunctor
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (n : ℤ)).mapIso
      ((derivedAbelianSupportedPushforward X.toRingedSpace T hT).mapIso (singleForgetIso H))

/-- **The abelian model comparison at the underlying abelian sheaf of a module**: the degree-`n`
cohomology of `i_* R𝓗_T^{ab}(Φℱ[0])` is `i_*ℋ ⁿ_T(Φℱ)` in the classical `ℕ`-indexed model.  This is
`Stacks.Cohomology.AbelianModelComparison.abelianModelComponent`, with its target spelled by
`Stacks.Perfect.GysinAbelianSquare.abelianLocalCohomologyPushforward`. -/
def abelianModelApp (H : X.Modules) :
    (DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (n : ℤ)).obj
        ((derivedAbelianSupportedPushforward X.toRingedSpace T hT).obj
          ((DerivedCategory.singleFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) 0).obj
            ((abelianSheaf X).obj H))) ≅
      (abelianLocalCohomologyPushforward X.toRingedSpace T hT n).obj ((abelianSheaf X).obj H) :=
  abelianModelComponent X.toRingedSpace T hT n ((abelianSheaf X).obj H)

/-- **[Stacks, Tag 0G74] part (2) at a module, built entirely from the unbounded model**: the
underlying abelian sheaf of `i_*ℋ ⁿ_T(ℱ)` is the abelian local cohomology sheaf `i_*ℋ ⁿ_T(Φℱ)`.

This is `forgetPushApp` followed by `abelianModelApp`.  It is the isomorphism by which
`Stacks.Perfect.AbelianCechCokernelPassage.supportCohomologyForgetAbMap` is a conjugation, which is
`supportCohomologyForgetAbMap_eq`. -/
def endoForgetIsoApp (H : X.Modules) :
    (abelianSheaf X).obj (supportCohomologySheaf hT H (n : ℤ)) ≅
      (abelianLocalCohomologyPushforward X.toRingedSpace T hT n).obj ((abelianSheaf X).obj H) :=
  forgetPushApp hT n H ≪≫ abelianModelApp hT n H

/-- The model comparison carries the degree-`n` cohomology of `i_* R𝓗_T^{ab}` applied to a
morphism of abelian sheaves to the abelian functor `i_*ℋ ⁿ_T` applied to it.  This is the
naturality of `Stacks.Cohomology.AbelianModelComparison.abelianModelComponent`, read as a
conjugation. -/
lemma model_conj {F G : X.Modules} (χ : (abelianSheaf X).obj F ⟶ (abelianSheaf X).obj G) :
    (abelianModelApp hT n F).hom ≫
        (abelianLocalCohomologyPushforward X.toRingedSpace T hT n).map χ ≫
        (abelianModelApp hT n G).inv =
      (DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (n : ℤ)).map
        ((derivedAbelianSupportedPushforward X.toRingedSpace T hT).map
          ((DerivedCategory.singleFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) 0).map χ)) :=
  conj_of_square (abelianModelApp hT n F) (abelianModelApp hT n G) _ _
    (abelianModelComponent_hom_naturality X.toRingedSpace T hT n χ)

/-- **The right-hand vertical arrow of the derived square of step (ii) of [Stacks, Tag 0G85] is a
conjugation**: it is `i_* R𝓗_T^{ab}` applied to `ψ` placed in degree `0` on abelian sheaves,
conjugated by the comparison of [Stacks, Tag 0G74] part (2) and by `singleForgetIso`. -/
lemma forgetSupportPushAbMap_eq {F G : X.Modules}
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    forgetSupportPushAbMap hT ψ =
      (forgetComparisonIso hT ((DerivedCategory.singleFunctor X.Modules 0).obj F)).hom ≫
        (derivedAbelianSupportedPushforward X.toRingedSpace T hT).map
          (singleForgetIso F).hom ≫
        (derivedAbelianSupportedPushforward X.toRingedSpace T hT).map
          ((DerivedCategory.singleFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) 0).map (abHom ψ)) ≫
        (derivedAbelianSupportedPushforward X.toRingedSpace T hT).map
          (singleForgetIso G).inv ≫
        (forgetComparisonIso hT ((DerivedCategory.singleFunctor X.Modules 0).obj G)).inv := by
  rw [Stacks.Perfect.AbelianCechCokernelPassage.forgetSupportPushAbMap, derivedSingleAb_eq]
  exact mid_formal (derivedAbelianSupportedPushforward X.toRingedSpace T hT) _ _ _ _ _

/-- The degree-`n` cohomology of the derived square's right-hand vertical arrow is the degree-`n`
cohomology of `i_* R𝓗_T^{ab}` applied to `ψ` in degree `0`, conjugated by `forgetPushApp`. -/
lemma forgetPush_conj {F G : X.Modules}
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (forgetPushApp hT n F).hom ≫
        (DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (n : ℤ)).map
          ((derivedAbelianSupportedPushforward X.toRingedSpace T hT).map
            ((DerivedCategory.singleFunctor
              (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) 0).map
              (abHom ψ))) ≫
        (forgetPushApp hT n G).inv =
      supportCohomologyForgetAbMap hT (n : ℤ) ψ :=
  conj_map_formal
    (DerivedCategory.homologyFunctor
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (n : ℤ))
    (forgetComparisonIso hT ((DerivedCategory.singleFunctor X.Modules 0).obj F))
    ((derivedAbelianSupportedPushforward X.toRingedSpace T hT).mapIso (singleForgetIso F))
    (forgetComparisonIso hT ((DerivedCategory.singleFunctor X.Modules 0).obj G))
    ((derivedAbelianSupportedPushforward X.toRingedSpace T hT).mapIso (singleForgetIso G))
    _ _ (forgetSupportPushAbMap_eq hT ψ)
    (forgetDerivedHomology (supportPushSingle hT F) (n : ℤ))
    (forgetDerivedHomology (supportPushSingle hT G) (n : ℤ))

/-- **The action of `i_*ℋ ⁿ_T` on a morphism of the underlying abelian sheaves obtained from the
unbounded model is a conjugation of the abelian functor `i_*ℋ ⁿ_T` applied to that morphism**, by
the isomorphism `endoForgetIsoApp` of [Stacks, Tag 0G74] part (2).

This is the result the file exists for: the other construction of the same action,
`Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafAbelianMap`, is such a conjugation by
construction, so comparing the two no longer involves `ψ`.  No hypothesis beyond `hT`; in
particular no quasi-coherence and nothing whatsoever on `ψ`. -/
theorem supportCohomologyForgetAbMap_eq {F G : X.Modules}
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    supportCohomologyForgetAbMap hT (n : ℤ) ψ =
      (endoForgetIsoApp hT n F).hom ≫
        (abelianLocalCohomologyPushforward X.toRingedSpace T hT n).map (abHom ψ) ≫
        (endoForgetIsoApp hT n G).inv := by
  rw [endoForgetIsoApp, endoForgetIsoApp, Iso.trans_hom, Iso.trans_inv, Category.assoc,
    reassoc_of% (model_conj hT n (abHom ψ)), forgetPush_conj hT n ψ]

/-- **[Stacks, Tag 0G74] part (2) at a module, built from the classical model**: the value at a
module of `Stacks.Perfect.GysinAbelianSquare.pushforwardLocalCohomologyForgetIso`, with both ends
of its type written as `Functor.obj` applied to an object. -/
def pushIsoApp (H : X.Modules) :
    (abelianSheaf X).obj
        ((GysinLocalCohomology.localCohomologyPushforwardFunctor hT (n : ℤ)).obj H) ≅
      (abelianLocalCohomologyPushforward X.toRingedSpace T hT n).obj ((abelianSheaf X).obj H) :=
  (pushforwardLocalCohomologyForgetIso hT n).app H

/-- **The two constructions of the action of `i_*ℋ ⁿ_T` on a morphism of the underlying abelian
sheaves agree, given the `ψ`-free identity of the two readings of [Stacks, Tag 0G74] part (2).**

The hypothesis `hforgetIso` is that identity in the spelling of [Stacks, Tag 0G7S]; it mentions no
morphism of coefficient modules.  Both actions are conjugations of the abelian functor
`i_*ℋ ⁿ_T` applied to `ψ` — the right-hand side by `supportCohomologyForgetAbMap_eq`, the left-hand
side by construction — so they agree as soon as the conjugating isomorphisms do.

The hypothesis is discharged, for every closed subset and every degree, by
`Stacks.Perfect.SupportedEndoForgetDegreewise.supportCohomologySheafForgetIso_hom_app`; the
resulting unconditional statement is
`supportCohomologySheafAbelianMap_eq_supportCohomologyForgetAbMap` of
`Stacks.Perfect.SupportedEndoForgetDegreewise`.  That file is downstream of this one, which is why
the hypothesis is still carried here. -/
theorem supportCohomologySheafAbelianMap_eq_supportCohomologyForgetAbMap_of_forgetIso
    {F G : X.Modules}
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (hforgetIso : ∀ H : X.Modules,
      (supportCohomologySheafForgetIso hT n).hom.app H = (endoForgetIsoApp hT n H).hom) :
    supportCohomologySheafAbelianMap hT n (abHom ψ) =
      supportCohomologyForgetAbMap hT (n : ℤ) ψ := by
  rw [supportCohomologyForgetAbMap_eq hT n ψ]
  exact conj_eq_formal ((supportCohomologySheafForgetIso hT n).app F) (endoForgetIsoApp hT n F)
    ((supportCohomologySheafForgetIso hT n).app G) (endoForgetIsoApp hT n G) _
    (hforgetIso F) (hforgetIso G)

end Unbounded

/-! ### The square of step (ii) of Stacks 0G85 in the Gysin map's spelling -/

section Assembly

variable {n : ℕ} (f : Fin (n + 1) → Γ(X, ⊤)) {F G : X.Modules}

/-- **The hypothesis `hforget` of
`cokernelLastDifToPushforwardAbelianNatural_of_forgetIsoSquare` of
`Stacks.Perfect.AbelianCechCokernelPassage`
follows from a `ψ`-free identity of isomorphisms.**

The hypothesis `forgetIsoApp` says that the comparison
`Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward` between the two places at
which the degree-`c` cohomology sheaf is taken carries the classical-model reading `pushIsoApp` of
[Stacks, Tag 0G74] part (2) to the unbounded-model reading `endoForgetIsoApp`.  It mentions no
morphism of coefficient modules and no Čech complex.

Given it, the square of the two actions is formal: the right-hand side is a conjugation by
`endoForgetIsoApp` by `supportCohomologyForgetAbMap_eq`, and
`Stacks.Perfect.GysinAbelianSquare.gysinTargetAbelianMap` is a conjugation by `pushIsoApp` by
construction. -/
theorem forgetIsoSquare_of_forgetIsoApp
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (forgetIsoApp : ∀ H : X.Modules,
      (abelianSheaf X).map (supportCohomologyToPushforward f H).hom ≫
          (pushIsoApp (isClosed_equationsClosedSet f) (n + 1) H).hom =
        (endoForgetIsoApp (isClosed_equationsClosedSet f) (n + 1) H).hom) :
    (abelianSheaf X).map (supportCohomologyToPushforward f F).hom ≫
        gysinTargetAbelianMap f (abHom ψ) =
      supportCohomologyForgetAbMap (isClosed_equationsClosedSet f) ((n + 1 : ℕ) : ℤ) ψ ≫
        (abelianSheaf X).map (supportCohomologyToPushforward f G).hom := by
  rw [supportCohomologyForgetAbMap_eq (isClosed_equationsClosedSet f) (n + 1) ψ]
  exact square_of_conj_formal
    (endoForgetIsoApp (isClosed_equationsClosedSet f) (n + 1) F)
    (endoForgetIsoApp (isClosed_equationsClosedSet f) (n + 1) G)
    (pushIsoApp (isClosed_equationsClosedSet f) (n + 1) F)
    (pushIsoApp (isClosed_equationsClosedSet f) (n + 1) G)
    _ _ _ (forgetIsoApp F) (forgetIsoApp G)

/-- **The square of step (ii) of [Stacks, Tag 0G85] above the Čech cokernel, in the spelling the
Gysin map of [Stacks, Tag 0G83] is built in**, from the `ψ`-free identity `forgetIsoApp`.

This is
`cokernelLastDifToPushforwardAbelianNatural_of_forgetIsoSquare` of
`Stacks.Perfect.AbelianCechCokernelPassage`
with its `ψ`-dependent hypothesis discharged by `forgetIsoSquare_of_forgetIsoApp`. -/
theorem cokernelLastDifToPushforwardAbelianNatural_of_forgetIsoApp
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (forgetIsoApp : ∀ H : X.Modules,
      (abelianSheaf X).map (supportCohomologyToPushforward f H).hom ≫
          (pushIsoApp (isClosed_equationsClosedSet f) (n + 1) H).hom =
        (endoForgetIsoApp (isClosed_equationsClosedSet f) (n + 1) H).hom) :
    Stacks.Perfect.AbelianClassMap.CokernelLastDifToPushforwardAbelianNatural f ψ :=
  cokernelLastDifToPushforwardAbelianNatural_of_forgetIsoSquare f ψ
    (forgetIsoSquare_of_forgetIsoApp f ψ forgetIsoApp)

/-- **The naturality of the class map of [Stacks, Tag 0G7Q] in a morphism of the underlying
abelian sheaves follows**, from the same `ψ`-free identity.  This chains
`cokernelLastDifToPushforwardAbelianNatural_of_forgetIsoApp` with the equivalence
`Stacks.Perfect.AbelianClassMap.topCechClassAbelianNatural_iff_abelianSquare`, through
`Stacks.Perfect.AbelianCechCokernelPassage.topCechClassAbelianNatural_of_forgetIsoSquare`. -/
theorem topCechClassAbelianNatural_of_forgetIsoApp
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (forgetIsoApp : ∀ H : X.Modules,
      (abelianSheaf X).map (supportCohomologyToPushforward f H).hom ≫
          (pushIsoApp (isClosed_equationsClosedSet f) (n + 1) H).hom =
        (endoForgetIsoApp (isClosed_equationsClosedSet f) (n + 1) H).hom) :
    Stacks.Perfect.GysinFractionDeRham.TopCechClassAbelianNatural f ψ :=
  topCechClassAbelianNatural_of_forgetIsoSquare f ψ
    (forgetIsoSquare_of_forgetIsoApp f ψ forgetIsoApp)

end Assembly

end Stacks.Perfect.AbelianSupportedEndoModelBridge

end
