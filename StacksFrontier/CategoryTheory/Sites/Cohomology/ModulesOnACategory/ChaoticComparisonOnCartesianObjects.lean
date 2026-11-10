module

public import Mathlib.CategoryTheory.Sites.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianObjectsLocalizing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticComparisonMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.MorphismsOverAnObject

/-!
# Comparing a topology with the chaotic topology on cartesian objects

Let `C` be a category carrying a Grothendieck topology `τ`, let `τ'` be the chaotic topology on
`C`, and let `O` be a `τ`-sheaf of rings.  The identity functor of `C` is a morphism of ringed
sites `ε : (C_τ, O_τ) ⟶ (C_τ', O_τ')`; since every presheaf is a `τ'`-sheaf, a module on
`(C_τ', O_τ')` is a presheaf of `O`-modules, `ε_*` is the forgetful functor and `ε^*` is
`τ`-sheafification.  Write `D(O)` for the derived category of presheaves of `O`-modules,
`RΓ(U, -)` for derived sections over an object `U` of `C` — on the chaotic side this is the exact
evaluation functor, so no derived correction occurs — and `QC(O) ⊆ D(O)` for the full subcategory
of cartesian objects, those `K` for which `RΓ(V, K) ⊗^L_{O(V)} O(U) ⟶ RΓ(U, K)` is invertible for
every `U ⟶ V` in `C`.

For an object `U` of `C`, `O_U` is the restriction of `O` to the localized site `(C/U, τ)`, and
`K|_U` the restriction of an object `K` of `D(O)` to `C/U`.

## Main definitions

* `Stacks.ModulesOnACategory.ChaoticComparison.overRingSheaf`: the restriction `O_U` of `O` to the
  localized site `(C/U, τ)`.
* `Stacks.ModulesOnACategory.ChaoticComparison.IsLocallyKFlatAcyclic`: the condition that for
  every object `U` of `C` and every object `P` of `D(O(U))` the canonical map
  `P ⟶ RΓ((C/U)_τ, (P ⊗^L_{O(U)} O_U)^#)` is invertible.

## Main results

* `Stacks.ModulesOnACategory.ChaoticComparison.isIso_of_forall_isIso_app`: a morphism of
  presheaves of modules which is invertible on sections over every object is invertible.
* `Stacks.ModulesOnACategory.ChaoticComparison.cartesianEquivalence`: `Rε_*` restricts to an
  equivalence from the objects `K` of `D(C_τ, O_τ)` with `Rε_*K` cartesian onto `QC(O)` as soon
  as the unit `M ⟶ Rε_*(ε^*M)` is invertible on `QC(O)`.
* `Stacks.ModulesOnACategory.ChaoticComparison.cartesianEquivalenceOfSectionwise`: the same
  equivalence, as soon as the unit becomes invertible on derived sections over every object of
  `C`.
* `Stacks.ModulesOnACategory.ChaoticComparison.homEpsilonPullback_bijective`: for `K` cartesian
  and `M` an object of `D((O_U)_τ)`, the morphisms `ε^*(K|_U) ⟶ M` are the morphisms
  `RΓ(U, K) ⟶ RΓ(U, Rε_*M)` of `D(O(U))`.
* `Stacks.ModulesOnACategory.ChaoticComparison.isIso_rGamma_unit_derivedRestriction`: under
  `IsLocallyKFlatAcyclic`, for a cartesian `M` and every object `U` of `C` the unit
  `M|_U ⟶ Rε_{U*}(ε_U^*(M|_U))` of the localized site becomes invertible on derived sections over
  the terminal object `id_U` of `C/U`.

## References

* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
* [Stacks Project, Tag 0GYV](https://stacks.math.columbia.edu/tag/0GYV)
* [Stacks Project, Tag 0H0S](https://stacks.math.columbia.edu/tag/0H0S)
* [Stacks Project, Tag 0H0T](https://stacks.math.columbia.edu/tag/0H0T)
* [Stacks Project, Section 21.42](https://stacks.math.columbia.edu/tag/0EWK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence

universe m w u v r

namespace Stacks.ModulesOnACategory.ChaoticComparison

attribute [local instance] HasDerivedCategory.standard

/-! ### Derived sections detect isomorphisms -/

section Detection

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ RingCat.{r}}

/-- **Sections detect isomorphisms of presheaves of modules.** A morphism of presheaves of
`O`-modules whose component over every object of `C` is invertible is invertible. -/
theorem isIso_of_forall_isIso_app {M N : PresheafOfModules.{m} O} (f : M ⟶ N)
    (hf : ∀ X : Cᵒᵖ, IsIso (f.app X)) : IsIso f := by
  let e : M ≅ N :=
    PresheafOfModules.isoMk (fun X ↦ let := hf X; asIso (f.app X))
      (fun {_ _} g ↦ f.naturality g)
  have he : e.hom = f := PresheafOfModules.hom_ext (fun _ ↦ rfl)
  rw [← he]
  infer_instance

end Detection

/-! ### The equivalence on cartesian objects -/

section Equivalence

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  (bc : BaseChangeData.{w} R.obj)

/-- The property of an object `K` of `D(C_τ, O_τ)` that `Rε_*K` is cartesian, that is, that
`RΓ(V, K) ⊗^L_{O(V)} O(U) ⟶ RΓ(U, K)` is invertible for every `U ⟶ V` in `C`. -/
abbrev IsCartesianPushforward :
    ObjectProperty (DerivedCategory (SheafOfModules.{max u v r w} R)) :=
  pushforwardProperty.{w} R (IsQC.{w} bc)

/-- `ε^*` carries a cartesian object to one whose derived pushforward is again cartesian, as soon
as the unit is invertible there. -/
theorem isCartesianPushforward_mapDerivedCategory_obj
    (hunit : ∀ M, IsQC.{w} bc M → IsIso ((derivedEpsilonAdjunction.{w} R).unit.app M))
    (M : DMod.{w} R.obj) (hM : IsQC.{w} bc M) :
    IsCartesianPushforward.{w} R bc ((epsilonPullback.{w} R).mapDerivedCategory.obj M) :=
  pushforwardProperty_mapDerivedCategory_obj.{w} R (IsQC.{w} bc) hunit M hM

/-- `ε^*` and `Rε_*` are mutually quasi-inverse equivalences between `QC(O)` and the full
subcategory of `D(C_τ, O_τ)` consisting of the objects `K` with `Rε_*K` in `QC(O)`, as soon as
the unit is invertible on `QC(O)`. -/
def cartesianEquivalence
    (hunit : ∀ M, IsQC.{w} bc M → IsIso ((derivedEpsilonAdjunction.{w} R).unit.app M)) :
    (IsCartesianPushforward.{w} R bc).FullSubcategory ≌ QC.{w} bc :=
  restrictedEquivalence.{w} R (IsQC.{w} bc) hunit

/-- The functor of `cartesianEquivalence` is `Rε_*`. -/
theorem cartesianEquivalence_functor
    (hunit : ∀ M, IsQC.{w} bc M → IsIso ((derivedEpsilonAdjunction.{w} R).unit.app M)) :
    (cartesianEquivalence.{w} R bc hunit).functor =
      restrictedPushforward.{w} R (IsQC.{w} bc) :=
  rfl

/-- The equivalence of `cartesianEquivalence`, as soon as `RΓ(U, M) ⟶ RΓ(U, Rε_*(ε^*M))` is
invertible for every cartesian `M` and every object `U` of `C`. -/
def cartesianEquivalenceOfSectionwise
    (hsect : ∀ M, IsQC.{w} bc M → ∀ U : Cᵒᵖ,
      IsIso ((RGamma.{w} R.obj U).map ((derivedEpsilonAdjunction.{w} R).unit.app M))) :
    (IsCartesianPushforward.{w} R bc).FullSubcategory ≌ QC.{w} bc :=
  cartesianEquivalence.{w} R bc
    (fun M hM ↦ QuasiCoherentEquivalence.RGamma_jointly_conservative.{w} _ (hsect M hM))

end Equivalence

/-! ### Morphisms out of a cartesian object over an object of `C` -/

section Bijective

variable {S : Type*} [Category S] {T : Type*} [Category T]

/-- If the counit of an adjunction `adj : L ⊣ Rr` is invertible at `A`, then applying `Rr` and
precomposing with an isomorphism `α : Rr.obj A ≅ P` is a bijection from the morphisms `A ⟶ B` onto
the morphisms `P ⟶ Rr.obj B`. -/
private theorem bijective_conj_rightAdjoint_map {L : S ⥤ T} {Rr : T ⥤ S} (adj : L ⊣ Rr) {A B : T}
    (hA : IsIso (adj.counit.app A)) {P : S} (α : Rr.obj A ≅ P) :
    Function.Bijective (fun f : A ⟶ B => α.inv ≫ Rr.map f) := by
  have hpre : Function.Bijective (fun f : A ⟶ B => adj.counit.app A ≫ f) :=
    ⟨fun a b hab => (cancel_epi (adj.counit.app A)).mp hab,
      fun b => ⟨inv (adj.counit.app A) ≫ b, by simp⟩⟩
  have hα : Function.Bijective (fun g : Rr.obj A ⟶ Rr.obj B => α.inv ≫ g) :=
    ⟨fun a b hab => by simpa using congrArg (fun t => α.hom ≫ t) hab,
      fun b => ⟨α.hom ≫ b, by simp⟩⟩
  have hfun : (fun f : A ⟶ B => α.inv ≫ Rr.map f) =
      (fun g : Rr.obj A ⟶ Rr.obj B => α.inv ≫ g) ∘ (adj.homEquiv (Rr.obj A) B) ∘
        (fun f : A ⟶ B => adj.counit.app A ≫ f) := by
    funext f
    change α.inv ≫ Rr.map f = α.inv ≫ adj.homEquiv (Rr.obj A) B (adj.counit.app A ≫ f)
    rw [Adjunction.homEquiv_apply, Functor.map_comp]
    simp only [adj.right_triangle_components_assoc]
  rw [hfun]
  exact hα.comp ((adj.homEquiv _ _).bijective.comp hpre)

end Bijective

section OverAnObject

open Stacks.ModulesOnACategory.MorphismsOverAnObject
open Stacks.Sites.OverModules (overRingPresheaf)
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange (baseChangeDataOfComm)
open Stacks.ModulesOnACategory.TerminalMorphismOfSites (morphismOfSites)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  (U : C)

/-- The restriction `O_U` of the sheaf of rings `O` to the site `(C/U, τ)` obtained by localizing
`τ` at `U`. -/
def overRingSheaf : Sheaf (J.over U) RingCat.{r} :=
  ⟨overRingPresheaf R.obj U, (Over.forget U).op_comp_isSheaf (J.over U) J R⟩

/-- The underlying presheaf of rings of `O_U` is the restriction of that of `O` along the forgetful
functor `C/U ⥤ C`; in particular its sections over `id_U` are `O(U)`. -/
theorem overRingSheaf_obj : (overRingSheaf R U).obj = overRingPresheaf R.obj U := rfl

variable [HasSheafify (J.over U) AddCommGrpCat.{max u v r w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]

/-- Let `K` be an object of `QC(O)` and let `M` be an arbitrary object of `D((O_U)_τ)`.
Transposing under the adjunction `ε^* ⊣ Rε_*` over `C/U` and then taking derived sections over the
terminal object `id_U` of `C/U` identifies the morphisms `ε^*(K|_U) ⟶ M` of `D((O_U)_τ)` with the
morphisms `RΓ(U, K) ⟶ RΓ(U, Rε_*M)` of `D(O(U))`. -/
@[stacks 0H0T "morphisms out of a sheafified cartesian object are maps of derived sections over U"]
theorem homEpsilonPullback_bijective
    (hO : ∀ (V : Cᵒᵖ) (x y : R.obj.obj V), x * y = y * x)
    (K : DMod.{w} R.obj)
    (hK : IsQC.{w} (baseChangeDataOfComm.{r, v, u, w} R.obj hO) K)
    (M : DerivedCategory (SheafOfModules.{max u v r w} (overRingSheaf R U))) :
    Function.Bijective (fun f : (epsilonPullback.{w} (overRingSheaf R U)).mapDerivedCategory.obj
        ((derivedRestriction.{w} R.obj U).obj K) ⟶ M =>
      ((derivedSectionsIso.{w} R.obj U).app K).inv ≫
        (RGamma.{w} (overRingPresheaf R.obj U) (Opposite.op (Over.mk (𝟙 U)))).map
          ((derivedEpsilonAdjunction.{w} (overRingSheaf R U)).unit.app
              ((derivedRestriction.{w} R.obj U).obj K) ≫
            (derivedEpsilonPushforward.{w} (overRingSheaf R U)).map f)) :=
  (bijective_conj_rightAdjoint_map
      (morphismOfSites (overRingPresheaf R.obj U) (comm_overRingPresheaf R.obj U hO)
        (Over.mkIdTerminal (X := U))).adj
      (main_counit_isIso.{w}
        (baseChangeDataOfComm (overRingPresheaf R.obj U)
          (comm_overRingPresheaf R.obj U hO))
        (morphismOfSites (overRingPresheaf R.obj U) (comm_overRingPresheaf R.obj U hO)
          (Over.mkIdTerminal (X := U)))
        _
        (isQC_derivedRestriction.{w} R.obj U (baseChangeDataOfComm.{r, v, u, w} R.obj hO)
          (baseChangeDataOfComm (overRingPresheaf R.obj U)
            (comm_overRingPresheaf R.obj U hO)) K hK))
      ((derivedSectionsIso.{w} R.obj U).app K)
      (B := (derivedEpsilonPushforward.{w} (overRingSheaf R U)).obj M)).comp
    ((derivedEpsilonAdjunction.{w} (overRingSheaf R U)).homEquiv _ M).bijective

end OverAnObject

/-! ### Locally K-flat acyclicity -/

section HypothesisTwo

open Stacks.ModulesOnACategory.MorphismsOverAnObject
open Stacks.Sites.OverModules (overRingPresheaf)
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange (baseChangeDataOfComm)
open Stacks.ModulesOnACategory.TerminalMorphismOfSites (morphismOfSites)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{max u v r w}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  (hO : ∀ (V : Cᵒᵖ) (x y : R.obj.obj V), x * y = y * x)

/-- For every object `U` of `C` and every K-flat complex `M^•` of `O(U)`-modules the canonical map
`M^• ⟶ RΓ((C/U)_τ, (M^• ⊗_{O(U)} O_U)^#)` is a quasi-isomorphism.

Here `M^•` is an object `P` of `D(O(U))`, and the canonical map is the unit
`P ⟶ RΓ(id_U, Lf_U^*P)` of the derived pullback along the morphism of sites
`(C/U, O_U) ⟶ (pt, O(U))`, followed by derived sections over the terminal object `id_U` of the
unit of the localized `ε_U`-adjunction. -/
def IsLocallyKFlatAcyclic : Prop :=
  ∀ U : C, ∀ P,
    IsIso ((morphismOfSites (overRingPresheaf R.obj U) (comm_overRingPresheaf R.obj U hO)
          (Over.mkIdTerminal (X := U))).adj.unit.app P ≫
      (RGamma.{w} (overRingPresheaf R.obj U) (Opposite.op (Over.mk (𝟙 U)))).map
        ((derivedEpsilonAdjunction.{w} (overRingSheaf R U)).unit.app
          ((morphismOfSites (overRingPresheaf R.obj U) (comm_overRingPresheaf R.obj U hO)
            (Over.mkIdTerminal (X := U))).Lpullback.obj P)))

/-- If the unit of an adjunction becomes invertible under a functor `G` at the source of an
isomorphism `c`, then it does so at the target. -/
private theorem isIso_map_unit_of_iso {D E F : Type*} [Category D] [Category E] [Category F]
    {Fl : D ⥤ E} {Fr : E ⥤ D} (adj : Fl ⊣ Fr) (G : D ⥤ F)
    {X Y : D} (c : X ⟶ Y) (hc : IsIso c) (he : IsIso (G.map (adj.unit.app X))) :
    IsIso (G.map (adj.unit.app Y)) := by
  have := hc
  have := he
  have : IsIso (G.map c ≫ G.map (adj.unit.app Y)) := by
    rw [← G.map_comp, ← adj.unit_naturality c, G.map_comp]
    infer_instance
  exact IsIso.of_isIso_comp_left (G.map c) (G.map (adj.unit.app Y))

/-- Under `IsLocallyKFlatAcyclic`, for every cartesian `M` and every object `U` of `C` the unit
`M|_U ⟶ Rε_{U*}(ε_U^*(M|_U))` of the localized site becomes invertible on derived sections over
the terminal object `id_U` of `C/U`. -/
theorem isIso_rGamma_unit_derivedRestriction (h2 : IsLocallyKFlatAcyclic.{w} R hO)
    (M : DMod.{w} R.obj) (hM : IsQC.{w} (baseChangeDataOfComm.{r, v, u, w} R.obj hO) M) (U : C) :
    IsIso ((RGamma.{w} (overRingPresheaf R.obj U) (Opposite.op (Over.mk (𝟙 U)))).map
      ((derivedEpsilonAdjunction.{w} (overRingSheaf R U)).unit.app
        ((derivedRestriction.{w} R.obj U).obj M))) := by
  set mos := morphismOfSites (overRingPresheaf R.obj U) (comm_overRingPresheaf R.obj U hO)
    (Over.mkIdTerminal (X := U)) with hmos
  have hK : IsQC.{w} (baseChangeDataOfComm (overRingPresheaf R.obj U)
      (comm_overRingPresheaf R.obj U hO)) ((derivedRestriction.{w} R.obj U).obj M) :=
    isQC_derivedRestriction.{w} R.obj U (baseChangeDataOfComm.{r, v, u, w} R.obj hO) _ M hM
  have hunit : IsIso (mos.adj.unit.app ((RGamma.{w} (overRingPresheaf R.obj U)
      (Opposite.op (Over.mk (𝟙 U)))).obj ((derivedRestriction.{w} R.obj U).obj M))) :=
    main_unit_isIso.{w} _ mos _
  have h2' : IsIso (mos.adj.unit.app ((RGamma.{w} (overRingPresheaf R.obj U)
        (Opposite.op (Over.mk (𝟙 U)))).obj ((derivedRestriction.{w} R.obj U).obj M)) ≫
      (RGamma.{w} (overRingPresheaf R.obj U) (Opposite.op (Over.mk (𝟙 U)))).map
        ((derivedEpsilonAdjunction.{w} (overRingSheaf R U)).unit.app
          ((RGamma.{w} (overRingPresheaf R.obj U) (Opposite.op (Over.mk (𝟙 U))) ⋙
            mos.Lpullback).obj ((derivedRestriction.{w} R.obj U).obj M)))) :=
    h2 U _
  exact isIso_map_unit_of_iso (derivedEpsilonAdjunction.{w} (overRingSheaf R U))
    (RGamma.{w} (overRingPresheaf R.obj U) (Opposite.op (Over.mk (𝟙 U))))
    (mos.adj.counit.app ((derivedRestriction.{w} R.obj U).obj M))
    (main_counit_isIso.{w} _ mos _ hK)
    (IsIso.of_isIso_comp_left (mos.adj.unit.app _) _)

end HypothesisTwo

end Stacks.ModulesOnACategory.ChaoticComparison

end
