module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DiagonalSectionClasses
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinProjectionFormula
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.PullbackHgroupRetraction
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.PullbackHgroupDeRham
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinCohomologyDeRhamKoszul
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeCohomology.CanonicalCupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.CanonicalPairingLaws
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.GradedCommutativity
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModulePullbackMap

/-!
# The Gysin maps of a closed immersion on ambient classes

Let `π : X ⟶ S` be smooth and `i : Z ⟶ X` a Koszul regular closed immersion of finite
presentation with conormal sheaf finite locally free of rank `c`. The Gysin maps
`γ^{p,q} : H^q(X, i_*Ω^p_{Z/S}) ⟶ H^{q+c}(X, Ω^{p+c}_{X/S})` of [Stacks, Tag 0G8A] are defined on
the cohomology of `i_*Ω^p_{Z/S}` on `X`. This file records how they act on the classes the proof of
[Stacks, Tag 0G8J] feeds them: restrictions `α|_Z` of classes `α` on `X`, read on `X` through the
restriction of forms `Ω^p_{X/S} ⟶ i_*Ω^p_{Z/S}`.

## Main results

* `Stacks.DeRham.CohomologicalGysin.abelianHgroupMap_forgetModules_map`: the abelian action of the
  underlying map of a morphism of modules is the map it induces on cohomology.
* `Stacks.DeRham.CohomologicalGysin.gysinCohomologyMap_formRestriction`: **[Stacks, Tag 0G8C] on
  ambient classes**, `γ^{p,q}(α|_Z) = (-1)^{qc} α ∪ γ^{0,0}(1)` with `α|_Z` the image of `α` in
  `H^q(X, i_*Ω^p_{Z/S})` and `γ^{0,0}(1)` the class `gysinUnitClass`.
* `Stacks.DeRham.CohomologicalGysin.formsBaseChangeHom_eq_formRestriction`: for a morphism
  `i : X ⟶ W` over `S`, the canonical map `Ω^p_{W/S} ⟶ i_*Ω^p_{X/S}` of [Stacks, Tag 01F9] is the
  restriction of forms.
* `Stacks.DeRham.CohomologicalGysin.pullbackHgroup_formsBaseChangeHom_self`: so the pullback map
  along `i` is the map induced by the restriction of forms followed by the pullback map at the
  identity of `i_*Ω^p_{X/S}`, an isomorphism when `i` is a closed immersion.
* `Stacks.DeRham.CohomologicalGysin.formRestriction_comp_retraction_eq`: the **ambient copy** of a
  class of `H^n(X, Ω^p_{X/S})` — pulled back along a retraction `G` of `i` and restricted to
  `i_*Ω^p_{X/S}` — does not depend on the retraction.
* `Stacks.DeRham.CohomologicalGysin.formRestriction_eq_of_pullbackHgroup`: the restriction of a
  class of `W` whose pullback along `i` is `θ` is the ambient copy of `θ`.
* `Stacks.DeRham.CohomologicalGysin.ambientCopy_comm_deRham`: the ambient copies commute with the
  abelian actions of the de Rham differentials.
* `Stacks.DeRham.CohomologicalGysin.hodgeCupStructureSheaf_swap`: the cup product of
  [Stacks, Tag 0G8C] on `Hᵈ(X, Ωᵈ) × Hᵈ(X, Ωᵈ)` is symmetric, the sign of Cohomology, Lemma 0FP5
  cancelling the sign of the wedge product of two `d`-forms.

## Implementation notes

The cup product of [Stacks, Tag 0G8C] is built in the standard model of the derived category;
the file opens the scope `Stacks.StandardDerivedModel`.

No class is transported along the equation `i ≫ π_W = f` of structure morphisms: an `eqToHom`
along it makes the kernel try to decide that equation by unfolding the sheaves of forms.
The statements for a general `f` take the equation as a hypothesis `hf` and the proofs `subst`
it, so that `f` becomes `i ≫ π_W`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction Stacks.Gysin Stacks.DeRham.GysinCohomologyBaseChange
open AlgebraicGeometry.Scheme.Hom Stacks.AlgebraicGeometry.ConormalEquations
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.DeRham.GysinCupHodge Stacks.DeRham.GysinCohomologyDeRham
open Stacks.DeRham.GysinCohomologyDeRhamKoszul
open Stacks.Cohomology.UnderlyingAbelianSheaf
open scoped Stacks.StandardDerivedModel

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.DeRham.CohomologicalGysin

/-! ### The abelian action of a module map -/

/-- **The abelian action of the underlying map of a morphism of modules is the map it induces on
cohomology.** -/
theorem abelianHgroupMap_forgetModules_map (X : RingedSpace.{u, u}) (a m : ℤ) (n : ℕ)
    (hn : m - a = n) {A B : RModules X} (φ : A ⟶ B) :
    abelianHgroupMap X a m n hn ((forgetModules X).map φ) =
      (Hfunctor (structureSheafRing X) ⊤ n).map φ := by
  unfold abelianHgroupMap
  rw [abelianDerivedMap_map, cohomologyDerivedSingleIso_hom_naturality, Iso.inv_hom_id_assoc]

/-- Cancelling an isomorphism inside a composite, at variables. -/
private lemma inv_hom_cancel_chase {C : Type*} [Category* C] {a x y z : C} (g : a ⟶ y)
    (e : x ≅ y) (k : y ⟶ z) : (g ≫ e.inv) ≫ e.hom ≫ k = g ≫ k := by
  simp

/-- Applying a functor to a composite and reassociating, at variables. -/
private lemma map_comp_assoc_chase {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {x y z : C} {t : D} (a : x ⟶ y) (b : y ⟶ z) (e : F.obj z ⟶ t) :
    F.map (a ≫ b) ≫ e = F.map a ≫ F.map b ≫ e := by
  rw [F.map_comp, Category.assoc]

/-- An isomorphism of abelian groups followed by its inverse, on an element, at variables. -/
private lemma inv_hom_apply_chase {A B : AddCommGrpCat.{u}} (φ : A ⟶ B) [IsIso φ] (x : A) :
    (inv φ).hom (φ.hom x) = x := by
  rw [← AddCommGrpCat.comp_apply, IsIso.hom_inv_id, AddCommGrpCat.id_apply]

/-- Pasting two commuting squares, at variables. -/
private lemma square_paste_chase {C : Type*} [Category* C] {a b c a' b' c' : C} (P : a ⟶ b)
    (H : b ⟶ c) (D : a ⟶ a') (Dw : b ⟶ b') (D' : c ⟶ c') (P' : a' ⟶ b') (H' : b' ⟶ c')
    (hR : H ≫ D' = Dw ≫ H') (hP : P ≫ Dw = D ≫ P') : (P ≫ H) ≫ D' = D ≫ P' ≫ H' := by
  rw [Category.assoc, hR, ← Category.assoc, hP, Category.assoc]

section Cup

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [LocallyOfFinitePresentation i]
  (π : X ⟶ S) [Smooth π]

/-- The Gysin map of [Stacks, Tag 0G8A] at `p = q = 0` sends the class of `1` to
`gysinUnitClass`. -/
theorem gysinHodgeFormsMapOfConormalRank_oneFormCohomologyClass
    (hK : IsKoszulRegularImmersion i) {c : ℕ} (hE : ConormalRank i c) :
    (gysinHodgeFormsMapOfConormalRank i π 0 hE
        (supportVanishing_relativeDifferentialForms i π hK c hE 0) 0).hom
      (Stacks.DeRham.GysinProjection.oneFormCohomologyClass (i ≫ π)) =
    gysinUnitClass i π hK hE := by
  rw [Stacks.DeRham.GysinCohomologyDeRhamConormal.gysinHodgeFormsMapOfConormalRank_eq]
  refine (congrArg (gysinCohomologyMap (Set.range i.base) (isClosed_range_base i) c
    (pushforwardRelativeForms i π ((0 : ℕ) : ℤ))
    (relativeDifferentialForms π (((0 : ℕ) : ℤ) + (c : ℤ)))
    (supportVanishing_relativeDifferentialForms i π hK c hE 0)
    (conormalGysinHom i π 0 hE ≫ (conormalGysinTargetIso i π c 0).hom) 0).hom
    (cohomologyPushforwardIso_oneFormCohomologyClass i π)).trans ?_
  rfl

/-- **[Stacks, Tag 0G8C] on ambient classes.** For `α ∈ H^q(X, Ω^p_{X/S})` with image
`α|_Z ∈ H^q(X, i_*Ω^p_{Z/S})` under the restriction of forms, the Gysin map of
[Stacks, Tag 0G8A] gives `γ^{p,q}(α|_Z) = (-1)^{qc} α ∪ γ^{0,0}(1)`, the cup product being that
of `gysinHodgeFormsMapOfConormalRank_hodgeRestriction` and `γ^{0,0}(1)` the class
`gysinUnitClass`. -/
theorem gysinCohomologyMap_formRestriction (hK : IsKoszulRegularImmersion i) {c : ℕ}
    (hE : ConormalRank i c) (p q : ℕ)
    (α : Hgroup X.ringCatSheaf ⊤ q (relativeDifferentialForms π (p : ℤ))) :
    (hgroupModuleShiftIso (X := X.toRingedSpace) (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))
        0 (q + c) ((q : ℤ) + (c : ℤ)) (by push_cast; ring)).hom
      ((gysinCohomologyMap (Set.range i.base) (isClosed_range_base i) c
          (pushforwardRelativeForms i π (p : ℤ))
          (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))
          (supportVanishing_relativeDifferentialForms i π hK c hE p)
          (conormalGysinHom i π p hE ≫ (conormalGysinTargetIso i π c p).hom) q).hom
        ((Hfunctor X.ringCatSheaf ⊤ q).map (formRestriction i π (p : ℤ)) α)) =
    ((q : ℤ) * (c : ℤ)).negOnePow •
      (hodgeCupStructureSheaf π p c q c).hom
        ((hgroupModuleShiftIso (X := X.toRingedSpace) (relativeDifferentialForms π (p : ℤ)) 0 q q
          (by simp)).hom α ⊗ₜ
        (hgroupModuleShiftIso (X := X.toRingedSpace) (relativeDifferentialForms π (c : ℤ)) 0
          (0 + c) c (by push_cast; ring)).hom
          ((Hfunctor X.ringCatSheaf ⊤ (0 + c)).map
            (eqToHom (congrArg (relativeDifferentialForms π) (by push_cast; ring)))
            (gysinUnitClass i π hK hE))) := by
  have key : hodgeRestriction i π p q ≫ gysinHodgeFormsMapOfConormalRank i π p hE
        (supportVanishing_relativeDifferentialForms i π hK c hE p) q =
      (Hfunctor X.ringCatSheaf ⊤ q).map (formRestriction i π (p : ℤ)) ≫
        gysinCohomologyMap (Set.range i.base) (isClosed_range_base i) c
          (pushforwardRelativeForms i π (p : ℤ))
          (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))
          (supportVanishing_relativeDifferentialForms i π hK c hE p)
          (conormalGysinHom i π p hE ≫ (conormalGysinTargetIso i π c p).hom) q := by
    rw [Stacks.DeRham.GysinCohomologyDeRhamConormal.gysinHodgeFormsMapOfConormalRank_eq]
    unfold hodgeRestriction
    exact inv_hom_cancel_chase _ _ _
  have h := gysinHodgeFormsMapOfConormalRank_hodgeRestriction i π hE hK p q α
  rw [gysinHodgeFormsMapOfConormalRank_oneFormCohomologyClass i π hK hE] at h
  refine Eq.trans ?_ h
  exact congrArg _ (congrArg (fun φ => φ.hom α) key).symm

/-- The Gysin map `γ^{p,q} : H^q(X, i_*Ω^p_{Z/S}) ⟶ H^{q+c}(X, Ω^{p+c}_{X/S})` of
[Stacks, Tag 0G8A], on the cohomology of `i_*Ω^p_{Z/S}` on `X`: the map of
`gysinCohomologyMap_formRestriction` and of [Stacks, Tag 0G8B]
(`Stacks.DeRham.GysinCohomologyDeRhamKoszul.koszulGysinCohomologyMap_comm_deRham`). -/
abbrev formsGysinMap (hK : IsKoszulRegularImmersion i) {c : ℕ} (hE : ConormalRank i c) (p q : ℕ) :=
  gysinCohomologyMap (Set.range i.base) (isClosed_range_base i) c
    (pushforwardRelativeForms i π (p : ℤ)) (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))
    (supportVanishing_relativeDifferentialForms i π hK c hE p)
    (conormalGysinHom i π p hE ≫ (conormalGysinTargetIso i π c p).hom) q

end Cup

/-! ### Pulling back along a closed immersion over the base -/

/-- **The pullback map at a factored `G`-map**: if `φ₁ = α ≫ φ₂`, then the pullback map of
[Stacks, Tag 01F9] at `φ₁` is the map induced by `α` followed by the pullback map at `φ₂`. -/
theorem pullbackHgroup_eq_map_comp_of_eq {X X' : RingedSpace.{u, u}} {G : X' ⟶ X}
    (P : CohomologyPullbackComparison G) (a m : ℤ) (n : ℕ) (hn : m - a = n)
    {M₁ M₂ : RModules X} {M' : RModules X'} (α : M₁ ⟶ M₂)
    (φ₁ : M₁ ⟶ (modulePushforward G).obj M') (φ₂ : M₂ ⟶ (modulePushforward G).obj M')
    (h : φ₁ = α ≫ φ₂) :
    pullbackHgroup P a m n hn φ₁ =
      (Hfunctor (structureSheafRing X) ⊤ n).map α ≫ pullbackHgroup P a m n hn φ₂ := by
  subst h
  rw [pullbackHgroup_eq_map_comp P a m n hn (α ≫ φ₂), pullbackHgroup_eq_map_comp P a m n hn φ₂,
    Functor.map_comp, Category.assoc]

section Ambient

variable {X W S : Scheme.{u}} (i : X ⟶ W) (πW : W ⟶ S)

/-- The restriction of forms `Ω^p_{W/S} ⟶ i_*Ω^p_{X/S}` along `i ≫ π_W`, as a morphism of
`𝒪_W`-modules into the direct image along the morphism of ringed spaces underlying `i`. -/
def formRestrictionModules (p : ℤ) :
    (relativeDifferentialForms πW p : RModules W.toRingedSpace) ⟶
      (modulePushforward i.toLRSHom.toShHom).obj (relativeDifferentialForms (i ≫ πW) p) :=
  formRestriction i πW p

/-- **The canonical map of forms along `i` is the restriction of forms**: for `i : X ⟶ W` over
`S`, with `X` over `S` through `i ≫ π_W`, the map `Ω^p_{W/S} ⟶ i_*Ω^p_{X/S}` of
[Stacks, Tag 01F9] is the restriction of forms. -/
theorem formsBaseChangeHom_eq_formRestriction (p : ℕ) :
    (formsBaseChangeHom i πW (i ≫ πW) (𝟙 S) (Category.comp_id _).symm (p : ℤ) :
      (relativeDifferentialForms πW (p : ℤ) : RModules W.toRingedSpace) ⟶
        (modulePushforward i.toLRSHom.toShHom).obj (relativeDifferentialForms (i ≫ πW) (p : ℤ))) =
      formRestrictionModules i πW (p : ℤ) ≫ 𝟙 _ :=
  (((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).homEquiv_unit _ _ _).trans
    (Stacks.DeRhamBaseChange.formsAdjoint_eq i (i ≫ πW) πW (𝟙 S)
      (Category.comp_id _).symm p).symm).trans (Category.comp_id _).symm

/-- **The pullback map along `i` is the map induced by the restriction of forms, followed by the
pullback map at the identity of `i_*Ω^p_{X/S}`.** -/
theorem pullbackHgroup_formsBaseChangeHom_self (a m : ℤ) (n : ℕ) (hn : m - a = n) (p : ℕ) :
    pullbackHgroup (CohomologyPullbackComparison.canonical i.toLRSHom.toShHom) a m n hn
        (formsBaseChangeHom i πW (i ≫ πW) (𝟙 S) (Category.comp_id _).symm (p : ℤ)) =
      (Hfunctor (structureSheafRing W.toRingedSpace) ⊤ n).map
          (formRestrictionModules i πW (p : ℤ)) ≫
        pullbackHgroup (CohomologyPullbackComparison.canonical i.toLRSHom.toShHom) a m n hn
          (𝟙 ((modulePushforward i.toLRSHom.toShHom).obj
            (relativeDifferentialForms (i ≫ πW) (p : ℤ)))) :=
  pullbackHgroup_eq_map_comp_of_eq _ a m n hn _ _ _ (formsBaseChangeHom_eq_formRestriction i πW p)

variable (f : X ⟶ S) (G : W ⟶ X) (wG : G ≫ f = πW ≫ 𝟙 S) (hi : i ≫ G = 𝟙 X)

include hi in
/-- Pulling back along a retraction `G` of the closed immersion `i` and restricting to
`i_*Ω^p_{X/S}` is the inverse of the pullback map along `i` at the identity of
`i_*Ω^p_{X/S}`, for `f = i ≫ π_W`. -/
theorem formRestriction_comp_retraction_self [IsClosedImmersion i] (wG : G ≫ (i ≫ πW) = πW ≫ 𝟙 S)
    (a m : ℤ) (n : ℕ) (hn : m - a = n) (p : ℕ) :
    haveI : Fact (Topology.IsClosedEmbedding i.toLRSHom.toShHom.hom.base) := ⟨i.isClosedEmbedding⟩
    haveI := isIso_pullbackHgroup_canonical_id i.toLRSHom.toShHom a m n hn
      (relativeDifferentialForms (i ≫ πW) (p : ℤ))
    pullbackHgroup (CohomologyPullbackComparison.canonical G.toLRSHom.toShHom) a m n hn
        (formsBaseChangeHom G (i ≫ πW) πW (𝟙 S) wG (p : ℤ)) ≫
      (Hfunctor (structureSheafRing W.toRingedSpace) ⊤ n).map
          (formRestrictionModules i πW (p : ℤ)) =
    inv (pullbackHgroup (CohomologyPullbackComparison.canonical i.toLRSHom.toShHom) a m n hn
      (𝟙 ((modulePushforward i.toLRSHom.toShHom).obj
        (relativeDifferentialForms (i ≫ πW) (p : ℤ))))) := by
  have : Fact (Topology.IsClosedEmbedding i.toLRSHom.toShHom.hom.base) := ⟨i.isClosedEmbedding⟩
  have := isIso_pullbackHgroup_canonical_id i.toLRSHom.toShHom a m n hn
    (relativeDifferentialForms (i ≫ πW) (p : ℤ))
  refine IsIso.eq_inv_of_inv_hom_id ?_
  have h := pullbackHgroup_formsBaseChangeHom_retraction (i ≫ πW) G πW wG i
    (Category.comp_id _).symm hi a m n hn p
  rw [pullbackHgroup_formsBaseChangeHom_self i πW a m n hn p] at h
  simpa only [Category.assoc] using h

include hi in
/-- **The ambient copy of a class does not depend on the retraction**: for a closed immersion
`i : X ⟶ W` over `S` with two retractions `G`, `G'` over `S`, pulling a class of
`Hⁿ(X, Ω^p_{X/S})` back to `W` along either and restricting it to `i_*Ω^p_{X/S}` gives the same
class. -/
theorem formRestriction_comp_retraction_eq [IsClosedImmersion i] (hf : i ≫ πW = f)
    (G' : W ⟶ X) (wG' : G' ≫ f = πW ≫ 𝟙 S) (hi' : i ≫ G' = 𝟙 X)
    (a m : ℤ) (n : ℕ) (hn : m - a = n) (p : ℕ) :
    pullbackHgroup (CohomologyPullbackComparison.canonical G.toLRSHom.toShHom) a m n hn
        (formsBaseChangeHom G f πW (𝟙 S) wG (p : ℤ)) ≫
      (Hfunctor (structureSheafRing W.toRingedSpace) ⊤ n).map
          (formRestrictionModules i πW (p : ℤ)) =
    pullbackHgroup (CohomologyPullbackComparison.canonical G'.toLRSHom.toShHom) a m n hn
        (formsBaseChangeHom G' f πW (𝟙 S) wG' (p : ℤ)) ≫
      (Hfunctor (structureSheafRing W.toRingedSpace) ⊤ n).map
        (formRestrictionModules i πW (p : ℤ)) := by
  subst hf
  exact (formRestriction_comp_retraction_self i πW G hi wG a m n hn p).trans
    (formRestriction_comp_retraction_self i πW G' hi' wG' a m n hn p).symm

include hi in
/-- **The restriction of a class whose pullback is known**: if the pullback along the closed
immersion `i` of a class `η` of `Hⁿ(W, Ω^p_{W/S})` is `θ`, then the restriction of `η` to
`i_*Ω^p_{X/S}` is the ambient copy of `θ` along any retraction `G` of `i`. -/
theorem formRestriction_eq_of_pullbackHgroup [IsClosedImmersion i] (hf : i ≫ πW = f)
    (w : i ≫ πW = f ≫ 𝟙 S) (a m : ℤ) (n : ℕ) (hn : m - a = n) (p : ℕ)
    (η : Hgroup (structureSheafRing W.toRingedSpace) ⊤ n (relativeDifferentialForms πW (p : ℤ)))
    (θ : Hgroup (structureSheafRing X.toRingedSpace) ⊤ n (relativeDifferentialForms f (p : ℤ)))
    (h : (pullbackHgroup (CohomologyPullbackComparison.canonical i.toLRSHom.toShHom) a m n hn
      (formsBaseChangeHom i πW f (𝟙 S) w (p : ℤ))).hom η = θ) :
    ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ n).map
        (formRestrictionModules i πW (p : ℤ))).hom η =
      (pullbackHgroup (CohomologyPullbackComparison.canonical G.toLRSHom.toShHom) a m n hn
          (formsBaseChangeHom G f πW (𝟙 S) wG (p : ℤ)) ≫
        (Hfunctor (structureSheafRing W.toRingedSpace) ⊤ n).map
          (formRestrictionModules i πW (p : ℤ))).hom θ := by
  subst hf h
  have : Fact (Topology.IsClosedEmbedding i.toLRSHom.toShHom.hom.base) := ⟨i.isClosedEmbedding⟩
  have := isIso_pullbackHgroup_canonical_id i.toLRSHom.toShHom a m n hn
    (relativeDifferentialForms (i ≫ πW) (p : ℤ))
  rw [formRestriction_comp_retraction_self i πW G hi wG a m n hn p]
  have e := pullbackHgroup_formsBaseChangeHom_self i πW a m n hn p
  refine Eq.trans ?_ (congrArg (fun φ => (inv (pullbackHgroup
    (CohomologyPullbackComparison.canonical i.toLRSHom.toShHom) a m n hn
      (𝟙 ((modulePushforward i.toLRSHom.toShHom).obj
        (relativeDifferentialForms (i ≫ πW) (p : ℤ)))))).hom (φ.hom η)) e).symm
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
  exact (inv_hom_apply_chase _ _).symm

/-- **The ambient copies commute with the de Rham differentials**: pulling back along `G` and
restricting to `i_*Ω^•_{X/S}` intertwines the abelian actions of the de Rham differential of
`X/S` and of its direct image along `i`. -/
theorem ambientCopy_comm_deRham (a m : ℤ) (n : ℕ) (hn : m - a = n) (p : ℕ) :
    (pullbackHgroup (CohomologyPullbackComparison.canonical G.toLRSHom.toShHom) a m n hn
        (formsBaseChangeHom G f πW (𝟙 S) wG (p : ℤ)) ≫
      (Hfunctor (structureSheafRing W.toRingedSpace) ⊤ n).map
        (formRestrictionModules i πW (p : ℤ))) ≫
        abelianHgroupMap W.toRingedSpace a m n hn (pushforwardDeRhamDifferentialAbHom i πW p) =
      abelianHgroupMap X.toRingedSpace a m n hn (deRhamDifferentialAbHom f p) ≫
        pullbackHgroup (CohomologyPullbackComparison.canonical G.toLRSHom.toShHom) a m n hn
          (formsBaseChangeHom G f πW (𝟙 S) wG ((p + 1 : ℕ) : ℤ)) ≫
        (Hfunctor (structureSheafRing W.toRingedSpace) ⊤ n).map
          (formRestrictionModules i πW ((p + 1 : ℕ) : ℤ)) := by
  have hR : (Hfunctor (structureSheafRing W.toRingedSpace) ⊤ n).map
        (formRestrictionModules i πW (p : ℤ)) ≫
        abelianHgroupMap W.toRingedSpace a m n hn (pushforwardDeRhamDifferentialAbHom i πW p) =
      abelianHgroupMap W.toRingedSpace a m n hn (deRhamDifferentialAbHom πW p) ≫
        (Hfunctor (structureSheafRing W.toRingedSpace) ⊤ n).map
          (formRestrictionModules i πW ((p + 1 : ℕ) : ℤ)) := by
    refine (congrArg (· ≫ abelianHgroupMap W.toRingedSpace a m n hn
      (pushforwardDeRhamDifferentialAbHom i πW p)) (abelianHgroupMap_forgetModules_map
        W.toRingedSpace a m n hn (formRestrictionModules i πW (p : ℤ))).symm).trans ?_
    refine (abelianHgroupMap_comp _ _ _ _ _ _ _).symm.trans ?_
    refine (congrArg (abelianHgroupMap W.toRingedSpace a m n hn)
      (formRestriction_comm_deRhamDifferentialAbHom i πW p)).trans ?_
    refine (abelianHgroupMap_comp _ _ _ _ _ _ _).trans ?_
    exact congrArg (_ ≫ ·) (abelianHgroupMap_forgetModules_map W.toRingedSpace a m n hn
      (formRestrictionModules i πW ((p + 1 : ℕ) : ℤ)))
  exact square_paste_chase _ _ _ _ _ _ _ hR
    (pullbackHgroup_formsBaseChangeHom_comm_deRham f G πW wG a m n hn p)

end Ambient


/-! ### The cup product on `Hᵈ(X, Ωᵈ) × Hᵈ(X, Ωᵈ)` is symmetric -/

section Swap

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens
attribute [local instance] _root_.SheafOfModules.monoidalCategorySheafTensor
  _root_.SheafOfModules.symmetricCategorySheafTensor
  _root_.SheafOfModules.monoidalPreadditiveSheafTensor
  _root_.SheafOfModules.monoidalClosedSheafTensor
  _root_.SheafOfModules.preservesColimit_tensorRight_sheafTensor
  Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexMonoidalCategory
  Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexSymmetricCategory

open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule cohomologyCast)
open AlgebraicGeometry.SheafOfModules (moduleDerived canonicalPairingModule)

/-- The multiplication of complexes in degree `0` of `GysinCupHodge` is the one of
`AlgebraicGeometry.SheafOfModules.singleMultiplication`. -/
theorem singleTensorMult_zero_eq {Y : RingedSpace.{u, u}}
    {F G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.sheaf)}
    (μ : ((sheafTensor.{u, u, u, u, u} Y.sheaf).obj F).obj G ⟶ H) :
    singleTensorMult (X := Y) μ 0 0 0 rfl =
      AlgebraicGeometry.SheafOfModules.singleMultiplication (A := Y.sheaf) μ := by
  refine HomologicalComplex.to_single_hom_ext ?_
  refine HomologicalComplex.mapBifunctor.hom_ext (fun a b h => ?_)
  have hab : a = 0 ∧ b = 0 := by
    change a + b = 0 at h
    omega
  obtain ⟨rfl, rfl⟩ := hab
  rw [ι_singleTensorMult_f μ 0 0 0 rfl h]
  change _ = HomologicalComplex.ιMapBifunctor _ _ _ _ 0 0 0 h ≫
    (HomologicalComplex.mkHomToSingle
      (AlgebraicGeometry.SheafOfModules.singleMultiplicationX (A := Y.sheaf) μ) _).f 0
  rw [HomologicalComplex.mkHomToSingle_f,
    AlgebraicGeometry.SheafOfModules.singleMultiplicationX,
    HomologicalComplex.ι_mapBifunctorDesc_assoc, ← Category.assoc, ← Category.assoc,
    ← Category.assoc, NatTrans.naturality]
  rfl

variable {X S : Scheme.{u}} (π : X ⟶ S)

/-- **The wedge product of two `d`-forms is `(-1)^{d·d}` times the wedge product in the other
order**, on local sections, at the multiplication of `hodgeCupStructureSheaf`. -/
theorem mulSheaf_relativeDifferentialForms_swap (d : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (x y : (relativeDifferentialForms π (d : ℤ)).val.obj U) :
    (SheafOfModules.GradedAlgebra.mulSheaf (relativeDifferentialFormsAlgebra π) (d : ℤ)
        (d : ℤ)).val.app U ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)).unit.app
          (PresheafOfModules.tensorObj (relativeDifferentialForms π (d : ℤ)).val
            (relativeDifferentialForms π (d : ℤ)).val) |>.app U (x ⊗ₜ y)) =
      ((-1 : ℤ) ^ (d * d) • SheafOfModules.GradedAlgebra.mulSheaf
        (relativeDifferentialFormsAlgebra π) (d : ℤ) (d : ℤ)).val.app U
        ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)).unit.app
          (PresheafOfModules.tensorObj (relativeDifferentialForms π (d : ℤ)).val
            (relativeDifferentialForms π (d : ℤ)).val) |>.app U (y ⊗ₜ x)) := by
  refine (SheafOfModules.GradedAlgebra.mulSheaf_unit (relativeDifferentialFormsAlgebra π)
    (d : ℤ) (d : ℤ) U x y).trans ?_
  refine (AlgebraicGeometry.SheafOfModules.formProduct_comm (deRhamAlgebras π) d d U x y).trans ?_
  refine Eq.trans ?_ (_root_.SheafOfModules.zsmul_val_app _ _ U _).symm
  exact congrArg ((-1 : ℤ) ^ (d * d) • ·)
    (SheafOfModules.GradedAlgebra.mulSheaf_unit (relativeDifferentialFormsAlgebra π)
      (d : ℤ) (d : ℤ) U y x).symm

/-- **The cup product of `hodgeCupStructureSheaf` on `Hᵈ(X, Ωᵈ) × Hᵈ(X, Ωᵈ)` is symmetric**: the
sign `(-1)^{d·d}` of graded commutativity of the cup product (Cohomology, Lemma 0FP5) cancels
against the sign `(-1)^{d·d}` of the wedge product of two `d`-forms. -/
theorem hodgeCupStructureSheaf_swap (d : ℕ)
    (x y : cohomologyModule (moduleDerived (A := X.sheaf)
      (singleNat (relativeDifferentialForms π (d : ℤ)) 0)) (d : ℤ)) :
    (hodgeCupStructureSheaf π d d d d).hom (x ⊗ₜ y) =
      (hodgeCupStructureSheaf π d d d d).hom (y ⊗ₜ x) := by
  have hcv := AlgebraicGeometry.SheafOfModules.singleMultiplication_comm_value
    (A := X.sheaf) _ ((-1 : ℤ) ^ (d * d) • SheafOfModules.GradedAlgebra.mulSheaf
      (relativeDifferentialFormsAlgebra π) (d : ℤ) (d : ℤ))
    (mulSheaf_relativeDifferentialForms_swap π d)
  have hcx := AlgebraicGeometry.SheafOfModules.multiplicationInt_braiding _ _ hcv
  have he := AlgebraicGeometry.SheafOfModules.canonicalPairingModule_comm _ _ hcx (d : ℤ) (d : ℤ)
    x y
  rw [AlgebraicGeometry.SheafOfModules.singleMultiplication_zsmul,
    AlgebraicGeometry.SheafOfModules.canonicalPairingModule_zsmul] at he
  have hs : (((d : ℤ) * (d : ℤ)).negOnePow : ℤ) * (-1 : ℤ) ^ (d * d) = 1 := by
    rw [show ((d : ℤ) * (d : ℤ)) = ((d * d : ℕ) : ℤ) by push_cast; ring,
      Int.coe_negOnePow_natCast, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  unfold hodgeCupStructureSheaf
  rw [singleTensorMult_zero_eq]
  refine he.trans ?_
  rw [ModuleCat.hom_zsmul, LinearMap.smul_apply, map_zsmul, smul_smul, hs, one_smul]
  rfl

/-- **The cup product on `Hᵉ(X, Ωᵉ) × Hᵉ(X, Ωᵉ)` is symmetric, in the spelling of
[Stacks, Tag 0G8C]**: the second factor read through the identification of the degree of the
forms, for a degree `e` equal to `c` (as `0 + c` and `c`). -/
theorem hodgeCupStructureSheaf_swap_shift (e c : ℕ) (he : e = c) (h : (e : ℤ) = (c : ℤ))
    (x y : Hgroup X.ringCatSheaf ⊤ e (relativeDifferentialForms π (e : ℤ))) :
    (hodgeCupStructureSheaf π e c e c).hom
        ((hgroupModuleShiftIso (X := X.toRingedSpace) (relativeDifferentialForms π (e : ℤ)) 0 e e
          (by simp)).hom x ⊗ₜ
        (hgroupModuleShiftIso (X := X.toRingedSpace) (relativeDifferentialForms π (c : ℤ)) 0 e c
          (by omega)).hom
          ((Hfunctor X.ringCatSheaf ⊤ e).map
            (eqToHom (congrArg (relativeDifferentialForms π) h)) y)) =
      (hodgeCupStructureSheaf π e c e c).hom
        ((hgroupModuleShiftIso (X := X.toRingedSpace) (relativeDifferentialForms π (e : ℤ)) 0 e e
          (by simp)).hom y ⊗ₜ
        (hgroupModuleShiftIso (X := X.toRingedSpace) (relativeDifferentialForms π (c : ℤ)) 0 e c
          (by omega)).hom
          ((Hfunctor X.ringCatSheaf ⊤ e).map
            (eqToHom (congrArg (relativeDifferentialForms π) h)) x)) := by
  subst he
  have hid : ∀ z, ((Hfunctor X.ringCatSheaf ⊤ e).map
      (eqToHom (congrArg (relativeDifferentialForms π) h))).hom z = z := fun z =>
    congrArg (fun φ => φ.hom z) ((Hfunctor X.ringCatSheaf ⊤ e).map_id _)
  rw [hid, hid]
  exact hodgeCupStructureSheaf_swap π e _ _

end Swap


/-! ### The Gysin maps of the diagonal and of the constant sections on `ξ` -/

section DiagonalTop

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

/-- Rewriting one factor of a cup product, swapping the factors and recognising the other side,
at variables. -/
private lemma swap_chase {M N T : Type*} {L : T} (sm : T → T) (cupS : M → M → T) (G : N → T)
    {b b' c : M} {u v : N} (hL : L = sm (cupS b c)) (hb : b = b')
    (hs : cupS b' c = cupS c b') (huv : u = v) (hR : G u = sm (cupS c b')) : L = G v := by
  rw [hL, hb, hs, ← hR, huv]

/-- The Gysin maps of two Koszul regular closed immersions `i`, `j` of conormal rank `n` agree at
the ambient copies of a class `ξ` along `Pu` and `Pv`, when `Pu ξ` is the Gysin class of `j`
and the restriction of the Gysin class of `i` to `j` is the ambient copy `Pv ξ`: both are `±` the
cup product of the two Gysin classes, which is symmetric. -/
private theorem formsGysinMap_eq_of_swap {Z Z' W S : Scheme.{u}} (π : W ⟶ S) [Smooth π] (n : ℕ)
    (i : Z ⟶ W) [IsClosedImmersion i] [LocallyOfFinitePresentation i]
    (j : Z' ⟶ W) [IsClosedImmersion j] [LocallyOfFinitePresentation j]
    (hKi : IsKoszulRegularImmersion i) (hEi : ConormalRank i n)
    (hKj : IsKoszulRegularImmersion j) (hEj : ConormalRank j n) {H : AddCommGrpCat.{u}} (ξ : H)
    (Pu Pv : H ⟶ Hgroup (structureSheafRing W.toRingedSpace) ⊤ (0 + n)
      (relativeDifferentialForms π (((0 : ℕ) : ℤ) + (n : ℤ))))
    (hu : Pu.hom ξ = gysinUnitClass j π hKj hEj)
    (hres : ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ (0 + n)).map
        (formRestrictionModules j π ((0 + n : ℕ) : ℤ))).hom (gysinUnitClass i π hKi hEi) =
      (Pv ≫ (Hfunctor (structureSheafRing W.toRingedSpace) ⊤ (0 + n)).map
        (formRestrictionModules j π ((0 + n : ℕ) : ℤ))).hom ξ) :
    (formsGysinMap i π hKi hEi (0 + n) (0 + n)).hom
      ((Pu ≫ (Hfunctor (structureSheafRing W.toRingedSpace) ⊤ (0 + n)).map
        (formRestrictionModules i π ((0 + n : ℕ) : ℤ))).hom ξ) =
    (formsGysinMap j π hKj hEj (0 + n) (0 + n)).hom
      ((Pv ≫ (Hfunctor (structureSheafRing W.toRingedSpace) ⊤ (0 + n)).map
        (formRestrictionModules j π ((0 + n : ℕ) : ℤ))).hom ξ) := by
  have hΔ := gysinCohomologyMap_formRestriction i π hKi hEi (0 + n) (0 + n) (Pu.hom ξ)
  have hS := gysinCohomologyMap_formRestriction j π hKj hEj (0 + n) (0 + n)
    (gysinUnitClass i π hKi hEi)
  refine (ConcreteCategory.bijective_of_isIso (hgroupModuleShiftIso
    (X := W.toRingedSpace)
    (relativeDifferentialForms π (((0 + n : ℕ) : ℤ) + (n : ℤ))) 0
    ((0 + n) + n) (((0 + n : ℕ) : ℤ) + (n : ℤ)) (by push_cast; ring)).hom).1 ?_
  exact swap_chase (fun t => (((0 + n : ℕ) : ℤ) * (n : ℤ)).negOnePow • t)
    (fun x y => (hodgeCupStructureSheaf π (0 + n) n ((0 + n : ℕ) : ℤ) (n : ℤ)).hom
      ((hgroupModuleShiftIso (X := W.toRingedSpace)
        (relativeDifferentialForms π ((0 + n : ℕ) : ℤ)) 0 (0 + n)
          ((0 + n : ℕ) : ℤ) (by simp)).hom x ⊗ₜ
        (hgroupModuleShiftIso (X := W.toRingedSpace)
          (relativeDifferentialForms π (n : ℤ)) 0 (0 + n) n
          (by push_cast; ring)).hom
          ((Hfunctor W.ringCatSheaf ⊤ (0 + n)).map
            (eqToHom (congrArg (relativeDifferentialForms π)
              (by push_cast; ring))) y)))
    (fun z => (hgroupModuleShiftIso (X := W.toRingedSpace)
      (relativeDifferentialForms π (((0 + n : ℕ) : ℤ) + (n : ℤ))) 0
      ((0 + n) + n) (((0 + n : ℕ) : ℤ) + (n : ℤ)) (by push_cast; ring)).hom
      ((formsGysinMap j π hKj hEj (0 + n) (0 + n)).hom z))
    hΔ hu (hodgeCupStructureSheaf_swap_shift π (0 + n) n (Nat.zero_add n)
      (by push_cast; ring) _ _) hres hS

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
  (n : ℕ) [SmoothOfRelativeDimension n f] (σ : Spec (.of A) ⟶ X) [IsClosedImmersion σ]
  [LocallyOfFinitePresentation σ] [Smooth (σ ≫ f)] [FormallyUnramified (σ ≫ f)]

include σ in
/-- **The Gysin maps of the diagonal and of `(σ ∘ f, id)` agree on `ξ`** (the case `x = ξ` of
"`γ^{n,n}(x) = x ⊗ ξ`" in the proof of [Stacks, Tag 0G8J]). Let `ξ = γ^{0,0}(1)` be the Gysin
class of the section, `W = X ×_A X` and `j = (σ ∘ f, id)`. The Gysin map `γ^{n,n}_Δ` of the
diagonal at the ambient copy `p₁^*ξ|_Δ` of `ξ` equals the Gysin map `γ^{n,n}_j` at the ambient
copy `p₂^*ξ|_j`: by [Stacks, Tag 0G8C] both are `±` a cup product of `p₁^*ξ = γ_j(1)` and
`η = γ_Δ(1)` (`j^*η = ξ`), and the cup product on `Hⁿ(W, Ωⁿ) × Hⁿ(W, Ωⁿ)` is symmetric. -/
theorem formsGysinMap_diagonal_eq_sectionFst (hσ : σ ≫ f = 𝟙 _) :
    haveI : LocallyOfFinitePresentation (pullback.diagonal f) := by
      have : LocallyOfFinitePresentation (pullback.diagonal f ≫ pullback.fst f f) := by
        rw [pullback.diagonal_fst]; infer_instance
      exact locallyOfFinitePresentation_of_comp _ (pullback.fst f f)
    haveI := smoothOfRelativeDimension_snd f n
    haveI : Smooth (pullback.snd f f) := SmoothOfRelativeDimension.smooth n _
    haveI := smoothOfRelativeDimension_fst f n
    haveI : Smooth (pullback.fst f f) := SmoothOfRelativeDimension.smooth n _
    haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
    haveI : IsClosedImmersion (sectionFst f σ hσ) :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion)
        (isPullback_section_fst f σ hσ) inferInstance
    haveI : LocallyOfFinitePresentation (sectionFst f σ hσ) :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
        (isPullback_section_fst f σ hσ) inferInstance
    haveI : Smooth (sectionFst f σ hσ ≫ pullback.snd f f) := by
      simpa only [pullback.lift_snd] using (inferInstance : Smooth (𝟙 X))
    haveI : FormallyUnramified (sectionFst f σ hσ ≫ pullback.snd f f) := by
      simpa only [pullback.lift_snd] using (inferInstance : FormallyUnramified (𝟙 X))
    (formsGysinMap (pullback.diagonal f) (pullback.fst f f ≫ f)
        (diagonal_koszul_and_conormalRank f n).1 (diagonal_koszul_and_conormalRank f n).2
        (0 + n) (0 + n)).hom
      ((pullbackHgroup (CohomologyPullbackComparison.canonical (pullback.fst f f).toLRSHom.toShHom)
          (0 : ℤ) (((0 : ℕ) : ℤ) + (n : ℤ)) (0 + n) (by omega)
          (formsBaseChangeHom (pullback.fst f f) f (pullback.fst f f ≫ f) (𝟙 _)
            (by rw [Category.comp_id]) (((0 : ℕ) : ℤ) + (n : ℤ))) ≫
        (Hfunctor (structureSheafRing (pullback f f).toRingedSpace) ⊤ (0 + n)).map
          (formRestrictionModules (pullback.diagonal f) (pullback.fst f f ≫ f)
            ((0 + n : ℕ) : ℤ))).hom (sectionGysinClass f σ n)) =
    (formsGysinMap (sectionFst f σ hσ) (pullback.fst f f ≫ f)
        (isKoszulRegularImmersion_of_smooth_of_smooth _ (pullback.snd f f))
        (conormalRank_of_formallyUnramified _ (pullback.snd f f) n) (0 + n) (0 + n)).hom
      ((pullbackHgroup (CohomologyPullbackComparison.canonical (pullback.snd f f).toLRSHom.toShHom)
          (0 : ℤ) (((0 : ℕ) : ℤ) + (n : ℤ)) (0 + n) (by omega)
          (formsBaseChangeHom (pullback.snd f f) f (pullback.fst f f ≫ f) (𝟙 _)
            (by rw [Category.comp_id, pullback.condition]) (((0 : ℕ) : ℤ) + (n : ℤ))) ≫
        (Hfunctor (structureSheafRing (pullback f f).toRingedSpace) ⊤ (0 + n)).map
          (formRestrictionModules (sectionFst f σ hσ) (pullback.fst f f ≫ f)
            ((0 + n : ℕ) : ℤ))).hom (sectionGysinClass f σ n)) := by
  have : LocallyOfFinitePresentation (pullback.diagonal f) := by
    have : LocallyOfFinitePresentation (pullback.diagonal f ≫ pullback.fst f f) := by
      rw [pullback.diagonal_fst]; infer_instance
    exact locallyOfFinitePresentation_of_comp _ (pullback.fst f f)
  have := smoothOfRelativeDimension_snd f n
  have : Smooth (pullback.snd f f) := SmoothOfRelativeDimension.smooth n _
  have := smoothOfRelativeDimension_fst f n
  have : Smooth (pullback.fst f f) := SmoothOfRelativeDimension.smooth n _
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsClosedImmersion (sectionFst f σ hσ) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (isPullback_section_fst f σ hσ) inferInstance
  have : LocallyOfFinitePresentation (sectionFst f σ hσ) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      (isPullback_section_fst f σ hσ) inferInstance
  have : Smooth (sectionFst f σ hσ ≫ pullback.snd f f) := by
    simpa only [pullback.lift_snd] using (inferInstance : Smooth (𝟙 X))
  have : FormallyUnramified (sectionFst f σ hσ ≫ pullback.snd f f) := by
    simpa only [pullback.lift_snd] using (inferInstance : FormallyUnramified (𝟙 X))
  have hres := formRestriction_eq_of_pullbackHgroup (sectionFst f σ hσ) (pullback.fst f f ≫ f) f
    (pullback.snd f f) (by rw [Category.comp_id, pullback.condition]) (pullback.lift_snd _ _ _)
    (by rw [pullback.lift_fst_assoc, Category.assoc, hσ, Category.comp_id])
    (by rw [pullback.lift_fst_assoc, Category.assoc, hσ, Category.comp_id]) 0
    (((0 : ℕ) : ℤ) + (n : ℤ)) (0 + n) (by omega) (0 + n)
    (gysinUnitClass (pullback.diagonal f) (pullback.fst f f ≫ f)
      (diagonal_koszul_and_conormalRank f n).1 (diagonal_koszul_and_conormalRank f n).2)
    (sectionGysinClass f σ n) (pullbackHgroup_diagonalGysinUnitClass f n σ hσ)
  exact formsGysinMap_eq_of_swap (pullback.fst f f ≫ f) n (pullback.diagonal f)
    (sectionFst f σ hσ) (diagonal_koszul_and_conormalRank f n).1
    (diagonal_koszul_and_conormalRank f n).2
    (isKoszulRegularImmersion_of_smooth_of_smooth _ (pullback.snd f f))
    (conormalRank_of_formallyUnramified _ (pullback.snd f f) n) (sectionGysinClass f σ n) _ _
    (pullbackHgroup_sectionGysinClass_fst f n σ hσ) hres

include σ in
/-- **The Gysin maps of the diagonal and of `(id, σ ∘ f)` agree on `ξ`**: the mirror of
`formsGysinMap_diagonal_eq_sectionFst`, with the ambient copies `p₂^*ξ|_Δ` and `p₁^*ξ|_{j'}`
for `j' = (id, σ ∘ f)`, from `p₂^*ξ = γ_{j'}(1)` and `j'^*η = ξ`. -/
theorem formsGysinMap_diagonal_eq_sectionSnd (hσ : σ ≫ f = 𝟙 _) :
    haveI : LocallyOfFinitePresentation (pullback.diagonal f) := by
      have : LocallyOfFinitePresentation (pullback.diagonal f ≫ pullback.fst f f) := by
        rw [pullback.diagonal_fst]; infer_instance
      exact locallyOfFinitePresentation_of_comp _ (pullback.fst f f)
    haveI := smoothOfRelativeDimension_snd f n
    haveI : Smooth (pullback.snd f f) := SmoothOfRelativeDimension.smooth n _
    haveI := smoothOfRelativeDimension_fst f n
    haveI : Smooth (pullback.fst f f) := SmoothOfRelativeDimension.smooth n _
    haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
    haveI : IsClosedImmersion (sectionSnd f σ hσ) :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion)
        (isPullback_section_snd f σ hσ) inferInstance
    haveI : LocallyOfFinitePresentation (sectionSnd f σ hσ) :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
        (isPullback_section_snd f σ hσ) inferInstance
    haveI : Smooth (sectionSnd f σ hσ ≫ pullback.fst f f) := by
      simpa only [pullback.lift_fst] using (inferInstance : Smooth (𝟙 X))
    haveI : FormallyUnramified (sectionSnd f σ hσ ≫ pullback.fst f f) := by
      simpa only [pullback.lift_fst] using (inferInstance : FormallyUnramified (𝟙 X))
    (formsGysinMap (pullback.diagonal f) (pullback.fst f f ≫ f)
        (diagonal_koszul_and_conormalRank f n).1 (diagonal_koszul_and_conormalRank f n).2
        (0 + n) (0 + n)).hom
      ((pullbackHgroup (CohomologyPullbackComparison.canonical (pullback.snd f f).toLRSHom.toShHom)
          (0 : ℤ) (((0 : ℕ) : ℤ) + (n : ℤ)) (0 + n) (by omega)
          (formsBaseChangeHom (pullback.snd f f) f (pullback.fst f f ≫ f) (𝟙 _)
            (by rw [Category.comp_id, pullback.condition]) (((0 : ℕ) : ℤ) + (n : ℤ))) ≫
        (Hfunctor (structureSheafRing (pullback f f).toRingedSpace) ⊤ (0 + n)).map
          (formRestrictionModules (pullback.diagonal f) (pullback.fst f f ≫ f)
            ((0 + n : ℕ) : ℤ))).hom (sectionGysinClass f σ n)) =
    (formsGysinMap (sectionSnd f σ hσ) (pullback.fst f f ≫ f)
        (isKoszulRegularImmersion_of_smooth_of_smooth _ (pullback.fst f f))
        (conormalRank_of_formallyUnramified _ (pullback.fst f f) n) (0 + n) (0 + n)).hom
      ((pullbackHgroup (CohomologyPullbackComparison.canonical (pullback.fst f f).toLRSHom.toShHom)
          (0 : ℤ) (((0 : ℕ) : ℤ) + (n : ℤ)) (0 + n) (by omega)
          (formsBaseChangeHom (pullback.fst f f) f (pullback.fst f f ≫ f) (𝟙 _)
            (by rw [Category.comp_id]) (((0 : ℕ) : ℤ) + (n : ℤ))) ≫
        (Hfunctor (structureSheafRing (pullback f f).toRingedSpace) ⊤ (0 + n)).map
          (formRestrictionModules (sectionSnd f σ hσ) (pullback.fst f f ≫ f)
            ((0 + n : ℕ) : ℤ))).hom (sectionGysinClass f σ n)) := by
  have : LocallyOfFinitePresentation (pullback.diagonal f) := by
    have : LocallyOfFinitePresentation (pullback.diagonal f ≫ pullback.fst f f) := by
      rw [pullback.diagonal_fst]; infer_instance
    exact locallyOfFinitePresentation_of_comp _ (pullback.fst f f)
  have := smoothOfRelativeDimension_snd f n
  have : Smooth (pullback.snd f f) := SmoothOfRelativeDimension.smooth n _
  have := smoothOfRelativeDimension_fst f n
  have : Smooth (pullback.fst f f) := SmoothOfRelativeDimension.smooth n _
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsClosedImmersion (sectionSnd f σ hσ) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (isPullback_section_snd f σ hσ) inferInstance
  have : LocallyOfFinitePresentation (sectionSnd f σ hσ) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      (isPullback_section_snd f σ hσ) inferInstance
  have : Smooth (sectionSnd f σ hσ ≫ pullback.fst f f) := by
    simpa only [pullback.lift_fst] using (inferInstance : Smooth (𝟙 X))
  have : FormallyUnramified (sectionSnd f σ hσ ≫ pullback.fst f f) := by
    simpa only [pullback.lift_fst] using (inferInstance : FormallyUnramified (𝟙 X))
  have hres := formRestriction_eq_of_pullbackHgroup (sectionSnd f σ hσ) (pullback.fst f f ≫ f) f
    (pullback.fst f f) (by rw [Category.comp_id]) (pullback.lift_fst _ _ _)
    (by rw [pullback.lift_fst_assoc, Category.id_comp])
    (by rw [pullback.lift_fst_assoc, Category.id_comp, Category.comp_id]) 0
    (((0 : ℕ) : ℤ) + (n : ℤ)) (0 + n) (by omega) (0 + n)
    (gysinUnitClass (pullback.diagonal f) (pullback.fst f f ≫ f)
      (diagonal_koszul_and_conormalRank f n).1 (diagonal_koszul_and_conormalRank f n).2)
    (sectionGysinClass f σ n) (pullbackHgroup_diagonalGysinUnitClass' f n σ hσ)
  exact formsGysinMap_eq_of_swap (pullback.fst f f ≫ f) n (pullback.diagonal f)
    (sectionSnd f σ hσ) (diagonal_koszul_and_conormalRank f n).1
    (diagonal_koszul_and_conormalRank f n).2
    (isKoszulRegularImmersion_of_smooth_of_smooth _ (pullback.fst f f))
    (conormalRank_of_formallyUnramified _ (pullback.fst f f) n) (sectionGysinClass f σ n) _ _
    (pullbackHgroup_sectionGysinClass_snd f n σ hσ) hres

end DiagonalTop


/-! ### Base functions and the pullback of forms over the same base -/

section BaseScalars

variable {A : Type u} [CommRing A] {X X' : Scheme.{u}} (f : X ⟶ Spec (.of A))
  (f' : X' ⟶ Spec (.of A)) (g : X' ⟶ X) (hg : g ≫ f = f') (w : g ≫ f = f' ≫ 𝟙 _)

include hg in
/-- **The base change of forms along a morphism over `Spec A` is `A`-linear**: it carries
multiplication by `c ∈ A` on `Ω^p_{X/A}` to multiplication by `c` on `g_*Ω^p_{X'/A}`. This is
`Stacks.Cech.formsBaseChangeHom_comp_globalSmul` for a commutative triangle over the same base
in place of a cartesian square. -/
theorem formsBaseChangeHom_comp_globalSmul_of_comp (p : ℤ) (c : A) :
    formsBaseChangeHom g f f' (𝟙 _) w p ≫
        (modulePushforward g.toLRSHom.toShHom).map
          (AlgebraicGeometry.globalSmul ((Stacks.Cech.globalRingHom f').hom c)
            (f'.relativeDifferentialForms p)) =
      AlgebraicGeometry.globalSmul ((Stacks.Cech.globalRingHom f).hom c)
          (f.relativeDifferentialForms p) ≫
        formsBaseChangeHom g f f' (𝟙 _) w p := by
  ext V t
  change (AlgebraicGeometry.globalSmul ((Stacks.Cech.globalRingHom f').hom c)
        (f'.relativeDifferentialForms p)).app
      (g ⁻¹ᵁ V) ((formsBaseChangeHom g f f' (𝟙 _) w p).app V t) =
    (formsBaseChangeHom g f f' (𝟙 _) w p).app V
      ((AlgebraicGeometry.globalSmul ((Stacks.Cech.globalRingHom f).hom c)
        (f.relativeDifferentialForms p)).app V t)
  refine (AlgebraicGeometry.globalSmul_app _ _ _ _).trans ?_
  refine Eq.trans ?_ (congrArg _ (AlgebraicGeometry.globalSmul_app _ _ _ _)).symm
  refine Eq.trans ?_ (Scheme.Modules.Hom.app_smul
    (N := Stacks.Cech.pushforwardModule g (f'.relativeDifferentialForms p))
    (formsBaseChangeHom g f f' (𝟙 _) w p) _ _).symm
  have hb : g.app V (AlgebraicGeometry.restrictTop ((Stacks.Cech.globalRingHom f).hom c) V) =
      AlgebraicGeometry.restrictTop ((Stacks.Cech.globalRingHom f').hom c) (g ⁻¹ᵁ V) := by
    have h := congr($(Stacks.Cech.baseRingHom_comp_app_of_comp f f' g hg V).hom c)
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp] at h
    exact h
  rw [← hb]
  rfl

include hg in
/-- **The pullback map along a morphism over `Spec A` is `A`-linear** on the cohomology of
forms: it commutes with multiplication by `c ∈ A`. -/
theorem pullbackHgroup_formsBaseChangeHom_globalSmul_of_comp (p : ℤ) (c : A) (a m : ℤ) (n : ℕ)
    (hn : m - a = n) (x : Hgroup X.ringCatSheaf ⊤ n (f.relativeDifferentialForms p)) :
    (pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) a m n hn
        (formsBaseChangeHom g f f' (𝟙 _) w p)).hom
        (((Hfunctor X.ringCatSheaf ⊤ n).map
          (AlgebraicGeometry.globalSmul ((Stacks.Cech.globalRingHom f).hom c)
            (f.relativeDifferentialForms p))).hom x) =
      ((Hfunctor X'.ringCatSheaf ⊤ n).map
          (AlgebraicGeometry.globalSmul ((Stacks.Cech.globalRingHom f').hom c)
            (f'.relativeDifferentialForms p))).hom
        ((pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) a m n hn
          (formsBaseChangeHom g f f' (𝟙 _) w p)).hom x) :=
  congrArg (fun k => k.hom x) (pullbackHgroup_naturality
    (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) a m n hn
    (AlgebraicGeometry.globalSmul ((Stacks.Cech.globalRingHom f).hom c)
      (f.relativeDifferentialForms p))
    (AlgebraicGeometry.globalSmul ((Stacks.Cech.globalRingHom f').hom c)
      (f'.relativeDifferentialForms p)) _ _
    (formsBaseChangeHom_comp_globalSmul_of_comp f f' g hg w p c))

end BaseScalars

end Stacks.DeRham.CohomologicalGysin

end
