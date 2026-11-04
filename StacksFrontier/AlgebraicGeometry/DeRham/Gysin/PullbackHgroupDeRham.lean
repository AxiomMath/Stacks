module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.PullbackHgroupCoefficients
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.PullbackHgroupNaturality
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologyPullbackShift
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.TransverseBaseChangeArrow
public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamComplexBaseChangeGraded

/-!
# Pullback maps on Hodge cohomology commute with the de Rham differentials

Let `f : X ⟶ S` be a morphism of schemes. A de Rham differential `d : Ω^p_{X/S} ⟶ Ω^{p+1}_{X/S}`
is not `𝒪_X`-linear, so it acts on the cohomology groups `Hⁿ(X, Ω^p_{X/S})` only through its
underlying morphism of abelian sheaves (`Stacks.DeRham.GysinCohomologyDeRham.abelianHgroupMap`).
It is, however, `f⁻¹𝒪_S`-linear: a morphism of modules on the ringed space
`X♭ = (X, f⁻¹𝒪_S)`. Comparing the two ringed spaces along `c : (X, 𝒪_X) ⟶ X♭`
(`Stacks.DeRham.GysinCohomologyBaseChange.pullbackHgroup_toInverseImageBase_abelianHgroupMap`)
this file shows:

* the abelian action of an `f⁻¹𝒪_S`-linear map on cohomology does not depend on the degree in
  which the modules are placed (`abelianHgroupMap_eq_of_inverseImageBase`);
* for a morphism `G : W ⟶ X` of schemes over `S`, **the pullback map
  `Hⁿ(X, Ω^p_{X/S}) ⟶ Hⁿ(W, Ω^p_{W/S})` of [Stacks, Tag 01F9] along the canonical map of forms
  commutes with the de Rham differentials** (`pullbackHgroup_formsBaseChangeHom_comm_deRham`).

The second is proved over the ringed spaces `X♭` and `W♭ = (W, h⁻¹𝒪_S)`, along the morphism
`G♭ : W♭ ⟶ X♭` of `Stacks.DeRhamBaseChange.relativeBaseOfEq`: there the map of forms and the
differentials are morphisms of modules, so the naturality of pullback maps applies, and the
composition law of pullback maps moves the result back to `X` and `W`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.UnderlyingAbelianSheaf
open Stacks.DeRham.CohomologicalGysin Stacks.DeRham.GysinCohomologyDeRham
open Stacks.DeRhamDirectImage (inverseImageBase toInverseImageBase)

namespace Stacks.DeRham.GysinCohomologyBaseChange

universe u

/-! ### Pullback maps along equal morphisms -/

/-- **Pullback maps along equal morphisms agree**, once the `G`-maps are matched along the
equality of the direct images. -/
theorem pullbackHgroup_canonical_congr {X X' : RingedSpace.{u, u}} {G₁ G₂ : X' ⟶ X}
    (hG : G₁ = G₂) (a m : ℤ) (n : ℕ) (hn : m - a = n) {M : RModules X} {M' : RModules X'}
    (φ : M ⟶ (modulePushforward G₁).obj M') :
    pullbackHgroup (CohomologyPullbackComparison.canonical G₁) a m n hn φ =
      pullbackHgroup (CohomologyPullbackComparison.canonical G₂) a m n hn
        (φ ≫ eqToHom (congrArg (fun G => (modulePushforward G).obj M') hG)) := by
  subst hG
  rw [eqToHom_refl, Category.comp_id]

/-! ### Independence of the placement degree -/

section Placement

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- `(X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)` is a homeomorphism onto a closed subset, as a `Fact`. -/
instance fact_isClosedEmbedding_toInverseImageBase :
    Fact (Topology.IsClosedEmbedding (toInverseImageBase f).hom.base) :=
  ⟨isClosedEmbedding_toInverseImageBase f⟩

/-- **The abelian action of an `f⁻¹𝒪_S`-linear map on cohomology does not depend on the degree in
which the modules are placed.** Both actions are conjugate, by the same isomorphism
`Hⁿ(X♭, c_*ℳ) ≅ Hⁿ(X, ℳ)`, to the map induced by the `f⁻¹𝒪_S`-linear map. -/
theorem abelianHgroupMap_eq_of_inverseImageBase (a a' m m' : ℤ) (n : ℕ) (hn : m - a = n)
    (hn' : m' - a' = n) {A B : RModules X.toRingedSpace}
    (ψf : (modulePushforward (toInverseImageBase f)).obj A ⟶
      (modulePushforward (toInverseImageBase f)).obj B)
    (ψ : (forgetModules X.toRingedSpace).obj A ⟶ (forgetModules X.toRingedSpace).obj B)
    (hψ : (forgetModules (inverseImageBase f)).map ψf = ψ) :
    abelianHgroupMap X.toRingedSpace a m n hn ψ =
      abelianHgroupMap X.toRingedSpace a' m' n hn' ψ := by
  have h₁ := pullbackHgroup_toInverseImageBase_abelianHgroupMap f a m n hn ψf ψ hψ
  have h₂ := pullbackHgroup_toInverseImageBase_abelianHgroupMap f a' m' n hn' ψf ψ hψ
  rw [pullbackHgroup_canonical_eq (toInverseImageBase f) a m n hn,
    pullbackHgroup_canonical_eq (toInverseImageBase f) a m n hn] at h₁
  rw [pullbackHgroup_canonical_eq (toInverseImageBase f) a' m' n hn',
    pullbackHgroup_canonical_eq (toInverseImageBase f) a' m' n hn'] at h₂
  have := isIso_pullbackHgroup_canonical_id (toInverseImageBase f) 0 n n (by omega) A
  exact (cancel_epi _).1 (h₁.trans h₂.symm)

/-- **The relative de Rham differential as a morphism of `f⁻¹𝒪_S`-modules**, between the direct
images of the forms along `(X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)`. -/
def deRhamDifferentialInverseImageBase (p : ℕ) :
    (modulePushforward (toInverseImageBase f)).obj (f.relativeDifferentialForms (p : ℤ)) ⟶
      (modulePushforward (toInverseImageBase f)).obj
        (f.relativeDifferentialForms ((p + 1 : ℕ) : ℤ)) :=
  (Scheme.Hom.deRhamComplex f).d p (p + 1)

/-- The underlying morphism of abelian sheaves of `deRhamDifferentialInverseImageBase` is the de
Rham differential read on abelian sheaves. -/
theorem forgetModules_map_deRhamDifferentialInverseImageBase (p : ℕ) :
    (forgetModules (inverseImageBase f)).map (deRhamDifferentialInverseImageBase f p) =
      Scheme.Hom.deRhamDifferentialAbHom f p :=
  rfl

/-- **The action of a de Rham differential on cohomology does not depend on the placement
degree.** -/
theorem abelianHgroupMap_deRham_eq (a a' m m' : ℤ) (n : ℕ) (hn : m - a = n) (hn' : m' - a' = n)
    (p : ℕ) :
    abelianHgroupMap X.toRingedSpace a m n hn (Scheme.Hom.deRhamDifferentialAbHom f p) =
      abelianHgroupMap X.toRingedSpace a' m' n hn' (Scheme.Hom.deRhamDifferentialAbHom f p) :=
  abelianHgroupMap_eq_of_inverseImageBase f a a' m m' n hn hn'
    (deRhamDifferentialInverseImageBase f p) _ rfl

end Placement

/-! ### Pullback along a morphism over `S` commutes with the de Rham differentials -/

section Pullback

variable {X W S : Scheme.{u}} (f : X ⟶ S) (G : W ⟶ X) (h : W ⟶ S) (w : G ≫ f = h ≫ 𝟙 S)

/-- **The canonical map of forms along `G`, over the inverse-image ringed spaces**: the direct
image of `Ω^p_{X/S} ⟶ G_*Ω^p_{W/S}` along `(X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)`, read as a `G♭`-map for the
morphism `G♭ : (W, h⁻¹𝒪_S) ⟶ (X, f⁻¹𝒪_S)` of `Stacks.DeRhamBaseChange.inverseImageBaseMap`. -/
def formsBaseChangeInverseImageBase (p : ℤ) :
    (modulePushforward (toInverseImageBase f)).obj (f.relativeDifferentialForms p) ⟶
      (modulePushforward (Stacks.DeRhamBaseChange.inverseImageBaseMap G h f (𝟙 S) w)).obj
        ((modulePushforward (toInverseImageBase h)).obj (h.relativeDifferentialForms p)) :=
  (modulePushforward (toInverseImageBase f)).map (Stacks.Gysin.formsBaseChangeHom G f h (𝟙 S) w p) ≫
    (modulePushforwardComp G.toLRSHom.toShHom (toInverseImageBase f)).hom.app
      (h.relativeDifferentialForms p) ≫
    eqToHom (congrArg (fun K => (modulePushforward K).obj (h.relativeDifferentialForms p))
      (Stacks.DeRhamBaseChange.toShHom_comp_toInverseImageBase G h f (𝟙 S) w)) ≫
    (modulePushforwardComp (toInverseImageBase h)
      (Stacks.DeRhamBaseChange.inverseImageBaseMap G h f (𝟙 S) w)).inv.app
      (h.relativeDifferentialForms p)

/-- `formsBaseChangeInverseImageBase` is the degree-`p` component of the canonical map of de Rham
complexes of the square (`Stacks.DeRhamBaseChange.formsPushforward`). -/
theorem formsBaseChangeInverseImageBase_eq (p : ℕ) :
    formsBaseChangeInverseImageBase f G h w (p : ℤ) =
      Stacks.DeRhamBaseChange.formsPushforward G h f (𝟙 S) w p := by
  have hu := (modulePullbackPushforwardAdjunction G.toLRSHom.toShHom).homEquiv_unit
    (f.relativeDifferentialForms (p : ℤ)) (h.relativeDifferentialForms (p : ℤ))
    (Scheme.Hom.relativeDifferentialFormsMap G f h (𝟙 S) w (p : ℤ))
  refine Eq.trans ?_ ((Stacks.DeRhamBaseChange.formsPushforward_eq G h f (𝟙 S) w p).trans
    (congrArg (_ ≫ ·) (Stacks.DeRhamBaseChange.pushforwardSquareIso_inv_app_eq G h f (𝟙 S) w
      _))).symm
  have he := eqToHom_app (congrArg modulePushforward
    (Stacks.DeRhamBaseChange.toShHom_comp_toInverseImageBase G h f (𝟙 S) w))
    (h.relativeDifferentialForms (p : ℤ))
  exact congrArg₂ (fun φ t => (modulePushforward (toInverseImageBase f)).map φ ≫
    ((modulePushforwardComp G.toLRSHom.toShHom (toInverseImageBase f)).hom.app
      (h.relativeDifferentialForms (p : ℤ)) ≫ t ≫
    (modulePushforwardComp (toInverseImageBase h)
      (Stacks.DeRhamBaseChange.inverseImageBaseMap G h f (𝟙 S) w)).inv.app
      (h.relativeDifferentialForms (p : ℤ)))) hu he.symm

/-- **The canonical map of forms commutes with the de Rham differentials, over the inverse-image
ringed spaces**: this is the chain map `Stacks.DeRhamBaseChange.deRhamPushforwardChain`. -/
theorem formsBaseChangeInverseImageBase_comm (p : ℕ) :
    formsBaseChangeInverseImageBase f G h w (p : ℤ) ≫
        (modulePushforward (Stacks.DeRhamBaseChange.inverseImageBaseMap G h f (𝟙 S) w)).map
          (deRhamDifferentialInverseImageBase h p) =
      deRhamDifferentialInverseImageBase f p ≫
        formsBaseChangeInverseImageBase f G h w ((p + 1 : ℕ) : ℤ) := by
  rw [formsBaseChangeInverseImageBase_eq, formsBaseChangeInverseImageBase_eq]
  exact (Stacks.DeRhamBaseChange.deRhamPushforwardChain G h f (𝟙 S) w).comm p (p + 1)

/-- The algebra of `pullbackHgroup_formsBaseChangeHom_comm_deRham`, at variables. -/
private lemma deRham_pullback_chase {C : Type*} [Category* C] {x₀ x₁ w₀ w₁ y₀ y₁ z₀ z₁ : C}
    (eX₀ : y₀ ⟶ x₀) (eX₁ : y₁ ⟶ x₁) (eW₀ : z₀ ⟶ w₀) (eW₁ : z₁ ⟶ w₁) (pb₀ : x₀ ⟶ w₀)
    (pb₁ : x₁ ⟶ w₁) (pf₀ : y₀ ⟶ z₀) (pf₁ : y₁ ⟶ z₁) (dX : x₀ ⟶ x₁) (dW : w₀ ⟶ w₁)
    (dXf : y₀ ⟶ y₁) (dWf : z₀ ⟶ z₁) [Epi eX₀]
    (k₀ : eX₀ ≫ pb₀ = pf₀ ≫ eW₀) (k₁ : eX₁ ≫ pb₁ = pf₁ ≫ eW₁)
    (bW : eW₀ ≫ dW = dWf ≫ eW₁) (bX : eX₀ ≫ dX = dXf ≫ eX₁)
    (nat : dXf ≫ pf₁ = pf₀ ≫ dWf) :
    pb₀ ≫ dW = dX ≫ pb₁ := by
  refine (cancel_epi eX₀).1 ?_
  rw [reassoc_of% k₀, bW, reassoc_of% bX, k₁, reassoc_of% nat]

/-- The pullback map along `G` of the canonical map of forms, read over the inverse-image ringed
spaces: `Hⁿ(X♭, c_*Ω^p_{X/S}) ≅ Hⁿ(X, Ω^p_{X/S}) ⟶ Hⁿ(W, Ω^p_{W/S})` is
`Hⁿ(X♭, c_*Ω^p_{X/S}) ⟶ Hⁿ(W♭, c_*Ω^p_{W/S}) ≅ Hⁿ(W, Ω^p_{W/S})`, by the composition law of
pullback maps along the two factorizations of `W ⟶ X♭`. -/
theorem pullbackHgroup_toInverseImageBase_comp_formsBaseChangeHom (a m : ℤ) (n : ℕ)
    (hn : m - a = n) (q : ℤ) :
    pullbackHgroup (CohomologyPullbackComparison.canonical (toInverseImageBase f)) a m n hn
        (𝟙 ((modulePushforward (toInverseImageBase f)).obj (f.relativeDifferentialForms q))) ≫
      pullbackHgroup (CohomologyPullbackComparison.canonical G.toLRSHom.toShHom) a m n hn
        (Stacks.Gysin.formsBaseChangeHom G f h (𝟙 S) w q) =
    pullbackHgroup (CohomologyPullbackComparison.canonical
        (Stacks.DeRhamBaseChange.inverseImageBaseMap G h f (𝟙 S) w)) a m n hn
        (formsBaseChangeInverseImageBase f G h w q) ≫
      pullbackHgroup (CohomologyPullbackComparison.canonical (toInverseImageBase h)) a m n hn
        (𝟙 ((modulePushforward (toInverseImageBase h)).obj (h.relativeDifferentialForms q))) := by
  have h1 := pullbackHgroup_canonical_comp G.toLRSHom.toShHom (toInverseImageBase f) a m n hn
    (𝟙 ((modulePushforward (toInverseImageBase f)).obj (f.relativeDifferentialForms q)))
    (Stacks.Gysin.formsBaseChangeHom G f h (𝟙 S) w q)
  have h2 := pullbackHgroup_canonical_comp (toInverseImageBase h)
    (Stacks.DeRhamBaseChange.inverseImageBaseMap G h f (𝟙 S) w) a m n hn
    (formsBaseChangeInverseImageBase f G h w q)
    (𝟙 ((modulePushforward (toInverseImageBase h)).obj (h.relativeDifferentialForms q)))
  have h3 := pullbackHgroup_canonical_congr
    (Stacks.DeRhamBaseChange.toShHom_comp_toInverseImageBase G h f (𝟙 S) w) a m n hn
    (𝟙 ((modulePushforward (toInverseImageBase f)).obj (f.relativeDifferentialForms q)) ≫
      (modulePushforward (toInverseImageBase f)).map
        (Stacks.Gysin.formsBaseChangeHom G f h (𝟙 S) w q) ≫
      (modulePushforwardComp G.toLRSHom.toShHom (toInverseImageBase f)).hom.app
        (h.relativeDifferentialForms q))
  rw [← h1, ← h2, h3]
  congr 1

/-- **The pullback map of Hodge cohomology along a morphism over `S` commutes with the de Rham
differentials.** For `G : W ⟶ X` over `S`, the pullback map `Hⁿ(X, Ω^p_{X/S}) ⟶ Hⁿ(W, Ω^p_{W/S})`
of [Stacks, Tag 01F9] along the canonical map of forms carries the action of
`d : Ω^p_{X/S} ⟶ Ω^{p+1}_{X/S}` to that of `d : Ω^p_{W/S} ⟶ Ω^{p+1}_{W/S}`, in every placement
degree. -/
theorem pullbackHgroup_formsBaseChangeHom_comm_deRham (a m : ℤ) (n : ℕ) (hn : m - a = n)
    (p : ℕ) :
    pullbackHgroup (CohomologyPullbackComparison.canonical G.toLRSHom.toShHom) a m n hn
        (Stacks.Gysin.formsBaseChangeHom G f h (𝟙 S) w (p : ℤ)) ≫
      abelianHgroupMap W.toRingedSpace a m n hn (Scheme.Hom.deRhamDifferentialAbHom h p) =
    abelianHgroupMap X.toRingedSpace a m n hn (Scheme.Hom.deRhamDifferentialAbHom f p) ≫
      pullbackHgroup (CohomologyPullbackComparison.canonical G.toLRSHom.toShHom) a m n hn
        (Stacks.Gysin.formsBaseChangeHom G f h (𝟙 S) w ((p + 1 : ℕ) : ℤ)) := by
  have := isIso_pullbackHgroup_canonical_id (toInverseImageBase f) a m n hn
    (f.relativeDifferentialForms (p : ℤ))
  exact deRham_pullback_chase _ _ _ _ _ _ _ _ _ _ _ _
    (pullbackHgroup_toInverseImageBase_comp_formsBaseChangeHom f G h w a m n hn (p : ℤ))
    (pullbackHgroup_toInverseImageBase_comp_formsBaseChangeHom f G h w a m n hn
      ((p + 1 : ℕ) : ℤ))
    (pullbackHgroup_toInverseImageBase_abelianHgroupMap h a m n hn
      (deRhamDifferentialInverseImageBase h p) (Scheme.Hom.deRhamDifferentialAbHom h p) rfl)
    (pullbackHgroup_toInverseImageBase_abelianHgroupMap f a m n hn
      (deRhamDifferentialInverseImageBase f p) (Scheme.Hom.deRhamDifferentialAbHom f p) rfl)
    (pullbackHgroup_naturality (CohomologyPullbackComparison.canonical
        (Stacks.DeRhamBaseChange.inverseImageBaseMap G h f (𝟙 S) w))
      a m n hn (deRhamDifferentialInverseImageBase f p) (deRhamDifferentialInverseImageBase h p)
      _ _ (formsBaseChangeInverseImageBase_comm f G h w p))

end Pullback

end Stacks.DeRham.GysinCohomologyBaseChange

end
