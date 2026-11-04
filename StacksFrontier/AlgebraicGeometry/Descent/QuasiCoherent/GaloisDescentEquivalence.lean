module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Galois
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcStack
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcEffectiveUnconditional
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiGluing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Galois descent for quasi-coherent modules: the fpqc stack condition and the Galois cover

Let `f : X ⟶ Y` be a surjective finite étale morphism of schemes, `G` a finite group, and
`a : Gᵐᵒᵖ →* Aut (Over.mk f)` an action of `G` on `X` over `Y` whose comparison map
`∐_{σ : G} X ⟶ X ×_Y X`, given on the summand indexed by `σ` by `(𝟙, f_σ)`, is an isomorphism.
This file supplies two of the inputs to Galois descent along such a cover: the fpqc stack
condition for quasi-coherent modules, and the identification of `∐_{(σ, τ) : G × G} X` with the
triple fibre product `X ×_Y X ×_Y X`.

## Main definitions

* `Stacks.Descent.galoisChosenPullback` and `Stacks.Descent.galoisChosenPullback₃` present
  `X ×_Y X` and `X ×_Y X ×_Y X` as chosen fibre products of the one-element family `{f}`.
* `Stacks.Descent.galoisTripleComparison` is the comparison `∐_{G × G} X ⟶ X ×_Y X ×_Y X` whose
  summand indexed by `(σ, τ)` has legs `𝟙`, `f_σ` and `f_(στ)`.

## Main results

* `Stacks.Descent.isStack_qcohPseudofunctor_fpqcTopology`: quasi-coherent modules form a stack
  for the fpqc topology.
* `Stacks.Descent.exists_hom_of_sigmaIso` and `Stacks.Descent.hom_ext_of_sigmaIso`: a morphism of
  quasi-coherent modules on a scheme presented as a coproduct is the same thing as a family of
  morphisms on the summands.
* `Stacks.Descent.galoisTripleComparison_isIso`: the action identifies `∐_{G × G} X` with the
  triple fibre product as soon as it identifies `∐_G X` with `X ×_Y X`.

## Implementation notes

Gluing a morphism along the coproduct presentation uses
`Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_openCover` for the open cover
`(AlgebraicGeometry.sigmaOpenCover _).pushforwardIso`.  The off-diagonal compatibility condition
is vacuous there: two distinct summands of a coproduct of schemes have empty intersection, and
the module hom-sets over an empty scheme are subsingletons.

`Stacks.Descent.galoisTripleComparison` is built as a composite of three maps, each an
isomorphism for its own reason — a coproduct of sections of the projections
`X ×_{f_σ, 𝟙} X ⟶ X`, the extensivity of `Scheme` through
`CategoryTheory.FinitaryPreExtensive.isIso_sigmaDesc_map`, and a base change of the Galois cover
comparison along itself.

## References

* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 0D1V](https://stacks.math.columbia.edu/tag/0D1V)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open AlgebraicGeometry

universe v u

namespace Stacks.Descent

/-! ### The fpqc stack condition -/

/-- **Quasi-coherent modules form a stack for the fpqc topology.** -/
@[sga "1 VIII 1.1" "more general"]
instance isStack_qcohPseudofunctor_fpqcTopology :
    qcohPseudofunctor.{u}.IsStack Scheme.fpqcTopology.{u} :=
  isStack_qcohPseudofunctor_of_forall_isEffective fun f hf D ↦
    QuasicoherentDescentData.isEffective_fpqcPrecoverage ⟨_, _, f⟩ hf D

/-! ### Gluing module morphisms along a coproduct presentation -/

/-- Morphisms of sheaves of modules over the empty scheme are unique. -/
theorem modules_hom_subsingleton_of_isEmpty {Z : Scheme.{u}} [IsEmpty Z] (M N : Z.Modules) :
    Subsingleton (M ⟶ N) := by
  refine ⟨fun φ ψ ↦ Scheme.Modules.hom_ext φ ψ fun U ↦ ?_⟩
  have hU : U = ⊥ := Subsingleton.elim _ _
  subst U
  have hterm := TopCat.Sheaf.isTerminalOfEmpty ((SheafOfModules.toSheaf Z.ringCatSheaf).obj N)
  have hzero : (𝟙 (N.presheaf.obj (.op ⊥)) : _ ⟶ _) = 0 := hterm.hom_ext _ _
  have h0 (x : N.presheaf.obj (.op ⊥)) : x = 0 := by
    simpa using congrArg (fun g : N.presheaf.obj (.op ⊥) ⟶ _ => g x) hzero
  have : Subsingleton (N.presheaf.obj (.op ⊥)) := ⟨fun x y ↦ (h0 x).trans (h0 y).symm⟩
  ext x
  exact Subsingleton.elim _ _

/-- **A morphism of quasi-coherent modules may be glued from its restrictions to the summands of
a coproduct presentation.**  If `c : ∐ Z ⟶ T` is an isomorphism, a family of morphisms of the
pullbacks of `M` and `N` to the summands comes from a single morphism `M ⟶ N`. -/
theorem exists_hom_of_sigmaIso {I : Type v} [Finite I] {Z : I → Scheme.{u}} {T : Scheme.{u}}
    (c : (∐ Z) ⟶ T) [IsIso c] (M N : T.Modules) (hM : M.IsQuasicoherent)
    (hN : N.IsQuasicoherent)
    (e : ∀ i, (Scheme.Modules.pullback (Sigma.ι Z i ≫ c)).obj M ⟶
      (Scheme.Modules.pullback (Sigma.ι Z i ≫ c)).obj N) :
    ∃ h : M ⟶ N, ∀ i, (Scheme.Modules.pullback (Sigma.ι Z i ≫ c)).map h = e i := by
  classical
  let U := (sigmaOpenCover Z).pushforwardIso c
  have hU : ∀ k, U.f k = Sigma.ι Z k ≫ c := fun k ↦
    (Scheme.Cover.pushforwardIso_f (sigmaOpenCover Z) c k).trans
      (congrArg (· ≫ c) (sigmaOpenCover_f Z k))
  let F := (nonempty_fullyFaithful_canonicalDescentFunctor_openCover U).some
  let M' : (SheafOfModules.isQuasicoherent T.ringCatSheaf).FullSubcategory := ⟨M, hM⟩
  let N' : (SheafOfModules.isQuasicoherent T.ringCatSheaf).FullSubcategory := ⟨N, hN⟩
  let DM := (AlgebraicGeometry.canonicalDescentFunctor U.f).obj M'
  let DN := (AlgebraicGeometry.canonicalDescentFunctor U.f).obj N'
  let η : DM ⟶ DN := ⟨{
    hom := e
    comm := by
      intro W q i j f₁ f₂ hf₁ hf₂
      by_cases hij : i = j
      · subst j
        have hf : f₁ = f₂ := (cancel_mono (U.f i)).1 (hf₁.trans hf₂.symm)
        subst f₂
        rw [DM.obj.hom_self q f₁ hf₁, DN.obj.hom_self q f₁ hf₁]
        simp
      · rw [hU i] at hf₁
        rw [hU j] at hf₂
        have hc' : (f₁ ≫ Sigma.ι Z i) ≫ c = (f₂ ≫ Sigma.ι Z j) ≫ c :=
          (Category.assoc f₁ (Sigma.ι Z i) c).trans
            ((hf₁.trans hf₂.symm).trans (Category.assoc f₂ (Sigma.ι Z j) c).symm)
        have : IsEmpty W := isEmpty_of_commSq_sigmaι_of_ne (g := Z)
          (⟨(cancel_mono c).1 hc'⟩ : CommSq f₁ f₂ (Sigma.ι Z i) (Sigma.ι Z j)) hij
        exact (modules_hom_subsingleton_of_isEmpty _ _).elim _ _
  }⟩
  refine ⟨(F.preimage η).hom, fun i ↦ ?_⟩
  exact congrArg (fun α ↦ α.hom.hom i) (F.map_preimage η)

/-- **A morphism of quasi-coherent modules is determined by its restrictions to the summands of a
coproduct presentation.** -/
theorem hom_ext_of_sigmaIso {I : Type v} [Finite I] {Z : I → Scheme.{u}} {T : Scheme.{u}}
    (c : (∐ Z) ⟶ T) [IsIso c] (M N : T.Modules) (hM : M.IsQuasicoherent)
    (hN : N.IsQuasicoherent) (h k : M ⟶ N)
    (e : ∀ i, (Scheme.Modules.pullback (Sigma.ι Z i ≫ c)).map h =
      (Scheme.Modules.pullback (Sigma.ι Z i ≫ c)).map k) : h = k := by
  classical
  let U := (sigmaOpenCover Z).pushforwardIso c
  let F := (nonempty_fullyFaithful_canonicalDescentFunctor_openCover U).some
  let M' : (SheafOfModules.isQuasicoherent T.ringCatSheaf).FullSubcategory := ⟨M, hM⟩
  let N' : (SheafOfModules.isQuasicoherent T.ringCatSheaf).FullSubcategory := ⟨N, hN⟩
  have hh : (ObjectProperty.homMk h : M' ⟶ N') = ObjectProperty.homMk k :=
    F.map_injective (by ext i; exact e i)
  exact congrArg (·.hom) hh

/-! ### The fibre products of the one-element family -/

/-- `X ×_Y X` as a chosen fibre product of `f` with itself. -/
def galoisChosenPullback {X Y : Scheme.{u}} (f : X ⟶ Y) : ChosenPullback f f where
  pullback := pullback f f
  p₁ := pullback.fst f f
  p₂ := pullback.snd f f
  condition := pullback.condition
  isLimit := pullbackIsPullback f f

/-- `X ×_Y X ×_Y X` as a chosen triple fibre product of `f`. -/
def galoisChosenPullback₃ {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ChosenPullback₃ (galoisChosenPullback f) (galoisChosenPullback f)
      (galoisChosenPullback f) := by
  let h := galoisChosenPullback f
  let t : ChosenPullback h.p₂ h.p₁ :=
    { pullback := pullback h.p₂ h.p₁
      p₁ := pullback.fst h.p₂ h.p₁
      p₂ := pullback.snd h.p₂ h.p₁
      condition := pullback.condition
      isLimit := pullbackIsPullback h.p₂ h.p₁ }
  let p₁ := t.p₁ ≫ h.p₁
  let p₃ := t.p₂ ≫ h.p₂
  let p := t.p₁ ≫ h.p
  let l : h.LiftStruct p₁ p₃ p :=
    { f := h.isPullback.lift p₁ p₃ (by
        dsimp [p₁, p₃]
        rw [Category.assoc, h.condition, ← Category.assoc, t.condition, Category.assoc,
          h.condition, Category.assoc])
      f_p₁ := by simp [p₁]
      f_p₂ := by simp [p₃]
      f_p := by
        dsimp [p, p₁, p₃]
        change (h.isPullback.lift _ _ _ ≫ h.p₁) ≫ f = t.p₁ ≫ (h.p₁ ≫ f)
        rw [h.isPullback.lift_fst]
        exact Category.assoc _ _ _ }
  exact ⟨t, p, p₁, p₃, l, by rfl, by rfl⟩

/-! ### The Galois cover comparison and its triple analogue -/

/-- The summand formula for the Galois cover comparison. -/
theorem galoisCoverComparison_ι {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : Gᵐᵒᵖ →* Aut (Over.mk f)) (σ : G) :
    Sigma.ι (fun _ : G ↦ X) σ ≫ galoisCoverComparison f a =
      pullback.lift (𝟙 X) (GaloisDescentData.twist G f a σ) (by
        rw [Category.id_comp, GaloisDescentData.twist_comp]) := by
  simp [galoisCoverComparison]

/-- The first leg of the comparison on the summand indexed by `σ` is the identity. -/
theorem galoisCoverComparison_ι_fst {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : Gᵐᵒᵖ →* Aut (Over.mk f)) (σ : G) :
    Sigma.ι (fun _ : G ↦ X) σ ≫ galoisCoverComparison f a ≫ pullback.fst f f = 𝟙 X := by
  rw [← Category.assoc, galoisCoverComparison_ι]
  exact pullback.lift_fst _ _ _

/-- The second leg of the comparison on the summand indexed by `σ` is `f_σ`. -/
theorem galoisCoverComparison_ι_snd {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : Gᵐᵒᵖ →* Aut (Over.mk f)) (σ : G) :
    Sigma.ι (fun _ : G ↦ X) σ ≫ galoisCoverComparison f a ≫ pullback.snd f f =
      GaloisDescentData.twist G f a σ := by
  rw [← Category.assoc, galoisCoverComparison_ι]
  exact pullback.lift_snd _ _ _

/-- The map `∐_{σ : G} X ⟶ X` which is `f_σ` on the summand indexed by `σ`. -/
def galoisTripleFirstMap {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : Gᵐᵒᵖ →* Aut (Over.mk f)) : (∐ fun _ : G ↦ X) ⟶ X :=
  Sigma.desc fun σ ↦ GaloisDescentData.twist G f a σ

/-- The map `∐_{σ : G} X ⟶ X` which is the identity on every summand. -/
def galoisTripleSecondMap {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (_a : Gᵐᵒᵖ →* Aut (Over.mk f)) : (∐ fun _ : G ↦ X) ⟶ X :=
  Sigma.desc fun _ ↦ 𝟙 X

/-- The second leg of the Galois cover comparison is `Stacks.Descent.galoisTripleFirstMap`. -/
theorem galoisCoverComparison_snd_eq_firstMap {G : Type v} [Group G] [Finite G]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (a : Gᵐᵒᵖ →* Aut (Over.mk f)) :
    galoisCoverComparison f a ≫ pullback.snd f f = galoisTripleFirstMap f a :=
  Sigma.hom_ext _ _ fun σ ↦ by simp [galoisTripleFirstMap, galoisCoverComparison_ι_snd]

/-- The first leg of the Galois cover comparison is `Stacks.Descent.galoisTripleSecondMap`. -/
theorem galoisCoverComparison_fst_eq_secondMap {G : Type v} [Group G] [Finite G]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (a : Gᵐᵒᵖ →* Aut (Over.mk f)) :
    galoisCoverComparison f a ≫ pullback.fst f f = galoisTripleSecondMap f a :=
  Sigma.hom_ext _ _ fun σ ↦ by simp [galoisTripleSecondMap, galoisCoverComparison_ι_fst]

/-- The inverse of the projection `X ×_{f_σ, 𝟙} X ⟶ X`, an isomorphism. -/
def galoisTripleFiberMap {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : Gᵐᵒᵖ →* Aut (Over.mk f)) (σ _τ : G) :
    X ⟶ pullback (GaloisDescentData.twist G f a σ) (𝟙 X) :=
  (asIso (pullback.fst (GaloisDescentData.twist G f a σ) (𝟙 X))).inv

/-- The comparison `∐_{(σ, τ) : G × G} X ⟶ X ×_Y X ×_Y X` whose `(σ, τ)` summand has legs
`𝟙`, `f_σ` and `f_(στ)`. -/
def galoisTripleComparison {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : Gᵐᵒᵖ →* Aut (Over.mk f)) [IsIso (galoisCoverComparison f a)] :
    (∐ fun _ : G × G ↦ X) ⟶ (galoisChosenPullback₃ f).pullback := by
  let c12 : (∐ fun _ : G ↦ X) ⟶ X := galoisTripleFirstMap f a
  let c23 : (∐ fun _ : G ↦ X) ⟶ X := galoisTripleSecondMap f a
  let u : (∐ fun _ : G × G ↦ X) ⟶
      (∐ fun p : G × G ↦ pullback (GaloisDescentData.twist G f a p.1) (𝟙 X)) :=
    Limits.Sigma.map fun p ↦ galoisTripleFiberMap f a p.1 p.2
  let s : (∐ fun p : G × G ↦ pullback (GaloisDescentData.twist G f a p.1) (𝟙 X)) ⟶
      pullback c12 c23 :=
    Sigma.desc fun p ↦ pullback.map (GaloisDescentData.twist G f a p.1) (𝟙 X) c12 c23
      (Sigma.ι (fun _ : G ↦ X) p.1) (Sigma.ι (fun _ : G ↦ X) p.2) (𝟙 X)
      (by simp [c12, galoisTripleFirstMap]) (by simp [c23, galoisTripleSecondMap])
  let v : pullback c12 c23 ⟶ (galoisChosenPullback₃ f).pullback :=
    pullback.map c12 c23 (pullback.snd f f) (pullback.fst f f)
      (galoisCoverComparison f a) (galoisCoverComparison f a) (𝟙 X)
      (by
        change galoisTripleFirstMap f a ≫ 𝟙 X = galoisCoverComparison f a ≫ pullback.snd f f
        rw [galoisCoverComparison_snd_eq_firstMap]
        simp)
      (by
        change galoisTripleSecondMap f a ≫ 𝟙 X = galoisCoverComparison f a ≫ pullback.fst f f
        rw [galoisCoverComparison_fst_eq_secondMap]
        simp)
  exact u ≫ s ≫ v

/-- **The triple-product decomposition.**  If the action identifies `∐_{σ : G} X` with `X ×_Y X`,
then `∐_{(σ, τ) : G × G} X` is identified with `X ×_Y X ×_Y X`. -/
theorem galoisTripleComparison_isIso {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : Gᵐᵒᵖ →* Aut (Over.mk f)) [IsIso (galoisCoverComparison f a)] :
    IsIso (galoisTripleComparison f a) := by
  classical
  have : Small.{u} G := Countable.toSmall G
  have : Small.{u} (G × G) := Countable.toSmall (G × G)
  unfold galoisTripleComparison
  refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ ?_)
  · dsimp [galoisTripleFiberMap]
    exact (Limits.Sigma.mapIso (fun p : G × G ↦
      (asIso (pullback.fst (GaloisDescentData.twist G f a p.1) (𝟙 X))).symm)).isIso_hom
  · exact FinitaryPreExtensive.isIso_sigmaDesc_map
      (fun σ : G ↦ GaloisDescentData.twist G f a σ) (fun _ : G ↦ 𝟙 X)
  · exact pullback.map_isIso _ _ _ _ _ _ _ _ _

end Stacks.Descent

end

end
