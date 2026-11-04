module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.GaloisEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldPointGaloisDescent
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleGaloisAction
public import StacksFrontier.FieldTheory.GaloisTensorProduct
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Galois descent for quasi-coherent modules along a finite Galois field extension

Let `K/k` be a finite Galois extension with group `G = K ≃ₐ[k] K` and let `X` be a scheme over
`k`.  The projection `X_K = X ×_{Spec k} Spec K ⟶ X` is a surjective finite étale morphism, the
automorphisms `f_σ = id_X × Spec σ` of `X_K` form an action of `Gᵐᵒᵖ` over `X`, and that action
identifies `∐_{σ : G} X_K` with `X_K ×_X X_K`.  Galois descent for quasi-coherent modules
along `X_K ⟶ X` (Stacks 0CDR) is the case of Stacks 0D1V for this action.

## Main definitions

* `Stacks.Descent.actionOverAut` turns an action of a group on an object `V` of a category, all
  of whose automorphisms commute with a fixed morphism `V ⟶ Y`, into an action of the group on
  `V` read as an object over `Y`.
* `Stacks.Descent.baseChangeProjection` is the projection `X_K ⟶ X`, and
  `Stacks.Descent.baseChangeOverAction` is the action of `Gᵐᵒᵖ` on it over `X`.
* `Stacks.Descent.specGaloisOverAction` is the same action for `X = Spec k`, that is the action
  of `Gᵐᵒᵖ` on `Spec K` over `Spec k` by the automorphisms `Spec σ`.
* `Stacks.Descent.baseChangeSigmaMap`, an isomorphism by
  `Stacks.Descent.baseChangeSigmaIso`, identifies the coproduct of the copies of `X ×_S T`
  indexed by a finite type with the fibre product of `X` and the coproduct of the copies of `T`,
  and `Stacks.Descent.selfPullbackFstIso` identifies the self-fibre-product of the projection
  `X ×_S T ⟶ X` with the fibre product of `X` and `T ×_S T`.

## Main results

* `Stacks.Descent.isFinite_baseChangeProjection`,
  `Stacks.Descent.etale_baseChangeProjection` and
  `Stacks.Descent.surjective_baseChangeProjection`: the projection `X_K ⟶ X` is finite, étale
  and surjective, being the base change of `Spec K ⟶ Spec k`.
* `Stacks.Descent.isIso_galoisCoverComparison_spec`: the Galois cover comparison of
  `Spec K ⟶ Spec k` is an isomorphism.
* `Stacks.Descent.isIso_galoisCoverComparison_baseChange`: the Galois cover comparison of
  `X_K ⟶ X` is an isomorphism.
* `Stacks.Descent.nonempty_equivalence_galoisDescentData_baseChange`: quasi-coherent modules on
  `X` are equivalent to systems `(ℱ, (φ_σ))` on `X_K`.

## References

* [Stacks Project, Tag 0CDR](https://stacks.math.columbia.edu/tag/0CDR)
* [Stacks Project, Tag 0D1V](https://stacks.math.columbia.edu/tag/0D1V)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped TensorProduct

universe v u

namespace Stacks.Descent

/-! ### From an action on an object to an action on it as an object over a base -/

/-- An action of a group on an object `V` all of whose automorphisms commute with a morphism
`f : V ⟶ Y`, read as an action on `V` as an object over `Y`. -/
def actionOverAut {C : Type u} [Category.{v} C] {G : Type*} [Group G] (act : Action C G)
    {Y : C} (f : act.V ⟶ Y) (hf : ∀ g, act.ρ g ≫ f = f) : G →* Aut (Over.mk f) where
  toFun g := Over.isoMk
    { hom := act.ρ g
      inv := act.ρ g⁻¹
      hom_inv_id := by simpa [End.mul_def] using (act.ρ.map_mul g⁻¹ g).symm
      inv_hom_id := by simpa [End.mul_def] using (act.ρ.map_mul g g⁻¹).symm }
    (hf g)
  map_one' := Aut.ext (Over.OverMorphism.ext act.ρ.map_one)
  map_mul' g h := by
    apply Aut.ext
    apply Over.OverMorphism.ext
    change act.ρ (g * h) = act.ρ h ≫ act.ρ g
    simp [End.mul_def]

/-- The automorphism of `Over.mk f` attached to `g` has underlying morphism `act.ρ g`. -/
@[simp]
lemma actionOverAut_hom_left {C : Type u} [Category.{v} C] {G : Type*} [Group G]
    (act : Action C G) {Y : C} (f : act.V ⟶ Y) (hf : ∀ g, act.ρ g ≫ f = f) (g : G) :
    (actionOverAut act f hf g).hom.left = act.ρ g := rfl

/-- On the summand indexed by `σ`, the Galois cover comparison is the lift of `𝟙 X` and the
twist by `σ`. -/
@[reassoc]
private alias galoisCoverComparison_summand := galoisCoverComparison_ι

/-! ### Rearranging the two fibre products -/

/-- The coproduct of one copy of `X` is `X`. -/
def punitSigmaIso {X : Scheme.{u}} : (∐ fun _ : PUnit.{1} ↦ X) ≅ X where
  hom := Sigma.desc fun _ ↦ 𝟙 X
  inv := Sigma.ι (fun _ : PUnit.{1} ↦ X) PUnit.unit
  hom_inv_id := by
    apply Sigma.hom_ext
    rintro ⟨⟩
    simp
  inv_hom_id := by simp

/-- The isomorphism `punitSigmaIso` restricts to the identity on the unique summand. -/
@[simp]
lemma punitSigmaIso_ι_hom {X : Scheme.{u}} (i : PUnit.{1}) :
    Sigma.ι (fun _ : PUnit.{1} ↦ X) i ≫ punitSigmaIso.hom = 𝟙 X := by
  simp [punitSigmaIso]

variable {G : Type u} [Finite G] {S X T : Scheme.{u}}

/-- The canonical map from the coproduct of the copies of `X ×_S T` indexed by `G` to the fibre
product of `X` and the coproduct of the copies of `T`: on the summand indexed by `σ` it is the
identity in the `X` coordinate and the inclusion of the `σ`-th summand in the other. -/
def baseChangeSigmaMap (f : X ⟶ S) (g : T ⟶ S) :
    (∐ fun _ : G ↦ pullback f g) ⟶ pullback f (Sigma.desc fun _ : G ↦ g) :=
  Sigma.desc fun σ ↦ pullback.map f g f (Sigma.desc fun _ : G ↦ g) (𝟙 X)
    (Sigma.ι (fun _ : G ↦ T) σ) (𝟙 S) (by simp) (by simp)

omit [Finite G] in
/-- On the summand indexed by `σ`, the map `baseChangeSigmaMap` followed by the first
projection is the first projection of `X ×_S T`. -/
@[simp]
lemma baseChangeSigmaMap_ι_fst (f : X ⟶ S) (g : T ⟶ S) (σ : G) :
    Sigma.ι (fun _ : G ↦ pullback f g) σ ≫ baseChangeSigmaMap (G := G) f g ≫
        pullback.fst f (Sigma.desc fun _ : G ↦ g) = pullback.fst f g := by
  rw [← Category.assoc, baseChangeSigmaMap, Sigma.ι_desc, pullback.lift_fst, Category.comp_id]

omit [Finite G] in
/-- On the summand indexed by `σ`, the map `baseChangeSigmaMap` followed by the second
projection is the second projection of `X ×_S T` followed by the inclusion of the `σ`-th
summand. -/
@[simp]
lemma baseChangeSigmaMap_ι_snd (f : X ⟶ S) (g : T ⟶ S) (σ : G) :
    Sigma.ι (fun _ : G ↦ pullback f g) σ ≫ baseChangeSigmaMap (G := G) f g ≫
        pullback.snd f (Sigma.desc fun _ : G ↦ g) =
      pullback.snd f g ≫ Sigma.ι (fun _ : G ↦ T) σ := by
  rw [← Category.assoc, baseChangeSigmaMap, Sigma.ι_desc, pullback.lift_snd]

/-- **Base change commutes with a finite coproduct.**  The map
`Stacks.Descent.baseChangeSigmaMap` is an isomorphism. -/
instance isIso_baseChangeSigmaMap (f : X ⟶ S) (g : T ⟶ S) :
    IsIso (baseChangeSigmaMap (G := G) f g) := by
  classical
  let fU : PUnit.{1} → Scheme.{u} := fun _ ↦ X
  let gG : G → Scheme.{u} := fun _ ↦ T
  let fUmap : ∀ i, fU i ⟶ S := fun _ ↦ f
  let gGmap : ∀ i, gG i ⟶ S := fun _ ↦ g
  let eReindex : (∐ fun _ : G ↦ pullback f g) ≅ (∐ fun _ : PUnit.{1} × G ↦ pullback f g) :=
    Sigma.whiskerEquiv (Equiv.punitProd G).symm fun _ ↦ Iso.refl (pullback f g)
  let c : (∐ fun _ : PUnit.{1} × G ↦ pullback f g) ⟶
      pullback (Sigma.desc fUmap) (Sigma.desc gGmap) :=
    Sigma.desc fun p ↦ pullback.map f g (Sigma.desc fUmap) (Sigma.desc gGmap)
      (Sigma.ι fU p.1) (Sigma.ι gG p.2) (𝟙 S) (by simp [fUmap]) (by simp [gGmap])
  have hc : IsIso c := by
    dsimp only [c, fUmap, gGmap]
    infer_instance
  let a : pullback (Sigma.desc fUmap) (Sigma.desc gGmap) ⟶ pullback f (Sigma.desc gGmap) :=
    pullback.map (Sigma.desc fUmap) (Sigma.desc gGmap) f (Sigma.desc gGmap)
      punitSigmaIso.hom (𝟙 _) (𝟙 _)
      (by
        apply Sigma.hom_ext
        rintro ⟨⟩
        simp [fU, fUmap, punitSigmaIso])
      (by simp)
  have ha : IsIso a := by
    dsimp only [a]
    infer_instance
  have hι (σ : G) : Sigma.ι (fun _ : G ↦ pullback f g) σ ≫ eReindex.hom =
      Sigma.ι (fun _ : PUnit.{1} × G ↦ pullback f g) ((Equiv.punitProd G).symm σ) := by
    dsimp only [eReindex]
    rw [Sigma.whiskerEquiv_hom, Sigma.ι_comp_map', Iso.refl_inv, Category.id_comp]
  have hfac : baseChangeSigmaMap (G := G) f g = eReindex.hom ≫ c ≫ a := by
    apply Sigma.hom_ext
    intro σ
    apply pullback.hom_ext
    · rw [Category.assoc, baseChangeSigmaMap_ι_fst, ← Category.assoc, ← Category.assoc, hι]
      dsimp only [c, a]
      simp [fU, fUmap, gG, gGmap, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc]
    · rw [Category.assoc, baseChangeSigmaMap_ι_snd, ← Category.assoc, ← Category.assoc, hι]
      dsimp only [c, a]
      simp [fU, fUmap, gG, gGmap, pullback.map, pullback.lift_snd]
  rw [hfac]
  infer_instance

/-- **Base change commutes with a finite coproduct.** -/
def baseChangeSigmaIso (f : X ⟶ S) (g : T ⟶ S) :
    (∐ fun _ : G ↦ pullback f g) ≅ pullback f (Sigma.desc fun _ : G ↦ g) :=
  asIso (baseChangeSigmaMap (G := G) f g)

/-- The forward map of `baseChangeSigmaIso` is `baseChangeSigmaMap`. -/
@[simp]
lemma baseChangeSigmaIso_hom (f : X ⟶ S) (g : T ⟶ S) :
    (baseChangeSigmaIso (G := G) f g).hom = baseChangeSigmaMap (G := G) f g := rfl

/-- The self-fibre-product of a projection `X ×_S T ⟶ X` is the fibre product of `X` and
`T ×_S T` over `S`. -/
def selfPullbackFstIso (f : X ⟶ S) (g : T ⟶ S) :
    pullback (pullback.fst f g) (pullback.fst f g) ≅ pullback f (pullback.fst g g ≫ g) :=
  pullbackRightPullbackFstIso f g (pullback.fst f g) ≪≫
    pullback.congrHom pullback.condition rfl ≪≫ pullbackAssoc f g g g

/-- The first projection of `Stacks.Descent.selfPullbackFstIso`. -/
lemma selfPullbackFstIso_hom_fst (f : X ⟶ S) (g : T ⟶ S) :
    (selfPullbackFstIso f g).hom ≫ pullback.fst f (pullback.fst g g ≫ g) =
      pullback.fst (pullback.fst f g) (pullback.fst f g) ≫ pullback.fst f g := by
  simp only [selfPullbackFstIso, Iso.trans_hom, Category.assoc, pullbackAssoc_hom_fst,
    pullback.congrHom_hom, pullback.map, pullback.lift_fst_assoc, Category.comp_id,
    pullbackRightPullbackFstIso_hom_fst_assoc]

/-- The `T ×_S T`-component of `Stacks.Descent.selfPullbackFstIso`, followed by the first
projection. -/
lemma selfPullbackFstIso_hom_snd_fst (f : X ⟶ S) (g : T ⟶ S) :
    (selfPullbackFstIso f g).hom ≫ pullback.snd f (pullback.fst g g ≫ g) ≫
        pullback.fst g g =
      pullback.fst (pullback.fst f g) (pullback.fst f g) ≫ pullback.snd f g := by
  simp only [selfPullbackFstIso, Iso.trans_hom, Category.assoc, pullbackAssoc_hom_snd_fst,
    pullback.congrHom_hom, pullback.map, pullback.lift_fst_assoc, Category.comp_id,
    pullbackRightPullbackFstIso_hom_fst_assoc]

/-- The `T ×_S T`-component of `Stacks.Descent.selfPullbackFstIso`, followed by the second
projection. -/
lemma selfPullbackFstIso_hom_snd_snd (f : X ⟶ S) (g : T ⟶ S) :
    (selfPullbackFstIso f g).hom ≫ pullback.snd f (pullback.fst g g ≫ g) ≫
        pullback.snd g g =
      pullback.snd (pullback.fst f g) (pullback.fst f g) ≫ pullback.snd f g := by
  simp only [selfPullbackFstIso, Iso.trans_hom, Category.assoc, pullbackAssoc_hom_snd_snd,
    pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id,
    pullbackRightPullbackFstIso_hom_snd]

/-! ### The Galois action on `Spec K` over `Spec k` -/

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- The morphism `Spec K ⟶ Spec k` attached to a field extension. -/
abbrev specOfExtension : Spec (.of K) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

/-- The action of the opposite of the `k`-algebra automorphism group of `K` on `Spec K` by the
morphisms `Spec σ`.  The group is the opposite one because `Spec` is contravariant. -/
def specGaloisAction : Action Scheme.{u} (K ≃ₐ[k] K)ᵐᵒᵖ where
  V := Spec (.of K)
  ρ :=
    { toFun := fun σ ↦ specMapAlgAut k K σ.unop
      map_one' := by simp
      map_mul' := fun σ τ ↦ by
        change specMapAlgAut k K (τ.unop * σ.unop) =
          specMapAlgAut k K τ.unop ≫ specMapAlgAut k K σ.unop
        exact specMapAlgAut_mul k K τ.unop σ.unop }

/-- The Galois action on `Spec K` as an action over `Spec k`: each `Spec σ` lies over `Spec k`
because `σ` is a `k`-algebra map. -/
def specGaloisOverAction : (K ≃ₐ[k] K)ᵐᵒᵖ →* Aut (Over.mk (specOfExtension k K)) :=
  actionOverAut (specGaloisAction k K) (specOfExtension k K)
    fun σ ↦ specMapAlgAut_comp_structureMap k K σ.unop

/-- The automorphism of `Spec K` over `Spec k` attached to `σ` has underlying morphism
`Spec σ`. -/
@[simp]
lemma specGaloisOverAction_hom_left (σ : K ≃ₐ[k] K) :
    (specGaloisOverAction k K (.op σ)).hom.left = specMapAlgAut k K σ := rfl

/-! ### The Galois situation of a base change -/

variable (Z : Over (Spec (.of k)))

/-- The projection `X_K ⟶ X` of the base change of a `k`-scheme to a field extension. -/
abbrev baseChangeProjection : SchemeOver.baseChange k K Z ⟶ Z.left :=
  pullback.fst Z.hom (specOfExtension k K)

/-- A twist `id_X × Spec σ` does not move the projection `X_K ⟶ X`. -/
lemma baseChangeAction_comp_fst (σ : (K ≃ₐ[k] K)ᵐᵒᵖ) :
    (galoisActionOnBaseChange k K Z).ρ σ ≫ baseChangeProjection k K Z =
      baseChangeProjection k K Z := by
  dsimp [galoisActionOnBaseChange, SchemeOver.baseChange]
  simp [pullback.map, pullback.lift_fst]

/-- A twist `id_X × Spec σ` acts on the `Spec K` coordinate by `Spec σ`. -/
lemma baseChangeAction_comp_snd (σ : (K ≃ₐ[k] K)ᵐᵒᵖ) :
    (galoisActionOnBaseChange k K Z).ρ σ ≫ pullback.snd Z.hom (specOfExtension k K) =
      pullback.snd Z.hom (specOfExtension k K) ≫ specMapAlgAut k K σ.unop := by
  dsimp [galoisActionOnBaseChange, SchemeOver.baseChange]
  simp only [pullback.map, Category.comp_id, pullback.lift_snd]

/-- The action of `Gᵐᵒᵖ` on the base change `X_K`, read as an action over `X`. -/
def baseChangeOverAction :
    (K ≃ₐ[k] K)ᵐᵒᵖ →* Aut (Over.mk (baseChangeProjection k K Z)) :=
  actionOverAut (galoisActionOnBaseChange k K Z) (baseChangeProjection k K Z)
    (baseChangeAction_comp_fst k K Z)

/-- The automorphism of `X_K` over `X` attached to `σ` has underlying morphism the twist
`id_X × Spec σ`. -/
@[simp]
lemma baseChangeOverAction_hom_left (σ : (K ≃ₐ[k] K)ᵐᵒᵖ) :
    (baseChangeOverAction k K Z σ).hom.left = (galoisActionOnBaseChange k K Z).ρ σ := rfl

/-- The projection `X_K ⟶ X` is surjective. -/
lemma surjective_baseChangeProjection : Surjective (baseChangeProjection k K Z) := by
  have : Surjective (specOfExtension k K) := inferInstance
  infer_instance

/-! ### The two legs of the Galois cover comparison over the base field -/

variable [FiniteDimensional k K]

/-- The projection `X_K ⟶ X` is finite when `K/k` is finite. -/
lemma isFinite_baseChangeProjection : IsFinite (baseChangeProjection k K Z) := by
  have : IsFinite (specOfExtension k K) := by
    rw [show specOfExtension k K = Spec.map (CommRingCat.ofHom (algebraMap k K)) from rfl,
      IsFinite.SpecMap_iff]
    simpa only [CommRingCat.hom_ofHom, RingHom.finite_algebraMap] using
      (inferInstance : Module.Finite k K)
  infer_instance

/-- The Galois cover comparison of `Spec K ⟶ Spec k` followed by the first projection is the
identity on every summand. -/
lemma galoisCoverComparison_spec_comp_fst :
    galoisCoverComparison (specOfExtension k K) (specGaloisOverAction k K) ≫
        pullback.fst (specOfExtension k K) (specOfExtension k K) =
      Sigma.desc fun _ : K ≃ₐ[k] K ↦ 𝟙 (Spec (.of K)) := by
  classical
  exact Sigma.hom_ext _ _ fun σ ↦ by rw [Sigma.ι_desc, galoisCoverComparison_ι_fst]

/-- The Galois cover comparison of `Spec K ⟶ Spec k` followed by the second projection is
`Spec σ` on the summand indexed by `σ`. -/
lemma galoisCoverComparison_spec_comp_snd :
    galoisCoverComparison (specOfExtension k K) (specGaloisOverAction k K) ≫
        pullback.snd (specOfExtension k K) (specOfExtension k K) =
      Sigma.desc fun σ : K ≃ₐ[k] K ↦ specMapAlgAut k K σ := by
  classical
  apply Sigma.hom_ext
  intro σ
  rw [Sigma.ι_desc, galoisCoverComparison_ι_snd]
  rfl

/-- The Galois cover comparison over the base field, composed with the projection, is the map
which is `Spec K ⟶ Spec k` on every summand. -/
lemma galoisCoverComparison_spec_comp_fst_comp :
    galoisCoverComparison (specOfExtension k K) (specGaloisOverAction k K) ≫
        (pullback.fst (specOfExtension k K) (specOfExtension k K) ≫ specOfExtension k K) =
      Sigma.desc fun _ : K ≃ₐ[k] K ↦ specOfExtension k K := by
  classical
  rw [← Category.assoc, galoisCoverComparison_spec_comp_fst]
  apply Sigma.hom_ext
  intro σ
  simp

/-! ### The Galois cover comparison over the base field -/

variable [IsGalois k K]

/-- The projection `X_K ⟶ X` is étale when `K/k` is finite Galois. -/
lemma etale_baseChangeProjection : Etale (baseChangeProjection k K Z) := by
  have : Etale (specOfExtension k K) := etale_specMap_algebraMap k K
  infer_instance

/-- The Galois cover comparison of `Spec K ⟶ Spec k`, composed with the identification of
`Spec K ×_{Spec k} Spec K` with `Spec (K ⊗[k] K)`, is `AlgebraicGeometry.sigmaSpec` followed by
the spectrum of `IsGalois.tensorProductEquivPi`. -/
lemma galoisCoverComparison_spec_comp_pullbackSpecIso :
    galoisCoverComparison (specOfExtension k K) (specGaloisOverAction k K) ≫
        (pullbackSpecIso k K K).hom =
      sigmaSpec (fun _ : K ≃ₐ[k] K ↦ CommRingCat.of K) ≫
        Spec.map (CommRingCat.ofHom
          (IsGalois.tensorProductEquivPi k K).toRingEquiv.toRingHom) := by
  classical
  ext σ
  let e := pullbackSpecIso k K K
  let ev := IsGalois.tensorEvalAlgHom (k := k) (K := K) σ
  let c : Spec (.of K) ⟶ pullback (specOfExtension k K) (specOfExtension k K) :=
    pullback.lift (𝟙 (Spec (.of K))) (specMapAlgAut k K σ) (by simp)
  have hl : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[k] K) ≫
      CommRingCat.ofHom ev.toRingHom = 𝟙 (CommRingCat.of K) := by
    ext x
    simp [ev]
  have hr : CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : K →+* K ⊗[k] K) ≫
      CommRingCat.ofHom ev.toRingHom = CommRingCat.ofHom σ.toRingEquiv.toRingHom := by
    ext x
    simp [ev]
  have hc : c = Spec.map (CommRingCat.ofHom ev.toRingHom) ≫ e.inv := by
    apply pullback.hom_ext
    · dsimp only [c]
      rw [pullback.lift_fst, Category.assoc]
      dsimp only [e]
      rw [pullbackSpecIso_inv_fst]
      simpa using (congrArg Spec.map hl).symm
    · dsimp only [c]
      rw [pullback.lift_snd, Category.assoc]
      dsimp only [e]
      rw [pullbackSpecIso_inv_snd]
      simpa [specMapAlgAut] using (congrArg Spec.map hr).symm
  calc
    _ = c ≫ e.hom := by
        have hcmp : Sigma.ι _ σ ≫
            galoisCoverComparison (specOfExtension k K) (specGaloisOverAction k K) = c := by
          rw [galoisCoverComparison_ι]
          dsimp only [c]
          congr 1
        rw [← Category.assoc, hcmp]
    _ = (Spec.map (CommRingCat.ofHom ev.toRingHom) ≫ e.inv) ≫ e.hom := by rw [hc]
    _ = Spec.map (CommRingCat.ofHom ev.toRingHom) := by simp [e]
    _ = Sigma.ι _ σ ≫ (sigmaSpec (fun _ : K ≃ₐ[k] K ↦ CommRingCat.of K) ≫
          Spec.map (CommRingCat.ofHom
            (IsGalois.tensorProductEquivPi k K).toRingEquiv.toRingHom)) := by
      rw [← Category.assoc, ι_sigmaSpec, ← Spec.map_comp, Spec.map_inj]
      ext x
      all_goals simp [ev]

/-- The Galois cover comparison of `Spec K ⟶ Spec k` is an isomorphism. -/
@[sga "7 XIII 1.1.3" "partial"]
lemma isIso_galoisCoverComparison_spec :
    IsIso (galoisCoverComparison (specOfExtension k K) (specGaloisOverAction k K)) := by
  classical
  have : IsIso (Spec.map (CommRingCat.ofHom
      (IsGalois.tensorProductEquivPi k K).toRingEquiv.toRingHom)) := by
    show IsIso (Spec.map
      (RingEquiv.toCommRingCatIso (IsGalois.tensorProductEquivPi k K).toRingEquiv).hom)
    infer_instance
  have : IsIso (galoisCoverComparison (specOfExtension k K) (specGaloisOverAction k K) ≫
      (pullbackSpecIso k K K).hom) := by
    rw [galoisCoverComparison_spec_comp_pullbackSpecIso]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (pullbackSpecIso k K K).hom

/-! ### Transporting the comparison to an arbitrary base -/

/-- The base change along `X ⟶ Spec k` of the Galois cover comparison of
`Spec K ⟶ Spec k`. -/
def baseChangeCoverComparisonMap :
    pullback Z.hom (Sigma.desc fun _ : K ≃ₐ[k] K ↦ specOfExtension k K) ⟶
      pullback Z.hom (pullback.fst (specOfExtension k K) (specOfExtension k K) ≫
        specOfExtension k K) :=
  pullback.map Z.hom (Sigma.desc fun _ : K ≃ₐ[k] K ↦ specOfExtension k K) Z.hom
    (pullback.fst (specOfExtension k K) (specOfExtension k K) ≫ specOfExtension k K)
    (𝟙 Z.left) (galoisCoverComparison (specOfExtension k K) (specGaloisOverAction k K))
    (𝟙 (Spec (.of k))) (Category.comp_id Z.hom)
    (by rw [Category.comp_id]; exact (galoisCoverComparison_spec_comp_fst_comp k K).symm)

/-- The base change of the Galois cover comparison of `Spec K ⟶ Spec k` is an isomorphism. -/
instance isIso_baseChangeCoverComparisonMap :
    IsIso (baseChangeCoverComparisonMap k K Z) := by
  have : IsIso (galoisCoverComparison (specOfExtension k K) (specGaloisOverAction k K)) :=
    isIso_galoisCoverComparison_spec k K
  dsimp only [baseChangeCoverComparisonMap]
  apply pullback.map_isIso

omit [IsGalois k K] in
/-- For an action `b` of `Gᵐᵒᵖ` on `X_K` over `X` whose automorphisms are those of
`AlgebraicGeometry.galoisActionOnBaseChange`, the Galois cover comparison of `X_K ⟶ X` followed
by `Stacks.Descent.selfPullbackFstIso` equals `Stacks.Descent.baseChangeSigmaMap` followed by the
base change of the Galois cover comparison of `Spec K ⟶ Spec k`. -/
lemma galoisCoverComparison_baseChange_comp_selfPullbackFstIso
    (b : (K ≃ₐ[k] K)ᵐᵒᵖ →* Aut (Over.mk (baseChangeProjection k K Z)))
    (hb : ∀ σ : K ≃ₐ[k] K,
      (b (.op σ)).hom.left = (galoisActionOnBaseChange k K Z).ρ (.op σ)) :
    galoisCoverComparison (baseChangeProjection k K Z) b ≫
        (selfPullbackFstIso Z.hom (specOfExtension k K)).hom =
      baseChangeSigmaMap (G := K ≃ₐ[k] K) Z.hom (specOfExtension k K) ≫
        baseChangeCoverComparisonMap k K Z := by
  classical
  have hcBase_fst : baseChangeCoverComparisonMap k K Z ≫
      pullback.fst Z.hom (pullback.fst (specOfExtension k K) (specOfExtension k K) ≫
        specOfExtension k K) =
      pullback.fst Z.hom (Sigma.desc fun _ : K ≃ₐ[k] K ↦ specOfExtension k K) := by
    dsimp only [baseChangeCoverComparisonMap, pullback.map]
    rw [pullback.lift_fst, Category.comp_id]
  have hcBase_snd : baseChangeCoverComparisonMap k K Z ≫
      pullback.snd Z.hom (pullback.fst (specOfExtension k K) (specOfExtension k K) ≫
        specOfExtension k K) =
      pullback.snd Z.hom (Sigma.desc fun _ : K ≃ₐ[k] K ↦ specOfExtension k K) ≫
        galoisCoverComparison (specOfExtension k K) (specGaloisOverAction k K) := by
    dsimp only [baseChangeCoverComparisonMap, pullback.map]
    rw [pullback.lift_snd]
  apply Sigma.hom_ext
  intro σ
  have hAfst := reassoc_of% galoisCoverComparison_ι_fst (baseChangeProjection k K Z) b σ
  have hAsnd := reassoc_of%
    ((galoisCoverComparison_ι_snd (baseChangeProjection k K Z) b σ).trans (hb σ))
  have hBfst : Sigma.ι (fun _ : K ≃ₐ[k] K ↦ SchemeOver.baseChange k K Z) σ ≫
      baseChangeSigmaMap (G := K ≃ₐ[k] K) Z.hom (specOfExtension k K) ≫
        pullback.fst Z.hom (Sigma.desc fun _ : K ≃ₐ[k] K ↦ specOfExtension k K) =
      pullback.fst Z.hom (specOfExtension k K) :=
    baseChangeSigmaMap_ι_fst (G := K ≃ₐ[k] K) Z.hom (specOfExtension k K) σ
  have hBsnd : Sigma.ι (fun _ : K ≃ₐ[k] K ↦ SchemeOver.baseChange k K Z) σ ≫
      baseChangeSigmaMap (G := K ≃ₐ[k] K) Z.hom (specOfExtension k K) ≫
        pullback.snd Z.hom (Sigma.desc fun _ : K ≃ₐ[k] K ↦ specOfExtension k K) =
      pullback.snd Z.hom (specOfExtension k K) ≫
        Sigma.ι (fun _ : K ≃ₐ[k] K ↦ Spec (.of K)) σ :=
    baseChangeSigmaMap_ι_snd (G := K ≃ₐ[k] K) Z.hom (specOfExtension k K) σ
  replace hBsnd := reassoc_of% hBsnd
  have hCfst :=
    galoisCoverComparison_ι_fst (specOfExtension k K) (specGaloisOverAction k K) σ
  have hCsnd :=
    galoisCoverComparison_ι_snd (specOfExtension k K) (specGaloisOverAction k K) σ
  have hD := baseChangeAction_comp_snd k K Z (.op σ)
  apply pullback.hom_ext
  · simp only [Category.assoc, selfPullbackFstIso_hom_fst, hcBase_fst, hAfst, hBfst]
  · apply pullback.hom_ext
    · simp only [Category.assoc, selfPullbackFstIso_hom_snd_fst, hcBase_snd, hAfst, hBsnd, hCfst,
        Category.comp_id]
    · simp only [Category.assoc, selfPullbackFstIso_hom_snd_snd, hcBase_snd, hAsnd, hBsnd, hCsnd,
        hD]
      rfl

/-- The Galois cover comparison of `X_K ⟶ X` is an isomorphism. -/
lemma isIso_galoisCoverComparison_baseChange :
    IsIso (galoisCoverComparison (baseChangeProjection k K Z) (baseChangeOverAction k K Z)) := by
  classical
  have : IsIso (galoisCoverComparison (baseChangeProjection k K Z)
      (baseChangeOverAction k K Z) ≫
      (selfPullbackFstIso Z.hom (specOfExtension k K)).hom) := by
    rw [galoisCoverComparison_baseChange_comp_selfPullbackFstIso k K Z _ fun _ ↦ rfl]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (selfPullbackFstIso Z.hom (specOfExtension k K)).hom

/-- **Galois descent for quasi-coherent modules.**  For a finite Galois extension `K/k` with
group `G` and a scheme `X` over `k`, the category of quasi-coherent `𝒪_X`-modules is equivalent
to the category of systems `(ℱ, (φ_σ)_{σ ∈ G})` where `ℱ` is quasi-coherent on `X_K`, each
`φ_σ : ℱ ≅ f_σ^* ℱ` is an isomorphism, and `φ_(στ) = f_σ^*(φ_τ) ∘ φ_σ`.  Here
`f_σ = id_X × Spec σ`. -/
@[stacks 0CDR]
theorem nonempty_equivalence_galoisDescentData_baseChange :
    Nonempty ((SheafOfModules.isQuasicoherent Z.left.ringCatSheaf).FullSubcategory ≌
      GaloisDescentData (K ≃ₐ[k] K) (baseChangeProjection k K Z)
        (baseChangeOverAction k K Z)) := by
  have := isFinite_baseChangeProjection k K Z
  have := etale_baseChangeProjection k K Z
  have := surjective_baseChangeProjection k K Z
  have := isIso_galoisCoverComparison_baseChange k K Z
  exact nonempty_equivalence_galoisDescentData (baseChangeProjection k K Z)
    (baseChangeOverAction k K Z)

end Stacks.Descent

end

end
