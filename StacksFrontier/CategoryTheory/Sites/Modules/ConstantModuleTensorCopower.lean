module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantModuleTensor
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Algebra.Module.Projective

/-!
# The tensor product of a sheaf with a module as a copower

Let `S` be a sheaf of `Λ`-modules and `M` a `Λ`-module. The sheaf `S ⊗_Λ M` comes with maps
`ev m : S ⟶ S ⊗_Λ M` (`s ↦ m ⊗ s`) for `m ∈ M`, linear in `m`, and a morphism out of
`S ⊗_Λ M` is the same as a `Λ`-linear family of morphisms out of `S` indexed by `M`: `S ⊗_Λ M` is
the copower of `S` by `M` in the `Λ`-linear category of sheaves.

Consequently every `Λ`-linear functor `G` between categories of sheaves of `Λ`-modules comes with
a comparison `G(S) ⊗_Λ M ⟶ G(S ⊗_Λ M)`, natural in `S`, `M` and `G` and compatible with
composition of functors. It is an isomorphism when `M` is finitely generated projective: a dual
basis of `M` writes `S ⊗_Λ M` as a finite copower, which every additive functor preserves.

## Main definitions

* `Stacks.ConstantModuleTensor.ev`, `Stacks.ConstantModuleTensor.lift`: the copower structure.
* `Stacks.ConstantModuleTensor.comparison`: `G(S) ⊗_Λ M ⟶ G(S ⊗_Λ M)` for `Λ`-linear `G`.

## Main results

* `Stacks.ConstantModuleTensor.hom_ext`, `Stacks.ConstantModuleTensor.ev_lift`.
* `Stacks.ConstantModuleTensor.isIso_comparison`: the comparison is an isomorphism for `M`
  finitely generated projective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v₁ u₁ v₂ u₂ v₃ u₃

namespace Stacks.ConstantModuleTensor

section Copower

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) {Λ : Type w} [CommRing Λ]

/-- The presheaf map `S ⟶ M ⊗_Λ S`, `s ↦ m ⊗ s`. -/
@[simps]
def evPresheaf (S : Cᵒᵖ ⥤ ModuleCat.{w} Λ) {M : ModuleCat.{w} Λ} (m : M) :
    S ⟶ ((presheafTensor Λ).obj S).obj M where
  app U := ModuleCat.ofHom (TensorProduct.mk Λ M (S.obj U) m)
  naturality U V f := by
    ext s
    rfl

/-- The presheaf map `M ⊗_Λ S ⟶ T` of a `Λ`-linear family of maps `S ⟶ T` indexed by `M`. -/
@[simps]
def liftPresheaf {S T : Cᵒᵖ ⥤ ModuleCat.{w} Λ} {M : ModuleCat.{w} Λ} (h : M →ₗ[Λ] (S ⟶ T)) :
    ((presheafTensor Λ).obj S).obj M ⟶ T where
  app U := ModuleCat.ofHom (TensorProduct.lift
    { toFun m := ((h m).app U).hom
      map_add' m m' := by rw [map_add, NatTrans.app_add, ModuleCat.hom_add]
      map_smul' r m := by
        rw [map_smul, NatTrans.app_smul, ModuleCat.hom_smul]
        rfl })
  naturality U V f := by
    ext : 1
    refine TensorProduct.ext' fun m s => ?_
    change ((h m).app V).hom ((S.map f).hom s) = (T.map f).hom (((h m).app U).hom s)
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, (h m).naturality]

/-- The presheaf map `liftPresheaf h : M ⊗_Λ S ⟶ T` restricts along `evPresheaf S m` to `h m`. -/
theorem evPresheaf_liftPresheaf {S T : Cᵒᵖ ⥤ ModuleCat.{w} Λ} {M : ModuleCat.{w} Λ}
    (h : M →ₗ[Λ] (S ⟶ T)) (m : M) : evPresheaf S m ≫ liftPresheaf h = h m := by
  ext U s
  rfl

variable [HasSheafify J (ModuleCat.{w} Λ)]

/-- **The structure maps of the copower**: `ev m : S ⟶ S ⊗_Λ M`, `s ↦ m ⊗ s`. -/
def ev (S : Sheaf J (ModuleCat.{w} Λ)) {M : ModuleCat.{w} Λ} (m : M) :
    S ⟶ ((sheafTensor J Λ).obj S).obj M :=
  ObjectProperty.homMk (evPresheaf S.obj m ≫ toSheafify J _)

/-- **The universal property of the copower**: the morphism `S ⊗_Λ M ⟶ T` of a `Λ`-linear
family of morphisms `S ⟶ T` indexed by `M`. -/
def lift {S T : Sheaf J (ModuleCat.{w} Λ)} {M : ModuleCat.{w} Λ} (h : M →ₗ[Λ] (S ⟶ T)) :
    ((sheafTensor J Λ).obj S).obj M ⟶ T :=
  ((sheafificationAdjunction J _).homEquiv _ T).symm
    (liftPresheaf (((sheafToPresheaf J (ModuleCat.{w} Λ)).mapLinearMap Λ).comp h))

/-- The morphism `lift h : S ⊗_Λ M ⟶ T` restricts along `ev m` to `h m`. -/
@[reassoc (attr := simp)]
theorem ev_lift {S T : Sheaf J (ModuleCat.{w} Λ)} {M : ModuleCat.{w} Λ} (h : M →ₗ[Λ] (S ⟶ T))
    (m : M) : ev J S m ≫ lift J h = h m := by
  apply Sheaf.hom_ext
  have h₁ : toSheafify J _ ≫ (lift J h).hom =
      liftPresheaf (((sheafToPresheaf J (ModuleCat.{w} Λ)).mapLinearMap Λ).comp h) := by
    have := (sheafificationAdjunction J (ModuleCat.{w} Λ)).homEquiv_unit _ T (lift J h)
    rw [lift, Equiv.apply_symm_apply] at this
    exact this.symm
  change evPresheaf S.obj m ≫ (toSheafify J _ ≫ (lift J h).hom) = (h m).hom
  rw [h₁, evPresheaf_liftPresheaf]
  rfl

/-- Two morphisms `S ⊗_Λ M ⟶ T` are equal if they agree after composing with `ev m` for every
`m ∈ M`. -/
theorem hom_ext {S T : Sheaf J (ModuleCat.{w} Λ)} {M : ModuleCat.{w} Λ}
    {φ ψ : ((sheafTensor J Λ).obj S).obj M ⟶ T} (h : ∀ m : M, ev J S m ≫ φ = ev J S m ≫ ψ) :
    φ = ψ := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ T.property
  refine NatTrans.ext (funext fun U => ?_)
  refine ModuleCat.MonoidalCategory.tensor_ext (M₁ := M) (M₂ := S.obj.obj U)
    (f := (toSheafify J _ ≫ φ.hom).app U) (g := (toSheafify J _ ≫ ψ.hom).app U) fun m s => ?_
  exact congrArg (fun χ : S ⟶ T => (χ.hom.app U).hom s) (h m)

/-- `ev (m + m') = ev m + ev m'`. -/
@[simp]
theorem ev_add (S : Sheaf J (ModuleCat.{w} Λ)) {M : ModuleCat.{w} Λ} (m m' : M) :
    ev J S (m + m') = ev J S m + ev J S m' := by
  apply Sheaf.hom_ext
  change evPresheaf S.obj (m + m') ≫ toSheafify J _ =
    evPresheaf S.obj m ≫ toSheafify J _ + evPresheaf S.obj m' ≫ toSheafify J _
  rw [← Preadditive.add_comp]
  congr 1
  all_goals (ext U s; exact TensorProduct.add_tmul m m' s)

/-- `ev (r • m) = r • ev m`. -/
@[simp]
theorem ev_smul (S : Sheaf J (ModuleCat.{w} Λ)) {M : ModuleCat.{w} Λ} (r : Λ) (m : M) :
    ev J S (r • m) = r • ev J S m := by
  apply Sheaf.hom_ext
  change evPresheaf S.obj (r • m) ≫ toSheafify J _ = r • (evPresheaf S.obj m ≫ toSheafify J _)
  rw [← Linear.smul_comp]
  congr 1

/-- `ev` as a `Λ`-linear map. -/
@[simps]
def evLinearMap (S : Sheaf J (ModuleCat.{w} Λ)) (M : ModuleCat.{w} Λ) :
    M →ₗ[Λ] (S ⟶ ((sheafTensor J Λ).obj S).obj M) where
  toFun m := ev J S m
  map_add' := ev_add J S
  map_smul' := ev_smul J S

/-- Expanding `m` along a family `∑ i, f i m • x i = m` expands `ev m` accordingly. -/
theorem sum_smul_ev (S : Sheaf J (ModuleCat.{w} Λ)) {M : ModuleCat.{w} Λ} {n : ℕ}
    {x : Fin n → M} {f : Fin n → (M →ₗ[Λ] Λ)} (hf : ∀ m : M, ∑ i, f i m • x i = m) (m : M) :
    ∑ i, f i m • ev J S (x i) = ev J S m := by
  conv_rhs => rw [← hf m]
  rw [← evLinearMap_apply, map_sum]
  simp

/-- For `u : M ⟶ M'`, `ev m` followed by `S ⊗_Λ u` is `ev (u m)`. -/
@[reassoc (attr := simp)]
theorem ev_map_right (S : Sheaf J (ModuleCat.{w} Λ)) {M M' : ModuleCat.{w} Λ} (u : M ⟶ M')
    (m : M) : ev J S m ≫ ((sheafTensor J Λ).obj S).map u = ev J S (u m) := by
  apply Sheaf.hom_ext
  change (evPresheaf S.obj m ≫ toSheafify J _) ≫ sheafifyMap J _ =
    evPresheaf S.obj (u m) ≫ toSheafify J _
  rw [Category.assoc, ← toSheafify_naturality, ← Category.assoc]
  congr 1

/-- For `a : S ⟶ S'`, `ev m` followed by `a ⊗_Λ M` is `a ≫ ev m`. -/
@[reassoc (attr := simp)]
theorem ev_map_left {S S' : Sheaf J (ModuleCat.{w} Λ)} (a : S ⟶ S') {M : ModuleCat.{w} Λ}
    (m : M) : ev J S m ≫ ((sheafTensor J Λ).map a).app M = a ≫ ev J S' m := by
  apply Sheaf.hom_ext
  change (evPresheaf S.obj m ≫ toSheafify J _) ≫ sheafifyMap J _ =
    a.hom ≫ evPresheaf S'.obj m ≫ toSheafify J _
  rw [Category.assoc, ← toSheafify_naturality, ← Category.assoc, ← Category.assoc]
  congr 1

/-- A finitely generated projective `Λ`-module `M` has a finite dual basis: finitely many `x i ∈ M`
and linear forms `f i : M →ₗ[Λ] Λ` with `∑ i, f i m • x i = m` for all `m ∈ M`. -/
theorem exists_dualBasis (M : ModuleCat.{w} Λ) [Module.Finite Λ M] [Module.Projective Λ M] :
    ∃ (n : ℕ) (x : Fin n → M) (f : Fin n → (M →ₗ[Λ] Λ)), ∀ m : M, ∑ i, f i m • x i = m := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' Λ M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  refine ⟨n, fun i => π (Pi.single i 1), fun i => (LinearMap.proj i).comp s, fun m => ?_⟩
  conv_rhs => rw [← LinearMap.id_apply (R := Λ) m, ← hs, LinearMap.comp_apply,
    pi_eq_sum_univ (s m), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval]
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]

end Copower

section Comparison

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {C' : Type u₂} [Category.{v₂} C'] (J' : GrothendieckTopology C')
  {Λ : Type w} [CommRing Λ] [HasSheafify J (ModuleCat.{w} Λ)] [HasSheafify J' (ModuleCat.{w} Λ)]
  (G : Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf J' (ModuleCat.{w} Λ)) [G.Additive] [G.Linear Λ]

/-- **The comparison `G(S) ⊗_Λ M ⟶ G(S ⊗_Λ M)`** of a `Λ`-linear functor: `m ⊗ G(s) ↦ G(m ⊗ s)`,
i.e. the map out of the copower given by the family `G(ev m)`. -/
def comparison (S : Sheaf J (ModuleCat.{w} Λ)) (M : ModuleCat.{w} Λ) :
    ((sheafTensor J' Λ).obj (G.obj S)).obj M ⟶ G.obj (((sheafTensor J Λ).obj S).obj M) :=
  lift J' ((G.mapLinearMap Λ).comp (evLinearMap J S M))

/-- The comparison `G(S) ⊗_Λ M ⟶ G(S ⊗_Λ M)` restricts along `ev m` to `G(ev m)`. -/
@[reassoc (attr := simp)]
theorem ev_comparison (S : Sheaf J (ModuleCat.{w} Λ)) {M : ModuleCat.{w} Λ} (m : M) :
    ev J' (G.obj S) m ≫ comparison J J' G S M = G.map (ev J S m) := by
  rw [comparison, ev_lift]
  rfl

/-- The comparison is natural in the module. -/
@[reassoc]
theorem comparison_naturality_right (S : Sheaf J (ModuleCat.{w} Λ)) {M M' : ModuleCat.{w} Λ}
    (u : M ⟶ M') :
    ((sheafTensor J' Λ).obj (G.obj S)).map u ≫ comparison J J' G S M' =
      comparison J J' G S M ≫ G.map (((sheafTensor J Λ).obj S).map u) :=
  hom_ext J' fun m => by
    rw [ev_map_right_assoc, ev_comparison, ev_comparison_assoc, ← G.map_comp, ev_map_right]

/-- The comparison is natural in the sheaf. -/
@[reassoc]
theorem comparison_naturality_left {S S' : Sheaf J (ModuleCat.{w} Λ)} (a : S ⟶ S')
    (M : ModuleCat.{w} Λ) :
    ((sheafTensor J' Λ).map (G.map a)).app M ≫ comparison J J' G S' M =
      comparison J J' G S M ≫ G.map (((sheafTensor J Λ).map a).app M) :=
  hom_ext J' fun m => by
    rw [ev_map_left_assoc, ev_comparison, ev_comparison_assoc, ← G.map_comp, ← G.map_comp,
      ev_map_left]

/-- The comparison is natural in the functor. -/
@[reassoc]
theorem comparison_natTrans (G' : Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf J' (ModuleCat.{w} Λ))
    [G'.Additive] [G'.Linear Λ] (θ : G ⟶ G') (S : Sheaf J (ModuleCat.{w} Λ))
    (M : ModuleCat.{w} Λ) :
    ((sheafTensor J' Λ).map (θ.app S)).app M ≫ comparison J J' G' S M =
      comparison J J' G S M ≫ θ.app (((sheafTensor J Λ).obj S).obj M) :=
  hom_ext J' fun m => by
    rw [ev_map_left_assoc, ev_comparison, ev_comparison_assoc, θ.naturality]

/-- The comparison of a composite is the composite of the comparisons. -/
theorem comparison_comp {C'' : Type u₃} [Category.{v₃} C''] (J'' : GrothendieckTopology C'')
    [HasSheafify J'' (ModuleCat.{w} Λ)]
    (H : Sheaf J' (ModuleCat.{w} Λ) ⥤ Sheaf J'' (ModuleCat.{w} Λ)) [H.Additive] [H.Linear Λ]
    (S : Sheaf J (ModuleCat.{w} Λ)) (M : ModuleCat.{w} Λ) :
    comparison J J'' (G ⋙ H) S M =
      comparison J' J'' H (G.obj S) M ≫ H.map (comparison J J' G S M) :=
  hom_ext J'' fun m => by
    rw [ev_comparison]
    change H.map (G.map (ev J S m)) = ev J'' (H.obj (G.obj S)) m ≫ _
    rw [ev_comparison_assoc, ← H.map_comp, ev_comparison]

/-- **The comparison is an isomorphism for a finitely generated projective module**: for `M`
finitely generated projective, `G(S) ⊗_Λ M ⟶ G(S ⊗_Λ M)` is an isomorphism. -/
instance isIso_comparison (S : Sheaf J (ModuleCat.{w} Λ)) (M : ModuleCat.{w} Λ)
    [Module.Finite Λ M] [Module.Projective Λ M] : IsIso (comparison J J' G S M) := by
  obtain ⟨n, x, f, hf⟩ := exists_dualBasis M
  let p : Fin n → (((sheafTensor J Λ).obj S).obj M ⟶ S) := fun i =>
    lift J (LinearMap.smulRight (f i) (𝟙 S))
  have hp : ∀ i (m : M), ev J S m ≫ p i = f i m • 𝟙 S := fun i m => by
    simp [p]
  have hsum : ∑ i, p i ≫ ev J S (x i) = 𝟙 _ := hom_ext J fun m => by
    rw [Preadditive.comp_sum, Category.comp_id]
    conv_rhs => rw [← sum_smul_ev J S hf m]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Category.assoc, hp, Linear.smul_comp, Category.id_comp]
  refine ⟨∑ i, G.map (p i) ≫ ev J' (G.obj S) (x i), ?_, ?_⟩
  · refine hom_ext J' fun m => ?_
    rw [ev_comparison_assoc, Category.comp_id, Preadditive.comp_sum,
      ← sum_smul_ev J' (G.obj S) hf m]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Category.assoc, ← G.map_comp, hp, G.map_smul, G.map_id, Linear.smul_comp,
      Category.id_comp]
  · rw [Preadditive.sum_comp]
    simp only [Category.assoc, ev_comparison, ← G.map_comp]
    rw [← G.map_sum, hsum, G.map_id]

end Comparison

end Stacks.ConstantModuleTensor
