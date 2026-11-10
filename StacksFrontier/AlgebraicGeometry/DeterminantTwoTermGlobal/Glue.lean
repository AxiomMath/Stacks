module

public import StacksFrontier.Homology.TwoTermComplex.DeterminantBaseChange
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Local

/-!
# Sheaves of modules from compatible systems of modules on the affine opens

Let `X` be a scheme. Suppose given, for every affine open `V`, a finite projective
`Γ(X, V)`-module `D(V)`, and for every strictly smaller affine open `W < V` a map
`D(V) → D(W)`, semilinear over the restriction `Γ(X, V) → Γ(X, W)`, exhibiting `D(W)` as
`Γ(X, W) ⊗_{Γ(X, V)} D(V)`, these maps being compatible with composition. Such a system glues to
a sheaf of `𝒪_X`-modules whose sections over an open `U` are the compatible families of elements
of `D(V)`, `V ⊆ U` affine; its sections over an affine open `V` are `D(V)`.

## Main definitions

* `AlgebraicGeometry.AffineLineSystem`: the data.
* `AlgebraicGeometry.AffineLineSystem.res`: the transition map for `W ≤ V`, the identity when
  `W = V`.
* `AlgebraicGeometry.AffineLineSystem.toModules`: the glued sheaf of modules.

## Main results

* `AlgebraicGeometry.AffineLineSystem.existsUnique_glue`: the elements of the system glue
  uniquely over an affine open from compatible elements on an affine cover of it.
* `AlgebraicGeometry.AffineLineSystem.sectionsEquiv`: the sections over an affine open `V` are
  `D(V)`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite TwoTermDeterminant
open scoped TensorProduct

namespace TwoTermDeterminant

open scoped ChangeOfRings

variable {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

/-- Two semilinear maps out of a base change agree as soon as they agree on the image of the
base change map. -/
theorem IsBaseChangeAlong.ext {σ : R →+* S} {φ : M →ₛₗ[σ] N} (hφ : IsBaseChangeAlong σ φ)
    {T : Type u} [CommRing T] {τ : S →+* T} {P : Type u} [AddCommGroup P] [Module T P]
    {h₁ h₂ : N →ₛₗ[τ] P} (h : ∀ m, h₁ (φ m) = h₂ (φ m)) : h₁ = h₂ := by
  let : Module S P := Module.compHom P τ
  let k₁ : N →ₗ[S] P := { toFun := h₁, map_add' := h₁.map_add, map_smul' := h₁.map_smulₛₗ }
  let k₂ : N →ₗ[S] P := { toFun := h₂, map_add' := h₂.map_add, map_smul' := h₂.map_smulₛₗ }
  obtain ⟨_, _, hu⟩ := hφ P (k₁.comp φ)
  have e := (hu k₁ rfl).trans (hu k₂ (LinearMap.ext fun m => (h m).symm)).symm
  ext n
  exact LinearMap.congr_fun e n

/-- An isomorphism out of an extension of scalars, normalized on `1 ⊗ m`, is a base change. -/
theorem isBaseChangeAlong_of_extendScalarsIso (σ : R →+* S) {A : ModuleCat.{u} R}
    {B : ModuleCat.{u} S} (e : (ModuleCat.extendScalars.{u, u, u} σ).obj A ≅ B)
    (φ : A →ₛₗ[σ] B) (hφ : ∀ a, e.hom ((1 : S) ⊗ₜ[R,σ] a) = φ a) :
    IsBaseChangeAlong σ φ := by
  let := σ.toAlgebra
  let : Module R B := Module.compHom B σ
  have : IsScalarTower R S B := ⟨fun r s x => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  let φ' : A →ₗ[R] B := { toFun := φ, map_add' := φ.map_add, map_smul' := φ.map_smulₛₗ }
  let e' : (ModuleCat.extendScalars σ).obj (ModuleCat.of R A) ≅ ModuleCat.of S B := e
  have hb : IsBaseChange S φ' :=
    AlgebraicGeometry.ModuleCat.isBaseChange_of_extendScalarsIso σ rfl e' φ' hφ
  exact isBaseChangeAlong_of_isBaseChange (fun _ => rfl) φ φ' (fun _ => rfl) hb

/-- **A base change transports along a ring isomorphism on the target.** -/
theorem IsBaseChangeAlong.of_ringEquiv_target {σ : R →+* S} {φ : M →ₛₗ[σ] N}
    (hφ : IsBaseChangeAlong σ φ) (e : S ≃+* S') {N' : Type u} [AddCommGroup N'] [Module S' N']
    (ψ : N ≃+ N') (hψ : ∀ (s : S) (n : N), ψ (s • n) = e s • ψ n) (σ' : R →+* S')
    (hσ : ∀ r, σ' r = e (σ r)) (φ' : M →ₛₗ[σ'] N') (hφ' : ∀ m, φ' m = ψ (φ m)) :
    IsBaseChangeAlong σ' φ' := by
  intro P _ _ g
  let : Module S P := Module.compHom P (e : S →+* S')
  let g₀ : M →ₛₗ[σ] P :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun r m => by
        rw [g.map_smulₛₗ, hσ]
        rfl }
  obtain ⟨k, hk, hu⟩ := hφ P g₀
  let k' : N' →ₗ[S'] P :=
    { toFun := fun n' => k (ψ.symm n')
      map_add' := fun a b => by rw [map_add, map_add]
      map_smul' := fun s' n' => by
        have : ψ.symm (s' • n') = e.symm s' • ψ.symm n' := by
          apply ψ.injective
          rw [hψ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
        rw [this, k.map_smul]
        change (e (e.symm s')) • k (ψ.symm n') = _
        rw [RingEquiv.apply_symm_apply]
        rfl }
  refine ⟨k', ?_, fun k'' hk'' => ?_⟩
  · ext m
    have := LinearMap.congr_fun hk m
    simp only [LinearMap.comp_apply] at this ⊢
    change k (ψ.symm (φ' m)) = g m
    rw [hφ', AddEquiv.symm_apply_apply]
    exact this
  · let k₀ : N →ₗ[S] P :=
      { toFun := fun n => k'' (ψ n)
        map_add' := fun a b => by rw [map_add, map_add]
        map_smul' := fun s n => by
          rw [hψ, k''.map_smul]
          rfl }
    have h0 : k₀ = k := hu k₀ (by
      ext m
      have := LinearMap.congr_fun hk'' m
      simp only [LinearMap.comp_apply] at this ⊢
      change k'' (ψ (φ m)) = g m
      rw [← hφ']
      exact this)
    ext n'
    change k'' n' = k (ψ.symm n')
    rw [← h0]
    change k'' n' = k'' (ψ (ψ.symm n'))
    rw [AddEquiv.apply_symm_apply]

/-- **A base change transports along a ring isomorphism on the source.** -/
theorem IsBaseChangeAlong.of_ringEquiv_source {R' M' : Type u} [CommRing R'] [AddCommGroup M']
    [Module R' M'] {σ : R →+* S} {φ : M →ₛₗ[σ] N} (hφ : IsBaseChangeAlong σ φ) (e : R' ≃+* R)
    (ψ : M' ≃+ M) (hψ : ∀ (r : R') (m : M'), ψ (r • m) = e r • ψ m) (σ' : R' →+* S)
    (hσ : ∀ r, σ' r = σ (e r)) (φ' : M' →ₛₗ[σ'] N) (hφ' : ∀ m, φ' m = φ (ψ m)) :
    IsBaseChangeAlong σ' φ' := by
  intro P _ _ g
  let g₀ : M →ₛₗ[σ] P :=
    { toFun := fun m => g (ψ.symm m)
      map_add' := fun a b => by rw [map_add, map_add]
      map_smul' := fun r m => by
        have : ψ.symm (r • m) = e.symm r • ψ.symm m := by
          apply ψ.injective
          rw [hψ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
        rw [this, g.map_smulₛₗ, hσ, RingEquiv.apply_symm_apply] }
  obtain ⟨k, hk, hu⟩ := hφ P g₀
  refine ⟨k, ?_, fun k' hk' => hu k' ?_⟩
  · ext m
    have := LinearMap.congr_fun hk (ψ m)
    simp only [LinearMap.comp_apply] at this ⊢
    rw [hφ', this]
    change g (ψ.symm (ψ m)) = g m
    rw [AddEquiv.symm_apply_apply]
  · ext m
    have := LinearMap.congr_fun hk' (ψ.symm m)
    simp only [LinearMap.comp_apply] at this ⊢
    rw [hφ', AddEquiv.apply_symm_apply] at this
    exact this

/-- An endomorphism of a base change fixing the base change map is the identity. -/
private theorem IsBaseChangeAlong.eq_id_of_comp_eq {σ : R →+* S} {φ : M →ₛₗ[σ] N}
    (hφ : IsBaseChangeAlong σ φ) (k : N →ₗ[S] N) (hk : k.comp φ = φ) : k = LinearMap.id := by
  obtain ⟨_, _, hu⟩ := hφ N φ
  exact (hu k hk).trans (hu LinearMap.id (LinearMap.id_comp φ)).symm

/-- Two base changes of the same module along the same ring map are canonically isomorphic. -/
theorem IsBaseChangeAlong.bijective_lift {σ : R →+* S} {φ : M →ₛₗ[σ] N}
    (hφ : IsBaseChangeAlong σ φ) {N' : Type u} [AddCommGroup N'] [Module S N']
    {φ' : M →ₛₗ[σ] N'} (hφ' : IsBaseChangeAlong σ φ') (k : N →ₗ[S] N') (hk : k.comp φ = φ') :
    Function.Bijective k := by
  obtain ⟨k', hk', -⟩ := hφ' N φ
  have h1 : k'.comp k = LinearMap.id := hφ.eq_id_of_comp_eq _ (by
    ext m
    simp only [LinearMap.comp_apply]
    rw [← LinearMap.comp_apply k φ, hk, ← LinearMap.comp_apply k' φ', hk'])
  have h2 : k.comp k' = LinearMap.id := hφ'.eq_id_of_comp_eq _ (by
    ext m
    simp only [LinearMap.comp_apply]
    rw [← LinearMap.comp_apply k' φ', hk', ← LinearMap.comp_apply k φ, hk])
  exact ⟨Function.LeftInverse.injective (g := k') fun x => LinearMap.congr_fun h1 x,
    Function.RightInverse.surjective (g := k') fun x => LinearMap.congr_fun h2 x⟩

/-- A base change in the semilinear sense is a base change in the sense of `IsBaseChange`. -/
theorem IsBaseChangeAlong.isBaseChange [Algebra R S] {σ : R →+* S}
    (hσ : ∀ r, algebraMap R S r = σ r) [Module R N] [IsScalarTower R S N] {φ : M →ₛₗ[σ] N}
    (hφ : IsBaseChangeAlong σ φ) (φ' : M →ₗ[R] N) (h : ∀ x, φ' x = φ x) : IsBaseChange S φ' := by
  let ψ : S ⊗[R] M →ₗ[S] N := φ'.liftBaseChange S
  let g : M →ₛₗ[σ] S ⊗[R] M :=
    { toFun := fun m => (1 : S) ⊗ₜ[R] m
      map_add' := fun a b => TensorProduct.tmul_add _ _ _
      map_smul' := fun r m => by
        rw [TensorProduct.tmul_smul, ← hσ, algebraMap_smul] }
  obtain ⟨h₀, hh₀, -⟩ := hφ (S ⊗[R] M) g
  have e1 : ψ.comp h₀ = LinearMap.id := by
    refine hφ.eq_id_of_comp_eq _ ?_
    ext m
    have := LinearMap.congr_fun hh₀ m
    simp only [LinearMap.comp_apply] at this ⊢
    rw [this]
    change ψ ((1 : S) ⊗ₜ[R] m) = φ m
    simp [ψ, h]
  have e2 : h₀.comp ψ = LinearMap.id := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext m
    simp only [TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_comp,
      TensorProduct.curry_apply, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Function.comp_apply, LinearMap.id_coe, id_eq]
    have := LinearMap.congr_fun hh₀ m
    simp only [LinearMap.comp_apply] at this
    simp only [ψ, LinearMap.liftBaseChange_tmul, one_smul, h]
    exact this
  refine IsBaseChange.of_equiv (LinearEquiv.ofLinearMap ψ h₀ e1 e2) fun m => ?_
  simp [ψ]

end TwoTermDeterminant

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **A compatible system of modules on the affine opens of a scheme**, with restriction maps
exhibiting each module as the base change of the module on any larger affine open. -/
structure AffineLineSystem (X : Scheme.{u}) where
  /-- The module over an affine open. -/
  obj (V : X.affineOpens) : ModuleCat.{u} Γ(X, V)
  /-- The restriction map to a smaller affine open. -/
  map {V W : X.affineOpens} (h : (W : X.Opens) ≤ V) :
    obj V →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] obj W
  map_id (V : X.affineOpens) (x : obj V) : map le_rfl x = x
  map_map {V W W' : X.affineOpens} (h : (W : X.Opens) ≤ V) (h' : (W' : X.Opens) ≤ W)
    (x : obj V) : map h' (map h x) = map (h'.trans h) x
  isBaseChange {V W : X.affineOpens} (h : (W : X.Opens) ≤ V) : IsBaseChangeAlong _ (map h)

namespace AffineLineSystem

variable (D : AffineLineSystem X)

/-! ### The structure sheaf glues along affine covers -/

/-- Sections of `𝒪_X` over an affine open glue uniquely from sections over a cover by smaller
affine opens which agree on every affine open contained in two members. -/
theorem existsUnique_glue_structureSheaf (V : X.affineOpens) {ι : Type u} (W : ι → X.affineOpens)
    (hW : ∀ i, (W i : X.Opens) ≤ V) (hcov : (V : X.Opens) ≤ ⨆ i, (W i : X.Opens))
    (a : ∀ i, Γ(X, W i))
    (ha : ∀ i j (W' : X.affineOpens) (h₁ : (W' : X.Opens) ≤ W i) (h₂ : (W' : X.Opens) ≤ W j),
      X.presheaf.map (homOfLE h₁).op (a i) = X.presheaf.map (homOfLE h₂).op (a j)) :
    ∃! b : Γ(X, V), ∀ i, X.presheaf.map (homOfLE (hW i)).op b = a i := by
  refine X.sheaf.existsUnique_gluing' (fun i => (W i : X.Opens)) (V : X.Opens)
    (fun i => homOfLE (hW i)) hcov a fun i j => ?_
  let U' : {W' : X.affineOpens // (W' : X.Opens) ≤ (W i : X.Opens) ⊓ (W j : X.Opens)} →
    X.Opens := fun W' => W'.1
  refine X.sheaf.eq_of_locally_eq' U' ((W i : X.Opens) ⊓ (W j : X.Opens))
    (fun W' => homOfLE W'.2) ?_ _ _ fun W' => ?_
  · intro x hx
    obtain ⟨_, ⟨W'', hW'', rfl⟩, hxW'', hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx ((W i : X.Opens) ⊓ W j).2
    exact Opens.mem_iSup.mpr ⟨⟨⟨W'', hW''⟩, hle⟩, hxW''⟩
  · have h1 := ha i j W'.1 (W'.2.trans inf_le_left) (W'.2.trans inf_le_right)
    have l1 : ∀ {U₁ U₂ U₃ : X.Opens} (f₁ : U₂ ⟶ U₁) (f₂ : U₃ ⟶ U₂) (x : Γ(X, U₁)),
        X.presheaf.map f₂.op (X.presheaf.map f₁.op x) = X.presheaf.map (f₂ ≫ f₁).op x := by
      intros
      rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    exact (l1 _ _ (a i)).trans (h1.trans (l1 _ _ (a j)).symm)

/-! ### Gluing the modules of the system -/

section Glue

variable {V : X.affineOpens}

/-- The restriction of scalars along the restriction of functions, as a semilinear map. -/
def resO {V W : X.affineOpens} (h : (W : X.Opens) ≤ V) :
    Γ(X, V) →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] Γ(X, W) where
  toFun := X.presheaf.map (homOfLE h).op
  map_add' := map_add _
  map_smul' r x := by
    simp only [smul_eq_mul, map_mul]

/-- A linear form on the module over `V`, followed by restriction of functions to `W ≤ V`,
factors uniquely through the restriction map to the module over `W`. -/
theorem existsUnique_coord {V W : X.affineOpens} (h : (W : X.Opens) ≤ V)
    (ε : D.obj V →ₗ[Γ(X, V)] Γ(X, V)) :
    ∃! εW : D.obj W →ₗ[Γ(X, W)] Γ(X, W), εW.comp (D.map h) = (resO h).comp ε :=
  D.isBaseChange h Γ(X, W) ((resO h).comp ε)

/-- The base change of a linear form on the module over `V` to the module over `W ≤ V`. -/
def coord {V W : X.affineOpens} (h : (W : X.Opens) ≤ V) (ε : D.obj V →ₗ[Γ(X, V)] Γ(X, V)) :
    D.obj W →ₗ[Γ(X, W)] Γ(X, W) :=
  (D.existsUnique_coord h ε).exists.choose

/-- The base change of `ε` to `W` takes the restriction of `x` to the restriction of `ε x`. -/
theorem coord_map {V W : X.affineOpens} (h : (W : X.Opens) ≤ V)
    (ε : D.obj V →ₗ[Γ(X, V)] Γ(X, V)) (x : D.obj V) :
    D.coord h ε (D.map h x) = X.presheaf.map (homOfLE h).op (ε x) :=
  LinearMap.congr_fun (D.existsUnique_coord h ε).exists.choose_spec x

/-- For `W' ≤ W ≤ V`, the base change of `ε` to `W'` agrees on restrictions from `W` with the
restriction to `W'` of the base change of `ε` to `W`. -/
theorem coord_map_map {V W W' : X.affineOpens} (h : (W : X.Opens) ≤ V)
    (h' : (W' : X.Opens) ≤ W) (ε : D.obj V →ₗ[Γ(X, V)] Γ(X, V)) (y : D.obj W) :
    D.coord (h'.trans h) ε (D.map h' y) = X.presheaf.map (homOfLE h').op (D.coord h ε y) := by
  let F₁ : D.obj W →ₛₗ[(X.presheaf.map (homOfLE h').op).hom] Γ(X, W') :=
    (D.coord (h'.trans h) ε).comp (D.map h')
  let F₂ : D.obj W →ₛₗ[(X.presheaf.map (homOfLE h').op).hom] Γ(X, W') :=
    (resO h').comp (D.coord h ε)
  have : F₁ = F₂ := by
    refine IsBaseChangeAlong.ext (D.isBaseChange h) fun x => ?_
    simp only [F₁, F₂, LinearMap.comp_apply]
    rw [D.map_map, coord_map, coord_map]
    simp only [resO, LinearMap.coe_mk, AddHom.coe_mk, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp]
    rfl
  exact LinearMap.congr_fun this y

/-- **Elements of the system glue uniquely along affine covers.** Let `V` be an affine open
covered by affine opens `W i ≤ V`, and let `t i ∈ D(W i)` agree on every affine open contained in
two members of the cover. Then there is a unique element of `D(V)` restricting to every `t i`. -/
theorem existsUnique_glue [∀ V : X.affineOpens, Module.Finite Γ(X, V) (D.obj V)]
    [∀ V : X.affineOpens, Module.Projective Γ(X, V) (D.obj V)] (V : X.affineOpens) {ι : Type u}
    (W : ι → X.affineOpens) (hW : ∀ i, (W i : X.Opens) ≤ V)
    (hcov : (V : X.Opens) ≤ ⨆ i, (W i : X.Opens)) (t : ∀ i, D.obj (W i))
    (ht : ∀ i j (W' : X.affineOpens) (h₁ : (W' : X.Opens) ≤ W i) (h₂ : (W' : X.Opens) ≤ W j),
      D.map h₁ (t i) = D.map h₂ (t j)) :
    ∃! s : D.obj V, ∀ i, D.map (hW i) s = t i := by
  classical
  obtain ⟨n, π, σ, -, -, hπσ⟩ := Module.Finite.exists_comp_eq_id_of_projective Γ(X, V) (D.obj V)
  let ε : Fin n → (D.obj V →ₗ[Γ(X, V)] Γ(X, V)) := fun k => (LinearMap.proj k).comp σ
  let e : Fin n → D.obj V := fun k => π (fun j => if k = j then 1 else 0)
  have hdecomp : ∀ x : D.obj V, x = ∑ k, ε k x • e k := by
    intro x
    conv_lhs => rw [← LinearMap.id_apply (R := Γ(X, V)) x, ← hπσ, LinearMap.comp_apply,
      pi_eq_sum_univ (σ x), map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul]
    rfl
  have hdecompW : ∀ {W' : X.affineOpens} (h : (W' : X.Opens) ≤ V) (y : D.obj W'),
      y = ∑ k, D.coord h (ε k) y • D.map h (e k) := by
    intro W' h y
    let F : D.obj W' →ₗ[Γ(X, W')] D.obj W' :=
      ∑ k, (LinearMap.smulRight (D.coord h (ε k)) (D.map h (e k)))
    have hF : F.comp (D.map h) = D.map h := by
      ext x
      simp only [F, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
        coord_map]
      conv_rhs => rw [hdecomp x, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [LinearMap.map_smulₛₗ]
    have hy := LinearMap.congr_fun ((D.isBaseChange h).eq_id_of_comp_eq F hF) y
    simp only [F, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply] at hy
    exact hy.symm
  have hcoord : ∀ k, ∃! b : Γ(X, V), ∀ i,
      X.presheaf.map (homOfLE (hW i)).op b = D.coord (hW i) (ε k) (t i) := by
    intro k
    refine existsUnique_glue_structureSheaf V W hW hcov _ fun i j W' h₁ h₂ => ?_
    rw [← coord_map_map, ← coord_map_map, ht i j W' h₁ h₂]
  choose b hb hbu using hcoord
  refine ⟨∑ k, b k • e k, fun i => ?_, fun s hs => ?_⟩
  · rw [map_sum, hdecompW (hW i) (t i)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.map_smulₛₗ, ← hb k i]
  · rw [hdecomp s]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hbu k (ε k s) fun i => by rw [← coord_map, hs i]]

end Glue

/-- **Elements of the system are determined on affine covers.** -/
theorem ext_of_cover [∀ V : X.affineOpens, Module.Finite Γ(X, V) (D.obj V)]
    [∀ V : X.affineOpens, Module.Projective Γ(X, V) (D.obj V)] (V : X.affineOpens) {ι : Type u}
    (W : ι → X.affineOpens) (hW : ∀ i, (W i : X.Opens) ≤ V)
    (hcov : (V : X.Opens) ≤ ⨆ i, (W i : X.Opens)) {x y : D.obj V}
    (h : ∀ i, D.map (hW i) x = D.map (hW i) y) : x = y := by
  obtain ⟨_, _, hu⟩ := D.existsUnique_glue V W hW hcov (fun i => D.map (hW i) x)
    fun i j W' h₁ h₂ => by rw [D.map_map, D.map_map]
  exact (hu x fun i => rfl).trans (hu y fun i => (h i).symm).symm

/-! ### The glued sheaf of modules -/

section Sheaf

/-- The affine opens contained in an open `U`. -/
abbrev AffBelow (U : X.Opens) := {V : X.affineOpens // (V : X.Opens) ≤ U}

/-- The module over an affine open `V ≤ U`, as a `Γ(X, U)`-module by restriction of scalars. -/
abbrev moduleBelow (U : X.Opens) (V : AffBelow U) : Module Γ(X, U) (D.obj V.1) :=
  Module.compHom _ (X.presheaf.map (homOfLE V.2).op).hom

attribute [local instance] moduleBelow

/-- Restricting a section of `𝒪_X` along `f₁` and then `f₂` is restricting it along `f₂ ≫ f₁`. -/
theorem map_comp_presheaf {U₁ U₂ U₃ : X.Opens} (f₁ : U₂ ⟶ U₁) (f₂ : U₃ ⟶ U₂)
    (x : Γ(X, U₁)) :
    X.presheaf.map f₂.op (X.presheaf.map f₁.op x) = X.presheaf.map (f₂ ≫ f₁).op x := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- Restricting a section of `𝒪_X` along an endomorphism of `U` is the identity. -/
theorem map_presheaf_id {U : X.Opens} (f : U ⟶ U) (x : Γ(X, U)) : X.presheaf.map f.op x = x := by
  rw [Subsingleton.elim f (𝟙 U), op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

/-- The compatible families of elements of the system over the affine opens contained in `U`. -/
def sectionsSubmodule (U : X.Opens) : Submodule Γ(X, U) (∀ V : AffBelow U, D.obj V.1) where
  carrier := {s | ∀ (V W : AffBelow U) (h : (W.1 : X.Opens) ≤ V.1), D.map h (s V) = s W}
  add_mem' {s t} hs ht V W h := by
    simp only [Pi.add_apply, map_add, hs V W h, ht V W h]
  zero_mem' V W h := by
    simp only [Pi.zero_apply, map_zero]
  smul_mem' r s hs V W h := by
    change D.map h (X.presheaf.map (homOfLE V.2).op r • s V) =
      X.presheaf.map (homOfLE W.2).op r • s W
    rw [LinearMap.map_smulₛₗ, hs V W h]
    congr 1
    exact map_comp_presheaf (homOfLE V.2) (homOfLE h) r

/-- The sections of the glued sheaf over an open `U`. -/
abbrev Sections (U : X.Opens) := D.sectionsSubmodule U

/-- Restriction of compatible families, as a function. -/
def restrictFun {U U' : X.Opens} (h : U' ≤ U) (s : D.Sections U) : D.Sections U' :=
  ⟨fun V => s.1 ⟨V.1, V.2.trans h⟩, fun V W hVW => s.2 ⟨V.1, V.2.trans h⟩ ⟨W.1, W.2.trans h⟩ hVW⟩

/-- The value of a restricted family at an affine open is the value of the family there. -/
theorem restrictFun_apply {U U' : X.Opens} (h : U' ≤ U) (s : D.Sections U) (V : AffBelow U') :
    (D.restrictFun h s).1 V = s.1 ⟨V.1, V.2.trans h⟩ := rfl

/-- Restriction of compatible families is semilinear over the restriction of functions. -/
theorem restrictFun_smul {U U' : X.Opens} (h : U' ≤ U) (r : Γ(X, U)) (s : D.Sections U) :
    D.restrictFun h (r • s) = (X.presheaf.map (homOfLE h).op r) • D.restrictFun h s := by
  refine Subtype.ext (funext fun V => ?_)
  change X.presheaf.map (homOfLE (V.2.trans h)).op r • s.1 ⟨V.1, V.2.trans h⟩ =
    X.presheaf.map (homOfLE V.2).op (X.presheaf.map (homOfLE h).op r) • s.1 ⟨V.1, V.2.trans h⟩
  rw [map_comp_presheaf]
  rfl

/-- Restriction of compatible families. -/
def restrict {U U' : X.Opens} (h : U' ≤ U) :
    D.Sections U →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] D.Sections U' where
  toFun := D.restrictFun h
  map_add' _ _ := rfl
  map_smul' := D.restrictFun_smul h

/-- The value of a restricted family at an affine open is the value of the family there. -/
theorem restrict_apply {U U' : X.Opens} (h : U' ≤ U) (s : D.Sections U) (V : AffBelow U') :
    (D.restrict h s).1 V = s.1 ⟨V.1, V.2.trans h⟩ := rfl

/-- The `𝒪_X(U)`-module structure on the sections over `U`. -/
instance sectionsModule (U : (X.Opens)ᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) (D.Sections U.unop) :=
  inferInstanceAs (Module Γ(X, U.unop) (D.Sections U.unop))

/-- The glued presheaf of modules. -/
def presheafOfModules : PresheafOfModules.{u} X.ringCatSheaf.obj where
  obj U := ModuleCat.of (X.ringCatSheaf.obj.obj U) (D.Sections U.unop)
  map {U U'} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map f).hom).obj
      (ModuleCat.of (X.ringCatSheaf.obj.obj U') (D.Sections U'.unop)))
    { toFun := D.restrict f.unop.le
      map_add' := map_add _
      map_smul' := (D.restrict f.unop.le).map_smulₛₗ }
  map_id U := by
    ext s
    rfl
  map_comp f g := by
    ext s
    rfl

section IsSheaf

variable [∀ V : X.affineOpens, Module.Finite Γ(X, V) (D.obj V)]
  [∀ V : X.affineOpens, Module.Projective Γ(X, V) (D.obj V)]

/-- The affine opens contained in `V` and in some member of a family of opens. -/
abbrev CoverIdx {ι : Type u} (U : ι → X.Opens) (V : X.affineOpens) :=
  Σ i : ι, {W : X.affineOpens // (W : X.Opens) ≤ (V : X.Opens) ⊓ U i}

/-- An affine open contained in `⨆ i, U i` is covered by the affine opens contained in it and in
some `U i`. -/
theorem le_iSup_coverIdx {ι : Type u} (U : ι → X.Opens) (V : X.affineOpens)
    (hV : (V : X.Opens) ≤ iSup U) :
    (V : X.Opens) ≤ ⨆ p : CoverIdx U V, (p.2.1 : X.Opens) := by
  intro x hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hV hx)
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (V : X.Opens) ⊓ U i from ⟨hx, hi⟩)
      ((V : X.Opens) ⊓ U i).2
  exact Opens.mem_iSup.mpr ⟨⟨i, ⟨⟨W, hW⟩, hle⟩⟩, hxW⟩

/-- The sections of the underlying presheaf of abelian groups are the compatible families. -/
def secEquiv (U : X.Opens) :
    ToType (D.presheafOfModules.presheaf.obj (op U)) ≃ D.Sections U :=
  Equiv.refl _

omit [∀ V : X.affineOpens, Module.Finite Γ(X, V) (D.obj V)]
  [∀ V : X.affineOpens, Module.Projective Γ(X, V) (D.obj V)] in
/-- The identification `secEquiv` takes restriction in the glued presheaf to `restrict`. -/
theorem secEquiv_map {U U' : X.Opens} (f : U' ⟶ U)
    (s : ToType (D.presheafOfModules.presheaf.obj (op U))) :
    D.secEquiv U' (D.presheafOfModules.presheaf.map f.op s) = D.restrict f.le (D.secEquiv U s) :=
  rfl

/-- Compatible elements of the system on the affine opens contained in an affine open `V` and in
some member of a cover `U` of `V` glue to a unique element of `D(V)`. -/
theorem existsUnique_glue_cover {ι : Type u} (U : ι → X.Opens) (V : X.affineOpens)
    (hV : (V : X.Opens) ≤ iSup U) (t : ∀ p : CoverIdx U V, D.obj p.2.1)
    (ht : ∀ (p q : CoverIdx U V) (W' : X.affineOpens) (h₁ : (W' : X.Opens) ≤ p.2.1)
      (h₂ : (W' : X.Opens) ≤ q.2.1), D.map h₁ (t p) = D.map h₂ (t q)) :
    ∃! x : D.obj V, ∀ p : CoverIdx U V, D.map (p.2.2.trans inf_le_left) x = t p :=
  D.existsUnique_glue V (W := fun p : CoverIdx U V => p.2.1)
    (fun p => p.2.2.trans inf_le_left) (le_iSup_coverIdx U V hV) t ht

/-- **The glued presheaf is a sheaf.** -/
theorem isSheaf_presheafOfModules :
    TopCat.Presheaf.IsSheaf (X := X) D.presheafOfModules.presheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  let sf' : ∀ i, D.Sections (U i) := fun i => D.secEquiv (U i) (sf i)
  have hsf' : ∀ i j (W : X.affineOpens) (hi : (W : X.Opens) ≤ U i) (hj : (W : X.Opens) ≤ U j),
      (sf' i).1 ⟨W, hi⟩ = (sf' j).1 ⟨W, hj⟩ := by
    intro i j W hi hj
    have h1 := congrArg (D.secEquiv (U i ⊓ U j)) (hsf i j)
    rw [secEquiv_map, secEquiv_map] at h1
    exact congrArg (fun r : D.Sections (U i ⊓ U j) => r.1 ⟨W, le_inf hi hj⟩) h1
  let t : ∀ (V : X.affineOpens) (p : CoverIdx U V), D.obj p.2.1 :=
    fun V p => (sf' p.1).1 ⟨p.2.1, p.2.2.trans inf_le_right⟩
  have ht : ∀ (V : X.affineOpens) (p q : CoverIdx U V) (W' : X.affineOpens)
      (h₁ : (W' : X.Opens) ≤ p.2.1) (h₂ : (W' : X.Opens) ≤ q.2.1),
      D.map h₁ (t V p) = D.map h₂ (t V q) := by
    intro V p q W' h₁ h₂
    have e1 := (sf' p.1).2 ⟨p.2.1, p.2.2.trans inf_le_right⟩
      ⟨W', h₁.trans (p.2.2.trans inf_le_right)⟩ h₁
    have e2 := (sf' q.1).2 ⟨q.2.1, q.2.2.trans inf_le_right⟩
      ⟨W', h₂.trans (q.2.2.trans inf_le_right)⟩ h₂
    exact e1.trans ((hsf' p.1 q.1 W' _ _).trans e2.symm)
  have hglue : ∀ V : AffBelow (iSup U), ∃! x : D.obj V.1,
      ∀ p : CoverIdx U V.1, D.map (p.2.2.trans inf_le_left) x = t V.1 p := fun V =>
    D.existsUnique_glue_cover U V.1 V.2 (t V.1) (ht V.1)
  choose x hx hxu using hglue
  have hcompat : ∀ (V W : AffBelow (iSup U)) (h : (W.1 : X.Opens) ≤ V.1),
      D.map h (x V) = x W := by
    intro V W h
    refine hxu W _ fun p => ?_
    rw [D.map_map]
    exact hx V ⟨p.1, ⟨p.2.1, le_inf ((p.2.2.trans inf_le_left).trans h) (p.2.2.trans inf_le_right)⟩⟩
  let s : D.Sections (iSup U) := ⟨x, fun V W h => hcompat V W h⟩
  have hs : ∀ i, D.restrict (le_iSup U i) s = sf' i := by
    intro i
    refine Subtype.ext (funext fun V => ?_)
    have := hx ⟨V.1, V.2.trans (le_iSup U i)⟩ ⟨i, ⟨V.1, le_inf le_rfl V.2⟩⟩
    rwa [D.map_id] at this
  refine ⟨(D.secEquiv _).symm s, fun i => ?_, fun s' hs' => ?_⟩
  · apply (D.secEquiv (U i)).injective
    rw [secEquiv_map, Equiv.apply_symm_apply]
    exact hs i
  · apply (D.secEquiv _).injective
    rw [Equiv.apply_symm_apply]
    refine Subtype.ext (funext fun V => hxu V _ fun p => ?_)
    rw [(D.secEquiv _ s').2 V ⟨p.2.1, (p.2.2.trans inf_le_left).trans V.2⟩
      (p.2.2.trans inf_le_left)]
    have h1 := congrArg (D.secEquiv (U p.1)) (hs' p.1)
    rw [secEquiv_map] at h1
    exact congrArg (fun r : D.Sections (U p.1) => r.1 ⟨p.2.1, p.2.2.trans inf_le_right⟩) h1

/-- **The glued sheaf of `𝒪_X`-modules.** -/
def toModules : X.Modules where
  val := D.presheafOfModules
  isSheaf := D.isSheaf_presheafOfModules

/-- The sections of the glued sheaf are the compatible families. -/
def sec (U : X.Opens) : Γ(D.toModules, U) ≃ D.Sections U :=
  Equiv.refl _

/-- The identification `sec` is additive. -/
theorem sec_add (U : X.Opens) (a b : Γ(D.toModules, U)) :
    D.sec U (a + b) = D.sec U a + D.sec U b := rfl

/-- The identification `sec` commutes with scalar multiplication by `Γ(X, U)`. -/
theorem sec_smul (U : X.Opens) (r : Γ(X, U)) (a : Γ(D.toModules, U)) :
    D.sec U (r • a) = r • D.sec U a := rfl

/-- The identification `sec` takes restriction in the glued sheaf to `restrict`. -/
theorem sec_map {U U' : X.Opens} (h : U' ≤ U) (a : Γ(D.toModules, U)) :
    D.sec U' (D.toModules.presheaf.map (homOfLE h).op a) = D.restrict h (D.sec U a) := rfl

/-- **The sections of the glued sheaf over an affine open are the module of the system.** -/
def sectionsEquiv (V : X.affineOpens) : Γ(D.toModules, V) ≃ₗ[Γ(X, V)] D.obj V where
  toFun s := (D.sec V s).1 ⟨V, le_rfl⟩
  invFun y := (D.sec V).symm ⟨fun W => D.map W.2 y, fun W W' h => D.map_map _ _ _⟩
  map_add' _ _ := rfl
  map_smul' r a := by
    rw [sec_smul]
    change X.presheaf.map (homOfLE le_rfl).op r • (D.sec V a).1 ⟨V, le_rfl⟩ =
      r • (D.sec V a).1 ⟨V, le_rfl⟩
    rw [map_presheaf_id]
  left_inv a := by
    apply (D.sec V).injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext (funext fun W => (D.sec V a).2 ⟨V, le_rfl⟩ W W.2)
  right_inv y := by
    change (D.sec V ((D.sec V).symm _)).1 ⟨V, le_rfl⟩ = y
    rw [Equiv.apply_symm_apply]
    exact D.map_id V y

/-- The image of a section under `sectionsEquiv` is its component at `V` itself. -/
theorem sectionsEquiv_apply (V : X.affineOpens) (a : Γ(D.toModules, V)) :
    D.sectionsEquiv V a = (D.sec V a).1 ⟨V, le_rfl⟩ := rfl

/-- The identification of sections over affine opens commutes with restriction. -/
theorem sectionsEquiv_restrict {V W : X.affineOpens} (h : (W : X.Opens) ≤ V)
    (a : Γ(D.toModules, V)) :
    D.sectionsEquiv W (D.toModules.presheaf.map (homOfLE h).op a) =
      D.map h (D.sectionsEquiv V a) :=
  ((D.sec V a).2 ⟨V, le_rfl⟩ ⟨W, h⟩ h).symm

/-- A section over an open is determined by its values on the affine opens it contains. -/
theorem sec_apply (U : X.Opens) (a : Γ(D.toModules, U)) (V : AffBelow U) :
    (D.sec U a).1 V = D.sectionsEquiv V.1 (D.toModules.presheaf.map (homOfLE V.2).op a) := rfl

end IsSheaf

section Quasicoherent

variable [∀ V : X.affineOpens, Module.Finite Γ(X, V) (D.obj V)]
  [∀ V : X.affineOpens, Module.Projective Γ(X, V) (D.obj V)]

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange in
/-- **The glued sheaf is quasi-coherent**: its sections over a basic open of an affine open are
the localization of its sections over the affine open, the restriction being a base change along
a localization. -/
theorem isQuasicoherent_toModules : D.toModules.IsQuasicoherent := by
  refine
    Stacks.AlgebraicGeometry.TorsionQuasicoherent.isQuasicoherent_of_isLocalizedModule_restrictₗ
      D.toModules fun U hU a => ?_
  let := moduleOfLE D.toModules (X.basicOpen_le a)
  let V : X.affineOpens := ⟨U, hU⟩
  let W : X.affineOpens := ⟨X.basicOpen a, hU.basicOpen a⟩
  have hWV : (W : X.Opens) ≤ V := X.basicOpen_le a
  have : IsScalarTower Γ(X, U) Γ(X, X.basicOpen a) Γ(D.toModules, X.basicOpen a) :=
    ⟨fun r s x => by
      rw [Algebra.smul_def, mul_smul]
      rfl⟩
  have : IsLocalization.Away a Γ(X, X.basicOpen a) := hU.isLocalization_basicOpen a
  refine (isLocalizedModule_iff_isBaseChange (Submonoid.powers a) Γ(X, X.basicOpen a) _).mpr ?_
  let ρ : Γ(D.toModules, U) →ₛₗ[(X.presheaf.map (homOfLE hWV).op).hom]
      Γ(D.toModules, X.basicOpen a) :=
    ((D.sectionsEquiv W).symm.toLinearMap.comp (D.map hWV)).comp (D.sectionsEquiv V).toLinearMap
  have hρ : IsBaseChangeAlong _ ρ :=
    ((D.isBaseChange hWV).comp_linearEquiv _).comp_linearEquiv_right _
  refine hρ.isBaseChange (fun _ => rfl) _ fun x => ?_
  change D.toModules.presheaf.map (homOfLE hWV).op x = (D.sectionsEquiv W).symm
    (D.map hWV (D.sectionsEquiv V x))
  rw [LinearEquiv.eq_symm_apply, sectionsEquiv_restrict]

end Quasicoherent

end Sheaf

end AffineLineSystem

end AlgebraicGeometry

end
