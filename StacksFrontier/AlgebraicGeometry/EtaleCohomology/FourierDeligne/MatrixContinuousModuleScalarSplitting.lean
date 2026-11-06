module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.MatrixContinuousModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierCoefficientVanishing

/-!
# Morphisms of matrix modules: intertwiners and coordinates along a basis of the coefficients

For a finite commutative ring `Λ` and representations `σ, σ'` of a topological group `G` on
`Λ^m`, `Λ^{m'}` with open kernels, an intertwiner `A` (`A σ(g) = σ'(g) A`) is a morphism of the
matrix modules (`Stacks.EtaleCohomology.matrixContinuousModuleHom`), and composition of
intertwiners is composition of morphisms.

For a homomorphism `ρ : Λ →+* Λ''` of finite commutative rings with elements `β_i ∈ Λ''` and
additive coordinate maps `π_i : Λ'' → Λ` (`i < e`) such that `π_i` is `Λ`-linear,
`π_j(β_i) = δ_{ij}` and `x = Σ_i ρ(π_i x) β_i` (a basis of `Λ''` over `Λ` with its coordinate
functionals), the matrix module of `ρ ∘ σ` over `Λ''`, read over `Λ`, splits as `e` copies of the
matrix module of `σ`: the coordinates `v ↦ π_k ∘ v` and the injections `v ↦ ρ(v) β_i` are
equivariant, and multiplication by `o ∈ Λ''` is the matrix `(π_k(o β_i))_{ki}`.

These are the module-level inputs of the extension of the level isogeny of Laumon's comparison
from `O_E` to `O''` (step R3 of the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main definitions

* `Stacks.EtaleCohomology.finiteTypeContinuousModuleLinearHom`: the morphism of finite continuous
  modules given by an equivariant linear map.
* `Stacks.EtaleCohomology.matrixContinuousModuleHom`: the morphism of matrix modules given by
  multiplication by an intertwiner.
* `Stacks.EtaleCohomology.matrixContinuousModuleCoordHom`: the coordinate `v ↦ π_k ∘ v`.
* `Stacks.EtaleCohomology.matrixContinuousModuleBasisHom`: the injection `v ↦ ρ(v) β_i`.
* `Stacks.EtaleCohomology.matrixContinuousModuleRestrictScalarsMulHom`: multiplication by
  `o ∈ Λ''`, read over `Λ`.

## Main results

* `Stacks.EtaleCohomology.matrixContinuousModuleHom_comp`: composition of intertwiners is
  composition of morphisms.
* `Stacks.EtaleCohomology.matrixContinuousModuleBasisHom_comp_coordHom`,
  `Stacks.EtaleCohomology.sum_matrixContinuousModuleCoordHom_comp_basisHom`: the coordinates and
  injections exhibit the matrix module of `ρ ∘ σ` as `e` copies of that of `σ`.
* `Stacks.EtaleCohomology.matrixContinuousModuleBasisHom_comp_mulHom`: multiplication by `o` is the
  matrix `(π_k(o β_i))_{ki}`.
-/

@[expose] public noncomputable section

open CategoryTheory Matrix Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

section Hom

variable {Λ : Type} [CommRing Λ] {G : Type (u + 1)} [Group G] [TopologicalSpace G]

/-- A morphism of finite `Λ`-modules with continuous `G`-action from an equivariant linear map. -/
def finiteTypeContinuousModuleLinearHom
    {P Q : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G}
    (f : P.obj.obj.obj.V →ₗ[Λ] Q.obj.obj.obj.V)
    (hf : ∀ (g : G) (x : P.obj.obj.obj.V),
      f ((P.obj.obj.obj.ρ g).asHom.hom x) = (Q.obj.obj.obj.ρ g).asHom.hom (f x)) : P ⟶ Q :=
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom f
      comm := fun g => by
        ext x
        exact hf g x }))

/-- The underlying map of `finiteTypeContinuousModuleLinearHom f hf` is `f`. -/
@[simp]
theorem finiteTypeContinuousModuleLinearHom_apply
    {P Q : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G}
    (f : P.obj.obj.obj.V →ₗ[Λ] Q.obj.obj.obj.V) (hf) (x : P.obj.obj.obj.V) :
    (finiteTypeContinuousModuleLinearHom f hf).hom.hom.hom.hom.hom x = f x :=
  rfl

/-- Morphisms of finite continuous `Λ`-modules agree when their underlying maps do. -/
theorem finiteTypeContinuousModule_hom_ext_apply
    {P Q : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G} {f g : P ⟶ Q}
    (h : ∀ x, f.hom.hom.hom.hom.hom x = g.hom.hom.hom.hom.hom x) : f = g := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  exact LinearMap.ext h

/-- The underlying map of a finite sum of morphisms is the sum of the underlying maps. -/
theorem finiteTypeContinuousModule_hom_sum_apply
    {P Q : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G} {ι : Type*} (s : Finset ι)
    (f : ι → (P ⟶ Q)) (x : P.obj.obj.obj.V) :
    (∑ i ∈ s, f i).hom.hom.hom.hom.hom x = ∑ i ∈ s, (f i).hom.hom.hom.hom.hom x := by
  have := additive_continuousModuleToModuleCat.{0, u + 1, u + 1} Λ G
  let F := finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ G ⋙
    Stacks.Injectives.continuousModuleUnderlying.{0, u + 1, u + 1} Λ G
  have h := congrArg (fun φ => φ.hom x) (F.map_sum f s)
  simp only [ModuleCat.hom_sum] at h
  exact h.trans (LinearMap.sum_apply _ _ _)

/-- The underlying map of a composite is the composite of the underlying maps. -/
@[simp]
theorem finiteTypeContinuousModule_comp_apply
    {P Q R : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G} (f : P ⟶ Q) (g : Q ⟶ R)
    (x : P.obj.obj.obj.V) :
    (f ≫ g).hom.hom.hom.hom.hom x = g.hom.hom.hom.hom.hom (f.hom.hom.hom.hom.hom x) :=
  rfl

/-- The underlying map of the identity morphism is the identity. -/
@[simp]
theorem finiteTypeContinuousModule_id_apply (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G)
    (x : P.obj.obj.obj.V) : (𝟙 P : P ⟶ P).hom.hom.hom.hom.hom x = x :=
  rfl

/-- The underlying map of the zero morphism is zero. -/
@[simp]
theorem finiteTypeContinuousModule_zero_apply
    (P Q : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G) (x : P.obj.obj.obj.V) :
    (0 : P ⟶ Q).hom.hom.hom.hom.hom x = 0 :=
  rfl

/-- The underlying map of `finiteTypeContinuousModuleSMul Λ P c` is `x ↦ c • x`. -/
@[simp]
theorem finiteTypeContinuousModuleSMul_apply (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G)
    (c : Λ) (x : P.obj.obj.obj.V) :
    (finiteTypeContinuousModuleSMul Λ P c).hom.hom.hom.hom.hom x = c • x :=
  rfl

end Hom

section Matrix

variable (Λ : Type) [CommRing Λ] {G : Type (u + 1)} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {m m' m'' : ℕ}

/-- **The morphism of matrix modules of an intertwiner** `A` (`A σ(g) = σ'(g) A`): multiplication
by `A`. -/
def matrixContinuousModuleHom {σ : G →* GL (Fin m) Λ} {σ' : G →* GL (Fin m') Λ}
    (hσ : IsOpen (σ.ker : Set G)) (hσ' : IsOpen (σ'.ker : Set G)) (A : Matrix (Fin m') (Fin m) Λ)
    (hA : ∀ g, A * (σ g).val = (σ' g).val * A) :
    matrixContinuousModule.{u + 1, u + 1} Λ σ hσ ⟶ matrixContinuousModule.{u + 1, u + 1} Λ σ' hσ' :=
  finiteTypeContinuousModuleLinearHom
    ((ULift.moduleEquiv (R := Λ)).symm.toLinearMap ∘ₗ Matrix.toLin' A ∘ₗ
      (ULift.moduleEquiv (R := Λ)).toLinearMap)
    fun g x => ULift.ext (by
      change A *ᵥ ((σ g).val *ᵥ x.down) = (σ' g).val *ᵥ (A *ᵥ x.down)
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA g])

/-- The underlying map of `matrixContinuousModuleHom Λ hσ hσ' A hA` is `x ↦ A *ᵥ x`. -/
@[simp]
theorem matrixContinuousModuleHom_apply_down {σ : G →* GL (Fin m) Λ} {σ' : G →* GL (Fin m') Λ}
    (hσ : IsOpen (σ.ker : Set G)) (hσ' : IsOpen (σ'.ker : Set G)) (A : Matrix (Fin m') (Fin m) Λ)
    (hA : ∀ g, A * (σ g).val = (σ' g).val * A)
    (x : (matrixContinuousModule.{u + 1, u + 1} Λ σ hσ).obj.obj.obj.V) :
    ((matrixContinuousModuleHom Λ hσ hσ' A hA).hom.hom.hom.hom.hom x).down = A *ᵥ x.down :=
  rfl

/-- **Composition of intertwiners is composition of morphisms.** -/
theorem matrixContinuousModuleHom_comp {σ : G →* GL (Fin m) Λ} {σ' : G →* GL (Fin m') Λ}
    {σ'' : G →* GL (Fin m'') Λ} (hσ : IsOpen (σ.ker : Set G)) (hσ' : IsOpen (σ'.ker : Set G))
    (hσ'' : IsOpen (σ''.ker : Set G)) (A : Matrix (Fin m') (Fin m) Λ)
    (hA : ∀ g, A * (σ g).val = (σ' g).val * A) (A' : Matrix (Fin m'') (Fin m') Λ)
    (hA' : ∀ g, A' * (σ' g).val = (σ'' g).val * A') :
    matrixContinuousModuleHom Λ hσ hσ' A hA ≫ matrixContinuousModuleHom Λ hσ' hσ'' A' hA' =
      matrixContinuousModuleHom Λ hσ hσ'' (A' * A) (fun g => by
        rw [Matrix.mul_assoc, hA g, ← Matrix.mul_assoc, hA' g, Matrix.mul_assoc]) :=
  finiteTypeContinuousModule_hom_ext_apply fun x => ULift.ext (by
    show A' *ᵥ (A *ᵥ x.down) = (A' * A) *ᵥ x.down
    rw [Matrix.mulVec_mulVec])

/-- **The intertwiner `c • 1` is multiplication by `c`.** -/
theorem matrixContinuousModuleHom_smul_one {σ : G →* GL (Fin m) Λ}
    (hσ : IsOpen (σ.ker : Set G)) (c : Λ)
    (hA : ∀ g, (c • 1 : Matrix (Fin m) (Fin m) Λ) * (σ g).val = (σ g).val * (c • 1)) :
    matrixContinuousModuleHom Λ hσ hσ (c • 1) hA =
      finiteTypeContinuousModuleSMul Λ (matrixContinuousModule.{u + 1, u + 1} Λ σ hσ) c :=
  finiteTypeContinuousModule_hom_ext_apply fun x => ULift.ext (by
    show (c • 1 : Matrix (Fin m) (Fin m) Λ) *ᵥ x.down = c • x.down
    rw [Matrix.smul_mulVec, Matrix.one_mulVec])

/-- **Equal representations have isomorphic matrix modules** (the identity of `Λ^m`). -/
def matrixContinuousModuleIsoOfEq {σ₁ σ₂ : G →* GL (Fin m) Λ} (hσ₁ : IsOpen (σ₁.ker : Set G))
    (hσ₂ : IsOpen (σ₂.ker : Set G)) (h : ∀ g, σ₁ g = σ₂ g) :
    matrixContinuousModule.{u + 1, u + 1} Λ σ₁ hσ₁ ≅
      matrixContinuousModule.{u + 1, u + 1} Λ σ₂ hσ₂ where
  hom := matrixContinuousModuleHom Λ hσ₁ hσ₂ 1 fun g => by rw [h g, Matrix.one_mul, Matrix.mul_one]
  inv := matrixContinuousModuleHom Λ hσ₂ hσ₁ 1 fun g => by rw [h g, Matrix.one_mul, Matrix.mul_one]
  hom_inv_id := finiteTypeContinuousModule_hom_ext_apply fun x => ULift.ext (by
    change (1 : Matrix (Fin m) (Fin m) Λ) *ᵥ ((1 : Matrix (Fin m) (Fin m) Λ) *ᵥ x.down) = x.down
    rw [Matrix.one_mulVec, Matrix.one_mulVec])
  inv_hom_id := finiteTypeContinuousModule_hom_ext_apply fun x => ULift.ext (by
    change (1 : Matrix (Fin m) (Fin m) Λ) *ᵥ ((1 : Matrix (Fin m) (Fin m) Λ) *ᵥ x.down) = x.down
    rw [Matrix.one_mulVec, Matrix.one_mulVec])

end Matrix

section Splitting

variable {Λ Λ'' : Type} [CommRing Λ] [CommRing Λ''] [Finite Λ] [Finite Λ''] (ρ : Λ →+* Λ'')
  {e : ℕ} (β : Fin e → Λ'') (π : Fin e → Λ'' →+ Λ)
  (h₁ : ∀ i (c : Λ) (x : Λ''), π i (ρ c * x) = c * π i x)
  {G : Type (u + 1)} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {m : ℕ}
  {σ : G →* GL (Fin m) Λ} (hσ : IsOpen (σ.ker : Set G))
  (hσ'' : IsOpen (((Matrix.GeneralLinearGroup.map ρ).comp σ).ker : Set G))

/-- The `k`-th coordinate `v ↦ π_k ∘ v`, from the matrix module of `ρ ∘ σ` over `Λ''` read over
`Λ`, to the matrix module of `σ`. -/
def matrixContinuousModuleCoordHom (k : Fin e) :
    finiteTypeContinuousModuleRestrictScalars ρ
        (matrixContinuousModule.{u + 1, u + 1} Λ'' ((Matrix.GeneralLinearGroup.map ρ).comp σ)
          hσ'') ⟶ matrixContinuousModule.{u + 1, u + 1} Λ σ hσ :=
  finiteTypeContinuousModuleLinearHom
    { toFun := fun v => ULift.up fun t => π k ((show ULift.{u + 1} (Fin m → Λ'') from v).down t)
      map_add' := fun v w => ULift.ext (funext fun t => map_add (π k) _ _)
      map_smul' := fun c v => ULift.ext (funext fun t => h₁ k c _) }
    fun g x => ULift.ext (funext fun s => by
      change π k (((σ g).val.map ρ *ᵥ (show ULift.{u + 1} (Fin m → Λ'') from x).down) s) =
        ((σ g).val *ᵥ fun t => π k ((show ULift.{u + 1} (Fin m → Λ'') from x).down t)) s
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, h₁])

/-- The `i`-th injection `v ↦ ρ(v) β_i`, from the matrix module of `σ` to the matrix module of
`ρ ∘ σ` over `Λ''` read over `Λ`. -/
def matrixContinuousModuleBasisHom (i : Fin e) :
    matrixContinuousModule.{u + 1, u + 1} Λ σ hσ ⟶ finiteTypeContinuousModuleRestrictScalars ρ
        (matrixContinuousModule.{u + 1, u + 1} Λ'' ((Matrix.GeneralLinearGroup.map ρ).comp σ)
          hσ'') :=
  finiteTypeContinuousModuleLinearHom
    { toFun := fun v => (show ULift.{u + 1} (Fin m → Λ'') from
        ULift.up fun t => ρ ((show ULift.{u + 1} (Fin m → Λ) from v).down t) * β i)
      map_add' := fun v w => ULift.ext (funext fun t => by
        change ρ (_ + _) * β i = ρ _ * β i + ρ _ * β i
        rw [map_add, add_mul])
      map_smul' := fun c v => ULift.ext (funext fun t => by
        change ρ (c * _) * β i = ρ c * (ρ _ * β i)
        rw [map_mul, mul_assoc]) }
    fun g x => ULift.ext (funext fun s => by
      change ρ (((σ g).val *ᵥ (show ULift.{u + 1} (Fin m → Λ) from x).down) s) * β i =
        ((σ g).val.map ρ *ᵥ fun t => ρ ((show ULift.{u + 1} (Fin m → Λ) from x).down t) * β i) s
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul,
        mul_assoc])

/-- Multiplication by `o ∈ Λ''` on the matrix module of `ρ ∘ σ` over `Λ''`, read over `Λ`. -/
def matrixContinuousModuleRestrictScalarsMulHom (o : Λ'') :
    finiteTypeContinuousModuleRestrictScalars ρ
        (matrixContinuousModule.{u + 1, u + 1} Λ'' ((Matrix.GeneralLinearGroup.map ρ).comp σ)
          hσ'') ⟶ finiteTypeContinuousModuleRestrictScalars ρ
        (matrixContinuousModule.{u + 1, u + 1} Λ'' ((Matrix.GeneralLinearGroup.map ρ).comp σ)
          hσ'') :=
  finiteTypeContinuousModuleLinearHom
    { toFun := fun v => (show ULift.{u + 1} (Fin m → Λ'') from
        ULift.up (o • (show ULift.{u + 1} (Fin m → Λ'') from v).down))
      map_add' := fun v w => ULift.ext (smul_add o _ _)
      map_smul' := fun c v => ULift.ext (by
        change o • (ρ c • _) = ρ c • (o • _)
        rw [smul_comm]) }
    fun g x => ULift.ext (by
      change o • ((σ g).val.map ρ *ᵥ (show ULift.{u + 1} (Fin m → Λ'') from x).down) =
        (σ g).val.map ρ *ᵥ (o • (show ULift.{u + 1} (Fin m → Λ'') from x).down)
      rw [Matrix.mulVec_smul])

/-- Evaluating a finite sum in `ULift (Fin m → R)` at a coordinate is evaluating termwise. -/
private theorem ulift_fin_down_sum_apply {ι R : Type*} [AddCommMonoid R] {m : ℕ} (s : Finset ι)
    (f : ι → ULift.{u + 1} (Fin m → R)) (t : Fin m) :
    (∑ i ∈ s, f i).down t = ∑ i ∈ s, (f i).down t := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl

include h₁ in
/-- `ι_i ≫ π_j = δ_{ij}`. -/
theorem matrixContinuousModuleBasisHom_comp_coordHom
    (h₂ : ∀ i j, π j (β i) = if i = j then 1 else 0) (i j : Fin e) :
    matrixContinuousModuleBasisHom ρ β hσ hσ'' i ≫ matrixContinuousModuleCoordHom ρ π h₁ hσ hσ'' j =
      if i = j then 𝟙 _ else 0 := by
  apply finiteTypeContinuousModule_hom_ext_apply fun x => ?_
  refine ULift.ext (funext fun t => ?_)
  show π j (ρ ((show ULift.{u + 1} (Fin m → Λ) from x).down t) * β i) = _
  rw [h₁, h₂]
  split_ifs
  · rw [mul_one]
    rfl
  · rw [mul_zero]
    rfl

include h₁ in
/-- `Σ_i π_i ≫ ι_i = 𝟙`. -/
theorem sum_matrixContinuousModuleCoordHom_comp_basisHom
    (h₃ : ∀ x : Λ'', ∑ i, ρ (π i x) * β i = x) :
    ∑ i, matrixContinuousModuleCoordHom ρ π h₁ hσ hσ'' i ≫
        matrixContinuousModuleBasisHom ρ β hσ hσ'' i = 𝟙 _ := by
  apply finiteTypeContinuousModule_hom_ext_apply fun x => ?_
  refine (finiteTypeContinuousModule_hom_sum_apply _ _ x).trans ?_
  refine ULift.ext (funext fun t => ?_)
  exact (ulift_fin_down_sum_apply _ _ t).trans (h₃ _)

include h₁ in
/-- **Multiplication by `o ∈ Λ''` is the matrix `(π_k(o β_i))_{ki}`**: `ι_i ≫ (o • -) =
Σ_k π_k(o β_i) • ι_k`. -/
theorem matrixContinuousModuleBasisHom_comp_mulHom
    (h₃ : ∀ x : Λ'', ∑ i, ρ (π i x) * β i = x) (o : Λ'') (i : Fin e) :
    matrixContinuousModuleBasisHom ρ β hσ hσ'' i ≫
        matrixContinuousModuleRestrictScalarsMulHom ρ hσ'' o =
      ∑ k, finiteTypeContinuousModuleSMul Λ _ (π k (o * β i)) ≫
        matrixContinuousModuleBasisHom ρ β hσ hσ'' k := by
  apply finiteTypeContinuousModule_hom_ext_apply fun x => ?_
  refine Eq.trans ?_ (finiteTypeContinuousModule_hom_sum_apply _ _ x).symm
  refine ULift.ext (funext fun t => ?_)
  have hk : ∀ k, ((finiteTypeContinuousModuleSMul Λ _ (π k (o * β i)) ≫
      matrixContinuousModuleBasisHom ρ β hσ hσ'' k).hom.hom.hom.hom.hom x).down t =
        ρ (π k (o * β i)) * β k * ρ ((show ULift.{u + 1} (Fin m → Λ) from x).down t) := fun k => by
    change ρ (π k (o * β i) * _) * β k = _
    rw [map_mul, mul_right_comm]
    rfl
  refine Eq.trans ?_ (ulift_fin_down_sum_apply _ _ t).symm
  rw [Finset.sum_congr rfl fun k _ => hk k, ← Finset.sum_mul, h₃]
  show o * (ρ ((show ULift.{u + 1} (Fin m → Λ) from x).down t) * β i) = _
  ring

end Splitting

end Stacks.EtaleCohomology

end
