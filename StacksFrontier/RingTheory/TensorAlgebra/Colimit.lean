module

public import Mathlib.Algebra.Colimit.Module
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tensor, symmetric and exterior algebras commute with directed colimits

Forming the tensor, symmetric or exterior algebra of a module commutes with filtered
(directed) colimits.

Throughout, `G : ι → Type*` is a directed system of `R`-modules over a directed preorder `ι`,
with transition maps `f i j h : G i →ₗ[R] G j`; the colimit of the modules is
`Module.DirectLimit G f`. Applying the tensor algebra functor to each `G i` gives a directed
system of `R`-algebras whose colimit is the generic `DirectLimit` of algebras, and the canonical
algebra map from that colimit to `TensorAlgebra R (Module.DirectLimit G f)` is an isomorphism.
The tensor and symmetric constructions work over a commutative semiring with additive
commutative monoid modules; the exterior construction requires a commutative ring and additive
commutative group modules. The base, index type and modules may lie in independent universes.

## Main results

* `TensorAlgebra.ofDirectLimit_bijective`, `SymmetricAlgebra.ofDirectLimit_bijective`,
  `ExteriorAlgebra.ofDirectLimit_bijective`: the canonical algebra maps
  `colim T(M_i) → T(colim M_i)`, `colim Sym(M_i) → Sym(colim M_i)` and
  `colim ⋀(M_i) → ⋀(colim M_i)` are bijective (Stacks 00DQ).
* `TensorAlgebra.equivDirectLimit`, `SymmetricAlgebra.equivDirectLimit`,
  `ExteriorAlgebra.equivDirectLimit`: the corresponding algebra isomorphisms.
* `SymmetricAlgebra.isSymmetricAlgebra_directLimit`: `colim Sym(M_i)` is a symmetric algebra
  of `colim M_i`.
-/

@[expose] public section

section TensorMap

variable {R : Type*} [CommSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable {P : Type*} [AddCommMonoid P] [Module R P]

/-- Functoriality of the tensor algebra: a linear map `M →ₗ[R] N` induces an algebra
homomorphism `TensorAlgebra R M →ₐ[R] TensorAlgebra R N`. -/
noncomputable def TensorAlgebra.map (φ : M →ₗ[R] N) :
    TensorAlgebra R M →ₐ[R] TensorAlgebra R N :=
  TensorAlgebra.lift R (TensorAlgebra.ι R ∘ₗ φ)

/-- `TensorAlgebra.map φ` sends the generator `ι R m` to `ι R (φ m)`. -/
@[simp] lemma TensorAlgebra.map_apply_ι (φ : M →ₗ[R] N) (m : M) :
    TensorAlgebra.map φ (TensorAlgebra.ι R m) = TensorAlgebra.ι R (φ m) := by
  rw [TensorAlgebra.map, TensorAlgebra.lift_ι_apply, LinearMap.comp_apply]

/-- The tensor algebra functor sends the identity to the identity. -/
@[simp] lemma TensorAlgebra.map_id :
    TensorAlgebra.map (LinearMap.id : M →ₗ[R] M) = AlgHom.id R (TensorAlgebra R M) := by
  apply TensorAlgebra.hom_ext
  ext m
  simp

/-- The tensor algebra functor preserves composition. -/
@[simp] lemma TensorAlgebra.map_comp_map (φ : M →ₗ[R] N) (ψ : N →ₗ[R] P) :
    (TensorAlgebra.map ψ).comp (TensorAlgebra.map φ) = TensorAlgebra.map (ψ ∘ₗ φ) := by
  apply TensorAlgebra.hom_ext
  ext m
  simp

end TensorMap

section System

variable {R : Type*} [CommSemiring R]
variable {ι : Type*} [Preorder ι] [DecidableEq ι] [IsDirectedOrder ι] [Nonempty ι]
variable {G : ι → Type*} [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j) [DirectedSystem G (fun i j h => f i j h)]

/-- Transition algebra maps of the directed system of tensor algebras. -/
noncomputable def tensorTrans (i j : ι) (h : i ≤ j) :
    TensorAlgebra R (G i) →ₐ[R] TensorAlgebra R (G j) :=
  TensorAlgebra.map (f i j h)

/-- The tensor algebras of a directed system of modules form a directed system of algebras. -/
instance :
    DirectedSystem (fun i => TensorAlgebra R (G i)) (fun i j h => tensorTrans f i j h) where
  map_self := by
    intro i x
    have h0 : f i i le_rfl = LinearMap.id := by
      ext y; rw [LinearMap.id_apply, DirectedSystem.map_self' (f := f)]
    rw [tensorTrans, h0, TensorAlgebra.map_id, AlgHom.id_apply]
  map_map := by
    intro k j i hij hjk x
    have hc : f j k hjk ∘ₗ f i j hij = f i k (hij.trans hjk) := by
      ext y; rw [LinearMap.comp_apply, DirectedSystem.map_map' (f := f)]
    unfold tensorTrans
    rw [← AlgHom.comp_apply, TensorAlgebra.map_comp_map, hc]

/-- The colimit of the directed system of tensor algebras. -/
abbrev TensorColim :=
  DirectLimit (fun i => TensorAlgebra R (G i)) (tensorTrans f)

/-- The canonical map `colim T(M_i) → T(colim M_i)`. -/
noncomputable def TensorAlgebra.ofDirectLimit :
    TensorColim f →ₐ[R] TensorAlgebra R (Module.DirectLimit G f) :=
  DirectLimit.Algebra.lift (fun i => TensorAlgebra R (G i)) (tensorTrans f) _
    (fun i => TensorAlgebra.map (Module.DirectLimit.of R ι G f i))
    (fun i j hij x => by
      rw [tensorTrans]
      have hof : Module.DirectLimit.of R ι G f j ∘ₗ f i j hij
          = Module.DirectLimit.of R ι G f i := by
        ext y; rw [LinearMap.comp_apply, Module.DirectLimit.of_f]
      rw [← AlgHom.comp_apply, TensorAlgebra.map_comp_map, hof])

/-- Linear part of the inverse map `T(colim M_i) → colim T(M_i)`. -/
noncomputable def tensorPsiAux :
    Module.DirectLimit G f →ₗ[R] TensorColim f :=
  Module.DirectLimit.lift R ι G f
    (fun i =>
      (DirectLimit.Algebra.of (fun i => TensorAlgebra R (G i)) (tensorTrans f) i).toLinearMap
        ∘ₗ TensorAlgebra.ι R)
    (fun i j hij x => by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
      rw [← DirectLimit.Algebra.of_f hij, tensorTrans, TensorAlgebra.map_apply_ι])

/-- The inverse map `T(colim M_i) → colim T(M_i)`. -/
noncomputable def TensorAlgebra.toDirectLimit :
    TensorAlgebra R (Module.DirectLimit G f) →ₐ[R] TensorColim f :=
  TensorAlgebra.lift R (tensorPsiAux f)

/-- `TensorAlgebra.ofDirectLimit` sends the class of `y ∈ T(M_i)` to the image of `y` under the
tensor algebra map induced by `M_i → colim M_i`. -/
@[simp] lemma TensorAlgebra.ofDirectLimit_mk (i : ι) (y : TensorAlgebra R (G i)) :
    TensorAlgebra.ofDirectLimit f ⟦⟨i, y⟩⟧ =
      TensorAlgebra.map (Module.DirectLimit.of R ι G f i) y := by
  rw [← DirectLimit.Algebra.of_apply, TensorAlgebra.ofDirectLimit, DirectLimit.Algebra.lift_of]

/-- `TensorAlgebra.toDirectLimit` sends the generator of `x ∈ M_i` viewed in `colim M_i` to the
class of the generator `ι R x ∈ T(M_i)`. -/
@[simp] lemma TensorAlgebra.toDirectLimit_ι_of (i : ι) (x : G i) :
    TensorAlgebra.toDirectLimit f (TensorAlgebra.ι R (Module.DirectLimit.of R ι G f i x)) =
      (⟦⟨i, TensorAlgebra.ι R x⟩⟧ : TensorColim f) := by
  simp [TensorAlgebra.toDirectLimit, tensorPsiAux]

/-- `TensorAlgebra.ofDirectLimit` is a left inverse of
`TensorAlgebra.toDirectLimit`. -/
lemma TensorAlgebra.ofDirectLimit_comp_toDirectLimit :
    (TensorAlgebra.ofDirectLimit f).comp (TensorAlgebra.toDirectLimit f) = AlgHom.id R _ := by
  ext i x
  simp

/-- `TensorAlgebra.toDirectLimit` is a left inverse of
`TensorAlgebra.ofDirectLimit`. -/
lemma TensorAlgebra.toDirectLimit_comp_ofDirectLimit :
    (TensorAlgebra.toDirectLimit f).comp (TensorAlgebra.ofDirectLimit f) = AlgHom.id R _ := by
  ext i x
  simp

/-- The natural algebra isomorphism `T(colim M_i) ≅ colim T(M_i)`. -/
noncomputable def TensorAlgebra.equivDirectLimit :
    TensorAlgebra R (Module.DirectLimit G f) ≃ₐ[R] TensorColim f :=
  AlgEquiv.ofAlgHom (TensorAlgebra.toDirectLimit f) (TensorAlgebra.ofDirectLimit f)
    (TensorAlgebra.toDirectLimit_comp_ofDirectLimit f)
    (TensorAlgebra.ofDirectLimit_comp_toDirectLimit f)

/-- Forming the tensor algebra commutes with directed colimits: the canonical algebra map
`colim T(M_i) → T(colim M_i)` is a bijection. -/
@[stacks 00DQ "tensor"]
theorem TensorAlgebra.ofDirectLimit_bijective :
    Function.Bijective (TensorAlgebra.ofDirectLimit f) := by
  exact (TensorAlgebra.equivDirectLimit f).symm.bijective

end System

section SymmetricMap

variable {R : Type*} [CommSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable {P : Type*} [AddCommMonoid P] [Module R P]

/-- Functoriality of the symmetric algebra: a linear map `M →ₗ[R] N` induces an algebra
homomorphism `SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R N`. -/
@[ega "II 1.7.1" "action on morphisms",
  ega "II 1.7.2" "special case",
  ega "II 2.9.5" "symmetric-algebra target",
  ega "II 4.1.2" "special case"]
noncomputable def symmetricAlgebraMap (φ : M →ₗ[R] N) :
    SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R N :=
  SymmetricAlgebra.lift (SymmetricAlgebra.ι R N ∘ₗ φ)

/-- `symmetricAlgebraMap φ` sends the generator `ι R M m` to `ι R N (φ m)`. -/
@[simp,
  ega "II 1.7.1" "partial",
  ega "II 2.9.5" "special case"]
lemma symmetricAlgebraMap_ι (φ : M →ₗ[R] N) (m : M) :
    symmetricAlgebraMap φ (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R N (φ m) := by
  rw [symmetricAlgebraMap, SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply]

/-- The symmetric algebra functor sends the identity to the identity. -/
@[ega "II 1.7.1" "identity law"]
lemma symmetricAlgebraMap_id :
    symmetricAlgebraMap (LinearMap.id : M →ₗ[R] M) = AlgHom.id R (SymmetricAlgebra R M) := by
  apply SymmetricAlgebra.algHom_ext
  ext m
  simp

/-- The symmetric algebra functor preserves composition. -/
@[ega "II 1.7.1" "composition law"]
lemma symmetricAlgebraMap_comp (φ : M →ₗ[R] N) (ψ : N →ₗ[R] P) :
    (symmetricAlgebraMap ψ).comp (symmetricAlgebraMap φ) = symmetricAlgebraMap (ψ ∘ₗ φ) := by
  apply SymmetricAlgebra.algHom_ext
  ext m
  simp

end SymmetricMap

section SymmetricSystem

variable {R : Type*} [CommSemiring R]
variable {ι : Type*} [Preorder ι] [DecidableEq ι] [IsDirectedOrder ι] [Nonempty ι]
variable {G : ι → Type*} [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j) [DirectedSystem G (fun i j h => f i j h)]

/-- Transition algebra maps of the directed system of symmetric algebras. -/
noncomputable def symmetricTrans (i j : ι) (h : i ≤ j) :
    SymmetricAlgebra R (G i) →ₐ[R] SymmetricAlgebra R (G j) :=
  symmetricAlgebraMap (f i j h)

/-- The symmetric algebras of a directed system of modules form a directed system of
algebras. -/
instance :
    DirectedSystem (fun i => SymmetricAlgebra R (G i)) (fun i j h => symmetricTrans f i j h) where
  map_self := by
    intro i x
    have h0 : f i i le_rfl = LinearMap.id := by
      ext y; rw [LinearMap.id_apply, DirectedSystem.map_self' (f := f)]
    rw [symmetricTrans, h0, symmetricAlgebraMap_id, AlgHom.id_apply]
  map_map := by
    intro k j i hij hjk x
    have hc : f j k hjk ∘ₗ f i j hij = f i k (hij.trans hjk) := by
      ext y; rw [LinearMap.comp_apply, DirectedSystem.map_map' (f := f)]
    unfold symmetricTrans
    rw [← AlgHom.comp_apply, symmetricAlgebraMap_comp, hc]

/-- The colimit of the directed system of symmetric algebras. -/
abbrev SymmetricColim :=
  DirectLimit (fun i => SymmetricAlgebra R (G i)) (symmetricTrans f)

/-- The canonical map `colim Sym(M_i) → Sym(colim M_i)`. -/
noncomputable def SymmetricAlgebra.ofDirectLimit :
    SymmetricColim f →ₐ[R] SymmetricAlgebra R (Module.DirectLimit G f) :=
  DirectLimit.Algebra.lift (fun i => SymmetricAlgebra R (G i)) (symmetricTrans f) _
    (fun i => symmetricAlgebraMap (Module.DirectLimit.of R ι G f i))
    (fun i j hij x => by
      rw [symmetricTrans]
      have hof : Module.DirectLimit.of R ι G f j ∘ₗ f i j hij
          = Module.DirectLimit.of R ι G f i := by
        ext y; rw [LinearMap.comp_apply, Module.DirectLimit.of_f]
      rw [← AlgHom.comp_apply, symmetricAlgebraMap_comp, hof])

/-- The canonical linear map `colim M_i → colim Sym(M_i)`. -/
noncomputable def SymmetricAlgebra.ιDirectLimit :
    Module.DirectLimit G f →ₗ[R] SymmetricColim f :=
  Module.DirectLimit.lift R ι G f
    (fun i =>
      (DirectLimit.Algebra.of (fun i => SymmetricAlgebra R (G i)) (symmetricTrans f) i).toLinearMap
        ∘ₗ SymmetricAlgebra.ι R (G i))
    (fun i j hij x => by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
      rw [← DirectLimit.Algebra.of_f hij, symmetricTrans, symmetricAlgebraMap_ι])

/-- The inverse map `Sym(colim M_i) → colim Sym(M_i)`. -/
noncomputable def SymmetricAlgebra.toDirectLimit :
    SymmetricAlgebra R (Module.DirectLimit G f) →ₐ[R] SymmetricColim f :=
  SymmetricAlgebra.lift (SymmetricAlgebra.ιDirectLimit f)

/-- `SymmetricAlgebra.ofDirectLimit` sends the class of `y ∈ Sym(M_i)` to the image of `y` under
the symmetric algebra map induced by `M_i → colim M_i`. -/
@[simp] lemma SymmetricAlgebra.ofDirectLimit_mk (i : ι) (y : SymmetricAlgebra R (G i)) :
    SymmetricAlgebra.ofDirectLimit f ⟦⟨i, y⟩⟧ =
      symmetricAlgebraMap (Module.DirectLimit.of R ι G f i) y := by
  rw [← DirectLimit.Algebra.of_apply, SymmetricAlgebra.ofDirectLimit, DirectLimit.Algebra.lift_of]

/-- `SymmetricAlgebra.toDirectLimit` sends the generator of `x ∈ M_i` viewed in `colim M_i` to
the class of the generator `ι R (G i) x ∈ Sym(M_i)`. -/
@[simp] lemma SymmetricAlgebra.toDirectLimit_ι_of (i : ι) (x : G i) :
    SymmetricAlgebra.toDirectLimit f (SymmetricAlgebra.ι R _ (Module.DirectLimit.of R ι G f i x)) =
      (⟦⟨i, SymmetricAlgebra.ι R (G i) x⟩⟧ : SymmetricColim f) := by
  simp [SymmetricAlgebra.toDirectLimit, SymmetricAlgebra.ιDirectLimit]

/-- `SymmetricAlgebra.ofDirectLimit` is a left inverse of
`SymmetricAlgebra.toDirectLimit`. -/
lemma SymmetricAlgebra.ofDirectLimit_comp_toDirectLimit :
    (SymmetricAlgebra.ofDirectLimit f).comp (SymmetricAlgebra.toDirectLimit f) = AlgHom.id R _ := by
  ext i x
  simp

/-- `SymmetricAlgebra.toDirectLimit` is a left inverse of
`SymmetricAlgebra.ofDirectLimit`. -/
lemma SymmetricAlgebra.toDirectLimit_comp_ofDirectLimit :
    (SymmetricAlgebra.toDirectLimit f).comp (SymmetricAlgebra.ofDirectLimit f) = AlgHom.id R _ := by
  ext i x
  simp

/-- The natural algebra isomorphism `Sym(colim M_i) ≅ colim Sym(M_i)`. -/
noncomputable def SymmetricAlgebra.equivDirectLimit :
    SymmetricAlgebra R (Module.DirectLimit G f) ≃ₐ[R] SymmetricColim f :=
  AlgEquiv.ofAlgHom (SymmetricAlgebra.toDirectLimit f) (SymmetricAlgebra.ofDirectLimit f)
    (SymmetricAlgebra.toDirectLimit_comp_ofDirectLimit f)
    (SymmetricAlgebra.ofDirectLimit_comp_toDirectLimit f)

/-- Forming the symmetric algebra commutes with directed colimits: the canonical algebra map
`colim Sym(M_i) → Sym(colim M_i)` is a bijection. -/
@[stacks 00DQ "symmetric"]
theorem SymmetricAlgebra.ofDirectLimit_bijective :
    Function.Bijective (SymmetricAlgebra.ofDirectLimit f) := by
  exact (SymmetricAlgebra.equivDirectLimit f).symm.bijective

/-- The canonical map `colim M_i → colim Sym(M_i)` exhibits `colim Sym(M_i)` as the symmetric
algebra of `colim M_i`. -/
theorem SymmetricAlgebra.isSymmetricAlgebra_directLimit :
    IsSymmetricAlgebra (SymmetricAlgebra.ιDirectLimit f) :=
  IsSymmetricAlgebra.of_equiv (SymmetricAlgebra.equivDirectLimit f) <| by
    ext i x
    simp [SymmetricAlgebra.equivDirectLimit, SymmetricAlgebra.toDirectLimit]

end SymmetricSystem

section ExteriorSystem

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Preorder ι] [DecidableEq ι] [IsDirectedOrder ι] [Nonempty ι]
variable {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j) [DirectedSystem G (fun i j h => f i j h)]

/-- Transition algebra maps of the directed system of exterior algebras. -/
noncomputable def exteriorTrans (i j : ι) (h : i ≤ j) :
    ExteriorAlgebra R (G i) →ₐ[R] ExteriorAlgebra R (G j) :=
  ExteriorAlgebra.map (f i j h)

/-- The exterior algebras of a directed system of modules form a directed system of
algebras. -/
instance :
    DirectedSystem (fun i => ExteriorAlgebra R (G i)) (fun i j h => exteriorTrans f i j h) where
  map_self := by
    intro i x
    have h0 : f i i le_rfl = LinearMap.id := by
      ext y; rw [LinearMap.id_apply, DirectedSystem.map_self' (f := f)]
    rw [exteriorTrans, h0, ExteriorAlgebra.map_id, AlgHom.id_apply]
  map_map := by
    intro k j i hij hjk x
    have hc : f j k hjk ∘ₗ f i j hij = f i k (hij.trans hjk) := by
      ext y; rw [LinearMap.comp_apply, DirectedSystem.map_map' (f := f)]
    unfold exteriorTrans
    rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, hc]

/-- The colimit of the directed system of exterior algebras. -/
abbrev ExteriorColim :=
  DirectLimit (fun i => ExteriorAlgebra R (G i)) (exteriorTrans f)

/-- The canonical map `colim ⋀(M_i) → ⋀(colim M_i)`. -/
noncomputable def ExteriorAlgebra.ofDirectLimit :
    ExteriorColim f →ₐ[R] ExteriorAlgebra R (Module.DirectLimit G f) :=
  DirectLimit.Algebra.lift (fun i => ExteriorAlgebra R (G i)) (exteriorTrans f) _
    (fun i => ExteriorAlgebra.map (Module.DirectLimit.of R ι G f i))
    (fun i j hij x => by
      rw [exteriorTrans]
      have hof : Module.DirectLimit.of R ι G f j ∘ₗ f i j hij
          = Module.DirectLimit.of R ι G f i := by
        ext y; rw [LinearMap.comp_apply, Module.DirectLimit.of_f]
      rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, hof])

/-- Linear part of the inverse map `⋀(colim M_i) → colim ⋀(M_i)`. -/
noncomputable def exteriorPsiAux :
    Module.DirectLimit G f →ₗ[R] ExteriorColim f :=
  Module.DirectLimit.lift R ι G f
    (fun i =>
      (DirectLimit.Algebra.of (fun i => ExteriorAlgebra R (G i)) (exteriorTrans f) i).toLinearMap
        ∘ₗ ExteriorAlgebra.ι R)
    (fun i j hij x => by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
      rw [← DirectLimit.Algebra.of_f hij, exteriorTrans, ExteriorAlgebra.map_apply_ι])

/-- The inverse map `⋀(colim M_i) → colim ⋀(M_i)`. -/
noncomputable def ExteriorAlgebra.toDirectLimit :
    ExteriorAlgebra R (Module.DirectLimit G f) →ₐ[R] ExteriorColim f :=
  ExteriorAlgebra.lift R ⟨exteriorPsiAux f, by
    intro m
    induction m using Module.DirectLimit.induction_on with
    | _ i x =>
      rw [exteriorPsiAux, Module.DirectLimit.lift_of]
      rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
      rw [← map_mul, ExteriorAlgebra.ι_sq_zero, map_zero]⟩

/-- `ExteriorAlgebra.ofDirectLimit` sends the class of `y ∈ ⋀(M_i)` to the image of `y` under
the exterior algebra map induced by `M_i → colim M_i`. -/
@[simp] lemma ExteriorAlgebra.ofDirectLimit_mk (i : ι) (y : ExteriorAlgebra R (G i)) :
    ExteriorAlgebra.ofDirectLimit f ⟦⟨i, y⟩⟧ =
      ExteriorAlgebra.map (Module.DirectLimit.of R ι G f i) y := by
  rw [← DirectLimit.Algebra.of_apply, ExteriorAlgebra.ofDirectLimit, DirectLimit.Algebra.lift_of]

/-- `ExteriorAlgebra.toDirectLimit` sends the generator of `x ∈ M_i` viewed in `colim M_i` to
the class of the generator `ι R x ∈ ⋀(M_i)`. -/
@[simp] lemma ExteriorAlgebra.toDirectLimit_ι_of (i : ι) (x : G i) :
    ExteriorAlgebra.toDirectLimit f (ExteriorAlgebra.ι R (Module.DirectLimit.of R ι G f i x)) =
      (⟦⟨i, ExteriorAlgebra.ι R x⟩⟧ : ExteriorColim f) := by
  simp [ExteriorAlgebra.toDirectLimit, exteriorPsiAux]

/-- `ExteriorAlgebra.ofDirectLimit` is a left inverse of
`ExteriorAlgebra.toDirectLimit`. -/
lemma ExteriorAlgebra.ofDirectLimit_comp_toDirectLimit :
    (ExteriorAlgebra.ofDirectLimit f).comp (ExteriorAlgebra.toDirectLimit f) = AlgHom.id R _ := by
  ext i x
  simp

/-- `ExteriorAlgebra.toDirectLimit` is a left inverse of
`ExteriorAlgebra.ofDirectLimit`. -/
lemma ExteriorAlgebra.toDirectLimit_comp_ofDirectLimit :
    (ExteriorAlgebra.toDirectLimit f).comp (ExteriorAlgebra.ofDirectLimit f) = AlgHom.id R _ := by
  ext i x
  simp

/-- The natural algebra isomorphism `⋀(colim M_i) ≅ colim ⋀(M_i)`. -/
noncomputable def ExteriorAlgebra.equivDirectLimit :
    ExteriorAlgebra R (Module.DirectLimit G f) ≃ₐ[R] ExteriorColim f :=
  AlgEquiv.ofAlgHom (ExteriorAlgebra.toDirectLimit f) (ExteriorAlgebra.ofDirectLimit f)
    (ExteriorAlgebra.toDirectLimit_comp_ofDirectLimit f)
    (ExteriorAlgebra.ofDirectLimit_comp_toDirectLimit f)

/-- Forming the exterior algebra commutes with directed colimits: the canonical algebra map
`colim ⋀(M_i) → ⋀(colim M_i)` is a bijection. -/
@[stacks 00DQ "exterior"]
theorem ExteriorAlgebra.ofDirectLimit_bijective :
    Function.Bijective (ExteriorAlgebra.ofDirectLimit f) := by
  exact (ExteriorAlgebra.equivDirectLimit f).symm.bijective

end ExteriorSystem
