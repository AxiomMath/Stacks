module

public import StacksFrontier.AlgebraicGeometry.SymSectionsBaseChange.SectionRing
public import StacksFrontier.AlgebraicGeometry.TensorPowerTrivialize.GeneralModule

/-!
# The graded ring of sections of `Sym(E ⊗ L)` over an open trivializing `L`

Let `X` be a scheme, `E` an `𝒪_X`-module and `L` an `𝒪_X`-module which is **trivial over an open
`U`**, the data of such a trivialization being an isomorphism
`e : L|_U ≅ 𝒪_U` of sheaves of modules on the localized site over `U`. Then the sections of
`E ⊗ L` over `U` are the sections of `E` over `U`, by `t ↦ t ⊗ g` for `g` the section of `L`
corresponding to `1`; and if `U` is affine and `E` is quasi-coherent, **the graded rings of
sections of `Sym(E ⊗ L)` and of `Sym(E)` over `U` are isomorphic**.

## Main definitions

* `SymmetricAlgebra.mapEquiv`: a linear equivalence of modules induces a ring equivalence of
  their symmetric algebras, carrying the `n`-th symmetric power onto the `n`-th symmetric power.
* `Stacks.SymTwistChart.generator`: the section of `L` over `U` that the trivialization sends
  to `1`.
* `Stacks.SymTwistChart.sectionsEquiv`: the linear equivalence `Γ(E, U) ≃ Γ(E ⊗ L, U)` given by
  the trivialization.
* `Stacks.SymTwistChart.chartRingEquiv`: **the ring isomorphism of the graded section rings**
  `Γ(U, Sym(E)) ≃+* Γ(U, Sym(E ⊗ L))`.

## Main results

* `Stacks.SymTwistChart.sectionsEquiv_apply`: the equivalence on sections is `t ↦ t ⊗ g`.
* `Stacks.SymTwistChart.chartRingEquiv_mem_grading`: **the isomorphism respects the grading**, so
  it is an isomorphism of graded rings.

## Implementation notes

The trivialization is an isomorphism `e : L|_U ≅ 𝒪_U` on the localized site, the hypothesis
`Stacks.AlgebraicGeometry.TrivializingSite.IsTrivializing` records, and the equivalence of sections
is `Stacks.SheafOfModules.TensorGenerator.tensorSectionsEquiv`; `L` need not be invertible.

The structure sheaf of the localized site is written `X.ringCatSheaf.over U`, as in
`Stacks.SheafOfModules.isoUnitOverOfHom` and `IsTrivializing`. It is definitionally but not
syntactically equal to
`Stacks.SheafOfModules.SliceRestriction.sliceStructureSheaf X.sheaf.obj h𝒪 U`, and
`attribute [local implicit_reducible] TopCat.Sheaf sheafCompose` lets the latter be accepted where
the former is written.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.SheafOfModules
open Stacks.SheafOfModules.TensorSheafification

universe u

namespace SymmetricAlgebra

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N]

/-- **A linear equivalence of modules induces a ring equivalence of their symmetric algebras.**
This is `SymmetricAlgebra.mapₛₗ` along the identity of the base ring, made into an equivalence by
the map of the inverse. -/
public def mapEquiv (e : M ≃ₗ[R] N) : SymmetricAlgebra R M ≃+* SymmetricAlgebra R N where
  toFun := mapₛₗ (RingHom.id R) (e : M →ₗ[R] N)
  invFun := mapₛₗ (RingHom.id R) (e.symm : N →ₗ[R] M)
  left_inv x :=
    (mapₛₗ_eq_comp (φ := RingHom.id R) (ψ := RingHom.id R) (χ := RingHom.id R)
      (e : M →ₗ[R] N) (e.symm : N →ₗ[R] M) (LinearMap.id (R := R) (M := M))
      (fun _ => rfl) (fun m => (e.symm_apply_apply m).symm) x).symm.trans
    (mapₛₗ_eq_self (φ := RingHom.id R) (LinearMap.id (R := R) (M := M))
      (fun _ => rfl) (fun _ => rfl) x)
  right_inv x :=
    (mapₛₗ_eq_comp (φ := RingHom.id R) (ψ := RingHom.id R) (χ := RingHom.id R)
      (e.symm : N →ₗ[R] M) (e : M →ₗ[R] N) (LinearMap.id (R := R) (M := N))
      (fun _ => rfl) (fun m => (e.apply_symm_apply m).symm) x).symm.trans
    (mapₛₗ_eq_self (φ := RingHom.id R) (LinearMap.id (R := R) (M := N))
      (fun _ => rfl) (fun _ => rfl) x)
  map_mul' := map_mul _
  map_add' := map_add _

/-- The ring equivalence `mapEquiv e` sends the generator `ι R M m` to `ι R N (e m)`. -/
@[simp]
public theorem mapEquiv_ι (e : M ≃ₗ[R] N) (m : M) :
    mapEquiv e (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R N (e m) :=
  mapₛₗ_ι _ _ m

/-- The ring equivalence `mapEquiv e` fixes the image of the base ring `R`. -/
@[simp]
public theorem mapEquiv_algebraMap (e : M ≃ₗ[R] N) (r : R) :
    mapEquiv e (algebraMap R (SymmetricAlgebra R M) r) =
      algebraMap R (SymmetricAlgebra R N) r :=
  mapₛₗ_algebraMap _ _ r

/-- **The equivalence carries the `n`-th symmetric power onto the `n`-th symmetric power.** -/
public theorem mapEquiv_mem_symmetricPower (e : M ≃ₗ[R] N) (n : ℕ)
    (x : SymmetricAlgebra R M) :
    mapEquiv e x ∈ SymPow.symmetricPower n R N ↔ x ∈ SymPow.symmetricPower n R M := by
  refine ⟨fun h => ?_, fun h => mapₛₗ_mem_symmetricPower _ _ n h⟩
  have h' := mapₛₗ_mem_symmetricPower (RingHom.id R) (e.symm : N →ₗ[R] M) n h
  rwa [show mapₛₗ (RingHom.id R) (e.symm : N →ₗ[R] M) (mapEquiv e x) = x from
    (mapEquiv e).left_inv x] at h'

end SymmetricAlgebra

namespace Stacks.SymTwistChart

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {X : Scheme.{u}} (E L : X.Modules)

/-- The sheaf condition on the structure sheaf of a scheme, in the spelling the tensor product of
sheaves of modules is indexed by. -/
public abbrev isSheafStr : Presheaf.IsSheaf (Opens.grothendieckTopology X)
    (structureRingPresheaf X.sheaf.obj) := X.ringCatSheaf.property

/-- `E ⊗ L`, the tensor product of two modules on a scheme, formed through the underlying ringed
space. -/
public abbrev tensorObj : X.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _
    X.sheaf.obj (forget₂ CommRingCat RingCat) (isSheafStr (X := X))⟩).obj E).obj L

variable [E.IsQuasicoherent] [(tensorObj E L).IsQuasicoherent]
  (hqcE : Stacks.SymGraded.IsQuasicoherentPieces E)
  (hqcEL : Stacks.SymGraded.IsQuasicoherentPieces (tensorObj E L))
  {U : X.Opens} (e : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))

/-- **The section of `L` over `U` that a trivialization sends to `1`.** -/
public abbrev generator : Γ(L, U) :=
  TensorGenerator.generator X.sheaf.obj (isSheafStr (X := X)) U L e

/-- **The sections of `E ⊗ L` over an open trivializing `L` are the sections of `E`.** The
equivalence is `t ↦ t ⊗ g` for `g` the section of `L` corresponding to `1`. -/
public def sectionsEquiv : Γ(E, U) ≃ₗ[Γ(X, U)] Γ(tensorObj E L, U) :=
  TensorGenerator.tensorSectionsEquiv X.sheaf.obj (isSheafStr (X := X)) U E L e

omit [SheafOfModules.IsQuasicoherent E] [SheafOfModules.IsQuasicoherent (tensorObj E L)] in
/-- **The equivalence is `t ↦ t ⊗ g`**, for `g` the section of `L` corresponding to `1`. -/
public theorem sectionsEquiv_apply (t : Γ(E, U)) :
    sectionsEquiv E L e t =
      tensorSectionsAt X.sheaf.obj (isSheafStr (X := X)) (op U) E L t (generator L e) :=
  TensorGenerator.tensorSectionsEquiv_apply X.sheaf.obj (isSheafStr (X := X)) U E L e t

/-- **The graded rings of sections of `Sym(E)` and of `Sym(E ⊗ L)` over an affine open
trivializing `L` are isomorphic.**

The isomorphism is `SymmetricAlgebra.mapEquiv (sectionsEquiv E L e)`, read on both sides through
`Stacks.SymGraded.AffinePieces.symSectionRingEquiv`. -/
public def chartRingEquiv (hUaff : IsAffineOpen U) :
    (Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).sectionRing U ≃+*
      (Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).sectionRing U :=
  ((Stacks.SymGraded.AffinePieces.symSectionRingEquiv E hUaff hqcE).trans
      (SymmetricAlgebra.mapEquiv (sectionsEquiv E L e))).trans
    (Stacks.SymGraded.AffinePieces.symSectionRingEquiv (tensorObj E L) hUaff hqcEL).symm

/-- **The isomorphism respects the grading**, so it is an isomorphism of graded rings. -/
public theorem chartRingEquiv_mem_grading (hUaff : IsAffineOpen U) (n : ℕ)
    (x : (Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).sectionRing U) :
    chartRingEquiv E L hqcE hqcEL e hUaff x ∈
        (Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).grading U n ↔
      x ∈ (Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).grading U n := by
  rw [← Stacks.SymGraded.AffinePieces.mem_symmetricPower_symSectionRingEquiv
      (tensorObj E L) hUaff hqcEL n,
    ← Stacks.SymGraded.AffinePieces.mem_symmetricPower_symSectionRingEquiv E hUaff hqcE n]
  refine Iff.trans (Iff.of_eq (congrArg
    (fun y => y ∈ SymPow.symmetricPower n Γ(X, U) Γ(tensorObj E L, U)) ?_))
    (SymmetricAlgebra.mapEquiv_mem_symmetricPower (sectionsEquiv E L e) n _)
  exact (Stacks.SymGraded.AffinePieces.symSectionRingEquiv
    (tensorObj E L) hUaff hqcEL).apply_symm_apply _

end Stacks.SymTwistChart

end
