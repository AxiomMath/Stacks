module

public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Site
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.LinearAlgebra.SymmetricPower.BaseChange

/-!
# The symmetric powers of the sections of a quasi-coherent module are a base change

Let `X` be a scheme, `N` a quasi-coherent `𝒪_X`-module and `U ≤ U'` two affine opens of `X`.
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isBaseChange_restrictₗ` says that the
restriction map on sections exhibits `Γ(N, U)` as the base change of `Γ(N, U')` along
`Γ(X, U') ⟶ Γ(X, U)`. **This file proves the same for the symmetric powers of the sections**:

`Sym^n_{Γ(X, U)}(Γ(N, U)) = Γ(X, U) ⊗_{Γ(X, U')} Sym^n_{Γ(X, U')}(Γ(N, U'))`.

This is the geometric form of `SymPow.baseChangeEquiv`, stated for the semilinear restriction
maps `Stacks.SymGraded.gradedMapₛₗ` of the homogeneous pieces of the sectionwise symmetric
algebra.

## Main definitions

* `Stacks.SymGraded.restrictSemilinear`: restriction of sections of a module on a scheme, as a
  map semilinear along the restriction map of the structure sheaf.
* `Stacks.SymGraded.gradedModuleOfLE`: the `Γ(X, U')`-module structure on
  `Sym^n_{Γ(X, U)}(Γ(N, U))` obtained by restricting scalars, for `U ≤ U'`.
* `Stacks.SymGraded.gradedRestrictₗ`: the induced map of degree-`n` graded pieces, as a
  `Γ(X, U')`-linear map for that structure.

## Main results

* `Stacks.SymGraded.isBaseChange_gradedRestrictₗ`: **the main result**, as described above, for a
  nonnegative degree.
* `Stacks.SymGraded.isBaseChange_gradedRestrictₗ_of_neg`: the same in a negative degree, where
  both pieces are zero.
* `Stacks.SymGraded.isBaseChange_gradedRestrictₗ_int`: the two combined, for every `n : ℤ`.
* `SymPow.symAlgBaseChangeHom_one_tmul_prod_ι`: the base change homomorphism of symmetric
  algebras carries `1 ⊗ (a product of degree-one generators)` to the product of the
  corresponding generators. This is the computation rule `SymPow.baseChangeEquiv` is pinned down
  by, and the only one needed here.

## Implementation notes

**Why the statement is `IsBaseChange` and not an isomorphism.** `SymPow.baseChangeEquiv` is an
isomorphism `B ⊗[A] Sym^n_A(M) ≃ₗ[B] Sym^n_B(B ⊗[A] M)`, whose right-hand side mentions the
tensor product again. A consumer holding a scheme has `Γ(N, U)` and not `Γ(X, U) ⊗ Γ(N, U')`, and
the identification of those two is itself an `IsBaseChange`. Composing the two identifications
*inside* an `IsBaseChange` statement about the restriction map is what makes the result usable:
the conclusion mentions only the restriction maps of `N` and of the structure sheaf.

**The scalar structures are explicit.** For `U ≤ U'` the ring `Γ(X, U)` is not an algebra over
`Γ(X, U')` by instance search, so the `Algebra`, `Module` and `IsScalarTower` instances are
supplied by `Stacks.AlgebraicGeometry.QuasicoherentBaseChange.algebraOfLE`,
`Stacks.SymGraded.gradedModuleOfLE` and `Stacks.SymGraded.gradedIsScalarTowerOfLE`, and appear as
`letI`s in the statements. This is where the `Γ(X, U')`-module structure on the target comes
from, and it is why the statement is possible at all: an `A`-module structure on `Sym^n_B(-)`
exists in the purely algebraic setting only as a `local instance` of
`StacksFrontier.LinearAlgebra.SymmetricPower.BaseChange`, which a consumer cannot name.

**Degrees.** `Stacks.SymGraded.gradedPiece` is `ℤ`-indexed and agrees with
`SymPow.symmetricPower` on a natural number by `rfl`, so `SymPow.baseChangeEquiv` plugs into the
nonnegative case with no transport. The negative case is separate because both sides are then the
zero submodule, and the base-change property of a map between two trivial modules is proved
rather than instantiated.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)

## Not done here

No tag is claimed. Tag 01I9 is the base change of the sections of a quasi-coherent module
themselves, which is `isBaseChange_restrictₗ` elsewhere; this file applies it to the symmetric
powers, which is not an assertion of that tag.

Nothing here concludes quasi-coherence of anything. Converting these base-change statements into
quasi-coherence of the homogeneous pieces of
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebra` needs a comparison between the restriction
to an open of a
sheafification of a presheaf of modules and the sheafification of its restriction, which does not
exist in this repository; see the `Not done here` section of
`StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Scheme`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open scoped TensorProduct

universe u

namespace SymPow

variable {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (M : Type u) [AddCommGroup M] [Module A M]

/-- The base change homomorphism of symmetric algebras carries `1 ⊗ ι(m)` to `ι(1 ⊗ m)`. -/
theorem symAlgBaseChangeHom_one_tmul_ι (m : M) :
    symAlgBaseChangeHom B M ((1 : B) ⊗ₜ[A] SymmetricAlgebra.ι A M m) =
      SymmetricAlgebra.ι B (B ⊗[A] M) ((1 : B) ⊗ₜ[A] m) := by
  rw [symAlgBaseChangeHom_tmul, map_one, one_mul, SymmetricAlgebra.lift_ι_apply,
    toSymBaseChange_apply]

/-- **The base change homomorphism of symmetric algebras on a product of degree-one
generators.** With `SymmetricAlgebra.symmetricPower_eq_span_prod_ι` this determines
`SymPow.baseChangeEquiv` on the degree-`n` piece. -/
theorem symAlgBaseChangeHom_one_tmul_prod_ι {n : ℕ} (s : Fin n → M) :
    symAlgBaseChangeHom B M
        ((1 : B) ⊗ₜ[A] ∏ i : Fin n, SymmetricAlgebra.ι A M (s i)) =
      ∏ i : Fin n, SymmetricAlgebra.ι B (B ⊗[A] M) ((1 : B) ⊗ₜ[A] s i) := by
  have hprod : (1 : B) ⊗ₜ[A] ∏ i : Fin n, SymmetricAlgebra.ι A M (s i) =
      ∏ i : Fin n, (1 : B) ⊗ₜ[A] SymmetricAlgebra.ι A M (s i) :=
    map_prod (Algebra.TensorProduct.includeRight :
      SymmetricAlgebra A M →ₐ[A] B ⊗[A] SymmetricAlgebra A M)
      (fun i : Fin n => SymmetricAlgebra.ι A M (s i)) Finset.univ
  rw [hprod, map_prod]
  exact Finset.prod_congr rfl fun i _ => symAlgBaseChangeHom_one_tmul_ι B M (s i)

end SymPow

namespace Stacks.SymGraded

variable {X : Scheme.{u}}

/-! ### Restriction of sections as a semilinear map -/

/-- **Restriction of sections of a module on a scheme, as a semilinear map** along the
restriction map of the structure sheaf. This is
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ` with the semilinearity written out
instead of being hidden in a restriction of scalars. -/
def restrictSemilinear (N : X.Modules) {U V : X.Opens} (h : U ≤ V) :
    Γ(N, V) →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] Γ(N, U) where
  toFun := N.presheaf.map (homOfLE h).op
  map_add' := map_add _
  map_smul' r x := N.map_smul (homOfLE h) r x

/-- `restrictSemilinear N h` sends a section to its image under the restriction map of `N`. -/
@[simp]
theorem restrictSemilinear_apply (N : X.Modules) {U V : X.Opens} (h : U ≤ V) (x : Γ(N, V)) :
    restrictSemilinear N h x = N.presheaf.map (homOfLE h).op x := rfl

/-- `restrictSemilinear N h` and `restrictₗ N h` agree on every section. -/
theorem restrictSemilinear_eq_restrictₗ (N : X.Modules) {U V : X.Opens} (h : U ≤ V)
    (x : Γ(N, V)) :
    letI := moduleOfLE N h
    restrictSemilinear N h x = restrictₗ N h x := rfl

/-! ### The graded pieces, with their restricted scalars -/

/-- The `Γ(X, V)`-module structure on the degree-`n` graded piece of the symmetric algebra of
the sections over `U`, for `U ≤ V`, obtained by restricting scalars along the restriction map of
the structure sheaf. -/
@[instance_reducible]
def gradedModuleOfLE (N : X.Modules) {U V : X.Opens} (h : U ≤ V) (n : ℤ) :
    Module Γ(X, V) (gradedPiece (R := Γ(X, U)) Γ(N, U) n) :=
  Module.compHom _ (X.presheaf.map (homOfLE h).op).hom

/-- The scalar tower `Γ(X, V) → Γ(X, U) → Sym^n_{Γ(X, U)}(Γ(N, U))` for `U ≤ V`. -/
theorem gradedIsScalarTowerOfLE (N : X.Modules) {U V : X.Opens} (h : U ≤ V) (n : ℤ) :
    letI := algebraOfLE X h
    letI := gradedModuleOfLE N h n
    IsScalarTower Γ(X, V) Γ(X, U) (gradedPiece (R := Γ(X, U)) Γ(N, U) n) :=
  let := algebraOfLE X h
  let := gradedModuleOfLE N h n
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- **The restriction map of the degree-`n` graded pieces**, as a `Γ(X, V)`-linear map for
`Stacks.SymGraded.gradedModuleOfLE`. Its underlying function is the semilinear
`Stacks.SymGraded.gradedMapₛₗ`. -/
def gradedRestrictₗ (N : X.Modules) {U V : X.Opens} (h : U ≤ V) (n : ℤ) :
    letI := gradedModuleOfLE N h n
    gradedPiece (R := Γ(X, V)) Γ(N, V) n →ₗ[Γ(X, V)]
      gradedPiece (R := Γ(X, U)) Γ(N, U) n :=
  letI := gradedModuleOfLE N h n
  { toFun := gradedMapₛₗ n (X.presheaf.map (homOfLE h).op).hom (restrictSemilinear N h)
    map_add' := map_add
      (gradedMapₛₗ n (X.presheaf.map (homOfLE h).op).hom (restrictSemilinear N h))
    map_smul' r x :=
      (gradedMapₛₗ n (X.presheaf.map (homOfLE h).op).hom
        (restrictSemilinear N h)).map_smul' r x }

/-- In the symmetric algebra, `gradedRestrictₗ N h n x` is the image of `x` under the
semilinear map of symmetric algebras induced by `restrictSemilinear N h`. -/
@[simp]
theorem gradedRestrictₗ_coe (N : X.Modules) {U V : X.Opens} (h : U ≤ V) (n : ℤ)
    (x : gradedPiece (R := Γ(X, V)) Γ(N, V) n) :
    letI := gradedModuleOfLE N h n
    ((gradedRestrictₗ N h n x : gradedPiece (R := Γ(X, U)) Γ(N, U) n) :
        SymmetricAlgebra Γ(X, U) Γ(N, U)) =
      SymmetricAlgebra.mapₛₗ (X.presheaf.map (homOfLE h).op).hom (restrictSemilinear N h)
        (x : SymmetricAlgebra Γ(X, V) Γ(N, V)) := rfl

/-! ### The base change property -/

/-- **The symmetric powers of the sections of a quasi-coherent module are a base change.** For
`U ≤ U'` affine opens of a scheme `X` and `N` a quasi-coherent `𝒪_X`-module, the restriction map
exhibits `Sym^n_{Γ(X, U)}(Γ(N, U))` as the base change of `Sym^n_{Γ(X, U')}(Γ(N, U'))` along
`Γ(X, U') ⟶ Γ(X, U)`. -/
theorem isBaseChange_gradedRestrictₗ (N : X.Modules) [N.IsQuasicoherent] {U U' : X.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U ≤ U') (n : ℕ) :
    letI := algebraOfLE X h
    letI := gradedModuleOfLE N h (n : ℤ)
    letI := gradedIsScalarTowerOfLE N h (n : ℤ)
    IsBaseChange Γ(X, U) (gradedRestrictₗ N h (n : ℤ)) := by
  let := algebraOfLE X h
  let := moduleOfLE N h
  let := isScalarTowerOfLE N h
  let := gradedModuleOfLE N h (n : ℤ)
  let := gradedIsScalarTowerOfLE N h (n : ℤ)
  have hbc := isBaseChange_restrictₗ N hU hU' h
  have he : ∀ m : Γ(N, U'),
      hbc.equiv ((1 : Γ(X, U)) ⊗ₜ[Γ(X, U')] m) = restrictSemilinear N h m := fun m =>
    (hbc.equiv_tmul 1 m).trans (one_smul _ _)
  let E : Γ(X, U) ⊗[Γ(X, U')] SymPow.symmetricPower n Γ(X, U') Γ(N, U') ≃ₗ[Γ(X, U)]
      gradedPiece (R := Γ(X, U)) Γ(N, U) (n : ℤ) :=
    (SymPow.baseChangeEquiv Γ(X, U) Γ(N, U') n).trans (gradedCongr (n : ℤ) hbc.equiv)
  have hE : ∀ y : SymPow.symmetricPower n Γ(X, U') Γ(N, U'),
      (E ((1 : Γ(X, U)) ⊗ₜ[Γ(X, U')] y) : SymmetricAlgebra Γ(X, U) Γ(N, U)) =
        SymmetricAlgebra.mapₛₗ (RingHom.id Γ(X, U)) hbc.equiv.toLinearMap
          (SymPow.symAlgBaseChangeHom Γ(X, U) Γ(N, U')
            ((1 : Γ(X, U)) ⊗ₜ[Γ(X, U')] (y : SymmetricAlgebra Γ(X, U') Γ(N, U')))) :=
    fun _ => rfl
  refine IsBaseChange.of_equiv E ?_
  let g : SymPow.symmetricPower n Γ(X, U') Γ(N, U') →ₛₗ[(X.presheaf.map (homOfLE h).op).hom]
      gradedPiece (R := Γ(X, U)) Γ(N, U) (n : ℤ) := {
    toFun := fun x => E ((1 : Γ(X, U)) ⊗ₜ[Γ(X, U')] x)
    map_add' := fun x y => by rw [TensorProduct.tmul_add, map_add E]
    map_smul' := fun a x => by
      have hB : (1 : Γ(X, U)) ⊗ₜ[Γ(X, U')] (a • x) =
          (X.presheaf.map (homOfLE h).op).hom a • ((1 : Γ(X, U)) ⊗ₜ[Γ(X, U')] x) := by
        rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
          Algebra.smul_def, mul_one]
        rfl
      rw [hB, map_smul E] }
  have key : g = gradedMapₛₗ (n : ℤ) (X.presheaf.map (homOfLE h).op).hom
      (restrictSemilinear N h) := by
    refine SymPow.ext_of_prod_ι fun s => Subtype.ext ?_
    refine Eq.trans (hE ⟨_, SymmetricAlgebra.prod_ι_mem _ s⟩) ?_
    change SymmetricAlgebra.mapₛₗ (RingHom.id Γ(X, U)) hbc.equiv.toLinearMap
        (SymPow.symAlgBaseChangeHom Γ(X, U) Γ(N, U')
          ((1 : Γ(X, U)) ⊗ₜ[Γ(X, U')] ∏ i : Fin n,
            SymmetricAlgebra.ι Γ(X, U') Γ(N, U') (s i))) =
      SymmetricAlgebra.mapₛₗ (X.presheaf.map (homOfLE h).op).hom (restrictSemilinear N h)
        (∏ i : Fin n, SymmetricAlgebra.ι Γ(X, U') Γ(N, U') (s i))
    rw [SymPow.symAlgBaseChangeHom_one_tmul_prod_ι, map_prod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [SymmetricAlgebra.mapₛₗ_ι, SymmetricAlgebra.mapₛₗ_ι]
    exact congrArg (SymmetricAlgebra.ι Γ(X, U) Γ(N, U)) (he (s i))
  intro x
  exact DFunLike.congr_fun key x

/-- In a negative degree both graded pieces are zero, so the restriction map is trivially a base
change. -/
theorem isBaseChange_gradedRestrictₗ_of_neg (N : X.Modules) {U U' : X.Opens} (h : U ≤ U')
    {n : ℤ} (hn : n < 0) :
    letI := algebraOfLE X h
    letI := gradedModuleOfLE N h n
    letI := gradedIsScalarTowerOfLE N h n
    IsBaseChange Γ(X, U) (gradedRestrictₗ N h n) := by
  let := algebraOfLE X h
  let := gradedModuleOfLE N h n
  let := gradedIsScalarTowerOfLE N h n
  have hbot : ∀ {W : X.Opens} (y : gradedPiece (R := Γ(X, W)) Γ(N, W) n), y = 0 := by
    intro W y
    match n, hn with
    | .negSucc _, _ =>
        have hmem : (y : SymmetricAlgebra Γ(X, W) Γ(N, W)) ∈
          (⊥ : Submodule Γ(X, W) (SymmetricAlgebra Γ(X, W) Γ(N, W))) := y.2
        rw [Submodule.mem_bot] at hmem
        exact Subtype.ext hmem
  have hsub : ∀ z : Γ(X, U) ⊗[Γ(X, U')] gradedPiece (R := Γ(X, U')) Γ(N, U') n, z = 0 := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul b y => rw [hbot y, TensorProduct.tmul_zero]
    | add p q hp hq => rw [hp, hq, add_zero]
  exact IsBaseChange.of_equiv
    (LinearEquiv.ofBijective
      (0 : Γ(X, U) ⊗[Γ(X, U')] gradedPiece (R := Γ(X, U')) Γ(N, U') n →ₗ[Γ(X, U)]
        gradedPiece (R := Γ(X, U)) Γ(N, U) n)
      ⟨fun z w _ => (hsub z).trans (hsub w).symm, fun y => ⟨0, (hbot y).symm⟩⟩)
    fun _ => (hbot _).trans (hbot _).symm

/-- **The base change property in every degree**: the nonnegative case is
`Stacks.SymGraded.isBaseChange_gradedRestrictₗ` and the negative one is
`Stacks.SymGraded.isBaseChange_gradedRestrictₗ_of_neg`. -/
theorem isBaseChange_gradedRestrictₗ_int (N : X.Modules) [N.IsQuasicoherent] {U U' : X.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U ≤ U') (n : ℤ) :
    letI := algebraOfLE X h
    letI := gradedModuleOfLE N h n
    letI := gradedIsScalarTowerOfLE N h n
    IsBaseChange Γ(X, U) (gradedRestrictₗ N h n) := by
  match n with
  | .ofNat k => exact isBaseChange_gradedRestrictₗ N hU hU' h k
  | .negSucc k => exact isBaseChange_gradedRestrictₗ_of_neg N h (Int.negSucc_lt_zero k)

end Stacks.SymGraded

end
