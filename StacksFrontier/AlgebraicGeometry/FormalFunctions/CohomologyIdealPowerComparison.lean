module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyIdealPowerSystemCompatible
public import StacksFrontier.RingTheory.Filtration.IdealPowerSystemComparison

/-!
# The comparison maps of [Stacks, Tag 02OA] part (4) for the cohomology of a filtration

Let `A` be a ring, `I ⊆ A` an ideal, `X` a scheme over `Spec A` and `ℱ` a sheaf of
`𝒪_X`-modules. `StacksFrontier/AlgebraicGeometry/FormalFunctions/CohomologyIdealPowerSystem.lean`
makes the cohomology modules `Hᵖ(X, Iⁿℱ)` over `Hᵖ(X, ℱ)` a
`Stacks.RingTheory.ReesSystem`, which is what parts (1), (2) and (3) of [Stacks, Tag 02OA] run
on. This file adds the one operation parts (4) and (5) need beyond them — multiplication by
`a ∈ Iᵏ` as a map `Hᵖ(X, ℱ) → Hᵖ(X, Iᵏℱ)`, out of the module at the bottom of the system — and
so makes the same modules a `Stacks.RingTheory.TopMulSystem`. The algebraic content of parts (4)
and (5) is carried out for such a system in
`StacksFrontier/RingTheory/Filtration/IdealPowerSystemComparison.lean`; here it is transported to
cohomology, with the conclusions of parts (1), (2) and (3) carried as hypotheses.

The new operation is induced by `Stacks.Cohomology.FormalFunctions.idealPowerSmulTop`,
multiplication by a function on the base read as a morphism `ℱ ⟶ Iᵏℱ` of sheaves of modules.
Every identity it has to satisfy is, as in the file for parts (1)-(3), proved by
`AlgebraicGeometry.cancel_sheafSubmodule_ι`: a morphism into a subsheaf is determined by its
composite with the inclusion into `ℱ`, and after that composite every identity is a module law
for `a • 𝟙 ℱ`.

## Main definitions

* `Stacks.Cohomology.FormalFunctions.cohomologyMulTop` — multiplication
  `Iᵏ ⊗ Hᵖ(X, ℱ) → Hᵖ(X, Iᵐℱ)` for `m ≤ k`.
* `Stacks.Cohomology.FormalFunctions.cohomologyTopMulSystem` — the system `n ↦ Hᵖ(X, Iⁿℱ)` over
  `Hᵖ(X, ℱ)` with that multiplication.
* `Stacks.Cohomology.FormalFunctions.cohomologyIdealPowerFunctor` — the inverse system
  `n ↦ Hᵖ(X, Iⁿℱ)` as a functor `ℕᵒᵖ ⥤ ModuleCat A`.

## Main results

* `Stacks.Cohomology.FormalFunctions.exists_comparison_cohomology` — **parts (4) and (5) of
  [Stacks, Tag 02OA]**, granted the conclusions of parts (1), (2) and (3): the comparison maps
  `IⁿHᵖ(X, ℱ) → Hᵖ(X, Iⁿ⁻ᶜℱ)`, the two composites, and the pro-isomorphism of the two inverse
  systems.

It is not registered as the tag: parts (1), (2) and (3) are hypotheses here, and they are
discharged only for a proper morphism and a coherent sheaf, in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/ArtinReesChain.lean`.

## References

* [Stacks Project, Tag 02OA](https://stacks.math.columbia.edu/tag/02OA)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower Stacks.Cohomology.AffineBase
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace Stacks.Cohomology.FormalFunctions

attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Over (Spec (.of A)))
  (F : X.left.Modules)

/-! ### Multiplication out of `ℱ` into the filtration -/

/-- Multiplying `ℱ` into `Iᵐℱ` and then dropping to `Iʲℱ` is multiplying `ℱ` into `Iʲℱ`. -/
theorem idealPowerSmulTop_comp_idealPowerMultipleMap {k m j : ℕ} (hm : m ≤ k) (hj : j ≤ m)
    (hj' : j ≤ k) (a : A) (ha : a ∈ I ^ k) :
    idealPowerSmulTop I X F hm a ha ≫ idealPowerMultipleMap (baseIdealSheaf A I X.hom) F hj =
      idealPowerSmulTop I X F hj' a ha :=
  cancel_sheafSubmodule_ι _ _ _
    (((Category.assoc _ _ _).trans
        ((congrArg (fun ψ ↦ idealPowerSmulTop I X F hm a ha ≫ ψ)
            (idealPowerMultipleMap_comp_ι (baseIdealSheaf A I X.hom) F hj)).trans
          (idealPowerSmulTop_comp_ι I X F hm a ha))).trans
      (idealPowerSmulTop_comp_ι I X F hj' a ha).symm)

/-- Multiplication out of `ℱ` depends on the function alone, not on the power of `I` it is
taken in. -/
theorem idealPowerSmulTop_congr {k k' m : ℕ} (hm : m ≤ k) (hm' : m ≤ k') {a a' : A}
    (ha : a ∈ I ^ k) (ha' : a' ∈ I ^ k') (e : a = a') :
    idealPowerSmulTop I X F hm a ha = idealPowerSmulTop I X F hm' a' ha' :=
  cancel_sheafSubmodule_ι _ _ _
    (((idealPowerSmulTop_comp_ι I X F hm a ha).trans
        (congrArg (fun c : A ↦ c • 𝟙 F) e)).trans
      (idealPowerSmulTop_comp_ι I X F hm' a' ha').symm)

/-- Multiplication out of `ℱ` is additive in the function. -/
theorem idealPowerSmulTop_add {k m : ℕ} (hm : m ≤ k) (a a' : A) (ha : a ∈ I ^ k)
    (ha' : a' ∈ I ^ k) :
    idealPowerSmulTop I X F hm (a + a') (Ideal.add_mem _ ha ha') =
      idealPowerSmulTop I X F hm a ha + idealPowerSmulTop I X F hm a' ha' :=
  cancel_sheafSubmodule_ι _ _ _ (hom_ext_of_sections X fun U x ↦
    apply_congr X (add_smul a a' (𝟙 F)) U x)

/-- Multiplication out of `ℱ` is `A`-linear in the function. -/
theorem idealPowerSmulTop_smul {k m : ℕ} (hm : m ≤ k) (r a : A) (ha : a ∈ I ^ k) :
    idealPowerSmulTop I X F hm (r * a) (Ideal.mul_mem_left _ r ha) =
      r • idealPowerSmulTop I X F hm a ha :=
  cancel_sheafSubmodule_ι _ _ _ (hom_ext_of_sections X fun U x ↦
    apply_congr X
      (((smul_id_comp_smul_id X F a r).trans
        (congrArg (fun c : A ↦ c • 𝟙 F) (mul_comm a r))).symm) U x)

variable (p : ℕ)

/-- **Multiplication `Iᵏ ⊗_A Hᵖ(X, ℱ) → Hᵖ(X, Iᵐℱ)`** for `m ≤ k`: the operation of
[Stacks, Tag 02OA] part (4) out of the module at the bottom of the system, `A`-linear in the
function by `A`-linearity of cohomology. -/
def cohomologyMulTop {k m : ℕ} (h : m ≤ k) :
    ↥(I ^ k) →ₗ[A] cohomology X F p →ₗ[A] cohomologyIdealPower I X F p m where
  toFun a := (((cohomologyFunctor X p).map
    (idealPowerSmulTop I X F h (a : A) a.2)).hom).restrictScalars A
  map_add' a a' := by
    refine LinearMap.ext fun x ↦ ?_
    change ((cohomologyFunctor X p).map
      (idealPowerSmulTop I X F h ((a : A) + (a' : A)) _)).hom x = _
    rw [idealPowerSmulTop_add I X F h (a : A) (a' : A) a.2 a'.2, Functor.map_add]
    rfl
  map_smul' r a := by
    refine LinearMap.ext fun x ↦ ?_
    change ((cohomologyFunctor X p).map
      (idealPowerSmulTop I X F h (r * (a : A)) _)).hom x = _
    rw [idealPowerSmulTop_smul I X F h r (a : A) a.2, Functor.map_smul]
    rfl

/-- A power of `I` is contained in the same power of the extension of `I` along the identity.
This is `Ideal.map_id`, in the form in which the multiplication maps of
`Stacks.Cohomology.FormalFunctions.cohomologyIdealPowerSystem` consume it. -/
theorem pow_le_map_id_pow (k : ℕ) : I ^ k ≤ (I.map (RingHom.id A)) ^ k :=
  le_of_eq (by rw [Ideal.map_id])

/-- **The system `n ↦ Hᵖ(X, Iⁿℱ)` over `Hᵖ(X, ℱ)` with the multiplication out of `Hᵖ(X, ℱ)`.**
This is `Stacks.Cohomology.FormalFunctions.cohomologyIdealPowerSystem`, its multiplication maps
read on `Iᵏ` itself rather than on the extension of `I` along the identity, together with the
four laws of `Stacks.RingTheory.TopMulSystem` for `cohomologyMulTop`. -/
def cohomologyTopMulSystem :
    Stacks.RingTheory.TopMulSystem I (cohomologyIdealPower I X F p) (cohomology X F p) where
  tr := fun {_ _} h ↦ cohomologyTr I X F p h
  tr_tr h₁ h₂ x := (cohomologyIdealPowerSystem I X F p).tr_tr h₁ h₂ x
  proj n := cohomologyProj I X F p n
  proj_tr h x := (cohomologyIdealPowerSystem I X F p).proj_tr h x
  mul k n := (cohomologyMul I X F p k n).comp (Submodule.inclusion (pow_le_map_id_pow I k))
  proj_mul k n a x :=
    (cohomologyIdealPowerSystem I X F p).proj_mul k n
      (Submodule.inclusion (pow_le_map_id_pow I k) a) x
  tr_mul_of_proj_eq_zero k n a x hx :=
    (cohomologyIdealPowerSystem I X F p).tr_mul_of_proj_eq_zero k n
      (Submodule.inclusion (pow_le_map_id_pow I k) a) x hx
  tr_self _ x :=
    (congrArg (fun φ : _ ⟶ _ ↦ ((cohomologyFunctor X p).map φ).hom x)
      (idealPowerMultipleMap_refl I X F _)).trans (cohomologyFunctor_map_id_apply X p x)
  mulTop := fun {_ _} h ↦ cohomologyMulTop I X F p h
  proj_mulTop := fun {_ _} h a x ↦
    (cohomologyFunctor_map_comp_apply X p _ _ x).trans
      ((congrArg (fun φ : _ ⟶ _ ↦ ((cohomologyFunctor X p).map φ).hom x)
        (idealPowerSmulTop_comp_ι I X F h (a : A) a.2)).trans
        (cohomologyFunctor_map_smul_id_apply X p (a : A) x))
  tr_mulTop := fun {_ _ _} h h' hj a x ↦
    (cohomologyFunctor_map_comp_apply X p _ _ x).trans
      (congrArg (fun φ : _ ⟶ _ ↦ ((cohomologyFunctor X p).map φ).hom x)
        (idealPowerSmulTop_comp_idealPowerMultipleMap I X F h hj h' (a : A) a.2))
  mulTop_congr := fun {_ _ _} h h' a a' x e ↦
    congrArg (fun φ : _ ⟶ _ ↦ ((cohomologyFunctor X p).map φ).hom x)
      (idealPowerSmulTop_congr I X F h h' a.2 a'.2 e)
  tr_mul_eq_mulTop_proj k _ a x :=
    (cohomologyFunctor_map_comp_apply X p _ _ x).trans
      ((congrArg (fun φ : _ ⟶ _ ↦ ((cohomologyFunctor X p).map φ).hom x)
        (idealPowerSmul_comp_idealPowerMultipleMap_eq I X F (a : A)
          (mem_pow_of_mem_map_id I (Submodule.inclusion (pow_le_map_id_pow I k) a).2))).trans
        (cohomologyFunctor_map_comp_apply X p _ _ x).symm)

/-- **The inverse system `n ↦ Hᵖ(X, Iⁿℱ)`** as a functor `ℕᵒᵖ ⥤ ModuleCat A`: the first of the
two systems of [Stacks, Tag 02OA] part (5). -/
abbrev cohomologyIdealPowerFunctor : ℕᵒᵖ ⥤ ModuleCat.{u} A :=
  (cohomologyTopMulSystem I X F p).system

/-- The value of `cohomologyIdealPowerFunctor` at `n` is `Hᵖ(X, Iⁿℱ)`. -/
@[simp]
theorem cohomologyIdealPowerFunctor_obj (n : ℕ) :
    (cohomologyIdealPowerFunctor I X F p).obj (op n) =
      ModuleCat.of A (cohomologyIdealPower I X F p n) := rfl

/-- For `m ≤ n`, the transition map of `cohomologyIdealPowerFunctor` is the map
`Hᵖ(X, Iⁿℱ) → Hᵖ(X, Iᵐℱ)` induced by the inclusion `Iⁿℱ ⊆ Iᵐℱ`. -/
@[simp]
theorem cohomologyIdealPowerFunctor_map {m n : ℕ} (h : m ≤ n) :
    (cohomologyIdealPowerFunctor I X F p).map (homOfLE h).op =
      ModuleCat.ofHom (cohomologyTr I X F p h) := rfl

/-- The multiplication map of `cohomologyTopMulSystem` out of the tensor product is the one
parts (1) and (2) of [Stacks, Tag 02OA] are stated with. -/
theorem cohomologyTopMulSystem_mulTensor (k n : ℕ) :
    (cohomologyTopMulSystem I X F p).mulTensor k n = cohomologyMulTensor I X F p k n := rfl

/-- **[Stacks, Tag 02OA], parts (4) and (5), granted parts (1), (2) and (3).** Let `A` be a
ring, `I ⊆ A` an ideal, `X` a scheme over `Spec A` and `ℱ` a sheaf of `𝒪_X`-modules, and let
`c` be an integer for which

1. `Iʳ⁻ᶜ ⊗ Hᵖ(X, Iᶜℱ) → Hᵖ(X, Iʳℱ)` is surjective for `r ≥ c`;
2. the image of `Hᵖ(X, Iʳℱ) → Hᵖ(X, ℱ)` lies in `Iʳ⁻ᶜHᵖ(X, ℱ)` for `r ≥ c`;
3. `Ker(Hᵖ(X, Iᵏℱ) → Hᵖ(X, ℱ)) = Ker(Hᵖ(X, Iᵏℱ) → Hᵖ(X, Iᵐℱ))` for `m + c ≤ k`.

Then there are maps `IⁿHᵖ(X, ℱ) → Hᵖ(X, Iⁿ⁻ᶜℱ)` for `n ≥ c` such that

* the composite `IⁿHᵖ(X, ℱ) → Hᵖ(X, Iⁿ⁻ᶜℱ) → Hᵖ(X, ℱ)` is the inclusion of `IⁿHᵖ(X, ℱ)`, which
  read inside `Iⁿ⁻²ᶜHᵖ(X, ℱ)` — where the image of `Hᵖ(X, Iⁿ⁻ᶜℱ) → Hᵖ(X, ℱ)` lies by (2) — is
  the source's statement that `IⁿHᵖ(X, ℱ) → Hᵖ(X, Iⁿ⁻ᶜℱ) → Iⁿ⁻²ᶜHᵖ(X, ℱ)` is canonical;
* the composite `Hᵖ(X, Iⁿℱ) → Iⁿ⁻ᶜHᵖ(X, ℱ) → Hᵖ(X, Iⁿ⁻²ᶜℱ)`, whose first map is the projection
  to `Hᵖ(X, ℱ)` read in `Iⁿ⁻ᶜHᵖ(X, ℱ)` by (2), is the canonical map, for `n ≥ 2c`;

and the two inverse systems `(Hᵖ(X, Iⁿℱ))` and `(IⁿHᵖ(X, ℱ))` are pro-isomorphic.

The content is `Stacks.RingTheory.TopMulSystem.comparison`, `.proj_comparison`,
`.comparison_proj` and `.nonempty_proIso`, at `cohomologyTopMulSystem`. -/
theorem exists_comparison_cohomology (c : ℕ)
    (h1 : ∀ (r : ℕ) (hr : c ≤ r), Function.Surjective
      ((cohomologyTr I X F p (Nat.sub_add_cancel hr).ge).comp
        (cohomologyMulTensor I X F p (r - c) c)))
    (h2 : ∀ r : ℕ, c ≤ r → LinearMap.range (cohomologyProj I X F p r) ≤
      I ^ (r - c) • (⊤ : Submodule A (cohomology X F p)))
    (h3 : ∀ (m k : ℕ) (hmk : m + c ≤ k),
      LinearMap.ker (cohomologyProj I X F p k) =
        LinearMap.ker (cohomologyTr I X F p
          (show m ≤ k from le_trans (Nat.le_add_right m c) hmk))) :
    ∃ cmp : ∀ n : ℕ, c ≤ n →
        ↥(I ^ n • (⊤ : Submodule A (cohomology X F p))) →ₗ[A]
          cohomologyIdealPower I X F p (n - c),
      (∀ (n : ℕ) (hn : c ≤ n) (y : ↥(I ^ n • (⊤ : Submodule A (cohomology X F p)))),
          cohomologyProj I X F p (n - c) (cmp n hn y) = (y : cohomology X F p)) ∧
        (∀ (n : ℕ) (hn : c + c ≤ n) (x : cohomologyIdealPower I X F p n)
            (y : ↥(I ^ (n - c) • (⊤ : Submodule A (cohomology X F p)))),
            (y : cohomology X F p) = cohomologyProj I X F p n x →
            cmp (n - c) (Nat.le_sub_of_add_le hn) y =
              cohomologyTr I X F p ((Nat.sub_le (n - c) c).trans (Nat.sub_le n c)) x) ∧
        Nonempty (InverseSequence.ProIso (cohomologyIdealPowerFunctor I X F p)
          (Stacks.RingTheory.idealPowerSmulSystem I (cohomology X F p))) := by
  have hker : ∀ (m k : ℕ) (h : m ≤ k), m + c ≤ k →
      LinearMap.ker ((cohomologyTopMulSystem I X F p).proj k) ≤
        LinearMap.ker ((cohomologyTopMulSystem I X F p).tr h) :=
    fun m k _ hmk ↦ (h3 m k hmk).le
  have hsurj : ∀ (r : ℕ) (hr : c ≤ r), Function.Surjective
      (((cohomologyTopMulSystem I X F p).tr (Nat.sub_add_cancel hr).ge).comp
        ((cohomologyTopMulSystem I X F p).mulTensor (r - c) c)) := h1
  refine ⟨fun n hn ↦ (cohomologyTopMulSystem I X F p).comparison c hker n (n - c) (by omega),
    fun n hn y ↦ (cohomologyTopMulSystem I X F p).proj_comparison c hker (by omega) y,
    fun n hn x y hy ↦ (cohomologyTopMulSystem I X F p).comparison_proj c hker hsurj
      (by omega) (by omega) (by omega) x y hy,
    (cohomologyTopMulSystem I X F p).nonempty_proIso c hker hsurj h2⟩

end Stacks.Cohomology.FormalFunctions

end
