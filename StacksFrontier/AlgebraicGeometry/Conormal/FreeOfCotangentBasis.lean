module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Immersion
public import StacksFrontier.AlgebraicGeometry.Blowup.AffineModelTwistBridge
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeInNormalBundle
public import StacksFrontier.AlgebraicGeometry.Modules.FreeMapIsoLocus
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineIsoCriterion
public import StacksFrontier.AlgebraicGeometry.AffineQcohEquivalence.Basic

/-!
# A conormal sheaf with a basis of global sections is free

Let `i : Z ⟶ X` be a closed immersion into an affine scheme, with kernel ideal
`I = ker(Γ(X, 𝒪_X) ⟶ Γ(Z, 𝒪_Z))`, and let `y₁, …, y_r ∈ I` generate `I`.  Suppose they are
linearly independent modulo `I²` over `Γ(X, 𝒪_X)/I`: from `Σ cⱼ yⱼ ∈ I²` it follows that every
`cⱼ ∈ I`.  Then the conormal sheaf `𝒞_{Z/X}` is free of rank `r`, with basis the classes of the
`yⱼ`.  The degree-one sections of the conormal algebra over an affine chart are `I/I²`
([Stacks, Tag 0631]), and a morphism of quasi-coherent modules on an affine scheme is invertible
once it is invertible on global sections.

## Main definitions

* `Stacks.Conormal.conormalSectionOfTop`: the global section of `𝒞_{Z/X}` attached to an element
  of `I`.
* `Stacks.Conormal.conormalFreeHom`: the morphism `𝒪_Z^r ⟶ 𝒞_{Z/X}` given by the classes of the
  `yⱼ`.

## Main results

* `Stacks.Conormal.isIso_conormalFreeHom`: that morphism is an isomorphism under the two
  hypotheses above.

## References

* [Stacks Project, Tag 0631](https://stacks.math.columbia.edu/tag/0631)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Conormal

variable {Z X : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i] {r : ℕ}

/-- A closed immersion into an affine scheme restricts to a closed immersion over `⊤`. -/
theorem isClosedImmersion_resLE_top :
    IsClosedImmersion (i.resLE (Stacks.Blowup.AffineModel.wholeSpace X).1
      (i ⁻¹ᵁ (Stacks.Blowup.AffineModel.wholeSpace X).1) le_rfl) := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

/-- The conormal sheaf `𝒞_{Z/X}` of the closed immersion, as an object of `Z.Modules`. -/
abbrev conormalModule : Z.Modules := conormalSheafDegreeOne i

/-- The degree-one section of the conormal sheaf attached to a global section of the kernel
ideal. -/
def conormalSectionOfTop (a : chartIdeal i (Stacks.Blowup.AffineModel.wholeSpace X)) :
    Γ(conormalModule i, ⊤) :=
  (conormalAlgebra i).localMap (Stacks.Blowup.AffineModel.wholeSpace X)
      (isClosedImmersion_resLE_top i) 1 ⟨a, by simp⟩

/-- The section attached to `c · a` is `c` times the section attached to `a`. -/
theorem conormalSectionOfTop_smul (c : Γ(X, ⊤))
    (a : chartIdeal i (Stacks.Blowup.AffineModel.wholeSpace X)) :
    conormalSectionOfTop i ⟨c * a, Ideal.mul_mem_left _ c a.2⟩ =
      (show Γ(Z, ⊤) from (i.app ⊤).hom c) • conormalSectionOfTop i a :=
  (conormalAlgebra i).localMap_smul (Stacks.Blowup.AffineModel.wholeSpace X)
    (isClosedImmersion_resLE_top i) 1 c
    ⟨a, by simp⟩ ⟨c * a, by simpa using Ideal.mul_mem_left _ c a.2⟩ rfl

/-- `conormalSectionOfTop` is additive. -/
theorem conormalSectionOfTop_add (a b : chartIdeal i (Stacks.Blowup.AffineModel.wholeSpace X)) :
    conormalSectionOfTop i (a + b) = conormalSectionOfTop i a + conormalSectionOfTop i b := by
  have h := map_add ((conormalAlgebra i).localMap (Stacks.Blowup.AffineModel.wholeSpace X)
    (isClosedImmersion_resLE_top i) 1) ⟨a, by simp⟩ ⟨b, by simp⟩
  exact h

/-- The section attached to `a` vanishes exactly when `a ∈ I²`. -/
theorem conormalSectionOfTop_eq_zero_iff
    (a : chartIdeal i (Stacks.Blowup.AffineModel.wholeSpace X)) :
    conormalSectionOfTop i a = 0 ↔
      (a : Γ(X, ⊤)) ∈ chartIdeal i (Stacks.Blowup.AffineModel.wholeSpace X) ^ 2 :=
  (conormalAlgebra i).localMap_eq_zero_iff (Stacks.Blowup.AffineModel.wholeSpace X)
    (isClosedImmersion_resLE_top i) 1 _

/-- Every global section of the conormal sheaf comes from an element of `I`. -/
theorem conormalSectionOfTop_surjective : Function.Surjective (conormalSectionOfTop i) := by
  intro t
  obtain ⟨a, ha⟩ :=
    (conormalAlgebra i).localMap_surjective (Stacks.Blowup.AffineModel.wholeSpace X)
      (isClosedImmersion_resLE_top i) 1 t
  exact ⟨⟨a, by simpa using a.2⟩, ha⟩

/-- The section attached to `0` is `0`. -/
theorem conormalSectionOfTop_zero :
    conormalSectionOfTop i (0 : chartIdeal i (Stacks.Blowup.AffineModel.wholeSpace X)) = 0 :=
  map_zero ((conormalAlgebra i).localMap (Stacks.Blowup.AffineModel.wholeSpace X)
    (isClosedImmersion_resLE_top i) 1)

/-- `conormalSectionOfTop_smul` with the scalar action of `Γ(X, 𝒪_X)` on `I`. -/
theorem conormalSectionOfTop_smul' (c : Γ(X, ⊤))
    (a : chartIdeal i (Stacks.Blowup.AffineModel.wholeSpace X)) :
    conormalSectionOfTop i (c • a) =
      (show Γ(Z, ⊤) from (i.app ⊤).hom c) • conormalSectionOfTop i a :=
  conormalSectionOfTop_smul i c a

/-- `conormalSectionOfTop` of a linear combination. -/
theorem conormalSectionOfTop_finsetSum_smul {ι : Type*} (s : Finset ι)
    (y : ι → chartIdeal i (Stacks.Blowup.AffineModel.wholeSpace X)) (c : ι → Γ(X, ⊤)) :
    conormalSectionOfTop i (∑ j ∈ s, c j • y j) =
      ∑ j ∈ s, (show Γ(Z, ⊤) from (i.app ⊤).hom (c j)) • conormalSectionOfTop i (y j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using conormalSectionOfTop_zero i
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, conormalSectionOfTop_add,
      conormalSectionOfTop_smul', ih]

variable (y : Fin r → chartIdeal i (Stacks.Blowup.AffineModel.wholeSpace X))

/-- The underlying element of a linear combination of the `y j` is the ring-element combination. -/
private theorem coe_sum_smul_ideal {R : Type*} [CommRing R] {I : Ideal R} (y : Fin r → I)
    (c : Fin r → R) : ((∑ j, c j • y j : I) : R) = ∑ j, c j * (y j : R) := by
  simp [smul_eq_mul]

/-- Linear independence modulo `I²` gives linear independence of the conormal classes over
`Γ(Z, 𝒪_Z)`. -/
theorem linearIndependent_conormalSectionOfTop
    (hreg : ∀ c : Fin r → Γ(X, ⊤),
      (∑ j, c j * (y j : Γ(X, ⊤))) ∈ chartIdeal i (Stacks.Blowup.AffineModel.wholeSpace X) ^ 2 →
        ∀ j, c j ∈ chartIdeal i (Stacks.Blowup.AffineModel.wholeSpace X)) :
    LinearIndependent Γ(Z, ⊤) (fun j => conormalSectionOfTop i (y j)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hsurj := i.app_surjective ⊤ (isAffineOpen_top X)
  choose c hc using fun j => hsurj (g j)
  have hsum : conormalSectionOfTop i (∑ j, c j • y j) = 0 := by
    rw [conormalSectionOfTop_finsetSum_smul]
    simpa only [hc] using hg
  rw [conormalSectionOfTop_eq_zero_iff] at hsum
  rw [← hc j]
  exact hreg c (by rwa [coe_sum_smul_ideal] at hsum) j

/-- Generators of `I` give generators of the global sections of the conormal sheaf. -/
theorem span_conormalSectionOfTop
    (hspan : chartIdeal i (Stacks.Blowup.AffineModel.wholeSpace X) ≤
      Ideal.span (Set.range fun j => (y j : Γ(X, ⊤)))) :
    Submodule.span Γ(Z, ⊤) (Set.range fun j => conormalSectionOfTop i (y j)) = ⊤ := by
  refine eq_top_iff.2 fun t _ => ?_
  obtain ⟨a, rfl⟩ := conormalSectionOfTop_surjective i t
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hspan a.2)
  have ha : a = ∑ j, c j • y j :=
    Subtype.ext (by rw [coe_sum_smul_ideal]; exact hc.symm)
  rw [ha, conormalSectionOfTop_finsetSum_smul]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- The morphism `𝒪_Z^r ⟶ 𝒞_{Z/X}` sending the `j`-th basis section to the class of `y j`. -/
def conormalFreeHom : Scheme.Modules.free Z (ULift.{u} (Fin r)) ⟶ conormalModule i :=
  Scheme.Modules.freeHomOfSections (conormalModule i) fun j => conormalSectionOfTop i (y j)

/-- **The conormal sheaf is free on the classes of the `yⱼ`.** -/
theorem isIso_conormalFreeHom
    (hspan : chartIdeal i (Stacks.Blowup.AffineModel.wholeSpace X) ≤
      Ideal.span (Set.range fun j => (y j : Γ(X, ⊤))))
    (hreg : ∀ c : Fin r → Γ(X, ⊤),
      (∑ j, c j * (y j : Γ(X, ⊤))) ∈ chartIdeal i (Stacks.Blowup.AffineModel.wholeSpace X) ^ 2 →
        ∀ j, c j ∈ chartIdeal i (Stacks.Blowup.AffineModel.wholeSpace X)) :
    IsIso (conormalFreeHom i y) := by
  have : IsAffine Z := isAffine_of_isAffineHom i
  have : (Scheme.Modules.free Z (ULift.{u} (Fin r))).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free _
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top _ ?_
  exact (ConcreteCategory.isIso_iff_bijective _).2
    (Scheme.Modules.bijective_app_top_freeHomOfSections _ _
      (linearIndependent_conormalSectionOfTop i y hreg) (span_conormalSectionOfTop i y hspan))

end Stacks.Conormal
