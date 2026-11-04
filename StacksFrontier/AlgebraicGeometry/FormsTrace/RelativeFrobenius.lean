module

public import StacksFrontier.AlgebraicGeometry.FormsTrace.FrobeniusLocal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.MeromorphicConstantModule.LocallyBijective
import StacksCore.Tactic.StacksAttribute

/-!
# The trace on forms of the relative Frobenius: Stacks, Lemma 0FW2

Let `p` be a prime number and let `X → S` be a smooth morphism of relative dimension `d` of
schemes in characteristic `p`. The relative Frobenius `F_{X/S} : X → X^{(p)}` (Varieties,
Definition 0CC9) is finite syntomic, and the corresponding map of Proposition 0FLC (3)

`Θ_{X/X^{(p)}} : F_{X/S, *}Ω^•_{X/S} → Ω^•_{X^{(p)}/S}`

is zero in all degrees except in degree `d`, where it is a surjection.

Finiteness is Varieties, Lemma 0CCD. Locally on `X^{(p)}` the relative Frobenius is a base change
of the universal Frobenius `x_i ↦ x_i ^ p` of `Spec ℤ[x_1, …, x_d]` along an étale chart
(`AlgebraicGeometry.exists_isPullback_relativeFrobenius_affineSpace`), which is syntomic; this
gives syntomicity. On the framed charts of
`AlgebraicGeometry.exists_relFramedOpen_relativeFrobenius`, which form a basis of the topology of
`X^{(p)}`, the sections of `Θ` vanish outside degree `d` and are surjective in degree `d`; a map
of sheaves which vanishes on a basis is zero, and one which is surjective on a basis is an
epimorphism.

## Main results

* `AlgebraicGeometry.relativeFrobenius_relativeFormsTrace`: **Stacks, Lemma 0FW2.**

## References

* [Stacks Project, Tag 0FW2](https://stacks.math.columbia.edu/tag/0FW2)
* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
* [Stacks Project, Tag 0CC9](https://stacks.math.columbia.edu/tag/0CC9)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X Y S : Scheme.{u}} (f : Y ⟶ X) (g : X ⟶ S) [IsFinite f] (hf : Syntomic f) (k : ℕ)
  {ι : Type*} (I : ι → f.RelFramedOpen g) (hI : Opens.IsBasis (Set.range fun a => (I a).U))

/-- A section is the trace of `m` if their images under the sections equivalences have the
corresponding local trace relation. -/
private theorem relativeFormsTrace_app_eq_of_relLocalTrace_eq (i : f.RelFramedOpen g)
    (m : Γ(relativeDifferentialForms (f ≫ g) k, f ⁻¹ᵁ i.U))
    (ω : Γ(relativeDifferentialForms g k, i.U))
    (h : relLocalTrace i k (relativeFormsSectionsEquiv (f ≫ g) i.isAffineOpen_preimage
      i.isAffineOpen_W i.le_comp k m) =
        relativeFormsSectionsEquiv g i.isAffineOpen i.isAffineOpen_W i.le k ω) :
    (f.relativeFormsTrace g hf k).app i.U m = ω :=
  (relativeFormsSectionsEquiv g i.isAffineOpen i.isAffineOpen_W i.le k).injective
    ((relativeFormsSectionsEquiv_relativeFormsTrace_app k hf i m).trans h)

include hI in
/-- **The trace on relative forms vanishes as soon as it vanishes on a basis of framed charts.** -/
theorem relativeFormsTrace_eq_zero_of_isBasis (h : ∀ a η, relLocalTrace (I a) k η = 0) :
    f.relativeFormsTrace g hf k = 0 := by
  have := AlgebraicGeometry.flat hf
  have := AlgebraicGeometry.locallyOfFinitePresentation hf
  have hz : (0 : (Scheme.Modules.pushforward f).obj (relativeDifferentialForms (f ≫ g) k) ⟶
      relativeDifferentialForms g k).val = 0 := (SheafOfModules.forget _).map_zero _ _
  refine Stacks.BasisRestriction.moduleSheafHom_ext_onBasis _ _ (fun a => (I a).U) hI _ _
    fun a => ?_
  rw [hz, PresheafOfModules.zero_app]
  refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  exact relativeFormsTrace_app_eq_of_relLocalTrace_eq _ _ hf k (I a) m 0
    ((h a _).trans (map_zero _).symm)

include hI in
/-- **The trace on relative forms is an epimorphism as soon as it is surjective on a basis of
framed charts.** -/
theorem epi_relativeFormsTrace_of_isBasis (h : ∀ a, Function.Surjective (relLocalTrace (I a) k)) :
    Epi (f.relativeFormsTrace g hf k) := by
  have := AlgebraicGeometry.flat hf
  have := AlgebraicGeometry.locallyOfFinitePresentation hf
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
    (Stacks.AlgebraicGeometry.MeromorphicConstantModule.isLocallySurjective_of_surjective_basis
      (B := fun a => (I a).U)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (f.relativeFormsTrace g hf k).val)
      hI fun a ω => ?_)
  obtain ⟨η₀, hη₀⟩ :=
    h a (relativeFormsSectionsEquiv g (I a).isAffineOpen (I a).isAffineOpen_W (I a).le k ω)
  obtain ⟨m, rfl⟩ := (relativeFormsSectionsEquiv (f ≫ g) (I a).isAffineOpen_preimage
    (I a).isAffineOpen_W (I a).le_comp k).surjective η₀
  exact ⟨m, relativeFormsTrace_app_eq_of_relLocalTrace_eq _ _ hf k (I a) m ω hη₀⟩

end Scheme.Hom

variable (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p) (X : Over S)
  (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- The framed charts of the relative Frobenius on which the trace on relative forms vanishes
outside degree `d` and is surjective in degree `d`. -/
abbrev GoodFrobeniusChart :=
  haveI := isFinite_relativeFrobenius S p hS X d
  {i : (relativeFrobenius S p hS X).left.RelFramedOpen ((frobeniusTwist S p hS).obj X).hom //
    (∀ k ≠ d, ∀ η, Scheme.Hom.relLocalTrace i k η = 0) ∧ Function.Surjective
        (Scheme.Hom.relLocalTrace i d)}

/-- **The good framed charts form a basis of the topology of the Frobenius twist.** -/
theorem isBasis_range_goodFrobeniusChart :
    Opens.IsBasis (Set.range fun i : GoodFrobeniusChart S p hS X d => i.1.U) := by
  rw [Opens.isBasis_iff_nbhd]
  intro N x hxN
  have h := exists_relFramedOpen_relativeFrobenius S p hS X d x N hxN
  obtain ⟨i, hxi, hiN, hgood⟩ := h
  exact ⟨i.U, ⟨⟨i, hgood⟩, rfl⟩, hxi, hiN⟩

/-- **Stacks, Lemma 0FW2.** Let `p` be a prime number and let `X → S` be a smooth morphism of
relative dimension `d` of schemes in characteristic `p`. Then:

* the relative Frobenius `F = F_{X/S} : X → X^{(p)}` (Varieties, Definition 0CC9) is finite and
  syntomic; it is a morphism over `S`, `F ≫ (X^{(p)} → S) = (X → S)`, so `F_*Ω^•_{F ≫ g}` is
  `F_{X/S,*}Ω^•_{X/S}`;
* the corresponding map `Θ_{X/X^{(p)}} : F_{X/S,*}Ω^•_{X/S} → Ω^•_{X^{(p)}/S}` of Proposition
  0FLC (3) (`AlgebraicGeometry.Scheme.Hom.relativeFormsTrace`, a map of complexes by
  `AlgebraicGeometry.Scheme.Hom.relativeFormsTrace_deRhamComplex_d`) is zero in every degree
  `k ≠ d`;
* in degree `d` it is a surjection (an epimorphism of sheaves of modules on `X^{(p)}`). -/
@[stacks 0FW2, sga "5 XV 1.Proposition2" "Clause a), special case"]
theorem relativeFrobenius_relativeFormsTrace :
    haveI := isFinite_relativeFrobenius S p hS X d
    IsFinite (relativeFrobenius S p hS X).left ∧ Syntomic (relativeFrobenius S p hS X).left ∧
      (relativeFrobenius S p hS X).left ≫ ((frobeniusTwist S p hS).obj X).hom = X.hom ∧
      (∀ k ≠ d, (relativeFrobenius S p hS X).left.relativeFormsTrace
          ((frobeniusTwist S p hS).obj X).hom (syntomic_relativeFrobenius S p hS X d) k = 0) ∧
      Epi ((relativeFrobenius S p hS X).left.relativeFormsTrace
          ((frobeniusTwist S p hS).obj X).hom (syntomic_relativeFrobenius S p hS X d) d) := by
  have := isFinite_relativeFrobenius S p hS X d
  have hB := isBasis_range_goodFrobeniusChart S p hS X d
  exact ⟨isFinite_relativeFrobenius S p hS X d, syntomic_relativeFrobenius S p hS X d,
      relativeFrobenius_snd S p hS X,
    fun k hk => Scheme.Hom.relativeFormsTrace_eq_zero_of_isBasis _ _ _ k _ hB fun i => i.2.1 k hk,
    Scheme.Hom.epi_relativeFormsTrace_of_isBasis _ _ _ d _ hB fun i => i.2.2⟩

end AlgebraicGeometry
