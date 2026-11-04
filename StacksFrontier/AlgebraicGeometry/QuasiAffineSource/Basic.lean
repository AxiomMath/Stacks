module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineStability
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A quasi-affine morphism into a quasi-affine scheme has quasi-affine source

Mathlib knows that an *affine* morphism into a quasi-affine scheme has quasi-affine source
(`AlgebraicGeometry.Scheme.IsQuasiAffine.of_isAffineHom`). This file proves the same statement for
a *quasi-affine* morphism.

## Main results

* `Stacks.QuasiAffineSource.isQuasiAffine_of_isQuasiAffineHom`: if `f : X ⟶ S` is quasi-affine and
  `S` is quasi-affine, then `X` is quasi-affine.
* `Stacks.QuasiAffineSource.exists_global_basicOpen_eq`: on a qcqs scheme, every basic open of a
  section over `X.basicOpen a` is a basic open of a global section.
* `Stacks.QuasiAffineSource.exists_isAffineOpen_basicOpen_of_isQuasiAffine_basicOpen`: if a basic
  open `X.basicOpen a` of a qcqs scheme is quasi-affine, every point of it lies in an affine basic
  open of a global section.
* `Stacks.QuasiAffineSource.isQuasiAffine_of_forall_exists_isQuasiAffine_basicOpen`: a qcqs scheme
  covered by quasi-affine basic opens of global sections is quasi-affine.

## References

* [Stacks Project, Tag 01SK](https://stacks.math.columbia.edu/tag/01SK)
* [Stacks Project, Tag 01P6](https://stacks.math.columbia.edu/tag/01P6)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.QuasiAffineSource

open AlgebraicGeometry

/-! ### Separatedness and quasi-separatedness of the source -/

/-- The source of a quasi-affine morphism into a quasi-affine scheme is separated. -/
theorem isSeparated_of_isQuasiAffineHom_of_isQuasiAffine {X S : Scheme.{u}} (f : X ⟶ S)
    [IsQuasiAffineHom f] [S.IsQuasiAffine] : X.IsSeparated := by
  constructor
  rw [← terminal.comp_from f]
  have h₂ : IsSeparated (terminal.from S) := Scheme.IsSeparated.isSeparated_terminal_from
  infer_instance

/-- The source of a quasi-affine morphism into a quasi-affine scheme is a quasi-separated space. -/
theorem quasiSeparatedSpace_of_isQuasiAffineHom {X S : Scheme.{u}} (f : X ⟶ S)
    [IsQuasiAffineHom f] [S.IsQuasiAffine] : QuasiSeparatedSpace X :=
  let := isSeparated_of_isQuasiAffineHom_of_isQuasiAffine f
  inferInstance

/-! ### Clearing the denominator -/

/-- Inside the basic open of `a`, multiplying a section by any power of the restriction of `a`
leaves its basic open unchanged. -/
theorem basicOpen_res_pow_mul (X : Scheme.{u}) (a : Γ(X, ⊤)) (n : ℕ)
    (r : Γ(X, X.basicOpen a)) :
    X.basicOpen ((a |_ X.basicOpen a) ^ n * r) = X.basicOpen r := by
  have hres : X.basicOpen (a |_ X.basicOpen a) = X.basicOpen a := by
    simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, Scheme.basicOpen_res]
    exact inf_idem _
  have hpow : X.basicOpen ((a |_ X.basicOpen a) ^ n) = X.basicOpen a := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; rw [pow_zero, Scheme.basicOpen_one]
    · rw [X.basicOpen_pow (a |_ X.basicOpen a) hn, hres]
  rw [Scheme.basicOpen_mul, hpow]
  exact inf_eq_right.mpr (X.basicOpen_le r)

/-- On a quasi-compact quasi-separated scheme the basic open of a section over `X.basicOpen a`
is the basic open of a global section, namely of `a` times a numerator of that section. -/
theorem exists_global_basicOpen_eq (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (a : Γ(X, ⊤)) (r : Γ(X, X.basicOpen a)) :
    ∃ y : Γ(X, ⊤), X.basicOpen (a * y) = X.basicOpen r := by
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X ⊤
    isCompact_univ isQuasiSeparated_univ a r
  refine ⟨y, ?_⟩
  have h1 : X.basicOpen (y |_ X.basicOpen a) = X.basicOpen r := by
    rw [hy, basicOpen_res_pow_mul]
  simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, Scheme.basicOpen_res] at h1
  rw [Scheme.basicOpen_mul, h1]

/-! ### The point-by-point input -/

/-- If one basic open `X.basicOpen a` of a qcqs scheme is a quasi-affine scheme, then every point
of it lies in an affine basic open of a **global** section. -/
theorem exists_isAffineOpen_basicOpen_of_isQuasiAffine_basicOpen (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (a : Γ(X, ⊤))
    (ha : (X.basicOpen a).toScheme.IsQuasiAffine) {x : X} (hx : x ∈ X.basicOpen a) :
    ∃ b : Γ(X, ⊤), IsAffineOpen (X.basicOpen b) ∧ x ∈ X.basicOpen b := by
  have := ha
  obtain ⟨-, ⟨-, ⟨t, ht, rfl⟩, rfl⟩, hxt, -⟩ :=
    (Scheme.IsQuasiAffine.isBasis_basicOpen (X.basicOpen a).toScheme).exists_subset_of_mem_open
      (Set.mem_univ (⟨x, hx⟩ : (X.basicOpen a).toScheme)) isOpen_univ
  have himg := Scheme.Opens.ι_image_basicOpen' (U := X.basicOpen a) t
  generalize X.presheaf.map (eqToHom (X.basicOpen a).ι_image_top.symm).op t = s at himg
  obtain ⟨y, hy⟩ := exists_global_basicOpen_eq X a s
  refine ⟨a * y, ?_⟩
  rw [hy, ← himg]
  exact ⟨(Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (X.basicOpen a).ι).2 ht,
    ⟨x, hx⟩, hxt, rfl⟩

/-- **Quasi-affineness is detected on a cover by basic opens of global sections.** A qcqs scheme
each of whose points lies in a basic open of a global section that is a quasi-affine scheme is
itself quasi-affine. -/
@[ega "II 5.1.2" "d') ⇒ a)"]
theorem isQuasiAffine_of_forall_exists_isQuasiAffine_basicOpen (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (H : ∀ x : X, ∃ a : Γ(X, ⊤), (X.basicOpen a).toScheme.IsQuasiAffine ∧ x ∈ X.basicOpen a) :
    X.IsQuasiAffine := by
  refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen X fun x ↦ ?_
  obtain ⟨a, ha, hx⟩ := H x
  exact exists_isAffineOpen_basicOpen_of_isQuasiAffine_basicOpen X a ha hx

/-! ### Affine morphisms are quasi-affine -/

/-- An affine morphism is quasi-affine. -/
instance isQuasiAffineHom_of_isAffineHom {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] :
    IsQuasiAffineHom f := by
  constructor
  intro U hU
  have : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
  infer_instance

/-! ### The main result -/

/-- **A quasi-affine morphism into a quasi-affine scheme has quasi-affine source.** This is an
alias of `AlgebraicGeometry.Scheme.IsQuasiAffine.of_isQuasiAffineHom`. -/
alias isQuasiAffine_of_isQuasiAffineHom :=
  AlgebraicGeometry.Scheme.IsQuasiAffine.of_isQuasiAffineHom

end Stacks.QuasiAffineSource

end
