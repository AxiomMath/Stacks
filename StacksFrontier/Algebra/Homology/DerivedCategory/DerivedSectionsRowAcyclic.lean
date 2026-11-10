module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSectionsDegeneration
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.PointwiseAcyclicComparison

/-!
# The row hypotheses from right acyclicity of the degreewise functors

`StacksDraft.DerivedSectionsComparison.isIso_alpha_app_of_hypotheses` makes the comparison
`α : Q(T(-)) ⟶ R⁺Γ((-)[0])` of [Stacks, Tag 09VX] an isomorphism at an object `M` as soon as the
*rows* of the double complex `A^{p,q} = T(I^q)^p` of the construction are resolutions of the
terms `T(M)^p`, in the form of
`StacksDraft.TotalComplexQuasiIso.Hypotheses` for the flipped double complex.

This file derives those hypotheses from a statement with no complexes in it:  that each
**degreewise functor** `M ↦ T(M)^p` is right acyclic at `M`.  That is the whole content of the
row condition — right acyclicity says exactly that `I^•` computes the right derived functors of
`T(-)^p` at `M` and that they vanish above degree zero, which read along the row is exactness
away from degree zero together with the kernel property in degree zero.

## Main results

* `StacksDraft.TotalComplexQuasiIso.diagonalFinite_flip`:  diagonal finiteness is preserved by
  flipping a double complex.
* `rowFunctor`:  the degreewise functor `M ↦ T(M)^p`.
* `quasiIso_gammaNu_rowFunctor`:  at an object right acyclic for `T(-)^p`, the row of the double
  complex is a resolution of `T(M)^p`.
* `hypotheses_flip_of_rightAcyclic`:  **the bridge** — the four row hypotheses, from right
  acyclicity of every `T(-)^p` at `M`.
* `hypotheses_flip_of_rightAcyclic_nonneg`:  the same, needing right acyclicity only in
  nonnegative degrees, the negative ones being zero functors.

## Implementation notes

The row `p` of the flipped double complex is *definitionally* `T(-)^p` applied to the resolution:
`(((bicx T I).obj M).flip.X p)` and `((gammaI (T ⋙ eval p) I).obj M)` have the same terms
`T(I^q)^p` and the same differentials `T(I^q ⟶ I^{q+1})^p`.  So no transport is needed and the
augmentation of the row is the existing `gammaNu` of the degreewise functor, whose `augZero` is
`T(-)^p` applied to the augmentation `M ⟶ I^0` — which is `rowAugFlip` read in degree `p`.

With that identification the two substantive fields are the two generic lemmas of
`StacksDraft.DerivedSectionsComparison` that the *column* hypotheses already use,
`exactAt_of_quasiIso_single` and `isIso_kernelLift_augZero`, applied to a quasi-isomorphism out of
a single complex; the quasi-isomorphism is
`CategoryTheory.Functor.quasiIso_mapHomologicalComplex_of_rightAcyclic_resolution`.

`isIso_kernelLift_augZero` takes its `QuasiIso` as an instance argument, and the chain map it
applies to is determined only by unification with the goal, so the instance is passed explicitly:
left to synthesis it is attempted while the chain map is still a metavariable.

## References

* [Stacks, Tag 09VX](https://stacks.math.columbia.edu/tag/09VX)
* [Stacks, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks, Tag 0157](https://stacks.math.columbia.edu/tag/0157)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex DerivedCategory

universe v₁ u₁ v₂ u₂

namespace StacksDraft.TotalComplexQuasiIso

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]

/-- **Flipping a double complex preserves diagonal finiteness.**  The two diagonals in total
degree `n` are exchanged by the involution `p ↦ n - p` of the index, so each is the image of the
other under a bijection. -/
lemma diagonalFinite_flip
    {Z : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    (h : DiagonalFinite Z) : DiagonalFinite Z.flip := by
  intro n
  refine ((h n).image (fun q ↦ n - q)).subset ?_
  intro p hp
  refine ⟨n - p, ?_, by simp⟩
  simp only [Set.mem_ofPred_eq] at hp ⊢
  have he : n - (n - p) = p := by omega
  rw [he]
  exact hp

end StacksDraft.TotalComplexQuasiIso

namespace StacksDraft.DerivedSectionsComparison

open StacksDraft.TotalComplexQuasiIso

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasCoproducts.{0} B]
variable [HasDerivedCategory B]
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory A] [EnoughInjectives A]
variable (Rs : A ⥤ CochainComplex.Plus (InjectiveObject A))
variable (ν : singlePlus A ⟶ IPlus Rs)
variable (T : A ⥤ CochainComplex B ℤ) [T.Additive]

/-- **The degreewise functor `M ↦ T(M)^p`.**  Its right acyclicity at `M` is what the row
hypotheses of the degeneration amount to. -/
abbrev rowFunctor (p : ℤ) : A ⥤ B := T ⋙ HomologicalComplex.eval B (ComplexShape.up ℤ) p

omit [HasCoproducts B] [HasDerivedCategory B] [HasDerivedCategory A] [EnoughInjectives A] in
/-- The row `p` of the flipped double complex is the degreewise functor applied to the
resolution. -/
theorem gammaI_rowFunctor_obj (M : A) (p : ℤ) :
    (gammaI (rowFunctor T p) (Icx Rs)).obj M = (((bicx T (Icx Rs)).obj M).flip).X p :=
  rfl

omit [HasCoproducts B] in
/-- **At an object right acyclic for `T(-)^p`, the row `p` of the double complex is a resolution
of `T(M)^p`.**  The resolution is bounded below and has injective terms, so this is
`CategoryTheory.Functor.quasiIso_mapHomologicalComplex_of_rightAcyclic_resolution` read through
`gammaNu_eq`, whose other factor is an isomorphism. -/
lemma quasiIso_gammaNu_rowFunctor (M : A) (p : ℤ) (hν : ∀ X : A, QuasiIso (nucx Rs ν X))
    (hrow : (rowFunctor T p).rightAcyclic M) :
    QuasiIso (gammaNu (rowFunctor T p) (Icx Rs) (nucx Rs ν) M) := by
  obtain ⟨n, hn⟩ := exists_isStrictlyGE_Icx Rs M
  have := hn
  have := hν M
  have h := CategoryTheory.Functor.quasiIso_mapHomologicalComplex_of_rightAcyclic_resolution
    (rowFunctor T p) n (injective_Icx_X Rs M) (nucx Rs ν M) hrow
  rw [gammaNu_eq]
  infer_instance

omit [HasCoproducts B] [HasDerivedCategory B] [HasDerivedCategory A] [EnoughInjectives A] in
/-- **The augmentation of the row is `rowAugFlip` in degree `p`.**  Both are the degreewise
functor applied to the augmentation `M ⟶ I^0` of the resolution. -/
lemma augZero_gammaNu_rowFunctor (M : A) (p : ℤ) :
    augZero ((rowFunctor T p).obj M) ((gammaI (rowFunctor T p) (Icx Rs)).obj M)
        (gammaNu (rowFunctor T p) (Icx Rs) (nucx Rs ν) M) =
      (rowAugFlip Rs ν T M).f p := by
  rw [augZero, gammaNu, mkHomFromSingle_f, Iso.inv_hom_id_assoc]
  rfl

/-- The row hypotheses, needing right acyclicity of `T(-)^p` at `M` only for `0 ≤ p`; the rows in
negative degrees are zero because `T` vanishes below degree zero. -/
private theorem hypotheses_flip_of_rightAcyclic_of_nonneg
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory B]
    (T : A ⥤ CochainComplex B ℤ) [T.Additive] (M : A)
    (hT0 : ∀ (Y : A) (q : ℤ), q < 0 → IsZero ((T.obj Y).X q))
    (hν : ∀ X : A, QuasiIso (nucx Rs ν X))
    (hGE : ((Icx Rs).obj M).IsStrictlyGE 0)
    (hrow : ∀ p : ℤ, 0 ≤ p → (rowFunctor T p).rightAcyclic M) :
    Hypotheses (T.obj M) (((bicx T (Icx Rs)).obj M).flip) (rowAugFlip Rs ν T M) where
  diagonalFinite :=
    diagonalFinite_flip (diagonalFinite_bicx T (Icx Rs) hT0 (exists_isStrictlyGE_Icx Rs) M)
  zero_of_neg p q hq := isZero_bicx_flip_X_X_of_isStrictlyGE Rs T M hGE p q hq
  exactAt_of_ne_zero p q hq := by
    rcases lt_or_ge p 0 with hp | hp
    · exact HomologicalComplex.ExactAt.of_isZero (hT0 _ p hp)
    · have := quasiIso_gammaNu_rowFunctor Rs ν T M p hν (hrow p hp)
      exact exactAt_of_quasiIso_single ((rowFunctor T p).obj M)
        ((gammaI (rowFunctor T p) (Icx Rs)).obj M)
        (gammaNu (rowFunctor T p) (Icx Rs) (nucx Rs ν) M) q hq
  inducesIsoKernel p := by
    rcases lt_or_ge p 0 with hp | hp
    · refine ⟨(hT0 M p hp).eq_of_src _ _, ?_⟩
      exact isIso_of_isZero _ (hT0 M p hp) (IsZero.of_mono (kernel.ι _) (hT0 _ p hp))
    · have hqi := quasiIso_gammaNu_rowFunctor Rs ν T M p hν (hrow p hp)
      have hz := isZero_bicx_flip_X_X_of_isStrictlyGE Rs T M hGE p (-1) (by omega)
      rw [← augZero_gammaNu_rowFunctor Rs ν T M p]
      exact ⟨augZero_comp_d _ _ _,
        @isIso_kernelLift_augZero B _ _ ((rowFunctor T p).obj M)
          ((gammaI (rowFunctor T p) (Icx Rs)).obj M) hz
          (gammaNu (rowFunctor T p) (Icx Rs) (nucx Rs ν) M) hqi⟩

omit [HasCoproducts B] in
/-- **The bridge:  the row hypotheses of the degeneration, from right acyclicity of the
degreewise functors.**  Let `T` vanish in negative degrees, let the functorial resolution be
concentrated in nonnegative degrees, and let every `T(-)^p` be right acyclic at `M`.  Then the
flipped double complex of the construction satisfies the hypotheses of [Stacks, Tag 0133], so
`StacksDraft.DerivedSectionsComparison.isIso_alpha_app_of_hypotheses` applies at `M`.

Nothing about injectivity of `M` is used:  the point of the statement is exactly that it holds at
objects which are not injective. -/
theorem hypotheses_flip_of_rightAcyclic (M : A)
    (hT0 : ∀ (Y : A) (q : ℤ), q < 0 → IsZero ((T.obj Y).X q))
    (hν : ∀ X : A, QuasiIso (nucx Rs ν X))
    (hGE : ((Icx Rs).obj M).IsStrictlyGE 0)
    (hrow : ∀ p : ℤ, (rowFunctor T p).rightAcyclic M) :
    Hypotheses (T.obj M) (((bicx T (Icx Rs)).obj M).flip) (rowAugFlip Rs ν T M) :=
  hypotheses_flip_of_rightAcyclic_of_nonneg Rs ν T M hT0 hν hGE fun p _ ↦ hrow p

/-- **The comparison of [Stacks, Tag 09VX] is an isomorphism at an object right acyclic for every
degreewise functor `T(-)^p`.**  This is `isIso_alpha_app_of_hypotheses` with the row hypotheses
discharged by `hypotheses_flip_of_rightAcyclic`. -/
theorem isIso_alpha_app_of_rightAcyclic (Γ : A ⥤ B) [Γ.Additive]
    (ε : ∀ X : A, (single B (ComplexShape.up ℤ) 0).obj (Γ.obj X) ⟶ T.obj X)
    (hε : ∀ {X Y : A} (φ : X ⟶ Y),
      (single B (ComplexShape.up ℤ) 0).map (Γ.map φ) ≫ ε Y = ε X ≫ T.map φ)
    (hT0 : ∀ (Y : A) (q : ℤ), q < 0 → IsZero ((T.obj Y).X q))
    (hεinj : ∀ Y : A, Injective Y → QuasiIso (ε Y))
    (hν : ∀ X : A, QuasiIso (nucx Rs ν X)) (M : A)
    (hGE : ((Icx Rs).obj M).IsStrictlyGE 0)
    (hrow : ∀ p : ℤ, (rowFunctor T p).rightAcyclic M) :
    IsIso ((alpha Γ Rs ν T ε hε hT0 hεinj hν).app M) :=
  isIso_alpha_app_of_hypotheses Rs ν Γ T ε hε hT0 hεinj hν M
    (hypotheses_flip_of_rightAcyclic Rs ν T M hT0 hν hGE hrow)

omit [HasCoproducts B] [HasDerivedCategory B] in
/-- **A kernel of a morphism out of a zero object is a zero object.** -/
theorem isZero_kernel_of_isZero_src {X Y : B} (g : X ⟶ Y) (hX : IsZero X) :
    IsZero (kernel g) := by
  rw [IsZero.iff_id_eq_zero]
  refine (cancel_mono (kernel.ι g)).mp ?_
  rw [Category.id_comp, zero_comp]
  exact hX.eq_of_tgt _ _

omit [HasCoproducts B] in
/-- **The row hypotheses, needing right acyclicity only in nonnegative degrees.**  In a negative
degree `p` the whole row consists of zero objects, because `T` vanishes below degree zero, so both
substantive fields are immediate:  the row is exact everywhere, and the kernel it must exhibit is
a kernel of a morphism out of a zero object.

This is the form the relative hypercovering complex is used in:  its degreewise functors are
nonzero only in nonnegative degrees, and there is nothing to prove about the others. -/
theorem hypotheses_flip_of_rightAcyclic_nonneg (M : A)
    (hT0 : ∀ (Y : A) (q : ℤ), q < 0 → IsZero ((T.obj Y).X q))
    (hν : ∀ X : A, QuasiIso (nucx Rs ν X))
    (hGE : ((Icx Rs).obj M).IsStrictlyGE 0)
    (hrow : ∀ n : ℕ, (rowFunctor T (n : ℤ)).rightAcyclic M) :
    Hypotheses (T.obj M) (((bicx T (Icx Rs)).obj M).flip) (rowAugFlip Rs ν T M) :=
  hypotheses_flip_of_rightAcyclic_of_nonneg Rs ν T M hT0 hν hGE fun p hp ↦ by
    lift p to ℕ using hp
    exact hrow p

end StacksDraft.DerivedSectionsComparison

end
