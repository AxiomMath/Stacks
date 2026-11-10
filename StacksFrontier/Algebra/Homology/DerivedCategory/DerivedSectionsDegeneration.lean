module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSectionsComparison

/-!
# Degeneration of the comparison map away from the injective objects

`StacksDraft.DerivedSectionsComparison.alpha` is the comparison

`α : Q(T(-)) ⟶ R⁺Γ((-)[0])`

built in the proof of [Stacks, Tag 09VX] out of an additive `T : A ⥤ CochainComplex B ℤ`
augmented by `ε : Γ(X)[0] ⟶ T(X)`, and
`StacksDraft.DerivedSectionsComparison.isIso_alpha_app` says that it is an isomorphism at every
*injective* object of `A`.

This file identifies exactly what makes it an isomorphism at an arbitrary object `M`:  that the
*rows* of the double complex `A^{p,q} = T(I^q)^p` of the construction are resolutions of the
corresponding terms `T(M)^p` of the complex, where `I^•` is the functorial injective resolution
of `M`.

## Main results

* `exists_resolutionData_isStrictlyGE`:  the functorial injective resolution of
  `StacksDraft.DerivedSectionsComparison.exists_resolutionData` can be chosen concentrated in
  nonnegative degrees.
* `isZero_bicx_flip_X_X_of_isStrictlyGE`:  with such a resolution the double complex vanishes in
  negative rows.
* `rowAugFlip`:  the augmentation of the row direction, `T(M) ⟶ A^{•,0}`, which is `T` applied to
  the augmentation `M ⟶ I^0` of the resolution.
* `quasiIso_tToTot_of_hypotheses`:  under the row hypotheses of [Stacks, Tag 0133] the second leg
  `T(M) ⟶ Tot(A)` of the comparison is a quasi-isomorphism.
* `isIso_alpha_app_of_hypotheses`:  therefore `α` is an isomorphism at `M`.
* `exists_comparison_of_hypotheses`:  the packaged statement — the comparison exists, is pinned by
  the augmentation, and is an isomorphism at every injective object *and* at every object
  satisfying the row hypotheses.

## Implementation notes

`rowZero` of the flipped double complex is the complex `A^{•,0} = T(I^0)`, by structure eta:  its
term in degree `p` is `(A.flip.X p).X 0 = (A.X 0).X p` and its differential is `(A.X 0).d`.  So
`rowAugFlip` needs no transport and is `T.map` of the augmentation of the resolution.

The row hypotheses are stated as `StacksDraft.TotalComplexQuasiIso.Hypotheses` of the flipped
double complex rather than as right acyclicity of the functors `M ↦ T(M)^p`:  that is the form
`quasiIso_total_of_resolution_flip` consumes, and it is weaker, since it asks for the resolution
to be the one the construction uses rather than for an arbitrary one.

## References

* [Stacks, Tag 09VX](https://stacks.math.columbia.edu/tag/09VX)
* [Stacks, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex DerivedCategory
open StacksDraft.TotalComplexQuasiIso

universe v₁ u₁ v₂ u₂

namespace StacksDraft.DerivedSectionsComparison

variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasCoproducts.{0} B]
variable [HasDerivedCategory B]
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory A] [EnoughInjectives A]
variable (Rs : A ⥤ CochainComplex.Plus (InjectiveObject A))
variable (ν : singlePlus A ⟶ IPlus Rs)
variable (Γ : A ⥤ B) [Γ.Additive]
variable (T : A ⥤ CochainComplex B ℤ) [T.Additive]
  (ε : ∀ X : A, (single B (ComplexShape.up ℤ) 0).obj (Γ.obj X) ⟶ T.obj X)
  (hε : ∀ {X Y : A} (φ : X ⟶ Y),
    (single B (ComplexShape.up ℤ) 0).map (Γ.map φ) ≫ ε Y = ε X ≫ T.map φ)
  (hT0 : ∀ (Y : A) (q : ℤ), q < 0 → IsZero ((T.obj Y).X q))
  (hεinj : ∀ Y : A, Injective Y → QuasiIso (ε Y))

/-- **A functorial injective resolution of the objects of `A` concentrated in nonnegative
degrees.**  This is `StacksDraft.DerivedSectionsComparison.exists_resolutionData` together with
the lower bound:  the resolving complex `I^•` of an object vanishes in every negative degree. -/
theorem exists_resolutionData_isStrictlyGE (A : Type u₁) [Category.{v₁} A] [Abelian A]
    (h : HasFunctorialInjectiveEmbeddings A) :
    ∃ (Rs : A ⥤ CochainComplex.Plus (InjectiveObject A))
      (ν : singlePlus A ⟶ Rs ⋙ (InjectiveObject.ι A).mapCochainComplexPlus),
      (∀ X : A, QuasiIso ((CochainComplex.Plus.ι A).map (ν.app X))) ∧
        ∀ X : A, ((Icx Rs).obj X).IsStrictlyGE 0 := by
  obtain ⟨Kf, η, hη⟩ := exists_injectiveEmbeddingData A h
  obtain ⟨Fr, α, hα, hGE⟩ :=
    CochainComplex.Plus.exists_functorial_injective_resolution_isStrictlyGE A Kf η hη
  exact ⟨singlePlus A ⋙ Fr, Functor.whiskerLeft (singlePlus A) α,
    fun X => hα ((singlePlus A).obj X),
    fun X => hGE ((singlePlus A).obj X) 0
      (by
        change CochainComplex.IsStrictlyGE ((single A (ComplexShape.up ℤ) 0).obj X) 0
        infer_instance)⟩

omit [HasCoproducts B] [HasDerivedCategory B] [HasDerivedCategory A] [EnoughInjectives A] in
/-- **The double complex of the construction vanishes in negative rows** when the resolution does:
in the flipped reading, its degree `q` is the resolution degree. -/
lemma isZero_bicx_flip_X_X_of_isStrictlyGE (M : A)
    (hGE : ((Icx Rs).obj M).IsStrictlyGE 0) (p q : ℤ) (hq : q < 0) :
    IsZero (((((bicx T (Icx Rs)).obj M).flip).X p).X q) :=
  have := hGE
  (HomologicalComplex.eval B (ComplexShape.up ℤ) p).map_isZero
    (T.map_isZero (((Icx Rs).obj M).isZero_of_isStrictlyGE 0 q hq))

/-- **The augmentation of the double complex in the row direction.**  The row `p` of
`A^{p,q} = T(I^q)^p` is the complex `q ↦ T(I^q)^p`, and the map into its degree-zero term from
`T(M)^p` is `T` applied to the augmentation `M ⟶ I^0` of the resolution.

Assembled over `p` this is a chain map `T(M) ⟶ A^{•,0}`, and `A^{•,0}` is `rowZero` of the
flipped double complex. -/
def rowAugFlip (M : A) : T.obj M ⟶ rowZero (((bicx T (Icx Rs)).obj M).flip) :=
  T.map (augZero M ((Icx Rs).obj M) (nucx Rs ν M))

omit [HasDerivedCategory B] [HasDerivedCategory A] [EnoughInjectives A] in
/-- **The second leg of the comparison is a quasi-isomorphism when the rows are resolutions.**
If the flipped double complex satisfies the hypotheses of [Stacks, Tag 0133], then the map
`tToTot : T(M) ⟶ Tot(A)` is a quasi-isomorphism. -/
lemma quasiIso_tToTot_of_hypotheses (M : A)
    (h : Hypotheses (T.obj M) (((bicx T (Icx Rs)).obj M).flip) (rowAugFlip Rs ν T M)) :
    QuasiIso (tToTot T (Icx Rs) (nucx Rs ν) M) := by
  obtain ⟨_, g, hg, hgq⟩ := quasiIso_total_of_resolution_flip (T.obj M)
    ((bicx T (Icx Rs)).obj M) (rowAugFlip Rs ν T M) h
  have heq : g = tToTot T (Icx Rs) (nucx Rs ν) M := by
    refine HomologicalComplex.hom_ext _ _ (fun n ↦ ?_)
    rw [hg n, tToTot_f']
    rfl
  rw [heq] at hgq
  exact hgq

/-- **The comparison is an isomorphism at an object whose rows are resolutions.**  If the rows of
the flipped double complex at `M` satisfy the hypotheses of [Stacks, Tag 0133], then `α` is an
isomorphism at `M`. -/
lemma isIso_alpha_app_of_hypotheses (hν : ∀ X : A, QuasiIso (nucx Rs ν X)) (M : A)
    (h : Hypotheses (T.obj M) (((bicx T (Icx Rs)).obj M).flip) (rowAugFlip Rs ν T M)) :
    IsIso ((alpha Γ Rs ν T ε hε hT0 hεinj hν).app M) := by
  have h1 : IsIso (DerivedCategory.Plus.Q.map ((tTotNat Rs ν T hT0).app M)) :=
    isIso_PlusQ_map _ (quasiIso_tToTot_of_hypotheses Rs ν T M h)
  rw [alpha, NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerRight_app]
  infer_instance

include hεinj in
/-- **The comparison map of [Stacks, Tag 09VX] with its degeneration.**  Under the hypotheses of
`StacksDraft.DerivedSectionsComparison.exists_comparison` there is a natural transformation
`α : Q(T(-)) ⟶ R⁺Γ((-)[0])` compatible with the augmentation, which is an isomorphism at every
injective object and also at every object for which the rows of the double complex of the
construction are resolutions. -/
theorem exists_comparison_of_hypotheses (hν : ∀ X : A, QuasiIso (nucx Rs ν X))
    (P : A → Prop)
    (hP : ∀ M : A, P M →
      Hypotheses (T.obj M) (((bicx T (Icx Rs)).obj M).flip) (rowAugFlip Rs ν T M)) :
    ∃ α : TPlus T hT0 ⋙ DerivedCategory.Plus.Q ⟶
        DerivedCategory.Plus.singleFunctor A 0 ⋙ Γ.rightDerivedFunctorPlus,
      Functor.whiskerRight (epsNat Γ T ε hε hT0) DerivedCategory.Plus.Q ≫ α =
          psi Γ Rs ν hν ∧
        (∀ X : A, Injective X → IsIso (α.app X)) ∧
        (∀ M : A, P M → IsIso (α.app M)) :=
  ⟨alpha Γ Rs ν T ε hε hT0 hεinj hν, epsNat_comp_alpha Γ Rs ν T ε hε hT0 hεinj hν,
    fun X _hX => isIso_alpha_app Γ Rs ν T ε hε hT0 hεinj hν X,
    fun M hM => isIso_alpha_app_of_hypotheses Rs ν Γ T ε hε hT0 hεinj hν M (hP M hM)⟩

end StacksDraft.DerivedSectionsComparison

end
