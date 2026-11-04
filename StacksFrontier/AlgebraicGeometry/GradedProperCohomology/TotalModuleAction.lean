module

public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.AffineFiniteType
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.CohomologyDirectSum
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.GradedAction

/-!
# The action of `B` on the total module, and the cohomology of the total module

[Stacks, Tag 0897]'s proof writes `H^p(X, ℱ)` both for the graded module `⨁ₙ H^p(X, ℱₙ)` and
for the cohomology of the single sheaf `⨁ₙ ℱₙ` whose direct image from `X'` is `ℱ`.
`GradedProperCohomology/CohomologyDirectSum.lean` identifies the two as `Γ(X, ⊤)`-modules;
this file adds the `B`-equivariance of that identification, which is what the conclusion of
part (1) — a statement about a graded `B`-module — needs.

A homogeneous element `b` of degree `k` acts on the total module `⨁ₙ ℱₙ` by the morphism
`totalActHom` which on the summand of degree `n` is the action `ℱₙ ⟶ ℱₙ₊ₖ` of
`GradedProperCohomology/GradedAction.lean` followed by the inclusion of the summand of degree
`n + k`. The comparison `H^p(X, ⨁ₙ ℱₙ) ≃ ⨁ₙ H^p(X, ℱₙ)` carries `H^p(totalActHom b)` to
multiplication by `b` for the graded action `gradedCohomologyModule`.

The proof is the compatibility of the comparison with the summand inclusions: `H^p` of the
inclusion of the degree-`n` summand lands in the degree-`n` component, which is
`gradedCohomologySumEquiv_cohoMap_ι`, and the claim then reduces to the homogeneous classes,
where it is `ι_comp_totalActHom` followed by `gradedCohomologyModule_smul_of`.

## Main definitions

* `Stacks.AlgebraicGeometry.GradedProperCohomology.totalActHom`: the endomorphism of
  `⨁ₙ ℱₙ` given by a homogeneous element of `B`.

## Main results

* `gradedCohomologySumEquiv_cohoMap_ι` and `gradedCohomologySumEquiv_symm_of`: the comparison
  matches the summand inclusions with the components of the direct sum.
* `gradedCohomologySumEquiv_cohoMap_totalActHom`: **the comparison
  `H^p(X, ⨁ₙ ℱₙ) ≃ ⨁ₙ H^p(X, ℱₙ)` is `B`-equivariant.**
* `moduleFinite_gradedCohomologySum_gradedAction`: **[Stacks, Tag 0897] part (1) with the
  graded `B`-module structure of its conclusion constructed rather than assumed.**

## Implementation notes

What is still assumed, and is what stands between this and an unconditional
[Stacks, Tag 0897] part (1): the coherent `𝒪_{X'}`-module `ℱ'` with `π_* ℱ' = ⨁ₙ ℱₙ`, and the
comparison of `⨁ₙ H^p(X, ℱₙ)` with `H^p(X', ℱ')`. The `Γ(X, ⊤)`-linear comparison is
`gradedCohomologyIsoPushforward`; making it `B`-linear needs, beyond this file, the
naturality of [Stacks, Tag 089W] at an endomorphism of `ℱ'`, which
`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward` is not currently equipped with
— it is a per-object isomorphism and no lemma states its naturality.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.GradedModule
open scoped AlgebraicGeometry ModuleCat.Algebra

universe u

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}}
  {𝓑 : _root_.SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {𝒜 : ℕ → Submodule A B}
  [_root_.GradedAlgebra 𝒜] (σ : HomogeneousSectionAssignment 𝒜 𝓑)
  (F : _root_.SheafOfModules.GradedModule 𝓑)

/-- **The endomorphism of the total module `⨁ₙ ℱₙ` given by a homogeneous element of `B`**:
on the summand of degree `n` it is the action `ℱₙ ⟶ ℱₙ₊ₖ` followed by the inclusion. -/
def totalActHom {k : ℕ} (b : ↥(𝒜 k)) : totalModule F ⟶ totalModule F :=
  Sigma.desc fun n : ℤ =>
    actHom σ F b n rfl ≫ Sigma.ι (fun m : ℤ => pieceModule F m) (n + (k : ℤ))

/-- On the summand of degree `n`, `totalActHom σ F b` is the action `ℱₙ ⟶ ℱₙ₊ₖ` of `b`
followed by the inclusion of the summand of degree `n + k`. -/
theorem ι_comp_totalActHom {k : ℕ} (b : ↥(𝒜 k)) (n : ℤ) :
    Sigma.ι (fun m : ℤ => pieceModule F m) n ≫ totalActHom σ F b =
      actHom σ F b n rfl ≫ Sigma.ι (fun m : ℤ => pieceModule F m) (n + (k : ℤ)) :=
  colimit.ι_desc _ _

section Qcqs

variable [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)]

/-- The comparison `H^p(X, ⨁ₙ ℱₙ) ≃ ⨁ₙ H^p(X, ℱₙ)` sends the class coming from the degree-`n`
summand to the degree-`n` component. -/
theorem gradedCohomologySumEquiv_cohoMap_ι (p : ℕ) (n : ℤ)
    (x : ↥(cohomologyOf X p (pieceModule F n))) :
    gradedCohomologySumEquiv F p
        (cohoMap p (Sigma.ι (fun m : ℤ => pieceModule F m) n) x) =
      DirectSum.of (fun m : ℤ => ↥(cohomologyOf X p (pieceModule F m))) n x := by
  have key :
      ((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map
            (Sigma.ι (fun m : ℤ => pieceModule F m) n) ≫
          (cohomologyTotalModuleIso F p ≪≫
            ModuleCat.coprodIsoDirectSum
              fun m : ℤ => cohomologyOf X p (pieceModule F m)).hom =
        ModuleCat.ofHom (DirectSum.lof Γ(X, ⊤) ℤ
          (fun m : ℤ => ↥(cohomologyOf X p (pieceModule F m))) n) := by
    have := preservesColimitsOfShape_discrete_int_cohomology (X := X) p
    rw [cohomologyTotalModuleIso, Iso.trans_hom, Iso.trans_hom]
    simp
  exact congrArg (fun φ : cohomologyOf X p (pieceModule F n) ⟶
    ModuleCat.of Γ(X, ⊤) (gradedCohomologySum F p) => φ.hom x) key

/-- The comparison in the other direction: the degree-`n` component comes from the degree-`n`
summand. -/
theorem gradedCohomologySumEquiv_symm_of (p : ℕ) (n : ℤ)
    (x : ↥(cohomologyOf X p (pieceModule F n))) :
    (gradedCohomologySumEquiv F p).symm
        (DirectSum.of (fun m : ℤ => ↥(cohomologyOf X p (pieceModule F m))) n x) =
      cohoMap p (Sigma.ι (fun m : ℤ => pieceModule F m) n) x :=
  (LinearEquiv.symm_apply_eq _).mpr (gradedCohomologySumEquiv_cohoMap_ι F p n x).symm

/-- **The identification `H^p(X, ⨁ₙ ℱₙ) ≃ ⨁ₙ H^p(X, ℱₙ)` carries the action of `B` on the
total module to the graded action of `B` on the graded cohomology**, on a homogeneous
element. -/
theorem gradedCohomologySumEquiv_cohoMap_totalActHom (p : ℕ) {k : ℕ} (b : ↥(𝒜 k))
    (z : gradedCohomologySum F p) :
    letI := gradedCohomologyModule σ F p
    gradedCohomologySumEquiv F p
        (cohoMap p (totalActHom σ F b) ((gradedCohomologySumEquiv F p).symm z)) =
      (b : B) • z := by
  let := gradedCohomologyModule σ F p
  induction z using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, smul_zero]
  | of n x =>
      have h1 : cohoMap p (totalActHom σ F b)
            (cohoMap p (Sigma.ι (fun m : ℤ => pieceModule F m) n) x) =
          cohoMap p (Sigma.ι (fun m : ℤ => pieceModule F m) (n + (k : ℤ)))
            (cohoMap p (actHom σ F b n rfl) x) :=
        ((cohoMap_comp p _ _ x).trans
          (congrArg (fun φ : pieceModule F n ⟶ totalModule F => cohoMap p φ x)
            (ι_comp_totalActHom σ F b n))).trans
          (cohoMap_comp p (actHom σ F b n rfl)
            (Sigma.ι (fun m : ℤ => pieceModule F m) (n + (k : ℤ))) x).symm
      rw [gradedCohomologySumEquiv_symm_of, h1, gradedCohomologySumEquiv_cohoMap_ι]
      exact (gradedCohomologyModule_smul_of σ F p b n x).symm
  | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz', smul_add]

end Qcqs

/-! ### Part (1) of Tag 0897 over the canonical graded action -/

/-- **[Stacks, Tag 0897] part (1), with the graded `B`-module structure of its conclusion
constructed rather than assumed.** Let `A` be a Noetherian ring, `B` a finitely generated
graded `A`-algebra, `f : X ⟶ Spec A` proper and `ℱ` a quasi-coherent graded `𝓑`-module of
finite type, and let `σ` give the global homogeneous sections of `𝓑` attached to the
homogeneous elements of `B`. Granted a proper `f' : X' ⟶ Spec B`, a coherent `𝒪_{X'}`-module
`ℱ'` and a comparison of `⨁ₙ H^p(X, ℱₙ)` with `H^p(X', ℱ')` that is linear for **that**
action, the graded `B`-module `⨁ₙ H^p(X, ℱₙ)` is a finite `B`-module.

The difference from `moduleFinite_gradedCohomologySum'` is the `B`-action: there it is an
instance binder, so the comparison constrains an arbitrary module structure; here it is
`gradedCohomologyModule`, the action induced by `𝓑` on `ℱ`, which is the one the tag's
conclusion is about. -/
theorem moduleFinite_gradedCohomologySum_gradedAction
    [IsNoetherianRing A] [Algebra.FiniteType A B] (σ : HomogeneousSectionAssignment 𝒜 𝓑)
    (f : X ⟶ Spec (.of A)) [IsProper f]
    (F : _root_.SheafOfModules.GradedModule 𝓑)
    (hqc : ∀ n : ℤ, (pieceModule F n).IsQuasicoherent)
    (hft : Stacks.Coherent.IsFiniteTypeOnAffine F)
    (p : ℕ)
    {X' : Scheme.{u}} (f' : X' ⟶ Spec (.of B)) [IsProper f']
    (F' : X'.Modules) [F'.IsCoherent]
    (cmp : letI := gradedCohomologyModule σ F p
      gradedCohomologySum F p ≃ₗ[B]
        ↥((ModuleCat.restrictScalars (specAlgebraRingHom B f')).obj
          (cohomologyOf X' p F'))) :
    letI := gradedCohomologyModule σ F p
    Module.Finite B (gradedCohomologySum F p) :=
  let := gradedCohomologyModule σ F p
  moduleFinite_gradedCohomologySum' A 𝒜 f F hqc hft p f' F' cmp

end Stacks.AlgebraicGeometry.GradedProperCohomology

end
