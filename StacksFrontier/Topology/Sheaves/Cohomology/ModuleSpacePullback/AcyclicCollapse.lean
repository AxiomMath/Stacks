module

public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Effaceable
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Precomp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The derived functor of a composite collapses as an isomorphism of δ-functors

Let `Ψ : A ⥤ B` be exact and let `G : B ⥤ D` be additive and left exact.  If `Ψ` carries every
injective object of `A` to a `G`-acyclic object of `B`, then the right derived functors of the
composite are `Ψ` followed by the right derived functors of `G`.  Degreewise that is
`Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic`.  **What this
file adds is that the collapse is an isomorphism of cohomological δ-functors**, so the two long
exact sequences match up: the comparison commutes with the connecting morphisms.

That is the step that a degreewise isomorphism does not give and cannot be made to give.  An
unconstrained family of isomorphisms `Rⁿ(Ψ ⋙ G) ≅ Ψ ⋙ RⁿG` satisfies no relation to the
connecting morphisms, exactly as for `Stacks.Cohomology.SpectralLimit.IsCohomologyMap`.

## Why both halves are available

Both sides are **universal** δ-functors (Stacks 010S), so by Stacks 010U a degree-zero
identification extends to an isomorphism of δ-functors, uniquely — and an isomorphism of
δ-functors is by definition compatible with the connecting morphisms, in both directions.

* The source, `Rⁿ(Ψ ⋙ G)`, is universal because right derived functors vanish on injective
  objects (Stacks 010T).  Nothing is needed for this.
* The target, `Ψ ⋙ RⁿG`, is universal because of the **acyclicity hypothesis itself**:
  `CategoryTheory.DeltaFunctor.Effaceable.precomp` asks that every object admit a monomorphism
  into one whose `Ψ`-image is killed by `Rⁿ⁺¹G`, and an injective object does, precisely because
  `G`-acyclicity of `Ψ(I)` *is* the vanishing of `Rⁿ⁺¹G(Ψ I)` (Stacks 015C,
  `Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived`).

So the one hypothesis that makes the degreewise collapse true is also the one that makes it
δ-compatible.  That is not a coincidence worth hiding: it is why no extra input appears below.

## The degree-zero normalisation

The isomorphism is pinned by its degree-zero component, taken to be the canonical one:
`Rⁿ` of a left exact functor is that functor in degree zero
(`CategoryTheory.Functor.rightDerivedZeroIsoSelf`), on both sides, and `Ψ ⋙ G` is the composite.
So `collapseZeroIso` involves no choice.

**What is deliberately not claimed** is that the degree-`n` component agrees with
`rightDerivedCompIsoOfAcyclic n` for `n > 0`.  Stacks 010U pins only degree zero, and the
degreewise comparison is built by a different route (the derived-category comparison
`CategoryTheory.Functor.rightDerivedFunctorPlusComp`); identifying them is a further statement
that nothing here needs.  A reader who needs a *formula* in positive degree should use
`rightDerivedCompIsoOfAcyclic`, and a reader who needs *δ-compatibility* should use this file;
the two are not interchangeable.

## Main results

* `Stacks.Cohomology.DeltaAcyclicCollapse.isUniversal_rightDerivedDeltaFunctor`: a right-derived
  δ-functor is universal.  Stated generally because it is the half of Stacks 010U that needs no
  hypothesis.
* `Stacks.Cohomology.DeltaAcyclicCollapse.effaceable_precomp` and `isUniversal_precomp`: the
  acyclicity hypothesis makes `Ψ ⋙ RⁿG` effaceable, hence universal.
* `Stacks.Cohomology.DeltaAcyclicCollapse.collapseDeltaIso`: **the collapse as an isomorphism of
  δ-functors.**
* `Stacks.Cohomology.DeltaAcyclicCollapse.collapseDeltaIso_comm` and
  `collapseDeltaIso_inv_comm`: the δ-square, in both directions.  The **inverse** direction is
  the one a consumer comparing `RⁿG(Ψ F)` with `Rⁿ(Ψ ⋙ G)(F)` wants, since the comparison map it
  has goes that way.
* `Stacks.Cohomology.DeltaAcyclicCollapse.collapseDeltaIso_unique`: the isomorphism is the unique
  one extending the degree-zero comparison (Stacks 010U, uniqueness).

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 010S](https://stacks.math.columbia.edu/tag/010S)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
* [Stacks Project, Tag 010U](https://stacks.math.columbia.edu/tag/010U)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.DeltaAcyclicCollapse

universe v₁ v₂ v₃ u₁ u₂ u₃

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [EnoughInjectives A] [HasDerivedCategory A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [EnoughInjectives B] [HasDerivedCategory B]
  {D : Type u₃} [Category.{v₃} D] [Abelian D] [HasDerivedCategory D]

/-- **A right-derived δ-functor is universal** (Stacks 010T): the higher right derived functors
of an additive functor vanish on injective objects, and the source has enough injectives.  This
is the half of Stacks 010U that costs nothing. -/
theorem isUniversal_rightDerivedDeltaFunctor (F : A ⥤ D) [F.Additive] :
    (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives F).IsUniversal :=
  DeltaFunctor.isUniversal_of_isZero_injective _
    (fun n I _ => F.isZero_rightDerived_obj_injective_succ n I)

variable (Ψ : A ⥤ B) [Ψ.Additive] [PreservesFiniteLimits Ψ] [PreservesFiniteColimits Ψ]
  (G : B ⥤ D) [G.Additive] [PreservesFiniteLimits G]

omit [HasDerivedCategory A] in
/-- **The acyclicity hypothesis is exactly effaceability of `Ψ ⋙ RⁿG`.**  Embed an object into
an injective one; its `Ψ`-image is `G`-acyclic by hypothesis, and `G`-acyclicity is the vanishing
of every higher right derived functor there (Stacks 015C). -/
theorem effaceable_precomp
    (hac : ∀ I : A, Injective I → G.rightAcyclic (Ψ.obj I)) :
    ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives G).precomp
      Ψ).Effaceable :=
  DeltaFunctor.Effaceable.precomp _ Ψ (fun X =>
    ⟨Injective.under X, Injective.ι X, inferInstance, fun n =>
      (Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived G
          (Ψ.obj (Injective.under X))).1
        (hac _ inferInstance) (n + 1) n.succ_pos⟩)

omit [HasDerivedCategory A] in
/-- **`Ψ ⋙ RⁿG` is a universal δ-functor** (Stacks 010T), by `effaceable_precomp`. -/
theorem isUniversal_precomp
    (hac : ∀ I : A, Injective I → G.rightAcyclic (Ψ.obj I)) :
    ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives G).precomp
      Ψ).IsUniversal :=
  have := effaceable_precomp Ψ G hac
  DeltaFunctor.isUniversal_of_effaceable _

/-- **The degree-zero comparison**, which involves no choice: in degree zero the right derived
functors of a left exact functor are that functor, on both sides. -/
def collapseZeroIso : (Ψ ⋙ G).rightDerived 0 ≅ Ψ ⋙ G.rightDerived 0 :=
  (Ψ ⋙ G).rightDerivedZeroIsoSelf ≪≫
    Functor.isoWhiskerLeft Ψ G.rightDerivedZeroIsoSelf.symm

/-- **The derived functor of a composite collapses as an isomorphism of δ-functors.**  For `Ψ`
exact carrying injectives to `G`-acyclic objects, the long exact sequence of `Rⁿ(Ψ ⋙ G)` and the
long exact sequence of `RⁿG` at the image sequence are identified — connecting morphisms
included.

Both sides are universal δ-functors, so Stacks 010U extends `collapseZeroIso` uniquely, and an
isomorphism of δ-functors is compatible with the connecting morphisms by definition. -/
def collapseDeltaIso (hac : ∀ I : A, Injective I → G.rightAcyclic (Ψ.obj I)) :
    Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives (Ψ ⋙ G) ≅
      (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives G).precomp Ψ :=
  have := isUniversal_rightDerivedDeltaFunctor (Ψ ⋙ G)
  have := isUniversal_precomp Ψ G hac
  DeltaFunctor.IsUniversal.isoOfIso (collapseZeroIso Ψ G)

/-- The degree-zero component of the collapse is the canonical comparison. -/
@[simp]
theorem collapseDeltaIso_hom_app_zero
    (hac : ∀ I : A, Injective I → G.rightAcyclic (Ψ.obj I)) :
    (collapseDeltaIso Ψ G hac).hom.app 0 = (collapseZeroIso Ψ G).hom := by
  have := isUniversal_rightDerivedDeltaFunctor (Ψ ⋙ G)
  have := isUniversal_precomp Ψ G hac
  exact DeltaFunctor.IsUniversal.lift_app_zero _ _

/-- The degree-zero component of the inverse collapse is the inverse canonical comparison. -/
@[simp]
theorem collapseDeltaIso_inv_app_zero
    (hac : ∀ I : A, Injective I → G.rightAcyclic (Ψ.obj I)) :
    (collapseDeltaIso Ψ G hac).inv.app 0 = (collapseZeroIso Ψ G).inv := by
  have := isUniversal_rightDerivedDeltaFunctor (Ψ ⋙ G)
  have := isUniversal_precomp Ψ G hac
  exact DeltaFunctor.IsUniversal.lift_app_zero _ _

/-- **The collapse commutes with the connecting morphisms.**  For a short exact sequence `S` of
`A`, the connecting morphism of `Rⁿ(Ψ ⋙ G)` at `S` and the connecting morphism of `RⁿG` at the
image sequence `Ψ(S)` are matched by the comparison. -/
theorem collapseDeltaIso_comm (hac : ∀ I : A, Injective I → G.rightAcyclic (Ψ.obj I))
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    ((collapseDeltaIso Ψ G hac).hom.app n).app S.X₃ ≫
        (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives G).δ
          (hS.map_of_exact Ψ) n =
      (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives (Ψ ⋙ G)).δ hS n ≫
        ((collapseDeltaIso Ψ G hac).hom.app (n + 1)).app S.X₁ :=
  (collapseDeltaIso Ψ G hac).hom.comm hS n

/-- **The inverse collapse commutes with the connecting morphisms.**  This is the direction a
consumer wants: it has a comparison *into* `Rⁿ(Ψ ⋙ G)` out of `RⁿG(Ψ −)`, and this says that
comparison is δ-compatible. -/
theorem collapseDeltaIso_inv_comm (hac : ∀ I : A, Injective I → G.rightAcyclic (Ψ.obj I))
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    ((collapseDeltaIso Ψ G hac).inv.app n).app S.X₃ ≫
        (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives (Ψ ⋙ G)).δ hS n =
      (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives G).δ
          (hS.map_of_exact Ψ) n ≫
        ((collapseDeltaIso Ψ G hac).inv.app (n + 1)).app S.X₁ :=
  (collapseDeltaIso Ψ G hac).inv.comm hS n

/-- **The collapse is the unique isomorphism of δ-functors extending the degree-zero
comparison** (Stacks 010U, uniqueness). -/
theorem collapseDeltaIso_unique (hac : ∀ I : A, Injective I → G.rightAcyclic (Ψ.obj I))
    (α : Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives (Ψ ⋙ G) ≅
      (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives G).precomp Ψ)
    (hα : α.hom.app 0 = (collapseZeroIso Ψ G).hom) : α = collapseDeltaIso Ψ G hac := by
  have := isUniversal_rightDerivedDeltaFunctor (Ψ ⋙ G)
  exact DeltaFunctor.IsUniversal.iso_ext
    (hα.trans (collapseDeltaIso_hom_app_zero Ψ G hac).symm)

end Stacks.Cohomology.DeltaAcyclicCollapse

end
