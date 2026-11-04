module

public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveLocusOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional

/-!
# The open subspace where a map of quasi-coherent modules is surjective

Let `X` be an algebraic space over a scheme `S` of a big fppf site and let `u : 𝓖 ⟶ 𝓕` be a map
of quasi-coherent `𝒪_X`-modules with `𝓕` of finite type. The support of the cokernel of `u` is a
closed subset of `|X|`, and its complement carries an open subspace of `X` (Stacks 03BZ). This
file records that a scheme over `X` factors through that open subspace exactly when the pullback
of `u` to it is surjective. It is the case `f = 𝟙` of Stacks 09TP, stated directly at the scheme
points of `X` rather than through the base changes of a situation of Stacks 083F.

## Main definitions

* `AlgebraicGeometry.Space.surjectivityLocus`: the open subspace of `X` on the complement of the
  support of `Coker u`.

## Main results

* `AlgebraicGeometry.Space.isOpenSubspace_surjectivityLocus`: it is an open subspace.
* `AlgebraicGeometry.Space.exists_factor_surjectivityLocus_iff`: a morphism `t : h_A ⟶ X` from
  a scheme of the site factors through it exactly when `t^*u` is an epimorphism.

## References

* [Stacks Project, Tag 09TP](https://stacks.math.columbia.edu/tag/09TP)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

variable {X : AlgebraicSpaces B S hS} {𝓖 𝓕 : Modules.{u, u} B S hS X.1 X.2} (u : 𝓖 ⟶ 𝓕)

/-- The cokernel of `u`, as an `𝒪_X`-module. Naming it fixes the module universe before the
cokernel is formed. -/
abbrev surjectivityCokernel : Modules.{u, u} B S hS X.1 X.2 := cokernel u

/-- The open subspace of `X` on which the map `u` is surjective: the subspace cut out by the
complement of the support of the cokernel of `u`. -/
def surjectivityLocus : Subfunctor X.1 :=
  openSubspaceOfPoints B S hS X.1
    (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (surjectivityCokernel u)))ᶜ

/-- The surjectivity locus of a map of quasi-coherent modules with target of finite type is an
open subspace. -/
theorem isOpenSubspace_surjectivityLocus (h𝓕 : SheafOfModules.IsFiniteTypeOnSite 𝓕) :
    IsOpenSubspace B S hS (surjectivityLocus u) := by
  have := isFiniteTypeOnSite_cokernel_of_isFiniteTypeOnSite B S hS X.1 X.2 u h𝓕
  exact isOpenSubspace_openSubspaceOfPoints B S hS X.2 _
    (isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.2
      (surjectivityCokernel u)).isOpen_compl

/-- **A scheme over `X` factors through the surjectivity locus exactly when the pullback of the map
to it is surjective.** For `t : h_A ⟶ X` with `A` a scheme of the site: `t` factors through
`AlgebraicGeometry.Space.surjectivityLocus u` if and only if `t^*u` is an epimorphism.

The factorization is a containment of the points of `A` in the complement of `Supp(Coker u)`
(`AlgebraicGeometry.Space.exists_factor_openSubspaceOfPoints_iff`), i.e. the emptiness of the
inverse image of that support, which is the support of `t^*Coker u` by Stacks 07TZ part (3); a
module is zero exactly when its support is empty, and `t^*Coker u = Coker(t^*u)` because pullback
is a left adjoint. -/
theorem exists_factor_surjectivityLocus_iff [𝓖.IsQuasicoherentOnSite]
    [𝓕.IsQuasicoherentOnSite] (h𝓕 : SheafOfModules.IsFiniteTypeOnSite 𝓕)
    {A : BigFppfOver B S hS} (t : yoneda.obj A ⟶ X.1) :
    (∃ k : yoneda.obj A ⟶ (surjectivityLocus u).toFunctor, k ≫ (surjectivityLocus u).ι = t) ↔
      Epi ((modulePullback B S hS (ObjectProperty.homMk t :
        (⟨yoneda.obj A, isAlgebraicSpace_yoneda B S hS A⟩ : AlgebraicSpaces B S hS) ⟶ X)).map
          u) := by
  set g : (⟨yoneda.obj A, isAlgebraicSpace_yoneda B S hS A⟩ : AlgebraicSpaces B S hS) ⟶ X :=
    ObjectProperty.homMk t with hg
  have hft := isFiniteTypeOnSite_cokernel_of_isFiniteTypeOnSite B S hS X.1 X.2 u h𝓕
  have hqc : (surjectivityCokernel u).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_cokernel_unconditional B S hS X.1 X.2 u
  have hset : ∀ {α β : Type _} (f : α → β) (s : Set β), Set.range f ⊆ sᶜ ↔ f ⁻¹' s = ∅ :=
    fun f s => by rw [Set.range_subset_iff, Set.eq_empty_iff_forall_notMem]; rfl
  rw [surjectivityLocus, exists_factor_openSubspaceOfPoints_iff, hset]
  have hsupp := supportOfSheaf_modulePullback_eq B S hS g (surjectivityCokernel u) hqc hft
  have hpts : pointsMap B S hS (yoneda.obj A) t = pointsMap B S hS
      (⟨yoneda.obj A, isAlgebraicSpace_yoneda B S hS A⟩ : AlgebraicSpaces B S hS).1 g.hom := rfl
  rw [hpts, ← hsupp, supportOfSheaf_eq_empty_iff_isZero]
  have hadj := modulePullbackAdjunction B S hS g
  have := hadj.isLeftAdjoint
  have hpc : PreservesColimitsOfSize.{0, 0} (modulePullback B S hS g) :=
    hadj.leftAdjoint_preservesColimits
  rw [Preadditive.epi_iff_isZero_cokernel]
  exact ⟨fun h => h.of_iso (PreservesCokernel.iso (modulePullback B S hS g) u).symm,
    fun h => h.of_iso (PreservesCokernel.iso (modulePullback B S hS g) u)⟩

end AlgebraicGeometry.Space

end
