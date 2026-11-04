module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseAcyclic
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleStalkConservative
public import StacksFrontier.Homology.ExtendScalars.IndependentUniverses

/-!
# Left exactness of the inverse image of modules along a flat morphism

Let `g : X' ⟶ X` be a flat morphism of algebraic spaces over a scheme `S`.  The inverse image
`g^*` of `𝒪_X`-modules is always right exact, being a left adjoint; flatness of `g` makes it
left exact as well, so `g^*` preserves finite limits and in particular kernels.

The argument is stalkwise.  At a geometric point `x̄` of `X'` the stalk of `g^*` is the stalk at
the image point followed by extension of scalars along the induced homomorphism of
structure-sheaf stalks; the stalk functors are exact, that homomorphism is flat, and extension
of scalars along a flat ring map is exact, so each composite `g^*` followed by a stalk functor
is exact.  The geometric points of `X'` are a conservative family of points of its small étale
site, so exactness of a short complex and injectivity of a map may be read off those composites.

## Main results

* `AlgebraicGeometry.Space.flat_smallEtaleStalkPullbackRingMap`: the homomorphism
  `(𝒪_X)_{g ∘ x̄} ⟶ (𝒪_{X'})_{x̄}` of structure-sheaf stalks induced by a flat morphism is flat.
* `AlgebraicGeometry.Space.preservesFiniteLimits_modulePullback_of_isFlat_hom`: the inverse image
  of modules along a flat morphism of algebraic spaces preserves finite limits.
* `AlgebraicGeometry.Space.preservesKernel_modulePullback_of_isFlat`: the kernel clause of the
  previous result, as the preservation of the limit of a parallel pair `v, 0`.

## References

* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 03MK](https://stacks.math.columbia.edu/tag/03MK)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X' X : AlgebraicSpaces B S hS}

/-- **The homomorphism of structure-sheaf stalks of a flat morphism is flat.**  For a flat
morphism `g : X' ⟶ X` of algebraic spaces and a geometric point `x̄` of `X'`, the homomorphism
`(𝒪_X)_{g ∘ x̄} ⟶ (𝒪_{X'})_{x̄}` along which Stacks 05V5 extends scalars is flat.

It is conjugate, by the comparisons of Stacks 05VQ with the étale local rings, to the
homomorphism `𝒪_{X, g ∘ x̄} ⟶ 𝒪_{X', x̄}` of étale local rings, which is flat by Stacks 03MK. -/
theorem flat_smallEtaleStalkPullbackRingMap (g : X' ⟶ X) (hg : IsFlat B S hS g.hom)
    (x : GeometricPoint B S hS X'.1) :
    (smallEtaleStalkPullbackRingMap B S hS g x).Flat := by
  have hcomp : ((pointStalkRingEquiv B S hS X' x).toRingHom.comp
      (smallEtaleStalkPullbackRingMap B S hS g x)).Flat := by
    rw [pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap B S hS g x]
    exact RingHom.Flat.comp
      (RingHom.Flat.of_bijective
        (pointStalkRingEquiv B S hS X (geometricPointMap g.hom x)).bijective)
      (flat_etaleLocalRingMap B S hS X'.2 X.2 g.hom hg x)
  have heq : (pointStalkRingEquiv B S hS X' x).symm.toRingHom.comp
        ((pointStalkRingEquiv B S hS X' x).toRingHom.comp
          (smallEtaleStalkPullbackRingMap B S hS g x)) =
      smallEtaleStalkPullbackRingMap B S hS g x :=
    RingHom.ext fun z => (pointStalkRingEquiv B S hS X' x).symm_apply_apply _
  rw [← heq]
  exact RingHom.Flat.comp hcomp
    (RingHom.Flat.of_bijective (pointStalkRingEquiv B S hS X' x).symm.bijective)

/-- The stalk functor at a geometric point on `𝒪`-modules, valued in modules over the
`CommRingCat`-valued stalk of the structure sheaf.

This is `Stacks.sheafModuleFiberOfCommRing` at the point of the small étale site determined by
the geometric point; the declared source and target fix the spelling of the two categories, so
that the implicit category arguments of `CategoryTheory.Limits.PreservesFiniteLimits` match on
the nose in the composites below. -/
private def structureModuleStalkFunctor (Z : AlgebraicSpaces B S hS)
    (z : GeometricPoint B S hS Z.1) :
    Modules.{u, u} B S hS Z.1 Z.2 ⥤
      ModuleCat.{u} (Stacks.ringFiber (etaleSitePoint B S hS Z.1 z Z.2)
        (smallEtaleRingedTopos B S hS Z).O.obj) :=
  Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Z.1 z Z.2)
    (smallEtaleRingedTopos B S hS Z).O

/-- The stalk functor at a geometric point preserves zero morphisms. -/
private instance preservesZeroMorphisms_structureModuleStalkFunctor (Z : AlgebraicSpaces B S hS)
    (z : GeometricPoint B S hS Z.1) :
    (structureModuleStalkFunctor B S hS Z z).PreservesZeroMorphisms :=
  Stacks.preservesZeroMorphisms_sheafModuleFiberOfCommRing
    (smallEtaleRingedTopos B S hS Z).O (etaleSitePoint B S hS Z.1 z Z.2)

/-- **Stacks 05VQ as a natural isomorphism of functors.**  The stalk at a geometric point `x̄` of
`X'` of the inverse image of an `𝒪_X`-module along `g : X' ⟶ X` is the extension of scalars of
its stalk at `g ∘ x̄` along the induced homomorphism of structure-sheaf stalks, naturally in the
module.

This is `Stacks.Sheaves.StalkPullback.stalkFunctorIso` for the morphism of small étale ringed
topoi of Stacks 03G8 and the matched pair of points determined by `x̄`. -/
private def modulePullbackStalkFiberIso (g : X' ⟶ X) (x : GeometricPoint B S hS X'.1) :
    modulePullback B S hS g ⋙ structureModuleStalkFunctor B S hS X' x ≅
      structureModuleStalkFunctor B S hS X (geometricPointMap g.hom x) ⋙
        ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS g x) :=
  Stacks.Sheaves.StalkPullback.stalkFunctorIso (smallEtaleRingedToposModulesHom B S hS g)
    (etaleSitePoint B S hS X'.1 x X'.2)
    (etaleSitePoint B S hS X.1 (geometricPointMap g.hom x) X.2)
    (smallEtaleInverseImageFiberIso B S hS g x)

/-- The inverse image of modules along a flat morphism, followed by the stalk functor at a
geometric point of the source, preserves finite limits: it is the stalk functor at the image
point followed by extension of scalars along a flat homomorphism of stalk rings. -/
private theorem preservesFiniteLimits_modulePullback_comp_stalk (g : X' ⟶ X)
    (hg : IsFlat B S hS g.hom) (x : GeometricPoint B S hS X'.1) :
    PreservesFiniteLimits
      (modulePullback B S hS g ⋙ structureModuleStalkFunctor B S hS X' x) := by
  have hstalk : PreservesFiniteLimits
      (structureModuleStalkFunctor B S hS X (geometricPointMap g.hom x)) :=
    Stacks.preservesFiniteLimits_sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS X.1 (geometricPointMap g.hom x) X.2)
      (smallEtaleRingedTopos B S hS X).O
  have hext : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (smallEtaleStalkPullbackRingMap B S hS g x)) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat _
      (flat_smallEtaleStalkPullbackRingMap B S hS g hg x)
  have hcomp : PreservesFiniteLimits
      (structureModuleStalkFunctor B S hS X (geometricPointMap g.hom x) ⋙
        ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS g x)) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (modulePullbackStalkFiberIso B S hS g x).symm

/-- The inverse image of modules, followed by the stalk functor at a geometric point of the
source, preserves finite colimits: both the stalk functors and extension of scalars are right
exact, with no flatness hypothesis. -/
private theorem preservesFiniteColimits_modulePullback_comp_stalk (g : X' ⟶ X)
    (x : GeometricPoint B S hS X'.1) :
    PreservesFiniteColimits
      (modulePullback B S hS g ⋙ structureModuleStalkFunctor B S hS X' x) := by
  obtain ⟨-, hstalk⟩ := (exactFunctor_iff _).mp
    (Stacks.exactFunctor_sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS X.1 (geometricPointMap g.hom x) X.2)
      (smallEtaleRingedTopos B S hS X).O)
  have hstalk' : PreservesFiniteColimits
      (structureModuleStalkFunctor B S hS X (geometricPointMap g.hom x)) := hstalk
  have hext : PreservesFiniteColimits
      (ModuleCat.extendScalars.{u, u, u} (smallEtaleStalkPullbackRingMap B S hS g x)) :=
    ModuleCat.extendScalars_preservesFiniteColimits _
  have hcomp : PreservesFiniteColimits
      (structureModuleStalkFunctor B S hS X (geometricPointMap g.hom x) ⋙
        ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS g x)) :=
    comp_preservesFiniteColimits _ _
  exact preservesFiniteColimits_of_natIso (modulePullbackStalkFiberIso B S hS g x).symm

/-- A short complex of modules is exact once its image under every stalk functor at a geometric
point is exact. -/
private theorem shortComplex_exact_of_forall_exact_map_stalk
    (T : ShortComplex (Modules.{u, u} B S hS X'.1 X'.2))
    (h : ∀ x : GeometricPoint B S hS X'.1,
      (T.map (structureModuleStalkFunctor B S hS X' x)).Exact) : T.Exact := by
  refine (Stacks.shortComplex_exact_iff_forall_exact_map_sheafModuleFiberOfCommRing
    (smallEtaleRingedTopos B S hS X').O
    (isConservativeFamilyOfPoints_etaleSitePoint B S hS X'.1 X'.2)).2 ?_
  rintro ⟨Φ, hΦ⟩
  obtain ⟨x, rfl⟩ := (ObjectProperty.ofObj_iff _ Φ).1 hΦ
  exact h x

/-- **The inverse image of modules along a flat morphism of algebraic spaces is left exact.**
For a flat morphism `g : X' ⟶ X` of algebraic spaces over `S`, the pullback `g^*` of
`𝒪_X`-modules preserves finite limits.

A short exact sequence of `𝒪_X`-modules is carried by `g^*` to an exact sequence with
monomorphic first map, because that may be checked on the stalks at the geometric points of
`X'`, where `g^*` becomes a flat base change of an exact stalk functor. -/
theorem preservesFiniteLimits_modulePullback_of_isFlat_hom (g : X' ⟶ X)
    (hg : IsFlat B S hS g.hom) :
    PreservesFiniteLimits (modulePullback B S hS g) := by
  have hleft := (modulePullbackAdjunction B S hS g).isLeftAdjoint
  have hbiprod : PreservesBinaryBiproducts (modulePullback B S hS g) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have hadd : (modulePullback B S hS g).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  refine (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).2 fun σ hσ => ?_
  have hmono := hσ.mono_f
  refine ⟨?_, ?_⟩
  · refine shortComplex_exact_of_forall_exact_map_stalk B S hS _ fun x => ?_
    have h₁ := preservesFiniteLimits_modulePullback_comp_stalk B S hS g hg x
    have h₂ := preservesFiniteColimits_modulePullback_comp_stalk B S hS g x
    exact hσ.exact.map (modulePullback B S hS g ⋙ structureModuleStalkFunctor B S hS X' x)
  · let T : ShortComplex (Modules.{u, u} B S hS X'.1 X'.2) :=
      ShortComplex.mk (0 : (modulePullback B S hS g).obj σ.X₁ ⟶
          (modulePullback B S hS g).obj σ.X₁)
        ((modulePullback B S hS g).map σ.f) zero_comp
    refine (T.exact_iff_mono rfl).1 ?_
    refine shortComplex_exact_of_forall_exact_map_stalk B S hS _ fun x => ?_
    have h₁ := preservesFiniteLimits_modulePullback_comp_stalk B S hS g hg x
    have h₂ := preservesFiniteColimits_modulePullback_comp_stalk B S hS g x
    refine ((T.map (structureModuleStalkFunctor B S hS X' x)).exact_iff_mono
      ((structureModuleStalkFunctor B S hS X' x).map_zero _ _)).2 ?_
    exact inferInstanceAs (Mono
      ((modulePullback B S hS g ⋙ structureModuleStalkFunctor B S hS X' x).map σ.f))

/-- **The inverse image of modules along a flat morphism of algebraic spaces preserves
kernels.**  For a flat morphism `g : X' ⟶ X` of algebraic spaces and a map `v : M ⟶ N` of
`𝒪_X`-modules, `g^*` carries the kernel of `v` to the kernel of `g^* v`. -/
theorem preservesKernel_modulePullback_of_isFlat (g : X' ⟶ X) (hg : IsFlat B S hS g.hom)
    {M N : Modules.{u, u} B S hS X.1 X.2} (v : M ⟶ N) :
    PreservesLimit (parallelPair v 0) (modulePullback B S hS g) :=
  have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS g hg
  inferInstance

end AlgebraicGeometry.Space

end
