module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RelativeProjRepresents
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruplesBaseChange

/-!
# The morphism to `Proj` attached to a quadruple over a scheme point of an algebraic space

In Situation 0849 let `X` be an algebraic space over a scheme `S`, let `𝒜` be a quasi-coherent
graded `𝒪_X`-algebra and let `F` be the functor of quadruples of Stacks 084A.  Stacks 084B
asserts a canonical isomorphism `Proj_Z(g^*𝒜) = Z ×_X F` for a scheme `Z` over `X`, and proves
it in two steps: the functor `F'` of quadruples of `g^*𝒜` satisfies `F' = Z ×_X F` — "the
verification is omitted" — and `F'` is representable by `Proj_Z(g^*𝒜)` by Constructions
27.16.4, 27.16.5, 27.16.6 and Definition 27.16.7, that is by Tags 01NY and 01NZ.

The first step is
`AlgebraicGeometry.Space.GradedAlgebraPoints.F.bijective_toBaseChange` of
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjQuadruplesBaseChange.lean`.  This file is the
**second** step: it feeds the scheme-level representability, which this library proves
unconditionally as
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.relativeProjRepresentableByFunctorUnconditional`,
into the datum of Stacks 084A, and so attaches to every quadruple over a scheme point `f` of `X`
its morphism into the relative homogeneous spectrum `Proj` of the restricted algebra `f^*𝒜`.

## Main definitions

* `AlgebraicGeometry.Space.GradedAlgebraPoints.ofQuasicoherentFamily` builds the datum of
  Stacks 084A out of a family of *quasi-coherent* graded algebras on the scheme points of `X` —
  a `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra` at each point, which is
  Situation 01NN there and is the strength the restriction `f^*𝒜` of Situation 0849 has.  The
  datum `AlgebraicGeometry.Space.GradedAlgebraPoints` itself carries only a bare graded algebra,
  with quasi-coherence forgotten, so it alone cannot reach the relative homogeneous spectrum.
* `AlgebraicGeometry.Space.GradedAlgebraPoints.F.projMorphism` is the morphism
  `T → Proj_T(f^*𝒜)` attached to a point of the fibre of `F(T)` over a `T`-point `f` of `X`,
  for a test object whose scheme is quasi-compact.

## Main results

* `AlgebraicGeometry.Space.GradedAlgebraPoints.F.injective_projMorphism`: distinct points of the
  fibre get distinct morphisms, so the fibre of `F(T)` over `f` is a *subset* of the morphisms
  `T → Proj_T(f^*𝒜)`.  This is the representability of the source's `F'` transported to the
  datum of Stacks 084A.
* `AlgebraicGeometry.Space.GradedAlgebraPoints.F.projMorphism_eq_of_equivalent`: equivalent
  quadruples of possibly different degrees get the same morphism, which is the identification of
  Tag 01NW.
* `AlgebraicGeometry.Space.GradedAlgebraPoints.comap_ofQuasicoherentFamily` and
  `AlgebraicGeometry.Space.GradedAlgebraPoints.F.projMorphism_comap`: **compatibility with
  further base change.**  Restricting the quasi-coherent family along `g : X' ⟶ X` is reindexing
  it, and the morphism attached to a quadruple for the restricted family at a point `f` is the
  one attached to it for the original family at `f ≫ g` — the same morphism, into the same
  relative homogeneous spectrum.

## Implementation notes

**Why the fibre and not the functor.**  Stacks 084A is formalized in this library as the value
`AlgebraicGeometry.Space.GradedAlgebraPoints.F` of the functor on each test object rather than as
a functor, so `Z ×_X F` is available only object by object and the morphism below is attached to
a point of a fibre rather than to a point of a presheaf.  What is still missing for the functor is
recorded in `StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjQuadruples.lean`; the pullback of a
quadruple, which the implementation notes there record as unavailable, is in fact constructed at
the level of schemes, as `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.pullback` with its two
functor laws `...F.pullback_id` and `...F.pullback_comp` assembled into the presheaf
`...RelativeProjQcohSheaf.F.functor`.  What the space-level functor needs beyond that is the
comparison between the restrictions of `𝒜` along a scheme point and along its composite with a
morphism of test objects, which the datum of Stacks 084A does not carry; that comparison exists
on the small étale site, for arbitrary morphisms, as
`AlgebraicGeometry.Space.gradedAlgebraPullbackCompIso`, and what is missing is its transport
through the chart restriction to the schemes of the test objects.

**Quasi-compactness of the test object is not a weakening.**  The source's `F(T)` is the union
over `d ≥ 1` of the sets of quadruples of degree `d` exactly when `T` is quasi-compact, and is
the inverse limit of those unions over the quasi-compact opens of `T` otherwise; this library
follows that convention, with the union
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.functor` and its extension
`...RelativeProjQcohSheaf.F.limFunctor` identified on quasi-compact test schemes by
`...RelativeProjQcohSheaf.F.limEquiv`.  The datum of Stacks 084A is the union on every test
object, so the morphism below is attached on exactly the test objects where that union is the
source's `F(T)`.

**Injective and not bijective: the one input that is missing.**  The fibre of `F(T)` over `f`
consists of the quadruples whose recorded morphism to the base is the identity of the scheme of
`T`, so its image under the representation is the set of morphisms `T → Proj_T(f^*𝒜)` whose
composite with the structure morphism of the relative homogeneous spectrum is the identity, that
is the set of *sections*.  Identifying the image needs the representation to be a representation
over the base — the statement that the morphism attached to a quadruple, followed by the
structure morphism, is the morphism to the base that the quadruple records.  That statement is
the field `homEquiv_symm_incl_comp_toBase` of
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RepresentingProjData`, it is nowhere discharged
in this library, and it is the reason the result below is an injection rather than the bijection
onto the sections of `Proj_T(f^*𝒜) → T` that Stacks 084B's `Z ×_X F` asks for.  No weakened form
of that bijection is stated here.

## References

* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 01NW](https://stacks.math.columbia.edu/tag/01NW)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NZ](https://stacks.math.columbia.edu/tag/01NZ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace AlgebraicGeometry.Space

namespace GradedAlgebraPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The datum of Stacks 084A from a quasi-coherent family -/

/-- **The restriction datum of Stacks 084A built from a quasi-coherent family.**

A family assigning to every object `T` of the site and every `T`-point `f` of `X` a
quasi-coherent graded algebra on the scheme of `T` — Situation 01NN there, which is the strength
the restriction `f^*𝒜` of Situation 0849 has — gives the datum of Stacks 084A by forgetting
commutativity, the vanishing in negative degrees and quasi-coherence, which is
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra`.

The datum `AlgebraicGeometry.Space.GradedAlgebraPoints` records only the bare graded algebra, so
it does not by itself reach the relative homogeneous spectrum of Tag 01NQ; the family below is
what the construction of this file is stated for. -/
def ofQuasicoherentFamily
    (alg : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ X) →
      SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj T)) :
    GradedAlgebraPoints B S hS X where
  algebra T f := situationAlgebra (alg T f)

/-- The graded algebra of `ofQuasicoherentFamily alg` at a `T`-point `f` of `X` is
`situationAlgebra (alg T f)`. -/
@[simp] theorem ofQuasicoherentFamily_algebra
    (alg : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ X) →
      SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj T))
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    (ofQuasicoherentFamily alg).algebra T f = situationAlgebra (alg T f) :=
  rfl

/-- **Compatibility with further base change, for the datum.** Restricting along `g : X' ⟶ X`
the datum of a quasi-coherent family is the datum of the family reindexed along composition with
`g`, which is the source's `(f')^*(g^*𝒜) = (g ∘ f')^*𝒜`. -/
theorem comap_ofQuasicoherentFamily
    (alg : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ X) →
      SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj T))
    (g : X' ⟶ X) :
    (ofQuasicoherentFamily alg).comap g =
      ofQuasicoherentFamily (fun T f => alg T (f ≫ g)) :=
  rfl

/-! ### The morphism into the relative homogeneous spectrum -/

variable (alg : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ X) →
  SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj T))

/-- **The point of the inverse-limit functor of Tag 01NY attached to a point of the fibre.**

A point of the fibre of `F(T)` over a `T`-point `f` of `X` is a class of quadruples of the
restricted algebra `f^*𝒜` over the identity of the scheme of `T`, hence a point of the
scheme-level union of the display 01NX at that scheme, by
`AlgebraicGeometry.Space.GradedAlgebraPoints.F.toSchemeF`; on a quasi-compact test scheme that
union is the value of the functor the relative homogeneous spectrum represents, by
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.limEquiv`. -/
def F.limPoint (T : BigFppfOver B S hS)
    (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T)) (f : yoneda.obj T ⟶ X)
    (q : F.fibre (ofQuasicoherentFamily alg) T f) :
    (F.limFunctor (situationAlgebra (alg T f))).obj
      (op ((BigFppfOver.toScheme B S hS).obj T)) :=
  (F.limEquiv (situationAlgebra (alg T f)) ((BigFppfOver.toScheme B S hS).obj T) hT).symm
    (F.toSchemeF (ofQuasicoherentFamily alg) T f q)

/-- On a quasi-compact test scheme `T`, the map `F.limPoint alg T hT f` from the fibre of `F(T)`
over a `T`-point `f` of `X` to the points of the inverse-limit functor is injective. -/
theorem F.injective_limPoint (T : BigFppfOver B S hS)
    (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T)) (f : yoneda.obj T ⟶ X) :
    Function.Injective (F.limPoint alg T hT f) := fun _ _ h =>
  F.toSchemeF_injective (ofQuasicoherentFamily alg) T f
    ((F.limEquiv (situationAlgebra (alg T f))
      ((BigFppfOver.toScheme B S hS).obj T) hT).symm.injective h)

/-- **The morphism `T → Proj_T(f^*𝒜)` attached to a quadruple over a scheme point of `X`.**

This is the second step of the source's proof of Stacks 084B, on the datum of Stacks 084A: the
representability of the functor of quadruples of the restricted algebra by its relative
homogeneous spectrum, which this library proves unconditionally under Situation 01NN as
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.relativeProjRepresentableByFunctorUnconditional`
(Tags 01NY and 01NZ), applied at the point `f`. -/
def F.projMorphism (T : BigFppfOver B S hS)
    (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T)) (f : yoneda.obj T ⟶ X)
    (q : F.fibre (ofQuasicoherentFamily alg) T f) :
    (BigFppfOver.toScheme B S hS).obj T ⟶ (relativeProj (alg T f)).scheme :=
  (relativeProjRepresentableByFunctorUnconditional (alg T f)).homEquiv.symm
    (F.limPoint alg T hT f q)

/-- **Distinct points of the fibre get distinct morphisms.** The fibre of `F(T)` over a `T`-point
`f` of `X` is a subset of the morphisms `T → Proj_T(f^*𝒜)`.

The image is not identified here; the input that would identify it as the set of sections of
`Proj_T(f^*𝒜) → T` is named in the implementation notes of this file. -/
theorem F.injective_projMorphism (T : BigFppfOver B S hS)
    (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T)) (f : yoneda.obj T ⟶ X) :
    Function.Injective (F.projMorphism alg T hT f) := fun _ _ h =>
  F.injective_limPoint alg T hT f
    ((relativeProjRepresentableByFunctorUnconditional (alg T f)).homEquiv.symm.injective h)

/-- **The identification of Tag 01NW, for the attached morphism.** Equivalent quadruples of
possibly different degrees have the same morphism into the relative homogeneous spectrum, so the
morphism depends only on the point of the fibre. -/
theorem F.projMorphism_eq_of_equivalent (T : BigFppfOver B S hS)
    (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T)) (f : yoneda.obj T ⟶ X)
    {d d' : ℤ} (hd : 0 < d) (hd' : 0 < d')
    {P : (ofQuasicoherentFamily alg).Quadruples T f d}
    {Q : (ofQuasicoherentFamily alg).Quadruples T f d'}
    (h : Quadruple.Equivalent P Q) :
    F.projMorphism alg T hT f (Quot.mk _ ⟨⟨d, hd⟩, P⟩) =
      F.projMorphism alg T hT f (Quot.mk _ ⟨⟨d', hd'⟩, Q⟩) :=
  congrArg (F.projMorphism alg T hT f) (Quot.sound (UnionRel.equivalent h))

/-- **Compatibility with further base change, for the attached morphism.** For `g : X' ⟶ X` the
morphism attached to a point of the fibre for the restricted family at a `T`-point `f` of `X'` is
the morphism attached to it for the original family at the `T`-point `f ≫ g` of `X`: the same
morphism, into the same relative homogeneous spectrum `Proj_T((g ∘ f)^*𝒜)`.

Both sides are the same term, because the restricted family is the original family reindexed
along composition with `g`. -/
theorem F.projMorphism_comap (g : X' ⟶ X) (T : BigFppfOver B S hS)
    (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T)) (f : yoneda.obj T ⟶ X')
    (q : F.fibre (ofQuasicoherentFamily (fun T f => alg T (f ≫ g))) T f) :
    F.projMorphism (fun T f => alg T (f ≫ g)) T hT f q =
      F.projMorphism alg T hT (f ≫ g) q :=
  rfl

end GradedAlgebraPoints

end AlgebraicGeometry.Space

end
