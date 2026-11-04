module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.RingTheory.PseudoCoherentMap.Defs

/-!
# Perfect morphisms of schemes

A morphism of schemes is *perfect* when it is locally of finite type and the map on sections
over every compatible pair of affine opens is a perfect ring map (Stacks 0687, through condition
(2) of Stacks 0686).

## Main definitions

* `AlgebraicGeometry.Perfect`: a morphism of schemes is perfect if it is locally of finite type
  and the map on sections over every compatible pair of affine opens is a perfect ring map.

## Implementation notes

Perfectness is a class extending `AlgebraicGeometry.LocallyOfFiniteType`, in keeping with
Mathlib's treatment of properties of morphisms of schemes, so a perfect morphism can be used
wherever a morphism locally of finite type is required. The shape of the binders follows
`AlgebraicGeometry.PseudoCoherent`, which is Stacks 067Z and is the companion notion.

Stacks 0687 defines perfectness by the equivalent conditions of Stacks 0686, of which condition
(2) — the condition on *every* compatible pair of affine opens — is the defining field here.
Condition (1), the existence of affine open coverings with the same property, and hence the
equivalence itself, is not covered: unlike `RingHom.PseudoCoherent` there is no
`RingHom.PropertyIsLocal` instance for perfectness of a ring map in this library, because the
notion carries a derived tensor product as data (see below) and the locality arguments of Stacks
0680 have not been run for it.

`RingHom.IsPerfectRingMap` takes the derived tensor product it reads Tor amplitude off as an
argument rather than using a canonical one, because the library has no canonical derived tensor
product of modules; `StacksDraft.TorAmplitude.CertifiedDerivedTensoring` bundles the bifunctor,
the comparison with termwise tensoring and the `IsLeftDerivedFunctor` certificate. The defining
field below therefore quantifies over every such certificate on `Γ(S, V)`. That quantification
is not vacuous: `StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring` produces one for
every commutative ring, and any two of them compute the same Tor amplitude, so the condition
does not depend on the choice.

The derived categories of modules come from `HasDerivedCategory.standard`, which
`StacksFrontier/Homology/TorAmplitude/Defs.lean` makes a local instance only, so it has to be
re-declared here.

## References

* [The Stacks Project, Lemma 36.61.1 (0686)](https://stacks.math.columbia.edu/tag/0686)
* [The Stacks Project, Definition 36.61.2 (0687)](https://stacks.math.columbia.edu/tag/0687)
* [The Stacks Project, Definition 15.83.1 (067H)](https://stacks.math.columbia.edu/tag/067H)
-/

@[expose] public noncomputable section

open CategoryTheory StacksDraft.TorAmplitude

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

universe u

/-- **Stacks 0687.** A morphism of schemes `f : X ⟶ S` is perfect if it is locally of finite
type and, for every affine open `U ⊆ X` and every affine open `V ⊆ S` with `U ⊆ f ⁻¹ᵁ V`, the
induced map on sections `Γ(S, V) ⟶ Γ(X, U)` is a perfect ring map, with respect to every
certified derived tensor product on `Γ(S, V)`.

This is condition (2) of Stacks 0686, which is the condition Stacks 0687 defines perfectness by. -/
@[mk_iff, stacks 0687]
public class Perfect {X S : Scheme.{u}} (f : X ⟶ S) : Prop extends LocallyOfFiniteType f where
  /-- The map on sections induced by any compatible pair of affine opens is a perfect ring
  map. -/
  perfect_appLE (f) :
    ∀ (U : X.Opens) (_ : IsAffineOpen U) (V : S.Opens) (_ : IsAffineOpen V)
      (hUV : U ≤ f ⁻¹ᵁ V),
        letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
        ∀ D : CertifiedDerivedTensoring.{u, u} Γ(S, V),
          RingHom.IsPerfectRingMap Γ(S, V) Γ(X, U) D.tensor D.comparison D.isLeftDerived

end AlgebraicGeometry

end
