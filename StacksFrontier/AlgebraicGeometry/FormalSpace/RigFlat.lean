module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.RingTheory.Rig.Flat

/-!
# Rig-flat morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. A morphism `f : X ⟶ Y` of locally
Noetherian formal algebraic spaces over `S` is *rig-flat* (Stacks 0GGX) when for every
commutative square

```
U ⟶ V
↓     ↓
X ⟶ Y
```

with `U` and `V` affine formal algebraic spaces and `U ⟶ X`, `V ⟶ Y` representable by
algebraic spaces and étale, the morphism `U ⟶ V` comes from a rig-flat map of adic Noetherian
topological rings.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsRigFlat`: **Stacks 0GGX**.

## Implementation notes

An affine formal algebraic space is presented by a formal spectrum, so "the morphism `U ⟶ V`
corresponds to a rig-flat map of rings" is rendered by quantifying over presentations: over adic
Noetherian topological rings `A`, `C`, over quotient systems `D`, `E` presenting them over `S`,
over identifications `U ≅ Spf E` and `V ≅ Spf D`, and over continuous homomorphisms `g : D → E`
whose formal spectrum map is the given chart morphism. Every such `g` is then required to be
rig-flat in the sense of Tag 0GGP.

The locally Noetherian hypotheses on `X` and `Y` are imposed by applications rather than built
into the predicate, which lets it be used before those hypotheses are available; the
representability and étaleness conditions on the charts use the notions of
`StacksFrontier.AlgebraicGeometry.Spaces.LargeValued`, since the sheaves carrying formal algebraic
spaces take values in `Type (u + 1)`. Being an `abbrev`, the predicate hands its
universal-quantifier interface directly to consumers with no unfolding lemma.

## References

* [Stacks Project, Tag 0GGX](https://stacks.math.columbia.edu/tag/0GGX)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.FormalSpace

universe u

/-- **Stacks 0GGX.** A morphism of formal algebraic spaces over `S` is *rig-flat* when every
morphism between affine, representable, étale charts of its source and target is induced by a
rig-flat continuous homomorphism of adic Noetherian topological rings. -/
@[stacks 0GGX]
abbrev IsRigFlat (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (U V : FppfSheaf B S hS)
    (_hU : IsAffineFormalAlgebraicSpace B S hS U)
    (_hV : IsAffineFormalAlgebraicSpace B S hS V)
    (a : U ⟶ X) (b : V ⟶ Y) (t : U ⟶ V)
    (ha : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS a.hom)
    (hb : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS b.hom),
    Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) a.hom ha →
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) b.hom hb →
      a ≫ f = t ≫ b → ∀ (A C : Type u)
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
          [IsNoetherianRing A]
        [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
          [IsNoetherianRing C],
        TopologicalRing.IsAdic A → TopologicalRing.IsAdic C →
        ∀ (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
          (E : QuotientSystem B S hS C) (eU : U ≅ formalSpectrum E)
          (eV : V ≅ formalSpectrum D) (g : ContinuousHom D E),
          t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv →
            Rig.RingHom.IsRigFlat g.toRingHom

end AlgebraicGeometry.FormalSpace

end
