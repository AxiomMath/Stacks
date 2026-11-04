module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.RingTheory.Rig.RigSmooth

/-!
# Rig-smooth morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. A morphism `f : X ⟶ Y` of locally
Noetherian formal algebraic spaces over `S` is *rig-smooth* (Stacks 0GCP) when for every
commutative square

```
U ⟶ V
↓     ↓
X ⟶ Y
```

with `U` and `V` affine formal algebraic spaces and `U ⟶ X`, `V ⟶ Y` representable by
algebraic spaces and étale, the morphism `U ⟶ V` comes from a rig-smooth map of adic
Noetherian topological rings.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsRigSmooth`: **Stacks 0GCP**.

## Implementation notes

An affine formal algebraic space is presented by a formal spectrum, so "the morphism `U ⟶ V`
corresponds to a rig-smooth map of rings" is rendered by quantifying over presentations: over
adic Noetherian topological rings `A`, `C`, over quotient systems `D`, `E` presenting them over
`S`, over identifications `U ≅ Spf E` and `V ≅ Spf D`, and over continuous homomorphisms
`g : D → E` whose formal spectrum map is the given chart morphism. Every such `g` is then
required to be rig-smooth in the sense of Tag 0GCJ: it is adic of topologically finite type —
condition (6) of Tag 0GBW — and makes its target rig-smooth over an ideal of definition of its
source. The existential form is used, so that a witnessing ideal of definition is immediately
available; by Tag 0GCI the choice of that ideal is immaterial.

The locally Noetherian hypotheses on `X` and `Y` are imposed by applications rather than built
into the predicate, which lets it be used before those hypotheses are available; the
representability and étaleness conditions on the charts use the notions of
`StacksFrontier.AlgebraicGeometry.Spaces.LargeValued`, since the sheaves carrying formal algebraic
spaces take values in `Type (u + 1)`. Being an `abbrev`, the predicate hands its
universal-quantifier interface directly to consumers with no unfolding lemma.

## References

* [Stacks Project, Tag 0GCP](https://stacks.math.columbia.edu/tag/0GCP)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.FormalSpace

universe u

/-- **Stacks 0GCP.** A morphism of formal algebraic spaces over `S` is *rig-smooth* when every
morphism between affine, representable, étale charts of its source and target is induced by a
rig-smooth continuous homomorphism of adic Noetherian topological rings. -/
@[stacks 0GCP]
abbrev IsRigSmooth (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
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
            ∃ (hft : Rig.FiniteTypeAdicAlgebraForEveryIdeal g.toRingHom) (I : Ideal A)
              (hI : TopologicalRing.IsIdealOfDefinition I),
              Rig.IsRigSmooth (Rig.adicFiniteTypeAlgebra g.toRingHom hft I hI)

/-- **Stacks 0GCQ, conditions (1) and (2).** A morphism of formal algebraic spaces over `S` is
rig-smooth exactly when rig-smoothness as a property of arrows of `WAdm^{Noeth}` holds on every
affine étale diagram over it: the two conditions are the same, which is what Definition 0GCP
says. -/
@[stacks 0GCQ "conditions (1) and (2)"]
theorem isRigSmooth_iff_hasPropertyOnEveryAffineEtaleDiagram (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    IsRigSmooth B S hS f ↔
      HasPropertyOnEveryAffineEtaleDiagram B S hS
        (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
        (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
          [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
          RingHom.IsRigSmoothArrow φ) f := by
  constructor
  · intro h U V a b t hU hV ⟨ha, haet⟩ ⟨hb, hbet⟩ hcomm A R _ _ _ _ _ _ _ _
      ⟨hAadic, hAnoeth⟩ ⟨hRadic, hRnoeth⟩ hA D E eU eV g hg _ _ _ _
    exact ⟨g.continuous,
      h U V hU hV a b t ha hb haet hbet hcomm A R hAadic hRadic hA D E eU eV g hg⟩
  · intro h U V hU hV a b t ha hb haet hbet hcomm A R _ _ _ _ _ _ _ _ _ _
      hAadic hRadic hA D E eU eV g hg
    have hP := h U V a b t hU hV ⟨ha, haet⟩ ⟨hb, hbet⟩ hcomm A R
      ⟨hAadic, inferInstance⟩ ⟨hRadic, inferInstance⟩ hA D E eU eV g hg
    exact hP.2

end AlgebraicGeometry.FormalSpace

end
