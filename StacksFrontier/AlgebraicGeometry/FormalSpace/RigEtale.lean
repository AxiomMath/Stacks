module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmooth
public import StacksFrontier.RingTheory.Restricted.RigEtale
public import StacksFrontier.RingTheory.Rig.RigSmooth

/-!
# Rig-étale morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. A morphism `f : X ⟶ Y` of locally
Noetherian formal algebraic spaces over `S` is *rig-étale* (Stacks 0AQM) when for every
commutative square

```
U ⟶ V
↓     ↓
X ⟶ Y
```

with `U` and `V` affine formal algebraic spaces and `U ⟶ X`, `V ⟶ Y` representable by
algebraic spaces and étale, the morphism `U ⟶ V` comes from a rig-étale map of adic
Noetherian topological rings. Such a morphism is rig-smooth, because on each chart a
rig-étale map of adic Noetherian topological rings is rig-smooth.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsRigEtale`: **Stacks 0AQM**.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigSmooth_of_isRigEtale`: **Stacks 0GD0**, a rig-étale
  morphism of formal algebraic spaces is rig-smooth.

## Implementation notes

The predicate is the chart-by-chart condition of `AlgebraicGeometry.FormalSpace.IsRigSmooth`
(Tag 0GCP) with rig-smoothness of the induced map of rings replaced by rig-étaleness: the
quantification over presentations of the affine formal charts — adic Noetherian topological
rings `A`, `C`, quotient systems `D`, `E` presenting them over `S`, identifications
`U ≅ Spf E` and `V ≅ Spf D`, and continuous homomorphisms `g : D → E` whose formal spectrum
map is the given chart morphism — is literally the same, and the requirement on `g` is
`RingHom.IsRigEtale` of Tag 0GCV. As for Tag 0GCP, the locally Noetherian hypotheses on `X`
and `Y` are imposed by applications rather than built into the predicate, so that Tag 0GD0 is
obtained without them.

Tag 0GD0 reduces chartwise to Tag 0GB1 (`Rig.isRigSmooth_of_isRigEtale`), which compares the
two conditions for one adically finite type algebra. The rig-étaleness of `g` provides an
ideal of definition of the source together with the completeness and finite-type data
exhibiting the target as an object of the category of Tag 0AL4; that object is the one named
by `Rig.adicFiniteTypeAlgebra`, so Tag 0GB1 applies to it directly.

## References

* [Stacks Project, Tag 0AQM](https://stacks.math.columbia.edu/tag/0AQM)
* [Stacks Project, Tag 0GD0](https://stacks.math.columbia.edu/tag/0GD0)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FormalSpace

universe u v

/-- **Stacks 0AQM.** A morphism of formal algebraic spaces over `S` is *rig-étale* when every
morphism between affine, representable, étale charts of its source and target is induced by a
rig-étale continuous homomorphism of adic Noetherian topological rings. -/
@[stacks 0AQM]
abbrev IsRigEtale (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
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
            RingHom.IsRigEtale g.toRingHom

/-- A rig-étale continuous homomorphism of Noetherian adic topological rings makes its target,
viewed over some ideal of definition of its source, a rig-smooth adically finite type
algebra. -/
private theorem exists_isRigSmooth_adicFiniteTypeAlgebra_of_isRigEtale
    {A : Type u} {C : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [IsNoetherianRing A]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
      [IsNoetherianRing C]
    (φ : A →+* C) (hφ : RingHom.IsRigEtale φ) :
    ∃ (hft : Rig.FiniteTypeAdicAlgebraForEveryIdeal φ) (I : Ideal A)
      (hI : TopologicalRing.IsIdealOfDefinition I),
      Rig.IsRigSmooth (Rig.adicFiniteTypeAlgebra φ hft I hI) := by
  obtain ⟨hft, I, hI, hc, hfin, hre⟩ := hφ
  refine ⟨hft, I, hI, ?_⟩
  let _ : Algebra A C := φ.toAlgebra
  have _ : Algebra.FiniteType (A ⧸ I) (C ⧸ I.map (algebraMap A C)) := hfin
  exact Rig.isRigSmooth_of_isRigEtale (Rig.AdicFiniteTypeAlgebra.of (I := I) C hc) hre

/-- **Stacks 0GD0.** A rig-étale morphism of formal algebraic spaces is rig-smooth. -/
@[stacks 0GD0]
theorem isRigSmooth_of_isRigEtale (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hf : IsRigEtale B S hS f) :
    IsRigSmooth B S hS f := by
  intro U V hU hV a b t ha hb hae hbe hcomm A C _ _ _ _ _ _ _ _ _ _ hAdicA hAdicC hwA D E eU eV g hg
  exact exists_isRigSmooth_adicFiniteTypeAlgebra_of_isRigEtale g.toRingHom
    (hf U V hU hV a b t ha hb hae hbe hcomm A C hAdicA hAdicC hwA D E eU eV g hg)

end AlgebraicGeometry.FormalSpace

end
