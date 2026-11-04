module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedPullbackLocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyUpToIsoInvariance

/-!
# Base change of a local property of morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, let `P` be a local property of morphisms
of `WAdm^count` which is stable under base change, and let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of locally countably indexed formal algebraic spaces over `S`. If `f` satisfies the
equivalent conditions of Stacks 0ANG, then so does the second projection `pr₂ : X ×_Y Z ⟶ Z`.

`P` being local is `TopologicalRing.PropertyIsLocalUpToIso P`: the three axioms of Situation
0CBA, with the completed corners `(A')^∧ = lim A'/IA'` and `(B')^∧ = lim B'/JB'` of the diagram
(87.21.2.1) taken up to isomorphism. `P` being stable under base change is
`TopologicalRing.IsStableUnderBaseChange P` (Situation 0GBC).

## Main results

* `hasProperty_pullback_snd_of_isLocalUpToIso_of_isLocallyCountablyIndexed`: if `f` satisfies
  condition (1) of Stacks 0ANG, then `X ×_Y Z` is locally countably indexed and `pr₂` satisfies
  all three conditions of Stacks 0ANG.
* `hasProperty_tfae_pullback_snd_of_isLocalUpToIso_of_isLocallyCountablyIndexed`: the same from
  any one of the conditions of Stacks 0ANG for `f`, together with their equivalence for `pr₂`.

## References

* [Stacks Project, Tag 0GBD](https://stacks.math.columbia.edu/tag/0GBD)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
* [Stacks Project, Tag 0GBC](https://stacks.math.columbia.edu/tag/0GBC)
* [Stacks Project, Tag 0GBB](https://stacks.math.columbia.edu/tag/0GBB)
* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `S` be a scheme. Let `P` be a local property of morphisms of `WAdm^count` which is
stable under base change. Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of locally countably
indexed formal algebraic spaces over `S`. If `f` satisfies the equivalent conditions of Stacks
0ANG, then so does `pr₂ : X ×_Y Z ⟶ Z`.

Here `hloc` says that `P` is local in the sense of Situation 0CBA, `hP` that it is stable under
base change (Situation 0GBC), and `hf` is condition (1) of Stacks 0ANG for `f`. The conclusion is
that `X ×_Y Z` is locally countably indexed (Stacks 0GBB, clause (1)) and that `pr₂` satisfies
all three conditions of Stacks 0ANG. -/
@[stacks 0GBD]
theorem hasProperty_pullback_snd_of_isLocalUpToIso_of_isLocallyCountablyIndexed
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hloc : TopologicalRing.PropertyIsLocalUpToIso.{u} P)
    (hP : TopologicalRing.IsStableUnderBaseChange.{u} P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (hZ : IsLocallyCountablyIndexed B S hS Z)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible P f) :
    IsLocallyCountablyIndexed B S hS (pullback f g) ∧
      HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsCountablyWeaklyAdmissible P
        (pullback.snd f g) ∧
      HasPropertyAfterTargetCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P
        (pullback.snd f g) ∧
      HasPropertyAfterSourceCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P
        (pullback.snd f g) :=
  hasProperty_pullback_snd_of_isLocallyCountablyIndexed B S hS P hP
    (hloc.propertyIsInvariantUnderSourceIso classIsWeaklyAdmissible_isCountablyWeaklyAdmissible
      classHasCountableNhdsZero_isCountablyWeaklyAdmissible)
    (hloc.propertyIsInvariantUnderTargetIsoOn classIsWeaklyAdmissible_isCountablyWeaklyAdmissible
      classHasCountableNhdsZero_isCountablyWeaklyAdmissible)
    f g hX hY hZ hf

/-- Let `S` be a scheme. Let `P` be a local property of morphisms of `WAdm^count` which is
stable under base change. Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of locally countably
indexed formal algebraic spaces over `S`. If `f` satisfies one, hence all, of the equivalent
conditions of Stacks 0ANG, then `X ×_Y Z` is locally countably indexed, the conditions of Stacks
0ANG are equivalent for `pr₂ : X ×_Y Z ⟶ Z`, and `pr₂` satisfies all three of them. -/
@[stacks 0GBD "the conditions of Stacks 0ANG for f taken as any one of them, and the \
conclusion including their equivalence for pr₂"]
theorem hasProperty_tfae_pullback_snd_of_isLocalUpToIso_of_isLocallyCountablyIndexed
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hloc : TopologicalRing.PropertyIsLocalUpToIso.{u} P)
    (hP : TopologicalRing.IsStableUnderBaseChange.{u} P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (hZ : IsLocallyCountablyIndexed B S hS Z)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS
        TopologicalRing.IsCountablyWeaklyAdmissible P f ∨
      HasPropertyAfterTargetCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P f ∨
      HasPropertyAfterSourceCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P f) :
    IsLocallyCountablyIndexed B S hS (pullback f g) ∧
      List.TFAE
        [ HasPropertyOnEveryAffineEtaleDiagram B S hS
            TopologicalRing.IsCountablyWeaklyAdmissible P (pullback.snd f g),
          HasPropertyAfterTargetCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P
            (pullback.snd f g),
          HasPropertyAfterSourceCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P
            (pullback.snd f g) ] ∧
      HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsCountablyWeaklyAdmissible P
        (pullback.snd f g) ∧
      HasPropertyAfterTargetCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P
        (pullback.snd f g) ∧
      HasPropertyAfterSourceCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P
        (pullback.snd f g) := by
  have hsrc : PropertyIsInvariantUnderSourceIso.{u}
      TopologicalRing.IsCountablyWeaklyAdmissible P := hloc.propertyIsInvariantUnderSourceIso
    classIsWeaklyAdmissible_isCountablyWeaklyAdmissible
    classHasCountableNhdsZero_isCountablyWeaklyAdmissible
  have htgt : PropertyIsInvariantUnderTargetIsoOn.{u}
      TopologicalRing.IsCountablyWeaklyAdmissible P := hloc.propertyIsInvariantUnderTargetIsoOn
    classIsWeaklyAdmissible_isCountablyWeaklyAdmissible
    classHasCountableNhdsZero_isCountablyWeaklyAdmissible
  have hf1 : HasPropertyOnEveryAffineEtaleDiagram B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible P f := by
    have tf := hasProperty_tfae_of_isLocallyCountablyIndexed B S hS P hP.isLocal hsrc htgt f hX hY
    rcases hf with h | h | h
    · exact h
    · exact (tf.out 1 2).2 h
    · exact (tf.out 1 3).2 h
  obtain ⟨hpb, h1, h2, h3⟩ :=
    hasProperty_pullback_snd_of_isLocalUpToIso_of_isLocallyCountablyIndexed B S hS P hloc hP f g
      hX hY hZ hf1
  exact ⟨hpb, hasProperty_tfae_of_isLocallyCountablyIndexed B S hS P hP.isLocal hsrc htgt
    (pullback.snd f g) hpb hZ, h1, h2, h3⟩

end AlgebraicGeometry.FormalSpace

end
