module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.ProjectiveSchemes
public import StacksFrontier.AlgebraicGeometry.RelativeProjChain.ComplementaryLinearEmbeddings
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoproductQuasiProjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Every base has disjoint projective embeddings

`AlgebraicGeometry.HasDisjointProjectiveEmbeddings S` of
`StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoproductQuasiProjective` asks that any two
relative projective spaces over `S` embed as closed subschemes of a single relative projective
space over `S` *with disjoint images*. This file proves it for every base scheme, so the two
coproduct results of that file hold with no hypothesis on `S`.

The witnesses are the two complementary linear embeddings of the integral models, which
`StacksFrontier.AlgebraicGeometry.RelativeProjChain.ComplementaryLinearEmbeddings` provides, base
changed along `S ⟶ Spec ℤ`; disjointness survives the base change because the image of a base
changed morphism lies in the inverse image, under the projection to the integral model, of the
image of the original.

## Main results

* `AlgebraicGeometry.disjoint_range_base_of_comp_eq`: disjointness of images transports along a
  commuting square, which is how disjointness is carried from the integral models to `S`.
* `AlgebraicGeometry.exists_disjoint_isClosedImmersion_projectiveSpaceOver`: the two
  complementary closed immersions `ℙⁿ_S, ℙᵐ_S ↪ ℙ^{n + m + 1}_S` over `S`, with disjoint
  images.
* `AlgebraicGeometry.hasDisjointProjectiveEmbeddings`: **every base scheme has disjoint
  projective embeddings.**
* `AlgebraicGeometry.isProjectiveMorphism_coprodDesc'` and
  `AlgebraicGeometry.isHQuasiProjective_coprodDesc'`: the disjoint union of two schemes
  H-projective, respectively H-quasi-projective, over `S` is H-projective, respectively
  H-quasi-projective, over `S`, with **no hypothesis on `S`**.

## Implementation notes

The two primed results are `AlgebraicGeometry.isProjectiveMorphism_coprodDesc` and
`AlgebraicGeometry.isHQuasiProjective_coprodDesc` with their hypothesis
`AlgebraicGeometry.HasDisjointProjectiveEmbeddings S` discharged by
`AlgebraicGeometry.hasDisjointProjectiveEmbeddings`.

## References

* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RelativeProjChain

universe u

namespace AlgebraicGeometry

/-- **Disjointness of images transports along a commuting square.** -/
theorem disjoint_range_base_of_comp_eq {XA XB Y ZA ZB W : Scheme.{u}}
    {ma : XA ⟶ Y} {mb : XB ⟶ Y} {sA : XA ⟶ ZA} {sB : XB ⟶ ZB} {sY : Y ⟶ W}
    {i : ZA ⟶ W} {j : ZB ⟶ W} (ha : ma ≫ sY = sA ≫ i) (hb : mb ≫ sY = sB ≫ j)
    (hij : Disjoint (Set.range i.base) (Set.range j.base)) :
    Disjoint (Set.range ma.base) (Set.range mb.base) := by
  have key : ∀ {X Z : Scheme.{u}} {m : X ⟶ Y} {s : X ⟶ Z} {t : Z ⟶ W},
      m ≫ sY = s ≫ t → ∀ p, sY (m p) = t (s p) := fun h p => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]
  rw [Set.disjoint_left] at hij ⊢
  rintro y ⟨pa, rfl⟩ ⟨pb, hpb⟩
  exact hij ⟨sA pa, (key ha pa).symm⟩ ⟨sB pb, by rw [← key hb pb, hpb]⟩

/-- Base changing a closed immersion along `S ⟶ Spec ℤ` gives a closed immersion over `S`
that commutes with both projections. -/
private theorem isClosedImmersion_pullbackMap_terminal {S A B : Scheme.{u}} {i : A ⟶ B}
    (hi : IsClosedImmersion i) :
    ∃ f : pullback (terminal.from S) (terminal.from A) ⟶ pullback (terminal.from S)
        (terminal.from B),
      IsClosedImmersion f ∧ f ≫ pullback.fst _ _ = pullback.fst _ _ ∧
        f ≫ pullback.snd _ _ = pullback.snd _ _ ≫ i := by
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    ⟨fun a c ha hc => @IsClosedImmersion.comp _ _ _ a c ha hc⟩
  exact ⟨pullback.map _ _ _ _ (𝟙 S) i (𝟙 _) (by simp) (by simp),
    MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance hi
      (Category.id_comp _).symm (by simp),
    (pullback.lift_fst _ _ _).trans (Category.comp_id _), pullback.lift_snd _ _ _⟩

/-- **The two complementary linear embeddings over a base `S`.** -/
theorem exists_disjoint_isClosedImmersion_projectiveSpaceOver (S : Scheme.{u}) (n m : ℕ) :
    ∃ (a : projectiveSpaceOver n S ⟶ projectiveSpaceOver (n + m + 1) S)
      (b : projectiveSpaceOver m S ⟶ projectiveSpaceOver (n + m + 1) S),
      IsClosedImmersion a ∧ IsClosedImmersion b ∧
        a ≫ (projectiveSpaceOver (n + m + 1) S ↘ S) = (projectiveSpaceOver n S ↘ S) ∧
        b ≫ (projectiveSpaceOver (n + m + 1) S ↘ S) = (projectiveSpaceOver m S ↘ S) ∧
        Disjoint (Set.range a.base) (Set.range b.base) := by
  obtain ⟨i, j, hi, hj, hij⟩ :=
    exists_disjoint_isClosedImmersion_projectiveSpaceAtUniverse.{u} n m
  obtain ⟨a, ha, haS, haY⟩ := isClosedImmersion_pullbackMap_terminal (S := S) hi
  obtain ⟨b, hb, hbS, hbY⟩ := isClosedImmersion_pullbackMap_terminal (S := S) hj
  exact ⟨a, b, ha, hb, haS, hbS, disjoint_range_base_of_comp_eq (sY := pullback.snd _ _)
    haY hbY hij⟩

/-- **Every base scheme has disjoint projective embeddings**: any two relative projective spaces
over `S` embed as closed subschemes of a single relative projective space over `S` with disjoint
images. -/
theorem hasDisjointProjectiveEmbeddings (S : Scheme.{u}) :
    HasDisjointProjectiveEmbeddings S := by
  intro n m
  obtain ⟨a, b, ha, hb, haS, hbS, hab⟩ :=
    exists_disjoint_isClosedImmersion_projectiveSpaceOver S n m
  exact ⟨n + m + 1, a, b, ha, hb, haS, hbS, hab⟩

/-- **The disjoint union of two H-projective schemes over `S` is H-projective over `S`**, with no
hypothesis on `S`. -/
theorem isProjectiveMorphism_coprodDesc' {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (hf : IsProjectiveMorphism f) (hg : IsProjectiveMorphism g) :
    IsProjectiveMorphism (coprod.desc f g) :=
  isProjectiveMorphism_coprodDesc (hasDisjointProjectiveEmbeddings S) hf hg

/-- **The disjoint union of two H-quasi-projective schemes over `S` is H-quasi-projective over
`S`**, with no hypothesis on `S`. -/
@[ega "II 5.3.6" "special case"]
theorem isHQuasiProjective_coprodDesc' {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (hf : IsHQuasiProjective f) (hg : IsHQuasiProjective g) :
    IsHQuasiProjective (coprod.desc f g) :=
  isHQuasiProjective_coprodDesc (hasDisjointProjectiveEmbeddings S) hf hg

end AlgebraicGeometry

end
