module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphismComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType

/-!
# Composition of quasi-separatedness for morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, and let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of formal algebraic spaces over `S`. The quasi-separatedness axiom of Stacks 0ARN
asks that the relative diagonal be quasi-compact, and this file proves that axiom stable
under composition for the quasi-compactness condition
`AlgebraicGeometry.Space.IsQuasiCompactULift` that
`AlgebraicGeometry.FormalSpace.IsQuasiSeparatedMorphism` is built from.

The relative diagonal of `f ≫ g` factors as the relative diagonal of `f` followed by the
comparison `X ×_Y X ⟶ X ×_Z X` of the two relative self-products, and that comparison is a
base change of the relative diagonal of `g`. The factorisation reduces the statement to
stability of the quasi-compactness condition under composition; the objects occurring in it
are the relative self-products `X ×_Y X` and `X ×_Z X`, which are only formal algebraic
spaces, so what is needed is a composition law carrying no hypothesis that its objects are
algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompactULift_comp_of_presheaf`: **Stacks 03HG** for
  morphisms of presheaves on the big fppf site of `S`, with no hypothesis that any of the
  three objects is an algebraic space.
* `AlgebraicGeometry.FormalSpace.isQuasiSeparatedMorphism_comp`: **Stacks 0ARR** for the
  quasi-separatedness axiom of Stacks 0ARN, read for
  `AlgebraicGeometry.FormalSpace.IsQuasiSeparatedMorphism`: a composite of morphisms with
  quasi-compact relative diagonal again has quasi-compact relative diagonal.

## Implementation notes

`AlgebraicGeometry.Space.isQuasiCompactULift_comp` already records Stacks 03HG, but it asks
its middle and final objects to be algebraic spaces, because it applies the quasi-compactness
of the first morphism at the fibre product `Z ×_K G` of the test object with the second
morphism, and the definition of the condition only admits algebraic spaces as test objects.
That hypothesis is unavailable here: the objects are relative self-products of formal
algebraic spaces.

It is also unnecessary. The fibre product `Z ×_K G` is known to be quasi-compact *as a space*,
which by Stacks 03E3 means precisely that it receives a surjective étale morphism `c` from a
universe-lifted Yoneda presheaf on a quasi-compact scheme of the site — and a universe-lifted
Yoneda presheaf *is* an algebraic space. So the quasi-compactness of the first morphism is
applied at that chart instead, and the resulting fibre product maps to the one wanted by a
base change of `c`, hence by a surjective étale morphism. Composing the two charts exhibits
the quasi-compact étale surjective chart that Stacks 03E3 asks for. This descent step is
`AlgebraicGeometry.Space.isQuasiCompactSpaceULift_pullback_of_chart`; it is the same device
by which `AlgebraicGeometry.Space.isQuasiCompactULift_of_forall_pullback_fst` manages, in
`StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType`, to reduce the condition to
represented test objects with no algebraic-space hypothesis either.

The auxiliary facts about the property of being étale, respectively surjective, after every
represented base change — that it holds for identities, is stable under composition and is
stable under base change — are private to
`StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType` and so are re-derived here;
each is one application of a Mathlib lemma about `CategoryTheory.MorphismProperty.relative`.
The stability of the inverse-image properties under composition is kept local to the proofs
that need it rather than declared as an instance, so that this module adds no instance.

The factorisation of the relative diagonal of a composite is
`AlgebraicGeometry.FormalSpace.diagonal_comp_eq_mapDesc`, taken from
`StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphismComposition`. It is pure category
theory, valid in any category with fibre products.

## References

* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03HG](https://stacks.math.columbia.edu/tag/03HG)
* [Stacks Project, Tag 0ARN](https://stacks.math.columbia.edu/tag/0ARN)
* [Stacks Project, Tag 0ARQ](https://stacks.math.columbia.edu/tag/0ARQ)
* [Stacks Project, Tag 0ARR](https://stacks.math.columbia.edu/tag/0ARR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Étaleness after every represented base change, for an étale morphism out of a
universe-lifted Yoneda presheaf: take the identity for the étale chart of the source. -/
private theorem relative_etale_of_isEtaleULift {U : BigFppfOver B S hS}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} {m : (uliftYoneda.{w}).obj U ⟶ F}
    (hm : IsEtaleULift.{w} B S hS m) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) m := by
  simpa using hm U (𝟙 _) (relative_id_etale B S hS U)

/-- Stability under composition of a property of schemes is inherited by the property of the
morphism of schemes underlying a morphism of the big fppf site of `S`. -/
private theorem inverseImage_comp (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
  MorphismProperty.IsStableUnderComposition.inverseImage _

/-- **Stacks 03E3** descends along a surjective étale chart, in the form needed for a fibre
product: let `f : F ⟶ G` and `g : P ⟶ G` be morphisms of presheaves on the big fppf site of
`S` and let `c` be a surjective étale morphism onto `P` from a universe-lifted Yoneda
presheaf. If the fibre product of `F` with that chart over `G` is quasi-compact as a space,
then so is `P ×_G F`.

The comparison `(c ≫ g) ×_G F ⟶ P ×_G F` is a base change of `c`, so it is again surjective
and étale after every represented base change; composing it with a quasi-compact surjective
étale chart of its source — which exists by hypothesis — gives one of `P ×_G F`. No hypothesis
that any of the presheaves involved is an algebraic space is needed. -/
theorem isQuasiCompactSpaceULift_pullback_of_chart
    {F G P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} {U : BigFppfOver B S hS}
    (f : F ⟶ G) (g : P ⟶ G) (c : (uliftYoneda.{w}).obj U ⟶ P)
    (hcSurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) c)
    (hcEtale : IsEtaleULift.{w} B S hS c)
    (h : IsQuasiCompactSpaceULift.{w} B S hS (pullback (c ≫ g) f)) :
    IsQuasiCompactSpaceULift.{w} B S hS (pullback g f) := by
  have hinstE := inverseImage_comp B S hS (@AlgebraicGeometry.Etale.{u})
  have hinstS := inverseImage_comp B S hS (@AlgebraicGeometry.Surjective.{u})
  have hcE := relative_etale_of_isEtaleULift B S hS hcEtale
  let κ : pullback (c ≫ g) f ⟶ pullback g f :=
    pullback.lift (pullback.fst (c ≫ g) f ≫ c) (pullback.snd (c ≫ g) f)
      (by rw [Category.assoc]; exact pullback.condition)
  have hbig : IsPullback (pullback.fst (c ≫ g) f) (κ ≫ pullback.snd g f) (c ≫ g) f := by
    simpa only [κ, pullback.lift_snd] using IsPullback.of_hasPullback (c ≫ g) f
  have hsquare : IsPullback κ (pullback.fst (c ≫ g) f) (pullback.fst g f) c :=
    (hbig.of_bot (by dsimp only [κ]; rw [pullback.lift_fst])
      (IsPullback.of_hasPullback g f)).flip
  have hκSurj := AlgebraicGeometry.Space.relative_of_isPullback B S hS hsquare hcSurj
  have hκEtale := AlgebraicGeometry.Space.relative_of_isPullback B S hS hsquare hcE
  obtain ⟨V, γ, hVc, hγSurj, hγEtale⟩ := h
  refine ⟨V, γ ≫ κ, hVc, relative_comp B S hS hγSurj hκSurj, ?_⟩
  intro U' φ hφ
  have h1 := hγEtale U' φ hφ
  have h2 := relative_comp B S hS h1 hκEtale
  simpa only [Category.assoc] using h2

/-- **Stacks 03HG** for morphisms of presheaves on the big fppf site of `S` with values in
`Type (max w u)`: a composition of quasi-compact morphisms is quasi-compact, with no
hypothesis that any of the three objects is an algebraic space.

This is `AlgebraicGeometry.Space.isQuasiCompactULift_comp` with its two algebraic-space
hypotheses removed, which is what makes it applicable to morphisms of formal algebraic
spaces. Given a quasi-compact algebraic space `Z` over the final object, the fibre product
`Z ×_K G` is quasi-compact as a space, hence receives a surjective étale chart from a
universe-lifted Yoneda presheaf on a quasi-compact scheme of the site; that chart *is* an
algebraic space, so the quasi-compactness of the first morphism may be applied at it, and
`AlgebraicGeometry.Space.isQuasiCompactSpaceULift_pullback_of_chart` descends the conclusion
back along the chart. -/
theorem isQuasiCompactULift_comp_of_presheaf
    {F G K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (a : F ⟶ G) (b : G ⟶ K)
    (ha : IsQuasiCompactULift.{w} B S hS a) (hb : IsQuasiCompactULift.{w} B S hS b) :
    IsQuasiCompactULift.{w} B S hS (a ≫ b) := by
  intro Z hZalg hZqc k
  obtain ⟨U, c, hUc, hcSurj, hcEtale⟩ := hb Z hZalg hZqc k
  have hUqc : IsQuasiCompactSpaceULift.{w} B S hS ((uliftYoneda.{w}).obj U) :=
    ⟨U, 𝟙 _, hUc, Space.relative_id_surjective B S hS U, fun _ φ hφ => by simpa using hφ⟩
  have hstep : IsQuasiCompactSpaceULift.{w} B S hS (pullback (c ≫ pullback.snd k b) a) :=
    ha ((uliftYoneda.{w}).obj U) (isAlgebraicSpaceULift_uliftYoneda.{w} B S hS U) hUqc
      (c ≫ pullback.snd k b)
  exact isQuasiCompactSpaceULift_of_iso B S hS (pullbackLeftPullbackSndIso k b a)
    (isQuasiCompactSpaceULift_pullback_of_chart B S hS a (pullback.snd k b) c hcSurj hcEtale
      hstep)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0ARR for the quasi-separatedness axiom of Stacks 0ARN.** A composite of two
morphisms of fppf sheaves on the big fppf site of `S` with quasi-compact relative diagonal
again has quasi-compact relative diagonal: the relative diagonal of `f ≫ g` factors as the
relative diagonal of `f`, quasi-compact since `f` is quasi-separated, followed by the
comparison `X ×_Y X ⟶ X ×_Z X`, quasi-compact since `g` is quasi-separated by Stacks 0ARQ,
part (3); and the quasi-compactness condition is stable under composition with no hypothesis
that the objects are algebraic spaces.

Quasi-compactness is read throughout as `AlgebraicGeometry.Space.IsQuasiCompactULift`, the
condition `AlgebraicGeometry.FormalSpace.IsQuasiSeparatedMorphism` is built from. As with the
definition, no hypothesis that the three sheaves are formal algebraic spaces is needed. -/
@[stacks 0ARR "part (2): quasi-separated, with quasi-compactness of the relative diagonal \
read as the condition AlgebraicGeometry.Space.IsQuasiCompactULift that this library's \
AlgebraicGeometry.FormalSpace.IsQuasiSeparatedMorphism is built from; the comparison of the \
two relative self-products is quasi-compact by Stacks 0ARQ, part (3), and that condition is \
stable under composition over formal algebraic spaces by \
AlgebraicGeometry.Space.isQuasiCompactULift_comp_of_presheaf"]
theorem isQuasiSeparatedMorphism_comp {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsQuasiSeparatedMorphism B S hS f) (hg : IsQuasiSeparatedMorphism B S hS g) :
    IsQuasiSeparatedMorphism B S hS (f ≫ g) := by
  have hhom : (pullback.diagonal f ≫ pullback.mapDesc f f g).hom =
      (pullback.diagonal f).hom ≫ (pullback.mapDesc f f g).hom := rfl
  change Space.IsQuasiCompactULift.{u + 1} B S hS (pullback.diagonal (f ≫ g)).hom
  rw [diagonal_comp_eq_mapDesc f g, hhom]
  exact Space.isQuasiCompactULift_comp_of_presheaf B S hS _ _ hf
    (isQuasiCompactULift_mapDesc B S hS f f g hg)

end AlgebraicGeometry.FormalSpace

end
