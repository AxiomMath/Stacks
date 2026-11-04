module

public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSpaceArbitraryChart
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The normalization of an algebraic space exists

`StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization` introduces
`AlgebraicGeometry.Space.NormalizationData`, the normalization of an algebraic space as data,
and says of itself that "the lemma asserts that such data *exists*, and only the construction
is entitled to the tag". This file constructs it, for an arbitrary algebraic space over `S`
whose étale scheme charts have finitely many irreducible components over every quasi-compact
open — which is condition (2) of Tag 0BB1, that is exactly the hypothesis of Tag 07U4 — and
with no size hypothesis.

Everything about the normalization of an algebraic space proved in this library was, until now,
an implication whose hypothesis had an instance only for a *representable* space
(`AlgebraicGeometry.Space.NormalizationData.ofRepresentable`, which also carries a size
hypothesis). In particular Stacks 0BHR was stated for a given datum `D` and concluded about
`D.hom`, so it presupposed the object whose finiteness it asserts; the unconditional form is
proved here, about *the* normalization — a named, constructed morphism.

## Main definitions

* `AlgebraicGeometry.Space.NormSpaceGluing.normalizationDataOfPresentation`: the construction of
  Tag 07U4 at a surjective étale presentation `R ⇉ U` of `F`, the quotient `U^ν / R^ν` with its
  morphism to `F`.
* `AlgebraicGeometry.Space.normalizationData`: **the** normalization of such an algebraic
  space, that construction at a chosen presentation; its `space` is `F^ν` and its `hom` is the
  normalization morphism.

## Main results

* `AlgebraicGeometry.Space.nonempty_normalizationData`: **Tag 07U4, the existence of the
  normalization.** An algebraic space over `S` satisfying the finiteness condition of Tag 0BB1
  has normalization data.
* `AlgebraicGeometry.Space.NormalizationData.existsUnique_iso_hom`: any two normalization data
  on the same algebraic space are carried to one another by a unique isomorphism over it.
* `AlgebraicGeometry.Space.hasLocallyFiniteIrreducibleComponents_of_isLocallyOfFiniteType`: an
  algebraic space locally of finite type over a Noetherian ring satisfies that finiteness
  condition.
* `AlgebraicGeometry.Space.isFinite_normalization_of_isAnalyticallyUnramified`: **Tag 0BHR**,
  about the normalization morphism of `AlgebraicGeometry.Space.normalizationData`.

## Implementation notes

**How the datum is built.** A surjective étale chart `w : h_U ⟶ F` is chosen and `R = U ×_F U`
formed; the normalizations `R^ν ⇉ U^ν` are an étale equivalence relation
(`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSpaceRelation`), the quotient sheaf
`U^ν/R^ν` is an algebraic space by Tag 02WW and comes with a morphism to `F` and with the chart
condition at `w` (`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSpaceQuotient`), and the
chart condition at every other étale chart is descent along the refinement
(`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSpaceArbitraryChart`). The three
finiteness proofs the construction consumes — for `U`, for `R` and for `R ×_U R` — are the one
for `U` propagated along étale morphisms by
`AlgebraicGeometry.finite_irreducibleComponents_of_smooth`.

**No size hypothesis.** Containment of a normalization in the big fppf site is free, by
`AlgebraicGeometry.Space.contains_normalizationScheme`, which rests on the size bound
`AlgebraicGeometry.Scheme.size_normalizationScheme_le`. This is strictly weaker than what
`AlgebraicGeometry.Space.NormalizationData.ofRepresentable` assumes, so that construction's
`hcontains` is redundant. It is left on `ofRepresentable`, whose statement is true as it stands;
`AlgebraicGeometry.Space.NormalizationData.ofRepresentableOfFiniteIrreducibleComponents` is the
same construction with that hypothesis discharged.

**The tag placement for 0BHR.** The source statement is "let `X` be an algebraic space locally
of finite type over an analytically unramified Noetherian local ring `A` whose structure
morphism is étale at every point of codimension `0`; then the normalization of `X` is finite
over `X`". `AlgebraicGeometry.Space.isFinite_normalization_of_isAnalyticallyUnramified` states
exactly that, and so carries `@[stacks 0BHR]`: its conclusion is
`IsFinite B S hS (normalizationData …).hom`, a statement about the one constructed
normalization morphism of `X`. It is deliberately not an existential over normalization data,
which would assert only that *some* normalization is finite and so would be weaker than the
source. The definite article is backed by
`AlgebraicGeometry.Space.NormalizationData.existsUnique_iso_hom`: the normalization is unique
up to a unique isomorphism over `X`, so finiteness of this one morphism is finiteness of every
normalization morphism of `X`.
`AlgebraicGeometry.Space.NormalizationData.isFinite_hom_of_isAnalyticallyUnramified` keeps the
same mathematics for an arbitrary datum — which is what the surrounding development consumes,
since its results are stated for an arbitrary one — but does not carry the tag: a theorem which
takes the normalization as a hypothesis does not assert that the normalization of `X` is finite
over `X`.

## References

* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
* [Stacks Project, Tag 0BB1](https://stacks.math.columbia.edu/tag/0BB1)
* [Stacks Project, Tag 0BHR](https://stacks.math.columbia.edu/tag/0BHR)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 07TD](https://stacks.math.columbia.edu/tag/07TD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The construction of Tag 07U4 at a presentation.** Let `F` be an algebraic space over `S`
satisfying condition (2) of Tag 0BB1, let `w : h_U ⟶ F` be a surjective étale scheme chart and
let `pr₁, pr₂ : R ⇉ U` be its kernel pair, `R = U ×_F U`. This is the normalization datum the
proof of Tag 07U4 builds from that presentation: its space is the quotient sheaf
`F^ν = U^ν / R^ν` (`AlgebraicGeometry.Space.NormSpaceGluing.normQuotient`) of the étale
equivalence relation formed by the normalizations of the charts, which is an algebraic space by
Tag 02WW, and its morphism is the descended morphism `F^ν ⟶ F`
(`AlgebraicGeometry.Space.NormSpaceGluing.normQuotientToBase`) of the normalization
`U^ν ⟶ U ⟶ F`.

The chart condition — the base change of `F^ν ⟶ F` along *every* surjective étale scheme chart
of `F` is the normalization of that chart — is checked at `w` by a computation with the kernel
pair of the quotient map and at every other chart by descent along the refinement. The three
finiteness conditions the gluing consumes, for `U`, for `R` and for `R ×_U R`, are the one of
Tag 0BB1 at `w`, propagated along étale morphisms. -/
def NormSpaceGluing.normalizationDataOfPresentation {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS F)
    {U R : BigFppfOver B S hS} (w : yoneda.obj U ⟶ F)
    (hwsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w)
    (hwet : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w)
    (pr₁ pr₂ : R ⟶ U) (hsq : IsPullback (yoneda.map pr₁) (yoneda.map pr₂) w w) :
    NormalizationData B S hS F := by
  classical
  have hU := hfin U w ((isEtale_iff_presheaf_of_yoneda B S hS w).mpr hwet)
  have _ : Etale ((BigFppfOver.toScheme B S hS).map pr₁) :=
    NormalizationGluing.etale_toScheme_map_pr₁ B S hS w pr₁ pr₂ hsq hwet
  have _ : Smooth ((BigFppfOver.toScheme B S hS).map pr₁) := inferInstance
  have hR := finite_irreducibleComponents_of_smooth
    ((BigFppfOver.toScheme B S hS).map pr₁) hU
  have _ : Etale ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst pr₂ pr₁)) :=
    NormalizationGluing.etale_toScheme_map_rel₂Fst B S hS w pr₁ pr₂ hsq hwet
  have _ : Smooth ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst pr₂ pr₁)) :=
    inferInstance
  have hR₂ := finite_irreducibleComponents_of_smooth
    ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst pr₂ pr₁)) hR
  refine { space := NormSpaceGluing.normQuotient B S hS w pr₁ pr₂ hsq hwet hU hR
           isAlgebraicSpace :=
             NormSpaceGluing.isAlgebraicSpace_normQuotient B S hS w pr₁ pr₂ hsq hwet hU hR hR₂
           hom := NormSpaceGluing.normQuotientToBase B S hS w pr₁ pr₂ hsq hwet hU hR hR₂ hF
           chart := ?_ }
  intro W w' _ hw'e
  have hw'et : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w' :=
    (isEtale_iff_presheaf_of_yoneda B S hS w').mp hw'e
  have hW := hfin W w' hw'e
  have hw' : yoneda.relativelyRepresentable w' :=
    relativelyRepresentable_of_isAlgebraicSpace B S hS hF w'
  have hjk : IsPullback (yoneda.map (hw'.fst' w)) (yoneda.map (hw'.snd w)) w' w :=
    hw'.isPullback' w
  have _ : Etale ((BigFppfOver.toScheme B S hS).map (hw'.snd w)) :=
    NormalizationGluing.etale_toScheme_map_k B S hS w w' hw'et (hw'.fst' w) (hw'.snd w) hjk
  have _ : Smooth ((BigFppfOver.toScheme B S hS).map (hw'.snd w)) := inferInstance
  have hV := finite_irreducibleComponents_of_smooth
    ((BigFppfOver.toScheme B S hS).map (hw'.snd w)) hU
  have _ : Etale ((BigFppfOver.toScheme B S hS).map (hw'.fst' w)) :=
    NormalizationGluing.etale_toScheme_map_j B S hS w hwet w' (hw'.fst' w) (hw'.snd w) hjk
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have _ : Etale ((BigFppfOver.toScheme B S hS).map
      (Limits.pullback.fst (hw'.fst' w) (hw'.fst' w))) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.Etale.{u})
      (((IsPullback.of_hasPullback (hw'.fst' w) (hw'.fst' w)).map
        (BigFppfOver.toScheme B S hS)).flip) inferInstance
  have _ : Smooth ((BigFppfOver.toScheme B S hS).map
      (Limits.pullback.fst (hw'.fst' w) (hw'.fst' w))) := inferInstance
  have hVV := finite_irreducibleComponents_of_smooth
    ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst (hw'.fst' w) (hw'.fst' w))) hV
  obtain ⟨b, hb⟩ := NormSpaceGluing.exists_chartMap_of_etaleChart B S hS w pr₁ pr₂ hsq hwet
    hwsurj hU hR hR₂ hF w' hw'et (hw'.fst' w) (hw'.snd w) hjk hW hV hVV
  exact ⟨hW, normSpace B S hS W hW, normSpaceProj B S hS W hW, b, Iso.refl _,
    (toScheme_map_normSpaceProj B S hS W hW).trans (Category.id_comp _).symm, hb⟩

/-- **Tag 07U4, the existence of the normalization.** An algebraic space over `S` every
quasi-compact open of every étale scheme chart of which has finitely many irreducible
components — condition (2) of Tag 0BB1 — has normalization data: an algebraic space `F^ν` over
`S` with a morphism `F^ν ⟶ F` whose base change along every surjective étale scheme chart of
`F` is the normalization of that chart.

The datum is glued along a surjective étale chart `w : h_U ⟶ F`: the normalizations of the
charts along `R = U ×_F U` form an étale equivalence relation, the quotient sheaf is an
algebraic space by Tag 02WW, and the chart condition is checked at `w` by a computation with
the kernel pair of the quotient map and at every other chart by descent along the refinement.
No representability and no bound on sizes is assumed.

The four numbered parts of Tag 07U4 are not proved here; they are the subject of
`StacksFrontier.AlgebraicGeometry.Spaces.Normal`,
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationIntegral` and
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationEtaleChart`, which assume the datum this
theorem produces. -/
@[stacks 07U4 "the existence of the normalization"]
theorem nonempty_normalizationData {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS F) :
    Nonempty (NormalizationData B S hS F) := by
  obtain ⟨U, w, hwsurj, hwet⟩ := hF.exists_atlas
  obtain ⟨R, pr₁, pr₂, hsq⟩ := exists_kernelPair_of_etale_atlas B S hS w hwet
  exact ⟨NormSpaceGluing.normalizationDataOfPresentation B S hS hF hfin w hwsurj hwet pr₁ pr₂ hsq⟩

namespace NormalizationData

section

variable {B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The normalization of an algebraic space is unique up to a unique isomorphism over it.**
Any two normalization data on the same algebraic space `F` are carried to one another by a
unique isomorphism commuting with the normalization morphisms. This is what justifies the
definite article in "the normalization of `F`".

Both comparison morphisms come from the universal property of the normalization, Stacks 0BB4
part (4): each normalization is normal by part (1), and each normalization morphism carries
points of codimension zero to points of codimension zero, being a bijection between them by
part (3). The two composites are the identity by the uniqueness half of the same property,
applied to the normalization morphism itself. -/
theorem existsUnique_iso_hom (D D' : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) :
    ∃! e : D.space ≅ D'.space, e.hom ≫ D'.hom = D.hom := by
  have hlift : ∀ E E' : NormalizationData B S hS F, ∃! a : E.space ⟶ E'.space,
      a ≫ E'.hom = E.hom := fun E E' =>
    existsUnique_lift_hom E' hF E.isAlgebraicSpace (E.hasEtaleLocalProperty_isNormal hF) E.hom
      fun _ hz => (E.bijOn_codimensionZeroPoints_hom hF).1 hz
  obtain ⟨a, ha, huniq⟩ := hlift D D'
  obtain ⟨b, hb, -⟩ := hlift D' D
  have hab : a ≫ b = 𝟙 D.space :=
    ExistsUnique.unique (hlift D D) (by rw [Category.assoc, hb, ha]) (Category.id_comp D.hom)
  have hba : b ≫ a = 𝟙 D'.space :=
    ExistsUnique.unique (hlift D' D') (by rw [Category.assoc, ha, hb]) (Category.id_comp D'.hom)
  exact ⟨⟨a, b, hab, hba⟩, ha, fun e he => Iso.ext (huniq e.hom he)⟩

end

end NormalizationData

/-- **The normalization of an algebraic space.** The normalization datum of an algebraic space
over `S` satisfying the finiteness condition of Tag 0BB1, built by the construction of Tag 07U4,
`AlgebraicGeometry.Space.NormSpaceGluing.normalizationDataOfPresentation`, at a chosen surjective
étale scheme chart `w : h_U ⟶ F` of `F` and its kernel pair `R = U ×_F U`: its `space` is the
normalization `F^ν = U^ν / R^ν` and its `hom` is the normalization morphism `F^ν ⟶ F`.

Choosing the chart is harmless, and the definite article is justified, because any two
normalization data on `F` are carried to one another by a *unique* isomorphism over `F`
(`AlgebraicGeometry.Space.NormalizationData.existsUnique_iso_hom`); so every property of this
datum invariant under such an isomorphism is a property of the normalization of `F`. Read in
the category of algebraic spaces over `S`, the space and the morphism are
`AlgebraicGeometry.Space.normalizationSpace` and `AlgebraicGeometry.Space.normalizationHom`
applied to this datum. -/
def normalizationData {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS F) :
    NormalizationData B S hS F :=
  let w := hF.exists_atlas.choose_spec.choose
  have hA := hF.exists_atlas.choose_spec.choose_spec
  NormSpaceGluing.normalizationDataOfPresentation B S hS hF hfin w hA.1 hA.2
    (yoneda.preimage (hA.2.rep.fst w)) (hA.2.rep.snd w)
    (by rw [yoneda.map_preimage]; exact hA.2.rep.isPullback w)

/-- **An algebraic space locally of finite type over a Noetherian ring satisfies the finiteness
condition of Tag 0BB1.** Every étale scheme chart is then locally of finite type over
`Spec A`, hence locally Noetherian, and a quasi-compact open of a locally Noetherian scheme has
finitely many irreducible components.

The base is a representable presheaf of the site together with an isomorphism of the scheme it
represents with `Spec A`, which is the form in which the hypothesis of Tag 0BHR is carried in
this library. -/
theorem hasLocallyFiniteIrreducibleComponents_of_isLocallyOfFiniteType {A : Type u} [CommRing A]
    [IsNoetherianRing A] {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Z : BigFppfOver B S hS} (f : F ⟶ yoneda.obj Z)
    (a : (BigFppfOver.toScheme B S hS).obj Z ⟶ Spec (.of A)) [IsIso a]
    (hft : IsLocallyOfFiniteType B S hS f) :
    HasLocallyFiniteIrreducibleComponents B S hS F := by
  intro U g hge V hV
  have hh : yoneda.map (yoneda.preimage (g ≫ f)) = g ≫ f := yoneda.map_preimage (g ≫ f)
  have hZid : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj Z)) :=
    (isEtale_iff_presheaf_of_yoneda B S hS (𝟙 (yoneda.obj Z))).mp
      (isEtale_id B S hS (yoneda.obj Z))
  have _ : LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (g ≫ f))) :=
    hft U Z g (𝟙 (yoneda.obj Z)) (yoneda.preimage (g ≫ f))
      ((isEtale_iff_presheaf_of_yoneda B S hS g).mp hge) hZid (by rw [hh]; simp)
  have _ : LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (g ≫ f)) ≫ a) := inferInstance
  have _ : IsLocallyNoetherian (Spec (CommRingCat.of A)) := inferInstance
  have _ : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (g ≫ f)) ≫ a)
  exact finite_irreducibleComponents_of_isCompact
    ((BigFppfOver.toScheme B S hS).obj U) V hV

/-- **Stacks 0BHR.** Let `(A, 𝔪)` be an analytically unramified Noetherian local ring and let
`F` be an algebraic space over `S` whose structure morphism goes to an object of the site with
underlying scheme `Spec A`. If `F` is locally of finite type over `A` and its structure
morphism is étale at every point of codimension zero, then **the** normalization morphism
`F^ν ⟶ F` of `F` is a finite morphism of algebraic spaces.

The normalization is the constructed one, neither assumed nor existentially quantified: `F` is
locally of finite type over a Noetherian ring, so its étale scheme charts are locally
Noetherian and satisfy the finiteness condition of Tag 0BB1, and
`AlgebraicGeometry.Space.normalizationData` is then the normalization of `F`, unique up to a
unique isomorphism over `F` by
`AlgebraicGeometry.Space.NormalizationData.existsUnique_iso_hom`. Finiteness of its
normalization morphism is
`AlgebraicGeometry.Space.NormalizationData.isFinite_hom_of_isAnalyticallyUnramified`, which is
Stacks 0BG8 on a surjective étale chart followed by the étale-local characterisation of
finiteness, condition (3) of Stacks 03ZQ.

The base is a representable presheaf with an isomorphism of its underlying scheme onto
`Spec A`, which is the source's hypothesis with no identification of schemes imposed and with
the base scheme `S` of the site left arbitrary. -/
@[stacks 0BHR, sga "3 XXV 4.2" "more general"]
theorem isFinite_normalization_of_isAnalyticallyUnramified {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (hA : IsAnalyticallyUnramified A)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {Z : BigFppfOver B S hS} (f : F ⟶ yoneda.obj Z)
    (a : (BigFppfOver.toScheme B S hS).obj Z ⟶ Spec (.of A)) [IsIso a]
    (hft : IsLocallyOfFiniteType B S hS f)
    (het : ∀ x : points B S hS F, localRingDimension B S hS x = 0 → IsEtaleAt B S hS f x) :
    IsFinite B S hS (normalizationData B S hS hF
      (hasLocallyFiniteIrreducibleComponents_of_isLocallyOfFiniteType B S hS f a hft)).hom :=
  NormalizationData.isFinite_hom_of_isAnalyticallyUnramified hA hF f a hft het _

end AlgebraicGeometry.Space

end
