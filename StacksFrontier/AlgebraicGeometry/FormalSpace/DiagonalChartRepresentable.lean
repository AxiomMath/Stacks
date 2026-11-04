module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.MorphismFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SmallSite
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda

/-!
# A subsheaf of a representable with an étale chart of finite type is representable

Let `S` be a scheme contained in a big fppf site `B`. The proof of **Stacks 0AIP** — the
diagonal of a formal algebraic space over `S` is representable by schemes, locally quasi-finite,
locally of finite type, a monomorphism and separated — tests the diagonal against a
scheme-valued point and has to show that the resulting fibre product, a *subsheaf* `E` of the
sheaf represented by an object `N` of the site, is itself represented by an object of the site.
The source does this in two moves: an étale covering of `E` by schemes makes `E` an algebraic
space, and the factorisation of each member as a closed immersion followed by an étale morphism
makes `E` locally quasi-finite and separated over `N`, so Stacks 03XX applies.

This file carries out both moves at once, from the data the geometric construction produces:
*one* object `W` of the site with a representable, surjective, étale morphism `h_W ⟶ E` whose
composite with the inclusion `E ⟶ h_N` is a morphism `W ⟶ N` of the site which is locally of
finite type. Nothing about formal algebraic spaces is used; the chart is the hypothesis.

What is **not** here is the construction of that chart for the diagonal of a formal algebraic
space, which is in `StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable`; see the
implementation notes.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_locallyOfFiniteType_of_mono_of_chart`: the criterion for
  presheaves of `Type (u + 1)` along the universe-lifted Yoneda embedding, returning in addition
  the local finite type of the representing morphism of the site over the ambient object, which
  is what the local finiteness assertions of Stacks 0AIP need.
* `AlgebraicGeometry.FormalSpace.essImage_uliftYoneda_of_mono_of_chart`: its representability
  half.
* `AlgebraicGeometry.FormalSpace.essImage_sheafifiedYoneda_of_mono_of_chart`: the same for an
  fppf sheaf and the sheafified Yoneda embedding, which is the shape in which the rest of the
  development states representability by objects of the site.
* `AlgebraicGeometry.FormalSpace.hasRepresentableRelativeProducts_of_exists_mono_chart`: the
  representability assertion of **Stacks 0AIP**, in the form
  `AlgebraicGeometry.FormalSpace.HasRepresentableRelativeProducts` in which this development
  records it, for a sheaf each of whose relative products of two scheme-valued points admits a
  chart as above.
* `AlgebraicGeometry.FormalSpace.exists_mono_toProd_pullback`: the ambient representable and the
  monomorphism into it, for the relative product of two scheme-valued points, so that the chart
  is the only datum the consumer has to construct.

## Implementation notes

The chart hypothesis is deliberately a monomorphism into a representable *plus* a chart, rather
than "`E` is an algebraic space, locally quasi-finite and separated over `h_N`": the latter is
Stacks 03XX verbatim, already available as
`AlgebraicGeometry.Space.isRepresentable_of_locallyQuasiFinite_separated`, and its hypotheses
are not the ones a covering argument hands you. From the chart the three of them are produced
here: the algebraic-space condition by Stacks 0BGR in the large value universe
(`AlgebraicGeometry.Space.isAlgebraicSpaceULift_of_relative_surjective_etale`), local finite
type over `h_N` by the descent of Stacks 06NR along the chart, which is locally surjective
because it is representable, surjective and étale, and then separatedness and local
quasi-finiteness by Stacks 0463 for a monomorphism locally of finite type, that is by
`AlgebraicGeometry.Space.isSeparated_isLocallyQuasiFinite_of_isLocallyOfFiniteType_mono`.
Only local finite type of `W ⟶ N` is asked of the chart; no quasi-finiteness and no
separatedness, both of which come from the monomorphism.

The value universe is handled once, here, and not by the consumer. A formal algebraic space is
a sheaf of `Type (u + 1)` while Stacks 03XX, Stacks 06NR and Stacks 0463 are stated for
presheaves of `Type u`. The shrinking of the algebraic space `E` to `Type u` is
`AlgebraicGeometry.Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift`; the inclusion
and the chart descend along that isomorphism because whiskering with
`CategoryTheory.uliftFunctor` is fully faithful, and the conclusion is lifted back along it.
This is why the statement instantiates at
`AlgebraicGeometry.FppfSheaf B S hS`, the universe in which Stacks 0AIP has to be read.

The chart itself is built in
`StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable`, where the ambient `N` is
`a ⨯ b` and the monomorphism into it is `…exists_mono_toProd_pullback` below: for a formal
algebraic space `X` with atlas `{Xₖ ⟶ X}` and two scheme-valued points `u : h_a ⟶ X`,
`v : h_b ⟶ X`, an object `W` of the site with a surjective étale representable morphism
`h_W ⟶ h_a ×_X h_b` and `W ⟶ a ⨯ b` locally of finite type. The members it collects are the
sheaves `h_{Zₖ} ×_{Xₖ} h_{Z'ₖ}`, for `Zₖ ⟶ h_a ×_X Xₖ` and `Z'ₖ ⟶ h_b ×_X Xₖ` scheme atlases of
those algebraic spaces, each represented by an object of the site by Stacks 0AI8 for the affine
formal algebraic space `Xₖ`, with its morphism to `Zₖ ⨯ Z'ₖ` a closed immersion and hence the
composite to `a ⨯ b` locally of finite type; the collection is point-indexed by `a ⨯ b` to get
below the site's size cutoff. That module's implementation notes describe the construction.

Besides the representing object, the criterion returns the local finite type of the morphism
`Po ⟶ N` of the site which realises the monomorphism, which is what the local finiteness
assertions of Stacks 0AIP are proved from. It is read off the every-étale-chart condition the
descent of Stacks 06NR produces, the representing isomorphism and the identity of `h_N` being
étale charts, by Stacks 03MJ. Separatedness and local quasi-finiteness are not returned: by
Stacks 0CT8 they follow at the level of schemes from that local finite type together with the
monomorphism, which the consumer already has.

No `@[stacks]` attribute is carried below. The representability criterion is Stacks 03XX in a
different shape, and that tag is already attached to
`AlgebraicGeometry.Space.isRepresentable_of_locallyQuasiFinite_separated`; and the statements
about `HasRepresentableRelativeProducts` are conditional on a chart, so they are not a
formalization of Stacks 0AIP, whose registrations are in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RelativeDiagonal` for the affine case and the
monomorphism and in `StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable` for the
four non-trivial assertions in general.

**Duplicates.** `relative_of_natIso` below carries the same name, statement and content as a
`private` declaration in the proof of Stacks 0AIP, and `sheafifiedYonedaPresheafIso`
is `private` under the name `sheafifiedYonedaToUliftPresheafIso` in
`StacksFrontier/AlgebraicGeometry/FormalSpace/Affine/FiniteTypeClassification.lean`. Both are
public here, being the
versions the construction of the chart itself consumes.

## References

* [Stacks Project, Tag 03XX](https://stacks.math.columbia.edu/tag/03XX)
* [Stacks Project, Tag 0463](https://stacks.math.columbia.edu/tag/0463)
* [Stacks Project, Tag 06NR](https://stacks.math.columbia.edu/tag/06NR)
* [Stacks Project, Tag 0AI8](https://stacks.math.columbia.edu/tag/0AI8)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0BGR](https://stacks.math.columbia.edu/tag/0BGR)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 0CT8](https://stacks.math.columbia.edu/tag/0CT8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A subsheaf of a universe-lifted representable carrying an étale chart of finite type is
represented by an object of the site, locally of finite type over the ambient object.** Let `E`
be an fppf sheaf of `Type (u + 1)` on the big fppf site of `S` which maps monomorphically to the
universe-lifted Yoneda presheaf of an object `c` of the site, and suppose given one object `W`
of the site and a morphism `q : h_W ⟶ E` which is representable by objects of the site,
surjective and étale, whose composite with the monomorphism is the universe-lifted Yoneda image
of a morphism `w : W ⟶ c` of the site which is locally of finite type. Then `E` is isomorphic to
the universe-lifted Yoneda presheaf of an object `Po` of the site, by an isomorphism carrying
the monomorphism to a morphism `Po ⟶ c` of the site which is itself locally of finite type.

The chart makes `E` an algebraic space over `S` by Stacks 0BGR, which lets it be shrunk to a
presheaf of `Type u`; local finite type of `w` descends along the chart to local finite type of
`E ⟶ h_c` by Stacks 06NR; a monomorphism locally of finite type is separated and locally
quasi-finite by Stacks 0463; and Stacks 03XX then makes `E ⟶ h_c` representable by objects of
the site, which at the identity point of `h_c` is the assertion about `E`.

The local finite type of the resulting morphism `Po ⟶ c` of the site is read off the
every-étale-chart condition which that descent produces: the isomorphism `h_{Po} ≅ E` and the
identity of `h_c` are étale charts of the two ends of `E ⟶ h_c`, and Stacks 03MJ identifies the
every-étale-chart condition for a morphism of the site with the condition on its underlying
morphism of schemes. The three facts about `E ⟶ h_c` which the proof establishes on its way —
local finite type, separatedness and local quasi-finiteness — are therefore all available on
`Po ⟶ c`, the last two from the first together with the monomorphism, so only the first is
returned. -/
theorem exists_locallyOfFiniteType_of_mono_of_chart
    {c : BigFppfOver B S hS} {E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hE : Presheaf.IsSheaf (BigFppfOver.topology B S hS) E)
    (m : E ⟶ uliftYoneda.{u + 1}.obj c) (hm : Mono m)
    {W : BigFppfOver B S hS} (w : W ⟶ c)
    (q : uliftYoneda.{u + 1}.obj W ⟶ E)
    (hfac : q ≫ m = uliftYoneda.{u + 1}.map w)
    (hw : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map w))
    (hsurj : (Space.surjectiveOnSite B S hS).relative uliftYoneda.{u + 1} q)
    (hetale : (Space.etaleOnSite B S hS).relative uliftYoneda.{u + 1} q) :
    ∃ (Po : BigFppfOver B S hS) (p : Po ⟶ c) (e : uliftYoneda.{u + 1}.obj Po ≅ E),
      e.hom ≫ m = uliftYoneda.{u + 1}.map p ∧
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map p) := by
  let H := (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
    uliftFunctor.{u + 1, u}
  obtain ⟨E', hE', ⟨eE⟩⟩ := Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS
    (Space.isAlgebraicSpaceULift_of_relative_surjective_etale B S hS hE
      (Space.isAlgebraicSpaceULift_uliftYoneda B S hS W) q hsurj hetale)
  let m' : E' ⟶ yoneda.obj c := H.preimage (eE.hom ≫ m)
  have hm' : H.map m' = eE.hom ≫ m := H.map_preimage _
  let q' : yoneda.obj W ⟶ E' := H.preimage (q ≫ eE.inv)
  have hq' : H.map q' = q ≫ eE.inv := H.map_preimage _
  have hfac' : q' ≫ m' = yoneda.map w := by
    apply H.map_injective
    rw [H.map_comp, hm', hq']
    exact (by simp : (q ≫ eE.inv) ≫ (eE.hom ≫ m) = q ≫ m).trans hfac
  have hmono : Mono m' := by
    let : Mono m := hm
    have h : Mono (eE.hom ≫ m) := inferInstance
    exact H.mono_of_mono_map (by rw [hm']; exact h)
  have hlftW : Space.IsLocallyOfFiniteType B S hS (yoneda.map w) :=
    Space.holdsOnEveryEtaleChart_yoneda_map B S hS
      LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget w hw
  have hq'surj : (MorphismProperty.presheaf (Space.surjectiveOnSite B S hS)) q' :=
    (Space.relative_comp_map_iff yoneda H (Space.surjectiveOnSite B S hS) q').mp
      (hq' ▸ MorphismProperty.RespectsIso.postcomp _ eE.inv q hsurj)
  have hq'et : (MorphismProperty.presheaf (Space.etaleOnSite B S hS)) q' :=
    (Space.relative_comp_map_iff yoneda H (Space.etaleOnSite B S hS) q').mp
      (hq' ▸ MorphismProperty.RespectsIso.postcomp _ eE.inv q hetale)
  have hlft : Space.IsLocallyOfFiniteType B S hS m' :=
    Space.isLocallyOfFiniteType_of_comp_of_locallySurjective B S hS
      (isAlgebraicSpace_yoneda B S hS W) hE' (isAlgebraicSpace_yoneda B S hS c)
      q' m' (by rwa [hfac'])
      (Space.isLocallySurjective_of_presheafSurjective_etale q' hq'surj hq'et)
  obtain ⟨hsep, hlqf⟩ :=
    Space.isSeparated_isLocallyQuasiFinite_of_isLocallyOfFiniteType_mono B S hS m' ⟨hlft, hmono⟩
  obtain ⟨P, p, _, hpb⟩ := Space.relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated B S hS
    m' hE' (isAlgebraicSpace_yoneda B S hS c) hlqf hsep (𝟙 (yoneda.obj c))
  have h2 : IsPullback (𝟙 E') m' m' (𝟙 (yoneda.obj c)) := IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨eP, hePm⟩ : ∃ eP : yoneda.obj P ≅ E', eP.hom ≫ m' = yoneda.map p :=
    ⟨hpb.isoIsPullback E' (yoneda.obj c) h2, hpb.isoIsPullback_hom_snd _ _ h2⟩
  refine ⟨P, p, H.mapIso eP ≪≫ eE, ?_, ?_⟩
  · have h3 : H.map eP.hom ≫ H.map m' = uliftYoneda.{u + 1}.map p := by
      rw [← H.map_comp, hePm]
      rfl
    rw [hm'] at h3
    exact (Category.assoc _ _ _).trans h3
  · exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget p).mp fun U V a b h ha hb hsq =>
      hlft U V (a ≫ eP.hom) b h (MorphismProperty.RespectsIso.postcomp _ _ a ha) hb
      (by rw [hsq, ← hePm, Category.assoc])

/-- **A subsheaf of a universe-lifted representable carrying an étale chart of finite type is
represented by an object of the site.** This is the representability half of
`AlgebraicGeometry.FormalSpace.exists_locallyOfFiniteType_of_mono_of_chart`. -/
theorem essImage_uliftYoneda_of_mono_of_chart
    {c : BigFppfOver B S hS} {E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hE : Presheaf.IsSheaf (BigFppfOver.topology B S hS) E)
    (m : E ⟶ uliftYoneda.{u + 1}.obj c) (hm : Mono m)
    {W : BigFppfOver B S hS} (w : W ⟶ c)
    (q : uliftYoneda.{u + 1}.obj W ⟶ E)
    (hfac : q ≫ m = uliftYoneda.{u + 1}.map w)
    (hw : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map w))
    (hsurj : (Space.surjectiveOnSite B S hS).relative uliftYoneda.{u + 1} q)
    (hetale : (Space.etaleOnSite B S hS).relative uliftYoneda.{u + 1} q) :
    uliftYoneda.{u + 1}.essImage E :=
  let ⟨Po, _, e, _, _⟩ := exists_locallyOfFiniteType_of_mono_of_chart B S hS hE m hm w q hfac hw
    hsurj hetale
  ⟨Po, ⟨e⟩⟩

/-- A relative morphism property along a functor only depends on the functor up to
isomorphism. -/
theorem relative_of_natIso {C : Type*} [Category* C] {D : Type*} [Category* D]
    {F G : C ⥤ D} (e : F ≅ G) (P : MorphismProperty C) {X Y : D} (f : X ⟶ Y)
    (h : P.relative F f) : P.relative G f := by
  refine ⟨fun a g => ?_, fun a b g t s ht => ?_⟩
  · obtain ⟨b, s, t, ht⟩ := h.1 (e.hom.app a ≫ g)
    exact ⟨b, s, e.inv.app b ≫ t, ht.of_iso (e.app b) (Iso.refl _) (e.app a) (Iso.refl _)
      (by simp) (e.hom.naturality s) (by simp) (by simp)⟩
  · exact h.property (e.hom.app a ≫ g) (e.hom.app b ≫ t) s
      (ht.of_iso (e.symm.app b) (Iso.refl _) (e.symm.app a) (Iso.refl _)
        (by simp) (e.inv.naturality s) (by simp) (by simp))

/-- The sheafified Yoneda embedding of the big fppf site of `S`, read as a presheaf, is the
universe-lifted Yoneda embedding, the site being subcanonical. -/
noncomputable def sheafifiedYonedaPresheafIso :
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS) ⋙
      sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)) ≅ uliftYoneda.{u + 1} := by
  letI : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  exact Functor.isoWhiskerRight
      (Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS))
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))) ≪≫
    GrothendieckTopology.uliftYonedaCompSheafToPresheaf.{u + 1}
      (BigFppfOver.topology B S hS)

/-- **A subsheaf of a representable carrying an étale chart of finite type is represented by an
object of the site**, for the sheafified Yoneda embedding. This is
`AlgebraicGeometry.FormalSpace.essImage_uliftYoneda_of_mono_of_chart` for an fppf sheaf
`E : AlgebraicGeometry.FppfSheaf B S hS` and the embedding in which this development states
representability by objects of the site.

The two embeddings agree up to isomorphism, the big fppf site being subcanonical, and the
forgetful functor to presheaves is fully faithful and preserves fibre products, so both the
monomorphism and the two relative properties of the chart transport. -/
theorem essImage_sheafifiedYoneda_of_mono_of_chart
    {c : BigFppfOver B S hS} {E : FppfSheaf B S hS}
    (m : E ⟶ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj c) (hm : Mono m)
    {W : BigFppfOver B S hS} (w : W ⟶ c)
    (q : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶ E)
    (hfac : q ≫ m = (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map w)
    (hw : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map w))
    (hsurj : (Space.surjectiveOnSite B S hS).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) q)
    (hetale : (Space.etaleOnSite B S hS).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) q) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).essImage E := by
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let K := sheafToPresheaf J (Type (u + 1))
  let gl := sheafifiedYonedaPresheafIso B S hS
  have hnat : ∀ {c₁ c₂ : BigFppfOver B S hS} (k : c₁ ⟶ c₂),
      K.map (F.map k) ≫ gl.hom.app c₂ = gl.hom.app c₁ ≫ uliftYoneda.{u + 1}.map k :=
    fun k => gl.hom.naturality k
  let m₂ : E.obj ⟶ uliftYoneda.{u + 1}.obj c := K.map m ≫ gl.hom.app c
  let q₂ : uliftYoneda.{u + 1}.obj W ⟶ E.obj := gl.inv.app W ≫ K.map q
  have hm₂ : Mono m₂ := by
    have := K.map_mono m
    infer_instance
  have hfac₂ : q₂ ≫ m₂ = uliftYoneda.{u + 1}.map w := by
    simp only [m₂, q₂, Category.assoc]
    rw [← K.map_comp_assoc, hfac, hnat w, Iso.inv_hom_id_app_assoc]
  have hrel : ∀ (P : MorphismProperty (BigFppfOver B S hS)),
      P.relative F q → P.relative uliftYoneda.{u + 1} q₂ := fun P hP =>
    MorphismProperty.RespectsIso.precomp _ (gl.inv.app W) (K.map q)
      (relative_of_natIso gl P (K.map q) ((Space.relative_comp_map_iff F K P q).mpr hP))
  obtain ⟨P, ⟨eP⟩⟩ := essImage_uliftYoneda_of_mono_of_chart B S hS E.property m₂ hm₂ w q₂ hfac₂
    hw (hrel _ hsurj) (hrel _ hetale)
  exact ⟨P, ⟨K.preimageIso (gl.app P ≪≫ eP)⟩⟩

/-- **The representability assertion of Stacks 0AIP from a chart of each relative product.** An
fppf sheaf `X` on the big fppf site of `S` has representable relative products — every morphism
to `X` from a sheaf represented by an object of the site is relatively representable, which is
the representability assertion of **Stacks 0AIP** in the form this development records it —
provided that for every two scheme-valued points `u`, `v` of `X` the relative product
`h_a ×_X h_b` maps monomorphically to the sheaf represented by an object `N` of the site and
carries a representable surjective étale chart `h_W ⟶ h_a ×_X h_b` whose composite with that
monomorphism is a morphism `W ⟶ N` of the site locally of finite type.

The relative product is then represented by an object of the site, by
`AlgebraicGeometry.FormalSpace.essImage_sheafifiedYoneda_of_mono_of_chart`, and the cartesian
square it sits in is the one relative representability asks for.

For a formal algebraic space `N` is `a ⨯ b` and the chart is the étale covering of the proof of
Stacks 0AIP; the implementation notes of this file say what remains to be proved about it. -/
theorem hasRepresentableRelativeProducts_of_exists_mono_chart {X : FppfSheaf B S hS}
    (hchart : ∀ (a b : BigFppfOver B S hS)
      (u : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj a ⟶ X)
      (v : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj b ⟶ X),
      ∃ (N W : BigFppfOver B S hS)
        (n : pullback u v ⟶ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj N)
        (w : W ⟶ N)
        (q : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶ pullback u v),
        Mono n ∧ q ≫ n = (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map w ∧
          LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map w) ∧
          (Space.surjectiveOnSite B S hS).relative
            (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) q ∧
          (Space.etaleOnSite B S hS).relative
            (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) q) :
    HasRepresentableRelativeProducts B S hS X := by
  intro a u b v
  obtain ⟨N, W, n, w, q, hn, hfac, hw, hsurj, hetale⟩ := hchart a b u v
  obtain ⟨P, ⟨eP⟩⟩ :=
    essImage_sheafifiedYoneda_of_mono_of_chart B S hS n hn w q hfac hw hsurj hetale
  refine ⟨P, (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).preimage
      (eP.hom ≫ pullback.snd u v), eP.hom ≫ pullback.fst u v, ?_⟩
  refine IsPullback.of_iso_pullback ⟨?_⟩ eP rfl
    ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_preimage _).symm
  rw [(Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_preimage,
    Category.assoc, Category.assoc, pullback.condition]

/-- **The relative product of two scheme-valued points sits inside the product of the site by a
monomorphism.** For two morphisms `u : h_a ⟶ X`, `v : h_b ⟶ X` of fppf sheaves out of sheaves
represented by objects of the site, the fibre product `h_a ×_X h_b` maps monomorphically to the
sheaf represented by the product `a ⨯ b` of the site, compatibly with the two projections.

This is the object `N` and the monomorphism `n` which
`AlgebraicGeometry.FormalSpace.hasRepresentableRelativeProducts_of_exists_mono_chart` asks for,
so that only the chart itself remains to be constructed. The sheafified Yoneda embedding
preserves binary products, the big fppf site being subcanonical, and two morphisms into a fibre
product agreeing after both projections agree. -/
theorem exists_mono_toProd_pullback [HasBinaryProducts (BigFppfOver B S hS)]
    (a b : BigFppfOver B S hS) {X : FppfSheaf B S hS}
    (u : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj a ⟶ X)
    (v : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj b ⟶ X) :
    ∃ n : pullback u v ⟶ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (a ⨯ b),
      Mono n ∧
      n ≫ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map prod.fst =
        pullback.fst u v ∧
      n ≫ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map prod.snd =
        pullback.snd u v := by
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  have : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  have : PreservesLimitsOfShape (Discrete WalkingPair) F :=
    preservesLimitsOfShape_of_natIso
      (Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS)).symm
  let e : F.obj (a ⨯ b) ≅ F.obj a ⨯ F.obj b := PreservesLimitPair.iso F a b
  have : Mono (prod.lift (pullback.fst u v) (pullback.snd u v)) :=
    ⟨fun g h hgh => pullback.hom_ext
      (by simpa only [Category.assoc, prod.lift_fst] using hgh =≫ prod.fst)
      (by simpa only [Category.assoc, prod.lift_snd] using hgh =≫ prod.snd)⟩
  refine ⟨prod.lift (pullback.fst u v) (pullback.snd u v) ≫ e.inv, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, PreservesLimitPair.iso_inv_fst, prod.lift_fst]
  · rw [Category.assoc, PreservesLimitPair.iso_inv_snd, prod.lift_snd]

end AlgebraicGeometry.FormalSpace

end
