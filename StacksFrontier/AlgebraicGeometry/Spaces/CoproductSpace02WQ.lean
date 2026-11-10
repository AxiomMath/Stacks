module

public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAtlas02WRb
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingInSite

/-!
# A coproduct of algebraic spaces

A coproduct `G = ∐ᵢ Fᵢ` of algebraic spaces over `S` is an algebraic space, provided the index
type and the members are not too large. This file supplies the scheme atlas, which is the
clause the source calls straightforward, and assembles it with the sheaf condition and the
representable diagonal.

The atlas is the coproduct `U = ∐ᵢ Uᵢ` of charts of the members. What makes `U` an object of the
site is a size hypothesis, and the two forms of it are kept apart:

* `AlgebraicGeometry.Space.exists_atlas_of_isColimit_of_contains` asks exactly what the source
  asks -- that the coproduct of the underlying schemes of the chosen charts lie in the site --
  and nothing about the size of the index type. It is the source's third step, and it needs the
  representability of the diagonal as an input, because the atlas clause of
  `AlgebraicGeometry.IsAlgebraicSpace` asks for surjectivity and étaleness *after every
  representable base change*, which presupposes that the atlas is relatively representable.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_isColimit` is the whole theorem, under the
  cofinality bound `#I < B.cutoff.ord.cof` on the index type. That bound discharges the
  containment automatically, through
  `AlgebraicGeometry.BigFppfSite.contains_sigma_of_lt_cof`, and it is also what the only
  available proof of the diagonal clause consumes.

## Main results

* `AlgebraicGeometry.Space.isLocallySurjective_of_isColimit_of_fac`: a morphism to a coproduct
  of fppf sheaves is locally surjective as soon as, for each summand, a locally surjective
  morphism onto that summand factors through it.
* `AlgebraicGeometry.Space.exists_atlas_of_isColimit_of_contains`: the coproduct of charts of
  the members is a surjective étale chart of the coproduct.
* `AlgebraicGeometry.Space.relativelyRepresentable_diag_of_isColimit`: a coproduct of algebraic
  spaces indexed below the cofinality of the cutoff has a representable diagonal.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_isColimit`: such a coproduct is an algebraic
  space.

## Implementation notes

Nothing here carries a `@[stacks 02WQ]` attribute. The source states its size hypothesis as
"`I` and the `Fᵢ` are not too large", offering as an example that the coproduct of a choice of
charts be isomorphic to an object of the site, whereas
`AlgebraicGeometry.Space.isAlgebraicSpace_of_isColimit` assumes `#I < B.cutoff.ord.cof`, which
`StacksFrontier.AlgebraicGeometry.Spaces.SiteGluing` records as the strictly stronger condition of
the two. So the theorem proved here is weaker than the one the source states, and the gap is
exactly the diagonal clause: the atlas clause is available under the source's own hypothesis,
which is what `AlgebraicGeometry.Space.exists_atlas_of_isColimit_of_contains` isolates.

The diagonal is not reproved. It is
`AlgebraicGeometry.Space.relativelyRepresentable_diag_of_openCover`, the general glueing theorem
of Stacks 02WR, applied to the covering map `𝟙 G`: a coproduct is covered by its own summands,
which are attached through representable open immersions by
`AlgebraicGeometry.Space.isOpenImmersion_coproductInj`. The other diagonal theorem of that
circle of ideas,
`AlgebraicGeometry.Space.relativelyRepresentable_diag_of_openCover_of_isAlgebraicSpace`, trades
the bound on `#I` for the hypothesis that the coproduct is an algebraic space, and is therefore
useless here: with the covered sheaf taken to be the coproduct itself that hypothesis contains
the conclusion. Its proof uses the assumed diagonal to produce an object of the site
representing `(V ×_G W) ×_G G`, which for `F = G` is the object being sought.

Local surjectivity of the atlas is proved from the covering property of the summands rather
than from any description of a coproduct of presheaves. The sieve on which a section of `G`
lies in one of the summands is refined by the sieve on which the resulting section of that
summand lifts along its chart; the composite sieve covers by transitivity, and on it the
section lifts along the atlas. No pointwise formula for a presheaf coproduct is used, which is
the same discipline as in `StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverSpace`.

Representability of the atlas is read off the diagonal through
`CategoryTheory.Functor.relativelyRepresentable.of_diag` rather than proved by hand. This is
why the diagonal is established before the atlas and passed to the atlas lemma as a hypothesis
rather than the two being proved independently.

Étaleness of the atlas is locality at the source along the open cover of `U` by the summands
`Uᵢ`, which are open immersions because they are the legs of a colimit cofan of schemes
(`AlgebraicGeometry.isOpenImmersion_of_isColimit_cofanMk`) and jointly surjective by
`AlgebraicGeometry.exists_mem_range_of_isColimit_cofanMk`. On the `i`-th summand the atlas is
the chart of `Fᵢ` followed by the inclusion of `Fᵢ`, which is étale as a composite of an étale
morphism and an open immersion.

## References

* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 02WR](https://stacks.math.columbia.edu/tag/02WR)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Local surjectivity of a morphism onto a coproduct -/

/-- **A morphism onto a coproduct of fppf sheaves is locally surjective once each summand is
locally covered through it.** If `G` is the coproduct of the `Fᵢ` and, for each `i`, a locally
surjective `aᵢ : Aᵢ ⟶ Fᵢ` factors through `f : P ⟶ G` after composing with the inclusion of the
`i`-th summand, then `f` is locally surjective.

A section of `G` lies, on a covering sieve, in one of the summands; on that sieve the resulting
section of the summand lifts along `aᵢ`, again after refining by a covering sieve; and a lift
along `aᵢ` gives a lift along `f` through the factorisation. -/
theorem isLocallySurjective_of_isColimit_of_fac
    {I : Type v} {Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (jj : ∀ i, Fᵢ i ⟶ G) (hcoprod : IsColimit (Cofan.mk G jj))
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : P ⟶ G.obj)
    {Aᵢ : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (aᵢ : ∀ i, Aᵢ i ⟶ (Fᵢ i).obj)
    (haᵢ : ∀ i, CategoryTheory.Presheaf.IsLocallySurjective
      (BigFppfOver.topology B S hS) (aᵢ i))
    (rᵢ : ∀ i, Aᵢ i ⟶ P) (hfac : ∀ i, rᵢ i ≫ f = aᵢ i ≫ (jj i).hom) :
    CategoryTheory.Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f := by
  classical
  have hcovG : (⨆ i, Subfunctor.range (jj i).hom).sheafify
      (BigFppfOver.topology B S hS) = ⊤ :=
    sheafify_iSup_range_hom_of_isColimit B S hS jj hcoprod
  refine ⟨fun {W} s => ?_⟩
  -- the sieve on which `s` lies in one of the summands
  refine (BigFppfOver.topology B S hS).transitive
    (sieveOfSection_iSup_range_mem B S hS (fun i => (jj i).hom) hcovG (U := op W) s) _ ?_
  rintro W' g hg
  have hg' : G.obj.map g.op s ∈ (⨆ i, Subfunctor.range (jj i).hom).obj (op W') := hg
  rw [Subfunctor.iSup_obj] at hg'
  obtain ⟨i, y, hy⟩ : ∃ i, ∃ y, ((jj i).hom).app (op W') y = G.obj.map g.op s := by
    simpa using hg'
  rw [CategoryTheory.Presheaf.pullback_imageSieve, ← hy]
  -- on that summand, refine by the sieve on which the section lifts along the chart
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (CategoryTheory.Presheaf.imageSieve_mem (f := aᵢ i)
      (BigFppfOver.topology B S hS) (U := op W') y)
  rintro W'' h ⟨z, hz⟩
  refine ⟨(rᵢ i).app (op W'') z, ?_⟩
  have h1 : f.app (op W'') ((rᵢ i).app (op W'') z) = ((jj i).hom).app (op W'')
      ((aᵢ i).app (op W'') z) := by
    simpa using ConcreteCategory.congr_hom (NatTrans.congr_app (hfac i) (op W'')) z
  rw [h1, hz]
  exact NatTrans.naturality_apply (jj i).hom h.op y

/-! ### The atlas of a coproduct -/

/-- **The coproduct of charts of the members is a chart of the coproduct.** Let `G` be the
coproduct of the fppf sheaves `Fᵢ`, let `aᵢ : yoneda.obj Uᵢ ⟶ Fᵢ` be surjective étale, and
suppose -- this is the hypothesis the source states -- that the coproduct of the schemes
underlying the `Uᵢ` lies in the site. If the diagonal of `G` is representable, then `G` admits
a surjective étale scheme atlas.

Representability of the diagonal is an input rather than a conclusion because the atlas clause
of `AlgebraicGeometry.IsAlgebraicSpace` tests surjectivity and étaleness after every
representable base change, so the atlas must first be known to be relatively representable; for
a morphism out of a representable that is exactly what a representable diagonal supplies. No
bound on the size of the index type is used. -/
theorem exists_atlas_of_isColimit_of_contains
    {I : Type u} {Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (jj : ∀ i, Fᵢ i ⟶ G) (hcoprod : IsColimit (Cofan.mk G jj))
    (Uᵢ : I → BigFppfOver B S hS) (aᵢ : ∀ i, yoneda.obj (Uᵢ i) ⟶ (Fᵢ i).obj)
    (hsurjᵢ : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (aᵢ i))
    (hetᵢ : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (aᵢ i))
    (hsum : B.Contains (∐ fun i => (BigFppfOver.toScheme B S hS).obj (Uᵢ i)))
    (hdiag : yoneda.relativelyRepresentable (diag G.obj)) :
    ∃ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ G.obj),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f := by
  classical
  let _ : (BigFppfOver.topology B S hS).Subcanonical := BigFppfOver.subcanonical B S hS
  set U : BigFppfOver B S hS := BigFppfOver.sigmaOver B S hS Uᵢ hsum with hU
  set inj : ∀ i, Uᵢ i ⟶ U := fun i => BigFppfOver.sigmaOverInj B S hS Uᵢ hsum i with hinj
  have hcolS : IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj U)
      (fun i => (BigFppfOver.toScheme B S hS).map (inj i))) :=
    BigFppfOver.isColimit_toScheme_sigmaOver B S hS Uᵢ hsum
  have hcolY : IsColimit (Cofan.mk ((BigFppfOver.topology B S hS).yoneda.obj U)
      (fun i => (BigFppfOver.topology B S hS).yoneda.map (inj i))) :=
    isColimit_yoneda_of_isColimit_toScheme B S hS Uᵢ U inj hcolS
  -- the atlas, assembled from the charts of the members
  set fam : ∀ i, (BigFppfOver.topology B S hS).yoneda.obj (Uᵢ i) ⟶ G :=
    fun i => (⟨aᵢ i⟩ : (BigFppfOver.topology B S hS).yoneda.obj (Uᵢ i) ⟶ Fᵢ i) ≫ jj i with hfam
  set fs : (BigFppfOver.topology B S hS).yoneda.obj U ⟶ G :=
    hcolY.desc (Cofan.mk G fam) with hfs
  set f : yoneda.obj U ⟶ G.obj := fs.hom with hf
  have hfac : ∀ i, yoneda.map (inj i) ≫ f = aᵢ i ≫ (jj i).hom := by
    intro i
    have h := hcolY.fac (Cofan.mk G fam) ⟨i⟩
    exact congrArg (fun φ => φ.hom) h
  -- the atlas is relatively representable, because the diagonal is
  have hrep : yoneda.relativelyRepresentable f :=
    Functor.relativelyRepresentable.of_diag hdiag f
  have hopeninj : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (inj i)) :=
    fun i => isOpenImmersion_of_isColimit_cofanMk hcolS i
  refine ⟨U, f, ?_, ?_⟩
  · -- surjective, because the atlas is locally surjective and relatively representable
    have hlsᵢ : ∀ i, CategoryTheory.Presheaf.IsLocallySurjective
        (BigFppfOver.topology B S hS) (aᵢ i) := fun i =>
      isLocallySurjective_of_presheaf_surjective_etale B S hS (hsurjᵢ i) (hetᵢ i)
    have hls : CategoryTheory.Presheaf.IsLocallySurjective
        (BigFppfOver.topology B S hS) f :=
      isLocallySurjective_of_isColimit_of_fac B S hS jj hcoprod f aᵢ hlsᵢ
        (fun i => yoneda.map (inj i)) hfac
    exact presheaf_surjective_of_isLocallySurjective B S hS hrep hls
  · -- étale, by locality at the source along the cover of `U` by the summands
    have _ : IsZariskiLocalAtSource (@_root_.AlgebraicGeometry.Etale.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource
        (P := @_root_.AlgebraicGeometry.Etale.{u}) (Q := RingHom.Etale)
    have _ := isStableUnderComposition_presheaf_inverseImage B S hS
      (@_root_.AlgebraicGeometry.Etale.{u})
    have hle : openImmersionOver B S hS ≤ MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Etale.{u}) (BigFppfOver.toScheme B S hS) := by
      intro X Y k hk
      have _ : _root_.AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map k) := hk
      change _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k)
      infer_instance
    refine presheaf_inverseImage_of_isZariskiLocalAtSource B S hS
      (@_root_.AlgebraicGeometry.Etale.{u}) hrep inj hopeninj
      (exists_mem_range_of_isColimit_cofanMk hcolS) ?_
    intro i
    rw [hfac i]
    exact MorphismProperty.comp_mem _ _ _ (hetᵢ i)
      (MorphismProperty.relative_monotone hle _
        (isOpenImmersion_coproductInj B S hS I Fᵢ G jj hcoprod i))

/-! ### The diagonal, and the theorem -/

/-- **A coproduct of algebraic spaces has a representable diagonal.** This is the general
glueing theorem `AlgebraicGeometry.Space.relativelyRepresentable_diag_of_openCover` of
Stacks 02WR applied to the identity of the coproduct: a coproduct is covered by its own
summands, which are attached through representable open immersions. -/
theorem relativelyRepresentable_diag_of_isColimit
    {I : Type u} (hI : #I < B.cutoff.ord.cof)
    {Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (hFᵢ : ∀ i, IsAlgebraicSpace B S hS (Fᵢ i).obj)
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (jj : ∀ i, Fᵢ i ⟶ G) (hcoprod : IsColimit (Cofan.mk G jj)) :
    yoneda.relativelyRepresentable (diag G.obj) := by
  refine relativelyRepresentable_diag_of_openCover B S hS G.property hI hFᵢ jj hcoprod
    (𝟙 G.obj) (fun i => ?_) inferInstance
  rw [Category.comp_id]
  exact isOpenImmersion_coproductInj B S hS I Fᵢ G jj hcoprod i

/-- **A coproduct of algebraic spaces is an algebraic space**, when the index type is smaller
than the cofinality of the site's size cutoff.

This is not the hypothesis of Stacks 02WQ, which asks instead that the coproduct of a choice of
charts of the members be an object of the site, and that is the weaker of the two conditions.
What is available under the source's own hypothesis is the atlas clause alone,
`AlgebraicGeometry.Space.exists_atlas_of_isColimit_of_contains`; the diagonal clause is what
consumes the bound on the index type. -/
theorem isAlgebraicSpace_of_isColimit
    {I : Type u} (hI : #I < B.cutoff.ord.cof)
    {Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (hFᵢ : ∀ i, IsAlgebraicSpace B S hS (Fᵢ i).obj)
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (jj : ∀ i, Fᵢ i ⟶ G) (hcoprod : IsColimit (Cofan.mk G jj)) :
    IsAlgebraicSpace B S hS G.obj := by
  classical
  choose Uᵢ aᵢ hsurjᵢ hetᵢ using fun i => (hFᵢ i).exists_atlas
  have hdiag : yoneda.relativelyRepresentable (diag G.obj) :=
    relativelyRepresentable_diag_of_isColimit B S hS hI hFᵢ jj hcoprod
  have hsum : B.Contains (∐ fun i => (BigFppfOver.toScheme B S hS).obj (Uᵢ i)) :=
    B.contains_sigma_of_lt_cof hI _ fun i => (Uᵢ i).left.2
  exact ⟨G.property, hdiag, exists_atlas_of_isColimit_of_contains B S hS jj hcoprod Uᵢ aᵢ
    hsurjᵢ hetᵢ hsum hdiag⟩

/-! ### Non-vacuity -/

/-- **The hypotheses of `AlgebraicGeometry.Space.isAlgebraicSpace_of_isColimit` are
satisfiable, at every at most countable index type and with arbitrary summands.** For any at
most countable family `Uᵢ` of objects of the site, the representable sheaves they carry are
algebraic spaces and their coproduct in the site exists, so the theorem applies and identifies
the representable sheaf of `∐ᵢ Uᵢ` as an algebraic space.

This rules out the possibility that the theorem is satisfied only emptily. The index type is
not required to be empty and the summands are not required to be initial: taking `I` a
two-element type and the `Uᵢ` two copies of the base gives two summands whose underlying
scheme is `S`, which is nonempty whenever `S` is. -/
theorem isAlgebraicSpace_yoneda_sigmaOver_of_countable {I : Type u} (hI : #I ≤ ℵ₀)
    (Uᵢ : I → BigFppfOver B S hS) :
    IsAlgebraicSpace B S hS (yoneda.obj (BigFppfOver.sigmaOver B S hS Uᵢ
      (B.contains_sigma_of_lt_cof (lt_of_le_of_lt hI B.aleph0_lt_cutoff_cof) _
        fun i => (Uᵢ i).left.2))) := by
  let _ : (BigFppfOver.topology B S hS).Subcanonical := BigFppfOver.subcanonical B S hS
  exact isAlgebraicSpace_of_isColimit B S hS (lt_of_le_of_lt hI B.aleph0_lt_cutoff_cof)
    (fun i => isAlgebraicSpace_yoneda B S hS (Uᵢ i))
    (fun i => (BigFppfOver.topology B S hS).yoneda.map
      (BigFppfOver.sigmaOverInj B S hS Uᵢ
        (B.contains_sigma_of_lt_cof (lt_of_le_of_lt hI B.aleph0_lt_cutoff_cof) _
          fun i => (Uᵢ i).left.2) i))
    (isColimit_yoneda_sigmaOver_of_countable B S hS hI Uᵢ)

/-- **The two-summand witness.** The base, viewed as an object of the site over itself, has
underlying scheme `S`. Feeding the constant family at this object on a two-element index type
to `AlgebraicGeometry.Space.isAlgebraicSpace_yoneda_sigmaOver_of_countable` therefore exhibits
a coproduct of two summands which are nonempty whenever the base is. -/
theorem toScheme_obj_terminalOver :
    (BigFppfOver.toScheme B S hS).obj (Over.mk (𝟙 (B.obj hS))) = S :=
  rfl

end AlgebraicGeometry.Space

end
