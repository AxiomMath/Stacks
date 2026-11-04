module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardAlgebraFunctorFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecBounded
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.EnlargementAboveCardinal

/-!
# Stacks 081W: the relative spectrum of an arbitrary quasi-coherent algebra

Let `X` be an algebraic space over a scheme `S` and `𝒜` a quasi-coherent sheaf of
`𝒪_X`-algebras. Stacks 081W defines the relative spectrum `\underline{Spec}_X(𝒜) ⟶ X` as the
affine morphism corresponding to `𝒜` under the anti-equivalence of Stacks 081V. This file
constructs it for **every** quasi-coherent `𝒜`, with no hypothesis.

## Where the relative spectrum lives

In this development algebraic spaces over `S` are sheaves on a big fppf site `B`, a category of
schemes cut out by a cardinal `B.cutoff`, while the sections of a sheaf of algebras on the small
étale site of `X` are arbitrary. A direct image `π_* 𝒪_Y` of an algebraic space `Y` affine over
`X` *in the same site* has fewer than `B.cutoff` sections over every étale chart, and an algebra
with at least that many sections over a chart is the direct image of no such `Y`:
`AlgebraicGeometry.Space.not_essSurj_affinePushforwardAlgebraFunctor_of_cutoff_le_mk_sections`,
with such algebras supplied by
`AlgebraicGeometry.Space.exists_quasicoherentAlgebra_cutoff_le_mk_sections`. So
`\underline{Spec}_X(𝒜)` cannot in general be an algebraic space of `B`.

It is an algebraic space of a larger big fppf site, as Stacks itself arranges (Stacks 03FO: "we
can always enlarge the big site at will"). The sections of `𝒜` over the étale charts of `X` are
`u`-small types and the small étale site of `X` is essentially small, so their cardinalities are
bounded by a single cardinal `AlgebraicGeometry.Space.AlgebraSheaf.sectionsBound 𝒜` of the
universe `u` (the essentially-small argument), and `B` is contained in a big fppf site `B'` whose
cutoff exceeds it (`AlgebraicGeometry.BigFppfSite.exists_isContained_lt_cutoff`). Over `B'`:

* `X` becomes the algebraic space `X'` of Stacks 03FP (`AlgebraicGeometry.changeBigSite`), whose
  small étale site contains that of `X` as a cocontinuous dense subsite
  (`AlgebraicGeometry.Space.changeBigSiteSmallEtale_isDenseSubsite`);
* `𝒜` becomes the quasi-coherent `𝒪_{X'}`-algebra `𝒜'` of the Comparison Lemma
  (`AlgebraicGeometry.Space.AlgebraSheaf.changeBigSiteExtend`), whose sections over the charts of
  `X` are those of `𝒜` (`AlgebraicGeometry.Space.AlgebraSheaf.changeBigSiteRestrictExtendIso`),
  and which has fewer than `B'.cutoff` sections over every chart of `X'`;

and `\underline{Spec}_X(𝒜)` is the algebraic space affine over `X'` corresponding to `𝒜'` under
Stacks 081V over `B'`, that is `AlgebraicGeometry.Space.boundedRelativeSpec` over `B'`.

## Main definitions

* `AlgebraicGeometry.Space.relativeSpectrumSite`: the enlarged big fppf site `B'`.
* `AlgebraicGeometry.Space.relativeSpectrumBase`: the algebraic space `X'` over `B'`.
* `AlgebraicGeometry.Space.relativeSpectrumAlgebra`: the quasi-coherent `𝒪_{X'}`-algebra `𝒜'`.
* `AlgebraicGeometry.Space.relativeSpectrum`: **Stacks 081W**, `\underline{Spec}_X(𝒜) ⟶ X'`.

## Main results

* `AlgebraicGeometry.Space.pushforwardAlgebraRelativeSpectrumIso`: its direct image is `𝒜'`.
* `AlgebraicGeometry.Space.existsUnique_iso_relativeSpectrum`: it is the object corresponding to
  `𝒜'`, up to unique isomorphism compatible with the direct images.
* `AlgebraicGeometry.Space.relativeSpectrumRestrictIso`: its direct image, read on the étale
  charts of `X`, is `𝒜` itself.

When `𝒜` is bounded, so that its relative spectrum already exists inside the site of `X`
(`AlgebraicGeometry.Space.boundedRelativeSpec`), the two agree:
`AlgebraicGeometry.Space.nonempty_iso_changeBigSite_boundedRelativeSpec` of
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpectrumBoundedCase`.

## References

* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03FO](https://stacks.math.columbia.edu/tag/03FO)
* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

/-! ### A bound on the sections of a sheaf of algebras -/

namespace AlgebraSheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **A cardinal bounding the sections of a sheaf of algebras over every étale chart.** The small
étale site is essentially small, so a sum over a small model of it is a cardinal of the universe
of the schemes. -/
def sectionsBound (A : AlgebraSheaf.{u, u} B S hS F hF) : Cardinal.{u} :=
  Cardinal.sum fun V : SmallModel.{u} (SmallEtale B S hS F) =>
    #(A.right.obj.obj (op ((equivSmallModel.{u} (SmallEtale B S hS F)).inverse.obj V)))

/-- The sections of `A` over any étale chart `V` have cardinality at most `A.sectionsBound`. -/
theorem mk_sections_le_sectionsBound (A : AlgebraSheaf.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F) : #(A.right.obj.obj (op V)) ≤ A.sectionsBound := by
  let e := equivSmallModel.{u} (SmallEtale B S hS F)
  exact (Cardinal.mk_congr ((CategoryTheory.forget CommRingCat).mapIso
    (A.right.obj.mapIso (e.unitIso.app V).op.symm)).toEquiv).trans_le
    (Cardinal.le_sum _ (e.functor.obj V))

end AlgebraSheaf

/-! ### The size of the extension of an algebra to an enlarged site -/

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **The extension of an algebra to an enlarged site has fewer sections than the larger cutoff**,
as soon as the sections of the algebra are bounded below it. A chart of `X'` is covered by
transported charts of `X` indexed by fewer than `B'.cutoff` elements
(`AlgebraicGeometry.Space.exists_ofArrows_mem_changeBigSiteSmallEtale`), its sections inject
into the product of the sections over those, which are sections of the algebra, and the cutoff of
`B'` is a strong limit. -/
theorem sectionsBelowCutoff_changeBigSiteExtend (A : AlgebraSheaf.{u, u} B S hS X.obj X.property)
    (hA : A.sectionsBound < B'.cutoff) :
    AlgebraSheaf.SectionsBelowCutoff B' S (BigFppfSite.contains_of_isContained h hS)
      (X := (changeBigSite B B' h S hS).obj X)
      (AlgebraSheaf.changeBigSiteExtend B B' h S hS X A) := by
  intro V
  let A' := AlgebraSheaf.changeBigSiteExtend B B' h S hS X A
  let G := changeBigSiteSmallEtale B B' h S hS X
  obtain ⟨ι, Y, f, hι, hf⟩ := exists_ofArrows_mem_changeBigSiteSmallEtale B B' h S hS X V
  let Φ : A'.right.obj.obj (op V) → ∀ k, A'.right.obj.obj (op (G.obj (Y k))) :=
    fun a k => A'.right.obj.map (f k).op a
  have hΦ : Function.Injective Φ := by
    intro a b hab
    refine A'.right.cond.isSeparated V _ hf a b fun Z g hg => ?_
    obtain ⟨k, l, rfl⟩ := Sieve.ofArrows.exists hg
    have hk := congrFun hab k
    simp only [Φ] at hk
    simp only [op_comp, Functor.map_comp, CommRingCat.comp_apply, hk]
  have hY (k : ι) : #(A'.right.obj.obj (op (G.obj (Y k)))) ≤ A.sectionsBound :=
    (Cardinal.mk_congr ((AlgebraSheaf.forget ⋙ sheafToPresheaf _ _ ⋙
      (evaluation _ _).obj (op (Y k)) ⋙ CategoryTheory.forget CommRingCat.{u}).mapIso
        (AlgebraSheaf.changeBigSiteRestrictExtendIso B B' h S hS X A)).toEquiv).trans_le
      (A.mk_sections_le_sectionsBound (Y k))
  calc #(A'.right.obj.obj (op V))
      ≤ #(∀ k, A'.right.obj.obj (op (G.obj (Y k)))) := Cardinal.mk_le_of_injective hΦ
    _ = Cardinal.prod fun k => #(A'.right.obj.obj (op (G.obj (Y k)))) := Cardinal.mk_pi _
    _ ≤ Cardinal.prod fun _ : ι => A.sectionsBound := Cardinal.prod_le_prod _ _ hY
    _ = A.sectionsBound ^ #ι := Cardinal.prod_const' _ _
    _ < B'.cutoff := Cardinal.power_lt_of_isStrongPrelimit B'.aleph0_lt_cutoff
        B'.cutoff_isStrongPrelimit hA hι

/-! ### The relative spectrum -/

variable {B S hS X}

/-- **The big fppf site on which `\underline{Spec}_X(𝒜)` lives**: a big fppf site containing `B`
whose cutoff exceeds the cardinality of the sections of `𝒜` over every étale chart of `X`
(`AlgebraicGeometry.Space.AlgebraSheaf.sectionsBound`). -/
def relativeSpectrumSite (A : QuasicoherentAlgebra B S hS X) : BigFppfSite.{u} :=
  Classical.choose (BigFppfSite.exists_isContained_lt_cutoff B A.obj.sectionsBound)

/-- The site `B` is contained in `relativeSpectrumSite A`. -/
theorem isContained_relativeSpectrumSite (A : QuasicoherentAlgebra B S hS X) :
    IsContained (τ := .fppf) B (relativeSpectrumSite A) :=
  (Classical.choose_spec (BigFppfSite.exists_isContained_lt_cutoff B A.obj.sectionsBound)).1

/-- The cutoff of `relativeSpectrumSite A` exceeds `A.obj.sectionsBound`. -/
theorem sectionsBound_lt_relativeSpectrumSite_cutoff (A : QuasicoherentAlgebra B S hS X) :
    A.obj.sectionsBound < (relativeSpectrumSite A).cutoff :=
  (Classical.choose_spec (BigFppfSite.exists_isContained_lt_cutoff B A.obj.sectionsBound)).2

/-- The base scheme `S` belongs to the enlarged site. -/
theorem contains_relativeSpectrumSite (A : QuasicoherentAlgebra B S hS X) :
    (relativeSpectrumSite A).Contains S :=
  BigFppfSite.contains_of_isContained (isContained_relativeSpectrumSite A) hS

/-- **`X` over the enlarged site**: the algebraic space of Stacks 03FP attached to `X`. -/
abbrev relativeSpectrumBase (A : QuasicoherentAlgebra B S hS X) :
    AlgebraicSpaces (relativeSpectrumSite A) S (contains_relativeSpectrumSite A) :=
  (changeBigSite B (relativeSpectrumSite A) (isContained_relativeSpectrumSite A) S hS).obj X

/-- **`𝒜` over the enlarged site**: the quasi-coherent `𝒪_{X'}`-algebra of the Comparison Lemma,
whose sections over the étale charts of `X` are those of `𝒜`. -/
def relativeSpectrumAlgebra (A : QuasicoherentAlgebra B S hS X) :
    QuasicoherentAlgebra (relativeSpectrumSite A) S (contains_relativeSpectrumSite A)
      (relativeSpectrumBase A) :=
  ⟨AlgebraSheaf.changeBigSiteExtend B (relativeSpectrumSite A) (isContained_relativeSpectrumSite A)
      S hS X A.obj,
    AlgebraSheaf.isQuasicoherent_changeBigSiteExtend B (relativeSpectrumSite A)
      (isContained_relativeSpectrumSite A) S hS X A.obj A.property⟩

/-- `𝒜` over the enlarged site has fewer sections than its cutoff over every étale chart. -/
theorem sectionsBelowCutoff_relativeSpectrumAlgebra (A : QuasicoherentAlgebra B S hS X) :
    AlgebraSheaf.SectionsBelowCutoff (relativeSpectrumSite A) S (contains_relativeSpectrumSite A)
      (relativeSpectrumAlgebra A).obj :=
  sectionsBelowCutoff_changeBigSiteExtend B (relativeSpectrumSite A)
    (isContained_relativeSpectrumSite A) S hS X A.obj
    (sectionsBound_lt_relativeSpectrumSite_cutoff A)

/-- **Stacks 081W.** The relative spectrum `\underline{Spec}_X(𝒜)` of an arbitrary quasi-coherent
sheaf of `𝒪_X`-algebras `𝒜` on an algebraic space `X`: the algebraic space affine over `X`
corresponding to `𝒜` under the anti-equivalence of Stacks 081V.

**Where it lives.** It is an algebraic space of the big fppf site
`AlgebraicGeometry.Space.relativeSpectrumSite 𝒜`, a big fppf site containing the site `B` of `X`,
and it is affine over `AlgebraicGeometry.Space.relativeSpectrumBase 𝒜`, which is `X` read in that
site (Stacks 03FP, `AlgebraicGeometry.changeBigSite`). It cannot in general live in `B` itself:
an algebra with at least `B.cutoff` sections over an étale chart is the direct image of no
algebraic space of `B` affine over `X`
(`AlgebraicGeometry.Space.not_essSurj_affinePushforwardAlgebraFunctor_of_cutoff_le_mk_sections`,
`AlgebraicGeometry.Space.exists_quasicoherentAlgebra_cutoff_le_mk_sections`), so the site is
enlarged, as Stacks 03FO allows, past the cardinality of the sections of `𝒜`.

**What it is.** It is the object of Stacks 081V over the enlarged site corresponding to
`AlgebraicGeometry.Space.relativeSpectrumAlgebra 𝒜`, which is `𝒜` read on the small étale site of
`X` enlarged (its sections over the charts of `X` are those of `𝒜`,
`AlgebraicGeometry.Space.relativeSpectrumRestrictIso`): its direct image is that algebra
(`AlgebraicGeometry.Space.pushforwardAlgebraRelativeSpectrumIso`) and it is unique up to unique
isomorphism with that property (`AlgebraicGeometry.Space.existsUnique_iso_relativeSpectrum`).
When `𝒜` is bounded it is the relative spectrum `AlgebraicGeometry.Space.boundedRelativeSpec`
built inside the site of `X`, read in the enlarged site
(`AlgebraicGeometry.Space.nonempty_iso_changeBigSite_boundedRelativeSpec`).

No hypothesis is placed on `𝒜` beyond quasi-coherence. -/
@[stacks 081W "the relative spectrum Spec_X(A) of an arbitrary quasi-coherent O_X-algebra A on \
an algebraic space X, with no further hypothesis: the algebraic space affine over X corresponding \
to A under 081V. It lives on an enlargement relativeSpectrumSite A of the big fppf site of X \
(Stacks 03FO; necessary, since an algebra with at least B.cutoff sections over a chart is the \
direct image of no space affine over X in the same site: \
not_essSurj_affinePushforwardAlgebraFunctor_of_cutoff_le_mk_sections), over X read there by 03FP; \
its direct image is A read there (pushforwardAlgebraRelativeSpectrumIso, \
relativeSpectrumRestrictIso) \
and it is unique up to unique isomorphism with that property (existsUnique_iso_relativeSpectrum)"]
def relativeSpectrum (A : QuasicoherentAlgebra B S hS X) :
    AffineOver (relativeSpectrumSite A) S (contains_relativeSpectrumSite A)
      (relativeSpectrumBase A) :=
  boundedRelativeSpec (relativeSpectrumSite A) S (contains_relativeSpectrumSite A)
    (relativeSpectrumAlgebra A) (sectionsBelowCutoff_relativeSpectrumAlgebra A)

/-- **The direct image of the structure sheaf of `\underline{Spec}_X(𝒜)` is `𝒜`**, read over the
enlarged site. -/
def pushforwardAlgebraRelativeSpectrumIso (A : QuasicoherentAlgebra B S hS X) :
    pushforwardAlgebra (relativeSpectrumSite A) S (contains_relativeSpectrumSite A)
        (relativeSpectrum A).obj ≅ (relativeSpectrumAlgebra A).obj :=
  pushforwardAlgebraBoundedRelativeSpecIso (relativeSpectrumSite A) S
    (contains_relativeSpectrumSite A) (relativeSpectrumAlgebra A)
    (sectionsBelowCutoff_relativeSpectrumAlgebra A)

/-- **On the étale charts of `X`, the direct image of the structure sheaf of
`\underline{Spec}_X(𝒜)` is `𝒜` itself**: restricted to the transported charts of `X`, the direct
image is `𝒜`. -/
def relativeSpectrumRestrictIso (A : QuasicoherentAlgebra B S hS X) :
    AlgebraSheaf.changeBigSiteRestrict B (relativeSpectrumSite A)
        (isContained_relativeSpectrumSite A) S hS X
        (pushforwardAlgebra (relativeSpectrumSite A) S (contains_relativeSpectrumSite A)
          (relativeSpectrum A).obj) ≅ A.obj :=
  (AlgebraSheaf.changeBigSiteRestrictFunctor B (relativeSpectrumSite A)
      (isContained_relativeSpectrumSite A) S hS X).mapIso
      (pushforwardAlgebraRelativeSpectrumIso A) ≪≫
    AlgebraSheaf.changeBigSiteRestrictExtendIso B (relativeSpectrumSite A)
      (isContained_relativeSpectrumSite A) S hS X A.obj

/-- The identification of the direct image of `\underline{Spec}_X(𝒜)` with `𝒜` over the
enlarged site, as an isomorphism of quasi-coherent algebras. -/
def quasicoherentPushforwardAlgebraRelativeSpectrumIso (A : QuasicoherentAlgebra B S hS X) :
    (quasicoherentPushforwardAlgebraFunctor (relativeSpectrumSite A) S
        (contains_relativeSpectrumSite A) (relativeSpectrumBase A)).obj (op (relativeSpectrum A)) ≅
      relativeSpectrumAlgebra A :=
  (quasicoherentAlgebraInclusion (relativeSpectrumSite A) S (contains_relativeSpectrumSite A)
    (relativeSpectrumBase A)).preimageIso (pushforwardAlgebraRelativeSpectrumIso A)

/-- **`\underline{Spec}_X(𝒜)` is the object corresponding to `𝒜`, up to unique isomorphism.** An
algebraic space `Y` affine over `X'` with an identification `e` of its direct image with `𝒜` is
isomorphic to `\underline{Spec}_X(𝒜)` over `X'` by exactly one isomorphism carrying `e` to the
canonical identification: the direct image is fully faithful on spaces affine over `X'`
(Stacks 081V). -/
theorem existsUnique_iso_relativeSpectrum (A : QuasicoherentAlgebra B S hS X)
    (Y : AffineOver (relativeSpectrumSite A) S (contains_relativeSpectrumSite A)
      (relativeSpectrumBase A))
    (e : (quasicoherentPushforwardAlgebraFunctor (relativeSpectrumSite A) S
        (contains_relativeSpectrumSite A) (relativeSpectrumBase A)).obj (op Y) ≅
      relativeSpectrumAlgebra A) :
    ∃! φ : Y ≅ relativeSpectrum A,
      (quasicoherentPushforwardAlgebraFunctor (relativeSpectrumSite A) S
          (contains_relativeSpectrumSite A) (relativeSpectrumBase A)).map φ.hom.op ≫ e.hom =
        (quasicoherentPushforwardAlgebraRelativeSpectrumIso A).hom := by
  let F := quasicoherentPushforwardAlgebraFunctor (relativeSpectrumSite A) S
    (contains_relativeSpectrumSite A) (relativeSpectrumBase A)
  have := full_affinePushforwardAlgebraFunctor (relativeSpectrumSite A) S
    (contains_relativeSpectrumSite A) (relativeSpectrumBase A)
  have := faithful_affinePushforwardAlgebraFunctor (relativeSpectrumSite A) S
    (contains_relativeSpectrumSite A) (relativeSpectrumBase A)
  let c := quasicoherentPushforwardAlgebraRelativeSpectrumIso A
  refine ⟨(F.preimageIso (c ≪≫ e.symm)).unop, ?_, fun ψ hψ => ?_⟩
  · show F.map (F.preimageIso (c ≪≫ e.symm)).hom ≫ e.hom = c.hom
    simp
  · apply Iso.ext
    apply Quiver.Hom.op_inj
    apply F.map_injective
    have h1 : F.map ψ.hom.op = c.hom ≫ e.inv := by
      rw [← hψ]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rfl
    show F.map ψ.hom.op = F.map (F.preimageIso (c ≪≫ e.symm)).hom
    rw [h1]
    simp

end AlgebraicGeometry.Space

end
