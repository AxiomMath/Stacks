module

public import StacksFrontier.AlgebraicGeometry.ProEtale.AppProetaleAlgebras
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.AbelianDirectImageFullyFaithful
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.ClosedFibreVanishing
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.WContractibleCoverCardinality
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.WContractibleLocalization
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ClopenRefinement
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.SmallSiteSheafificationSections
public import StacksFrontier.AlgebraicGeometry.Properties.ClosedSubsetIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ProetaleComparison
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero and a closed subscheme on the small pro-étale site

Let `X` be a scheme, let `Z ⊂ X` be a closed subscheme with inclusion `i : Z ⟶ X`, and let
`j : U ⟶ X` be the inclusion of the complementary open subscheme. For an abelian sheaf `F` on
the small pro-étale site of `X`, the counit of `j_! ⊣ j^{-1}` and the unit of `i^{-1} ⊣ i_*`
are the two canonical maps of
`0 → j_! j^{-1} F → F → i_* i^{-1} F → 0`
and they compose to zero, so that they form a short complex on `X_proétale`.

## Main definitions

* `AlgebraicGeometry.ProEtale.Abelian.proetaleDirectImage` is the direct image `i_*` of abelian
  pro-étale sheaves along an arbitrary morphism of schemes, namely restriction along pro-étale
  base change.
* `AlgebraicGeometry.ProEtale.Abelian.proetaleInverseImage` is the inverse image `i^{-1}`, the
  sheafified left Kan extension along pro-étale base change.
* `AlgebraicGeometry.ProEtale.Abelian.proetaleInverseImageDirectImageAdj` is the adjunction
  `i^{-1} ⊣ i_*`.
* `AlgebraicGeometry.ProEtale.openClosedShortComplex` is the short complex
  `j_! j^{-1} F ⟶ F ⟶ i_* i^{-1} F` of the tag.

## Main results

* `AlgebraicGeometry.ProEtale.isZero_proetaleRestriction_proetaleDirectImage`: restricting to
  `U` a direct image from `Z` gives zero.
* `AlgebraicGeometry.ProEtale.isZero_proetaleInverseImage_extensionByZero`: the inverse image
  to `Z` of an extension by zero from `U` is zero.
* `AlgebraicGeometry.ProEtale.extensionByZero_counit_comp_proetaleInverseImage_unit`: the two
  canonical maps of the tag compose to zero.
* `AlgebraicGeometry.ProEtale.shortExact_map_proetaleRestriction`: the short complex is short
  exact over the open part `U`.
* `AlgebraicGeometry.ProEtale.shortExact_map_proetaleInverseImage_of_isAffine`: it is short
  exact over the closed part `Z`, with nothing assumed, for a closed immersion of affine
  schemes. The same conclusion under full faithfulness of `i_*` as a hypothesis is
  `AlgebraicGeometry.ProEtale.shortExact_map_proetaleInverseImage`.
* `AlgebraicGeometry.ProEtale.hasEnoughObjects_isAffine_isWeaklyContractible`: **Stacks 0990**
  for the unrestricted small pro-étale site — every object is covered by affine weakly
  contractible ones.
* `AlgebraicGeometry.ProEtale.hasEnoughObjects_openPart_or_closedFibre`: the geometric reduction
  of the source's proof of the tag. Quasi-compactness of `j` makes the closed fibre of an affine
  object of `X_proétale` cut out by finitely many equations, and the resulting ind-Zariski
  localization of [Stacks, Tag 096V](https://stacks.math.columbia.edu/tag/096V) splits every
  affine weakly contractible object into a part lying over `U` and a part all of whose points
  specialize into the closed fibre.
* `AlgebraicGeometry.ProEtale.shortExact_of_hasEnoughObjects`: short exactness of a short
  complex of sheaves is tested on sections over a covering family of objects.
* `AlgebraicGeometry.ProEtale.shortExact_openClosedShortComplex_of_isIso_unit_app`: short
  exactness of the short complex on `X_proétale` itself, at the source's hypotheses, from the
  single remaining input described below.
* `AlgebraicGeometry.ProEtale.shortExact_map_proetaleInverseImage_of_isIso_unit_app`: the same
  input gives short exactness over the closed part `Z` for an arbitrary `X`, so the affineness
  of `shortExact_map_proetaleInverseImage_of_isAffine` is not part of the tag either.

## What is proved and what is not

[Stacks, Tag 09AH](https://stacks.math.columbia.edu/tag/09AH) asserts that the two canonical
maps form a *short exact* sequence when `j` is quasi-compact. This file constructs the two maps,
proves that they form a short complex, proves that the short complex is short exact over `U`,
proves that it is short exact over `Z` when `X` and `Z` are affine, and carries out the source's
own proof of short exactness on `X_proétale` down to one input:
`shortExact_openClosedShortComplex_of_isIso_unit_app` is the tag's conclusion, at the source's
hypotheses — `i` a closed immersion, `j` the complementary open immersion, `j` quasi-compact —
assuming only that

> the unit `F ⟶ i_* i^{-1} F` is invertible on sections over every object of `X_proétale` which
> is affine, weakly contractible, and all of whose points specialize into its closed fibre.

That assumption is exactly [Stacks, Tag 09AC](https://stacks.math.columbia.edu/tag/09AC) for the
site of `AlgebraicGeometry.Scheme.ProEt`, in the form in which the source uses it. It is not
proved in this file; it is `AlgebraicGeometry.ProEtale.isIso_proetaleUnit_app_of_specializes`,
and the resulting unconditional short exactness on `X_proétale` is
`AlgebraicGeometry.ProEtale.shortExact_openClosedShortComplex`.

What the source's proof needs, and where each piece now stands:

1. Enough affine weakly contractible objects, Stacks 0990 — proved here as
   `hasEnoughObjects_isAffine_isWeaklyContractible`, from
   `AlgebraicGeometry.ProEtale.exists_small_faithfullyFlat_ind_etale_wContractible` and the
   clopen-refinement criterion of [Stacks, Tag 098H](https://stacks.math.columbia.edu/tag/098H).
2. The ind-Zariski cover that quasi-compactness of `j` produces, Stacks 096V — proved here as
   `hasEnoughObjects_openPart_or_closedFibre`, using
   `AlgebraicGeometry.exists_fg_ideal_zeroLocus_eq_inter` for the finitely generated ideal and
   `AlgebraicGeometry.ProEtale.isWContractible_localizationRing` for w-contractibility of the
   localization along the closed fibre.
3. Vanishing of `j_!` on an object all of whose points specialize into the closed fibre,
   Stacks 09AG — already available as
   `AlgebraicGeometry.ProEtale.isZero_extensionByZero_sections_of_specializes_to_closed`.
4. `i^{-1}F(V ×_X Z) = F(V)` on such an object, Stacks 09AC, *via the unit of the adjunction* —
   the missing input. Two separate things stand between it and what the library has.

   The nearest statement,
   `AlgebraicGeometry.ProEtale.abelianProetaleInverseImage_sections_iso_closedFibre`, is an
   abstract natural isomorphism of the two section functors and not invertibility of the unit.
   The one does not give the other: a natural isomorphism `Λ ≅ Γ_V` together with the unit
   `Γ_V ⟹ Λ` makes the composite a natural endomorphism of `Γ_V`, which by Yoneda is
   `Hom(α, -)` for an endomorphism `α` of the free abelian sheaf on `V`, and nothing identifies
   that `α` with the identity.

   It is also stated on the small pro-étale sites of a chosen *big* pro-étale site rather than
   on `AlgebraicGeometry.Scheme.ProEt`. The site comparison a transport would run along,
   [Stacks, Tag 098X](https://stacks.math.columbia.edu/tag/098X), is no longer an obstruction
   for this site: it is `AlgebraicGeometry.ProEtale.appInclusion_isDenseSubsite` with its
   `AlgebraicGeometry.ProEtale.HasAppCover` hypothesis discharged outright by
   `AlgebraicGeometry.ProEtale.hasAppCover`. What such a transport would have to carry across is
   the adjunction together with its unit, not merely the two functors separately.

   The geometric heart of 09AC for these objects is available, on the affine ind-étale site of
   an affine scheme: `AlgebraicGeometry.ProEtale.isIso_counit_app_of_isWContractible` says that
   the counit `v(V ×_X Z) ⟶ V` of the adjunction `v ⊣ u` of
   [Stacks, Tag 09BK](https://stacks.math.columbia.edu/tag/09BK) is invertible whenever the ring
   of global sections of `V` is w-contractible and the ideal cutting out its closed fibre lies
   in the Jacobson radical of that ring, and that rests on the ring-theoretic retraction of
   `StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.JacobsonQuotientRetraction`. Reading that as
   invertibility of the unit at `V` needs in addition that sheafification does not change the
   sections of the presheaf `F ∘ v^op` at `V ×_X Z`, which is the sheafification step of clause
   (1) of [Stacks, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL); for presheaves of sets
   on `AlgebraicGeometry.Scheme.ProEt` that step is
   [Stacks, Tag 0F63](https://stacks.math.columbia.edu/tag/0F63),
   `AlgebraicGeometry.Scheme.ProEt.bijective_toSheafify_app_of_isWeaklyContractible`. Neither an
   abelian form of it nor a transport of the adjunction is in the library.

Full faithfulness of `i_*` is clause (6) of
[Stacks, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL) and, for a closed immersion of
affine schemes, is now available as
`AlgebraicGeometry.ProEtale.Abelian.fullyFaithful_proetaleDirectImage`. It is what
`isIso_proetaleInverseImage_map_unit_of_isAffine` and hence
`shortExact_map_proetaleInverseImage_of_isAffine` rest on, and no hypothesis is left in either.

It is not the input above and does not yield it. Full faithfulness of a right adjoint says
exactly that the counit `i^{-1} i_* ⟶ 𝟭` is invertible, whereas the input is about the unit
`𝟭 ⟶ i_* i^{-1}`, which here is not invertible at all: over an object pulled back from
`U_proétale` its target vanishes, by `isZero_proetaleSections_of_isEmpty` through
`isEmpty_proetaleBaseChange_proetalePostcompose`, while its source `F(V)` is unconstrained. The
objects at which the unit *is* invertible are cut out geometrically, and which they are is the
content of 09AC rather than a consequence of the abstract adjunction data.

Nor is full faithfulness needed for the tag: once the input above is granted, short exactness on
`X_proétale` follows for an arbitrary `X`, and applying the right exact functor `i^{-1}` to it
gives the statement over `Z` with no affineness, which is
`shortExact_map_proetaleInverseImage_of_isIso_unit_app`.

## Implementation notes

The two maps are adjunction maps, so there is nothing to choose: the left one is the counit of
`AlgebraicGeometry.ProEtale.Abelian.extensionByZero_adjunction` and the right one is the unit of
`AlgebraicGeometry.ProEtale.Abelian.proetaleInverseImageDirectImageAdj`, and both are natural in
the sheaf. Here `j^{-1}` is read as restriction along composition with `j`, which is how the
left adjoint `j_!` of this library is defined, while `i^{-1}` is the sheafified left Kan
extension along base change, which is the reading available for a morphism that is not weakly
étale.

Sheafification of `AddCommGrpCat`-valued presheaves on the small pro-étale site is registered as
an instance here, rather than produced inside each proof as the surrounding files do, so that
the abelian structure on the sheaf category — and hence the zero morphism the short complex
speaks about — is the same one throughout.

The vanishing statements come from one geometric fact: a weakly étale `U`-scheme has empty base
change to `Z`, because the images of `i` and of `j` in `X` are disjoint. An abelian sheaf has
zero sections over an object of the small pro-étale site whose underlying scheme is empty,
because the empty sieve covers such an object.

Short exactness on `X_proétale` is assembled sectionwise rather than through a conservative
family of points, which is how the étale sequence of
[Stacks, Tag 095L](https://stacks.math.columbia.edu/tag/095L) is proved in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence`: a short
complex of sheaves is short exact as soon as its sequences of sections over the objects of a
family covering every object of the site are short exact, `shortExact_of_hasEnoughObjects`, and
on each of the two kinds of object produced by `hasEnoughObjects_openPart_or_closedFibre` the
sequence of sections is *split* — over the open part the third term vanishes and the first map
is invertible, over the closed-fibre part the first term vanishes and the second map is the one
the missing input speaks about. No homology is ever computed.

The two covering families are built from finite jointly surjective families of quasi-compact
weakly étale morphisms, `sieve_ofArrows_mem_proetaleTopology`, and from Zariski coverings,
`sieve_ofArrows_mem_proetaleTopology_of_isOpenImmersion`; the refinement step that composes the
two reductions is `hasEnoughObjects_refine`.

## References

* [Stacks Project, Tag 09AH](https://stacks.math.columbia.edu/tag/09AH)
* [Stacks Project, Tag 09AC](https://stacks.math.columbia.edu/tag/09AC)
* [Stacks Project, Tag 09AE](https://stacks.math.columbia.edu/tag/09AE)
* [Stacks Project, Tag 09AG](https://stacks.math.columbia.edu/tag/09AG)
* [Stacks Project, Tag 095L](https://stacks.math.columbia.edu/tag/095L)
* [Stacks Project, Tag 096V](https://stacks.math.columbia.edu/tag/096V)
* [Stacks Project, Tag 0990](https://stacks.math.columbia.edu/tag/0990)
* [Stacks Project, Tag 098H](https://stacks.math.columbia.edu/tag/098H)
* [Stacks Project, Tag 098X](https://stacks.math.columbia.edu/tag/098X)
* [Stacks Project, Tag 09BK](https://stacks.math.columbia.edu/tag/09BK)
* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
* [Stacks Project, Tag 0F63](https://stacks.math.columbia.edu/tag/0F63)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w w'

namespace AlgebraicGeometry.ProEtale

/-- Presheaves of abelian groups on the small pro-étale site admit sheafification: the site is
essentially small. -/
instance hasSheafify_proetale_addCommGrpCat (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v} :=
  hasSheafify_proetale.{u, v} X

namespace Abelian

/-- The direct image of abelian pro-étale sheaves along a morphism of schemes: restriction
along pro-étale base change. -/
@[implicit_reducible]
def proetaleDirectImage {Z X : Scheme.{u}} (i : Z ⟶ X) :
    Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v} :=
  (Scheme.proetaleBaseChange i).sheafPushforwardContinuous
    AddCommGrpCat.{max (u + 1) v} (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z)

/-- The inverse image of abelian pro-étale sheaves along a morphism of schemes: the sheafified
left Kan extension along pro-étale base change. -/
@[implicit_reducible]
def proetaleInverseImage {Z X : Scheme.{u}} (i : Z ⟶ X) :
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{max (u + 1) v} :=
  Functor.sheafPullbackConstruction.sheafPullback (Scheme.proetaleBaseChange i)
    AddCommGrpCat.{max (u + 1) v} (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z)

/-- Restriction of abelian pro-étale sheaves along a weakly étale morphism is additive: it is
precomposition on presheaves, so it acts on sections by the identity. -/
instance additive_proetaleRestriction {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j] :
    (proetaleRestriction.{u, v} j).Additive := by
  constructor
  intro F G α β
  ext V x
  rfl

/-- Inverse image is left adjoint to direct image for abelian pro-étale sheaves. -/
def proetaleInverseImageDirectImageAdj {Z X : Scheme.{u}} (i : Z ⟶ X) :
    proetaleInverseImage.{u, v} i ⊣ proetaleDirectImage.{u, v} i :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.proetaleBaseChange i) AddCommGrpCat.{max (u + 1) v}
    (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z)

end Abelian

/-! ### Sections over an empty object -/

/-- An abelian sheaf on the small pro-étale site has zero sections over an object whose
underlying scheme is empty: the empty sieve covers such an object. -/
theorem isZero_proetaleSections_of_isEmpty {X : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) (V : X.ProEt)
    (hV : IsEmpty V.left) : IsZero (F.obj.obj (op V)) :=
  letI := hV
  (F.isTerminalOfBotCover V (Scheme.ProEt.bot_mem_topology V)).isZero

/-- An abelian sheaf on the small pro-étale site all of whose groups of sections vanish is
zero. -/
theorem isZero_of_forall_isZero_proetaleSections {X : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v})
    (hF : ∀ V : X.ProEt, IsZero (F.obj.obj (op V))) : IsZero F :=
  IsZero.of_full_of_faithful_of_isZero (sheafToPresheaf _ _) F
    ((Functor.isZero_iff _).2 fun V ↦ hF V.unop)

/-- Inverse image of abelian pro-étale sheaves is additive: it is a left adjoint, hence
preserves binary coproducts, hence binary biproducts. -/
instance additive_proetaleInverseImage {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (Abelian.proetaleInverseImage.{u, v} i).Additive := by
  have _ := (Abelian.proetaleInverseImageDirectImageAdj.{u, v} i).leftAdjoint_preservesColimits
  have _ : Limits.PreservesBinaryBiproducts (Abelian.proetaleInverseImage.{u, v} i) :=
    CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- If the direct image `i_*` of abelian pro-étale sheaves is fully faithful, then the unit
`F ⟶ i_* i^{-1} F` becomes invertible after applying `i^{-1}`. -/
theorem isIso_proetaleInverseImage_map_unit {Z X : Scheme.{u}} (i : Z ⟶ X)
    (hi : (Abelian.proetaleDirectImage.{u, v} i).FullyFaithful)
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :
    IsIso ((Abelian.proetaleInverseImage.{u, v} i).map
      ((Abelian.proetaleInverseImageDirectImageAdj.{u, v} i).unit.app F)) := by
  let _ := hi.full
  let _ := hi.faithful
  infer_instance

/-- For a closed immersion of affine schemes the unit `F ⟶ i_* i^{-1} F` becomes invertible
after applying `i^{-1}`, with nothing assumed.

The direct image `i_*` is fully faithful by Stacks 09BL (6),
`AlgebraicGeometry.ProEtale.Abelian.fullyFaithful_proetaleDirectImage`, so the counit of
`i^{-1} ⊣ i_*` is invertible, and the triangle identity then makes the counit at `i^{-1}F` a
two-sided inverse of `i^{-1}` of the unit. -/
theorem isIso_proetaleInverseImage_map_unit_of_isAffine {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsAffine X] [IsAffine Z] [IsClosedImmersion i]
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :
    IsIso ((Abelian.proetaleInverseImage.{u, v} i).map
      ((Abelian.proetaleInverseImageDirectImageAdj.{u, v} i).unit.app F)) :=
  isIso_proetaleInverseImage_map_unit.{u, v} i
    (Abelian.fullyFaithful_proetaleDirectImage.{u, v} i) F

/-! ### Testing a short complex of sheaves on a covering family of objects -/

section CoveringObjects

variable {C : Type w} [Category.{w'} C] {A : Type*} [Category A]
  {J : GrothendieckTopology C} {B : ObjectProperty C}

/-- Two morphisms of sheaves agreeing on sections over the objects of a family which covers
every object of the site are equal. -/
theorem sheaf_hom_ext_of_hasEnoughObjects (hB : J.HasEnoughObjects B)
    {F G : Sheaf J A} {α β : F ⟶ G}
    (h : ∀ ⦃V : C⦄, B V → α.hom.app (op V) = β.hom.app (op V)) : α = β := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  obtain ⟨I, W, f, hf, hW⟩ := hB V.unop
  apply G.property.hom_ext_ofArrows f hf
  intro k
  rw [← α.hom.naturality, ← β.hom.naturality, h (hW k)]

/-- A morphism of sheaves which is a monomorphism on sections over the objects of a covering
family is a monomorphism. -/
theorem mono_of_hasEnoughObjects (hB : J.HasEnoughObjects B)
    {F G : Sheaf J A} (α : F ⟶ G)
    (h : ∀ ⦃V : C⦄, B V → Mono (α.hom.app (op V))) : Mono α := by
  constructor
  intro H β γ hβγ
  refine sheaf_hom_ext_of_hasEnoughObjects hB (fun V hV ↦ ?_)
  have _ := h hV
  exact (cancel_mono (α.hom.app (op V))).mp
    (congrArg (fun e : H ⟶ G ↦ e.hom.app (op V)) hβγ)

/-- A morphism of sheaves which is an epimorphism on sections over the objects of a covering
family is an epimorphism. -/
theorem epi_of_hasEnoughObjects (hB : J.HasEnoughObjects B)
    {F G : Sheaf J A} (α : F ⟶ G)
    (h : ∀ ⦃V : C⦄, B V → Epi (α.hom.app (op V))) : Epi α := by
  constructor
  intro H β γ hβγ
  refine sheaf_hom_ext_of_hasEnoughObjects hB (fun V hV ↦ ?_)
  have _ := h hV
  exact (cancel_epi (α.hom.app (op V))).mp
    (congrArg (fun e : F ⟶ H ↦ e.hom.app (op V)) hβγ)

/-- **Short exactness is tested on a covering family of objects.** A short complex of sheaves
whose sequences of sections over the objects of a family covering every object of the site are
short exact is itself short exact.

The two outer conditions are read off directly; exactness in the middle is epimorphy of the
canonical map to the kernel of the second map, and evaluation at an object preserves that
kernel because it preserves finite limits. -/
theorem shortExact_of_hasEnoughObjects [Abelian A] [HasSheafify J A]
    (hB : J.HasEnoughObjects B) (S : ShortComplex (Sheaf J A))
    (h : ∀ ⦃V : C⦄, B V → (S.map ((sheafSections J A).obj (op V))).ShortExact) :
    S.ShortExact := by
  have hf : Mono S.f := mono_of_hasEnoughObjects hB S.f fun _ hV ↦ (h hV).mono_f
  have hg : Epi S.g := epi_of_hasEnoughObjects hB S.g fun _ hV ↦ (h hV).epi_g
  refine ShortComplex.ShortExact.mk' (S.exact_iff_epi_kernel_lift.mpr ?_) hf hg
  refine epi_of_hasEnoughObjects hB _ (fun V hV ↦ ?_)
  let E := (sheafSections J A).obj (op V)
  have _ : PreservesFiniteLimits E :=
    comp_preservesFiniteLimits (sheafToPresheaf J A) ((evaluation _ _).obj (op V))
  change Epi (E.map (kernel.lift S.g S.f S.zero))
  have _ : Epi (kernel.lift (E.map S.g) (E.map S.f) (S.map E).zero) :=
    (h hV).exact.epi_kernelLift
  have _ : Epi (E.map (kernel.lift S.g S.f S.zero) ≫ kernelComparison S.g E) := by
    rw [map_lift_kernelComparison]
    infer_instance
  exact (epi_comp_iff_of_isIso (E.map (kernel.lift S.g S.f S.zero))
    (kernelComparison S.g E)).mp inferInstance

/-- A covering family may be refined: if every object of a covering family is itself covered by
objects with a second property, that second property defines a covering family too. -/
theorem hasEnoughObjects_refine {B' : ObjectProperty C} (hB : J.HasEnoughObjects B)
    (h : ∀ ⦃V : C⦄, B V → ∃ (I : Type w') (W : I → C) (f : ∀ k, W k ⟶ V),
      Sieve.ofArrows W f ∈ J V ∧ ∀ k, B' (W k)) :
    J.HasEnoughObjects B' := by
  intro V
  obtain ⟨I, W, f, hf, hW⟩ := hB V
  choose I' W' f' hf' hW' using fun k ↦ h (hW k)
  refine ⟨Σ k, I' k, fun a ↦ W' a.1 a.2, fun a ↦ f' a.1 a.2 ≫ f a.1, ?_,
    fun a ↦ hW' a.1 a.2⟩
  simpa only [Presieve.bindOfArrows_ofArrows] using J.bindOfArrows hf hf'

end CoveringObjects

/-! ### Coverings of the small pro-étale site -/

/-- The forgetful functor from the small pro-étale site of `X` to schemes. -/
abbrev proetaleToScheme (X : Scheme.{u}) : X.ProEt ⥤ Scheme.{u} :=
  Scheme.ProEt.forget X ⋙ Over.forget X

/-- A finite jointly surjective family of quasi-compact weakly étale morphisms of the small
pro-étale site generates a covering sieve. -/
theorem sieve_ofArrows_mem_proetaleTopology {X : Scheme.{u}} {V : X.ProEt} {ι : Type*}
    [Finite ι] (W : ι → X.ProEt) (f : ∀ a, W a ⟶ V)
    (hwe : ∀ a, WeaklyEtale (f a).hom.left)
    (hqc : ∀ a, QuasiCompact (f a).hom.left)
    (hsurj : ∀ x : V.left, ∃ a y, (f a).hom.left.base y = x) :
    Sieve.ofArrows W f ∈ Scheme.ProEt.topology X V := by
  have _ := hwe
  have _ := hqc
  apply Precoverage.generate_mem_toGrothendieck
  have _ : Scheme.JointlySurjective
      (Scheme.precoverage (@WeaklyEtale : MorphismProperty Scheme.{u})) :=
    Scheme.instJointlySurjectivePrecoverage
  let C : V.left.Cover (Scheme.precoverage @WeaklyEtale) :=
    Scheme.Cover.mkOfCovers ι (fun a ↦ (W a).left) (fun a ↦ (f a).hom.left) hsurj hwe
  have _ : Finite C.I₀ := inferInstanceAs (Finite ι)
  have _ : ∀ a : C.I₀, QuasiCompact (C.f a) := hqc
  have _ : QuasiCompactCover C.toPreZeroHypercover := QuasiCompactCover.of_finite
  have hmem : C.presieve₀ ∈ Scheme.proetalePrecoverage V.left := C.ofQuasiCompactCover.mem₀
  rw [Scheme.ProEt.precoverage, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
  exact hmem

/-- A jointly surjective family of open immersions of the small pro-étale site generates a
covering sieve: a Zariski covering is a pro-étale covering. -/
theorem sieve_ofArrows_mem_proetaleTopology_of_isOpenImmersion {X : Scheme.{u}} {V : X.ProEt}
    {ι : Type*} (W : ι → X.ProEt) (f : ∀ a, W a ⟶ V)
    (hoi : ∀ a, IsOpenImmersion (f a).hom.left)
    (hsurj : ∀ x : V.left, ∃ a y, (f a).hom.left.base y = x) :
    Sieve.ofArrows W f ∈ Scheme.ProEt.topology X V := by
  have _ := hoi
  apply Precoverage.generate_mem_toGrothendieck
  let C : V.left.Cover (Scheme.precoverage @IsOpenImmersion) :=
    Scheme.Cover.mkOfCovers ι (fun a ↦ (W a).left) (fun a ↦ (f a).hom.left) hsurj hoi
  have hmem : C.presieve₀ ∈ Scheme.proetalePrecoverage V.left := by
    have _ : MorphismProperty.ContainsIdentities (@WeaklyEtale.{u}) :=
      MorphismProperty.IsMultiplicative.toContainsIdentities
    exact Scheme.zariskiPrecoverage_le_propQCPrecoverage _ C.mem₀
  rw [Scheme.ProEt.precoverage, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
  exact hmem

/-- An affine object of the small pro-étale site whose ring of global sections is
w-contractible is a weakly contractible object of that site.

This is the converse of `AlgebraicGeometry.Scheme.ProEt.isWContractible_globalSections_of_isWeaklyContractible`;
it goes through the clopen-refinement criterion of Stacks 098H. -/
theorem isWeaklyContractible_of_isWContractible {X : Scheme.{u}} (V : X.ProEt)
    [IsAffine V.left] (hV : ProetaleWContractible.IsWContractible.{u, u} Γ(V.left, ⊤)) :
    (Scheme.ProEt.topology X).IsWeaklyContractible V := by
  classical
  refine GrothendieckTopology.isWeaklyContractible_of_clopenRefinements
    (Scheme.ProEt.topology X) (proetaleToScheme X) V (fun Z hZ ↦ ?_) (fun f hf ↦ ?_) ?_
  · have _ : IsEmpty Z.left := hZ
    exact Scheme.ProEt.bot_mem_topology Z
  · exact (proetaleToScheme X).mono_of_mono_map hf
  intro S hS
  let e : ProetaleWContractible.specOf Γ(V.left, ⊤) ≅ V.left := V.left.isoSpec.symm
  have hpush : S.functorPushforward (proetaleToScheme X) ∈
      Scheme.proetaleTopology V.left :=
    (CoverPreserving.of_isContinuous (proetaleToScheme X) (Scheme.ProEt.topology X)
      Scheme.proetaleTopology).cover_preserve hS
  obtain ⟨n, Vi, g, hdec, href⟩ :=
    ProetaleWContractible.everyProetaleCoverHasZariskiRefinement_of_wContractible Γ(V.left, ⊤) hV
      ((S.functorPushforward (proetaleToScheme X)).pullback e.hom)
      (Scheme.proetaleTopology.pullback_stable e.hom hpush)
  have hdecV := ProetaleWContractible.IsClopenDecompositionCover.comp_iso e Vi g hdec
  have hoi : ∀ i, IsOpenImmersion (g i ≫ e.hom) := hdecV.openImmersion
  have _ := hoi
  have hweV : WeaklyEtale V.hom := V.prop
  have hwecomp : ∀ i, WeaklyEtale ((g i ≫ e.hom) ≫ V.hom) := fun i ↦ by
    have _ := hoi i
    infer_instance
  let U : Fin n → X.ProEt := fun i ↦
    @Scheme.ProEt.mk X _ ((g i ≫ e.hom) ≫ V.hom) (hwecomp i)
  let f : ∀ i, U i ⟶ V := fun i ↦ MorphismProperty.Over.homMk (g i ≫ e.hom) rfl
  have hmapf : ∀ i, (f i).hom.left = g i ≫ e.hom := fun i ↦ rfl
  have hqc : ∀ i, QuasiCompact (f i).hom.left := by
    intro i
    show QuasiCompact (g i ≫ e.hom)
    have hclosed : Topology.IsClosedEmbedding (g i ≫ e.hom).base :=
      ⟨(hoi i).base_open.isEmbedding, (hdecV.clopen i).1⟩
    have _ : CompactSpace ↥(Vi i) := hclosed.compactSpace
    exact quasiCompact_of_compactSpace _
  have hsurj : ∀ x : V.left, ∃ i y, (f i).hom.left.base y = x := by
    intro x
    have hx : x ∈ ⋃ i, Set.range (g i ≫ e.hom).base := by
      rw [hdecV.cover]; trivial
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, y, hy⟩
  refine ⟨n, U, f, ?_, ?_, ?_⟩
  · exact hdecV
  · refine sieve_ofArrows_mem_proetaleTopology U f (fun i ↦ ?_) hqc hsurj
    show WeaklyEtale (g i ≫ e.hom)
    have _ := hoi i
    infer_instance
  · intro i
    obtain ⟨Z, k, h, hk, hfac⟩ := href i
    have hw : h ≫ Z.hom = (U i).hom := by
      have hkw : k.hom.left ≫ V.hom = Z.hom := by simpa using k.hom.w
      show h ≫ Z.hom = (g i ≫ e.hom) ≫ V.hom
      refine Eq.trans (congrArg (fun t ↦ h ≫ t) hkw.symm) ?_
      refine Eq.trans (Category.assoc h k.hom.left V.hom).symm ?_
      exact congrArg (fun t ↦ t ≫ V.hom) hfac.symm
    let h' : U i ⟶ Z := MorphismProperty.Over.homMk h hw
    have hfi : f i = h' ≫ k := by
      apply MorphismProperty.Comma.Hom.ext'
      apply CategoryTheory.Comma.hom_ext
      · change g i ≫ e.hom = h ≫ k.hom.left
        exact hfac
      · exact Subsingleton.elim _ _
    rw [hfi]
    exact S.downward_closed hk h'

/-- The ring of global sections of the spectrum of a w-contractible ring is w-contractible. -/
private theorem isWContractible_globalSections_specOf_aux (L : Type u) [CommRing L]
    (hL : ProetaleWContractible.IsWContractible.{u, u} L) :
    ProetaleWContractible.IsWContractible.{u, u} Γ(ProetaleWContractible.specOf L, ⊤) :=
  have _ : IsAffine (ProetaleWContractible.specOf L) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of L)))
  ProetaleWContractible.isWContractible_of_isWeaklyContractible (ProetaleWContractible.specOf L)
    (((ProetaleWContractible.main_theorem L).out 1 2).mp hL)

/-- An affine scheme is covered, in the pro-étale topology, by a single affine scheme whose ring
of global sections is w-contractible. -/
theorem exists_affine_wContractible_proetale_cover (T : Scheme.{u}) [IsAffine T] :
    ∃ (D : Scheme.{u}) (g : D ⟶ T), IsAffine D ∧
      ProetaleWContractible.IsWContractible.{u, u} Γ(D, ⊤) ∧ WeaklyEtale g ∧ Surjective g := by
  classical
  let A := Γ(T, ⊤)
  let κ : Cardinal.{u} := max Cardinal.aleph0 (Cardinal.mk A)
  obtain ⟨D, hD, f, hff, hind, hwd, -⟩ :=
    exists_small_faithfullyFlat_ind_etale_wContractible A κ (le_max_left _ _) (le_max_right _ _)
  let _ : CommRing D := hD
  let _ : Algebra A D := f.toAlgebra
  let r : A ⟶ CommRingCat.of D := CommRingCat.ofHom f
  have hri : CommRingCat.etale.ind.{u} r := (MorphismProperty.ind_iff_ind_underMk _).mpr hind
  have _ : WeaklyEtale (Spec.map r) := weaklyEtale_specMap_of_ind_etale r hind
  have _ : Surjective (Spec.map r) := ((flat_and_surjective_SpecMap_iff r).mpr hff).2
  have _ : IsAffine (ProetaleWContractible.specOf D) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of D)))
  exact ⟨Spec (CommRingCat.of D), Spec.map r ≫ T.isoSpec.inv, inferInstance,
    isWContractible_globalSections_specOf_aux D hwd, inferInstance, inferInstance⟩

/-- Every object of the small pro-étale site of `X` is covered by affine objects. -/
theorem hasEnoughObjects_isAffine (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).HasEnoughObjects (fun V : X.ProEt ↦ IsAffine V.left) := by
  intro V
  have _ : WeaklyEtale V.hom := V.prop
  have hwec : ∀ k, WeaklyEtale (V.left.affineCover.f k ≫ V.hom) := fun k ↦ inferInstance
  refine ⟨V.left.affineCover.I₀,
    fun k ↦ @Scheme.ProEt.mk X _ (V.left.affineCover.f k ≫ V.hom) (hwec k),
    fun k ↦ MorphismProperty.Over.homMk (V.left.affineCover.f k) rfl, ?_, fun k ↦ ?_⟩
  · refine sieve_ofArrows_mem_proetaleTopology_of_isOpenImmersion _ _ (fun k ↦ ?_) (fun x ↦ ?_)
    · show IsOpenImmersion (V.left.affineCover.f k)
      infer_instance
    · exact ⟨V.left.affineCover.idx x, (V.left.affineCover.covers x).choose,
        (V.left.affineCover.covers x).choose_spec⟩
  · exact inferInstanceAs (IsAffine (V.left.affineCover.X k))

/-- **Stacks 0990 for the small pro-étale site of a scheme.** Every object of `X_proétale` is
covered by affine objects which are weakly contractible objects of the site. -/
@[stacks 0990 "the small pro-etale site of a scheme, in the unrestricted form of \
AlgebraicGeometry.Scheme.ProEt: every object is covered by affine weakly contractible ones"]
theorem hasEnoughObjects_isAffine_isWeaklyContractible (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).HasEnoughObjects
      (fun V : X.ProEt ↦ IsAffine V.left ∧
        (Scheme.ProEt.topology X).IsWeaklyContractible V) := by
  refine hasEnoughObjects_refine (hasEnoughObjects_isAffine X) (fun V hV ↦ ?_)
  have _ := hV
  obtain ⟨D, g, hDaff, hDw, hwe, hsurj⟩ := exists_affine_wContractible_proetale_cover V.left
  have _ : WeaklyEtale V.hom := V.prop
  have _ := hwe
  have _ := hsurj
  have _ := hDaff
  have hwecomp : WeaklyEtale (g ≫ V.hom) := inferInstance
  let W : X.ProEt := @Scheme.ProEt.mk X _ (g ≫ V.hom) hwecomp
  have hWaff : IsAffine W.left := hDaff
  refine ⟨PUnit.{u + 1}, fun _ ↦ W, fun _ ↦ MorphismProperty.Over.homMk g rfl, ?_,
    fun _ ↦ ⟨hWaff, ?_⟩⟩
  · refine sieve_ofArrows_mem_proetaleTopology _ _ (fun _ ↦ hwe)
      (fun _ ↦ quasiCompact_of_compactSpace _) (fun x ↦ ?_)
    obtain ⟨y, hy⟩ := hsurj.1 x
    exact ⟨PUnit.unit, y, hy⟩
  · exact isWeaklyContractible_of_isWContractible W hDw

/-- **Stacks 0990, in the form the derived-completeness results consume.** The small pro-étale
site of a scheme has enough weakly contractible objects.

This is the theorem above with the affineness of the covering objects forgotten, which is the
shape `CategoryTheory.GrothendieckTopology.HasEnoughWeaklyContractibleObjects` asks for — it
unfolds to `HasEnoughObjects J (IsWeaklyContractible J)`. It is what supplies the `hX` hypothesis
of the derived-completeness results for this site, among them Stacks 09BY in
`StacksFrontier.AlgebraicGeometry.ProEtale.AdicCompletionCriterion`. -/
@[stacks 0990 "the small pro-etale site of a scheme has enough weakly contractible objects, the \
form HasEnoughWeaklyContractibleObjects asks for"]
theorem hasEnoughWeaklyContractibleObjects_proetale (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).HasEnoughWeaklyContractibleObjects :=
  hasEnoughObjects_refine (hasEnoughObjects_isAffine_isWeaklyContractible X)
    (fun V hV ↦ ⟨PUnit.{u + 1}, fun _ ↦ V, fun _ ↦ 𝟙 V, by
      have hid : Sieve.ofArrows (fun _ : PUnit.{u + 1} ↦ V) (fun _ ↦ 𝟙 V) = ⊤ := by
        rw [← Sieve.id_mem_iff_eq_top]
        exact Sieve.ofArrows_mk _ _ PUnit.unit
      rw [hid]
      exact (Scheme.ProEt.topology X).top_mem V, fun _ ↦ hV.2⟩)

/-! ### The ind-Zariski cover coming from quasi-compactness of the open immersion -/

/-- The range of a quasi-compact morphism of schemes is retrocompact. -/
theorem isRetrocompact_range_of_quasiCompact {A B : Scheme.{u}} (f : A ⟶ B) [QuasiCompact f] :
    IsRetrocompact (Set.range f.base) := by
  intro O hc ho
  have h := (QuasiCompact.isCompact_preimage (f := f) O ho hc).image f.continuous
  simpa only [Set.image_preimage_eq_inter_range, Set.inter_comm] using h

/-- `Spec` of a localization is weakly étale. -/
theorem weaklyEtale_specMap_of_isLocalization {A L : Type u} [CommRing A] [CommRing L]
    [Algebra A L] (M : Submonoid A) [IsLocalization M L] :
    WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap A L))) := by
  have hwe := (weaklyEtale_of_isLocalization_etale_filteredColimit.{u, u, u} A).1 L M
  have hf : Flat (Spec.map (CommRingCat.ofHom (algebraMap A L))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr hwe.flat
  refine ⟨hf, ?_⟩
  rw [diagonal_SpecMap A L]
  have hflat : Flat (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.lmul' A (S := L)).toRingHom)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact hwe.flat_lmul'
  exact MorphismProperty.comp_mem _ _ _ hflat inferInstance

/-- **Stacks 096V, geometrically.** The canonical ind-Zariski localization of an affine scheme
along the closed subset cut out by an ideal, as a morphism onto the set of points specializing
into that subset. -/
def localizationToAffine (V : Scheme.{u}) [IsAffine V] (I : Ideal Γ(V, ⊤)) :
    Spec (CommRingCat.of (localizationRing I (1 : Γ(V, ⊤)))) ⟶ V :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(V, ⊤) (localizationRing I (1 : Γ(V, ⊤))))) ≫
    V.isoSpec.inv

instance weaklyEtale_localizationToAffine (V : Scheme.{u}) [IsAffine V] (I : Ideal Γ(V, ⊤)) :
    WeaklyEtale (localizationToAffine V I) := by
  have _ := weaklyEtale_specMap_of_isLocalization
    (L := localizationRing I (1 : Γ(V, ⊤))) (localizationSubmonoid I 1)
  unfold localizationToAffine
  infer_instance

/-- The closed subset cut out by an ideal is contained in the image of the canonical
localization along it. -/
theorem zeroLocus_subset_range_localizationToAffine (V : Scheme.{u}) [IsAffine V]
    (I : Ideal Γ(V, ⊤)) :
    V.zeroLocus (U := ⊤) (I : Set Γ(V, ⊤)) ⊆ Set.range (localizationToAffine V I).base := by
  intro x hx
  rw [← V.isoSpec_inv_image_zeroLocus (I : Set Γ(V, ⊤))] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  have hpr : p ∈ Set.range (PrimeSpectrum.comap
      (algebraMap Γ(V, ⊤) (localizationRing I (1 : Γ(V, ⊤))))) := by
    rw [localization_comap_range]
    exact ⟨p, ⟨fun _ hx ↦ hp hx, p.2.one_notMem⟩, specializes_refl p⟩
  obtain ⟨q, hq⟩ := hpr
  refine ⟨q, ?_⟩
  show V.isoSpec.inv.base
      ((Spec.map (CommRingCat.ofHom
        (algebraMap Γ(V, ⊤) (localizationRing I (1 : Γ(V, ⊤)))))).base q) = _
  exact congrArg V.isoSpec.inv.base hq

/-- Every point of the canonical localization along a closed subset specializes into that
subset. -/
theorem exists_specializes_mem_zeroLocus_localizationRing {A : Type u} [CommRing A] (I : Ideal A)
    (p : PrimeSpectrum (localizationRing I (1 : A))) :
    ∃ q : PrimeSpectrum (localizationRing I (1 : A)), p ⤳ q ∧
      I ≤ (PrimeSpectrum.comap (algebraMap A (localizationRing I (1 : A))) q).asIdeal := by
  have hp : PrimeSpectrum.comap (algebraMap A (localizationRing I (1 : A))) p ∈
      Set.range (PrimeSpectrum.comap (algebraMap A (localizationRing I (1 : A)))) := ⟨p, rfl⟩
  rw [localization_comap_range] at hp
  obtain ⟨q, hq, hpq⟩ := hp
  have hqrange : q ∈ Set.range
      (PrimeSpectrum.comap (algebraMap A (localizationRing I (1 : A)))) := by
    rw [localization_comap_range]
    exact ⟨q, hq, specializes_refl q⟩
  obtain ⟨q', rfl⟩ := hqrange
  exact ⟨q', (PrimeSpectrum.localization_comap_isEmbedding (localizationRing I (1 : A))
    (localizationSubmonoid I (1 : A))).isInducing.specializes_iff.mp hpq, hq.1⟩

/-- The ring of global sections of the spectrum of a w-contractible ring is w-contractible. -/
theorem isWContractible_globalSections_specOf (L : Type u) [CommRing L]
    (hL : ProetaleWContractible.IsWContractible.{u, u} L) :
    ProetaleWContractible.IsWContractible.{u, u} Γ(ProetaleWContractible.specOf L, ⊤) :=
  isWContractible_globalSections_specOf_aux L hL

/-- Quasi-compactness of the complementary open immersion makes the closed fibre of an affine
pro-étale object cut out by a finitely generated ideal. -/
theorem exists_fg_ideal_closedFibre {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [QuasiCompact j] (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (V : X.ProEt) [IsAffine V.left] :
    ∃ I : Ideal Γ(V.left, ⊤), I.FG ∧
      Set.range (pullback.fst V.hom i).base =
        V.left.zeroLocus (U := ⊤) (I : Set Γ(V.left, ⊤)) := by
  have hcompl : Set.range (pullback.fst V.hom j).base =
      (Set.range (pullback.fst V.hom i).base)ᶜ := by
    rw [Scheme.Pullback.range_fst, Scheme.Pullback.range_fst, hij]
    rfl
  have hretro : IsRetrocompact (Set.range (pullback.fst V.hom i).base)ᶜ := by
    rw [← hcompl]
    exact isRetrocompact_range_of_quasiCompact _
  obtain ⟨I, hI, hzero⟩ :=
    AlgebraicGeometry.exists_fg_ideal_zeroLocus_eq_inter V.left
      (Set.range (pullback.fst V.hom i).base)
      (IsClosedImmersion.isClosedEmbedding (pullback.fst V.hom i)).isClosed_range
      hretro ⊤ (isAffineOpen_top V.left)
  exact ⟨I, hI, by simpa using hzero⟩

/-- Every point of the canonical localization of an affine pro-étale object along its closed
fibre specializes into that fibre. -/
theorem specializes_closedFibre_localizationToAffine {Z X : Scheme.{u}} (i : Z ⟶ X)
    (V : X.ProEt) [IsAffine V.left] (I : Ideal Γ(V.left, ⊤))
    (hI : Set.range (pullback.fst V.hom i).base =
      V.left.zeroLocus (U := ⊤) (I : Set Γ(V.left, ⊤)))
    (x : Spec (CommRingCat.of (localizationRing I (1 : Γ(V.left, ⊤))))) :
    ∃ z : (pullback (localizationToAffine V.left I ≫ V.hom) i : Scheme.{u}),
      Specializes x ((pullback.fst (localizationToAffine V.left I ≫ V.hom) i).base z) := by
  obtain ⟨q, hxq, hq⟩ := exists_specializes_mem_zeroLocus_localizationRing I x
  have hqzero : (localizationToAffine V.left I).base q ∈
      V.left.zeroLocus (U := ⊤) (I : Set Γ(V.left, ⊤)) := by
    rw [← V.left.isoSpec_inv_image_zeroLocus (I : Set Γ(V.left, ⊤))]
    exact ⟨PrimeSpectrum.comap (algebraMap Γ(V.left, ⊤)
      (localizationRing I (1 : Γ(V.left, ⊤)))) q, hq, rfl⟩
  rw [← hI] at hqzero
  obtain ⟨z, hz⟩ := hqzero
  have heq : (localizationToAffine V.left I ≫ V.hom).base q =
      i.base ((pullback.snd V.hom i).base z) := by
    calc (localizationToAffine V.left I ≫ V.hom).base q
        = V.hom.base ((localizationToAffine V.left I).base q) := rfl
      _ = V.hom.base ((pullback.fst V.hom i).base z) := by rw [← hz]
      _ = (pullback.fst V.hom i ≫ V.hom).base z := rfl
      _ = (pullback.snd V.hom i ≫ i).base z := by rw [pullback.condition]
      _ = i.base ((pullback.snd V.hom i).base z) := rfl
  obtain ⟨z', hz'1, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := localizationToAffine V.left I ≫ V.hom) (g := i) q
      ((pullback.snd V.hom i).base z) heq
  exact ⟨z', by rw [hz'1]; exact hxq⟩

/-- **Stacks 09AH, the geometric reduction.** For a closed immersion `i` and its complementary
quasi-compact open immersion `j`, every object of `X_proétale` is covered by objects which are
either pulled back from `U_proétale`, or affine, weakly contractible and with all their points
specializing into the closed fibre.

Quasi-compactness of `j` is what makes the closed fibre of an affine object cut out by finitely
many equations, and hence what produces the ind-Zariski localization of Stacks 096V along it. -/
@[stacks 09AH "the geometric reduction of the source's proof: quasi-compactness of j splits \
every affine weakly contractible object of X_proetale into a part lying over U and the \
ind-Zariski localization along its closed fibre"]
theorem hasEnoughObjects_openPart_or_closedFibre {Z U X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ) :
    (Scheme.ProEt.topology X).HasEnoughObjects (fun V : X.ProEt ↦
      (∃ W : U.ProEt, Nonempty (V ≅ (proetalePostcompose j).obj W)) ∨
      (IsAffine V.left ∧ (Scheme.ProEt.topology X).IsWeaklyContractible V ∧
        ∀ x : V.left, ∃ z : (pullback V.hom i : Scheme.{u}),
          Specializes x ((pullback.fst V.hom i).base z))) := by
  classical
  refine hasEnoughObjects_refine (hasEnoughObjects_isAffine_isWeaklyContractible X)
    (fun V hV ↦ ?_)
  obtain ⟨hVaff, hVw⟩ := hV
  have _ := hVaff
  have _ : WeaklyEtale V.hom := V.prop
  obtain ⟨I, hIfg, hIz⟩ := exists_fg_ideal_closedFibre i j hij V
  have hL : ProetaleWContractible.IsWContractible.{u, u}
      (localizationRing I (1 : Γ(V.left, ⊤))) :=
    isWContractible_localizationRing.{u, u} Γ(V.left, ⊤) I hIfg
      (Scheme.ProEt.isWContractible_globalSections_of_isWeaklyContractible V hVw)
  have hweo : WeaklyEtale (pullback.fst V.hom j ≫ V.hom) := inferInstance
  have hwec : WeaklyEtale (localizationToAffine V.left I ≫ V.hom) := inferInstance
  let Wo : X.ProEt := @Scheme.ProEt.mk X _ (pullback.fst V.hom j ≫ V.hom) hweo
  let Wc : X.ProEt := @Scheme.ProEt.mk X _ (localizationToAffine V.left I ≫ V.hom) hwec
  let W : ULift.{u} Bool → X.ProEt := fun b ↦ cond b.down Wc Wo
  let f : ∀ b, W b ⟶ V := fun b ↦ by
    rcases b with ⟨b⟩
    cases b
    · exact MorphismProperty.Over.homMk (pullback.fst V.hom j) rfl
    · exact MorphismProperty.Over.homMk (localizationToAffine V.left I) rfl
  have hWcaff : IsAffine Wc.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (localizationRing I (1 : Γ(V.left, ⊤))))))
  refine ⟨ULift.{u} Bool, W, f, ?_, ?_⟩
  · refine sieve_ofArrows_mem_proetaleTopology W f (fun b ↦ ?_) (fun b ↦ ?_) (fun x ↦ ?_)
    · rcases b with ⟨b⟩; cases b
      · exact inferInstanceAs (WeaklyEtale (pullback.fst V.hom j))
      · exact weaklyEtale_localizationToAffine V.left I
    · rcases b with ⟨b⟩; cases b
      · exact inferInstanceAs (QuasiCompact (pullback.fst V.hom j))
      · show QuasiCompact (localizationToAffine V.left I)
        exact quasiCompact_of_compactSpace _
    · by_cases hx : x ∈ Set.range (pullback.fst V.hom i).base
      · obtain ⟨y, hy⟩ :=
          zeroLocus_subset_range_localizationToAffine V.left I (hIz ▸ hx)
        exact ⟨⟨true⟩, y, hy⟩
      · have hxo : x ∈ Set.range (pullback.fst V.hom j).base := by
          rw [Scheme.Pullback.range_fst]
          show V.hom.base x ∈ Set.range j.base
          rw [hij]
          rwa [Scheme.Pullback.range_fst] at hx
        obtain ⟨y, hy⟩ := hxo
        exact ⟨⟨false⟩, y, hy⟩
  · rintro ⟨b⟩
    cases b
    · refine Or.inl ⟨@Scheme.ProEt.mk U _ (pullback.snd V.hom j) inferInstance, ⟨?_⟩⟩
      exact MorphismProperty.Over.isoMk (Iso.refl _) (by
        show 𝟙 _ ≫ pullback.snd V.hom j ≫ j = pullback.fst V.hom j ≫ V.hom
        simpa only [Category.id_comp] using (pullback.condition (f := V.hom) (g := j)).symm)
    · exact Or.inr ⟨hWcaff,
        isWeaklyContractible_of_isWContractible Wc
          (isWContractible_globalSections_specOf _ hL),
        specializes_closedFibre_localizationToAffine i V I hIz⟩

/-! ### A closed subscheme and its open complement -/

section Complementary

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) [WeaklyEtale j]
  (hij : Set.range j.base = (Set.range i.base)ᶜ)

include hij

/-- The base change to `Z` of a weakly étale scheme over `U` is empty, `U` and `Z` having
disjoint images in `X`. -/
theorem isEmpty_proetaleBaseChange_proetalePostcompose (W : U.ProEt) :
    IsEmpty ((Scheme.proetaleBaseChange i).obj ((proetalePostcompose j).obj W)).left := by
  change IsEmpty (Limits.pullback (C := Scheme.{u}) (W.hom ≫ j) i)
  refine Scheme.isEmpty_pullback _ _ (Set.disjoint_left.2 ?_)
  rintro x ⟨w, rfl⟩ ⟨z, hz⟩
  have hu : (W.hom ≫ j).base w ∈ Set.range j.base := ⟨W.hom.base w, by simp⟩
  rw [hij] at hu
  exact hu ⟨z, hz⟩

/-- Restricting to `U` a direct image from `Z` gives zero: the sections of such a restriction
over a weakly étale `U`-scheme are sections over an empty scheme. -/
theorem isZero_proetaleRestriction_proetaleDirectImage
    (G : Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{max (u + 1) v}) :
    IsZero ((Abelian.proetaleRestriction.{u, v} j).obj
      ((Abelian.proetaleDirectImage.{u, v} i).obj G)) :=
  isZero_of_forall_isZero_proetaleSections _ fun W ↦
    isZero_proetaleSections_of_isEmpty G _
      (isEmpty_proetaleBaseChange_proetalePostcompose i j hij W)

/-- The inverse image to `Z` of an extension by zero from `U` is zero: by the two adjunctions it
receives no nonzero map, since restricting to `U` a direct image from `Z` already vanishes. -/
theorem isZero_proetaleInverseImage_extensionByZero
    (G : Sheaf (Scheme.ProEt.topology U) AddCommGrpCat.{max (u + 1) v}) :
    IsZero ((Abelian.proetaleInverseImage.{u, v} i).obj
      ((Abelian.extensionByZero.{u, v} j).obj G)) := by
  rw [IsZero.iff_id_eq_zero]
  apply ((Abelian.proetaleInverseImageDirectImageAdj.{u, v} i).homEquiv _ _).injective
  apply ((Abelian.extensionByZero_adjunction.{u, v} j).homEquiv _ _).injective
  exact (isZero_proetaleRestriction_proetaleDirectImage i j hij _).eq_of_tgt _ _

/-- The composite `j_! j^{-1} F ⟶ F ⟶ i_* i^{-1} F` of the two canonical maps of the tag is
zero: under the adjunction `j_! ⊣ j^{-1}` it corresponds to a map into `j^{-1} i_* i^{-1} F`,
which is zero. -/
theorem extensionByZero_counit_comp_proetaleInverseImage_unit
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :
    (Abelian.extensionByZero_adjunction.{u, v} j).counit.app F ≫
      (Abelian.proetaleInverseImageDirectImageAdj.{u, v} i).unit.app F = 0 := by
  apply ((Abelian.extensionByZero_adjunction.{u, v} j).homEquiv _ _).injective
  exact (isZero_proetaleRestriction_proetaleDirectImage i j hij _).eq_of_tgt _ _

/-- **Stacks 09AH.** The canonical short complex `j_! j^{-1} F ⟶ F ⟶ i_* i^{-1} F` on the small
pro-étale site of `X`, for a closed subscheme `i : Z ⟶ X` and the inclusion `j : U ⟶ X` of its
complement. Its two maps are the counit of `j_! ⊣ j^{-1}` and the unit of `i^{-1} ⊣ i_*`.

The tag states in addition that this short complex is short exact when `j` is quasi-compact. That
is not proved here: `shortExact_openClosedShortComplex_of_isIso_unit_app` below reduces it to the
single input described in the header of this file. -/
@[stacks 09AH "the two canonical maps j_! j^{-1} F -> F -> i_* i^{-1} F and the fact that they \
compose to zero, i.e. the short complex of the tag; its short exactness is NOT proved here, see \
shortExact_openClosedShortComplex_of_isIso_unit_app"]
def openClosedShortComplex
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :
    ShortComplex (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :=
  ShortComplex.mk ((Abelian.extensionByZero_adjunction.{u, v} j).counit.app F)
    ((Abelian.proetaleInverseImageDirectImageAdj.{u, v} i).unit.app F)
    (extensionByZero_counit_comp_proetaleInverseImage_unit i j hij F)

omit hij in
/-- For an open immersion `j`, the counit `j_! j^{-1} F ⟶ F` becomes invertible after
restricting to `U`: the unit of `j_! ⊣ j^{-1}` is invertible there, so `j_!` is fully
faithful. -/
theorem isIso_proetaleRestriction_map_counit [IsOpenImmersion j]
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :
    IsIso ((Abelian.proetaleRestriction.{u, v} j).map
      ((Abelian.extensionByZero_adjunction.{u, v} j).counit.app F)) := by
  have _ : IsIso (Abelian.extensionByZero_adjunction.{u, v} j).unit :=
    extensionByZero_unit_isIso_abelian.{u, v} j
  let ff := (Abelian.extensionByZero_adjunction.{u, v} j).fullyFaithfulLOfIsIsoUnit
  let _ := ff.full
  let _ := ff.faithful
  infer_instance

/-- **Stacks 09AH, over the open part.** Restricted to `U`, the short complex of the tag is
short exact, and indeed split: its third term vanishes over `U` and its first map becomes
invertible there. -/
@[stacks 09AH "exactness over the open part only: the restriction to U of the canonical short \
complex is short exact, unconditionally. Short exactness of the sequence on X_proetale itself \
is NOT proved in this file: shortExact_openClosedShortComplex_of_isIso_unit_app proves it at \
the source's hypotheses but assumes Tag 09AC for the site of AlgebraicGeometry.Scheme.ProEt, \
namely that the unit F -> i_* i^{-1} F is invertible on sections over every affine weakly \
contractible object all of whose points specialize into its closed fibre"]
theorem shortExact_map_proetaleRestriction [IsOpenImmersion j]
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :
    ((openClosedShortComplex.{u, v} i j hij F).map
      (Abelian.proetaleRestriction.{u, v} j)).ShortExact :=
  (ShortComplex.Splitting.ofIsIsoOfIsZero _
    (isIso_proetaleRestriction_map_counit j F)
    (isZero_proetaleRestriction_proetaleDirectImage i j hij _)).shortExact

/-- **Stacks 09AH, over the closed part.** If the direct image `i_*` of abelian pro-étale
sheaves is fully faithful — which is clause (6) of
[Stacks, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL) — then the inverse image to `Z`
of the short complex of the tag is short exact, and indeed split: its first term vanishes over
`Z` and its second map becomes invertible there.

For a closed immersion of affine schemes the hypothesis is discharged outright, which is
`shortExact_map_proetaleInverseImage_of_isAffine`. -/
theorem shortExact_map_proetaleInverseImage
    (hi : (Abelian.proetaleDirectImage.{u, v} i).FullyFaithful)
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :
    ((openClosedShortComplex.{u, v} i j hij F).map
      (Abelian.proetaleInverseImage.{u, v} i)).ShortExact :=
  (ShortComplex.Splitting.ofIsZeroOfIsIso _
    (isZero_proetaleInverseImage_extensionByZero i j hij _)
    (isIso_proetaleInverseImage_map_unit i hi F)).shortExact

/-- **Stacks 09AH, over the closed part.** For a closed immersion `i : Z ⟶ X` of affine schemes,
the inverse image to `Z` of the short complex of the tag is short exact, and indeed split: its
first term vanishes over `Z` and its second map becomes invertible there, with nothing assumed.

Invertibility of the second map is full faithfulness of `i_*`, which is clause (6) of
[Stacks, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL); it is carried by
`isIso_proetaleInverseImage_map_unit_of_isAffine`, and affineness of `X` and of `Z` is what that
clause is proved under. For arbitrary `X` the same conclusion is
`shortExact_map_proetaleInverseImage_of_isIso_unit_app`, which needs no affineness and no full
faithfulness, at the price of the input of
`shortExact_openClosedShortComplex_of_isIso_unit_app`. -/
theorem shortExact_map_proetaleInverseImage_of_isAffine
    [IsAffine X] [IsAffine Z] [IsClosedImmersion i]
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :
    ((openClosedShortComplex.{u, v} i j hij F).map
      (Abelian.proetaleInverseImage.{u, v} i)).ShortExact :=
  shortExact_map_proetaleInverseImage.{u, v} i j hij
    (Abelian.fullyFaithful_proetaleDirectImage.{u, v} i) F

end Complementary

/-! ### Short exactness on `X_proétale` -/

section Assembly

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)

/-- Complementary immersions have empty intersection. -/
theorem isEmpty_pullback_of_range_eq_compl
    (hij : Set.range j.base = (Set.range i.base)ᶜ) :
    IsEmpty (pullback j i : Scheme.{u}) := by
  refine Scheme.isEmpty_pullback _ _ (Set.disjoint_left.2 ?_)
  rintro x ⟨w, rfl⟩ hxi
  have hx : j.base w ∈ Set.range j.base := ⟨w, rfl⟩
  rw [hij] at hx
  exact hx hxi

/-- **Stacks 09AH on `X_proétale`, reduced to Stacks 09AC.** For a closed immersion `i` and its
complementary quasi-compact open immersion `j`, the canonical short complex
`j_! j^{-1} F ⟶ F ⟶ i_* i^{-1} F` is short exact on `X_proétale`, provided the unit
`F ⟶ i_* i^{-1} F` is invertible on sections over every affine weakly contractible object all
of whose points specialize into the closed fibre.

The hypothesis is exactly [Stacks, Tag 09AC](https://stacks.math.columbia.edu/tag/09AC) for the
unrestricted small pro-étale site; see the discussion at the head of this file. -/
theorem shortExact_openClosedShortComplex_of_isIso_unit_app [IsClosedImmersion i]
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (hunit : ∀ V : X.ProEt, IsAffine V.left →
      (Scheme.ProEt.topology X).IsWeaklyContractible V →
      (∀ x : V.left, ∃ z : (pullback V.hom i : Scheme.{u}),
        Specializes x ((pullback.fst V.hom i).base z)) →
      ∀ F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v},
        IsIso (((Abelian.proetaleInverseImageDirectImageAdj.{u, v} i).unit.app F).hom.app
          (op V)))
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :
    (openClosedShortComplex.{u, v} i j hij F).ShortExact := by
  refine shortExact_of_hasEnoughObjects
    (hasEnoughObjects_openPart_or_closedFibre i j hij) _ ?_
  rintro V (⟨W, ⟨e⟩⟩ | ⟨hVaff, hVw, hspec⟩)
  · have hcounit : IsIso (((Abelian.extensionByZero_adjunction.{u, v} j).counit.app F).hom.app
        (op ((proetalePostcompose j).obj W))) := by
      have _ := isIso_proetaleRestriction_map_counit.{u, v} j F
      exact inferInstanceAs (IsIso
        (((sheafSections (Scheme.ProEt.topology U) AddCommGrpCat.{max (u + 1) v}).obj
          (op W)).map ((Abelian.proetaleRestriction.{u, v} j).map
            ((Abelian.extensionByZero_adjunction.{u, v} j).counit.app F))))
    have h3 : IsZero
        (((Abelian.proetaleDirectImage.{u, v} i).obj
          ((Abelian.proetaleInverseImage.{u, v} i).obj F)).obj.obj
            (op ((proetalePostcompose j).obj W))) :=
      isZero_proetaleSections_of_isEmpty.{u, v}
        ((Abelian.proetaleInverseImage.{u, v} i).obj F)
        ((Scheme.proetaleBaseChange i).obj ((proetalePostcompose j).obj W))
        (isEmpty_proetaleBaseChange_proetalePostcompose i j hij W)
    refine (ShortComplex.Splitting.ofIsIsoOfIsZero _
      ((NatTrans.isIso_app_iff_of_iso _ e.op).mp hcounit) ?_).shortExact
    exact h3.of_iso ((Functor.mapIso
      ((Abelian.proetaleDirectImage.{u, v} i).obj
        ((Abelian.proetaleInverseImage.{u, v} i).obj F)).obj e.op).symm)
  · have _ := hVaff
    refine (ShortComplex.Splitting.ofIsZeroOfIsIso _ ?_ (hunit V hVaff hVw hspec F)).shortExact
    exact isZero_extensionByZero_sections_of_specializes_to_closed.{u, v} j i
      (isEmpty_pullback_of_range_eq_compl i j hij) V hspec
      ((Abelian.proetaleRestriction.{u, v} j).obj F)

/-- **Stacks 09AH over the closed part, with no full-faithfulness hypothesis.** Granted the same
input as `shortExact_openClosedShortComplex_of_isIso_unit_app`, the inverse image to `Z` of the
short complex of the tag is short exact — the hypothesis that `i_*` be fully faithful, carried by
`shortExact_map_proetaleInverseImage`, is not needed.

Only right exactness of `i^{-1}` is used, which holds because it is a left adjoint: the second map
of the short complex is a cokernel of the first, that is preserved, and the first term becomes
zero, so the second map becomes a cokernel of a map out of a zero object, i.e. invertible. In
particular clause (1) of [Stacks, Tag 09AA](https://stacks.math.columbia.edu/tag/09AA), that
`i^{-1}` commutes with limits, is not needed. -/
theorem shortExact_map_proetaleInverseImage_of_isIso_unit_app [IsClosedImmersion i]
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (hunit : ∀ V : X.ProEt, IsAffine V.left →
      (Scheme.ProEt.topology X).IsWeaklyContractible V →
      (∀ x : V.left, ∃ z : (pullback V.hom i : Scheme.{u}),
        Specializes x ((pullback.fst V.hom i).base z)) →
      ∀ F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v},
        IsIso (((Abelian.proetaleInverseImageDirectImageAdj.{u, v} i).unit.app F).hom.app
          (op V)))
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :
    ((openClosedShortComplex.{u, v} i j hij F).map
      (Abelian.proetaleInverseImage.{u, v} i)).ShortExact := by
  have _ := (Abelian.proetaleInverseImageDirectImageAdj.{u, v} i).leftAdjoint_preservesColimits
  have hS := shortExact_openClosedShortComplex_of_isIso_unit_app.{u, v} i j hij hunit F
  have h₁ : IsZero ((Abelian.proetaleInverseImage.{u, v} i).obj
      (openClosedShortComplex.{u, v} i j hij F).X₁) :=
    isZero_proetaleInverseImage_extensionByZero i j hij _
  have _ := hS.epi_g
  have hepi : Epi ((Abelian.proetaleInverseImage.{u, v} i).map
      (openClosedShortComplex.{u, v} i j hij F).g) := inferInstance
  have hex := hS.exact.map_of_epi_of_preservesCokernel
    (Abelian.proetaleInverseImage.{u, v} i) hS.epi_g inferInstance
  exact ShortComplex.ShortExact.mk' hex ⟨fun _ _ _ ↦ h₁.eq_of_tgt _ _⟩ hepi

end Assembly

end AlgebraicGeometry.ProEtale

end
