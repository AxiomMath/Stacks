module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.ZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.OpensSectionsOfInjective
public import StacksFrontier.AlgebraicGeometry.LimitUniverse.PairOpensDescent
import all StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites

/-!
# The leg of an inverse image, read on sections over an open subscheme

Let `k : T ⟶ S` be a morphism of schemes, `G` an abelian sheaf on Mathlib's small étale site of
`S`, `𝒢` one on that of `T`, and `ι : k^{-1}G ⟶ 𝒢` a morphism of abelian sheaves — in
[Stacks, Tag 09YQ], a *leg* of the presentation of `𝒢` as `colim_i f_i^{-1}F_i`, with `k` a
projection of the limit cone. This file builds from `ι` the family of maps on **sections over the
open subschemes**

`G(W) ⟶ 𝒢(k^{-1}W)`,   `W` an open subscheme of `S`,

and proves that it commutes with restriction along an inclusion of opens.

That family is what the degree-zero half of Tag 09YQ is a statement about, and it is the datum of
`Stacks.EtaleCohomology.OpensAcyclicity.sectionsDifference_preimage_of_surjective_of_injective`,
the level step of the hypothesis `hsub` of
`subsingleton_H_smallEtale_of_affineOpens_acyclic_of_sectionsDifference` (in the namespace
`Stacks.EtaleCohomology.OpensAcyclicity`). It extends the construction over the **terminal**
object (`Stacks.EtaleCohomology.etaleUnitSection` and
`Stacks.EtaleCohomology.etaleSectionsRestriction` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleCohomologyDegreeZeroSections`,
the unit of the adjunction and the pullback map on *global* sections) to every open subscheme, and
rests on a comparison between the inclusion `AlgebraicGeometry.opensToEtale` of the open
subschemes into the small étale site and base change along a morphism of schemes.

## Main results

* `Stacks.EtaleCohomology.opensToEtaleBaseChangeIso` — **the preimage of an open subscheme is its
  base change**: for `W` an open subscheme of `S`, the object `k^{-1}W` of the small étale site of
  `T` is `Stacks.EtaleCohomology.smallEtaleBaseChange k` applied to the object `W` of the small
  étale site of `S`, naturally in `W` (`opensToEtaleBaseChangeIso_naturality`).
* `Stacks.EtaleCohomology.etaleTransposeSection` — a morphism out of an inverse image, read on
  sections over an object of the site, with its naturality in the object.
* `Stacks.EtaleCohomology.etaleOpensLeg` and
  `Stacks.EtaleCohomology.etaleOpensLeg_restrict` — **the leg on sections over an open subscheme,
  and its compatibility with restriction.**
* `Stacks.EtaleCohomology.opensSectionsLeg`, `opensSectionsLeg_comp_restrict` and
  `opensSectionsLeg_restrict` — the same, spelled with
  `Stacks.EtaleCohomology.OpensAcyclicity.opensSections`, which is the vocabulary of the
  degree-zero gluing condition.
* `Stacks.EtaleCohomology.OpensAcyclicity.sectionsDifference_of_surjective_opensLeg` —
  **`hsub` for the colimit sheaf of [Stacks, Tag 09YQ]**, from the surjectivity of that leg on
  sections at *some* level above the one the open lives on, and nothing else.

The surjectivity it asks for is over the opens of a level whose preimage in the limit is
quasi-compact, and such an open need not be quasi-compact itself.
`Stacks.EtaleCohomology.surjective_opensSectionsLeg_of_isCompact` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleOpensLegQuasiCompact.lean`
reduces it to the surjectivity over the opens that *are* quasi-compact at their level, which is
the only form the available results can produce; see that file.

## Implementation notes

**Morphisms into an object with a monomorphic structure morphism are unique.** Both the geometric
naturality of the comparison and the square it is used through are instances of
`etale_hom_ext_of_mono`: two morphisms of `T.Etale` with the same source and the same target agree
as soon as the structure morphism of the target is a monomorphism, because the structure morphism
of the source factors through each of them
(`CategoryTheory.MorphismProperty.Over.w`). Open immersions are monomorphisms and so are their
base changes, so no square of the fibre product is ever computed: the naturality of
`opensToEtaleBaseChangeIso` costs one application of that lemma and the whole pullback is confined
to the construction of the isomorphism itself, where it is
`AlgebraicGeometry.isPullback_morphismRestrict` — Mathlib's statement that `X ×_Y W` is `f^{-1}W`
for an open `W`.

This is also why `etale_hom_ext_of_mono` takes its monomorphism hypothesis as an **explicit
argument** rather than an instance: the structure morphism of `(opensToEtale T).obj W` is `W.ι`
only up to unfolding `AlgebraicGeometry.opensToEtale`, which instance search does not do, so
`Mono ((opensToEtale T).obj W).hom` is not synthesized even though `Mono W.ι` is. Passing it
explicitly lets the two be matched by `exact`, which does unfold.

**The direct image is restriction along base change, and only definitionally.** The sections of
`k_*𝒢` over an object `Z` of the small étale site of `S` *are* the sections of `𝒢` over the base
change `Z ×_S T`, but the two are spelled differently and the equality is definitional; a
composite written through the first spelling stops being type-correct at the transparency
`rewrite` builds its motive at. `etaleTransposeSection` names the component of the transpose of `ι`
in the second spelling, which seals that junction inside one definition — the device the
implementation notes of `SmallEtaleCohomologyDegreeZeroSections.lean` introduce for the unit over
the terminal object, used here over an arbitrary object.

## `hsub` for the colimit sheaf, and what it still rests on

`sectionsDifference_of_surjective_opensLeg` assembles the last section of this file: for an
inverse system of schemes over a nonempty directed index with affine transition morphisms, a limit
cone with quasi-separated vertex `X`, an abelian sheaf `𝒢` on the small étale site of `X`,
**injective** abelian sheaves `F_i` on the small étale sites of the levels and maps
`ι_i : f_i^{-1}F_i ⟶ 𝒢`, the degree-zero gluing condition holds for `𝒢` at every pair consisting
of a quasi-compact open `U` and an affine open `V` of `X` as soon as, for every open `W` of a
level `X_i` whose preimage in `X` is quasi-compact, `opensSectionsLeg` is **surjective on
sections** over the pullback of `W` to *some* level `X_j` with `j ≥ i`.

Surjectivity is asked for only **eventually** — at some level above the one the open lives on —
because that is the form [Stacks, Tag 09YQ] supplies: a section of a colimit over a quasi-compact
open comes from *some* level, and nothing pins that level to the one the open happened to be
written on. The weaker hypothesis costs the transport nothing. The opens `U'`, `V'` that the pair
descends to pull back along the transition to opens of the later level with the *same* preimages in
`X`, because the projection at the later level factors through the transition
(`CategoryTheory.Limits.Cone.w`), so the whole argument below simply runs at the level the
hypothesis hands back rather than at the level the pair descended to.

Three inputs from the library are used and none of them is assumed:

* `AlgebraicGeometry.exists_preimage_eq_pair` — [Stacks, Tag 01Z4] (1) for a *pair*: `U` and `V`
  are the preimages of two opens of one and the same level;
* `Stacks.EtaleCohomology.OpensAcyclicity.sectionsDifference_of_injective` — the Mayer--Vietoris
  splitting at the level, which holds for an arbitrary pair of opens of the level because `F_k` is
  injective there, through
  `sectionsDifference_preimage_of_surjective_of_injective`;
* `opensSectionsLeg_restrict` of this file, the compatibility the transport needs.

Quasi-separatedness of `X` enters in exactly one place and is not avoidable: `U ⊓ V` has to be
quasi-compact for the surjectivity hypothesis to be applicable to it, and the intersection of two
quasi-compact opens is quasi-compact precisely under that hypothesis
(`QuasiSeparatedSpace.inter_isCompact`). It is a hypothesis of the dévissage that consumes `hsub`,
`subsingleton_H_smallEtale_of_affineOpens_acyclic_of_sectionsDifference` (in the namespace
`Stacks.EtaleCohomology.OpensAcyclicity`), so nothing is added.

**What `hsub` therefore still owes, exactly and only, is the surjectivity in that eventual
form — and, by
`Stacks.EtaleCohomology.surjective_opensSectionsLeg_of_isCompact`, only over the opens of a level
that are quasi-compact there.** That is the degree-zero statement of [Stacks, Tag 09YQ] over a
quasi-compact
quasi-separated étale object descending from a level — joint surjectivity of the legs on sections,
which is a statement about the colimit over the levels and so never about one level alone — which
is the same crossing the degree-zero statement `H0` and the first geometric hypothesis `haff` each
still owe. Nothing else about the presentation is used: not the separatedness half of the
degree-zero statement, not the universal property of the colimit, and not a single cohomology
group of the limit. In particular `hsub` needs **no sheaf-level site crossing** and, as the
implementation notes record, no naturality of the Mayer--Vietoris comparison in the open
subscheme.

What is available for the surjectivity is
`Stacks.EtaleCohomology.QcSeparatedColimit.sectionOver_colimit_of_qcqs_etale_object`, for a
colimit presentation of sheaves of **sets** on the size-bounded small *affine* étale sites of
[Stacks, Tag 021B] and the levels of [Stacks, Tag 0EYL]. The abelian counterpart over an object is
Stacks 09YP, `Stacks.WeakSites.ColimitSiteCohomology.isColimitCohomologyCocone` in degree zero;
it is stated over an *object of the colimit site*, so on the raised small affine étale site it
answers for affine opens only, and `U ⊓ V` with `U` quasi-compact and `V` affine is a
quasi-compact open of an affine scheme and need not be affine. Passing from affine objects to such
an open is the finite one-hypercover step that
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf'` performs for
sheaves of sets.

**That step is also available at abelian coefficients.**
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab` of the file
`AbelianSectionsOverAnObjectOfColimitOfFiniteSites` in the folder
`StacksFrontier.CategoryTheory.Sites.InverseSystem` is the same statement with `Type w` replaced
by `Ab.{w}`. Nothing in the one-hypercover step is a
colimit — its two object-level inputs, joint surjectivity and separatedness of the legs on
sections over the objects of a level, are hypotheses — so it is its own set-valued instance along
`CategoryTheory.forget Ab`, and no transport of a universal property across the coefficients is
involved; see that file's implementation notes. What the surjectivity therefore still owes is
**not** the one-hypercover step but those two object-level inputs for the *abelian* system at the
levels of
[Stacks, Tag 0EYL]. From an abelian `IsColimitPresentation` on those levels they are the case
`p = 0` of `Stacks.WeakSites.ColimitSiteCohomology.isColimitCohomologyCocone`, and directly the
`private Stacks.WeakSites.ColimitSiteCohomology.isColimit_sectionsCocone_of_presentation` of
`StacksFrontier/CategoryTheory/Sites/InverseSystem/CohomologyOfColimitOfFiniteSites.lean`, which is
a colimit cocone of the groups of sections over every object of every level and so, over a
filtered index, exactly joint surjectivity together with separatedness. The passage of the
presentation from Mathlib's small étale sites to those levels is what
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleSystemIdentityLaw.lean`
measures as blocked by the identity law of
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.AbelianSheafSystem`.

**Why `hsub` cannot instead be deduced from a vanishing.**
`sectionsDifference_of_injective` gets the gluing condition from the vanishing of `H^1(U ⊔ V, F)`,
and for the colimit sheaf that vanishing is proved over every object of the raised small affine
étale site of the limit (`Stacks.Cohomology.VanishesOnObjects`, as
`Stacks.EtaleCohomology.QcqsLimitCohomology.vanishesOnObjects_colimit_of_pointwise_injective`).
`U ⊔ V` is not such an object, and the two routes from the affine objects to it both close:
upgrading condition (1) of [Stacks, Tag 07A1] to total acyclicity needs condition (2),
`Stacks.Cohomology.CechComplexExactPos`, which is not proved for the colimit sheaf; and deducing
`H^1(U ⊔ V, 𝒢) = 0` by applying the dévissage to the scheme `U ⊔ V` needs `hsub` for the pairs of
opens of `U ⊔ V`, which is circular, the induction on the number of affine opens not decreasing
there. The degree-zero descent of sections is therefore not one route among several but the only
one, and that is why `hsub` is a degree-zero statement.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 0A50](https://stacks.math.columbia.edu/tag/0A50)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe v u

namespace Stacks.EtaleCohomology

section Mono

variable {T : Scheme.{u}}

/-- Two morphisms of the small étale site of `T` with the same source and the same target are
equal as soon as the structure morphism of the target is a monomorphism. -/
public theorem etale_hom_ext_of_mono {A B : T.Etale} (hB : Mono B.hom) (f g : A ⟶ B) : f = g :=
  have := hB
  MorphismProperty.Over.Hom.ext ((cancel_mono B.hom).1
    ((MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm))

end Mono

section OpensBaseChange

variable {T S : Scheme.{u}} (k : T ⟶ S)

/-- **The preimage of an open subscheme is its base change, read in the small étale sites.** -/
public def opensToEtaleBaseChangeIso (W : S.Opens) :
    (opensToEtale T).obj (k ⁻¹ᵁ W) ≅
      (smallEtaleBaseChange k).obj ((opensToEtale S).obj W) :=
  MorphismProperty.Over.isoMk (isPullback_morphismRestrict k W).isoPullback
    (show (isPullback_morphismRestrict k W).isoPullback.hom ≫ pullback.snd W.ι k =
      (k ⁻¹ᵁ W).ι from (isPullback_morphismRestrict k W).isoPullback_hom_snd)

/-- The structure morphism of the base change of an open subscheme is a monomorphism. -/
public theorem mono_hom_smallEtaleBaseChange_opensToEtale (W : S.Opens) :
    Mono ((smallEtaleBaseChange k).obj ((opensToEtale S).obj W)).hom :=
  show Mono (pullback.snd W.ι k) from
    (isPullback_morphismRestrict k W).isoPullback_inv_snd ▸
      mono_comp (isPullback_morphismRestrict k W).isoPullback.inv (k ⁻¹ᵁ W).ι

/-- The isomorphism `opensToEtaleBaseChangeIso` is natural in the open subscheme. -/
public theorem opensToEtaleBaseChangeIso_naturality {W W' : S.Opens} (h : W ≤ W') :
    (opensToEtaleBaseChangeIso k W).hom ≫
        (smallEtaleBaseChange k).map ((opensToEtale S).map (homOfLE h)) =
      (opensToEtale T).map (homOfLE (k.preimage_mono h)) ≫ (opensToEtaleBaseChangeIso k W').hom :=
  etale_hom_ext_of_mono (mono_hom_smallEtaleBaseChange_opensToEtale k W') _ _

end OpensBaseChange

section Leg

variable {T S : Scheme.{u}} (k : T ⟶ S)
  [HasSheafify S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  {G : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
  {𝒢 : Sheaf T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}

/-- **A map out of an inverse image, read on sections over an object.** -/
public def etaleTransposeSection (ι : (etaleAbelianInverseImage.{u, v} k).obj G ⟶ 𝒢) (Z : S.Etale) :
    G.obj.obj (op Z) ⟶ 𝒢.obj.obj (op ((smallEtaleBaseChange k).obj Z)) :=
  (((etaleAbelianInverseImageDirectImageAdj.{u, v} k).homEquiv G 𝒢) ι).hom.app (op Z)

omit [HasSheafify S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}] in
/-- `etaleTransposeSection` is natural in the object. -/
public theorem etaleTransposeSection_naturality (ι : (etaleAbelianInverseImage.{u, v} k).obj G ⟶ 𝒢)
    {Z Z' : S.Etale} (g : Z ⟶ Z') :
    G.obj.map g.op ≫ etaleTransposeSection k ι Z =
      etaleTransposeSection k ι Z' ≫ 𝒢.obj.map ((smallEtaleBaseChange k).map g).op :=
  (((etaleAbelianInverseImageDirectImageAdj.{u, v} k).homEquiv G 𝒢) ι).hom.naturality g.op

/-- **The leg on sections over an open subscheme.** -/
public def etaleOpensLeg (ι : (etaleAbelianInverseImage.{u, v} k).obj G ⟶ 𝒢) (W : S.Opens) :
    G.obj.obj (op ((opensToEtale S).obj W)) ⟶
      𝒢.obj.obj (op ((opensToEtale T).obj (k ⁻¹ᵁ W))) :=
  etaleTransposeSection k ι ((opensToEtale S).obj W) ≫
    𝒢.obj.map (opensToEtaleBaseChangeIso k W).hom.op

omit [HasSheafify S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}] in
/-- **The leg on sections commutes with restriction along an inclusion of opens.** -/
public theorem etaleOpensLeg_restrict (ι : (etaleAbelianInverseImage.{u, v} k).obj G ⟶ 𝒢)
    {W W' : S.Opens} (h : W ≤ W') :
    G.obj.map ((opensToEtale S).map (homOfLE h)).op ≫ etaleOpensLeg k ι W =
      etaleOpensLeg k ι W' ≫
        𝒢.obj.map ((opensToEtale T).map (homOfLE (k.preimage_mono h))).op := by
  rw [etaleOpensLeg, etaleOpensLeg, ← Category.assoc,
    etaleTransposeSection_naturality k ι ((opensToEtale S).map (homOfLE h)),
    Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
    opensToEtaleBaseChangeIso_naturality k h]

end Leg

/-! ### The leg in the vocabulary of the one-universe model -/

section LegOpensSections

variable {T S : Scheme.{u}} (k : T ⟶ S)
  [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}]
  [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
  {G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
  {𝒢 : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}

/-- **The leg on sections over an open subscheme, spelled with
`Stacks.EtaleCohomology.OpensAcyclicity.opensSections`** — the groups of sections of the sheaves
read on the one-universe model of the small étale site, which is the vocabulary the degree-zero
gluing condition is stated in. The two spellings are definitionally equal; naming this one seals
the junction, see the implementation notes. -/
public def opensSectionsLeg (ι : (etaleAbelianInverseImage.{u, u + 1} k).obj G ⟶ 𝒢)
    (W : S.Opens) :
    OpensAcyclicity.opensSections ((MayerVietoris.mayerVietorisRestrict S).obj G) W ⟶
      OpensAcyclicity.opensSections ((MayerVietoris.mayerVietorisRestrict T).obj 𝒢) (k ⁻¹ᵁ W) :=
  etaleOpensLeg k ι W

omit [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}] in
/-- `Stacks.EtaleCohomology.etaleOpensLeg_restrict` in the vocabulary of the one-universe
model. -/
public theorem opensSectionsLeg_comp_restrict
    (ι : (etaleAbelianInverseImage.{u, u + 1} k).obj G ⟶ 𝒢) {W W' : S.Opens} (h : W ≤ W') :
    OpensAcyclicity.opensSectionsRestrict ((MayerVietoris.mayerVietorisRestrict S).obj G) h ≫
        opensSectionsLeg k ι W =
      opensSectionsLeg k ι W' ≫
        OpensAcyclicity.opensSectionsRestrict
          ((MayerVietoris.mayerVietorisRestrict T).obj 𝒢) (k.preimage_mono h) :=
  etaleOpensLeg_restrict k ι h

omit [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}] in
/-- **The leg on sections commutes with restriction**, read on elements: the hypothesis `hleg` of
`Stacks.EtaleCohomology.OpensAcyclicity.sectionsDifference_preimage_of_surjective_of_injective`. -/
public theorem opensSectionsLeg_restrict (ι : (etaleAbelianInverseImage.{u, u + 1} k).obj G ⟶ 𝒢)
    {W W' : S.Opens} (h : W ≤ W')
    (x : ToType (OpensAcyclicity.opensSections
      ((MayerVietoris.mayerVietorisRestrict S).obj G) W')) :
    OpensAcyclicity.opensSectionsRestrict ((MayerVietoris.mayerVietorisRestrict T).obj 𝒢)
        (k.preimage_mono h) (opensSectionsLeg k ι W' x) =
      opensSectionsLeg k ι W
        (OpensAcyclicity.opensSectionsRestrict
          ((MayerVietoris.mayerVietorisRestrict S).obj G) h x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    opensSectionsLeg_comp_restrict k ι h]

end LegOpensSections

/-! ### Pulling an open of a level back to a later level -/

section ConePreimage

open Stacks.EtaleCohomology.SmallEtaleLimitCohomology (conePi)

/-- **Pulling an open of a level back to a later level does not change its preimage in the
limit.** For `a : j ⟶ i` in `Iᵒᵖ` the projection at `j` factors as `f_j = f_i ≫ f_{ij}`
(`CategoryTheory.Limits.Cone.w`), and the preimage along a composite is the composite of the
preimages, definitionally.

This is the transport the *pointwise* form of the degree-zero statement of [Stacks, Tag 09YQ]
needs: a section of the colimit sheaf over `f_i^{-1}W` is a section over `f_j^{-1}(f_{ij}^{-1}W)`
only through this equality, which holds propositionally and not syntactically. -/
public theorem conePi_preimage_map_preimage {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
    (c : Cone D) {i j : Iᵒᵖ} (a : j ⟶ i) (W : (D.obj i).Opens) :
    conePi c j ⁻¹ᵁ (D.map a ⁻¹ᵁ W) = conePi c i ⁻¹ᵁ W := by
  rw [show conePi c j ⁻¹ᵁ (D.map a ⁻¹ᵁ W) = (conePi c j ≫ D.map a) ⁻¹ᵁ W from rfl,
    show conePi c j ≫ D.map a = conePi c i from c.w a]

end ConePreimage

end Stacks.EtaleCohomology

/-! ### `hsub` for the colimit sheaf of Stacks 09YQ -/

namespace Stacks.EtaleCohomology.OpensAcyclicity

open Stacks.EtaleCohomology.SmallEtaleLimitCohomology (conePi)

section Hsub

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : Iᵒᵖ ⥤ Scheme.{max u v}} {c : Cone D}
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
  [∀ i : Iᵒᵖ, HasSheafify (D.obj i).smallEtaleTopology AddCommGrpCat.{max u v + 1}]
  [HasSheafify (c.pt).smallEtaleTopology AddCommGrpCat.{max u v + 1}]

omit [∀ i : Iᵒᵖ, HasSheafify (D.obj i).smallEtaleTopology AddCommGrpCat.{max u v + 1}] in
/-- **The second geometric hypothesis of [Stacks, Tag 09YQ]: `hsub` for the colimit sheaf.** Let
`(X_i)` be an inverse system of schemes over a nonempty directed index with affine transition
morphisms, let `X` be the vertex of a limit cone with projections `f_i`, quasi-separated, let `𝒢`
be an abelian sheaf on Mathlib's small étale site of `X`, and let `F_i` be **injective** abelian
sheaves on those of the `X_i` together with maps `ι_i : f_i^{-1}F_i ⟶ 𝒢` — the data of the
colimit sheaf `colim_i f_i^{-1}F_i` of that tag. Suppose that for every open `W` of a level `X_i`
whose preimage in `X` is quasi-compact, **every section** of `𝒢` over `f_i^{-1}W` comes from a
section of `F_j` over the pullback of `W` to *some* level `X_j` above `X_i` — the level depending
on the section, and not necessarily `X_i` itself. Then for every quasi-compact open `U` and affine
open `V` of `X` every section of `𝒢` over `U ⊓ V` is the difference of a section over `U` and a
section over `V`.

This is the hypothesis `hsub` of
`subsingleton_H_smallEtale_of_affineOpens_acyclic_of_sectionsDifference` and of
`SmallEtaleLimitCohomology.isCohomologyColimit_of_degreeZero_of_affineOpensAcyclic`.

The hypothesis is **pointwise** in the section, and that is forced: the stronger form — a level
`X_j` at which the leg is *surjective*, the level chosen before the section — is false. For
`I = ℕ`, `D` constant at `Spec k` with identity transitions and `F_i` the constant sheaf on
`⊕_{p < i} ℤ` with the inclusions as transitions, `𝒢 = colim_i f_i^{-1}F_i` is the constant sheaf
on `⊕_{p < ω} ℤ`: every section of `𝒢` comes from some level and no single `F_j(X_j) ⟶ 𝒢(X)` is
surjective. The weakening costs this theorem nothing, for the reason
`Stacks.EtaleCohomology.OpensAcyclicity.exists_sectionsDifference_preimage_of_leg` records.

The proof is three steps and no cohomology of the limit occurs in any of them. `U` and `V` descend
to opens `U'`, `V'` of one level `X_k` by [Stacks, Tag 01Z4] (1)
(`AlgebraicGeometry.exists_preimage_eq_pair`); the section to be split is handed to the hypothesis
at `U' ⊓ V'`, whose preimage is `U ⊓ V`, and it comes back from a level `X_j` above `X_k`; `F_j` is
injective, so the splitting holds over the pullbacks of `U'`, `V'` to `X_j` for free, with no
quasi-compactness and no affineness used at the level
(`Stacks.EtaleCohomology.OpensAcyclicity.sectionsDifference_of_injective`); and the leg carries it
down the projection (`exists_sectionsDifference_preimage_of_leg`, whose compatibility datum is
`opensSectionsLeg_restrict`). Pulling `U'` and `V'` back along the transition changes neither of
their preimages in `X` (`Stacks.EtaleCohomology.conePi_preimage_map_preimage`), and the two
sections produced at `X_j` are carried to `U` and `V` by restriction along those equalities. The
module docstring says what is available for the hypothesis. -/
public theorem sectionsDifference_of_surjective_opensLeg [QuasiSeparatedSpace c.pt]
    (hc : IsLimit c) (𝒢 : Sheaf (c.pt).smallEtaleTopology AddCommGrpCat.{max u v + 1})
    (F : ∀ i : Iᵒᵖ, Sheaf (D.obj i).smallEtaleTopology AddCommGrpCat.{max u v + 1})
    (hF : ∀ i : Iᵒᵖ, Injective (F i))
    (ι : ∀ i : Iᵒᵖ,
      (etaleAbelianInverseImage.{max u v, max u v + 1} (conePi c i)).obj (F i) ⟶ 𝒢)
    (hsurj : ∀ (i : Iᵒᵖ) (W : (D.obj i).Opens),
      IsCompact ((conePi c i ⁻¹ᵁ W : (c.pt).Opens) : Set c.pt) →
      ∀ τ : ToType (opensSections ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝒢)
        (conePi c i ⁻¹ᵁ W)),
      ∃ (j : Iᵒᵖ) (a : j ⟶ i) (σ : ToType (opensSections
        ((MayerVietoris.mayerVietorisRestrict (D.obj j)).obj (F j)) (D.map a ⁻¹ᵁ W))),
        opensSectionsLeg (conePi c j) (ι j) (D.map a ⁻¹ᵁ W) σ =
          opensSectionsRestrict ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝒢)
            (conePi_preimage_map_preimage c a W).le τ)
    (U V : (c.pt).Opens) (hU : IsCompact (U : Set c.pt)) (hV : IsAffineOpen V) :
    SectionsDifference ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝒢) U V := by
  obtain ⟨k, U', V', hU', hV'⟩ := exists_preimage_eq_pair D c hc U V hU hV.isCompact
  have hUV : IsCompact ((U ⊓ V : (c.pt).Opens) : Set c.pt) :=
    QuasiSeparatedSpace.inter_isCompact (U : Set c.pt) (V : Set c.pt) U.isOpen hU V.isOpen
      hV.isCompact
  subst hU'
  subst hV'
  intro τ
  obtain ⟨j, a, σ, hσ⟩ := hsurj k (U' ⊓ V')
    (by rw [Scheme.Hom.preimage_inf]; exact hUV) τ
  -- the projection at `j` factors through the transition, so the two opens of `X_j` that `U'` and
  -- `V'` pull back to have the same preimages in `X`
  have hj : ∀ W : (D.obj k).Opens,
      conePi c j ⁻¹ᵁ (D.map a ⁻¹ᵁ W) = c.π.app k ⁻¹ᵁ W := conePi_preimage_map_preimage c a
  have hinfj : conePi c j ⁻¹ᵁ (D.map a ⁻¹ᵁ U') ⊓ conePi c j ⁻¹ᵁ (D.map a ⁻¹ᵁ V') =
      c.π.app k ⁻¹ᵁ U' ⊓ c.π.app k ⁻¹ᵁ V' := by
    rw [hj, hj]
  have := hF j
  have := MayerVietoris.injective_mayerVietorisRestrict (F j)
  obtain ⟨p, q, hpq⟩ := exists_sectionsDifference_preimage_of_leg (conePi c j)
    (G := (MayerVietoris.mayerVietorisRestrict (D.obj j)).obj (F j))
    (𝒢 := (MayerVietoris.mayerVietorisRestrict c.pt).obj 𝒢)
    (fun W => opensSectionsLeg (conePi c j) (ι j) W)
    (fun {_ _} h x => opensSectionsLeg_restrict (conePi c j) (ι j) h x)
    (D.map a ⁻¹ᵁ U') (D.map a ⁻¹ᵁ V') (sectionsDifference_of_injective _ _ _) σ
  refine ⟨opensSectionsRestrict _ (hj U').ge p, opensSectionsRestrict _ (hj V').ge q, ?_⟩
  refine opensSectionsRestrict_injective_of_eq _ hinfj.le hinfj ?_
  rw [map_sub (ConcreteCategory.hom (opensSectionsRestrict
      ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝒢) hinfj.le)),
    opensSectionsRestrict_restrict, opensSectionsRestrict_restrict,
    opensSectionsRestrict_restrict, opensSectionsRestrict_restrict]
  exact hpq.trans hσ

end Hsub

end Stacks.EtaleCohomology.OpensAcyclicity

end
