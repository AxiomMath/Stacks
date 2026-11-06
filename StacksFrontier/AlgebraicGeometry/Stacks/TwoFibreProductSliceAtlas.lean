module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Permanence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.LimitPreservingFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingTwoFibreProductObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.MorphismSpaceIsoClass
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointBaseChange
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceBaseChangeComposite
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SlicePointOfSection
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable
public import StacksFrontier.Deformation.Artin.Versality.SmoothImpliesVersalityCondition
public import StacksFrontier.Deformation.Artin.Versality.SmoothnessFromPredeformation

/-!
# The atlas of a base change along a scheme-valued point, as a 1-morphism over the slice

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S`, let `U` be an object of that site and let `y` be a scheme-valued point of `𝒴` over
`U`. `AlgebraicGeometry.Stack.HasRelativeProperty` (**Stacks 03YK**) tests a property of `f` on a
presheaf `T` on the big fppf site of `U` equivalent, *over that slice*, to the first projection of
the 2-fibre product `(Sch/U)_{fppf} ×_{y, 𝒴, f} 𝒳`. This file turns a scheme atlas of `T` into a
1-morphism into that 2-fibre product over the slice, and identifies the two composites a consumer
needs.

The point of the exercise is the proof of **Stacks 07XX**: the deformation-theoretic criterion for
smoothness is available for the 1-morphism `(Sch/W)_{fppf} ⟶ (Sch/U)_{fppf}` induced by a morphism
of schemes (`Deformation.Artin.smooth_of_isSmoothOnPredeformationCategories`), and what the general
1-morphism supplies is the condition for the projection of the 2-fibre product
(**Stacks 07XV**, at the ordering of the cospan that Stacks 03YK presents). An atlas member of `T`
bridges the two.

## Main definitions

* `AlgebraicGeometry.Stack.sliceObjHom`: an object of the big fppf site of `U`, read as an object
  of the big fppf site of `S` together with its structure morphism to `U`.

## Main results

* `AlgebraicGeometry.Stack.exists_sliceAtlasPoint`: a section `h_W ⟶ T` of the representing
  presheaf is a 1-morphism `(Sch/W)_{fppf} ⟶ (Sch/U)_{fppf} ×_{y, 𝒴, f} 𝒳` strictly over the
  slice, whose value at the tautological object is vertically identified with the object the
  section names.
* `AlgebraicGeometry.Stack.comp_structureFunctor_of_comp_fst`: such a 1-morphism is strictly over
  the big fppf site of `S` as well, for the structure functor of the 2-fibre product.
* `AlgebraicGeometry.Stack.representingMap_sliceAtlasPoint`: the morphism of representing
  presheaves it induces over `S` (**Stacks 04SW**) is the lower-shriek extension `Λ_U a` of the
  atlas member `a`.
* `AlgebraicGeometry.Stack.isRelativelySmooth_sliceAtlasPoint`: it is therefore a smooth
  1-morphism in the sense of **Stacks 04XB** when `a` is a smooth atlas.
* `AlgebraicGeometry.Stack.relativelyRepresentable_pullbackFst_of_isAlgebraicSpace`: a base
  change of a morphism out of a representable presheaf into an algebraic space over `S` is
  representable by schemes, by the diagonal clause of **Stacks 025Y**.
* `AlgebraicGeometry.Stack.relativelyRepresentable_relocalizeToYoneda_sliceAtlasPoint`: hence the
  representability hypothesis that the library's clause of **Stacks 07XW** carries beyond the source
  holds automatically at an atlas point of the base change.
* `AlgebraicGeometry.Stack.isSmoothOnPredeformationCategories_sliceAtlasPoint`: **Stacks 07XW**
  at the atlas point, giving it the condition of **Stacks 07XS**, with no representability
  hypothesis left.
* `AlgebraicGeometry.Stack.isSmoothOnPredeformationCategories_sliceObjHom`: the condition of
  **Stacks 07XS** for the 1-morphism `(Sch/W)_{fppf} ⟶ (Sch/U)_{fppf}` induced by the structure
  morphism of the atlas, from the same condition for `f` and for the atlas 1-morphism.
* `AlgebraicGeometry.Stack.smooth_sliceObjHom_of_isSmoothOnPredeformationCategories`: the atlas
  scheme is then smooth over `U`.
* `AlgebraicGeometry.Stack.isSmooth_toYonedaId_of_smooth_atlas`: **Stacks 0AHD** descends that to
  smoothness of the algebraic space over `U`.
* `Stack.isLocallyOfFiniteType_toYonedaId_of_isLocallyOfFinitePresentation_algebraicSpaceMap`:
  an algebraic space over `U` whose structural morphism of **Stacks 04SG** is locally of finite
  presentation over `S` is locally of finite type over `U`.
* `AlgebraicGeometry.Stack.locallyOfFiniteType_sliceObjHom_of_isSmooth_atlas`: *every* smooth
  atlas member of such an algebraic space is locally of finite type over `U` — no choice of
  atlas is involved.
* `AlgebraicGeometry.Stack.locallyOfFiniteType_relocalize_of_isSmooth_atlas`: hence locally of
  finite type over `S`, which is the finite-type hypothesis the smoothness criterion needs of
  the atlas scheme.
* `AlgebraicGeometry.Stack.hasRelativeProperty_smooth_of_isSmoothOnPredeformationCategories`: the
  whole reduction step of **Stacks 07XX**, from the condition of Stacks 07XS for `f` to
  smoothness of `f` in the sense of **Stacks 03YK**.
* `AlgebraicGeometry.Stack.isRelativelySmooth_of_isSmoothOnPredeformationCategories`:
  **Stacks 07XX** for a general 1-morphism, at the source's four hypotheses.

## Implementation notes

*Nothing here constructs the 1-morphism.* It already exists:
`StacksRepresentableCFG.exists_pointOverMap_of_section` produces, from a morphism `h_W ⟶ T` of
presheaves on a slice `𝒞/X` and an equivalence over `𝒞/X` between a category fibred in groupoids
and the category of elements of `T`, a 1-morphism `𝒞/W.left ⥤` that category which is *strictly*
over `CategoryTheory.Over.map W.hom`, together with a vertical identification of its value at the
tautological object. `AlgebraicGeometry.Stack.exists_sliceAtlasPoint` only instantiates it at the
first projection of the 2-fibre product, whose fibredness in groupoids over the slice is
`CategoryTheory.PresheafOfCategories.isFiberedInGroupoids_fst_overMap_of`, and keeps the vertical
identification: it is the only data tying the 1-morphism to the atlas member it came from, and
`AlgebraicGeometry.Stack.representingMap_sliceAtlasPoint` is what spends it.

*No genuine 2-isomorphism is needed.* One might expect the composite
`(Sch/W)_{fppf} ⟶ (Sch/U)_{fppf} ×_{y, 𝒴, f} 𝒳 ⟶ (Sch/U)_{fppf}` to be only 2-isomorphic to the
1-morphism `CategoryTheory.Over.map` of the structure morphism of `W`. It is not: the two are
*equal* as functors. The first leg is strictly over `CategoryTheory.Over.map W.hom` by the above,
and the second leg is strictly over the slice by
`CategoryTheory.TwoFibreProductOver.fst_comp_eq`, so the two legs compose to `Over.map W.hom` on
the nose; and `W.hom` is, syntactically, the underlying morphism of the structure morphism
`AlgebraicGeometry.Stack.sliceObjHom` of `W` read in the site of `S`. The only propositional step
is `CategoryTheory.Over.mapComp_eq`, used to recognise `Over.map W.hom ⋙ Over.map U.hom` as
`Over.map` of the composite structure morphism.

That the two functors are equal is nevertheless not enough to rewrite one for the other, because
the condition of Stacks 07XS takes the commuting equation as a further argument whose *type*
mentions the functor; `rw` cannot abstract the functor out of the goal without making that
argument ill-typed. The transport is therefore still routed through
`Deformation.Artin.isSmoothOnPredeformationCategories_of_natIso`, at the 2-isomorphism
`CategoryTheory.eqToIso` of the equality — every component of which is vertical because it is an
`CategoryTheory.eqToHom`. No 2-isomorphism beyond that is used, and in particular nothing has to
be known about how the atlas 1-morphism interacts with the comparison of the 2-fibre product.

*How the atlas point is made smooth.* The condition of Stacks 07XS for the atlas 1-morphism `c`
is the hypothesis `hc` of
`AlgebraicGeometry.Stack.isSmoothOnPredeformationCategories_sliceObjHom`, and it is the content
of **Stacks 07XW** read at `c`. Discharging it needs the smoothness of `c` in the sense of
`AlgebraicGeometry.Stack.IsRelativelySmooth`, which is a statement about bundled categories
fibred in groupoids over `S` rather than about the bare functors, and that is what the
`AtlasSmooth` section supplies.

Bundle the slice over the atlas scheme as `AlgebraicGeometry.Stack.schemeSlice` of `W`
relocalized along `U ⟶ S`, bundle the 2-fibre product as
`CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare` of the point `y` and of `f`, and
bundle `c` between them with `AlgebraicGeometry.Stack.schemeSliceMap`, which recovers `c` as its
underlying functor definitionally. Both are representable by algebraic spaces over `S`: the
source by `h_{W/S}` (`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_schemeSlice`) and
the target by `Λ_U T` (`AlgebraicGeometry.Stack.relocalizeFibreEquivalence`, which converts the
equivalence over the *slice* for the *first projection* that Stacks 03YK supplies into one over
`S` for the *structure functor*). So the bridge of Stacks 04XB,
`AlgebraicGeometry.Stack.isRelativelySmooth_iff_isSmooth_representingMap`, reduces smoothness of
`c` to smoothness of the induced morphism `h_{W/S} ⟶ Λ_U T` of representing presheaves.

That morphism is computed in `AlgebraicGeometry.Stack.representingMap_sliceAtlasPoint`: it is
`Λ_U a`, read through the presentation of `h_{W/S}` as `Λ_U h_{W/U}` of **Stacks 03I4** part (2)
(`CategoryTheory.OverShriek.relocalizeYonedaFactorIso`). The computation is where the vertical
identification kept by `AlgebraicGeometry.Stack.exists_sliceAtlasPoint` is spent: the morphism
goes out of a representable presheaf, so the Yoneda lemma reduces it to the value at the identity
section, and **Stacks 04SW**
(`AlgebraicGeometry.Stack.morphismSpaceEquiv_app_sectionOfObj`) computes that value at the
tautological object of the big fppf site of `W`, whose image under `c` is identified with the
object the atlas member names. Smoothness of `Λ_U a` is then smoothness of `a`, the
every-étale-chart condition of Stacks 03MJ being unchanged by the lower-shriek extension
(`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeMap_iff`). No 2-Yoneda uniqueness
statement is needed, and nothing has to be known about how `c` interacts with the comparison of
the 2-fibre product.

*What the descent section adds.* The step from smoothness of the atlas scheme over `U` to
smoothness over `U` of the algebraic space it covers — **Stacks 0AHD** in the smooth case,
`AlgebraicGeometry.Space.isSmooth_of_comp_surjective_isSmooth` — and the reading of the result as
the structural morphism that `AlgebraicGeometry.Stack.HasRelativeProperty` tests *are* carried
out, in `AlgebraicGeometry.Stack.isSmooth_toYonedaId_of_smooth_atlas` and
`AlgebraicGeometry.Stack.smoothMorphismProperty_algebraicSpaceMap_of_smooth_atlas`. The descent
runs entirely over the big fppf site of `U`: Stacks 03YK tests the structural morphism of the
image of Stacks 04SG's forward functor, and that morphism's every-étale-chart condition is the
one over `U` itself, by `AlgebraicGeometry.Stack.prop_algebraicSpaceMap_iff` followed by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff`. So the triangle 0AHD is
applied to is the one formed by a scheme atlas of the representing space, the space, and the
terminal object of the site of `U`, and no relocalization of the atlas is needed.

*How the atlas point is made representable by schemes.* The library's clause of Stacks 07XW
(`Deformation.Artin.isSmoothOnPredeformationCategories_of_isRelativelySmooth_of_representable`)
carries, beyond the source, a hypothesis `hrep` asking each algebraic space representing a base
change of the 1-morphism along a scheme-valued point of the target to be representable by
*schemes*; it is the one place the implementation notes of
`StacksFrontier/Deformation/Artin/Versality/SmoothImpliesVersalityCondition.lean` record that file
as falling short. At an atlas point it is automatic, and
`AlgebraicGeometry.Stack.relativelyRepresentable_relocalizeToYoneda_sliceAtlasPoint` discharges
it, for a reason the general clause cannot use.

The reason is not the universal property of the lower-shriek extension. It is that the *source*
of the atlas point is a slice of the site, so its representing presheaf is representable, while
its target is representable by the algebraic space `Λ_U T`. The structural morphism of the
lower-shriek extension of a presheaf representing a base change along a scheme-valued point is
identified with the base change of the induced morphism of representing presheaves by
`AlgebraicGeometry.Stack.arrowIsoRelocalizeFibrePullback` — already in the library, and already the
engine of the Stacks 04XB bridge used above. So the presheaf in question is a base change of a
morphism *out of a representable presheaf* into an algebraic space, and the *diagonal* clause of
`AlgebraicGeometry.IsAlgebraicSpace` — not the atlas clause — makes every such morphism
relatively representable, by `CategoryTheory.Functor.relativelyRepresentable.of_diag`; relative
representability is then stable under base change. That is
`AlgebraicGeometry.Stack.relativelyRepresentable_pullbackFst_of_isAlgebraicSpace`.

Nothing is needed about *which* morphism of representing presheaves the atlas point induces, so
`AlgebraicGeometry.Stack.representingMap_sliceAtlasPoint` is not used for this, the atlas member
and its smoothness do not appear, and the statement holds for an arbitrary 1-morphism out of the
relocalized slice.

*Finite type hypotheses, and how they are discharged.*
`Deformation.Artin.smooth_of_isSmoothOnPredeformationCategories` asks both schemes to be locally
of finite type over a locally Noetherian `S`. Both are derived, as the source derives them,
and no finite-type hypothesis is carried by the assembly theorems.

For the *point* `V` it is the source's own reduction, Criteria for Representability, Lemma 07WI,
formalized as `AlgebraicGeometry.Stack.hasRelativeProperty_of_affine_locallyOfFinitePresentation`:
it reduces `AlgebraicGeometry.Stack.HasRelativeProperty` for a base-change-stable, fppf-local
property to the scheme-valued points whose object is affine and locally of finite presentation
over `S`, granted that `𝒴 ⟶ (Sch/S)_{fppf}` is limit preserving on objects. The assembly is
routed through it, so `V ⟶ S` arrives locally of finite presentation, hence locally of finite
type. Smoothness is base-change stable (**Stacks 03ZE**) and fppf local on the target
(**Stacks 0429**), which are the two conditions that reduction asks of the property; the second
is an instance whose index universe the relative property does not pin, so it is pinned by hand.

For the *atlas member* `W` no choice of atlas is needed, and the statement that an earlier
version of this note called the remaining lemma — that a smooth atlas *may be chosen* locally of
finite presentation over `V` — is weaker than the truth. Once the representing algebraic space
`F` is locally of finite type over `V`, *every* object `W` of the big fppf site of `V` carrying a
smooth `a : h_W ⟶ F` has `W ⟶ V` locally of finite type, because the structure morphism of `W`
to the terminal object of the site of `V` *is* the composite `a ≫ (F ⟶ ∗)`: smooth implies
locally of finite type (**Stacks 06MH**), local finite type is stable under composition
(**Stacks 03XG**), and **Stacks 03MJ** for a morphism of the site reads the conclusion back on
the morphism of schemes. That is
`AlgebraicGeometry.Stack.locallyOfFiniteType_sliceObjHom_of_isSmooth_atlas`; surjectivity of `a`
is not used. Composing with `V ⟶ S` gives `W ⟶ S` locally of finite type.

Local finite type of `F` over `V` comes from local finite presentation of the base change, which
is what the hypotheses `hlimX` and `hlimY` supply, through the cancellation for Stacks 06CU
(`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_toTerminalCFG`) and then **Stacks 06CX**
(`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation`): that
equivalence states local finite presentation of a 1-morphism *as* the relative property of
Stacks 03YK, point by point, so its value at the very point and representing space the assembly
is working at is already the needed statement — no projection out of a relative property and no
transport between presentations of the 2-fibre product is involved. Reading it over `V` instead
of over `S` is `AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_algebraicSpaceMap_iff_toYonedaId`,
and local finite presentation implies local finite type by **Stacks 0464**.

*The hypotheses are the source's.* `hfrep` is condition (1) of Stacks 07XX, `hf` is its (2),
`hlimX` is its (3) — the structure morphism `𝒳 ⟶ (Sch/S)_{fppf}` limit preserving on objects —
and `hlimY` is its (4), together with `S` locally Noetherian. Nothing beyond them is carried.

Asking (3) of `f : 𝒳 ⟶ 𝒴` instead would be strictly stronger. The only use made of (3) is
through **Stacks 06CX**, and what makes the weaker form suffice is a
*cancellation* for the condition of Stacks 06CU: from `𝒳 ⟶ (Sch/S)_{fppf}` limit preserving on
objects and `𝒴` limit preserving, `f` is limit preserving on objects. That is the argument the
source leaves implicit, and it is
`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_toTerminalCFG`: an object of `𝒳` over an
affine limit descends to a stage by (3), the given object of `𝒴` is pulled back to that stage so
that the cartesian comparison becomes a *vertical* one, and that vertical comparison descends to
a further stage because the colimit comparison for `𝒴` is full — the half of limit preservation
that essential surjectivity does not give. It is none of the three stability properties of
Stacks 06CU, which are base change (**Stacks 06CV**), composition (**Stacks 06CW**) and
reindexing, and it does not follow from them.

The descent of a vertical morphism that it needs is `Deformation.Artin.descentHom_of_full`, which
is public.

Two other routes to the same end were examined and are not shorter. Taking the base change
`𝒵 = (Sch/V)_{fppf} ×_{y, 𝒴, f} 𝒳` through Stacks 07XM part (1) and Stacks 06CX — the source's
own route, formalized as
`Stack.isRepresentableBySpaceLocallyOfFinitePresentation_twoFibreProduct_schemeFibredCategory`
— bounds `𝒵 ⟶ (Sch/S)_{fppf}` rather than `𝒵 ⟶ (Sch/V)_{fppf}`, and converting the one into the
other needs both the projection of a relative property to the structural morphism of one chosen
representing space at the final object of the site, which
`StacksFrontier/AlgebraicGeometry/Stacks/LimitPreservingSetoidRepresentable.lean` records as
deliberately absent, and the cancellation of Stacks 05WT
(`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_comp`) against `V ⟶ S`. Reading the
first projection of the 2-fibre product as a base change of `f`
(`AlgebraicGeometry.BigFppfOver.isLimitPreservingOnObjects_twoFibreProductSquareFst`) asks for
`f` limit preserving on objects at the outset, so it is circular.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 02Y6](https://stacks.math.columbia.edu/tag/02Y6)
* [Stacks Project, Tag 03I4](https://stacks.math.columbia.edu/tag/03I4)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03XG](https://stacks.math.columbia.edu/tag/03XG)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03ZE](https://stacks.math.columbia.edu/tag/03ZE)
* [Stacks Project, Tag 0429](https://stacks.math.columbia.edu/tag/0429)
* [Stacks Project, Tag 0464](https://stacks.math.columbia.edu/tag/0464)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 05WT](https://stacks.math.columbia.edu/tag/05WT)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 06CV](https://stacks.math.columbia.edu/tag/06CV)
* [Stacks Project, Tag 06CW](https://stacks.math.columbia.edu/tag/06CW)
* [Stacks Project, Tag 06CX](https://stacks.math.columbia.edu/tag/06CX)
* [Stacks Project, Tag 06MH](https://stacks.math.columbia.edu/tag/06MH)
* [Stacks Project, Tag 07WI](https://stacks.math.columbia.edu/tag/07WI)
* [Stacks Project, Tag 07XM](https://stacks.math.columbia.edu/tag/07XM)
* [Stacks Project, Tag 07XN](https://stacks.math.columbia.edu/tag/07XN)
* [Stacks Project, Tag 07XS](https://stacks.math.columbia.edu/tag/07XS)
* [Stacks Project, Tag 07XU](https://stacks.math.columbia.edu/tag/07XU)
* [Stacks Project, Tag 07XV](https://stacks.math.columbia.edu/tag/07XV)
* [Stacks Project, Tag 07XW](https://stacks.math.columbia.edu/tag/07XW)
* [Stacks Project, Tag 07XX](https://stacks.math.columbia.edu/tag/07XX)
* [Stacks Project, Tag 0AHD](https://stacks.math.columbia.edu/tag/0AHD)
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.PresheafOfCategories

universe v₁ u₁

/-- **The tautological object of a slice names the identity section.** Under the presentation of
the relocalization functor `Over.map W.hom` as the category of elements of the presheaf
represented by `W` (`CategoryTheory.PresheafOfCategories.overMapElementsEquivalenceOver`), the
object `id_{W.left}` of `𝒞/W.left` lies over `W` and names the identity of `W`.

The identification of the object it lies over with `W` is not syntactic — it is
`id_{W.left} ≫ W.hom = W.hom` — so the section named is read off through
`CategoryTheory.PresheafOfCategories.sectionOfObj_eq_map_eqToHom`. -/
lemma sectionOfObj_overMapElements_taut {C : Type u₁} [Category.{v₁} C] {X : C} (W : Over X) :
    sectionOfObj (overMapElementsEquivalenceOver W.hom) (Over.mk (𝟙 W.left))
        (over_mk_eq W (Category.id_comp W.hom)) = 𝟙 W := by
  rw [sectionOfObj_eq_map_eqToHom]
  apply Over.OverMorphism.ext
  simp
  rfl

end CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (U : BigFppfOver B S hS)

/-- **An object of the big fppf site of `U`, with its structure morphism to `U` read in the big
fppf site of `S`.** Relocalizing `W` along `U ⟶ S` gives an object of the big fppf site of `S`,
and `W.hom` is then a morphism of that site to `U`. -/
abbrev sliceObjHom (W : BigFppfOver B U.left.1 U.left.2) :
    (Over.map U.hom).obj W ⟶ U :=
  Over.homMk W.hom

section Atlas

variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
  (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
  (hy : y ⋙ 𝒴.val.p = Over.map U.hom)
  (T : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)

include hy in
/-- **A section of the presheaf representing a base change is a 1-morphism into the 2-fibre
product, strictly over the slice.** Let `T` be a presheaf on the big fppf site of `U` equivalent,
over that site, to the first projection of `(Sch/U)_{fppf} ×_{y, 𝒴, f} 𝒳` — the comparison that
`AlgebraicGeometry.Stack.HasRelativeProperty` quantifies over. Every `a : h_W ⟶ T` is then a
1-morphism from the big fppf site of `W` to that 2-fibre product, lying strictly over
`CategoryTheory.Over.map` of the structure morphism of `W`.

Its value at the tautological object of the big fppf site of `W` is identified, by a vertical
isomorphism, with the object of the 2-fibre product that the section `a` names
(`StacksRepresentableCFG.objOfSection`). That identification is the only data tying the
1-morphism to the atlas member it came from, and
`AlgebraicGeometry.Stack.representingMap_sliceAtlasPoint` is what it is for.

This is `StacksRepresentableCFG.exists_pointOverMap_of_section` at the first projection, which is
fibred in groupoids over the slice by Stacks 02Y6
(`CategoryTheory.PresheafOfCategories.isFiberedInGroupoids_fst_overMap_of`). -/
theorem exists_sliceAtlasPoint
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f))
      (presheafOfCategories (T ⋙ typeToCat)).p)
    (W : BigFppfOver B U.left.1 U.left.2) (a : yoneda.obj W ⟶ T) :
    ∃ (c : BigFppfOver B W.left.1 W.left.2 ⥤
        TwoFibreProductOver (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
      (_ : c ⋙ TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f) =
        Over.map (sliceObjHom B S hS U W).left)
      (ξ : c.obj (Over.mk (𝟙 W.left)) ≅
        StacksRepresentableCFG.objOfSection e W (a.app (op W) (𝟙 W))),
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f)).IsHomLift (𝟙 W) ξ.hom :=
  StacksRepresentableCFG.exists_pointOverMap_of_section
    (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
      (CatFiberedInGroupoids.homFunctor f))
    (PresheafOfCategories.isFiberedInGroupoids_fst_overMap_of U.hom 𝒳.property 𝒴.property hy
      (CatFiberedInGroupoids.homFunctor_comp_p f))
    e W a

/-- **A 1-morphism into the 2-fibre product which is strictly over the slice is strictly over the
big fppf site of `S`.** Composing with the first projection of
`(Sch/U)_{fppf} ×_{y, 𝒴, f} 𝒳` and then with the structure 1-morphism of the slice is composing
with the structure functor of the 2-fibre product, by
`CategoryTheory.TwoFibreProductOver.fst_comp_eq`; the two structure morphisms then compose by
`CategoryTheory.Over.mapComp_eq`. -/
theorem comp_structureFunctor_of_comp_fst
    (W : BigFppfOver B U.left.1 U.left.2)
    (c : BigFppfOver B W.left.1 W.left.2 ⥤
      TwoFibreProductOver (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f))
    (hc : c ⋙ TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f) =
      Over.map (sliceObjHom B S hS U W).left) :
    c ⋙ TwoFibreProductOver.structureFunctor (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f) =
      Over.map ((Over.map U.hom).obj W).hom := by
  rw [← TwoFibreProductOver.fst_comp_eq, ← Functor.assoc, hc]
  exact (Over.mapComp_eq W.hom U.hom).symm

end Atlas

section Smooth

variable [IsLocallyNoetherian S]
  {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
  (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
  (hy : y ⋙ 𝒴.val.p = Over.map U.hom)

include hy in
/-- **The condition of Stacks 07XS for the structure morphism of an atlas of a base change.**
Let `c` be a 1-morphism from the big fppf site of `W` to `(Sch/U)_{fppf} ×_{y, 𝒴, f} 𝒳`, strictly
over `CategoryTheory.Over.map` of the structure morphism of `W` — for instance the one
`AlgebraicGeometry.Stack.exists_sliceAtlasPoint` attaches to an atlas member of a presheaf
representing the base change. If `f` satisfies the smoothness condition of Stacks 07XS, and so
does `c`, then so does the 1-morphism `(Sch/W)_{fppf} ⟶ (Sch/U)_{fppf}` induced by the structure
morphism of `W`.

The middle leg is **Stacks 07XV** at the ordering of the cospan that Stacks 03YK presents,
`Deformation.Artin.isSmoothOnPredeformationCategories_twoFibreProductFst`, and the two legs are
joined by **Stacks 07XU**. The hypothesis `hc` is **Stacks 07XW** read at `c`;
`AlgebraicGeometry.Stack.isSmoothOnPredeformationCategories_sliceAtlasPoint` discharges it for
the 1-morphism attached to a smooth atlas member.

It carries no tag: the content is the composition law Stacks 07XU applied to two instances
already registered, and the hypothesis `hc` is not one the source states separately. -/
theorem isSmoothOnPredeformationCategories_sliceObjHom
    (W : BigFppfOver B U.left.1 U.left.2)
    (c : BigFppfOver B W.left.1 W.left.2 ⥤
      TwoFibreProductOver (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f))
    (hcfst : c ⋙ TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f) =
      Over.map (sliceObjHom B S hS U W).left)
    (hc : Deformation.Artin.IsSmoothOnPredeformationCategories B S hS
      (Over.map ((Over.map U.hom).obj W).hom)
      (TwoFibreProductOver.structureFunctor (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f))
      c (comp_structureFunctor_of_comp_fst B S hS U f y W c hcfst))
    (hf : Deformation.Artin.IsSmoothOnPredeformationCategories B S hS 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor_comp_p f)) :
    Deformation.Artin.IsSmoothOnPredeformationCategories B S hS
      (Over.map ((Over.map U.hom).obj W).hom) (Over.map U.hom)
      (Over.map (sliceObjHom B S hS U W).left)
      (Over.mapComp_eq W.hom U.hom).symm := by
  have hF : (c ⋙ TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f)) ⋙ Over.map U.hom =
      Over.map ((Over.map U.hom).obj W).hom := by
    rw [Functor.assoc, TwoFibreProductOver.fst_comp_eq]
    exact comp_structureFunctor_of_comp_fst B S hS U f y W c hcfst
  have hG : Over.map (sliceObjHom B S hS U W).left ⋙ Over.map U.hom =
      Over.map ((Over.map U.hom).obj W).hom := (Over.mapComp_eq W.hom U.hom).symm
  have hfst : Deformation.Artin.IsSmoothOnPredeformationCategories B S hS
      (TwoFibreProductOver.structureFunctor (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f))
      (Over.map U.hom)
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f))
      TwoFibreProductOver.fst_comp_eq :=
    Deformation.Artin.isSmoothOnPredeformationCategories_twoFibreProductFst B S hS
      𝒳.val.p 𝒴.val.p (Over.map U.hom) (CatFiberedInGroupoids.homFunctor f) y
      𝒳.property 𝒴.property (Functor.IsFiberedInGroupoids.over_map U.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p f) hy hf
  have hcomp : Deformation.Artin.IsSmoothOnPredeformationCategories B S hS
      (Over.map ((Over.map U.hom).obj W).hom) (Over.map U.hom)
      (c ⋙ TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f)) hF :=
    Deformation.Artin.isSmoothOnPredeformationCategories_comp B S hS
      (Over.map ((Over.map U.hom).obj W).hom)
      (TwoFibreProductOver.structureFunctor (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f))
      (Over.map U.hom) c
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f))
      (comp_structureFunctor_of_comp_fst B S hS U f y W c hcfst)
      TwoFibreProductOver.fst_comp_eq hc hfst
  have hα : ∀ x : BigFppfOver B W.left.1 W.left.2, (Over.map U.hom).IsHomLift
      (𝟙 ((Over.map ((Over.map U.hom).obj W).hom).obj x))
      ((eqToIso hcfst).hom.app x) := by
    intro x
    rw [eqToIso.hom]
    refine IsHomLift.of_fac' (Over.map U.hom) _ _ (Functor.congr_obj hF x)
      (Functor.congr_obj hG x) ?_
    rw [eqToHom_app, eqToHom_map, Category.id_comp, eqToHom_trans]
  exact @Deformation.Artin.isSmoothOnPredeformationCategories_of_natIso B S hS _ _ _ _
    (Over.map ((Over.map U.hom).obj W).hom) (Over.map U.hom)
    (c ⋙ TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
      (CatFiberedInGroupoids.homFunctor f))
    (Over.map (sliceObjHom B S hS U W).left) hF hG (eqToIso hcfst) hα hcomp

include hy in
/-- **The atlas scheme of a base change along a scheme-valued point is smooth over the point.**
In the situation of
`AlgebraicGeometry.Stack.isSmoothOnPredeformationCategories_sliceObjHom`, with `W` and `U`
locally of finite type over a locally Noetherian `S`, the structure morphism `W ⟶ U` is a smooth
morphism of schemes.

This is the previous result followed by
`Deformation.Artin.smooth_of_isSmoothOnPredeformationCategories`, the case of **Stacks 07XX**
for a 1-morphism induced by a morphism of schemes. It is the step of the proof of Stacks 07XX
that produces the smoothness of an atlas of the base change;
`AlgebraicGeometry.Stack.isRelativelySmooth_of_isSmoothOnPredeformationCategories` assembles it
into Stacks 07XX for a general 1-morphism. -/
theorem smooth_sliceObjHom_of_isSmoothOnPredeformationCategories
    (W : BigFppfOver B U.left.1 U.left.2)
    [LocallyOfFiniteType ((Over.map U.hom).obj W).hom.hom]
    [LocallyOfFiniteType U.hom.hom]
    (c : BigFppfOver B W.left.1 W.left.2 ⥤
      TwoFibreProductOver (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f))
    (hcfst : c ⋙ TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f) =
      Over.map (sliceObjHom B S hS U W).left)
    (hc : Deformation.Artin.IsSmoothOnPredeformationCategories B S hS
      (Over.map ((Over.map U.hom).obj W).hom)
      (TwoFibreProductOver.structureFunctor (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f))
      c (comp_structureFunctor_of_comp_fst B S hS U f y W c hcfst))
    (hf : Deformation.Artin.IsSmoothOnPredeformationCategories B S hS 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor_comp_p f)) :
    Smooth (sliceObjHom B S hS U W).left.hom :=
  Deformation.Artin.smooth_of_isSmoothOnPredeformationCategories B S hS
    ((Over.map U.hom).obj W) U (sliceObjHom B S hS U W)
    (isSmoothOnPredeformationCategories_sliceObjHom B S hS U f y hy W c hcfst hc hf)

end Smooth

section Descent

/-- The structure morphism of `W` towards the terminal object of the big fppf site of `U` is the
composite of `a : h_W ⟶ F` with the structural morphism of `F`. -/
private lemma yoneda_map_homMk_eq_comp_toYonedaId
    {F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u}
    (W : BigFppfOver B U.left.1 U.left.2) (a : yoneda.obj W ⟶ F) :
    yoneda.map (Over.homMk W.hom (by simp) : W ⟶ Over.mk (𝟙 (B.obj U.left.2))) =
      a ≫ Space.toYonedaId B U.left.1 U.left.2 F := by
  ext Z k
  exact Over.OverMorphism.ext (Over.w k)

/-- **The structure morphism of an algebraic space over `U` is smooth once one scheme atlas of
it is smooth over `U`.** This is **Stacks 0AHD** in the smooth case
(`AlgebraicGeometry.Space.isSmooth_of_comp_surjective_isSmooth`) applied over the big fppf site
of `U` itself, to the triangle whose hypotenuse is the structure morphism of the atlas: that
morphism is `CategoryTheory.yoneda` of the structure morphism of `W` in the site of `U`, hence
smooth as a morphism of algebraic spaces as soon as the underlying morphism of schemes is
(Stacks 03MJ, in the form
`AlgebraicGeometry.Space.presheafImpliesHoldsOnEveryEtaleChart_of_etale_precomp`).

The morphism of schemes asked for is the one
`AlgebraicGeometry.Stack.smooth_sliceObjHom_of_isSmoothOnPredeformationCategories` produces. -/
theorem isSmooth_toYonedaId_of_smooth_atlas
    {F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (W : BigFppfOver B U.left.1 U.left.2) (a : yoneda.obj W ⟶ F)
    (hasurj : Space.IsSurjective B U.left.1 U.left.2 a)
    (hasm : Space.IsSmooth B U.left.1 U.left.2 a)
    (hW : Smooth (sliceObjHom B S hS U W).left.hom) :
    Space.IsSmooth B U.left.1 U.left.2 (Space.toYonedaId B U.left.1 U.left.2 F) := by
  -- The structure morphism of `W` towards the terminal object of the big fppf site of `U`.
  let φ : W ⟶ Over.mk (𝟙 (B.obj U.left.2)) := Over.homMk W.hom (by simp)
  have hyon : yoneda.map φ = _ := yoneda_map_homMk_eq_comp_toYonedaId B S hS U W a
  refine Space.isSmooth_of_comp_surjective_isSmooth B U.left.1 U.left.2
    (isAlgebraicSpace_yoneda B U.left.1 U.left.2 W) hF
    (isAlgebraicSpace_yoneda B U.left.1 U.left.2 (Over.mk (𝟙 (B.obj U.left.2))))
    a (yoneda.map φ) (Space.toYonedaId B U.left.1 U.left.2 F) hyon hasurj hasm ?_
  refine Space.presheafImpliesHoldsOnEveryEtaleChart_of_etale_precomp B U.left.1 U.left.2
    (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u}) (fun i p _ hp => ?_) _
    ((Space.presheaf_yoneda_map_iff B U.left.1 U.left.2 smooth_isStableUnderBaseChange φ).2 hW)
  have : Smooth p := hp
  infer_instance

/-- **The relative smoothness property of Stacks 03YK at one scheme-valued point, from a smooth
atlas of the representing algebraic space.** The structural morphism that
`AlgebraicGeometry.Stack.HasRelativeProperty` tests is read on the lower-shriek extension by
Stacks 04SG (`AlgebraicGeometry.Stack.prop_algebraicSpaceMap_iff`), and the every-étale-chart
condition for that extension is the same condition over the site of `U` itself
(`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff`); so the goal is
smoothness of `F` over `U`, which is the previous result. -/
theorem smoothMorphismProperty_algebraicSpaceMap_of_smooth_atlas
    {F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (W : BigFppfOver B U.left.1 U.left.2) (a : yoneda.obj W ⟶ F)
    (hasurj : Space.IsSurjective B U.left.1 U.left.2 a)
    (hasm : Space.IsSmooth B U.left.1 U.left.2 a)
    (hW : Smooth (sliceObjHom B S hS U W).left.hom) :
    Space.smoothMorphismProperty B S hS (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) := by
  have : (Space.smoothMorphismProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (prop_algebraicSpaceMap_iff B S hS (Space.smoothMorphismProperty B S hS) U F hF).mpr <|
    (Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B U.left.1 S U.left.2 hS U.hom
      (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u}) F).mpr
      (isSmooth_toYonedaId_of_smooth_atlas B S hS U hF W a hasurj hasm hW)

end Descent

section AtlasFiniteType

/-- **A base change locally of finite presentation over `S` is locally of finite type over the
point.** The structural morphism that `AlgebraicGeometry.Stack.HasRelativeProperty` tests on an
algebraic space `F` over `U` is the image of `F` under the forward functor of **Stacks 04SG**;
local finite presentation of that morphism over `S` is the every-étale-chart condition, over `U`
itself, for the structural morphism of `F` to the terminal object of the big fppf site of `U`
(`AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_algebraicSpaceMap_iff_toYonedaId`), and local
finite presentation implies local finite type (**Stacks 0464**).

The hypothesis is the value at one scheme-valued point of the relative property of Stacks 03YK
at the locally-of-finite-presentation property, which is the shape in which **Stacks 06CX**
(`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation`)
delivers local finite presentation of a 1-morphism limit preserving on objects. -/
theorem isLocallyOfFiniteType_toYonedaId_of_isLocallyOfFinitePresentation_algebraicSpaceMap
    {F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (hFfp : Space.IsLocallyOfFinitePresentation B S hS
      (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom) :
    Space.IsLocallyOfFiniteType B U.left.1 U.left.2 (Space.toYonedaId B U.left.1 U.left.2 F) :=
  Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B U.left.1 U.left.2
    ((holdsOnEveryEtaleChart_algebraicSpaceMap_iff_toYonedaId (B := B) (S := S) (hS := hS)
      (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      U F hF).mp hFfp)

/-- **Every smooth atlas member of an algebraic space locally of finite type over `U` is itself
locally of finite type over `U`.** No *choice* of atlas is involved: for an arbitrary object `W`
of the big fppf site of `U` and an arbitrary smooth `a : h_W ⟶ F`, the structure morphism
`W ⟶ U` is locally of finite type as soon as `F` is locally of finite type over `U`.

The reason is that the structure morphism of `W` towards the terminal object of the big fppf
site of `U` *is* the composite `a ≫ (F ⟶ ∗)` — the same identity that
`AlgebraicGeometry.Stack.isSmooth_toYonedaId_of_smooth_atlas` uses in the other direction — so
the claim is local finite type of a composite of morphisms of algebraic spaces. A smooth
morphism is locally of finite type (**Stacks 06MH**) and local finite type is stable under
composition (**Stacks 03XG**); reading the conclusion back on the morphism of schemes is
**Stacks 03MJ** for a morphism of the site
(`AlgebraicGeometry.Space.isLocallyOfFiniteType_yoneda_map_iff`).

Neither surjectivity of `a` nor the atlas clause of Stacks 025Y is used. -/
theorem locallyOfFiniteType_sliceObjHom_of_isSmooth_atlas
    {F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (hFft : Space.IsLocallyOfFiniteType B U.left.1 U.left.2
      (Space.toYonedaId B U.left.1 U.left.2 F))
    (W : BigFppfOver B U.left.1 U.left.2) (a : yoneda.obj W ⟶ F)
    (hasm : Space.IsSmooth B U.left.1 U.left.2 a) :
    LocallyOfFiniteType (sliceObjHom B S hS U W).left.hom := by
  -- The structure morphism of `W` towards the terminal object of the big fppf site of `U`.
  let φ : W ⟶ Over.mk (𝟙 (B.obj U.left.2)) := Over.homMk W.hom (by simp)
  have hyon : yoneda.map φ = _ := yoneda_map_homMk_eq_comp_toYonedaId B S hS U W a
  refine (Space.isLocallyOfFiniteType_yoneda_map_iff B U.left.1 U.left.2 φ).1 ?_
  rw [hyon]
  exact Space.isLocallyOfFiniteType_comp B U.left.1 U.left.2
    (isAlgebraicSpace_yoneda B U.left.1 U.left.2 W) hF
    (isAlgebraicSpace_yoneda B U.left.1 U.left.2 (Over.mk (𝟙 (B.obj U.left.2))))
    a (Space.toYonedaId B U.left.1 U.left.2 F)
    (Space.isLocallyOfFiniteType_of_isSmooth B U.left.1 U.left.2 hasm) hFft

/-- **The atlas member of a base change locally of finite presentation over the point is locally
of finite type over `S`.** This is the hypothesis that
`AlgebraicGeometry.Stack.smooth_sliceObjHom_of_isSmoothOnPredeformationCategories` carries on the
atlas scheme, discharged from local finite presentation of the base change over the point
(the previous two results) together with local finite type of the point itself. -/
theorem locallyOfFiniteType_relocalize_of_isSmooth_atlas [LocallyOfFiniteType U.hom.hom]
    {F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (hFfp : Space.IsLocallyOfFinitePresentation B S hS
      (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom)
    (W : BigFppfOver B U.left.1 U.left.2) (a : yoneda.obj W ⟶ F)
    (hasm : Space.IsSmooth B U.left.1 U.left.2 a) :
    LocallyOfFiniteType ((Over.map U.hom).obj W).hom.hom :=
  MorphismProperty.comp_mem
    (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) _ _
    (locallyOfFiniteType_sliceObjHom_of_isSmooth_atlas B S hS U hF
      (isLocallyOfFiniteType_toYonedaId_of_isLocallyOfFinitePresentation_algebraicSpaceMap
        B S hS U hF hFfp) W a hasm)
    ‹LocallyOfFiniteType U.hom.hom›

end AtlasFiniteType

section AtlasSmooth

variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
  (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
  (T : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
  (e : StacksRepresentableCFG.EquivalenceOver
    (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
      (CatFiberedInGroupoids.homFunctor f))
    (presheafOfCategories (T ⋙ typeToCat)).p)

/-- The identity section of `h_{W/S}` is named by the tautological object of the big fppf site of
`W`, read through `AlgebraicGeometry.Stack.schemeSliceEquivalenceOver`. -/
lemma sectionOfObj_schemeSliceEquivalenceOver_taut (V : BigFppfOver B S hS) :
    PresheafOfCategories.sectionOfObj (schemeSliceEquivalenceOver B S hS V)
        (Over.mk (𝟙 V.left)) (PresheafOfCategories.over_mk_eq V (Category.id_comp V.hom)) =
      𝟙 V :=
  PresheafOfCategories.sectionOfObj_overMapElements_taut V

/-- **The section of `Λ_U T` named by the object a section of `T` names.** The object of the
2-fibre product that a section `s` of `T` over `W` names (`StacksRepresentableCFG.objOfSection`)
lies over `W` relocalized to the big fppf site of `S`, and through
`AlgebraicGeometry.Stack.relocalizeFibreEquivalence` it names the section of the lower-shriek
extension `Λ_U T` carrying the structure morphism of `W` as its factorization and `s` as its
section. -/
lemma sectionOfObj_relocalizeFibreEquivalence_objOfSection
    (W : BigFppfOver B U.left.1 U.left.2) (s : T.obj (op W))
    (hobj : (TwoFibreProductOver.structureFunctor (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f)).obj
        (StacksRepresentableCFG.objOfSection e W s) = (Over.map U.hom).obj W) :
    PresheafOfCategories.sectionOfObj (relocalizeFibreEquivalence B S hS U f y T e)
        (StacksRepresentableCFG.objOfSection e W s) hobj =
      OverShriek.relocalizeMk (W := op ((Over.map U.hom).obj W)) U.hom T W.hom s rfl := by
  rw [relocalizeFibreEquivalence, PresheafOfCategories.sectionOfObj_ofEq,
    PresheafOfCategories.sectionOfObj_trans]
  refine Eq.trans ?_ (PresheafOfCategories.sectionOfObj_relocalizeElementsEquivalenceOver U.hom T
    (⟨W, Discrete.mk s⟩ : (presheafOfCategories (T ⋙ typeToCat)).obj))
  refine PresheafOfCategories.sectionOfObj_eq_of_fiberIso _ _ _
    (Functor.Fiber.isoMk (e.counitIso.app (⟨W, Discrete.mk s⟩ :
      (presheafOfCategories (T ⋙ typeToCat)).obj)) ?_)
  exact StacksRepresentableCFG.isHomLift_comp_of_isHomLift_id
    (presheafOfCategories (T ⋙ typeToCat)).p (Over.map U.hom) _
    (e.isHomLift_counitIso_hom_app (⟨W, Discrete.mk s⟩ :
      (presheafOfCategories (T ⋙ typeToCat)).obj))

/-- The same for any object of the 2-fibre product vertically isomorphic to the one a section of
`T` over `W` names: objects of one fibre identified by a vertical isomorphism name the same
section (`CategoryTheory.PresheafOfCategories.sectionOfObj_eq_of_fiberIso`), and verticality for
the first projection gives verticality for the structure functor
(`CategoryTheory.TwoFibreProductOver.fst_comp_eq`). -/
lemma sectionOfObj_relocalizeFibreEquivalence_of_iso
    (W : BigFppfOver B U.left.1 U.left.2) (s : T.obj (op W))
    (x : TwoFibreProductOver (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
      (CatFiberedInGroupoids.homFunctor f))
    (hx : (TwoFibreProductOver.structureFunctor (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
      (CatFiberedInGroupoids.homFunctor f)).obj x = (Over.map U.hom).obj W)
    (ξ : x ≅ StacksRepresentableCFG.objOfSection e W s)
    (hξ : (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
      (CatFiberedInGroupoids.homFunctor f)).IsHomLift (𝟙 W) ξ.hom) :
    PresheafOfCategories.sectionOfObj (relocalizeFibreEquivalence B S hS U f y T e) x hx =
      OverShriek.relocalizeMk (W := op ((Over.map U.hom).obj W)) U.hom T W.hom s rfl := by
  have hobj : (TwoFibreProductOver.structureFunctor (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
      (CatFiberedInGroupoids.homFunctor f)).obj
      (StacksRepresentableCFG.objOfSection e W s) = (Over.map U.hom).obj W := by
    rw [← TwoFibreProductOver.fst_comp_eq]
    exact congrArg (Over.map U.hom).obj (StacksRepresentableCFG.obj_objOfSection e W s)
  have hξ' : (TwoFibreProductOver.structureFunctor (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
      (CatFiberedInGroupoids.homFunctor f)).IsHomLift
      (𝟙 ((Over.map U.hom).obj W)) ξ.hom := by
    rw [← TwoFibreProductOver.fst_comp_eq]
    exact StacksRepresentableCFG.isHomLift_comp_of_isHomLift_id _ (Over.map U.hom) _ hξ
  rw [PresheafOfCategories.sectionOfObj_eq_of_fiberIso _ hx hobj (Functor.Fiber.isoMk ξ hξ')]
  exact sectionOfObj_relocalizeFibreEquivalence_objOfSection B S hS U f y T e W s hobj

/-- **The morphism of representing presheaves induced by an atlas point (Stacks 04SW).** Let `ĉ`
be a 1-morphism from the big fppf site of `W`, relocalized over `S`, to the 2-fibre product
`(Sch/U)_{fppf} ×_{y, 𝒴, f} 𝒳`, whose value at the tautological object is identified by a
vertical isomorphism with the object that a section `a : h_W ⟶ T` names. Then the morphism of
representing presheaves it induces is `Λ_U a`, read through the presentation of `h_{W/S}` as
`Λ_U h_{W/U}` of Stacks 03I4 part (2)
(`CategoryTheory.OverShriek.relocalizeYonedaFactorIso`).

This is what ties `ĉ` to the atlas member it came from. The morphism of presheaves goes out of a
representable one, so the Yoneda lemma reduces the claim to its value at the identity section;
that value is computed by **Stacks 04SW**
(`AlgebraicGeometry.Stack.morphismSpaceEquiv_app_sectionOfObj`) at the tautological object, which
names the identity section on the source
(`AlgebraicGeometry.Stack.sectionOfObj_schemeSliceEquivalenceOver_taut`) and, by the vertical
identification, the section `(W.hom, a(id_W))` of `Λ_U T` on the target. -/
lemma representingMap_sliceAtlasPoint (hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (W : BigFppfOver B U.left.1 U.left.2) (a : yoneda.obj W ⟶ T)
    (ĉ : schemeSlice B S hS ((Over.map U.hom).obj W) ⟶
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (schemeSliceMap B S hS U y hy) f).pt)
    (ξ : (CatFiberedInGroupoids.homFunctor ĉ).obj (Over.mk (𝟙 W.left)) ≅
      StacksRepresentableCFG.objOfSection e W (a.app (op W) (𝟙 W)))
    (hξ : (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
      (CatFiberedInGroupoids.homFunctor f)).IsHomLift (𝟙 W) ξ.hom) :
    representingMap B S hS (schemeSlice B S hS ((Over.map U.hom).obj W))
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (schemeSliceMap B S hS U y hy) f).pt
        (yoneda.obj ((Over.map U.hom).obj W))
        ((OverShriek.relocalizePresheafFunctor U.hom).obj T)
        (schemeSliceEquivalenceOver B S hS ((Over.map U.hom).obj W))
        (relocalizeFibreEquivalence B S hS U f y T e) ĉ =
      (OverShriek.relocalizeYonedaFactorIso (W := (Over.map U.hom).obj W) (ψ := W.hom)
          U.hom rfl).hom ≫
        (OverShriek.relocalizePresheafFunctor U.hom).map a := by
  have hmain := morphismSpaceEquiv_app_sectionOfObj B S hS
    (schemeSlice B S hS ((Over.map U.hom).obj W))
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (schemeSliceMap B S hS U y hy) f).pt
    (yoneda.obj ((Over.map U.hom).obj W))
    ((OverShriek.relocalizePresheafFunctor U.hom).obj T)
    (schemeSliceEquivalenceOver B S hS ((Over.map U.hom).obj W))
    (relocalizeFibreEquivalence B S hS U f y T e)
    ⟨CatFiberedInGroupoids.homFunctor ĉ, CatFiberedInGroupoids.homFunctor_comp_p ĉ⟩
    (Over.mk (𝟙 ((Over.map U.hom).obj W).left))
    (PresheafOfCategories.over_mk_eq ((Over.map U.hom).obj W)
      (Category.id_comp ((Over.map U.hom).obj W).hom))
  rw [sectionOfObj_schemeSliceEquivalenceOver_taut] at hmain
  have hiota : yonedaEquiv (OverShriek.relocalizeYonedaFactorIso
      (W := (Over.map U.hom).obj W) (ψ := W.hom) U.hom rfl).hom =
      OverShriek.relocalizeMk (W := op ((Over.map U.hom).obj W)) U.hom (yoneda.obj W) W.hom
        (𝟙 W) rfl := by
    rw [OverShriek.relocalizeYonedaFactorIso_hom, OverShriek.relocalizeYonedaFactorHom]
    exact Equiv.apply_symm_apply _ _
  refine yonedaEquiv.injective ?_
  rw [yonedaEquiv_comp, hiota]
  exact ((yonedaEquiv_apply _).trans (hmain.trans
    (sectionOfObj_relocalizeFibreEquivalence_of_iso B S hS U f y T e W
      (a.app (op W) (𝟙 W)) _ _ ξ hξ))).trans rfl

/-- **The relocalization of a smooth atlas member is a smooth morphism of algebraic spaces over
`S`.** The every-étale-chart condition of Stacks 03MJ is unchanged by the lower-shriek extension
(`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeMap_iff`) and by precomposition with
an isomorphism. -/
lemma isSmooth_relocalizeYonedaFactorIso_comp
    (W : BigFppfOver B U.left.1 U.left.2) (a : yoneda.obj W ⟶ T)
    (hasm : Space.IsSmooth B U.left.1 U.left.2 a) :
    Space.IsSmooth B S hS ((OverShriek.relocalizeYonedaFactorIso
        (W := (Over.map U.hom).obj W) (ψ := W.hom) U.hom rfl).hom ≫
      (OverShriek.relocalizePresheafFunctor U.hom).map a) :=
  (Space.holdsOnEveryEtaleChart_iso_comp_iff B S hS
      (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u})
      (OverShriek.relocalizeYonedaFactorIso (W := (Over.map U.hom).obj W) (ψ := W.hom)
        U.hom rfl).hom
      ((OverShriek.relocalizePresheafFunctor U.hom).map a)).mpr
    ((Space.holdsOnEveryEtaleChart_relocalizeMap_iff B U.left.1 S U.left.2 hS U.hom
      (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u}) a).mpr hasm)

/-- **An atlas point of the base change is a smooth 1-morphism in the sense of Stacks 04XB.**
Both its source and its target are representable by algebraic spaces over `S` — the source by
`h_{W/S}` (`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_schemeSlice`), the target by
`Λ_U T` (`AlgebraicGeometry.Stack.relocalizeFibreEquivalence`) — so the bridge of Stacks 04XB
(`AlgebraicGeometry.Stack.isRelativelySmooth_iff_isSmooth_representingMap`) reads its relative
smoothness on the induced morphism of representing presheaves, which
`AlgebraicGeometry.Stack.representingMap_sliceAtlasPoint` identifies with `Λ_U a`. -/
theorem isRelativelySmooth_sliceAtlasPoint (hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (hT : IsAlgebraicSpace B U.left.1 U.left.2 T)
    (W : BigFppfOver B U.left.1 U.left.2) (a : yoneda.obj W ⟶ T)
    (hasm : Space.IsSmooth B U.left.1 U.left.2 a)
    (ĉ : schemeSlice B S hS ((Over.map U.hom).obj W) ⟶
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (schemeSliceMap B S hS U y hy) f).pt)
    (ξ : (CatFiberedInGroupoids.homFunctor ĉ).obj (Over.mk (𝟙 W.left)) ≅
      StacksRepresentableCFG.objOfSection e W (a.app (op W) (𝟙 W)))
    (hξ : (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
      (CatFiberedInGroupoids.homFunctor f)).IsHomLift (𝟙 W) ξ.hom) :
    IsRelativelySmooth B S hS ĉ := by
  have hΛ := isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom T hT
  have htgt : IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (schemeSliceMap B S hS U y hy) f).pt :=
    ⟨(OverShriek.relocalizePresheafFunctor U.hom).obj T, hΛ,
      ⟨relocalizeFibreEquivalence B S hS U f y T e⟩⟩
  refine (isRelativelySmooth_iff_isSmooth_representingMap B S hS ĉ
    (isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS ĉ
      (isRepresentableByAlgebraicSpace_schemeSlice B S hS ((Over.map U.hom).obj W)) htgt)
    (yoneda.obj ((Over.map U.hom).obj W))
    ((OverShriek.relocalizePresheafFunctor U.hom).obj T)
    (isAlgebraicSpace_yoneda B S hS ((Over.map U.hom).obj W)) hΛ
    (schemeSliceEquivalenceOver B S hS ((Over.map U.hom).obj W))
    (relocalizeFibreEquivalence B S hS U f y T e)).mpr ?_
  rw [representingMap_sliceAtlasPoint B S hS U f y T e hy W a ĉ ξ hξ]
  exact isSmooth_relocalizeYonedaFactorIso_comp B S hS U T W a hasm

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance (priority := high) hasPullback_presheaf_TwoFibreProductSliceAtlas
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Limits.HasLimit (Limits.cospan f g) :=
  Limits.HasLimitsOfShape.has_limit _

/-- **A base change of a morphism into an algebraic space over `S`, along an arbitrary morphism
of presheaves, is representable by schemes when the morphism being based changed goes out of a
representable presheaf.** The diagonal clause of `AlgebraicGeometry.IsAlgebraicSpace` makes every
morphism out of a representable presheaf relatively representable
(`CategoryTheory.Functor.relativelyRepresentable.of_diag`), and relative representability is
stable under base change.

It is the *diagonal* clause of Stacks 025Y that is used, not the atlas clause. The binary
products that the criterion of `CategoryTheory.Functor.relativelyRepresentable.of_diag` asks of
the site come from its terminal object and its fibre products. -/
theorem relativelyRepresentable_pullbackFst_of_isAlgebraicSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W : BigFppfOver B S hS}
    (b : A ⟶ X) (m : yoneda.obj W ⟶ X) :
    yoneda.relativelyRepresentable (Limits.pullback.fst b m) :=
  let : Limits.HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks (BigFppfOver B S hS)
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback b m).flip
    (hX.diagonal_representable.of_diag m)

include e in
/-- **The representability hypothesis of the library's clause of Stacks 07XW is automatic at an
atlas point.** Let `ĉ` be *any* 1-morphism from the big fppf site of an object `W` of the site of
`U`, relocalized over `S`, to the 2-fibre product `(Sch/U)_{fppf} ×_{y, 𝒴, f} 𝒳`. Then every
algebraic space `G` over an object `V` of the big fppf site of `S` which represents a base change
of `ĉ` along a scheme-valued point of the 2-fibre product is representable by *schemes*, in the
sense that the structural morphism `Λ_V G ⟶ h_V` of its lower-shriek extension is relatively
representable.

This is the hypothesis `hrep` of
`Deformation.Artin.isSmoothOnPredeformationCategories_of_isRelativelySmooth_of_representable`
read at `ĉ`, and it holds for a reason the general clause cannot use. The source of `ĉ` is a
slice of the site, so *its* representing presheaf is representable; the target is representable
by `Λ_U T`, which is an algebraic space over `S`
(`AlgebraicGeometry.Space.isAlgebraicSpace_viewOver`). The structural morphism of `Λ_V G` is the
base change of the induced morphism of representing presheaves along the scheme-valued point
(`AlgebraicGeometry.Stack.arrowIsoRelocalizeFibrePullback`), hence a base change of a morphism
*from a representable presheaf* into an algebraic space, which
`AlgebraicGeometry.Stack.relativelyRepresentable_pullbackFst_of_isAlgebraicSpace` makes
relatively representable.

Nothing is needed about *which* morphism of representing presheaves `ĉ` induces, so neither the
atlas member nor its smoothness appears; in particular the computation of
`AlgebraicGeometry.Stack.representingMap_sliceAtlasPoint` is not used here. -/
theorem relativelyRepresentable_relocalizeToYoneda_sliceAtlasPoint
    (hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (hT : IsAlgebraicSpace B U.left.1 U.left.2 T)
    (W : BigFppfOver B U.left.1 U.left.2)
    (ĉ : schemeSlice B S hS ((Over.map U.hom).obj W) ⟶
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (schemeSliceMap B S hS U y hy) f).pt)
    (V : BigFppfOver B S hS)
    (v : BigFppfOver B V.left.1 V.left.2 ⥤
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (schemeSliceMap B S hS U y hy) f).pt.val.obj)
    (hv : v ⋙ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (schemeSliceMap B S hS U y hy) f).pt.val.p = Over.map V.hom)
    (G : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (hG : IsAlgebraicSpace B V.left.1 V.left.2 G)
    (he : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map V.hom)
        (schemeSlice B S hS ((Over.map U.hom).obj W)).val.p
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (schemeSliceMap B S hS U y hy) f).pt.val.p v
        (CatFiberedInGroupoids.homFunctor ĉ))
      (presheafOfCategories (G ⋙ typeToCat)).p) :
    yoneda.relativelyRepresentable (OverShriek.relocalizeToYoneda V.hom G) := by
  have hΛ : IsAlgebraicSpace B S hS ((OverShriek.relocalizePresheafFunctor U.hom).obj T) :=
    isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom T hT
  exact (MorphismProperty.arrow_mk_iso_iff
    (yoneda.relativelyRepresentable.inverseImage
      (ObjectProperty.ι fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
    (arrowIsoRelocalizeFibrePullback B S hS V ĉ v hv
      (yoneda.obj ((Over.map U.hom).obj W))
      ((OverShriek.relocalizePresheafFunctor U.hom).obj T)
      (schemeSliceEquivalenceOver B S hS ((Over.map U.hom).obj W))
      (relocalizeFibreEquivalence B S hS U f y T e)
      (isAlgebraicSpace_yoneda B S hS ((Over.map U.hom).obj W)) hΛ G he hG)).mp
    (relativelyRepresentable_pullbackFst_of_isAlgebraicSpace B S hS hΛ _ _)

/-- **Stacks 07XW at an atlas point of the base change.** The atlas point is smooth by
`AlgebraicGeometry.Stack.isRelativelySmooth_sliceAtlasPoint`, so the representable-and-smooth
clause of Stacks 07XW
(`Deformation.Artin.isSmoothOnPredeformationCategories_of_isRelativelySmooth_of_representable`)
gives it the condition of **Stacks 07XS**.

The hypothesis `hrep` that clause carries beyond the source is discharged here by
`AlgebraicGeometry.Stack.relativelyRepresentable_relocalizeToYoneda_sliceAtlasPoint`, so this
statement carries no representability hypothesis of its own. -/
theorem isSmoothOnPredeformationCategories_sliceAtlasPoint [IsLocallyNoetherian S]
    (hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (hT : IsAlgebraicSpace B U.left.1 U.left.2 T)
    (W : BigFppfOver B U.left.1 U.left.2) (a : yoneda.obj W ⟶ T)
    (hasm : Space.IsSmooth B U.left.1 U.left.2 a)
    (ĉ : schemeSlice B S hS ((Over.map U.hom).obj W) ⟶
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (schemeSliceMap B S hS U y hy) f).pt)
    (ξ : (CatFiberedInGroupoids.homFunctor ĉ).obj (Over.mk (𝟙 W.left)) ≅
      StacksRepresentableCFG.objOfSection e W (a.app (op W) (𝟙 W)))
    (hξ : (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
      (CatFiberedInGroupoids.homFunctor f)).IsHomLift (𝟙 W) ξ.hom) :
    Deformation.Artin.IsSmoothOnPredeformationCategories B S hS
      (Over.map ((Over.map U.hom).obj W).hom)
      (TwoFibreProductOver.structureFunctor (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f))
      (CatFiberedInGroupoids.homFunctor ĉ)
      (CatFiberedInGroupoids.homFunctor_comp_p ĉ) :=
  Deformation.Artin.isSmoothOnPredeformationCategories_of_isRelativelySmooth_of_representable
    B S hS ĉ
    (isRelativelySmooth_sliceAtlasPoint B S hS U f y T e hy hT W a hasm ĉ ξ hξ)
    fun V v hv G hG he =>
      relativelyRepresentable_relocalizeToYoneda_sliceAtlasPoint B S hS U f y T e hy hT W ĉ
        V v hv G hG he.some

end AtlasSmooth

section Assembly

variable [IsLocallyNoetherian S]
  {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)

/-- **The smoothness condition of Stacks 07XS for `f` makes `f` smooth in the sense of
Stacks 03YK.**

This is the reduction step of **Stacks 07XX**. Given a scheme-valued point `V` of `𝒴` and an
algebraic space `F` representing the base change along it, the atlas of `F` supplied by
Stacks 025Y (`AlgebraicGeometry.Space.exists_isSurjective_isSmooth_atlas`) becomes a 1-morphism
`c` into the 2-fibre product by `AlgebraicGeometry.Stack.exists_sliceAtlasPoint`, keeping the
vertical identification of its value at the tautological object with the object the atlas member
names; `AlgebraicGeometry.Stack.isSmoothOnPredeformationCategories_sliceAtlasPoint` gives it the
condition of **Stacks 07XS**, and
`AlgebraicGeometry.Stack.smooth_sliceObjHom_of_isSmoothOnPredeformationCategories` then makes the
atlas scheme smooth over `V`. Descent along the atlas (**Stacks 0AHD**) upgrades that to
smoothness of `F` over `V`, which is what Stacks 03YK asks.

The two finite-type hypotheses that
`Deformation.Artin.smooth_of_isSmoothOnPredeformationCategories` needs are *derived*, as the
source derives them. The point `V` is made affine and locally of finite presentation over `S` by
the reduction of **Stacks 07WI**
(`AlgebraicGeometry.Stack.hasRelativeProperty_of_affine_locallyOfFinitePresentation`), which is
what `hlimY` is for; and the atlas scheme is made locally of finite type over `S` by
`AlgebraicGeometry.Stack.locallyOfFiniteType_relocalize_of_isSmooth_atlas` out of local finite
presentation of the base change over the point, which is what `hlimX` and `hlimY` are for,
through the cancellation for Stacks 06CU
(`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_toTerminalCFG`) and **Stacks 06CX**.

The hypotheses are exactly the source's: `hfrep` is its (1), `hf` its (2), `hlimX` its (3) and
`hlimY` its (4). The tag is carried by
`AlgebraicGeometry.Stack.isRelativelySmooth_of_isSmoothOnPredeformationCategories`, which is this
result paired with `hfrep` and so states the source's conclusion. -/
theorem hasRelativeProperty_smooth_of_isSmoothOnPredeformationCategories
    (hfrep : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hlimX : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒳
      (terminalCFG B S hS) (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳)))
    (hlimY : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒴)
    (hf : Deformation.Artin.IsSmoothOnPredeformationCategories B S hS 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor_comp_p f)) :
    HasRelativeProperty B S hS (Space.smoothMorphismProperty B S hS) f hfrep := by
  -- the locality instance of Stacks 0429, at the index universe the relative property leaves open
  have _ : (Space.smoothMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) := inferInstance
  -- the cancellation for Stacks 06CU: conditions (3) and (4) make `f` limit preserving on objects
  have hlimf : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS 𝒳 𝒴 f :=
    isLimitPreservingOnObjects_of_toTerminalCFG.{u, u, u} B S hS 𝒳 𝒴 f hlimX hlimY
  -- Stacks 06CX: `f` limit preserving on objects is `f` locally of finite presentation
  have hfp := (isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation B S hS 𝒳 𝒴 f
    hfrep).1 hlimf
  refine hasRelativeProperty_of_affine_locallyOfFinitePresentation.{u, u, u} B S hS
    (Space.smoothMorphismProperty B S hS) f hfrep
    (isLimitPreservingOnObjects_toTerminalCFG_of_isLimitPreserving B S hS 𝒴 hlimY) ?_
  intro V _hVaff hVfp y hy F hF he
  let : LocallyOfFinitePresentation V.hom.hom := hVfp
  let : LocallyOfFiniteType V.hom.hom := inferInstance
  obtain ⟨W, a, hasurj, hasm⟩ := Space.exists_isSurjective_isSmooth_atlas B V.left.1 V.left.2 hF
  obtain ⟨c, hcfst, ξ, hξ⟩ := exists_sliceAtlasPoint B S hS V f y hy F he.some W a
  let : LocallyOfFiniteType ((Over.map V.hom).obj W).hom.hom :=
    locallyOfFiniteType_relocalize_of_isSmooth_atlas B S hS V hF (hfp V y hy F hF he) W a hasm
  refine smoothMorphismProperty_algebraicSpaceMap_of_smooth_atlas B S hS V hF W a hasurj hasm
    (smooth_sliceObjHom_of_isSmoothOnPredeformationCategories B S hS V f y hy W c hcfst ?_ hf)
  exact isSmoothOnPredeformationCategories_sliceAtlasPoint B S hS V f y F he.some hy hF W a hasm
    (schemeSliceMap B S hS ((Over.map V.hom).obj W) c
      (comp_structureFunctor_of_comp_fst B S hS V f y W c hcfst)) ξ hξ

/-- **Stacks 07XX.** Let `S` be a locally Noetherian scheme and `f : 𝒳 ⟶ 𝒴` a 1-morphism of
categories fibred in groupoids over the big fppf site of `S`. If (1) `f` is representable by
algebraic spaces, (2) `f` satisfies the deformation-theoretic smoothness condition of
**Stacks 07XS**, (3) the structure morphism `𝒳 ⟶ (Sch/S)_{fppf}` is limit preserving on objects
in the sense of **Stacks 06CU**, and (4) `𝒴` is limit preserving in the sense of **Stacks 07XL**,
then `f` is smooth.

`AlgebraicGeometry.Stack.IsRelativelySmooth` bundles the representability witness with the
relative property of Stacks 03YK at the smooth property, which is what "smooth" means for a
1-morphism, so this is
`AlgebraicGeometry.Stack.hasRelativeProperty_smooth_of_isSmoothOnPredeformationCategories` paired
with `hfrep`. Condition (3) enters only through the cancellation for Stacks 06CU,
`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_toTerminalCFG`.

The case of a 1-morphism induced by a morphism of schemes — the key ingredient, where the
appeal to More on Morphisms is made — is
`Deformation.Artin.smooth_of_isSmoothOnPredeformationCategories`. -/
@[stacks 07XX "the general 1-morphism, at the source's own hypotheses: (1) hfrep, (2) hf, \
(3) hlimX, (4) hlimY, and S locally Noetherian. The case of a 1-morphism induced by a morphism \
of schemes is smooth_of_isSmoothOnPredeformationCategories"]
theorem isRelativelySmooth_of_isSmoothOnPredeformationCategories
    (hfrep : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hlimX : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒳
      (terminalCFG B S hS) (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳)))
    (hlimY : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒴)
    (hf : Deformation.Artin.IsSmoothOnPredeformationCategories B S hS 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor_comp_p f)) :
    IsRelativelySmooth B S hS f :=
  ⟨hfrep, hasRelativeProperty_smooth_of_isSmoothOnPredeformationCategories.{u, u} B S hS f hfrep
    hlimX hlimY hf⟩

end Assembly

end AlgebraicGeometry.Stack

end
