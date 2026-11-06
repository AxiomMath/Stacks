module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackIsFreeModule
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFreeLocusChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GeometricPointStalkSections

/-!
# The geometric fibre of a morphism of algebraic spaces, and clause (3) of Stacks 0CZS

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`ȳ` be a geometric point of `Y`.  The **geometric fibre** `X_ȳ` is the fibre product
`X ×_{Y, ȳ} Spec(κ(ȳ))`, formed in the category of algebraic spaces over `S`: the spectrum of the
field of a geometric point is an object of the big fppf site, hence a representable algebraic
space, the geometric point is a morphism of algebraic spaces out of it, and fibre products of
algebraic spaces exist by Stacks 02X2.  This is the algebraic-space analogue of the scheme-level
`AlgebraicGeometry.geometricFibre`.

A geometric point `x̄` of `X` has a canonical lift to the geometric fibre over `ȳ = f ∘ x̄`: the
two morphisms `Spec(κ(x̄)) ⟶ X` and `Spec(κ(x̄)) ⟶ Spec(κ(ȳ))` classifying `x̄` and the
tautological point agree over `Y`, so they factor through the fibre, over the *same* field — so the
lift is again a geometric point.

With those in hand, clause (3) of Stacks 0CZS — `F_ȳ` is finite free in an étale neighbourhood of
`x̄` *inside* the geometric fibre `X_ȳ` — is the statement that the lift of `x̄` lies in the
finite-free étale locus of the inverse image of `F` to the fibre.  The source calls the implication
`(4) ⟹ (3)` immediate, and so it is here: the étale free locus only grows under an inverse image,
because an étale neighbourhood trivializing `F` pulls back to one trivializing its inverse image.

## Main definitions

* `AlgebraicGeometry.Space.geometricFibre`, `AlgebraicGeometry.Space.geometricFibreToSource` and
  `AlgebraicGeometry.Space.geometricFibreToPoint`: the geometric fibre `X_ȳ` and its two
  projections.
* `AlgebraicGeometry.Space.geometricFibrePoint`: the canonical lift of a geometric point `x̄` of
  `X` to the geometric fibre over `ȳ = f ∘ x̄`.

## Main results

* `AlgebraicGeometry.Space.isFiniteFreeModule_modulePullback`: **Stacks 03DF (2) for the inverse
  image of Stacks 03LU** — the inverse image of a finite free module along a morphism of algebraic
  spaces is finite free.
* the finite-free étale locus grows under an arbitrary inverse image:
`AlgebraicGeometry.Space.preimage_etaleFiniteFreeLocus_subset_etaleFiniteFreeLocus_modulePullback`
* `AlgebraicGeometry.Space.pointsMap_geometricFibreToSource_geometricFibrePoint`: the lift of `x̄`
  to the geometric fibre lies over `x̄`.
* **Stacks 0CZS, (4) implies (3)**:
`AlgebraicGeometry.Space.mem_etaleFiniteFreeLocus_geometricFibre_of_isFiniteFreeNearGeometricPoint`
* **Stacks 0CZS, (1) implies (3)**, under the source's own hypotheses:
`AlgebraicGeometry.Space.mem_etaleFiniteFreeLocus_geometricFibre_of_flat_geometricFibreModuleStalk`

## Implementation notes

**Why the fibre can be formed.**  A geometric point of an algebraic space is, by definition, a
field-valued point whose field is algebraically closed, and a field-valued point carries the
spectrum of its field as an object `AlgebraicGeometry.Space.FieldValuedPoint.siteObject` of the big
fppf site over `S`; a representable presheaf on that site is an algebraic space
(`AlgebraicGeometry.isAlgebraicSpace_yoneda`), and the section defining the point is, through the
Yoneda equivalence, a morphism of presheaves out of it.  So nothing has to leave the ambient site:
`X_ȳ` is an algebraic space over the *same* base `S`, with its own small étale site, and the
inverse image of `F` to it is the ordinary `AlgebraicGeometry.Space.modulePullback` of Stacks 03LU.
The relocalized reading of the fibre — as an algebraic space over `Spec(κ(ȳ))` rather than over `S`
— is `AlgebraicGeometry.Space.fiberOverField`; it is not used here, and no comparison of the two is
claimed.

**The lift of the geometric point.**  `AlgebraicGeometry.Space.exists_points_of_isPullback`
(Stacks 03H4) produces *some* point of a fibre product over a compatible pair of points, over the
field of a common extension.  Here no extension is needed and the point is canonical: the geometric
point of the target is `AlgebraicGeometry.Space.geometricPointMap f.hom x̄`, which has the *same*
field, containment witness and structure morphism as `x̄`, so the tautological morphism
`Spec(κ(x̄)) ⟶ Spec(κ(ȳ))` is the identity and the square commutes on the nose after the Yoneda
equivalence.  The lift is therefore `CategoryTheory.IsPullback.lift` applied to the classifying
morphism of `x̄` and that identity, read back as a section by `CategoryTheory.yonedaEquiv`, and it
is algebraically closed because its field is that of `x̄`.

**A warning about the names.**  `AlgebraicGeometry.Space.geometricFibreLocalRing` and
`AlgebraicGeometry.Space.geometricFibreModuleStalk`, which clauses (1) and (2) of Stacks 0CZS are
carried on, are *not* the étale local ring and the geometric stalk of the
`AlgebraicGeometry.Space.geometricFibre` constructed here: they are the quotients
`𝒪_{X, x̄} / 𝔪_{ȳ} 𝒪_{X, x̄}` and `F_{x̄} / 𝔪_{ȳ} F_{x̄}`, which is condition (1) of Stacks 05WY.
Identifying the two is condition (2) of Stacks 05WY and is not available, so nothing below relates
them.

**Clause (3) only from clause (4) in this file.**  The source's cycle closes clause (3) through
`(3) ⟹ (2)`, which identifies the stalk of `F_ȳ` at `x̄` on the fibre with the quotient
`F_x̄ / 𝔪_ȳ F_x̄` that clauses (1) and (2) are carried in here.  That identification is condition
(2) of Stacks 05WY, which
`StacksFrontier/AlgebraicGeometry/Spaces/FibreFlatnessGeometricPoint.lean` does not state, and this
file obtains clause (3) from clause (4) only; nothing below relates the quotient to a stalk on the
fibre constructed here.

The reverse implication does **not** need that identification, and is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/GeometricFibreStalkClauseThree.lean`.  The defining square
of `X_ȳ` is cartesian, so clause (1) for `f` at `x̄` and clause (1) for the structure morphism
`X_ȳ ⟶ Spec(κ(ȳ))` at the lift of `x̄` are the same condition — a comparison of two quotients,
`AlgebraicGeometry.Space.flat_geometricFibreModuleStalk_modulePullback_iff_of_isPullback`, which
identifies no stalk — and clause (3) is clause (4) for the inverse image of `F` on `X_ȳ` over that
structure morphism.  So clause (3) does join the equivalence, in its Zariski-chart reading on the
fibre, as `AlgebraicGeometry.Space.flat_geometricFibreModuleStalk_geometricFibre_tfae` there; and
the locus reading concluded in below implies clause (4) at the locus of `F`, as
`AlgebraicGeometry.Space.mem_etaleFiniteFreeLocus_of_mem_etaleFiniteFreeLocus_geometricFibre`.
What stays unavailable is condition (2) of Stacks 05WY itself.

**Finite freeness of an inverse image.**  Stacks 03DF (2) is
`AlgebraicGeometry.RingedToposHom.pullbackModules_isFiniteFree`, for the pullback functor attached
to a morphism of ringed topoi; `AlgebraicGeometry.Space.modulePullback` of Stacks 03LU is the other
of the two parallel constructions out of the same morphism of ringed topoi, and
`AlgebraicGeometry.Space.modulePullback_eq` identifies them.  This is exactly how the unranked
`AlgebraicGeometry.Space.isFreeModule_modulePullback` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackIsFreeModule.lean` is obtained, and the two
proofs below are the finite-free transcription of the pair for plain freeness.

## References

* [Stacks Project, Tag 0CZS](https://stacks.math.columbia.edu/tag/0CZS)
* [Stacks Project, Tag 0CZT](https://stacks.math.columbia.edu/tag/0CZT)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DF](https://stacks.math.columbia.edu/tag/03DF)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 05WY](https://stacks.math.columbia.edu/tag/05WY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The inverse image of a finite free module -/

/-- **Stacks 03DF (2) for the inverse image of Stacks 03LU.**  The inverse image along a morphism
`f : X ⟶ Y` of algebraic spaces of a finite free `𝒪_Y`-module is a finite free `𝒪_X`-module.

This is `AlgebraicGeometry.RingedToposHom.pullbackModules_isFiniteFree` carried onto the inverse
image of Stacks 03LU, exactly as the unranked
`AlgebraicGeometry.Space.isFreeModule_modulePullback` is: `AlgebraicGeometry.Space.modulePullback`
is *defined* as `pullbackModules` of the morphism of small étale ringed topoi
(`AlgebraicGeometry.Space.modulePullback_eq`, by `rfl`), and the four-field morphism that
definition goes through is the one the ringed-topos statement uses
(`AlgebraicGeometry.RingedToposHom.toModulesHom_eq_toRingedToposModulesHom`), so the two rewrites
need no transport.  No `@[stacks 03DF]` attribute is attached: the tag is already registered on
the ringed-topos statement. -/
theorem isFiniteFreeModule_modulePullback {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (G : Modules.{u, u} B S hS Y.1 Y.2)
    (h : SheafOfModules.IsFiniteFree
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) G) :
    SheafOfModules.IsFiniteFree
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
      ((modulePullback B S hS f).obj G) := by
  have hpull := AlgebraicGeometry.RingedToposHom.pullbackModules_isFiniteFree
    (smallEtaleRingedToposHom B S hS f) h
  rwa [(smallEtaleRingedToposHom B S hS f).toModulesHom_eq_toRingedToposModulesHom] at hpull

/-- **The finite-free étale locus grows under an arbitrary inverse image.**  Every point of `|X'|`
whose image in `|X|` admits an étale neighbourhood on which `F` becomes finite free itself admits
one on which the inverse image `(g')^*F` becomes finite free.

This is the finite-free transcription of `AlgebraicGeometry.Space.preimage_etaleFreeLocus_subset`
of `StacksFrontier/AlgebraicGeometry/Spaces/EtaleFreeLocusPullback.lean`, with the same proof: the
neighbourhood is the base change `V' = X' ×_X V` of Stacks 02X2, étale over `X'` by Stacks 03FU,
carrying a point over the given one because a cartesian square is surjective onto the fibre
product of the point sets, and the inverse image of `(g')^*F` to it is the inverse image of `a^*F`
along the other projection, hence finite free by Stacks 03DF (2). -/
theorem preimage_etaleFiniteFreeLocus_subset_etaleFiniteFreeLocus_modulePullback
    {X X' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (F : Modules.{u, u} B S hS X.1 X.2) :
    pointsMap B S hS X'.1 g'.hom ⁻¹' etaleFiniteFreeLocus B S hS F ⊆
      etaleFiniteFreeLocus B S hS ((modulePullback B S hS g').obj F) := by
  rintro x' ⟨V, a, hae, ⟨v, hv⟩, hfree⟩
  have hp := AlgebraicSpaces.isPullback_fiberProduct B S hS g' a
  refine ⟨AlgebraicSpaces.fiberProduct B S hS g' a,
    ObjectProperty.homMk (pullback.fst g'.hom a.hom), ?_, ?_, ?_⟩
  · exact isEtale_of_isPullback B S hS _ _ a g'
      hp.flip hae
  · obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS
      (AlgebraicSpaces.isPullback_hom B S hS hp) x' v hv.symm
    exact ⟨w, hw⟩
  · exact Stacks.SheafOfModules.isFiniteFree_of_iso
      (modulePullbackCommSquareObjIso B S hS hp.w F).symm
      (isFiniteFreeModule_modulePullback B S hS _ _ hfree)

/-! ### The geometric fibre over a geometric point of the target -/

/-- **The geometric fibre `X_ȳ`** of a morphism `f : X ⟶ Y` of algebraic spaces at a geometric
point `ȳ` of `Y`: the fibre product of `f` with the geometric point, formed in the category of
algebraic spaces over the base by Stacks 02X2. -/
abbrev geometricFibre {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (ybar : GeometricPoint B S hS Y.1) : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS f (geometricPointHom ybar)

/-- The projection `X_ȳ ⟶ X` of the geometric fibre, along which a module on `X` is restricted to
the fibre. -/
abbrev geometricFibreToSource {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (ybar : GeometricPoint B S hS Y.1) : geometricFibre B S hS f ybar ⟶ X :=
  ObjectProperty.homMk (pullback.fst f.hom (geometricPointHom ybar).hom)

/-- The structure morphism `X_ȳ ⟶ Spec(κ(ȳ))` of the geometric fibre. -/
abbrev geometricFibreToPoint {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (ybar : GeometricPoint B S hS Y.1) :
    geometricFibre B S hS f ybar ⟶ geometricPointSpace ybar :=
  ObjectProperty.homMk (pullback.snd f.hom (geometricPointHom ybar).hom)

/-- **Stacks 02X2 for the geometric fibre**, read on the underlying presheaves: the defining square
of `X_ȳ` is cartesian as a square of presheaves on the big fppf site. -/
theorem isPullback_geometricFibre {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (ybar : GeometricPoint B S hS Y.1) :
    IsPullback (geometricFibreToSource B S hS f ybar).hom
      (geometricFibreToPoint B S hS f ybar).hom f.hom (geometricPointHom ybar).hom :=
  AlgebraicSpaces.isPullback_hom B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f (geometricPointHom ybar))

/-- The classifying morphism of a geometric point of `X`, followed by `f`, is the classifying
morphism of its image geometric point of `Y`. -/
theorem yonedaEquiv_symm_value_comp {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (xbar : GeometricPoint B S hS X.1) :
    yonedaEquiv.symm xbar.val.value ≫ f.hom =
      (geometricPointHom (geometricPointMap f.hom xbar)).hom := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact (Equiv.apply_symm_apply yonedaEquiv _).symm

/-- **The canonical lift of a geometric point to the geometric fibre through it.**  The classifying
morphism of `x̄` and the identity of `Spec(κ(x̄))` agree over `Y`, so they factor through the
geometric fibre over `ȳ = f ∘ x̄`; the resulting section is a field-valued point over the field of
`x̄`, which is algebraically closed. -/
def geometricFibrePoint {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (xbar : GeometricPoint B S hS X.1) :
    GeometricPoint B S hS (geometricFibre B S hS f (geometricPointMap f.hom xbar)).1 :=
  ⟨{ carrier := xbar.val.carrier
     contained := xbar.val.contained
     toBase := xbar.val.toBase
     value := yonedaEquiv
       ((isPullback_geometricFibre B S hS f (geometricPointMap f.hom xbar)).lift
         (yonedaEquiv.symm xbar.val.value) (𝟙 _)
         ((yonedaEquiv_symm_value_comp B S hS f xbar).trans (Category.id_comp _).symm)) },
    xbar.property⟩

/-- **The lift of a geometric point to the geometric fibre lies over it.** -/
theorem pointsMap_geometricFibreToSource_geometricFibrePoint
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (xbar : GeometricPoint B S hS X.1) :
    pointsMap B S hS (geometricFibre B S hS f (geometricPointMap f.hom xbar)).1
        (geometricFibreToSource B S hS f (geometricPointMap f.hom xbar)).hom
        (geometricFibrePoint B S hS f xbar).image = xbar.image := by
  have hp := isPullback_geometricFibre B S hS f (geometricPointMap f.hom xbar)
  rw [show (geometricFibrePoint B S hS f xbar).image =
    (geometricFibrePoint B S hS f xbar).val.class B S hS _ from rfl, pointsMap_class]
  refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS X.1
    ⟨_, FieldValuedPoint.dominates_refl B S hS X.1 _, ⟨𝟙 _, ?_⟩⟩
  show X.1.map (𝟙 xbar.val.siteObject).op xbar.val.value =
    (geometricFibreToSource B S hS f (geometricPointMap f.hom xbar)).hom.app _
      (yonedaEquiv (hp.lift (yonedaEquiv.symm xbar.val.value) (𝟙 _) _))
  rw [op_id, Functor.map_id_apply]
  exact ((congrArg yonedaEquiv (hp.lift_fst (yonedaEquiv.symm xbar.val.value) (𝟙 _) _)).trans
    (Equiv.apply_symm_apply yonedaEquiv _)).symm

/-! ### Clause (3) of Stacks 0CZS -/

/-- **Stacks 0CZS, (4) implies (3).**  If a quasi-coherent `𝒪_X`-module `M` is finite free in an
étale neighbourhood of a geometric point `x̄` of `X` — clause (4), in the source's Zariski-chart
reading — then the inverse image of `M` to the geometric fibre `X_ȳ` through `x̄` is finite free in
an étale neighbourhood of the lift of `x̄` to that fibre, which is clause (3).

The source calls this implication immediate, and so it is: clause (4) puts `x` in the finite-free
étale locus of `M` on `|X|`
(`AlgebraicGeometry.Space.mem_etaleFiniteFreeLocus_of_isFiniteFreeNearGeometricPoint`), and that
locus only grows under an inverse image, the lift of `x̄` lying over `x̄` by
`AlgebraicGeometry.Space.pointsMap_geometricFibreToSource_geometricFibrePoint`. -/
@[stacks 0CZS "(4) implies (3), with the geometric fibre X_ybar formed as the fibre product of f \
with the geometric point ybar = f o xbar in the category of algebraic spaces over S (02X2), the \
etale neighbourhood of xbar inside X_ybar read as in the locus of 0CZT, and clause (4) in the \
source's Zariski-chart reading"]
theorem mem_etaleFiniteFreeLocus_geometricFibre_of_isFiniteFreeNearGeometricPoint
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (xbar : GeometricPoint B S hS X.1)
    (h : IsFiniteFreeNearGeometricPoint B S hS xbar M) :
    (geometricFibrePoint B S hS f xbar).image ∈
      etaleFiniteFreeLocus B S hS ((modulePullback B S hS
        (geometricFibreToSource B S hS f (geometricPointMap f.hom xbar))).obj M) :=
  preimage_etaleFiniteFreeLocus_subset_etaleFiniteFreeLocus_modulePullback B S hS _ M
    (by
      rw [Set.mem_preimage, pointsMap_geometricFibreToSource_geometricFibrePoint B S hS f xbar]
      exact mem_etaleFiniteFreeLocus_of_isFiniteFreeNearGeometricPoint B S hS M hM xbar h)

/-- **Stacks 0CZS, (1) implies (3).**  Let `f : X ⟶ Y` be locally of finite presentation, let `M`
be a quasi-coherent `𝒪_X`-module of finite presentation on charts and let `x̄` be a geometric point
of `X`.  If `M` is flat at `x` over `Y` and the geometric fibre stalk `(M_{ȳ})_{x̄}` is a flat
`𝒪_{X_{ȳ}, x̄}`-module, then the inverse image of `M` to the geometric fibre is finite free in an
étale neighbourhood of the lift of `x̄`.

This is `(1) ⟹ (4)` followed by `(4) ⟹ (3)`.  The fibre stalk and its base ring are in the
quotient form `M_{x̄} / 𝔪_{ȳ} M_{x̄}` over `𝒪_{X, x̄} / 𝔪_{ȳ} 𝒪_{X, x̄}`, as they are throughout
this development; the identification of that quotient with the étale local ring of the geometric
fibre constructed here is condition (2) of Stacks 05WY and is not available. -/
@[stacks 0CZS "(1) implies (3), with the geometric fibre X_ybar formed as the fibre product of f \
with ybar = f o xbar (02X2) and the fibre stalk of clause (1) in the QUOTIENT FORM \
M_xbar / m_ybar M_xbar over O_{X, xbar} / m_ybar O_{X, xbar}, whose identification with the etale \
local ring of that fibre is condition (2) of Stacks 05WY and is not available"]
theorem mem_etaleFiniteFreeLocus_geometricFibre_of_flat_geometricFibreModuleStalk
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (M : Modules.{u, u} B S hS X.1 X.2)
    [M.IsQuasicoherentOnSite] (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hfp : IsFinitePresentationOnCharts B S hS X.2 M)
    (xbar : GeometricPoint B S hS X.1)
    (hflat : IsFlatOverAtGeometricPoint B S hS f M xbar)
    (hfibre : Module.Flat (geometricFibreLocalRing B S hS f xbar)
      (geometricFibreModuleStalk B S hS f M xbar)) :
    (geometricFibrePoint B S hS f xbar).image ∈
      etaleFiniteFreeLocus B S hS ((modulePullback B S hS
        (geometricFibreToSource B S hS f (geometricPointMap f.hom xbar))).obj M) :=
  mem_etaleFiniteFreeLocus_geometricFibre_of_isFiniteFreeNearGeometricPoint B S hS f M
    inferInstance xbar
    (isFiniteFreeNearGeometricPoint_of_flat_geometricFibreModuleStalk B S hS f M hf hfp xbar
      hflat hfibre)

end AlgebraicGeometry.Space

end
