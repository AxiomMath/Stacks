module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.Injective
public import Mathlib.RingTheory.Valuation.LocalSubring
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImageValuativePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactAffineMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDiagonalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UnibranchCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.Criterion
public import StacksFrontier.RingTheory.Valuation.Extension.Defs

/-!
# Valuative criteria for morphisms of algebraic spaces

The two halves of the valuative criterion of Stacks 03IX — the existence and the uniqueness
part — are stable under base change, and each of them is one half of a criterion for a
geometric property of a morphism of algebraic spaces over `S`: a quasi-compact morphism with
the existence part is universally closed, and a quasi-separated morphism with the uniqueness
part is separated. Conversely a separated morphism has the uniqueness part, and a
quasi-separated universally closed morphism has the existence part, so that for a quasi-compact
quasi-separated morphism universal closedness and the existence part agree. The last result of
the file is the flat lifting statement of Stacks 089F: a flat morphism of algebraic spaces
lifts a valuation-ring point of its target, after an extension of valuation rings, as soon as
the closed point of that valuation ring is in the image.

## Main definitions

No new definitions are introduced; the valuative criterion itself is
`AlgebraicGeometry.Space.ValuativeCriterion` of Stacks 03IX.

## Main results

* `AlgebraicGeometry.Space.valuativeCriterion_existence_of_isPullback` and
  `AlgebraicGeometry.Space.valuativeCriterion_uniqueness_of_isPullback` are the two cases of
  Stacks 03IY: each half of the criterion is stable under base change.
* `AlgebraicGeometry.Space.valuativeCriterion_uniqueness_of_isSeparated` is Stacks 03KU: a
  separated morphism satisfies the uniqueness part.
* `AlgebraicGeometry.Space.universallyClosed_of_isQuasiCompact_of_valuativeCriterion_existence`
  is Stacks 03KA: a quasi-compact morphism with the existence part is universally closed.
* `AlgebraicGeometry.Space.isSeparated_of_isQuasiSeparated_of_valuativeCriterion_uniqueness` is
  Stacks 03KV: a quasi-separated morphism with the uniqueness part is separated.
* `AlgebraicGeometry.Space.valuativeCriterion_existence_of_isQuasiSeparated_of_universallyClosed`
  and
  `AlgebraicGeometry.Space`
  `.universallyClosed_iff_valuativeCriterion_existence_of_isQuasiCompact_of_isQuasiSeparated`
  are the two parts of Stacks 0A3X.
* `AlgebraicGeometry.Space.exists_valuationRing_extension_lift_of_isFlat` is Stacks 089F.

## Implementation notes

The two base-change statements are given in the cartesian-square form used throughout this
directory, which specialises to the chosen fibre product at
`CategoryTheory.IsPullback.of_hasPullback`; neither uses any property of the four presheaves,
because a valuative square for the base change induces one for the original morphism by
composition, and the universal property of the square produces the lift back.

The left column `Spec K ⟶ Spec R` of a valuative square is written out in
`AlgebraicGeometry.Space.ValuativeSquare` and is abbreviated here by
`AlgebraicGeometry.Space.ValuativeSquare.fracHom`; the private lemmas at the head of the file
record the commuting square of site objects underlying a dominating extension, which is the
only compatibility of a dominating extension used below.

Stacks 03KA is proved by reducing to an affine base, which is Stacks 03IT in the form
`AlgebraicGeometry.Space.universallyClosed_of_isClosedMorphism_yoneda` composed with
`AlgebraicGeometry.Space.isClosedMorphism_pullback_fst_of_affine`. On an affine base the source
is quasi-compact (Stacks 03E4, 03H6), so it has a surjective étale chart with affine scheme,
and the points of a represented presheaf are the points of its scheme by
`AlgebraicGeometry.Space.schemePointsHomeomorph`. The image of a closed set of points is
therefore the preimage of the image of a closed subset of `Spec Γ` under a map of prime
spectra, and such an image is closed as soon as it is stable under specialization. That
stability is exactly what the existence part gives: a specialization in the target is realized
by a valuation ring, obtained from the stalk at the specializing point as in Stacks 01J8, and
a lift over that valuation ring carries the closed point to a specialization of the chosen
point of the source.

Stacks 03KV uses Stacks 03KA for the relative diagonal: the diagonal satisfies the existence
part because the uniqueness part identifies the two projections of a valuative square for it,
so no dominating extension is needed, and the trivial dominating extension of the given square
has a lift. The diagonal is then universally closed; being also separated, locally of finite
type, a monomorphism and locally quasi-finite (Stacks 03HK), every represented base change of
it is finite and a monomorphism, hence a closed immersion.

Stacks 0A3X, part (1), is the converse of Stacks 03KA under quasi-separatedness instead of
quasi-compactness. A valuative square for `f` presents the generic point of its valuation ring
as a point of the base change `X ×_Y Spec A`, through a section `g` of the projection to
`Spec A` whose composite with that projection is `Spec K ⟶ Spec A`. The projection is
quasi-separated (Stacks 03KL) and `Spec K ⟶ Spec A` is affine, so `g` is quasi-compact by
Stacks 03KS, and the points of its scheme-theoretic image are the closure of the image of `g`
by part (4) of Stacks 082Z. Universal closedness makes the image of that closed set in
`|Spec A|` closed, and it contains the generic point, so it is everything; Stacks 089B then
realizes a point of the image lying over the closed point of `Spec A` by a valuation ring
dominating `A`, and composing the resulting square with `Z ⟶ X ×_Y Spec A ⟶ X` is the lift.
Part (2) combines part (1) with Stacks 03KA.

For Stacks 089F the fibre product `X ×_Y Spec A` has a point over the closed point of
`Spec A` by Stacks 03H4, visible on a chart `U` by Stacks 03H5. The chart is flat over `Spec A`
because flatness is stable under base change (Stacks 03MO) and is tested on étale charts, so
the induced homomorphism from `A` to the local ring of `U` at the chosen point is flat and
local, hence faithfully flat; a prime of that local ring contracting to the zero ideal of `A`
therefore exists, and factoring the map to the fraction field of the quotient through a
valuation subring produces the extension. Size bounds put the spectrum of that valuation ring
back into the chosen big site.

## References

* [Stacks Project, Tag 03IY](https://stacks.math.columbia.edu/tag/03IY)
* [Stacks Project, Tag 03KA](https://stacks.math.columbia.edu/tag/03KA)
* [Stacks Project, Tag 03KU](https://stacks.math.columbia.edu/tag/03KU)
* [Stacks Project, Tag 03KV](https://stacks.math.columbia.edu/tag/03KV)
* [Stacks Project, Tag 089F](https://stacks.math.columbia.edu/tag/089F)
* [Stacks Project, Tag 0A3X](https://stacks.math.columbia.edu/tag/0A3X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Pullbacks of presheaves on the big fppf site over `S`, supplied directly: instance search
for them now times out. -/
local instance (priority := high) hasLimit_cospan_presheaf_ValuativeCriteria
    {Z₁ Z₂ Z₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z₁ ⟶ Z₀) (f : Z₂ ⟶ Z₀) :
    HasLimit (cospan g f) :=
  @HasLimitsOfShape.has_limit _ _ _ _ functorCategoryHasLimitsOfShape _

/-! ### The morphism of site objects attached to a valuative square -/

/-- The morphism of site objects `Spec K ⟶ Spec R` which is the left column of a valuative
square. -/
noncomputable abbrev ValuativeSquare.fracHom {f : X ⟶ Y} (q : ValuativeSquare f) :
    siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) ⟶
      siteObject B S hS q.ring_mem q.base :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K))) :
    B.obj q.field_mem ⟶ B.obj q.ring_mem)

/-- The left column of a valuative square `q`, read through `q.fracHom`. -/
theorem ValuativeSquare.comm' {f : X ⟶ Y} (q : ValuativeSquare f) :
    q.generic ≫ f = yoneda.map q.fracHom ≫ q.special := q.comm

/-- The left column of a lift, read through `q.fracHom`. -/
theorem ValuativeSquare.Lift.generic_comm' {f : X ⟶ Y} {q : ValuativeSquare f}
    (l : q.Lift) : yoneda.map q.fracHom ≫ l.map = q.generic := l.generic_comm

/-- The square of site objects underlying a dominating extension commutes: the two paths
`Spec K' ⟶ Spec R` through `Spec K` and through `Spec R'` agree. -/
theorem ValuativeSquare.DominatingExtension.genericOver_comp_fracHom
    {f : X ⟶ Y} {q : ValuativeSquare f} (e : q.DominatingExtension) :
    e.genericOver ≫ q.fracHom = e.square.fracHom ≫ e.specialOver := by
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  change B.inclusion.map e.genericOver.left ≫ B.inclusion.map q.fracHom.left =
    B.inclusion.map e.square.fracHom.left ≫ B.inclusion.map e.specialOver.left
  rw [e.genericOver_left, e.specialOver_left]
  simp only [ValuativeSquare.fracHom, Over.homMk_left, ObjectProperty.ι_map,
    ObjectProperty.homMk_hom]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext e.fraction_comm.symm

/-- The same square, after applying `yoneda`. -/
theorem ValuativeSquare.DominatingExtension.yonedaMap_genericOver_comp_fracHom
    {f : X ⟶ Y} {q : ValuativeSquare f} (e : q.DominatingExtension) :
    yoneda.map e.genericOver ≫ yoneda.map q.fracHom =
      yoneda.map e.square.fracHom ≫ yoneda.map e.specialOver := by
  rw [← yoneda.map_comp, ← yoneda.map_comp, e.genericOver_comp_fracHom]

/-- The same square, pushed forward along an arbitrary morphism out of `Spec R`. -/
theorem ValuativeSquare.DominatingExtension.generic_comp
    {f : X ⟶ Y} {q : ValuativeSquare f} (e : q.DominatingExtension)
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (t : yoneda.obj (siteObject B S hS q.ring_mem q.base) ⟶ W) :
    yoneda.map e.square.fracHom ≫ yoneda.map e.specialOver ≫ t =
      yoneda.map e.genericOver ≫ yoneda.map q.fracHom ≫ t := by
  rw [← Category.assoc, ← Category.assoc, e.yonedaMap_genericOver_comp_fracHom]

/-- A valuative square for `b` gives one for `p`, by composing with the other sides of a
commuting square. -/
private noncomputable abbrev ValuativeSquare.pushforward
    {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : F ⟶ F'} {b : F ⟶ G} {p : F' ⟶ G'}
    {q : G ⟶ G'} (w : a ≫ p = b ≫ q) (v : ValuativeSquare b) : ValuativeSquare p :=
  { R := v.R, K := v.K, ring_mem := v.ring_mem, field_mem := v.field_mem, base := v.base
    generic := v.generic ≫ a, special := v.special ≫ q
    comm := by rw [Category.assoc, w, ← Category.assoc, v.comm', Category.assoc] }

/-! ### Base change -/

/-- **Stacks 03IY, uniqueness part.** The base change of a morphism of algebraic spaces
satisfying the uniqueness part of the valuative criterion satisfies it again.

Two lifts of a valuative square for the base change `b` agree after composing with `a`, by
uniqueness for `p` applied to the induced valuative square, and after composing with `b`,
because both are lifts; so they agree. -/
@[stacks 03IY "uniqueness part"]
theorem valuativeCriterion_uniqueness_of_isPullback
    {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : F ⟶ F'} {b : F ⟶ G} {p : F' ⟶ G'} {q : G ⟶ G'} (sq : IsPullback a b p q)
    (hp : ValuativeCriterion.Uniqueness p) : ValuativeCriterion.Uniqueness b := by
  intro v
  refine ⟨fun x₁ x₂ => ?_⟩
  let vp := v.pushforward sq.w
  let lift (l : v.Lift) : vp.Lift :=
    { map := l.map ≫ a
      generic_comm := by rw [← Category.assoc, l.generic_comm']
      special_comm := by rw [Category.assoc, sq.w, ← Category.assoc, l.special_comm] }
  have hmap : x₁.map = x₂.map := by
    refine sq.hom_ext ?_ (x₁.special_comm.trans x₂.special_comm.symm)
    exact congrArg ValuativeSquare.Lift.map ((hp vp).allEq (lift x₁) (lift x₂))
  cases x₁; cases x₂; cases hmap; rfl

/-- **Stacks 03IY, existence part.** The base change of a morphism of algebraic spaces
satisfying the existence part of the valuative criterion satisfies it again.

A valuative square for the base change `b` induces one for `p`; a dominating extension and a
lift there, together with the bottom edge pushed along the extension, define a map into the
fibre product by the universal property of the cartesian square, and that map is a lift of
the dominating extension of the original square. -/
@[stacks 03IY "existence part"]
theorem valuativeCriterion_existence_of_isPullback
    {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : F ⟶ F'} {b : F ⟶ G} {p : F' ⟶ G'} {q : G ⟶ G'} (sq : IsPullback a b p q)
    (hp : ValuativeCriterion.Existence p) : ValuativeCriterion.Existence b := by
  intro v
  let vp := v.pushforward sq.w
  obtain ⟨e, ⟨l⟩⟩ := hp vp
  have hcompat : l.map ≫ p = (yoneda.map e.specialOver ≫ v.special) ≫ q := by
    rw [l.special_comm, e.special_comm, Category.assoc]
  let vb : ValuativeSquare b :=
    { R := e.square.R, K := e.square.K
      ring_mem := e.square.ring_mem, field_mem := e.square.field_mem
      base := e.square.base
      generic := yoneda.map e.genericOver ≫ v.generic
      special := yoneda.map e.specialOver ≫ v.special
      comm := by
        rw [Category.assoc, v.comm', ← Category.assoc,
          e.yonedaMap_genericOver_comp_fracHom, Category.assoc] }
  let ev : v.DominatingExtension :=
    { square := vb
      ringMap := e.ringMap, fieldMap := e.fieldMap, isLocalHom := e.isLocalHom
      fraction_comm := e.fraction_comm, base_comm := e.base_comm
      genericOver := e.genericOver, genericOver_left := e.genericOver_left
      specialOver := e.specialOver, specialOver_left := e.specialOver_left
      generic_comm := rfl, special_comm := rfl }
  have hgenA : (yoneda.map e.square.fracHom ≫
        sq.lift l.map (yoneda.map e.specialOver ≫ v.special) hcompat) ≫ a =
      (yoneda.map e.genericOver ≫ v.generic) ≫ a := by
    rw [Category.assoc, sq.lift_fst, Category.assoc]
    exact l.generic_comm'.trans e.generic_comm
  have hgenB : (yoneda.map e.square.fracHom ≫
        sq.lift l.map (yoneda.map e.specialOver ≫ v.special) hcompat) ≫ b =
      (yoneda.map e.genericOver ≫ v.generic) ≫ b := by
    rw [Category.assoc, sq.lift_snd, Category.assoc, v.comm']
    exact e.generic_comp v.special
  exact ⟨ev, ⟨{ map := sq.lift l.map (yoneda.map e.specialOver ≫ v.special) hcompat
                generic_comm := sq.hom_ext hgenA hgenB
                special_comm := sq.lift_snd _ _ _ }⟩⟩

/-! ### Separated morphisms satisfy the uniqueness part -/

/-- **Stacks 03KU.** A separated morphism of algebraic spaces satisfies the uniqueness part
of the valuative criterion.

Two lifts of a valuative square assemble into a morphism `Spec R ⟶ X ×_Y X`; the base change
of the relative diagonal along it is a closed immersion of schemes which is surjective on
global sections, because the generic point of `Spec R` lifts through it, hence an
isomorphism. The two lifts therefore agree. -/
@[stacks 03KU, ega "II 7.3.2" "more general"]
theorem valuativeCriterion_uniqueness_of_isSeparated (f : X ⟶ Y)
    (hf : IsSeparated B S hS f) : ValuativeCriterion.Uniqueness f := by
  classical
  intro v
  refine ⟨fun x₁ x₂ => ?_⟩
  have hxy : x₁.map ≫ f = x₂.map ≫ f := x₁.special_comm.trans x₂.special_comm.symm
  set w : yoneda.obj (siteObject B S hS v.ring_mem v.base) ⟶ pullback f f :=
    pullback.lift x₁.map x₂.map hxy with hwdef
  have hgen : yoneda.map v.fracHom ≫ w = v.generic ≫ pullback.diagonal f := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hwdef, pullback.lift_fst, Category.assoc, pullback.diagonal_fst,
        Category.comp_id]
      exact x₁.generic_comm'
    · rw [Category.assoc, hwdef, pullback.lift_snd, Category.assoc, pullback.diagonal_snd,
        Category.comp_id]
      exact x₂.generic_comm'
  -- The base change of the relative diagonal along `w`.
  have sq := hf.rep.isPullback w
  have hsClosed : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hf.rep.snd w)) :=
    hf.property w (hf.rep.fst w) (hf.rep.snd w) sq
  -- The generic point lifts through the base change, so `s` is injective on global sections.
  have hkOver : yoneda.preimage (sq.lift v.generic (yoneda.map v.fracHom) hgen.symm) ≫
      hf.rep.snd w = v.fracHom := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, Functor.map_preimage]
    exact sq.lift_snd v.generic (yoneda.map v.fracHom) hgen.symm
  have hsIso : IsIso ((BigFppfOver.toScheme B S hS).map (hf.rep.snd w)) := by
    have hk : (BigFppfOver.toScheme B S hS).map
          (yoneda.preimage (sq.lift v.generic (yoneda.map v.fracHom) hgen.symm)) ≫
        (BigFppfOver.toScheme B S hS).map (hf.rep.snd w) =
          Spec.map (CommRingCat.ofHom (algebraMap v.R v.K)) := by
      rw [← Functor.map_comp, hkOver]
      rfl
    have hcomp : Function.Injective
        (((BigFppfOver.toScheme B S hS).map
          (yoneda.preimage (sq.lift v.generic (yoneda.map v.fracHom) hgen.symm)) ≫
          (BigFppfOver.toScheme B S hS).map (hf.rep.snd w)).appTop) := by
      rw [hk]
      have hQ : (RingHom.toMorphismProperty fun φ ↦ Function.Injective φ).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.injective_respectsIso
      change RingHom.toMorphismProperty (fun φ ↦ Function.Injective φ) _
      rw [← MorphismProperty.arrow_mk_iso_iff
        (P := RingHom.toMorphismProperty fun φ ↦ Function.Injective φ)
        (arrowIsoΓSpecOfIsAffine (CommRingCat.ofHom (algebraMap v.R v.K)))]
      exact FaithfulSMul.algebraMap_injective v.R v.K
    have : _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map (hf.rep.snd w)) := hsClosed
    have hsTarget : IsAffine ((BigFppfOver.toScheme B S hS).obj
        (siteObject B S hS v.ring_mem v.base)) :=
      inferInstanceAs (IsAffine (Spec (.of v.R)))
    have hinj : Function.Injective
        ((BigFppfOver.toScheme B S hS).map (hf.rep.snd w)).appTop := by
      intro x y hxy
      refine hcomp ?_
      simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp,
        Function.comp_apply, hxy]
    exact IsClosedImmersion.isIso_of_injective_of_isAffine hinj
  have : IsIso (hf.rep.snd w) := isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)
  have : Epi (yoneda.map (hf.rep.snd w)) := by
    have : IsIso (yoneda.map (hf.rep.snd w)) := Functor.map_isIso _ _
    exact IsIso.epi_of_iso _
  have hcancel : yoneda.map (hf.rep.snd w) ≫ w ≫ pullback.fst f f =
      yoneda.map (hf.rep.snd w) ≫ w ≫ pullback.snd f f := by
    rw [← Category.assoc, ← Category.assoc, ← sq.w, Category.assoc, Category.assoc,
      pullback.diagonal_fst, pullback.diagonal_snd]
  have hmap : x₁.map = x₂.map := by
    calc x₁.map = w ≫ pullback.fst f f := by rw [hwdef, pullback.lift_fst]
      _ = w ≫ pullback.snd f f := (cancel_epi (yoneda.map (hf.rep.snd w))).mp hcancel
      _ = x₂.map := by rw [hwdef, pullback.lift_snd]
  cases x₁; cases x₂; cases hmap; rfl

/-! ### Universal closedness from the existence part -/

/-- **A valuative square out of a specialization.** Let `f : F ⟶ U` be a morphism into a
represented presheaf, let `p` be a field-valued point of `F`, and let `q` be a field-valued
point of `U` whose underlying scheme point is a specialization of the image of `p`. If `f`
satisfies the existence part of the valuative criterion, then there is a valuative square for
`f` whose generic point is `p`, read through a morphism `k` of site objects, together with a
dominating extension of it carrying a lift, and whose bottom edge takes the closed point of
the valuation ring to the scheme point of `q`.

The valuation ring is obtained by factoring the composite of the specialization map
`𝒪_{U, q} ⟶ 𝒪_{U, p}` with the local homomorphism `𝒪_{U, p} ⟶ κ(p)` attached to `p` through a
valuation subring of `κ(p)`, as in Stacks 01J8. -/
private theorem exists_valuativeSquare_of_specializes {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : BigFppfOver B S hS) (f : F ⟶ yoneda.obj U)
    (p : FieldValuedPoint B S hS F) (q : FieldValuedPoint B S hS (yoneda.obj U))
    (hsp : schemePoint B S hS U (FieldValuedPoint.map B S hS F f p) ⤳
      schemePoint B S hS U q)
    (hval : ValuativeCriterion.Existence f) :
    ∃ (v : ValuativeSquare f) (e : v.DominatingExtension), Nonempty e.square.Lift ∧
      ∃ k : siteObject B S hS v.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap v.R v.K)) ≫ v.base) ⟶
            p.siteObject B S hS F,
        v.generic = yoneda.map k ≫ yonedaEquiv.symm p.value ∧
        schemePoint B S hS U (FieldValuedPoint.map B S hS
            (yoneda.obj (siteObject B S hS v.ring_mem v.base)) v.special
            (schemePointRepresentative B S hS (siteObject B S hS v.ring_mem v.base)
              (IsLocalRing.closedPoint v.R))) = schemePoint B S hS U q := by
  classical
  let T := (BigFppfOver.toScheme B S hS).obj U
  let pY : FieldValuedPoint B S hS (yoneda.obj U) := FieldValuedPoint.map B S hS F f p
  let u : p.siteObject B S hS F ⟶ U := pY.value
  let g : Spec (.of p.carrier) ⟶ T := B.inclusion.map u.left
  let y := schemePoint B S hS U q
  have hsp' : g (IsLocalRing.closedPoint p.carrier) ⤳ y := hsp
  let φ : T.presheaf.stalk y ⟶ CommRingCat.of p.carrier :=
    T.presheaf.stalkSpecializes hsp' ≫ Scheme.stalkClosedPointTo g
  obtain ⟨A, hA, hA_local⟩ := IsLocalRing.exists_factor_valuationRing φ.hom
  have hKcard : Cardinal.mk p.carrier < B.cutoff := by
    have h : (Spec (.of p.carrier)).size < B.cutoff := p.contained
    rw [Scheme.size_Spec] at h
    exact (le_max_right Cardinal.aleph0 (Cardinal.mk p.carrier)).trans_lt h
  have hAmem : B.Contains (Spec (.of A)) := by
    change (Spec (.of A)).size < B.cutoff
    rw [Scheme.size_Spec]
    exact max_lt B.aleph0_lt_cutoff
      ((Cardinal.mk_le_of_injective Subtype.val_injective).trans_lt hKcard)
  let localMap : CommRingCat.of (T.presheaf.stalk y) ⟶ CommRingCat.of A :=
    CommRingCat.ofHom (φ.hom.codRestrict A.toSubring hA)
  let vA : Spec (.of A) ⟶ T := Spec.map localMap ≫ T.fromSpecStalk y
  have hfactor : Spec.map (CommRingCat.ofHom (algebraMap A p.carrier)) ≫ vA = g := by
    have hφ : Spec.map φ ≫ T.fromSpecStalk y = g := by
      change Spec.map (T.presheaf.stalkSpecializes hsp' ≫ Scheme.stalkClosedPointTo g) ≫
        T.fromSpecStalk y = g
      rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp']
      exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk (f := g)
    have hRing' : CommRingCat.ofHom ((algebraMap A p.carrier).comp localMap.hom) = φ :=
      CommRingCat.hom_ext (by ext a; rfl)
    calc Spec.map (CommRingCat.ofHom (algebraMap A p.carrier)) ≫ vA
        = Spec.map (localMap ≫ CommRingCat.ofHom (algebraMap A p.carrier)) ≫
            T.fromSpecStalk y := by simp only [vA, ← Spec.map_comp_assoc]
      _ = Spec.map φ ≫ T.fromSpecStalk y := by rw [← CommRingCat.ofHom_comp, hRing']
      _ = g := hφ
  let baseA : Spec (.of A) ⟶ S := vA ≫ B.inclusion.map U.hom
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap A p.carrier)) ≫ baseA = p.toBase := by
    calc Spec.map (CommRingCat.ofHom (algebraMap A p.carrier)) ≫ baseA
        = (Spec.map (CommRingCat.ofHom (algebraMap A p.carrier)) ≫ vA) ≫
            B.inclusion.map U.hom := by simp only [baseA, Category.assoc]
      _ = g ≫ B.inclusion.map U.hom := by rw [hfactor]
      _ = p.toBase := congrArg (fun k ↦ B.inclusion.map k) (Over.w u)
  let qFrac : siteObject B S hS p.contained
      (Spec.map (CommRingCat.ofHom (algebraMap A p.carrier)) ≫ baseA) ⟶
        siteObject B S hS hAmem baseA :=
    Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap A p.carrier))) :
        B.obj p.contained ⟶ B.obj hAmem)
  let idK : siteObject B S hS p.contained
      (Spec.map (CommRingCat.ofHom (algebraMap A p.carrier)) ≫ baseA) ⟶
        p.siteObject B S hS F :=
    Over.homMk (𝟙 (B.obj p.contained)) (by
      apply ObjectProperty.hom_ext
      change p.toBase = _
      exact hbase.symm)
  let vB : B.obj hAmem ⟶ U.left := B.inclusion.preimage vA
  have hvB : B.inclusion.map vB = vA :=
    B.inclusion.map_preimage (X := B.obj hAmem) (Y := U.left) vA
  let specialOver : siteObject B S hS hAmem baseA ⟶ U :=
    Over.homMk vB (by
      apply ObjectProperty.hom_ext
      change B.inclusion.map vB ≫ B.inclusion.map U.hom = baseA
      rw [hvB])
  have harrow : idK ≫ u = qFrac ≫ specialOver := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change B.inclusion.map (𝟙 (B.obj p.contained)) ≫ B.inclusion.map u.left =
      Spec.map (CommRingCat.ofHom (algebraMap A p.carrier)) ≫ B.inclusion.map vB
    rw [B.inclusion.map_id, Category.id_comp, hvB]
    exact hfactor.symm
  have hmapu : yoneda.map u = yonedaEquiv.symm pY.value := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_yoneda_map]
    rfl
  have hcomm : (yoneda.map idK ≫ yonedaEquiv.symm p.value) ≫ f
      = yoneda.map qFrac ≫ yoneda.map specialOver := by
    have h1 : (yoneda.map idK ≫ yonedaEquiv.symm p.value) ≫ f
        = yoneda.map idK ≫ yoneda.map u :=
      ((Category.assoc _ _ _).trans
        (congrArg (fun t ↦ yoneda.map idK ≫ t)
          (yonedaEquiv_symm_naturality_right (p.siteObject B S hS F) f p.value))).trans
        (congrArg (fun t ↦ yoneda.map idK ≫ t) hmapu.symm)
    rw [h1, ← Functor.map_comp, ← Functor.map_comp, harrow]
  let v : ValuativeSquare f :=
    { R := A, K := p.carrier, ring_mem := hAmem, field_mem := p.contained, base := baseA
      generic := yoneda.map idK ≫ yonedaEquiv.symm p.value
      special := yoneda.map specialOver
      comm := hcomm }
  have hAlocalRing : IsLocalRing ↥A.toSubring := A.isLocalRing
  have hclosedA : Spec.map localMap (IsLocalRing.closedPoint A) =
      IsLocalRing.closedPoint (T.presheaf.stalk y) :=
    IsLocalRing.comap_closedPoint (φ.hom.codRestrict A.toSubring hA)
  have hvA : vA (IsLocalRing.closedPoint A) = y := by
    change T.fromSpecStalk y (Spec.map localMap (IsLocalRing.closedPoint A)) = y
    rw [hclosedA]
    exact T.fromSpecStalk_closedPoint
  have hcenter : schemePoint B S hS U (FieldValuedPoint.map B S hS
      (yoneda.obj (siteObject B S hS hAmem baseA)) (yoneda.map specialOver)
      (schemePointRepresentative B S hS (siteObject B S hS hAmem baseA)
        (IsLocalRing.closedPoint A))) = schemePoint B S hS U q := by
    rw [schemePoint_map_yoneda,
      schemePointRepresentative_point B S hS (siteObject B S hS hAmem baseA)
        (IsLocalRing.closedPoint A)]
    change B.inclusion.map vB (IsLocalRing.closedPoint A) = y
    rw [hvB]
    exact hvA
  obtain ⟨e, hlift⟩ := hval v
  exact ⟨v, e, hlift, idK, rfl, hcenter⟩

section PointTopology

attribute [local instance] pointTopology

/-- A specialization of scheme points of a represented presheaf is a specialization of its
points. -/
theorem specializes_class_of_schemePoint_specializes (U : BigFppfOver B S hS)
    (p q : FieldValuedPoint B S hS (yoneda.obj U))
    (h : schemePoint B S hS U p ⤳ schemePoint B S hS U q) :
    p.class B S hS (yoneda.obj U) ⤳ q.class B S hS (yoneda.obj U) := by
  refine (schemePointsHomeomorph B S hS U).isInducing.specializes_iff.mp ?_
  rw [schemePointsHomeomorph_apply, schemePointsHomeomorph_apply,
    pointsToScheme_class, pointsToScheme_class]
  exact h

/-- **A dotted arrow gives a specialization.** Let `v` be a valuative square for
`f : F ⟶ G` whose generic arrow is a field-valued point `p` of `F`, read through a morphism `k`
of site objects, and let a dominating extension of `v` carry a dotted arrow. Then the closed
point of the extended valuation ring maps to a point of `F` which specializes `p` and which `f`
takes to the image of the closed point of the valuation ring of `v` along the bottom edge.

The generic point of the spectrum of the extended valuation ring maps to `p` and its closed
point to a specialization of it, because the map on points is continuous; the bottom triangle
of the dotted arrow computes the image in `G`. -/
theorem exists_specializes_pointsMap_eq_of_lift {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} (v : ValuativeSquare f) (e : v.DominatingExtension) (l : e.square.Lift)
    (p : FieldValuedPoint B S hS F)
    (k : siteObject B S hS v.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap v.R v.K)) ≫ v.base) ⟶
          p.siteObject B S hS F)
    (hgeneric : v.generic = yoneda.map k ≫ yonedaEquiv.symm p.value) :
    ∃ r : points B S hS F, p.class B S hS F ⤳ r ∧
      pointsMap B S hS F f r = (FieldValuedPoint.map B S hS
        (yoneda.obj (siteObject B S hS v.ring_mem v.base)) v.special
        (schemePointRepresentative B S hS (siteObject B S hS v.ring_mem v.base)
          (IsLocalRing.closedPoint v.R))).class B S hS G := by
  classical
  set RObj := siteObject B S hS e.square.ring_mem e.square.base with hRObj
  set frac := siteObject B S hS e.square.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap e.square.R e.square.K)) ≫ e.square.base)
    with hfrac
  let genericPoint : FieldValuedPoint B S hS (yoneda.obj frac) :=
    { carrier := e.square.K
      contained := e.square.field_mem
      toBase := Spec.map (CommRingCat.ofHom (algebraMap e.square.R e.square.K)) ≫
        e.square.base
      value := yonedaEquiv (yoneda.map (𝟙 frac)) }
  let ringGeneric := FieldValuedPoint.map B S hS (yoneda.obj frac)
    (yoneda.map e.square.fracHom) genericPoint
  let ringCenter := schemePointRepresentative B S hS RObj
    (IsLocalRing.closedPoint e.square.R)
  have hringSp : schemePoint B S hS RObj ringGeneric ⤳ schemePoint B S hS RObj ringCenter := by
    rw [schemePointRepresentative_point B S hS RObj (IsLocalRing.closedPoint e.square.R)]
    exact IsLocalRing.specializes_closedPoint _
  have hclassSp := specializes_class_of_schemePoint_specializes RObj
    ringGeneric ringCenter hringSp
  have hrsp : (FieldValuedPoint.map B S hS (yoneda.obj RObj) l.map ringGeneric).class
        B S hS F ⤳
      (FieldValuedPoint.map B S hS (yoneda.obj RObj) l.map ringCenter).class B S hS F :=
    hclassSp.map (continuous_pointsMap B S hS l.map)
  -- The generic point of the extension represents `p`.
  have hnat : yoneda.map e.square.fracHom ≫ l.map =
      yoneda.map (e.genericOver ≫ k) ≫ yonedaEquiv.symm p.value := by
    calc yoneda.map e.square.fracHom ≫ l.map = e.square.generic := l.generic_comm'
      _ = yoneda.map e.genericOver ≫ v.generic := e.generic_comm
      _ = yoneda.map e.genericOver ≫ yoneda.map k ≫ yonedaEquiv.symm p.value := by
            rw [hgeneric]
      _ = yoneda.map (e.genericOver ≫ k) ≫ yonedaEquiv.symm p.value := by
            rw [Functor.map_comp, Category.assoc]
  have hpLiftEq : FieldValuedPoint.map B S hS (yoneda.obj RObj) l.map ringGeneric =
      FieldValuedPoint.map B S hS (yoneda.obj frac)
        (yoneda.map (e.genericOver ≫ k) ≫ yonedaEquiv.symm p.value) genericPoint := by
    change FieldValuedPoint.map B S hS (yoneda.obj frac)
      (yoneda.map e.square.fracHom ≫ l.map) genericPoint = _
    rw [hnat]
  have hpExt : (FieldValuedPoint.map B S hS (yoneda.obj frac)
      (yoneda.map (e.genericOver ≫ k) ≫ yonedaEquiv.symm p.value) genericPoint).class
        B S hS F = p.class B S hS F := by
    refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS F ⟨_,
      FieldValuedPoint.dominates_refl B S hS F _, ⟨e.genericOver ≫ k, ?_⟩⟩
    change F.map (e.genericOver ≫ k).op p.value =
      (yoneda.map (e.genericOver ≫ k) ≫ yonedaEquiv.symm p.value).app
        (Opposite.op frac) (yonedaEquiv (yoneda.map (𝟙 frac)))
    rw [yonedaEquiv_symm_naturality_left, yonedaEquiv_yoneda_map, yonedaEquiv_symm_app_apply]
    exact (F.map_id_apply (Opposite.op frac) _).symm
  refine ⟨(FieldValuedPoint.map B S hS (yoneda.obj RObj) l.map ringCenter).class B S hS F,
    ?_, ?_⟩
  · rw [← hpExt, ← hpLiftEq]
    exact hrsp
  -- The closed point of the extension maps to `q`.
  · set sqRing := siteObject B S hS v.ring_mem v.base with hsqRing
    set sqCenter := schemePointRepresentative B S hS sqRing (IsLocalRing.closedPoint v.R)
      with hsqCenterDef
    have hextCenter : schemePoint B S hS sqRing
        (FieldValuedPoint.map B S hS (yoneda.obj RObj) (yoneda.map e.specialOver)
          ringCenter) = IsLocalRing.closedPoint v.R := by
      rw [schemePoint_map_yoneda,
        schemePointRepresentative_point B S hS RObj (IsLocalRing.closedPoint e.square.R)]
      have : IsLocalHom e.ringMap := e.isLocalHom
      change B.inclusion.map e.specialOver.left
        (IsLocalRing.closedPoint e.square.R) = _
      rw [e.specialOver_left]
      exact IsLocalRing.comap_closedPoint e.ringMap
    have hsqCenter : schemePoint B S hS sqRing sqCenter = IsLocalRing.closedPoint v.R :=
      schemePointRepresentative_point B S hS sqRing (IsLocalRing.closedPoint v.R)
    have hclassCenter := class_eq_class_of_schemePoint_eq sqRing _ _
      (hextCenter.trans hsqCenter.symm)
    have hfield : FieldValuedPoint.map B S hS F f
          (FieldValuedPoint.map B S hS (yoneda.obj RObj) l.map ringCenter) =
        FieldValuedPoint.map B S hS (yoneda.obj sqRing) v.special
          (FieldValuedPoint.map B S hS (yoneda.obj RObj) (yoneda.map e.specialOver)
            ringCenter) := by
      rw [← FieldValuedPoint.map_comp, ← FieldValuedPoint.map_comp, l.special_comm,
        e.special_comm]
    rw [pointsMap_class, hfield, ← pointsMap_class, hclassCenter, pointsMap_class]


/-- **A specializing point from the existence part.** If `f : F ⟶ U` satisfies the existence
part of the valuative criterion, every specialization of the image of a point of `F` inside a
represented target is the image of a specialization of that point.

The valuation ring produced by `exists_valuativeSquare_of_specializes` carries a lift, and
`exists_specializes_pointsMap_eq_of_lift` reads off the specializing point. -/
private theorem exists_specializes_pointsMap_eq_of_valuativeExistence
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : BigFppfOver B S hS) (f : F ⟶ yoneda.obj U)
    (p : FieldValuedPoint B S hS F) (q : FieldValuedPoint B S hS (yoneda.obj U))
    (hsp : schemePoint B S hS U (FieldValuedPoint.map B S hS F f p) ⤳
      schemePoint B S hS U q)
    (hval : ValuativeCriterion.Existence f) :
    ∃ r : points B S hS F, p.class B S hS F ⤳ r ∧
      pointsMap B S hS F f r = q.class B S hS (yoneda.obj U) := by
  obtain ⟨v, e, ⟨l⟩, k, hgeneric, hcenter⟩ :=
    exists_valuativeSquare_of_specializes U f p q hsp hval
  obtain ⟨r, hr, hfr⟩ := exists_specializes_pointsMap_eq_of_lift v e l p k hgeneric
  exact ⟨r, hr, hfr.trans (class_eq_class_of_schemePoint_eq U _ _ hcenter)⟩

/-- **The affine test for closedness.** A quasi-compact morphism from an algebraic space to a
represented presheaf whose scheme is affine, satisfying the existence part of the valuative
criterion, induces a closed map on points.

The source is quasi-compact, so it has a surjective étale chart `A` with affine scheme. The
points of a represented presheaf are the points of its scheme, so the image of a closed set
of points of `F` is cut out by the image of a closed subset of `Spec Γ(A)` under the map of
prime spectra induced by `Γ(U) ⟶ Γ(A)`; by
`exists_specializes_pointsMap_eq_of_valuativeExistence` that image is stable under
specialization, hence closed. -/
private theorem isClosedMap_pointsMap_of_isAffine_target
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (f : F ⟶ yoneda.obj U) (hf : IsQuasiCompact B S hS f)
    (hval : ValuativeCriterion.Existence f) :
    IsClosedMap (pointsMap B S hS F f) := by
  classical
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) :=
    Scheme.compactSpace_of_isAffine _
  have hUqc : IsQuasiCompactSpace B S hS (yoneda.obj U) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).2 (compactSpace_points_yoneda B S hS U)
  have hFqc : IsQuasiCompactSpace B S hS F :=
    isQuasiCompactSpace_of_iso B S hS (asIso (pullback.snd (𝟙 (yoneda.obj U)) f))
      (hf (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) hUqc (𝟙 _))
  obtain ⟨A, φ, hAaffine, hφsurj, hφetale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS F hF).mp hFqc
  have hφsurjPoints : Function.Surjective (pointsMap B S hS (yoneda.obj A) φ) :=
    (surjective_iff_surjective_pointsMap B S hS F hF A φ).mp hφsurj
  have hAaff : IsAffine ((BigFppfOver.toScheme B S hS).obj A) := hAaffine
  set k : A ⟶ U := yoneda.preimage (φ ≫ f) with hkdef
  have hk : yoneda.map k = φ ≫ f := yoneda.map_preimage (φ ≫ f)
  set m := (BigFppfOver.toScheme B S hS).map k with hmdef
  set hA' := ((BigFppfOver.toScheme B S hS).obj A).isoSpec.hom.homeomorph with hA'def
  set hU' := ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom.homeomorph with hU'def
  set eA := schemePointsHomeomorph B S hS A with heA
  set eU := schemePointsHomeomorph B S hS U with heU
  -- The chart identifies the map on points with the map on scheme points.
  have hbridge (x : points B S hS (yoneda.obj A)) :
      eU (pointsMap B S hS F f (pointsMap B S hS (yoneda.obj A) φ x)) = m (eA x) := by
    rw [heU, heA, schemePointsHomeomorph_apply, schemePointsHomeomorph_apply,
      show pointsMap B S hS F f (pointsMap B S hS (yoneda.obj A) φ x) =
        pointsMap B S hS (yoneda.obj A) (yoneda.map k) x from by
          rw [hk, pointsMap_comp]; rfl]
    exact pointsToScheme_pointsMap B S hS k x
  -- The naturality square of the two affine identifications.
  have hnat (x : (BigFppfOver.toScheme B S hS).obj A) :
      hU' (m x) = PrimeSpectrum.comap m.appTop.hom (hA' x) :=
    (congrArg (fun t ↦ t x) (Scheme.isoSpec_hom_naturality m)).symm
  intro C hC
  set P : Set (points B S hS (yoneda.obj A)) :=
    pointsMap B S hS (yoneda.obj A) φ ⁻¹' C with hPdef
  have hP : IsClosed P := hC.preimage (continuous_pointsMap B S hS φ)
  set V : Set ((BigFppfOver.toScheme B S hS).obj A) := eA.symm ⁻¹' P with hVdef
  have hV : IsClosed V := hP.preimage eA.symm.continuous
  set Vspec := hA' '' V with hVspecDef
  have hVspec : IsClosed Vspec := hA'.isClosedMap V hV
  set imageSpec := PrimeSpectrum.comap m.appTop.hom '' Vspec with himageSpecDef
  -- The image of `C` is cut out by `imageSpec`.
  have himage_eq : pointsMap B S hS F f '' C = eU ⁻¹' (hU' ⁻¹' imageSpec) := by
    ext z
    constructor
    · rintro ⟨w, hwC, rfl⟩
      obtain ⟨wA, hwA⟩ := hφsurjPoints w
      have hxV : eA wA ∈ V := by
        rw [hVdef, Set.mem_preimage, Homeomorph.symm_apply_apply, hPdef, Set.mem_preimage,
          hwA]
        exact hwC
      refine ⟨hA' (eA wA), ⟨eA wA, hxV, rfl⟩, ?_⟩
      rw [← hnat (eA wA), ← hbridge wA, hwA]
    · rintro ⟨w, ⟨x, hxV, rfl⟩, hz⟩
      refine ⟨pointsMap B S hS (yoneda.obj A) φ (eA.symm x), hxV, ?_⟩
      refine eU.injective ?_
      rw [hbridge (eA.symm x), Homeomorph.apply_symm_apply]
      exact hU'.injective ((hnat x).trans hz)
  -- The valuative criterion makes that image stable under specialization.
  have hstable : StableUnderSpecialization imageSpec := by
    rintro z z' hzz' ⟨w, ⟨x, hxV, rfl⟩, rfl⟩
    set pA := schemePointRepresentative B S hS A x with hpA
    set pX := FieldValuedPoint.map B S hS (yoneda.obj A) φ pA with hpX
    set y := hU'.symm z' with hy
    set qU := schemePointRepresentative B S hS U y with hqU
    have hpAclass : eA (pA.class B S hS (yoneda.obj A)) = x := by
      rw [heA, schemePointsHomeomorph_apply, pointsToScheme_class, hpA]
      exact schemePointRepresentative_point B S hS A x
    have hsymm : eA.symm x = pA.class B S hS (yoneda.obj A) :=
      (Homeomorph.symm_apply_eq _).2 hpAclass.symm
    have hpXC : pX.class B S hS F ∈ C := by
      have hmem := hxV
      rw [hVdef, Set.mem_preimage, hPdef, Set.mem_preimage, hsymm] at hmem
      rwa [hpX, ← pointsMap_class]
    have hsource : schemePoint B S hS U (FieldValuedPoint.map B S hS F f pX) = m x := by
      rw [← pointsToScheme_class B S hS U, ← pointsMap_class, hpX, ← pointsMap_class,
        show pointsToScheme B S hS U
            (pointsMap B S hS F f (pointsMap B S hS (yoneda.obj A) φ
              (pA.class B S hS (yoneda.obj A)))) =
            eU (pointsMap B S hS F f (pointsMap B S hS (yoneda.obj A) φ
              (pA.class B S hS (yoneda.obj A)))) from by
          rw [heU, schemePointsHomeomorph_apply],
        hbridge, hpAclass]
    have htarget : schemePoint B S hS U (FieldValuedPoint.map B S hS F f pX) ⤳
        schemePoint B S hS U qU := by
      rw [hqU, schemePointRepresentative_point B S hS U y, hsource, hy]
      have h := hzz'.map hU'.symm.continuous
      rwa [← hnat x, Homeomorph.symm_apply_apply] at h
    obtain ⟨r, hpr, hrf⟩ :=
      exists_specializes_pointsMap_eq_of_valuativeExistence U f pX qU htarget hval
    have hmemImage : qU.class B S hS (yoneda.obj U) ∈ pointsMap B S hS F f '' C :=
      ⟨r, hpr.mem_closed hC hpXC, hrf⟩
    have hqz : hU' (eU (qU.class B S hS (yoneda.obj U))) = z' := by
      rw [heU, schemePointsHomeomorph_apply, pointsToScheme_class, hqU,
        schemePointRepresentative_point B S hS U y, hy]
      exact hU'.apply_symm_apply z'
    rw [himage_eq] at hmemImage
    have hmem2 : hU' (eU (qU.class B S hS (yoneda.obj U))) ∈ imageSpec :=
      Set.mem_preimage.mp (Set.mem_preimage.mp hmemImage)
    rwa [hqz] at hmem2
  have hclosedSpec : IsClosed imageSpec :=
    PrimeSpectrum.isClosed_image_of_stableUnderSpecialization m.appTop.hom Vspec hVspec
      hstable
  rw [himage_eq]
  exact (hclosedSpec.preimage hU'.continuous).preimage eU.continuous

/-- **Stacks 03KA.** A quasi-compact morphism of algebraic spaces over `S` which satisfies the
existence part of the valuative criterion is universally closed.

By Stacks 03IT it is enough to check that the base change along every morphism from a
represented presheaf with affine scheme is closed on points; such a base change is again
quasi-compact (Stacks 03HF) and again satisfies the existence part (Stacks 03IY), so
`isClosedMap_pointsMap_of_isAffine_target` applies. -/
@[stacks 03KA]
theorem universallyClosed_of_isQuasiCompact_of_valuativeCriterion_existence
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsQuasiCompact B S hS f) (hval : ValuativeCriterion.Existence f) :
    UniversallyClosed B S hS f :=
  universallyClosed_of_isClosedMorphism_yoneda B S hS f
    (isClosedMorphism_pullback_fst_of_affine B S hS f fun W g hW ↦
      isClosedMap_pointsMap_of_isAffine_target
        (isAlgebraicSpace_pullback B S hS g f (isAlgebraicSpace_yoneda B S hS W) hX hY)
        W hW (pullback.fst g f)
        (isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback g f).flip hf)
        (valuativeCriterion_existence_of_isPullback (IsPullback.of_hasPullback g f).flip hval))

/-! ### The existence part from universal closedness -/

/-- The spectrum of the inclusion of a domain into its fraction field carries the closed point
of the fraction field to the generic point of the spectrum of the domain. -/
public theorem spec_algebraMap_closedPoint_eq_genericPoint
    {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] :
    (Spec.map (CommRingCat.ofHom (algebraMap R K)) : Spec (.of K) ⟶ Spec (.of R))
        (IsLocalRing.closedPoint K) =
      genericPoint (Spec (.of R)) := by
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap R K) (IsLocalRing.maximalIdeal K) = _
  rw [genericPoint_eq_bot_of_affine, IsLocalRing.maximalIdeal_eq_bot,
    Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)]
  rfl

/-- A closed set of points of a represented presheaf containing a point whose underlying point
of the representing scheme specializes to every point is the whole point space. -/
public theorem eq_univ_of_isClosed_of_specializes (U : BigFppfOver B S hS)
    (W : Set (points B S hS (yoneda.obj U))) (hW : IsClosed W)
    (c : points B S hS (yoneda.obj U)) (hc : c ∈ W)
    (hspec : ∀ t : (BigFppfOver.toScheme B S hS).obj U,
      pointsToScheme B S hS U c ⤳ t) :
    W = Set.univ := by
  have key : ∀ t : points B S hS (yoneda.obj U),
      (schemePointsHomeomorph B S hS U).symm (pointsToScheme B S hS U t) = t :=
    fun t ↦ (schemePointsHomeomorph B S hS U).symm_apply_apply t
  refine Set.eq_univ_of_forall fun z ↦ ?_
  have h := (hspec (pointsToScheme B S hS U z)).map
    (schemePointsHomeomorph B S hS U).symm.continuous
  rw [key c, key z] at h
  exact hW.stableUnderSpecialization h hc

/-- **Stacks 0A3X, part (1).** A quasi-separated universally closed morphism of algebraic spaces
over `S` satisfies the existence part of the valuative criterion.

A valuative square for `f` presents the generic point of its valuation ring `A` as a point of
the base change `P = X ×_Y Spec A`, through a section `g : Spec K ⟶ P`. Quasi-separatedness of
`P ⟶ Spec A` makes `g` quasi-compact (Stacks 03KS), the morphism `Spec K ⟶ Spec A` being
affine, so the points of the scheme-theoretic image `Z ⊆ P` of `g` are the closure of the
image of `g` (Stacks 082Z). Universal closedness makes the image of that closed set in
`|Spec A|` closed, and it contains the generic point, hence everything; so some point of `|Z|`
lies over the closed point of `Spec A`. Stacks 089B realizes that point by a valuation ring
`A'` with fraction field `K'` and a square `Spec K' ⟶ Spec K`, `Spec A' ⟶ Z`; composing with
`Z ⟶ P ⟶ X` gives the lift, and `A'` dominates `A` because the closed point of `Spec A'` maps
to the closed point of `Spec A`. -/
@[stacks 0A3X "part (1)"]
theorem valuativeCriterion_existence_of_isQuasiSeparated_of_universallyClosed
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hqs : IsQuasiSeparated B S hS f) (huc : UniversallyClosed B S hS f) :
    ValuativeCriterion.Existence f := by
  classical
  intro q
  let TA := siteObject B S hS q.ring_mem q.base
  let TK := siteObject B S hS q.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)
  have hA : IsAlgebraicSpace B S hS (yoneda.obj TA) := isAlgebraicSpace_yoneda B S hS TA
  have hK : IsAlgebraicSpace B S hS (yoneda.obj TK) := isAlgebraicSpace_yoneda B S hS TK
  have hP : IsAlgebraicSpace B S hS (pullback q.special f) :=
    isAlgebraicSpace_pullback B S hS q.special f hA hX hY
  let p : pullback q.special f ⟶ yoneda.obj TA := pullback.fst q.special f
  let pr : pullback q.special f ⟶ X := pullback.snd q.special f
  let g : yoneda.obj TK ⟶ pullback q.special f :=
    pullback.lift (yoneda.map q.fracHom) q.generic q.comm'.symm
  have hgp : g ≫ p = yoneda.map q.fracHom := pullback.lift_fst _ _ _
  have hgpr : g ≫ pr = q.generic := pullback.lift_snd _ _ _
  have htg : toSchemeTheoreticImage B S hS g ≫
      (schemeTheoreticImageSubfunctor B S hS g).ι = g :=
    toSchemeTheoreticImage_ι B S hS g
  -- The section `g` is quasi-compact, by Stacks 03KS.
  have hqsp : IsQuasiSeparated B S hS p :=
    (MorphismProperty.IsStableUnderBaseChange.diagonal
      (P := quasiCompactPresheafProperty B S hS)).of_isPullback
        (IsPullback.of_hasPullback q.special f).flip hqs
  have hgqc : IsQuasiCompact B S hS g := by
    refine isQuasiCompact_of_comp_of_isQuasiSeparated B S hS g p hK hA ?_ hqsp
    rw [hgp]
    refine isQuasiCompact_yoneda_map_of_isAffineHom B S hS q.fracHom ?_
    change _root_.AlgebraicGeometry.IsAffineHom
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)))
    infer_instance
  -- The scheme-theoretic image of `g`, whose points are the closure of the image of `g`.
  have hrange :
      Set.range (pointsMap B S hS (schemeTheoreticImageSubfunctor B S hS g).toFunctor
          (schemeTheoreticImageSubfunctor B S hS g).ι) =
        closure (Set.range (pointsMap B S hS (yoneda.obj TK) g)) :=
    range_pointsMap_ι_schemeTheoreticImage_eq_closure_of_isQuasiCompact B S hS g hK hP hgqc
  -- Universal closedness makes the image of that closed set closed in `|Spec A|`.
  have hW : IsClosed (pointsMap B S hS (pullback q.special f) p ''
      closure (Set.range (pointsMap B S hS (yoneda.obj TK) g))) :=
    huc (yoneda.obj TA) hA q.special _ isClosed_closure
  let tK := schemePointRepresentative B S hS TK (IsLocalRing.closedPoint q.K)
  let xGen := pointsMap B S hS (yoneda.obj TK) g (tK.class B S hS (yoneda.obj TK))
  have hxGen : pointsMap B S hS (pullback q.special f) p xGen ∈
      pointsMap B S hS (pullback q.special f) p ''
        closure (Set.range (pointsMap B S hS (yoneda.obj TK) g)) :=
    ⟨xGen, subset_closure ⟨_, rfl⟩, rfl⟩
  have hgenPoint : pointsToScheme B S hS TA
      (pointsMap B S hS (pullback q.special f) p xGen) = genericPoint (Spec (.of q.R)) := by
    have h1 : pointsMap B S hS (pullback q.special f) p xGen =
        pointsMap B S hS (yoneda.obj TK) (g ≫ p) (tK.class B S hS (yoneda.obj TK)) :=
      (congrFun (pointsMap_comp B S hS (yoneda.obj TK) g p) _).symm
    rw [h1, hgp, pointsToScheme_pointsMap B S hS q.fracHom, pointsToScheme_class,
      schemePointRepresentative_point B S hS TK (IsLocalRing.closedPoint q.K)]
    change (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)))
      (IsLocalRing.closedPoint q.K) = _
    exact spec_algebraMap_closedPoint_eq_genericPoint
  -- Hence the closed point of `Spec A` is hit as well.
  have hWuniv : pointsMap B S hS (pullback q.special f) p ''
      closure (Set.range (pointsMap B S hS (yoneda.obj TK) g)) = Set.univ :=
    eq_univ_of_isClosed_of_specializes TA _ hW _ hxGen fun t ↦ by
      rw [hgenPoint]
      exact (genericPoint_spec (Spec (.of q.R))).specializes (Set.mem_univ t)
  let cA := schemePointRepresentative B S hS TA (IsLocalRing.closedPoint q.R)
  obtain ⟨xs, hxs, hxsmap⟩ : cA.class B S hS (yoneda.obj TA) ∈
      pointsMap B S hS (pullback q.special f) p ''
        closure (Set.range (pointsMap B S hS (yoneda.obj TK) g)) :=
    hWuniv.symm ▸ Set.mem_univ _
  have hxsZ : xs ∈ Set.range (pointsMap B S hS
      (schemeTheoreticImageSubfunctor B S hS g).toFunctor
      (schemeTheoreticImageSubfunctor B S hS g).ι) := by rw [hrange]; exact hxs
  obtain ⟨z, hz⟩ := hxsZ
  -- Stacks 089B realizes `z` by a valuation ring dominating `A`.
  obtain ⟨q', w, hwclosed, hwspecial⟩ :=
    exists_valuativeSquare_toSchemeTheoreticImage B S hS g hK hP hgqc z
  let RObj := siteObject B S hS q'.ring_mem q'.base
  let KObj := siteObject B S hS q'.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap q'.R q'.K)) ≫ q'.base)
  let genericOver : KObj ⟶ TK := yoneda.preimage q'.generic
  have hgenericOver : yoneda.map genericOver = q'.generic := yoneda.map_preimage _
  let specialOver : RObj ⟶ TA :=
    yoneda.preimage (q'.special ≫ (schemeTheoreticImageSubfunctor B S hS g).ι ≫ p)
  have hspecialOver : yoneda.map specialOver =
      q'.special ≫ (schemeTheoreticImageSubfunctor B S hS g).ι ≫ p :=
    yoneda.map_preimage _
  let fieldMap : q.K →+* q'.K := (Spec.preimage (B.inclusion.map genericOver.left)).hom
  have hfieldMap : Spec.map (CommRingCat.ofHom fieldMap) = B.inclusion.map genericOver.left :=
    Spec.map_preimage _
  let ringMap : q.R →+* q'.R := (Spec.preimage (B.inclusion.map specialOver.left)).hom
  have hringMap : Spec.map (CommRingCat.ofHom ringMap) = B.inclusion.map specialOver.left :=
    Spec.map_preimage _
  -- The solid square of site objects underlying the extension.
  have hsq : genericOver ≫ q.fracHom = q'.fracHom ≫ specialOver := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, hgenericOver, hspecialOver]
    calc q'.generic ≫ yoneda.map q.fracHom
        = q'.generic ≫ g ≫ p := by rw [hgp]
      _ = q'.generic ≫ (toSchemeTheoreticImage B S hS g ≫
            (schemeTheoreticImageSubfunctor B S hS g).ι) ≫ p := by rw [htg]
      _ = (yoneda.map q'.fracHom ≫ q'.special) ≫
            (schemeTheoreticImageSubfunctor B S hS g).ι ≫ p := by
          rw [← q'.comm']; simp only [Category.assoc]
      _ = yoneda.map q'.fracHom ≫
            q'.special ≫ (schemeTheoreticImageSubfunctor B S hS g).ι ≫ p := by
          simp only [Category.assoc]
  have hsqScheme : B.inclusion.map genericOver.left ≫
        Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) =
      Spec.map (CommRingCat.ofHom (algebraMap q'.R q'.K)) ≫
        B.inclusion.map specialOver.left := by
    have h : B.inclusion.map (Over.Hom.left (genericOver ≫ q.fracHom)) =
        B.inclusion.map (Over.Hom.left (q'.fracHom ≫ specialOver)) :=
      congrArg (fun k : KObj ⟶ TA ↦ B.inclusion.map (Over.Hom.left k)) hsq
    rw [Over.comp_left, Over.comp_left, Functor.map_comp, Functor.map_comp] at h
    simpa only [ValuativeSquare.fracHom, Over.homMk_left, ObjectProperty.ι_map,
      ObjectProperty.homMk_hom] using h
  have hfraction : (algebraMap q'.R q'.K).comp ringMap = fieldMap.comp (algebraMap q.R q.K) := by
    have he : CommRingCat.ofHom ((algebraMap q'.R q'.K).comp ringMap) =
        CommRingCat.ofHom (fieldMap.comp (algebraMap q.R q.K)) := by
      apply Spec.map_injective
      rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
        hringMap, hfieldMap]
      exact hsqScheme.symm
    exact congrArg CommRingCat.Hom.hom he
  have hbase : q'.base = Spec.map (CommRingCat.ofHom ringMap) ≫ q.base := by
    rw [hringMap]
    exact (congrArg B.inclusion.map (Over.w specialOver)).symm
  -- The new valuation ring dominates `A`, by the closed point of `Spec A'`.
  have hclosed : PrimeSpectrum.comap ringMap (IsLocalRing.closedPoint q'.R) =
      IsLocalRing.closedPoint q.R := by
    have h1 : pointsMap B S hS (yoneda.obj RObj) (yoneda.map specialOver) w =
        cA.class B S hS (yoneda.obj TA) := by
      rw [hspecialOver, pointsMap_comp, Function.comp_apply, pointsMap_comp,
        Function.comp_apply, hwspecial, hz]
      exact hxsmap
    have h2 := pointsToScheme_pointsMap_yoneda B S hS specialOver w
    rw [h1, hwclosed] at h2
    have h4 : pointsToScheme B S hS TA (cA.class B S hS (yoneda.obj TA)) =
        IsLocalRing.closedPoint q.R := by
      rw [pointsToScheme_class]
      exact schemePointRepresentative_point B S hS TA (IsLocalRing.closedPoint q.R)
    change (Spec.map (CommRingCat.ofHom ringMap)) (IsLocalRing.closedPoint q'.R) =
      IsLocalRing.closedPoint q.R
    rw [hringMap]
    exact h2.symm.trans h4
  -- The dominating extension, with its lift.
  let lift : yoneda.obj RObj ⟶ X :=
    q'.special ≫ (schemeTheoreticImageSubfunctor B S hS g).ι ≫ pr
  have hliftGeneric : yoneda.map q'.fracHom ≫ lift = yoneda.map genericOver ≫ q.generic := by
    rw [hgenericOver]
    calc yoneda.map q'.fracHom ≫
            q'.special ≫ (schemeTheoreticImageSubfunctor B S hS g).ι ≫ pr
        = (yoneda.map q'.fracHom ≫ q'.special) ≫
            (schemeTheoreticImageSubfunctor B S hS g).ι ≫ pr := by
          simp only [Category.assoc]
      _ = (q'.generic ≫ toSchemeTheoreticImage B S hS g) ≫
            (schemeTheoreticImageSubfunctor B S hS g).ι ≫ pr := by rw [q'.comm']
      _ = q'.generic ≫ (toSchemeTheoreticImage B S hS g ≫
            (schemeTheoreticImageSubfunctor B S hS g).ι) ≫ pr := by
          simp only [Category.assoc]
      _ = q'.generic ≫ g ≫ pr := by rw [htg]
      _ = q'.generic ≫ q.generic := by rw [hgpr]
  have hliftSpecial : lift ≫ f = yoneda.map specialOver ≫ q.special := by
    rw [hspecialOver]
    calc (q'.special ≫ (schemeTheoreticImageSubfunctor B S hS g).ι ≫ pr) ≫ f
        = q'.special ≫ (schemeTheoreticImageSubfunctor B S hS g).ι ≫ pr ≫ f := by
          simp only [Category.assoc]
      _ = q'.special ≫ (schemeTheoreticImageSubfunctor B S hS g).ι ≫ p ≫ q.special := by
          rw [show pr ≫ f = p ≫ q.special from pullback.condition.symm]
      _ = (q'.special ≫ (schemeTheoreticImageSubfunctor B S hS g).ι ≫ p) ≫ q.special := by
          simp only [Category.assoc]
  refine ⟨{ square :=
              { R := q'.R, K := q'.K, ring_mem := q'.ring_mem, field_mem := q'.field_mem
                base := q'.base
                generic := yoneda.map genericOver ≫ q.generic
                special := yoneda.map specialOver ≫ q.special
                comm := by rw [← hliftGeneric, Category.assoc, hliftSpecial] }
            ringMap := ringMap
            fieldMap := fieldMap
            isLocalHom := (IsLocalRing.isLocalHom_iff_comap_closedPoint ringMap).2 hclosed
            fraction_comm := hfraction
            base_comm := hbase
            genericOver := genericOver
            genericOver_left := hfieldMap.symm
            specialOver := specialOver
            specialOver_left := hringMap.symm
            generic_comm := rfl
            special_comm := rfl },
    ⟨⟨lift, hliftGeneric, hliftSpecial⟩⟩⟩

/-- **Stacks 0A3X, part (2).** A quasi-compact quasi-separated morphism of algebraic spaces over
`S` is universally closed exactly when it satisfies the existence part of the valuative
criterion.

One direction is Stacks 03KA, the other is part (1). -/
@[stacks 0A3X "part (2)"]
theorem universallyClosed_iff_valuativeCriterion_existence_of_isQuasiCompact_of_isQuasiSeparated
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hqc : IsQuasiCompact B S hS f) (hqs : IsQuasiSeparated B S hS f) :
    UniversallyClosed B S hS f ↔ ValuativeCriterion.Existence f :=
  ⟨valuativeCriterion_existence_of_isQuasiSeparated_of_universallyClosed hX hY f hqs,
    universallyClosed_of_isQuasiCompact_of_valuativeCriterion_existence hX hY f hqc⟩

/-! ### Separatedness from the uniqueness part -/

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the pullbacks `pullback f f` of presheaves on the big fppf site
/-- The relative diagonal of a morphism satisfying the uniqueness part of the valuative
criterion satisfies the existence part.

A valuative square for the diagonal gives two lifts of an induced valuative square for `f`,
namely its bottom edge followed by each projection; uniqueness identifies them, and the
common value is a lift of the original square over the valuation ring itself, so no
dominating extension is needed. -/
private theorem valuativeCriterion_existence_pullbackDiagonal_of_uniqueness (f : X ⟶ Y)
    (hu : ValuativeCriterion.Uniqueness f) :
    ValuativeCriterion.Existence (pullback.diagonal f) := by
  intro q
  have hgen {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (t : pullback f f ⟶ T) :
      yoneda.map q.fracHom ≫ q.special ≫ t = q.generic ≫ pullback.diagonal f ≫ t := by
    simp only [← Category.assoc, q.comm']
  let qf : ValuativeSquare f :=
    { R := q.R, K := q.K, ring_mem := q.ring_mem, field_mem := q.field_mem, base := q.base
      generic := q.generic
      special := q.special ≫ pullback.fst f f ≫ f
      comm := by simpa [Category.assoc] using (hgen (pullback.fst f f ≫ f)).symm }
  let leftLift : qf.Lift :=
    { map := q.special ≫ pullback.fst f f
      generic_comm := by simpa [Category.assoc] using hgen (pullback.fst f f)
      special_comm := rfl }
  let rightLift : qf.Lift :=
    { map := q.special ≫ pullback.snd f f
      generic_comm := by simpa [Category.assoc] using hgen (pullback.snd f f)
      special_comm := by
        simpa [Category.assoc] using
          congrArg (fun t ↦ q.special ≫ t) (pullback.condition (f := f) (g := f)).symm }
  have hmaps : leftLift.map = rightLift.map :=
    congrArg ValuativeSquare.Lift.map ((hu qf).allEq leftLift rightLift)
  have hid (R : Type u) [CommRing R] : Spec.map (CommRingCat.ofHom (RingHom.id R)) = 𝟙 _ := by
    rw [show CommRingCat.ofHom (RingHom.id R) = 𝟙 (CommRingCat.of R) from rfl, Spec.map_id]
  let ext : q.DominatingExtension :=
    { square := q
      ringMap := RingHom.id q.R, fieldMap := RingHom.id q.K
      isLocalHom := isLocalHom_id q.R
      fraction_comm := by simp
      base_comm := by rw [hid q.R, Category.id_comp]
      genericOver := 𝟙 _
      genericOver_left := (hid q.K).symm
      specialOver := 𝟙 _
      specialOver_left := (hid q.R).symm
      generic_comm := by rw [yoneda.map_id, Category.id_comp]
      special_comm := by rw [yoneda.map_id, Category.id_comp] }
  have lifted : q.Lift :=
    { map := q.special ≫ pullback.fst f f
      generic_comm := leftLift.generic_comm
      special_comm := by
        refine pullback.hom_ext ?_ ?_
        · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
        · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id]
          exact hmaps }
  exact ⟨ext, ⟨lifted⟩⟩

/-- **Stacks 03KV.** A quasi-separated morphism of algebraic spaces over `S` which satisfies
the uniqueness part of the valuative criterion is separated.

Quasi-separatedness is quasi-compactness of the relative diagonal, and the diagonal satisfies
the existence part of the criterion, so by Stacks 03KA it is universally closed. Being also
separated, locally of finite type and locally quasi-finite (Stacks 03HK), every represented
base change of it is a proper locally quasi-finite morphism of schemes, hence finite; being in
addition a monomorphism, it is a closed immersion. -/
@[stacks 03KV]
theorem isSeparated_of_isQuasiSeparated_of_valuativeCriterion_uniqueness
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hqs : IsQuasiSeparated B S hS f) (hu : ValuativeCriterion.Uniqueness f) :
    IsSeparated B S hS f := by
  have hdAlg := isAlgebraicSpace_pullback B S hS f f hX hX hY
  have hRep : yoneda.relativelyRepresentable (pullback.diagonal f) :=
    relativelyRepresentable_pullbackDiagonal B S hS f hX
  have hUC' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.UniversallyClosed.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (pullback.diagonal f) :=
    (presheaf_universallyClosed_iff B S hS hX hdAlg hRep).2
      (universallyClosed_of_isQuasiCompact_of_valuativeCriterion_existence hX hdAlg
        (pullback.diagonal f) hqs
        (valuativeCriterion_existence_pullbackDiagonal_of_uniqueness f hu))
  have hProperLqf : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      ((@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      (BigFppfOver.toScheme B S hS))) (pullback.diagonal f) := by
    refine ⟨hRep, ?_⟩
    intro V W g fst snd hp
    have hsep := (presheaf_isSeparated_pullbackDiagonal B S hS f hX).property g fst snd hp
    have huc := hUC'.property g fst snd hp
    have hlft :=
      (presheaf_locallyOfFiniteType_pullbackDiagonal B S hS f hX).property g fst snd hp
    have hlqf :=
      ((presheaf_locallyQuasiFinite_pullbackDiagonal B S hS f hX).property g fst snd hp).2
    have h1 : _root_.AlgebraicGeometry.IsSeparated
      ((BigFppfOver.toScheme B S hS).map snd) := hsep
    have h2 : _root_.AlgebraicGeometry.UniversallyClosed
      ((BigFppfOver.toScheme B S hS).map snd) := huc
    have h3 : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map snd) := hlft
    exact ⟨_root_.AlgebraicGeometry.IsProper.mk, hlqf⟩
  have hFinite : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (pullback.diagonal f) := by
    refine MorphismProperty.relative_monotone (F := yoneda) ?_ _ hProperLqf
    intro V W g hg
    exact (_root_.AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite
      ((BigFppfOver.toScheme B S hS).map g)).2 hg
  refine ⟨hRep, fun V W g fst snd hp ↦ ?_⟩
  exact (_root_.AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono
    ((BigFppfOver.toScheme B S hS).map snd)).2
    ⟨hFinite.property g fst snd hp,
      (presheaf_monomorphisms_pullbackDiagonal B S hS f hX).property g fst snd hp⟩

end PointTopology

/-! ### Lifting a valuation ring through a flat morphism -/

/-- Two field-valued points of a represented presheaf defining the same point have the same
image of the closed point, so one of them has that image at the closed point of a local ring
if and only if the other does. -/
private theorem map_closedPoint_of_class_eq (V : BigFppfOver B S hS) {A : Type u} [CommRing A]
    [IsLocalRing A] (e : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of A))
    (p q : FieldValuedPoint B S hS (yoneda.obj V))
    (h : p.class B S hS (yoneda.obj V) = q.class B S hS (yoneda.obj V))
    (hp : e.hom ((BigFppfOver.toScheme B S hS).map p.value
      (IsLocalRing.closedPoint p.carrier)) = IsLocalRing.closedPoint A) :
    e.hom ((BigFppfOver.toScheme B S hS).map q.value
      (IsLocalRing.closedPoint q.carrier)) = IsLocalRing.closedPoint A := by
  obtain ⟨r, ⟨k, hk⟩, ⟨l, hl⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS (yoneda.obj V) p q).mp h
  have key (s : FieldValuedPoint B S hS (yoneda.obj V))
      (m : r.siteObject B S hS (yoneda.obj V) ⟶ s.siteObject B S hS (yoneda.obj V))
      (hm : m ≫ s.value = r.value) :
      (BigFppfOver.toScheme B S hS).map s.value (IsLocalRing.closedPoint s.carrier) =
        (BigFppfOver.toScheme B S hS).map r.value (IsLocalRing.closedPoint r.carrier) := by
    have hSub : Subsingleton
        ((BigFppfOver.toScheme B S hS).obj (s.siteObject B S hS (yoneda.obj V))) :=
      inferInstanceAs (Subsingleton (Spec (.of s.carrier)))
    have h1 : (BigFppfOver.toScheme B S hS).map m ≫ (BigFppfOver.toScheme B S hS).map s.value =
        (BigFppfOver.toScheme B S hS).map r.value := by rw [← Functor.map_comp, hm]
    have h3 : (BigFppfOver.toScheme B S hS).map m (IsLocalRing.closedPoint r.carrier) =
        IsLocalRing.closedPoint s.carrier := hSub.elim _ _
    rw [← h1]
    exact (congrArg _ h3.symm).trans (Scheme.Hom.comp_apply _ _ _).symm
  rw [key q l hl, ← key p k hk, hp]

/-- **Stacks 089F.** Let `f : X ⟶ Y` be a flat morphism of algebraic spaces over `S` and let
`Spec A ⟶ Y` be a morphism with `A` a valuation ring. If the closed point of `Spec A` maps to
a point of `|Y|` in the image of `|X| → |Y|`, then there is an extension of valuation rings
`A ⟶ A'` and a commutative square filling in `Spec A' ⟶ X` over `Spec A ⟶ Y`.

The point of `|X|` above the closed point is produced by a chart `U ⟶ X ×_Y Spec A` of the
fibre product (Stacks 03H4, 03H5). The chart is flat over `Spec A` because flatness is stable
under base change (Stacks 03MO) and may be read on étale charts, so the induced homomorphism
`A ⟶ 𝒪_{U, u}` is flat and local, hence faithfully flat; a prime of the stalk contracting to
the zero ideal of `A` therefore exists, and factoring the resulting map to its fraction field
through a valuation subring gives `A'`. -/
@[stacks 089F]
theorem exists_valuationRing_extension_lift_of_isFlat
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsFlat B S hS f)
    (V : BigFppfOver B S hS)
    (e : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of A))
    (g : yoneda.obj V ⟶ Y)
    (p : FieldValuedPoint B S hS (yoneda.obj V))
    (hp : e.hom ((BigFppfOver.toScheme B S hS).map p.value
      (IsLocalRing.closedPoint p.carrier)) = IsLocalRing.closedPoint A)
    (himage : ∃ x : points B S hS X, pointsMap B S hS X f x =
      pointsMap B S hS (yoneda.obj V) g (p.class B S hS (yoneda.obj V))) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : IsDomain A') (_ : ValuationRing A') (ι : A →+* A'),
      ValuationRing.IsExtension ι ∧
      ∃ (V' : BigFppfOver B S hS)
        (e' : (BigFppfOver.toScheme B S hS).obj V' ≅ Spec (.of A'))
        (j : V' ⟶ V) (lift : yoneda.obj V' ⟶ X),
        (BigFppfOver.toScheme B S hS).map j ≫ e.hom =
          e'.hom ≫ Spec.map (CommRingCat.ofHom ι) ∧
        lift ≫ f = yoneda.map j ≫ g := by
  classical
  obtain ⟨x, hx⟩ := himage
  set Xsp : AlgebraicSpaces B S hS := ⟨X, hX⟩ with hXsp
  set Vsp : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ with hVsp
  set fsp : Xsp ⟶ (⟨Y, hY⟩ : AlgebraicSpaces B S hS) := ObjectProperty.homMk f with hfsp
  set gsp : Vsp ⟶ (⟨Y, hY⟩ : AlgebraicSpaces B S hS) := ObjectProperty.homMk g with hgsp
  have sq := AlgebraicSpaces.isPullback_fiberProduct B S hS fsp gsp
  obtain ⟨w, hwx, hwv⟩ :=
    exists_point_of_isPullback B S hS sq x (p.class B S hS (yoneda.obj V)) hx
  obtain ⟨U, a, hSurj, hEtale⟩ :=
    (AlgebraicSpaces.fiberProduct B S hS fsp gsp).property.exists_atlas
  obtain ⟨z, hz⟩ :=
    (surjective_iff_surjective_pointsMap B S hS (AlgebraicSpaces.fiberProduct B S hS fsp gsp).1
      (AlgebraicSpaces.fiberProduct B S hS fsp gsp).property U a).mp hSurj w
  obtain ⟨q, hq⟩ := Quot.exists_rep z
  have hqW : pointsMap B S hS (yoneda.obj U) a (q.class B S hS (yoneda.obj U)) = w := by
    rw [show q.class B S hS (yoneda.obj U) = z from hq]; exact hz
  set snd₀ := (ObjectProperty.homMk (pullback.snd f g) :
    AlgebraicSpaces.fiberProduct B S hS fsp gsp ⟶ Vsp).hom with hsnd₀
  set fst₀ := (ObjectProperty.homMk (pullback.fst f g) :
    AlgebraicSpaces.fiberProduct B S hS fsp gsp ⟶ Xsp).hom with hfst₀
  set h : U ⟶ V := yoneda.preimage (a ≫ snd₀) with hhdef
  have hmap : yoneda.map h = a ≫ snd₀ := yoneda.map_preimage (a ≫ snd₀)
  have hqV : pointsMap B S hS (yoneda.obj U) (a ≫ snd₀)
      (q.class B S hS (yoneda.obj U)) = p.class B S hS (yoneda.obj V) := by
    rw [pointsMap_comp, Function.comp_apply, hqW]; exact hwv
  set qV := FieldValuedPoint.map B S hS (yoneda.obj U) (a ≫ snd₀) q with hqVdef
  have hclosedV := map_closedPoint_of_class_eq V e p qV
    ((pointsMap_class B S hS (yoneda.obj U) (a ≫ snd₀) q).symm.trans hqV).symm hp
  -- The induced morphism of schemes `U ⟶ V` and its stalk at the chosen point.
  set u : (BigFppfOver.toScheme B S hS).obj U :=
    (BigFppfOver.toScheme B S hS).map q.value (IsLocalRing.closedPoint q.carrier) with hu
  have hval : qV.value = q.value ≫ h :=
    (congrArg (fun α ↦ α.app (Opposite.op (q.siteObject B S hS (yoneda.obj U))) q.value)
      hmap).symm
  have hclosedU : e.hom ((BigFppfOver.toScheme B S hS).map h u) =
      IsLocalRing.closedPoint A := by
    have h1 : (BigFppfOver.toScheme B S hS).map qV.value
          (IsLocalRing.closedPoint qV.carrier) =
        (BigFppfOver.toScheme B S hS).map h u := by
      calc (BigFppfOver.toScheme B S hS).map qV.value
            (IsLocalRing.closedPoint qV.carrier)
          = ((BigFppfOver.toScheme B S hS).map q.value ≫
              (BigFppfOver.toScheme B S hS).map h) (IsLocalRing.closedPoint q.carrier) := by
            rw [← (BigFppfOver.toScheme B S hS).map_comp, ← hval]
            rfl
        _ = (BigFppfOver.toScheme B S hS).map h u := by
            rw [hu]; exact Scheme.Hom.comp_apply _ _ _
    rw [← h1]
    exact hclosedV
  -- Flatness of the composite `U ⟶ V ≅ Spec A`.
  have hproj : IsFlat B S hS snd₀ :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hf
  have hflat : Flat ((BigFppfOver.toScheme B S hS).map h) :=
    hproj U V a (𝟙 (yoneda.obj V)) h hEtale
      (presheaf_etale_of_iso B S hS (Iso.refl (yoneda.obj V)))
      (by rw [hmap, Category.comp_id])
  set k : (BigFppfOver.toScheme B S hS).obj U ⟶ Spec (.of A) :=
    (BigFppfOver.toScheme B S hS).map h ≫ e.hom with hkdef
  have hkflat : Flat k := by
    rw [hkdef]
    infer_instance
  have hkclosed : k u = IsLocalRing.closedPoint A := by
    rw [hkdef, Scheme.Hom.comp_apply]; exact hclosedU
  set ek : CommRingCat.of A ≅ (Spec (.of A)).presheaf.stalk (k u) :=
    (AlgebraicGeometry.stalkClosedPointIso (.of A)).symm ≪≫
      (Spec (.of A)).presheaf.stalkCongr (.of_eq hkclosed.symm) with hek
  set α : CommRingCat.of A ⟶ ((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk u :=
    ek.hom ≫ k.stalkMap u with hα
  have hαflat : RingHom.Flat α.hom := by
    rw [hα]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso ek.hom)) (Flat.stalkMap k u)
  have hαlocal : IsLocalHom α.hom := by
    have h1 : IsLocalHom ek.hom.hom :=
      IsLocalHom.of_surjective ek.hom.hom (ConcreteCategory.bijective_of_isIso ek.hom).2
    have h2 : IsLocalHom (k.stalkMap u).hom := inferInstance
    rw [hα]
    change IsLocalHom ((k.stalkMap u).hom.comp ek.hom.hom)
    exact RingHom.isLocalHom_comp _ _
  let _ : Algebra A (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk u) :=
    α.hom.toAlgebra
  have hαff : RingHom.FaithfullyFlat α.hom := by
    have h1 : Module.Flat A (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk u) := by
      rw [← RingHom.flat_algebraMap_iff]
      simpa only [RingHom.algebraMap_toAlgebra] using hαflat
    have h2 : IsLocalHom (algebraMap A
        (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk u)) := by
      rw [RingHom.algebraMap_toAlgebra]; exact hαlocal
    rw [← RingHom.algebraMap_toAlgebra α.hom, RingHom.faithfullyFlat_algebraMap_iff]
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  obtain ⟨P, hP⟩ := (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hαff).2
    ⟨⊥, Ideal.isPrime_bot⟩
  -- The fraction field of the quotient by that prime, and a valuation subring of it.
  set D := ((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk u ⧸ P.asIdeal with hD
  set ψ : A →+* D := (Ideal.Quotient.mk P.asIdeal).comp α.hom with hψ
  have hzero : Ideal.comap α.hom P.asIdeal = (⊥ : Ideal A) := by
    rw [← PrimeSpectrum.comap_asIdeal α.hom ⟨P.asIdeal, P.isPrime⟩]
    exact congrArg PrimeSpectrum.asIdeal hP
  have hψinj : Function.Injective ψ := by
    intro b c hbc
    have hmem : α.hom (b - c) ∈ P.asIdeal := by
      refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
      change ψ (b - c) = 0
      rw [map_sub, hbc, sub_self]
    have hmem' : (b - c) ∈ Ideal.comap α.hom P.asIdeal := hmem
    rw [hzero] at hmem'
    exact sub_eq_zero.mp (Ideal.mem_bot.mp hmem')
  set K := FractionRing D with hK
  have hψKinj : Function.Injective ((algebraMap D K).comp ψ) :=
    (IsFractionRing.injective D K).comp hψinj
  obtain ⟨Vring, hρsub, hρlocal⟩ := IsLocalRing.exists_factor_valuationRing
    (((algebraMap D K).comp (Ideal.Quotient.mk P.asIdeal)) :
      ((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk u →+* K)
  set γ : ((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk u →+* Vring :=
    (((algebraMap D K).comp (Ideal.Quotient.mk P.asIdeal))).codRestrict
      Vring.toSubring hρsub with hγ
  set ι : A →+* Vring := γ.comp α.hom with hι
  have hιinj : Function.Injective ι := fun b c hbc ↦
    hψKinj (congrArg (fun t : Vring ↦ (t : K)) hbc)
  have hιext : ValuationRing.IsExtension ι :=
    ⟨hιinj, RingHom.isLocalHom_comp γ α.hom⟩
  -- Size bounds putting `Spec Vring` in the site.
  have hCsize : Cardinal.mk (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk u) ≤
      ((BigFppfOver.toScheme B S hS).obj U).size :=
    Scheme.mk_stalk_le_size ((BigFppfOver.toScheme B S hS).obj U) u
  have hDsize : Cardinal.mk D ≤ ((BigFppfOver.toScheme B S hS).obj U).size :=
    (Cardinal.mk_le_of_surjective (fun t ↦ Ideal.Quotient.mk_surjective t)).trans hCsize
  have hKsize : Cardinal.mk K ≤ ((BigFppfOver.toScheme B S hS).obj U).size :=
    (Cardinal.mk_le_of_isLocalization (nonZeroDivisors D) K).trans
      (max_le ((BigFppfOver.toScheme B S hS).obj U).aleph0_le_size hDsize)
  have hSpecK : B.Contains (Spec (.of K)) :=
    Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      (CommRingCat.of K) U.left.2
      (hKsize.trans (Cardinal.self_le_power _ Cardinal.one_le_aleph0))
  have hSpecV : B.Contains (Spec (.of Vring)) :=
    Scheme.size_Spec_lt_of_subring B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      Vring.toSubring hSpecK
  -- The new site object and the lift.
  set mU : Spec (.of Vring) ⟶ (BigFppfOver.toScheme B S hS).obj U :=
    Spec.map (CommRingCat.ofHom γ) ≫
      ((BigFppfOver.toScheme B S hS).obj U).fromSpecStalk u with hmU
  have hekspec : Spec.map ek.hom = (Spec (.of A)).fromSpecStalk (k u) := by
    rw [hek, Iso.trans_hom, Iso.symm_hom, Spec.map_comp,
      AlgebraicGeometry.Spec_stalkClosedPointIso]
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk
      ((Inseparable.of_eq hkclosed.symm).ge)
  have hmuk : mU ≫ k = Spec.map (CommRingCat.ofHom ι) := by
    rw [hmU, Category.assoc, hkdef]
    rw [show ((BigFppfOver.toScheme B S hS).obj U).fromSpecStalk u ≫
        ((BigFppfOver.toScheme B S hS).map h ≫ e.hom) =
        Spec.map (k.stalkMap u) ≫ (Spec (.of A)).fromSpecStalk (k u) from by
      rw [← hkdef, Scheme.SpecMap_stalkMap_fromSpecStalk]]
    rw [← hekspec, ← Spec.map_comp, ← Spec.map_comp, hι, hα]
    rfl
  set iV : Spec (.of Vring) ⟶ (BigFppfOver.toScheme B S hS).obj V :=
    Spec.map (CommRingCat.ofHom ι) ≫ e.inv with hiV
  have hmuk' : mU ≫ ((BigFppfOver.toScheme B S hS).map h ≫ e.hom) =
      Spec.map (CommRingCat.ofHom ι) := by rw [← hkdef]; exact hmuk
  have hmuh : mU ≫ (BigFppfOver.toScheme B S hS).map h = iV := by
    rw [hiV, ← hmuk',
      Category.assoc mU ((BigFppfOver.toScheme B S hS).map h ≫ e.hom) e.inv,
      Category.assoc ((BigFppfOver.toScheme B S hS).map h) e.hom e.inv, e.hom_inv_id,
      Category.comp_id]
  set Vobj : B.Schemes := ⟨Spec (.of Vring), hSpecV⟩ with hVobj
  set pV : Vobj ⟶ V.left := B.inclusion.preimage (X := Vobj) (Y := V.left) iV with hpVdef
  have hpV : B.inclusion.map pV = iV :=
    B.inclusion.map_preimage (X := Vobj) (Y := V.left) iV
  set pU : Vobj ⟶ U.left := B.inclusion.preimage (X := Vobj) (Y := U.left) mU with hpUdef
  have hpU : B.inclusion.map pU = mU :=
    B.inclusion.map_preimage (X := Vobj) (Y := U.left) mU
  set V' : BigFppfOver B S hS := Over.mk (pV ≫ V.hom) with hV'
  have hleft : pU ≫ h.left = pV := by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, hpU, hpV, ← hmuh]
    rfl
  have hOver : pU ≫ U.hom = V'.hom := by
    apply B.inclusion.map_injective
    change B.inclusion.map (pU ≫ U.hom) = B.inclusion.map (pV ≫ V.hom)
    rw [← hleft, Category.assoc, Over.w h]
  set j : V' ⟶ V := Over.homMk pV with hj
  set jU : V' ⟶ U := Over.homMk pU hOver with hjU
  have hjcomp : jU ≫ h = j := Over.OverMorphism.ext hleft
  refine ⟨Vring, inferInstance, inferInstance, inferInstance, ι, hιext,
    V', Iso.refl _, j, yoneda.map jU ≫ a ≫ fst₀, ?_, ?_⟩
  · rw [show (BigFppfOver.toScheme B S hS).map j = iV from hpV, hiV, Category.assoc,
      e.inv_hom_id, Category.comp_id, Iso.refl_hom, Category.id_comp]
  · have hWcomm : fst₀ ≫ f = snd₀ ≫ g := pullback.condition
    rw [← hjcomp, Functor.map_comp, hmap]
    simp only [Category.assoc, hWcomm]

end AlgebraicGeometry.Space

end
