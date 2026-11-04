module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.OfSchemeHom
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.TranscendenceDegree
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayDimensionFormula
public import StacksFrontier.AlgebraicGeometry.Morphisms.JacobsonPoints.Tfae
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.TranscendenceDegreeChart

/-!
# Relative dimension of a morphism of algebraic spaces

Stacks 04NM attaches to a point `x` of the source of a morphism of algebraic spaces
`f : X ⟶ Y` over a scheme `S` two numerical invariants: the dimension of the fibre of `f`
through `x`, and the transcendence degree of `x` over its image. Requiring the first to be
bounded by, or equal to, a fixed natural number at *every* point of the source gives the two
global notions of relative dimension of this file.

The file then proves two things about the transcendence degree. It is insensitive to a locally
quasi-finite first factor: for `X ⟶ Y ⟶ Z` with `X ⟶ Y` locally quasi-finite, a point of `X`
and its image in `Y` have the same transcendence degree over `Z`. And it vanishes at a finite
type point of an algebraic space locally of finite type over a Jacobson algebraic space.

## Main definitions

* `AlgebraicGeometry.Space.HasRelativeDimensionLEAt` is relative dimension `≤ d` at a point.
* `AlgebraicGeometry.Space.HasRelativeDimensionLE` is **Stacks 06LR**, part (1).
* `AlgebraicGeometry.Space.HasRelativeDimension` is **Stacks 06LR**, part (2).

## Main results

* `AlgebraicGeometry.Space.HasRelativeDimension.hasRelativeDimensionLE`: a morphism of
  relative dimension `d` has relative dimension `≤ d`.
* `AlgebraicGeometry.Space.hasTranscendenceDegreeAt_comp_iff_of_isLocallyQuasiFinite` is
  **Stacks 06RX**: a locally quasi-finite first factor does not change the transcendence
  degree over the final target.
* `AlgebraicGeometry.Space.hasTranscendenceDegreeAt_zero_of_isFiniteTypePoint` is
  **Stacks 0ECY**: over a Jacobson algebraic space, a finite type point of an algebraic space
  locally of finite type has transcendence degree zero.
* `AlgebraicGeometry.Space.dimensionAtPoint_eq_add_of_hasRelativeDimension` is
  **Stacks 0AFH**: a flat morphism locally of finite type of relative dimension `d` between
  locally Noetherian algebraic spaces raises the dimension at a point by `d`.
* `AlgebraicGeometry.residueField_module_finite_of_locallyQuasiFinite`: a locally
  quasi-finite morphism of schemes has a finite residue-field extension at every point of its
  source.
* `AlgebraicGeometry.trdeg_residueField_eq_of_locallyQuasiFinite` is the scheme-level content
  of Stacks 06RX, and
  `hasResidueFieldTranscendenceDegree_comp_iff_of_locallyQuasiFinite` in the namespace
  `AlgebraicGeometry.MorphismOfGerms` is its germ-level form.
  `AlgebraicGeometry.MorphismOfGerms.hasResidueFieldTranscendenceDegree_ofSchemeHom_iff`, which
  unfolds the germ property of Tag 04NK for the germ of a morphism of schemes as a transcendence
  degree of residue fields, is imported.

## Implementation notes

`AlgebraicGeometry.Space.HasRelativeDimensionAt` of Tag 04NM is a predicate on a value in
`ℕ∞` rather than a function returning one, so "the relative dimension at `x` is at most `d`"
is rendered here as the existence of a value `e ≤ d` which the relative dimension at `x` has.
Since the bound `d` is a natural number, such an `e` is automatically finite, and the
pointwise bound is the statement of the source.

All three relative-dimension predicates are abbreviations, as the pointwise predicate of Tag
04NM already is, so the chart-locality API of Tag 04NC applies to them without an unfolding
lemma. Following Tag 04NM they are stated for an arbitrary morphism of presheaves on the big
fppf site of `S`; the algebraic-space hypotheses on source and target are supplied by clients
where that API needs them.

Equality of transcendence degrees is stated as an equivalence for each possible value in `ℕ∞`,
since the invariant of Tag 04NM is a predicate on values; by
`AlgebraicGeometry.MorphismOfGerms.hasResidueFieldTranscendenceDegree_unique` at most one
value holds, so the equivalence says exactly that the two degrees agree.

Tag 06RX also assumes the second morphism locally of finite type. That hypothesis is not
needed: the transcendence degree is defined, and read on étale charts, for an arbitrary
morphism, and the argument only uses local quasi-finiteness of the first morphism. So the
statement below omits it.

Four auxiliary results in the namespaces `AlgebraicGeometry` and
`AlgebraicGeometry.MorphismOfGerms` carry the scheme-level and germ-level content; no
algebraic space occurs in them. On charts the transcendence degree of Tag 04NM is the germ
property of Tag 04NK, and the germ of a morphism of schemes is represented on the whole
source, which the top open subscheme identification
`AlgebraicGeometry.Scheme.topIso` turns into the residue field of the ambient scheme — itself
an instance of the scheme-level comparison, since an isomorphism is locally quasi-finite.
Finiteness of the residue-field extension of a locally quasi-finite morphism is read off the
quasi-finiteness of the stalk map, `AlgebraicGeometry.Scheme.Hom.quasiFiniteAt`, through
`Algebra.WeaklyQuasiFiniteAt.finite_residueField` for the maximal ideals of the two stalks.

The space-level reduction to charts is
`AlgebraicGeometry.Space.exists_compatible_etale_charts_comp` of Tag 04NM, which supplies
surjective étale charts of the three spaces compatible with both morphisms; on them the two
transcendence degrees in question are those of the induced morphisms of charts, and the
identity charts of Tag 04NC read those off as germ properties.

The hypothesis that the target of Tag 0ECY is Jacobson is the étale-local property of Tag
03E6 for `JacobsonSpace`, written out as the existence of one surjective étale atlas by a
Jacobson scheme. It is written out, as in
`StacksFrontier/AlgebraicGeometry/Spaces/Jacobson.lean`, because
`AlgebraicGeometry.Space.HasEtaleLocalProperty` takes the étale locality of its property as
an instance argument; by Tag 03E8 the unfolded form is the same condition. Its proof base
changes the source along that atlas: the base change is surjective and étale over the source,
so by Tag 06EJ the chosen finite type point lifts to one of the base change, Tag 06EF puts
that lift at a closed point of an étale scheme chart, and the chart maps to the Jacobson
scheme by a morphism locally of finite type, so clause (4) of Tag 01TB makes the residue field
extension finite and the transcendence degree zero.

## References

* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
* [Stacks Project, Tag 04N5](https://stacks.math.columbia.edu/tag/04N5)
* [Stacks Project, Tag 04NL](https://stacks.math.columbia.edu/tag/04NL)
* [Stacks Project, Tag 04ZK](https://stacks.math.columbia.edu/tag/04ZK)
* [Stacks Project, Tag 06LR](https://stacks.math.columbia.edu/tag/06LR)
* [Stacks Project, Tag 06RX](https://stacks.math.columbia.edu/tag/06RX)
* [Stacks Project, Tag 0AFE](https://stacks.math.columbia.edu/tag/0AFE)
* [Stacks Project, Tag 0AFH](https://stacks.math.columbia.edu/tag/0AFH)
* [Stacks Project, Tag 0ECY](https://stacks.math.columbia.edu/tag/0ECY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Relative dimension -/

/-- The relative dimension of `f` at `x` is at most `d`: it has some value `e ≤ d`. -/
abbrev HasRelativeDimensionLEAt (d : ℕ) (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (x : points B S hS F) : Prop :=
  ∃ e : ℕ, e ≤ d ∧ HasRelativeDimensionAt (e : ℕ∞) B S hS f x

/-- **Stacks 06LR, part (1).** A morphism of algebraic spaces has *relative dimension `≤ d`*
if it has relative dimension `≤ d` at every point of its source. -/
@[stacks 06LR "part (1): relative dimension at most d"]
abbrev HasRelativeDimensionLE (d : ℕ) (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) : Prop :=
  ∀ x : points B S hS F, HasRelativeDimensionLEAt d B S hS f x

/-- **Stacks 06LR, part (2).** A morphism of algebraic spaces has *relative dimension `d`* if
it has relative dimension `d` at every point of its source. -/
@[stacks 06LR "part (2): relative dimension d"]
abbrev HasRelativeDimension (d : ℕ) (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) : Prop :=
  ∀ x : points B S hS F, HasRelativeDimensionAt (d : ℕ∞) B S hS f x

/-- A morphism of relative dimension `d` has relative dimension `≤ d`. -/
theorem HasRelativeDimension.hasRelativeDimensionLE {d : ℕ} {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : HasRelativeDimension d B S hS f) : HasRelativeDimensionLE d B S hS f :=
  fun x => ⟨d, le_rfl, hf x⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry

/-! ### Transcendence degree through a locally quasi-finite morphism of schemes -/

/-- A locally quasi-finite morphism of schemes induces a finite extension of residue fields at
every point of its source: the stalk map is quasi-finite, and the residue fields of the two
stalks are the residue fields of their maximal ideals. -/
theorem residueField_module_finite_of_locallyQuasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] (x : X) :
    let _ := (f.residueFieldMap x).hom.toAlgebra
    Module.Finite (Y.residueField (f x)) (X.residueField x) := by
  let R : Type u := Y.presheaf.stalk (f x)
  let A : Type u := X.presheaf.stalk x
  let φ : R →+* A := (f.stalkMap x).hom
  let : Algebra R A := φ.toAlgebra
  have : Algebra.QuasiFinite R A :=
    RingHom.quasiFinite_algebraMap.mp (Scheme.Hom.quasiFiniteAt f x)
  let p : Ideal R := IsLocalRing.maximalIdeal R
  let P : Ideal A := IsLocalRing.maximalIdeal A
  have : p.IsPrime := (IsLocalRing.maximalIdeal.isMaximal R).isPrime
  have : P.IsPrime := (IsLocalRing.maximalIdeal.isMaximal A).isPrime
  have : P.LiesOver p := ⟨(IsLocalRing.maximalIdeal_comap φ).symm⟩
  have : p.IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  have : P.IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime P) :=
    Localization.AtPrime.algebraOfLiesOver p P
  have : Localization.AtPrime.IsLiesOverAlgebra p P := inferInstance
  have : Module.Finite p.ResidueField P.ResidueField := inferInstance
  let eR : IsLocalRing.ResidueField R ≃+* p.ResidueField :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal p (Localization.AtPrime p)
  let eA : IsLocalRing.ResidueField A ≃+* P.ResidueField :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P)
  let : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A) :=
    (IsLocalRing.ResidueField.map φ).toAlgebra
  have hcompat : (algebraMap p.ResidueField P.ResidueField).comp eR.toRingHom =
      eA.toRingHom.comp (IsLocalRing.ResidueField.map φ) := by
    ext z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    show algebraMap p.ResidueField P.ResidueField (eR (IsLocalRing.residue R r)) =
      eA ((IsLocalRing.ResidueField.map φ) (IsLocalRing.residue R r))
    rw [IsLocalRing.ResidueField.map_residue]
    show algebraMap p.ResidueField P.ResidueField
        ((IsLocalization.AtPrime.equivQuotMaximalIdeal p (Localization.AtPrime p))
          (Ideal.Quotient.mk _ r)) =
      (IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P))
        (Ideal.Quotient.mk _ (φ r))
    rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk,
      IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk]
    show algebraMap p.ResidueField P.ResidueField (algebraMap R p.ResidueField r) =
      algebraMap A P.ResidueField (φ r)
    exact Ideal.ResidueField.map_algebraMap p P φ
      (IsLocalRing.maximalIdeal_comap φ).symm r
  have hdim : Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A) =
      Module.finrank p.ResidueField P.ResidueField :=
    Algebra.finrank_eq_of_equiv_equiv eR eA hcompat
  show Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)
  exact Module.finite_of_finrank_pos (hdim ▸ Module.finrank_pos)

/-- **The scheme-level content of Stacks 06RX.** For `p : A ⟶ B` locally quasi-finite and
`q : B ⟶ C`, the residue field at a point `x` of `A` and the residue field at `p x` have the
same transcendence degree over the residue field at the image of `x` in `C`: the first is a
finite extension of the second, so it contributes nothing to the tower. -/
theorem trdeg_residueField_eq_of_locallyQuasiFinite
    {A B C : Scheme.{u}} (p : A ⟶ B) (q : B ⟶ C) [LocallyQuasiFinite p] (x : A) :
    let _ : Algebra (C.residueField (q (p x))) (A.residueField x) :=
      ((p ≫ q).residueFieldMap x).hom.toAlgebra
    let _ : Algebra (C.residueField (q (p x))) (B.residueField (p x)) :=
      (q.residueFieldMap (p x)).hom.toAlgebra
    Algebra.trdeg (C.residueField (q (p x))) (A.residueField x) =
      Algebra.trdeg (C.residueField (q (p x))) (B.residueField (p x)) := by
  let K := C.residueField (q (p x))
  let K' := B.residueField (p x)
  let L := A.residueField x
  let : Algebra K' L := (p.residueFieldMap x).hom.toAlgebra
  let : Algebra K K' := (q.residueFieldMap (p x)).hom.toAlgebra
  let : Algebra K L := ((p ≫ q).residueFieldMap x).hom.toAlgebra
  have : IsScalarTower K K' L := IsScalarTower.of_algebraMap_eq' (by
    ext a
    show ((p ≫ q).residueFieldMap x).hom a =
      (p.residueFieldMap x).hom ((q.residueFieldMap (p x)).hom a)
    rw [Scheme.residueFieldMap_comp]
    rfl)
  have : Module.Finite K' L := residueField_module_finite_of_locallyQuasiFinite p x
  have : Algebra.IsAlgebraic K' L := Algebra.IsAlgebraic.of_finite K' L
  simpa [show Algebra.trdeg K' L = 0 from trdeg_eq_zero] using (trdeg_add_eq K K' (A := L)).symm

namespace MorphismOfGerms

/-- **The germ-level content of Stacks 06RX.** If a germ of a morphism of schemes factors as a
locally quasi-finite morphism followed by a second morphism, its residue-field transcendence
degree is that of the second morphism at the intermediate point. -/
theorem hasResidueFieldTranscendenceDegree_comp_iff_of_locallyQuasiFinite (r : ℕ∞)
    {A B C : Scheme.{u}} (h : A ⟶ C) (p : A ⟶ B) (q : B ⟶ C) (hh : h = p ≫ q)
    [LocallyQuasiFinite p] (x : A) (y : B) (hy : p x = y) :
    HasResidueFieldTranscendenceDegree r (ofSchemeHom h x) ↔
      HasResidueFieldTranscendenceDegree r (ofSchemeHom q y) := by
  subst hy hh
  rw [hasResidueFieldTranscendenceDegree_ofSchemeHom_iff,
    hasResidueFieldTranscendenceDegree_ofSchemeHom_iff]
  exact Iff.of_eq (congrArg (fun c : Cardinal => Cardinal.toENat c = r)
    (trdeg_residueField_eq_of_locallyQuasiFinite p q x))

/-- A germ of a morphism of schemes inducing a finite residue-field extension has
residue-field transcendence degree zero. -/
private theorem hasResidueFieldTranscendenceDegree_zero_of_finite {X Y : Scheme.{u}} (φ : X ⟶ Y)
    (x : X) (hfin : letI := (φ.residueFieldMap x).hom.toAlgebra
      Module.Finite (Y.residueField (φ x)) (X.residueField x)) :
    HasResidueFieldTranscendenceDegree 0 (ofSchemeHom φ x) := by
  refine (hasResidueFieldTranscendenceDegree_ofSchemeHom_iff φ x 0).mpr ?_
  let _ : Algebra (Y.residueField (φ x)) (X.residueField x) :=
    (φ.residueFieldMap x).hom.toAlgebra
  have _ : Module.Finite (Y.residueField (φ x)) (X.residueField x) := hfin
  have _ : Algebra.IsAlgebraic (Y.residueField (φ x)) (X.residueField x) :=
    Algebra.IsAlgebraic.of_finite _ _
  show Cardinal.toENat (Algebra.trdeg (Y.residueField (φ x)) (X.residueField x)) = 0
  rw [trdeg_eq_zero]
  simp

end MorphismOfGerms

/-! ### The local dimension of a fibre of a morphism of schemes -/

/-- The local dimension of the fibre of a morphism of schemes through a point of its source
only depends on that point. The statement cannot be obtained by rewriting, because the point of
the fibre named by a point of the source depends on the base point. -/
private theorem topologicalKrullDimAt_fiber_congr {X Y : Scheme.{u}} (f : X ⟶ Y) {x x' : X}
    (h : x = x') :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      topologicalKrullDimAt (f.fiber (f x')) (f.asFiber x') := by
  cases h
  rfl


/-- A morphism of schemes locally of finite type whose fibres have local dimension `d` at
every point of its source has relative dimension `d` in the sense of part (3) of Tag 02NJ: a
scheme locally of finite type over a field with constant local dimension `d` is
equidimensional, and its dimension is the supremum of its local dimensions. -/
private theorem relativeDimension_of_forall_topologicalKrullDimAt_fiber_eq {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] {d : ℕ}
    (hd : ∀ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (d : WithBot ℕ∞)) :
    RelativeDimension f d := by
  intro s hs
  have _ : LocallyOfFiniteType (f.fiberToSpecResidueField s) := by
    show LocallyOfFiniteType (pullback.snd f (Y.fromSpecResidueField s))
    infer_instance
  have _ : Nonempty (f.fiber s) := hs
  have hlocal : ∀ w : f.fiber s, topologicalKrullDimAt (f.fiber s) w = (d : WithBot ℕ∞) :=
    fun w ↦ (Scheme.Hom.topologicalKrullDimAt_fiber_fiberι f s w).symm.trans
      (hd (f.fiberι s w))
  refine ⟨equidimensional_of_topologicalKrullDimAt_eq (Y.residueField s) (f.fiber s)
    (f.fiberToSpecResidueField s) hlocal, ?_⟩
  have hloc : ∀ w : f.fiber s,
      TopologicalSpace.localKrullDim (f.fiber s) w = (d : WithBot ℕ∞) := fun w ↦ by
    simpa only [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim] using hlocal w
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  simp [hloc]

namespace Space

/-! ### Transcendence degree through a locally quasi-finite morphism of algebraic spaces -/

/-- The residue-field transcendence degree holds on every étale chart at a point if and only if
it holds on one given chart. -/
private theorem holdsOnEveryEtaleChartAtPoint_hasResidueFieldTranscendenceDegree_iff
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (r : ℕ∞)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G} {x : points B S hS F}
    (c : EtaleChartAtPoint B S hS f x) :
    HoldsOnEveryEtaleChartAtPoint B S hS
      (@MorphismOfGerms.HasResidueFieldTranscendenceDegree.{u} r) f x ↔
    MorphismOfGerms.HasResidueFieldTranscendenceDegree r
      (MorphismOfGerms.ofSchemeHom ((BigFppfOver.toScheme B S hS).map c.h)
        (c.sourcePoint B S hS)) :=
  holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS _
    (MorphismOfGerms.residueFieldTranscendenceDegree_isEtaleLocalOnSourceAndTarget r) f x c

/-- **Stacks 06RX.** Let `X ⟶ Y ⟶ Z` be morphisms of algebraic spaces over `S` with `X ⟶ Y`
locally quasi-finite, and let `x` be a point of `X`. The transcendence degree of `x` over its
image in `Z` is the transcendence degree of the image of `x` in `Y` over that same point: on
compatible étale charts the first morphism becomes a locally quasi-finite morphism of schemes,
which contributes a finite residue-field extension and so no transcendence degree. -/
@[stacks 06RX]
theorem hasTranscendenceDegreeAt_comp_iff_of_isLocallyQuasiFinite
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsLocallyQuasiFinite B S hS f) (x : points B S hS X) (r : ℕ∞) :
    HasTranscendenceDegreeAt B S hS (f ≫ g) x r ↔
      HasTranscendenceDegreeAt B S hS g (pointsMap B S hS X f x) r := by
  classical
  obtain ⟨U, V, W, a, b, c, α, β, u, v, w, _haSurj, haEt, _hbSurj, hbEt, _hcSurj, _hcEt,
    hcommF, _hcommG, _hau, hαu, _hβv, _hvb, _hwc, _hdF, _hdG, _hdC, _htrF, htrG, htrComp⟩ :=
    exists_compatible_etale_charts_comp B S hS hX hY hZ f g x
  rw [htrComp r, htrG r]
  clear _htrF htrG htrComp _hdF _hdG _hdC
  obtain ⟨p, rfl⟩ := Quot.exists_rep u
  subst hαu
  set T := BigFppfOver.toScheme B S hS
  let pV := FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map α) p
  let t : Spec (.of p.carrier) := IsLocalRing.closedPoint p.carrier
  let c₁ := etaleChartAtPointOfId B S hS U W (α ≫ β) p t
  let c₂ := etaleChartAtPointOfId B S hS V W β pV t
  show HoldsOnEveryEtaleChartAtPoint B S hS
      (@MorphismOfGerms.HasResidueFieldTranscendenceDegree.{u} r) (yoneda.map (α ≫ β))
      (p.class B S hS (yoneda.obj U)) ↔
    HoldsOnEveryEtaleChartAtPoint B S hS
      (@MorphismOfGerms.HasResidueFieldTranscendenceDegree.{u} r) (yoneda.map β)
      (pV.class B S hS (yoneda.obj V))
  rw [holdsOnEveryEtaleChartAtPoint_hasResidueFieldTranscendenceDegree_iff B S hS r c₁,
    holdsOnEveryEtaleChartAtPoint_hasResidueFieldTranscendenceDegree_iff B S hS r c₂]
  have hlqf : LocallyQuasiFinite (T.map α) := (hf U V a b α haEt hbEt hcommF).2
  have hy : (T.map α) ((T.map p.value) t) = (T.map pV.value) t := by
    show (T.map α) ((T.map p.value) t) = (T.map (p.value ≫ α)) t
    rw [Functor.map_comp]
    rfl
  exact MorphismOfGerms.hasResidueFieldTranscendenceDegree_comp_iff_of_locallyQuasiFinite r
    (T.map (α ≫ β)) (T.map α) (T.map β) (T.map_comp α β) _ _ hy

/-! ### Transcendence degree at a finite type point over a Jacobson algebraic space -/

/-- **Stacks 0ECY.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is
locally of finite type, with `Y` Jacobson. Then the transcendence degree of a finite type
point `x` of `X` over its image is zero.

The Jacobson hypothesis is the étale-local property of Tag 03E6 for `JacobsonSpace`, written
out as one surjective étale atlas by a Jacobson scheme. -/
@[stacks 0ECY]
theorem hasTranscendenceDegreeAt_zero_of_isFiniteTypePoint
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (hJac : ∃ (V : BigFppfOver B S hS) (b : yoneda.obj V ⟶ Y),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) b ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) b ∧
      JacobsonSpace ((BigFppfOver.toScheme B S hS).obj V))
    (x : points B S hS X) (hx : IsFiniteTypePoint B S hS X x) :
    HasTranscendenceDegreeAt B S hS f x 0 := by
  classical
  obtain ⟨V, b, hbSurjRel, hbEt, hVJac⟩ := hJac
  set T := BigFppfOver.toScheme B S hS
  let Xs : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Vs : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
  let fs : Xs ⟶ (⟨Y, hY⟩ : AlgebraicSpaces B S hS) := ObjectProperty.homMk f
  let gs : Vs ⟶ (⟨Y, hY⟩ : AlgebraicSpaces B S hS) := ObjectProperty.homMk b
  let Z := AlgebraicSpaces.fiberProduct B S hS fs gs
  let pX : Z ⟶ Xs := ObjectProperty.homMk (pullback.fst fs.hom gs.hom)
  let pV : Z ⟶ Vs := ObjectProperty.homMk (pullback.snd fs.hom gs.hom)
  have hsq := AlgebraicSpaces.isPullback_fiberProduct B S hS fs gs
  have hpSurj : IsSurjective B S hS pX.hom := isSurjective_of_isPullback B S hS hsq.flip
    ((presheafSurjective_iff_isSurjective_yoneda B S hS Y hY V b).mp hbSurjRel)
  have hpEt : IsEtale B S hS pX.hom :=
    isEtale_of_isPullback B S hS pV pX gs fs hsq.flip
      (isEtale_of_presheaf_etale B S hS hbEt)
  obtain ⟨z, hzft, hzmap⟩ : x ∈ pointsMap B S hS Z.1 pX.hom '' finiteTypePoints B S hS Z.1 := by
    rwa [image_finiteTypePoints_eq B S hS pX.hom Z.property hX
      (isLocallyOfFiniteType_of_isEtale B S hS hX hpEt) hpSurj]
  obtain ⟨U, a, p, haEt, huClosed, hza⟩ :=
    (isFiniteTypePoint_iff_exists_isClosed_etaleChart B S hS Z.1 Z.property z).mp hzft
  let aX : yoneda.obj U ⟶ X := a ≫ pX.hom
  let h : U ⟶ V := yoneda.preimage (a ≫ pV.hom)
  have hsqcond : pX.hom ≫ f = pV.hom ≫ b := pullback.condition
  have hcomm : yoneda.map h ≫ b = aX ≫ f := by
    simp only [h, aX, Functor.map_preimage, Category.assoc, hsqcond]
  have haXEt : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf aX :=
    presheaf_etale_of_isEtale B S hS (isEtale_comp B S hS haEt hpEt)
  have _ : LocallyOfFiniteType (T.map h) := hf U V aX b h haXEt hbEt hcomm
  let c : EtaleChartAtPoint B S hS f x :=
    { U := U
      V := V
      a := aX
      b := b
      h := h
      a_etale := haXEt
      b_etale := hbEt
      comm := hcomm
      representative := p
      point := IsLocalRing.closedPoint p.carrier
      maps_to := by
        have hstep : pointsMap B S hS (yoneda.obj U) aX (p.class B S hS (yoneda.obj U)) =
            pointsMap B S hS Z.1 pX.hom
              (pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U))) := by
          rw [show aX = a ≫ pX.hom from rfl, pointsMap_comp]
          rfl
        rw [hstep, hza, hzmap] }
  refine (holdsOnEveryEtaleChartAtPoint_hasResidueFieldTranscendenceDegree_iff B S hS 0 c).mpr ?_
  have h4 := ((jacobsonSpace_finiteTypePoints_tfae (T.obj V)).out 1 4).mp hVJac
  exact MorphismOfGerms.hasResidueFieldTranscendenceDegree_zero_of_finite (T.map h)
    (schemePoint B S hS U p) (h4 (T.obj U) (T.map h) (schemePoint B S hS U p) huClosed).2

/-! ### The dimension formula for a flat morphism of relative dimension `d` -/

/-- **Stacks 0AFH.** Let `f : X ⟶ Y` be a morphism of locally Noetherian algebraic spaces over
`S` which is flat, locally of finite type and of relative dimension `d`. Then for every point
`x` of `X` with image `y` in `Y` we have `dim_x(X) = dim_y(Y) + d`.

Local Noetherianity of an algebraic space is the étale-local property of Tag 03E6 for
`AlgebraicGeometry.IsLocallyNoetherian`, as in
`StacksFrontier/AlgebraicGeometry/Spaces/NoetherianSpaces.lean`. The source is assumed locally
Noetherian, as in the statement of the tag, but the hypothesis is not used: by Tag 04ZK it
follows from local Noetherianity of the target and local finite type of `f`, which is how the
chart of the source is seen to be locally Noetherian below.

The proof reduces everything to one commuting square of surjective étale charts `α : U ⟶ V`
over `f`, obtained by Tag 02X1 from the locally Noetherian atlas of the target. The induced
morphism of schemes is flat and locally of finite type, being the chart morphism of a flat
morphism locally of finite type, and its source is locally Noetherian because its target is.
It has relative dimension `d` in the scheme sense of part (3) of Tag 02NJ: the pointed chart
built from the canonical field-valued representative of a point `w` of `U` reads the relative
dimension of `f` above `w` as the local dimension of the fibre of the chart morphism through
`w`, so that local dimension is `d` at every point of `U`, and constant local fibre dimension
over a field gives equidimensional fibres of dimension `d`. The dimension formula for the
chart morphism is then Tag 0AFE, and its two sides are the dimensions of the two algebraic
spaces at the corresponding points, by the chart independence of Tag 04N5. -/
@[stacks 0AFH]
theorem dimensionAtPoint_eq_add_of_hasRelativeDimension
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (_hNX : HasEtaleLocalProperty B S hS X (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (hNY : HasEtaleLocalProperty B S hS Y (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (f : X ⟶ Y) (hflat : IsFlat B S hS f) (hft : IsLocallyOfFiniteType B S hS f)
    {d : ℕ} (hdim : HasRelativeDimension d B S hS f) (x : points B S hS X) :
    dimensionAtPoint B S hS X hX x =
      dimensionAtPoint B S hS Y hY (pointsMap B S hS X f x) + (d : WithBot ℕ∞) := by
  classical
  set T := BigFppfOver.toScheme B S hS
  -- one commuting square of surjective étale charts over `f`, with locally Noetherian target
  obtain ⟨V, b, hbSurj, hbEtale, hVnoeth⟩ := hNY
  obtain ⟨U, a, α, hsq, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
  have _ : IsLocallyNoetherian (T.obj V) := hVnoeth
  have _ : LocallyOfFiniteType (T.map α) := hft U V a b α haEtale hbEtale hsq.symm
  have _ : IsLocallyNoetherian (T.obj U) :=
    LocallyOfFiniteType.isLocallyNoetherian (T.map α)
  have _ : _root_.AlgebraicGeometry.Flat (T.map α) :=
    hflat U V a b α haEtale hbEtale hsq.symm
  -- the chart morphism has relative dimension `d` in the scheme sense
  have hfibre : ∀ w : T.obj U, topologicalKrullDimAt ((T.map α).fiber ((T.map α) w))
      ((T.map α).asFiber w) = (d : WithBot ℕ∞) := by
    intro w
    set p := schemePointRepresentative B S hS U w
    let c : EtaleChartAtPoint B S hS f
        (pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U))) :=
      { U := U, V := V, a := a, b := b, h := α, a_etale := haEtale, b_etale := hbEtale
        comm := hsq.symm, representative := p
        point := IsLocalRing.closedPoint p.carrier, maps_to := rfl }
    exact (topologicalKrullDimAt_fiber_congr (T.map α)
      (schemePointRepresentative_point B S hS U w : c.sourcePoint B S hS = w)).symm.trans
      ((hasFiberDimensionAt_ofSchemeHom_iff (T.map α) (c.sourcePoint B S hS)
        (d : ℕ∞)).mp (hdim _ c))
  -- a field-valued representative of `x` on the chart, and its image on the target chart
  obtain ⟨z, hz⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U a).mp haSurj x
  obtain ⟨p, rfl⟩ := Quot.exists_rep z
  set pV := FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map α) p with hpV
  have hpVmaps : pointsMap B S hS (yoneda.obj V) b (pV.class B S hS (yoneda.obj V)) =
      pointsMap B S hS X f x := by
    rw [hpV, ← pointsMap_class, ← Function.comp_apply
      (f := pointsMap B S hS (yoneda.obj V) b), ← pointsMap_comp, ← hsq, pointsMap_comp,
      Function.comp_apply, hz]
  rw [dimensionAtPoint_eq_of_etale_chart B S hS X hX x U a haEtale p hz,
    dimensionAtPoint_eq_of_etale_chart B S hS Y hY _ V b hbEtale pV hpVmaps,
    hpV, schemePoint_map_yoneda B S hS α p]
  exact topologicalKrullDimAt_eq_add_of_relativeDimension (T.map α)
    (relativeDimension_of_forall_topologicalKrullDimAt_fiber_eq (T.map α) hfibre)
    (schemePoint B S hS U p)

end Space

end AlgebraicGeometry

end
