module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.FieldValued
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact

/-!
# Comparing the covering families of algebraic spaces: fppf coverings are fpqc coverings

An fppf covering of algebraic spaces over `S` is flat and locally of finite presentation with
jointly surjective maps on points (**Stacks 03Y8**), while an fpqc covering asks every affine
scheme-valued point of the target to admit a *finite affine* fpqc refinement factoring through
the family (**Stacks 03MQ**). This module proves that the first condition implies the second,
which is the comparison **Stacks 0DFQ** makes, and repackages it as the inequality

`AlgebraicGeometry.Space.Topology.fppf.precoverage ≤`
`AlgebraicGeometry.Space.Topology.fpqc.precoverage`

of the two precoverages of **Stacks 03YH**. That inequality is what lets a property of
morphisms of algebraic spaces known to be local at the target for the fpqc precoverage be used
at the fppf precoverage, where the relative properties of representable 1-morphisms of
algebraic stacks (**Stacks 03YK**) are stated.

The argument is the one of the source. Fix an affine `T` over the target `F` and form the fibre
products `P i = T ×_F X i`, which are algebraic spaces whose first projections again form an
fppf covering, of `T` this time. Each `P i` has a surjective étale chart `U i` by a scheme, and
the composites `U i → T` are flat and locally of finite presentation because they are étale
charts of the projections. Joint surjectivity on points transports to surjectivity of the
underlying scheme maps: a point `x` of `T` is the image of a field-valued point whose class is
hit by some `P i`, hence by some `U i`, and two field-valued points of a *scheme* with a common
extension have the same underlying point (**Stacks 01J9**). So the family `U i → T` is an fppf
covering of the affine scheme `T`, hence an fpqc covering, hence quasi-compact; refining it by
finitely many affine opens of the `U i` that still cover `T` gives the required finite affine
family, and each member factors through the corresponding `X i` through its chart of `P i`.

Two side results are proved on the way because the source argument needs them and the library
does not have them: the base change of an fppf covering is an fppf covering (**Stacks 03Y9**),
and being locally of finite presentation is stable under base change (**Stacks 03XR**), the
latter being the instance of **Stacks 0AMM** at that property.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_isStableUnderBaseChange`:
  **Stacks 03XR**, the case of being locally of finite presentation.
* `AlgebraicGeometry.Space.isFppfCovering_fibreProduct`: **Stacks 03Y9**, base change.
* `AlgebraicGeometry.Space.isFppfCovering_comp`: **Stacks 03Y9**, composition.
* `AlgebraicGeometry.Space.isFpqcCovering_of_isFppfCovering`: **Stacks 0DFQ** for fppf
  coverings.
* `AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`: the same comparison between the
  two precoverages of **Stacks 03YH**.
* `AlgebraicGeometry.Space.smooth_isLocalAtTarget_fppf`: **Stacks 0429** at the fppf
  precoverage, which is the form the relative properties of **Stacks 03YK** ask for.

## Implementation notes

`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage` is a plain theorem and not an
instance — it is an inequality of precoverages, not a class — and the fpqc-to-fppf transport it
enables is `CategoryTheory.MorphismProperty.IsLocalAtTarget.of_le`. Following the scheme-level
precedent of `AlgebraicGeometry.Scheme.fppfPrecoverage_le_fpqcPrecoverage`, which the folds of
Stacks 02X4 apply through a local `have` rather than globally, only one `IsLocalAtTarget`
instance is registered globally here: the smooth one, whose fpqc form
`AlgebraicGeometry.Space.smooth_isLocalAtTarget_fpqc` is already a global instance, so making
its fppf form global adds no new ambient commitment. Every other property should transport with
an explicit `.of_le` at the point of use.

`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_isStableUnderBaseChange` is additionally
registered as an instance, because the relative properties of Stacks 03YK need the base-change
stability of that property in scope already when their statements are elaborated.

The field-valued point of `T` used for surjectivity is built from the residue field at a point,
which must be shown to lie in the chosen big fppf site; that is a cardinality estimate on the
residue field against `AlgebraicGeometry.Scheme.size`, and it is the only place where the site's
cutoff is touched.

Both `AlgebraicGeometry.FieldValuedPoint` (of a scheme, Stacks 01J9) and
`AlgebraicGeometry.Space.FieldValuedPoint` (of a presheaf, Stacks 03BU) occur, and they are
different notions; inside `namespace AlgebraicGeometry.Space` the scheme-level one is therefore
written with its full name throughout.

## References

* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03XR](https://stacks.math.columbia.edu/tag/03XR)
* [Stacks Project, Tag 03Y8](https://stacks.math.columbia.edu/tag/03Y8)
* [Stacks Project, Tag 03Y9](https://stacks.math.columbia.edu/tag/03Y9)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 0429](https://stacks.math.columbia.edu/tag/0429)
* [Stacks Project, Tag 0DFQ](https://stacks.math.columbia.edu/tag/0DFQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v w

/-! ### Two side results: base change of the two fppf conditions -/

/-- **Stacks 03XR**, the case of being locally of finite presentation: that property of
morphisms of algebraic spaces over `S` is stable under base change.

Being locally of finite presentation is étale local on the source and target (Stacks 04R3) and
stable under base change, so this is the instance of Stacks 0AMM at that property. -/
@[stacks 03XR "locally of finite presentation"]
theorem isLocallyOfFinitePresentation_isStableUnderBaseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        IsLocallyOfFinitePresentation B S hS f.hom) :=
  holdsOnEveryEtaleChart_isStableUnderBaseChange B S hS
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget

attribute [instance] isLocallyOfFinitePresentation_isStableUnderBaseChange

/-- **Stacks 03Y9.** Pulling an fppf covering of algebraic spaces over `S` back along a
morphism of algebraic spaces gives an fppf covering of the new target: the first projections of
the fibre products of Stacks 02X2 form an fppf covering. -/
@[stacks 03Y9 "base_change_cover"]
theorem isFppfCovering_fibreProduct
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {X X' : AlgebraicSpaces B S hS}
    (Xi : I → AlgebraicSpaces B S hS)
    (f : ∀ i, Xi i ⟶ X) (g : X' ⟶ X)
    (hf : IsFppfCovering B S hS (fun i => (Xi i).1) (fun i => (f i).hom)) :
    IsFppfCovering B S hS
      (fun i => (AlgebraicSpaces.fiberProduct B S hS g (f i)).1)
      (fun i => pullback.fst g.hom (f i).hom) := by
  refine ⟨X'.property,
    (fun i => (AlgebraicSpaces.fiberProduct B S hS g (f i)).property), ?_, ?_, ?_⟩
  · intro i
    exact (isFlat_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS g (f i)).flip (hf.flat i)
  · intro i
    exact (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS g (f i)).flip
      (hf.locallyOfFinitePresentation i)
  · apply Set.eq_univ_of_forall
    intro x'
    have hcover : pointsMap B S hS X'.1 g.hom x' ∈
        ⋃ i, Set.range (fun y => pointsMap B S hS (Xi i).1 (f i).hom y) := by
      rw [hf.jointly_surjective]
      exact Set.mem_univ _
    rcases Set.mem_iUnion.mp hcover with ⟨i, y, hy⟩
    obtain ⟨w, hwp, _⟩ := exists_point_of_isPullback B S hS
      (AlgebraicSpaces.isPullback_fiberProduct B S hS g (f i)) x' y hy.symm
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr ⟨w, hwp⟩⟩

/-- **Stacks 03Y9.** Composing an fppf covering of an algebraic space over `S` with an fppf
covering of each of its members gives an fppf covering: flatness and being locally of finite
presentation are stable under composition (Stacks 03MN and 03XQ), and a point of the target is
hit by a member of the first covering, hence by a member of the covering of that member. -/
@[stacks 03Y9 "composition_cover"]
theorem isFppfCovering_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (I : Type v) (J : I → Type w)
    (Xᵢ : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (Xᵢⱼ : ∀ i, J i → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (f : ∀ i, Xᵢ i ⟶ X) (g : ∀ i j, Xᵢⱼ i j ⟶ Xᵢ i)
    (hf : IsFppfCovering B S hS Xᵢ f)
    (hg : ∀ i, IsFppfCovering B S hS (Xᵢⱼ i) (g i)) :
    IsFppfCovering B S hS (fun p : Σ i, J i => Xᵢⱼ p.1 p.2)
      (fun p => g p.1 p.2 ≫ f p.1) := by
  refine ⟨hf.target_isAlgebraicSpace,
    fun p => (hg p.1).source_isAlgebraicSpace p.2, fun p => ?_, fun p => ?_, ?_⟩
  · exact isFlat_comp B S hS ((hg p.1).source_isAlgebraicSpace p.2)
      (hf.source_isAlgebraicSpace p.1) hf.target_isAlgebraicSpace (g p.1 p.2) (f p.1)
      ((hg p.1).flat p.2) (hf.flat p.1)
  · exact isLocallyOfFinitePresentation_comp B S hS
      ((hg p.1).source_isAlgebraicSpace p.2) (hf.source_isAlgebraicSpace p.1)
      hf.target_isAlgebraicSpace (g p.1 p.2) (f p.1)
      ((hg p.1).locallyOfFinitePresentation p.2) (hf.locallyOfFinitePresentation p.1)
  · refine Set.eq_univ_iff_forall.mpr fun x => ?_
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hf.jointly_surjective x)
    obtain ⟨j, z, hz⟩ := Set.mem_iUnion.mp
      (Set.eq_univ_iff_forall.mp (hg i).jointly_surjective y)
    refine Set.mem_iUnion.mpr ⟨⟨i, j⟩, Set.mem_range.mpr ⟨z, ?_⟩⟩
    rw [pointsMap_comp B S hS (Xᵢⱼ i j) (g i j) (f i), Function.comp_apply, hz, hy]

/-! ### Residue fields of a scheme in the site -/

/-- The residue field at a point of a scheme has cardinality at most the scheme's size: it is a
quotient of the stalk at that point, whose cardinality is bounded by the size. -/
theorem residueField_size_le (X : Scheme.{u}) (x : X) :
    Cardinal.mk (X.residueField x) ≤ X.size :=
  (Cardinal.mk_le_of_surjective (X.residue_surjective x)).trans (Scheme.mk_stalk_le_size X x)

/-- The spectrum of the residue field at a point of a scheme contained in a big fppf site is
itself contained in that site. -/
theorem residueField_spec_contained (B : BigFppfSite.{u})
    {X : Scheme.{u}} (hX : B.Contains X) (x : X) :
    B.Contains (Spec (X.residueField x)) :=
  Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (X.residueField x) hX
    ((residueField_size_le X x).trans (Cardinal.self_le_power _ Cardinal.one_le_aleph0))

/-- The field-valued point of a *scheme* underlying a field-valued point of its presheaf of
points. -/
noncomputable def reprSchemePoint
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {U : BigFppfOver B S hS}
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    AlgebraicGeometry.FieldValuedPoint ((BigFppfOver.toScheme B S hS).obj U) where
  carrier := p.carrier
  map := p.value.left.hom

/-- Two field-valued points of a representable presheaf with a common extension have the same
underlying point of the representing scheme. -/
theorem reprSchemePoint_eq_of_commonExtension
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {U : BigFppfOver B S hS}
    {p q : FieldValuedPoint B S hS (yoneda.obj U)}
    (h : FieldValuedPoint.HasCommonExtension B S hS (yoneda.obj U) p q) :
    (reprSchemePoint p).point = (reprSchemePoint q).point := by
  rcases h with ⟨r, hp, hq⟩
  have key (s : FieldValuedPoint B S hS (yoneda.obj U))
      (h : FieldValuedPoint.Dominates B S hS (yoneda.obj U) r s) :
      (reprSchemePoint r).point = (reprSchemePoint s).point := by
    obtain ⟨f, hf⟩ := h
    have hf' : f ≫ s.value = r.value := by simpa using hf
    refine (AlgebraicGeometry.FieldValuedPoint.hasCommonExtension_iff_point_eq
      (reprSchemePoint r) (reprSchemePoint s)).mp
      ⟨reprSchemePoint r, ⟨𝟙 _, by simp⟩, f.left.hom, ?_⟩
    change f.left.hom ≫ s.value.left.hom = r.value.left.hom
    exact congrArg (fun k => k.left.hom) hf'
  exact (key p hp).symm.trans (key q hq)

/-! ### An fppf covering is an fpqc covering -/

/-- **Stacks 0DFQ**, the fppf case: an fppf covering of algebraic spaces over `S` is an fpqc
covering. -/
@[stacks 0DFQ "fppf coverings"]
theorem isFpqcCovering_of_isFppfCovering
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (f : ∀ i, X i ⟶ F)
    (hf : IsFppfCovering B S hS X f) :
    IsFpqcCovering B S hS f := by
  classical
  refine ⟨hf.flat, fun T h => ?_⟩
  let T₀ := (BigAffineFppf.toScheme B S hS).obj T
  let F₀ : AlgebraicSpaces B S hS := ⟨F, hf.target_isAlgebraicSpace⟩
  let X₀ : I → AlgebraicSpaces B S hS :=
    fun i => ⟨X i, hf.source_isAlgebraicSpace i⟩
  let f₀ : ∀ i, X₀ i ⟶ F₀ := fun i => ObjectProperty.homMk (f i)
  let Tobj := (BigAffineFppf.inclusion B S hS).obj T
  let T₁ : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj Tobj, isAlgebraicSpace_yoneda B S hS Tobj⟩
  let h₁ : T₁ ⟶ F₀ := ObjectProperty.homMk h
  let P : I → AlgebraicSpaces B S hS :=
    fun i => AlgebraicSpaces.fiberProduct B S hS h₁ (f₀ i)
  let pFst (i : I) : P i ⟶ T₁ :=
    ObjectProperty.homMk (pullback.fst h₁.hom (f₀ i).hom)
  let pSnd (i : I) : P i ⟶ X₀ i :=
    ObjectProperty.homMk (pullback.snd h₁.hom (f₀ i).hom)
  have hpullObj (i : I) : pFst i ≫ h₁ = pSnd i ≫ f₀ i :=
    (AlgebraicSpaces.isPullback_fiberProduct B S hS h₁ (f₀ i)).w
  have hpbFst (i : I) : (pFst i).hom = pullback.fst h (f i) := by
    change pullback.fst h₁.hom (f₀ i).hom = pullback.fst h (f i)
    simp [h₁, f₀]
  have hP : IsFppfCovering B S hS (fun i => (P i).1)
      (fun i => pullback.fst h (f i)) := by
    simpa [P, h₁, f₀, T₁, F₀, X₀] using
      isFppfCovering_fibreProduct B S hS X₀ f₀ h₁ hf
  choose U a haSurj haEtale using fun i => (P i).property.exists_atlas
  let qsite : ∀ i, U i ⟶ Tobj := fun i =>
    yoneda.preimage (a i ≫ pullback.fst h (f i))
  have hqmap (i : I) : yoneda.map (qsite i) = a i ≫ pullback.fst h (f i) := by simp [qsite]
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have hidEtale : Q.presheaf (𝟙 (yoneda.obj Tobj)) := by
    change yoneda.relativelyRepresentable (𝟙 (yoneda.obj Tobj)) ∧ _
    refine ⟨Functor.relativelyRepresentable.of_isIso yoneda (𝟙 _), ?_⟩
    intro A C g fst snd hpb
    have : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
    have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map _
    change Etale ((BigFppfOver.toScheme B S hS).map snd)
    exact inferInstance
  have hflat (i : I) : Flat ((BigFppfOver.toScheme B S hS).map (qsite i)) :=
    hP.flat i (U i) Tobj (a i) (𝟙 _) (qsite i) (haEtale i) hidEtale (by rw [hqmap]; simp)
  have hlfp (i : I) :
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (qsite i)) :=
    hP.locallyOfFinitePresentation i (U i) Tobj (a i) (𝟙 _) (qsite i)
      (haEtale i) hidEtale (by rw [hqmap]; simp)
  let Y : I → Scheme.{u} := fun i => (BigFppfOver.toScheme B S hS).obj (U i)
  let g : ∀ i, Y i ⟶ T₀ := fun i => (BigFppfOver.toScheme B S hS).map (qsite i)
  have hscheme : Presieve.ofArrows Y g ∈ Scheme.fppfPrecoverage T₀ := by
    rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨?_, fun i => ⟨hflat i, hlfp i⟩⟩
    intro x
    have hSpec : B.Contains (Spec (.of (T₀.residueField x))) :=
      B.residueField_spec_contains (by
        change B.Contains ((BigFppfOver.toScheme B S hS).obj Tobj)
        exact Tobj.left.property) x
    let π : B.inclusion.obj (B.obj hSpec) ⟶
        B.inclusion.obj ((BigFppfOver.forget B S hS).obj Tobj) :=
      T₀.fromSpecResidueField x
    let b : B.inclusion.obj (B.obj hSpec) ⟶ B.inclusion.obj (B.obj hS) := by
      change Spec (.of (T₀.residueField x)) ⟶ S
      exact π ≫ B.inclusion.map Tobj.hom
    let pt : FieldValuedPoint B S hS (yoneda.obj Tobj) := {
      carrier := T₀.residueField x
      contained := hSpec
      toBase := b
      value := Over.homMk (B.inclusion.preimage π) (by
        ext
        change (B.inclusion.map (B.inclusion.preimage π)) ≫
          B.inclusion.map Tobj.hom = π ≫ B.inclusion.map Tobj.hom
        rw [B.inclusion.map_preimage]) }
    have hpt : (reprSchemePoint pt).point = x := by
      change ((B.inclusion.map (B.inclusion.preimage π)).base)
        (IsLocalRing.closedPoint (T₀.residueField x)) = x
      rw [B.inclusion.map_preimage]
      exact Scheme.fromSpecResidueField_apply x _
    have hx := Set.eq_univ_iff_forall.mp hP.jointly_surjective
      (pt.class B S hS (yoneda.obj Tobj))
    rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
    rcases hi with ⟨p, hp⟩
    have haPoints :=
      (surjective_iff_surjective_pointsMap B S hS
        (P i).1 (P i).property (U i) (a i)).mp (haSurj i)
    obtain ⟨q, hq⟩ := haPoints p
    obtain ⟨r, rfl⟩ := Quot.exists_rep q
    let rclass := r.class B S hS (yoneda.obj (U i))
    let rT : FieldValuedPoint B S hS (yoneda.obj Tobj) :=
      FieldValuedPoint.map B S hS (yoneda.obj (U i)) (yoneda.map (qsite i)) r
    have hcomp : pointsMap B S hS (yoneda.obj (U i))
        (yoneda.map (qsite i)) rclass = pt.class B S hS (yoneda.obj Tobj) := by
      calc
        _ = pointsMap B S hS (P i).1 (pullback.fst h (f i))
              (pointsMap B S hS (yoneda.obj (U i)) (a i) rclass) := by
            rw [hqmap]
            exact Quot.inductionOn rclass fun _ => rfl
        _ = pt.class B S hS (yoneda.obj Tobj) := by rw [hq, hp]
    have hrT : rT.class B S hS (yoneda.obj Tobj) =
        pt.class B S hS (yoneda.obj Tobj) := by
      simpa [rT, rclass] using hcomp
    have hschemePt := reprSchemePoint_eq_of_commonExtension
      (FieldValuedPoint.class_eq_class_iff B S hS (yoneda.obj Tobj) rT pt |>.mp hrT)
    refine ⟨i, (reprSchemePoint r).point, ?_⟩
    change ((BigFppfOver.toScheme B S hS).map (qsite i))
      ((reprSchemePoint r).point) = x
    rw [← hpt, ← hschemePt]
    rfl
  have hfpqc := Scheme.fppfPrecoverage_le_fpqcPrecoverage T₀ hscheme
  let R : PreZeroHypercover T₀ := ⟨I, Y, g⟩
  have hqc : QuasiCompactCover R := by
    change Presieve.ofArrows Y g ∈ Scheme.fpqcPrecoverage T₀ at hfpqc
    change (Presieve.ofArrows Y g ∈ Scheme.qcPrecoverage T₀) ∧ _ at hfpqc
    exact (Scheme.presieve₀_mem_qcPrecoverage_iff).mp hfpqc.1
  have : IsAffine T₀ := BigAffineFppf.isAffine_toScheme_obj B S hS T
  have : CompactSpace T₀ := inferInstance
  obtain ⟨n, idx, V, hVaff, hVcover⟩ :=
    QuasiCompactCover.exists_isAffineOpen_of_isCompact R (isAffineOpen_top T₀).isCompact
  have hVk (k : Fin n) : B.Contains (Scheme.Opens.toScheme (V k)) :=
    (Scheme.size_coe_opens_le (Y (idx k)) (V k)).trans_lt (U (idx k)).left.property
  let openIncl (k : Fin n) : Scheme.Opens.toScheme (V k) ⟶ Y (idx k) := (V k).ι
  let openInclSite (k : Fin n) : B.obj (hVk k) ⟶ (U (idx k)).left :=
    B.inclusion.preimage (openIncl k)
  let Wsite (k : Fin n) : BigFppfOver B S hS :=
    Over.mk (openInclSite k ≫ (U (idx k)).hom)
  let Wobj (k : Fin n) : BigAffineFppf B S hS :=
    ⟨Wsite k, by
      change IsAffine (Scheme.Opens.toScheme (V k))
      exact hVaff k⟩
  let openMap (k : Fin n) : Wsite k ⟶ U (idx k) :=
    Over.homMk (openInclSite k) (by ext; simp [Wsite, openInclSite])
  let wmap (k : Fin n) : Wobj k ⟶ T :=
    ObjectProperty.homMk (openMap k ≫ qsite (idx k))
  have hwmapScheme (k : Fin n) :
      (BigAffineFppf.toScheme B S hS).map (wmap k) = openIncl k ≫ g (idx k) := by
    dsimp [wmap, openMap, g, BigFppfOver.toScheme]
    change B.inclusion.map (openInclSite k) ≫
        (BigFppfOver.toScheme B S hS).map (qsite (idx k)) =
      openIncl k ≫ (BigFppfOver.toScheme B S hS).map (qsite (idx k))
    rw [B.inclusion.map_preimage]
  let WI := ULift.{u + 1} (Fin n)
  let W : PreZeroHypercover.{u + 1} T :=
    ⟨WI, fun k => Wobj k.down, fun k => wmap k.down⟩
  have hWjoint (z : T₀) : ∃ k : WI,
      z ∈ Set.range ((BigAffineFppf.toScheme B S hS).map (wmap k.down)) := by
    have hcover' : (⋃ k, g (idx k) '' (V k : Set (Y (idx k)))) = Set.univ := by
      simpa [R, g] using hVcover
    have hz : z ∈ ⋃ k, g (idx k) '' (V k : Set (Y (idx k))) :=
      hcover'.symm ▸ Set.mem_univ z
    obtain ⟨k, y, hy, hzy⟩ := Set.mem_iUnion.mp hz
    refine ⟨⟨k⟩, ⟨⟨y, hy⟩, ?_⟩⟩
    rw [hwmapScheme]
    change (g (idx k)) ((openIncl k) ⟨y, hy⟩) = z
    simpa [openIncl] using hzy
  have hWflat (k : Fin n) :
      Flat ((BigAffineFppf.toScheme B S hS).map (wmap k)) := by
    rw [hwmapScheme]
    have : Flat (openIncl k) := inferInstance
    have : Flat (g (idx k)) := hflat (idx k)
    infer_instance
  have hWlfp (k : Fin n) :
      LocallyOfFinitePresentation ((BigAffineFppf.toScheme B S hS).map (wmap k)) := by
    rw [hwmapScheme]
    have : LocallyOfFinitePresentation (openIncl k) := inferInstance
    have : LocallyOfFinitePresentation (g (idx k)) := hlfp (idx k)
    infer_instance
  have hWfppf : Presieve.ofArrows
      (fun k : WI => (BigAffineFppf.toScheme B S hS).obj (Wobj k.down))
      (fun k : WI => (BigAffineFppf.toScheme B S hS).map (wmap k.down)) ∈
        Scheme.fppfPrecoverage T₀ := by
    rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨hWjoint, fun k => ⟨hWflat k.down, hWlfp k.down⟩⟩
  have hWfpqc : Presieve.map (BigAffineFppf.toScheme B S hS) W.presieve₀ ∈
      Scheme.fpqcPrecoverage T₀ := by
    simpa [W] using (Scheme.fppfPrecoverage_le_fpqcPrecoverage T₀) hWfppf
  refine ⟨W, inferInstance, hWfpqc, ?_⟩
  intro k
  let k' : Fin n := k.down
  let lift : yoneda.obj (Wsite k') ⟶ (P (idx k')).1 :=
    yoneda.map (openMap k') ≫ a (idx k')
  let c : yoneda.obj (Wsite k') ⟶ X (idx k') := lift ≫ (pSnd (idx k')).hom
  refine ⟨idx k', c, ?_⟩
  change c ≫ f (idx k') =
    yoneda.map ((BigAffineFppf.inclusion B S hS).map (wmap k')) ≫ h
  dsimp [c, lift, wmap]
  have hpull : (pFst (idx k')).hom ≫ h = (pSnd (idx k')).hom ≫ f (idx k') := by
    simpa [h₁, f₀] using congrArg (fun t => t.hom) (hpullObj (idx k'))
  calc
    _ = yoneda.map (openMap k') ≫
        (a (idx k') ≫ ((pSnd (idx k')).hom ≫ f (idx k'))) := by
          simp [Category.assoc]
    _ = yoneda.map (openMap k') ≫
        (a (idx k') ≫ ((pFst (idx k')).hom ≫ h)) := by rw [← hpull]
    _ = (yoneda.map (openMap k') ≫
        (a (idx k') ≫ pullback.fst h (f (idx k')))) ≫ h := by
          rw [hpbFst]
          cat_disch
    _ = yoneda.map (openMap k' ≫ qsite (idx k')) ≫ h := by
          rw [← hqmap, ← Functor.map_comp]

/-! ### The comparison of precoverages, and its first consumer -/

/-- Every fppf covering family of algebraic spaces over `S` is an fpqc covering family: the
fppf precoverage of Stacks 03YH is contained in the fpqc one. This is
`AlgebraicGeometry.Space.isFpqcCovering_of_isFppfCovering` read on the precoverages, and it is
what `CategoryTheory.MorphismProperty.IsLocalAtTarget.of_le` needs in order to carry locality at
the target from the fpqc precoverage, where it is proved, to the fppf precoverage, where the
relative properties of Stacks 03YK are stated. -/
theorem fppfPrecoverage_le_fpqcPrecoverage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Topology.fppf.precoverage.{u, v} B S hS ≤ Topology.fpqc.precoverage.{u, v} B S hS := by
  intro Y R hR
  obtain ⟨I, Yi, g, rfl, hg⟩ := hR
  exact ⟨I, Yi, g, rfl, hg.1, hg.2.1,
    isFpqcCovering_of_isFppfCovering B S hS
      (fun i => (Yi i).obj) (fun i => (g i).hom) hg.2.2⟩

/-- **Stacks 0429** at the fppf precoverage: smoothness of morphisms of algebraic spaces over
`S` is local at the target for the fppf topology. The fpqc form is
`AlgebraicGeometry.Space.smooth_isLocalAtTarget_fpqc`, and the two are compared by
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`. This is the form in which Stacks
03YK's relative properties ask for it. -/
@[stacks 0429 "the fppf precoverage"]
instance smooth_isLocalAtTarget_fppf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (smoothMorphismProperty B S hS).IsLocalAtTarget
      (Topology.fppf.precoverage.{u, v} B S hS) :=
  .of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)

end AlgebraicGeometry.Space

end
