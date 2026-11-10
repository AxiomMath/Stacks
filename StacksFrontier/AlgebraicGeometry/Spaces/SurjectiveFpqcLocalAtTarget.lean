module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Surjectivity of morphisms of algebraic spaces is fpqc local on the base (Stacks 041Q)

Surjectivity of a morphism of algebraic spaces over `S` is surjectivity of the induced map on
the point sets of Stacks 03BU. This file collects it as a `CategoryTheory.MorphismProperty` on
the category of algebraic spaces over `S`, proves it stable under composition (Stacks 03MG) and
local on the base for the fpqc topology (Stacks 041Q), and derives the fppf form that the
relative properties of Stacks 03YK ask for as an instance argument.

## Main definitions

* `AlgebraicGeometry.Space.surjectiveMorphismProperty`: surjectivity as a `MorphismProperty` on
  `AlgebraicGeometry.AlgebraicSpaces`, the companion of
  `AlgebraicGeometry.Space.smoothMorphismProperty`.

## Main results

* `AlgebraicGeometry.Space.isSurjective_comp`: **Stacks 03MG**.
* `AlgebraicGeometry.Space.isJointlySurjective_of_isFpqcCovering`: an fpqc covering is jointly
  surjective on points.
* `AlgebraicGeometry.Space.surjective_isLocalAtTarget_fpqc`: **Stacks 041Q**.
* `AlgebraicGeometry.Space.surjective_isLocalAtTarget_fppf`: the same at the fppf precoverage.

## Implementation notes

The fpqc locality is Stacks' own hint for 041Q: use Tag 03H4. One direction is exactly
`AlgebraicGeometry.Space.exists_point_of_isPullback` — a point of the target of a base change
and a point above its image amalgamate to a point of the fibre product — and the other needs a
point of the target to be lifted along the covering, which is `exists_point_of_fpqcCovering`
below.

That lifting is where the fpqc condition is used, and it is the only substantial argument here.
A point of `Y` is a class of field-valued points; a representative `p` has affine site object
`Spec κ`, so the fpqc condition applies to it and yields a *finite* affine family refining the
covering over `Spec κ`. Since `Spec κ` has a unique point, one member of that family already
carries a point above it, and the canonical field-valued point at its residue field
(`AlgebraicGeometry.Space.schemePointRepresentative`) maps into some `Yi i`; its image in `Y`
and `p` have a common extension, so they define the same point of `Y`.

The fppf form is `CategoryTheory.MorphismProperty.IsLocalAtTarget.of_le` against
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage` (Stacks 0DFQ), exactly as for
smoothness in Stacks 0429.

## References

* [Stacks Project, Tag 041Q](https://stacks.math.columbia.edu/tag/041Q)
* [Stacks Project, Tag 03MG](https://stacks.math.columbia.edu/tag/03MG)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 0DFQ](https://stacks.math.columbia.edu/tag/0DFQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Surjectivity of morphisms of algebraic spaces over `S` (**Stacks 03ME**), as a property of
morphisms of the category `AlgebraicGeometry.AlgebraicSpaces`. -/
abbrev surjectiveMorphismProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => IsSurjective B S hS f.hom

/-- A composite of morphisms surjective on points is surjective on points. -/
@[stacks 03MG]
theorem isSurjective_comp {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsSurjective B S hS f) (hg : IsSurjective B S hS g) :
    IsSurjective B S hS (f ≫ g) := by
  intro z
  obtain ⟨y, rfl⟩ := hg z
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨x, Quot.inductionOn x (fun _ => rfl)⟩

/-- Surjectivity of morphisms of algebraic spaces over `S` is stable under base change. -/
instance surjectiveMorphismProperty_isStableUnderBaseChange :
    (surjectiveMorphismProperty B S hS).IsStableUnderBaseChange :=
  ⟨fun sq ha => isSurjective_of_isPullback B S hS sq ha⟩

/-- Surjectivity of morphisms of algebraic spaces over `S` is stable under composition. -/
instance surjectiveMorphismProperty_isStableUnderComposition :
    (surjectiveMorphismProperty B S hS).IsStableUnderComposition :=
  ⟨fun _ _ ha hb => isSurjective_comp B S hS ha hb⟩

/-- An isomorphism of algebraic spaces is surjective on points. -/
private theorem pointsMap_surjective_of_iso {X Y : AlgebraicSpaces B S hS} (e : X ≅ Y) :
    Function.Surjective (pointsMap B S hS X.1 e.hom.hom) := by
  intro y
  refine ⟨pointsMap B S hS Y.1 e.inv.hom y, ?_⟩
  have he : e.inv.hom ≫ e.hom.hom = 𝟙 Y.1 := congrArg (fun k => k.hom) e.inv_hom_id
  change (pointsMap B S hS X.1 e.hom.hom ∘ pointsMap B S hS Y.1 e.inv.hom) y = y
  rw [← pointsMap_comp, he, pointsMap_id]
  rfl

/-- Surjectivity of morphisms of algebraic spaces over `S` is invariant under composition with
isomorphisms on either side. -/
instance surjectiveMorphismProperty_respectsIso :
    (surjectiveMorphismProperty B S hS).RespectsIso :=
  MorphismProperty.RespectsIso.mk _
    (fun {X Y Z} e f hf => by
      change Function.Surjective (pointsMap B S hS Y.1 f.hom) at hf
      change Function.Surjective (pointsMap B S hS X.1 (e.hom.hom ≫ f.hom))
      intro z
      obtain ⟨y, hy⟩ := hf z
      obtain ⟨x, hx⟩ := pointsMap_surjective_of_iso B S hS e y
      refine ⟨x, ?_⟩
      rw [pointsMap_comp]
      simp only [Function.comp_apply, hx, hy])
    (fun {X Y Z} e f hf => by
      change Function.Surjective (pointsMap B S hS X.1 f.hom) at hf
      change Function.Surjective (pointsMap B S hS X.1 (f ≫ e.hom).hom)
      intro z
      obtain ⟨y, hy⟩ := pointsMap_surjective_of_iso B S hS e z
      obtain ⟨x, hx⟩ := hf y
      refine ⟨x, ?_⟩
      rw [ObjectProperty.FullSubcategory.comp_hom, pointsMap_comp]
      simp only [Function.comp_apply, hx, hy])

/-- A point of the target of an fpqc covering of algebraic spaces is the image of a point of
one of its members. -/
private theorem exists_point_of_fpqcCovering
    {I : Type v} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Yi : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : ∀ i, Yi i ⟶ Y) (hc : IsFpqcCovering B S hS g) (y : points B S hS Y) :
    ∃ i, ∃ x : points B S hS (Yi i), pointsMap B S hS (Yi i) (g i) x = y := by
  classical
  induction y using Quot.inductionOn with
  | _ p =>
    let T : BigAffineFppf B S hS :=
      ⟨p.siteObject, inferInstanceAs (IsAffine (Spec (.of p.carrier)))⟩
    let η : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj T) ⟶ Y := yonedaEquiv.symm p.value
    obtain ⟨U, _, hfpqc, hfac⟩ := hc.2 T η
    let TS := (BigAffineFppf.toScheme B S hS).obj T
    have : Unique TS := by
      change Unique (Spec (.of p.carrier))
      infer_instance
    let xT : TS := default
    have hfamily : Presieve.ofArrows
        (fun i => (BigAffineFppf.toScheme B S hS).obj (U.X i))
        (fun i => (BigAffineFppf.toScheme B S hS).map (U.f i)) ∈
        Scheme.precoverage @Flat TS := by
      have hmap : Presieve.map (BigAffineFppf.toScheme B S hS) U.presieve₀ =
          Presieve.ofArrows
            (fun i => (BigAffineFppf.toScheme B S hS).obj (U.X i))
            (fun i => (BigAffineFppf.toScheme B S hS).map (U.f i)) := by
        simp [PreZeroHypercover.presieve₀]
      change Presieve.map (BigAffineFppf.toScheme B S hS) U.presieve₀ ∈
          Scheme.qcPrecoverage TS ∧
        Presieve.map (BigAffineFppf.toScheme B S hS) U.presieve₀ ∈
          Scheme.precoverage @Flat TS at hfpqc
      rw [hmap] at hfpqc
      exact hfpqc.2
    change Presieve.ofArrows
        (fun i => (BigAffineFppf.toScheme B S hS).obj (U.X i))
        (fun i => (BigAffineFppf.toScheme B S hS).map (U.f i)) ∈
          Scheme.jointlySurjectivePrecoverage TS ∧ _ at hfamily
    obtain ⟨j, z, hz⟩ :=
      (Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff
        Scheme.forget).mp hfamily.1 xT
    obtain ⟨i, a, hafac⟩ := hfac j
    let Wj := (BigAffineFppf.inclusion B S hS).obj (U.X j)
    let z' : (BigFppfOver.toScheme B S hS).obj Wj := z
    let qpt := schemePointRepresentative B S hS Wj z'
    let qmap : qpt.siteObject ⟶ Wj := qpt.value
    let xp : FieldValuedPoint B S hS (Yi i) :=
      { carrier := qpt.carrier
        field := qpt.field
        contained := qpt.contained
        toBase := qpt.toBase
        value := a.app (Opposite.op qpt.siteObject) qpt.value }
    let fpoint : FieldValuedPoint B S hS Y :=
      { carrier := qpt.carrier
        field := qpt.field
        contained := qpt.contained
        toBase := qpt.toBase
        value := (g i).app (Opposite.op qpt.siteObject)
          (a.app (Opposite.op qpt.siteObject) qpt.value) }
    have hqpt : qpt.value = yonedaEquiv (yoneda.map qmap) := rfl
    let k := qmap ≫ ((BigAffineFppf.inclusion B S hS).map (U.f j))
    refine ⟨i, xp.class B S hS (Yi i), ?_⟩
    rw [pointsMap_class]
    change fpoint.class B S hS Y = p.class B S hS Y
    apply FieldValuedPoint.class_eq_class_of_hasCommonExtension
    refine ⟨fpoint, FieldValuedPoint.dominates_refl B S hS Y fpoint, k, ?_⟩
    change Y.map k.op p.value = fpoint.value
    calc
      Y.map k.op p.value = Y.map k.op (yonedaEquiv η) := by simp [η]
      _ = yonedaEquiv (yoneda.map k ≫ η) := yonedaEquiv_naturality η k
      _ = η.app (Opposite.op qpt.siteObject) (yonedaEquiv (yoneda.map k)) :=
        yonedaEquiv_comp (yoneda.map k) η
      _ = fpoint.value := by
        change _ = (a ≫ g i).app (Opposite.op qpt.siteObject) qpt.value
        rw [hafac, hqpt]
        simp [k, Functor.map_comp, yonedaEquiv]

/-- **An fpqc covering of algebraic spaces is jointly surjective on points.**  The images of
the induced maps on the point sets of Stacks 03BU cover the points of the common target.

Joint surjectivity is not part of the definition of an fpqc covering of Stacks 03MQ, which asks
only for flatness of the members together with the refinement condition on affine objects; it is
a consequence, because a point of the target has an affine site object with a unique point, to
which the refinement condition applies. -/
theorem isJointlySurjective_of_isFpqcCovering
    {I : Type v} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Yi : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : ∀ i, Yi i ⟶ Y) (hc : IsFpqcCovering B S hS g) :
    IsJointlySurjective B S hS Yi g :=
  (isJointlySurjective_iff B S hS Yi g).2 (exists_point_of_fpqcCovering B S hS g hc)

/-- Surjectivity of morphisms of algebraic spaces over `S` is local on the base for the fpqc
topology. -/
@[stacks 041Q, sga "4 IV 8.5.5" "more general"]
instance surjective_isLocalAtTarget_fpqc :
    (surjectiveMorphismProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) := by
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff
    (P := surjectiveMorphismProperty B S hS)
    (K := Topology.precoverage.{u, v} .fpqc B S hS) ?_
  intro X Y f R hR
  refine ⟨fun hf _ g _ _ => MorphismProperty.pullback_snd f g hf, fun h => ?_⟩
  change Function.Surjective (pointsMap B S hS X.1 f.hom)
  obtain ⟨I, Yi, g, hR, -, -, hcover⟩ := hR
  intro y
  obtain ⟨i, yi, hyi⟩ := exists_point_of_fpqcCovering B S hS
    (fun i => (g i).hom) hcover y
  have hloc := h (g i) (by rw [hR]; exact ⟨i⟩)
  change Function.Surjective
    (pointsMap B S hS (pullback f (g i)).1 (pullback.snd f (g i)).hom) at hloc
  obtain ⟨w, hw⟩ := hloc yi
  have hsq : (pullback.fst f (g i)).hom ≫ f.hom =
      (pullback.snd f (g i)).hom ≫ (g i).hom := by
    simpa only [ObjectProperty.FullSubcategory.comp_hom] using
      congrArg (fun k => k.hom) (IsPullback.of_hasPullback f (g i)).w
  refine ⟨pointsMap B S hS (pullback f (g i)).1 (pullback.fst f (g i)).hom w, ?_⟩
  rw [pointsMap_apply_comm B S hS hsq, hw, hyi]

/-- **Stacks 041Q** at the fppf precoverage: surjectivity of morphisms of algebraic spaces over
`S` is local at the target for the fppf topology. This is the form in which the relative
properties of Stacks 03YK ask for it; the comparison of precoverages is Stacks 0DFQ,
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`. -/
@[stacks 041Q "the fppf precoverage"]
instance surjective_isLocalAtTarget_fppf :
    (surjectiveMorphismProperty B S hS).IsLocalAtTarget
      (Topology.fppf.precoverage.{u, v} B S hS) :=
  .of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)

end AlgebraicGeometry.Space

end
