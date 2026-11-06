module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupsAtClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.GroupoidTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationUniqueLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology

/-!
# Base change along an étale morphism which is an isomorphism over a closed point

Let `f : V ⟶ X` be an étale morphism of algebraic spaces over a scheme `S` and let `T ⊆ X` be
a subfunctor, with point set `{x}`, which `f` carries isomorphically onto from its preimage:
this is the situation of an elementary étale neighbourhood `(V, v) ⟶ (X, x)` of a closed point,
`T` being the closed point `{x}` (Stacks 0BH9). For an algebraic space `a : A ⟶ X` over `X`
write `P = A ×_X V`. Then `P ⟶ A` is a bijection between the points of `P` over `x` and the
points of `A` over `x`, a closed point of `P` over `x` maps to a closed point of `A`, and the
reduced closed subspace of `A` on that point pulls back to the reduced closed subspace of `P` on
the point above it.

This is how the proof of Stacks 0BHF, and of its normalized variant Stacks 0BHL, moves a centre
of a blowing up of the base change `P` of `A` to a centre of a blowing up of `A` itself.

## Main results

* `AlgebraicGeometry.Space.pointsMap_fst_injOn_of_isIso_fromPreimage`: the first projection of
  `A ×_X V` is injective on the points over `T`.
* `AlgebraicGeometry.Space.isClosed_singleton_pointsMap_fst_of_isIso_fromPreimage`: a closed
  point of `A ×_X V` over `x` maps to a closed point of `A`.
* `AlgebraicGeometry.Space.preimageClosedSubspace_closedPointSubspace`: along an étale morphism
  with a single point above a closed point, the reduced closed subspace on that closed point
  pulls back to the reduced closed subspace on the point above it.

## References

* [Stacks Project, Tag 0BH9](https://stacks.math.columbia.edu/tag/0BH9)
* [Stacks Project, Tag 0BHF](https://stacks.math.columbia.edu/tag/0BHF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {V X A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_FibreOverClosedPoint :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_FibreOverClosedPoint
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- If `T.fromPreimage f` is an isomorphism, so is its base change along `a : A ⟶ X`: the
preimage of `T` in `A ×_X V` maps isomorphically onto the preimage of `T` in `A`. This is checked
on sections, where it is the bijectivity of `T.fromPreimage f` read through the fibre product. -/
theorem isIso_fromPreimage_fst_of_isIso_fromPreimage (f : V ⟶ X) (a : A ⟶ X)
    (T : Subfunctor X) (hT : IsIso (T.fromPreimage f)) :
    IsIso ((T.preimage a).fromPreimage (pullback.fst a f)) := by
  have hbij : ∀ U, Function.Bijective ((T.fromPreimage f).app U) := fun U =>
    (isIso_iff_bijective _).mp (inferInstanceAs (IsIso ((T.fromPreimage f).app U)))
  refine (NatTrans.isIso_iff_isIso_app _).mpr fun U => ?_
  have hcond : ∀ y : (pullback a f).obj U, a.app U ((pullback.fst a f).app U y) =
      f.app U ((pullback.snd a f).app U y) := fun y => by
    have h := ConcreteCategory.congr_hom (congr_app (pullback.condition (f := a) (g := f)) U) y
    simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using h
  refine (isIso_iff_bijective _).mpr ⟨fun y₁ y₂ hy => ?_, fun z => ?_⟩
  · have h₁ : (pullback.fst a f).app U y₁.1 = (pullback.fst a f).app U y₂.1 :=
      congrArg Subtype.val hy
    have hsnd : ∀ y : ((T.preimage a).preimage (pullback.fst a f)).obj U,
        f.app U ((pullback.snd a f).app U y.1) ∈ T.obj U := fun y => by
      rw [← hcond]
      exact y.2
    have h₂ : (pullback.snd a f).app U y₁.1 = (pullback.snd a f).app U y₂.1 := by
      have : (T.fromPreimage f).app U ⟨_, hsnd y₁⟩ = (T.fromPreimage f).app U ⟨_, hsnd y₂⟩ := by
        apply Subtype.ext
        show f.app U ((pullback.snd a f).app U y₁.1) = f.app U ((pullback.snd a f).app U y₂.1)
        rw [← hcond, ← hcond, h₁]
      exact congrArg Subtype.val ((hbij U).1 this)
    exact Subtype.ext (pullback_obj_ext a f U _ _ h₁ h₂)
  · obtain ⟨w, hw⟩ := (hbij U).2 ⟨a.app U z.1, z.2⟩
    have hw' : f.app U w.1 = a.app U z.1 := congrArg Subtype.val hw
    obtain ⟨y, hy₁, hy₂⟩ := exists_pullback_obj B S hS a f (A := U.unop) z.1 w.1 hw'.symm
    refine ⟨⟨y, ?_⟩, Subtype.ext hy₁⟩
    show a.app U ((pullback.fst a f).app U y) ∈ T.obj U
    rw [hy₁]
    exact z.2

/-- **The first projection of `A ×_X V` is injective on the points over `T`.** If
`T.fromPreimage f` is an isomorphism and `T` has the single point `x`, two points of `A ×_X V`
lying over `x` with the same image in `A` are equal. -/
theorem pointsMap_fst_injOn_of_isIso_fromPreimage (f : V ⟶ X) (a : A ⟶ X)
    (T : Subfunctor X) (hT : IsIso (T.fromPreimage f)) {x : points B S hS X}
    (hTx : Set.range (pointsMap B S hS T.toFunctor T.ι) = {x})
    {t t' : points B S hS (pullback a f)}
    (ht : pointsMap B S hS A a (pointsMap B S hS _ (pullback.fst a f) t) = x)
    (htt' : pointsMap B S hS _ (pullback.fst a f) t = pointsMap B S hS _ (pullback.fst a f) t') :
    t = t' := by
  set AT := T.preimage a
  set PT := AT.preimage (pullback.fst a f)
  have hiso := isIso_fromPreimage_fst_of_isIso_fromPreimage f a T hT
  have hrange : Set.range (pointsMap B S hS PT.toFunctor PT.ι) =
      pointsMap B S hS _ (pullback.fst a f) ⁻¹' (pointsMap B S hS A a ⁻¹' {x}) := by
    have h1 := subspacePointSet_preimage B S hS (pullback.fst a f) AT
    have h2 := subspacePointSet_preimage B S hS a T
    simp only [subspacePointSet] at h1 h2
    rw [h1, h2, hTx]
  have ht' : pointsMap B S hS A a (pointsMap B S hS _ (pullback.fst a f) t') = x := by
    rw [← htt', ht]
  obtain ⟨s, rfl⟩ : t ∈ Set.range (pointsMap B S hS PT.toFunctor PT.ι) := by
    rw [hrange]; exact ht
  obtain ⟨s', rfl⟩ : t' ∈ Set.range (pointsMap B S hS PT.toFunctor PT.ι) := by
    rw [hrange]; exact ht'
  have hcomp : PT.ι ≫ pullback.fst a f = AT.fromPreimage (pullback.fst a f) ≫ AT.ι :=
    (AT.fromPreimage_ι _).symm
  rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hcomp, pointsMap_comp_apply,
    pointsMap_comp_apply] at htt'
  have h1 := pointsMap_injective_of_mono B S hS AT.ι htt'
  have : Mono (AT.fromPreimage (pullback.fst a f)) := @IsIso.mono_of_iso _ _ _ _ _ hiso
  have h2 := pointsMap_injective_of_mono B S hS (AT.fromPreimage (pullback.fst a f)) h1
  rw [h2]

/-- The reduced closed subspace on a closed point has that point as its only point. -/
theorem range_pointsMap_ι_closedPointSubspace {A : AlgebraicSpaces B S hS}
    (a : points B S hS A.obj) (ha : IsClosed ({a} : Set (points B S hS A.obj))) :
    Set.range (pointsMap B S hS (closedPointSubspace B S hS a ha).1.toFunctor
      (closedPointSubspace B S hS a ha).1.ι) = {a} :=
  range_pointsMap_ι_reducedClosedSubspace B S hS A.obj A.property {a} ha

/-- **The reduced closed subspace on a closed point pulls back, along an étale morphism with a
single point above it, to the reduced closed subspace on that point.** The inverse image is a
closed subspace whose point set is the preimage `{t}` of `{a}`, and it is reduced, being étale
over a reduced space; the uniqueness half of Stacks 03IQ identifies it. -/
theorem preimageClosedSubspace_closedPointSubspace {T A : AlgebraicSpaces B S hS} (φ : T ⟶ A)
    (hφ : IsEtale B S hS φ.hom) {a : points B S hS A.obj}
    (ha : IsClosed ({a} : Set (points B S hS A.obj))) {t : points B S hS T.obj}
    (ht : IsClosed ({t} : Set (points B S hS T.obj)))
    (hfib : pointsMap B S hS T.obj φ.hom ⁻¹' {a} = {t}) :
    preimageClosedSubspace φ (closedPointSubspace B S hS a ha) =
      closedPointSubspace B S hS t ht := by
  set Z := closedPointSubspace B S hS a ha
  set W := (preimageClosedSubspace φ Z).1
  have hWc : IsClosedSubspace B S hS W := (preimageClosedSubspace φ Z).2
  have hZpts : Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) = {a} :=
    range_pointsMap_ι_closedPointSubspace a ha
  have hWz : Set.range (pointsMap B S hS W.toFunctor W.ι) = {t} := by
    have h := subspacePointSet_preimage B S hS φ.hom Z.1
    simp only [subspacePointSet] at h
    show Set.range (pointsMap B S hS (Z.1.preimage φ.hom).toFunctor
      (Z.1.preimage φ.hom).ι) = _
    rw [h, hZpts, hfib]
  have hsq : IsPullback (Z.1.fromPreimage φ.hom) W.ι Z.1.ι φ.hom :=
    Subfunctor.isPullback_fromPreimage Z.1 φ.hom
  have hZalg : IsAlgebraicSpace B S hS Z.1.toFunctor := Z.2.1
  have hWalg : IsAlgebraicSpace B S hS W.toFunctor := hWc.1
  have hsq' := isPullback_homMk B S hS T.property hZalg A.property hWalg hsq.flip
  have hfet : IsEtale B S hS (Z.1.fromPreimage φ.hom) :=
    isEtale_of_isPullback B S hS _ _ _ _ hsq' hφ
  have hWr : HasEtaleLocalProperty B S hS W.toFunctor (fun Y : Scheme.{u} => IsReduced Y) :=
    hasEtaleLocalProperty_of_isEtale B S hS hWalg hZalg hfet
      (hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS A.obj A.property {a} ha)
  exact Subtype.ext (eq_closedPointSubspace B S hS t ht W hWc hWz hWr)

/-- **A closed point of `A ×_X V` over `x` maps to a closed point of `A`.** The complement of its
image is the union of the inverse image in `|A|` of `|X| ∖ {x}`, open because `x` is closed, and
of the image of the complement of the point, open because `A ×_X V ⟶ A` is étale; the two sets
agree because every point of `A` over `x` lifts to a point over the distinguished point of `V`
(Stacks 03H4) and the lift is unique by
`AlgebraicGeometry.Space.pointsMap_fst_injOn_of_isIso_fromPreimage`. -/
theorem isClosed_singleton_pointsMap_fst_of_isIso_fromPreimage (hV : IsAlgebraicSpace B S hS V)
    (hX : IsAlgebraicSpace B S hS X) (hA : IsAlgebraicSpace B S hS A) (f : V ⟶ X)
    (hf : IsEtale B S hS f) (a : A ⟶ X)
    (T : Subfunctor X) (hT : IsIso (T.fromPreimage f)) {x : points B S hS X}
    (hTx : Set.range (pointsMap B S hS T.toFunctor T.ι) = {x})
    (hx : IsClosed ({x} : Set (points B S hS X))) {t : points B S hS (pullback a f)}
    (ht : IsClosed ({t} : Set (points B S hS (pullback a f))))
    (htx : pointsMap B S hS A a (pointsMap B S hS _ (pullback.fst a f) t) = x) :
    IsClosed ({pointsMap B S hS _ (pullback.fst a f) t} : Set (points B S hS A)) := by
  have hP : IsAlgebraicSpace B S hS (pullback a f) := isAlgebraicSpace_pullback B S hS a f hA hV hX
  have hfst : IsEtale B S hS (pullback.fst a f) := isEtale_pullback_fst B S hS hA hX hV a f hf
  have hopen : IsOpenMap (pointsMap B S hS _ (pullback.fst a f)) :=
    isOpenMap_pointsMap_of_isEtale B S hS _ hP hA hfst
  have hcond : ∀ w : points B S hS (pullback a f),
      pointsMap B S hS A a (pointsMap B S hS _ (pullback.fst a f) w) =
        pointsMap B S hS V f (pointsMap B S hS _ (pullback.snd a f) w) := by
    intro w
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, pullback.condition]
  have heq : ({pointsMap B S hS _ (pullback.fst a f) t} : Set (points B S hS A))ᶜ =
      pointsMap B S hS A a ⁻¹' {x}ᶜ ∪ pointsMap B S hS _ (pullback.fst a f) '' {t}ᶜ := by
    ext b
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_preimage,
      Set.mem_image]
    constructor
    · intro hb
      by_cases hbx : pointsMap B S hS A a b = x
      · right
        obtain ⟨w, hw₁, hw₂⟩ := exists_points_of_isPullback B S hS (IsPullback.of_hasPullback a f)
          b (pointsMap B S hS _ (pullback.snd a f) t) (by rw [hbx, ← htx, hcond])
        exact ⟨w, fun hwt => hb (by rw [← hw₁, hwt]), hw₁⟩
      · exact Or.inl hbx
    · rintro (hb | ⟨w, hwt, rfl⟩)
      · intro hbt
        exact hb (by rw [hbt, htx])
      · intro hwt'
        exact hwt (pointsMap_fst_injOn_of_isIso_fromPreimage f a T hT hTx htx hwt'.symm).symm
  rw [← isOpen_compl_iff, heq]
  exact ((hx.isOpen_compl).preimage (continuous_pointsMap B S hS a)).union
    (hopen _ ht.isOpen_compl)

end AlgebraicGeometry.Space
