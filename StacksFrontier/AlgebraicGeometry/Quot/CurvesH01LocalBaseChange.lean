module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable

/-!
# The locus `κ = H⁰` of a family of curves, from local degree-zero base change

`AlgebraicGeometry.isOpenCurvesLocus_isH01CurveFamily_of` proves condition (o) of Stacks 0E0E for
`Curves^{h0,1}` (Stacks 0E6I) from two inputs: `hopen`, condition (o) for the fibrewise condition
`k = H⁰(X_k, 𝒪_{X_k})`, and `hpush`, Stacks 0E6B (a). This file reduces `hopen` to one statement
about a single family, local on its base: **local degree-zero cohomology and base change**,
`AlgebraicGeometry.CurveFamily.HasLocalH0BaseChange`. It says that if `k = H⁰(X_k, 𝒪_{X_k})` at
one field-valued point `Spec k ⟶ S`, then there is an open neighbourhood `Ω` of its point such
that `Γ(T, 𝒪_T) ⟶ Γ(X_T, 𝒪_{X_T})` is bijective for every morphism `T ⟶ S` of the site sending
the points of `T` into `Ω`. That is what the proof of Stacks 0E6B produces over an affine chart of
the base (for schemes it is the first half of
`Stacks.AlgebraicGeometry.ProperFlatStructureSheafSplitting.exists_away_patch`), and it contains
both the openness of the locus `κ(s) = H⁰(X_s, 𝒪_{X_s})` (Stacks 0E0R, part (2), at `i = 0`) and
the independence of that condition of the field over the point (Stacks 0E0R, part (1)).

## Main definitions

* `AlgebraicGeometry.CurveFamily.IsH0BijectiveAt`: `k = H⁰(X_k, 𝒪_{X_k})` at one field-valued
  point of the base.
* `AlgebraicGeometry.CurveFamily.HasLocalH0BaseChange`: local degree-zero cohomology and base
  change for one family.

## Main results

* `AlgebraicGeometry.CurveFamily.isH0BijectiveAt_iff_of_hom`: for a morphism of families
  `F ⟶ G`, the fibre of `F` over a field-valued point is the fibre of `G` over its image.
* `AlgebraicGeometry.CurveFamily.isH0BijectiveAt_of_class_eq`: under local base change, the
  condition at a field-valued point depends only on its point.
* `isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres_of_hasLocalH0BaseChange`: the
  input `hopen` of `isOpenCurvesLocus_isH01CurveFamily_of`, from local base change.
* `AlgebraicGeometry.isOpenCurvesLocus_isH01CurveFamily_of_hasLocalH0BaseChange`: condition (o)
  for `Curves^{h0,1}` from local base change and Stacks 0E6B (a).

## References

* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **`k = H⁰(X_k, 𝒪_{X_k})` at a field-valued point.** For a field-valued point `Spec k ⟶ S` of
the base of a family of curves `X ⟶ S`, pullback of global regular functions along the projection
`X ×_S Spec k ⟶ Spec k` is bijective. -/
def IsH0BijectiveAt (X : CurveFamily B hZ)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) : Prop :=
  Function.Bijective (Space.globalFunctionsMap B integerBase hZ
    (ObjectProperty.homMk (pullback.snd X.toBase.hom (schemeSpaceMap p.value).hom) :
      AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap p.value) ⟶
        schemeSpace p.siteObject))

/-- `HasBijectiveGlobalFunctionsOnFieldFibres` is `IsH0BijectiveAt` at every field-valued point. -/
theorem hasBijectiveGlobalFunctionsOnFieldFibres_iff_forall_isH0BijectiveAt
    (X : CurveFamily B hZ) :
    HasBijectiveGlobalFunctionsOnFieldFibres B hZ X ↔ ∀ p, IsH0BijectiveAt X p :=
  Iff.rfl

/-- **Local degree-zero cohomology and base change for a family of curves.** If
`k = H⁰(X_k, 𝒪_{X_k})` at a field-valued point `p : Spec k ⟶ S` of the base, there is an open
set `Ω` of points of `S` containing the point of `p` such that, for every morphism `t : T ⟶ S` of
the site whose map on points lands in `Ω`, pullback of global regular functions along the base
change `X ×_S T ⟶ T` is bijective. -/
def HasLocalH0BaseChange (X : CurveFamily B hZ) : Prop :=
  ∀ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj, IsH0BijectiveAt X p →
    ∃ Ω : Set (Space.points B integerBase hZ (schemeSpace X.base).obj),
      IsOpen Ω ∧ p.class B integerBase hZ _ ∈ Ω ∧
        ∀ (T : BigFppfOver B integerBase hZ) (t : T ⟶ X.base),
          Set.range (Space.pointsMap B integerBase hZ (schemeSpace T).obj
            (schemeSpaceMap t).hom) ⊆ Ω →
          Function.Bijective (Space.globalFunctionsMap B integerBase hZ
            (ObjectProperty.homMk (pullback.snd X.toBase.hom (schemeSpaceMap t).hom) :
              AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap t) ⟶
                schemeSpace T))

/-- **The fibre of a pulled-back family is the fibre of the original one.** For a morphism of
families of curves `a : F ⟶ G` and a field-valued point `p` of the base of `F`, `k = H⁰` holds for
the fibre of `F` over `p` exactly when it holds for the fibre of `G` over the image of `p`: the
first fibre is the second, the square of `a` being cartesian. -/
theorem isH0BijectiveAt_iff_of_hom {F G : CurveFamily B hZ} (a : F ⟶ G)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj) :
    IsH0BijectiveAt F p ↔
      IsH0BijectiveAt G (p.map B integerBase hZ _ (schemeSpaceMap a.baseMap).hom) := by
  suffices key : ∀ w : schemeSpace p.siteObject ⟶ schemeSpace G.base,
      w = schemeSpaceMap p.value ≫ schemeSpaceMap a.baseMap →
      (IsH0BijectiveAt F p ↔ Function.Bijective (Space.globalFunctionsMap B integerBase hZ
        (ObjectProperty.homMk (pullback.snd G.toBase.hom w.hom) :
          AlgebraicSpaces.fiberProduct B integerBase hZ G.toBase w ⟶
            schemeSpace p.siteObject))) from
    key _ (schemeSpaceMap_comp p.value a.baseMap)
  rintro w rfl
  have sqG := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ G.toBase
    (schemeSpaceMap p.value ≫ schemeSpaceMap a.baseMap)
  have sq := (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ F.toBase
    (schemeSpaceMap p.value)).paste_horiz a.cartesian
  unfold IsH0BijectiveAt
  rw [← IsPullback.isoIsPullback_hom_snd _ _ sq sqG, Space.globalFunctionsMap_comp,
    RingHom.coe_comp]
  exact (Space.globalFunctionsMapEquiv B integerBase hZ
    (sq.isoIsPullback _ _ sqG)).bijective.of_comp_iff' _

/-- The map on points of a field-valued point `q : Spec k ⟶ S`, read as a morphism of algebraic
spaces, has the point of `q` as its only value: `Spec k` has one point. -/
theorem range_pointsMap_schemeSpaceMap_value_subset {X : CurveFamily B hZ}
    (q : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) :
    Set.range (Space.pointsMap B integerBase hZ (schemeSpace q.siteObject).obj
      (schemeSpaceMap q.value).hom) ⊆ {q.class B integerBase hZ _} := by
  have : Subsingleton ((BigFppfOver.toScheme B integerBase hZ).obj q.siteObject) :=
    inferInstanceAs (Subsingleton (Spec (.of q.carrier)))
  let τ : Space.FieldValuedPoint B integerBase hZ (schemeSpace q.siteObject).obj :=
    { carrier := q.carrier
      contained := q.contained
      toBase := q.toBase
      value := 𝟙 q.siteObject }
  rintro _ ⟨x, rfl⟩
  have hx : x = τ.class B integerBase hZ _ :=
    (Space.pointsEquivScheme B integerBase hZ q.siteObject).injective (Subsingleton.elim _ _)
  have hτ : τ.map B integerBase hZ _ (schemeSpaceMap q.value).hom = q := by
    rcases q with ⟨k, hk, b, v⟩
    exact congrArg (Space.FieldValuedPoint.mk _ _ _)
      (Category.id_comp (show (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hZ) : BigFppfOver B integerBase hZ) ⟶
        X.base from v))
  rw [hx, Space.pointsMap_class]
  exact Set.mem_singleton_iff.2 (congrArg (Space.FieldValuedPoint.class B integerBase hZ _) hτ)

/-- **Under local base change, `k = H⁰` at a field-valued point depends only on its point.** -/
theorem isH0BijectiveAt_of_class_eq {X : CurveFamily B hZ} (hX : X.HasLocalH0BaseChange)
    {p q : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj}
    (hpq : p.class B integerBase hZ _ = q.class B integerBase hZ _)
    (hp : IsH0BijectiveAt X p) : IsH0BijectiveAt X q := by
  obtain ⟨Ω, -, hpΩ, hΩ⟩ := hX p hp
  exact hΩ q.siteObject q.value ((range_pointsMap_schemeSpaceMap_value_subset q).trans
    (Set.singleton_subset_iff.2 (hpq ▸ hpΩ)))

end CurveFamily

/-- **The input `hopen` of `isOpenCurvesLocus_isH01CurveFamily_of`, from local degree-zero base
change.** If every family of curves has local degree-zero cohomology and base change, the
fibrewise condition `k = H⁰(X_k, 𝒪_{X_k})` satisfies condition (o) of Stacks 0E0E: the open of
the base of a family `G` is the set of points at which `k = H⁰` holds for one, equivalently every,
field-valued representative. -/
theorem isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres_of_hasLocalH0BaseChange
    {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
    (h : ∀ G : CurveFamily B hZ, G.HasLocalH0BaseChange) :
    IsOpenCurvesLocus B hZ (CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ) := by
  refine IsOpenCurvesLocus.of_points fun G => ?_
  refine ⟨{s | ∃ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace G.base).obj,
      p.class B integerBase hZ _ = s ∧ G.IsH0BijectiveAt p}, ?_, fun F a => ?_⟩
  · refine isOpen_iff_forall_mem_open.2 ?_
    rintro _ ⟨p, rfl, hp⟩
    obtain ⟨Ω, hΩo, hpΩ, hΩ⟩ := h G p hp
    refine ⟨Ω, fun s hs => ?_, hΩo, hpΩ⟩
    obtain ⟨q, rfl⟩ := Quot.exists_rep s
    exact ⟨q, rfl, hΩ q.siteObject q.value
      ((CurveFamily.range_pointsMap_schemeSpaceMap_value_subset q).trans
        (Set.singleton_subset_iff.2 hs))⟩
  · constructor
    · rintro hF _ ⟨t, rfl⟩
      obtain ⟨p, rfl⟩ := Quot.exists_rep t
      exact ⟨_, (Space.pointsMap_class B integerBase hZ _ _ p).symm,
        (CurveFamily.isH0BijectiveAt_iff_of_hom a p).1 (hF p)⟩
    · intro hΩ p
      obtain ⟨q, hq, hbq⟩ := hΩ ⟨p.class B integerBase hZ _, rfl⟩
      rw [Space.pointsMap_class] at hq
      exact (CurveFamily.isH0BijectiveAt_iff_of_hom a p).2
        (CurveFamily.isH0BijectiveAt_of_class_eq (h G) hq hbq)

/-- **Condition (o) of Stacks 0E0E for `Curves^{h0,1}` (Stacks 0E6I), from local degree-zero base
change and Stacks 0E6B (a).** The input `hloc` is local degree-zero cohomology and base change for
every family of curves, and `hpush` is part (a) of Stacks 0E6B for families of curves. -/
theorem isOpenCurvesLocus_isH01CurveFamily_of_hasLocalH0BaseChange
    {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
    (hloc : ∀ G : CurveFamily B hZ, G.HasLocalH0BaseChange)
    (hpush : ∀ X : CurveFamily B hZ, CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
      HasUniversallyBijectiveGlobalFunctions B hZ X) :
    IsOpenCurvesLocus B hZ (IsH01CurveFamily B hZ) :=
  isOpenCurvesLocus_isH01CurveFamily_of
    (isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres_of_hasLocalH0BaseChange hloc) hpush

end AlgebraicGeometry

end
