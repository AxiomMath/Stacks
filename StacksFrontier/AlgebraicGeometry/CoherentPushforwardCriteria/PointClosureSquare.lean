module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.BaseChange
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme

/-!
# The closure of a point across an open immersion

Let `j : U ⟶ X` be an open immersion of schemes and let `x` be a point of `U`. Write `W` for the
reduced closed subscheme of `U` supported on the closure of `{x}` and `Z` for the reduced closed
subscheme of `X` supported on the closure of `{j x}`. This file builds the commutative square
relating them,

```
W  ──j'──▶  Z
│           │
│           │
▼           ▼
U  ──j───▶  X
```

shows that the top arrow is again an open immersion, and records the resulting comparison of
iterated direct images, `j_* i_{W,*} ℱ ≅ i_{Z,*} j'_* ℱ`.

It also shows that the square is cartesian, and records the comparison in the inverse image
direction that cartesianness gives, `j^* i_{Z,*} 𝒪_Z ≅ i_{W,*} 𝒪_W`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.pushforwardPointClosureIso` is the comparison of the two
  iterated direct images around the square of point closures, applied to the structure sheaf
  of `W`.
* `AlgebraicGeometry.Scheme.Modules.pullbackPointClosureIso` is the comparison in the inverse
  image direction: the restriction to `U` of `i_{Z,*} 𝒪_Z` is `i_{W,*} 𝒪_W`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.exists_isOpenImmersion_pointClosure`: the square
  exists and its top arrow is an open immersion.
* `AlgebraicGeometry.Scheme.IdealSheafData.isOpenImmersion_of_comp_subschemeι_eq`: the square
  determines its top arrow, so *every* morphism of point closures making it commute is an open
  immersion.
* `AlgebraicGeometry.Scheme.IdealSheafData.range_of_pointClosureSquare`: the square is
  cartesian, that is `W` is exactly the part of `Z` lying over `U`.

## Implementation notes

The closures carry their reduced induced closed subscheme structures, represented by the
vanishing ideal sheaves of the point closures. The top arrow is obtained from
`Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support`: `W` is reduced and its
image in `X` lies in the closure of `{j x}`, so the composite `W ⟶ U ⟶ X` factors through `Z`.

That `j'` is an open immersion is proved by identifying it with the inclusion of the open
subscheme `V = i_Z ⁻¹ᵁ j.opensRange` of `Z`. Both `W` and `V` are reduced schemes mapping to `X`
with the same image, so each factors through the other by the same factorization criterion, and
the two composites are the identity because `i_W` and `V.ι ≫ i_Z` are monomorphisms. This route
avoids computing stalk maps.

`pushforwardPointClosureIso` is an application of the general square comparison
`Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso` rather than the same composite
written out here. That matters for elaboration cost as well as for duplication: assembled
directly at the point-closure square, every implicit argument of the composite is one of the
large `vanishingIdeal` terms, which makes a direct construction ask for a raised heartbeat
budget. With the schemes abstracted into variables, as the general lemma has them, it
elaborates at once.

`pullbackPointClosureIso` is assembled the same way, through the general open base-change
isomorphism `pullbackPushforwardUnitIsoOfCartesian` for a cartesian square whose vertical arrows
are the one open immersion `V.ι`: cartesianness identifies `W` with the open subscheme
`i_Z ⁻¹ᵁ V` of `Z`, and the restriction to `V` of a direct image along `i_Z` is the direct image
along `i_Z ∣_ V` of the restriction to `i_Z ⁻¹ᵁ V`, which is
`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`.

## References

* [Stacks Project, Tag 0BK2](https://stacks.math.columbia.edu/tag/0BK2)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Along an open immersion the closure of a point is computed by preimage: the preimage of the
closure of `{j x}` is the closure of `{x}`. -/
private theorem preimage_closure_singleton {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (x : U) : j.base ⁻¹' closure ({j x} : Set X) = closure ({x} : Set U) := by
  rw [j.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage j.continuous]
  congr 1
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact j.isOpenEmbedding.injective.eq_iff

namespace Scheme.IdealSheafData

/-- A point of the closure of `{x}` lies in the support of the vanishing ideal of that closure. -/
private theorem mem_support_vanishingIdeal_closure {X : Scheme.{u}} {x y : X}
    (h : y ∈ closure ({x} : Set X)) :
    y ∈ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).support := by
  rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  simpa using h

/-- Commuting squares of schemes commute on underlying points. -/
private theorem base_apply_eq_of_comp_eq {A B C D : Scheme.{u}} {f : A ⟶ B} {g : B ⟶ D}
    {h : A ⟶ C} {k : C ⟶ D} (hc : f ≫ g = h ≫ k) (a : A) :
    g.base (f.base a) = k.base (h.base a) := by
  simpa using congrArg (fun f => f.base a) hc

/-- **Stacks Project, Tag 0BK2.** For an open immersion `j : U ⟶ X` and a point `x` of `U`, the
reduced closure of `{x}` in `U` is an open subscheme of the reduced closure of `{j x}` in `X`,
compatibly with the two closed immersions: there is an open immersion `j'` making the square of
canonical inclusions commute. -/
@[stacks 0BK2 "commutative square of closures", ega "I 5.2.3" "special case"]
theorem exists_isOpenImmersion_pointClosure {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [IsLocallyNoetherian U] [IsLocallyNoetherian X] (x : U) :
    let W := (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set U))).subscheme
    let Z := (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set X))).subscheme
    ∃ j' : W ⟶ Z, IsOpenImmersion j' ∧
      j' ≫ (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subschemeι =
        (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set U))).subschemeι ≫ j := by
  set IW := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set U)) with hIW
  set IZ := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({j x} : Set X)) with hIZ
  have : IsReduced IW.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have : IsReduced IZ.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hrW : Set.range IW.subschemeι.base = closure ({x} : Set U) :=
    range_subschemeι_vanishingIdeal _
  have hrZ : Set.range IZ.subschemeι.base = closure ({j x} : Set X) :=
    range_subschemeι_vanishingIdeal _
  -- The composite `W ⟶ U ⟶ X` lands in the closure of `{j x}`, hence factors through `Z`.
  obtain ⟨j', hj'⟩ := (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support
      IZ (IW.subschemeι ≫ j)).2 (by
    rintro _ ⟨w, rfl⟩
    have hw : IW.subschemeι.base w ∈ closure ({x} : Set U) := hrW ▸ ⟨w, rfl⟩
    have h2 : j.base (IW.subschemeι.base w) ∈ closure ({j x} : Set X) := by
      simpa using (_root_.image_closure_subset_closure_image j.continuous) ⟨_, hw, rfl⟩
    exact mem_support_vanishingIdeal_closure h2)
  refine ⟨j', ?_, hj'⟩
  -- `V` is the part of `Z` lying over `U`; it is an open subscheme of `Z`, and reduced.
  set V : IZ.subscheme.Opens := IZ.subschemeι ⁻¹ᵁ j.opensRange
  have : IsReduced V.toScheme := isReduced_of_isOpenImmersion V.ι
  have hCrange : Set.range (V.ι ≫ IZ.subschemeι).base ⊆ Set.range j.base := by
    rintro _ ⟨v, rfl⟩
    exact v.2
  set g : V.toScheme ⟶ U := IsOpenImmersion.lift j (V.ι ≫ IZ.subschemeι) hCrange
  have hgfac : g ≫ j = V.ι ≫ IZ.subschemeι := IsOpenImmersion.lift_fac _ _ _
  -- The image of `V` in `U` lies in the closure of `{x}`, so `V` factors through `W`.
  have hDrange : Set.range g.base ⊆ (IW.support : Set U) := by
    rintro _ ⟨v, rfl⟩
    have h1 : j.base (g.base v) ∈ closure ({j x} : Set X) := by
      rw [base_apply_eq_of_comp_eq hgfac]
      exact hrZ ▸ ⟨V.ι.base v, rfl⟩
    exact mem_support_vanishingIdeal_closure (by rwa [← preimage_closure_singleton j x])
  obtain ⟨k, hk⟩ := (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support
    IW g).2 hDrange
  -- Conversely `j'` factors through `V`, because `i_Z ∘ j' = j ∘ i_W` lands in the range of `j`.
  have hFrange : Set.range j'.base ⊆ Set.range V.ι.base := by
    rintro _ ⟨w, rfl⟩
    rw [V.range_ι]
    show IZ.subschemeι.base (j'.base w) ∈ j.opensRange
    rw [base_apply_eq_of_comp_eq hj']
    exact ⟨_, rfl⟩
  set j'' : IW.subscheme ⟶ V.toScheme := IsOpenImmersion.lift V.ι j' hFrange
  have hj''fac : j'' ≫ V.ι = j' := IsOpenImmersion.lift_fac _ _ _
  -- `j''` and `k` are mutually inverse, by cancelling the monomorphisms `i_W` and `V.ι ≫ i_Z`.
  have hG1 : j'' ≫ k = 𝟙 IW.subscheme := by
    have hb : j'' ≫ g = IW.subschemeι := by
      apply (cancel_mono j).mp
      rw [Category.assoc, hgfac, ← Category.assoc, hj''fac, hj']
    apply (cancel_mono IW.subschemeι).mp
    rw [Category.assoc, hk, hb, Category.id_comp]
  have hG2 : k ≫ j'' = 𝟙 V.toScheme := by
    apply (cancel_mono (V.ι ≫ IZ.subschemeι)).mp
    rw [Category.id_comp, ← Category.assoc (k ≫ j'') V.ι, Category.assoc k j'' V.ι,
      hj''fac, Category.assoc, hj', ← Category.assoc, hk, hgfac]
  have : IsIso j'' := ⟨⟨k, hG1, hG2⟩⟩
  rw [← hj''fac]
  infer_instance

/-- Any morphism of point closures making the square commute is the open immersion of
`exists_isOpenImmersion_pointClosure`: the closed immersion it is composed with is a
monomorphism, so the square determines it. -/
theorem isOpenImmersion_of_comp_subschemeι_eq {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsLocallyNoetherian U] [IsLocallyNoetherian X] (x : U)
    (j' : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set U))).subscheme ⟶
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subscheme)
    (comm : j' ≫ (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subschemeι =
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set U))).subschemeι ≫ j) :
    IsOpenImmersion j' := by
  obtain ⟨j'', hj'', hcomm⟩ :=
    Scheme.IdealSheafData.exists_isOpenImmersion_pointClosure j x
  have hEq : j' = j'' := (cancel_mono (Scheme.IdealSheafData.vanishingIdeal
    (Closeds.closure ({j x} : Set X))).subschemeι).mp (comm.trans hcomm.symm)
  rw [hEq]
  exact hj''

/-- **Stacks Project, Tag 0BK2.** The square of point closures is cartesian: the reduced closure
of `{x}` in `U` is exactly the part of the reduced closure of `{j x}` in `X` lying over `U`. -/
@[stacks 0BK2 "cartesianness of the square of closures"]
theorem range_of_pointClosureSquare {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (x : U)
    (j' : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set U))).subscheme ⟶
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subscheme)
    (comm : j' ≫ (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subschemeι =
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set U))).subschemeι ≫ j) :
    Set.range j'.base = (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set X))).subschemeι.base ⁻¹' Set.range j.base := by
  have hrW : Set.range (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set U))).subschemeι.base = closure ({x} : Set U) :=
    range_subschemeι_vanishingIdeal _
  have hrZ : Set.range (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set X))).subschemeι.base = closure ({j x} : Set X) :=
    range_subschemeι_vanishingIdeal _
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, (base_apply_eq_of_comp_eq comm w).symm⟩
  · rintro ⟨u, hu⟩
    have huc : u ∈ closure ({x} : Set U) := by
      rw [← preimage_closure_singleton j x, Set.mem_preimage, hu]
      exact hrZ ▸ ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := hrW ▸ huc
    refine ⟨w, (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set X))).subschemeι.isClosedEmbedding.injective ?_⟩
    rw [base_apply_eq_of_comp_eq comm, hw, hu]

end Scheme.IdealSheafData

namespace Scheme.Modules

/-- **Stacks Project, Tag 0BK2.** The canonical comparison of the two iterated direct images of
the structure sheaf of the reduced closure of `{x}` around the commutative square of point
closures: pushing forward first to `U` and then to `X` agrees with pushing forward first to the
closure of `{j x}` and then to `X`. -/
@[stacks 0BK2 "direct-image comparison"]
noncomputable def pushforwardPointClosureIso {U X : Scheme.{u}} (j : U ⟶ X) (x : U)
    (j' : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set U))).subscheme ⟶
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subscheme)
    (comm : j' ≫ (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subschemeι =
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set U))).subschemeι ≫ j) :
    (Scheme.Modules.pushforward j).obj
      ((Scheme.Modules.pushforward
        (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set U))).subschemeι).obj
        (SheafOfModules.unit
          (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({x} : Set U))).subscheme.ringCatSheaf)) ≅
    (Scheme.Modules.pushforward
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subschemeι).obj
      ((Scheme.Modules.pushforward j').obj
        (SheafOfModules.unit
          (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({x} : Set U))).subscheme.ringCatSheaf)) :=
  (Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso comm.symm).app _

/-- Restriction along the inverse of an isomorphism of schemes is the direct image along the
isomorphism: restriction along `e.inv` is a retraction of the direct image along `e.inv`, which
is inverse to the direct image along `e.hom`. -/
noncomputable def restrictInvObjIsoPushforwardObj {Y Z : Scheme.{u}} (e : Y ≅ Z)
    (N : Y.Modules) :
    (Scheme.Modules.restrictFunctor e.inv).obj N ≅ (Scheme.Modules.pushforward e.hom).obj N :=
  have i₁ : (Scheme.Modules.pushforward e.inv).obj
      ((Scheme.Modules.pushforward e.hom).obj N) ≅ N :=
    (Scheme.Modules.pushforwardComp e.hom e.inv).app N ≪≫
      (Scheme.Modules.pushforwardCongr e.hom_inv_id).app N ≪≫
      (Scheme.Modules.pushforwardId Y).app N
  ((Scheme.Modules.restrictFunctor e.inv).mapIso i₁).symm ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso e.inv).app _

/-- The direct image of the structure sheaf along an isomorphism of schemes is the structure
sheaf of the target. -/
noncomputable def pushforwardObjUnitIsoOfIso {Y Z : Scheme.{u}} (e : Y ≅ Z) :
    (Scheme.Modules.pushforward e.hom).obj (SheafOfModules.unit.{u} Y.ringCatSheaf) ≅
      SheafOfModules.unit.{u} Z.ringCatSheaf :=
  (restrictInvObjIsoPushforwardObj e _).symm ≪≫ Scheme.Modules.restrictUnitIso e.inv

/-- **Open base change for a direct image of structure sheaves.** Let `f : Z ⟶ X` be a morphism,
`V : X.Opens`, and `j' : W ⟶ Z` an open immersion with range the preimage of `V`, sitting over
`g : W ⟶ V`. Then the restriction to `V` of `f_* 𝒪_Z` is `g_* 𝒪_W`. -/
noncomputable def pullbackPushforwardUnitIsoOfCartesian {X Z W : Scheme.{u}}
    (V : X.Opens) (f : Z ⟶ X) (g : W ⟶ V.toScheme) (j' : W ⟶ Z) [IsOpenImmersion j']
    (comm : j' ≫ f = g ≫ V.ι)
    (hr : Set.range j'.base = Set.range (f ⁻¹ᵁ V).ι.base) :
    (Scheme.Modules.pullback V.ι).obj
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit.{u} Z.ringCatSheaf)) ≅
      (Scheme.Modules.pushforward g).obj (SheafOfModules.unit.{u} W.ringCatSheaf) :=
  let e : W ≅ (f ⁻¹ᵁ V).toScheme := IsOpenImmersion.isoOfRangeEq j' _ hr
  have hfac : e.hom ≫ (f ∣_ V) = g := by
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
      IsOpenImmersion.isoOfRangeEq_hom_fac, comm]
  ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app _).symm ≪≫
    (Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso f V).app _ ≪≫
    (Scheme.Modules.pushforward (f ∣_ V)).mapIso (Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ V).ι) ≪≫
    (Scheme.Modules.pushforward (f ∣_ V)).mapIso (pushforwardObjUnitIsoOfIso e).symm ≪≫
    (Scheme.Modules.pushforwardComp e.hom (f ∣_ V)).app _ ≪≫
    (Scheme.Modules.pushforwardCongr hfac).app _

/-- **Stacks Project, Tag 0BK2.** The comparison of direct images of the structure sheaf of a
point closure in the inverse image direction: the restriction to the open subscheme `V` of the
direct image of `𝒪_Z` along the closure of `{V.ι x}` in `X` is the direct image of `𝒪_W` along
the closure of `{x}` in `V`. -/
@[stacks 0BK2 "inverse-image comparison"]
noncomputable def pullbackPointClosureIso {X : Scheme.{u}} [IsLocallyNoetherian X]
    (V : X.Opens) (x : V.toScheme)
    (j' : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set V.toScheme))).subscheme ⟶
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({V.ι.base x} : Set X))).subscheme)
    (comm : j' ≫ (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({V.ι.base x} : Set X))).subschemeι =
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set V.toScheme))).subschemeι ≫ V.ι) :
    (Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pushforward
        (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({V.ι.base x} : Set X))).subschemeι).obj
        (SheafOfModules.unit.{u} (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({V.ι.base x} : Set X))).subscheme.ringCatSheaf)) ≅
      (Scheme.Modules.pushforward (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set V.toScheme))).subschemeι).obj
        (SheafOfModules.unit.{u} (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set V.toScheme))).subscheme.ringCatSheaf) :=
  haveI : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
  haveI := Scheme.IdealSheafData.isOpenImmersion_of_comp_subschemeι_eq V.ι x j' comm
  pullbackPushforwardUnitIsoOfCartesian V _ _ j' comm (by
    rw [Scheme.IdealSheafData.range_of_pointClosureSquare V.ι x j' comm,
      Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    rfl)

end Scheme.Modules

end AlgebraicGeometry
