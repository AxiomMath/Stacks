module

public import StacksFrontier.Deformation.Artin.Versality.DiagonalFibreDescent
public import StacksFrontier.Deformation.Artin.Versality.SetoidOpenness
public import StacksFrontier.Deformation.ArtinCriteria.BaseChangeRetraction

/-!
# Openness of versality from local retractions

Let `𝒳` be a category fibred in groupoids over the big fppf site of a locally Noetherian scheme
`S`, satisfying (RS*). Assume that a versal object retracts, over a neighbourhood of its versal
point, every first-order thickening of schemes locally of finite type through which it maps,
that objects over first-order thickenings of affine schemes of finite type descend to
first-order thickenings of finite type, and that towers of first-order thickenings are
effective in the weak sense that each member of the tower maps compatibly to one object over a
first-order thickening. Then versality specializes (Stacks 0G2K) and is open (Stacks 0CXU).

The proofs are those of the source; the local retraction is the step where the source uses the
algebraic space `Z = (Sch/U) ×_𝒳 (Sch/U')`, Stacks 0CXM and Stacks 04AM. For a category with
diagonal representable by algebraic spaces and locally of finite type satisfying (RS) it is
`Deformation.Artin.BaseChange.exists_localRetraction_of_isVersalAt`.

## Main definitions

* `Deformation.Artin.HasLocalRetractions`: versal objects retract first-order thickenings over
  a neighbourhood of the versal point.
* `Deformation.Artin.HasWeaklyEffectiveThickeningTowers`: towers of first-order thickenings map
  compatibly to one object.

## Main results

* `Deformation.Artin.isVersalAt_of_specializes_of_hasLocalRetractions`: versality at a point is
  versality at its generalizations of finite type.
* `Deformation.Artin.isOpenVersality_of_hasLocalRetractions`: openness of versality.
* `Deformation.Artin.hasThickeningDescent_of_isLimitPreserving`: descent along first-order
  thickenings for a limit preserving category.
* `Deformation.Artin.hasLocalRetractions_of_hasRepresentableDiagonal`.

## Implementation notes

Condition (4) of Stacks 0CXU asks the systems `(ξₙ)` of Stacks 0CXT to be effective, i.e. to
come from one object over `Spec (lim Rₙ)` with compatible isomorphisms to the `ξₙ`. Its proof
only uses arrows `ξₙ ⟶ ξ` whose composites with the given arrows `x ⟶ ξₙ` agree, which is
`Deformation.Artin.HasWeaklyEffectiveThickeningTowers`; this is what the proof of Stacks 0CYF
delivers, since there the compatibility of the isomorphisms along the transition maps is not
available.

## References

* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
* [Stacks Project, Tag 0G2K](https://stacks.math.columbia.edu/tag/0G2K)
* [Stacks Project, Tag 0CXM](https://stacks.math.columbia.edu/tag/0CXM)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ClosedImmersionTFAE

namespace Deformation.Artin

universe u v w

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : Type v} [Category.{w} F] (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)

/-- *Local retractions at versal points.* For every arrow `r : x ⟶ ξ'` over a first-order
thickening of schemes locally of finite type over `S` and every finite type point `u₀` at which
`x` is versal, there are an arrow `cw : w ⟶ ξ'` over an open immersion whose image contains the
image of `u₀`, and an arrow `β : w ⟶ x` with `s' ≫ β = t'` whenever `t' ≫ r = s' ≫ cw`. -/
abbrev HasLocalRetractions : Prop :=
  ∀ (x ξ' : F) (r : x ⟶ ξ'),
    LocallyOfFiniteType (B.inclusion.map (p.obj x).hom) →
    LocallyOfFiniteType (B.inclusion.map (p.obj ξ').hom) →
    Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map r)) →
    ∀ (u₀ : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x)),
      IsFiniteTypePoint u₀ →
      IsVersalAt ((Over.post B.inclusion).obj (p.obj x)) (p ⋙ Over.post B.inclusion) u₀ x rfl →
      ∃ (w : F) (cw : w ⟶ ξ')
        (_ : IsOpenImmersion ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map cw)))
        (w₀ : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj w))
        (_ : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map cw)).base w₀ =
          ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map r)).base u₀)
        (β : w ⟶ x),
        ∀ (z' : F) (t' : z' ⟶ x) (s' : z' ⟶ w), t' ≫ r = s' ≫ cw → s' ≫ β = t'

/-- *Weak effectivity of towers of first-order thickenings.* For an object `x` over an affine
scheme `U` locally of finite type over `S` whose image lies in an open `W` of `S` with
`good W`, every tower `x ⟶ x₁ ⟶ x₂ ⟶ …` over first-order thickenings `U ⟶ Uₙ`, whose steps
are closed immersions, has arrows `xₙ ⟶ ξ` whose composites with `x ⟶ xₙ` agree, and such that
`U ⟶ T` is a first-order thickening, `T` being the scheme under `ξ`. -/
abbrev HasWeaklyEffectiveThickeningTowers (good : S.Opens → Prop) : Prop :=
  ∀ (x : F) (xs : ℕ → F) (step : ∀ n, xs n ⟶ xs (n + 1)) (fromX : ∀ n, x ⟶ xs n),
    (∃ hzero : xs 0 = x, fromX 0 = eqToHom hzero.symm) →
    (∀ n, fromX (n + 1) = fromX n ≫ step n) →
    IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x)) →
    LocallyOfFiniteType (B.inclusion.map (p.obj x).hom) →
    (∃ W : S.Opens, good W ∧ Set.range (B.inclusion.map (p.obj x).hom).base ⊆ (W : Set S)) →
    (∀ n, Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (fromX (n + 1))))) →
    (∀ n, IsClosedImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (step (n + 1))))) →
    ∃ (ξ : F) (ι : ∀ n, xs (n + 1) ⟶ ξ), (∀ n, fromX (n + 1) ≫ ι n = fromX 1 ≫ ι 0) ∧
      Stacks.Thickenings.IsFirstOrderThickening
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (fromX 1 ≫ ι 0)))

/-- Effective towers are weakly effective. -/
theorem HasEffectiveThickeningTowers.weaklyEffective {good : S.Opens → Prop}
    (h : HasEffectiveThickeningTowers B S hS p good) :
    HasWeaklyEffectiveThickeningTowers B S hS p good := by
  intro x xs step fromX _ hfromS hxaff hxlft hW hthick hstep
  obtain ⟨ξ, ι, hι, hthick₁⟩ := h x xs step fromX hfromS hxaff hxlft hW hthick hstep
  refine ⟨ξ, ι, fun n => ?_, hthick₁⟩
  induction n with
  | zero => rfl
  | succ n ih => rw [hfromS (n + 1), Category.assoc, hι n, ih]

/-! ### Retractions over a neighbourhood -/

/-- The structure morphism of the source of an arrow of the big fppf site factors through its
target. -/
private theorem map_comp_inclusion_map_hom {X Y : AlgebraicGeometry.BigFppfOver B S hS}
    (f : X ⟶ Y) :
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f ≫ B.inclusion.map Y.hom =
      B.inclusion.map X.hom :=
  (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w f))

/-- The scheme map under an arrow `s` lifting `j`, up to the identifications of the objects. -/
private theorem toScheme_map_map_comp_eqToHom {a y : F}
    {b c : AlgebraicGeometry.BigFppfOver B S hS} (j : b ⟶ c) (s : a ⟶ y) [p.IsHomLift j s] :
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        (p.map s ≫ eqToHom (IsHomLift.codomain_eq p j s)) =
      eqToHom (congrArg _ (IsHomLift.domain_eq p j s)) ≫
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j := by
  rw [IsHomLift.fac' p j s]
  simp

/-- **A versal object retracts an arrow through which a first-order thickening factors.** Given
local retractions, if `r : x ⟶ y` and `e : y ⟶ ξ'` are such that `r ≫ e` lies over a first-order
thickening of schemes locally of finite type and `x` is versal at the finite type point `u₀`,
there is an open neighbourhood `O'` of the image of `u₀` such that every arrow `s : z ⟶ y` whose
composite with `e` lies over a morphism with image in `O'` admits `β : z ⟶ x` retracting `r`
along `s`. -/
theorem exists_open_localRetraction_comp_of_hasLocalRetractions (hp : p.IsFiberedInGroupoids)
    (hL : HasLocalRetractions B S hS p) (x y ξ' : F)
    (hx : LocallyOfFiniteType (B.inclusion.map (p.obj x).hom))
    (hξ' : LocallyOfFiniteType (B.inclusion.map (p.obj ξ').hom))
    (r : x ⟶ y) (e : y ⟶ ξ')
    (hr : Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (r ≫ e))))
    (u₀ : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))
    (hu₀ : IsFiniteTypePoint u₀)
    (hvers : IsVersalAt ((Over.post B.inclusion).obj (p.obj x)) (p ⋙ Over.post B.inclusion)
      u₀ x rfl) :
    ∃ O' : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj ξ')).Opens,
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (r ≫ e))).base u₀ ∈ O' ∧
      ∀ (z : F) (s : z ⟶ y),
        Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
          (p.map (s ≫ e))).base ⊆ O' →
        ∃ β : z ⟶ x, ∀ (x' : F) (a : x' ⟶ x) (b : x' ⟶ z), a ≫ r = b ≫ s → b ≫ β = a := by
  let V := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  obtain ⟨w, cw, hopen, w₀, hw₀, β, hret⟩ := hL x ξ' (r ≫ e) hx hξ' hr u₀ hu₀ hvers
  refine ⟨(V.map (p.map cw)).opensRange, ⟨w₀, hw₀⟩, ?_⟩
  intro z s hrange
  -- the arrow `s ≫ e` lies over a morphism factoring through the open immersion under `cw`
  let m : V.obj (p.obj z) ⟶ V.obj (p.obj w) :=
    IsOpenImmersion.lift (V.map (p.map cw)) (V.map (p.map (s ≫ e))) (by
      intro t ht
      exact hrange ht)
  have hm : m ≫ V.map (p.map cw) = V.map (p.map (s ≫ e)) := IsOpenImmersion.lift_fac _ _ _
  let mS : p.obj z ⟶ p.obj w := Over.homMk (ObjectProperty.homMk m) (by
    apply ObjectProperty.hom_ext
    change m ≫ B.inclusion.map (p.obj w).hom = B.inclusion.map (p.obj z).hom
    rw [← map_comp_inclusion_map_hom B S hS (p.map cw), ← Category.assoc, hm,
      map_comp_inclusion_map_hom B S hS (p.map (s ≫ e))])
  have hmS : mS ≫ p.map cw = p.map (s ≫ e) :=
    Over.OverMorphism.ext <| ObjectProperty.hom_ext _ hm
  obtain ⟨zw, ⟨-, hzw⟩, -⟩ := hp.unique_lift cw (s ≫ e) mS hmS
  refine ⟨zw ≫ β, fun x' a b hab => ?_⟩
  have h := hret x' a (b ≫ zw) (by simp only [Category.assoc, hzw, reassoc_of% hab])
  simpa only [Category.assoc] using h


/-! ### Versality and generalization -/

/-- **Stacks 0G2K, from local retractions.** Let `𝒳` satisfy (RS*), have local retractions and
descent along first-order thickenings, and let `x` lie over an affine scheme `U` locally of
finite type over `S` whose image lies in an affine open of `S`. If `x` is versal at a finite type
point `u₀` and `u` is a finite type point of `U` specializing to `u₀`, then `x` is versal at
`u`. -/
theorem isVersalAt_of_specializes_of_hasLocalRetractions (hp : p.IsFiberedInGroupoids)
    [IsLocallyNoetherian S] (hRS : SatisfiesRSStar B S hS p hp)
    (hL : HasLocalRetractions B S hS p) (hD : HasThickeningDescent B S hS p) (x : F)
    [IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))]
    [LocallyOfFiniteType (B.inclusion.map (p.obj x).hom)]
    (hW : ∃ W : S.Opens, IsAffineOpen W ∧
      Set.range (B.inclusion.map (p.obj x).hom).base ⊆ (W : Set S))
    {u u₀ : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x)}
    (hu : IsFiniteTypePoint u) (hu₀ : IsFiniteTypePoint u₀) (hspec : u ⤳ u₀)
    (hvers : IsVersalAt ((Over.post B.inclusion).obj (p.obj x)) (p ⋙ Over.post B.inclusion)
      u₀ x rfl) :
    IsVersalAt ((Over.post B.inclusion).obj (p.obj x)) (p ⋙ Over.post B.inclusion) u x rfl := by
  classical
  let V := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have : LocallyOfFiniteType ((Over.post B.inclusion).obj (p.obj x)).hom :=
    inferInstanceAs (LocallyOfFiniteType (B.inclusion.map (p.obj x).hom))
  by_contra hnot
  obtain ⟨T, i, y, hy, r, hr, hthick, -, -, hno⟩ :=
    exists_firstOrderThickening_without_localRetraction B S hS p hp hRS (p.obj x) x rfl u hu
      hnot
  subst hy
  have hr' : p.map r = i := by simpa using hr
  have hthick_r : Stacks.Thickenings.IsFirstOrderThickening (V.map (p.map r)) := by
    rwa [hr']
  -- descend `y` to a first-order thickening of finite type
  obtain ⟨ξ', e, -, hlft', hthick'⟩ := hD y (p.obj x) (p.map r) inferInstance inferInstance
    hthick_r hW
  have : IsLocallyNoetherian (B.inclusion.obj (B.obj hS)) := ‹IsLocallyNoetherian S›
  have : IsLocallyNoetherian (V.obj (p.obj ξ')) :=
    LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map (p.obj ξ').hom)
  obtain ⟨O', hO'₀, hO'⟩ := exists_open_localRetraction_comp_of_hasLocalRetractions B S hS p hp
    hL x y ξ' inferInstance hlft' r e (by rwa [Functor.map_comp, Functor.map_comp]) u₀ hu₀ hvers
  -- the open neighbourhood of `u` in `T` lying over `O'`
  let Wsch : (V.obj (p.obj y)).Opens := (V.map (p.map e)) ⁻¹ᵁ O'
  have hWc : B.Contains Wsch :=
    lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion Wsch.ι) (p.obj y).left.2
  let W := AlgebraicGeometry.BigFppfOver.siteObjectOver B S hS (p.obj y) hWc Wsch.ι
  let j : W ⟶ p.obj y := AlgebraicGeometry.BigFppfOver.siteMapOver B S hS (p.obj y) hWc Wsch.ι
  have hu_mem : (V.map i).base u ∈ Wsch := by
    have h1 := (hspec.map (V.map (p.map (r ≫ e))).continuous).mem_open O'.isOpen hO'₀
    change (V.map (p.map e)).base ((V.map i).base u) ∈ O'
    rwa [Functor.map_comp, Functor.map_comp, hr', Scheme.Hom.comp_apply] at h1
  obtain ⟨z, s, hs⟩ := hp.exists_lift j y rfl
  have hz : p.obj z = W := IsHomLift.domain_eq p j s
  have hsV : V.map (p.map s) = eqToHom (congrArg V.obj hz) ≫ V.map j := by
    simpa only [eqToHom_refl, Category.comp_id] using
      toScheme_map_map_comp_eqToHom B S hS p j s
  have hrange : Set.range (V.map (p.map (s ≫ e))).base ⊆ O' := by
    rintro _ ⟨t, rfl⟩
    rw [Functor.map_comp, Functor.map_comp, hsV, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact (show ((Wsch : Scheme.{u}) : Type u) from
      (eqToHom (congrArg V.obj hz)).base t).2
  obtain ⟨β, hβ⟩ := hO' z s hrange
  have hsc : p.IsCartesian (p.map s) s :=
    (hp.isStronglyCartesian s).isCartesian_of_isStronglyCartesian
  refine hno W j ⟨(V.map i).base u, hu_mem⟩ rfl (inferInstanceAs (IsOpenImmersion Wsch.ι)) z hz s
    (IsHomLift.fac' p j s) hsc ?_
  -- the pullback of the neighbourhood to `U`
  let Pop : (V.obj (p.obj x)).Opens := (V.map i) ⁻¹ᵁ Wsch
  have hPc : B.Contains Pop :=
    lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion Pop.ι) (p.obj x).left.2
  let P := AlgebraicGeometry.BigFppfOver.siteObjectOver B S hS (p.obj x) hPc Pop.ι
  let ta : P ⟶ p.obj x :=
    AlgebraicGeometry.BigFppfOver.siteMapOver B S hS (p.obj x) hPc Pop.ι
  let g : P ⟶ W := Over.homMk (ObjectProperty.homMk (V.map i ∣_ Wsch)) (by
    apply ObjectProperty.hom_ext
    change (V.map i ∣_ Wsch) ≫ Wsch.ι ≫ B.inclusion.map (p.obj y).hom =
      Pop.ι ≫ B.inclusion.map (p.obj x).hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc,
      map_comp_inclusion_map_hom B S hS i])
  have hsq : ta ≫ i = g ≫ j :=
    Over.OverMorphism.ext <| ObjectProperty.hom_ext _ (morphismRestrict_ι (V.map i) Wsch).symm
  obtain ⟨x', a, ha⟩ := hp.exists_lift ta x rfl
  have hx' : p.obj x' = P := IsHomLift.domain_eq p ta a
  have : p.IsHomLift i r := by
    rw [← hr']
    infer_instance
  have : p.IsStronglyCartesian j s := hp.isStronglyCartesian_homLift j s
  let b : x' ⟶ z := Functor.IsStronglyCartesian.map p j s hsq (a ≫ r)
  have hb : b ≫ s = a ≫ r := Functor.IsStronglyCartesian.fac p j s hsq (a ≫ r)
  refine ⟨β, x', a, b, (hp.isStronglyCartesian a).isCartesian_of_isStronglyCartesian,
    (hp.isStronglyCartesian b).isCartesian_of_isStronglyCartesian, ?_, hb.symm,
    hβ x' a b hb.symm⟩
  have haV : V.map (p.map a ≫ eqToHom rfl) = eqToHom (congrArg V.obj hx') ≫ V.map ta :=
    toScheme_map_map_comp_eqToHom B S hS p ta a
  have hbV : V.map (p.map b ≫ eqToHom hz) = eqToHom (congrArg V.obj hx') ≫ V.map g :=
    toScheme_map_map_comp_eqToHom B S hS p g b
  rw [haV, hbV]
  exact isPullback_eqToHom_comp _ (isPullback_morphismRestrict (V.map i) Wsch).flip

/-! ### Openness of versality -/

/-- **Stacks 0CXU, the affine case, from local retractions.** Let `x` lie over an affine scheme
`U` locally of finite type over `S`, with image in an affine open `G` of `S` satisfying `good`.
If `x` is versal at the finite type point `u₀`, then `x` is versal at every finite type point of
an open neighbourhood of `u₀`. -/
theorem exists_open_isVersalAt_of_isAffine_of_hasLocalRetractions (hp : p.IsFiberedInGroupoids)
    [IsLocallyNoetherian S] (hRS : SatisfiesRSStar B S hS p hp)
    (hL : HasLocalRetractions B S hS p) (hD : HasThickeningDescent B S hS p)
    (good : S.Opens → Prop) (heff : HasWeaklyEffectiveThickeningTowers B S hS p good) (x : F)
    [IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))]
    [LocallyOfFiniteType (B.inclusion.map (p.obj x).hom)]
    (G : S.Opens) (hG : good G) (hGaff : IsAffineOpen G)
    (hxG : Set.range (B.inclusion.map (p.obj x).hom).base ⊆ (G : Set S))
    (u₀ : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))
    (hu₀ : IsFiniteTypePoint u₀)
    (hvers : IsVersalAt ((Over.post B.inclusion).obj (p.obj x)) (p ⋙ Over.post B.inclusion)
      u₀ x rfl) :
    ∃ W : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x)).Opens, u₀ ∈ W ∧
      ∀ u ∈ W, IsFiniteTypePoint u →
        IsVersalAt ((Over.post B.inclusion).obj (p.obj x)) (p ⋙ Over.post B.inclusion) u x
          rfl := by
  classical
  let V := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let q := p ⋙ Over.post B.inclusion
  let X := V.obj (p.obj x)
  have : IsLocallyNoetherian (B.inclusion.obj (B.obj hS)) := ‹IsLocallyNoetherian S›
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map (p.obj x).hom)
  have : IsNoetherian X := {}
  have : LocallyOfFiniteType (q.obj x).hom :=
    inferInstanceAs (LocallyOfFiniteType (B.inclusion.map (p.obj x).hom))
  have : IsAffine (q.obj x).left :=
    ‹IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))›
  have : IsAffine (B.inclusion.obj (p.obj x).left) :=
    ‹IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))›
  have : QuasiCompact (q.obj x).hom :=
    quasiCompact_of_range_subset_isAffineOpen (B.inclusion.map (p.obj x).hom) hGaff hxG
  have hW : ∃ W : S.Opens, IsAffineOpen W ∧
      Set.range (B.inclusion.map (p.obj x).hom).base ⊆ (W : Set S) := ⟨G, hGaff, hxG⟩
  by_contra hcon
  push Not at hcon
  let E : Set X := {u | IsFiniteTypePoint u ∧ ¬ IsVersalAt (q.obj x) q u x rfl}
  have hgen : ∀ e ∈ E, ¬ e ⤳ u₀ := fun e he hspec =>
    he.2 (isVersalAt_of_specializes_of_hasLocalRetractions B S hS p hp hRS hL hD x hW he.1 hu₀
      hspec hvers)
  have hcl : u₀ ∈ closure E := by
    rw [mem_closure_iff]
    intro O hO hu₀O
    obtain ⟨u, hu, hft, hnv⟩ := hcon ⟨O, hO⟩ hu₀O
    exact ⟨u, hu, hft, hnv⟩
  obtain ⟨v, hvE, hinc, hclv⟩ := exists_seq_of_mem_closure X hcl hgen
  -- the tower of Stacks 0G2S at the points `v n`
  obtain ⟨xs, step, fromX, hzero, hfrom0, hfromS, hprops⟩ :=
    exists_sequence_firstOrderThickenings_without_localRetraction B S hS p hp hRS (q.obj x) x
      rfl v (fun n => (hvE n).1) hinc (fun n => (hvE n).2)
  have hthick : ∀ n, Stacks.Thickenings.IsFirstOrderThickening
      (V.map (p.map (fromX (n + 1)))) := fun n => by
    have h := (hprops n).1
    simp only [eqToHom_refl, Category.id_comp] at h
    exact h
  have hstep : ∀ n, IsClosedImmersion (V.map (p.map (step (n + 1)))) := by
    intro n
    have hepi := (hprops (n + 1)).2.1.1
    let i := V.map (p.map (step (n + 1)))
    let j₁ := V.map (p.map (fromX (n + 1)))
    let j₂ := V.map (p.map (fromX (n + 2)))
    have hj : j₂ = j₁ ≫ i := by
      change V.map (p.map (fromX (n + 2))) = _
      rw [hfromS (n + 1), Functor.map_comp, Functor.map_comp]
    have h₁ : IsHomeomorph j₁.base := by
      have := (hthick n).1
      exact isHomeomorph_iff_isEmbedding_surjective.mpr
        ⟨j₁.isClosedEmbedding.isEmbedding, (hthick n).isThickening.2⟩
    have h₂ : Topology.IsClosedEmbedding j₂.base := by
      have := (hthick (n + 1)).1
      exact j₂.isClosedEmbedding
    let e := h₁.homeomorph
    have hie : (i.base : _ → _) = j₂.base ∘ e.symm := by
      funext y
      have hy : j₁.base (e.symm y) = y := e.apply_symm_apply y
      conv_lhs => rw [← hy]
      change (j₁ ≫ i).base (e.symm y) = _
      rw [← hj]
      rfl
    exact isClosedImmersion_of_epi_unitToPushforwardObjUnit
      i ⟨hie ▸ h₂.comp e.symm.isClosedEmbedding, hepi⟩
  obtain ⟨ξ, ι, hcomp, hthick₁⟩ := heff x xs step fromX ⟨hzero, hfrom0⟩ hfromS inferInstance
    inferInstance
    ⟨G, hG, hxG⟩ hthick hstep
  -- descent and the local retraction
  obtain ⟨ξ', e, -, hlft', hthick'⟩ := hD ξ (p.obj x) (p.map (fromX 1 ≫ ι 0)) inferInstance
    inferInstance hthick₁ hW
  obtain ⟨O', hO'₀, hO'⟩ := exists_open_localRetraction_comp_of_hasLocalRetractions B S hS p hp
    hL x ξ ξ' inferInstance hlft' (fromX 1 ≫ ι 0) e (by rwa [Functor.map_comp, Functor.map_comp])
    u₀ hu₀ hvers
  -- a point of the sequence inside the neighbourhood
  let OU : X.Opens := (V.map (p.map ((fromX 1 ≫ ι 0) ≫ e))) ⁻¹ᵁ O'
  obtain ⟨_, hmO, ⟨n, rfl⟩⟩ := mem_closure_iff.mp hclv OU OU.isOpen hO'₀
  obtain ⟨y, rW, z, t, s, hopen, hrange, hts, hpb⟩ := exists_open_restriction_square B S hS p hp
    (fromX (n + 1)) ((V.map (p.map (ι n ≫ e))) ⁻¹ᵁ O')
  have hmem : (V.map (p.map (fromX (n + 1)))).base (v n) ∈
      (V.map (p.map (ι n ≫ e))) ⁻¹ᵁ O' := by
    change (V.map (p.map (ι n ≫ e))).base ((V.map (p.map (fromX (n + 1)))).base (v n)) ∈ O'
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, ← Functor.map_comp, ← Category.assoc,
      hcomp n]
    exact hmO
  obtain ⟨β, hβ⟩ := hO' y (rW ≫ ι n) (by
    rintro _ ⟨a, rfl⟩
    rw [Category.assoc, Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply]
    have ha : (V.map (p.map rW)).base a ∈ Set.range (V.map (p.map rW)).base := ⟨a, rfl⟩
    rw [hrange] at ha
    exact ha)
  have hpt : ∃ z' : (q.obj y).left, (q.map rW).left z' =
      (eqToHom (congrArg Over.left (rfl : q.obj x = q.obj x)).symm ≫
        (q.map (fromX (n + 1))).left) (v n) := by
    have h : (V.map (p.map (fromX (n + 1)))).base (v n) ∈ Set.range (V.map (p.map rW)).base := by
      rw [hrange]
      exact hmem
    obtain ⟨z', hz'⟩ := h
    refine ⟨z', ?_⟩
    simp only [eqToHom_refl, Category.id_comp]
    exact hz'
  exact (hprops n).2.2 y rW hopen hpt z t s hpb ⟨β, hβ z t s (by
    rw [← hcomp n, ← Category.assoc, hts, Category.assoc]), hts⟩

/-- **Stacks 0CXU, from local retractions.** Let `𝒳` satisfy (RS*), have local retractions,
descent along first-order thickenings, and weakly effective towers of first-order thickenings
over the opens of a family `good` of affine opens covering `S`. Then `𝒳` satisfies openness of
versality. -/
theorem isOpenVersality_of_hasLocalRetractions (hp : p.IsFiberedInGroupoids)
    [IsLocallyNoetherian S] (hRS : SatisfiesRSStar B S hS p hp)
    (hL : HasLocalRetractions B S hS p) (hD : HasThickeningDescent B S hS p)
    (good : S.Opens → Prop) (hgood : ∀ s : S, ∃ G : S.Opens, good G ∧ IsAffineOpen G ∧ s ∈ G)
    (heff : HasWeaklyEffectiveThickeningTowers B S hS p good) :
    ∀ (U : Over S), LocallyOfFiniteType U.hom →
      ∀ (x : F) (hx : (p ⋙ Over.post B.inclusion).obj x = U) (u₀ : U.left),
        IsFiniteTypePoint u₀ →
        IsVersalAt U (p ⋙ Over.post B.inclusion) u₀ x hx →
        ∃ W : U.left.Opens, u₀ ∈ W.1 ∧
          ∀ u ∈ W.1, IsFiniteTypePoint u →
            IsVersalAt U (p ⋙ Over.post B.inclusion) u x hx := by
  classical
  intro U hU x hx u₀ hu₀ hvers
  subst hx
  let V := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let q := p ⋙ Over.post B.inclusion
  let fS := B.inclusion.map (p.obj x).hom
  obtain ⟨G, hG, hGaff, hu₀G⟩ := hgood (fS.base u₀)
  obtain ⟨U₁, hU₁aff, hu₀U₁, hU₁G⟩ :=
    exists_isAffineOpen_mem_and_subset (X := V.obj (p.obj x)) (U := fS ⁻¹ᵁ G) (x := u₀) hu₀G
  have hU₁c : B.Contains U₁ :=
    lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion U₁.ι) (p.obj x).left.2
  let T₁ := AlgebraicGeometry.BigFppfOver.siteObjectOver B S hS (p.obj x) hU₁c U₁.ι
  let j₁ : T₁ ⟶ p.obj x := AlgebraicGeometry.BigFppfOver.siteMapOver B S hS (p.obj x) hU₁c U₁.ι
  obtain ⟨x₁, ρ, hρ⟩ := hp.exists_lift j₁ x rfl
  have hx₁ : p.obj x₁ = T₁ := IsHomLift.domain_eq p j₁ ρ
  let jρ := V.map (p.map ρ)
  have hjρ : jρ = eqToHom (congrArg V.obj hx₁) ≫ V.map j₁ := by
    simpa only [eqToHom_refl, Category.comp_id] using
      toScheme_map_map_comp_eqToHom B S hS p j₁ ρ
  have : IsOpenImmersion (V.map j₁) := inferInstanceAs (IsOpenImmersion U₁.ι)
  have : IsOpenImmersion jρ := by
    rw [hjρ]
    infer_instance
  have : IsAffine (V.obj T₁) := hU₁aff
  have : IsAffine (V.obj (p.obj x₁)) := IsAffine.of_isIso (eqToHom (congrArg V.obj hx₁))
  have hS₁ : B.inclusion.map (p.obj x₁).hom = jρ ≫ fS :=
    (map_comp_inclusion_map_hom B S hS (p.map ρ)).symm
  have : LocallyOfFiniteType fS := hU
  have : LocallyOfFiniteType (B.inclusion.map (p.obj x₁).hom) := by
    rw [hS₁]
    infer_instance
  have hrange₁ : Set.range jρ.base = (U₁ : Set _) := by
    rw [hjρ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      (ConcreteCategory.bijective_of_isIso (eqToHom (congrArg V.obj hx₁)).base).2.range_eq,
      Set.image_univ]
    exact U₁.range_ι
  have hmemU₁ (t : V.obj (p.obj x₁)) : jρ.base t ∈ (U₁ : Set _) := by
    rw [← hrange₁]
    exact ⟨t, rfl⟩
  have hx₁G : Set.range (B.inclusion.map (p.obj x₁).hom).base ⊆ (G : Set S) := by
    rintro _ ⟨t, rfl⟩
    rw [hS₁, Scheme.Hom.comp_apply]
    exact hU₁G (hmemU₁ t)
  -- versality at a point of `U₁` is versality at its image in `U`
  have hiff : ∀ t : V.obj (p.obj x₁),
      IsVersalAt (q.obj x₁) q t x₁ rfl ↔ IsVersalAt (q.obj x) q (jρ.base t) x rfl := by
    intro t
    refine isVersalAt_iff_restrict B S hS p hp hGaff.fromSpec rfl rfl ρ jρ ‹_›
      (by simp only [schemeMap, eqToHom_refl, Category.id_comp, Category.comp_id]; rfl) t ?_ ?_
    · rw [hGaff.range_fromSpec]
      rintro _ ⟨k, rfl⟩
      change fS.base (((q.obj x).left.fromSpecResidueField (jρ.base t)).base k) ∈ G
      have hk : ((q.obj x).left.fromSpecResidueField (jρ.base t)).base k = jρ.base t :=
        (Set.ext_iff.mp (Scheme.range_fromSpecResidueField (X := (q.obj x).left) (jρ.base t))
          _).mp ⟨k, rfl⟩
      rw [hk]
      exact hU₁G (hmemU₁ t)
    · rw [hGaff.range_fromSpec]
      rintro _ ⟨k, rfl⟩
      change (B.inclusion.map (p.obj x₁).hom).base
        (((q.obj x₁).left.fromSpecResidueField t).base k) ∈ G
      exact hx₁G ⟨_, rfl⟩
  obtain ⟨u₀', hu₀'⟩ : u₀ ∈ Set.range jρ.base := hrange₁ ▸ hu₀U₁
  obtain ⟨W₁, hu₀W₁, hW₁⟩ := exists_open_isVersalAt_of_isAffine_of_hasLocalRetractions B S hS p hp
    hRS hL hD good heff x₁ G hG hGaff hx₁G u₀' (isFiniteTypePoint_of_isOpenImmersion jρ u₀'
      (by rwa [hu₀'])) ((hiff u₀').mpr (by rwa [hu₀']))
  refine ⟨jρ.opensFunctor.obj W₁, ⟨u₀', hu₀W₁, hu₀'⟩, ?_⟩
  rintro _ ⟨t, htW, rfl⟩ hft
  exact (hiff t).mp (hW₁ t htW (isFiniteTypePoint_of_isOpenImmersion jρ t hft))


/-! ### Descent along first-order thickenings for a limit preserving category -/

/-- A first-order thickening followed by an `eqToHom` is a first-order thickening. -/
theorem isFirstOrderThickening_comp_eqToHom {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (h : Y = Y')
    (hf : Stacks.Thickenings.IsFirstOrderThickening f) :
    Stacks.Thickenings.IsFirstOrderThickening (f ≫ eqToHom h) := by
  subst h
  simpa using hf

/-- **Descent along first-order thickenings.** If `𝒳` is limit preserving, an object of `𝒳` over
a first-order thickening `U ⟶ T` of an affine scheme `U` of finite type over an affine open
`Spec Λ` of `S` is the pullback of an object over `Spec R'`, for a finite type `Λ`-subalgebra
`R' ⊆ Γ(T)` surjecting onto `Γ(U)`; in particular `U ⟶ Spec R'` is again a first-order
thickening. The ring `Γ(T)` is the filtered colimit of its finitely generated subalgebras over
one containing lifts of generators of `Γ(U)`, so `T` is the limit of their spectra. -/
theorem hasThickeningDescent_of_isLimitPreserving
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (AlgebraicGeometry.BigFppfOver B S hS))
    (h3 : IsLimitPreserving.{u, u, u, w, v} B S hS 𝒳) :
    HasThickeningDescent B S hS 𝒳.val.p := by
  classical
  intro ξ U i hUaff hUlft hthick ⟨W, hWaff, hUW⟩
  have hp : 𝒳.val.p.IsFiberedInGroupoids := 𝒳.isFiberedInGroupoids
  let : 𝒳.val.p.IsFibered := hp.isFibered
  let VV := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let T := 𝒳.val.p.obj ξ
  have : IsAffine (VV.obj U) := hUaff
  have : IsAffine (VV.obj T) :=
    Stacks.Thickenings.isAffine_of_isThickening hthick.isThickening
  have : IsAffine W := hWaff
  have : IsClosedImmersion (VV.map i) := hthick.1
  let fU : VV.obj U ⟶ S := B.inclusion.map U.hom
  let fT : VV.obj T ⟶ S := B.inclusion.map T.hom
  have hiT : VV.map i ≫ fT = fU := map_comp_inclusion_map_hom B S hS i
  have hTW : Set.range fT.base ⊆ Set.range W.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    obtain ⟨u, rfl⟩ := hthick.isThickening.2 t
    rw [← Scheme.Hom.comp_apply, hiT]
    exact hUW ⟨u, rfl⟩
  let τ : VV.obj T ⟶ W := IsOpenImmersion.lift W.ι fT hTW
  have hτ : τ ≫ W.ι = fT := IsOpenImmersion.lift_fac _ _ _
  let Λ : CommRingCat.{u} := Γ(W, ⊤)
  let R : CommRingCat.{u} := Γ(VV.obj T, ⊤)
  let R₀ : CommRingCat.{u} := Γ(VV.obj U, ⊤)
  let : Algebra Λ R := τ.appTop.hom.toAlgebra
  let : Algebra Λ R₀ := (VV.map i ≫ τ).appTop.hom.toAlgebra
  let q : R →ₐ[Λ] R₀ :=
    { (VV.map i).appTop.hom with
      commutes' := fun l => by
        change (VV.map i).appTop.hom (τ.appTop.hom l) = (VV.map i ≫ τ).appTop.hom l
        rw [Scheme.Hom.comp_appTop]
        rfl }
  have hqsurj : Function.Surjective q :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (VV.map i)).2
  have hqker : (RingHom.ker q.toRingHom) ^ 2 = ⊥ :=
    ker_appTop_sq_of_isFirstOrderThickening (VV.map i) hthick
  have hft : Algebra.FiniteType Λ R₀ := by
    have hl : LocallyOfFiniteType (VV.map i ≫ τ) := by
      have : LocallyOfFiniteType ((VV.map i ≫ τ) ≫ W.ι) := by
        rw [Category.assoc, hτ, hiT]
        exact hUlft
      exact locallyOfFiniteType_of_comp _ W.ι
    exact HasRingHomProperty.appTop @LocallyOfFiniteType (VV.map i ≫ τ) hl
  obtain ⟨s₀, hs₀⟩ := hft.out
  choose lift hlift using hqsurj
  let G : Finset R := s₀.image lift
  let A₀ : Subalgebra Λ R := Algebra.adjoin Λ (G : Set R)
  have : Fact A₀.FG := ⟨Subalgebra.fg_adjoin_finset G⟩
  have hG : Algebra.adjoin Λ (q '' (G : Set R)) = ⊤ := by
    rw [show q '' (G : Set R) = (s₀ : Set R₀) by simp [G, Set.image_image, hlift], hs₀]
  -- the inverse system of spectra of finitely generated subalgebras
  let J := FGSubalgebraAbove Λ R A₀
  have hWc : B.Contains W :=
    lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion W.ι) hS
  have hΛc : B.Contains (Spec Λ) :=
    lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion (W : Scheme.{u}).isoSpec.inv) hWc
  have hAc (A : J) : B.Contains (Spec (CommRingCat.of A.1)) := by
    have : Algebra.FiniteType Λ A.1 := (Subalgebra.fg_iff_finiteType A.1).mp A.2.1
    exact Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit Λ A.1
      hΛc
  let toS : Spec Λ ⟶ S := (W : Scheme.{u}).isoSpec.inv ≫ W.ι
  let stage (A : J) : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (X := B.obj (hAc A)) (Y := B.obj hS)
      (Spec.map (CommRingCat.ofHom (algebraMap Λ A.1)) ≫ toS))
  let stageMap {A A' : J} (h : A ≤ A') : stage A' ⟶ stage A :=
    Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom))) (by
        apply ObjectProperty.hom_ext
        change Spec.map _ ≫ Spec.map _ ≫ toS = Spec.map _ ≫ toS
        rw [← Category.assoc, ← Spec.map_comp]
        rfl)
  let D : Jᵒᵖ ⥤ AlgebraicGeometry.BigFppfOver B S hS :=
    { obj := fun A => stage A.unop
      map := fun h => stageMap (leOfHom h.unop)
      map_id := fun A => by
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        change Spec.map _ = 𝟙 _
        rw [show CommRingCat.ofHom (Subalgebra.inclusion (le_refl A.unop.1)).toRingHom =
          𝟙 _ from rfl, Spec.map_id]
      map_comp := fun h h' => by
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        change Spec.map _ = Spec.map _ ≫ Spec.map _
        rw [← Spec.map_comp]
        rfl }
  have hRc : B.Contains (Spec R) :=
    lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion (VV.obj T).isoSpec.inv) T.left.2
  let T₁ : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (X := B.obj hRc) (Y := B.obj hS)
      (Spec.map τ.appTop ≫ toS))
  let c : Cone D :=
    { pt := T₁
      π :=
        { app := fun A => Over.homMk (ObjectProperty.homMk
            (Spec.map (CommRingCat.ofHom A.unop.1.val.toRingHom))) (by
              apply ObjectProperty.hom_ext
              change Spec.map _ ≫ Spec.map _ ≫ toS = Spec.map _ ≫ toS
              rw [← Category.assoc, ← Spec.map_comp]
              rfl)
          naturality := fun A A' h => by
            apply Over.OverMorphism.ext
            apply ObjectProperty.hom_ext
            change 𝟙 _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
            rw [Category.id_comp, ← Spec.map_comp]
            rfl } }
  have hc : IsLimit (VV.mapCone c) := by
    convert isLimitOfPreserves Scheme.Spec (fgSubalgebraAboveRingCoconeIsColimit Λ R A₀).op
      using 1 <;> rfl
  have haff : ∀ A, IsAffineOver B S hS (D.obj A) := fun A =>
    (inferInstance : IsAffine (Spec (CommRingCat.of A.unop.1)))
  have hcaff : IsAffineOver B S hS c.pt := (inferInstance : IsAffine (Spec R))
  let D' : Jᵒᵖ ⥤ BigAffineFppf B S hS := (IsAffineOver B S hS).lift D haff
  let c' : Cone D' :=
    { pt := ⟨c.pt, hcaff⟩
      π :=
        { app := fun A => ObjectProperty.homMk (c.π.app A)
          naturality := fun A A' h => by
            apply ObjectProperty.hom_ext
            change 𝟙 _ ≫ c.π.app A' = c.π.app A ≫ D.map h
            rw [Category.id_comp, c.w h] } }
  have hc' : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c') := hc
  have : (colimitComparison 𝒳.val.p (D' ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c')).EssSurj := (h3 Jᵒᵖ D' c' hc').essSurj
  have hdesc : DescentObj 𝒳.val.p (D' ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c') :=
    descentObj_of_essSurj 𝒳.val.p _ _
  -- the object over `Spec R`
  have hTT₁ : (VV.obj T).isoSpec.inv ≫ fT = Spec.map τ.appTop ≫ toS := by
    rw [← hτ, ← Category.assoc, ← Scheme.isoSpec_inv_naturality]
    simp only [toS, Category.assoc]
  let isoT : T₁ ⟶ T := Over.homMk (ObjectProperty.homMk (VV.obj T).isoSpec.inv)
    (ObjectProperty.hom_ext _ hTT₁)
  have : IsIso isoT := by
    have : IsIso (VV.map isoT) := inferInstanceAs (IsIso (VV.obj T).isoSpec.inv)
    exact isIso_of_reflects_iso isoT VV
  obtain ⟨ξ₁, φ, hφ⟩ := hp.exists_lift isoT ξ rfl
  have hξ₁ : 𝒳.val.p.obj ξ₁ = T₁ := IsHomLift.domain_eq _ isoT φ
  have : 𝒳.val.p.IsStronglyCartesian isoT φ := hp.isStronglyCartesian_homLift isoT φ
  have : IsIso φ := Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.p isoT φ
  obtain ⟨k, xk, δ, hδ⟩ := hdesc ⟨ξ₁, hξ₁⟩
  let ξ' := xk.1
  let e : ξ ⟶ ξ' := inv φ ≫ δ
  have : Algebra.FiniteType Λ k.unop.1 := (Subalgebra.fg_iff_finiteType k.unop.1).mp k.unop.2.1
  have hξ' : 𝒳.val.p.obj ξ' = D.obj k := xk.2
  have h₁ : 𝒳.val.p.map φ = eqToHom hξ₁ ≫ isoT := by
    rw [IsHomLift.fac' 𝒳.val.p isoT φ]
    simp
  have h₂ : 𝒳.val.p.map δ = eqToHom hξ₁ ≫ c.π.app k ≫ eqToHom hξ'.symm := by
    have := hδ
    exact IsHomLift.fac' 𝒳.val.p (((BigAffineFppf.inclusion B S hS).mapCone c').π.app k) δ
  have hea : 𝒳.val.p.map e = inv isoT ≫ c.π.app k ≫ eqToHom hξ'.symm := by
    change 𝒳.val.p.map (inv φ ≫ δ) = _
    rw [Functor.map_comp, Functor.map_inv]
    simp only [h₁, h₂, IsIso.inv_comp, inv_eqToHom, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
  refine ⟨ξ', e, ?_, ?_, ?_⟩
  · rw [hξ']
    exact (inferInstance : IsAffine (Spec (CommRingCat.of k.unop.1)))
  · rw [hξ']
    change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k.unop.1)) ≫ toS)
    have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k.unop.1))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
    have : LocallyOfFiniteType toS := by
      simp only [toS]
      infer_instance
    infer_instance
  · -- `U ⟶ Spec R'` is the spectrum of `R' ⟶ R ⟶ Γ(U)`
    have hsq := surjective_ker_sq_of_le_subalgebra q hqker (G : Set R) hG k.unop.1
      ((Algebra.subset_adjoin).trans k.unop.2.2)
    have key : VV.map i ≫ (VV.obj T).isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom k.unop.1.val.toRingHom) = (VV.obj U).isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom k.unop.1.val.toRingHom ≫ (VV.map i).appTop) := by
      rw [Spec.map_comp]
      exact (Scheme.isoSpec_hom_naturality_assoc (VV.map i) _).symm
    have h := isFirstOrderThickening_iso_comp (VV.obj U).isoSpec.hom _
      (Stacks.Smooth.isFirstOrderThickening_specMap
        (CommRingCat.ofHom k.unop.1.val.toRingHom ≫ (VV.map i).appTop) hsq.1 hsq.2)
    rw [← key] at h
    have hVe : VV.map (𝒳.val.p.map e) = (VV.obj T).isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom k.unop.1.val.toRingHom) ≫
          eqToHom (congrArg VV.obj hξ'.symm) := by
      rw [hea, Functor.map_comp, Functor.map_comp, Functor.map_inv, eqToHom_map]
      congr 1
      change inv (VV.obj T).isoSpec.inv = _
      simp
    rw [hVe, ← Category.assoc, ← Category.assoc]
    exact isFirstOrderThickening_comp_eqToHom _ _ (by simpa only [Category.assoc] using h)

/-! ### Local retractions for categories with representable diagonal -/

/-- **Local retractions from a representable diagonal.** A category fibred in groupoids over the
big fppf site of a locally Noetherian scheme, whose diagonal is representable by algebraic spaces
and locally of finite type and which satisfies (RS), has local retractions at versal points. -/
theorem hasLocalRetractions_of_hasRepresentableDiagonal [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (AlgebraicGeometry.BigFppfOver B S hS))
    (hΔ : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS 𝒳)
    (hΔlft :
      letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
      ∀ (T : AlgebraicGeometry.BigFppfOver B S hS)
        (a b : 𝒳.val.p.Fiber T)
        (G : (AlgebraicGeometry.BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u),
        AlgebraicGeometry.IsAlgebraicSpace B T.left.1 T.left.2 G →
        Nonempty (G ⋙ uliftFunctor.{v, u} ≅
          ((Over.iteratedSliceBackward T).op ⋙ 𝒳.val.p.isomPresheaf a b) ⋙
            uliftFunctor.{u, v}) →
        AlgebraicGeometry.Space.IsLocallyOfFiniteType B T.left.1 T.left.2
          (terminal.from G : G ⟶
            ⊤_ ((AlgebraicGeometry.BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)))
    (hRS : SatisfiesRS B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids) :
    HasLocalRetractions B S hS 𝒳.val.p := by
  intro x ξ r hx hξ hr u₀ hu₀ hvers
  exact BaseChange.exists_localRetraction_of_isVersalAt B S hS 𝒳 hΔ hΔlft hRS x ξ r hr u₀ hu₀
    hvers

end Deformation.Artin

end
