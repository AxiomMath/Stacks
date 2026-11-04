module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityTestMap
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClass
public import StacksFrontier.AlgebraicGeometry.Chow.GysinGysinPulledBackModule

/-!
# The class at infinity commutes with Gysin maps

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, let
`g : T ⟶ X` be locally of finite type, and let `D = Z(s) ⊆ T` be the zero scheme of a global
section `s` of an invertible module `L` on `T`. This file proves the third axiom of Stacks 0B76
for the cap operation `C ∩ -` of Stacks 0F9J: `C ∩ -` on `D` applied to `s^* α` is the Gysin map of
the pullback of `s` to `W_∞ ×_X T` applied to `C ∩ α`.

The source's "formal argument" is, for a lift `β` of `α` on `W ×_X T`:

* the Gysin image `s_W^* β` of `β` along the pullback of `s` to `W ×_X T` is a lift of `s^* α` on
  `W ×_X D`, because Gysin maps commute with restriction to the chart over `𝐀¹_X` and with flat
  pullback along its projection (Stacks 0B71);
* `C ∩ s^* α = i_∞^* s_W^* β` and `s'^* (C ∩ α) = s'^* i_∞^* β`, and the two Gysin maps commute
  (Stacks 0B73).

## Main results

* `Stacks.Chow.gysinSystemOfInvertible_flatPullback_comp_of_isIso` — Stacks 0B71 in relative
  dimension one, for a module pulled back in two steps and read through an isomorphism of zero
  schemes; this is the computation on the chart over `𝐀¹_X`.
* `Stacks.Chow.IsModificationLift.gysin` — the Gysin image of a lift is a lift of the Gysin
  image.
* `Stacks.Chow.gysinCapOfLift_gysin` — **Stacks 0B76 (3)** for the cap operation of the class at
  infinity.

## References

* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0B71](https://stacks.math.columbia.edu/tag/0B71)
* [Stacks Project, Tag 0B73](https://stacks.math.columbia.edu/tag/0B73)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The pullback of the divisor to the modification -/

section Geometry

variable {X S W T : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f) (g : T ⟶ X)
  (L : T.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- The pullback of `D = Z(s)` to `W ×_X T`: the zero scheme of the pulled-back section. -/
abbrev modificationDivisor : (modificationBaseChange f b g).IdealSheafData :=
  Stacks.Divisors.zeroScheme (modificationBaseChange f b g)
    ((Scheme.Modules.pullback (pullback.snd (modificationProjection f b) g)).obj L)
    (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (modificationProjection f b) g) L s)

/-- The base change of `D ⟶ T` to the modification is a closed immersion. -/
instance isClosedImmersion_modificationBaseChangeMap_zeroScheme :
    IsClosedImmersion (bivariantBaseChangeMap (modificationProjection f b) g
      (Stacks.Divisors.zeroScheme T L s).subschemeι) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion)
    (isPullback_bivariantBaseChangeMap (modificationProjection f b) g _) inferInstance

/-- The pulled-back divisor is the base change `W ×_X D` of `W ×_X T`. -/
theorem ker_modificationBaseChangeMap_zeroScheme :
    (bivariantBaseChangeMap (modificationProjection f b) g
      (Stacks.Divisors.zeroScheme T L s).subschemeι).ker = modificationDivisor f b g L s := by
  rw [AlgebraicGeometry.ker_eq_comap_ker_of_isPullback
      (isPullback_bivariantBaseChangeMap (modificationProjection f b) g _).flip,
    Scheme.IdealSheafData.ker_subschemeι, modificationDivisor, Stacks.Divisors.zeroScheme_pullback]

/-- The identification of the pulled-back divisor with `W ×_X D`. -/
def modificationDivisorIso :
    (modificationDivisor f b g L s).subscheme ≅
      modificationBaseChange f b ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) :=
  (isoSubschemeOfKer _ _ (ker_modificationBaseChangeMap_zeroScheme f b g L s)).symm

/-- The identification of the pulled-back divisor with `W ×_X D`, followed by the base change of
`D ⟶ T` to the modification, is the inclusion of the pulled-back divisor. -/
@[reassoc (attr := simp)]
theorem modificationDivisorIso_hom_comp :
    (modificationDivisorIso f b g L s).hom ≫
        bivariantBaseChangeMap (modificationProjection f b) g
          (Stacks.Divisors.zeroScheme T L s).subschemeι =
      (modificationDivisor f b g L s).subschemeι := by
  rw [modificationDivisorIso, Iso.symm_hom, Iso.inv_comp_eq, isoSubschemeOfKer_hom_subschemeι]

/-- The base change of `D ⟶ T` to the chart over `𝐀¹_X` is a closed immersion. -/
instance isClosedImmersion_modificationAffineChartMap_zeroScheme :
    IsClosedImmersion (modificationAffineChartMap f b g
      (Stacks.Divisors.zeroScheme T L s).subschemeι) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion)
    (isPullback_modificationAffineChartMap f b g _) inferInstance

/-- The pullback of `D` to the chart over `𝐀¹_X`. -/
abbrev modificationAffineDivisor : (modificationAffineChart f b g).IdealSheafData :=
  Stacks.Divisors.zeroScheme (modificationAffineChart f b g)
    ((Scheme.Modules.pullback (modificationAffineChartι f b g)).obj
      ((Scheme.Modules.pullback (pullback.snd (modificationProjection f b) g)).obj L))
    (AlgebraicGeometry.pullbackGlobalSections (modificationAffineChartι f b g) _
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (modificationProjection f b) g) L s))

/-- The closed subscheme cut out by the base change of `D ⟶ T` to the chart over `𝐀¹_X` is the
pullback of `D` to that chart. -/
theorem ker_modificationAffineChartMap_zeroScheme :
    (modificationAffineChartMap f b g (Stacks.Divisors.zeroScheme T L s).subschemeι).ker =
      modificationAffineDivisor f b g L s := by
  rw [AlgebraicGeometry.ker_eq_comap_ker_of_isPullback
      (isPullback_modificationAffineChartMap f b g _).flip,
    ker_modificationBaseChangeMap_zeroScheme, modificationAffineDivisor,
    Stacks.Divisors.zeroScheme_pullback]

/-- The identification of the pulled-back divisor of the chart with the chart of `W ×_X D`. -/
def modificationAffineDivisorIso :
    (modificationAffineDivisor f b g L s).subscheme ≅
      modificationAffineChart f b ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) :=
  (isoSubschemeOfKer _ _ (ker_modificationAffineChartMap_zeroScheme f b g L s)).symm

/-- The identification of the pulled-back divisor of the chart with the chart of `W ×_X D`,
followed by the base change of `D ⟶ T` to the chart, is the inclusion of that divisor. -/
@[reassoc (attr := simp)]
theorem modificationAffineDivisorIso_hom_comp :
    (modificationAffineDivisorIso f b g L s).hom ≫
        modificationAffineChartMap f b g (Stacks.Divisors.zeroScheme T L s).subschemeι =
      (modificationAffineDivisor f b g L s).subschemeι := by
  rw [modificationAffineDivisorIso, Iso.symm_hom, Iso.inv_comp_eq, isoSubschemeOfKer_hom_subschemeι]

/-- The open immersion of the pulled-back divisor of the chart into the pulled-back divisor. -/
abbrev modificationAffineDivisorMap :
    (modificationAffineDivisor f b g L s).subscheme ⟶ (modificationDivisor f b g L s).subscheme :=
  Stacks.Divisors.zeroSchemePullbackMap (modificationAffineChartι f b g) _ _

/-- The inclusion of the pulled-back divisor of the chart into the pulled-back divisor is an open
immersion, being a base change of the open immersion of the chart. -/
instance isOpenImmersion_modificationAffineDivisorMap :
    IsOpenImmersion (modificationAffineDivisorMap f b g L s) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
    (Stacks.Divisors.isPullback_zeroSchemePullbackMap _ _ _) inferInstance

/-- The two identifications with the base change to `D` are compatible with the charts. -/
theorem modificationAffineDivisorIso_comp_ι :
    (modificationAffineDivisorIso f b g L s).hom ≫
        modificationAffineChartι f b ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) =
      modificationAffineDivisorMap f b g L s ≫ (modificationDivisorIso f b g L s).hom := by
  refine (cancel_mono (bivariantBaseChangeMap (modificationProjection f b) g
    (Stacks.Divisors.zeroScheme T L s).subschemeι)).1 ?_
  rw [Category.assoc, ← modificationAffineChartMap_ι, modificationAffineDivisorIso_hom_comp_assoc,
    Category.assoc, modificationDivisorIso_hom_comp,
    Stacks.Divisors.zeroSchemePullbackMap_comp_subschemeι]

/-- The identification of the pulled-back divisor with `W ×_X D` is a morphism over the base. -/
theorem modificationDivisorIso_over :
    (modificationDivisorIso f b g L s).hom ≫
        modificationBaseChangeOver f b ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) =
      (modificationDivisor f b g L s).subschemeι ≫ modificationBaseChangeOver f b g := by
  rw [← modificationBaseChangeMap_over, modificationDivisorIso_hom_comp_assoc]

/-- The inverse of the identification of the fibre at infinity of `W ×_X T'` with its presentation
as a zero scheme, followed by the base change of `T' ⟶ T`, is the base change of `T' ⟶ T` to the
fibres at infinity followed by their inclusion. -/
theorem modificationInfinityZeroSchemeIso_inv_comp_baseChangeMap {T' : Scheme.{u}} (h : T' ⟶ T) :
    (modificationInfinityZeroSchemeIso f b (h ≫ g)).inv ≫
        (Stacks.Divisors.zeroScheme (modificationBaseChange f b (h ≫ g))
          (modificationInfinityModule f b (h ≫ g))
          (modificationInfinitySection f b (h ≫ g))).subschemeι ≫
        bivariantBaseChangeMap (modificationProjection f b) g h =
      bivariantBaseChangeMap (modificationProjectionAtInfinity f b) g h ≫
        modificationInfinityBaseChange f b g := by
  rw [Iso.inv_comp_eq, modificationInfinityBaseChange_comp_map f b g h
      (bivariantBaseChangeMap (modificationProjectionAtInfinity f b) g h)
      (isPullback_bivariantBaseChangeMap _ _ _).w.symm (bivariantBaseChangeMap_fst _ _ _),
    modificationInfinityZeroSchemeIso_hom_comp_assoc]

end Geometry

/-! ### The Gysin image of a lift -/

/-- **Stacks 0B71 through an isomorphism of zero schemes, in relative dimension one.** Let
`π : A ⟶ T` be flat of relative dimension `1` and factor as `A ⟶ B ⟶ T`; let `L` be invertible
on `T` with a global section `s` and zero scheme `D`, and let `π' : A' ⟶ D` be flat of relative
dimension `1`. If `v` identifies the zero scheme of the pullback of `s` to `A` (pulled back in two
steps) with `A'` over `π` and `π'`, then pushing forward along `v` the Gysin image of `π^* α` gives
`π'^*` of the Gysin image of `α`. -/
theorem gysinSystemOfInvertible_flatPullback_comp_of_isIso (C : ChowSituation.{u})
    {A B T A' : Scheme.{u}} (p : T ⟶ C.S) [LocallyOfFiniteType p] (pA : A ⟶ C.S)
    [LocallyOfFiniteType pA] (pA' : A' ⟶ C.S) [LocallyOfFiniteType pA'] (ι : A ⟶ B) (q : B ⟶ T)
    (π : A ⟶ T) [LocallyOfFiniteType π] [Flat π] (hπ : ι ≫ q = π) (hpA : π ≫ p = pA)
    (hr : AlgebraicGeometry.RelativeDimension π 1) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (π' : A' ⟶ (Stacks.Divisors.zeroScheme T L s).subscheme)
    [LocallyOfFiniteType π'] [Flat π']
    (hpA' : π' ≫ (Stacks.Divisors.zeroScheme T L s).subschemeι ≫ p = pA')
    (hr' : AlgebraicGeometry.RelativeDimension π' 1)
    (v : (Stacks.Divisors.zeroScheme A
        ((Scheme.Modules.pullback ι).obj ((Scheme.Modules.pullback q).obj L))
        (AlgebraicGeometry.pullbackGlobalSections ι ((Scheme.Modules.pullback q).obj L)
          (AlgebraicGeometry.pullbackGlobalSections q L s))).subscheme ⟶ A') [IsIso v]
    (hv : v ≫ pA' = (Stacks.Divisors.zeroScheme A
        ((Scheme.Modules.pullback ι).obj ((Scheme.Modules.pullback q).obj L))
        (AlgebraicGeometry.pullbackGlobalSections ι ((Scheme.Modules.pullback q).obj L)
          (AlgebraicGeometry.pullbackGlobalSections q L s))).subschemeι ≫ pA)
    (hvπ : v ≫ π' ≫ (Stacks.Divisors.zeroScheme T L s).subschemeι =
      (Stacks.Divisors.zeroScheme A
        ((Scheme.Modules.pullback ι).obj ((Scheme.Modules.pullback q).obj L))
        (AlgebraicGeometry.pullbackGlobalSections ι ((Scheme.Modules.pullback q).obj L)
          (AlgebraicGeometry.pullbackGlobalSections q L s))).subschemeι ≫ π)
    (k : ℤ) (α : chowGroup C p (k + 1)) :
    properChowPushforward C ((Stacks.Divisors.zeroScheme A
        ((Scheme.Modules.pullback ι).obj ((Scheme.Modules.pullback q).obj L))
        (AlgebraicGeometry.pullbackGlobalSections ι ((Scheme.Modules.pullback q).obj L)
          (AlgebraicGeometry.pullbackGlobalSections q L s))).subschemeι ≫ pA) pA' v hv (k + 1)
        (properPushforwardDescends C _ _ _ _ _)
        ((gysinSystemOfInvertible C).onChow pA
          ((Scheme.Modules.pullback ι).obj ((Scheme.Modules.pullback q).obj L))
          (AlgebraicGeometry.pullbackGlobalSections ι ((Scheme.Modules.pullback q).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q L s)) (k + 1)
          (flatPullbackChow C pA p π hpA 1 hr (k + 1) (flatPullbackDescends C _ _ _ _ _ _ _) α)) =
      flatPullbackChow C pA' ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ p) π' hpA' 1 hr' k
        (flatPullbackDescends C _ _ _ _ _ _ _) ((gysinSystemOfInvertible C).onChow p L s k α) := by
  subst hπ hpA hpA'
  have hZ := Stacks.Divisors.zeroScheme_pullback_comp ι q L s
  have hG := heq_gysinHomomorphismOnChowOfInvertible C ((ι ≫ q) ≫ p) (k + 1)
    ((Scheme.Modules.pullback ι).obj ((Scheme.Modules.pullback q).obj L))
    ((Scheme.Modules.pullback (ι ≫ q)).obj L)
    (AlgebraicGeometry.pullbackGlobalSections ι ((Scheme.Modules.pullback q).obj L)
      (AlgebraicGeometry.pullbackGlobalSections q L s))
    (AlgebraicGeometry.pullbackGlobalSections (ι ≫ q) L s)
    ((Scheme.Modules.pullbackComp ι q).app L) hZ
    (gysinOfInvertibleDescends C _ _ _ _) (gysinOfInvertibleDescends C _ _ _ _)
  have hGx := heq_gysin_apply ((ι ≫ q) ≫ p) (k + 1) hZ _ _ hG
    (flatPullbackChow C ((ι ≫ q) ≫ p) p (ι ≫ q) rfl 1 hr (k + 1)
      (flatPullbackDescends C _ _ _ _ _ _ _) α)
  have key : ∀ (Z : A.IdealSheafData) (_hZ : pullbackZeroScheme (ι ≫ q) L s = Z)
      (v : Z.subscheme ⟶ A') [IsIso v]
      (hv : v ≫ π' ≫ (Stacks.Divisors.zeroScheme T L s).subschemeι ≫ p =
        Z.subschemeι ≫ (ι ≫ q) ≫ p)
      (_hvπ : v ≫ π' ≫ (Stacks.Divisors.zeroScheme T L s).subschemeι = Z.subschemeι ≫ ι ≫ q)
      (y : chowGroup C (Z.subschemeι ≫ (ι ≫ q) ≫ p) (k + 1))
      (_hy : y ≍ (gysinSystemOfInvertible C).onChow ((ι ≫ q) ≫ p)
        ((Scheme.Modules.pullback (ι ≫ q)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (ι ≫ q) L s) (k + 1)
        (flatPullbackChow C ((ι ≫ q) ≫ p) p (ι ≫ q) rfl 1 hr (k + 1)
          (flatPullbackDescends C _ _ _ _ _ _ _) α)),
      properChowPushforward C (Z.subschemeι ≫ (ι ≫ q) ≫ p)
          (π' ≫ (Stacks.Divisors.zeroScheme T L s).subschemeι ≫ p) v hv (k + 1)
          (properPushforwardDescends C _ _ _ _ _) y =
        flatPullbackChow C (π' ≫ (Stacks.Divisors.zeroScheme T L s).subschemeι ≫ p)
          ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ p) π' rfl 1 hr' k
          (flatPullbackDescends C _ _ _ _ _ _ _)
          ((gysinSystemOfInvertible C).onChow p L s k α) := by
    intro Z hZ' v _ hv hvπ y hy
    subst hZ'
    obtain rfl := eq_of_heq hy
    have hτ : v ≫ π' = zeroSchemePullbackHom (ι ≫ q) L s := by
      refine (cancel_mono (Stacks.Divisors.zeroScheme T L s).subschemeι).1 ?_
      rw [Category.assoc, hvπ, zeroSchemePullbackHom_subschemeι]
    have h02RG := flatPullbackChow_chowPushforwardOfIso C _ _ _ _ (𝟙 _) (Category.id_comp _) v hv
      (zeroSchemePullbackHom (ι ≫ q) L s) (zeroSchemePullbackHom_comp _ L s C p _ rfl) π' rfl
      (by rw [Category.comp_id, hτ]) 1
      (relativeDimension_zeroSchemePullbackHom _ L s 1 hr) hr' k
      (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
      ((gysinSystemOfInvertible C).onChow p L s k α)
    have hid := chowPushforwardOfIso_id C ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ p) k
      ((gysinSystemOfInvertible C).onChow p L s k α)
    have h1 := (DFunLike.congr_arg (flatPullbackChow C _ _ π' rfl 1 hr' k
      (flatPullbackDescends C _ _ _ _ _ _ _)) hid).symm.trans h02RG
    have h0B71 := gysinSystemOfInvertible_flatPullback C p ((ι ≫ q) ≫ p) (ι ≫ q) rfl 1 hr k L s α
    refine eq_of_heq (HEq.trans ?_ (heq_of_eq h1.symm))
    exact properChowPushforward_heq_congr C _ _ v hv (by push_cast; ring) _ _ _ _
      ((gysinSystemOnChow_heq_congr _ _ _ _ (by push_cast; ring) _ _
        (chowGroupDegreeEquiv_heq C _ (by ring : k + 1 + (1 : ℕ) = k + (1 : ℕ) + 1) _).symm).trans
        (heq_of_eq h0B71))
  exact key _ hZ.symm v hv hvπ _ hGx

/-- Pushing forward along `w`, then `a`, then `c`, with `w ≫ a ≫ c = 𝟙`, is the identity. -/
theorem properChowPushforward_comp_comp_eq_self (C : ChowSituation.{u}) {A B D : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (sD : D ⟶ C.S) [LocallyOfFiniteType sD] (w : D ⟶ A) [IsProper w] (a : A ⟶ B) [IsProper a]
    (c : B ⟶ D) [IsProper c] (hw : w ≫ sA = sD) (ha : a ≫ sB = sA) (hc : c ≫ sD = sB)
    (h : w ≫ a ≫ c = 𝟙 D) (k : ℤ) (y : chowGroup C sD k) :
    properChowPushforward C sB sD c hc k (properPushforwardDescends C _ _ _ _ _)
        (properChowPushforward C sA sB a ha k (properPushforwardDescends C _ _ _ _ _)
          (properChowPushforward C sD sA w hw k
            (properPushforwardDescends C _ _ _ _ _) y)) = y := by
  rw [← properChowPushforward_comp_apply C sD sA sB w a (w ≫ a) rfl hw ha
      (by rw [Category.assoc, ha, hw]) k (properPushforwardDescends C _ _ _ _ _)
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _),
    ← properChowPushforward_comp_apply C sD sB sD (w ≫ a) c (𝟙 D)
      (by rw [Category.assoc, h]) _ hc (Category.id_comp sD) k
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
      (properPushforwardDescends C _ _ _ _ _)]
  exact chowPushforwardOfIso_id C sD k y

section Lift

variable (C : ChowSituation.{u}) {X W T : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b] (g : T ⟶ X) [LocallyOfFiniteType g]
  (L : T.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- **The Gysin image of a lift is a lift of the Gysin image** (Stacks 0B71). If `β` lifts `α` on
`W ×_X T`, then the Gysin image of `β` along the pullback of `s`, read on `W ×_X D`, lifts `s^* α`:
the Gysin map commutes with restriction to the chart over `𝐀¹_X`, and on the chart with flat
pullback along its projection to `T`. -/
theorem IsModificationLift.gysin
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) (k : ℤ)
    {α : chowGroup C (g ≫ f) (k + 1)}
    {β : chowGroup C (modificationBaseChangeOver f b g) (k + 1 + 1)}
    (hβ : IsModificationLift C f b hA g (k + 1) α β) :
    IsModificationLift C f b hA ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) k
      ((gysinSystemOfInvertible C).onChow (g ≫ f) L s k α)
      (chowPushforwardOfIso C ((modificationDivisor f b g L s).subschemeι ≫
          modificationBaseChangeOver f b g)
        (modificationBaseChangeOver f b ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g))
        (modificationDivisorIso f b g L s).hom (modificationDivisorIso_over f b g L s) (k + 1)
        ((gysinSystemOfInvertible C).onChow (modificationBaseChangeOver f b g)
          ((Scheme.Modules.pullback (pullback.snd (modificationProjection f b) g)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections
            (pullback.snd (modificationProjection f b) g) L s)
          (k + 1) β)) := by
  have := flat_modificationAffineChartProjection f b g hA
  have := flat_modificationAffineChartProjection f b
    ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) hA
  unfold IsModificationLift at hβ ⊢
  -- restriction to the chart commutes with the identification of the divisor with `W ×_X D`
  have hsq : IsPullback (modificationAffineDivisorMap f b g L s)
      (modificationAffineDivisorIso f b g L s).hom (modificationDivisorIso f b g L s).hom
      (modificationAffineChartι f b ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)) :=
    IsPullback.of_vert_isIso ⟨(modificationAffineDivisorIso_comp_ι f b g L s).symm⟩
  have hjZ := Stacks.Divisors.zeroSchemePullbackMap_comp_structureMorphism
    (modificationAffineChartι f b g)
    ((Scheme.Modules.pullback (pullback.snd (modificationProjection f b) g)).obj L)
    (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (modificationProjection f b) g) L s)
    (modificationBaseChangeOver f b g) (modificationAffineChartOver C f b g) rfl
  have hε' : (modificationAffineDivisorIso f b g L s).hom ≫
      modificationAffineChartOver C f b ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) =
      (modificationAffineDivisor f b g L s).subschemeι ≫ modificationAffineChartOver C f b g := by
    rw [← modificationAffineChartMap_over, modificationAffineDivisorIso_hom_comp_assoc]
  rw [chowPushforwardOfIso, chowGroupRestrict_properChowPushforward C _ _ _ _
    (modificationDivisorIso f b g L s).hom (modificationDivisorIso_over f b g L s)
    (modificationAffineDivisorMap f b g L s) hjZ
    (modificationAffineChartι f b ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)) rfl
    (modificationAffineDivisorIso f b g L s).hom hε' hsq (k + 1) _
    (properPushforwardDescends C _ _ _ _ _)]
  -- the Gysin map commutes with restriction to the chart
  rw [gysinSystemOfInvertible_isNaturalUnderOpensRestriction C (modificationBaseChangeOver f b g)
    (modificationAffineChartOver C f b g) (modificationAffineChartι f b g) rfl _ _ (k + 1)
    (modificationAffineDivisorMap f b g L s)
    (Stacks.Divisors.zeroSchemePullbackMap_comp_subschemeι _ _ _) hjZ β, hβ]
  -- on the chart, the Gysin map commutes with flat pullback along the projection to `T`
  refine gysinSystemOfInvertible_flatPullback_comp_of_isIso C (g ≫ f) _ _
    (modificationAffineChartι f b g) (pullback.snd (modificationProjection f b) g)
    (modificationAffineChartProjection f b g) rfl (modificationAffineChartProjection_over C f b g)
    (relativeDimension_modificationAffineChartProjection f b g hA) L s
    (modificationAffineChartProjection f b ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g))
    ?_ (relativeDimension_modificationAffineChartProjection f b _ hA)
    (modificationAffineDivisorIso f b g L s).hom hε' ?_ k α
  rw [← modificationAffineChartMap_projection, modificationAffineDivisorIso_hom_comp_assoc]

end Lift

section Law

variable (C : ChowSituation.{u}) {X W T : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b] (g : T ⟶ X) [LocallyOfFiniteType g]
  (L : T.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-! ### The cap operation commutes with Gysin maps -/

/-- **Stacks 0B76 (3) for the class at infinity** (Stacks 0F9J). Let `D = Z(s) ⊆ T` and let `E`
be the zero scheme of the pullback of `s` to `W_∞ ×_X T`, identified with `W_∞ ×_X D` by `e` over
`W_∞ ×_X T`. Then `e_* (C ∩ s^* α) = s'^* (C ∩ α)`.

For a lift `β` of `α`, `C ∩ s^* α` is computed from the lift `s_W^* β` of `s^* α`
(`Stacks.Chow.IsModificationLift.gysin`), and both sides become the two composites of the Gysin
maps of `s_W` and of the section at infinity applied to `β`, which agree by Stacks 0B73
(`Stacks.Chow.gysinSystemOfInvertible_comm_properPushforward`). -/
theorem gysinCapOfLift_gysin (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) (k : ℤ)
    (e : pullback (modificationProjectionAtInfinity f b)
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≅
      (Stacks.Divisors.zeroScheme (pullback (modificationProjectionAtInfinity f b) g)
          ((Scheme.Modules.pullback (pullback.snd (modificationProjectionAtInfinity f b) g)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections
            (pullback.snd (modificationProjectionAtInfinity f b) g) L s)).subscheme)
    (he : e.hom ≫ (Stacks.Divisors.zeroScheme (pullback (modificationProjectionAtInfinity f b) g)
          ((Scheme.Modules.pullback (pullback.snd (modificationProjectionAtInfinity f b) g)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections
            (pullback.snd (modificationProjectionAtInfinity f b) g) L s)).subschemeι =
      bivariantBaseChangeMap (modificationProjectionAtInfinity f b) g
        (Stacks.Divisors.zeroScheme T L s).subschemeι)
    (hbase : e.hom ≫ ((Stacks.Divisors.zeroScheme
          (pullback (modificationProjectionAtInfinity f b) g)
          ((Scheme.Modules.pullback (pullback.snd (modificationProjectionAtInfinity f b) g)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections
            (pullback.snd (modificationProjectionAtInfinity f b) g) L s)).subschemeι ≫
          modificationInfinityBaseChangeOver f b g) =
      modificationInfinityBaseChangeOver f b ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g))
    (α : chowGroup C (g ≫ f) (k + 1)) :
    properChowPushforward C (modificationInfinityBaseChangeOver f b
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g))
        ((Stacks.Divisors.zeroScheme (pullback (modificationProjectionAtInfinity f b) g)
          ((Scheme.Modules.pullback (pullback.snd (modificationProjectionAtInfinity f b) g)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections
            (pullback.snd (modificationProjectionAtInfinity f b) g) L s)).subschemeι ≫
          modificationInfinityBaseChangeOver f b g) e.hom hbase k
        (properPushforwardDescends C _ _ _ _ _)
        (gysinCapAtInfinity C f b hA ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) k
          ((gysinSystemOfInvertible C).onChow (g ≫ f) L s k α)) =
      (gysinSystemOfInvertible C).onChow (modificationInfinityBaseChangeOver f b g)
        ((Scheme.Modules.pullback (pullback.snd (modificationProjectionAtInfinity f b) g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections
          (pullback.snd (modificationProjectionAtInfinity f b) g) L s) k
        (gysinCapAtInfinity C f b hA g (k + 1) α) := by
  obtain ⟨β, hβ⟩ := exists_isModificationLift C f b hA g (k + 1) α
  have hβD := IsModificationLift.gysin C f b g L s hA k hβ
  refine (congrArg (properChowPushforward C _ _ e.hom hbase k
    (properPushforwardDescends C _ _ _ _ _))
    (gysinCapAtInfinity_eq_of_isModificationLift C f b hA _ k _ _ hβD)).trans
    (Eq.trans ?_ (congrArg ((gysinSystemOfInvertible C).onChow _ _ _ k)
      (gysinCapAtInfinity_eq_of_isModificationLift C f b hA g (k + 1) α β hβ)).symm)
  have hr₂ : (modificationInfinityZeroSchemeIso f b g).hom ≫
      pullback.snd (modificationProjectionAtInfinity f b) g =
      (Stacks.Divisors.zeroScheme (modificationBaseChange f b g) (modificationInfinityModule f b g)
        (modificationInfinitySection f b g)).subschemeι ≫
        pullback.snd (modificationProjection f b) g := by
    rw [← modificationInfinityBaseChange_comp_snd, modificationInfinityZeroSchemeIso_hom_comp_assoc]
  have hr₁ : (modificationDivisorIso f b g L s).hom ≫
      modificationBaseChangeToRelativeLine f b ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) =
      (modificationDivisor f b g L s).subschemeι ≫ modificationBaseChangeToRelativeLine f b g := by
    rw [← modificationBaseChangeMap_toRelativeLine, modificationDivisorIso_hom_comp_assoc]
  have hwy : (e.inv ≫ (modificationInfinityZeroSchemeIso f b
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)).inv) ≫
      (Stacks.Divisors.zeroScheme (modificationBaseChange f b
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g))
        (modificationInfinityModule f b ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g))
        (modificationInfinitySection f b
          ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g))).subschemeι ≫
      bivariantBaseChangeMap (modificationProjection f b) g
        (Stacks.Divisors.zeroScheme T L s).subschemeι =
      (Stacks.Divisors.zeroScheme (pullback (modificationProjectionAtInfinity f b) g)
        ((Scheme.Modules.pullback (pullback.snd (modificationProjectionAtInfinity f b) g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections
          (pullback.snd (modificationProjectionAtInfinity f b) g) L s)).subschemeι ≫
        modificationInfinityBaseChange f b g := by
    rw [Category.assoc, modificationInfinityZeroSchemeIso_inv_comp_baseChangeMap, ← Category.assoc,
      (Iso.inv_comp_eq e).2 he.symm]
  have hw : (e.inv ≫ (modificationInfinityZeroSchemeIso f b
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)).inv) ≫
      ((Stacks.Divisors.zeroScheme (modificationBaseChange f b
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g))
        (modificationInfinityModule f b ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g))
        (modificationInfinitySection f b
          ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g))).subschemeι ≫
      modificationBaseChangeOver f b ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)) =
      (Stacks.Divisors.zeroScheme (pullback (modificationProjectionAtInfinity f b) g)
        ((Scheme.Modules.pullback (pullback.snd (modificationProjectionAtInfinity f b) g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections
          (pullback.snd (modificationProjectionAtInfinity f b) g) L s)).subschemeι ≫
        modificationInfinityBaseChangeOver f b g :=
    (Category.assoc _ _ _).trans ((congrArg (e.inv ≫ ·) ((Iso.inv_comp_eq _).2
      (modificationInfinityZeroSchemeIso_over C f b
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)).symm)).trans
      ((Iso.inv_comp_eq e).2 hbase.symm))
  have := lineInfinityDivisor_isEffectiveCartierDivisor C.S
  have key := gysinSystemOfInvertible_comm_properPushforward C (modificationBaseChangeOver f b g)
    (modificationInfinityBaseChangeOver f b g)
    (modificationBaseChangeOver f b ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g))
    (modificationBaseChangeToRelativeLine f b g) (pullback.snd (modificationProjection f b) g)
    (Stacks.Divisors.divisorSheaf (lineInfinityDivisor C.S)) L
    (Stacks.Divisors.divisorSheafGlobalSection (lineInfinityDivisor C.S)) s
    (modificationInfinityZeroSchemeIso f b g).hom (modificationInfinityZeroSchemeIso_over C f b g)
    (pullback.snd (modificationProjectionAtInfinity f b) g) hr₂
    (modificationInfinityBaseChange f b g) (modificationInfinityZeroSchemeIso_hom_comp f b g)
    (modificationDivisorIso f b g L s).hom (modificationDivisorIso_over f b g L s)
    (modificationBaseChangeToRelativeLine f b ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g))
    hr₁ (bivariantBaseChangeMap (modificationProjection f b) g
      (Stacks.Divisors.zeroScheme T L s).subschemeι)
    (modificationDivisorIso_hom_comp f b g L s)
    (e.inv ≫ (modificationInfinityZeroSchemeIso f b
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)).inv) hw hwy k β
  refine (congrArg (fun z ↦ properChowPushforward C _ _ e.hom hbase k
    (properPushforwardDescends C _ _ _ _ _) (chowPushforwardOfIso C _ _
      (modificationInfinityZeroSchemeIso f b
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)).hom
      (modificationInfinityZeroSchemeIso_over C f b _) k z)) key.symm).trans ?_
  exact properChowPushforward_comp_comp_eq_self C _ _ _
    (e.inv ≫ (modificationInfinityZeroSchemeIso f b
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)).inv)
    (modificationInfinityZeroSchemeIso f b
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)).hom e.hom hw
    (modificationInfinityZeroSchemeIso_over C f b _) hbase (by simp) k _

end Law

end Stacks.Chow

end
