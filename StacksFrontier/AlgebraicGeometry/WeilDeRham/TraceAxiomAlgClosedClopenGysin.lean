module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.TraceAxiomAlgClosedKunneth

/-!
# The Gysin pullback of the class of a rational point to an open and closed subscheme

Let `X` be smooth projective over a field `k`, of constant dimension `d`, let `U ⊆ X` be open and
closed, and let `x` be a `k`-rational point of `X`. The Gysin pullback of Stacks 0FF3
(`Stacks.Chow.codimensionGysin`) along the inclusion `U ⟶ X` carries the class
`[x] = x_*[Spec k] ∈ CH^d(X)` to

* the class `[x] ∈ CH^d(U)` of the same point, if `x` lies in `U`
  (`Stacks.WeilDeRham.codimensionGysin_clopen_pointChowClass_of_mem`);
* `0`, if `x` does not lie in `U`
  (`Stacks.WeilDeRham.codimensionGysin_clopen_pointChowClass_of_not_mem`).

Both are proved for an arbitrary open immersion `j : V ⟶ X` of schemes smooth over `k`, `X`
separated of constant dimension `d` (`Stacks.WeilDeRham.codimensionGysin_openImmersion_point` and
`Stacks.WeilDeRham.codimensionGysin_openImmersion_point_eq_zero`). The square
`Spec k ×_X V ⟶ V` is cartesian. The Gysin map is formed on the pieces `V_{d,e}`, and only
`V_{d,d} = V` is nonempty; there `j^!` commutes with the pushforward along `x` (Stacks 0B76 (1)),
so `j^![x]` is the pushforward of `j^! ∩ [Spec k]_0` computed at the test scheme
`x : Spec k ⟶ X`. If `x` factors through `V` the fibre product is `Spec k`, of the expected
dimension `0`, and Stacks 0FF7 gives `j^! ∩ [Spec k]_0 = [Spec k]_0`; if `x` misses `V` the fibre
product is empty and the class is `0`.

## References

* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0FF7](https://stacks.math.columbia.edu/tag/0FF7)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme

universe u

namespace Stacks.WeilDeRham

open Stacks.Chow

variable {k : Type u} [Field k]

section OpenImmersion

variable {X V : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX] [IsSeparated sX]
  (sV : V ⟶ (fieldChowSituation k).S) [Smooth sV] (j : V ⟶ X) [hjo : IsOpenImmersion j]
  (hj : j ≫ sX = sV)

omit [IsSeparated sX] in
include hj in
/-- An open subscheme of a smooth scheme of constant dimension `d` has constant dimension `d`. -/
theorem relativeDimension_of_openImmersion {d : ℕ} (hd : RelativeDimension sX d) :
    RelativeDimension sV d := by
  have h := RelativeDimension.comp_of_flat j sX (relativeDimension_of_isOpenImmersion j) hd
  rw [zero_add] at h
  subst hj
  exact h

omit [Smooth sX] in
include hj in
/-- An open subscheme of a separated scheme is separated. -/
theorem isSeparated_of_openImmersion : IsSeparated sV := by
  subst hj
  infer_instance

/-- **`j^![x] = [x]` on the piece `V_{d,d}`**, for an open immersion `j : V ⟶ X` and a rational
point `x` of `V`: the Gysin map of `j` on `V_{d,d}` carries the part of `[j ∘ x]` on `X_d` to the
restriction of `[x]`.

By Stacks 0B76 (1) the Gysin map commutes with the pushforward along `x`, and by Stacks 0FF7 at the
test scheme `j ∘ x : Spec k ⟶ X` it carries `[Spec k]_0` to `[Z]_0` for `Z = V ×_X Spec k`, which
is `Spec k` mapping to `V` by `x`. -/
theorem dimPartPieceGysin_openImmersion_point {d : ℕ} (hd : RelativeDimension sX d)
    (x : (fieldChowSituation k).S ⟶ V) (hx : x ≫ sV = 𝟙 _) :
    haveI := isSeparated_of_openImmersion sX sV j hj
    haveI : IsProper x := isProper_of_comp_eq_id hx
    haveI : IsProper (x ≫ j) :=
      isProper_of_comp_eq_id (show (x ≫ j) ≫ sX = 𝟙 _ by rw [Category.assoc, hj, hx])
    dimPartPieceGysin sV sX hj d d (d : ℤ)
        (chowCodimPushforward k (𝟙 _) sX (x ≫ j) (by rw [Category.assoc, hj, hx]) 0 d
          (chowCodimFundamental k (𝟙 _)) d) =
      chowGroupRestrict (fieldChowSituation k) (partBase sV d)
        (dimPartPieceBase sV sX j d d) (dimPartPiece sV sX j d d).ι rfl ((d : ℤ) - d)
        (chowCodimPushforward k (𝟙 _) sV x hx 0 d (chowCodimFundamental k (𝟙 _)) d) := by
  have := isSeparated_of_openImmersion sX sV j hj
  have : IsProper x := isProper_of_comp_eq_id hx
  have hx' : (x ≫ j) ≫ sX = 𝟙 _ := by rw [Category.assoc, hj, hx]
  have : IsProper (x ≫ j) := isProper_of_comp_eq_id hx'
  have hV := relativeDimension_of_openImmersion sX sV j hj hd
  have : IsIso (dimPart sX d).ι := isIso_dimPart_ι_of_relativeDimension _ hd
  obtain ⟨δU, hδU⟩ : ∃ δU : (fieldChowSituation k).S ⟶ (dimPart sX d).toScheme,
      δU ≫ (dimPart sX d).ι = x ≫ j :=
    ⟨(x ≫ j) ≫ inv (dimPart sX d).ι, by simp⟩
  have : IsProper δU := by
    have : IsProper (δU ≫ (dimPart sX d).ι) := by rw [hδU]; infer_instance
    exact IsProper.of_comp δU (dimPart sX d).ι
  have hpt : schemeDeltaDimension (fieldChowSituation k) (𝟙 (fieldChowSituation k).S) ≤
      (((d : ℤ) - d : ℤ) : EInt) := by
    rw [sub_self]
    exact Stacks.WeilCohomology.schemeDeltaDimension_le_of_relativeDimension (𝟙 _)
      (relativeDimension_of_isOpenImmersion (𝟙 _))
  -- the part of `[j ∘ x]` on `X_d` is `(δU : Spec k ⟶ X_d)_* [Spec k]_0`
  have h1 : chowCodimPushforward k (𝟙 _) sX (x ≫ j) hx' 0 d (chowCodimFundamental k (𝟙 _)) d =
      properChowPushforward (fieldChowSituation k) ((δU ≫ (dimPart sX d).ι) ≫ sX)
        ((dimPart sX d).ι ≫ sX) δU (by simp [Category.assoc]) _
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
        (fundamentalChowClass (fieldChowSituation k) ((δU ≫ (dimPart sX d).ι) ≫ sX)
          ((d : ℤ) - (d : ℤ))) := by
    change chowGroupRestrict (fieldChowSituation k) sX ((dimPart sX d).ι ≫ sX)
        (dimPart sX d).ι rfl _
        (properChowPushforward (fieldChowSituation k) (𝟙 _) sX (x ≫ j) hx' _
          (properPushforwardDescends _ _ _ _ _ _)
          (chowCodimTotal k (𝟙 _) 0 _ (chowCodimFundamental k (𝟙 _)))) = _
    rw [chowCodimTotal_chowCodimFundamental (𝟙 _) (relativeDimension_of_isOpenImmersion (𝟙 _)),
      chowGroupRestrict_properChowPushforward (fieldChowSituation k) (𝟙 _) sX
        ((δU ≫ (dimPart sX d).ι) ≫ sX) ((dimPart sX d).ι ≫ sX) (x ≫ j) hx' (𝟙 _)
        (by rw [hδU, Category.id_comp, hx']) (dimPart sX d).ι rfl δU
        (by simp [Category.assoc]) (IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, hδU]⟩)
        _ _ (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _),
      chowGroupRestrict_fundamentalChowClass (fieldChowSituation k) (𝟙 _) _ (𝟙 _) _ _ hpt]
  rw [h1]
  -- the Gysin map on the piece is the cap with `j^!` at the test scheme `X_d ⟶ X`, restricted
  change chowGroupDegreeEquiv _ _ _
    ((dimPartPieceGysinClass sV sX hj d d).capTargetHom _ _ _ _ _ _ _ _ _) = _
  rw [chowGroupDegreeEquiv_eq_iff_heq, BivariantClass.capTargetHom_apply]
  refine (dimPartPieceGysinClass_capTarget_heq sV sX hj d d _ _).trans ?_
  -- Stacks 0B76 (1): `j^!` commutes with the pushforward along `δU`
  rw [(smoothGysinClass (fieldChowSituation k) sV sX hj _).cap_properPushforward
    (dimPart sX d).ι δU (bivariantBaseChangeMap j (dimPart sX d).ι δU)
    (isPullback_bivariantBaseChangeMap j (dimPart sX d).ι δU)
    (by simp [bivariantBaseChangeMap]) _ _]
  -- the scheme-theoretic intersection `Z = V ×_X Spec k` is the point `x`
  have hcond : pullback.fst j (δU ≫ (dimPart sX d).ι) ≫ j =
      (pullback.snd j (δU ≫ (dimPart sX d).ι) ≫ x) ≫ j := by
    rw [pullback.condition, hδU, Category.assoc]
  have hfst : pullback.fst j (δU ≫ (dimPart sX d).ι) =
      pullback.snd j (δU ≫ (dimPart sX d).ι) ≫ x := (cancel_mono j).1 hcond
  have hfs : pullback.fst j (δU ≫ (dimPart sX d).ι) ≫ sV =
      pullback.snd j (δU ≫ (dimPart sX d).ι) := by
    rw [hfst, Category.assoc, hx, Category.comp_id]
  have ha : pullback.fst j (δU ≫ (dimPart sX d).ι) ≫ sV ≫ x =
      pullback.fst j (δU ≫ (dimPart sX d).ι) := by
    rw [← Category.assoc, hfs, ← hfst]
  have hψφ : (pullback.fst j (δU ≫ (dimPart sX d).ι) ≫ sV) ≫
      pullback.lift x (𝟙 _) (by rw [hδU, Category.id_comp]) = 𝟙 _ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp, ha]
    · simp only [Category.assoc, pullback.lift_snd, Category.id_comp, Category.comp_id]
      exact hfs
  have hφψ : pullback.lift x (𝟙 _) (by rw [hδU, Category.id_comp]) ≫
      (pullback.fst j (δU ≫ (dimPart sX d).ι) ≫ sV) = 𝟙 _ := by
    rw [pullback.lift_fst_assoc, hx]
  have : IsIso (pullback.fst j (δU ≫ (dimPart sX d).ι) ≫ sV) := ⟨_, hψφ, hφψ⟩
  -- Stacks 0FF7 at the test scheme `j ∘ x : Spec k ⟶ X`: `j^![Spec k]_0 = [Z]_0`
  have hrelT : RelativeDimension ((δU ≫ (dimPart sX d).ι) ≫ sX) 0 := by
    have key : ∀ (s : (fieldChowSituation k).S ⟶ (fieldChowSituation k).S)
        [LocallyOfFiniteType s], s = 𝟙 _ → RelativeDimension s 0 := by
      rintro s _ rfl
      exact relativeDimension_of_isOpenImmersion (𝟙 _)
    exact key _ (by rw [hδU, hx'])
  have hdim : ∀ ξ : (pullback j (δU ≫ (dimPart sX d).ι) : Scheme.{u}),
      relativeDimension (fieldChowSituation k).dimensionFunction
          (pullback.fst j (δU ≫ (dimPart sX d).ι) ≫ sV) ξ ≤
        ((d : ℤ) - d) - ((d : ℤ) - (d : ℤ)) := by
    intro ξ
    have h := relativeDimension_comp_isOpenImmersion (fieldChowSituation k).dimensionFunction
      (pullback.fst j (δU ≫ (dimPart sX d).ι) ≫ sV) (𝟙 _) ξ
    rw [Category.comp_id] at h
    rw [h]
    exact (relativeDimension_le_of_schemeDeltaDimension_le' (fieldChowSituation k) (𝟙 _)
      (Stacks.WeilCohomology.schemeDeltaDimension_le_of_relativeDimension (𝟙 _)
        (relativeDimension_of_isOpenImmersion (𝟙 _))) _).trans (by simp)
  rw [cap_completedBivariantSequenceOfInvertible_lciGysinMap_fundamentalChowClass
    (fieldChowSituation k) sV sX hj
    (isLocalCompleteIntersectionMorphism_of_smooth_of_smooth j sX sV hj)
    (GysinMapExists.of_smooth_source j sX sV hj) (δU ≫ (dimPart sX d).ι)
    (n := d) (m := (d : ℤ)) (m' := (d : ℤ) - (d : ℤ))
    (fun W ↦ Stacks.WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension k sV
      d hV W)
    (fun W ↦ Stacks.WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension k
      sX d hd W)
    (fun W ↦ (Stacks.WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension k _
      0 hrelT W).trans (by simp))
    hdim (fun ξ _ ↦ Stacks.WeilCohomology.isCohenMacaulayLocalRing_stalk_of_smooth k (𝟙 _) _)]
  -- the piece `V_{d,d}` is all of `V`, and all of `V ×_X X_d`
  have : IsIso (dimPartPieceToPreimage sV sX j d d) := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    rw [Scheme.Opens.opensRange_ι_morphismRestrict, dimPart_eq_top_of_relativeDimension sV hV]
    simp
  have : IsIso (dimPartPieceToPullback sV sX j d d) := by
    dsimp only [dimPartPieceToPullback]
    infer_instance
  have : IsIso (dimPart sV d).ι := isIso_dimPart_ι_of_relativeDimension sV hV
  have : IsIso (dimPartPiece sV sX j d d).ι := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    rw [Scheme.Opens.opensRange_ι]
    change (dimPart sV d).ι ⁻¹ᵁ (j ⁻¹ᵁ dimPart sX d) = ⊤
    rw [dimPart_eq_top_of_relativeDimension sX hd]
    simp
  rw [chowGroupRestrict_properChowPushforward_of_isIso (fieldChowSituation k) _ _ _ _ _
    (dimPartPieceToPullback sV sX j d d)]
  -- the class of the point is `x_*[Spec k]_0`
  have h2 : chowCodimPushforward k (𝟙 _) sV x hx 0 d (chowCodimFundamental k (𝟙 _)) d =
      chowGroupRestrict (fieldChowSituation k) sV (partBase sV d) (dimPart sV d).ι rfl
        ((d : ℤ) - d)
        (properChowPushforward (fieldChowSituation k) (𝟙 _) sV x hx ((d : ℤ) - d)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
          (fundamentalChowClass (fieldChowSituation k) (𝟙 _) ((d : ℤ) - d))) := by
    change chowGroupRestrict (fieldChowSituation k) sV (partBase sV d) (dimPart sV d).ι rfl _
      (properChowPushforward (fieldChowSituation k) (𝟙 _) sV x hx _
        (properPushforwardDescends _ _ _ _ _ _)
        (chowCodimTotal k (𝟙 _) 0 _ (chowCodimFundamental k (𝟙 _)))) = _
    rw [chowCodimTotal_chowCodimFundamental (𝟙 _) (relativeDimension_of_isOpenImmersion (𝟙 _))]
  rw [h2, chowGroupRestrict_comp,
    chowGroupRestrict_properChowPushforward_of_isIso (fieldChowSituation k) _ _ _ _ _
      ((dimPartPiece sV sX j d d).ι ≫ (dimPart sV d).ι)]
  -- `Z ⟶ V_{d,d}` is `x` through `Z ≅ Spec k`
  have hmor : bivariantBaseChangeMap j (dimPart sX d).ι δU ≫
        inv (dimPartPieceToPullback sV sX j d d) =
      (pullback.fst j (δU ≫ (dimPart sX d).ι) ≫ sV) ≫
        x ≫ inv ((dimPartPiece sV sX j d d).ι ≫ (dimPart sV d).ι) := by
    rw [IsIso.comp_inv_eq]
    apply pullback.hom_ext
    · simp [bivariantBaseChangeMap, ha]
    · rw [← cancel_mono (dimPart sX d).ι]
      simp only [Category.assoc, ← pullback.condition, dimPartPieceToPullback_fst_assoc]
      simp [bivariantBaseChangeMap, reassoc_of% ha]
  have hxπ : (x ≫ inv ((dimPartPiece sV sX j d d).ι ≫ (dimPart sV d).ι)) ≫
      dimPartPieceBase sV sX j d d = 𝟙 _ := by
    simp [hx]
  rw [properChowPushforward_congr_hom (fieldChowSituation k) _ _ hmor _
      (by rw [Category.assoc, hxπ, Category.comp_id]) _ _
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _),
    ← DFunLike.congr_fun (properChowPushforward_comp (fieldChowSituation k)
      (pullback.fst j (δU ≫ (dimPart sX d).ι) ≫ sV) (𝟙 _)
      (dimPartPieceBase sV sX j d d)
      (pullback.fst j (δU ≫ (dimPart sX d).ι) ≫ sV)
      (x ≫ inv ((dimPartPiece sV sX j d d).ι ≫ (dimPart sV d).ι))
      (Category.comp_id _) hxπ _
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso _ _ _ _ _ _)
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)),
    AddMonoidHom.comp_apply,
    properChowPushforward_eq_chowPushforwardOfIso (fieldChowSituation k)
      (pullback.fst j (δU ≫ (dimPart sX d).ι) ≫ sV) (𝟙 _)
      (pullback.fst j (δU ≫ (dimPart sX d).ι) ≫ sV),
    chowPushforwardOfIso_fundamentalChowClass]
  -- both sides are `x_*[Spec k]_0`, in degrees written differently
  have key : ∀ a b : ℤ, a = b →
      properChowPushforward (fieldChowSituation k) (𝟙 _)
          (dimPartPieceBase sV sX j d d)
          (x ≫ inv ((dimPartPiece sV sX j d d).ι ≫ (dimPart sV d).ι)) hxπ a
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
          (fundamentalChowClass (fieldChowSituation k) (𝟙 _) a) ≍
        properChowPushforward (fieldChowSituation k) (𝟙 _)
          (dimPartPieceBase sV sX j d d)
          (x ≫ inv ((dimPartPiece sV sX j d d).ι ≫ (dimPart sV d).ι)) hxπ b
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
          (fundamentalChowClass (fieldChowSituation k) (𝟙 _) b) := by
    rintro a _ rfl
    rfl
  exact key _ _ (by ring)

/-- **`j^![x] = 0` on the piece `V_{d,d}`**, for an open immersion `j : V ⟶ X` and a rational
point `x` of `X` outside the image of `j`: by Stacks 0B76 (1) the Gysin map of `j` on `V_{d,d}`
carries the part of `[x]` on `X_d` to a pushforward from `V ×_X Spec k`, which is empty. -/
theorem dimPartPieceGysin_openImmersion_point_eq_zero {d : ℕ} (hd : RelativeDimension sX d)
    (x : (fieldChowSituation k).S ⟶ X) (hx : x ≫ sX = 𝟙 _)
    (hxV : ∀ z, x.base z ∉ Set.range j.base) :
    haveI : IsProper x := isProper_of_comp_eq_id hx
    dimPartPieceGysin sV sX hj d d (d : ℤ)
        (chowCodimPushforward k (𝟙 _) sX x hx 0 d (chowCodimFundamental k (𝟙 _)) d) = 0 := by
  have : IsProper x := isProper_of_comp_eq_id hx
  have : IsIso (dimPart sX d).ι := isIso_dimPart_ι_of_relativeDimension _ hd
  obtain ⟨δU, hδU⟩ : ∃ δU : (fieldChowSituation k).S ⟶ (dimPart sX d).toScheme,
      δU ≫ (dimPart sX d).ι = x :=
    ⟨x ≫ inv (dimPart sX d).ι, by simp⟩
  have : IsProper δU := by
    have : IsProper (δU ≫ (dimPart sX d).ι) := by rw [hδU]; infer_instance
    exact IsProper.of_comp δU (dimPart sX d).ι
  have hpt : schemeDeltaDimension (fieldChowSituation k) (𝟙 (fieldChowSituation k).S) ≤
      (((d : ℤ) - d : ℤ) : EInt) := by
    rw [sub_self]
    exact Stacks.WeilCohomology.schemeDeltaDimension_le_of_relativeDimension (𝟙 _)
      (relativeDimension_of_isOpenImmersion (𝟙 _))
  -- the part of `[x]` on `X_d` is `(δU : Spec k ⟶ X_d)_* [Spec k]_0`
  have h1 : chowCodimPushforward k (𝟙 _) sX x hx 0 d (chowCodimFundamental k (𝟙 _)) d =
      properChowPushforward (fieldChowSituation k) ((δU ≫ (dimPart sX d).ι) ≫ sX)
        ((dimPart sX d).ι ≫ sX) δU (by simp [Category.assoc]) _
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
        (fundamentalChowClass (fieldChowSituation k) ((δU ≫ (dimPart sX d).ι) ≫ sX)
          ((d : ℤ) - (d : ℤ))) := by
    change chowGroupRestrict (fieldChowSituation k) sX ((dimPart sX d).ι ≫ sX)
        (dimPart sX d).ι rfl _
        (properChowPushforward (fieldChowSituation k) (𝟙 _) sX x hx _
          (properPushforwardDescends _ _ _ _ _ _)
          (chowCodimTotal k (𝟙 _) 0 _ (chowCodimFundamental k (𝟙 _)))) = _
    rw [chowCodimTotal_chowCodimFundamental (𝟙 _) (relativeDimension_of_isOpenImmersion (𝟙 _)),
      chowGroupRestrict_properChowPushforward (fieldChowSituation k) (𝟙 _) sX
        ((δU ≫ (dimPart sX d).ι) ≫ sX) ((dimPart sX d).ι ≫ sX) x hx (𝟙 _)
        (by rw [hδU, Category.id_comp, hx]) (dimPart sX d).ι rfl δU
        (by simp [Category.assoc]) (IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, hδU]⟩)
        _ _ (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _),
      chowGroupRestrict_fundamentalChowClass (fieldChowSituation k) (𝟙 _) _ (𝟙 _) _ _ hpt]
  rw [h1]
  change chowGroupDegreeEquiv _ _ _
    ((dimPartPieceGysinClass sV sX hj d d).capTargetHom _ _ _ _ _ _ _ _ _) = _
  rw [chowGroupDegreeEquiv_eq_iff_heq, BivariantClass.capTargetHom_apply]
  refine (dimPartPieceGysinClass_capTarget_heq sV sX hj d d _ _).trans ?_
  -- Stacks 0B76 (1): `j^!` commutes with the pushforward along `δU`
  rw [(smoothGysinClass (fieldChowSituation k) sV sX hj _).cap_properPushforward
    (dimPart sX d).ι δU (bivariantBaseChangeMap j (dimPart sX d).ι δU)
    (isPullback_bivariantBaseChangeMap j (dimPart sX d).ι δU)
    (by simp [bivariantBaseChangeMap]) _ _]
  -- the scheme-theoretic intersection `Z = V ×_X Spec k` is empty
  have : IsEmpty (pullback j (δU ≫ (dimPart sX d).ι) : Scheme.{u}) := by
    refine ⟨fun ξ ↦ hxV ((pullback.snd j (δU ≫ (dimPart sX d).ι)).base ξ)
      ⟨(pullback.fst j (δU ≫ (dimPart sX d).ι)).base ξ, ?_⟩⟩
    have hc : pullback.fst j (δU ≫ (dimPart sX d).ι) ≫ j =
        pullback.snd j (δU ≫ (dimPart sX d).ι) ≫ x :=
      pullback.condition.trans
        (congrArg (fun t ↦ pullback.snd j (δU ≫ (dimPart sX d).ι) ≫ t) hδU)
    exact congrArg (fun f : pullback j (δU ≫ (dimPart sX d).ι) ⟶ X ↦ f.base ξ) hc
  have hsub := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k)
    (pullback.fst j (δU ≫ (dimPart sX d).ι) ≫ sV)
  generalize (smoothGysinClass (fieldChowSituation k) sV sX hj _).cap
    (δU ≫ (dimPart sX d).ι) _ _ = c
  rw [Subsingleton.elim c 0, map_zero, map_zero]
  have key : ∀ a b : ℤ, a = b →
      (0 : chowGroup (fieldChowSituation k) (dimPartPieceBase sV sX j d d) a) ≍
        (0 : chowGroup (fieldChowSituation k) (dimPartPieceBase sV sX j d d) b) := by
    rintro a _ rfl
    rfl
  exact key _ _ (by ring)

/-- **The Gysin pullback along an open immersion of the class of a rational point in its image.**
Let `X` be smooth and separated over a field `k`, of constant dimension `d`, let `j : V ⟶ X` be an
open immersion and `x : Spec k ⟶ V` a `k`-rational point of `V`. Then the Gysin map of Stacks 0FF3
carries `[j ∘ x] ∈ CH^d(X)` to `[x] ∈ CH^d(V)`: the square with corners `Spec k`, `V`, `Spec k`,
`X` is cartesian of the expected dimension `0` (Stacks 0FF7). -/
theorem codimensionGysin_openImmersion_point {d : ℕ} (hd : RelativeDimension sX d)
    (x : (fieldChowSituation k).S ⟶ V) (hx : x ≫ sV = 𝟙 _) :
    haveI := isSeparated_of_openImmersion sX sV j hj
    haveI : IsProper x := isProper_of_comp_eq_id hx
    haveI : IsProper (x ≫ j) :=
      isProper_of_comp_eq_id (show (x ≫ j) ≫ sX = 𝟙 _ by rw [Category.assoc, hj, hx])
    codimensionGysin sV sX hj (d : ℤ)
        (chowCodimPushforward k (𝟙 _) sX (x ≫ j) (by rw [Category.assoc, hj, hx]) 0 d
          (chowCodimFundamental k (𝟙 _))) =
      chowCodimPushforward k (𝟙 _) sV x hx 0 d (chowCodimFundamental k (𝟙 _)) := by
  have hV := relativeDimension_of_openImmersion sX sV j hj hd
  funext e
  -- the parts `V_e`, `e ≠ d`, are empty
  by_cases he : e = d
  swap
  · have := isEmpty_dimPart_of_ne sV hV he
    exact (subsingleton_chowGroup_of_isEmpty _ _ _).elim _ _
  subst he
  apply (chowGroupDimPartPieceEquiv sV sX (f := j) e ((e : ℤ) - (e : ℕ))).injective
  funext ⟨e'⟩
  rw [chowGroupDimPartPieceEquiv_apply, chowGroupDimPartPieceEquiv_apply,
    chowGroupRestrict_codimensionGysin]
  -- the pieces `V_{d,e'}`, `e' ≠ d`, are empty
  by_cases he' : e' = e
  swap
  · have : IsEmpty (dimPartPiece sV sX j e e').toScheme :=
      ⟨fun y ↦ he' (eq_of_mem_dimPart sX hd y.2)⟩
    exact (subsingleton_chowGroup_of_isEmpty _ _ _).elim _ _
  subst he'
  exact dimPartPieceGysin_openImmersion_point sX sV j hj hd x hx

/-- **The Gysin pullback along an open immersion of the class of a rational point outside its
image is zero.** Let `X` be smooth and separated over a field `k`, of constant dimension `d`, let
`j : V ⟶ X` be an open immersion and `x : Spec k ⟶ X` a `k`-rational point of `X` not in the image
of `j`. Then the Gysin map of Stacks 0FF3 carries `[x] ∈ CH^d(X)` to `0`: the fibre product
`V ×_X Spec k` is empty. -/
theorem codimensionGysin_openImmersion_point_eq_zero {d : ℕ} (hd : RelativeDimension sX d)
    (x : (fieldChowSituation k).S ⟶ X) (hx : x ≫ sX = 𝟙 _)
    (hxV : ∀ z, x.base z ∉ Set.range j.base) :
    haveI : IsProper x := isProper_of_comp_eq_id hx
    codimensionGysin sV sX hj (d : ℤ)
        (chowCodimPushforward k (𝟙 _) sX x hx 0 d (chowCodimFundamental k (𝟙 _))) = 0 := by
  have hV := relativeDimension_of_openImmersion sX sV j hj hd
  funext e
  by_cases he : e = d
  swap
  · have := isEmpty_dimPart_of_ne sV hV he
    exact (subsingleton_chowGroup_of_isEmpty _ _ _).elim _ _
  subst he
  apply (chowGroupDimPartPieceEquiv sV sX (f := j) e ((e : ℤ) - (e : ℕ))).injective
  funext ⟨e'⟩
  rw [chowGroupDimPartPieceEquiv_apply, chowGroupDimPartPieceEquiv_apply,
    chowGroupRestrict_codimensionGysin]
  by_cases he' : e' = e
  swap
  · have : IsEmpty (dimPartPiece sV sX j e e').toScheme :=
      ⟨fun y ↦ he' (eq_of_mem_dimPart sX hd y.2)⟩
    exact (subsingleton_chowGroup_of_isEmpty _ _ _).elim _ _
  subst he'
  rw [dimPartPieceGysin_openImmersion_point_eq_zero sX sV j hj hd x hx hxV]
  exact (map_zero _).symm

end OpenImmersion

/-! ### Open and closed subschemes of a smooth projective scheme -/

/-- The inclusion of an open subscheme of a smooth projective scheme is an open immersion (instance
search does not see `(toScheme k).obj X` as a scheme). -/
theorem isOpenImmersion_clopen_ι (X : (SmoothProjectiveScheme k).FullSubcategory)
    (U : ((toScheme k).obj X).Opens) : IsOpenImmersion U.ι := by
  let Y : Scheme.{u} := (toScheme k).obj X
  let V : Y.Opens := U
  exact (inferInstance : IsOpenImmersion V.ι)

/-- **The Gysin pullback to an open and closed subscheme of the class of a rational point in it.**
For `X` smooth projective over `k` of constant dimension `d`, `U ⊆ X` open and closed and `x` a
`k`-rational point of `U`, the Gysin map of Stacks 0FF3 along `U ⟶ X` carries `[x] ∈ CH^d(X)` to
`[x] ∈ CH^d(U)`. -/
theorem codimensionGysin_clopen_pointChowClass_of_mem
    (X : (SmoothProjectiveScheme k).FullSubcategory) {d : ℕ} (hd : RelativeDimension X.obj.hom d)
    (U : ((toScheme k).obj X).Opens) (hU : IsClopen (U : Set ((toScheme k).obj X)))
    (x : Spec (.of k) ⟶ (toScheme k).obj (clopen X U hU))
    (hx : x ≫ (clopen X U hU).obj.hom = 𝟙 _) :
    haveI := locallyOfFiniteType_map (clopenInclusion X U hU)
    Stacks.Chow.codimensionGysin (clopen X U hU).obj.hom X.obj.hom
        (w (clopenInclusion X U hU)) (d : ℤ)
        (pointChowClass (x ≫ (toScheme k).map (clopenInclusion X U hU))
          (by rw [Category.assoc, w]; exact hx) d) =
      pointChowClass x hx d := by
  have : IsSeparated X.obj.hom := (isProjective X).isSeparated
  exact codimensionGysin_openImmersion_point X.obj.hom (clopen X U hU).obj.hom U.ι
    (hjo := isOpenImmersion_clopen_ι X U) (w (clopenInclusion X U hU)) hd x hx

/-- **The Gysin pullback to an open and closed subscheme of the class of a rational point outside
it is zero.** For `X` smooth projective over `k` of constant dimension `d`, `U ⊆ X` open and closed
and `x` a `k`-rational point of `X` not in `U`, the Gysin map of Stacks 0FF3 along `U ⟶ X` carries
`[x] ∈ CH^d(X)` to `0`. -/
theorem codimensionGysin_clopen_pointChowClass_of_not_mem
    (X : (SmoothProjectiveScheme k).FullSubcategory) {d : ℕ} (hd : RelativeDimension X.obj.hom d)
    (U : ((toScheme k).obj X).Opens) (hU : IsClopen (U : Set ((toScheme k).obj X)))
    (x : Spec (.of k) ⟶ (toScheme k).obj X) (hx : x ≫ X.obj.hom = 𝟙 _)
    (hxU : ∀ z, x.base z ∉ U) :
    haveI := locallyOfFiniteType_map (clopenInclusion X U hU)
    Stacks.Chow.codimensionGysin (clopen X U hU).obj.hom X.obj.hom
        (w (clopenInclusion X U hU)) (d : ℤ) (pointChowClass x hx d) = 0 := by
  have : IsSeparated X.obj.hom := (isProjective X).isSeparated
  refine codimensionGysin_openImmersion_point_eq_zero X.obj.hom (clopen X U hU).obj.hom U.ι
    (hjo := isOpenImmersion_clopen_ι X U) (w (clopenInclusion X U hU)) hd x hx
    fun z hz ↦ hxU z ?_
  obtain ⟨y, hy⟩ := hz
  rw [← hy]
  exact y.2

end Stacks.WeilDeRham

end
