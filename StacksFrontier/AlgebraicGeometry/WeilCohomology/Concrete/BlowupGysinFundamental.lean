module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DimensionClassCodimension
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupExcess
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionGysinTransversal
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.BlowupFormulaHomogeneous
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBaseUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionDeformationTop

/-!
# The Gysin map of the blowing up on the class of the centre

Let `i : Z ⟶ X` be a closed immersion of smooth projective schemes over a field `k`, with `X` of
dimension `n` and `Z` of dimension `e = n - r`, `r ≥ 1`. Let `b : X' ⟶ X` be the blowing up of `X`
in `Z`, `j : E ⟶ X'` the exceptional divisor, `π : E ⟶ Z`, and
`𝓕 = Ker(π^*𝒞_{Z/X} ⟶ 𝒞_{E/X'})` the excess bundle of Tag 0FVA, of rank `r - 1`. This file proves
the step

  `b^![Z] = j_*(c_{r-1}(𝓕^∨) ∩ [E])`   in `CH^r(X')`

of the proof of [Stacks, Tag 0FIH]: the blow up formula of Tag 0FVA on the fundamental class of the
centre, with the Gysin map `b^!` of Stacks 0FF3 graded by codimension
(`Stacks.Chow.codimensionGysin`) and the class `j_*(c_{r-1}(𝓕^∨) ∩ [E]_{n-1}) ∈ CH_e(X')` read in
codimension `r` (`Stacks.WeilCohomology.chowGroupToCodimension`).

## The proof

On the part `X'_n = X'` of `X'` the codimension-graded Gysin map is the cap product with the Gysin
class of `b` at the test scheme `X_n ⟶ X` (`Stacks.Chow.dimPartPieceGysinClass_capTarget_heq`),
and `[Z]` there is the restriction of `i_*[Z]_e`. A bivariant class commutes with restricting its
test scheme along an open immersion (Stacks 0B76 (2) in relative dimension zero,
`Stacks.Chow.BivariantClass.chowGroupRestrict_capTarget`), so this is the restriction of
`b^! ∩ i_*[Z]_e`, which the blow up formula computes
(`Stacks.Chow.capTarget_lciGysinClass_blowUpToBase_pushforward`): `𝓕^∨` has rank `r - 1` and `π`
relative dimension `r - 1`.

## Main results

* `Stacks.Chow.BivariantClass.chowGroupRestrict_capTarget`: restricting `c ∩ α` to `X ×_Y U` is
  capping `α|_U` at the test scheme `U ⟶ Y`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.capTarget_smoothGysinClass_blowupHom`:
  `b^!(i_*[Z]_e) = j_*(c_{r-1}(𝓕^∨) ∩ [E]_{n-1})` in `CH_e(X')`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.codimensionGysin_blowupHom_closedSubschemeClass`:
  `b^![Z] = j_*(c_{r-1}(𝓕^∨) ∩ [E])` in `CH^r(X')`.

## References

* [Stacks Project, Tag 0FIH](https://stacks.math.columbia.edu/tag/0FIH)
* [Stacks Project, Tag 0FVA](https://stacks.math.columbia.edu/tag/0FVA)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite locally free module of constant rank `s` has rank `s` at every point. -/
theorem finiteLocallyFreeRank_eq_of_isFiniteLocallyFreeOfRank {X : Scheme.{u}} (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (s : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E s] (x : X) :
    finiteLocallyFreeRank E x = s := by
  have hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (toRingSheafModule E) s := hE
  obtain ⟨q, hq, hcard⟩ := hE'.exists_isFiniteLocallyFreeOfRankData
  have hx : x ∈ ⨆ k, q.X k := by
    rw [(Opens.coversTop_iff _ q.X).mp q.coversTop]; trivial
  rw [TopologicalSpace.Opens.mem_iSup] at hx
  obtain ⟨k, hk⟩ := hx
  have h := Stacks.SheafOfModules.finiteLocallyFreeRank_eq_card (toRingSheafModule E)
    (LocallyFreeRank.scheme_stalksNontrivial X) q hq k x hk
  rw [Nat.card_congr (hcard k).some, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact h

/-- A finite locally free module of constant rank `s` has rank `s` on every connected component. -/
theorem rankOnConnectedComponent_eq_of_isFiniteLocallyFreeOfRank {X : Scheme.{u}}
    (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E s]
    (a : _root_.ConnectedComponents X) : rankOnConnectedComponent E a = s := by
  obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe a
  exact finiteLocallyFreeRank_eq_of_isFiniteLocallyFreeOfRank E s x

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.Chow

/-- **Restricting a cap product on the target to the base change of an open subscheme.** For a
bivariant class `c ∈ A^p(X ⟶ Y)`, an open immersion `ι : U ⟶ Y` and `α ∈ CH_k(Y)`, the
restriction of `c ∩ α ∈ CH_{k-p}(X)` to `X ×_Y U` is `c ∩ α|_U`, the cap of `c` at the test
scheme `ι`: Stacks 0B76 (2) for the open immersion `ι`, flat of relative dimension zero, read
through `X ×_Y Y ≅ X`. -/
theorem BivariantClass.chowGroupRestrict_capTarget {C : ChowSituation.{u}} {G : GysinSystem C}
    {X Y U : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ}
    (c : BivariantClass C G sX sY f hf p) (ι : U ⟶ Y) [IsOpenImmersion ι] (k : ℤ)
    (α : chowGroup C sY k) :
    chowGroupRestrict C sX (pullback.fst f ι ≫ sX) (pullback.fst f ι) rfl (k - p)
        (c.capTarget C G sX sY f hf p k α) =
      c.cap ι k (chowGroupRestrict C sY (ι ≫ sY) ι rfl k α) := by
  let v' : pullback f ι ⟶ pullback f (𝟙 Y) := pullback.fst f ι ≫ (pullbackIdIso f).hom
  have : IsOpenImmersion v' := by dsimp only [v']; infer_instance
  have hv'fst : v' ≫ pullback.fst f (𝟙 Y) = pullback.fst f ι := by
    simp only [v', Category.assoc, pullbackIdIso_hom_fst, Category.comp_id]
  have hsq : IsPullback (pullback.snd f ι) v' ι (pullback.snd f (𝟙 Y)) :=
    (IsPullback.of_hasPullback f ι).flip.of_iso (Iso.refl _) (Iso.refl _) (pullbackIdIso f)
      (Iso.refl _) (by simp) (by simp [v']) (by simp) (by simp)
  have hcap := BivariantClass.cap_chowGroupRestrict C G sX sY f hf p c (𝟙 Y) ι ι
    (Category.comp_id ι) v' hsq hv'fst k
    (by rw [Category.id_comp]) (by rw [← Category.assoc, hv'fst])
    (chowGroupCongr C (Category.id_comp sY).symm k α)
  rw [BivariantClass.capTarget,
    chowPushforwardOfIso_eq_chowGroupRestrict C _ _ (pullbackIdIso f).inv _ (pullbackIdIso f).hom
      (Iso.hom_inv_id _), chowGroupRestrict_comp]
  refine (DFunLike.congr_fun (chowGroupRestrict_congr C _ _ _ _ _ v' rfl
    (by rw [← Category.assoc, hv'fst])) _).trans (hcap.trans ?_)
  congr 1

end Stacks.Chow

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

open Stacks.Chow
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf)

variable {k : Type u} [Field k] {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
  [IsClosedImmersion i.hom.left]

variable {n e r : ℕ} (hX : RelativeDimension X.obj.hom n) (hZ : RelativeDimension Z.obj.hom e)
  (hr : e + r = n) (hr0 : 0 < r)

include hX hZ hr hr0 in
/-- **The blow up formula on the fundamental class of the centre: `b^!(i_*[Z]_e) =
j_*(c_{r-1}(𝓕^∨) ∩ [E]_{n-1})`** in `CH_e(X')`, for `X` of dimension `n`, `Z` of dimension `e` and
`r = n - e ≥ 1`: the degree-`0` Gysin class of the blowing up `b` (Stacks 0FF3) capped with the
pushforward of the fundamental class of `Z` (Tag 0FVA,
`Stacks.Chow.capTarget_lciGysinClass_blowUpToBase_pushforward`, with `𝓕^∨` of rank `r - 1` and `π`
of relative dimension `r - 1`). -/
theorem capTarget_smoothGysinClass_blowupHom :
    (smoothGysinClass (fieldChowSituation k) (blowupObj i).obj.hom X.obj.hom
        (Over.w (blowupHom i).hom) 0).capTarget (fieldChowSituation k)
        (gysinSystemOfInvertible _) _ _ _ _ 0 e
        (properChowPushforward (fieldChowSituation k) (i.hom.left ≫ X.obj.hom) X.obj.hom
          i.hom.left rfl e
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
          (fundamentalChowClass (fieldChowSituation k) (i.hom.left ≫ X.obj.hom) e)) ≍
      properChowPushforward (fieldChowSituation k) (exceptionalObj i).obj.hom
        (blowupObj i).obj.hom (exceptionalHom i).hom.left (Over.w (exceptionalHom i).hom)
        (((n - 1 : ℕ) : ℤ) - ((r - 1 : ℕ) : ℤ))
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
        (excessChernCap i r ((n - 1 : ℕ) : ℤ)) := by
  have hi := isRegularImmersion_of_isClosedImmersion i
  have hG := gysinMapExists_blowupHom i
  have : IsLocallyNoetherian (Stacks.Blowup.blowUp i.hom.left.ker) :=
    isLocallyNoetherian (blowupObj i)
  have : IsLocallyNoetherian
      (Limits.pullback (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left) :=
    isLocallyNoetherian (exceptionalObj i)
  have hFr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (excessConormal i) (r - 1) := by
    have h := isFiniteLocallyFreeOfRank_excessConormal i hX hZ (by omega)
    rwa [show n - e - 1 = r - 1 by omega] at h
  have := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
    (excessConormal i) (r - 1) hFr
  have hF : ∀ a, Scheme.Modules.rankOnConnectedComponent
      (dualSheaf (excessConormal i)) a = r - 1 :=
    fun a ↦ Scheme.Modules.rankOnConnectedComponent_eq_of_isFiniteLocallyFreeOfRank _ _ a
  have hπ : RelativeDimension
      (pullback.snd (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left) (r - 1) := by
    have h := relativeDimension_exceptionalProj i hX hZ
    rwa [show n - 1 - e = r - 1 by omega] at h
  have hdim : schemeDeltaDimension (fieldChowSituation k) (i.hom.left ≫ X.obj.hom) ≤
      ((e : ℤ) : EInt) := by
    have key : ∀ (q : Z.obj.left ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType q] [Flat q],
        q = Z.obj.hom → schemeDeltaDimension (fieldChowSituation k) q ≤ ((e : ℤ) : EInt) := by
      rintro q _ _ rfl
      exact schemeDeltaDimension_le_of_relativeDimension Z.obj.hom hZ
    exact key _ (Over.w i.hom)
  have h := capTarget_lciGysinClass_blowUpToBase_pushforward (fieldChowSituation k) i.hom.left hi
    X.obj.hom hG (r - 1) hF hπ e hdim
  refine h.trans ?_
  have hsE : pullback.fst (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left ≫
      Stacks.Blowup.blowUpToBase i.hom.left.ker ≫ X.obj.hom = (exceptionalObj i).obj.hom := by
    show _ = pullback.snd _ _ ≫ Z.obj.hom
    rw [pullback.condition_assoc, Over.w i.hom]
  have : LocallyOfFiniteType
      (X := Limits.pullback (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left)
      (Y := (fieldChowSituation k).S) (exceptionalObj i).obj.hom :=
    (inferInstance : LocallyOfFiniteType (exceptionalObj i).obj.hom)
  have : IsProper (X := Limits.pullback (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left)
      (Y := (blowupObj i).obj.left)
      (pullback.fst (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left) :=
    (inferInstance : IsProper (exceptionalHom i).hom.left)
  refine properChowPushforward_heq_of_morphism_eq (fieldChowSituation k)
    (A := Limits.pullback (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left)
    (B := (blowupObj i).obj.left) (sB := (blowupObj i).obj.hom)
    (pullback.fst (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left)
    (pullback.fst (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left) rfl hsE _ _ (by omega)
    _ _ ?_
  have key : ∀ (q : (exceptionalObj i).obj.left ⟶ (fieldChowSituation k).S)
      [LocallyOfFiniteType q] (_ : q = (exceptionalObj i).obj.hom) (m m' : ℤ) (_ : m = m'),
      chowCohomologyCap (fieldChowSituation k) (gysinSystemOfInvertible _) q ((r - 1 : ℕ) : ℤ)
          (totalChernOfFiniteLocallyFree (fieldChowSituation k) q (dualSheaf (excessConormal i))
            (r - 1)) m (fundamentalChowClass (fieldChowSituation k) q m) ≍
        excessChernCap i r m' := by
    rintro q _ rfl m m' rfl
    rfl
  refine @key _ (show LocallyOfFiniteType (pullback.fst (Stacks.Blowup.blowUpToBase
      i.hom.left.ker) i.hom.left ≫ Stacks.Blowup.blowUpToBase i.hom.left.ker ≫ X.obj.hom) from
    inferInstance) hsE _ _ ?_
  omega

include hX hZ hr hr0 in
/-- **`b^![Z]` on the part `X'_n` of `X'`, over the part `X_n` of `X`**: the Gysin map of the
blowing up on the piece `X'_{n,n} = X'_n ∩ b⁻¹(X_n)` (`Stacks.Chow.dimPartPieceGysin`) carries the
component of `[Z]` on `X_n` to the restriction of `j_*(c_{r-1}(𝓕^∨) ∩ [E]_{n-1})` to the piece. -/
theorem dimPartPieceGysin_blowupHom_closedSubschemeClass :
    dimPartPieceGysin (blowupObj i).obj.hom X.obj.hom (Over.w (blowupHom i).hom) n n (r : ℤ)
        (closedSubschemeClass X.obj.hom i.hom.left (r : ℤ) n) ≍
      chowGroupRestrict (fieldChowSituation k) (blowupObj i).obj.hom
        (dimPartPieceBase (blowupObj i).obj.hom X.obj.hom (blowupHom i).hom.left n n)
        ((dimPartPiece (blowupObj i).obj.hom X.obj.hom (blowupHom i).hom.left n n).ι ≫
          (dimPart (blowupObj i).obj.hom n).ι) (by rw [Category.assoc])
        (((n - 1 : ℕ) : ℤ) - ((r - 1 : ℕ) : ℤ))
        (properChowPushforward (fieldChowSituation k) (exceptionalObj i).obj.hom
          (blowupObj i).obj.hom (exceptionalHom i).hom.left (Over.w (exceptionalHom i).hom)
          (((n - 1 : ℕ) : ℤ) - ((r - 1 : ℕ) : ℤ))
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
          (excessChernCap i r ((n - 1 : ℕ) : ℤ))) := by
  -- the class `[Z]` on `X_n` is the restriction of `i_*[Z]_{n-r}`
  have hβ : closedSubschemeClass X.obj.hom i.hom.left (r : ℤ) n =
      chowGroupRestrict (fieldChowSituation k) X.obj.hom ((dimPart X.obj.hom n).ι ≫ X.obj.hom)
        (dimPart X.obj.hom n).ι rfl ((n : ℤ) - r)
        (properChowPushforward (fieldChowSituation k) (i.hom.left ≫ X.obj.hom) X.obj.hom
          i.hom.left rfl ((n : ℤ) - r)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
          (fundamentalChowClass (fieldChowSituation k) (i.hom.left ≫ X.obj.hom)
            ((n : ℤ) - r))) := by
    rw [closedSubschemeClass_apply,
      mk_cycleAssociatedToClosedSubscheme_eq_properChowPushforward (fieldChowSituation k)
        X.obj.hom i.hom.left (i.hom.left ≫ X.obj.hom) rfl _
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)]
  -- `b^!` on the piece is `b^!` capped at the test scheme `X_n`, restricted to the piece
  have hL := dimPartPieceGysinClass_capTarget_heq (blowupObj i).obj.hom X.obj.hom
    (Over.w (blowupHom i).hom) n n ((n : ℤ) - r)
    (closedSubschemeClass X.obj.hom i.hom.left (r : ℤ) n)
  rw [hβ, ← BivariantClass.chowGroupRestrict_capTarget, chowGroupRestrict_comp,
    chowGroupRestrict_congr (fieldChowSituation k) _ _ _ _ _
      ((dimPartPiece (blowupObj i).obj.hom X.obj.hom (blowupHom i).hom.left n n).ι ≫
        (dimPart (blowupObj i).obj.hom n).ι)
      (dimPartPieceToPullback_fst _ _ _ n n) (by rw [Category.assoc])] at hL
  refine (chowGroupDegreeEquiv_heq _ _ _ _).trans ((hβ ▸ hL).trans ?_)
  -- `b^! ∩ i_*[Z]_{n-r}` is the blow up formula
  have hdeg : ∀ (q : ℤ) (_ : q = 0) (m : ℤ) (_ : m = e),
      (smoothGysinClass (fieldChowSituation k) (blowupObj i).obj.hom X.obj.hom
          (Over.w (blowupHom i).hom) q).capTarget (fieldChowSituation k)
          (gysinSystemOfInvertible _) _ _ _ _ q m
          (properChowPushforward (fieldChowSituation k) (i.hom.left ≫ X.obj.hom) X.obj.hom
            i.hom.left rfl m
            (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
            (fundamentalChowClass (fieldChowSituation k) (i.hom.left ≫ X.obj.hom) m)) ≍
        (smoothGysinClass (fieldChowSituation k) (blowupObj i).obj.hom X.obj.hom
          (Over.w (blowupHom i).hom) 0).capTarget (fieldChowSituation k)
          (gysinSystemOfInvertible _) _ _ _ _ 0 e
          (properChowPushforward (fieldChowSituation k) (i.hom.left ≫ X.obj.hom) X.obj.hom
            i.hom.left rfl e
            (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
            (fundamentalChowClass (fieldChowSituation k) (i.hom.left ≫ X.obj.hom) e)) := by
    rintro q rfl m rfl
    rfl
  exact chowGroupRestrict_heq_of_heq (fieldChowSituation k) _ _ _ _ (by omega) _ _
    ((hdeg _ (by ring) _ (by omega)).trans (capTarget_smoothGysinClass_blowupHom i hX hZ hr hr0))

include hX hZ hr hr0 in
/-- **`b^![Z] = j_*(c_{r-1}(𝓕^∨) ∩ [E])` in `CH^r(X')`** (proof of Lemma 0FIH, the codimension
form of Tag 0FVA). Let `i : Z ⟶ X` be a closed immersion of smooth projective schemes over `k`,
`X` of dimension `n` and `Z` of dimension `e`, so that `Z` has codimension `r = n - e ≥ 1`. The
Gysin map of Stacks 0FF3 of the blowing up `b : X' ⟶ X`, graded by codimension, carries the class
`[Z] ∈ CH^r(X)` to the class `j_*(c_{r-1}(𝓕^∨) ∩ [E]_{n-1})` of dimension
`(n - 1) - (r - 1) = e`, read in codimension `r` on `X'`, where `j : E ⟶ X'` is the exceptional
divisor and `𝓕` the excess bundle of Tag 0FVA (`excessChernCap`). -/
theorem codimensionGysin_blowupHom_closedSubschemeClass :
    codimensionGysin (blowupObj i).obj.hom X.obj.hom (Over.w (blowupHom i).hom) (r : ℤ)
        (closedSubschemeClass X.obj.hom i.hom.left (r : ℤ)) =
      chowGroupToCodimension (blowupObj i).obj.hom (((n - 1 : ℕ) : ℤ) - ((r - 1 : ℕ) : ℤ))
        (r : ℤ)
        (properChowPushforward (fieldChowSituation k) (exceptionalObj i).obj.hom
          (blowupObj i).obj.hom (exceptionalHom i).hom.left (Over.w (exceptionalHom i).hom)
          (((n - 1 : ℕ) : ℤ) - ((r - 1 : ℕ) : ℤ))
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
          (excessChernCap i r ((n - 1 : ℕ) : ℤ))) := by
  have hX' := relativeDimension_blowupObj i hX
  funext d
  by_cases hd : d = n
  swap
  · have := isEmpty_dimPart_of_ne (blowupObj i).obj.hom hX' hd
    have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k)
      (partBase (blowupObj i).obj.hom d) ((d : ℤ) - r)
    exact Subsingleton.elim _ _
  subst d
  refine (chowGroupDimPartPieceEquiv (blowupObj i).obj.hom X.obj.hom (f := (blowupHom i).hom.left)
    n ((n : ℤ) - r)).injective (funext fun t ↦ ?_)
  obtain ⟨t⟩ := t
  rw [chowGroupDimPartPieceEquiv_apply, chowGroupDimPartPieceEquiv_apply,
    chowGroupRestrict_codimensionGysin]
  by_cases ht : t = n
  swap
  · have hemp := isEmpty_dimPart_of_ne X.obj.hom hX ht
    have : IsEmpty (dimPartPiece (blowupObj i).obj.hom X.obj.hom (blowupHom i).hom.left n
        t).toScheme := ⟨fun w ↦ hemp.false ⟨_, w.2⟩⟩
    have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k)
      (dimPartPieceBase (blowupObj i).obj.hom X.obj.hom (blowupHom i).hom.left n t)
      ((n : ℤ) - r)
    exact Subsingleton.elim _ _
  subst t
  have hM : ((n - 1 : ℕ) : ℤ) - ((r - 1 : ℕ) : ℤ) = (n : ℤ) - r := by omega
  refine eq_of_heq ((dimPartPieceGysin_blowupHom_closedSubschemeClass i hX hZ hr hr0).trans ?_)
  refine HEq.symm ((chowGroupRestrict_heq_of_heq (fieldChowSituation k) _ _ _ rfl hM.symm _ _
    (chowGroupToCodimension_apply_heq _ _ _ _ n hM)).trans ?_)
  rw [chowGroupRestrict_comp]

end Stacks.WeilCohomology.SmoothProjectiveScheme

end
