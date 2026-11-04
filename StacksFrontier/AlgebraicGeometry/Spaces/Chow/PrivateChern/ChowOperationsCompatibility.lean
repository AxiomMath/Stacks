module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.FlatPullbackChow
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.TopSegreFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.FirstChernCapChow
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCapCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCapAdditive

/-!
# Compatibilities of the operations on Chow homology

In Situation 0EDT the operations on the Chow homology `CH_*(X) = ⨁_k CH_k(X)` of a good algebraic
space which enter the Chern classes, flat pullback, proper pushforward and the cap product with
the first Chern class of an invertible module, satisfy on `CH_*` the identities that chapter 82
proves for them on cycles:

* flat pullback commutes with proper pushforward along a cartesian square (Stacks 0EPD),
* flat pullback commutes with the cap product with `c₁` (Stacks 0EQR),
* flat pullbacks compose (Stacks 0EPA),
* the cap product with `c₁(ℒ)` only depends on `ℒ` up to isomorphism.

The Chow groups are those whose rational equivalences are indexed in the universe `u + 1`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.chowHomology_hom_ext`: homomorphisms out of `CH_*(X)` are
  determined on the classes of homogeneous cycles.
* `AlgebraicGeometry.Space.PrivateChern.flatPullbackChow_properPushforwardChow`: Stacks 0EPD.
* `AlgebraicGeometry.Space.PrivateChern.flatPullbackChow_firstChernCapChow`: Stacks 0EQR.
* `AlgebraicGeometry.Space.PrivateChern.flatPullbackChow_flatPullbackChow_of_comm`: Stacks 0EPA,
  for two factorizations of the same morphism.
* `AlgebraicGeometry.Space.PrivateChern.firstChernCapChow_congr_iso`: invariance of the cap
  product under isomorphism.

## References

* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
* [Stacks Project, Tag 0EPA](https://stacks.math.columbia.edu/tag/0EPA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.PrivateChern

variable (D : BaseSpaceDimensionSituation.{u})

section Classes

variable {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
  (hX : D.IsGood sX)

/-- **Homomorphisms out of the Chow homology are determined on classes of cycles.** -/
theorem chowHomology_hom_ext {M : Type*} [AddCommMonoid M]
    {φ ψ : chowHomology.{u, u + 1} D sX hX →+ M}
    (h : ∀ (k : ℤ) (b : CycleGroup D sX k),
      φ (DirectSum.of _ k (chowClass.{u + 1} D sX hX k b)) =
        ψ (DirectSum.of _ k (chowClass.{u + 1} D sX hX k b))) : φ = ψ :=
  DirectSum.addHom_ext fun k x => by
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
    exact h k b

/-- Equal composites of homomorphisms out of the Chow homology agree, if they agree on classes. -/
private theorem comp_apply_eq_of_chowClass {M N₁ N₂ : Type*} [AddCommMonoid M] [AddCommMonoid N₁]
    [AddCommMonoid N₂] {φ₁ : N₁ →+ M} {φ₂ : chowHomology.{u, u + 1} D sX hX →+ N₁}
    {ψ₁ : N₂ →+ M} {ψ₂ : chowHomology.{u, u + 1} D sX hX →+ N₂}
    (h : ∀ (k : ℤ) (b : CycleGroup D sX k),
      φ₁ (φ₂ (DirectSum.of _ k (chowClass.{u + 1} D sX hX k b))) =
        ψ₁ (ψ₂ (DirectSum.of _ k (chowClass.{u + 1} D sX hX k b))))
    (β : chowHomology.{u, u + 1} D sX hX) : φ₁ (φ₂ β) = ψ₁ (ψ₂ β) :=
  DFunLike.congr_fun (chowHomology_hom_ext (φ := φ₁.comp φ₂) (ψ := ψ₁.comp ψ₂) D sX hX h) β

/-- Classes of cycles with the same coefficients in equal degrees are the same element of the
Chow homology. -/
theorem of_chowClass_congr {a b : ℤ} (h : a = b) (x : CycleGroup D sX a) (y : CycleGroup D sX b)
    (hxy : x.1 = y.1) :
    DirectSum.of (fun k => chowGroup.{u + 1} D sX hX k) a (chowClass.{u + 1} D sX hX a x) =
      DirectSum.of (fun k => chowGroup.{u + 1} D sX hX k) b (chowClass.{u + 1} D sX hX b y) := by
  subst h
  obtain rfl : x = y := Subtype.ext hxy
  rfl

/-- The identification of Chow groups in equal degrees on the class of a cycle. -/
theorem chowGroupDegreeCongr_chowClass {a b : ℤ} (h : a = b) (x : CycleGroup D sX a) :
    chowGroupDegreeCongr.{u, u + 1} D sX hX h (chowClass.{u + 1} D sX hX a x) =
      chowClass.{u + 1} D sX hX b (cycleGroupCast D sX h x) := by
  subst h
  rfl

/-- Two cycles with the same class in the Chow group at the canonical embeddings have the same
class in `CH_k(X)`. -/
theorem chowClass_eq_of_chowClassCanonical_eq {k : ℤ} {x y : CycleGroup D sX k}
    (h : chowClassCanonical.{u + 1} D sX hX k x = chowClassCanonical.{u + 1} D sX hX k y) :
    chowClass.{u + 1} D sX hX k x = chowClass.{u + 1} D sX hX k y :=
  congrArg (chowGroupCanonicalToChowGroup.{u + 1} D sX hX k) h

/-- **The cap product with `c₁(𝒩)` on the class of a cycle**:
`c₁(𝒩) ∩ [β] = [c₁(𝒩) ∩ β]` for `β ∈ Z_{k+1}(X)`. -/
theorem firstChernCapChow_of_chowClass (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N) (k : ℤ)
    (b : CycleGroup D sX (k + 1)) :
    firstChernCapChow.{u, u + 1} D sX hX N hN
        (DirectSum.of _ (k + 1) (chowClass.{u + 1} D sX hX (k + 1) b)) =
      DirectSum.of (fun k => chowGroup.{u + 1} D sX hX k) k
        (chowClass.{u + 1} D sX hX k
          (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k) b)) := by
  rw [firstChernCapChow, gradedChowMap_of, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    chowGroupDegreeCongr_chowClass, chowDescend_chowClass _ _ _ _ _ _
      (respectsRationalEquivalence_firstChernCapCycleMap D sX hX N hN _)]
  have key : ∀ (j : ℤ) (hj : j = k) (h' : k + 1 = j + 1),
      DirectSum.of (fun k => chowGroup.{u + 1} D sX hX k) j
        (chowClass.{u + 1} D sX hX j (firstChernCapCycleMap D sX hX j
          (canonicalFirstChernRule D sX hX N hN j) (cycleGroupCast D sX h' b))) =
      DirectSum.of (fun k => chowGroup.{u + 1} D sX hX k) k
        (chowClass.{u + 1} D sX hX k
          (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k) b)) := by
    rintro j rfl h'
    rfl
  exact key _ (by omega) _

/-- **The cap product with `c₁` depends on the invertible module up to isomorphism.** -/
theorem firstChernCapChow_congr_iso (N N' : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (hN' : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N')
    (e : N ≅ N') :
    firstChernCapChow.{u, u + 1} D sX hX N hN = firstChernCapChow.{u, u + 1} D sX hX N' hN' := by
  refine chowHomology_hom_ext D sX hX fun k b => ?_
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [firstChernCapChow_of_chowClass, firstChernCapChow_of_chowClass]
  exact congrArg _ (canonicalFirstChernCap_congr_iso hX N N' hN hN' e j b)

end Classes

section FlatPullback

variable {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
  (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX)
  (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
  (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-- Flat pullback on the class of a cycle, `f^*[β] = [f^*β]`, graded in any degree `n = k + r`. -/
theorem flatPullbackChow_of_chowClass_eq (k n : ℤ) (hkn : k + (r : ℤ) = n)
    (b : CycleGroup D sY k) :
    flatPullbackChow.{u, u + 1} D sX hX sY hY f hbase r hflat hr
        (DirectSum.of _ k (chowClass.{u + 1} D sY hY k b)) =
      DirectSum.of (fun k => chowGroup.{u + 1} D sX hX k) n
        (chowClass.{u + 1} D sX hX n
          (flatPullbackMap D sX hX sY hY f hbase r hflat hr k n hkn b)) :=
  (flatPullbackChow_of_chowClass.{u, 0} D sX hX sY hY f hbase r hflat hr k b).trans
    (of_chowClass_congr D sX hX hkn _ _ rfl)

/-- **Stacks 0EQR on Chow homology**: `f^*(c₁(ℒ) ∩ β) = c₁(f^*ℒ) ∩ f^*β`. -/
theorem flatPullbackChow_firstChernCapChow (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleModule (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (β : chowHomology.{u, u + 1} D sY hY) :
    flatPullbackChow.{u, u + 1} D sX hX sY hY f hbase r hflat hr
        (firstChernCapChow.{u, u + 1} D sY hY L hL β) =
      firstChernCapChow.{u, u + 1} D sX hX (pullbackLine D sX hX sY hY f L)
        (isInvertibleModule_pullbackLine D sX hX sY hY f L hL)
        (flatPullbackChow.{u, u + 1} D sX hX sY hY f hbase r hflat hr β) := by
  refine comp_apply_eq_of_chowClass D sY hY (fun k b => ?_) _
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [firstChernCapChow_of_chowClass, flatPullbackChow_of_chowClass_eq D sX hX sY hY f hbase r
      hflat hr j (j + r) rfl,
    flatPullbackChow_of_chowClass_eq D sX hX sY hY f hbase r hflat hr (j + 1) (j + r + 1)
      (by ring), firstChernCapChow_of_chowClass]
  refine congrArg _ (chowClass_eq_of_chowClassCanonical_eq D sX hX ?_)
  exact chowClassCanonical_flatPullbackMap_firstChernCapCycleMap D sX hX sY hY f hbase r hflat hr
    L hL j b

end FlatPullback

section BaseChange

variable {X' X Y' Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX' : X' ⟶ D.space) (hX' : D.IsGood sX') (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY' : Y' ⟶ D.space) (hY' : D.IsGood sY') (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hg'base : g' ≫ sX = sX') (hf'base : f' ≫ sY' = sX') (hfbase : f ≫ sY = sX)
    (hgbase : g ≫ sY = sY') (r : ℕ)
    (hgflat : IsFlat D.site D.base D.base_mem g)
    (hgr : HasRelativeDimension r D.site D.base D.base_mem g)
    (hg'flat : IsFlat D.site D.base D.base_mem g')
    (hg'r : HasRelativeDimension r D.site D.base D.base_mem g')

/-- **Stacks 0EPD on Chow homology**: for a cartesian square with `f` proper and `g` flat of
relative dimension `r`, `g^* f_* = f'_* g'^*`. -/
theorem flatPullbackChow_properPushforwardChow (sq : IsPullback g' f' f g)
    (hfproper : IsProper D.site D.base D.base_mem f)
    (hf'proper : IsProper D.site D.base D.base_mem f') (β : chowHomology.{u, u + 1} D sX hX) :
    flatPullbackChow.{u, u + 1} D sY' hY' sY hY g hgbase r hgflat hgr
        (properPushforwardChow.{u, u + 1} D sX hX sY hY f hfbase hfproper β) =
      properPushforwardChow.{u, u + 1} D sX' hX' sY' hY' f' hf'base hf'proper
        (flatPullbackChow.{u, u + 1} D sX' hX' sX hX g' hg'base r hg'flat hg'r β) := by
  refine comp_apply_eq_of_chowClass D sX hX (fun k b => ?_) _
  rw [properPushforwardChow_of, chowGroupProperPushforward_chowClass,
    flatPullbackChow_of_chowClass_eq D sY' hY' sY hY g hgbase r hgflat hgr k (k + r) rfl,
    flatPullbackChow_of_chowClass_eq D sX' hX' sX hX g' hg'base r hg'flat hg'r k (k + r) rfl,
    properPushforwardChow_of, chowGroupProperPushforward_chowClass]
  exact congrArg _ (congrArg _ (flatPullback_properPushforward_unconditional D sX' hX' sX hX sY'
    hY' sY hY hg'base hf'base hfbase hgbase r hgflat hgr sq hfproper k (k + r) rfl b))

end BaseChange

section Composition

variable {X Y Y' Z : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (sY' : Y' ⟶ D.space) (hY' : D.IsGood sY') (sZ : Z ⟶ D.space) (hZ : D.IsGood sZ)

/-- **Stacks 0EPA on Chow homology, for two factorizations.** If `f ≫ g = f' ≫ g'` with `f`, `g`,
`f'`, `g'` flat of relative dimensions `r`, `s`, `r'`, `s'` and `r + s = r' + s'`, then
`f^* g^* = f'^* g'^*`. -/
theorem flatPullbackChow_flatPullbackChow_of_comm {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X ⟶ Y'}
    {g' : Y' ⟶ Z} (hcomm : f ≫ g = f' ≫ g') (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY)
    (hf' : f' ≫ sY' = sX) (hg' : g' ≫ sZ = sY') (r s r' s' : ℕ) (hrs : r + s = r' + s')
    (hff : IsFlat D.site D.base D.base_mem f)
    (hfr : HasRelativeDimension r D.site D.base D.base_mem f)
    (hgf : IsFlat D.site D.base D.base_mem g)
    (hgs : HasRelativeDimension s D.site D.base D.base_mem g)
    (hff' : IsFlat D.site D.base D.base_mem f')
    (hfr' : HasRelativeDimension r' D.site D.base D.base_mem f')
    (hgf' : IsFlat D.site D.base D.base_mem g')
    (hgs' : HasRelativeDimension s' D.site D.base D.base_mem g')
    (α : chowHomology.{u, u + 1} D sZ hZ) :
    flatPullbackChow.{u, u + 1} D sX hX sY hY f hf r hff hfr
        (flatPullbackChow.{u, u + 1} D sY hY sZ hZ g hg s hgf hgs α) =
      flatPullbackChow.{u, u + 1} D sX hX sY' hY' f' hf' r' hff' hfr'
        (flatPullbackChow.{u, u + 1} D sY' hY' sZ hZ g' hg' s' hgf' hgs' α) := by
  refine comp_apply_eq_of_chowClass D sZ hZ (fun k b => ?_) _
  rw [flatPullbackChow_of_chowClass_eq D sY hY sZ hZ g hg s hgf hgs k (k + s) rfl,
    flatPullbackChow_of_chowClass_eq D sX hX sY hY f hf r hff hfr (k + s) (k + s + r) rfl,
    flatPullbackChow_of_chowClass_eq D sY' hY' sZ hZ g' hg' s' hgf' hgs' k (k + s') rfl,
    flatPullbackChow_of_chowClass_eq D sX hX sY' hY' f' hf' r' hff' hfr' (k + s') (k + s' + r')
      rfl]
  refine of_chowClass_congr D sX hX (by omega) _ _ ?_
  have e₁ := congrArg (fun φ => (φ b).1) (flatPullbackMap_comp D sX hX sY hY sZ hZ f g hf hg
    r s hff hfr hgf hgs k (k + s + r) (by push_cast; omega))
  have e₂ := congrArg (fun φ => (φ b).1) (flatPullbackMap_comp D sX hX sY' hY' sZ hZ f' g' hf' hg'
    r' s' hff' hfr' hgf' hgs' k (k + s' + r') (by push_cast; omega))
  simp only [AddMonoidHom.comp_apply] at e₁ e₂
  rw [← e₁, ← e₂]
  exact flatPullbackMap_coe_congr D sX hX sZ hZ hcomm hrs _ _ _ _ _ _ k _ _ _ _ b

end Composition

end AlgebraicGeometry.Space.PrivateChern

end
