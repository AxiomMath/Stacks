module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleClassProperCover
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.HilbertBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.LimitDescentCore
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Relative
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.Absolute
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Relative cycles over a quasi-compact and quasi-separated base

Let `S` be a quasi-compact and quasi-separated scheme, let `f : X ⟶ S` be of finite presentation,
let `r ≥ 0` and let `α` be a family of `r`-cycles on the fibres of `X/S`. Over such a base the
valuative definition of a relative cycle is replaced by two conditions which, by
[Tag 0H6W](https://stacks.math.columbia.edu/tag/0H6W), are equivalent:

1. `α` is the base change of a relative `r`-cycle `α₀ ∈ z(X₀/S₀, r)` along a cartesian square
   whose right-hand column `X₀ ⟶ S₀` is a finite type morphism of Noetherian schemes;
2. there is a completely decomposed proper morphism `g : S' ⟶ S` of finite presentation such that
   `g^*α` lies in the image of the cycle class map of
   [Tag 0H6V](https://stacks.math.columbia.edu/tag/0H6V).

## Main definitions

* `Stacks.Chow.IsCartesianBaseChange` — the relation "`α` is the base change of `α₀` through the
  cartesian square", read on the fibres of `f` through an isomorphism `X ≅ X₀ ×_{S₀} S` over `S`.
* `Stacks.Chow.ComesFromNoetherianBase` — condition (1) of Tag 0H6W.
* `Stacks.Chow.HasCompletelyDecomposedCycleClassCover` — condition (2) of Tag 0H6W.

## Main results

* `Stacks.Chow.pullbackInCycleClassImage_of_isCartesianBaseChange` — membership of a base change
  in the image of the cycle class map passes through the cartesian square of condition (1).
* `Stacks.Chow.hasCompletelyDecomposedCycleClassCover_of_comesFromNoetherianBase` — the
  implication (1) ⟹ (2).
* `Stacks.Chow.comesFromNoetherianBase_of_hasCompletelyDecomposedCycleClassCover` — the
  implication (2) ⟹ (1).
* `Stacks.Chow.comesFromNoetherianBase_iff_hasCompletelyDecomposedCycleClassCover` — **Stacks
  Project, Lemma 0H6W**.

## Implementation notes

The source's "finite presentation" is locally of finite presentation, quasi-compact and
quasi-separated; Mathlib's `LocallyOfFinitePresentation` together with `QuasiCompact` lacks the
last, so `f` carries `QuasiSeparated f` explicitly. It is needed: condition (1) makes `f` a base
change of a morphism of Noetherian schemes, hence quasi-separated, while condition (2) holds for
the zero family on any `X` of finite presentation in Mathlib's weaker sense. For the cover `g` of
condition (2) the two notions agree, `g` being proper.

The cartesian square of condition (1) is recorded as an isomorphism `e : X ≅ X₀ ×_{S₀} S`
together with the identity `e.hom ≫ pr₂ = f` making it an isomorphism over `S`, and the base
change relation reads `h^*α₀` on the fibres of `f` through `e` with
`Stacks.Chow.fiberCycleRestrict`, since the two families live over the two isomorphic schemes `X`
and `X₀ ×_{S₀} S`.

The implication (1) ⟹ (2) is the source's: over the Noetherian base `S₀`, Tag 0H59 gives a
proper, completely decomposed `q : S₀' ⟶ S₀` whose pullback of `α₀` is a cycle class; `S₀'` is
Noetherian, so `q` is of finite presentation; and `S' = S ×_{S₀} S₀'` is the cover asked for. The
base change of the cycle class to `S'` is computed with Tag 0H4P, part (1), and the transport of
members of `Hilb` along the canonical isomorphisms of fibre products.

The implication (2) ⟹ (1) writes `S` as a limit of schemes of finite type over `ℤ`
(Limits, Proposition 01ZA), descends `X` to a stage (Limits, Lemma 01ZM), and then applies the
descent of the cover, of the members of `Hilb` and of the family itself to a later stage, which is
`Stacks.Chow.exists_relativeCycles_baseChangeFamily_eq_of_pullbackInCycleClassImage` and is shared
with the proof of Tag 0H5D.

## References

* [Stacks Project, Tag 0H6W](https://stacks.math.columbia.edu/tag/0H6W)
* [Stacks Project, Tag 0H59](https://stacks.math.columbia.edu/tag/0H59)
* [Stacks Project, Tag 0H5D](https://stacks.math.columbia.edu/tag/0H5D)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Base change of a family of cycles through a cartesian square -/

/-- The relation "`α` is the base change of `α₀` through the cartesian square": `α` is the base
change `h^*α₀` on the fibres of `X₀ ×_{S₀} S ⟶ S`, read on the fibres of `f` through the
isomorphism `e : X ≅ X₀ ×_{S₀} S` over `S`. -/
def IsCartesianBaseChange {X S X₀ S₀ : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ)
    (α : FamilyOfCycles f r) (f₀ : X₀ ⟶ S₀) [LocallyOfFiniteType f₀] (h : S ⟶ S₀)
    (e : X ≅ pullback f₀ h) (hc : e.hom ≫ pullback.snd f₀ h = f) (α₀ : FamilyOfCycles f₀ r) :
    Prop :=
  α = fun s => fiberCycleRestrict (pullback.snd f₀ h) f e.hom hc s r (baseChangeFamily f₀ h r α₀ s)

/-! ### The two conditions of Tag 0H6W -/

/-- **Stacks Project, Tag 0H6W, condition (1).** A family of `r`-cycles on the fibres of `X/S`
comes from a Noetherian base when there is a cartesian square with right-hand column a finite
type morphism `f₀ : X₀ ⟶ S₀` of Noetherian schemes and a relative `r`-cycle
`α₀ ∈ z(X₀/S₀, r)` whose base change along `S ⟶ S₀` is the given family. -/
def ComesFromNoetherianBase {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ)
    (α : FamilyOfCycles f r) : Prop :=
  ∃ (X₀ S₀ : Scheme.{u}) (_ : IsNoetherian X₀) (hS₀ : IsNoetherian S₀) (f₀ : X₀ ⟶ S₀)
      (hft₀ : LocallyOfFiniteType f₀) (_ : QuasiCompact f₀) (h : S ⟶ S₀)
      (e : X ≅ pullback f₀ h) (hc : e.hom ≫ pullback.snd f₀ h = f),
    letI := hS₀
    letI := hft₀
    ∃ α₀ ∈ relativeCycles f₀ r, IsCartesianBaseChange f r α f₀ h e hc α₀

/-- **Stacks Project, Tag 0H6W, condition (2).** A family of `r`-cycles on the fibres of `X/S`
has a completely decomposed cycle class cover when there is a morphism `g : S' ⟶ S` which is
completely decomposed, proper and of finite presentation and whose base change `g^*α` lies in
the image of the cycle class homomorphism of Tag 0H6V on `X ×_S S' / S'`. -/
def HasCompletelyDecomposedCycleClassCover {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] (r : ℕ) (α : FamilyOfCycles f r) : Prop :=
  ∃ (S' : Scheme.{u}) (g : S' ⟶ S), IsCompletelyDecomposed g ∧ IsProper g ∧
    LocallyOfFinitePresentation g ∧ QuasiCompact g ∧ PullbackInCycleClassImage f r α g

/-! ### Membership in the image of the cycle class map under base change -/

/-- If the base change of `α` along a composite `k ≫ g` is in the image of the cycle class map,
then so is the base change of `g^*α` along `k`: the two base changes are identified through the
canonical isomorphism `(X ×_S S') ×_{S'} T ≅ X ×_S T` by Tag 0H4P, part (1), and the members of
`Hilb` are transported along that isomorphism. -/
theorem pullbackInCycleClassImage_baseChangeFamily {X S S' T : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] (r : ℕ) (α : FamilyOfCycles f r)
    (g : S' ⟶ S) (k : T ⟶ S') (hk : PullbackInCycleClassImage f r α (k ≫ g)) :
    PullbackInCycleClassImage (pullback.snd f g) r (baseChangeFamily f g r α) k := by
  obtain ⟨c, hc⟩ := hk
  refine ⟨FreeAbelianGroup.map (fun Z ↦ Z.restrict (pullbackLeftPullbackSndIso f g k).hom
    (pullbackLeftPullbackSndIso_hom_snd f g k)) c, ?_⟩
  rw [HilbertCycleDatum.cycleClassMap_map_restrict, hc, baseChangeFamily_baseChangeFamily_comp]

/-- **The base change compatibility through the cartesian square of condition (1).** If `α` is
the base change of `α₀` through the cartesian square and the base change of `α₀` along
`p : T' ⟶ S₀` lies in the image of the cycle class map, then so does the base change of `α`
along the base change `S ×_{S₀} T' ⟶ S` of `p`. -/
theorem pullbackInCycleClassImage_of_isCartesianBaseChange {X S X₀ S₀ T' : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f] (r : ℕ) (α : FamilyOfCycles f r)
    (f₀ : X₀ ⟶ S₀) [LocallyOfFinitePresentation f₀] [QuasiCompact f₀] (h : S ⟶ S₀)
    (e : X ≅ pullback f₀ h) (hc : e.hom ≫ pullback.snd f₀ h = f) (α₀ : FamilyOfCycles f₀ r)
    (hbase : IsCartesianBaseChange f r α f₀ h e hc α₀) (p : T' ⟶ S₀)
    (hp : PullbackInCycleClassImage f₀ r α₀ p) :
    PullbackInCycleClassImage f r α (pullback.snd p h) := by
  have h₁ : PullbackInCycleClassImage f₀ r α₀ (pullback.snd p h ≫ h) := by
    rw [← pullback.condition]
    exact pullbackInCycleClassImage_comp f₀ r α₀ p (pullback.fst p h) hp
  rw [IsCartesianBaseChange] at hbase
  rw [hbase]
  exact pullbackInCycleClassImage_of_restrict (pullback.snd f₀ h) f e.hom hc r
    (baseChangeFamily f₀ h r α₀) (pullback.snd p h)
    (pullbackInCycleClassImage_baseChangeFamily f₀ r α₀ h (pullback.snd p h) h₁)

/-! ### From a Noetherian base to a completely decomposed cycle class cover -/

/-- **Stacks Project, Lemma 0H6W, the implication (1) ⟹ (2).** If `α` is the base change of a
relative `r`-cycle on a finite type morphism of Noetherian schemes, then there is a completely
decomposed proper morphism `g : S' ⟶ S` of finite presentation with `g^*α` in the image of the
cycle class map of Tag 0H6V. No hypothesis on `S` or `f` beyond finite presentation is used. -/
theorem hasCompletelyDecomposedCycleClassCover_of_comesFromNoetherianBase {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f] (r : ℕ)
    (α : FamilyOfCycles f r) (h1 : ComesFromNoetherianBase f r α) :
    HasCompletelyDecomposedCycleClassCover f r α := by
  obtain ⟨X₀, S₀, _, _, f₀, _, _, h, e, hc, α₀, hα₀, hbase⟩ := h1
  obtain ⟨S₀', q, hq, himg, hqcd⟩ :=
    exists_isProper_isCompletelyDecomposed_pullbackInCycleClassImage_of_isRelativeCycle f₀ r hα₀
  have : IsNoetherian S₀' := isNoetherian_of_locallyOfFiniteType q
  exact ⟨pullback q h, pullback.snd q h, isCompletelyDecomposed_pullback q h hqcd,
    inferInstance, inferInstance, inferInstance,
    pullbackInCycleClassImage_of_isCartesianBaseChange f r α f₀ h e hc α₀ hbase q himg⟩

/-! ### From a completely decomposed cycle class cover to a Noetherian base -/

/-- Condition (1) of Tag 0H6W from data over a Noetherian scheme `S₀`: if `X` is isomorphic over
`S` to a scheme `Y ⟶ S`, which in turn is isomorphic over `S` to `X₀ ×_{S₀} S` for a finite type
morphism `f₀ : X₀ ⟶ S₀`, and if a relative `r`-cycle `α₀` on `X₀/S₀` base changes to `α` read
through these isomorphisms, then `α` comes from a Noetherian base. -/
theorem comesFromNoetherianBase_of_baseChangeFamily_eq {X S S₀ X₀ Y : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (r : ℕ) (α : FamilyOfCycles f r) [IsNoetherian S₀] (f₀ : X₀ ⟶ S₀)
    [LocallyOfFiniteType f₀] [QuasiCompact f₀] (h : S ⟶ S₀) (p : Y ⟶ S) [LocallyOfFiniteType p]
    (eX : X ≅ Y) (heX : eX.hom ≫ p = f) (E : pullback f₀ h ⟶ Y) [IsIso E]
    (hE : E ≫ p = pullback.snd f₀ h) (α₀ : FamilyOfCycles f₀ r) (hα₀ : α₀ ∈ relativeCycles f₀ r)
    (hbase : baseChangeFamily f₀ h r α₀ = fun s => fiberCycleRestrict p (pullback.snd f₀ h) E hE
      s r (fiberCycleRestrict f p eX.inv (by rw [← heX, Iso.inv_hom_id_assoc]) s r (α s))) :
    ComesFromNoetherianBase f r α := by
  have : IsNoetherian X₀ := isNoetherian_of_locallyOfFiniteType f₀
  let e : X ≅ pullback f₀ h := eX ≪≫ (asIso E).symm
  have hc : e.hom ≫ pullback.snd f₀ h = f := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc]
    rw [← hE, IsIso.inv_hom_id_assoc, heX]
  refine ⟨X₀, S₀, inferInstance, inferInstance, f₀, inferInstance, inferInstance, h, e, hc, α₀,
    hα₀, ?_⟩
  rw [IsCartesianBaseChange, hbase]
  funext s
  rw [fiberCycleRestrict_fiberCycleRestrict, fiberCycleRestrict_fiberCycleRestrict,
    fiberCycleRestrict_eq_self]
  simp [e]

/-- **Stacks Project, Lemma 0H6W, the implication (2) ⟹ (1).** Let `S` be quasi-compact and
quasi-separated and let `f : X ⟶ S` be of finite presentation. If some completely decomposed
proper morphism `g : S' ⟶ S` of finite presentation has `g^*α` in the image of the cycle class map,
then `α` is the base change of a relative `r`-cycle on a finite type morphism of Noetherian
schemes.

`S` is the limit of schemes `S_i` of finite type over `ℤ` with affine transition morphisms
(Tag 01ZA), and `X` is the base change of a scheme `Y ⟶ S_{i₀}` of finite presentation
(Tag 01ZM); the descent of `g`, of the members of `Hilb` and of `α` to a later stage `S_i` gives
the relative cycle over the Noetherian scheme `S_i`. -/
theorem comesFromNoetherianBase_of_hasCompletelyDecomposedCycleClassCover {X S : Scheme.{u}}
    [CompactSpace S] [QuasiSeparatedSpace S] (f : X ⟶ S) [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f] (r : ℕ) (α : FamilyOfCycles f r)
    (h2 : HasCompletelyDecomposedCycleClassCover f r α) : ComesFromNoetherianBase f r α := by
  obtain ⟨S', g, hcd, hprop, hlfp, -, hPB⟩ := h2
  obtain ⟨I, _, _, _, F, c, haff, hlft, hqcF, ⟨hc⟩⟩ := S.exists_isLimit_affine_locallyOfFiniteType
  have : ∀ {i j : Iᵒᵈ} (v : i ⟶ j), IsAffineHom (F.map v) := haff
  have : ∀ i, IsNoetherian (F.obj i) := fun i =>
    have := hlft i
    have := hqcF i
    isNoetherian_of_locallyOfFiniteType_terminal_from (F.obj i)
  let C : Cone F := Cone.mk S c
  obtain ⟨i₀, Y, p, a, hp, hpb⟩ :=
    LimitDescent.exists_isPullback_of_finitePresentation_of_essentiallySmall F C hc f
      ⟨inferInstance, inferInstance, inferInstance⟩
  have : LocallyOfFinitePresentation p := hp.1
  have : QuasiCompact p := hp.2.1
  let eX : X ≅ pullback p (C.π.app i₀) := hpb.isoPullback
  have heX : eX.hom ≫ pullback.snd p (C.π.app i₀) = f := hpb.isoPullback_hom_snd
  have heX' : eX.inv ≫ f = pullback.snd p (C.π.app i₀) := by rw [← heX, Iso.inv_hom_id_assoc]
  let α' : FamilyOfCycles (pullback.snd p (C.π.app i₀)) r := fun s =>
    fiberCycleRestrict f (pullback.snd p (C.π.app i₀)) eX.inv heX' s r (α s)
  obtain ⟨i, u, αᵢ, hαᵢ, hbase⟩ :=
    exists_relativeCycles_baseChangeFamily_eq_of_pullbackInCycleClassImage F C hc p r α' g hcd
      (pullbackInCycleClassImage_of_restrict f (pullback.snd p (C.π.app i₀)) eX.inv heX' r α g hPB)
  exact comesFromNoetherianBase_of_baseChangeFamily_eq f r α (pullback.snd p (F.map u))
    (C.π.app i) (pullback.snd p (C.π.app i₀)) eX heX _ (by simp) αᵢ hαᵢ hbase

/-! ### Tag 0H6W -/

/-- **Stacks Project, Lemma 0H6W.** Let `S` be a quasi-compact and quasi-separated scheme, let
`f : X ⟶ S` be a morphism of finite presentation, let `r ≥ 0` and let `α` be a family of
`r`-cycles on the fibres of `X/S`. The following are equivalent:

1. there are a cartesian square with right-hand column a finite type morphism `X₀ ⟶ S₀` of
   Noetherian schemes and `α₀ ∈ z(X₀/S₀, r)` such that `α` is the base change of `α₀` by
   `S ⟶ S₀`;
2. there is a completely decomposed proper morphism `g : S' ⟶ S` of finite presentation such
   that `g^*α` is in the image of the cycle class map of Tag 0H6V.

Finite presentation of `f` is spelled `LocallyOfFinitePresentation`, `QuasiCompact` and
`QuasiSeparated`, as in the source. -/
@[stacks 0H6W]
theorem comesFromNoetherianBase_iff_hasCompletelyDecomposedCycleClassCover {X S : Scheme.{u}}
    [CompactSpace S] [QuasiSeparatedSpace S] (f : X ⟶ S) [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f] (r : ℕ) (α : FamilyOfCycles f r) :
    ComesFromNoetherianBase f r α ↔ HasCompletelyDecomposedCycleClassCover f r α :=
  ⟨hasCompletelyDecomposedCycleClassCover_of_comesFromNoetherianBase f r α,
    comesFromNoetherianBase_of_hasCompletelyDecomposedCycleClassCover f r α⟩

end Stacks.Chow

end
