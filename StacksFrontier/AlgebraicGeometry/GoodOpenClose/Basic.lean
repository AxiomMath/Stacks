module

public import StacksFrontier.AlgebraicGeometry.GoodOpenClose.Restrict
public import StacksFrontier.AlgebraicGeometry.GoodOpenClose.Reverse

/-!
# Good opens of `Proj` are the opens below the invertible locus

Let `S` be a graded ring, `X = Proj(S)` and `d` a natural number. An open of `X` is *good* if on
it every `𝒪_X(dn)` is invertible and every multiplication map `𝒪_X(nd) ⊗ 𝒪_X(md) → 𝒪_X(nd+md)`
is an isomorphism, and `W_d` is the supremum of the good opens. This file proves that an open is
good exactly when it lies in `W_d`, and with it that `W_d` is itself good and that the class of
good opens is closed under arbitrary suprema and under passing to a smaller open.

## Main results

* `Stacks.AlgebraicGeometry.GoodOpenClose.isGoodOpen_of_le_ratioLocus`: every open contained in
  the union of the standard opens `D₊(fg)` with `deg f = deg g + d` is a good open.
* `Stacks.AlgebraicGeometry.GoodOpenClose.isGoodOpen_iff_le_whereInvertible`: an open is good
  exactly when it lies in `W_d`.
* `Stacks.AlgebraicGeometry.GoodOpenClose.isGoodOpen_sSup`,
  `Stacks.AlgebraicGeometry.GoodOpenClose.isGoodOpen_iSup`,
  `Stacks.AlgebraicGeometry.GoodOpenClose.isGoodOpen_whereInvertible` and
  `Stacks.AlgebraicGeometry.GoodOpenClose.isGoodOpen_mono`: goodness is closed under suprema,
  `W_d` is good, and goodness passes to smaller opens.

## References

* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjInvertibleLocus

namespace Stacks.AlgebraicGeometry.GoodOpenClose

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-! ### The standard opens of the ratio locus, as a single indexed family -/

/-- The index type of the standard opens `D₊(fg)` with `deg f = deg g + d`: a common degree and
the two homogeneous elements. -/
abbrev RatioIndex (d : ℕ) : Type u := Σ e : ℕ, (𝒮 (e + d)) × (𝒮 e)

/-- The standard open attached to an index. -/
def ratioOpen (d : ℕ) (i : RatioIndex 𝒮 d) : (AlgebraicGeometry.Proj 𝒮).Opens :=
  AlgebraicGeometry.Proj.basicOpen 𝒮 ((i.2.1 : S) * (i.2.2 : S))

/-- The family of opens of an open subscheme `U` cut out by the standard opens of the ratio
locus. -/
def ratioCover (d : ℕ) (U : (AlgebraicGeometry.Proj 𝒮).Opens) (i : RatioIndex 𝒮 d) :
    U.toScheme.Opens :=
  U.ι ⁻¹ᵁ ratioOpen 𝒮 d i

/-- The family covers the open subscheme as soon as the open lies in the ratio locus. -/
theorem iSup_ratioCover {d : ℕ} {U : (AlgebraicGeometry.Proj 𝒮).Opens}
    (hU : U ≤ ProjShared.ratioLocus 𝒮 d) : iSup (ratioCover 𝒮 d U) = ⊤ := by
  refine top_le_iff.mp fun y _ => ?_
  have hmem : U.ι.base y ∈ U := by
    have hrange : U.ι.base y ∈ U.ι.opensRange := ⟨y, rfl⟩
    rwa [Scheme.Opens.opensRange_ι] at hrange
  obtain ⟨e, f, g, hf, hg, hfx, hgx⟩ :=
    (ProjShared.mem_ratioLocus_iff 𝒮 d (U.ι.base y)).mp (hU hmem)
  refine Opens.mem_iSup.mpr ⟨⟨e, ⟨⟨f, hf⟩, ⟨g, hg⟩⟩⟩, ?_⟩
  change U.ι.base y ∈ AlgebraicGeometry.Proj.basicOpen 𝒮 (f * g)
  rw [AlgebraicGeometry.Proj.mem_basicOpen]
  exact fun hmul => ((U.ι.base y).isPrime.mem_or_mem hmul).elim hfx hgx

/-! ### Invertibility of the twists on an open of the ratio locus -/

variable {p q : S} {e d : ℕ}

/-- The ratio trivialization `ratioOverIsoUnit` of `𝒪(nd)` on `D₊(pq)`, read as a sectionwise
trivialization on the site of opens of `Proj S`. -/
def ratioTriv (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ} (hc : (n : ℤ) * d = c) :
    Stacks.SheafDescent.Trivialization (AlgebraicGeometry.Proj 𝒮).presheaf
      (twistingSheaf 𝒮 c).val (AlgebraicGeometry.Proj.basicOpen 𝒮 (p * q)) :=
  Stacks.SheafDescent.Trivialization.ofIso _ (AlgebraicGeometry.Proj 𝒮).ringCatSheaf.2
    (ratioOverIsoUnit 𝒮 hp hq hc)

/-- The twists `𝒪(dn)` become invertible after restriction to any open contained in the union of
the standard opens `D₊(fg)` with `deg f = deg g + d`. -/
theorem isInvertible_pullback_twistingSheaf_of_le_ratioLocus
    {U : (AlgebraicGeometry.Proj 𝒮).Opens} (hU : U ≤ ProjShared.ratioLocus 𝒮 d) (n : ℤ) :
    SheafOfModules.IsInvertible U.toScheme.presheaf U.toScheme.ringCatSheaf.2
      ((Scheme.Modules.pullback U.ι).obj (twistingSheaf 𝒮 ((d : ℤ) * n))) :=
  isInvertible_pullback_of_trivializing_cover U (twistingSheaf 𝒮 ((d : ℤ) * n))
    (ratioCover 𝒮 d U) (iSup_ratioCover 𝒮 hU) (ratioOpen 𝒮 d) (fun _ => le_rfl)
    fun i => ratioTriv 𝒮 i.2.1.2 i.2.2.2 (mul_comm (n : ℤ) (d : ℤ))

/-! ### The multiplication maps on an open of the ratio locus -/

/-- The multiplication map between two `d`-divisible twists is bijective on the sections over
every open contained in the ratio locus. -/
theorem bijective_twistMultAb_app_of_le_ratioLocus
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjShared.ratioLocus 𝒮 d)
    {n m a b : ℤ} (ha : (n : ℤ) * d = a) (hb : (m : ℤ) * d = b) :
    Function.Bijective (ConcreteCategory.hom ((TwistTensor.twistMultAb 𝒮 a b).app (op W))) := by
  refine TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective
    ((SheafOfModules.toSheaf (structureSheafRing
      (AlgebraicGeometry.Proj 𝒮).toRingedSpace)).map (twistMultiplicationMap 𝒮 a b)) W
    fun x hx => ?_
  obtain ⟨e', f, g, hf, hg, hfx, hgx⟩ := (ProjShared.mem_ratioLocus_iff 𝒮 d x).mp (hW hx)
  have hx' : x ∈ ProjectiveSpectrum.basicOpen 𝒮 (f * g) := fun hmul =>
    (x.isPrime.mem_or_mem hmul).elim hfx hgx
  exact (ConcreteCategory.isIso_iff_bijective _).mp
    (TwistTensor.isIso_stalkFunctor_map_twistMultiplication 𝒮 hf hg ha hb hx')

/-- On an open contained in the ratio locus, the restriction of the multiplication map
`𝒪(dn) ⊗ 𝒪(dm) → 𝒪(dn + dm)` is an isomorphism. -/
theorem isIso_restrictFunctor_twistMultiplicationMap
    {U : (AlgebraicGeometry.Proj 𝒮).Opens} (hU : U ≤ ProjShared.ratioLocus 𝒮 d) (n m : ℤ) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (twistMultiplicationMap 𝒮 ((d : ℤ) * n) ((d : ℤ) * m))) := by
  have hpre : IsIso ((Scheme.Modules.toPresheaf U.toScheme).map
      ((Scheme.Modules.restrictFunctor U.ι).map
        (twistMultiplicationMap 𝒮 ((d : ℤ) * n) ((d : ℤ) * m)))) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_twistMultAb_app_of_le_ratioLocus 𝒮
      ((U.ι_image_le V.unop).trans hU) (mul_comm (n : ℤ) (d : ℤ)) (mul_comm (m : ℤ) (d : ℤ))
  exact isIso_of_reflects_iso _ (Scheme.Modules.toPresheaf U.toScheme)

/-! ### Good opens and the invertible locus -/

/-- Every open contained in the union of the standard opens `D₊(fg)` with `deg f = deg g + d` is
a good open. -/
theorem isGoodOpen_of_le_ratioLocus (d : ℕ) {U : (AlgebraicGeometry.Proj 𝒮).Opens}
    (hU : U ≤ ProjShared.ratioLocus 𝒮 d) : IsGoodOpen 𝒮 d U :=
  ⟨fun n => isInvertible_pullback_twistingSheaf_of_le_ratioLocus 𝒮 hU n,
    fun n m => isIso_restrictFunctor_twistMultiplicationMap 𝒮 hU n m⟩

/-- An open is good exactly when it lies in the largest good open `whereInvertible 𝒮 d`. -/
theorem isGoodOpen_iff_le_whereInvertible (d : ℕ) (U : (AlgebraicGeometry.Proj 𝒮).Opens) :
    IsGoodOpen 𝒮 d U ↔ U ≤ whereInvertible 𝒮 d :=
  ⟨le_whereInvertible_of_isGoodOpen 𝒮,
    fun h => isGoodOpen_of_le_ratioLocus 𝒮 d (h.trans (whereInvertible_le_ratioLocus 𝒮 d))⟩

/-- For `0 < d`, an open is good exactly when it lies in the largest good open
`whereInvertible 𝒮 d`. -/
@[stacks 01MU "maximality and goodness of the invertible locus"]
theorem isGoodOpen_iff_le_whereInvertible_of_pos (d : ℕ) (_hd : 0 < d)
    (U : (AlgebraicGeometry.Proj 𝒮).Opens) :
    IsGoodOpen 𝒮 d U ↔ U ≤ whereInvertible 𝒮 d :=
  isGoodOpen_iff_le_whereInvertible 𝒮 d U

/-- Goodness passes to smaller opens. -/
theorem isGoodOpen_mono (d : ℕ) {U V : (AlgebraicGeometry.Proj 𝒮).Opens} (hUV : U ≤ V)
    (hV : IsGoodOpen 𝒮 d V) : IsGoodOpen 𝒮 d U :=
  (isGoodOpen_iff_le_whereInvertible 𝒮 d U).mpr
    (hUV.trans ((isGoodOpen_iff_le_whereInvertible 𝒮 d V).mp hV))

/-- Goodness is closed under arbitrary suprema. -/
theorem isGoodOpen_sSup (d : ℕ) {T : Set (AlgebraicGeometry.Proj 𝒮).Opens}
    (hT : ∀ U ∈ T, IsGoodOpen 𝒮 d U) : IsGoodOpen 𝒮 d (sSup T) :=
  (isGoodOpen_iff_le_whereInvertible 𝒮 d _).mpr
    (sSup_le fun U hU => le_whereInvertible_of_isGoodOpen 𝒮 (hT U hU))

/-- Goodness is closed under indexed suprema. -/
theorem isGoodOpen_iSup (d : ℕ) {ι : Type*} {U : ι → (AlgebraicGeometry.Proj 𝒮).Opens}
    (hU : ∀ i, IsGoodOpen 𝒮 d (U i)) : IsGoodOpen 𝒮 d (⨆ i, U i) :=
  (isGoodOpen_iff_le_whereInvertible 𝒮 d _).mpr
    (iSup_le fun i => le_whereInvertible_of_isGoodOpen 𝒮 (hU i))

/-- The largest good open `whereInvertible 𝒮 d` is itself good. -/
theorem isGoodOpen_whereInvertible (d : ℕ) : IsGoodOpen 𝒮 d (whereInvertible 𝒮 d) :=
  isGoodOpen_sSup 𝒮 d fun _ hU => hU

/-- For `0 < d`, the largest good open `whereInvertible 𝒮 d` is the union of the standard opens
`D₊(fg)` with `deg f = deg g + d`. -/
@[stacks 01MU "equality of the two open subsets"]
theorem whereInvertible_eq_iSup_basicOpen_mul_of_pos (d : ℕ) (_hd : 0 < d) :
    whereInvertible 𝒮 d =
      ⨆ (e : ℕ) (f : 𝒮 (e + d)) (g : 𝒮 e),
        AlgebraicGeometry.Proj.basicOpen 𝒮 ((f : S) * (g : S)) :=
  whereInvertible_eq_iSup_basicOpen_mul 𝒮 d

end Stacks.AlgebraicGeometry.GoodOpenClose

end
