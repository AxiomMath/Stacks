module

public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersectionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedIdentity
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBase
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescent
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.FundamentalClass
public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Rank
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.DefiningIdealConormalBridge
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeShortExact
public import StacksFrontier.AlgebraicGeometry.Divisors.Relative.SmoothSection
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FormallyUnramified
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward

/-!
# `Δ^! ∘ pr_i^* = 1` for the Gysin class of the diagonal

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `g : Y ⟶ Z` be a
smooth morphism of relative dimension `d`, with `Y` locally of finite type over `S`, let
`Δ : Y ⟶ Y ×_Z Y` be the diagonal and `pr_1, pr_2 : Y ×_Z Y ⟶ Y` the projections. **Stacks 0FBS**
asserts, here at constant relative dimension `d`, that the Gysin class
`Δ^! ∈ A^d(Y ⟶ Y ×_Z Y)` of Stacks 0FBR satisfies

  `Δ^! ∘ pr_i^* = 1`   in `A^0(Y)`,

that is, for every `t : T ⟶ Y` locally of finite type and every `α ∈ CH_k(T)`, capping the flat
pullback of `α` to `(Y ×_Z Y) ×_Y T` with `Δ^!` returns `α`.

The proof is the source's. By `Stacks.Chow.diagonalGysinClass_compFlatPullbackEqOne_of` it is
the corresponding identity `c ∘ (ι ≫ pr_i)^* = 1` for the class `c = c(Y ⟶ U, 𝒩)` of Stacks 0FBK of
the closed factor `Δ' : Y ⟶ U` of the diagonal, `U ⊆ Y ×_Z Y` being the open subscheme in which
the diagonal is closed. That identity holds in general: let `i : Z ⟶ X` be a closed immersion with
a virtual normal sheaf `𝒩` of rank `r`, and let `q : X ⟶ Z` be a smooth retraction of `i` of
relative dimension `r`. Then `c(Z ⟶ X, 𝒩) ∘ q^* = 1`.

* By Stacks 02UC, applied to the difference of `c ∘ q^*` and `1` in `A^0(Z)`, it suffices to take
  `α = [T]` with `T` integral of dimension `k`.
* Then `q^*[T] = [W]` for `W = X ×_Z T`, and `dim_δ W ≤ k + r` (Stacks 02RE).
* The base change of `i` to `W` is the section `s : T ⟶ W` of the smooth projection `W ⟶ T`. It is
  a regular immersion (Stacks 067R), and its conormal sheaf is `s^*Ω_{W/T}` by the conormal
  sequence of Stacks 06AA, since `Ω_{T/T} = 0`; so it has rank `r`.
* Stacks 0FBM at vanishing excess now gives `c ∩ [W]_{k+r} = [T]_k`.

## Main results

* `Stacks.Chow.isFiniteLocallyFreeOfRank_conormalModule_of_comp_eq_id` — the conormal sheaf of a
  section of a smooth morphism of relative dimension `r` is finite locally free of rank `r`.
* `Stacks.Chow.BivariantClass.compFlatPullback` — the composite `D ∘ pr^*` (Stacks 0B75), read
  in `A^0(Y)`.
* `Stacks.Chow.BivariantClass.compFlatPullback_eq_one_iff` — `D ∘ pr^* = 1` as an equality of
  bivariant classes is equivalent to the identity on cap operations.
* `Stacks.Chow.BivariantClass.compFlatPullbackEqOne_of_fundamentalChowClass` — the reduction of
  Stacks 02UC: `D ∘ pr^* = 1` holds once it holds on the fundamental classes of integral schemes.
* `Stacks.Chow.IsVirtualNormalBundleClass.compFlatPullbackEqOne` — `c(Z ⟶ X, 𝒩) ∘ q^* = 1` for a
  smooth retraction `q` of `i` of relative dimension the rank of `𝒩`.
* `Stacks.Chow.diagonalClosedFactorClass_compFlatPullbackEqOne` — the identity for the closed
  factor of the diagonal and `ι ≫ pr`, for any smooth retraction `pr` of the diagonal of relative
  dimension `d`.
* `Stacks.Chow.diagonalGysinClass_compFlatPullbackEqOne_fst`,
  `Stacks.Chow.diagonalGysinClass_compFlatPullbackEqOne_snd` — the identity on cap operations,
  for the two projections.
* `Stacks.Chow.diagonalGysinClass_compFlatPullback_eq_one` — `Δ^! ∘ pr_i^! = 1` in `A^0(Y)` as
  an equality of bivariant classes, for both projections, at constant relative dimension `d`. The
  general case of Stacks 0FBS is
  `Stacks.Chow.diagonalGysinMap_comp_eq_completedIdentityClass`, in
  `StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinMap`.

## Implementation notes

The source writes `pr_i^!` for the Gysin class of the smooth projection; it is read here as the
flat pullback class `pr_i^*` of Stacks 0B78, which is its Gysin class by Stacks 0FF3 (factor
`pr_i` as `𝟙` followed by itself). The identity `Δ^! ∘ pr_i^* = 1` is proved first on cap
operations, as `Stacks.Chow.BivariantClass.CompFlatPullbackEqOne` — these are the two hypotheses
`hD₁`, `hD₂` of `Stacks.Chow.smoothShiftEquiv`, the core of Stacks 0FBT — and then, by
`Stacks.Chow.BivariantClass.compFlatPullback_eq_one_iff`, as an equality in `A^0(Y)`.

The reduction to integral test schemes is carried out at the Gysin system of the first Chern class
of an invertible module, where the composite of two bivariant classes (Stacks 0B75) and the class
`1 ∈ A^0(Z)` are available; this is the Gysin system of `Δ^!`.

## References

* [Stacks Project, Tag 0FBS](https://stacks.math.columbia.edu/tag/0FBS)
* [Stacks Project, Tag 0FBR](https://stacks.math.columbia.edu/tag/0FBR)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Tag 067R](https://stacks.math.columbia.edu/tag/067R)
* [Stacks Project, Tag 06AA](https://stacks.math.columbia.edu/tag/06AA)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0FBT](https://stacks.math.columbia.edu/tag/0FBT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

/-! ### The conormal sheaf of a section of a smooth morphism -/

/-- **The conormal sheaf of a section of a smooth morphism.** Let `h : W ⟶ T` be smooth of
relative dimension `d` and let `s : T ⟶ W` be an immersion with `s ≫ h = 𝟙 T`. Then the conormal
sheaf `𝒞_{T/W}` is finite locally free of rank `d`: the conormal sequence
`0 ⟶ 𝒞_{T/W} ⟶ s^*Ω_{W/T} ⟶ Ω_{T/T} ⟶ 0` of Stacks 06AA is exact, `T` being smooth over itself,
and `Ω_{T/T} = 0`, so `𝒞_{T/W} ≅ s^*Ω_{W/T}`, of rank `d`. -/
theorem isFiniteLocallyFreeOfRank_conormalModule_of_comp_eq_id {W T : Scheme.{u}}
    (h : W ⟶ T) [Smooth h] {d : ℕ} (hd : RelativeDimension h d) (s : T ⟶ W) [IsImmersion s]
    (hs : s ≫ h = 𝟙 T) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule s) d := by
  have hsm : Smooth (s ≫ h) := by rw [hs]; infer_instance
  have : FormallyUnramified (s ≫ h) := by rw [hs]; infer_instance
  have hse := Stacks.ConormalSequenceRight.conormalShortComplex_shortExact s h hsm
  have hg : (Stacks.ConormalSequenceRight.conormalShortComplex s h).g = 0 :=
    (Scheme.Hom.isZero_relativeDifferentials_of_formallyUnramified (s ≫ h)).eq_of_tgt _ _
  have := hse.mono_f
  have := hse.exact.epi_f hg
  have := isIso_of_mono_of_epi (Stacks.ConormalSequenceRight.conormalShortComplex s h).f
  have : (SheafOfModules.pushforward.{u} s.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction s).isRightAdjoint
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    ((asIso (Stacks.ConormalSequenceRight.conormalShortComplex s h).f).symm ≪≫
      Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge s)
    (Stacks.AlgebraicGeometry.ComponentDegrees.rankPullbackData s.base s.toRingCatSheafHom _ d
      (Scheme.Hom.isFiniteLocallyFreeOfRank_relativeDifferentials_of_relativeDimension h hd))

/-! ### Pushforward along an isomorphism detects heterogeneous equality -/

/-- Pushforward along an isomorphism over the base is injective, also between two presentations
of the degree: two classes of equal degrees have heterogeneously equal pushforwards exactly when
they are heterogeneously equal. -/
theorem chowPushforwardOfIso_heq_iff {C : ChowSituation.{u}} {A B : Scheme.{u}}
    {sA : A ⟶ C.S} [LocallyOfFiniteType sA] {sB : B ⟶ C.S} [LocallyOfFiniteType sB]
    (v : A ⟶ B) [IsIso v] (hv : v ≫ sB = sA) {k l : ℤ} (hkl : k = l) (x : chowGroup C sA k)
    (y : chowGroup C sA l) :
    chowPushforwardOfIso C sA sB v hv k x ≍ chowPushforwardOfIso C sA sB v hv l y ↔ x ≍ y := by
  subst hkl
  rw [heq_iff_eq, heq_iff_eq]
  exact (chowPushforwardOfIso_injective C sA sB v hv k).eq_iff

/-! ### Reduction to integral test schemes -/

section Reduction

variable {C : ChowSituation.{u}} {Y P : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
  {sP : P ⟶ C.S} [LocallyOfFiniteType sP] {Δ : Y ⟶ P} [LocallyOfFiniteType Δ] {r : ℕ}

/-- **The composite `D ∘ pr^*`, read in `A^0(Y)`.** Let `D ∈ A^r(Y ⟶ P)` be a class for
`Δ : Y ⟶ P` and let `pr : P ⟶ Y` be a flat retraction of `Δ` of relative dimension `r`. The
composite (Stacks 0B75) of the flat pullback class `pr^* ∈ A^{-r}(P ⟶ Y)` of Stacks 0B78 with `D`
is a class in `A^{r - r}(Y ⟶ Y)` for `Δ ≫ pr`; through `Δ ≫ pr = 𝟙 Y` and `r - r = 0` it is a
class in `A^0(Y) = A^0(Y ⟶ Y)`. -/
def BivariantClass.compFlatPullback
    (D : BivariantClass C (gysinSystemOfInvertible C) (Δ ≫ sP) sP Δ rfl r) (pr : P ⟶ Y)
    [LocallyOfFiniteType pr] [Flat pr] (hpr : pr ≫ sY = sP) (hdiag : Δ ≫ pr = 𝟙 Y)
    (hr : AlgebraicGeometry.RelativeDimension pr r) :
    BivariantClass C (gysinSystemOfInvertible C) sY sY (𝟙 Y) (Category.id_comp sY) 0 :=
  bivariantClassDegreeCongr C (gysinSystemOfInvertible C) sY sY (𝟙 Y)
    (Category.id_comp sY) (show (r : ℤ) + -(r : ℤ) = 0 by ring)
    (BivariantClass.congrHom hdiag (Category.id_comp sY)
      (bivariantClassCongrBase C (gysinSystemOfInvertible C) (Δ ≫ pr)
        (by rw [← hpr, ← Category.assoc, hdiag, Category.id_comp]) rfl
        (hv := comp_comp_structureMorphism_eq rfl hpr)
        (hv' := by rw [hdiag, Category.id_comp]) ((r : ℤ) + -(r : ℤ))
        (bivariantCompositeOfInvertible C (Δ ≫ sP) sP sY Δ pr rfl hpr (r : ℤ) (-(r : ℤ)) D
          (flatPullbackBivariantClassOfInvertible C sP sY pr hpr r hr))))

/-- **The cap operation of `D ∘ pr^*`.** Capping `α ∈ CH_k(T)` with the composite `D ∘ pr^*`,
read in `A^0(Y)`, caps the flat pullback of `α` to `P ×_Y T` with `D`, read on `T` through
`Stacks.Chow.sectionPullbackIso` and on `Y ×_Y T` through the base-change isomorphism. -/
theorem BivariantClass.compFlatPullback_cap_heq
    (D : BivariantClass C (gysinSystemOfInvertible C) (Δ ≫ sP) sP Δ rfl r) (pr : P ⟶ Y)
    [LocallyOfFiniteType pr] [Flat pr] (hpr : pr ≫ sY = sP) (hdiag : Δ ≫ pr = 𝟙 Y)
    (hr : AlgebraicGeometry.RelativeDimension pr r) {T : Scheme.{u}} (t : T ⟶ Y)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sY) k) :
    (D.compFlatPullback pr hpr hdiag hr).cap t k α ≍
      chowPushforwardOfIso C (t ≫ sY) (pullback.fst (𝟙 Y) t ≫ sY)
        (identityBaseChangeIso t).inv (identityBaseChangeIso_hom_comp C sY t) (k + r - r)
        (chowPushforwardOfIso C (pullback.fst Δ (pullback.fst pr t) ≫ (Δ ≫ sP)) (t ≫ sY)
          (sectionPullbackIso Δ pr hdiag t).hom
          (sectionPullbackIso_hom_comp_structureMorphism Δ pr hdiag t hpr) (k + r - r)
          (D.cap (pullback.fst pr t) (k + r)
            (flatPullbackChow C (pullback.fst pr t ≫ sP) (t ≫ sY) (pullback.snd pr t)
              (pullbackSnd_comp_structureMorphism hpr t) r
              (relativeDimension_pullbackSnd pr hr t) k
              (flatPullbackDescends C _ _ _ _ _ _ _) α))) := by
  set F := flatPullbackBivariantClassOfInvertible C sP sY pr hpr r hr with hF
  have hsA : Δ ≫ sP = sY := by rw [← hpr, ← Category.assoc, hdiag, Category.id_comp]
  have hw : (pullbackRightPullbackFstIso pr t Δ).hom ≫ (pullback.congrHom hdiag rfl).hom =
      (sectionPullbackIso Δ pr hdiag t).hom ≫ (identityBaseChangeIso t).inv := by
    refine pullback.hom_ext ?_ ?_
    · simp [sectionPullback_fst_eq Δ pr hdiag t]
    · simp [identityBaseChangeIso]
  have hD : D.cap (pullback.fst pr t) (k - -(r : ℤ)) (F.cap t k α) ≍
      D.cap (pullback.fst pr t) (k + r)
        (flatPullbackChow C (pullback.fst pr t ≫ sP) (t ≫ sY) (pullback.snd pr t)
          (pullbackSnd_comp_structureMorphism hpr t) r
          (relativeDimension_pullbackSnd pr hr t) k
          (flatPullbackDescends C _ _ _ _ _ _ _) α) :=
    BivariantClass.cap_heq D _ (by ring)
      (IsBivariantFlatPullback.cap_heq (hS1 := flatPullbackDescends C)
    (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C _ _ pr hpr r hr)
          t k α)
  have h1 : (bivariantClassCongrBase C (gysinSystemOfInvertible C) (Δ ≫ pr) hsA rfl
      (hv := comp_comp_structureMorphism_eq rfl hpr)
      (hv' := by rw [hdiag, Category.id_comp]) ((r : ℤ) + -(r : ℤ))
      (bivariantCompositeOfInvertible C (Δ ≫ sP) sP sY Δ pr rfl hpr (r : ℤ) (-(r : ℤ))
        D F)).cap t k α ≍
      chowPushforwardOfIso C (pullback.fst Δ (pullback.fst pr t) ≫ (Δ ≫ sP))
        (pullback.fst (Δ ≫ pr) t ≫ (Δ ≫ sP)) (pullbackRightPullbackFstIso pr t Δ).hom
        (by simp) (k + r - r)
        (D.cap (pullback.fst pr t) (k + r)
          (flatPullbackChow C (pullback.fst pr t ≫ sP) (t ≫ sY) (pullback.snd pr t)
            (pullbackSnd_comp_structureMorphism hpr t) r
            (relativeDimension_pullbackSnd pr hr t) k
            (flatPullbackDescends C _ _ _ _ _ _ _) α)) := by
    refine (bivariantClassCongrBase_cap C _ (Δ ≫ pr) hsA rfl _ _ t k α α HEq.rfl).trans ?_
    refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
    rw [bivariantCompositeCap_apply, properChowPushforward_eq_chowPushforwardOfIso]
    exact chowPushforwardOfIso_heq _ _ _ rfl rfl (by ring) hD
  refine (bivariantClassDegreeCongr_cap C _ _ _ _ _ _ _ t k α).trans ?_
  rw [BivariantClass.congrHom_cap]
  exact (chowPushforwardOfIso_heq_comp_of_comp_eq _ _ _ hw (by simp) _ (by rw [hsA]) rfl
      (by ring) _ _ h1).trans
    (chowPushforwardOfIso_heq_comp_of_comp_eq _ _ _ rfl _ _ rfl rfl rfl _ _ HEq.rfl).symm

/-- `D ∘ pr^*` and `1` agree on a class exactly when capping its flat pullback with `D` returns
it. -/
theorem BivariantClass.compFlatPullback_cap_eq_iff
    (D : BivariantClass C (gysinSystemOfInvertible C) (Δ ≫ sP) sP Δ rfl r) (pr : P ⟶ Y)
    [LocallyOfFiniteType pr] [Flat pr] (hpr : pr ≫ sY = sP) (hdiag : Δ ≫ pr = 𝟙 Y)
    (hr : AlgebraicGeometry.RelativeDimension pr r) {T : Scheme.{u}} (t : T ⟶ Y)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sY) k) :
    (D.compFlatPullback pr hpr hdiag hr).cap t k α =
        (bivariantIdentityClassOfInvertible C sY).cap t k α ↔
      chowPushforwardOfIso C (pullback.fst Δ (pullback.fst pr t) ≫ (Δ ≫ sP)) (t ≫ sY)
          (sectionPullbackIso Δ pr hdiag t).hom
          (sectionPullbackIso_hom_comp_structureMorphism Δ pr hdiag t hpr) (k + r - r)
          (D.cap (pullback.fst pr t) (k + r)
            (flatPullbackChow C (pullback.fst pr t ≫ sP) (t ≫ sY) (pullback.snd pr t)
              (pullbackSnd_comp_structureMorphism hpr t) r
              (relativeDimension_pullbackSnd pr hr t) k
              (flatPullbackDescends C _ _ _ _ _ _ _) α)) =
        chowGroupDegreeEquiv C (t ≫ sY) (by ring) α := by
  have hI := bivariantIdentityClassOfInvertible_cap_heq C sY t k α
  have hK := D.compFlatPullback_cap_heq pr hpr hdiag hr t k α
  rw [← heq_iff_eq, eq_comm, chowGroupDegreeEquiv_eq_iff_heq]
  constructor
  · intro hc
    exact ((chowPushforwardOfIso_heq_iff _ _ (by ring) _ _).1
      (hK.symm.trans (hc.trans hI))).symm
  · intro hc
    exact hK.trans (((chowPushforwardOfIso_heq_iff _ _ (by ring) _ _).2 hc.symm).trans hI.symm)

/-- **`D ∘ pr^* = 1` as an equality of bivariant classes.** The composite `D ∘ pr^*`, read in
`A^0(Y)`, is the unit `1 ∈ A^0(Y)` exactly when the identity holds on cap operations, in the form
`Stacks.Chow.BivariantClass.CompFlatPullbackEqOne`. -/
theorem BivariantClass.compFlatPullback_eq_one_iff
    (D : BivariantClass C (gysinSystemOfInvertible C) (Δ ≫ sP) sP Δ rfl r) (pr : P ⟶ Y)
    [LocallyOfFiniteType pr] [Flat pr] (hpr : pr ≫ sY = sP) (hdiag : Δ ≫ pr = 𝟙 Y)
    (hr : AlgebraicGeometry.RelativeDimension pr r) :
    D.compFlatPullback pr hpr hdiag hr = bivariantIdentityClassOfInvertible C sY ↔
      D.CompFlatPullbackEqOne pr hpr hdiag hr := by
  constructor
  · intro h T t _ k α
    exact (D.compFlatPullback_cap_eq_iff pr hpr hdiag hr t k α).1 (by rw [h])
  · intro h
    ext T t _ k α
    exact (D.compFlatPullback_cap_eq_iff pr hpr hdiag hr t k α).2 (h t k α)

/-- **Stacks 02UC for `D ∘ pr^* = 1`.** Let `D ∈ A^r(Y ⟶ P)` be a class for `Δ : Y ⟶ P` and let
`pr : P ⟶ Y` be a flat retraction of `Δ` of relative dimension `r`. If capping the flat pullback
of the fundamental class `[T]_k` to `P ×_Y T` with `D` returns `[T]_k` for every integral scheme
`T` locally of finite type over `Y`, then `D ∘ pr^* = 1` on every class of every test scheme.

The composite `D ∘ pr^* ∈ A^0(Y)` (Stacks 0B75, `Stacks.Chow.BivariantClass.compFlatPullback`)
caps by the left-hand side of the identity, and `1` caps by the identity; so the identity holds for
all classes exactly when the two bivariant classes are equal, and by Stacks 02UC this is checked on
the fundamental classes of integral test schemes. -/
theorem BivariantClass.compFlatPullbackEqOne_of_fundamentalChowClass
    (D : BivariantClass C (gysinSystemOfInvertible C) (Δ ≫ sP) sP Δ rfl r) (pr : P ⟶ Y)
    [LocallyOfFiniteType pr] [Flat pr] (hpr : pr ≫ sY = sP) (hdiag : Δ ≫ pr = 𝟙 Y)
    (hr : AlgebraicGeometry.RelativeDimension pr r)
    (h : ∀ {T : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t] [IsIntegral T] (k : ℤ),
      chowPushforwardOfIso C (pullback.fst Δ (pullback.fst pr t) ≫ (Δ ≫ sP)) (t ≫ sY)
          (sectionPullbackIso Δ pr hdiag t).hom
          (sectionPullbackIso_hom_comp_structureMorphism Δ pr hdiag t hpr) (k + r - r)
          (D.cap (pullback.fst pr t) (k + r)
            (flatPullbackChow C (pullback.fst pr t ≫ sP) (t ≫ sY) (pullback.snd pr t)
              (pullbackSnd_comp_structureMorphism hpr t) r
              (relativeDimension_pullbackSnd pr hr t) k
              (flatPullbackDescends C _ _ _ _ _ _ _) (fundamentalChowClass C (t ≫ sY) k))) =
        chowGroupDegreeEquiv C (t ≫ sY) (by ring) (fundamentalChowClass C (t ≫ sY) k)) :
    D.CompFlatPullbackEqOne pr hpr hdiag hr := by
  refine (D.compFlatPullback_eq_one_iff pr hpr hdiag hr).1 (eq_of_sub_eq_zero ?_)
  rw [BivariantClass.eq_zero_iff_capsIntegralFundamentalClassesToZero]
  intro T t _ _ k
  rw [BivariantClass.sub_cap, sub_eq_zero]
  exact (D.compFlatPullback_cap_eq_iff pr hpr hdiag hr t k _).2 (h t k)

end Reduction

/-! ### A virtual normal Gysin class against flat pullback along a smooth retraction -/

section Retraction

variable {C : ChowSituation.{u}} {Z X : Scheme.{u}} {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ]
  {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {i : Z ⟶ X} [IsClosedImmersion i]
  {𝒩 : VirtualNormalBundle i} {r : ℕ}
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]

/-- **`c(Z ⟶ X, 𝒩) ∘ q^* = 1` for a smooth retraction `q`.** Let `i : Z ⟶ X` be a closed
immersion of schemes locally of finite type over the base with a virtual normal sheaf `𝒩` of
constant rank `r`, let `c` be a bivariant class satisfying the relation of Stacks 0FBK for `𝒩`
(for instance `c(Z ⟶ X, 𝒩)`), and let `q : X ⟶ Z` be smooth of relative dimension `r` with
`i ≫ q = 𝟙 Z`. Then `c ∘ q^* = 1` in `A^0(Z)`.

By `Stacks.Chow.BivariantClass.compFlatPullbackEqOne_of_fundamentalChowClass` it suffices to
treat `[T]_k` for `T` integral of dimension `k` over `t : T ⟶ Z`. Its flat pullback is `[W]_{k+r}`
for `W = X ×_Z T`, of dimension at most `k + r`; the base change of `i` to `W` is the section
`T ⟶ W` of the smooth projection `W ⟶ T`, a regular immersion (Stacks 067R) whose conormal sheaf
has rank `r` (`Stacks.Chow.isFiniteLocallyFreeOfRank_conormalModule_of_comp_eq_id`); and Stacks
0FBM at vanishing excess (`Stacks.Chow.virtualNormalBundleClass_cap_fundamentalChowClass`) gives
`c ∩ [W]_{k+r} = [T]_k`. -/
theorem IsVirtualNormalBundleClass.compFlatPullbackEqOne
    {c : BivariantClass C (gysinSystemOfInvertible C) (i ≫ sX) sX i rfl (r : ℤ)}
    (hc : IsVirtualNormalBundleClass C (i ≫ sX) sX i rfl (gysinSystemOfInvertible C) 𝒩 r c)
    (q : X ⟶ Z) [Smooth q] (hq : q ≫ sZ = sX) (hdiag : i ≫ q = 𝟙 Z)
    (hr : AlgebraicGeometry.RelativeDimension q r) :
    c.CompFlatPullbackEqOne q hq hdiag hr := by
  refine BivariantClass.compFlatPullbackEqOne_of_fundamentalChowClass c q hq hdiag hr ?_
  intro T t _ _ k
  by_cases hk : relativeDimension C.dimensionFunction (t ≫ sZ) (genericPoint T) = k
  · have hT : schemeDeltaDimension C (t ≫ sZ) ≤ (k : EInt) := by
      rw [schemeDeltaDimension_eq_genericPoint, hk]
    rw [flatPullbackChow_fundamentalChowClass C _ _ _ _ r _ k _ hT]
    have hW : schemeDeltaDimension C (pullback.fst q t ≫ sX) ≤ ((k + r : ℤ) : EInt) :=
      schemeDeltaDimension_le_add_of_flat C _ (t ≫ sZ) (pullback.snd q t)
        (pullbackSnd_comp_structureMorphism hq t) r (relativeDimension_pullbackSnd q hr t) hT
    -- the section `T ⟶ X ×_Z T` of the smooth projection, and the square it sits in
    set s : T ⟶ pullback q t := pullback.lift (t ≫ i) (𝟙 T)
      (by rw [Category.assoc, hdiag, Category.comp_id, Category.id_comp]) with hs
    have hs₁ : s ≫ pullback.snd q t = 𝟙 T := pullback.lift_snd _ _ _
    have hs₂ : s ≫ pullback.fst q t = t ≫ i := pullback.lift_fst _ _ _
    set e : T ⟶ pullback i (pullback.fst q t) := pullback.lift t s hs₂.symm with he
    have he₁ : e ≫ pullback.fst i (pullback.fst q t) = t := pullback.lift_fst _ _ _
    have he₂ : e ≫ pullback.snd i (pullback.fst q t) = s := pullback.lift_snd _ _ _
    have : IsIso e := isIso_of_isPullback_of_section i q hdiag t (IsPullback.of_hasPullback q t)
      e he₁ (by rw [reassoc_of% he₂, hs₁])
    have sq : IsPullback s t (pullback.fst q t) i :=
      (IsPullback.of_iso_pullback ⟨hs₂.symm⟩ (asIso e) he₁ he₂).flip
    have : IsClosedImmersion s := MorphismProperty.of_isPullback sq.flip inferInstance
    have hreg : IsRegularImmersion s :=
      Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section (pullback.snd q t) s hs₁
    have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule s) r :=
      isFiniteLocallyFreeOfRank_conormalModule_of_comp_eq_id (pullback.snd q t)
        (relativeDimension_pullbackSnd q hr t) s hs₁
    rw [virtualNormalBundleClass_cap_fundamentalChowClass C (i ≫ sX) sX i rfl 𝒩 r hc
        (pullback.fst q t) s t sq (s ≫ (pullback.fst q t ≫ sX)) rfl hreg (k + r) hW,
      chowPushforwardOfIso_fundamentalChowClass, chowGroupDegreeEquiv_fundamentalChowClass]
  · have h0 : fundamentalChowClass C (t ≫ sZ) k = 0 := by
      rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_ne C _ genericPoints_eq_singleton hk,
        map_zero]
    rw [h0, map_zero, map_zero, map_zero, map_zero]

end Retraction

/-! ### The diagonal of a smooth morphism -/

section Diagonal

variable (C : ChowSituation.{u}) {Y Z : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (g : Y ⟶ Z) [Smooth g] {d : ℕ} (hd : RelativeDimension g d)

/-- **`c(Y ⟶ U, 𝒩) ∘ (ι ≫ pr)^* = 1`.** For `pr : Y ×_Z Y ⟶ Y` a smooth retraction of the
diagonal of relative dimension `d`, such as either projection, the class
`Stacks.Chow.diagonalClosedFactorClass` of the closed factor `Δ' : Y ⟶ U` of the diagonal
satisfies `c ∘ (ι ≫ pr)^* = 1`, where `ι : U ⟶ Y ×_Z Y` is the inclusion of the open subscheme in
which the diagonal is closed. This is
`Stacks.Chow.IsVirtualNormalBundleClass.compFlatPullbackEqOne` for `Δ'`, whose normal bundle has
rank `d`, and the retraction `ι ≫ pr`. It is the hypothesis of
`Stacks.Chow.diagonalGysinClass_compFlatPullbackEqOne_of`. -/
theorem diagonalClosedFactorClass_compFlatPullbackEqOne (pr : pullback g g ⟶ Y) [Smooth pr]
    (hpr : pr ≫ sY = pullback.fst g g ≫ sY) (hdiag : pullback.diagonal g ≫ pr = 𝟙 Y)
    (hr : RelativeDimension pr d) :
    (diagonalClosedFactorClass C sY g hd).CompFlatPullbackEqOne (sY := sY)
      ((pullback.diagonal g).coborderRange.ι ≫ pr) (by rw [Category.assoc, hpr])
      (by rw [← Category.assoc, Scheme.Hom.liftCoborder_ι, hdiag])
      (by
        simpa using RelativeDimension.comp_of_flat _ pr
          (relativeDimension_of_isOpenImmersion (pullback.diagonal g).coborderRange.ι) hr) :=
  have := isFiniteLocallyFreeOfRank_diagonalVirtualNormalBundle g hd
  IsVirtualNormalBundleClass.compFlatPullbackEqOne
    (isVirtualNormalBundleClass_virtualNormalBundleClass C _ _ _ rfl _ d)
    ((pullback.diagonal g).coborderRange.ι ≫ pr) (by rw [Category.assoc, hpr])
    (by rw [← Category.assoc, Scheme.Hom.liftCoborder_ι, hdiag])
    (by
      simpa using RelativeDimension.comp_of_flat _ pr
        (relativeDimension_of_isOpenImmersion (pullback.diagonal g).coborderRange.ι) hr)

/-- **`Δ^! ∘ pr_1^* = 1` on cap operations.** For `g : Y ⟶ Z`
smooth of relative dimension `d`, capping the flat pullback along `pr_1 : Y ×_Z Y ⟶ Y` with the
Gysin class `Δ^!` of the diagonal is the identity on the Chow groups of every test scheme over
`Y`. -/
theorem diagonalGysinClass_compFlatPullbackEqOne_fst :
    (diagonalGysinClass C sY g hd).CompFlatPullbackEqOne (pullback.fst g g) rfl
      (pullback.diagonal_fst g) (relativeDimension_pullback_fst_self g hd) :=
  diagonalGysinClass_compFlatPullbackEqOne_of C sY g hd (pullback.fst g g) rfl
    (pullback.diagonal_fst g) (relativeDimension_pullback_fst_self g hd)
    (diagonalClosedFactorClass_compFlatPullbackEqOne C sY g hd (pullback.fst g g) rfl
      (pullback.diagonal_fst g) (relativeDimension_pullback_fst_self g hd))

/-- **`Δ^! ∘ pr_2^* = 1` on cap operations.** For `g : Y ⟶ Z`
smooth of relative dimension `d`, with `Z` over the base compatibly with `Y`, capping the flat
pullback along `pr_2 : Y ×_Z Y ⟶ Y` with the Gysin class `Δ^!` of the diagonal is the identity on
the Chow groups of every test scheme over `Y`. -/
theorem diagonalGysinClass_compFlatPullbackEqOne_snd (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (hg : g ≫ sZ = sY) :
    (diagonalGysinClass C sY g hd).CompFlatPullbackEqOne (pullback.snd g g)
      (smoothShift_pullback_snd_comp_structureMorphism C sY sZ g hg) (pullback.diagonal_snd g)
      (relativeDimension_pullback_snd g g d hd) :=
  diagonalGysinClass_compFlatPullbackEqOne_of C sY g hd (pullback.snd g g)
    (smoothShift_pullback_snd_comp_structureMorphism C sY sZ g hg) (pullback.diagonal_snd g)
    (relativeDimension_pullback_snd g g d hd)
    (diagonalClosedFactorClass_compFlatPullbackEqOne C sY g hd (pullback.snd g g)
      (smoothShift_pullback_snd_comp_structureMorphism C sY sZ g hg) (pullback.diagonal_snd g)
      (relativeDimension_pullback_snd g g d hd))

/-- **`Δ^! ∘ pr_i^! = 1` in `A^0(Y)` at constant relative dimension, for `i = 1, 2`.** Let
`g : Y ⟶ Z` be a smooth morphism of constant relative dimension `d` of schemes locally of finite
type over the base, let
`Δ : Y ⟶ Y ×_Z Y` be the diagonal, with Gysin class `Δ^! ∈ A^d(Y ⟶ Y ×_Z Y)` (Stacks 0FBR), and
let `pr_1, pr_2 : Y ×_Z Y ⟶ Y` be the projections, smooth of relative dimension `d`, whose Gysin
classes are the flat pullback classes `pr_i^! = pr_i^* ∈ A^{-d}(Y ×_Z Y ⟶ Y)` (Stacks 0FF3,
0B78). Then for both projections the composite `Δ^! ∘ pr_i^!` (Stacks 0B75), read in `A^0(Y)`
through `Δ ≫ pr_i = 𝟙 Y`, is the unit `1 ∈ A^0(Y)`. For an arbitrary smooth `g`, with the
Gysin maps in the completed groups of Stacks 0FE0, the identity is
`Stacks.Chow.diagonalGysinMap_comp_eq_completedIdentityClass`. -/
theorem diagonalGysinClass_compFlatPullback_eq_one (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (hg : g ≫ sZ = sY) :
    (diagonalGysinClass C sY g hd).compFlatPullback (pullback.fst g g) rfl
        (pullback.diagonal_fst g) (relativeDimension_pullback_fst_self g hd) =
        bivariantIdentityClassOfInvertible C sY ∧
      (diagonalGysinClass C sY g hd).compFlatPullback (pullback.snd g g)
        (smoothShift_pullback_snd_comp_structureMorphism C sY sZ g hg) (pullback.diagonal_snd g)
        (relativeDimension_pullback_snd g g d hd) =
        bivariantIdentityClassOfInvertible C sY :=
  ⟨(BivariantClass.compFlatPullback_eq_one_iff _ _ _ _ _).2
      (diagonalGysinClass_compFlatPullbackEqOne_fst C sY g hd),
    (BivariantClass.compFlatPullback_eq_one_iff _ _ _ _ _).2
      (diagonalGysinClass_compFlatPullbackEqOne_snd C sY g hd sZ hg)⟩

end Diagonal

end Stacks.Chow

end
