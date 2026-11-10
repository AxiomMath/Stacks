module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedGradingProduct
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.SupportedProductPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ClosedCover
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.SupportedIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Perfect.KGroups.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ClosedSupportPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction

/-!
# The ring `A⁽¹⁾(Z ⟶ X)`

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : Z ⟶ X` be a
closed immersion of schemes locally of finite type over `S`. The localized Chern classes of a
perfect object of `X` supported on `Z` (Stacks 0FES) take values in

  `A⁽¹⁾(Z ⟶ X) = A⁰(X) × ∏_{i ≥ 1} Aⁱ(Z ⟶ X)`

(`Stacks.Chow.localizedBivariantGrading` at `p = 1`; its factors of negative degree vanish for a
closed immersion), multiplied by the recipe of Stacks 0FA0 with every degree `n ≥ 1` kept
localized: `(a b)₀ = a₀ b₀` in `A⁰(X)`, and for `n ≥ 1` the degree-`n` component is the sum of
`res(aᵢ) ∘ bⱼ` (`i, j ≥ 1`, `i + j = n`), `aₙ ∘ b₀` and `res(a₀) ∘ bₙ`
(`Stacks.Chow.localizedGradingCutoffMul` with output cutoff `1`). The source omits the
verification that these multiplications are associative. This file proves that they make
`A⁽¹⁾(Z ⟶ X)` a ring, with unit `1 ∈ A⁰(X)`, in which every element `1 + c₁ + c₂ + ⋯` is a unit.
The ring is not commutative in general; the elements of a set of pairwise commuting elements
generate a commutative submonoid (`Submonoid.closureCommMonoidOfComm`), subring
(`Subring.closureCommRingOfComm`) and, among units, subgroup (`Subgroup.closureCommGroupOfComm`).

The ring axioms are proved on the operations on the test schemes, as for the ring of total Chow
cohomology classes (`Stacks.Chow.TotalChowClass.instRing`). For a test scheme `t : T ⟶ X` let
`i : Z ×_X T ⟶ T` be the base change of `f`. An element `a` operates on
`CH_*(T) × CH_*(Z ×_X T)`, in index `0` by `(x, y) ↦ (a₀ ∩ x, res(a₀) ∩ y)` and in index `n ≥ 1`
by `(x, y) ↦ (0, aₙ ∩ (x + i_* y))` (`Stacks.Chow.localizedGradingOp`); this is a graded cap family
(`Stacks.Chow.GradedCapFamily`), and these form a ring. The operation of a product is the product
of the operations (`Stacks.Chow.localizedGradingOp_mul`): in index `n ≥ 1` this is the cap formula
of each of the three maps of Stacks 0FA0 (`Stacks.Chow.supportedLeftComp_cap`,
`Stacks.Chow.supportedRightComp_cap`), the description `res(c) ∘ c' = c ∘ i_* c'` of the third one
(`Stacks.Chow.supportedMul_eq_supportedRightComp`, Stacks 0FA1), and the projection formula
`d ∩ i_* y = i_*(res(d) ∩ y)`. An element is determined by its operations
(`Stacks.Chow.localizedGrading_ext_op`), whence every ring axiom.

Finally, a perfect object supported on `Z` has zero derived pullback to `X ∖ Z`
(`AlgebraicGeometry.supportedPerfect_isZero_derivedPullback_compl`), the hypothesis under which its
localized Chern classes are defined.

## Main definitions

* `Stacks.Chow.supportedClassRestriction`, `Stacks.Chow.ambientClassRestriction` — the restrictions
  `A^p(Z ⟶ X) ⟶ A^p(Z)` of Stacks 0FA1 and `A^p(X) ⟶ A^p(Z)` of Stacks 0B7F, over `Z`.
* `Stacks.Chow.localizedGradingOp` — the operation of `A⁽¹⁾(Z ⟶ X)` on a test scheme.
* `Stacks.Chow.instRingLocalizedGradingOne` — the ring `A⁽¹⁾(Z ⟶ X)`.
* `Stacks.Chow.localizedGradingInv` — the inverse of an element `1 + c₁ + c₂ + ⋯`.

## Main results

* `Stacks.Chow.supportedClassRestriction_supportedLeftComp`,
  `Stacks.Chow.supportedClassRestriction_supportedRightComp` — `res(b ∘ c) = b · res(c)` and
  `res(c ∘ d) = res(c) · res(d)`.
* `Stacks.Chow.localizedGradingOp_mul`, `Stacks.Chow.localizedGradingOp_one`,
  `Stacks.Chow.localizedGrading_ext_op`.
* `Stacks.Chow.localizedGrading_mul_def` — the product is `Stacks.Chow.localizedGradingCutoffMul`.
* `Stacks.Chow.localizedGrading_isUnit_of_fst_zero` — `1 + c₁ + c₂ + ⋯` is a unit.
* `AlgebraicGeometry.supportedPerfect_isZero_derivedPullback_compl` — `E|_{X ∖ Z} = 0` for
  `E ∈ D_{Z,perf}(𝒪_X)`.

## Implementation notes

The ring structure is an instance on `localizedBivariantGrading C (gysinSystemOfInvertible C) sZ
sX f hf 1` itself, so that the total localized Chern class of
`Stacks.Chow.LocalizedChernData.totalLocalizedChern` at `p = 1` is an element of the ring with no
conversion; its additive group is the product group of the abbreviation.

The source's display of Stacks 0FA0 for `p = q = 1` has output cutoff `p + q = 2` and would push
the degree-`1` part of a product to `A¹(X)`; the target of Stacks 0FES keeps it localized, so the
product here is the one with output cutoff `1`. It uses the same three maps: in degree
`n ≥ p + q - 1` one of `i ≥ p` and `j ≥ q` always holds.

## References

* [Stacks Project, Tag 0FES](https://stacks.math.columbia.edu/tag/0FES)
* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 0FA1](https://stacks.math.columbia.edu/tag/0FA1)
* [Stacks Project, Tag 0FEP](https://stacks.math.columbia.edu/tag/0FEP)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Congruences -/

section Congr

variable {C : ChowSituation.{u}} {G : GysinSystem C}

/-- The cap operation of a finite sum of bivariant classes is the sum of the cap operations. -/
theorem BivariantClass.sum_cap {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
    {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
    {hf : f ≫ sY = sX} {p : ℤ} {ι : Type*} (s : Finset ι)
    (c : ι → BivariantClass C G sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    (∑ i ∈ s, c i).cap g k α = ∑ i ∈ s, (c i).cap g k α := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, BivariantClass.add_cap, ih]

/-- Heterogeneously equal Chow cohomology classes of equal degrees operate heterogeneously equally
on every test scheme. -/
theorem BivariantClass.idRule_heq_of_class_heq {X : Scheme.{u}} {sX : X ⟶ C.S}
    [LocallyOfFiniteType sX] {p p' : ℤ} (hp : p = p') {c : chowCohomologyComponent C G sX p}
    {c' : chowCohomologyComponent C G sX p'} (hc : c ≍ c') {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    c.idRule C sX G g k α ≍ c'.idRule C sX G g k α := by
  subst hp
  cases hc
  rfl

/-- **Stacks 0B76 (1) for the operation of a Chow cohomology class**, with the test morphism of
the source of the proper morphism given up to equality: for `h : T' ⟶ T` proper and
`g' = h ≫ g`, the operation of `x` commutes with `h_*`. -/
theorem BivariantClass.idRule_chowPush_heq {X : Scheme.{u}} {sX : X ⟶ C.S}
    [LocallyOfFiniteType sX] {p : ℤ} (x : chowCohomologyComponent C G sX p) {T T' : Scheme.{u}}
    (g : T ⟶ X) [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h] (g' : T' ⟶ X)
    [LocallyOfFiniteType g'] (hg : g' = h ≫ g) (hh : h ≫ g ≫ sX = g' ≫ sX) (k : ℤ)
    (β : chowGroup C (g' ≫ sX) k) :
    x.idRule C sX G g k (chowPush C (g' ≫ sX) (g ≫ sX) h hh k β) ≍
      chowPush C (g' ≫ sX) (g ≫ sX) h hh (k - p) (x.idRule C sX G g' k β) := by
  subst hg
  exact heq_of_eq (x.idRule_properNaturality C sX G g h k _ _ β)

/-- Transport along an equality of degrees in a product of two graded families acts on each
factor. -/
theorem gradedDegreeCast_prod_fst_heq {A B : ℤ → Type*} [∀ k, AddCommGroup (A k)]
    [∀ k, AddCommGroup (B k)] {k l : ℤ} (h : k = l) (x : A k × B k) :
    (gradedDegreeCast (fun k ↦ A k × B k) h x).1 ≍ x.1 := by
  subst h
  rfl

/-- Transport along an equality of degrees in a product of two graded families acts on each
factor. -/
theorem gradedDegreeCast_prod_snd_heq {A B : ℤ → Type*} [∀ k, AddCommGroup (A k)]
    [∀ k, AddCommGroup (B k)] {k l : ℤ} (h : k = l) (x : A k × B k) :
    (gradedDegreeCast (fun k ↦ A k × B k) h x).2 ≍ x.2 := by
  subst h
  rfl

end Congr

/-! ### The restrictions to `Z` -/

section Restriction

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : Z ⟶ X) [IsClosedImmersion f]
  (hf : f ≫ sX = sZ)

/-- **The restriction `res : A^p(Z ⟶ X) ⟶ A^p(Z)` of Stacks 0FA1**, read against the structure
morphism `sZ` of `Z` rather than `f ≫ sX`: the restriction of the first factor in the third
multiplication `(c, c') ↦ res(c) ∘ c'` of Stacks 0FA0 (`Stacks.Chow.supportedMul`). -/
def supportedClassRestriction (p : ℤ) :
    BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf p →+
      chowCohomologyComponent C (gysinSystemOfInvertible C) sZ p :=
  (bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 Z) hf hf p).toAddMonoidHom.comp
    (closedImmersionChowCohomologyRestriction C (gysinSystemOfInvertible C) sZ sX f hf p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C))

/-- **The restriction `res : A^p(X) ⟶ A^p(Z)` of Stacks 0B7F** along `f`, read against the
structure morphism `sZ` of `Z` rather than `f ≫ sX`: the restriction of the first factor in the
second multiplication `(d, c) ↦ res(d) ∘ c` of Stacks 0FA0 (`Stacks.Chow.ambientSupportedMul`). -/
def ambientClassRestriction (p : ℤ) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) sX p →+
      chowCohomologyComponent C (gysinSystemOfInvertible C) sZ p :=
  (bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 Z) hf hf p).toAddMonoidHom.comp
    (chowCohomologyRestriction C (gysinSystemOfInvertible C) sX f p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C))

variable {C sZ sX f hf}

/-- The third multiplication of Stacks 0FA0 is the composition after the restriction of the first
factor. -/
theorem supportedMul_eq_supportedLeftComp {p q : ℤ}
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf p)
    (c' : BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf q) :
    supportedMul C sZ sX f hf c c' =
      supportedLeftComp C sZ sX f hf (supportedClassRestriction C sZ sX f hf p c) c' :=
  rfl

/-- The second multiplication of Stacks 0FA0 is the composition after the restriction of the
first factor. -/
theorem ambientSupportedMul_eq_supportedLeftComp {p q : ℤ}
    (d : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf q) :
    ambientSupportedMul C sZ sX f hf d c =
      supportedLeftComp C sZ sX f hf (ambientClassRestriction C sZ sX f hf p d) c :=
  rfl

omit [IsClosedImmersion f] in
/-- The two projections of `Z ×_X T`, for a test scheme `g : T ⟶ Z`, agree after `g`, `f` being a
monomorphism. -/
theorem pullbackFst_eq_pullbackSnd_comp [Mono f] {T : Scheme.{u}} (g : T ⟶ Z) :
    pullback.fst f (g ≫ f) = pullback.snd f (g ≫ f) ≫ g :=
  (cancel_mono f).1 (by simp [pullback.condition])

omit [LocallyOfFiniteType sZ] [IsClosedImmersion f] in
/-- The base change `Z ×_X T ⟶ T` of `f` along `g ≫ f` lies over the base, read through `sZ`. -/
theorem pullbackSnd_comp_comp_sZ [Mono f] {T : Scheme.{u}} (g : T ⟶ Z) :
    pullback.snd f (g ≫ f) ≫ g ≫ sZ = pullback.fst f (g ≫ f) ≫ sZ := by
  rw [pullbackFst_eq_pullbackSnd_comp g, Category.assoc]

/-- **Stacks 0FA1 on the test schemes, read over `sZ`.** The operation of `res(c) ∈ A^p(Z)` on a
test scheme `g : T ⟶ Z` is the cap operation of `c` on `g ≫ f`, pushed forward along the
isomorphism `Z ×_X T ⟶ T`. -/
theorem supportedClassRestriction_idRule {p : ℤ}
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf p) {T : Scheme.{u}}
    (g : T ⟶ Z) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sZ) k)
    (α' : chowGroup C ((g ≫ f) ≫ sX) k) (hα : α' ≍ α) :
    (supportedClassRestriction C sZ sX f hf p c).idRule C sZ (gysinSystemOfInvertible C) g k α ≍
      chowPush C (pullback.fst f (g ≫ f) ≫ sZ) (g ≫ sZ) (pullback.snd f (g ≫ f))
        (pullbackSnd_comp_comp_sZ g) (k - p) (c.cap (g ≫ f) k α') := by
  subst hf
  change (bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 Z) rfl rfl p
    (closedImmersionChowCohomologyRestriction C (gysinSystemOfInvertible C) _ sX f rfl p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)).idRule C _ _ g k α ≍ _
  rw [BivariantClass.idRule_bivariantClassCongrBase,
    closedImmersionChowCohomologyRestriction_idRule]
  refine (chowGroupCongr_heq C _ _ _).trans ?_
  refine chowPush_heq C _ _ _ rfl rfl rfl ?_
  refine BivariantClass.cap_heq_congr c (g ≫ f) rfl _ _ ?_
  exact (chowGroupCongr_heq C _ _ _).trans ((chowGroupCongr_heq C _ _ _).trans hα.symm)

/-- **Stacks 0B7F on the test schemes, read over `sZ`.** The operation of `res(d) ∈ A^p(Z)` on a
test scheme `g : T ⟶ Z` is the operation of `d` on `g ≫ f`. -/
theorem ambientClassRestriction_idRule {p : ℤ}
    (d : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p) {T : Scheme.{u}}
    (g : T ⟶ Z) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sZ) k)
    (α' : chowGroup C ((g ≫ f) ≫ sX) k) (hα : α' ≍ α) :
    (ambientClassRestriction C sZ sX f hf p d).idRule C sZ (gysinSystemOfInvertible C) g k α ≍
      d.idRule C sX (gysinSystemOfInvertible C) (g ≫ f) k α' := by
  subst hf
  change (bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 Z) rfl rfl p
    (chowCohomologyRestriction C (gysinSystemOfInvertible C) sX f p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) d)).idRule C _ _ g k α ≍ _
  rw [BivariantClass.idRule_bivariantClassCongrBase, chowCohomologyRestriction_idRule]
  refine (chowGroupCongr_heq C _ _ _).trans ?_
  refine IdentityCapRule.heq_congr C sX _ rfl rfl ?_
  exact (chowGroupCongr_heq C _ _ _).trans ((chowGroupCongr_heq C _ _ _).trans hα.symm)

/-- Transport of a Chow class of `T` along `g ≫ sZ = (g ≫ f) ≫ sX` changes nothing. -/
private theorem chowGroupCongr_comp_heq (hf : f ≫ sX = sZ) {T : Scheme.{u}} (g : T ⟶ Z)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sZ) k) :
    chowGroupCongr C (show g ≫ sZ = (g ≫ f) ≫ sX by rw [Category.assoc, hf]) k α ≍ α :=
  chowGroupCongr_heq C _ _ _

/-- **The restriction of a composition `b ∘ c`**: for `b ∈ A^p(Z)` and `c ∈ A^q(Z ⟶ X)`,
`res(b ∘ c) = b · res(c)` in `A^{p+q}(Z)`. -/
theorem supportedClassRestriction_supportedLeftComp {p q : ℤ}
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sZ p)
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf q) :
    supportedClassRestriction C sZ sX f hf (p + q) (supportedLeftComp C sZ sX f hf b c) =
      b.mulId C sZ (supportedClassRestriction C sZ sX f hf q c) := by
  refine BivariantClass.eq_of_idRule_eq C sZ _ _ _ fun {T} g _ k α ↦ eq_of_heq ?_
  have hα := chowGroupCongr_comp_heq hf g k α
  refine (supportedClassRestriction_idRule _ g k α _ hα).trans ?_
  refine HEq.trans ?_ (BivariantClass.idRule_mulId C sZ b _ g k α).symm
  refine (chowPush_heq C (pullback.snd f (g ≫ f)) (pullbackSnd_comp_comp_sZ g)
    (pullbackSnd_comp_comp_sZ g) rfl rfl (by ring)
    (supportedLeftComp_cap C sZ sX f hf b c (g ≫ f) k _)).trans ?_
  refine HEq.trans ?_ (IdentityCapRule.heq_congr C sZ _ rfl rfl
    (supportedClassRestriction_idRule c g k α _ hα)).symm
  refine (HEq.trans ?_ (b.idRule_chowPush_heq g (pullback.snd f (g ≫ f))
    (pullback.fst f (g ≫ f)) (pullbackFst_eq_pullbackSnd_comp g) (pullbackSnd_comp_comp_sZ g)
    (k - q) _).symm)
  rfl

/-- **The restriction of a composition `c ∘ d`**: for `c ∈ A^p(Z ⟶ X)` and `d ∈ A^q(X)`,
`res(c ∘ d) = res(c) · res(d)` in `A^{p+q}(Z)`. -/
theorem supportedClassRestriction_supportedRightComp {p q : ℤ}
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf p)
    (d : chowCohomologyComponent C (gysinSystemOfInvertible C) sX q) :
    supportedClassRestriction C sZ sX f hf (p + q) (supportedRightComp C sZ sX f hf c d) =
      (supportedClassRestriction C sZ sX f hf p c).mulId C sZ
        (ambientClassRestriction C sZ sX f hf q d) := by
  refine BivariantClass.eq_of_idRule_eq C sZ _ _ _ fun {T} g _ k α ↦ eq_of_heq ?_
  have hα := chowGroupCongr_comp_heq hf g k α
  refine (supportedClassRestriction_idRule _ g k α _ hα).trans ?_
  refine HEq.trans ?_ (BivariantClass.idRule_mulId C sZ _ _ g k α).symm
  refine (chowPush_heq C (pullback.snd f (g ≫ f)) (pullbackSnd_comp_comp_sZ g)
    (pullbackSnd_comp_comp_sZ g) rfl rfl (by ring)
    (supportedRightComp_cap C sZ sX f hf c d (g ≫ f) k _)).trans ?_
  exact (supportedClassRestriction_idRule c g (k - q) _ _
    (ambientClassRestriction_idRule d g k α _ hα).symm).symm

/-- **The restriction of `1 ∈ A^0(X)` is `1 ∈ A^0(Z)`.** -/
theorem ambientClassRestriction_bivariantIdentityClassOfInvertible :
    ambientClassRestriction C sZ sX f hf 0 (bivariantIdentityClassOfInvertible C sX) =
      bivariantIdentityClassOfInvertible C sZ := by
  refine BivariantClass.eq_of_idRule_eq C sZ _ _ _ fun {T} g _ k α ↦ eq_of_heq ?_
  have hα := chowGroupCongr_comp_heq hf g k α
  refine (ambientClassRestriction_idRule _ g k α _ hα).trans ?_
  refine (idRule_bivariantIdentityClassOfInvertible_heq C sX (g ≫ f) k _).trans ?_
  exact hα.trans (idRule_bivariantIdentityClassOfInvertible_heq C sZ g k α).symm

/-- The restriction to `Z` commutes with the transport along an equality of degrees. -/
theorem ambientClassRestriction_bivariantClassDegreeCongr {p p' : ℤ} (h : p = p')
    (d : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p) :
    ambientClassRestriction C sZ sX f hf p'
        (bivariantClassDegreeCongr C _ sX sX (𝟙 X) (Category.id_comp sX) h d) =
      bivariantClassDegreeCongr C _ sZ sZ (𝟙 Z) (Category.id_comp sZ) h
        (ambientClassRestriction C sZ sX f hf p d) := by
  subst h
  rfl

/-- The restriction to `Z` respects heterogeneous equality of classes of equal degrees. -/
theorem ambientClassRestriction_heq {p p' : ℤ} (hp : p = p')
    {d : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p}
    {d' : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p'} (hd : d ≍ d') :
    ambientClassRestriction C sZ sX f hf p d ≍ ambientClassRestriction C sZ sX f hf p' d' := by
  subst hp
  cases hd
  rfl

/-- **The projection formula along `Z ×_X T ⟶ T`.** For `d ∈ A^p(X)`, a test scheme `t : T ⟶ X`
and `β ∈ CH_k(Z ×_X T)`, the operation of `d` on the pushforward of `β` to `T` is the
pushforward of the operation of `res(d) ∈ A^p(Z)` on `β`. -/
theorem idRule_chowPush_pullbackSnd {p : ℤ}
    (d : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p) {T : Scheme.{u}}
    (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ) (β : chowGroup C (pullback.fst f t ≫ sZ) k) :
    d.idRule C sX (gysinSystemOfInvertible C) t k
        (chowPush C (pullback.fst f t ≫ sZ) (t ≫ sX) (pullback.snd f t)
          (pullbackSnd_comp_structureMorphism hf t) k β) =
      chowPush C (pullback.fst f t ≫ sZ) (t ≫ sX) (pullback.snd f t)
        (pullbackSnd_comp_structureMorphism hf t) (k - p)
        ((ambientClassRestriction C sZ sX f hf p d).idRule C sZ (gysinSystemOfInvertible C)
          (pullback.fst f t) k β) := by
  have hs : pullback.fst f t ≫ sZ = (pullback.fst f t ≫ f) ≫ sX := by
    rw [Category.assoc, hf]
  have hβ := chowGroupCongr_comp_heq hf (pullback.fst f t) k β
  have hh : pullback.snd f t ≫ t ≫ sX = (pullback.fst f t ≫ f) ≫ sX := by
    rw [← hs, pullbackSnd_comp_structureMorphism hf t]
  refine eq_of_heq ?_
  refine (IdentityCapRule.heq_congr C sX _ rfl rfl
    (chowPush_heq C (pullback.snd f t) _ hh hs rfl rfl hβ.symm)).trans ?_
  refine (d.idRule_chowPush_heq t (pullback.snd f t) (pullback.fst f t ≫ f) pullback.condition hh
    k _).trans ?_
  exact chowPush_heq C (pullback.snd f t) _ _ hs.symm rfl rfl
    (ambientClassRestriction_idRule d (pullback.fst f t) k β _ hβ).symm

end Restriction

/-! ### The operation of `A⁽¹⁾(Z ⟶ X)` on the test schemes -/

section Operation

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : Z ⟶ X) [IsClosedImmersion f]
  (hf : f ≫ sX = sZ) {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t]

/-- The graded group `CH_k(T) × CH_k(Z ×_X T)` of a test scheme `t : T ⟶ X`, on which
`A⁽¹⁾(Z ⟶ X)` operates. -/
abbrev localizedGradingTestGroup (k : ℤ) : Type u :=
  chowGroup C (t ≫ sX) k × chowGroup C (pullback.fst f t ≫ sZ) k

/-- **The operation of an element of `A⁽¹⁾(Z ⟶ X)` on a test scheme** `t : T ⟶ X`, with
`i : Z ×_X T ⟶ T` the base change of `f`: the graded cap family on
`CH_*(T) × CH_*(Z ×_X T)` whose index-`0` component is `(x, y) ↦ (a₀ ∩ x, res(a₀) ∩ y)` and whose
index-`n` component for `n ≥ 1` is `(x, y) ↦ (0, aₙ ∩ (x + i_* y))`. -/
def localizedGradingOp (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1) :
    GradedCapFamily (localizedGradingTestGroup C sZ sX f t) := fun k n =>
  match n with
  | 0 => ((a.1 ⟨((0 : ℕ) : ℤ), by norm_num⟩).idRule C sX (gysinSystemOfInvertible C) t k).prodMap
      ((ambientClassRestriction C sZ sX f hf _ (a.1 ⟨((0 : ℕ) : ℤ), by norm_num⟩)).idRule C sZ
        (gysinSystemOfInvertible C) (pullback.fst f t) k)
  | n + 1 => (AddMonoidHom.inr _ _).comp
      (((a.2 ⟨((n + 1 : ℕ) : ℤ), by omega⟩).cap t k).comp
        (AddMonoidHom.fst _ _ + (chowPush C (pullback.fst f t ≫ sZ) (t ≫ sX) (pullback.snd f t)
          (pullbackSnd_comp_structureMorphism hf t) k).comp (AddMonoidHom.snd _ _)))

variable {C sZ sX f hf t}

/-- The index-`0` component of the operation: `(x, y) ↦ (a₀ ∩ x, res(a₀) ∩ y)`. -/
theorem localizedGradingOp_zero
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1) (k : ℤ)
    (xy : localizedGradingTestGroup C sZ sX f t k) :
    localizedGradingOp C sZ sX f hf t a k 0 xy =
      ((a.1 ⟨((0 : ℕ) : ℤ), by norm_num⟩).idRule C sX (gysinSystemOfInvertible C) t k xy.1,
        (ambientClassRestriction C sZ sX f hf _ (a.1 ⟨((0 : ℕ) : ℤ), by norm_num⟩)).idRule C sZ
          (gysinSystemOfInvertible C) (pullback.fst f t) k xy.2) :=
  rfl

/-- The index-`n` component of the operation for `n ≥ 1`: `(x, y) ↦ (0, aₙ ∩ (x + i_* y))`. -/
theorem localizedGradingOp_of_pos
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1) (k : ℤ) {n : ℕ}
    (hn : 1 ≤ n) (xy : localizedGradingTestGroup C sZ sX f t k) :
    localizedGradingOp C sZ sX f hf t a k n xy =
      (0, (a.2 ⟨(n : ℤ), by omega⟩).cap t k (xy.1 + chowPush C (pullback.fst f t ≫ sZ) (t ≫ sX)
        (pullback.snd f t) (pullbackSnd_comp_structureMorphism hf t) k xy.2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

/-- The first component of the operation vanishes in positive index, and on elements with first
component zero. -/
theorem localizedGradingOp_fst_eq_zero
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1) (k : ℤ) (n : ℕ)
    (xy : localizedGradingTestGroup C sZ sX f t k) (h : 1 ≤ n ∨ xy.1 = 0) :
    (localizedGradingOp C sZ sX f hf t a k n xy).1 = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [localizedGradingOp_zero, h.resolve_left (by omega), map_zero]
  · rw [localizedGradingOp_of_pos a k hn]

end Operation

/-! ### Bookkeeping of the sums -/

/-- Reindexing a sum over `0 ≤ i ≤ n` by `j = n - i`. -/
theorem sum_Icc_zero_eq_sum_range_sub {M : Type*} [AddCommMonoid M] (F : ℤ → M) (n : ℕ) :
    ∑ i ∈ Finset.Icc (0 : ℤ) n, F i = ∑ j ∈ Finset.range (n + 1), F ((n : ℤ) - j) := by
  refine Finset.sum_nbij' (fun i ↦ ((n : ℤ) - i).toNat) (fun j ↦ (n : ℤ) - j) ?_ ?_ ?_ ?_ ?_ <;>
    intro i hi <;> simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢
  · omega
  · omega
  · omega
  · omega
  · congr 1
    omega

/-- Transport along an equality of degrees in a product of two graded families preserves the
vanishing of the first factor. -/
theorem gradedDegreeCast_prod_fst_eq_zero {A B : ℤ → Type*} [∀ k, AddCommGroup (A k)]
    [∀ k, AddCommGroup (B k)] {k l : ℤ} (h : k = l) (x : A k × B k) (hx : x.1 = 0) :
    (gradedDegreeCast (fun k ↦ A k × B k) h x).1 = 0 := by
  subst h
  exact hx

/-! ### The ring structure -/

section Ring

variable {C : ChowSituation.{u}} {Z X : Scheme.{u}} {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ]
  {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {f : Z ⟶ X} [IsClosedImmersion f]
  {hf : f ≫ sX = sZ}

/-- **The product of `A⁽¹⁾(Z ⟶ X)`**: the multiplication of Stacks 0FA0 with output cutoff `1`
(`Stacks.Chow.localizedGradingCutoffMul`), which keeps every degree `n ≥ 1` localized. -/
instance instMulLocalizedGradingOne :
    Mul (localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1) :=
  ⟨localizedGradingCutoffMul C sZ sX f hf 1 (by norm_num)⟩

/-- **The unit of `A⁽¹⁾(Z ⟶ X)`**: the class `1 ∈ A⁰(X)` in degree `0`, and zero in every other
degree. -/
instance instOneLocalizedGradingOne :
    One (localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1) :=
  ⟨(fun i ↦ if h : i.1 = 0 then
      bivariantClassDegreeCongr C _ sX sX (𝟙 X) (Category.id_comp sX) h.symm
        (bivariantIdentityClassOfInvertible C sX)
    else 0, 0)⟩

/-- The product of `A⁽¹⁾(Z ⟶ X)` is the multiplication with output cutoff `1`. -/
theorem localizedGrading_mul_def
    (a b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1) :
    a * b = localizedGradingCutoffMul C sZ sX f hf 1 (by norm_num) a b :=
  rfl

/-- The degree-`0` component of `1 ∈ A⁽¹⁾(Z ⟶ X)` is `1 ∈ A⁰(X)`. -/
theorem localizedGrading_one_fst_of_eq {i : {i : ℤ // i < ((1 : ℕ) : ℤ)}} (h : i.1 = 0) :
    (1 : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1).1 i =
      bivariantClassDegreeCongr C _ sX sX (𝟙 X) (Category.id_comp sX) h.symm
        (bivariantIdentityClassOfInvertible C sX) :=
  dite_eq_left h

/-- The components of `1 ∈ A⁽¹⁾(Z ⟶ X)` in negative degrees vanish. -/
theorem localizedGrading_one_fst_of_ne {i : {i : ℤ // i < ((1 : ℕ) : ℤ)}} (h : i.1 ≠ 0) :
    (1 : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1).1 i = 0 :=
  dite_eq_right h

/-- The components of `1 ∈ A⁽¹⁾(Z ⟶ X)` in positive degrees vanish. -/
theorem localizedGrading_one_snd (i : {i : ℤ // ((1 : ℕ) : ℤ) ≤ i}) :
    (1 : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1).2 i = 0 :=
  rfl

/-- The operation of the degree-`0` component of a product `a b` is the composite of those of
`a` and `b`. -/
theorem localizedGrading_mul_fst_zero_idRule
    (a b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1)
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (x : chowGroup C (g ≫ sX) k) :
    ((a * b).1 ⟨((0 : ℕ) : ℤ), by norm_num⟩).idRule C sX (gysinSystemOfInvertible C) g k x ≍
      (a.1 ⟨((0 : ℕ) : ℤ), by norm_num⟩).idRule C sX (gysinSystemOfInvertible C) g
        (k - ((0 : ℕ) : ℤ))
        ((b.1 ⟨((0 : ℕ) : ℤ), by norm_num⟩).idRule C sX (gysinSystemOfInvertible C) g k x) := by
  have h0 : Finset.Icc (0 : ℤ) ((0 : ℕ) : ℤ) = {0} := by simp
  rw [localizedGrading_mul_def, localizedGradingCutoffMul_fst, h0, Finset.sum_singleton]
  refine (BivariantClass.idRule_bivariantClassDegreeCongr C _ sX _ _ g k x).trans ?_
  refine (BivariantClass.idRule_mulId C sX _ _ g k x).trans ?_
  rw [localizedGradingPush_of_lt _ (by norm_num), localizedGradingPush_of_lt _ (by norm_num)]
  refine (BivariantClass.idRule_heq_of_class_heq rfl
    (congr_arg_heq a.1 (Subtype.ext (by norm_num))) g _ _).trans ?_
  exact IdentityCapRule.heq_congr C sX _ rfl (by norm_num)
    (BivariantClass.idRule_heq_of_class_heq (by norm_num)
      (congr_arg_heq b.1 (Subtype.ext (by norm_num))) g k x)

section Term

variable (a b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1)
  {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)

private theorem term_heq_right_comp {i₁ i₁' i₂ i₂' : ℤ} (e₁ : i₁ = i₁') (e₂ : i₂ = i₂')
    (h₁ : ((1 : ℕ) : ℤ) ≤ i₁) (h₁' : ((1 : ℕ) : ℤ) ≤ i₁') (h₂ : i₂ < ((1 : ℕ) : ℤ))
    (h₂' : i₂' < ((1 : ℕ) : ℤ)) (z : chowGroup C (t ≫ sX) k) :
    (a.2 ⟨i₁, h₁⟩).cap t (k - i₂)
        ((b.1 ⟨i₂, h₂⟩).idRule C sX (gysinSystemOfInvertible C) t k z) ≍
      (a.2 ⟨i₁', h₁'⟩).cap t (k - i₂')
        ((b.1 ⟨i₂', h₂'⟩).idRule C sX (gysinSystemOfInvertible C) t k z) := by
  subst e₁ e₂
  rfl

private theorem term_heq_left_comp {i₁ i₁' i₂ i₂' : ℤ} (e₁ : i₁ = i₁') (e₂ : i₂ = i₂')
    (h₁ : i₁ < ((1 : ℕ) : ℤ)) (h₁' : i₁' < ((1 : ℕ) : ℤ)) (h₂ : ((1 : ℕ) : ℤ) ≤ i₂)
    (h₂' : ((1 : ℕ) : ℤ) ≤ i₂') (z : chowGroup C (t ≫ sX) k) :
    (ambientClassRestriction C sZ sX f hf i₁ (a.1 ⟨i₁, h₁⟩)).idRule C sZ
        (gysinSystemOfInvertible C) (pullback.fst f t) (k - i₂) ((b.2 ⟨i₂, h₂⟩).cap t k z) ≍
      (ambientClassRestriction C sZ sX f hf i₁' (a.1 ⟨i₁', h₁'⟩)).idRule C sZ
        (gysinSystemOfInvertible C) (pullback.fst f t) (k - i₂') ((b.2 ⟨i₂', h₂'⟩).cap t k z) := by
  subst e₁ e₂
  rfl

private theorem term_heq_mul {i₁ i₁' i₂ i₂' : ℤ} (e₁ : i₁ = i₁') (e₂ : i₂ = i₂')
    (h₁ : ((1 : ℕ) : ℤ) ≤ i₁) (h₁' : ((1 : ℕ) : ℤ) ≤ i₁') (h₂ : ((1 : ℕ) : ℤ) ≤ i₂)
    (h₂' : ((1 : ℕ) : ℤ) ≤ i₂') (z : chowGroup C (t ≫ sX) k) :
    (a.2 ⟨i₁, h₁⟩).cap t (k - i₂)
        (chowPush C (pullback.fst f t ≫ sZ) (t ≫ sX) (pullback.snd f t)
          (pullbackSnd_comp_structureMorphism hf t) (k - i₂) ((b.2 ⟨i₂, h₂⟩).cap t k z)) ≍
      (a.2 ⟨i₁', h₁'⟩).cap t (k - i₂')
        (chowPush C (pullback.fst f t ≫ sZ) (t ≫ sX) (pullback.snd f t)
          (pullbackSnd_comp_structureMorphism hf t) (k - i₂') ((b.2 ⟨i₂', h₂'⟩).cap t k z)) := by
  subst e₁ e₂
  rfl

/-- The summand `j = 0` of the component of index `n + 1` of the operation of a product: the
summand `aₙ₊₁ ∘ b₀`. -/
private theorem localizedGradingOp_mul_term_zero (n : ℕ)
    (xy : localizedGradingTestGroup C sZ sX f t k)
    (hn : ((1 + 1 : ℕ) : ℤ) ≤ ((n + 1 : ℕ) : ℤ) + 1)
    (hk : k - ((0 : ℕ) : ℤ) - ((n + 1 - 0 : ℕ) : ℤ) = k - ((n + 1 : ℕ) : ℤ)) :
    (localizedGradingTerm C sZ sX f hf a b hn (((n + 1 : ℕ) : ℤ) - (0 : ℕ))).cap t k
        (xy.1 + chowPush C (pullback.fst f t ≫ sZ) (t ≫ sX) (pullback.snd f t)
          (pullbackSnd_comp_structureMorphism hf t) k xy.2) ≍
      (capTo (localizedGradingOp C sZ sX f hf t a) (n + 1 - 0) hk
        (localizedGradingOp C sZ sX f hf t b k 0 xy)).2 := by
  rw [localizedGradingTerm_of_le_of_lt a b hn (by push_cast; omega) (by push_cast; omega)]
  refine (supportedRightComp_cap C sZ sX f hf _ _ t k _).trans ?_
  rw [capTo_def]
  refine HEq.trans ?_ (gradedDegreeCast_prod_snd_heq _ _).symm
  rw [localizedGradingOp_of_pos a _ (by omega), localizedGradingOp_zero]
  dsimp only
  rw [← idRule_chowPush_pullbackSnd, ← map_add]
  exact term_heq_right_comp a b t k (by push_cast; omega) (by push_cast; omega) _ _ _ _ _

/-- The summand `j = n + 1` of the component of index `n + 1` of the operation of a product: the
summand `res(a₀) ∘ bₙ₊₁`. -/
private theorem localizedGradingOp_mul_term_last (n : ℕ)
    (xy : localizedGradingTestGroup C sZ sX f t k)
    (hn : ((1 + 1 : ℕ) : ℤ) ≤ ((n + 1 : ℕ) : ℤ) + 1)
    (hk : k - ((n + 1 : ℕ) : ℤ) - ((n + 1 - (n + 1) : ℕ) : ℤ) = k - ((n + 1 : ℕ) : ℤ)) :
    (localizedGradingTerm C sZ sX f hf a b hn (((n + 1 : ℕ) : ℤ) - (n + 1 : ℕ))).cap t k
        (xy.1 + chowPush C (pullback.fst f t ≫ sZ) (t ≫ sX) (pullback.snd f t)
          (pullbackSnd_comp_structureMorphism hf t) k xy.2) ≍
      (capTo (localizedGradingOp C sZ sX f hf t a) (n + 1 - (n + 1)) hk
        (localizedGradingOp C sZ sX f hf t b k (n + 1) xy)).2 := by
  rw [localizedGradingTerm_of_lt a b hn (by push_cast; omega) (by push_cast; omega),
    ambientSupportedMul_eq_supportedLeftComp]
  refine (supportedLeftComp_cap C sZ sX f hf _ _ t k _).trans ?_
  rw [capTo_congr_index _ (Nat.sub_self (n + 1)), capTo_def]
  refine HEq.trans ?_ (gradedDegreeCast_prod_snd_heq _ _).symm
  rw [localizedGradingOp_zero, localizedGradingOp_of_pos b _ (by omega)]
  exact term_heq_left_comp a b t k (by push_cast; omega) (by push_cast; omega) _ _ _ _ _

/-- The summand `0 < j < n + 1` of the component of index `n + 1` of the operation of a product:
the summand `res(aₙ₊₁₋ⱼ) ∘ bⱼ = aₙ₊₁₋ⱼ ∘ f_* bⱼ`. -/
private theorem localizedGradingOp_mul_term_mid (n j : ℕ) (hj0 : 0 < j) (hjn : j < n + 1)
    (xy : localizedGradingTestGroup C sZ sX f t k)
    (hn : ((1 + 1 : ℕ) : ℤ) ≤ ((n + 1 : ℕ) : ℤ) + 1)
    (hk : k - (j : ℤ) - ((n + 1 - j : ℕ) : ℤ) = k - ((n + 1 : ℕ) : ℤ)) :
    (localizedGradingTerm C sZ sX f hf a b hn (((n + 1 : ℕ) : ℤ) - j)).cap t k
        (xy.1 + chowPush C (pullback.fst f t ≫ sZ) (t ≫ sX) (pullback.snd f t)
          (pullbackSnd_comp_structureMorphism hf t) k xy.2) ≍
      (capTo (localizedGradingOp C sZ sX f hf t a) (n + 1 - j) hk
        (localizedGradingOp C sZ sX f hf t b k j xy)).2 := by
  rw [localizedGradingTerm_of_le_of_le a b hn (by push_cast; omega) (by push_cast; omega),
    supportedMul_eq_supportedRightComp]
  refine (supportedRightComp_cap C sZ sX f hf _ _ t k _).trans ?_
  rw [idRule_properPushforwardChowCohomology, capTo_def]
  refine HEq.trans ?_ (gradedDegreeCast_prod_snd_heq _ _).symm
  rw [localizedGradingOp_of_pos a _ (by omega : 1 ≤ n + 1 - j),
    localizedGradingOp_of_pos b _ (by omega : 1 ≤ j)]
  dsimp only
  rw [zero_add]
  exact term_heq_mul a b t k (by push_cast; omega) (by push_cast; omega) _ _ _ _ _

/-- The summand of index `j` of the component of index `n + 1` of the operation of a product. -/
theorem localizedGradingOp_mul_term (n j : ℕ) (hj : j ≤ n + 1)
    (xy : localizedGradingTestGroup C sZ sX f t k)
    (hd : (((n + 1 : ℕ) : ℤ) - j) + (((n + 1 : ℕ) : ℤ) - (((n + 1 : ℕ) : ℤ) - j)) =
      ((n + 1 : ℕ) : ℤ))
    (hn : ((1 + 1 : ℕ) : ℤ) ≤ ((n + 1 : ℕ) : ℤ) + 1)
    (hk : k - (j : ℤ) - ((n + 1 - j : ℕ) : ℤ) = k - ((n + 1 : ℕ) : ℤ)) :
    (bivariantClassDegreeCongr C _ sZ sX f hf hd
        (localizedGradingTerm C sZ sX f hf a b hn (((n + 1 : ℕ) : ℤ) - j))).cap t k
        (xy.1 + chowPush C (pullback.fst f t ≫ sZ) (t ≫ sX) (pullback.snd f t)
          (pullbackSnd_comp_structureMorphism hf t) k xy.2) =
      (capTo (localizedGradingOp C sZ sX f hf t a) (n + 1 - j) hk
        (localizedGradingOp C sZ sX f hf t b k j xy)).2 := by
  refine eq_of_heq ((bivariantClassDegreeCongr_cap C _ _ _ _ _ _ _ t k _).trans ?_)
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact localizedGradingOp_mul_term_zero a b t k n xy hn hk
  rcases eq_or_lt_of_le hj with rfl | hjn
  · exact localizedGradingOp_mul_term_last a b t k n xy hn hk
  · exact localizedGradingOp_mul_term_mid a b t k n j hj0 hjn xy hn hk

end Term

/-- **The operation of a product is the convolution of the operations.** -/
theorem localizedGradingOp_mul
    (a b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1)
    {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] :
    localizedGradingOp C sZ sX f hf t (a * b) =
      localizedGradingOp C sZ sX f hf t a * localizedGradingOp C sZ sX f hf t b := by
  funext k m
  refine AddMonoidHom.ext fun xy ↦ ?_
  rw [gradedCap_mul_apply]
  rcases m with _ | n
  · -- index `0`: the degree-`0` components multiply
    rw [Finset.sum_range_one, convolveTerm_of_le _ _ _ le_rfl, capTo_def]
    refine Prod.ext (eq_of_heq ?_) (eq_of_heq ?_)
    · refine HEq.trans ?_ (gradedDegreeCast_prod_fst_heq _ _).symm
      rw [localizedGradingOp_zero, localizedGradingOp_zero, localizedGradingOp_zero]
      exact localizedGrading_mul_fst_zero_idRule a b t k xy.1
    · refine HEq.trans ?_ (gradedDegreeCast_prod_snd_heq _ _).symm
      rw [localizedGradingOp_zero, localizedGradingOp_zero, localizedGradingOp_zero]
      dsimp only
      have hs : pullback.fst f t ≫ sZ = (pullback.fst f t ≫ f) ≫ sX := by
        rw [Category.assoc, hf]
      have hy := chowGroupCongr_comp_heq hf (pullback.fst f t) k xy.2
      refine (ambientClassRestriction_idRule _ _ k _ _ hy).trans ?_
      refine (localizedGrading_mul_fst_zero_idRule a b _ k _).trans ?_
      refine HEq.trans ?_ (ambientClassRestriction_idRule _ (pullback.fst f t) _ _
        (chowGroupCongr C hs _ _) (chowGroupCongr_heq C hs _ _)).symm
      exact IdentityCapRule.heq_congr C sX _ rfl rfl
        ((ambientClassRestriction_idRule _ _ k _ _ hy).symm.trans
          (chowGroupCongr_heq C hs _ _).symm)
  · -- index `n + 1`
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum, localizedGradingOp_of_pos _ _ (by omega)]
      refine (Finset.sum_eq_zero fun j hj ↦ ?_).symm
      have hjm : j ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [convolveTerm_of_le _ _ _ hjm, capTo_def]
      refine gradedDegreeCast_prod_fst_eq_zero _ _ (localizedGradingOp_fst_eq_zero _ _ _ _ ?_)
      by_cases hj1 : 1 ≤ n + 1 - j
      · exact Or.inl hj1
      · exact Or.inr (localizedGradingOp_fst_eq_zero _ _ _ _ (Or.inl (by omega)))
    · rw [Prod.snd_sum, localizedGradingOp_of_pos _ _ (by omega)]
      dsimp only
      rw [localizedGrading_mul_def, localizedGradingCutoffMul_snd, BivariantClass.sum_cap,
        sum_Icc_zero_eq_sum_range_sub]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hjm : j ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [convolveTerm_of_le _ _ _ hjm]
      exact localizedGradingOp_mul_term a b t k n j hjm xy _ _ _

/-- The operation of a sum is the sum of the operations. -/
theorem localizedGradingOp_add
    (a b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1)
    {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] :
    localizedGradingOp C sZ sX f hf t (a + b) =
      localizedGradingOp C sZ sX f hf t a + localizedGradingOp C sZ sX f hf t b := by
  funext k m
  refine AddMonoidHom.ext fun xy ↦ ?_
  rcases m with _ | n
  · simp only [Pi.add_apply, AddMonoidHom.add_apply, localizedGradingOp_zero, Prod.fst_add,
      BivariantClass.idRule_add, map_add, Prod.mk_add_mk]
  · simp only [Pi.add_apply, AddMonoidHom.add_apply,
      localizedGradingOp_of_pos _ _ (by omega : 1 ≤ n + 1),
      Prod.mk_add_mk, add_zero, Prod.snd_add, BivariantClass.add_cap]

/-- The operation of `0` is zero. -/
theorem localizedGradingOp_zero_class {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] :
    localizedGradingOp C sZ sX f hf t 0 = 0 := by
  have h := localizedGradingOp_add (0 : localizedBivariantGrading C (gysinSystemOfInvertible C)
    sZ sX f hf 1) 0 t
  rw [add_zero] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

/-- **The operation of `1` is the identity.** -/
theorem localizedGradingOp_one {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] :
    localizedGradingOp C sZ sX f hf t 1 = 1 := by
  funext k m
  refine AddMonoidHom.ext fun xy ↦ ?_
  rcases m with _ | n
  · rw [gradedCap_one_apply_zero, localizedGradingOp_zero]
    refine Prod.ext (eq_of_heq ?_) (eq_of_heq ?_)
    · refine HEq.trans ?_ (gradedDegreeCast_prod_fst_heq _ _).symm
      rw [localizedGrading_one_fst_of_eq (i := ⟨((0 : ℕ) : ℤ), by norm_num⟩) (by norm_num)]
      exact (BivariantClass.idRule_bivariantClassDegreeCongr C _ sX _ _ t k _).trans
        (idRule_bivariantIdentityClassOfInvertible_heq C sX t k _)
    · refine HEq.trans ?_ (gradedDegreeCast_prod_snd_heq _ _).symm
      rw [localizedGrading_one_fst_of_eq (i := ⟨((0 : ℕ) : ℤ), by norm_num⟩) (by norm_num)]
      dsimp only
      rw [ambientClassRestriction_bivariantClassDegreeCongr,
        ambientClassRestriction_bivariantIdentityClassOfInvertible]
      exact (BivariantClass.idRule_bivariantClassDegreeCongr C _ sZ _ _ _ k _).trans
        (idRule_bivariantIdentityClassOfInvertible_heq C sZ _ k _)
  · rw [gradedCap_one_of_ne (by omega), localizedGradingOp_of_pos _ _ (by omega)]
    rfl

/-- The degree-`0` component of an element of `A⁽¹⁾(Z ⟶ X)` is determined by the index-`0`
components of its operations on the test schemes. -/
theorem localizedGrading_fst_zero_eq_of_op
    {a b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1}
    (h : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ),
      localizedGradingOp C sZ sX f hf t a k 0 = localizedGradingOp C sZ sX f hf t b k 0) :
    a.1 ⟨((0 : ℕ) : ℤ), by norm_num⟩ = b.1 ⟨((0 : ℕ) : ℤ), by norm_num⟩ := by
  refine BivariantClass.eq_of_idRule_eq C sX _ _ _ fun {T} g _ k x ↦ ?_
  have := congrArg Prod.fst (DFunLike.congr_fun (h g k)
    ((x, 0) : localizedGradingTestGroup C sZ sX f g k))
  rwa [localizedGradingOp_zero, localizedGradingOp_zero] at this

/-- The degree-`n` component, `n ≥ 1`, of an element of `A⁽¹⁾(Z ⟶ X)` is determined by the
index-`n` components of its operations on the test schemes. -/
theorem localizedGrading_snd_eq_of_op
    {a b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1} {n : ℕ}
    (hn : 1 ≤ n)
    (h : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ),
      localizedGradingOp C sZ sX f hf t a k n = localizedGradingOp C sZ sX f hf t b k n) :
    a.2 ⟨(n : ℤ), by omega⟩ = b.2 ⟨(n : ℤ), by omega⟩ := by
  refine BivariantClass.ext C _ _ _ _ _ _ fun {T} g _ k x ↦ ?_
  have := congrArg Prod.snd (DFunLike.congr_fun (h g k)
    ((x, 0) : localizedGradingTestGroup C sZ sX f g k))
  rwa [localizedGradingOp_of_pos _ _ hn, localizedGradingOp_of_pos _ _ hn, map_zero,
    add_zero] at this

/-- **An element of `A⁽¹⁾(Z ⟶ X)` is determined by its operations on the test schemes**, index by
index. -/
theorem localizedGrading_ext_op_index
    {a b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1}
    (h : ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ),
      localizedGradingOp C sZ sX f hf t a k n = localizedGradingOp C sZ sX f hf t b k n) :
    a = b := by
  refine Prod.ext (funext fun ⟨i, hi⟩ ↦ ?_) (funext fun ⟨i, hi⟩ ↦ ?_)
  · rcases lt_or_eq_of_le (show i ≤ 0 by omega) with hi0 | rfl
    · rw [chowCohomologyComponent_eq_zero_of_neg C _ sX hi0 (a.1 ⟨i, hi⟩),
        chowCohomologyComponent_eq_zero_of_neg C _ sX hi0 (b.1 ⟨i, hi⟩)]
    · exact localizedGrading_fst_zero_eq_of_op (h 0)
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = n := ⟨i.toNat, by omega⟩
    exact localizedGrading_snd_eq_of_op (by omega) (h n)

/-- **An element of `A⁽¹⁾(Z ⟶ X)` is determined by its operations on the test schemes.** -/
theorem localizedGrading_ext_op
    {a b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1}
    (h : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t],
      localizedGradingOp C sZ sX f hf t a = localizedGradingOp C sZ sX f hf t b) : a = b :=
  localizedGrading_ext_op_index fun n _ t _ k ↦ by rw [h t]

/-- **The ring `A⁽¹⁾(Z ⟶ X)`** of Stacks 0FES: the group
`A⁰(X) × ∏_{i ≥ 1} Aⁱ(Z ⟶ X)` (with the vanishing groups of negative degree) with the
multiplication of Stacks 0FA0 with output cutoff `1`, under which every degree `n ≥ 1` stays
localized, and unit `1 ∈ A⁰(X)`. The source omits the verification that the multiplications are
associative; here every ring axiom is the corresponding identity of the operations on the test
schemes (`Stacks.Chow.localizedGradingOp`), by `Stacks.Chow.localizedGrading_ext_op`. -/
instance instRingLocalizedGradingOne :
    Ring (localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1) where
  __ := (inferInstance : AddCommGroup
    (localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1))
  mul_assoc a b c := localizedGrading_ext_op fun t _ ↦ by
    simp only [localizedGradingOp_mul, mul_assoc]
  one_mul a := localizedGrading_ext_op fun t _ ↦ by
    rw [localizedGradingOp_mul, localizedGradingOp_one, one_mul]
  mul_one a := localizedGrading_ext_op fun t _ ↦ by
    rw [localizedGradingOp_mul, localizedGradingOp_one, mul_one]
  zero_mul a := localizedGrading_ext_op fun t _ ↦ by
    rw [localizedGradingOp_mul, localizedGradingOp_zero_class, zero_mul]
  mul_zero a := localizedGrading_ext_op fun t _ ↦ by
    rw [localizedGradingOp_mul, localizedGradingOp_zero_class, mul_zero]
  left_distrib a b c := localizedGrading_ext_op fun t _ ↦ by
    simp only [localizedGradingOp_mul, localizedGradingOp_add, mul_add]
  right_distrib a b c := localizedGrading_ext_op fun t _ ↦ by
    simp only [localizedGradingOp_mul, localizedGradingOp_add, add_mul]

/-- The operation on a test scheme, as an additive map. -/
def localizedGradingOpHom {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] :
    localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1 →+
      GradedCapFamily (localizedGradingTestGroup C sZ sX f t) where
  toFun := localizedGradingOp C sZ sX f hf t
  map_zero' := localizedGradingOp_zero_class t
  map_add' a b := localizedGradingOp_add a b t

/-- The operation on a test scheme, as a ring homomorphism. -/
def localizedGradingOpRingHom {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] :
    localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1 →+*
      GradedCapFamily (localizedGradingTestGroup C sZ sX f t) where
  toFun := localizedGradingOp C sZ sX f hf t
  map_one' := localizedGradingOp_one t
  map_mul' a b := localizedGradingOp_mul a b t
  map_zero' := localizedGradingOp_zero_class t
  map_add' a b := localizedGradingOp_add a b t

/-- The ring homomorphism `Stacks.Chow.localizedGradingOpRingHom` evaluates to the operation. -/
theorem localizedGradingOpRingHom_apply {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t]
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1) :
    localizedGradingOpRingHom t a = localizedGradingOp C sZ sX f hf t a :=
  rfl

/-! ### Units -/

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the ring structure on `localizedBivariantGrading` (`map_sub`)
/-- The operation of a difference is the difference of the operations. -/
private theorem localizedGradingOp_sub {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t]
    (a b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1) (k : ℤ) (l : ℕ) :
    localizedGradingOp C sZ sX f hf t (a - b) k l =
      localizedGradingOp C sZ sX f hf t a k l - localizedGradingOp C sZ sX f hf t b k l := by
  rw [← localizedGradingOpRingHom_apply, map_sub]
  rfl

/-- If the operations of `y` vanish in index `0`, those of `y ^ m` vanish in every index `< m`. -/
theorem localizedGradingOp_pow_of_lt
    {y : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1}
    (hy : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ),
      localizedGradingOp C sZ sX f hf t y k 0 = 0) (m : ℕ) {T : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] (k : ℤ) {l : ℕ} (hl : l < m) :
    localizedGradingOp C sZ sX f hf t (y ^ m) k l = 0 := by
  induction m generalizing k l with
  | zero => omega
  | succ m ih =>
    refine AddMonoidHom.ext fun xy ↦ ?_
    rw [pow_succ, ← localizedGradingOpRingHom_apply, map_mul, gradedCap_mul_apply,
      AddMonoidHom.zero_apply]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have hjl : j ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [convolveTerm_of_le _ _ _ hjl, capTo_def]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [localizedGradingOpRingHom_apply, localizedGradingOpRingHom_apply, hy t k,
        AddMonoidHom.zero_apply, map_zero, map_zero]
    · rw [localizedGradingOpRingHom_apply, ih _ (by omega), AddMonoidHom.zero_apply, map_zero]

/-- **The inverse of an element `1 + c₁ + c₂ + ⋯` of `A⁽¹⁾(Z ⟶ X)`**: for `a = 1 - y`, the element
whose degree-`0` component is `1` and whose degree-`n` component, `n ≥ 1`, is that of
`∑_{m ≤ n} yᵐ`. It is the inverse of `a` when the degree-`0` component of `a` is `1`
(`Stacks.Chow.localizedGrading_mul_inv`). -/
def localizedGradingInv (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1) :
    localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1 :=
  ((1 : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1).1,
    fun n ↦ (∑ m ∈ Finset.range (n.1.toNat + 1), (1 - a) ^ m).2 n)

/-- The degree-`0` component of `Stacks.Chow.localizedGradingInv a` is `1`. -/
theorem localizedGradingInv_fst
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1) :
    (localizedGradingInv a).1 =
      (1 : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1).1 :=
  rfl

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the ring structure on `localizedBivariantGrading`
/-- **An element `1 + c₁ + c₂ + ⋯` of `A⁽¹⁾(Z ⟶ X)` has `Stacks.Chow.localizedGradingInv` as a
right inverse.** -/
theorem localizedGrading_mul_inv
    {a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1}
    (ha : a.1 ⟨((0 : ℕ) : ℤ), by norm_num⟩ =
      (1 : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1).1
        ⟨((0 : ℕ) : ℤ), by norm_num⟩) :
    a * localizedGradingInv a = 1 := by
  set y := 1 - a with hy_def
  have hy : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ),
      localizedGradingOp C sZ sX f hf t y k 0 = 0 := by
    intro T t _ k
    refine AddMonoidHom.ext fun xy ↦ ?_
    rw [hy_def, localizedGradingOp_sub, AddMonoidHom.sub_apply, localizedGradingOp_zero,
      localizedGradingOp_zero, ha, sub_self, AddMonoidHom.zero_apply]
  -- the partial sums `Sₙ = ∑_{m ≤ n} yᵐ`
  have hS : ∀ (n l : ℕ), l ≤ n → ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t]
      (k : ℤ), localizedGradingOp C sZ sX f hf t (∑ m ∈ Finset.range (n + 1), y ^ m) k l =
        localizedGradingOp C sZ sX f hf t (∑ m ∈ Finset.range (l + 1), y ^ m) k l := by
    intro n l hln T t _ k
    rw [← localizedGradingOpRingHom_apply, ← localizedGradingOpRingHom_apply, map_sum, map_sum,
      Finset.sum_apply, Finset.sum_apply, Finset.sum_apply, Finset.sum_apply,
      ← Finset.sum_range_add_sum_Ico _ (show l + 1 ≤ n + 1 by omega), add_eq_left]
    refine Finset.sum_eq_zero fun m hm ↦ ?_
    rw [localizedGradingOpRingHom_apply,
      localizedGradingOp_pow_of_lt hy m t k (by have := (Finset.mem_Ico.mp hm).1; omega)]
  -- the inverse agrees with `Sₙ` in the indices `≤ n`
  have hb : ∀ (n l : ℕ), l ≤ n → ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t]
      (k : ℤ), localizedGradingOp C sZ sX f hf t (localizedGradingInv a) k l =
        localizedGradingOp C sZ sX f hf t (∑ m ∈ Finset.range (n + 1), y ^ m) k l := by
    intro n l hln T t _ k
    rw [hS n l hln t k]
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · refine AddMonoidHom.ext fun xy ↦ ?_
      rw [localizedGradingOp_zero, localizedGradingOp_zero, localizedGradingInv_fst, zero_add,
        Finset.sum_range_one, pow_zero]
    · refine AddMonoidHom.ext fun xy ↦ ?_
      rw [localizedGradingOp_of_pos _ _ hl, localizedGradingOp_of_pos _ _ hl]
      rfl
  refine localizedGrading_ext_op_index fun n T t _ k ↦ ?_
  rw [localizedGradingOp_mul]
  have hmul : (localizedGradingOp C sZ sX f hf t a * localizedGradingOp C sZ sX f hf t
      (localizedGradingInv a)) k n = (localizedGradingOp C sZ sX f hf t a *
        localizedGradingOp C sZ sX f hf t (∑ m ∈ Finset.range (n + 1), y ^ m)) k n :=
    gradedCap_mul_apply_congr (fun _ _ _ ↦ rfl) (fun l hl k' ↦ hb n l hl t k') k
  rw [hmul, ← localizedGradingOp_mul, show a = 1 - y by rw [hy_def, sub_sub_cancel],
    mul_neg_geom_sum, localizedGradingOp_sub,
    localizedGradingOp_pow_of_lt hy (n + 1) t k (by omega), sub_zero]

/-- **An element `1 + c₁ + c₂ + ⋯` of `A⁽¹⁾(Z ⟶ X)` is a unit**: an element whose degree-`0`
component is `1 ∈ A⁰(X)` is invertible, with inverse `Stacks.Chow.localizedGradingInv`. -/
theorem localizedGrading_isUnit_of_fst_zero
    {a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1}
    (ha : a.1 ⟨((0 : ℕ) : ℤ), by norm_num⟩ =
      (1 : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf 1).1
        ⟨((0 : ℕ) : ℤ), by norm_num⟩) :
    IsUnit a := by
  have h₁ := localizedGrading_mul_inv ha
  have h₂ := localizedGrading_mul_inv (a := localizedGradingInv a) rfl
  have h₃ : a = localizedGradingInv (localizedGradingInv a) := by
    calc a = a * (localizedGradingInv a * localizedGradingInv (localizedGradingInv a)) := by
          rw [h₂, mul_one]
      _ = localizedGradingInv (localizedGradingInv a) := by rw [← mul_assoc, h₁, one_mul]
  have h₄ : localizedGradingInv a * a = 1 :=
    (congrArg (localizedGradingInv a * ·) h₃).trans h₂
  exact ⟨⟨a, localizedGradingInv a, h₁, h₄⟩, rfl⟩

end Ring

end Stacks.Chow

/-! ### Supported perfect objects vanish off the support -/

namespace AlgebraicGeometry

open Stacks.Cohomology

attribute [local instance 10000] HasDerivedCategory.standard

/-- **An object whose cohomology sheaves are supported on a closed subscheme `Z` vanishes on
`X ∖ Z`**: its derived pullback to the open complement of `Z` is zero. The derived pullback along
an open immersion is restriction, which is exact and so computes the cohomology sheaves of the
restriction as the restrictions of the cohomology sheaves; these have vanishing stalks at every
point of `X ∖ Z`. -/
theorem isZero_derivedPullback_compl_of_supp_subset {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (E : DerivedCategory X.Modules)
    (hE : ∀ n : ℤ, SheafOfModules.supp
      ((DerivedCategory.homologyFunctor X.Modules n).obj E) ⊆ Set.range i.base) :
    IsZero ((DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X.toRingedSpace.ofRestrict (⟨(Set.range i.base)ᶜ,
        i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X.Opens).isOpenEmbedding)).obj E) := by
  have hsupp : CohomologySupportedOn (structureSheafRing X.toRingedSpace)
      (Set.range i.base) E := by
    intro n x hx
    have hx' : x ∉ SheafOfModules.supp
        ((DerivedCategory.homologyFunctor X.Modules n).obj E) := fun h ↦ hx (hE n h)
    simp only [SheafOfModules.supp, Set.mem_ofPred_eq, not_exists, not_not] at hx'
    refine (AddCommGrpCat.isZero_iff_subsingleton).2 ⟨fun a b ↦ ?_⟩
    rw [hx' a, hx' b]
  exact (Stacks.Cohomology.PushforwardRestriction.isZero_derived_restrict_compl_of_supported
    (structureSheafRing X.toRingedSpace) (Set.range i.base)
    i.isClosedEmbedding.isClosed_range E hsupp).of_iso
    ((DerivedOpenImmersion.derivedPullbackOpenRestrictionIso X.toRingedSpace _).app E)

/-- **A perfect object supported on a closed subscheme `Z` vanishes on `X ∖ Z`** (the input of
Remark 0FEP and Stacks 0FES): for `E ∈ D_{Z,perf}(𝒪_X)`, the derived pullback of `E` to the open
complement of `Z` is zero. This is the first alternative of condition (2) of Situation 0GUJ
(`Stacks.Chow.LocalizedChernData.IsZeroOnComplement`). -/
theorem supportedPerfect_isZero_derivedPullback_compl {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (E : supportedPerfectDerivedCategory i) :
    IsZero ((DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X.toRingedSpace.ofRestrict (⟨(Set.range i.base)ᶜ,
        i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X.Opens).isOpenEmbedding)).obj E.1) :=
  isZero_derivedPullback_compl_of_supp_subset i E.1 E.2.2

end AlgebraicGeometry

end
