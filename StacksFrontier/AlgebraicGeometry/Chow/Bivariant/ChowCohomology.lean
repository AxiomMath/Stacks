module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ChowCohomology

/-!
# Chow cohomology and the restriction maps of bivariant classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. For a scheme `X` locally
of finite type over `S` the Chow cohomology group `A^p(X)` is the bivariant group `A^p(X ⟶ X)` of
the identity, namely `Stacks.Chow.chowCohomologyComponent`, and `A^*(X)` is the graded group
`Stacks.Chow.chowCohomology`. Two special cases of the restriction map of Stacks 0F9Z are treated
here. For a closed immersion `i : Z ⟶ X` the restriction of a bivariant class `c ∈ A^p(Z ⟶ X)` is
a class `res(c) ∈ A^p(Z)` satisfying

  `res(c) ∩ α = c ∩ i_*α`   for `α ∈ CH_*(Z)`,

which is **Stacks 0FA1**; and for an arbitrary morphism `f : Y' ⟶ Y` there is a canonical map
`res : A^*(Y) ⟶ A^*(Y')`, often written `f^*`, which is **Stacks 0B7F**.

## Main definitions

* `Stacks.Chow.selfPullbackIso`, `Stacks.Chow.pullbackIdIso`, `Stacks.Chow.selfPullbackIdIso`,
  `Stacks.Chow.selfPullbackCompIdIso` — the canonical identifications of `Z` with the fibre
  products `Z ×_X Z`, `X ×_X Z` and `(Z ×_X Z) ×_Z Z` occurring in the two sides of that formula.
* `Stacks.Chow.pullbackIdBaseChangeIso` — the base change of a monomorphism `i : Z ⟶ X` along
  `X ×_X Z ⟶ X`, which is the morphism `Z ⟶ Z` the source pushes forward along.
* `Stacks.Chow.closedImmersionChowCohomologyRestriction` — **Stacks 0FA1**, the restriction map
  `A^p(Z ⟶ X) ⟶ A^p(Z)` of a closed immersion.
* `Stacks.Chow.chowCohomologyRestriction`, `Stacks.Chow.chowCohomologyTotalRestriction` —
  **Stacks 0B7F**, the restriction maps `A^p(Y) ⟶ A^p(Y')` and `A^*(Y) ⟶ A^*(Y')`.

## Main results

* `Stacks.Chow.bivariantRestrictionCap_id_eq_cap_properChowPushforward` — **Stacks 0FA1**, the
  formula `res(c) ∩ α = c ∩ i_*α`, both sides read in `CH_{k-p}(Z)` through the canonical
  identifications above.
* `Stacks.Chow.bivariantRestriction_cap_id_eq_cap_properChowPushforward`,
  `Stacks.Chow.closedImmersionChowCohomologyRestriction_cap` — the same formula for the restricted
  bivariant class `Stacks.Chow.bivariantRestriction` and for the restriction map into `A^p(Z)`.
* `Stacks.Chow.chowCohomologyRestriction_cap` — the cap formula `res(c) ∩ α = c ∩ α` of Stacks
  0F9Z for the restriction map of Stacks 0B7F.

## Implementation notes

### How the formula is stated

The cap operation of a bivariant class lands in the *chosen* categorical pullback, so the two
sides of `res(c) ∩ α = c ∩ i_*α` are not literally elements of the same group: with `res(c)` read
on the test scheme `𝟙 Z` the left-hand side lives on `(Z ×_X Z) ×_Z Z` and the right-hand side,
read on the test scheme `𝟙 X`, lives on `X ×_X Z`. Both fibre products are canonically isomorphic
to `Z` — for the first one because a monomorphism is its own kernel pair, Mathlib's
`CategoryTheory.IsKernelPair.id_of_mono` — and the statement pushes each side forward along the
inverse of its identification, so that the asserted equality is an equality in `CH_{k-p}(Z)`, as
in the source.

The formula is stated three times, for the three forms in which `res(c)` is available: for the
cap operation `Stacks.Chow.bivariantRestrictionCap` of the restriction, which is what the proof
works with and which determines the class by `Stacks.Chow.eq_of_isBivariantRestriction`; for the
class `Stacks.Chow.bivariantRestriction` itself, a class for `Z ×_X Z ⟶ Z`; and for the class in
`A^p(Z)` obtained from it by `Stacks.Chow.bivariantTransport` along `Z ×_X Z ≅ Z`, which is the
`res` of the source. In the last form the left-hand side is read on `Z` through `Z ×_Z Z ≅ Z`
instead.

### The one hypothesis

Forming `i_*α` needs an instance of Stacks 02S2 for `i`, which is
`Stacks.Chow.ProperPushforwardFactorsThroughRationalEquivalence` and is not formalized in this
repository; it is therefore a hypothesis, as it is an explicit argument of
`Stacks.Chow.properChowPushforward` itself. It occurs in the conclusion, so by proof irrelevance
the quantified statement is equivalent to the unconditional one once Stacks 02S2 lands. The
pushforwards along the three comparison isomorphisms need no such hypothesis: that case of
Stacks 02S2 is proved outright, as
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isIso`.

The proof is the source's: the restricted cap operation is the cap operation of `c` at the test
morphism `i` by Stacks 0F9Z, and the proper-pushforward axiom of `c` at the test morphism `𝟙 X`
and the proper morphism `i` turns `c ∩ i_*α` into the pushforward of `c ∩ α` along the base
change of `i`, which for a monomorphism is an isomorphism.

### The multiplicativity of `res` is not proved, so Stacks 0B7F is partial

Stacks 0B7F asks for the restriction map to be a map of `ℤ`-algebras. The map is given here and
the ring structure on `A^*` is `Stacks.Chow.chowCohomologyGRingOfInvertible` of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyCompositionRing`; what is missing is
that `res` respects it, that is `res(c · c') = res(c) · res(c')` and `res(1) = 1`. The attributes
are in phrase form accordingly.

What is proved of Stacks 0B7F is therefore: the canonical homomorphism of groups
`A^p(Y) ⟶ A^p(Y')` in each degree, the induced homomorphism of graded groups
`A^*(Y) ⟶ A^*(Y')`, and the cap formula `res(c) ∩ α = c ∩ α` that characterizes it.

### How Stacks 0B7F is built

`A^p(Y)` is the bivariant group of `𝟙 Y`, and the restriction map of Stacks 0F9Z along
`f : Y' ⟶ Y` produces a class for the base change `Y ×_Y Y' ⟶ Y'`, not for `𝟙 Y'`. The two
morphisms are isomorphic over `Y'` — the base change of an identity is one — and
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Transport` carries a bivariant class across such an
isomorphism, which is what turns the class of Stacks 0F9Z into one of `A^p(Y')`. The Gysin axiom
of a transported class is not a consequence of the axioms of the original, so the map carries the
isomorphism case of Stacks 02TA for the Gysin system, exactly as
`Stacks.Chow.bivariantRestriction` does.

## References

* [Stacks Project, Tag 0FA1](https://stacks.math.columbia.edu/tag/0FA1)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The fibre products of a monomorphism and of an identity -/

section Pullbacks

variable {Z X : Scheme.{u}} (i : Z ⟶ X)

/-- The identification `Z ≅ Z ×_X Z` of the source of a monomorphism with its self fibre product,
whose two projections are both the identity. -/
def selfPullbackIso [Mono i] : Z ≅ pullback i i :=
  (IsKernelPair.id_of_mono i).isoPullback

/-- The first projection of the self fibre product undoes the identification with `Z`. -/
@[reassoc (attr := simp)]
theorem selfPullbackIso_hom_fst [Mono i] : (selfPullbackIso i).hom ≫ pullback.fst i i = 𝟙 Z :=
  (IsKernelPair.id_of_mono i).isoPullback_hom_fst

/-- The second projection of the self fibre product undoes the identification with `Z`. -/
@[reassoc (attr := simp)]
theorem selfPullbackIso_hom_snd [Mono i] : (selfPullbackIso i).hom ≫ pullback.snd i i = 𝟙 Z :=
  (IsKernelPair.id_of_mono i).isoPullback_hom_snd

/-- The identification `Z ≅ X ×_X Z` of the source of `i : Z ⟶ X` with the base change of `i`
along the identity of `X`. -/
def pullbackIdIso : Z ≅ pullback i (𝟙 X) :=
  (IsPullback.of_horiz_isIso (fst := 𝟙 Z) (snd := i) (f := i) (g := 𝟙 X)
    ⟨by rw [Category.id_comp, Category.comp_id]⟩).isoPullback

/-- The first projection of `X ×_X Z` undoes the identification with `Z`. -/
@[reassoc (attr := simp)]
theorem pullbackIdIso_hom_fst : (pullbackIdIso i).hom ≫ pullback.fst i (𝟙 X) = 𝟙 Z :=
  IsPullback.isoPullback_hom_fst _

/-- The second projection of `X ×_X Z` is `i` under the identification with `Z`. -/
@[reassoc (attr := simp)]
theorem pullbackIdIso_hom_snd : (pullbackIdIso i).hom ≫ pullback.snd i (𝟙 X) = i :=
  IsPullback.isoPullback_hom_snd _

/-- The identification `Z ≅ (Z ×_X Z) ×_Z Z` of `Z` with the base change, along the identity of
`Z`, of the second projection of the self fibre product of a monomorphism. -/
def selfPullbackIdIso [Mono i] : Z ≅ pullback (pullback.snd i i) (𝟙 Z) :=
  (IsPullback.of_horiz_isIso (fst := (selfPullbackIso i).hom) (snd := 𝟙 Z)
    (f := pullback.snd i i) (g := 𝟙 Z) ⟨by simp⟩).isoPullback

/-- The first projection of `(Z ×_X Z) ×_Z Z` is the identification of `Z` with `Z ×_X Z`. -/
@[reassoc (attr := simp)]
theorem selfPullbackIdIso_hom_fst [Mono i] :
    (selfPullbackIdIso i).hom ≫ pullback.fst (pullback.snd i i) (𝟙 Z) = (selfPullbackIso i).hom :=
  IsPullback.isoPullback_hom_fst _

/-- The second projection of `(Z ×_X Z) ×_Z Z` undoes the identification with `Z`. -/
@[reassoc (attr := simp)]
theorem selfPullbackIdIso_hom_snd [Mono i] :
    (selfPullbackIdIso i).hom ≫ pullback.snd (pullback.snd i i) (𝟙 Z) = 𝟙 Z :=
  IsPullback.isoPullback_hom_snd _

/-- The identification `Z ≅ Z ×_X Z` of `Z` with the fibre product of `i` and `i ≫ 𝟙 X`, for a
monomorphism `i`. -/
def selfPullbackCompIdIso [Mono i] : Z ≅ pullback i (i ≫ 𝟙 X) :=
  (selfPullbackIso i).trans (pullback.congrHom rfl (Category.comp_id i)).symm

/-- The first projection of the fibre product of `i` and `i ≫ 𝟙 X` undoes the identification
with `Z`. -/
@[reassoc (attr := simp)]
theorem selfPullbackCompIdIso_hom_fst [Mono i] :
    (selfPullbackCompIdIso i).hom ≫ pullback.fst i (i ≫ 𝟙 X) = 𝟙 Z := by
  simp [selfPullbackCompIdIso]

/-- The second projection of the fibre product of `i` and `i ≫ 𝟙 X` undoes the identification
with `Z`. -/
@[reassoc (attr := simp)]
theorem selfPullbackCompIdIso_hom_snd [Mono i] :
    (selfPullbackCompIdIso i).hom ≫ pullback.snd i (i ≫ 𝟙 X) = 𝟙 Z := by
  simp [selfPullbackCompIdIso]

/-- The first projection of the fibre product of `i` and `i ≫ 𝟙 X` is the inverse of the
canonical identification with `Z`. -/
theorem selfPullbackCompIdIso_inv [Mono i] :
    (selfPullbackCompIdIso i).inv = pullback.fst i (i ≫ 𝟙 X) :=
  (cancel_epi (selfPullbackCompIdIso i).hom).mp (by simp)

/-- The base change of a monomorphism `i : Z ⟶ X` along the second projection `X ×_X Z ⟶ X`: an
isomorphism `Z ×_X Z ≅ X ×_X Z`, which is the morphism `Z ⟶ Z` of the source of Stacks 0FA1. -/
def pullbackIdBaseChangeIso [Mono i] : pullback i (i ≫ 𝟙 X) ≅ pullback i (𝟙 X) :=
  (selfPullbackCompIdIso i).symm.trans (pullbackIdIso i)

/-- The base change isomorphism `Z ×_X Z ≅ X ×_X Z` is compatible with the projections
to `Z`. -/
@[reassoc (attr := simp)]
theorem pullbackIdBaseChangeIso_hom_fst [Mono i] :
    (pullbackIdBaseChangeIso i).hom ≫ pullback.fst i (𝟙 X) = pullback.fst i (i ≫ 𝟙 X) := by
  simp [pullbackIdBaseChangeIso, selfPullbackCompIdIso_inv]

/-- The base change of a monomorphism along the second projection of `X ×_X Z` is again a base
change of it: the cartesian square the proper-pushforward axiom of a bivariant class is applied
to. -/
theorem pullbackIdBaseChangeIso_isPullback [Mono i] :
    IsPullback (pullback.snd i (i ≫ 𝟙 X)) (pullbackIdBaseChangeIso i).hom i
      (pullback.snd i (𝟙 X)) :=
  (IsKernelPair.id_of_mono i).of_iso (selfPullbackCompIdIso i) (Iso.refl Z) (pullbackIdIso i)
    (Iso.refl X) (by simp) (by simp [pullbackIdBaseChangeIso]) (by simp) (by simp)

/-- The comparison isomorphism `(Z ×_X Z) ×_Z Z ≅ Z ×_X Z` of the two fibre products through which
the restriction of a bivariant class along `i` operates at the test scheme `𝟙 Z`. -/
def selfRestrictionCompIso : pullback (pullback.snd i i) (𝟙 Z) ≅ pullback i i :=
  (pullbackLeftPullbackSndIso i i (𝟙 Z)).trans (pullback.congrHom rfl (Category.id_comp i))

/-- The comparison isomorphism `(Z ×_X Z) ×_Z Z ≅ Z ×_X Z` is compatible with the projections
to `Z`. -/
@[reassoc (attr := simp)]
theorem selfRestrictionCompIso_hom_fst :
    (selfRestrictionCompIso i).hom ≫ pullback.fst i i =
      pullback.fst (pullback.snd i i) (𝟙 Z) ≫ pullback.fst i i := by
  simp [selfRestrictionCompIso]

/-- The comparison isomorphism `(Z ×_X Z) ×_Z Z ≅ Z ×_X Z` is compatible with the projections
to the test scheme. -/
@[reassoc (attr := simp)]
theorem selfRestrictionCompIso_hom_snd :
    (selfRestrictionCompIso i).hom ≫ pullback.snd i i =
      pullback.snd (pullback.snd i i) (𝟙 Z) := by
  simp [selfRestrictionCompIso]

/-- The identification of `Z` with `(Z ×_X Z) ×_Z Z`, followed by the comparison isomorphism with
`Z ×_X Z`, is the identification of `Z` with its self fibre product. -/
theorem selfPullbackIdIso_hom_comp_selfRestrictionCompIso_hom [Mono i] :
    (selfPullbackIdIso i).hom ≫ (selfRestrictionCompIso i).hom = (selfPullbackIso i).hom := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- The structure morphisms of `(Z ×_X Z) ×_Z Z` and of `Z` over a scheme agree under the
canonical identification. -/
theorem selfPullbackIdIso_inv_comp [Mono i] {W : Scheme.{u}} (q : Z ⟶ W) :
    (selfPullbackIdIso i).inv ≫ q =
      pullback.fst (pullback.snd i i) (𝟙 Z) ≫ (pullback.fst i i ≫ q) := by
  rw [Iso.inv_comp_eq, selfPullbackIdIso_hom_fst_assoc, selfPullbackIso_hom_fst_assoc]

/-- The structure morphisms of `Z ×_X Z` and of `Z` over a scheme agree under the canonical
identification. -/
theorem selfPullbackIso_inv_comp [Mono i] {W : Scheme.{u}} (q : Z ⟶ W) :
    (selfPullbackIso i).inv ≫ q = pullback.fst i i ≫ q := by
  rw [Iso.inv_comp_eq, selfPullbackIso_hom_fst_assoc]

/-- The structure morphisms of `X ×_X Z` and of `Z` over a scheme agree under the canonical
identification. -/
theorem pullbackIdIso_inv_comp {W : Scheme.{u}} (q : Z ⟶ W) :
    (pullbackIdIso i).inv ≫ q = pullback.fst i (𝟙 X) ≫ q := by
  rw [Iso.inv_comp_eq, pullbackIdIso_hom_fst_assoc]

end Pullbacks

/-! ### The restriction of a bivariant class along a closed immersion -/

section ClosedImmersion

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X)
  [IsClosedImmersion i] (hi : i ≫ sX = sZ) (p : ℤ)

omit [LocallyOfFiniteType sZ] [LocallyOfFiniteType sX] [IsClosedImmersion i] in
include hi in
/-- The structure morphism of `Z` over the base, read on the test scheme of the restriction at the
identity. -/
theorem id_comp_comp_structureMorphism_eq : sZ = 𝟙 Z ≫ (i ≫ sX) := by
  rw [Category.id_comp, hi]

omit [LocallyOfFiniteType sZ] [LocallyOfFiniteType sX] [IsClosedImmersion i] in
include hi in
/-- The structure morphism of `Z` over the base, read through the test morphism `i ≫ 𝟙 X`. -/
theorem comp_id_comp_structureMorphism_eq : sZ = (i ≫ 𝟙 X) ≫ sX := by
  rw [Category.comp_id, hi]

/-- **Stacks 0FA1.** For a closed immersion `i : Z ⟶ X` of schemes locally of finite type over
the base and a bivariant class `c` of degree `p` for `i`, the restriction `res(c)` of `c` along
`i` — a class of degree `p` for `Z ×_X Z ⟶ Z`, whose cap operation at the test scheme `𝟙 Z` is
read on `Z` through the canonical identification `(Z ×_X Z) ×_Z Z ≅ Z` — satisfies

  `res(c) ∩ α = c ∩ i_*α`

in `CH_{k-p}(Z)` for every `α ∈ CH_k(Z)`, the right-hand side being read on `Z` through the
canonical identification `X ×_X Z ≅ Z`. -/
@[stacks 0FA1]
theorem bivariantRestrictionCap_id_eq_cap_properChowPushforward
    (c : BivariantClass C G sZ sX i hi p) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sZ sX i hi k)
    (α : chowGroup C sZ k) :
    chowPushforwardOfIso C (pullback.fst (pullback.snd i i) (𝟙 Z) ≫ (pullback.fst i i ≫ sZ)) sZ
        (selfPullbackIdIso i).inv (selfPullbackIdIso_inv_comp i sZ) (k - p)
        (bivariantRestrictionCap C G sZ sX i hi i p c (𝟙 Z) k
          (chowGroupCongr C (id_comp_comp_structureMorphism_eq C sZ sX i hi) k α)) =
      chowPushforwardOfIso C (pullback.fst i (𝟙 X) ≫ sZ) sZ (pullbackIdIso i).inv
        (pullbackIdIso_inv_comp i sZ) (k - p)
        (c.cap (𝟙 X) k (chowGroupCongr C (Category.id_comp sX).symm k
          (properChowPushforward C sZ sX i hi k hfac α))) := by
  have hcompId : i ≫ 𝟙 X = i := Category.comp_id i
  have hbaseW : (selfRestrictionCompIso i).inv ≫
      (pullback.fst (pullback.snd i i) (𝟙 Z) ≫ (pullback.fst i i ≫ sZ)) =
        pullback.fst i i ≫ sZ := by
    rw [Iso.inv_comp_eq, selfRestrictionCompIso_hom_fst_assoc]
  have hfacW := properPushforwardFactorsThroughRationalEquivalence_of_isIso C
    (pullback.fst i i ≫ sZ) (pullback.fst (pullback.snd i i) (𝟙 Z) ≫ (pullback.fst i i ≫ sZ))
    (selfRestrictionCompIso i).inv hbaseW (k - p)
  have hu' : i ≫ (𝟙 X ≫ sX) = (i ≫ 𝟙 X) ≫ sX := by rw [Category.comp_id, Category.id_comp]
  have hfacA : ProperPushforwardFactorsThroughRationalEquivalence C ((i ≫ 𝟙 X) ≫ sX)
      (𝟙 X ≫ sX) i hu' k :=
    properPushforwardFactorsThroughRationalEquivalence_congr_base C
      (comp_id_comp_structureMorphism_eq C sZ sX i hi) (Category.id_comp sX).symm i hi hu' k hfac
  have hbaseB : (pullbackIdBaseChangeIso i).hom ≫ (pullback.fst i (𝟙 X) ≫ sZ) =
      pullback.fst i (i ≫ 𝟙 X) ≫ sZ := by
    rw [pullbackIdBaseChangeIso_hom_fst_assoc]
  have hfacB := properPushforwardFactorsThroughRationalEquivalence_of_isIso C
    (pullback.fst i (i ≫ 𝟙 X) ≫ sZ) (pullback.fst i (𝟙 X) ≫ sZ)
    (pullbackIdBaseChangeIso i).hom hbaseB (k - p)
  have hbaseCongr : (pullback.congrHom (rfl : i = i) hcompId).hom ≫ (pullback.fst i i ≫ sZ) =
      pullback.fst i (i ≫ 𝟙 X) ≫ sZ := by simp
  have hisoL : (selfRestrictionCompIso i).inv ≫ (selfPullbackIdIso i).inv =
      (selfPullbackIso i).inv := by
    rw [← Iso.trans_inv,
      Iso.ext (by simpa using selfPullbackIdIso_hom_comp_selfRestrictionCompIso_hom i :
        ((selfPullbackIdIso i).trans (selfRestrictionCompIso i)).hom = (selfPullbackIso i).hom)]
  have hisoR : (pullbackIdBaseChangeIso i).hom ≫ (pullbackIdIso i).inv =
      (pullback.congrHom (rfl : i = i) hcompId).hom ≫ (selfPullbackIso i).inv := by
    simp [pullbackIdBaseChangeIso, selfPullbackCompIdIso]
  rw [bivariantRestrictionCap_eq C G sZ sX i hi i p c (𝟙 Z) i (Category.id_comp i)
      (by rw [Category.id_comp]) (selfRestrictionCompIso i) (selfRestrictionCompIso_hom_fst i)
      (selfRestrictionCompIso_hom_snd i) k hbaseW hfacW,
    properChowPushforward_eq_chowPushforwardOfIso C (pullback.fst i i ≫ sZ)
      (pullback.fst (pullback.snd i i) (𝟙 Z) ≫ (pullback.fst i i ≫ sZ))
      (selfRestrictionCompIso i).inv hbaseW (k - p) hfacW,
    chowPushforwardOfIso_comp_apply C (pullback.fst i i ≫ sZ)
      (pullback.fst (pullback.snd i i) (𝟙 Z) ≫ (pullback.fst i i ≫ sZ)) sZ
      (selfRestrictionCompIso i).inv (selfPullbackIdIso i).inv hbaseW
      (selfPullbackIdIso_inv_comp i sZ) (k - p),
    chowPushforwardOfIso_congr_apply C (pullback.fst i i ≫ sZ) sZ
      ((selfRestrictionCompIso i).inv ≫ (selfPullbackIdIso i).inv) (selfPullbackIso i).inv hisoL
      (by rw [Category.assoc, selfPullbackIdIso_inv_comp i sZ, hbaseW])
      (selfPullbackIso_inv_comp i sZ) (k - p),
    chowGroupCongr_chowGroupCongr C (id_comp_comp_structureMorphism_eq C sZ sX i hi)
      (by rw [Category.id_comp] : 𝟙 Z ≫ (i ≫ sX) = i ≫ sX) k α,
    properChowPushforward_chowGroupCongr C (comp_id_comp_structureMorphism_eq C sZ sX i hi)
      (Category.id_comp sX).symm i hi hu' k hfac hfacA α,
    c.proper_naturality (𝟙 X) i (pullbackIdBaseChangeIso i).hom
      (pullbackIdBaseChangeIso_isPullback i) (pullbackIdBaseChangeIso_hom_fst i) k hfacA hfacB,
    properChowPushforward_eq_chowPushforwardOfIso C (pullback.fst i (i ≫ 𝟙 X) ≫ sZ)
      (pullback.fst i (𝟙 X) ≫ sZ) (pullbackIdBaseChangeIso i).hom hbaseB (k - p) hfacB,
    chowPushforwardOfIso_comp_apply C (pullback.fst i (i ≫ 𝟙 X) ≫ sZ)
      (pullback.fst i (𝟙 X) ≫ sZ) sZ (pullbackIdBaseChangeIso i).hom (pullbackIdIso i).inv
      hbaseB (pullbackIdIso_inv_comp i sZ) (k - p),
    chowPushforwardOfIso_congr_apply C (pullback.fst i (i ≫ 𝟙 X) ≫ sZ) sZ
      ((pullbackIdBaseChangeIso i).hom ≫ (pullbackIdIso i).inv)
      ((pullback.congrHom (rfl : i = i) hcompId).hom ≫ (selfPullbackIso i).inv) hisoR
      (by rw [Category.assoc, pullbackIdIso_inv_comp i sZ, hbaseB])
      (by rw [Category.assoc, selfPullbackIso_inv_comp i sZ, hbaseCongr]) (k - p),
    ← chowPushforwardOfIso_comp_apply C (pullback.fst i (i ≫ 𝟙 X) ≫ sZ)
      (pullback.fst i i ≫ sZ) sZ (pullback.congrHom (rfl : i = i) hcompId).hom
      (selfPullbackIso i).inv hbaseCongr (selfPullbackIso_inv_comp i sZ) (k - p),
    chowPushforwardOfIso_congrHom_cap C G sZ sX i hi p c hcompId hbaseCongr k α
      (comp_id_comp_structureMorphism_eq C sZ sX i hi) hi.symm]

/-- **Stacks 0FA1** for the restricted class itself: the bivariant class
`Stacks.Chow.bivariantRestriction` of `c` along the closed immersion `i`, read at the test scheme
`𝟙 Z`, satisfies `res(c) ∩ α = c ∩ i_*α` in `CH_{k-p}(Z)`. -/
@[stacks 0FA1 "for the restricted bivariant class"]
theorem bivariantRestriction_cap_id_eq_cap_properChowPushforward
    (hgys : G.IsNaturalUnderBaseChangeIso) (c : BivariantClass C G sZ sX i hi p) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sZ sX i hi k)
    (α : chowGroup C sZ k) :
    chowPushforwardOfIso C (pullback.fst (pullback.snd i i) (𝟙 Z) ≫ (pullback.fst i i ≫ sZ)) sZ
        (selfPullbackIdIso i).inv (selfPullbackIdIso_inv_comp i sZ) (k - p)
        ((bivariantRestriction C G sZ sX i hi i p hgys c).cap (𝟙 Z) k
          (chowGroupCongr C (id_comp_comp_structureMorphism_eq C sZ sX i hi) k α)) =
      chowPushforwardOfIso C (pullback.fst i (𝟙 X) ≫ sZ) sZ (pullbackIdIso i).inv
        (pullbackIdIso_inv_comp i sZ) (k - p)
        (c.cap (𝟙 X) k (chowGroupCongr C (Category.id_comp sX).symm k
          (properChowPushforward C sZ sX i hi k hfac α))) :=
  bivariantRestrictionCap_id_eq_cap_properChowPushforward C G sZ sX i hi p c k hfac α

/-- **Stacks 0FA1.** The restriction map `res : A^p(Z ⟶ X) ⟶ A^p(Z)` along a closed immersion
`i : Z ⟶ X`, a homomorphism of groups: the restriction map of Stacks 0F9Z along `i`, followed by
the transport of a bivariant class along the canonical isomorphism `Z ×_X Z ≅ Z`. -/
@[stacks 0FA1 "the restriction map to A^p(Z)"]
def closedImmersionChowCohomologyRestriction (hgys : G.IsNaturalUnderBaseChangeIso) :
    BivariantClass C G sZ sX i hi p →+ chowCohomologyComponent C G (i ≫ sX) p :=
  (bivariantTransportAddHom C G (pullback.fst i i ≫ sZ) (i ≫ sX) (i ≫ sX)
      (pullback.snd i i) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi i) (𝟙 Z)
      (Category.id_comp (i ≫ sX)) (asIso (pullback.snd i i)) (by simp) p hgys).comp
    (bivariantRestrictionAddHom C G sZ sX i hi i p hgys)

omit [LocallyOfFiniteType sZ] [LocallyOfFiniteType sX] [IsClosedImmersion i] in
include hi in
/-- The identification `Z ×_Z Z ≅ Z` of the test scheme of a class in `A^p(Z)` at the identity is
a morphism over the base. -/
theorem identityBaseChangeIso_id_comp_base :
    (identityBaseChangeIso (𝟙 Z)).hom ≫ sZ = pullback.fst (𝟙 Z) (𝟙 Z) ≫ (i ≫ sX) := by
  rw [id_comp_comp_structureMorphism_eq C sZ sX i hi]
  exact identityBaseChangeIso_hom_comp_base C (i ≫ sX) (𝟙 Z)

/-- **Stacks 0FA1.** The restriction map `res : A^p(Z ⟶ X) ⟶ A^p(Z)` of a closed immersion
satisfies `res(c) ∩ α = c ∩ i_*α` in `CH_{k-p}(Z)` for every `α ∈ CH_k(Z)`, both sides being read
on `Z` through the canonical identifications `Z ×_Z Z ≅ Z` and `X ×_X Z ≅ Z`. -/
@[stacks 0FA1 "the cap formula for the restriction map to A^p(Z)"]
theorem closedImmersionChowCohomologyRestriction_cap (hgys : G.IsNaturalUnderBaseChangeIso)
    (c : BivariantClass C G sZ sX i hi p) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sZ sX i hi k)
    (α : chowGroup C sZ k) :
    chowPushforwardOfIso C (pullback.fst (𝟙 Z) (𝟙 Z) ≫ (i ≫ sX)) sZ
        (identityBaseChangeIso (𝟙 Z)).hom
        (identityBaseChangeIso_id_comp_base C sZ sX i hi) (k - p)
        ((closedImmersionChowCohomologyRestriction C G sZ sX i hi p hgys c).cap (𝟙 Z) k
          (chowGroupCongr C (id_comp_comp_structureMorphism_eq C sZ sX i hi) k α)) =
      chowPushforwardOfIso C (pullback.fst i (𝟙 X) ≫ sZ) sZ (pullbackIdIso i).inv
        (pullbackIdIso_inv_comp i sZ) (k - p)
        (c.cap (𝟙 X) k (chowGroupCongr C (Category.id_comp sX).symm k
          (properChowPushforward C sZ sX i hi k hfac α))) := by
  have hsnd : pullback.snd (pullback.snd i i) (𝟙 Z) = (selfPullbackIdIso i).inv :=
    (cancel_epi (selfPullbackIdIso i).hom).mp (by simp)
  have hκbase := transportPullbackIso_hom_comp_base C (pullback.fst i i ≫ sZ) (i ≫ sX) (i ≫ sX)
    (pullback.snd i i) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi i) (𝟙 Z)
    (Category.id_comp (i ≫ sX)) (asIso (pullback.snd i i)) (by simp) (𝟙 Z)
  have hcap : (closedImmersionChowCohomologyRestriction C G sZ sX i hi p hgys c).cap (𝟙 Z) k
        (chowGroupCongr C (id_comp_comp_structureMorphism_eq C sZ sX i hi) k α) =
      chowPushforwardOfIso C
        (pullback.fst (pullback.snd i i) (𝟙 Z) ≫ (pullback.fst i i ≫ sZ))
        (pullback.fst (𝟙 Z) (𝟙 Z) ≫ (i ≫ sX))
        (transportPullbackIso (pullback.snd i i) (𝟙 Z) (asIso (pullback.snd i i)) (by simp)
          (𝟙 Z)).hom hκbase (k - p)
        (bivariantRestrictionCap C G sZ sX i hi i p c (𝟙 Z) k
          (chowGroupCongr C (id_comp_comp_structureMorphism_eq C sZ sX i hi) k α)) :=
    rfl
  rw [hcap, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_congr_apply C
      (pullback.fst (pullback.snd i i) (𝟙 Z) ≫ (pullback.fst i i ≫ sZ)) sZ _
      (selfPullbackIdIso i).inv (by rw [← hsnd]; simp) _ (selfPullbackIdIso_inv_comp i sZ)
      (k - p)]
  exact bivariantRestrictionCap_id_eq_cap_properChowPushforward C G sZ sX i hi p c k hfac α

end ClosedImmersion

/-! ### The restriction map on Chow cohomology -/

section Restriction

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Y Y' : Scheme.{u}} (sY : Y ⟶ C.S)
  [LocallyOfFiniteType sY] (f : Y' ⟶ Y) [LocallyOfFiniteType f] (p : ℤ)

/-- **Stacks 0B7F.** The restriction map `res : A^p(Y) ⟶ A^p(Y')` along a morphism `f : Y' ⟶ Y`
of schemes locally of finite type over the base, a homomorphism of groups: the special case
`X = Y`, `f = 𝟙 Y` of the restriction map of Stacks 0F9Z, followed by the transport of a
bivariant class along the canonical isomorphism `Y ×_Y Y' ≅ Y'`. It is often written `f^*`.

The tag asserts more, namely that the induced map `A^*(Y) ⟶ A^*(Y')` of the graded groups is a
map of `ℤ`-algebras. The multiplication is composition of bivariant classes, and the graded ring
it makes of `A^*(Y)` is `Stacks.Chow.chowCohomologyGRing` of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyCompositionRing`, hypothesis-free for
the Gysin system this repository constructs as `Stacks.Chow.chowCohomologyGRingOfInvertible`. Only
the additive map is given here; that it respects that multiplication is
`Stacks.Chow.chowCohomologyRestriction_chowCohomologyRingMul` of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyMultiplicative`, which assembles the
`ℤ`-algebra map of the tag as
`Stacks.Chow.chowCohomologyTotalRestrictionAlgHomOfInvertible`. -/
@[stacks 0B7F "the canonical map"]
def chowCohomologyRestriction (hgys : G.IsNaturalUnderBaseChangeIso) :
    chowCohomologyComponent C G sY p →+ chowCohomologyComponent C G (f ≫ sY) p :=
  (bivariantTransportAddHom C G (pullback.fst (𝟙 Y) f ≫ sY) (f ≫ sY) (f ≫ sY)
      (pullback.snd (𝟙 Y) f)
      (pullbackSnd_comp_structureMorphism_eq C sY sY (𝟙 Y) (Category.id_comp sY) f) (𝟙 Y')
      (Category.id_comp (f ≫ sY)) (identityBaseChangeIso f) (by simp) p hgys).comp
    (bivariantRestrictionAddHom C G sY sY (𝟙 Y) (Category.id_comp sY) f p hgys)

/-- **Stacks 0B7F.** The restriction map on Chow cohomology satisfies the cap formula of Stacks
0F9Z: `res(c) ∩ α = c ∩ α` for every `α ∈ CH_k(T)` and every test scheme `g : T ⟶ Y'`, both
sides read in `CH_{k-p}(T)` through the canonical identifications `Y' ×_{Y'} T ≅ T` and
`Y ×_Y T ≅ T`. -/
@[stacks 0B7F "the cap formula for the canonical map"]
theorem chowCohomologyRestriction_cap (hgys : G.IsNaturalUnderBaseChangeIso)
    (c : chowCohomologyComponent C G sY p) {T : Scheme.{u}} (g : T ⟶ Y') [LocallyOfFiniteType g]
    (k : ℤ)
    (α : chowGroup C (g ≫ (f ≫ sY)) k) :
    chowPushforwardOfIso C (pullback.fst (𝟙 Y') g ≫ (f ≫ sY)) (g ≫ (f ≫ sY))
        (identityBaseChangeIso g).hom (identityBaseChangeIso_hom_comp_base C (f ≫ sY) g) (k - p)
        ((chowCohomologyRestriction C G sY f p hgys c).cap g k α) =
      chowPushforwardOfIso C (pullback.fst (𝟙 Y) (g ≫ f) ≫ sY) (g ≫ (f ≫ sY))
        (identityBaseChangeIso (g ≫ f)).hom
        (by rw [← Category.assoc]; exact identityBaseChangeIso_hom_comp_base C sY (g ≫ f))
        (k - p) (c.cap (g ≫ f) k (chowGroupCongr C (Category.assoc g f sY).symm k α)) := by
  have hcap : (chowCohomologyRestriction C G sY f p hgys c).cap g k α =
      chowPushforwardOfIso C
        (pullback.fst (pullback.snd (𝟙 Y) f) g ≫ (pullback.fst (𝟙 Y) f ≫ sY))
        (pullback.fst (𝟙 Y') g ≫ (f ≫ sY))
        (transportPullbackIso (pullback.snd (𝟙 Y) f) (𝟙 Y') (identityBaseChangeIso f)
          (by simp) g).hom
        (transportPullbackIso_hom_comp_base C (pullback.fst (𝟙 Y) f ≫ sY) (f ≫ sY) (f ≫ sY)
          (pullback.snd (𝟙 Y) f)
          (pullbackSnd_comp_structureMorphism_eq C sY sY (𝟙 Y) (Category.id_comp sY) f) (𝟙 Y')
          (Category.id_comp (f ≫ sY)) (identityBaseChangeIso f) (by simp) g)
        (k - p)
        (chowPushforwardOfIso C (pullback.fst (𝟙 Y) (g ≫ f) ≫ sY)
          (pullback.fst (pullback.snd (𝟙 Y) f) g ≫ (pullback.fst (𝟙 Y) f ≫ sY))
          (pullbackLeftPullbackSndIso (𝟙 Y) f g).inv (by simp) (k - p)
          (c.cap (g ≫ f) k (chowGroupCongr C (Category.assoc g f sY).symm k α))) :=
    rfl
  rw [hcap, chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply]
  exact chowPushforwardOfIso_congr_apply C (pullback.fst (𝟙 Y) (g ≫ f) ≫ sY) (g ≫ (f ≫ sY)) _
    (identityBaseChangeIso (g ≫ f)).hom (by simp [transportPullbackIso]) _ _ (k - p) _

/-- **Stacks 0B7F.** The restriction map `res : A^*(Y) ⟶ A^*(Y')` of the graded Chow cohomology
groups along `f : Y' ⟶ Y`, a homomorphism of graded groups: the degreewise restriction map.

The tag asserts that this is a map of `ℤ`-algebras. The multiplication on `A^*` is composition of
bivariant classes and the graded ring it produces is `Stacks.Chow.chowCohomologyGRing` of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyCompositionRing`. Only additivity is
proved here; that this map respects that multiplication is
`Stacks.Chow.chowCohomologyTotalRestriction_mul` of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyMultiplicative`, and the `ℤ`-algebra
map of the tag is `Stacks.Chow.chowCohomologyTotalRestrictionAlgHomOfInvertible` there. -/
@[stacks 0B7F "the canonical map of graded groups"]
def chowCohomologyTotalRestriction (hgys : G.IsNaturalUnderBaseChangeIso) :
    chowCohomology C G sY →+ chowCohomology C G (f ≫ sY) :=
  DirectSum.map fun p ↦ chowCohomologyRestriction C G sY f p hgys

end Restriction

end Stacks.Chow

end
