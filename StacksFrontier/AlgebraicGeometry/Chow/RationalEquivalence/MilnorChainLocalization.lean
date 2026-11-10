module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksFrontier.AlgebraicGeometry.Chow.Cycles.LocalizationSplitting
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKTransport
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.PointwiseCycles
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.PointwiseMilnorBoundary
public import StacksCore.Tactic.StacksAttribute

/-!
# The degreewise split localization sequence of Milnor K-chains

Let `(S, δ)` be the base situation of chapter 42 and let `p : X ⟶ S` be locally of finite type.
Let `U ⊆ X` be open and let `Y ⊆ X` be a closed subscheme whose underlying set is the
complement. Stacks 0GUA asserts, for every Milnor degree `n` and every relative dimension `m`,
a split short exact sequence

`0 → ⨁'_{y ∈ Y, δ(y) = m} K_n^M(κ(y)) → ⨁'_{x ∈ X, δ(x) = m} K_n^M(κ(x)) →`
`⨁'_{u ∈ U, δ(u) = m} K_n^M(κ(u)) → 0`

of the locally finite direct sums of Stacks 0GU2. This file constructs that sequence and its
splitting.

## The construction

Both immersions are treated at once. A morphism `f : Z ⟶ X` whose underlying map is injective
and which induces an isomorphism on every residue field does not change relative dimension
(`Stacks.Chow.relativeDimension_comp_of_bijective_residueFieldMap`), so it identifies the points
of `Z` of relative dimension `m` with a subset of those of `X`; that is
`Stacks.Chow.immersionPoint`. Milnor K-theory is functorial in the field
(`milnorKTransport`), so a chain on `X` restricts to a chain on `Z`
(`Stacks.Chow.milnorChainComap`) and a chain on `Z` extends by zero to a chain on `X`
(`Stacks.Chow.milnorChainExtend`).

Restriction is locally finite because a compact subset of a scheme is contained in a
quasi-compact open (`AlgebraicGeometry.exists_isCompact_opens_superset`), and extension by zero
is locally finite exactly when `f` is quasi-compact. For the closed immersion that is automatic;
for the open immersion it is the local Noetherianness of `X`, which chapter 42 supplies, and it
is the same hypothesis as in `AlgebraicGeometry.mem_locallyFiniteDirectSum_of_subset_isOpen`.

The two extensions are complementary: a point of `X` lies either in `Y` or in `U` and not in
both, so extension from `Y` of the restriction to `Y` plus extension from `U` of the restriction
to `U` is the identity. That identity is the `id` field of the splitting, and the splitting
gives short exactness by `CategoryTheory.ShortComplex.Splitting.shortExact`.

## What is carried

The closed subscheme is not required to carry the reduced induced structure: the only
hypotheses used are that the morphism is a closed immersion and that its image is the
complement of the open. This generalizes the statement of the source, exactly as in
`Stacks.Chow.exists_rationallyEquivalent_properPushforward_of_cycleGroupRestrict`.

**The compatibility of this sequence with the two boundary maps of Stacks 0GU9 is not proved
here**, and neither is the six-term exact sequence the snake lemma produces from it; both are
proved elsewhere, the latter being `Stacks.Chow.milnorChowLocalization_exact` in
`StacksFrontier/AlgebraicGeometry/Chow/RationalEquivalence/MilnorChowLocalizationSequence.lean`. The
clause strings below say exactly what is claimed. All four squares are proved elsewhere: for the
tame-symbol differential, by `Stacks.Chow.milnorChainComap_pointwiseMilnorBoundary` and
`Stacks.Chow.pointwiseMilnorBoundary_milnorChainExtend` in
`StacksFrontier/AlgebraicGeometry/Chow/RationalEquivalence/MilnorChainBoundaryCompatible.lean`;
for the divisor differential of Stacks 0GU3, by
`Stacks.Chow.milnorChainComap_pointwiseDivisorDifferential` and
`Stacks.Chow.pointwiseDivisorDifferential_milnorChainExtend` in
`StacksFrontier/AlgebraicGeometry/Chow/RationalEquivalence/MilnorChainDivisorCompatible.lean`.

## Main definitions

* `Stacks.Chow.MilnorChainGroup` — the locally finite direct sum of the degree-`n` Milnor
  K-groups of the residue fields at the points of relative dimension `m`.
* `Stacks.Chow.milnorChainComap` — restriction of chains along an immersion.
* `Stacks.Chow.milnorChainExtend` — extension by zero of chains along an immersion.
* `Stacks.Chow.milnorChainLocalizationComplex` — the three chain groups and the two maps, as a
  short complex of abelian groups.

## Main results

* `AlgebraicGeometry.exists_isCompact_opens_superset` — a compact subset of a scheme is
  contained in a quasi-compact open.
* `Stacks.Chow.milnorChainComap_milnorChainExtend` — restricting an extension by zero returns
  the original chain.
* `Stacks.Chow.milnorChainLocalizationSplitting` — **Stacks 0GUA**: the splitting of the
  degreewise localization sequence.
* `Stacks.Chow.milnorChainLocalization_shortExact` — **Stacks 0GUA**: the degreewise
  localization sequence is short exact.
* `Stacks.Chow.milnorChainLocalization_shortExact_degrees` — **Stacks 0GUA**: the three split
  short exact sequences of the tag, for `i = 2, 1, 0`.

## References

* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
* [Stacks Project, Tag 0GU2](https://stacks.math.columbia.edu/tag/0GU2)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Compact subsets of a scheme -/

/-- **A compact subset of a scheme is contained in a quasi-compact open.** The affine opens
cover the scheme and are quasi-compact, so finitely many of them already cover the subset and
their union is a quasi-compact open. -/
theorem exists_isCompact_opens_superset {X : Scheme.{u}} {K : Set X} (hK : IsCompact K) :
    ∃ V : X.Opens, IsCompact (V : Set X) ∧ K ⊆ (V : Set X) := by
  have hcover : K ⊆ ⋃ U : X.affineOpens, ((U : X.Opens) : Set X) := by
    intro x _
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun U : X.affineOpens ↦ ((U : X.Opens) : Set X))
    (fun U ↦ (U : X.Opens).2) hcover
  refine ⟨⟨⋃ U ∈ (s : Set X.affineOpens), ((U : X.Opens) : Set X),
    isOpen_biUnion fun U _ ↦ (U : X.Opens).2⟩, ?_, ?_⟩
  · exact s.finite_toSet.isCompact_biUnion fun U _ ↦ U.2.isCompact
  · simpa using hs

/-- **An open immersion into a locally Noetherian scheme is quasi-compact.** The preimage of a
quasi-compact open `V` is homeomorphic to `V` intersected with the image, which is quasi-compact
by `AlgebraicGeometry.isCompact_inter_of_isLocallyNoetherian`. -/
@[sga "3 VIB 1.4.2" "Open immersions"]
theorem quasiCompact_of_isOpenImmersion {X U : Scheme.{u}} [IsLocallyNoetherian X] (j : U ⟶ X)
    [IsOpenImmersion j] : QuasiCompact j := by
  refine ⟨fun V hVopen hV ↦ ?_⟩
  refine j.isOpenEmbedding.isInducing.isCompact_iff.mpr ?_
  rw [Set.image_preimage_eq_inter_range]
  exact isCompact_inter_of_isLocallyNoetherian ⟨V, hVopen⟩ hV (Set.range j.base)

/-- **An open immersion into a scheme locally of finite type over a locally Noetherian base is
quasi-compact**, because such a scheme is itself locally Noetherian. -/
@[sga "3 VIB 1.4.2" "Open immersions"]
theorem quasiCompact_of_isOpenImmersion_of_locallyOfFiniteType {X U S : Scheme.{u}}
    [IsLocallyNoetherian S] (q : X ⟶ S) [LocallyOfFiniteType q] (j : U ⟶ X)
    [IsOpenImmersion j] : QuasiCompact j :=
  let := LocallyOfFiniteType.isLocallyNoetherian q
  quasiCompact_of_isOpenImmersion j

end AlgebraicGeometry

namespace Stacks.Chow

/-! ### The chain groups -/

/-- **Stacks 0GU2.** The group of locally finite families of degree-`n` Milnor K-classes at the
points of relative dimension `m`. For `n = 0` this is the group of `m`-cycles, for `n = 1` the
source of the divisor differential of Stacks 0GU3, and for `n = 2` the source of the tame-symbol
differential of Stacks 0GU9. -/
abbrev MilnorChainGroup (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) (m : ℤ)
    (n : ℕ) : Type u :=
  ↥(locallyFiniteDirectSum X (pointsOfDimension C p m)
    fun x ↦ MilnorKTheory (X.residueField x.1) n)

/-! ### The two transports of degree-one Milnor K-theory agree -/

/-- **The general functorial transport of degree-one Milnor K-theory agrees with the
Units-based transport.** `milnorKTransport` is the functoriality of Milnor K-theory in the
field, defined for every ring homomorphism and used by `Stacks.Chow.milnorChainComap` and
`Stacks.Chow.milnorChainExtend`; `Stacks.Chow.milnorKOneTransport` is the identification of
degree-one Milnor K-theory with the unit group of the field, read additively, used by
`Stacks.Chow.pointClosureMilnorBoundary`. For a ring *equivalence* the two agree, which is what
lets the degreewise localization sequence at `n = 1` be compared with the tame-symbol
differential. -/
theorem milnorKTransport_eq_milnorKOneTransport {k₁ k₂ : Type u} [Field k₁] [Field k₂]
    (φ : k₁ ≃+* k₂) (y : MilnorKTheory k₁ 1) :
    milnorKTransport (φ : k₁ →+* k₂) 1 y = milnorKOneTransport φ y := by
  apply (milnorKTheoryOneAddEquiv k₂).injective
  rw [milnorKTheoryOneAddEquiv_milnorKTransport]
  show milnorKUnitsMap (φ : k₁ →+* k₂) (milnorKTheoryOneAddEquiv k₁ y) =
    milnorKTheoryOneAddEquiv k₂ (milnorKOneTransport φ y)
  rw [milnorKOneTransport]
  change milnorKUnitsMap (φ : k₁ →+* k₂) (milnorKTheoryOneAddEquiv k₁ y) =
    milnorKTheoryOneAddEquiv k₂
      ((milnorKTheoryOneAddEquiv k₂).symm
        ((MonoidHom.toAdditive (Units.map (φ : k₁ →+* k₂).toMonoidHom))
          (milnorKTheoryOneAddEquiv k₁ y)))
  rw [AddEquiv.apply_symm_apply]
  rfl

section Immersion

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (p : X ⟶ C.S) (f : Z ⟶ X)
  (hinj : Function.Injective f.base)
  (hbij : ∀ z : Z, Function.Bijective (f.residueFieldMap z).hom)

/-! ### Points and residue fields along an immersion -/

include hbij in
/-- The relative dimension of a point of `Z` is the relative dimension of its image: a morphism
inducing an isomorphism on residue fields does not change relative dimension. -/
theorem base_mem_pointsOfDimension {m : ℤ} (z : pointsOfDimension C (f ≫ p) m) :
    f.base z.1 ∈ pointsOfDimension C p m := by
  rw [mem_pointsOfDimension,
    ← relativeDimension_comp_of_bijective_residueFieldMap C.dimensionFunction f p z.1 (hbij z.1)]
  exact z.2

/-- The point of `X` underlying a point of `Z` of relative dimension `m`. -/
abbrev immersionPoint (m : ℤ) (z : pointsOfDimension C (f ≫ p) m) : pointsOfDimension C p m :=
  ⟨f.base z.1, base_mem_pointsOfDimension C p f hbij z⟩

include hinj in
/-- Distinct points of `Z` have distinct images. -/
theorem immersionPoint_injective (m : ℤ) :
    Function.Injective (immersionPoint C p f hbij m) :=
  fun _ _ h ↦ Subtype.ext (hinj (congrArg Subtype.val h))

include hbij in
/-- A point of `X` of relative dimension `m` lying in the image comes from a point of `Z` of
relative dimension `m`. -/
theorem exists_immersionPoint_eq {m : ℤ} (x : pointsOfDimension C p m)
    (hx : (x : X) ∈ Set.range f.base) :
    ∃ z : pointsOfDimension C (f ≫ p) m, immersionPoint C p f hbij m z = x := by
  obtain ⟨z, hz⟩ := hx
  have hdim : z ∈ pointsOfDimension C (f ≫ p) m := by
    rw [mem_pointsOfDimension,
      relativeDimension_comp_of_bijective_residueFieldMap C.dimensionFunction f p z (hbij z), hz]
    exact x.2
  exact ⟨⟨z, hdim⟩, Subtype.ext hz⟩

/-- The isomorphism of residue fields induced at a point of `Z` by a morphism that is bijective
on residue fields. -/
def immersionResidueFieldEquiv (z : Z) :
    ↥(X.residueField (f.base z)) ≃+* ↥(Z.residueField z) :=
  RingEquiv.ofBijective (f.residueFieldMap z).hom (hbij z)

/-- Transport along a ring endomorphism acting as the identity is the identity. -/
theorem milnorKTransport_eq_self {k : Type u} [Field k] (φ : k →+* k) (hφ : ∀ a, φ a = a)
    (n : ℕ) (y : MilnorKTheory k n) : milnorKTransport φ n y = y := by
  rw [show φ = RingHom.id k from RingHom.ext hφ, milnorKTransport_id_apply]

/-! ### Restriction of chains along an immersion -/

/-- Restriction of a pointwise family of Milnor K-classes along an immersion, before the
local-finiteness condition: the coordinate at a point of `Z` is the coordinate at its image,
transported along the isomorphism of residue fields. -/
def milnorChainComapPi (m : ℤ) (n : ℕ) :
    (∀ x : pointsOfDimension C p m, MilnorKTheory (X.residueField x.1) n) →+
      ∀ z : pointsOfDimension C (f ≫ p) m, MilnorKTheory (Z.residueField z.1) n :=
  AddMonoidHom.pi fun z ↦
    (milnorKTransport ((immersionResidueFieldEquiv f hbij z.1 : _ →+* _)) n).comp
      (Pi.evalAddMonoidHom _ (immersionPoint C p f hbij m z))

/-- The coordinate of the restriction at a point of `Z` is the coordinate at its image,
transported along the isomorphism of residue fields. -/
@[simp]
theorem milnorChainComapPi_apply (m : ℤ) (n : ℕ)
    (a : ∀ x : pointsOfDimension C p m, MilnorKTheory (X.residueField x.1) n)
    (z : pointsOfDimension C (f ≫ p) m) :
    milnorChainComapPi C p f hbij m n a z =
      milnorKTransport ((immersionResidueFieldEquiv f hbij z.1 : _ →+* _)) n
        (a (immersionPoint C p f hbij m z)) :=
  rfl

include hinj in
/-- Restriction preserves local finiteness: the support only shrinks, the image of a
quasi-compact open of `Z` lies in a quasi-compact open of `X`, and distinct points of `Z` have
distinct images. -/
theorem milnorChainComapPi_mem (m : ℤ) (n : ℕ) (a : MilnorChainGroup C p m n) :
    milnorChainComapPi C p f hbij m n a.1 ∈
      locallyFiniteDirectSum Z (pointsOfDimension C (f ≫ p) m)
        fun z ↦ MilnorKTheory (Z.residueField z.1) n := by
  intro W hW
  obtain ⟨V, hV, hKV⟩ := exists_isCompact_opens_superset (hW.image f.continuous)
  refine Set.Finite.of_finite_image (f := immersionPoint C p f hbij m)
    ((a.2 V hV).subset ?_)
    (Set.injOn_of_injective (immersionPoint_injective C p f hinj hbij m))
  rintro x ⟨z, ⟨hzW, hzne⟩, rfl⟩
  refine ⟨hKV ⟨z.1, hzW, rfl⟩, fun h ↦ hzne ?_⟩
  rw [milnorChainComapPi_apply, h, map_zero]

include hinj in
/-- **Restriction of locally finite Milnor K-chains along an immersion.** -/
def milnorChainComap (m : ℤ) (n : ℕ) :
    MilnorChainGroup C p m n →+ MilnorChainGroup C (f ≫ p) m n :=
  AddMonoidHom.codRestrict
    ((milnorChainComapPi C p f hbij m n).comp
      (locallyFiniteDirectSum X (pointsOfDimension C p m)
        fun x ↦ MilnorKTheory (X.residueField x.1) n).subtype) _
    (milnorChainComapPi_mem C p f hinj hbij m n)

include hinj in
/-- The coordinate of the restriction of a chain at a point of `Z` is the coordinate at its image,
transported along the isomorphism of residue fields. -/
@[simp]
theorem milnorChainComap_apply (m : ℤ) (n : ℕ) (a : MilnorChainGroup C p m n)
    (z : pointsOfDimension C (f ≫ p) m) :
    (milnorChainComap C p f hinj hbij m n a).1 z =
      milnorKTransport ((immersionResidueFieldEquiv f hbij z.1 : _ →+* _)) n
        (a.1 (immersionPoint C p f hbij m z)) :=
  rfl

/-! ### Extension by zero of chains along an immersion -/

/-- The coordinate of the extension by zero at the image of a prescribed point of `Z`: the
coordinate there, transported backwards along the isomorphism of residue fields. -/
def milnorChainExtendHomOf {m : ℤ} {n : ℕ} (x : pointsOfDimension C p m)
    (z : pointsOfDimension C (f ≫ p) m) (hz : immersionPoint C p f hbij m z = x) :
    (∀ w : pointsOfDimension C (f ≫ p) m, MilnorKTheory (Z.residueField w.1) n) →+
      MilnorKTheory (X.residueField x.1) n :=
  (milnorKTransport
      ((X.residueFieldCongr (congrArg Subtype.val hz)).commRingCatIsoToRingEquiv.toRingHom) n).comp
    ((milnorKTransport ((immersionResidueFieldEquiv f hbij z.1).symm : _ →+* _) n).comp
      (Pi.evalAddMonoidHom _ z))

/-- The value of `milnorChainExtendHomOf` is the coordinate at `z`, transported backwards along
the isomorphism of residue fields and then along the identification of residue fields given by
`hz`. -/
@[simp]
theorem milnorChainExtendHomOf_apply {m : ℤ} {n : ℕ} (x : pointsOfDimension C p m)
    (z : pointsOfDimension C (f ≫ p) m) (hz : immersionPoint C p f hbij m z = x)
    (a : ∀ w : pointsOfDimension C (f ≫ p) m, MilnorKTheory (Z.residueField w.1) n) :
    milnorChainExtendHomOf C p f hbij x z hz a =
      milnorKTransport
          ((X.residueFieldCongr
            (congrArg Subtype.val hz)).commRingCatIsoToRingEquiv.toRingHom) n
        (milnorKTransport ((immersionResidueFieldEquiv f hbij z.1).symm : _ →+* _) n (a z)) :=
  rfl

/-- At the image of `z` itself the outer transport is the identity. -/
theorem milnorChainExtendHomOf_apply_rfl {m : ℤ} {n : ℕ}
    (z : pointsOfDimension C (f ≫ p) m)
    (a : ∀ w : pointsOfDimension C (f ≫ p) m, MilnorKTheory (Z.residueField w.1) n) :
    milnorChainExtendHomOf C p f hbij (immersionPoint C p f hbij m z) z rfl a =
      milnorKTransport ((immersionResidueFieldEquiv f hbij z.1).symm : _ →+* _) n (a z) := by
  rw [milnorChainExtendHomOf_apply]
  exact milnorKTransport_eq_self _ (fun _ ↦ rfl) _ _

include hinj in
/-- The point of `Z` producing a given point of `X` is unique, so the extension by zero does not
depend on which one is used. -/
theorem milnorChainExtendHomOf_congr {m : ℤ} {n : ℕ} (x : pointsOfDimension C p m)
    (z z' : pointsOfDimension C (f ≫ p) m) (hz : immersionPoint C p f hbij m z = x)
    (hz' : immersionPoint C p f hbij m z' = x) :
    milnorChainExtendHomOf C p f hbij x z hz (n := n) =
      milnorChainExtendHomOf C p f hbij x z' hz' := by
  obtain rfl : z = z' := immersionPoint_injective C p f hinj hbij m (hz.trans hz'.symm)
  rfl

open Classical in
/-- The coordinate at a point of `X` of the extension by zero of a chain on `Z`: the transported
coordinate at the unique preimage if there is one, and zero otherwise. -/
def milnorChainExtendAtHom {m : ℤ} {n : ℕ} (x : pointsOfDimension C p m) :
    (∀ w : pointsOfDimension C (f ≫ p) m, MilnorKTheory (Z.residueField w.1) n) →+
      MilnorKTheory (X.residueField x.1) n :=
  if h : ∃ z, immersionPoint C p f hbij m z = x then
    milnorChainExtendHomOf C p f hbij x h.choose h.choose_spec
  else 0

include hinj in
/-- At the image of a point `z` of `Z`, the extension by zero is the coordinate at `z`,
transported along the isomorphism of residue fields. -/
theorem milnorChainExtendAtHom_of_eq {m : ℤ} {n : ℕ} (x : pointsOfDimension C p m)
    (z : pointsOfDimension C (f ≫ p) m) (hz : immersionPoint C p f hbij m z = x) :
    milnorChainExtendAtHom C p f hbij x (n := n) =
      milnorChainExtendHomOf C p f hbij x z hz := by
  classical
  rw [milnorChainExtendAtHom, dite_eq_left ⟨z, hz⟩]
  exact milnorChainExtendHomOf_congr C p f hinj hbij x _ z _ hz

/-- At a point of `X` that is not the image of any point of `Z`, the extension by zero vanishes. -/
theorem milnorChainExtendAtHom_of_notMem {m : ℤ} {n : ℕ} (x : pointsOfDimension C p m)
    (hx : ∀ z, immersionPoint C p f hbij m z ≠ x) :
    milnorChainExtendAtHom C p f hbij x (n := n) = 0 := by
  classical
  rw [milnorChainExtendAtHom, dite_eq_right]
  rintro ⟨z, hz⟩
  exact hx z hz

/-- Off the image of `f` the extension by zero vanishes. -/
theorem milnorChainExtendAtHom_of_notMem_range {m : ℤ} {n : ℕ} (x : pointsOfDimension C p m)
    (hx : (x : X) ∉ Set.range f.base) :
    milnorChainExtendAtHom C p f hbij x (n := n) = 0 :=
  milnorChainExtendAtHom_of_notMem C p f hbij x
    fun z hz ↦ hx ⟨z.1, congrArg Subtype.val hz⟩

/-- Extension by zero of a pointwise family of Milnor K-classes along an immersion, before the
local-finiteness condition. -/
def milnorChainExtendPi (m : ℤ) (n : ℕ) :
    (∀ z : pointsOfDimension C (f ≫ p) m, MilnorKTheory (Z.residueField z.1) n) →+
      ∀ x : pointsOfDimension C p m, MilnorKTheory (X.residueField x.1) n :=
  AddMonoidHom.pi fun x ↦ milnorChainExtendAtHom C p f hbij x

/-- The coordinate of `milnorChainExtendPi` at a point `x` of `X` is `milnorChainExtendAtHom` at
`x`. -/
@[simp]
theorem milnorChainExtendPi_apply (m : ℤ) (n : ℕ)
    (a : ∀ z : pointsOfDimension C (f ≫ p) m, MilnorKTheory (Z.residueField z.1) n)
    (x : pointsOfDimension C p m) :
    milnorChainExtendPi C p f hbij m n a x = milnorChainExtendAtHom C p f hbij x a :=
  rfl

/-- At the image of a point `z` of `Z`, the extension by zero is the coordinate at `z`,
transported backwards along the isomorphism of residue fields. -/
private theorem milnorChainExtendAtHom_immersionPoint (hinj : Function.Injective f.base)
    {m : ℤ} {n : ℕ} (z : pointsOfDimension C (f ≫ p) m)
    (a : ∀ w : pointsOfDimension C (f ≫ p) m, MilnorKTheory (Z.residueField w.1) n) :
    milnorChainExtendAtHom C p f hbij (immersionPoint C p f hbij m z) a =
      milnorKTransport ((immersionResidueFieldEquiv f hbij z.1).symm : _ →+* _) n (a z) := by
  rw [milnorChainExtendAtHom_of_eq C p f hinj hbij _ z rfl,
    milnorChainExtendHomOf_apply_rfl C p f hbij z]

include hinj in
/-- Extension by zero preserves local finiteness exactly when `f` is quasi-compact: the support
of the extension is the image of the support, and the preimage of a quasi-compact open of `X` is
a quasi-compact open of `Z`. -/
theorem milnorChainExtendPi_mem (hqc : QuasiCompact f) (m : ℤ) (n : ℕ)
    (a : MilnorChainGroup C (f ≫ p) m n) :
    milnorChainExtendPi C p f hbij m n a.1 ∈
      locallyFiniteDirectSum X (pointsOfDimension C p m)
        fun x ↦ MilnorKTheory (X.residueField x.1) n := by
  intro V hV
  have hVc : IsCompact ((f ⁻¹ᵁ V : Z.Opens) : Set Z) :=
    hqc.isCompact_preimage (V : Set X) V.2 hV
  refine Set.Finite.subset
    ((a.2 (f ⁻¹ᵁ V) hVc).image (immersionPoint C p f hbij m)) ?_
  rintro x ⟨hxV, hxne⟩
  have hex : ∃ z, immersionPoint C p f hbij m z = x := by
    by_contra hcon
    push Not at hcon
    rw [milnorChainExtendPi_apply, milnorChainExtendAtHom_of_notMem C p f hbij x hcon] at hxne
    exact hxne rfl
  obtain ⟨z, rfl⟩ := hex
  refine ⟨z, ⟨hxV, fun h0 ↦ hxne ?_⟩, rfl⟩
  rw [milnorChainExtendPi_apply, milnorChainExtendAtHom_immersionPoint C p f hbij hinj z, h0,
    map_zero]

include hinj in
/-- **Extension by zero of locally finite Milnor K-chains along an immersion.** The coordinate
at a point in the image is the coordinate at the unique preimage, transported along the
isomorphism of residue fields; elsewhere it is zero. -/
def milnorChainExtend (hqc : QuasiCompact f) (m : ℤ) (n : ℕ) :
    MilnorChainGroup C (f ≫ p) m n →+ MilnorChainGroup C p m n :=
  AddMonoidHom.codRestrict
    ((milnorChainExtendPi C p f hbij m n).comp
      (locallyFiniteDirectSum Z (pointsOfDimension C (f ≫ p) m)
        fun z ↦ MilnorKTheory (Z.residueField z.1) n).subtype) _
    (milnorChainExtendPi_mem C p f hinj hbij hqc m n)

include hinj in
/-- The coordinate of the extension by zero of a chain at a point of `X` is given by
`milnorChainExtendAtHom`. -/
@[simp]
theorem milnorChainExtend_apply (hqc : QuasiCompact f) (m : ℤ) (n : ℕ)
    (a : MilnorChainGroup C (f ≫ p) m n) (x : pointsOfDimension C p m) :
    (milnorChainExtend C p f hinj hbij hqc m n a).1 x =
      milnorChainExtendAtHom C p f hbij x a.1 :=
  rfl

include hinj in
/-- **Restricting an extension by zero returns the original chain.** -/
theorem milnorChainComap_milnorChainExtend (hqc : QuasiCompact f) (m : ℤ) (n : ℕ) :
    (milnorChainComap C p f hinj hbij m n).comp
        (milnorChainExtend C p f hinj hbij hqc m n) =
      AddMonoidHom.id (MilnorChainGroup C (f ≫ p) m n) := by
  refine AddMonoidHom.ext fun a ↦ Subtype.ext (funext fun z ↦ ?_)
  rw [AddMonoidHom.comp_apply, milnorChainComap_apply, milnorChainExtend_apply,
    milnorChainExtendAtHom_immersionPoint C p f hbij hinj z]
  exact milnorKTransport_milnorKTransport_symm (immersionResidueFieldEquiv f hbij z.1) n (a.1 z)

/-- Extending the restriction of a chain recovers the chain at the image of a point of `Z`. -/
private theorem milnorChainExtendAtHom_milnorChainComap (hinj : Function.Injective f.base)
    {m : ℤ} {n : ℕ} (a : MilnorChainGroup C p m n) (z : pointsOfDimension C (f ≫ p) m) :
    milnorChainExtendAtHom C p f hbij (immersionPoint C p f hbij m z)
        (milnorChainComap C p f hinj hbij m n a).1 =
      a.1 (immersionPoint C p f hbij m z) := by
  rw [milnorChainExtendAtHom_immersionPoint C p f hbij hinj z, milnorChainComap_apply]
  exact milnorKTransport_symm_milnorKTransport (immersionResidueFieldEquiv f hbij z.1) n _

end Immersion

/-! ### The degreewise localization sequence -/

section Localization

variable (C : ChowSituation.{u}) {X Y U : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (i : Y ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]

/-- A closed immersion is injective on points. -/
theorem injective_base_of_isClosedImmersion : Function.Injective i.base :=
  i.isClosedEmbedding.injective

/-- A closed immersion induces an isomorphism on residue fields. -/
theorem bijective_residueFieldMap_closedImmersion :
    ∀ y : Y, Function.Bijective (i.residueFieldMap y).hom :=
  fun y ↦ bijective_residueFieldMap_of_isClosedImmersion i y

/-- An open immersion is injective on points. -/
theorem injective_base_of_isOpenImmersion : Function.Injective j.base :=
  j.isOpenEmbedding.injective

/-- An open immersion induces an isomorphism on residue fields. -/
theorem bijective_residueFieldMap_openImmersion :
    ∀ u : U, Function.Bijective (j.residueFieldMap u).hom :=
  fun _ ↦ ConcreteCategory.bijective_of_isIso _

omit [LocallyOfFiniteType p] in
/-- The composite of extension by zero from the closed subscheme with restriction to the
complementary open subscheme vanishes: a point of the open subscheme is not a point of the
closed one. -/
theorem milnorChainComap_milnorChainExtend_eq_zero
    (hcomp : Set.range i.base = (Set.range j.base)ᶜ) (m : ℤ) (n : ℕ)
    (b : MilnorChainGroup C (i ≫ p) m n) :
    milnorChainComap C p j (injective_base_of_isOpenImmersion j)
        (bijective_residueFieldMap_openImmersion j) m n
      (milnorChainExtend C p i (injective_base_of_isClosedImmersion i)
        (bijective_residueFieldMap_closedImmersion i) inferInstance m n b) = 0 := by
  refine Subtype.ext (funext fun u ↦ ?_)
  have hmem : (immersionPoint C p j (bijective_residueFieldMap_openImmersion j) m u : X) ∉
      Set.range i.base := by
    rw [hcomp]
    exact fun hcon ↦ hcon ⟨u.1, rfl⟩
  rw [milnorChainComap_apply, milnorChainExtend_apply,
    milnorChainExtendAtHom_of_notMem_range C p i
      (bijective_residueFieldMap_closedImmersion i) _ hmem, AddMonoidHom.zero_apply, map_zero]
  rfl

/-- **The two extensions are complementary.** A point of `X` lies in exactly one of the closed
subscheme and the open subscheme, and at a point of either the corresponding composite returns
the original coordinate while the other vanishes. -/
theorem milnorChainExtend_milnorChainComap_add
    (hcomp : Set.range i.base = (Set.range j.base)ᶜ) (m : ℤ) (n : ℕ)
    (a : MilnorChainGroup C p m n) :
    milnorChainExtend C p i (injective_base_of_isClosedImmersion i)
        (bijective_residueFieldMap_closedImmersion i) inferInstance m n
        (milnorChainComap C p i (injective_base_of_isClosedImmersion i)
          (bijective_residueFieldMap_closedImmersion i) m n a) +
      milnorChainExtend C p j (injective_base_of_isOpenImmersion j)
        (bijective_residueFieldMap_openImmersion j)
        (quasiCompact_of_isOpenImmersion_of_locallyOfFiniteType p j) m n
        (milnorChainComap C p j (injective_base_of_isOpenImmersion j)
          (bijective_residueFieldMap_openImmersion j) m n a) = a := by
  refine Subtype.ext (funext fun x ↦ ?_)
  change milnorChainExtendAtHom C p i (bijective_residueFieldMap_closedImmersion i) x
        (milnorChainComap C p i (injective_base_of_isClosedImmersion i)
          (bijective_residueFieldMap_closedImmersion i) m n a).1 +
      milnorChainExtendAtHom C p j (bijective_residueFieldMap_openImmersion j) x
        (milnorChainComap C p j (injective_base_of_isOpenImmersion j)
          (bijective_residueFieldMap_openImmersion j) m n a).1 = a.1 x
  by_cases hx : (x : X) ∈ Set.range j.base
  · have hxi : (x : X) ∉ Set.range i.base := by rw [hcomp]; exact fun hcon ↦ hcon hx
    obtain ⟨w, rfl⟩ :=
      exists_immersionPoint_eq C p j (bijective_residueFieldMap_openImmersion j) x hx
    rw [milnorChainExtendAtHom_of_notMem_range C p i
        (bijective_residueFieldMap_closedImmersion i) _ hxi,
      milnorChainExtendAtHom_milnorChainComap C p j (bijective_residueFieldMap_openImmersion j)
        (injective_base_of_isOpenImmersion j) a w, AddMonoidHom.zero_apply, zero_add]
  · have hxi : (x : X) ∈ Set.range i.base := by rw [hcomp]; exact hx
    obtain ⟨w, rfl⟩ :=
      exists_immersionPoint_eq C p i (bijective_residueFieldMap_closedImmersion i) x hxi
    rw [milnorChainExtendAtHom_of_notMem_range C p j
        (bijective_residueFieldMap_openImmersion j) _ hx,
      milnorChainExtendAtHom_milnorChainComap C p i
        (bijective_residueFieldMap_closedImmersion i) (injective_base_of_isClosedImmersion i) a w,
      AddMonoidHom.zero_apply, add_zero]

/-- **Stacks 0GUA.** The degreewise localization sequence of locally finite Milnor K-chains: the
chains on the closed subscheme `Y`, on `X` and on the open subscheme `U`, with extension by zero
from `Y` and restriction to `U`. -/
@[stacks 0GUA "the degreewise localization sequence of the tag, for one relative dimension m and \
one Milnor degree n: the locally finite direct sums of Stacks 0GU2 for the closed subscheme, the \
ambient scheme and the complementary open subscheme, together with the extension-by-zero map \
from the closed subscheme and the restriction map to the open subscheme, as a short complex of \
abelian groups; its compatibility with the two boundary maps of Stacks 0GU9, and the six-term \
exact sequence \
the snake lemma yields from it, are proved not here but in \
Stacks.Chow.milnorChowLocalization_exact, \
Stacks.Chow.milnorChainComap_pointwiseMilnorBoundary, \
Stacks.Chow.pointwiseMilnorBoundary_milnorChainExtend, \
Stacks.Chow.milnorChainComap_pointwiseDivisorDifferential and \
Stacks.Chow.pointwiseDivisorDifferential_milnorChainExtend"]
def milnorChainLocalizationComplex (hcomp : Set.range i.base = (Set.range j.base)ᶜ)
    (m : ℤ) (n : ℕ) : ShortComplex AddCommGrpCat.{u} where
  X₁ := AddCommGrpCat.of (MilnorChainGroup C (i ≫ p) m n)
  X₂ := AddCommGrpCat.of (MilnorChainGroup C p m n)
  X₃ := AddCommGrpCat.of (MilnorChainGroup C (j ≫ p) m n)
  f := AddCommGrpCat.ofHom
    (milnorChainExtend C p i (injective_base_of_isClosedImmersion i)
      (bijective_residueFieldMap_closedImmersion i) inferInstance m n)
  g := AddCommGrpCat.ofHom
    (milnorChainComap C p j (injective_base_of_isOpenImmersion j)
      (bijective_residueFieldMap_openImmersion j) m n)
  zero := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun b ↦
    milnorChainComap_milnorChainExtend_eq_zero C p i j hcomp m n b)

/-- **Stacks 0GUA.** The degreewise localization sequence is split: restriction to `Y` is a
retraction of the extension by zero from `Y`, extension by zero from `U` is a section of the
restriction to `U`, and the two composites add up to the identity. -/
@[stacks 0GUA "the splitting of the degreewise localization sequence of the tag: restriction to \
the closed subscheme retracts the extension by zero from it, extension by zero from the open \
subscheme sections the restriction to it, and the two resulting idempotents of the chains on \
the ambient scheme add up to the identity"]
def milnorChainLocalizationSplitting (hcomp : Set.range i.base = (Set.range j.base)ᶜ)
    (m : ℤ) (n : ℕ) :
    (milnorChainLocalizationComplex C p i j hcomp m n).Splitting where
  r := AddCommGrpCat.ofHom
    (milnorChainComap C p i (injective_base_of_isClosedImmersion i)
      (bijective_residueFieldMap_closedImmersion i) m n)
  s := AddCommGrpCat.ofHom
    (milnorChainExtend C p j (injective_base_of_isOpenImmersion j)
      (bijective_residueFieldMap_openImmersion j)
      (quasiCompact_of_isOpenImmersion_of_locallyOfFiniteType p j) m n)
  f_r := AddCommGrpCat.hom_ext
    (milnorChainComap_milnorChainExtend C p i (injective_base_of_isClosedImmersion i)
      (bijective_residueFieldMap_closedImmersion i) inferInstance m n)
  s_g := AddCommGrpCat.hom_ext
    (milnorChainComap_milnorChainExtend C p j (injective_base_of_isOpenImmersion j)
      (bijective_residueFieldMap_openImmersion j)
      (quasiCompact_of_isOpenImmersion_of_locallyOfFiniteType p j) m n)
  id := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun a ↦
    milnorChainExtend_milnorChainComap_add C p i j hcomp m n a)

/-- **Stacks 0GUA.** The degreewise localization sequence is short exact: it is split, and a
split short complex is short exact. -/
@[stacks 0GUA "the short exactness of the degreewise localization sequence of the tag, in one \
relative dimension and one Milnor degree: extension by zero from the closed subscheme is \
injective, restriction to the open subscheme is surjective, and the image of the first is the \
kernel of the second"]
theorem milnorChainLocalization_shortExact
    (hcomp : Set.range i.base = (Set.range j.base)ᶜ) (m : ℤ) (n : ℕ) :
    (milnorChainLocalizationComplex C p i j hcomp m n).ShortExact :=
  (milnorChainLocalizationSplitting C p i j hcomp m n).shortExact

/-! ### The three degrees of Stacks 0GU9 -/

omit [LocallyOfFiniteType p] in
/-- In Milnor degree two and relative dimension `k + 2` the middle term of the degreewise
localization sequence is the degree-two Milnor K-chain group of Stacks 0GU9. -/
theorem milnorChainLocalizationComplex_X₂_two
    (hcomp : Set.range i.base = (Set.range j.base)ᶜ) (k : ℤ) :
    (milnorChainLocalizationComplex C p i j hcomp (k + 2) 2).X₂ =
      AddCommGrpCat.of (PointwiseKTwoGroup C p k) :=
  rfl

omit [LocallyOfFiniteType p] in
/-- In Milnor degree one and relative dimension `k + 1` the middle term of the degreewise
localization sequence is the degree-one Milnor K-chain group of Stacks 0GU3. -/
theorem milnorChainLocalizationComplex_X₂_one
    (hcomp : Set.range i.base = (Set.range j.base)ᶜ) (k : ℤ) :
    (milnorChainLocalizationComplex C p i j hcomp (k + 1) 1).X₂ =
      AddCommGrpCat.of (PointwiseKOneGroup C p k) :=
  rfl

omit [LocallyOfFiniteType p] in
/-- In Milnor degree zero and relative dimension `k` the middle term of the degreewise
localization sequence is the group of `k`-cycles in its pointwise form, Stacks 0GU2. -/
theorem milnorChainLocalizationComplex_X₂_zero
    (hcomp : Set.range i.base = (Set.range j.base)ᶜ) (k : ℤ) :
    (milnorChainLocalizationComplex C p i j hcomp k 0).X₂ =
      AddCommGrpCat.of (PointwiseCycleGroup C p k) :=
  rfl

/-- **Stacks 0GUA.** The three split short exact sequences of the tag, for `i = 2, 1, 0`: the
locally finite direct sums of degree-`i` Milnor K-groups at the points of relative dimension
`k + i`, for the closed subscheme, the ambient scheme and the complementary open subscheme. By
`Stacks.Chow.milnorChainLocalizationComplex_X₂_two`,
`Stacks.Chow.milnorChainLocalizationComplex_X₂_one` and
`Stacks.Chow.milnorChainLocalizationComplex_X₂_zero` the middle terms are the three groups that
carry the complex of Stacks 0GU9. -/
@[stacks 0GUA "the three split short exact sequences of the tag, for i = 2, 1 and 0: for an open \
subscheme and a closed subscheme with complementary underlying set, the sequence of locally \
finite direct sums of the degree-i Milnor K-groups of the residue fields at the points of \
relative dimension k + i is short exact and split; the middle terms are exactly the three groups \
carrying the complex of Stacks 0GU9. Only the sequences themselves are proved here; their \
compatibility with the two boundary maps of that complex is proved in \
Stacks.Chow.milnorChainComap_pointwiseMilnorBoundary, \
Stacks.Chow.pointwiseMilnorBoundary_milnorChainExtend, \
Stacks.Chow.milnorChainComap_pointwiseDivisorDifferential and \
Stacks.Chow.pointwiseDivisorDifferential_milnorChainExtend, and the six-term exact sequence the \
snake lemma yields from them is Stacks.Chow.milnorChowLocalization_exact"]
theorem milnorChainLocalization_shortExact_degrees
    (hcomp : Set.range i.base = (Set.range j.base)ᶜ) (k : ℤ) :
    (milnorChainLocalizationComplex C p i j hcomp (k + 2) 2).ShortExact ∧
      (milnorChainLocalizationComplex C p i j hcomp (k + 1) 1).ShortExact ∧
      (milnorChainLocalizationComplex C p i j hcomp k 0).ShortExact :=
  ⟨milnorChainLocalization_shortExact C p i j hcomp (k + 2) 2,
    milnorChainLocalization_shortExact C p i j hcomp (k + 1) 1,
    milnorChainLocalization_shortExact C p i j hcomp k 0⟩

end Localization

end Stacks.Chow

end
