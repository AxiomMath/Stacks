module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.UnibranchEtaleCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.BranchCount
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.AffineElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PresheafPointTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.BoundedElementaryEtaleNeighborhoodModel

/-!
# Local irreducibility at a point of an algebraic space

Let `x` be a point of an algebraic space `F` over `S`. Three conditions on the elementary étale
neighbourhoods of `x` agree: the local ring of every such neighbourhood at its distinguished
point has a unique minimal prime; exactly one irreducible component of every such neighbourhood
passes through its distinguished point; and every such local ring is unibranch. The counted
forms also agree: the three numbers are simultaneously bounded by `n` and attained.

A decent algebraic space is *unibranch at `x`* when those conditions hold, and *unibranch*
when it is unibranch at every one of its points. The *number of branches at `x`* is the natural
number appearing in the counted conditions when one of them does, and `∞` when none does.

## Main definitions

* `AlgebraicGeometry.Space.HasMinimalPrimeCountOnElementaryNeighborhoods`,
  `AlgebraicGeometry.Space.HasComponentCountOnElementaryNeighborhoods` and
  `AlgebraicGeometry.Space.HasBranchCountOnElementaryNeighborhoods`: the three counted
  conditions of Tag 0DQ8.
* `AlgebraicGeometry.Space.IsUnibranchAt` and `AlgebraicGeometry.Space.IsUnibranch`:
  unibranchness of a decent algebraic space at a point and at every point, Tag 0DQ7.
* `AlgebraicGeometry.Space.numberOfBranches`: the number of branches of a decent algebraic
  space at a point, with value in `ℕ∞`, Tag 0DQ9.

## Main results

* `AlgebraicGeometry.Space.forall_existsUnique_minimalPrimes_iff_forall_existsUnique_component`
  and
  `AlgebraicGeometry.Space.forall_existsUnique_component_iff_forall_isUnibranchAt`: the first two
  equivalences of Tag 0DQ6.
* `AlgebraicGeometry.Space.hasMinimalPrimeCount_iff_hasComponentCount` and
  `AlgebraicGeometry.Space.hasComponentCount_iff_hasBranchCount`: the first two equivalences of
  Tag 0DQ8.
* `AlgebraicGeometry.Space.exists_elementaryEtaleNeighborhood_componentsThrough_equiv`: an
  elementary étale neighbourhood of the distinguished point of an elementary étale neighbourhood
  of `x` is matched, on irreducible components through the distinguished point, by an elementary
  étale neighbourhood of `x`.
* `AlgebraicGeometry.Space.numberOfBranches_eq_nat_iff`: a finite value of the number of
  branches at `x` is exactly the value appearing in the counted conditions of Tag 0DQ8.
* `AlgebraicGeometry.Space.numberOfBranches_eq_top_iff`: the number of branches at `x` is
  infinite exactly when no natural number satisfies those conditions.

## Implementation notes

An elementary étale neighbourhood of `x` is `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood`
of Tag 0BGU, whose scheme is an object of the chosen big fppf site; the scheme-level elementary
étale neighbourhoods of its distinguished point are the `AlgebraicGeometry.EtaleNeighborhood` of
Tag 02LE satisfying `AlgebraicGeometry.EtaleNeighborhood.IsElementary`.

The two kinds of neighbourhood are compared by composition. The composite of a scheme-level
neighbourhood with a neighbourhood of `x` is again a neighbourhood of `x` once its scheme is
small enough for the site, which an affine open around the distinguished point is, because an
étale morphism is locally of finite type; the residue-field spectrum is then automatically small
enough, since it maps to the scheme by a quasi-compact monomorphism. Passing to that affine open
does not change the irreducible components through the distinguished point, an open immersion
matching them with those of the ambient scheme.

The counts take values in `ℕ∞`, so a neighbourhood with infinitely many components through its
distinguished point does not accidentally satisfy a bound by a natural number. Conditions (1)
and (2) agree neighbourhood by neighbourhood, by the correspondence of Tag 00ET; conditions (2)
and (3) agree because the number of branches of a scheme at a point is the supremum of the
component counts of its elementary étale neighbourhoods, which is Tag 0CB4.

Although the source states the counted equivalences for a positive `n`, they also hold for
`n = 0`: all three conditions then fail, because the local ring of a scheme at a point always
has a minimal prime.

Unibranchness at `x` is defined by condition (3) of Tag 0DQ6, unibranchness of the local rings
of the elementary étale neighbourhoods. That condition is phrased through the scheme-level
`AlgebraicGeometry.IsUnibranchAt`, so it is visibly the same notion as for a scheme, Tag 0BQ2,
and it inherits the ring-theoretic API of unibranch local rings; conditions (1) and (2) are
reached from it by the equivalences above.

The number of branches at `x` is the infimum in `ℕ∞` of the natural numbers satisfying
condition (3) of Tag 0DQ8, so that the empty infimum records the case of infinitely many
branches. At most one natural number satisfies that condition, since the condition both bounds
the branch counts of the elementary étale neighbourhoods by that number and attains it, and two
such numbers therefore bound each other; so the infimum is the value the source names. The two
characterizations below let clients use the count without unfolding the infimum.

Decency of the space is carried as an explicit hypothesis of both definitions, as in the source
definitions, even though the conditions defining them make sense for any algebraic space:
without decency the category of elementary étale neighbourhoods of `x` can be empty, in which
case the pointwise condition holds vacuously and no natural number satisfies the counted
condition, so that the number of branches is `⊤`.

## References

* [Stacks Project, Tag 0DQ6](https://stacks.math.columbia.edu/tag/0DQ6)
* [Stacks Project, Tag 0DQ7](https://stacks.math.columbia.edu/tag/0DQ7)
* [Stacks Project, Tag 0DQ8](https://stacks.math.columbia.edu/tag/0DQ8)
* [Stacks Project, Tag 0DQ9](https://stacks.math.columbia.edu/tag/0DQ9)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-! ### Irreducible components through a point under an open embedding -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
  (x : points B S hS X)

/-- The residue field map of an elementary étale neighbourhood is an isomorphism at its point. -/
private theorem isIso_residueFieldMap_of_isElementary {X : Scheme.{u}} {x : X}
    (V : _root_.AlgebraicGeometry.EtaleNeighborhood X x) (hV : V.IsElementary) :
    IsIso (V.toBase.residueFieldMap V.point) :=
  (isIso_comp_left_iff (X.residueFieldCongr V.map_point).inv
    (V.toBase.residueFieldMap V.point)).mp hV

/-- The composite of a scheme-level elementary étale neighbourhood of the distinguished point of
an elementary étale neighbourhood of `x` with that neighbourhood, taken over `x` again. -/
private def ElementaryEtaleNeighborhood.compScheme
    (U : ElementaryEtaleNeighborhood B S hS X hX x)
    (V : _root_.AlgebraicGeometry.EtaleNeighborhood U.scheme.left.1 U.point)
    (hV : V.IsElementary) (hsmall : B.Contains V.scheme) :
    ElementaryEtaleNeighborhood B S hS X hX x := by
  let T : BigFppfOver B S hS := Over.mk (⟨V.toBase ≫ U.scheme.hom.1⟩ : B.obj hsmall ⟶ B.obj hS)
  let f : T ⟶ U.scheme := Over.homMk ⟨V.toBase⟩
  have hf : IsIso (f.left.1.residueFieldMap V.point) :=
    isIso_residueFieldMap_of_isElementary V hV
  have hfetale : _root_.AlgebraicGeometry.Etale f.left.1 := V.etale_toBase
  refine
    { scheme := T
      point := V.point
      residueField_contained := B.residueField_spec_contains T.left.property V.point
      toSpace := yoneda.map f ≫ U.toSpace
      etale_toSpace := isEtale_comp B S hS
        ((isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map f)).mpr
          ((presheaf_yoneda_map_etale_iff B S hS f).mpr hfetale)) U.etale_toSpace
      map_point := ?_
      mono_residueField := ?_ }
  · have hc := B.residueField_spec_contains T.left.property V.point
    have hcomp : pointsMap B S hS (yoneda.obj T) (yoneda.map f ≫ U.toSpace)
          (presheafPoint B S hS T V.point hc) =
        pointsMap B S hS (yoneda.obj U.scheme) U.toSpace
          (pointsMap B S hS (yoneda.obj T) (yoneda.map f)
            (presheafPoint B S hS T V.point hc)) :=
      rfl
    rw [hcomp, pointsMap_presheafPoint B S hS T U.scheme f V.point hc
      (B.residueField_spec_contains U.scheme.left.property (f.left.1 V.point))]
    exact (congrArg (fun p ↦ pointsMap B S hS (yoneda.obj U.scheme) U.toSpace
      (presheafPoint B S hS U.scheme p (B.residueField_spec_contains U.scheme.left.property p)))
      V.map_point).trans U.map_point
  · have hd : IsIso (residueFieldObjectMap B S hS T U.scheme f V.point) :=
      isIso_residueFieldObjectMap B S hS T U.scheme f V.point
    have hmono : Mono (yoneda.map (residueFieldMap B S hS U.scheme (f.left.1 V.point)
        (B.residueField_spec_contains U.scheme.left.property (f.left.1 V.point))) ≫ U.toSpace) := by
      have hm : ∀ (p : U.scheme.left.1), p = U.point →
          ∀ (hc : B.Contains (Spec (.of (U.scheme.left.1.residueField p)))),
          Mono (yoneda.map (residueFieldMap B S hS U.scheme p hc) ≫ U.toSpace) := by
        rintro p rfl hc
        exact U.mono_residueField
      exact hm _ V.map_point _
    have heq := congrArg (fun k ↦ yoneda.map k ≫ U.toSpace)
      (residueFieldObjectMap_comp B S hS T U.scheme f V.point)
    simp only [Functor.map_comp, Category.assoc] at heq
    rw [← heq]
    infer_instance

/-- **The comparison of the two kinds of neighbourhood.** An elementary étale neighbourhood of
the distinguished point of an elementary étale neighbourhood of `x` has the same irreducible
components through its distinguished point as some elementary étale neighbourhood of `x`: an
affine open around the distinguished point is small enough for the chosen big site, and an open
immersion matches the components through corresponding points. -/
theorem exists_elementaryEtaleNeighborhood_componentsThrough_equiv
    (U : ElementaryEtaleNeighborhood B S hS X hX x)
    (V : _root_.AlgebraicGeometry.EtaleNeighborhood U.scheme.left.1 U.point)
    (hV : V.IsElementary) :
    ∃ W : ElementaryEtaleNeighborhood B S hS X hX x,
      Nonempty ({C : Set W.scheme.left.1 //
          C ∈ irreducibleComponents W.scheme.left.1 ∧ W.point ∈ C} ≃
        {C : Set V.scheme // C ∈ irreducibleComponents V.scheme ∧ V.point ∈ C}) := by
  obtain ⟨_, ⟨O₀, hO, rfl⟩, hpO, -⟩ :=
    V.scheme.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ V.point) isOpen_univ
  let O : V.scheme.Opens := O₀
  let p : (O : Scheme.{u}) := ⟨V.point, hpO⟩
  let V' : _root_.AlgebraicGeometry.EtaleNeighborhood U.scheme.left.1 U.point :=
    { scheme := O
      point := p
      toBase := O.ι ≫ V.toBase
      map_point := V.map_point }
  have hV' : V'.IsElementary := by
    show IsIso ((U.scheme.left.1.residueFieldCongr V'.map_point).inv ≫
      (O.ι ≫ V.toBase).residueFieldMap p)
    rw [Scheme.residueFieldMap_comp]
    have hv : IsIso (V.toBase.residueFieldMap (O.ι p)) :=
      isIso_residueFieldMap_of_isElementary V hV
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' hv inferInstance)
  have : IsAffine (O : Scheme.{u}) := hO
  have hsmall : B.Contains V'.scheme :=
    (Scheme.size_le_of_locallyOfFiniteType V'.toBase).trans_lt U.scheme.left.2
  exact ⟨ElementaryEtaleNeighborhood.compScheme B S hS X hX x U V' hV' hsmall,
    ⟨componentsThroughEquivOfIsOpenEmbedding O.ι.isOpenEmbedding p⟩⟩

/-! ### Conditions (1) and (2) of Tag 0DQ6 -/

/-- **Stacks 0DQ6, conditions (1) and (2).** The local ring of every elementary étale
neighbourhood of `x` at its distinguished point has a unique minimal prime exactly when exactly
one irreducible component of every such neighbourhood passes through its distinguished point. -/
@[stacks 0DQ6 "conditions (1) and (2)"]
theorem forall_existsUnique_minimalPrimes_iff_forall_existsUnique_component :
    (∀ U : ElementaryEtaleNeighborhood B S hS X hX x,
        ∃! q : Ideal (U.scheme.left.1.presheaf.stalk U.point),
          q ∈ minimalPrimes (U.scheme.left.1.presheaf.stalk U.point)) ↔
      ∀ U : ElementaryEtaleNeighborhood B S hS X hX x,
        ∃! Z : irreducibleComponents U.scheme.left.1,
          U.point ∈ (Z : Set U.scheme.left.1) := by
  refine forall_congr' fun U ↦ (existsUnique_mem_iff_encard_eq_one _).trans ?_
  rw [← _root_.AlgebraicGeometry.encard_irreducibleComponentsThrough_eq_minimalPrimes_stalk]
  exact (existsUnique_mem_iff_encard_eq_one _).symm.trans
    (componentsThroughPack U.point).existsUnique_subtype_congr.symm

/-! ### Conditions (2) and (3) of Tag 0DQ6 -/

/-- **Stacks 0DQ6, conditions (2) and (3).** Exactly one irreducible component of every
elementary étale neighbourhood of `x` passes through its distinguished point exactly when the
local ring of every such neighbourhood at its distinguished point is unibranch. -/
@[stacks 0DQ6 "conditions (2) and (3)"]
theorem forall_existsUnique_component_iff_forall_isUnibranchAt :
    (∀ U : ElementaryEtaleNeighborhood B S hS X hX x,
        ∃! Z : irreducibleComponents U.scheme.left.1,
          U.point ∈ (Z : Set U.scheme.left.1)) ↔
      ∀ U : ElementaryEtaleNeighborhood B S hS X hX x,
        _root_.AlgebraicGeometry.IsUnibranchAt U.scheme.left.1 U.point := by
  constructor
  · intro h U
    refine (_root_.AlgebraicGeometry.isUnibranchAt_iff_existsUnique_irreducibleComponent
      U.scheme.left.1 U.point).mpr fun V hV ↦ ?_
    obtain ⟨W, ⟨e⟩⟩ :=
      exists_elementaryEtaleNeighborhood_componentsThrough_equiv B S hS X hX x U V hV
    exact ((componentsThroughPack W.point).trans
      (e.trans (componentsThroughPack V.point).symm)).existsUnique_subtype_congr.mp (h W)
  · intro h U
    exact (_root_.AlgebraicGeometry.isUnibranchAt_iff_existsUnique_irreducibleComponent
        U.scheme.left.1 U.point).mp (h U)
      (_root_.AlgebraicGeometry.EtaleNeighborhood.self U.scheme.left.1 U.point)
      (_root_.AlgebraicGeometry.EtaleNeighborhood.isElementary_self U.scheme.left.1 U.point)

/-! ### The three counted conditions of Tag 0DQ8 -/

/-- **Stacks 0DQ8, condition (1).** The local ring of every elementary étale neighbourhood of
`x` at its distinguished point has at most `n` minimal primes, and some such neighbourhood has
exactly `n`. -/
def HasMinimalPrimeCountOnElementaryNeighborhoods (n : ℕ) : Prop :=
  (∀ U : ElementaryEtaleNeighborhood B S hS X hX x,
      Set.encard (minimalPrimes (U.scheme.left.1.presheaf.stalk U.point)) ≤ (n : ℕ∞)) ∧
    ∃ U : ElementaryEtaleNeighborhood B S hS X hX x,
      Set.encard (minimalPrimes (U.scheme.left.1.presheaf.stalk U.point)) = (n : ℕ∞)

/-- **Stacks 0DQ8, condition (2).** At most `n` irreducible components of every elementary étale
neighbourhood of `x` pass through its distinguished point, and through the distinguished point of
some such neighbourhood exactly `n` pass. -/
def HasComponentCountOnElementaryNeighborhoods (n : ℕ) : Prop :=
  (∀ U : ElementaryEtaleNeighborhood B S hS X hX x,
      Set.encard {Z ∈ irreducibleComponents U.scheme.left.1 | U.point ∈ Z} ≤ (n : ℕ∞)) ∧
    ∃ U : ElementaryEtaleNeighborhood B S hS X hX x,
      Set.encard {Z ∈ irreducibleComponents U.scheme.left.1 | U.point ∈ Z} = (n : ℕ∞)

/-- **Stacks 0DQ8, condition (3).** Every elementary étale neighbourhood of `x` has at most `n`
branches at its distinguished point, and some such neighbourhood has exactly `n`. -/
def HasBranchCountOnElementaryNeighborhoods (n : ℕ) : Prop :=
  (∀ U : ElementaryEtaleNeighborhood B S hS X hX x,
      _root_.AlgebraicGeometry.numberOfBranches U.scheme.left.1 U.point ≤ (n : ℕ∞)) ∧
    ∃ U : ElementaryEtaleNeighborhood B S hS X hX x,
      _root_.AlgebraicGeometry.numberOfBranches U.scheme.left.1 U.point = (n : ℕ∞)

/-- **Stacks 0DQ8, conditions (1) and (2).** A point of a presheaf on the big fppf site has
minimal-prime count `n` on its elementary étale neighbourhoods exactly when it has
irreducible-component count `n` on them: the two counts agree neighbourhood by
neighbourhood. -/
@[stacks 0DQ8 "conditions (1) and (2)"]
theorem hasMinimalPrimeCount_iff_hasComponentCount (n : ℕ) :
    HasMinimalPrimeCountOnElementaryNeighborhoods B S hS X hX x n ↔
      HasComponentCountOnElementaryNeighborhoods B S hS X hX x n := by
  simp only [HasMinimalPrimeCountOnElementaryNeighborhoods,
    HasComponentCountOnElementaryNeighborhoods,
    ← _root_.AlgebraicGeometry.encard_irreducibleComponentsThrough_eq_minimalPrimes_stalk]

/-- A bound on the number of irreducible components through the distinguished point of every
elementary étale neighbourhood of `x` bounds the number of branches of every such neighbourhood
at its distinguished point: that number is the supremum of the component counts of the
elementary étale neighbourhoods of the distinguished point, and each of those is matched by a
neighbourhood of `x`. -/
private theorem numberOfBranches_le_of_forall_componentCount_le (n : ℕ∞)
    (hall : ∀ U : ElementaryEtaleNeighborhood B S hS X hX x,
      Set.encard {Z ∈ irreducibleComponents U.scheme.left.1 | U.point ∈ Z} ≤ n)
    (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    _root_.AlgebraicGeometry.numberOfBranches U.scheme.left.1 U.point ≤ n := by
  rw [_root_.AlgebraicGeometry.numberOfBranches_eq_iSup_encard_irreducibleComponentsThrough]
  refine iSup_le fun V ↦ iSup_le fun hV ↦ ?_
  obtain ⟨W, ⟨e⟩⟩ :=
    exists_elementaryEtaleNeighborhood_componentsThrough_equiv B S hS X hX x U V hV
  exact (Set.encard_congr e).symm.trans_le (hall W)

/-- An elementary étale neighbourhood of `x` whose branch count at its distinguished point is
the natural number `n` is matched by one with exactly `n` irreducible components through its
distinguished point: the supremum defining the branch count is finite, so it is attained at an
elementary étale neighbourhood of the distinguished point, which a neighbourhood of `x`
matches. -/
private theorem exists_componentCount_eq_of_numberOfBranches_eq (n : ℕ)
    (U : ElementaryEtaleNeighborhood B S hS X hX x)
    (hU : _root_.AlgebraicGeometry.numberOfBranches U.scheme.left.1 U.point = (n : ℕ∞)) :
    ∃ W : ElementaryEtaleNeighborhood B S hS X hX x,
      Set.encard {Z ∈ irreducibleComponents W.scheme.left.1 | W.point ∈ Z} = (n : ℕ∞) := by
  classical
  let I := {V : _root_.AlgebraicGeometry.EtaleNeighborhood U.scheme.left.1 U.point //
    V.IsElementary}
  let c : I → ℕ∞ := fun V ↦
    Set.encard {Z ∈ irreducibleComponents V.1.scheme | V.1.point ∈ Z}
  have : Nonempty I :=
    ⟨⟨_root_.AlgebraicGeometry.EtaleNeighborhood.self U.scheme.left.1 U.point,
      _root_.AlgebraicGeometry.EtaleNeighborhood.isElementary_self U.scheme.left.1 U.point⟩⟩
  have hsup : (⨆ V : I, c V) = (n : ℕ∞) := by
    rw [← hU,
      _root_.AlgebraicGeometry.numberOfBranches_eq_iSup_encard_irreducibleComponentsThrough]
    exact (iSup_subtype'
      (p := fun V : _root_.AlgebraicGeometry.EtaleNeighborhood U.scheme.left.1 U.point ↦
        V.IsElementary)
      (f := fun V _ ↦ Set.encard {Z ∈ irreducibleComponents V.scheme | V.point ∈ Z})).symm
  obtain ⟨V, hV⟩ := ENat.exists_eq_iSup_of_lt_top (hsup.trans_lt (ENat.natCast_lt_top n))
  obtain ⟨W, ⟨e⟩⟩ :=
    exists_elementaryEtaleNeighborhood_componentsThrough_equiv B S hS X hX x U V.1 V.2
  exact ⟨W, (Set.encard_congr e).trans (hV.trans hsup)⟩

/-- **Stacks 0DQ8, conditions (2) and (3).** A point of a presheaf on the big fppf site has
irreducible-component count `n` on its elementary étale neighbourhoods exactly when it has
branch count `n` on them. -/
@[stacks 0DQ8 "conditions (2) and (3)"]
theorem hasComponentCount_iff_hasBranchCount (n : ℕ) :
    HasComponentCountOnElementaryNeighborhoods B S hS X hX x n ↔
      HasBranchCountOnElementaryNeighborhoods B S hS X hX x n := by
  constructor
  · rintro ⟨hall, U, hU⟩
    have hb := numberOfBranches_le_of_forall_componentCount_le B S hS X hX x (n : ℕ∞) hall
    exact ⟨hb, U, le_antisymm (hb U) (hU.symm.trans_le
      (_root_.AlgebraicGeometry.encard_irreducibleComponentsThrough_le_numberOfBranches _ _))⟩
  · rintro ⟨hall, U, hU⟩
    exact ⟨fun W ↦
        (_root_.AlgebraicGeometry.encard_irreducibleComponentsThrough_le_numberOfBranches
          _ W.point).trans (hall W),
      exists_componentCount_eq_of_numberOfBranches_eq B S hS X hX x n U hU⟩

/-! ### The minimal primes of the henselian local ring -/

/-- **The bridge to the henselian local ring.** The henselian local ring at `x` has exactly as
many minimal primes as the local ring of an elementary étale neighbourhood of `x` has branches,
for every such neighbourhood: the henselian local ring is a henselization of that local ring, and
a ring isomorphism matches minimal primes. -/
theorem encard_minimalPrimes_henselianLocalRing (hDecent : IsDecentSpace B S hS X)
    (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    Set.encard (minimalPrimes (henselianLocalRing B S hS X hX x hDecent : Type (u + 1))) =
      _root_.AlgebraicGeometry.numberOfBranches U.scheme.left.1 U.point := by
  rw [_root_.AlgebraicGeometry.numberOfBranches_eq_numberOfBranchesOfLocalRing,
    numberOfBranchesOfLocalRing_eq_encard_minimalPrimes]
  obtain ⟨ι, -, -, -, ⟨hc⟩⟩ := _root_.AlgebraicGeometry.isColimit_globalSections
    U.scheme.left.1 U.point
    (henselizationData (U.scheme.left.1.presheaf.stalk U.point)).carrier
  obtain ⟨e, -⟩ := exists_henselianLocalRing_equiv B S hS X hX x hDecent U _ ι hc
  have hb := bijOn_minimalPrimes_ringEquiv e
  rw [← hb.image_eq, hb.injOn.encard_image]

/-- The branch counts of all the elementary étale neighbourhoods of `x` equal `m` exactly when the
henselian local ring at `x` has exactly `m` minimal primes. -/
private theorem forall_numberOfBranches_eq_iff_encard_minimalPrimes_henselianLocalRing
    (hDecent : IsDecentSpace B S hS X) (m : ℕ∞) :
    (∀ U : ElementaryEtaleNeighborhood B S hS X hX x,
        _root_.AlgebraicGeometry.numberOfBranches U.scheme.left.1 U.point = m) ↔
      Set.encard (minimalPrimes (henselianLocalRing B S hS X hX x hDecent : Type (u + 1))) = m := by
  refine ⟨fun h ↦ ?_, fun h U ↦ (encard_minimalPrimes_henselianLocalRing B S hS X hX x hDecent
    U).symm.trans h⟩
  obtain ⟨U, -⟩ := exists_affine_elementaryEtaleNeighborhood' B S hS hX hDecent x
  exact (encard_minimalPrimes_henselianLocalRing B S hS X hX x hDecent U).trans (h U)

/-! ### Condition (4) of Tag 0DQ6 -/

/-- **Stacks 0DQ6, conditions (3) and (4).** The local ring of every elementary étale
neighbourhood of `x` at its distinguished point is unibranch exactly when the henselian local ring
at `x` has a unique minimal prime: the two counts agree for every neighbourhood, and a decent
algebraic space has one. -/
theorem forall_isUnibranchAt_iff_existsUnique_minimalPrimes_henselianLocalRing
    (hDecent : IsDecentSpace B S hS X) :
    (∀ U : ElementaryEtaleNeighborhood B S hS X hX x,
        _root_.AlgebraicGeometry.IsUnibranchAt U.scheme.left.1 U.point) ↔
      ∃! p : Ideal (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)),
        p ∈ minimalPrimes (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)) := by
  rw [existsUnique_mem_iff_encard_eq_one,
    ← forall_numberOfBranches_eq_iff_encard_minimalPrimes_henselianLocalRing B S hS X hX x hDecent]
  exact forall_congr' fun U ↦ (_root_.AlgebraicGeometry.numberOfBranches_eq_one_iff _ _).symm

/-- **Stacks 0DQ6.** For a point of a decent algebraic space the four conditions of the source are
equivalent: every elementary étale neighbourhood has a local ring with a unique minimal prime, has
a unique irreducible component through its distinguished point, and has a unibranch local ring;
and the henselian local ring at the point has a unique minimal prime. -/
@[stacks 0DQ6 "(1)-(4) equivalent"]
theorem tfae_localIrreducibility (hDecent : IsDecentSpace B S hS X) :
    List.TFAE
      [∀ U : ElementaryEtaleNeighborhood B S hS X hX x,
          ∃! q : Ideal (U.scheme.left.1.presheaf.stalk U.point),
            q ∈ minimalPrimes (U.scheme.left.1.presheaf.stalk U.point),
        ∀ U : ElementaryEtaleNeighborhood B S hS X hX x,
          ∃! Z : irreducibleComponents U.scheme.left.1,
            U.point ∈ (Z : Set U.scheme.left.1),
        ∀ U : ElementaryEtaleNeighborhood B S hS X hX x,
          _root_.AlgebraicGeometry.IsUnibranchAt U.scheme.left.1 U.point,
        ∃! p : Ideal (henselianLocalRing B S hS X hX x hDecent : Type (u + 1)),
          p ∈ minimalPrimes (henselianLocalRing B S hS X hX x hDecent : Type (u + 1))] := by
  tfae_have 1 ↔ 2 :=
    forall_existsUnique_minimalPrimes_iff_forall_existsUnique_component B S hS X hX x
  tfae_have 2 ↔ 3 := forall_existsUnique_component_iff_forall_isUnibranchAt B S hS X hX x
  tfae_have 3 ↔ 4 :=
    forall_isUnibranchAt_iff_existsUnique_minimalPrimes_henselianLocalRing B S hS X hX x hDecent
  tfae_finish

/-! ### Condition (4) of Tag 0DQ8 -/

/-- **Stacks 0DQ8, conditions (3) and (4).** Every elementary étale neighbourhood of `x` has at
most `n` branches at its distinguished point with `n` attained at one of them exactly when the
henselian local ring at `x` has exactly `n` minimal primes: the branch counts of all the
neighbourhoods equal that number of minimal primes. -/
theorem hasBranchCount_iff_encard_minimalPrimes_henselianLocalRing
    (hDecent : IsDecentSpace B S hS X) (n : ℕ) :
    HasBranchCountOnElementaryNeighborhoods B S hS X hX x n ↔
      Set.encard (minimalPrimes (henselianLocalRing B S hS X hX x hDecent : Type (u + 1))) =
        (n : ℕ∞) := by
  have h := forall_numberOfBranches_eq_iff_encard_minimalPrimes_henselianLocalRing
    B S hS X hX x hDecent (n : ℕ∞)
  refine ⟨fun ⟨_, U, hU⟩ ↦ (encard_minimalPrimes_henselianLocalRing B S hS X hX x hDecent U).trans
    hU, fun hn ↦ ?_⟩
  obtain ⟨U₀, -⟩ := exists_affine_elementaryEtaleNeighborhood' B S hS hX hDecent x
  exact ⟨fun U ↦ (h.mpr hn U).le, U₀, h.mpr hn U₀⟩

/-- **Stacks 0DQ8.** For a point of a decent algebraic space and a natural number `n` the four
conditions of the source are equivalent: the minimal primes of the local ring, the irreducible
components through the distinguished point, and the branches each number at most `n` over all
elementary étale neighbourhoods with `n` attained at one of them; and the henselian local ring at
the point has exactly `n` minimal primes. -/
@[stacks 0DQ8 "(1)-(4) equivalent"]
theorem tfae_hasBranchCount (hDecent : IsDecentSpace B S hS X) (n : ℕ) :
    List.TFAE
      [HasMinimalPrimeCountOnElementaryNeighborhoods B S hS X hX x n,
        HasComponentCountOnElementaryNeighborhoods B S hS X hX x n,
        HasBranchCountOnElementaryNeighborhoods B S hS X hX x n,
        Set.encard (minimalPrimes (henselianLocalRing B S hS X hX x hDecent : Type (u + 1))) =
          (n : ℕ∞)] := by
  tfae_have 1 ↔ 2 := hasMinimalPrimeCount_iff_hasComponentCount B S hS X hX x n
  tfae_have 2 ↔ 3 := hasComponentCount_iff_hasBranchCount B S hS X hX x n
  tfae_have 3 ↔ 4 :=
    hasBranchCount_iff_encard_minimalPrimes_henselianLocalRing B S hS X hX x hDecent n
  tfae_finish

/-! ### Unibranch decent algebraic spaces -/

/-- **Stacks 0DQ7, unibranch at a point.** A decent algebraic space is *unibranch at `x`* when
the local ring of every elementary étale neighbourhood of `x` at its distinguished point is
unibranch, which is condition (3) of Tag 0DQ6. -/
@[stacks 0DQ7 "unibranch at a point"]
abbrev IsUnibranchAt (_hDecent : IsDecentSpace B S hS X) : Prop :=
  ∀ U : ElementaryEtaleNeighborhood B S hS X hX x,
    _root_.AlgebraicGeometry.IsUnibranchAt U.scheme.left.1 U.point

/-- **Stacks 0DQ7, unibranch.** A decent algebraic space is *unibranch* when it is unibranch at
every one of its points. -/
@[stacks 0DQ7 "unibranch"]
abbrev IsUnibranch (hDecent : IsDecentSpace B S hS X) : Prop :=
  ∀ y : points B S hS X, IsUnibranchAt B S hS X hX y hDecent

/-! ### The number of branches of a decent algebraic space at a point -/

/-- At most one natural number satisfies the branch-count condition of Tag 0DQ8 at `x`: the
condition bounds the branch count of every elementary étale neighbourhood of `x` at its
distinguished point by that number and attains it, so two such numbers bound each other. -/
private theorem hasBranchCount_unique {n m : ℕ}
    (hn : HasBranchCountOnElementaryNeighborhoods B S hS X hX x n)
    (hm : HasBranchCountOnElementaryNeighborhoods B S hS X hX x m) : n = m := by
  obtain ⟨hnall, U, hnU⟩ := hn
  obtain ⟨hmall, V, hmV⟩ := hm
  exact_mod_cast le_antisymm (hnU.symm.trans_le (hmall U)) (hmV.symm.trans_le (hnall V))

/-- The set of values in `ℕ∞` of the branch-count condition of Tag 0DQ8 at `x` is the singleton
of any natural number satisfying that condition. -/
private theorem hasBranchCount_values_eq_singleton {n : ℕ}
    (hn : HasBranchCountOnElementaryNeighborhoods B S hS X hX x n) :
    {v : ℕ∞ | ∃ m : ℕ, HasBranchCountOnElementaryNeighborhoods B S hS X hX x m ∧
        v = (m : ℕ∞)} = {(n : ℕ∞)} :=
  Set.eq_singleton_iff_unique_mem.mpr ⟨⟨n, hn, rfl⟩, by
    rintro v ⟨m, hm, rfl⟩
    rw [hasBranchCount_unique B S hS X hX x hm hn]⟩

/-- **Stacks 0DQ9.** The number of branches of a decent algebraic space at a point: the natural
number satisfying the equivalent conditions of Tag 0DQ8 if there is one, and `⊤` otherwise. -/
@[stacks 0DQ9]
def numberOfBranches (_hDecent : IsDecentSpace B S hS X) : ℕ∞ :=
  sInf {v : ℕ∞ | ∃ n : ℕ, HasBranchCountOnElementaryNeighborhoods B S hS X hX x n ∧
    v = (n : ℕ∞)}

/-- The number of branches of a decent algebraic space at a point is infinite exactly when no
natural number satisfies the equivalent conditions of Tag 0DQ8. -/
@[stacks 0DQ9 "infinite value"]
theorem numberOfBranches_eq_top_iff (hDecent : IsDecentSpace B S hS X) :
    numberOfBranches B S hS X hX x hDecent = ⊤ ↔
      ∀ n : ℕ, ¬ HasBranchCountOnElementaryNeighborhoods B S hS X hX x n := by
  rw [numberOfBranches, sInf_eq_top]
  exact ⟨fun h n hn ↦ absurd (h (n : ℕ∞) ⟨n, hn, rfl⟩) (ENat.natCast_lt_top n).ne,
    fun h _ ⟨n, hn, _⟩ ↦ (h n hn).elim⟩

/-- A finite value of the number of branches of a decent algebraic space at a point is exactly
the value appearing in the equivalent conditions of Tag 0DQ8. -/
@[stacks 0DQ9 "finite value"]
theorem numberOfBranches_eq_nat_iff (hDecent : IsDecentSpace B S hS X) (n : ℕ) :
    numberOfBranches B S hS X hX x hDecent = (n : ℕ∞) ↔
      HasBranchCountOnElementaryNeighborhoods B S hS X hX x n := by
  refine ⟨fun h ↦ ?_, fun hn ↦ ?_⟩
  · by_cases hex : ∃ m : ℕ, HasBranchCountOnElementaryNeighborhoods B S hS X hX x m
    · obtain ⟨m, hm⟩ := hex
      rw [numberOfBranches, hasBranchCount_values_eq_singleton B S hS X hX x hm,
        sInf_singleton] at h
      obtain rfl : m = n := by exact_mod_cast h
      exact hm
    · rw [(numberOfBranches_eq_top_iff B S hS X hX x hDecent).mpr (not_exists.mp hex)] at h
      exact absurd h (ENat.natCast_lt_top n).ne'
  · rw [numberOfBranches, hasBranchCount_values_eq_singleton B S hS X hX x hn, sInf_singleton]

end AlgebraicGeometry.Space

end
