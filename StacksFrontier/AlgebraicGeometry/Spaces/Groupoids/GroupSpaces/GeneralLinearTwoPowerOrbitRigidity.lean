module

public import StacksFrontier.AlgebraicGeometry.Spaces.DenseClosedPointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ContractedPieceOrbitAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.GeneralLinearTwoPowerOrbitMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.GeneralLinearTwoPowerRationalPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.GeneralLinearTwoPowerSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.DenseWitnessedAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence

/-!
# From a Zariski open set of group elements to all of them

The contraction step of [Stacks, Tag 0AEM] delivers an identity only over an open neighbourhood
of the identity of `G = (GL_{2,K})^m`: applied to a closed subvariety `C` of `(ℙ¹_K)^m` which
`f` maps to a point, [Stacks, Tag 0AEJ] gives an open `U ⊆ G` such that for every `K`-point `M`
of `U` the translate `M · C` is carried by `f` into something finite over `Spec K`, whence
`f(M · x) = f(M · y)` for the two rational points `x, y` of `C`.  The exercise the source then
quotes is a density statement about the orbit of `(x, y)` under the *whole* group, so the step
has to get from `U(K)` to `G(K)`.

This file does that.  Two framings are available and the cheaper one is taken.

* **The closure framing (not taken).** Transport the density along the orbit map
  `γ : G ⟶ (ℙ¹_K)^m`: `γ⁻¹(cl γ(U))` is closed and contains `U`, hence contains `cl U = G`
  because `G` is irreducible, so `cl γ(U) ⊇ cl γ(G)` and the `U`-orbit of a point is as dense as
  its `G`-orbit.  This needs the closure of the image of a morphism of algebraic spaces on
  points, the irreducibility of `|G|` as a point space rather than as a scheme, and a density
  statement about the orbit restated for `U` rather than `G`.
* **The group-side rigidity framing (taken).** Do not move the density to the target at all.
  The two morphisms `G ⟶ Z`, `g ↦ f(g · x)` and `g ↦ f(g · y)`, are
  `AlgebraicGeometry.Space.generalLinearTwoPowerOrbitMap` followed by `f`; they agree at every
  `K`-point of `U`; the `K`-points of `|G|` lying in a nonempty open subspace are dense
  (`AlgebraicGeometry.Space.dense_setOf_exists_rationalPoint_notMem` at the represented space
  `G`); `G` is reduced and `Z` is separated over the base; so the two morphisms are *equal*
  (`AlgebraicGeometry.Space.eq_of_eq_on_dense_witnessed_base`), and the identity therefore holds
  at every `K`-point of `G` whatsoever.

The second framing is cheaper and leaves less to maintain: every input it needs is already
available, it never mentions a closure or an image, and the density it consumes is density in
`|G|` — which the representability of `G` by an irreducible affine scheme of finite type over
`K` supplies directly — rather than density of an orbit in a fibre product.  It also yields a
*stronger* conclusion than the closure argument does: not "the orbit under `U(K)` is dense" but
the identity `f ∘ γ_x = f ∘ γ_y` of morphisms out of the whole group, from which the value at
every `K`-point of `G` follows by
`AlgebraicGeometry.Space.comp_generalLinearTwoPowerOrbitMap`.

Turning a dense set of points of `|G|` into a dense set of *tuples of matrices* is
`AlgebraicGeometry.Space.exists_eq_yoneda_map_generalLinearTwoPowerSitePoint`, and lifting such
a rational point through the open subspace `U` it lands in is
`AlgebraicGeometry.Space.le_of_range_pointsMap_ι_subset` at the range of that rational point —
a morphism out of the terminal presheaf is a split monomorphism, so its range has its image on
points as point set.

## Main results

* `AlgebraicGeometry.Space.exists_sectionOfOpenSubspace_of_range_pointsMap_subset`: a rational
  point of an algebraic space whose image on points lies in an open subspace factors through
  that open subspace.
* `AlgebraicGeometry.Space.comp_orbitMap_eq_of_eq_on_openSubspace`: **the rigidity step** — if
  `f(M · x) = f(M · y)` for every `K`-point `M` of a nonempty open subspace of `G`, then the two
  orbit maps of `x` and `y` followed by `f` are equal as morphisms out of `G`.
* `AlgebraicGeometry.Space.comp_matrixAut_eq_of_eq_on_openSubspace`: the same read at an
  arbitrary `K`-point: **`f(M · x) = f(M · y)` for every `m`-tuple `M` of invertible
  matrices.**
* `AlgebraicGeometry.Space.comp_orbitMap_eq_of_contractedPiece` and
  `AlgebraicGeometry.Space.comp_matrixAut_eq_of_contractedPiece`: **the contraction step of
  [Stacks, Tag 0AEM] for all of `G`** — the two theorems above fed by
  `AlgebraicGeometry.Space.exists_isOpenSubspace_forall_comp_matrixAut_comp_eq_of_factors`,
  which is [Stacks, Tag 0AEJ] together with the constancy of a morphism from an irreducible
  piece into a space finite over the algebraically closed field.  No hypothesis beyond the
  geometric input — `C` a contracted closed subspace with preirreducible point space carrying
  the two rational points — is left.

## Implementation notes

The subject of this file is only the passage from `U(K)` to `G(K)`; the open subspace `U`, and
the agreement over its `K`-points, are taken from
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/GroupSpaces/ContractedPieceOrbitAgreement.lean`,
where [Stacks, Tag 0AEJ]'s finiteness is spent.

One hypothesis is inherited unchanged from that file and from the contraction step
`AlgebraicGeometry.Space.exists_isOpenSubspace_forall_isFinite_comp_eq_orbitMap`: `hconst` asks
that `f` carry `C` to a *rational* point `ζ` of `Z`, not merely that the image of `|C|` be a
single point of `|Z|`.  Producing that rational point from a one-point image is a separate step
and is not done here; the passage from `U(K)` to `G(K)` neither needs nor weakens it.

## References

* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 084N](https://stacks.math.columbia.edu/tag/084N)
* [Stacks Project, Tag 0AEJ](https://stacks.math.columbia.edu/tag/0AEJ)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Lifting a rational point through an open subspace -/

section Lift

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism out of the terminal presheaf of the big fppf site over `S` into a presheaf is a
split monomorphism: the structure morphism of the target to the base is a retraction of it,
there being only one morphism to the base. -/
theorem isSplitMono_of_isTerminal_src
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hT : IsTerminal T) (ξ : T ⟶ X) :
    IsSplitMono ξ :=
  IsSplitMono.mk ⟨⟨hT.from X, hT.hom_ext _ _⟩⟩

/-- **A rational point of an algebraic space whose image on points lies in an open subspace
factors through that open subspace.**

The range of the rational point is a subfunctor whose point set is exactly the image on points
(the rational point is a split monomorphism, its source being terminal), so it is contained in
the open subspace by the injectivity half of clause (1) of [Stacks, Tag 03BZ]. -/
theorem exists_sectionOfOpenSubspace_of_range_pointsMap_subset
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hT : IsTerminal T) (ξ : T ⟶ X) {U : Subfunctor X}
    (hU : IsOpenSubspace B S hS U)
    (hsub : Set.range (pointsMap B S hS T ξ) ⊆
      Set.range (pointsMap B S hS U.toFunctor U.ι)) :
    ∃ s : T ⟶ U.toFunctor, s ≫ U.ι = ξ := by
  let := isSplitMono_of_isTerminal_src B S hS hT ξ
  have hle : Subfunctor.range ξ ≤ U :=
    le_of_range_pointsMap_ι_subset B S hS hU
      ((range_pointsMap_ι_range B S hS ξ).trans_subset hsub)
  refine ⟨Subfunctor.toRange ξ ≫ Subfunctor.homOfLe hle, ?_⟩
  rw [Category.assoc, Subfunctor.homOfLe_ι, Subfunctor.toRange_ι]

end Lift

/-! ### The rigidity step on the group -/

section Rigidity

variable (k : Type u) [Field k] [IsAlgClosed k] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (CommRingCat.of k))) (m : ℕ)
  {Z : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u}
  (z : Z ⟶ baseFunctor k B hk)
  (f : projectiveLinePower k B hk (Fin m) ⟶ Z)
  (x y : baseFunctor k B hk ⟶ projectiveLinePower k B hk (Fin m))

omit [IsAlgClosed k] in
/-- The underlying scheme of the site object `(GL₂)^m` is integral and its structure morphism is
of finite type: it is a variety over `k`. -/
private theorem isVariety_generalLinearTwoPowerSiteObject :
    IsVariety k (B.inclusion.map (generalLinearTwoPowerSiteObject k B hk m).hom) :=
  isVariety_generalLinearTwoPowerStructureMap k m

omit [IsAlgClosed k] in
/-- `(GL₂)^m` is a reduced algebraic space over `Spec k`: it is represented by an object of the
site whose underlying scheme is integral. -/
private theorem hasEtaleLocalProperty_isReduced_generalLinearTwoPower :
    HasEtaleLocalProperty B (Spec (CommRingCat.of k)) hk
      (generalLinearTwoPowerFunctor k B hk m) (fun W : Scheme.{u} => IsReduced W) :=
  let := isVariety_generalLinearTwoPowerSiteObject k B hk m
  hasEtaleLocalProperty_of_representable B (Spec (CommRingCat.of k)) hk _ _
    (generalLinearTwoPowerSiteObject k B hk m) (Iso.refl _) inferInstance

/-- **The rigidity step: an identity holding at every `k`-point of a nonempty open subspace of
`(GL₂)^m` holds as an identity of morphisms out of `(GL₂)^m`.**

Let `Z` be an algebraic space separated over `Spec k`, let `f : (ℙ¹_k)^m ⟶ Z` and let `x, y` be
two `k`-rational points of `(ℙ¹_k)^m`.  Let `U` be an open subspace of `(GL₂)^m` with at least
one point, and suppose `f(M · x) = f(M · y)` for every `k`-point `M` of `(GL₂)^m` factoring
through `U`.  Then the two orbit maps `g ↦ g · x` and `g ↦ g · y` followed by `f` are the same
morphism `(GL₂)^m ⟶ Z`.

The `k`-rational points of `|(GL₂)^m|` outside the closed complement of `U` are dense, each is
named by an `m`-tuple of invertible matrices, each such tuple factors through `U` and therefore
equalizes the two morphisms, and the agreement locus of two morphisms into a space separated
over the base is closed in the reduced `(GL₂)^m`. -/
theorem comp_orbitMap_eq_of_eq_on_openSubspace
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Z)
    (hz_sep : IsSeparated B (Spec (CommRingCat.of k)) hk z)
    {U : Subfunctor (generalLinearTwoPowerFunctor k B hk m)}
    (hU : IsOpenSubspace B (Spec (CommRingCat.of k)) hk U)
    (hUne : ∃ p, p ∈ Set.range (pointsMap B (Spec (CommRingCat.of k)) hk U.toFunctor U.ι))
    (hagree : ∀ (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k)
        (s : baseFunctor k B hk ⟶ U.toFunctor),
      s ≫ U.ι = yoneda.map (generalLinearTwoPowerSitePoint k B hk m M) →
      x ≫ (projectiveLinePowerFunctorMatrixAut k B hk m M).hom ≫ f =
        y ≫ (projectiveLinePowerFunctorMatrixAut k B hk m M).hom ≫ f) :
    generalLinearTwoPowerOrbitMap k B hk m x ≫ f =
      generalLinearTwoPowerOrbitMap k B hk m y ≫ f := by
  let := isVariety_generalLinearTwoPowerSiteObject k B hk m
  have hopen : IsOpen (Set.range (pointsMap B (Spec (CommRingCat.of k)) hk U.toFunctor U.ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B (Spec (CommRingCat.of k)) hk U.ι hU.2
  have hdense := dense_setOf_exists_rationalPoint_notMem B k hk
    (generalLinearTwoPowerSiteObject k B hk m)
    (Iso.refl (generalLinearTwoPowerFunctor k B hk m)) inferInstance inferInstance
    (Z := (Set.range (pointsMap B (Spec (CommRingCat.of k)) hk U.toFunctor U.ι))ᶜ)
    (isClosed_compl_iff.2 hopen) (by simpa using hUne)
  refine eq_of_eq_on_dense_witnessed_base B (Spec (CommRingCat.of k)) hk
    (isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _) hZ
    (hasEtaleLocalProperty_isReduced_generalLinearTwoPower k B hk m)
    (base_isTerminal k B hk)
    (isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _) z hz_sep _ _ _ hdense ?_
  rintro p ⟨⟨ξ, hpξ, hξp⟩, hpU⟩
  obtain ⟨M, hM⟩ := exists_eq_yoneda_map_generalLinearTwoPowerSitePoint k B hk m ξ
  obtain ⟨s, hs⟩ := exists_sectionOfOpenSubspace_of_range_pointsMap_subset B
    (Spec (CommRingCat.of k)) hk (base_isTerminal k B hk) ξ hU
    (hξp.trans (Set.singleton_subset_iff.2 (not_not.1 hpU)))
  refine ⟨_, ξ, ?_, hpξ⟩
  rw [← hM, ← Category.assoc, ← Category.assoc,
    comp_generalLinearTwoPowerOrbitMap k B hk m x M,
    comp_generalLinearTwoPowerOrbitMap k B hk m y M, Category.assoc, Category.assoc]
  exact hagree M s (by rw [hs, hM])

/-- **The identity at every `k`-point of `(GL₂)^m`**: with the hypotheses of
`AlgebraicGeometry.Space.comp_orbitMap_eq_of_eq_on_openSubspace`, `f(M · x) = f(M · y)` for
*every* `m`-tuple `M` of invertible two-by-two matrices over `k`, not only for those in the open
subspace.  This is what the exercise quoted in the proof of [Stacks, Tag 0AEM] is applied to. -/
theorem comp_matrixAut_eq_of_eq_on_openSubspace
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Z)
    (hz_sep : IsSeparated B (Spec (CommRingCat.of k)) hk z)
    {U : Subfunctor (generalLinearTwoPowerFunctor k B hk m)}
    (hU : IsOpenSubspace B (Spec (CommRingCat.of k)) hk U)
    (hUne : ∃ p, p ∈ Set.range (pointsMap B (Spec (CommRingCat.of k)) hk U.toFunctor U.ι))
    (hagree : ∀ (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k)
        (s : baseFunctor k B hk ⟶ U.toFunctor),
      s ≫ U.ι = yoneda.map (generalLinearTwoPowerSitePoint k B hk m M) →
      x ≫ (projectiveLinePowerFunctorMatrixAut k B hk m M).hom ≫ f =
        y ≫ (projectiveLinePowerFunctorMatrixAut k B hk m M).hom ≫ f)
    (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k) :
    x ≫ (projectiveLinePowerFunctorMatrixAut k B hk m M).hom ≫ f =
      y ≫ (projectiveLinePowerFunctorMatrixAut k B hk m M).hom ≫ f := by
  rw [← reassoc_of% comp_generalLinearTwoPowerOrbitMap k B hk m x M,
    ← reassoc_of% comp_generalLinearTwoPowerOrbitMap k B hk m y M,
    comp_orbitMap_eq_of_eq_on_openSubspace k B hk m z f x y hZ hz_sep hU hUne hagree]

end Rigidity

/-! ### The contraction step of 0AEM for the whole group -/

section Assemble

variable (k : Type u) [Field k] [IsAlgClosed k] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (CommRingCat.of k))) (m : ℕ)
  {Z : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u}
  (z : Z ⟶ baseFunctor k B hk)
  (f : projectiveLinePower k B hk (Fin m) ⟶ Z)
  (C : Subfunctor (projectiveLinePower k B hk (Fin m)))
  (ζ : baseFunctor k B hk ⟶ Z)
  (x y : baseFunctor k B hk ⟶ projectiveLinePower k B hk (Fin m))

/-- **The contraction step of [Stacks, Tag 0AEM], as an identity of morphisms out of the whole
group.**

Let `Z` be an algebraic space over `k`, separated and locally of finite type over `Spec k`, let
`f : (ℙ¹_k)^m ⟶ Z` and let `C` be a closed subspace of `(ℙ¹_k)^m` with preirreducible point
space which `f` carries to a single point `ζ`.  Let `x` and `y` be two `k`-rational points of
`(ℙ¹_k)^m` factoring through `C`.  Then the two orbit maps `g ↦ g · x` and `g ↦ g · y` followed
by `f` are the *same* morphism `(GL₂)^m ⟶ Z`.

[Stacks, Tag 0AEJ], through
`AlgebraicGeometry.Space.exists_isOpenSubspace_forall_comp_matrixAut_comp_eq_of_factors`, gives
`f(M · x) = f(M · y)` for the `k`-points `M` of an open subspace `U` containing the identity;
the rigidity step above turns that into an identity over all of `(GL₂)^m`. -/
theorem comp_orbitMap_eq_of_contractedPiece
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Z)
    (hz_sep : IsSeparated B (Spec (CommRingCat.of k)) hk z)
    (hz_lft : IsLocallyOfFiniteType B (Spec (CommRingCat.of k)) hk z)
    (hC : IsClosedSubspace B (Spec (CommRingCat.of k)) hk C)
    (hconst : C.ι ≫ f = toBaseFunctor k B hk C.toFunctor ≫ ζ)
    (hCirr : PreirreducibleSpace (points B (Spec (CommRingCat.of k)) hk C.toFunctor))
    (hx : ∃ l, l ≫ C.ι = x) (hy : ∃ l, l ≫ C.ι = y) :
    generalLinearTwoPowerOrbitMap k B hk m x ≫ f =
      generalLinearTwoPowerOrbitMap k B hk m y ≫ f := by
  obtain ⟨U, hU, hb, hagree⟩ :=
    exists_isOpenSubspace_forall_comp_matrixAut_comp_eq_of_factors k B hk m z f C ζ hZ hz_sep
      hz_lft hC hconst hCirr x y hx hy
  exact comp_orbitMap_eq_of_eq_on_openSubspace k B hk m z f x y hZ hz_sep hU ⟨_, hb⟩ hagree

/-- **`f(M · x) = f(M · y)` for every `m`-tuple `M` of invertible two-by-two matrices over
`k`**, under the hypotheses of
`AlgebraicGeometry.Space.comp_orbitMap_eq_of_contractedPiece`: the identity of orbit maps read
at the `k`-point of `(GL₂)^m` named by `M`.

This is what the exercise quoted in the proof of [Stacks, Tag 0AEM] is applied to, with the
restriction to a Zariski open subset of the group already removed. -/
theorem comp_matrixAut_eq_of_contractedPiece
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Z)
    (hz_sep : IsSeparated B (Spec (CommRingCat.of k)) hk z)
    (hz_lft : IsLocallyOfFiniteType B (Spec (CommRingCat.of k)) hk z)
    (hC : IsClosedSubspace B (Spec (CommRingCat.of k)) hk C)
    (hconst : C.ι ≫ f = toBaseFunctor k B hk C.toFunctor ≫ ζ)
    (hCirr : PreirreducibleSpace (points B (Spec (CommRingCat.of k)) hk C.toFunctor))
    (hx : ∃ l, l ≫ C.ι = x) (hy : ∃ l, l ≫ C.ι = y)
    (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k) :
    x ≫ (projectiveLinePowerFunctorMatrixAut k B hk m M).hom ≫ f =
      y ≫ (projectiveLinePowerFunctorMatrixAut k B hk m M).hom ≫ f := by
  obtain ⟨U, hU, hb, hagree⟩ :=
    exists_isOpenSubspace_forall_comp_matrixAut_comp_eq_of_factors k B hk m z f C ζ hZ hz_sep
      hz_lft hC hconst hCirr x y hx hy
  exact comp_matrixAut_eq_of_eq_on_openSubspace k B hk m z f x y hZ hz_sep hU ⟨_, hb⟩ hagree M

end Assemble

end AlgebraicGeometry.Space

end
