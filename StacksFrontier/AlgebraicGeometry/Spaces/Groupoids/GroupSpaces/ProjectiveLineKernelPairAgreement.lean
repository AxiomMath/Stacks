module

public import StacksFrontier.AlgebraicGeometry.Spaces.DenseClosedPointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ProjectiveLinePowerOrbitDense
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ProjectiveLinePowerSlicePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.SubsetProjectionKernelPair
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.DenseWitnessedAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# The orbit-density exercise of Stacks 0AEM, restated on the kernel pair

The contraction step of [Stacks, Tag 0AEM] has, at this point, the identity

`f(M · x) = f(M · y)` for *every* `m`-tuple `M` of invertible two-by-two matrices over `K`

for two distinct `K`-rational points `x ≠ y` of `(ℙ¹_K)^m`
(`AlgebraicGeometry.Space.comp_matrixAut_eq_of_contractedPiece`), and has to conclude that `f`
factors through the projection onto the set `S = {i | xᵢ = yᵢ}` of coordinates on which `x` and
`y` agree. This file is that conclusion, which is the exercise the source leaves to the reader.

The reduction to a single identity is
`AlgebraicGeometry.Space.exists_eq_subsetProjection_comp_of_kernelPair_eq`: the projection is
split, hence the coequalizer of its own kernel pair, so it is enough to prove that the two legs
of that kernel pair agree after `f`. The kernel pair is itself a power of the projective line,
indexed by the coordinates outside `S` together with a second full copy of the coordinates
(`AlgebraicGeometry.Space.isPullback_subsetKernelPair`), and *that* is where the density
argument runs — not in the square `(ℙ¹_K)^m × (ℙ¹_K)^m`, where the statement
`AlgebraicGeometry.dense_setOf_exists_powerMatrixAut` is vacuous as soon as `S ≠ ∅`.

The density argument has three parts.

* **Which points of the kernel pair the orbit reaches.** A `K`-rational point of the kernel pair
  is a pair `(p, q)` of rational points of `(ℙ¹_K)^m` with `pᵢ = qᵢ` for `i ∈ S`; the orbit of
  `(x, y)` reaches it as soon as moreover `pᵢ ≠ qᵢ` for every `i ∉ S`, by
  `AlgebraicGeometry.Space.exists_comp_projectiveLinePowerFunctorMatrixAut_hom_eq_and_eq`.
* **The locus where some coordinate outside `S` coincides is closed and proper.** For a
  coordinate `c` outside `S` the agreement locus of the two coordinate morphisms
  `π_{inl c}, π_{inr c}` of the kernel pair is a closed subspace, the projective line being
  separated over `Spec K` (Stacks 084N through
  `AlgebraicGeometry.Space.eqSubfunctor`). It is proper because the kernel pair is reduced, so a
  closed subspace with all the points is everything (Stacks 03JJ), which would force
  `π_{inl c} = π_{inr c}`; and that fails at the rational point whose `inl` coordinates are
  `xⱼ` and whose `inr` coordinates are `yⱼ`, for a coordinate `j` at which `x` and `y` differ.
  Finitely many proper closed subsets of an irreducible space do not cover it.
* **The rational points off that locus are dense**, by
  `AlgebraicGeometry.Space.dense_setOf_exists_rationalPoint_notMem` at the kernel pair, which is
  represented by an object of the site whose scheme is an irreducible power of the projective
  line proper over `Spec K`.

Those three parts feed
`AlgebraicGeometry.Space.eq_of_eq_on_dense_witnessed_base`: each point of the dense set is
witnessed by a rational point which the orbit reaches, and at which the two legs therefore agree.

## Main results

* `AlgebraicGeometry.Space.comp_subsetKernelPair_eq_of_comp_matrixAut_eq`: **the two legs of the
  kernel pair agree after `f`.**
* `AlgebraicGeometry.Space.exists_coordinateProjection_comp_eq_of_comp_matrixAut_eq`: **`f`
  factors through the projection onto the coordinates on which `x` and `y` agree** — the
  conclusion of the contraction step of [Stacks, Tag 0AEM].

## References

* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 084N](https://stacks.math.columbia.edu/tag/084N)
* [Stacks Project, Tag 0AEL](https://stacks.math.columbia.edu/tag/0AEL)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
* [Stacks Project, Tag 0B2U](https://stacks.math.columbia.edu/tag/0B2U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Finitely many proper closed subsets do not cover an irreducible space -/

/-- In a nonempty preirreducible space a finite family of nonempty open sets has nonempty
intersection: each member is dense, and a finite intersection of dense open sets is dense. -/
private theorem nonempty_iInter_of_isOpen_of_preirreducible {α : Type*} [TopologicalSpace α]
    [PreirreducibleSpace α] [Nonempty α] {ι : Type*} [Finite ι] (s : ι → Set α)
    (hopen : ∀ i, IsOpen (s i)) (hne : ∀ i, (s i).Nonempty) :
    (⋂ i, s i).Nonempty := by
  classical
  let := Fintype.ofFinite ι
  have key : ∀ t : Finset ι, Dense (⋂ i ∈ t, s i) := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · simp
    · intro a t _ ih
      rw [Finset.set_biInter_insert]
      exact ((hopen a).dense (hne a)).inter_of_isOpen_left ih (hopen a)
  simpa only [Finset.mem_univ, Set.iInter_true] using (key Finset.univ).nonempty

/-! ### The projective line is separated over the base -/

variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (CommRingCat.of K)))

/-- **The projective line, read as an object of the big fppf site, is separated over the
base.** Its structure morphism in the site underlies the structure morphism of `ℙ¹_K` over
`Spec K`, which is proper, hence separated. -/
theorem isSeparated_yoneda_map_projectiveLineSiteToBase :
    IsSeparated B (Spec (CommRingCat.of K)) hK
      (yoneda.map (projectiveLineSiteToBase K B hK)) := by
  rw [isSeparated_yoneda_map_iff, toScheme_map_projectiveLineSiteToBase]
  exact inferInstanceAs (_root_.AlgebraicGeometry.IsSeparated
    (projectiveSpaceOverRing 1 (CommRingCat.of K) ↘ Spec (CommRingCat.of K)))

/-! ### A power of the projective line at a finite index type, as a represented space -/

/-- A power of the projective line indexed by a finite type, read as the functor of points of
the object of the site representing the self-product of `ℙ¹_K` with that many factors. -/
noncomputable def projectiveLinePowerFiniteYonedaIso (α : Type v) [Small.{u} α] [Finite α] :
    projectiveLinePower K B hK α ≅
      yoneda.obj (projectiveSpacePowerSiteObject K B hK (Nat.card α)) :=
  projectiveLinePowerReindexIso K B hK (Finite.equivFin α) ≪≫
    (projectiveSpacePowerYonedaIso K B hK (Nat.card α)).symm

/-- A power of the projective line indexed by a finite type is reduced: it is represented by an
object of the site whose underlying scheme is smooth over `Spec K`, hence reduced. -/
theorem hasEtaleLocalProperty_isReduced_projectiveLinePowerFinite (α : Type v) [Small.{u} α]
    [Finite α] :
    HasEtaleLocalProperty B (Spec (CommRingCat.of K)) hK (projectiveLinePower K B hK α)
      (fun W : Scheme.{u} => IsReduced W) :=
  hasEtaleLocalProperty_of_representable B (Spec (CommRingCat.of K)) hK _ _
    (projectiveLinePowerSiteObject K B hK (Nat.card α))
    (projectiveLinePowerReindexIso K B hK (Finite.equivFin α) ≪≫
      projectiveLinePowerRepresentationIso K B hK (Nat.card α))
    (isReduced_projectiveLinePowerSiteObject K B hK (Nat.card α))

variable [IsAlgClosed K]

/-- The scheme of the site object representing a power of the projective line indexed by a finite
type is irreducible. -/
private theorem irreducibleSpace_toScheme_projectiveSpacePowerSiteObject (α : Type v)
    [Small.{u} α] [Finite α] :
    IrreducibleSpace ((BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).obj
      (projectiveSpacePowerSiteObject K B hK (Nat.card α))) :=
  irreducibleSpace_projectiveSpacePowerOver K (Nat.card α)

/-- The point space of a power of the projective line indexed by a finite type is
preirreducible: it is homeomorphic to the point space of an irreducible power of `ℙ¹_K`. -/
theorem preirreducibleSpace_points_projectiveLinePowerFinite (α : Type v) [Small.{u} α]
    [Finite α] :
    PreirreducibleSpace (points B (Spec (CommRingCat.of K)) hK (projectiveLinePower K B hK α)) :=
  have := irreducibleSpace_toScheme_projectiveSpacePowerSiteObject K B hK α
  (pointsHomeomorphSchemeOfIso B K hK _
      (projectiveLinePowerFiniteYonedaIso K B hK α)).symm.surjective.preirreducibleSpace
    (pointsHomeomorphSchemeOfIso B K hK _
      (projectiveLinePowerFiniteYonedaIso K B hK α)).symm.continuous

/-- The point space of a power of the projective line indexed by a finite type is nonempty. -/
theorem nonempty_points_projectiveLinePowerFinite (α : Type v) [Small.{u} α] [Finite α] :
    Nonempty (points B (Spec (CommRingCat.of K)) hK (projectiveLinePower K B hK α)) :=
  have := irreducibleSpace_toScheme_projectiveSpacePowerSiteObject K B hK α
  ⟨(pointsHomeomorphSchemeOfIso B K hK _
    (projectiveLinePowerFiniteYonedaIso K B hK α)).symm (Classical.arbitrary _)⟩

/-- The rational points of a power of the projective line indexed by a finite type which avoid
a proper closed subset of its point space are dense. -/
theorem dense_setOf_exists_rationalPoint_notMem_projectiveLinePowerFinite (α : Type v)
    [Small.{u} α] [Finite α]
    {E : Set (points B (Spec (CommRingCat.of K)) hK (projectiveLinePower K B hK α))}
    (hE : IsClosed E) (hE' : ∃ p, p ∉ E) :
    Dense {p : points B (Spec (CommRingCat.of K)) hK (projectiveLinePower K B hK α) |
      (∃ ξ : baseFunctor K B hK ⟶ projectiveLinePower K B hK α,
        p ∈ Set.range (pointsMap B (Spec (CommRingCat.of K)) hK _ ξ) ∧
          Set.range (pointsMap B (Spec (CommRingCat.of K)) hK _ ξ) ⊆ {p}) ∧ p ∉ E} :=
  have := irreducibleSpace_toScheme_projectiveSpacePowerSiteObject K B hK α
  let : _root_.AlgebraicGeometry.IsProper
      (B.inclusion.map (projectiveSpacePowerSiteObject K B hK (Nat.card α)).hom) :=
    isProper_projectiveSpacePowerOver K (Nat.card α)
  dense_setOf_exists_rationalPoint_notMem B K hK _
    (projectiveLinePowerFiniteYonedaIso K B hK α) inferInstance inferInstance hE hE'

/-! ### The locus where two coordinates coincide -/

/-- **The locus in a power of the projective line where two prescribed coordinates
coincide**, as a subfunctor: the agreement locus of the two coordinate morphisms, read into
the functor of points of the object of the site representing `ℙ¹_K`. -/
noncomputable def coordinateAgreementSubfunctor (α : Type v) [Small.{u} α] (a b : α) :
    Subfunctor (projectiveLinePower K B hK α) :=
  eqSubfunctor B (Spec (CommRingCat.of K)) hK (yoneda.map (projectiveLineSiteToBase K B hK))
    (Pi.π (fun _ : α => projectiveLineFunctor K B hK) a ≫
      (projectiveLineRestrictedYonedaIso K B hK).hom)
    (Pi.π (fun _ : α => projectiveLineFunctor K B hK) b ≫
      (projectiveLineRestrictedYonedaIso K B hK).hom)
    ((base_isTerminal K B hK).hom_ext _ _)

omit [IsAlgClosed K] in
/-- A subfunctor lies in the coincidence locus of two coordinates exactly when the two
coordinate morphisms agree on it. -/
theorem le_coordinateAgreementSubfunctor_iff (α : Type v) [Small.{u} α] (a b : α)
    (V : Subfunctor (projectiveLinePower K B hK α)) :
    V ≤ coordinateAgreementSubfunctor K B hK α a b ↔
      V.ι ≫ Pi.π (fun _ : α => projectiveLineFunctor K B hK) a =
        V.ι ≫ Pi.π (fun _ : α => projectiveLineFunctor K B hK) b := by
  rw [coordinateAgreementSubfunctor, le_eqSubfunctor_iff]
  simp only [← Category.assoc]
  exact Iso.cancel_iso_hom_right _ _ (projectiveLineRestrictedYonedaIso K B hK)

omit [IsAlgClosed K] in
/-- A morphism into a power of the projective line whose two prescribed coordinates agree has
its range inside the coincidence locus of those coordinates. -/
theorem range_le_coordinateAgreementSubfunctor (α : Type v) [Small.{u} α] (a b : α)
    {W : (BigFppfOver B (Spec (CommRingCat.of K)) hK)ᵒᵖ ⥤ Type u}
    (w : W ⟶ projectiveLinePower K B hK α)
    (hw : w ≫ Pi.π (fun _ : α => projectiveLineFunctor K B hK) a =
      w ≫ Pi.π (fun _ : α => projectiveLineFunctor K B hK) b) :
    Subfunctor.range w ≤ coordinateAgreementSubfunctor K B hK α a b := by
  refine range_le_eqSubfunctor_of_comp_eq B (Spec (CommRingCat.of K)) hK _ _ _
    ((base_isTerminal K B hK).hom_ext _ _) w ?_
  simp only [← Category.assoc]
  exact hw =≫ (projectiveLineRestrictedYonedaIso K B hK).hom

omit [IsAlgClosed K] in
/-- The coincidence locus of two coordinates is a closed subspace: the projective line is
separated over the base, so the agreement locus of two morphisms into it is closed
(Stacks 084N). -/
theorem isClosedSubspace_coordinateAgreementSubfunctor (α : Type v) [Small.{u} α] [Finite α]
    (a b : α) :
    IsClosedSubspace B (Spec (CommRingCat.of K)) hK
      (coordinateAgreementSubfunctor K B hK α a b) :=
  isClosedSubspace_eqSubfunctor B (Spec (CommRingCat.of K)) hK
    (isAlgebraicSpace_yoneda B (Spec (CommRingCat.of K)) hK _)
    (isAlgebraicSpace_projectiveLinePower K B hK α)
    (isAlgebraicSpace_yoneda B (Spec (CommRingCat.of K)) hK _) _ _ _ _
    (isSeparated_yoneda_map_projectiveLineSiteToBase K B hK)

omit [IsAlgClosed K] in
/-- The point set of the coincidence locus of two coordinates is closed. -/
theorem isClosed_range_pointsMap_coordinateAgreementSubfunctor (α : Type v) [Small.{u} α]
    [Finite α] (a b : α) :
    IsClosed (Set.range (pointsMap B (Spec (CommRingCat.of K)) hK
      (coordinateAgreementSubfunctor K B hK α a b).toFunctor
      (coordinateAgreementSubfunctor K B hK α a b).ι)) :=
  isClosed_range_pointsMap_of_isClosedImmersion B (Spec (CommRingCat.of K)) hK
    (isAlgebraicSpace_projectiveLinePower K B hK α) _
    (isClosedSubspace_coordinateAgreementSubfunctor K B hK α a b).2

omit [IsAlgClosed K] in
/-- **The coincidence locus of two coordinates is a proper closed subset**, as soon as some
rational point has those two coordinates distinct: were its point set everything, the power of
the projective line being reduced would make the locus the whole space (Stacks 03JJ), hence the
two coordinate morphisms equal. -/
theorem range_pointsMap_coordinateAgreementSubfunctor_ne_univ (α : Type v) [Small.{u} α]
    [Finite α] (a b : α) (ξ : baseFunctor K B hK ⟶ projectiveLinePower K B hK α)
    (hξ : ξ ≫ Pi.π (fun _ : α => projectiveLineFunctor K B hK) a ≠
      ξ ≫ Pi.π (fun _ : α => projectiveLineFunctor K B hK) b) :
    Set.range (pointsMap B (Spec (CommRingCat.of K)) hK
        (coordinateAgreementSubfunctor K B hK α a b).toFunctor
        (coordinateAgreementSubfunctor K B hK α a b).ι) ≠ Set.univ := by
  intro hfull
  obtain ⟨l, hl⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B
    (Spec (CommRingCat.of K)) hK (isAlgebraicSpace_projectiveLinePower K B hK α)
    (isAlgebraicSpace_projectiveLinePower K B hK α)
    (coordinateAgreementSubfunctor K B hK α a b)
    (isClosedSubspace_coordinateAgreementSubfunctor K B hK α a b)
    (hasEtaleLocalProperty_isReduced_projectiveLinePowerFinite K B hK α)
    (𝟙 (projectiveLinePower K B hK α))).2 (by simp [hfull])
  have htop : (⊤ : Subfunctor (projectiveLinePower K B hK α)) ≤
      coordinateAgreementSubfunctor K B hK α a b := by
    intro V v _
    have hval : (l.app V v).1 = v :=
      congrArg (fun j : projectiveLinePower K B hK α ⟶ projectiveLinePower K B hK α =>
        j.app V v) hl
    exact hval ▸ (l.app V v).2
  have heq : Pi.π (fun _ : α => projectiveLineFunctor K B hK) a ≫
      (projectiveLineRestrictedYonedaIso K B hK).hom =
    Pi.π (fun _ : α => projectiveLineFunctor K B hK) b ≫
      (projectiveLineRestrictedYonedaIso K B hK).hom :=
    (eqSubfunctor_eq_top_iff B (Spec (CommRingCat.of K)) hK _ _ _ _).1
      (le_antisymm le_top htop)
  exact hξ (congrArg (fun t => ξ ≫ t)
    ((Iso.cancel_iso_hom_right _ _ (projectiveLineRestrictedYonedaIso K B hK)).1 heq))

/-! ### The two legs of the kernel pair agree -/

/-- **The two legs of the kernel pair of the projection onto the coordinates on which `x` and
`y` agree take the same value after `f`.**

This is the exercise quoted in the proof of [Stacks, Tag 0AEM], restated where it is not
vacuous. Let `x ≠ y` be two `K`-rational points of `(ℙ¹_K)^m`, let `S` be the set of coordinates
on which they agree, and suppose `f(M · x) = f(M · y)` for every `m`-tuple `M` of invertible
two-by-two matrices. The kernel pair of the projection onto the coordinates in `S` is the power
of the projective line indexed by the coordinates outside `S` together with a second copy of all
of them; a rational point of it off the finitely many coincidence loci of the paired coordinates
has the coincidence pattern of `(x, y)`, hence lies in the orbit of `(x, y)`, hence is a point
at which the two legs agree after `f`; and those rational points are dense. The agreement locus
is closed, `Z` being separated over `Spec K`, so the two legs agree outright. -/
theorem comp_subsetKernelPair_eq_of_comp_matrixAut_eq (m : ℕ)
    {Z : (BigFppfOver B (Spec (CommRingCat.of K)) hK)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of K)) hK Z)
    (z : Z ⟶ baseFunctor K B hK)
    (hz_sep : IsSeparated B (Spec (CommRingCat.of K)) hK z)
    (g : projectiveLinePower K B hK (Fin m) ⟶ Z)
    (x y : baseFunctor K B hK ⟶ projectiveLinePower K B hK (Fin m)) (hxy : x ≠ y)
    (S : Finset (Fin m))
    (hS : ∀ i : Fin m, i ∈ S ↔
      x ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) i =
        y ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) i)
    (hagree : ∀ M : Fin m → Matrix.GeneralLinearGroup (Fin 2) K,
      x ≫ (projectiveLinePowerFunctorMatrixAut K B hK m M).hom ≫ g =
        y ≫ (projectiveLinePowerFunctorMatrixAut K B hK m M).hom ≫ g) :
    subsetKernelPairFst K B hK (Finset.univ : Finset (Fin m)) S ≫
        (coordinateProjectionUnivIso K B hK m).inv ≫ g =
      subsetKernelPairSnd K B hK (Finset.univ : Finset (Fin m)) S ≫
        (coordinateProjectionUnivIso K B hK m).inv ≫ g := by
  classical
  let : PreirreducibleSpace (points B (Spec (CommRingCat.of K)) hK
      (projectiveLinePower K B hK
        (subsetComplIndex (Finset.univ : Finset (Fin m)) S ⊕
          ↥(Finset.univ : Finset (Fin m))))) :=
    preirreducibleSpace_points_projectiveLinePowerFinite K B hK _
  let : Nonempty (points B (Spec (CommRingCat.of K)) hK
      (projectiveLinePower K B hK
        (subsetComplIndex (Finset.univ : Finset (Fin m)) S ⊕
          ↥(Finset.univ : Finset (Fin m))))) :=
    nonempty_points_projectiveLinePowerFinite K B hK _
  -- the inverse of the projection onto all the coordinates reads coordinate `i` off `⟨i, _⟩`
  have hpi : ∀ i : Fin m, (coordinateProjectionUnivIso K B hK m).inv ≫
        Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) i =
      Pi.π (fun _ : ↥(Finset.univ : Finset (Fin m)) => projectiveLineFunctor K B hK)
        ⟨i, Finset.mem_univ i⟩ := fun i =>
    (Pi.map'_comp_π _ _ i).trans (Category.comp_id _)
  -- a coordinate at which `x` and `y` differ
  obtain ⟨j, hj⟩ : ∃ j : Fin m,
      x ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) j ≠
        y ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) j := by
    by_contra hcon
    exact hxy (Pi.hom_ext _ _ fun i => not_not.1 fun h => hcon ⟨i, h⟩)
  -- the rational point of the kernel pair with `x_j` in every `inl` slot and `y_j` in every
  -- `inr` slot: its paired coordinates are distinct, so no coincidence locus is everything
  obtain ⟨ξ₀, hξ₀l, hξ₀r⟩ : ∃ ξ₀ : baseFunctor K B hK ⟶ projectiveLinePower K B hK
      (subsetComplIndex (Finset.univ : Finset (Fin m)) S ⊕ ↥(Finset.univ : Finset (Fin m))),
      (∀ c : subsetComplIndex (Finset.univ : Finset (Fin m)) S,
          ξ₀ ≫ Pi.π (fun _ : subsetComplIndex (Finset.univ : Finset (Fin m)) S ⊕
              ↥(Finset.univ : Finset (Fin m)) => projectiveLineFunctor K B hK) (Sum.inl c) =
            x ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) j) ∧
        ∀ i : ↥(Finset.univ : Finset (Fin m)),
          ξ₀ ≫ Pi.π (fun _ : subsetComplIndex (Finset.univ : Finset (Fin m)) S ⊕
              ↥(Finset.univ : Finset (Fin m)) => projectiveLineFunctor K B hK) (Sum.inr i) =
            y ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) j :=
    ⟨Pi.lift (fun b => Sum.elim
        (fun _ : subsetComplIndex (Finset.univ : Finset (Fin m)) S =>
          x ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) j)
        (fun _ : ↥(Finset.univ : Finset (Fin m)) =>
          y ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) j) b),
      fun c => Pi.lift_comp_π _ (Sum.inl c), fun i => Pi.lift_comp_π _ (Sum.inr i)⟩
  -- the point set of the coincidence locus of the paired coordinates at `c`
  let bad := fun c : subsetComplIndex (Finset.univ : Finset (Fin m)) S =>
    Set.range (pointsMap B (Spec (CommRingCat.of K)) hK
      (coordinateAgreementSubfunctor K B hK
        (subsetComplIndex (Finset.univ : Finset (Fin m)) S ⊕
          ↥(Finset.univ : Finset (Fin m))) (Sum.inl c) (Sum.inr c.1)).toFunctor
      (coordinateAgreementSubfunctor K B hK
        (subsetComplIndex (Finset.univ : Finset (Fin m)) S ⊕
          ↥(Finset.univ : Finset (Fin m))) (Sum.inl c) (Sum.inr c.1)).ι)
  have hclosed : ∀ c, IsClosed (bad c) := fun c =>
    isClosed_range_pointsMap_coordinateAgreementSubfunctor K B hK _ _ _
  have hne : ∀ c, bad c ≠ Set.univ := by
    intro c
    refine range_pointsMap_coordinateAgreementSubfunctor_ne_univ K B hK _ _ _ ξ₀ ?_
    rw [hξ₀l c, hξ₀r c.1]
    exact hj
  -- the bad locus is closed and proper
  have hbadne : ∃ p, p ∉ ⋃ c, bad c := by
    obtain ⟨p, hp⟩ := nonempty_iInter_of_isOpen_of_preirreducible (fun c => (bad c)ᶜ)
      (fun c => (hclosed c).isOpen_compl) (fun c => Set.nonempty_compl.2 (hne c))
    refine ⟨p, ?_⟩
    simpa only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_iUnion, not_exists] using hp
  -- the rational points off the bad locus are dense
  have hdense := dense_setOf_exists_rationalPoint_notMem_projectiveLinePowerFinite K B hK
    (subsetComplIndex (Finset.univ : Finset (Fin m)) S ⊕ ↥(Finset.univ : Finset (Fin m)))
    (isClosed_iUnion_of_finite hclosed) hbadne
  refine eq_of_eq_on_dense_witnessed_base B (Spec (CommRingCat.of K)) hK
    (isAlgebraicSpace_projectiveLinePower K B hK _) hZ
    (hasEtaleLocalProperty_isReduced_projectiveLinePowerFinite K B hK _)
    (base_isTerminal K B hK) (isAlgebraicSpace_yoneda B (Spec (CommRingCat.of K)) hK _) z hz_sep
    _ _ _ hdense ?_
  rintro p ⟨⟨ξ, hξmem, hξsub⟩, hξbad⟩
  refine ⟨baseFunctor K B hK, ξ, ?_, hξmem⟩
  -- the paired coordinates of `ξ` are distinct outside `S`
  have hξne : ∀ c : subsetComplIndex (Finset.univ : Finset (Fin m)) S,
      ξ ≫ Pi.π (fun _ : subsetComplIndex (Finset.univ : Finset (Fin m)) S ⊕
          ↥(Finset.univ : Finset (Fin m)) => projectiveLineFunctor K B hK) (Sum.inl c) ≠
        ξ ≫ Pi.π (fun _ : subsetComplIndex (Finset.univ : Finset (Fin m)) S ⊕
          ↥(Finset.univ : Finset (Fin m)) => projectiveLineFunctor K B hK) (Sum.inr c.1) := by
    intro c heq
    refine hξbad (Set.mem_iUnion.2 ⟨c, ?_⟩)
    exact mem_range_pointsMap_ι_of_range_le B (Spec (CommRingCat.of K)) hK ξ _
      (range_le_coordinateAgreementSubfunctor K B hK _ (Sum.inl c) (Sum.inr c.1) ξ heq) hξmem
  -- `ξ` has the coincidence pattern of `(x, y)`, so it lies in the orbit
  have hpat : ∀ i : Fin m,
      (x ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) i =
          y ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) i) ↔
        ((ξ ≫ subsetKernelPairFst K B hK (Finset.univ : Finset (Fin m)) S ≫
              (coordinateProjectionUnivIso K B hK m).inv) ≫
            Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) i =
          (ξ ≫ subsetKernelPairSnd K B hK (Finset.univ : Finset (Fin m)) S ≫
              (coordinateProjectionUnivIso K B hK m).inv) ≫
            Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) i) := by
    intro i
    by_cases hi : i ∈ S
    · refine iff_of_true ((hS i).1 hi) ?_
      simp only [Category.assoc, hpi i,
        subsetKernelPairFst_comp_π_of_mem K B hK (⟨i, Finset.mem_univ i⟩ :
          ↥(Finset.univ : Finset (Fin m))) hi,
        subsetKernelPairSnd_comp_π K B hK (⟨i, Finset.mem_univ i⟩ :
          ↥(Finset.univ : Finset (Fin m)))]
    · refine iff_of_false (fun h => hi ((hS i).2 h)) ?_
      simp only [Category.assoc, hpi i,
        subsetKernelPairFst_comp_π_of_notMem K B hK (⟨i, Finset.mem_univ i⟩ :
          ↥(Finset.univ : Finset (Fin m))) hi,
        subsetKernelPairSnd_comp_π K B hK (⟨i, Finset.mem_univ i⟩ :
          ↥(Finset.univ : Finset (Fin m)))]
      exact hξne ⟨⟨i, Finset.mem_univ i⟩, hi⟩
  obtain ⟨M, hM₁, hM₂⟩ := exists_comp_projectiveLinePowerFunctorMatrixAut_hom_eq_and_eq K B hK m
    x y
    (ξ ≫ subsetKernelPairFst K B hK (Finset.univ : Finset (Fin m)) S ≫
      (coordinateProjectionUnivIso K B hK m).inv)
    (ξ ≫ subsetKernelPairSnd K B hK (Finset.univ : Finset (Fin m)) S ≫
      (coordinateProjectionUnivIso K B hK m).inv)
    hxy hpat
  have h₁ := hM₁ =≫ g
  have h₂ := hM₂ =≫ g
  simp only [Category.assoc] at h₁ h₂
  rw [← h₁, ← h₂]
  exact hagree M

/-- **The contraction step of [Stacks, Tag 0AEM]: `f` factors through the projection onto the
coordinates on which `x` and `y` agree.**

The projection onto those coordinates is split, hence the coequalizer of its own kernel pair
(`AlgebraicGeometry.Space.exists_eq_subsetProjection_comp_of_kernelPair_eq`), and the two legs
of that kernel pair agree after `f` by
`AlgebraicGeometry.Space.comp_subsetKernelPair_eq_of_comp_matrixAut_eq`.  The projection onto
all the coordinates is an isomorphism, so the factorization through the projection onto the
subset follows by composing the projections. -/
theorem exists_coordinateProjection_comp_eq_of_comp_matrixAut_eq (m : ℕ)
    {Z : (BigFppfOver B (Spec (CommRingCat.of K)) hK)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of K)) hK Z)
    (z : Z ⟶ baseFunctor K B hK)
    (hz_sep : IsSeparated B (Spec (CommRingCat.of K)) hK z)
    (g : projectiveLinePower K B hK (Fin m) ⟶ Z)
    (x y : baseFunctor K B hK ⟶ projectiveLinePower K B hK (Fin m)) (hxy : x ≠ y)
    (S : Finset (Fin m))
    (hS : ∀ i : Fin m, i ∈ S ↔
      x ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) i =
        y ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) i)
    (hagree : ∀ M : Fin m → Matrix.GeneralLinearGroup (Fin 2) K,
      x ≫ (projectiveLinePowerFunctorMatrixAut K B hK m M).hom ≫ g =
        y ≫ (projectiveLinePowerFunctorMatrixAut K B hK m M).hom ≫ g) :
    ∃ g' : projectiveLinePower K B hK S ⟶ Z, g = coordinateProjection K B hK m S ≫ g' := by
  obtain ⟨g', hg'⟩ := exists_eq_subsetProjection_comp_of_kernelPair_eq K B hK
    (Finset.subset_univ S) ((coordinateProjectionUnivIso K B hK m).inv ≫ g)
    (comp_subsetKernelPair_eq_of_comp_matrixAut_eq K B hK m hZ z hz_sep g x y hxy S hS hagree)
  refine ⟨g', ?_⟩
  calc g = (coordinateProjectionUnivIso K B hK m).hom ≫
        (coordinateProjectionUnivIso K B hK m).inv ≫ g := (Iso.hom_inv_id_assoc _ _).symm
    _ = coordinateProjection K B hK m Finset.univ ≫
        subsetProjection K B hK (Finset.subset_univ S) ≫ g' := by
        rw [hg']
        rfl
    _ = coordinateProjection K B hK m S ≫ g' := by
        rw [← Category.assoc, coordinateProjection_comp_subsetProjection]

end AlgebraicGeometry.Space

end
