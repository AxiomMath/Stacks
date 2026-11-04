module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenSchemeLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreSquareOverIsoSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedEtaleDiagonalComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces

/-!
# The covering of a space over the fibre square of a separated étale morphism

Let `f : V ⟶ W` be a separated étale morphism of algebraic spaces over a scheme `S`. Its fibre
square `V ×_W V` is cut by the point set of the relative diagonal into two open subspaces, the
diagonal part `Δ` and its complement `Δᶜ`: this is the decomposition `V ×_W V = Δ(V) ⊔ U`
which opens the proof of Stacks 0BGY.

Any algebraic space `Q` with a morphism `κ : Q ⟶ V ×_W V` inherits that decomposition as an
fppf covering of `Q` by two open subspaces, and on the two pieces the two projections of the
fibre square behave in complementary ways: on the diagonal piece they agree after `κ`, and on
the complementary piece the common composite to `W` lands in the open complement of any closed
subspace `T` whose preimage is carried isomorphically onto it.

## Main definitions

* `AlgebraicGeometry.Space.diagOpen` and `AlgebraicGeometry.Space.offDiagOpen`: the diagonal
  part of the fibre square and its complement, as open subspaces.
* `AlgebraicGeometry.Space.diagPair`: the two of them as a family indexed by `Bool`.

## Main results

* `AlgebraicGeometry.Space.diagOpen_eq_range`: the diagonal part is the range of the relative
  diagonal, so the two projections agree on it.
* `AlgebraicGeometry.Space.offDiagOpen_eq_openComplement`: the complementary part is the open
  complement of that range.
* `AlgebraicGeometry.Space.isFppfCovering_diagPair_preimage`: the two pieces pulled back along
  `κ` form an fppf covering of `Q`.
* `AlgebraicGeometry.Space.diagPreimage_comp_fst_eq_snd`: on the diagonal piece the two
  projections of the fibre square agree.
* `AlgebraicGeometry.Space.range_offDiagPreimage_le_openComplement`: **the step
  `U ×_W T = ∅`** — on the complementary piece the composite to `W` lands in the open
  complement of `T`.

## Implementation notes

The two pieces are cut out as `AlgebraicGeometry.Space.openSubspaceOfPoints` of the point set
of the relative diagonal and of its complement, rather than taken from
`AlgebraicGeometry.Space.exists_diagonalComplement_decomposition`. That way their point sets
are available by definition, which is what the covering property needs, and their preimages
along `κ` are again cut out by point sets through
`AlgebraicGeometry.Space.preimage_openSubspaceOfPoints`. They are then *identified* with the
range of the diagonal and with the open complement of that range, using that an open subspace
is determined by its point set
(`AlgebraicGeometry.Space.eq_openSubspaceOfPoints_range_pointsMap_ι`); it is through those
identifications that the two geometric conclusions are drawn.

The lattice form of the decomposition — the join sheafifying to the top and the meet to the
sheafified bottom — is not used: a covering and the two one-sided conclusions are all the
amalgamation of a morphism out of `Q` needs, and the covering is checked on points by
Stacks 03BZ.

Membership in the open complement of the range of the diagonal is used exactly as its
definition reads: a restriction of a section of the complementary piece whose image in `W`
lands in `T` lies over an empty scheme, because that restriction lands in the range of the
diagonal by `AlgebraicGeometry.Space.preimage_fst_comp_eq_range_diagonal`.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : V ⟶ W)
  (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W)

/-! ### The two pieces of the fibre square -/

/-- The point set of the relative diagonal of `f` inside the point space of its fibre
square. -/
noncomputable def diagPoints : Set (points B S hS (pullback f f)) :=
  Set.range (pointsMap B S hS V (pullback.diagonal f))

/-- The diagonal part of the fibre square of `f`, as an open subspace. -/
noncomputable def diagOpen : Subfunctor (pullback f f) :=
  openSubspaceOfPoints B S hS (pullback f f) (diagPoints B S hS f)

/-- The complement of the diagonal in the fibre square of `f`, as an open subspace. -/
noncomputable def offDiagOpen : Subfunctor (pullback f f) :=
  openSubspaceOfPoints B S hS (pullback f f) (diagPoints B S hS f)ᶜ

/-- The two pieces of the fibre square as a family indexed by `Bool`. -/
noncomputable def diagPair (b : Bool) : Subfunctor (pullback f f) :=
  cond b (offDiagOpen B S hS f) (diagOpen B S hS f)

/-- The piece of `diagPair` at `false` is the diagonal part. -/
@[simp] theorem diagPair_false : diagPair B S hS f false = diagOpen B S hS f := rfl

/-- The piece of `diagPair` at `true` is the off-diagonal part. -/
@[simp] theorem diagPair_true : diagPair B S hS f true = offDiagOpen B S hS f := rfl

variable (hf : IsEtale B S hS f) (hsep : IsSeparated B S hS f)

include hV hW in
/-- The fibre square of `f` is an algebraic space. -/
theorem isAlgebraicSpace_pullback_self : IsAlgebraicSpace B S hS (pullback f f) :=
  isAlgebraicSpace_pullback B S hS f f hV hV hW

include hV hW hf hsep in
/-- The point set of the relative diagonal is open and closed. -/
theorem isClopen_diagPoints : IsClopen (diagPoints B S hS f) :=
  isClopen_range_pointsMap_pullbackDiagonal B S hS hV hW f hf hsep

include hV hW hf hsep in
/-- The diagonal part of the fibre square is an open subspace. -/
theorem isOpenSubspace_diagOpen : IsOpenSubspace B S hS (diagOpen B S hS f) :=
  isOpenSubspace_openSubspaceOfPoints B S hS
    (isAlgebraicSpace_pullback_self B S hS f hV hW) _
    (isClopen_diagPoints B S hS f hV hW hf hsep).2

include hV hW hf hsep in
/-- The complement of the diagonal in the fibre square is an open subspace. -/
theorem isOpenSubspace_offDiagOpen : IsOpenSubspace B S hS (offDiagOpen B S hS f) :=
  isOpenSubspace_openSubspaceOfPoints B S hS
    (isAlgebraicSpace_pullback_self B S hS f hV hW) _
    (isClopen_diagPoints B S hS f hV hW hf hsep).1.isOpen_compl

include hV hW hf hsep in
/-- Each piece of the fibre square is an open subspace. -/
theorem isOpenSubspace_diagPair (b : Bool) : IsOpenSubspace B S hS (diagPair B S hS f b) := by
  cases b
  · exact isOpenSubspace_diagOpen B S hS f hV hW hf hsep
  · exact isOpenSubspace_offDiagOpen B S hS f hV hW hf hsep

/-! ### The two pieces identified -/

include hV hW hf hsep in
/-- **The diagonal part of the fibre square is the range of the relative diagonal.** Both are
open subspaces with the same point set. -/
theorem diagOpen_eq_range :
    diagOpen B S hS f = Subfunctor.range (pullback.diagonal f) := by
  have _ : Mono (pullback.diagonal f) := inferInstance
  have hopen : IsOpenSubspace B S hS (Subfunctor.range (pullback.diagonal f)) :=
    isOpenSubspace_subfunctorRange B S hS hV
      (isOpenImmersion_diagonal_of_isUnramified B S hS hV hW f
        (isUnramified_of_isEtale B S hS hf))
  rw [eq_openSubspaceOfPoints_range_pointsMap_ι B S hS
    (isAlgebraicSpace_pullback_self B S hS f hV hW) hopen, diagOpen, diagPoints,
    range_pointsMap_ι_range B S hS (pullback.diagonal f)]

include hV hW hf hsep in
/-- **The complementary part of the fibre square is the open complement of the range of the
relative diagonal.** -/
theorem offDiagOpen_eq_openComplement :
    offDiagOpen B S hS f = openComplement B S hS (Subfunctor.range (pullback.diagonal f)) := by
  have _ : Mono (pullback.diagonal f) := inferInstance
  rw [openComplement_eq_openSubspaceOfPoints_compl, offDiagOpen, diagPoints,
    range_pointsMap_ι_range B S hS (pullback.diagonal f)]

/-! ### The induced covering of a space over the fibre square -/

variable {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (κ : Q ⟶ pullback f f)
  (hQ : IsAlgebraicSpace B S hS Q)

include hV hW hQ in
/-- Each piece of the fibre square pulls back to an open subspace of `Q`. -/
theorem isOpenSubspace_diagPair_preimage (hb : ∀ b, IsOpenSubspace B S hS (diagPair B S hS f b))
    (b : Bool) : IsOpenSubspace B S hS ((diagPair B S hS f b).preimage κ) :=
  isOpenSubspace_preimage B S hS κ _ (isAlgebraicSpace_pullback_self B S hS f hV hW) hQ (hb b)

/-- The point set of a piece of the fibre square pulled back along `κ`. -/
theorem range_pointsMap_ι_diagPair_preimage (b : Bool) :
    Set.range (pointsMap B S hS ((diagPair B S hS f b).preimage κ).toFunctor
        ((diagPair B S hS f b).preimage κ).ι) =
      pointsMap B S hS Q κ ⁻¹' (cond b (diagPoints B S hS f)ᶜ (diagPoints B S hS f)) := by
  cases b
  · rw [diagPair_false, diagOpen, preimage_openSubspaceOfPoints,
      range_pointsMap_ι_openSubspaceOfPoints]
    rfl
  · rw [diagPair_true, offDiagOpen, preimage_openSubspaceOfPoints,
      range_pointsMap_ι_openSubspaceOfPoints]
    rfl

include hV hW hf hsep hQ in
/-- **The two pieces of the fibre square pulled back along `κ` form an fppf covering of
`Q`.** -/
theorem isFppfCovering_diagPair_preimage :
    IsFppfCovering B S hS
      (fun b : Bool => ((diagPair B S hS f b).preimage κ).toFunctor)
      (fun b : Bool => ((diagPair B S hS f b).preimage κ).ι) := by
  have hb := isOpenSubspace_diagPair B S hS f hV hW hf hsep
  have hopen := isOpenSubspace_diagPair_preimage B S hS f hV hW κ hQ hb
  refine isFppfCovering_of_isZariskiCovering B S hS hQ (fun b => (hopen b).1)
    ⟨fun b => (hopen b).2, fun x => ?_⟩
  have key (b : Bool)
      (hx : pointsMap B S hS Q κ x ∈ cond b (diagPoints B S hS f)ᶜ (diagPoints B S hS f)) :
      ∃ i, x ∈ Set.range (pointsMap B S hS ((diagPair B S hS f i).preimage κ).toFunctor
        ((diagPair B S hS f i).preimage κ).ι) :=
    ⟨b, by rw [range_pointsMap_ι_diagPair_preimage]; exact hx⟩
  by_cases hx : pointsMap B S hS Q κ x ∈ diagPoints B S hS f
  · exact key false hx
  · exact key true hx

/-! ### The two one-sided conclusions -/

include hV hW hf hsep in
/-- **On the diagonal piece the two projections of the fibre square agree.** -/
theorem diagPreimage_comp_fst_eq_snd :
    ((diagOpen B S hS f).preimage κ).ι ≫ κ ≫ pullback.fst f f =
      ((diagOpen B S hS f).preimage κ).ι ≫ κ ≫ pullback.snd f f := by
  have _ : Mono (pullback.diagonal f) := inferInstance
  have hfac : ((diagOpen B S hS f).preimage κ).ι ≫ κ =
      (diagOpen B S hS f).fromPreimage κ ≫ (diagOpen B S hS f).ι :=
    ((diagOpen B S hS f).fromPreimage_ι κ).symm
  have hrange : (diagOpen B S hS f).ι ≫ pullback.fst f f =
      (diagOpen B S hS f).ι ≫ pullback.snd f f := by
    rw [diagOpen_eq_range B S hS f hV hW hf hsep]
    have h : (asIso (Subfunctor.toRange (pullback.diagonal f))).inv ≫ pullback.diagonal f =
        (Subfunctor.range (pullback.diagonal f)).ι :=
      (asIso (Subfunctor.toRange (pullback.diagonal f))).inv_comp_eq.2
        (Subfunctor.toRange_ι (pullback.diagonal f)).symm
    rw [← h, Category.assoc, Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd]
  rw [← Category.assoc, ← Category.assoc, hfac, Category.assoc, Category.assoc, hrange]


variable (T : Subfunctor W) (hT : IsIso (T.fromPreimage f))

include hV hW hf hsep hT in
/-- **The step `U ×_W T = ∅` of the proof of Stacks 0BGY.** On the complementary piece the
composite to `W` lands in the open complement of `T`: a restriction of a section of that piece
whose image in `W` lies in `T` lands in the range of the diagonal, hence lies over an empty
scheme. -/
theorem range_offDiagPreimage_le_openComplement :
    Subfunctor.range (((offDiagOpen B S hS f).preimage κ).ι ≫ κ ≫
        (pullback.fst f f ≫ f)) ≤ openComplement B S hS T := by
  have hdiag : T.preimage (pullback.fst f f ≫ f) ≤
      Subfunctor.range (pullback.diagonal f) := by
    rw [preimage_fst_comp_eq_range_diagonal B S hS f T hT]
    exact Subfunctor.range_comp_le _ _
  rintro A _ ⟨z, rfl⟩
  intro A' a ha
  have hz : κ.app A (((offDiagOpen B S hS f).preimage κ).ι.app A z) ∈
      (openComplement B S hS (Subfunctor.range (pullback.diagonal f))).obj A := by
    rw [← offDiagOpen_eq_openComplement B S hS f hV hW hf hsep]
    exact z.2
  refine hz A' a ?_
  refine hdiag A' ?_
  change (pullback.fst f f ≫ f).app A' ((pullback f f).map a
    (κ.app A (((offDiagOpen B S hS f).preimage κ).ι.app A z))) ∈ T.obj A'
  rw [NatTrans.naturality_apply]
  exact ha

end AlgebraicGeometry.Space

end
