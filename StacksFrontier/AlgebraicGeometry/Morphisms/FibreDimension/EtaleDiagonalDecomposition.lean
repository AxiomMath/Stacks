module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleUniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleDiagonalComplement

/-!
# The off-diagonal part of `X ×_Y X` for a separated étale morphism, and the drop in fibre degree

The third paragraph of Stacks 03XW runs an induction on an integer bounding the degrees of the
fibres of an étale morphism `t : T' ⟶ T` of affine schemes, and the mechanism of its inductive
step is this: the scheme `T' ×_T T'` decomposes into open and closed affine subschemes
`Δ(T') ⨿ T^*`, the first projection restricted to `Δ(T')` is an isomorphism and so has fibres
with exactly one point, and therefore the first projection restricted to `T^*` has fibre degrees
bounded by one less than the bound for `T' ×_T T' ⟶ T'`.

This file isolates that mechanism for an arbitrary étale separated morphism of schemes. The
decomposition is the clopen splitting of `X ×_Y X` along the range of the relative diagonal: the
range is open because `f` is étale, hence formally unramified and locally of finite type, which
is Tag 02GE and is Mathlib's `AlgebraicGeometry.isOpenImmersion_diagonal`; and it is closed
because `f` is separated. `AlgebraicGeometry.offDiagonal` is the complementary piece, as an
open subscheme.

The degree drop is proved through the cardinality form of the bound rather than through ranks of
fibres, which is what Tag 03WU is for: `AlgebraicGeometry.etale_boundsFiberDegrees_tfae` turns a
bound on the degrees of the fibres of an étale morphism into a bound on the number of points of
every field-valued base change, and back. In that form the argument is a counting argument: a
field-valued point of `X` lifts along the diagonal to one point of the fibre of
`X ×_Y X ⟶ X` which is *not* in the off-diagonal part, while the fibre of the off-diagonal part
injects into that fibre, so its cardinality is at most one less.

## Main definitions

* `AlgebraicGeometry.offDiagonal`: for a separated morphism `f : X ⟶ Y` of schemes, the open
  subscheme of `X ×_Y X` complementary to the range of the relative diagonal. This is `T^*` of
  Stacks 03XW. **This is a new definition.**

## Main results

* `AlgebraicGeometry.isClopen_range_diagonal`: for an étale separated morphism the range of the
  relative diagonal is open and closed.
* `AlgebraicGeometry.disjoint_offDiagonal_range_diagonal` and
  `AlgebraicGeometry.union_range_diagonal_offDiagonal`: the two pieces are disjoint and cover.
* `AlgebraicGeometry.isClosed_offDiagonal` and `AlgebraicGeometry.isAffine_offDiagonal`: the
  off-diagonal part is closed, and is affine when the source and target are. Its first projection
  to the source is étale by instance search.
* `AlgebraicGeometry.boundsFiberDegrees_offDiagonal_fst`: **the degree drop.** If `n + 1` bounds
  the degrees of the fibres of an étale separated `f`, then `n` bounds the degrees of the fibres
  of the first projection `offDiagonal f ⟶ X`.

## Implementation notes

Nothing here carries a tag. The decomposition and the degree drop are two sentences of the third
paragraph of the proof of Stacks 03XW, not statements of a tag of their own; the inputs they use
are Tag 02GE, Tag 03J7 (`AlgebraicGeometry.boundsFiberDegrees_isStableUnderBaseChange`) and
Tag 03WU (`AlgebraicGeometry.etale_boundsFiberDegrees_tfae`).

Tag 02GE arrives through Mathlib: openness of the diagonal of an étale morphism is Mathlib's
instance `AlgebraicGeometry.isOpenImmersion_diagonal` for a formally unramified morphism locally
of finite type, which is what the tag-carrying
`AlgebraicGeometry.Unramified.isOpenImmersion_diagonal` of
`StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Diagonal` itself delegates to, so that module
is not imported here.

`AlgebraicGeometry.offDiagonal` needs only separatedness of `f`, since all that the open set
asks for is that the range of the diagonal be closed; étaleness enters in the statements about
it.

The counting step is carried out on the chosen fibre product `X ×_Y X` and then transported: the
fibre of the off-diagonal part over a field-valued point `g` is presented as
`(X ×_Y X) ×_X Spec k` intersected with the off-diagonal part, which is the composite of two
chosen fibre products, and the comparison with `pullback g (offDiagonal f).ι ≫ pullback.fst f f`
is the isomorphism of two pullbacks of one cospan.

## References

* [Stacks Project, Tag 03XW](https://stacks.math.columbia.edu/tag/03XW)
* [Stacks Project, Tag 02GE](https://stacks.math.columbia.edu/tag/02GE)
* [Stacks Project, Tag 03J7](https://stacks.math.columbia.edu/tag/03J7)
* [Stacks Project, Tag 03WU](https://stacks.math.columbia.edu/tag/03WU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### The clopen decomposition of `X ×_Y X` -/

/-- **The off-diagonal part of `X ×_Y X`.** For a separated morphism `f : X ⟶ Y` of schemes this
is the open subscheme of `X ×_Y X` whose points are those not in the range of the relative
diagonal; it is `T^*` in the decomposition `T' ×_T T' = Δ(T') ⨿ T^*` of Stacks 03XW.

Only separatedness is required, because all the open set asks for is that the range of the
diagonal be closed. -/
def offDiagonal [IsSeparated f] : (pullback f f).Opens :=
  ⟨(Set.range (pullback.diagonal f).base)ᶜ,
    (pullback.diagonal f).isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The points of `AlgebraicGeometry.offDiagonal` are exactly those outside the range of the
relative diagonal. -/
theorem coe_offDiagonal [IsSeparated f] :
    (offDiagonal f : Set (pullback f f : Scheme.{u})) =
      (Set.range (pullback.diagonal f).base)ᶜ :=
  rfl

/-- The off-diagonal part is disjoint from the range of the relative diagonal. -/
theorem disjoint_offDiagonal_range_diagonal [IsSeparated f] :
    Disjoint (offDiagonal f : Set (pullback f f : Scheme.{u}))
      (Set.range (pullback.diagonal f).base) := by
  rw [coe_offDiagonal]
  exact disjoint_compl_left

/-- The range of the relative diagonal together with the off-diagonal part covers `X ×_Y X`. -/
theorem union_range_diagonal_offDiagonal [IsSeparated f] :
    Set.range (pullback.diagonal f).base ∪ (offDiagonal f : Set (pullback f f : Scheme.{u})) =
      Set.univ := by
  rw [coe_offDiagonal, Set.union_compl_self]

/-- For an étale separated morphism the off-diagonal part is closed as well as open, being the
complement of the open range of the relative diagonal. -/
theorem isClosed_offDiagonal [Etale f] [IsSeparated f] :
    IsClosed (offDiagonal f : Set (pullback f f : Scheme.{u})) := by
  rw [coe_offDiagonal, isClosed_compl_iff]
  exact (isClopen_range_diagonal f).isOpen

/-- The off-diagonal part of `X ×_Y X` is affine when `X` and `Y` are: it is a closed subscheme
of the affine scheme `X ×_Y X`, being an open subscheme whose point set is closed, and a closed
immersion is affine. -/
theorem isAffine_offDiagonal [Etale f] [IsAffine X] [IsAffine Y] :
    IsAffine (offDiagonal f).toScheme := by
  have hci : IsClosedImmersion (offDiagonal f).ι :=
    IsClosedImmersion.of_isPreimmersion (offDiagonal f).ι
      (by simpa using isClosed_offDiagonal f)
  exact isAffine_of_isAffineHom (offDiagonal f).ι

/-! ### The drop in fibre degree -/

/-- The counting step behind the degree drop: for an étale morphism `f : X ⟶ Y`, an open subset
`V` of `X ×_Y X` disjoint from the range of the relative diagonal and a field-valued point `g`
of `X`, the fibre of `V ⟶ X` over `g` has at least one point fewer than the fibre of
`X ×_Y X ⟶ X` over `g`.

The point which is in the second fibre and not in the first is the one the diagonal provides:
`g` composed with the relative diagonal is a section of the fibre over `g`, and its image lies
in the range of the diagonal, which `V` avoids. The first fibre injects into the second because
it is its intersection with `V`, cut out by the open immersion `V.ι`. -/
private theorem cardinalMk_pullback_succ_le_of_disjoint_range_diagonal [Etale f]
    (V : (pullback f f).Opens)
    (hV : Disjoint (V : Set (pullback f f : Scheme.{u}))
      (Set.range (pullback.diagonal f).base))
    (n : ℕ) (k : Type u) [Field k] (g : Spec (.of k) ⟶ X)
    (hn : Cardinal.mk (pullback g (pullback.fst f f) : Scheme.{u}) ≤
      ((n + 1 : ℕ) : Cardinal.{u})) :
    Cardinal.mk (pullback g (V.ι ≫ pullback.fst f f) : Scheme.{u}) ≤ (n : Cardinal.{u}) := by
  classical
  set π := pullback.fst f f with hπ
  set b := pullback.snd g π with hb
  set j := pullback.fst b V.ι with hj
  -- the fibre of `V` over `g` is the fibre of `X ×_Y X` over `g` intersected with `V`
  have sq1 : IsPullback (pullback.fst g π) b g π := IsPullback.of_hasPullback _ _
  have sq2 : IsPullback j (pullback.snd b V.ι) b V.ι := IsPullback.of_hasPullback _ _
  have e : (pullback b V.ι : Scheme.{u}) ≅ pullback g (V.ι ≫ π) :=
    (sq2.paste_horiz sq1).isoIsPullback _ _ (IsPullback.of_hasPullback g (V.ι ≫ π))
  have hcard : Cardinal.mk (pullback g (V.ι ≫ π) : Scheme.{u}) =
      Cardinal.mk (pullback b V.ι : Scheme.{u}) :=
    (Cardinal.mk_congr e.hom.homeomorph.toEquiv).symm
  rw [hcard]
  -- evaluating a commuting triangle on points
  have hpt : ∀ {A B C : Scheme.{u}} {p : A ⟶ B} {q : B ⟶ C} {r : A ⟶ C}, p ≫ q = r →
      ∀ x, q.base (p.base x) = r.base x := fun h x => by rw [← h]; rfl
  -- the fibre of `V` lands in `V`
  have hjmem : ∀ y : (pullback b V.ι : Scheme.{u}),
      b.base (j.base y) ∈ (V : Set (pullback f f : Scheme.{u})) := fun y => by
    rw [← Scheme.Opens.range_ι V, hpt pullback.condition y]
    exact ⟨_, rfl⟩
  -- the diagonal provides a point of the fibre of `X ×_Y X` outside `V`
  have hcomm : (𝟙 (Spec (.of k))) ≫ g = (g ≫ pullback.diagonal f) ≫ π := by
    rw [Category.id_comp, Category.assoc, hπ, pullback.diagonal_fst, Category.comp_id]
  set s := pullback.lift (𝟙 (Spec (.of k))) (g ≫ pullback.diagonal f) hcomm with hs
  obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
  have hsmem : b.base (s.base x) ∈ Set.range (pullback.diagonal f).base := by
    exact ⟨g.base x, (hpt (pullback.lift_snd _ _ hcomm) x).symm⟩
  -- so the fibre of `V` plus one point injects into the fibre of `X ×_Y X`
  have hjoi : IsOpenImmersion j := by rw [hj]; infer_instance
  have hjinj : Function.Injective j.base := j.isOpenEmbedding.injective
  have hinj : Function.Injective
      (fun o : Option (pullback b V.ι : Scheme.{u}) => o.elim (s.base x) j.base) := by
    have hout : ∀ y : (pullback b V.ι : Scheme.{u}), s.base x ≠ j.base y := by
      intro y hy
      have hmem : b.base (s.base x) ∈ (V : Set (pullback f f : Scheme.{u})) := by
        rw [hy]; exact hjmem y
      exact absurd hmem (Set.disjoint_right.mp hV hsmem)
    rintro (_ | y₁) (_ | y₂) h <;> simp only [Option.elim] at h
    · rfl
    · exact absurd h (hout y₂)
    · exact absurd h.symm (hout y₁)
    · exact congrArg some (hjinj h)
  have hle : Cardinal.mk (Option (pullback b V.ι : Scheme.{u})) ≤
      Cardinal.mk (pullback g π : Scheme.{u}) := Cardinal.mk_le_of_injective hinj
  rw [Cardinal.mk_option] at hle
  -- and a finite cardinal with `m + 1 ≤ n + 1` is at most `n`
  have hn' : Cardinal.mk (pullback g π : Scheme.{u}) ≤ (n : Cardinal.{u}) + 1 := by
    push_cast at hn; exact hn
  have hfin : Cardinal.mk (pullback b V.ι : Scheme.{u}) < Cardinal.aleph0.{u} :=
    lt_of_le_of_lt (le_trans (self_le_add_right _ 1) (hle.trans hn'))
      (by exact_mod_cast Cardinal.natCast_lt_aleph0 (n := n + 1))
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp hfin
  rw [hm] at hle ⊢
  have hmn : ((m + 1 : ℕ) : Cardinal.{u}) ≤ ((n + 1 : ℕ) : Cardinal.{u}) := by
    push_cast
    exact hle.trans hn'
  exact_mod_cast Nat.succ_le_succ_iff.mp (by exact_mod_cast hmn)

/-- **The degree drop of the induction of Stacks 03XW.** If `n + 1` bounds the degrees of the
fibres of an étale separated morphism `f : X ⟶ Y` of schemes, then `n` bounds the degrees of the
fibres of the first projection `offDiagonal f ⟶ X` of its off-diagonal part.

Both bounds are read through the cardinality criterion of Tag 03WU: the bound for `f` passes to
the first projection `X ×_Y X ⟶ X` by base change (Tag 03J7), the counting step
subtracts the point contributed by the diagonal, and the criterion is applied backwards to the
first projection of the off-diagonal part, which is étale. -/
theorem boundsFiberDegrees_offDiagonal_fst [Etale f] [IsSeparated f] (n : ℕ)
    (h : BoundsFiberDegrees f ((n + 1 : ℕ) : ℤ)) :
    BoundsFiberDegrees ((offDiagonal f).ι ≫ pullback.fst f f) ((n : ℕ) : ℤ) := by
  have hetale : Etale ((offDiagonal f).ι ≫ pullback.fst f f) := inferInstance
  have hπ : BoundsFiberDegrees (pullback.fst f f) ((n + 1 : ℕ) : ℤ) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {_ _ : Scheme.{u}} (p : _ ⟶ _) ↦ BoundsFiberDegrees p ((n + 1 : ℕ) : ℤ))
      (IsPullback.of_hasPullback f f).flip h
  have hcard := ((etale_boundsFiberDegrees_tfae (pullback.fst f f) (n + 1)).out 1 2).mp hπ
  refine ((etale_boundsFiberDegrees_tfae ((offDiagonal f).ι ≫ pullback.fst f f) n).out 2 1).mp ?_
  intro k hk g
  exact cardinalMk_pullback_succ_le_of_disjoint_range_diagonal f (offDiagonal f)
    (disjoint_offDiagonal_range_diagonal f) n k g (hcard k g)

end AlgebraicGeometry

end
