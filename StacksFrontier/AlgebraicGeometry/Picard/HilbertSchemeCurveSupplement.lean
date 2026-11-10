module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeOpenChart
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorSeparated
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Basic
public import StacksFrontier.AlgebraicGeometry.HilbertFibreAffineOpen.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurve
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Hilbert schemes of points of a curve

Let `X` be a geometrically irreducible smooth proper curve over a field `k` in which every finite
set of points lies in an affine open (for instance, `X` projective). For every `d` the degree-`d`
Hilbert functor of points of `X` is represented by a scheme `H_d` over `k` which is smooth of
dimension `d`, proper and irreducible. This is part (1) of [Stacks, Tag 0B9I], proved as in the
source: representability is Tag 0B9A, separatedness Tag 0B98, smoothness Tag 0B9H, and properness
and irreducibility come from the surjection `X^d ⟶ H_d` built from the point-addition morphisms
of Tag 0B9G, by Tags 03GN and 038F.

## Main results

* `Stacks.Hilbert.Curve.exists_hilbertScheme` (the degree-zero scheme is the base by
  `Stacks.Hilbert.isIso_hom_of_representsHilbertFunctorOfRank_zero`)

## References

* [Stacks Project, Tag 0B9I](https://stacks.math.columbia.edu/tag/0B9I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Hilbert.Curve

/-- A finite locally free morphism of positive rank is surjective. -/
theorem surjective_of_isFiniteLocallyFreeOfRank_succ {X Y : Scheme.{u}} (f : X ⟶ Y) {d : ℕ}
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f (d + 1)] : Surjective f := by
  have h := (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    f).mp (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f (d + 1))
  have : IsFinite f := h.1
  have : Flat f := h.2.1
  refine f.one_le_finrank_iff_surjective.mp fun y ↦ ?_
  have hfr : Scheme.Hom.finrank f y = d + 1 :=
    (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq f (d + 1)).mp
      inferInstance y
  change 1 ≤ Scheme.Hom.finrank f y
  omega

variable {S : Scheme.{u}}

variable (X : Over S) [SmoothOfRelativeDimension 1 X.hom] [IsSeparated X.hom]
  (hX : HasAffineFinitePointsInFibres X.hom)

omit [SmoothOfRelativeDimension 1 X.hom] in
include hX in
/-- The Hilbert functors of points of a separated relative curve with the fibrewise affineness
property are representable (Tag 0B9A). -/
theorem exists_represents (d : ℕ) : Nonempty (Σ H : Over S, RepresentsHilbertFunctorOfRank X H d) :=
  exists_representsHilbertFunctorOfRank_of_isSeparated X d fun s x hx ↦
    Stacks.HilbertFibreAffineOpen.exists_isAffineOpen_forall_mem_of_hasAffineFinitePointsInFibres
      hX d s x hx

/-- A chosen degree-`d` Hilbert scheme. -/
def scheme (d : ℕ) : Over S := (exists_represents X hX d).some.1

/-- Its universal property. -/
def represents (d : ℕ) : RepresentsHilbertFunctorOfRank X (scheme X hX d) d :=
  (exists_represents X hX d).some.2

/-- The degree-`d` Hilbert scheme `scheme X hX d` is smooth of relative dimension `d` over `S`. -/
theorem smoothOfRelativeDimension_scheme (d : ℕ) :
    SmoothOfRelativeDimension d (scheme X hX d).hom :=
  smoothOfRelativeDimension_of_represents (scheme X hX) (represents X hX) d

omit [SmoothOfRelativeDimension 1 X.hom] in
/-- The degree-`d` Hilbert scheme `scheme X hX d` is separated over `S`. -/
theorem isSeparated_scheme (d : ℕ) : IsSeparated (scheme X hX d).hom :=
  isSeparated_of_representsHilbertFunctorOfRank X (scheme X hX d) d (represents X hX d)

/-- The point-addition morphism `H_d ×_S X ⟶ H_{d+1}` (Tag 0B9G). -/
def add (d : ℕ) : scheme X hX d ⨯ X ⟶ scheme X hX (d + 1) :=
  addPoint (represents X hX d) (represents X hX (d + 1))

/-- The point-addition morphism `add X hX d` is finite locally free of rank `d + 1`. -/
instance isFiniteLocallyFreeOfRank_add_left (d : ℕ) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (add X hX d).left (d + 1) :=
  IsPointAddition.isFiniteLocallyFreeOfRank_left
    (isPointAddition_addPoint (represents X hX d) (represents X hX (d + 1)))

/-- The point-addition morphism `add X hX d` is surjective. -/
instance surjective_add_left (d : ℕ) : Surjective (add X hX d).left :=
  surjective_of_isFiniteLocallyFreeOfRank_succ (d := d) _

omit [SmoothOfRelativeDimension 1 X.hom] in
/-- The structure morphism of `scheme X hX d ⨯ X` over `S` is the composite of the isomorphism
onto the fibre product over `S`, the first projection, and the structure morphism of
`scheme X hX d`. -/
theorem prod_hom_eq (d : ℕ) : (scheme X hX d ⨯ X).hom =
    (Over.prodLeftIsoPullback (scheme X hX d) X).hom ≫ pullback.fst _ _ ≫ (scheme X hX d).hom := by
  rw [← Category.assoc, Over.prodLeftIsoPullback_hom_fst, Over.w]

/-- **The Hilbert schemes of points of a proper curve are proper.** -/
theorem isProper_scheme [IsProper X.hom] (d : ℕ) : IsProper (scheme X hX d).hom := by
  induction d with
  | zero =>
    have := isIso_hom_of_representsHilbertFunctorOfRank_zero (represents X hX 0)
    infer_instance
  | succ d ih =>
    have : IsProper (scheme X hX d ⨯ X).hom := by
      rw [prod_hom_eq]
      infer_instance
    have := isSeparated_scheme X hX (d + 1)
    have := (smoothOfRelativeDimension_scheme X hX (d + 1)).smooth
    exact isProper_of_isProper_of_surjective (add X hX d).left (scheme X hX (d + 1)).hom
      (scheme X hX d ⨯ X).hom (Over.w (add X hX d))

/-- The target of a surjective morphism from an irreducible scheme is irreducible. -/
private theorem irreducibleSpace_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    [IrreducibleSpace X] : IrreducibleSpace Y :=
  Function.Surjective.irreducibleSpace f.continuous f.surjective

/-- **The Hilbert schemes of points of a geometrically irreducible curve over a field are
irreducible.** -/
theorem irreducibleSpace_scheme {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 X.hom] [IsSeparated X.hom] [GeometricallyIrreducible X.hom]
    (hX : HasAffineFinitePointsInFibres X.hom) (d : ℕ) : IrreducibleSpace (scheme X hX d).left := by
  induction d with
  | zero =>
    have := isIso_hom_of_representsHilbertFunctorOfRank_zero (represents X hX 0)
    exact irreducibleSpace_of_surjective (inv (scheme X hX 0).hom)
  | succ d ih =>
    have := (SmoothOfRelativeDimension.smooth 1 X.hom)
    have : IrreducibleSpace ↥(Limits.pullback (scheme X hX d).hom X.hom) := inferInstance
    have : IrreducibleSpace (scheme X hX d ⨯ X).left :=
      irreducibleSpace_of_surjective (Over.prodLeftIsoPullback (scheme X hX d) X).inv
    exact irreducibleSpace_of_surjective (add X hX d).left

/-- **The Hilbert schemes of points of a curve are smooth proper varieties of dimension `d`**
(part (1) of Tag 0B9I) for a geometrically irreducible smooth proper curve over a field in which
every finite set of points lies in an affine open, which holds when the curve is projective
(Remark 0B9B). The source deduces that last property from projectivity of proper curves,
Tag 0A26. -/
@[sga "4 XVII 6.3.8" "special case"]
theorem exists_hilbertScheme {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] [GeometricallyIrreducible X.hom]
    (hX : HasAffineFinitePointsInFibres X.hom) (d : ℕ) :
    ∃ H : Over (Spec (.of k)), Nonempty (RepresentsHilbertFunctorOfRank X H d) ∧
      SmoothOfRelativeDimension d H.hom ∧ IsProper H.hom ∧ IsIntegral H.left := by
  refine ⟨scheme X hX d, ⟨represents X hX d⟩, smoothOfRelativeDimension_scheme X hX d,
    isProper_scheme X hX d, ?_⟩
  have := irreducibleSpace_scheme X hX d
  have := (smoothOfRelativeDimension_scheme X hX d).smooth
  have : IsReduced (scheme X hX d).left := isReduced_of_smooth (scheme X hX d).hom
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end Stacks.Hilbert.Curve

end
