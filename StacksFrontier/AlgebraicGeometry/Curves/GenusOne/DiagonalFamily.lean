module

public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassEquationNoetherian

/-!
# A curve of genus one as an elliptic curve over itself

Let `X` be a proper scheme over a field `k`, smooth of relative dimension one, with
`dim_k H⁰(X, 𝒪_X) = 1` and genus one. Every `k`-rational point `q` of `X` makes `(X, q)` an
elliptic curve over `Spec k`, and the second projection `X ×_k X ⟶ X`, pointed by the diagonal,
is an elliptic curve over `X` whose fibre at a rational point `q` is `(X, q)`. This *diagonal
family* is the tautological family of all the pointed curves `(X, q)`; comparing it with the
constant family `(X, p)` over the moduli stack of elliptic curves is how the automorphisms of `X`
are described.

## Main definitions

* `AlgebraicGeometry.GenusOne.pointedFamily`: the curve `X` pointed by a section, as a family
  over `Spec k`.
* `AlgebraicGeometry.GenusOne.diagonalFamily`: the second projection `X ×_k X ⟶ X`, pointed by
  the diagonal.
* `AlgebraicGeometry.GenusOne.diagonalFamilyPullbackIso`: the restriction of the diagonal family
  along a morphism `a : T ⟶ X` is the base change `X ×_k T`, pointed by `(a, 𝟙)`.
* `AlgebraicGeometry.GenusOne.diagonalFamilyPointIso`: the restriction of the diagonal family
  along a rational point `q` is `(X, q)`.

## Main results

* `AlgebraicGeometry.GenusOne.isGenusOneAt_pointedFamily`,
  `AlgebraicGeometry.GenusOne.isElliptic_pointedFamily`: `(X, q)` is an elliptic curve over
  `Spec k`.
* `AlgebraicGeometry.GenusOne.isElliptic_diagonalFamily`: the diagonal family is an elliptic curve
  over `X`.

## Implementation notes

The genus-one conditions on the fibres are transported along base change by
`AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.isGenusOneAt_iff_of_isPullback`: the
diagonal family is the base change of `X ⟶ Spec k` along `X ⟶ Spec k`, and the fibre of
`X ⟶ Spec k` at the point of `Spec k` is the base change of `X` along the extension of `k` to the
residue field of that point, where `H⁰` and `H¹` are unchanged
(`AlgebraicGeometry.finrank_structureSheafCohomology_baseChange`,
`AlgebraicGeometry.genus_baseChange`).

## References

* [Stacks Project, Tag 072J](https://stacks.math.columbia.edu/tag/072J)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.GenusOne

open ModuliEllipticCurves

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The curve `X` pointed by a section `q` of `f`, as a pointed family over `Spec k`. -/
abbrev pointedFamily (q : Spec (.of k) ⟶ X) (hq : q ≫ f = 𝟙 _) : PointedFamily (Spec (.of k)) where
  total := X
  map := f
  zero := q
  zero_map := hq

/-- The **diagonal family**: the second projection `X ×_k X ⟶ X`, pointed by the diagonal. Its
fibre over a rational point `q` of `X` is `X` pointed by `q`. -/
abbrev diagonalFamily : PointedFamily X where
  total := pullback f f
  map := pullback.snd f f
  zero := pullback.lift (𝟙 X) (𝟙 X) rfl
  zero_map := pullback.lift_snd _ _ _

/-- The restriction of the diagonal family along `a : T ⟶ X` is the base change `X ×_k T` along
`t = a ≫ f`, with the section `(a, 𝟙)`: the underlying isomorphism of total spaces. -/
def diagonalFamilyPullbackIso {T : Scheme.{u}} (a : T ⟶ X) (t : T ⟶ Spec (.of k))
    (ha : a ≫ f = t) : pullback (pullback.snd f f) a ≅ pullback f t where
  hom := pullback.lift (pullback.fst _ _ ≫ pullback.fst f f) (pullback.snd _ a) (by
    rw [Category.assoc, pullback.condition (f := f) (g := f), ← Category.assoc,
      pullback.condition (f := pullback.snd f f) (g := a), Category.assoc, ha])
  inv := pullback.lift (pullback.lift (pullback.fst f t) (pullback.snd f t ≫ a) (by
      rw [Category.assoc, ha, pullback.condition])) (pullback.snd f t) (by simp)
  hom_inv_id := by
    refine pullback.hom_ext (f := pullback.snd f f) (g := a) ?_ ?_
    · refine pullback.hom_ext (f := f) (g := f) ?_ ?_
      · simp
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
        rw [pullback.lift_snd_assoc]
        exact (pullback.condition (f := pullback.snd f f) (g := a)).symm
    · simp
  inv_hom_id := by refine pullback.hom_ext (f := f) (g := t) ?_ ?_ <;> simp

/-- The isomorphism `diagonalFamilyPullbackIso` commutes with the projections to `T`. -/
@[reassoc (attr := simp)]
theorem diagonalFamilyPullbackIso_hom_snd {T : Scheme.{u}} (a : T ⟶ X) (t : T ⟶ Spec (.of k))
    (ha : a ≫ f = t) :
    (diagonalFamilyPullbackIso f a t ha).hom ≫ pullback.snd f t = pullback.snd _ a := by
  simp [diagonalFamilyPullbackIso]

/-- Followed by the projection to `X`, the isomorphism `diagonalFamilyPullbackIso` is the first
projection of `X ×_k X`. -/
@[reassoc (attr := simp)]
theorem diagonalFamilyPullbackIso_hom_fst {T : Scheme.{u}} (a : T ⟶ X) (t : T ⟶ Spec (.of k))
    (ha : a ≫ f = t) :
    (diagonalFamilyPullbackIso f a t ha).hom ≫ pullback.fst f t =
      pullback.fst _ _ ≫ pullback.fst f f := by
  simp [diagonalFamilyPullbackIso]

/-- The inverse of `diagonalFamilyPullbackIso` commutes with the projections to `T`. -/
@[reassoc (attr := simp)]
theorem diagonalFamilyPullbackIso_inv_snd {T : Scheme.{u}} (a : T ⟶ X) (t : T ⟶ Spec (.of k))
    (ha : a ≫ f = t) :
    (diagonalFamilyPullbackIso f a t ha).inv ≫ pullback.snd _ a = pullback.snd f t := by
  simp [diagonalFamilyPullbackIso]

/-- The inverse of `diagonalFamilyPullbackIso`, followed by the first projection of `X ×_k X`, is
the projection of `X ×_k T` to `X`. -/
@[reassoc (attr := simp)]
theorem diagonalFamilyPullbackIso_inv_fst_fst {T : Scheme.{u}} (a : T ⟶ X)
    (t : T ⟶ Spec (.of k)) (ha : a ≫ f = t) :
    (diagonalFamilyPullbackIso f a t ha).inv ≫ pullback.fst _ a ≫ pullback.fst f f =
      pullback.fst f t := by
  simp [diagonalFamilyPullbackIso]

/-- The section of the restricted diagonal family is `(a, 𝟙)`. -/
@[reassoc (attr := simp)]
theorem zero_diagonalFamilyPullbackIso_hom {T : Scheme.{u}} (a : T ⟶ X) (t : T ⟶ Spec (.of k))
    (ha : a ≫ f = t) :
    ((diagonalFamily f).pullback a).zero ≫ (diagonalFamilyPullbackIso f a t ha).hom =
      pullback.lift a (𝟙 T) (by rw [ha, Category.id_comp]) := by
  refine pullback.hom_ext (f := f) (g := t) ?_ ?_ <;> simp [diagonalFamilyPullbackIso]

/-- **The fibre of the diagonal family at a rational point `q` is `(X, q)`.** -/
def diagonalFamilyPointIso (q : Spec (.of k) ⟶ X) (hq : q ≫ f = 𝟙 _) :
    FamilyIso ((diagonalFamily f).pullback q) (pointedFamily f q hq) where
  iso :=
    { hom := pullback.fst _ q ≫ pullback.fst f f
      inv := pullback.lift (pullback.lift (𝟙 X) (f ≫ q) (by
          rw [Category.id_comp, Category.assoc, hq, Category.comp_id])) f (by simp)
      hom_inv_id := by
        refine pullback.hom_ext (f := pullback.snd f f) (g := q) ?_ ?_
        · refine pullback.hom_ext (f := f) (g := f) ?_ ?_
          · simp
          · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
            rw [pullback.condition_assoc (f := f) (g := f), ← Category.assoc,
              pullback.condition (f := pullback.snd f f) (g := q), Category.assoc,
              reassoc_of% hq]
        · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
          rw [pullback.condition (f := f) (g := f), ← Category.assoc,
            pullback.condition (f := pullback.snd f f) (g := q), Category.assoc, hq,
            Category.comp_id]
      inv_hom_id := by simp }
  iso_map := by
    change (pullback.fst _ q ≫ pullback.fst f f) ≫ f = pullback.snd _ q
    rw [Category.assoc, pullback.condition (f := f) (g := f), ← Category.assoc,
      pullback.condition (f := pullback.snd f f) (g := q), Category.assoc, hq, Category.comp_id]
  zero_iso := by
    change pullback.lift (q ≫ pullback.lift (𝟙 X) (𝟙 X) rfl) (𝟙 _) _ ≫
      pullback.fst _ q ≫ pullback.fst f f = q
    simp

/-! ### The genus-one conditions -/

variable [IsProper f] (h0 : Module.finrank k (structureSheafCohomology f 0) = 1)
  (hg : genus f = 1)
include h0 hg

/-- The fibre of `X ⟶ Spec k` at the point of `Spec k` is a curve of genus one with
one-dimensional `H⁰`. -/
theorem isGenusOneAt_pointedFamily (q : Spec (.of k) ⟶ X) (hq : q ≫ f = 𝟙 _)
    (s : Spec (.of k)) : (pointedFamily f q hq).IsGenusOneAt s := by
  have hs : s = (show Spec (.of k) from ⟨⊥, Ideal.isPrime_bot⟩) := Subsingleton.elim _ _
  subst hs
  rw [PointedFamily.isGenusOneAt_iff_residueField]
  have hpb := IsPullback.of_hasPullback f
    (Spec.map (CommRingCat.ofHom (algebraMap k (⊥ : Ideal k).ResidueField)))
  refine ⟨?_, ?_⟩
  · rw [← h0]
    exact finrank_structureSheafCohomology_baseChange k _ _ _ f hpb 0
  · rw [← hg]
    exact genus_baseChange k _ _ _ f hpb

/-- **`(X, q)` is an elliptic curve over `Spec k`.** -/
theorem isElliptic_pointedFamily [SmoothOfRelativeDimension 1 f] (q : Spec (.of k) ⟶ X)
    (hq : q ≫ f = 𝟙 _) : (pointedFamily f q hq).IsElliptic :=
  ⟨inferInstanceAs (IsProper f), inferInstanceAs (SmoothOfRelativeDimension 1 f),
    isGenusOneAt_pointedFamily f h0 hg q hq⟩

/-- **The diagonal family is an elliptic curve over `X`.** It is the base change of
`X ⟶ Spec k` along `X ⟶ Spec k`. -/
theorem isElliptic_diagonalFamily [SmoothOfRelativeDimension 1 f] (q : Spec (.of k) ⟶ X)
    (hq : q ≫ f = 𝟙 _) : (diagonalFamily f).IsElliptic := by
  refine ⟨inferInstanceAs (IsProper (pullback.snd f f)),
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
      (IsPullback.of_hasPullback f f) ‹_›, fun s ↦ ?_⟩
  have : IsProper (pointedFamily f q hq).map := inferInstanceAs (IsProper f)
  exact (PointedFamily.isGenusOneAt_iff_of_isPullback (E := diagonalFamily f)
    (E₀ := pointedFamily f q hq) f (pullback.fst f f) (IsPullback.of_hasPullback f f) s).2
    (isGenusOneAt_pointedFamily f h0 hg q hq _)

end AlgebraicGeometry.GenusOne
