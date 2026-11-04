module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ClosedPointsFibre.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ClosedPointsInFibres
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Locus
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField

/-!
# Dense closed points in a fibre over a locally Noetherian base

Let `f : X ⟶ S` be locally of finite type with `S` locally Noetherian, let `x ⤳ x'` in `X` with
`x'` closed in its fibre, and assume the two points lie over different points of `S`. Then the
points of the fibre `X_{f x}` which are closed in that fibre and lie between `x` and `x'` are
dense in the closure of `x` in `X_{f x}`. This is the conclusion of Stacks 053U for a locally
Noetherian base, proved along the route sketched in Stacks 05GV: induct on the codimension of
`f x'` in `S`, and produce the intermediate closed point from Stacks 05GU applied to the reduced
induced structure on the closure of `x`, inside which `x` is the generic point.

In one step of the induction Stacks 05GU produces a closed subscheme `Z` of that closure through
`x'` which is quasi-finite over `S` at `x'`, together with a point `z` of `Z` in a prescribed
open with `f z ≠ f x'`. Quasi-finiteness holds on an open set (Stacks 01TI), hence at `z`, so `z`
is isolated and therefore closed in the fibre of `Z`; a closed immersion carries a point closed
in a fibre to a point closed in a fibre, so `z` is closed in `X_{f z}`. If `z` lies in the fibre
of `x` it is the point asked for, and otherwise `f z` has smaller codimension than `f x'`, so the
induction hypothesis applies to the pair `x ⤳ z`.

## Main results

* `AlgebraicGeometry.closure_closedPoints_between_fiber_eq_of_isLocallyNoetherian`: **Stacks 053U
  for a locally Noetherian base**, by the route of Stacks 05GV.
* `AlgebraicGeometry.isClosed_asFiber_comp` and `AlgebraicGeometry.isClosed_asFiber_of_comp`: the
  two halves of the statement that a point of a subscheme is closed in its fibre over `S` exactly
  when its image is.

## Implementation notes

The hypothesis `f x ≠ f x'` (or `x = x'`) is the exact range of validity of the density
conclusion of Stacks 053U, by
`AlgebraicGeometry.closure_closedPoints_between_fiber_eq_iff`
(`StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ClosedPointsBetweenInFibres`): outside it `x'`
lies in the fibre of `x`, a point of `X_{f x}` closed in `X_{f x}` which specializes to `x'`
*is* `x'`, so the set of the tag is a subsingleton and is not dense in the closure of `x` unless
that closure is a point. The source states its conclusion with no hypothesis relating `f x` and
`f x'`; the computation behind the restriction is
`AlgebraicGeometry.closure_closedPoints_between_fiber_subset_singleton_of_eq_base`
(`StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ClosedPointsInFibres`).
The disjunct `x = x'` is the degenerate case and is already
`closure_closedPoints_between_fiber_eq_of_isClosed`.

The induction runs on a natural number bounding `Order.coheight (f x')`, which is finite because
it is the Krull dimension of the local ring of `S` at `f x'` and that ring is Noetherian local.
This replaces the source's replacement of `S` by the spectrum of that local ring, and makes the
base case vacuous rather than trivial: a point of codimension zero admits no proper
generalization, so no pair with `f x ≠ f x'` lies over it.

## References

* [Stacks Project, Tag 05GV](https://stacks.math.columbia.edu/tag/05GV)
* [Stacks Project, Tag 053U](https://stacks.math.columbia.edu/tag/053U)
* [Stacks Project, Tag 05GU](https://stacks.math.columbia.edu/tag/05GU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A point of the fibre of `j ≫ f` through `y` has image in `X` lying over the image of `y`. -/
private lemma fiber_comp_base {Y X S : Scheme.{u}} (j : Y ⟶ X) (f : X ⟶ S) (y : Y)
    (w : (j ≫ f).fiber ((j ≫ f) y)) :
    f (j ((j ≫ f).fiberι ((j ≫ f) y) w)) = f (j y) := by
  have hfac := congrArg (fun m : (j ≫ f).fiber ((j ≫ f) y) ⟶ S => m w)
    ((j ≫ f).fiber_fac ((j ≫ f) y))
  change f (j ((j ≫ f).fiberι ((j ≫ f) y) w)) =
    S.fromSpecResidueField ((j ≫ f) y)
      ((j ≫ f).fiberToSpecResidueField ((j ≫ f) y) w) at hfac
  rwa [Scheme.fromSpecResidueField_apply] at hfac

/-- A point of the source of a preimmersion is closed in its fibre over `S` as soon as its image
is: the fibre of the composite maps injectively and continuously to the fibre of `f`, matching
the two points. -/
public theorem isClosed_asFiber_comp {Y X S : Scheme.{u}} (j : Y ⟶ X) [IsPreimmersion j]
    (f : X ⟶ S) (y : Y) (h : IsClosed ({f.asFiber (j y)} : Set (f.fiber (f (j y))))) :
    IsClosed ({(j ≫ f).asFiber y} : Set ((j ≫ f).fiber ((j ≫ f) y))) := by
  let φ : (j ≫ f).fiber ((j ≫ f) y) → f.fiber (f (j y)) := fun w ↦
    (f.fiberHomeo (f (j y))).symm
      ⟨j ((j ≫ f).fiberι ((j ≫ f) y) w), fiber_comp_base j f y w⟩
  have hφcont : Continuous φ :=
    (f.fiberHomeo (f (j y))).symm.continuous.comp
      ((j.continuous.comp ((j ≫ f).fiberι ((j ≫ f) y)).continuous).subtype_mk _)
  have hpre : φ ⁻¹' {f.asFiber (j y)} = {(j ≫ f).asFiber y} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun hw ↦ ?_, ?_⟩
    · have hjw : j ((j ≫ f).fiberι ((j ≫ f) y) w) = j y := by
        simpa [φ] using congrArg (f.fiberι (f (j y))) hw
      exact ((j ≫ f).fiberι ((j ≫ f) y)).isEmbedding.injective
        (by simpa only [Scheme.Hom.fiberι_asFiber] using j.isEmbedding.injective hjw)
    · rintro rfl
      refine (f.fiberι (f (j y))).isEmbedding.injective ?_
      have hφι : f.fiberι (f (j y)) (φ ((j ≫ f).asFiber y)) =
          j ((j ≫ f).fiberι ((j ≫ f) y) ((j ≫ f).asFiber y)) := by simp [φ]
      rw [hφι, Scheme.Hom.fiberι_asFiber (j ≫ f) y, Scheme.Hom.fiberι_asFiber f (j y)]
  exact hpre ▸ h.preimage hφcont

/-- The image of a point closed in its fibre over `S` is closed in its fibre, for a morphism of
sources whose composite with `f` is again locally of finite type: the residue field of the image
embeds into a residue field finite over that of the base point. -/
public theorem isClosed_asFiber_of_comp {Y X S : Scheme.{u}} (j : Y ⟶ X) (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyOfFiniteType (j ≫ f)] (y : Y)
    (h : IsClosed ({(j ≫ f).asFiber y} : Set ((j ≫ f).fiber ((j ≫ f) y)))) :
    IsClosed ({f.asFiber (j y)} : Set (f.fiber (f (j y)))) := by
  let : Algebra (S.residueField (f (j y))) (X.residueField (j y)) :=
    (f.residueFieldMap (j y)).hom.toAlgebra
  let : Algebra (X.residueField (j y)) (Y.residueField y) := (j.residueFieldMap y).hom.toAlgebra
  let : Algebra (S.residueField (f (j y))) (Y.residueField y) :=
    ((j ≫ f).residueFieldMap y).hom.toAlgebra
  have : IsScalarTower (S.residueField (f (j y))) (X.residueField (j y)) (Y.residueField y) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp j f y))
  have : FiniteDimensional (S.residueField (f (j y))) (Y.residueField y) :=
    (isClosed_asFiber_iff_finite_residueField (j ≫ f) y).mp h
  exact (isClosed_asFiber_iff_finite_residueField f (j y)).mpr
    (FiniteDimensional.of_injective
      (IsScalarTower.toAlgHom (S.residueField (f (j y))) (X.residueField (j y))
        (Y.residueField y)).toLinearMap (RingHom.injective (j.residueFieldMap y).hom))

/-- A point of `X` lying over `s` gives a point of the fibre `X_s`, closed in `X_s` as soon as it
is closed in the fibre through it. -/
private lemma exists_fiberι_eq_isClosed {X S : Scheme.{u}} (f : X ⟶ S) {s : S} {w : X}
    (hw : f w = s) (h : IsClosed ({f.asFiber w} : Set (f.fiber (f w)))) :
    ∃ y : f.fiber s, f.fiberι s y = w ∧ IsClosed ({y} : Set (f.fiber s)) := by
  subst hw
  exact ⟨f.asFiber w, f.fiberι_asFiber w, h⟩

/-- A point of a locally Noetherian scheme has finite codimension: its codimension is the Krull
dimension of the local ring there, which is Noetherian local. -/
private lemma coheight_lt_top {S : Scheme.{u}} [IsLocallyNoetherian S] (s : S) :
    Order.coheight s < ⊤ := by
  have h := ringKrullDim_lt_top (R := S.presheaf.stalk s)
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact WithBot.coe_lt_coe.mp (by simpa only [WithBot.coe_top] using h)

/-- A proper specialization in a locally Noetherian scheme strictly increases the codimension. -/
private lemma coheight_lt_coheight_of_specializes {S : Scheme.{u}} [IsLocallyNoetherian S]
    {s t : S} (h : s ⤳ t) (hne : s ≠ t) : Order.coheight s < Order.coheight t :=
  Order.coheight_strictAnti
    (lt_of_le_not_ge (show t ≤ s from h) fun h' ↦ hne (h.antisymm h').eq) (coheight_lt_top s)

/-- One step of the induction behind Stacks 05GV, from Stacks 05GU: for `x ⤳ x'` with `x'`
closed in its fibre and `f x ≠ f x'`, some point of an open neighbourhood `W` of `x` lies between
`x` and `x'`, is closed in its fibre, and lies over a point other than `f x'`. -/
private lemma exists_isClosed_asFiber_between_mem_of_ne {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] {x x' : X} {W : Set X} (hW : IsOpen W)
    (hxW : x ∈ W) (hxx' : x ⤳ x') (hx' : IsClosed ({f.asFiber x'} : Set (f.fiber (f x'))))
    (hne : f x ≠ f x') :
    ∃ z ∈ W, x ⤳ z ∧ z ⤳ x' ∧ f z ≠ f x' ∧
      IsClosed ({f.asFiber z} : Set (f.fiber (f z))) := by
  let T : Closeds X := Closeds.closure ({x} : Set X)
  let jm : (Scheme.IdealSheafData.vanishingIdeal T).subscheme ⟶ X :=
    (Scheme.IdealSheafData.vanishingIdeal T).subschemeι
  have hrange : Set.range jm = closure ({x} : Set X) :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal T
  obtain ⟨x₁, hx₁⟩ : x ∈ Set.range jm := hrange ▸ subset_closure rfl
  obtain ⟨x₁', hx₁'⟩ : x' ∈ Set.range jm := hrange ▸ specializes_iff_mem_closure.mp hxx'
  have hx₁x₁' : x₁ ⤳ x₁' :=
    jm.isEmbedding.isInducing.specializes_iff.mp (by rwa [hx₁, hx₁'])
  have hbase : IsClosed ({f.asFiber (jm x₁')} : Set (f.fiber (f (jm x₁')))) := by rwa [hx₁']
  obtain ⟨Z, i, hi, xZ, hxZ, hqf, zZ, hzZW, hzZxZ, hzZne⟩ :=
    Stacks.ClosedPointsFibre.exists_closedSubscheme_quasiFiniteAt_meeting_open (jm ≫ f) x₁'
      ⟨jm ⁻¹' W, hW.preimage jm.continuous⟩ (isClosed_asFiber_comp jm f x₁' hbase)
      ⟨x₁, by simpa only [Set.mem_preimage, hx₁] using hxW, hx₁x₁',
        by rw [show (jm ≫ f) x₁ = f x from by rw [← hx₁]; rfl,
          show (jm ≫ f) x₁' = f x' from by rw [← hx₁']; rfl]; exact hne⟩
  have hqfz : quasiFiniteAt (i ≫ (jm ≫ f)) zZ := by
    rw [← mem_quasiFiniteLocus_iff]
    exact hzZxZ.mem_open (quasiFiniteLocus (i ≫ (jm ≫ f))).2
      ((mem_quasiFiniteLocus_iff _ xZ).mpr hqf)
  refine ⟨jm (i zZ), hzZW,
    specializes_iff_mem_closure.mpr (by rw [← hrange]; exact ⟨i zZ, rfl⟩), ?_,
    by rwa [← hx₁'],
    isClosed_asFiber_of_comp jm f (i zZ)
      (isClosed_asFiber_of_comp i (jm ≫ f) zZ hqfz.2.isClopen_singleton_asFiber.isClosed)⟩
  simpa only [hxZ, hx₁'] using (hzZxZ.map i.continuous).map jm.continuous

/-- The induction behind Stacks 05GV: a point of `X_{f x}` closed in `X_{f x}` and lying between
`x` and `x'` can be found in any open neighbourhood `W` of `x` in `X`, by induction on a bound
for the codimension of `f x'`. -/
private theorem exists_isClosed_fiberι_mem_of_coheight_le {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (x : X) (W : Set X) (hW : IsOpen W)
    (hxW : x ∈ W) :
    ∀ (n : ℕ) (x' : X), x ⤳ x' → IsClosed ({f.asFiber x'} : Set (f.fiber (f x'))) →
      f x ≠ f x' → Order.coheight (f x') ≤ (n : ℕ∞) →
      ∃ y : f.fiber (f x), f.fiberι (f x) y ∈ W ∧ IsClosed ({y} : Set (f.fiber (f x))) ∧
        x ⤳ f.fiberι (f x) y ∧ f.fiberι (f x) y ⤳ x' := by
  intro n
  induction n with
  | zero =>
    intro x' hxx' hx' hne hdim
    exact absurd ((coheight_lt_coheight_of_specializes (hxx'.map f.continuous) hne).trans_le hdim)
      (by simp)
  | succ n ih =>
    intro x' hxx' hx' hne hdim
    obtain ⟨z, hzW, hxz, hzx', hzne, hclosedz⟩ :=
      exists_isClosed_asFiber_between_mem_of_ne f hW hxW hxx' hx' hne
    by_cases hfz : f z = f x
    · obtain ⟨y, hy, hyclosed⟩ := exists_fiberι_eq_isClosed f hfz hclosedz
      exact ⟨y, by rwa [hy], hyclosed, by rwa [hy], by rwa [hy]⟩
    · have hdim' : Order.coheight (f z) ≤ (n : ℕ∞) := by
        have hlt : Order.coheight (f z) < ((n + 1 : ℕ) : ℕ∞) :=
          (coheight_lt_coheight_of_specializes (hzx'.map f.continuous) hzne).trans_le hdim
        lift Order.coheight (f z) to ℕ using hlt.ne_top with m hm
        exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast hlt)
      obtain ⟨y, hy, hyclosed, hxy, hyz⟩ := ih z hxz hclosedz (Ne.symm hfz) hdim'
      exact ⟨y, hy, hyclosed, hxy, hyz.trans hzx'⟩

/-- **Stacks 053U for a locally Noetherian base.** For `f : X ⟶ S` locally of finite type with
`S` locally Noetherian, `x ⤳ x'` with `x'` closed in its fibre and `f x ≠ f x'` (or `x = x'`),
the points of `X_{f x}` closed in `X_{f x}` and lying between `x` and `x'` are dense in the
closure of `x` in `X_{f x}`. -/
@[stacks 05GV "the theorem the remark asserts, by the route it sketches; the hypothesis \
  `f x ≠ f x'` (or `x = x'`) is added, Stacks 053U being false without it"]
public theorem closure_closedPoints_between_fiber_eq_of_isLocallyNoetherian {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S] (x x' : X) (hxx' : x ⤳ x')
    (hx' : IsClosed ({f.asFiber x'} : Set (f.fiber (f x'))))
    (hs : f x ≠ f x' ∨ x = x') :
    closure {y : f.fiber (f x) | IsClosed ({y} : Set (f.fiber (f x))) ∧
        x ⤳ f.fiberι (f x) y ∧ f.fiberι (f x) y ⤳ x'} =
      closure ({f.asFiber x} : Set (f.fiber (f x))) := by
  obtain hne | rfl := hs
  · refine closure_closedPoints_between_fiber_eq_of_forall_isOpen f x x' fun U hU hxU ↦ ?_
    obtain ⟨V, hV, hVU⟩ := (f.fiberι (f x)).isEmbedding.isInducing.isOpen_iff.mp hU
    have hxV : x ∈ V := by
      have hmem : f.asFiber x ∈ f.fiberι (f x) ⁻¹' V := by rwa [hVU]
      simpa only [Set.mem_preimage, Scheme.Hom.fiberι_asFiber] using hmem
    obtain ⟨n, hn⟩ : ∃ n : ℕ, Order.coheight (f x') ≤ (n : ℕ∞) :=
      (ENat.ne_top_iff_exists.mp (coheight_lt_top (f x')).ne_top).imp fun _ h ↦ h.ge
    obtain ⟨y, hy, hyclosed, hxy, hyx'⟩ :=
      exists_isClosed_fiberι_mem_of_coheight_le f x V hV hxV n x' hxx' hx' hne hn
    exact ⟨y, by rwa [← hVU], hyclosed, hxy, hyx'⟩
  · exact closure_closedPoints_between_fiber_eq_of_isClosed f x x hxx' hx'

end AlgebraicGeometry

end
