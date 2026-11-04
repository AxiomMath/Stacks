module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.Topology.Sober
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Differentials
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Points of a group scheme over a field are products of maximal points

Let `G` be a group scheme over a field `k`.  Every point `x` of `G` is the product of two maximal
points: there is a point `u` of `G ×_k G` with `μ u = x` whose two projections are generic
points of irreducible components of `G` ([SGA3, Exp. VI_A, 6.1]; Perrin's thesis, II 1.1).

## Main results

* `AlgebraicGeometry.exists_mul_eq_of_maximal`.

## Implementation notes

Let `F` be the fibre of `μ` over `x`, that is the fibre product of `Spec κ(x) ⟶ G` and `μ`.
The two shearing automorphisms `(g, h) ↦ (gh, h)` and `(g, h) ↦ (gh, g)` of `G ×_k G` show that
`(μ, pr₂)` and `(μ, pr₁)` both exhibit `G ×_k G` as `G ×_k G`; pasting with the fibre square,
each composite `F ⟶ G ×_k G ⟶ G` of a projection is a base change of `Spec κ(x) ⟶ Spec k`,
hence flat, hence generalizing.  A generalizing continuous map sends maximal points to maximal
points (`mem_irreducibleComponents_closure_of_generalizingMap`), and `F` is nonempty because
`μ` is surjective, so a maximal point of `F` does it.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GrpObj

universe u

/-- **A generalizing continuous map sends maximal points to maximal points**: if the closure of
`v` is an irreducible component, so is the closure of `f v`. -/
theorem mem_irreducibleComponents_closure_of_generalizingMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [QuasiSober Y] {f : X → Y} (hf : Continuous f) (hg : GeneralizingMap f)
    {v : X} (hv : closure {v} ∈ irreducibleComponents X) :
    closure {f v} ∈ irreducibleComponents Y := by
  obtain ⟨Z, hZ, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (isIrreducible_singleton (x := f v)).closure
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  obtain ⟨w, hwv, hfw⟩ := hg (hξ.specializes (hsub (subset_closure rfl)))
  have hwmem : w ∈ closure {v} := hv.2 (isIrreducible_singleton (x := w)).closure
    (specializes_iff_closure_subset.mp hwv) (subset_closure rfl)
  have hZsub : Z ⊆ closure {f v} := by
    rw [← hξ.def, ← hfw, ← specializes_iff_closure_subset]
    exact (specializes_iff_mem_closure.mpr hwmem).map hf
  rwa [subset_antisymm hsub hZsub]

namespace AlgebraicGeometry

open GroupSchemeDifferentials

section Shear

variable {S G : Scheme.{u}} (f : G ⟶ S) [GrpObj (Over.mk f)]

/-- **The second shearing automorphism** `(g, h) ↦ (gh, g)` of `G ×_S G`, with inverse
`(a, g) ↦ (g, g⁻¹ a)`. -/
@[sga "3 VIA 0.1" "partial"]
noncomputable def shearFstIso : (Over.mk f ⊗ Over.mk f) ≅ (Over.mk f ⊗ Over.mk f) where
  hom := lift μ[Over.mk f] (fst _ _)
  inv := lift (snd _ _) ((snd _ _)⁻¹ * fst _ _)
  hom_inv_id := by apply hom_ext <;> simp [GrpObj.comp_inv, MonObj.comp_mul, MonObj.mul_eq_mul]
  inv_hom_id := by apply hom_ext <;> simp [MonObj.comp_mul, MonObj.mul_eq_mul]

/-- **Multiplication and the first projection exhibit `G ×_S G` as a fibre product of `f` with
itself**, through the shearing automorphism `(g, h) ↦ (gh, g)`. -/
@[sga "3 VIA 0.1" "partial"]
lemma isPullback_mul_fst : IsPullback (mul f) (pullback.fst f f) f f := by
  refine IsPullback.of_iso_pullback ⟨(mul_comp f).trans pullback.condition.symm⟩
    ((Over.forget S).mapIso (shearFstIso f)) ?_ ?_
  · change ((shearFstIso f).hom ≫ fst (Over.mk f) (Over.mk f)).left = _
    simp [shearFstIso]
    rfl
  · change ((shearFstIso f).hom ≫ snd (Over.mk f) (Over.mk f)).left = _
    simp [shearFstIso]

end Shear

variable (k : Type u) [Field k] (G : Grp (Over (Spec (CommRingCat.of k))))

/-- **Every point of a group scheme over a field is a product of two maximal points**
([SGA3, Exp. VI_A, 6.1]; Perrin, II 1.1): for every point `x` of `G` there is a point `u` of
`G ×_k G` with `μ u = x` whose two projections are generic points of irreducible components
of `G`. -/
@[sga "3 VIA 6.1"]
theorem exists_mul_eq_of_maximal (x : G.X.left) :
    ∃ u : (G.X ⊗ G.X).left, μ[G.X].left u = x ∧
      closure {pullback.fst G.X.hom G.X.hom u} ∈ irreducibleComponents G.X.left ∧
      closure {pullback.snd G.X.hom G.X.hom u} ∈ irreducibleComponents G.X.left := by
  let f := G.X.hom
  let : GrpObj (Over.mk f) := G.grp
  let xm := G.X.left.fromSpecResidueField x
  -- the fibre of the multiplication over `x` is nonempty
  obtain ⟨p, -⟩ : unitSection f x ∈ Set.range (pullback.fst (mul f) xm) := by
    rw [Scheme.Pullback.range_fst]
    let pt : Spec (G.X.left.residueField x) := IsLocalRing.closedPoint (G.X.left.residueField x)
    refine ⟨pt, ?_⟩
    change G.X.left.fromSpecResidueField x pt = _
    rw [Scheme.fromSpecResidueField_apply, ← Scheme.Hom.comp_apply, unitSection_mul]
    rfl
  -- a maximal point of the fibre
  obtain ⟨Z, hZ, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {p}
    isIrreducible_singleton
  let v := hZ.1.genericPoint
  have hv : closure {v} ∈ irreducibleComponents (pullback (mul f) xm : Scheme.{u}) := by
    rwa [(hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)).def]
  -- both projections of the fibre to `G` are flat
  have : Subsingleton (Spec (CommRingCat.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hflat : Flat (xm ≫ f) := inferInstance
  have key : ∀ q : pullback f f ⟶ G.X.left, IsPullback (mul f) q f f →
      closure {(pullback.fst (mul f) xm ≫ q) v} ∈ irreducibleComponents G.X.left := fun q hq => by
    have : Flat (pullback.fst (mul f) xm ≫ q) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        ((IsPullback.of_hasPullback (mul f) xm).paste_horiz hq.flip).flip hflat
    exact mem_irreducibleComponents_closure_of_generalizingMap
      (pullback.fst (mul f) xm ≫ q).continuous (Flat.generalizingMap _) hv
  refine ⟨pullback.fst (mul f) xm v, ?_, key _ (isPullback_mul_fst f), key _ (isPullback_mul f)⟩
  change (pullback.fst (mul f) xm ≫ mul f) v = x
  rw [pullback.condition, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

end AlgebraicGeometry
