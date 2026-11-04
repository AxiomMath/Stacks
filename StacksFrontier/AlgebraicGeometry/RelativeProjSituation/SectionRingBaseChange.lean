module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.GradedPullback
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.PullbackSectionCalculus
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.SituationData
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback

/-!
# The graded section rings of a relative `Proj` situation base-change along a morphism

A relative `Proj` situation `s` glues the charts `Proj 𝒜(W)`, `W` an affine open of the base,
along the restriction maps `𝒜(W) ⟶ 𝒜(V)` of their graded rings of sections,
`Stacks.RelativeProj.Situation.gradedRestrict`.

Given situations `s` on `S` and `s'` on `S'`, a morphism `g : S' ⟶ S` and an identification of
the graded algebra of `s'` with the pullback of that of `s` — a
`SheafOfModules.GradedAlgebra.UnitalHom` out of `Stacks.Conormal.gradedPullback g s.algebra` —
this file constructs a homomorphism of graded rings

  `𝒜(W) ⟶ 𝒜'(W')`

for every pair of opens `W ⊆ S`, `W' ⊆ S'` with `W' ⊆ g⁻¹W`.

## Main definitions

* `Stacks.RelativeProj.Situation.pieceSectionHom` is the degree-`n` component: pull a
  homogeneous section back along `g` and read it through the identification of the algebras.
* `Stacks.RelativeProj.Situation.sectionRingBaseChange` is the induced homomorphism of the
  graded rings of sections, and
  `Stacks.RelativeProj.Situation.gradedBaseChange` is the same as a homomorphism of *graded*
  rings.

## Main results

* `Stacks.RelativeProj.Situation.pullbackSection_algebra_mul` and `pullbackSection_algebra_one`:
  pulling sections back to a pair `(W, W')` is multiplicative and unital for the pulled-back
  graded algebra.
* `Stacks.RelativeProj.Situation.pieceSectionHom_mul` and `pieceSectionHom_one`: the degreewise
  components are multiplicative and unital.
* `Stacks.RelativeProj.Situation.gmul_eq_algebra_mul` and `gone_eq_algebra_one`: the graded
  product and unit of the section ring are the product and unit of the graded algebra.

## Implementation notes

The degree index crosses from `ℕ` to `ℤ`: the graded algebra of a situation is indexed by `ℤ`
and its section ring by `ℕ`, so a product in degrees `n` and `m` lands in `𝒜(W)_{↑(n + m)}` on
one side and in `𝒜(W)_{↑n + ↑m}` on the other. The two are definitionally but not
syntactically equal, so the multiplicativity and unitality proofs are in term mode.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite DirectSum
open HomogeneousIdeal

universe u

namespace Stacks.RelativeProj.Situation

/-! ### Products and the unit in the section ring -/

/-- The graded product of two homogeneous sections is their product in the graded algebra. -/
public theorem gmul_eq_algebra_mul (r : Situation.{u}) (U : r.base.Opens) (n m : ℕ)
    (a : r.sectionPieces U n) (b : r.sectionPieces U m) :
    (GradedMonoid.GMul.mul a b : r.sectionPieces U (n + m)) =
      (r.algebra.mul (n : ℤ) (m : ℤ)).app (op U) a b :=
  eq_of_heq ((sectionRingStructure r).mul_homogeneous U n m a b)

/-- The graded unit of the section ring is the unit of the graded algebra. -/
public theorem gone_eq_algebra_one (r : Situation.{u}) (U : r.base.Opens) :
    (GradedMonoid.GOne.one : r.sectionPieces U 0) = r.algebra.one.eval (op U) :=
  (sectionRingStructure r).one_homogeneous U

/-! ### Pulling homogeneous sections back to a pair of opens -/

variable {s s' : Situation.{u}} (g : s'.base ⟶ s.base)

/-- Restricting the pullback of a section to `g⁻¹W` down to `W' ≤ g⁻¹W` is pulling it back to
`W'`. -/
private theorem map_pullbackSection_homOfLE (M : s.base.Modules) (W : s.base.Opens)
    (W' : s'.base.Opens) (h : W' ≤ g ⁻¹ᵁ W) (a : M.val.obj (op W)) :
    ((Scheme.Modules.pullback g).obj M).val.map (homOfLE h).op
        (Scheme.Modules.pullbackSection g M W (g ⁻¹ᵁ W) le_rfl a) =
      Scheme.Modules.pullbackSection g M W W' h a :=
  Stacks.AlgebraicGeometry.ModuleLimits.pullbackSection_shrink g M W (g ⁻¹ᵁ W) W' le_rfl h h a

/-- **Pulling back a product of homogeneous sections.** Pulling sections back from `W` to an open
`W' ≤ g⁻¹W` carries the product of the graded algebra to the product of its pullback. -/
public theorem pullbackSection_algebra_mul (i j : ℤ) (W : s.base.Opens) (W' : s'.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) (a : (s.algebra.piece i).val.obj (op W))
    (b : (s.algebra.piece j).val.obj (op W)) :
    Scheme.Modules.pullbackSection g (s.algebra.piece (i + j)) W W' h
        ((s.algebra.mul i j).app (op W) a b) =
      ((Stacks.Conormal.gradedPullback g s.algebra).mul i j).app (op W')
        (Scheme.Modules.pullbackSection g (s.algebra.piece i) W W' h a)
        (Scheme.Modules.pullbackSection g (s.algebra.piece j) W W' h b) := by
  have h1 := Stacks.Conormal.gradedPullback_mul_pullbackSection g s.algebra i j W a b
  have h2 := ((Stacks.Conormal.gradedPullback g s.algebra).mul i j).naturality (homOfLE h).op
      (Scheme.Modules.pullbackSection g (s.algebra.piece i) W (g ⁻¹ᵁ W) le_rfl a)
      (Scheme.Modules.pullbackSection g (s.algebra.piece j) W (g ⁻¹ᵁ W) le_rfl b)
  rw [h1] at h2
  rwa [← map_pullbackSection_homOfLE g (s.algebra.piece (i + j)) W W' h,
    ← map_pullbackSection_homOfLE g (s.algebra.piece i) W W' h,
    ← map_pullbackSection_homOfLE g (s.algebra.piece j) W W' h]

/-- **Pulling back the unit.** Pulling sections back from `W` to an open `W' ≤ g⁻¹W` carries the
unit of the graded algebra to the unit of its pullback. -/
public theorem pullbackSection_algebra_one (W : s.base.Opens) (W' : s'.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) :
    Scheme.Modules.pullbackSection g (s.algebra.piece 0) W W' h (s.algebra.one.eval (op W)) =
      (Stacks.Conormal.gradedPullback g s.algebra).one.eval (op W') := by
  rw [← map_pullbackSection_homOfLE g (s.algebra.piece 0) W W' h,
    ← Stacks.Conormal.gradedPullback_one_eval g s.algebra W]
  exact (Stacks.Conormal.gradedPullback g s.algebra).one.property (homOfLE h).op

/-! ### The base change of the graded section rings -/

variable (Φ : SheafOfModules.GradedAlgebra.UnitalHom
  (Stacks.Conormal.gradedPullback g s.algebra) s'.algebra)

/-- **The degree-`n` component of the base change of section rings.** A homogeneous section of
`𝒜` over `W` is pulled back along `g` to `W'` and read through the identification of `𝒜'` with
the pullback of `𝒜`. -/
public def pieceSectionHom (n : ℕ) (W : s.base.Opens) (W' : s'.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) : s.sectionPieces W n →+ s'.sectionPieces W' n :=
  ((Φ.app (n : ℤ)).val.app (op W')).hom.toAddMonoidHom.comp
    ((((Scheme.Modules.pullback g).obj (s.algebra.piece (n : ℤ))).val.map
          (homOfLE h).op).hom.toAddMonoidHom.comp
      ((((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          (s.algebra.piece (n : ℤ))).val.app (op W)).hom.toAddMonoidHom))

/-- `Stacks.RelativeProj.Situation.pieceSectionHom` pulls a section back along `g` and applies the
identification of the algebras. -/
public theorem pieceSectionHom_apply (n : ℕ) (W : s.base.Opens) (W' : s'.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) (a : s.sectionPieces W n) :
    pieceSectionHom g Φ n W W' h a =
      (Φ.app (n : ℤ)).val.app (op W')
        (Scheme.Modules.pullbackSection g (s.algebra.piece (n : ℤ)) W W' h a) := rfl

/-- **The degreewise components are multiplicative.** -/
public theorem pieceSectionHom_mul (n m : ℕ) (W : s.base.Opens) (W' : s'.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) (a : s.sectionPieces W n) (b : s.sectionPieces W m) :
    pieceSectionHom g Φ (n + m) W W' h ((s.algebra.mul (n : ℤ) (m : ℤ)).app (op W) a b) =
      (s'.algebra.mul (n : ℤ) (m : ℤ)).app (op W')
        (pieceSectionHom g Φ n W W' h a) (pieceSectionHom g Φ m W W' h b) :=
  (congrArg (fun z => (Φ.app ((n : ℤ) + (m : ℤ))).val.app (op W') z)
    (pullbackSection_algebra_mul g (n : ℤ) (m : ℤ) W W' h a b)).trans
      (Φ.map_mul (n : ℤ) (m : ℤ) (op W') _ _)

/-- **The degreewise components are unital.** -/
public theorem pieceSectionHom_one (W : s.base.Opens) (W' : s'.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) :
    pieceSectionHom g Φ 0 W W' h (s.algebra.one.eval (op W)) = s'.algebra.one.eval (op W') :=
  (congrArg (fun z => (Φ.app 0).val.app (op W') z)
    (pullbackSection_algebra_one g W W' h)).trans (Φ.map_one (op W'))

/-- The base change of graded section rings, additively. -/
public def sectionRingBaseChangeAddHom (W : s.base.Opens) (W' : s'.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) : s.sectionRing W →+ s'.sectionRing W' :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (s'.sectionPieces W') n).comp (pieceSectionHom g Φ n W W' h)

/-- `Stacks.RelativeProj.Situation.sectionRingBaseChangeAddHom` on a homogeneous summand is
`Stacks.RelativeProj.Situation.pieceSectionHom`. -/
@[simp] public theorem sectionRingBaseChangeAddHom_of (W : s.base.Opens) (W' : s'.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) (n : ℕ) (a : s.sectionPieces W n) :
    sectionRingBaseChangeAddHom g Φ W W' h (DirectSum.of (s.sectionPieces W) n a) =
      DirectSum.of (s'.sectionPieces W') n (pieceSectionHom g Φ n W W' h a) := by
  simp [sectionRingBaseChangeAddHom]

/-- **The base change of the graded rings of sections**, for a pair of opens `W ⊆ S`,
`W' ⊆ g⁻¹W ⊆ S'`. On a homogeneous summand it is
`Stacks.RelativeProj.Situation.pieceSectionHom`. -/
public def sectionRingBaseChange (W : s.base.Opens) (W' : s'.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) : s.sectionRing W →+* s'.sectionRing W' where
  toFun := sectionRingBaseChangeAddHom g Φ W W' h
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    rw [DirectSum.one_def, sectionRingBaseChangeAddHom_of, DirectSum.one_def]
    refine congrArg (DirectSum.of (s'.sectionPieces W') 0) ?_
    rw [gone_eq_algebra_one s W, pieceSectionHom_one, gone_eq_algebra_one s' W']
  map_mul' := by
    rw [(sectionRingBaseChangeAddHom g Φ W W' h).map_mul_iff]
    refine DirectSum.addHom_ext' (fun n => AddMonoidHom.ext (fun a => ?_))
    refine DirectSum.addHom_ext' (fun m => AddMonoidHom.ext (fun b => ?_))
    change sectionRingBaseChangeAddHom g Φ W W' h
        (DirectSum.of (s.sectionPieces W) n a * DirectSum.of (s.sectionPieces W) m b) =
      sectionRingBaseChangeAddHom g Φ W W' h (DirectSum.of (s.sectionPieces W) n a) *
        sectionRingBaseChangeAddHom g Φ W W' h (DirectSum.of (s.sectionPieces W) m b)
    rw [DirectSum.of_mul_of, sectionRingBaseChangeAddHom_of, sectionRingBaseChangeAddHom_of,
      sectionRingBaseChangeAddHom_of, DirectSum.of_mul_of]
    refine congrArg (DirectSum.of (s'.sectionPieces W') (n + m)) ?_
    rw [gmul_eq_algebra_mul s W n m a b, gmul_eq_algebra_mul s' W' n m _ _,
      pieceSectionHom_mul]

/-- `Stacks.RelativeProj.Situation.sectionRingBaseChange` on a homogeneous summand is
`Stacks.RelativeProj.Situation.pieceSectionHom`. -/
@[simp] public theorem sectionRingBaseChange_of (W : s.base.Opens) (W' : s'.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) (n : ℕ) (a : s.sectionPieces W n) :
    sectionRingBaseChange g Φ W W' h (DirectSum.of (s.sectionPieces W) n a) =
      DirectSum.of (s'.sectionPieces W') n (pieceSectionHom g Φ n W W' h a) :=
  sectionRingBaseChangeAddHom_of g Φ W W' h n a

/-- **The base change of section rings, as a homomorphism of graded rings.** -/
public def gradedBaseChange (W : s.base.Opens) (W' : s'.base.Opens) (h : W' ≤ g ⁻¹ᵁ W) :
    s.sectionRingGrading W →+*ᵍ s'.sectionRingGrading W' where
  toRingHom := sectionRingBaseChange g Φ W W' h
  map_mem := by
    rintro n x ⟨a, rfl⟩
    exact ⟨_, (sectionRingBaseChange_of g Φ W W' h n a).symm⟩

/-- `Stacks.RelativeProj.Situation.gradedBaseChange` is
`Stacks.RelativeProj.Situation.sectionRingBaseChange` as a function. -/
@[simp] public theorem gradedBaseChange_apply (W : s.base.Opens) (W' : s'.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) (x : s.sectionRing W) :
    gradedBaseChange g Φ W W' h x = sectionRingBaseChange g Φ W W' h x := rfl

end Stacks.RelativeProj.Situation

end
