module

public import Mathlib.CategoryTheory.GradedObject.Single
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalChowCycleData
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalTheoryPairing
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotiveMonoid
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TateRealization
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilRealization
public import StacksFrontier.CategoryTheory.GradedObject.KoszulBraiding
public import StacksFrontier.CategoryTheory.GradedObject.Linear

/-!
# Classical Weil cohomology theories and realizations of Chow motives

Stacks 0FH3 says that, for `k` algebraically closed and `F` of characteristic zero, a classical
Weil cohomology theory (Stacks 0FGV) is the same thing as a `ℚ`-linear functor
`G : M_k ⥤ graded F-vector spaces` of symmetric monoidal categories together with an isomorphism
`F[2] → G(𝟏(1))` such that `G(h(X))` lives in nonnegative degrees and `dim_F G⁰(h(X)) = 1` for
every smooth projective variety `X`. This file sets up both sides of that correspondence and
proves the part of it that takes place inside cohomology: in the presence of axioms (A)(a) and
(A)(b), conditions (1) and (2) are equivalent to axioms (A)(c) and (A)(d).

## Main definitions

* `Stacks.WeilCohomology.ClassicalMotiveRealization`: side (2) of Stacks 0FH3, an additive
  `ℚ`-linear functor `G : M_k ⥤ GradedObject ℤ (ModuleCat F)` of symmetric monoidal categories
  (graded vector spaces carrying the Koszul sign rule of Stacks 0FFX), with an isomorphism
  `F[2] ≅ G(𝟏(1))` and conditions (1) and (2).
* `Stacks.WeilCohomology.PoincarePairingSetup.MotiveComparison`: an identification
  `H^i(X) ≅ G(h(X))^i`, natural in `X`, of the cohomology of a pairing setup with a functor on
  motives: the sense in which `H^*(X) = G(h(X))` in the proof of Stacks 0FH3.
* `Stacks.WeilCohomology.PreClassicalWeilCohomologyTheory.toClassicalOfNonneg`: data satisfying
  all of (A), (B), (C) except possibly (A)(c), (A)(d) and conditions (1), (2) form a classical
  Weil cohomology theory.

## Main results

* `Stacks.WeilCohomology.PoincarePairingSetup.eq_zero_of_two_mul_dimension_lt`: under (A)(b),
  vanishing in negative degrees gives vanishing in degrees above `2d`.
* `Stacks.WeilCohomology.PoincarePairingSetup.bijective_integration_of_finrank_eq_one`: under
  (A)(a) and (A)(b), if `dim_F H⁰(X) = 1` then `∫_X` is an isomorphism.
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.finrank_piece_zero`: conversely
  `dim_F H⁰(X) = 1` for a classical Weil cohomology theory.

## References

* [Stacks Project, Tag 0FH3](https://stacks.math.columbia.edu/tag/0FH3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open scoped TensorProduct MonObj
open Stacks.WeilCohomology.ChowMotiveCat (h tate)

universe u v

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]

/-! ### Conditions (1), (2) against axioms (A)(c), (A)(d) -/

namespace PoincarePairingSetup

variable (S : PoincarePairingSetup.{u, v, v} k F)

/-- Under Poincaré duality (A)(b), cohomology vanishing in negative degrees vanishes in degrees
above `2d` as well: `H^i(X)` pairs perfectly with `H^{2d - i}(X) = 0`. -/
theorem eq_zero_of_two_mul_dimension_lt
    (hneg : ∀ X (i : ℤ), i < 0 → ∀ a : (S.H X).piece i, a = 0)
    (X : (SmoothProjective k).FullSubcategory) {i : ℤ} (hi : 2 * (S.dimension X : ℤ) < i)
    (a : (S.H X).piece i) : a = 0 := by
  have hinj := (LinearMap.IsPerfPair.bijective_left
    ((S.H X).tracePairing (S.dimension X) (S.integration X) i) (self := S.perfect X i)).injective
  refine hinj ?_
  ext b
  rw [hneg X _ (by omega) b, map_zero, map_zero]

/-- Transporting an element to an equal degree gives any element it is heterogeneously equal to. -/
private theorem degreeCast_eq_of_heq {R : Type v} [CommRing R] {X : ℤ → Type v}
    [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)] {i j : ℤ} {h : i = j} {x : X i} {y : X j}
    (hxy : x ≍ y) : ExternallyGraded.degreeCast (R := R) (X := X) h x = y :=
  eq_of_heq ((ExternallyGraded.degreeCast_heq _ _).trans hxy)

omit [CharZero F] in
/-- In an externally graded algebra the unit acts trivially on the left of every piece, written
without heterogeneous equality. -/
theorem _root_.ExternallyGradedAlgebra.degreeCast_mul_one_left
    (A : ExternallyGradedAlgebra.{v, v} F) (i : ℤ) (a : A.piece i) :
    ExternallyGraded.degreeCast (R := F) (X := A.piece) (zero_add i) (A.mul 0 i A.one a) = a :=
  degreeCast_eq_of_heq (A.one_mul i a)

omit [CharZero F] in
/-- The unit of an externally graded algebra with nonzero degree zero piece is nonzero. -/
theorem _root_.ExternallyGradedAlgebra.one_ne_zero_of_nontrivial
    (A : ExternallyGradedAlgebra.{v, v} F) [Nontrivial (A.piece 0)] : A.one ≠ 0 := by
  intro h
  obtain ⟨a, ha⟩ := exists_ne (0 : A.piece 0)
  apply ha
  rw [← A.degreeCast_mul_one_left 0 a, h, map_zero, LinearMap.zero_apply, map_zero]

/-- The trace pairing against the unit is the trace map. -/
theorem tracePairing_one (X : (SmoothProjective k).FullSubcategory)
    (b : (S.H X).piece (2 * (S.dimension X : ℤ) - 0)) :
    (S.H X).tracePairing (S.dimension X) (S.integration X) 0 (S.H X).one b =
      S.integration X (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece) (by omega) b) := by
  simp only [ExternallyGradedAlgebra.tracePairing, LinearMap.compr₂_apply, LinearMap.comp_apply]
  congr 1
  exact degreeCast_eq_of_heq (((S.H X).one_mul _ b).trans
    (ExternallyGraded.degreeCast_heq _ _).symm)

/-- Under (A)(a) and (A)(b), if `H⁰(X)` is one dimensional then the trace map
`∫_X : H^{2d}(X) → F` is an isomorphism. -/
theorem bijective_integration_of_finrank_eq_one (X : (SmoothProjective k).FullSubcategory)
    (h1 : Module.finrank F ((S.H X).piece 0) = 1) : Function.Bijective (S.integration X) := by
  have := S.finite X 0
  have : Nontrivial ((S.H X).piece 0) := Module.nontrivial_of_finrank_eq_succ h1
  have hone : (S.H X).one ≠ 0 := (S.H X).one_ne_zero_of_nontrivial
  set p := (S.H X).tracePairing (S.dimension X) (S.integration X) 0
  have := S.perfect X 0
  -- `e : H^{2d - 0}(X) ≃ H^{2d}(X)`
  let e := ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
    (show 2 * (S.dimension X : ℤ) - 0 = 2 * (S.dimension X : ℤ) by omega)
  have hint : ∀ b, S.integration X (e b) = p (S.H X).one b := fun b => (S.tracePairing_one X b).symm
  have hinj : Function.Injective (S.integration X) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    obtain ⟨b', rfl⟩ : ∃ b', e b' = b := ⟨ExternallyGraded.degreeCast (R := F)
      (X := (S.H X).piece) (by omega) b,
      degreeCast_eq_of_heq (ExternallyGraded.degreeCast_heq _ _)⟩
    have : b' = 0 := by
      apply (LinearMap.IsPerfPair.bijective_right p).injective
      ext a
      obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' _ hone).1 h1 a
      rw [LinearMap.flip_apply, map_smul, LinearMap.smul_apply, ← hint, hb, smul_zero,
        map_zero, LinearMap.zero_apply]
    rw [this, map_zero]
  refine ⟨hinj, fun y => ?_⟩
  -- `∫_X` is nonzero, as `p 1 ≠ 0`, and a nonzero functional to `F` is surjective
  have hp1 : p (S.H X).one ≠ 0 := fun h =>
    hone ((LinearMap.IsPerfPair.bijective_left p).injective (h.trans (map_zero p).symm))
  obtain ⟨b, hb⟩ : ∃ b, p (S.H X).one b ≠ 0 := not_forall.1 fun h => hp1 (LinearMap.ext h)
  refine ⟨(y / p (S.H X).one b) • e b, ?_⟩
  rw [map_smul, hint, smul_eq_mul, div_mul_cancel₀ _ hb]

end PoincarePairingSetup

omit [CharZero F] in
/-- A family of pieces indexed by equal degrees has equal dimensions. -/
theorem _root_.ExternallyGradedAlgebra.finrank_piece_congr (A : ExternallyGradedAlgebra.{v, v} F)
    {i j : ℤ} (h : i = j) : Module.finrank F (A.piece i) = Module.finrank F (A.piece j) := by
  subst h
  rfl

namespace ClassicalWeilCohomologyTheory

variable {Ch : ChowCycleData.{u, u} k} (T : ClassicalWeilCohomologyTheory.{u, v, v, u} k F Ch)

/-- Condition (1) of Stacks 0FH3 for a classical Weil cohomology theory: by (A)(c), `H^*(X)`
lives in nonnegative degrees. -/
theorem eq_zero_of_neg (X : (SmoothProjective k).FullSubcategory) {i : ℤ} (hi : i < 0)
    (a : (T.H X).piece i) : a = 0 :=
  T.bounded X i (Or.inl hi) a

/-- Condition (2) of Stacks 0FH3 for a classical Weil cohomology theory: `dim_F H⁰(X) = 1`, since
`H⁰(X)` is dual to `H^{2d}(X)` by (A)(b), and `∫_X : H^{2d}(X) → F` is an isomorphism by (A)(d). -/
theorem finrank_piece_zero (X : (SmoothProjective k).FullSubcategory) :
    Module.finrank F ((T.H X).piece 0) = 1 := by
  have := T.finite X 0
  have := T.perfect X 0
  rw [Module.finrank_of_isPerfPair
    ((T.H X).tracePairing (T.dimension X) (T.integration X).toLinearMap 0),
    (T.H X).finrank_piece_congr (sub_zero _), (T.integration X).finrank_eq, Module.finrank_self]

end ClassicalWeilCohomologyTheory

namespace PreClassicalWeilCohomologyTheory

variable {Ch : ChowCycleData.{u, u} k} (T : PreClassicalWeilCohomologyTheory.{u, v, v, u} k F Ch)

/-- **The first paragraph of the proof of Stacks 0FH3.** Data `(D1)`, `(D2)`, `(D3)` satisfying
all of `(A)`, `(B)`, `(C)` except possibly `(A)(c)` and `(A)(d)` form a classical Weil
cohomology theory as soon as `H^*(X)` lives in nonnegative degrees and `dim_F H⁰(X) = 1` for
every smooth projective variety `X`: by `(A)(a)` and `(A)(b)` these two conditions imply
`(A)(c)` and `(A)(d)`. -/
noncomputable def toClassicalOfNonneg
    (hneg : ∀ X (i : ℤ), i < 0 → ∀ a : (T.H X).piece i, a = 0)
    (hfin : ∀ X, Module.finrank F ((T.H X).piece 0) = 1) :
    ClassicalWeilCohomologyTheory.{u, v, v, u} k F Ch :=
  T.toClassical
    (fun X i hi a => hi.elim (fun h => hneg X i h a)
      (fun h => T.toPoincarePairingSetup.eq_zero_of_two_mul_dimension_lt hneg X h a))
    (fun X => T.toPoincarePairingSetup.bijective_integration_of_finrank_eq_one X (hfin X))

/-- The classical Weil cohomology theory `T.toClassicalOfNonneg hneg hfin` has underlying
preclassical theory `T`. -/
@[simp]
theorem toPre_toClassicalOfNonneg (hneg hfin) : (T.toClassicalOfNonneg hneg hfin).toPre = T :=
  rfl

end PreClassicalWeilCohomologyTheory

/-! ### Realizations of Chow motives -/

variable (k F) in
/-- **Side (2) of Stacks 0FH3.** A `ℚ`-linear (additive, with `ℚ`-linear maps on morphisms)
functor `G : M_k ⥤ graded F-vector spaces` of symmetric monoidal categories, graded vector
spaces carrying the Koszul sign rule of Stacks 0FFX, together with an isomorphism
`F[2] ≅ G(𝟏(1))` of graded `F`-vector spaces (`F[2]` is `F` placed in degree `-2`), such
that for every smooth projective variety `X`

1. `G(h(X))` lives in nonnegative degrees, and
2. `dim_F G⁰(h(X)) = 1`. -/
structure ClassicalMotiveRealization where
  /-- The functor `G : M_k ⥤ graded F-vector spaces`. -/
  G : ChowMotiveCat k ⥤ GradedObject ℤ (ModuleCat.{v} F)
  /-- `G` is a functor of symmetric monoidal categories, for the Koszul sign rule. -/
  braided : letI : BraidedCategory (GradedObject ℤ (ModuleCat.{v} F)) :=
    GradedObject.koszulBraidedCategory
    G.Braided
  /-- `G` is additive. -/
  additive : G.Additive
  /-- `G` is `ℚ`-linear. -/
  linear : G.Linear ℚ
  /-- The isomorphism `F[2] ≅ G(𝟏(1))` of graded `F`-vector spaces. -/
  tateIso : (GradedObject.single (-2)).obj (ModuleCat.of F F) ≅ G.obj (tate k 1)
  /-- Condition (1): `G(h(X))` lives in nonnegative degrees. -/
  nonneg : ∀ (X : (SmoothProjective k).FullSubcategory) (i : ℤ), i < 0 →
    IsZero ((G.obj ((h k).obj (op ((SmoothProjective.toSchemeCat k).obj X)))) i)
  /-- Condition (2): `dim_F G⁰(h(X)) = 1`. -/
  finrank_zero : ∀ X : (SmoothProjective k).FullSubcategory,
    Module.finrank F ((G.obj ((h k).obj (op ((SmoothProjective.toSchemeCat k).obj X)))) 0) = 1

/-- The isomorphism `F[2] ≅ G(𝟏(1))` determined by a linear isomorphism `F ≅ G(𝟏(1))⁻²`, when
`G(𝟏(1))` is concentrated in degree `-2`. -/
noncomputable def tateIsoOfLinearEquiv {G : ChowMotiveCat k ⥤ GradedObject ℤ (ModuleCat.{v} F)}
    (hG : ∀ i, i ≠ -2 → IsZero ((G.obj (tate k 1)) i)) (e : F ≃ₗ[F] (G.obj (tate k 1)) (-2)) :
    (GradedObject.single (-2)).obj (ModuleCat.of F F) ≅ G.obj (tate k 1) :=
  GradedObject.isoMk _ _ fun i =>
    if hi : i = -2 then
      GradedObject.singleObjApplyIsoOfEq (-2) _ i hi ≪≫ e.toModuleIso ≪≫ eqToIso (by rw [hi])
    else (GradedObject.isInitialSingleObjApply (-2) _ i hi).isZero.iso (hG i hi)

omit [IsAlgClosed k] [CharZero F] in
/-- If `G` is monoidal and `G(𝟏(1))` is concentrated in degree `-2`, there is an isomorphism
`F[2] ≅ G(𝟏(1))`: by Stacks 0FH1 (`ChowMotiveCat.finrank_tate_apply`), `G(𝟏(1))⁻²` is one
dimensional. -/
theorem nonempty_tateIso {G : ChowMotiveCat k ⥤ GradedObject ℤ (ModuleCat.{v} F)} [G.Monoidal]
    (hG : ∀ i, i ≠ -2 → IsZero ((G.obj (tate k 1)) i)) :
    Nonempty ((GradedObject.single (-2)).obj (ModuleCat.of F F) ≅ G.obj (tate k 1)) := by
  have h1 : Module.finrank F ((G.obj (tate k 1)) (-2)) = 1 := by
    simpa using ChowMotiveCat.finrank_tate_apply hG 1
  have : FiniteDimensional F ((G.obj (tate k 1)) (-2)) := Module.finite_of_finrank_eq_succ h1
  exact ⟨tateIsoOfLinearEquiv hG (LinearEquiv.ofFinrankEq _ _ (by rw [h1, Module.finrank_self]))⟩

namespace ClassicalMotiveRealization

variable (R : ClassicalMotiveRealization k F)

omit [IsAlgClosed k] in
/-- `G(𝟏(1))` is concentrated in degree `-2`, being isomorphic to `F[2]`: the hypothesis of
Stacks 0FH1. -/
theorem isZero_tate_apply (i : ℤ) (hi : i ≠ -2) : IsZero ((R.G.obj (tate k 1)) i) :=
  ((GradedObject.isInitialSingleObjApply (-2) _ i hi).isZero).of_iso
    ((GradedObject.eval i).mapIso R.tateIso).symm

/-- The underlying realization of side (2) of Stacks 0FHM: forget the isomorphism
`F[2] ≅ G(𝟏(1))` and conditions (1), (2), keeping that `G(𝟏(1))` is concentrated in degree
`-2`. -/
def toWeilRealization : WeilRealization k F where
  functor := R.G
  braided := R.braided
  additive := R.additive
  linear := R.linear
  tate_degree := R.isZero_tate_apply

omit [IsAlgClosed k] in
/-- The functor of `R.toWeilRealization` is `R.G`. -/
@[simp]
theorem toWeilRealization_functor : R.toWeilRealization.functor = R.G :=
  rfl

end ClassicalMotiveRealization

namespace PoincarePairingSetup

/-- The cohomology of a pairing setup as a functor to graded `F`-vector spaces,
`X ↦ (n ↦ H^n(X))`, `f ↦ f^*`. -/
@[simps]
noncomputable def cohomologyFunctor (S : PoincarePairingSetup.{u, v, v} k F) :
    (SmoothProjective k).FullSubcategoryᵒᵖ ⥤ GradedObject ℤ (ModuleCat.{v} F) where
  obj X n := ModuleCat.of F ((S.H X.unop).piece n)
  map f n := ModuleCat.ofHom (S.pullback f.unop n)
  map_id X := by
    funext n
    ext a
    simp [S.pullback_id]
  map_comp f g := by
    funext n
    ext a
    simp [S.pullback_comp]

/-- An identification of the cohomology of a pairing setup `S` with a functor `G` on Chow
motives: linear isomorphisms `H^i(X) ≅ G(h(X))^i` for every smooth projective variety `X`,
natural in `X` (pullback `f^*` corresponds to `G(h(f))`, with `h(f) = [Γ_f]`). This is the sense
of `H^*(X) = G(h(X))` in Stacks 0FH1, 0FH2 and 0FH3. -/
structure MotiveComparison (S : PoincarePairingSetup.{u, v, v} k F)
    (G : ChowMotiveCat k ⥤ GradedObject ℤ (ModuleCat.{v} F)) where
  /-- The isomorphism `H^i(X) ≅ G(h(X))^i`. -/
  iso : ∀ (X : (SmoothProjective k).FullSubcategory) (i : ℤ),
    (S.H X).piece i ≃ₗ[F] (G.obj ((h k).obj (op ((SmoothProjective.toSchemeCat k).obj X)))) i
  /-- Naturality: `f^*` corresponds to `G(h(f))`. -/
  iso_pullback : ∀ {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y) (i : ℤ)
    (a : (S.H Y).piece i),
    iso X i (S.pullback f i a) =
      ((G.map ((h k).map ((SmoothProjective.toSchemeCat k).op.map f.op))) i).hom (iso Y i a)

namespace MotiveComparison

section ofIso

variable {S : PoincarePairingSetup.{u, v, v} k F}
  {G : ChowMotiveCat k ⥤ GradedObject ℤ (ModuleCat.{v} F)}

/-- A comparison from a natural isomorphism `G ∘ h ≅ H^*` of functors on smooth projective
varieties. -/
noncomputable def ofIso
    (ψ : (SmoothProjective.toSchemeCat k).op ⋙ h k ⋙ G ≅ S.cohomologyFunctor) :
    S.MotiveComparison G where
  iso X i := ((GradedObject.eval i).mapIso (ψ.app (op X))).symm.toLinearEquiv
  iso_pullback f i a :=
    congrArg (fun φ => ModuleCat.Hom.hom (φ i) a) (ψ.inv.naturality f.op)

/-- A comparison transported along a natural isomorphism `G ≅ G'` of functors on motives. -/
noncomputable def mapIso {G' : ChowMotiveCat k ⥤ GradedObject ℤ (ModuleCat.{v} F)}
    (E : S.MotiveComparison G) (θ : G ≅ G') : S.MotiveComparison G' where
  iso X i := (E.iso X i).trans ((GradedObject.eval i).mapIso
    (θ.app ((h k).obj (op ((SmoothProjective.toSchemeCat k).obj X))))).toLinearEquiv
  iso_pullback {X Y} f i a := by
    have hn := congrArg (fun φ ↦ ModuleCat.Hom.hom (φ i) (E.iso Y i a))
      (θ.hom.naturality ((h k).map ((SmoothProjective.toSchemeCat k).op.map f.op)))
    exact (congrArg _ (E.iso_pullback f i a)).trans hn

end ofIso

variable {S : PoincarePairingSetup.{u, v, v} k F}
  {G : ChowMotiveCat k ⥤ GradedObject ℤ (ModuleCat.{v} F)} (E : S.MotiveComparison G)
include E

/-- Condition (1) of Stacks 0FH3 transported along a comparison. -/
theorem eq_zero_of_isZero {X : (SmoothProjective k).FullSubcategory} {i : ℤ}
    (hX : IsZero ((G.obj ((h k).obj (op ((SmoothProjective.toSchemeCat k).obj X)))) i))
    (a : (S.H X).piece i) : a = 0 :=
  (E.iso X i).injective ((ModuleCat.isZero_iff_subsingleton.1 hX).elim _ _)

/-- Condition (1) of Stacks 0FH3 transported back along a comparison. -/
theorem isZero_of_eq_zero {X : (SmoothProjective k).FullSubcategory} {i : ℤ}
    (hX : ∀ a : (S.H X).piece i, a = 0) :
    IsZero ((G.obj ((h k).obj (op ((SmoothProjective.toSchemeCat k).obj X)))) i) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun a b => (E.iso X i).symm.injective ?_⟩
  rw [hX ((E.iso X i).symm a), hX ((E.iso X i).symm b)]

/-- Condition (2) of Stacks 0FH3 transported along a comparison. -/
theorem finrank_eq (X : (SmoothProjective k).FullSubcategory) (i : ℤ) :
    Module.finrank F ((S.H X).piece i) =
      Module.finrank F ((G.obj ((h k).obj (op ((SmoothProjective.toSchemeCat k).obj X)))) i) :=
  (E.iso X i).finrank_eq

/- The multiplication and unit of `h(X)` are those of `ChowMotiveCat.monObjMotive`, stated through
the generic monoidal structure of twisted Karoubi envelopes, as there (comparing morphisms over the
two instance paths makes `isDefEq` unfold correspondences). -/
attribute [-instance] ChowMotiveCat.monoidalCategory ChowMotiveCat.braidedCategory
  ChowMotiveCat.symmetricCategory GradedCategory.TwistedKaroubi.monoidalCategoryStruct in
/-- A comparison `H^*(X) ≅ G(h(X))` with a monoidal functor `G` is *multiplicative* when it
identifies the unit and the cup product of `H^*(X)` with the unit and multiplication that
`G(h(X))` inherits, through the monoidal structure of `G`, from the commutative monoid `h(X)`
(multiplication `[Γ_Δ]`, unit `[Γ_{X → Spec k}]`, `ChowMotiveCat.monObjMotive`): so
`H^*(X) = G(h(X))` as graded algebras. -/
structure IsMultiplicative [G.Monoidal] : Prop where
  /-- The unit of `H^*(X)` is the image of `1 ∈ F = G(𝟏)⁰` under `G(η) : G(𝟏) ⟶ G(h(X))`. -/
  iso_one : ∀ X : (SmoothProjective k).FullSubcategory,
    E.iso X 0 (S.H X).one =
      ((G.map η[GradedCategory.TwistedKaroubi.ofObj (R := ℚ)
          (GradedCompositionData.Obj.mk ((SmoothProjective.toSchemeCat k).obj X) :
            CorrespondenceCategory k)]) 0).hom
        ((Functor.LaxMonoidal.ε G 0).hom
          ((GradedObject.Monoidal.tensorUnit₀ (I := ℤ) (C := ModuleCat.{v} F)).inv.hom 1))
  /-- The cup product of `H^*(X)` is `G(h(X)) ⊗ G(h(X)) ⟶ G(h(X) ⊗ h(X)) ⟶ G(h(X))`, the second
  map being `G(μ)`. -/
  iso_mul : ∀ (X : (SmoothProjective k).FullSubcategory) (i j : ℤ) (a : (S.H X).piece i)
    (b : (S.H X).piece j),
    E.iso X (i + j) ((S.H X).mul i j a b) =
      ((G.map μ[GradedCategory.TwistedKaroubi.ofObj (R := ℚ)
          (GradedCompositionData.Obj.mk ((SmoothProjective.toSchemeCat k).obj X) :
            CorrespondenceCategory k)]) (i + j)).hom
        (((Functor.LaxMonoidal.μ G _ _) (i + j)).hom
          ((GradedObject.Monoidal.ιTensorObj
            (G.obj ((h k).obj (op ((SmoothProjective.toSchemeCat k).obj X))))
            (G.obj ((h k).obj (op ((SmoothProjective.toSchemeCat k).obj X)))) i j (i + j) rfl).hom
            (E.iso X i a ⊗ₜ E.iso X j b)))

end MotiveComparison

end PoincarePairingSetup

end Stacks.WeilCohomology

end
