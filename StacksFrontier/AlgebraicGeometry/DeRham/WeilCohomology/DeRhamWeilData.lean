module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FirstChernClassData
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.GradedDeRhamCohomology
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.PullbackScalars
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.PullbackEvenDegreeRing
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.DeRhamCohomologyFirstChernClass
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.DeRhamFirstChernClassSquare

/-!
# The data (D0), (D1), (D2') of de Rham cohomology over a field

Let `k` be a field. Section 0FWC of the Stacks project takes, on the category of smooth projective
schemes over `k`, the following data in the sense of Weil Cohomology Theories, Section 0FID:

* (D0) the Tate line `F(1) = F = k`;
* (D1) the functor `X ↦ H^*_{dR}(X/k) = ⨁_{n ∈ 𝐙} H^n_{dR}(X/k)`, with the cup product of
  Section 50.4 (graded commutative by Tag 0FM3) and the pullback of Section 0FL6;
* (D2') the de Rham first Chern class `c₁^{dR} : Pic(X) ⟶ H^2_{dR}(X/k)` of Section 0FLE.

This file assembles them into `Stacks.WeilCohomology.FirstChernClassData k k`.

## Main definitions

* `Stacks.DeRhamWeil.scalarHom`: `k ⟶ Γ(X, p^{-1}𝒪_{Spec k})`, through which `k` acts on
  `H^n_{dR}(X/k)`.
* `Stacks.DeRhamWeil.cohomology`: `H^*_{dR}(X/k)`, a `𝐙`-graded `k`-algebra.
* `Stacks.DeRhamWeil.pullback`: the pullback `f^* : H^*_{dR}(Y/k) ⟶ H^*_{dR}(X/k)`, a map of
  `k`-algebras.
* `Stacks.DeRhamWeil.firstChernClass`: `c₁^{dR} : Pic(X) ⟶ H^2_{dR}(X/k)`.
* `Stacks.DeRhamWeil.deRhamFirstChernClassData`: **the data (D0), (D1), (D2') of de Rham
  cohomology**.

## References

* [Stacks Project, Section 0FWC](https://stacks.math.columbia.edu/tag/0FWC)
* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Section 0FL6](https://stacks.math.columbia.edu/tag/0FL6)
* [Stacks Project, Tag 0FM3](https://stacks.math.columbia.edu/tag/0FM3)
* [Stacks Project, Section 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry DirectSum
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.DeRhamWeil

variable {k : Type u} [Field k]

/-! ### Scalars -/

section Scalars

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- The global sections `Γ(X, p^{-1}𝒪_S)` of the base ring sheaf of the de Rham complex of
`p : X ⟶ S`, over which `H^n_{dR}(X/S)` is a module. -/
abbrev baseSectionRing : Type u :=
  (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf)).obj.obj (op ⊤)

/-- The map `Γ(S, 𝒪_S) ⟶ Γ(X, p^{-1}𝒪_S)`. -/
def baseScalarHom : Γ(S, ⊤) →+* baseSectionRing p :=
  (Scheme.Hom.inverseImageGlobalSections p).hom

/-- **The map on base scalars of a commutative square**: for `g' ≫ f = f' ≫ g`, the map
`Γ(X, f^{-1}𝒪_S) ⟶ Γ(X', f'^{-1}𝒪_{S'})` of the inverse-image ringed spaces is compatible with the
maps from `Γ(S, 𝒪_S)` and `Γ(S', 𝒪_{S'})`. -/
theorem globalRingHom_inverseImageBaseMap_baseScalarHom {X' S' : Scheme.{u}} (g' : X' ⟶ X)
    (f' : X' ⟶ S') (g : S' ⟶ S) (w : g' ≫ p = f' ≫ g) (a : Γ(S, ⊤)) :
    (Stacks.Cohomology.LerayCupPairing.globalRingHom
        (inverseImageBaseMap g' f' p g w)).hom (baseScalarHom p a) =
      baseScalarHom f' (g.appTop a) := by
  have h := congrArg (fun F => (Stacks.Cohomology.LerayCupPairing.globalRingHom F).hom a)
    (inverseImageBaseMap_comp_inverseImageBaseProjection g' f' p g w)
  exact h

end Scalars

/-- **`k` acting on de Rham cohomology over `k`**: `k = Γ(Spec k, 𝒪) ⟶ Γ(X, p^{-1}𝒪_{Spec k})`. -/
def scalarHom {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) : k →+* baseSectionRing p :=
  (baseScalarHom p).comp (Scheme.ΓSpecIso (.of k)).inv.hom

/-! ### The cohomology -/

variable (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- The de Rham complex package of `X ⟶ Spec k`. -/
abbrev algebras := Scheme.Hom.deRhamAlgebras X.obj.hom

/-- The de Rham differential of `X ⟶ Spec k`. -/
abbrev differential := AlgebraicGeometry.SheafOfModules.deRhamDifferential (algebras X)

/-- **`H^n_{dR}(X/k)`**, in the realization by derived global sections of modules in which the cup
product lives. -/
abbrev piece (n : ℤ) : Type u :=
  AlgebraicGeometry.SheafOfModules.deRhamPiece (algebras X) (differential X) n

/-- `H^n_{dR}(X/k)` as a `k`-module, through `scalarHom`. -/
instance (n : ℤ) : Module k (piece X n) :=
  Module.compHom _ (scalarHom X.obj.hom)

/-- The action of `c : k` on `H^n_{dR}(X/k)` is that of its image under `scalarHom`. -/
theorem smul_piece_def (c : k) {n : ℤ} (x : piece X n) :
    c • x = (scalarHom X.obj.hom c) • x :=
  rfl

/-- The cup product is `k`-linear in its first argument. -/
theorem cup_smul_left (c : k) (i j : ℤ) (x : piece X i) (y : piece X j) :
    AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup (algebras X) (differential X) i j
        (c • x) y =
      c • AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup (algebras X) (differential X) i j
        x y :=
  AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup_smul_left _ _ i j
    (scalarHom X.obj.hom c) x y

/-- The cup product is `k`-linear in its second argument. -/
theorem cup_smul_right (c : k) (i j : ℤ) (x : piece X i) (y : piece X j) :
    AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup (algebras X) (differential X) i j
        x (c • y) =
      c • AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup (algebras X) (differential X) i j
        x y :=
  AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup_smul_right _ _ i j
    (scalarHom X.obj.hom c) x y

/-- The pieces `H^n_{dR}(X/k)` form a graded `k`-algebra under the cup product. -/
instance : DirectSum.GAlgebra k (piece X) :=
  AlgebraicGeometry.SheafOfModules.deRhamGAlgebra (algebras X) (differential X)
    (cup_smul_left X) (cup_smul_right X)

/-- **`H^*_{dR}(X/k) = ⨁_{n ∈ 𝐙} H^n_{dR}(X/k)`**, a `𝐙`-graded `k`-algebra under the cup
product. -/
abbrev cohomology : Type u :=
  DirectSum ℤ (piece X)

/-- The degree-`n` part `H^n_{dR}(X/k)` of `H^*_{dR}(X/k)`. -/
abbrev grade (n : ℤ) : Submodule k (cohomology X) :=
  DirectSum.rangeGrading k (piece X) n

/-- A class of `H^n_{dR}(X/k)` lies in the degree-`n` part of `H^*_{dR}(X/k)`. -/
theorem of_mem_grade (n : ℤ) (x : piece X n) :
    DirectSum.of (piece X) n x ∈ grade X n :=
  (DirectSum.mem_rangeGrading k (piece X) n _).2 ⟨x, rfl⟩

/-- `H^*_{dR}(X/k)` is a graded algebra with respect to its degree-`n` parts `grade X n`. -/
instance gradedAlgebra : _root_.GradedAlgebra (grade X) where
  __ := DirectSum.rangeGradingDecomposition k (piece X)
  one_mem := of_mem_grade X 0 _
  mul_mem i j a b ha hb := by
    obtain ⟨x, rfl⟩ := (DirectSum.mem_rangeGrading k _ i a).1 ha
    obtain ⟨y, rfl⟩ := (DirectSum.mem_rangeGrading k _ j b).1 hb
    rw [DirectSum.of_mul_of]
    exact of_mem_grade X (i + j) _

/-- **The Koszul sign rule** `a ∪ b = (-1)^{ij} b ∪ a` on `H^*_{dR}(X/k)` (Tag 0FM3). -/
theorem graded_comm (i j : ℤ) (a b : cohomology X) (ha : a ∈ grade X i) (hb : b ∈ grade X j) :
    a * b = (Int.negOnePow (i * j) : ℤ) • (b * a) :=
  AlgebraicGeometry.SheafOfModules.gradedDeRhamCohomology_mul_comm _ _ k i j a b ha hb

/-! ### Pullback -/

variable {X} {Y Z : (SmoothProjectiveScheme k).FullSubcategory}

/-- The square formed by `f : X ⟶ Y` over `Spec k` and the identity of `Spec k` commutes. -/
theorem square_w (f : X ⟶ Y) :
    (toScheme k).map f ≫ Y.obj.hom = X.obj.hom ≫ 𝟙 (Spec (.of k)) := by
  rw [Category.comp_id]
  exact SmoothProjectiveScheme.w f

/-- The pullback `f^* : H^n_{dR}(Y/k) ⟶ H^n_{dR}(X/k)` in one degree. -/
def pullbackPiece (f : X ⟶ Y) (n : ℤ) : piece Y n →+ piece X n :=
  deRhamPullbackSquare ((toScheme k).map f) X.obj.hom Y.obj.hom (𝟙 _) (square_w f) n

/-- The pullback `f^*` on `H^n_{dR}` is `k`-linear. -/
theorem pullbackPiece_smul (f : X ⟶ Y) (n : ℤ) (c : k) (z : piece Y n) :
    pullbackPiece f n (c • z) = c • pullbackPiece f n z := by
  refine (deRhamPullbackSquare_smul _ _ _ _ (square_w f) n (scalarHom Y.obj.hom c) z).trans ?_
  exact congrArg (· • _) (globalRingHom_inverseImageBaseMap_baseScalarHom Y.obj.hom _ _ _
    (square_w f) _)

/-- The pullback `f^*` is compatible with the cup product. -/
theorem pullbackPiece_cup (f : X ⟶ Y) (i j : ℤ) (x : piece Y i) (y : piece Y j) :
    pullbackPiece f (i + j)
        (AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup (algebras Y) (differential Y) i j
          x y) =
      AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup (algebras X) (differential X) i j
        (pullbackPiece f i x) (pullbackPiece f j y) :=
  deRhamPullbackSquare_cup _ _ _ _ (square_w f) i j x y

/-- The pullback `f^*` sends the unit class of `H^0_{dR}(Y/k)` to that of `H^0_{dR}(X/k)`. -/
theorem pullbackPiece_one (f : X ⟶ Y) :
    pullbackPiece f 0 (AlgebraicGeometry.SheafOfModules.deRhamOneClass (algebras Y)
        (differential Y)) =
      AlgebraicGeometry.SheafOfModules.deRhamOneClass (algebras X) (differential X) :=
  deRhamPullbackSquare_one _ _ _ _ (square_w f)

/-- The pullback `f^* : H^*_{dR}(Y/k) ⟶ H^*_{dR}(X/k)` as a ring homomorphism. -/
def pullbackRingHom (f : X ⟶ Y) : cohomology Y →+* cohomology X :=
  DirectSum.toSemiring (fun n => (DirectSum.of (piece X) n).comp (pullbackPiece f n))
    (by
      exact (congrArg (DirectSum.of (piece X) 0) (pullbackPiece_one f)).trans rfl)
    (fun {i j} x y => by
      change DirectSum.of (piece X) (i + j) (pullbackPiece f (i + j)
          (AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup _ _ i j x y)) =
        DirectSum.of (piece X) i (pullbackPiece f i x) *
          DirectSum.of (piece X) j (pullbackPiece f j y)
      rw [pullbackPiece_cup, DirectSum.of_mul_of]
      rfl)

/-- On the degree-`n` summand, `pullbackRingHom f` is `pullbackPiece f n`. -/
theorem pullbackRingHom_of (f : X ⟶ Y) (n : ℤ) (x : piece Y n) :
    pullbackRingHom f (DirectSum.of (piece Y) n x) =
      DirectSum.of (piece X) n (pullbackPiece f n x) :=
  DirectSum.toSemiring_of _ _ _ _ _

/-- **The pullback `f^* : H^*_{dR}(Y/k) ⟶ H^*_{dR}(X/k)`** of Section 0FL6, a map of
`k`-algebras. -/
def pullback (f : X ⟶ Y) : cohomology Y →ₐ[k] cohomology X where
  __ := pullbackRingHom f
  commutes' c := by
    rw [DirectSum.algebraMap_apply, DirectSum.algebraMap_apply]
    refine (pullbackRingHom_of f 0 _).trans ?_
    change DirectSum.of (piece X) 0 (pullbackPiece f 0 (c • _)) = _
    rw [pullbackPiece_smul, pullbackPiece_one]
    rfl

/-- On the degree-`n` summand, `pullback f` is `pullbackPiece f n`. -/
theorem pullback_of (f : X ⟶ Y) (n : ℤ) (x : piece Y n) :
    pullback f (DirectSum.of (piece Y) n x) = DirectSum.of (piece X) n (pullbackPiece f n x) :=
  pullbackRingHom_of f n x

/-- Two `k`-algebra maps out of `H^*_{dR}(Y/k)` agreeing on every summand `H^n_{dR}(Y/k)` are
equal. -/
theorem pullback_ext {f g : cohomology Y →ₐ[k] cohomology X}
    (h : ∀ n (x : piece Y n), f (DirectSum.of (piece Y) n x) = g (DirectSum.of (piece Y) n x)) :
    f = g :=
  AlgHom.coe_ringHom_injective (DirectSum.ringHom_ext h)

/-- The pullback along the identity is the identity. -/
theorem pullback_id (X : (SmoothProjectiveScheme k).FullSubcategory) :
    pullback (𝟙 X) = AlgHom.id k (cohomology X) := by
  refine pullback_ext fun n x => ?_
  rw [pullback_of]
  exact congrArg (DirectSum.of (piece X) n)
    ((deRhamPullbackSquare_congr X.obj.hom X.obj.hom rfl rfl (square_w (𝟙 X)) (by simp) n
      x).trans (deRhamPullbackSquare_id X.obj.hom (by simp) n x))

/-- Pullback is contravariantly functorial: `(f ≫ g)^* = f^* ∘ g^*`. -/
theorem pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback (f ≫ g) = (pullback f).comp (pullback g) := by
  refine pullback_ext fun n x => ?_
  rw [AlgHom.comp_apply, pullback_of, pullback_of, pullback_of]
  refine congrArg (DirectSum.of (piece X) n) ?_
  refine (deRhamPullbackSquare_congr X.obj.hom Z.obj.hom ((toScheme k).map_comp f g)
    (Category.comp_id (𝟙 _)).symm (square_w (f ≫ g))
    (by rw [Category.assoc, SmoothProjectiveScheme.w g, SmoothProjectiveScheme.w f,
      Category.comp_id, Category.comp_id]) n x).trans ?_
  exact (deRhamPullbackSquare_comp _ _ _ _ (square_w g) _ _ (𝟙 _) (square_w f) _ n x).symm

/-- The pullback `f^*` preserves the degree. -/
theorem pullback_mem_grade (f : X ⟶ Y) (n : ℤ) (a : cohomology Y) (ha : a ∈ grade Y n) :
    pullback f a ∈ grade X n := by
  obtain ⟨x, rfl⟩ := (DirectSum.mem_rangeGrading k _ n a).1 ha
  rw [pullback_of]
  exact of_mem_grade X n _

/-! ### The first Chern class -/

variable (X)

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

/-- **`c₁^{dR} : Pic(X) ⟶ H^2_{dR}(X/k)`** (Section 0FLE): logarithmic differentiation on
`Pic(X) = H^1(X, 𝒪_X^*)`, read in the realization of `H^2_{dR}` in which the cup product lives. -/
def firstChernClassPiece : ((toScheme k).obj X).picardGroup →+ piece X 2 :=
  ((AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (algebras X)
      (differential X) 2).hom.hom).comp
    ((AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelian (algebras X)
      (differential X)).comp
      (Stacks.GluePicard.picardModelAddEquiv ((toScheme k).obj X).toRingedSpace).toAddMonoidHom)

/-- The coordinate `H^*(X)(1) = H^*(X) ⊗ k ≅ H^*(X)` on the twist by the trivial line `k`. -/
def untwist (V : Type u) [AddCommGroup V] [Module k V] (n : ℤ) : tateTwist k k V n ≃ₗ[k] V :=
  tateTwistCoordinates (LinearEquiv.refl k k) n

/-- **The de Rham first Chern class** `c₁^{dR} : Pic(X) ⟶ H^2_{dR}(X/k)(1)`, the twist by the
trivial line `F(1) = k` read through its canonical coordinate. -/
def firstChernClass : ((toScheme k).obj X).picardGroup →+ tateTwist k k (cohomology X) 1 :=
  ((untwist (cohomology X) 1).symm.toLinearMap.toAddMonoidHom).comp
    (((DirectSum.of (piece X) 2)).comp (firstChernClassPiece X))

/-- The first Chern class `firstChernClass X L` lies in the twist of the degree-`2` part
`H^2_{dR}(X/k)(1)`. -/
theorem firstChernClass_mem (L : ((toScheme k).obj X).picardGroup) :
    firstChernClass X L ∈
      LinearMap.range (tateTwistMap (L := k) (grade X 2).subtype 1) := by
  refine ⟨(untwist (grade X 2) 1).symm ⟨_, of_mem_grade X 2 (firstChernClassPiece X L)⟩, ?_⟩
  apply (untwist (cohomology X) 1).injective
  rw [untwist, tateTwistCoordinates_map, ← untwist, LinearEquiv.apply_symm_apply]
  exact ((untwist (cohomology X) 1).apply_symm_apply _).symm

/-! ### The data -/

variable (k) in
/-- **The data (D0), (D1), (D2') of de Rham cohomology** (Section 0FWC): the Tate line `k`, the
functor `X ↦ H^*_{dR}(X/k)` with cup product and pullback, and the de Rham first Chern class. -/
def deRhamFirstChernClassData : FirstChernClassData k k where
  tate := k
  finrank_tate := Module.finrank_self k
  H := cohomology
  grade := grade
  graded_comm := graded_comm
  pull := pullback
  pull_id := pullback_id
  pull_comp := pullback_comp
  pull_grade := pullback_mem_grade
  c₁ := firstChernClass
  c₁_mem := firstChernClass_mem

end Stacks.DeRhamWeil

end
