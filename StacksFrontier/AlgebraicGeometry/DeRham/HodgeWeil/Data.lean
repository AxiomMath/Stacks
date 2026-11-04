module

public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamWeilData
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FirstChernClassData
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.PullbackCup
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.FirstChernClass

/-!
# The data (D0), (D1), (D2') of Hodge cohomology over a field

Remark 0FWE of the Stacks project considers, on the category of smooth projective schemes over a
field `k`, Hodge cohomology `X ↦ H^*_{Hodge}(X/k) = ⨁_n ⨁_{p + q = n} H^q(X, Ω^p_{X/k})` equipped
with the Hodge first Chern class `c₁^{Hodge}`, as data in the sense of Weil Cohomology Theories,
Section 0FID:

* (D0) the Tate line `F(1) = F = k`;
* (D1) the functor `X ↦ H^*_{Hodge}(X/k)`, with the cup product of Section 50.5 (graded
  commutative by Tag 0FM5) and the pullback maps;
* (D2') `c₁^{Hodge} : Pic(X) ⟶ H^1(X, Ω^1_{X/k}) ⊂ H^2_{Hodge}(X/k)`.

This file assembles them into `Stacks.WeilCohomology.FirstChernClassData k k`.

## Main definitions

* `Stacks.HodgeWeil.hodgeScalarsOverField`: `k ⟶ Γ(X, p⁻¹𝒪_{Spec k})`, through which `k` acts
  on Hodge cohomology of a `k`-scheme.
* `Stacks.HodgeWeil.hodgeFirstChernClassTw`: `c₁^{Hodge}` with values in the twist
  `H^*_{Hodge}(X/k)(1)` by the trivial line `k`.
* `Stacks.HodgeWeil.hodgeFirstChernClassData`: **the data (D0), (D1), (D2') of Hodge
  cohomology**.

## References

* [Stacks Project, Tag 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0FM5](https://stacks.math.columbia.edu/tag/0FM5)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite Stacks.WeilCohomology
open Stacks.WeilCohomology.SmoothProjectiveScheme

universe u

namespace Stacks.HodgeWeil

variable {k : Type u} [Field k]

variable (k) in
/-- `k ⟶ Γ(Spec k, 𝒪)`, the inverse of the canonical isomorphism. -/
def specScalars : k →+* (Spec (CommRingCat.of k)).sheaf.obj.obj (op ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

/-- The scalars `k ⟶ Γ(X, p⁻¹𝒪_{Spec k})` of a `k`-scheme `p : X ⟶ Spec k`. -/
abbrev hodgeScalarsOverField {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) :
    k →+* hodgeBaseRing p :=
  hodgeScalars (specScalars k) p

variable (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- `H^*_{Hodge}(X/k)` of a smooth projective scheme over `k`. -/
abbrev hodgeAlgebraOf : Type u := hodgeAlgebra (formsAlgebras X.obj.hom)

/-- `H^*_{Hodge}(X/k)` is a `k`-algebra through `Stacks.HodgeWeil.hodgeScalarsOverField`. -/
instance : Algebra k (hodgeAlgebraOf X) :=
  hodgeAlgebraAlgebra (formsAlgebras X.obj.hom) (hodgeScalarsOverField X.obj.hom)

/-- The grading of `H^*_{Hodge}(X/k)` by total degree. -/
abbrev hodgeGradeOf (n : ℤ) : Submodule k (hodgeAlgebraOf X) :=
  hodgeGrade (formsAlgebras X.obj.hom) (hodgeScalarsOverField X.obj.hom) n

/-- `H^*_{Hodge}(X/k)` is a graded algebra for the grading by total degree. -/
instance : _root_.GradedAlgebra (hodgeGradeOf X) :=
  hodgeGradedAlgebra (formsAlgebras X.obj.hom) (hodgeScalarsOverField X.obj.hom)

variable {X} {Y Z : (SmoothProjectiveScheme k).FullSubcategory}

/-- A morphism `f : X ⟶ Y` of smooth projective `k`-schemes commutes with the structure morphisms
to `Spec k`. -/
theorem hodgeSquare_w (f : X ⟶ Y) :
    f.hom.left ≫ Y.obj.hom = X.obj.hom ≫ 𝟙 (Spec (.of k)) :=
  (Over.w f.hom).trans (Category.comp_id _).symm

/-- The pullback `f^* : H^*_{Hodge}(Y/k) ⟶ H^*_{Hodge}(X/k)`, a map of `k`-algebras. -/
def hodgePullbackOf (f : X ⟶ Y) : hodgeAlgebraOf Y →ₐ[k] hodgeAlgebraOf X :=
  hodgeAlgebraPullbackOverBase f.hom.left (specScalars k)
    Y.obj.hom X.obj.hom (hodgeSquare_w f)

/-- The pullback along the identity is the identity. -/
theorem hodgePullbackOf_id (X : (SmoothProjectiveScheme k).FullSubcategory) :
    hodgePullbackOf (𝟙 X) = AlgHom.id k (hodgeAlgebraOf X) :=
  hodgeAlgebraPullbackOverBase_id (specScalars k) X.obj.hom (hodgeSquare_w (𝟙 X))

/-- The pullback along a composite is the composite of the pullbacks: `(g ∘ f)^* = f^* ∘ g^*`. -/
theorem hodgePullbackOf_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    hodgePullbackOf (f ≫ g) = (hodgePullbackOf f).comp (hodgePullbackOf g) :=
  hodgeAlgebraPullbackOverBase_comp g.hom.left
    (specScalars k) Z.obj.hom Y.obj.hom X.obj.hom
    f.hom.left (hodgeSquare_w g) (hodgeSquare_w f) (hodgeSquare_w (f ≫ g))

/-- The pullback `f^*` preserves the total degree. -/
theorem hodgePullbackOf_mem_grade (f : X ⟶ Y) (n : ℤ) (a : hodgeAlgebraOf Y)
    (ha : a ∈ hodgeGradeOf Y n) : hodgePullbackOf f a ∈ hodgeGradeOf X n :=
  hodgeAlgebraPullbackOverBase_mem_hodgeGrade f.hom.left
    (specScalars k) Y.obj.hom X.obj.hom (hodgeSquare_w f) n a ha

/-! ### The first Chern class -/

variable (X)

/-- The bidegree `(1, 1)` of `H^1(X, Ω^1)` inside total degree `2`. -/
def bidegreeOneOne : HodgeBidegreeInt 2 := ⟨(1, 1), rfl⟩

/-- `c₁^{Hodge} : Pic(X) ⟶ H^2_{Hodge}(X/k)`: the Hodge first Chern class in
`H^1(X, Ω^1_{X/k})`, as a class of total degree `2`. -/
def hodgeFirstChernClassPiece :
    ((toScheme k).obj X).picardGroup →+ hodgePiece (formsAlgebras X.obj.hom) 2 :=
  (DirectSum.of (fun i : HodgeBidegreeInt 2 =>
      (AlgebraicGeometry.SheafOfModules.hodgeCohomologyComponent (formsAlgebras X.obj.hom)
        i.1.1 (i.1.2 : ℤ) : Type u)) bidegreeOneOne).comp
    (hodgeFirstChernClassModule X.obj.hom)

/-- **The Hodge first Chern class** `c₁^{Hodge} : Pic(X) ⟶ H^2_{Hodge}(X/k)(1)`, the twist by
the trivial line `F(1) = k` read through its canonical coordinate. -/
def hodgeFirstChernClassTw :
    ((toScheme k).obj X).picardGroup →+ tateTwist k k (hodgeAlgebraOf X) 1 :=
  ((Stacks.DeRhamWeil.untwist (k := k) (hodgeAlgebraOf X) 1).symm.toLinearMap.toAddMonoidHom).comp
    ((DirectSum.of (hodgePiece (formsAlgebras X.obj.hom)) 2).comp
      (hodgeFirstChernClassPiece X))

/-- The Hodge first Chern class `c₁^{Hodge}(L)` lies in the image of the twist
`H^2_{Hodge}(X/k)(1)` of the degree-`2` part. -/
theorem hodgeFirstChernClassTw_mem (L : ((toScheme k).obj X).picardGroup) :
    hodgeFirstChernClassTw X L ∈
      LinearMap.range (tateTwistMap (L := k) (hodgeGradeOf X 2).subtype 1) := by
  let a : hodgeGradeOf X 2 := ⟨_, of_mem_hodgeGrade _ _ 2 (hodgeFirstChernClassPiece X L)⟩
  refine ⟨(Stacks.DeRhamWeil.untwist (k := k) (hodgeGradeOf X 2) 1).symm a, ?_⟩
  apply (Stacks.DeRhamWeil.untwist (k := k) (hodgeAlgebraOf X) 1).injective
  refine (tateTwistCoordinates_map (F := k) (L := k) (LinearEquiv.refl k k) 1
    (hodgeGradeOf X 2).subtype _).trans ?_
  have h2 := (Stacks.DeRhamWeil.untwist (k := k) (hodgeGradeOf X 2) 1).apply_symm_apply a
  exact (congrArg Subtype.val h2).trans (LinearEquiv.apply_symm_apply _ _).symm

/-! ### The data -/

variable (k) in
/-- **The data (D0), (D1), (D2') of Hodge cohomology** (Stacks Remark 0FWE): the Tate line `k`,
the functor `X ↦ H^*_{Hodge}(X/k)` with cup product and pullback, and the Hodge first Chern
class. -/
def hodgeFirstChernClassData : FirstChernClassData k k where
  tate := k
  finrank_tate := Module.finrank_self k
  H := hodgeAlgebraOf
  grade := hodgeGradeOf
  graded_comm X := hodgeAlgebra_graded_comm (formsAlgebras X.obj.hom)
    (hodgeScalarsOverField X.obj.hom)
  pull := hodgePullbackOf
  pull_id := hodgePullbackOf_id
  pull_comp := hodgePullbackOf_comp
  pull_grade := hodgePullbackOf_mem_grade
  c₁ := hodgeFirstChernClassTw
  c₁_mem := hodgeFirstChernClassTw_mem

end Stacks.HodgeWeil

end
