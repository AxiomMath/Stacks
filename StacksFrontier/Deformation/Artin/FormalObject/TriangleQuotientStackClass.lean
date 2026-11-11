module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.GroupAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackTrivialActionCechClass
public import StacksFrontier.Deformation.Artin.FormalObject.TriangleQuotientStackNonTorsion

/-!
# The first cohomology class of `ξ_0` has infinite order

Let `A` be a nonzero abelian variety over an infinite field `k` and let `ξ_0` be the object of
`[Spec(k)/A]` over the reduced triangle glued along the generic point of `A`
(`Deformation.Artin.triangleObject`). This file proves that its class in
`H¹_fppf(X_0, A)`, the class of the fppf `A`-torsor it corresponds to by Stacks 04WM
(`AlgebraicGeometry.Space.quotientStackTrivialActionClass`), has infinite order.

The class map of `[S/G]` for a commutative group algebraic space `G` is Čech-compatible
(`Deformation.Artin.isCechCompatible_quotientStackTrivialActionClass`): an object presented on a
covering by a descent datum represented by a Čech cocycle `c` has a class of finite order only
if `c` is torsion. A descent datum represented by `c` is isomorphic to the descent datum built
from `c` itself (`CategoryTheory.Functor.Rigidification.isoOfIsRepresentedBy`), and for that one
this is `AlgebraicGeometry.Space.isTorsionClass_of_isOfFinAddOrder_quotientStackTrivialActionClass`.
Combined with `Deformation.Artin.not_isOfFinAddOrder_triangleObject` this gives the result.

## Main results

* `Deformation.Artin.isCechCompatible_quotientStackTrivialActionClass`: the class map of a
  classifying stack is Čech-compatible.
* `Deformation.Artin.not_isOfFinAddOrder_quotientStackTrivialActionClass_triangleObject`: the
  class of `ξ_0` in `H¹_fppf(X_0, A)` has infinite order.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Space
open scoped MonoidalCategory

universe w u

namespace Deformation.Artin

open CategoryTheory.Functor

section CechCompatible

variable {k : Type u} [Field k] {𝒞 : BigFppfSite.{u}} {hk : 𝒞.Contains (Spec (.of k))}
  (G : GroupAlgebraicSpace 𝒞 (Spec (.of k)) hk (baseS 𝒞 _ hk) (isAlgebraicSpace_baseS 𝒞 _ hk))
  [G.IsCommutative]
  [∀ U : BigFppfOver 𝒞 (Spec (.of k)) hk,
    HasSheafify ((BigFppfOver.topology 𝒞 (Spec (.of k)) hk).over U) AddCommGrpCat.{u}]
  [∀ U : BigFppfOver 𝒞 (Spec (.of k)) hk,
    HasExt.{w} (Sheaf ((BigFppfOver.topology 𝒞 (Spec (.of k)) hk).over U) AddCommGrpCat.{u})]
  [∀ U : BigFppfOver 𝒞 (Spec (.of k)) hk,
    ((BigFppfOver.topology 𝒞 (Spec (.of k)) hk).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The class map of a classifying stack is Čech-compatible.** For a commutative group
algebraic space `G` over `Spec k`, the class in `H¹(T, G)` of an object of `[Spec(k)/G]` over
`T` (Stacks 04WM and 03AJ) has finite order only if every Čech cocycle representing a
presenting descent datum of the object on an fppf covering of `T` is torsion. -/
theorem isCechCompatible_quotientStackTrivialActionClass :
    IsCechCompatible (M := fun T ↦ Sheaf.H.{w} ((GroupAlgebraicSpace.pointsSheaf G).over T) 1) G
      (quotientStackTrivialActionClass.{w} G) := by
  intro T 𝒰 h𝒰 x D c hD ⟨e⟩ hx
  let ρ := trivialActionRigidification G
  have hD' := ρ.isRepresentedBy_descentDatumOfCocycle (fun i ↦ trivialActionPoint G (𝒰.X i)) c
  let φ := ρ.isoOfIsRepresentedBy hD hD' (fun _ ↦ 1) (fun Y i₁ i₂ f₁ f₂ _ ↦ by
    simp [FamilyCocycle.twist_val])
  exact isTorsionClass_of_isOfFinAddOrder_quotientStackTrivialActionClass 𝒰 h𝒰 x c
    (e ≪≫ (Stack.presentingDescentFunctor (baseTrivialActionGroupoid G) 𝒰).mapIso φ) hx

end CechCompatible

section Triangle

variable {k : Type u} [Field k] {𝒞 : BigFppfSite.{u}} {hk : 𝒞.Contains (Spec (.of k))}
  {A : Over (Spec (.of k))} [GrpObj A] [IsAbelianVariety k A] (hA : 𝒞.Contains A.left)
  (hRA : ∀ n : ℕ, 𝒞.Contains (Spec (.of (triangleLevel A.left.functionField n))))
  [∀ U : BigFppfOver 𝒞 (Spec (.of k)) hk,
    HasSheafify ((BigFppfOver.topology 𝒞 (Spec (.of k)) hk).over U) AddCommGrpCat.{u}]
  [∀ U : BigFppfOver 𝒞 (Spec (.of k)) hk,
    HasExt.{w} (Sheaf ((BigFppfOver.topology 𝒞 (Spec (.of k)) hk).over U) AddCommGrpCat.{u})]
  [∀ U : BigFppfOver 𝒞 (Spec (.of k)) hk,
    ((BigFppfOver.topology 𝒞 (Spec (.of k)) hk).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The group algebraic space of an abelian variety is commutative. -/
instance isCommutative_siteGroupSpace : (siteGroupSpace (hk := hk) A hA).IsCommutative :=
  GroupAlgebraicSpace.isCommutative_ofGroupScheme_of_isAbelianVariety A hA

/-- **The class of `ξ_0` has infinite order.** Let `A` be a nonzero abelian variety over an
infinite field `k` and `K = k(A)`. The object `ξ_0` of `[Spec(k)/A]` over the reduced triangle
`X_0` over `K`, glued along the generic point of `A`, has a class of infinite order in
`H¹_fppf(X_0, A)`: the class of the fppf `A`-torsor it corresponds to by Stacks 04WM. -/
theorem not_isOfFinAddOrder_quotientStackTrivialActionClass_triangleObject [Infinite k]
    (hdim : 1 ≤ Stacks.Groupoids.abelianVarietyDimension A) :
    letI := functionFieldAlgebra A
    ¬ IsOfFinAddOrder (quotientStackTrivialActionClass.{w} (siteGroupSpace A hA)
      (triangleObject A.left.functionField 𝒞 hk hRA hA (genericPointOverField A) 0).1) :=
  not_isOfFinAddOrder_triangleObject hA hRA hdim _
    (isCechCompatible_quotientStackTrivialActionClass (siteGroupSpace A hA))

end Triangle

end Deformation.Artin

end
