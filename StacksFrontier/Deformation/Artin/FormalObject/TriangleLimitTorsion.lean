module

public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ConstantGroupSpaceH1Torsion
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackTrivialActionClass
public import StacksFrontier.Deformation.Artin.FormalObject.TriangleCompletion
public import StacksFrontier.RingTheory.NodalChart.Regularity

/-!
# Objects of `[Spec k/A]` over the limit of the triangle have torsion class

Let `A` be an abelian variety over a field `k` and `G` its group algebraic space over `Spec k`
(Stacks 043I). For an object `x` of `[Spec k/G]` over an object `U` of the big fppf site of
`Spec k` whose scheme is a two dimensional regular integral Noetherian scheme, the class of `x` in
`H¹(U, G)` has finite order (Stacks 0AF9 and 0AFA,
`AlgebraicGeometry.Space.GroupAlgebraicSpace.isOfFinAddOrder_h1_over_of_dim_two`). This file
discharges the size conditions of that statement, which hold in every big fppf site, and applies
it to the spectrum of the limit `R = K[x, y]^∧` of the thickenings of the triangle, a two
dimensional regular Noetherian domain (`Deformation.Artin.triangleCompletion`). This is the
assertion "torsors over the limit are torsion" of the discussion before Stacks 0CXX.

## Main results

* `AlgebraicGeometry.BigFppfSite.contains_spec_functionField`: the spectrum of the function
  field of an integral scheme in a big fppf site lies in the site.
* `AlgebraicGeometry.Space.GroupAlgebraicSpace.isOfFinAddOrder_h1_over_of_isRegular`: every class
  in `H¹(U, G)` has finite order when the scheme of `U` is a two dimensional regular integral
  Noetherian scheme, with no size hypothesis.
* `isOfFinAddOrder_quotientStackTrivialActionClass_of_iso_spec_triangleCompletion`, in the
  namespace `AlgebraicGeometry.Space.GroupAlgebraicSpace`: **the class of every object of
  `[Spec k/G]` over `Spec R` has finite order.**

## References

* [Stacks Project, Tag 0CXX](https://stacks.math.columbia.edu/tag/0CXX)
* [Stacks Project, Tag 0AF9](https://stacks.math.columbia.edu/tag/0AF9)
* [Stacks Project, Tag 0AFA](https://stacks.math.columbia.edu/tag/0AFA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

universe w u

namespace AlgebraicGeometry

/-- **The function field of an integral scheme of a big fppf site lies in the site**: its
spectrum is the spectrum of the residue field at the generic point. -/
theorem BigFppfSite.contains_spec_functionField (B : BigFppfSite.{u}) {W : Scheme.{u}}
    (hW : B.Contains W) [IsIntegral W] : B.Contains (Spec W.functionField) := by
  have hres := BigFppfSite.residueField_spec_contains B hW (genericPoint W)
  have : IsIso (W.residue (genericPoint W)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨RingHom.injective (W.residue (genericPoint W)).hom,
      W.residue_surjective (genericPoint W)⟩
  exact (Scheme.size_congr
    (Scheme.Spec.mapIso (asIso (W.residue (genericPoint W))).op)).symm.trans_lt hres

end AlgebraicGeometry

namespace AlgebraicGeometry.Space.GroupAlgebraicSpace

variable {𝒞 : BigFppfSite.{u}} {k : Type u} [Field k] {hk : 𝒞.Contains (Spec (.of k))}
  (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety k A] (hA : 𝒞.Contains A.left)
  [∀ V : BigFppfOver 𝒞 (Spec (.of k)) hk,
    HasSheafify ((BigFppfOver.topology 𝒞 _ hk).over V) AddCommGrpCat.{u}]
  [∀ V : BigFppfOver 𝒞 (Spec (.of k)) hk,
    HasExt.{w} (Sheaf ((BigFppfOver.topology 𝒞 _ hk).over V) AddCommGrpCat.{u})]
  [∀ V : BigFppfOver 𝒞 (Spec (.of k)) hk,
    ((BigFppfOver.topology 𝒞 _ hk).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : BigFppfOver 𝒞 (Spec (.of k)) hk,
    HasSheafify (BigFppfOver.topology 𝒞 (BigFppfOver.objScheme 𝒞 _ hk V)
      (BigFppfOver.contains_objScheme 𝒞 _ hk V)) AddCommGrpCat.{u}]
  [∀ V : BigFppfOver 𝒞 (Spec (.of k)) hk,
    HasExt.{w} (Sheaf (BigFppfOver.topology 𝒞 (BigFppfOver.objScheme 𝒞 _ hk V)
      (BigFppfOver.contains_objScheme 𝒞 _ hk V)) AddCommGrpCat.{u})]
  [∀ V : BigFppfOver 𝒞 (Spec (.of k)) hk,
    EnoughInjectives (Sheaf (BigFppfOver.topology 𝒞 (BigFppfOver.objScheme 𝒞 _ hk V)
      (BigFppfOver.contains_objScheme 𝒞 _ hk V)) AddCommGrpCat.{u})]

/-- **Every class in `H¹(U, G)` has finite order** when the scheme of `U` is a two dimensional
regular integral Noetherian scheme, for the group algebraic space `G` of an abelian variety `A`
over `k`. This is `isOfFinAddOrder_h1_over_of_dim_two` with its size conditions discharged: the
function field of the scheme of `U` and the base changes of `A` to it and to `U` lie in every
big fppf site containing `A` and `U`. -/
theorem isOfFinAddOrder_h1_over_of_isRegular (U : BigFppfOver 𝒞 (Spec (.of k)) hk)
    [IsIntegral (BigFppfOver.objScheme 𝒞 _ hk U)]
    [AlgebraicGeometry.IsNoetherian (BigFppfOver.objScheme 𝒞 _ hk U)]
    (hreg : IsRegular (BigFppfOver.objScheme 𝒞 _ hk U))
    (hdim : topologicalKrullDim (BigFppfOver.objScheme 𝒞 _ hk U) = (2 : WithBot ℕ∞))
    (c : Sheaf.H.{w} ((pointsSheaf (ofGroupScheme (hS := hk) A hA)).over U) 1) :
    IsOfFinAddOrder c := by
  have hK := BigFppfSite.contains_spec_functionField 𝒞 (BigFppfOver.contains_objScheme 𝒞 _ hk U)
  exact isOfFinAddOrder_h1_over_of_dim_two U A hA hK hreg hdim
    (Scheme.size_pullback_lt _ _ hA (BigFppfOver.contains_objScheme 𝒞 _ hk U))
    (Scheme.size_pullback_lt _ _ hA
      (BigFppfOver.contains_objScheme 𝒞 _ hk (genericPointOver U hK))) c

/-- **Every object of `[Spec k/G]` over the limit of the thickenings of the triangle has a class
of finite order.** Let `K` be a field and `R = K[x, y]^∧` the `xy(x + y - 1)`-adic completion,
the limit of the thickenings `K[x, y] ⧸ (xy(x + y - 1)) ^ (n + 1)`. For the group algebraic space
`G` of an abelian variety `A` over `k` and an object `x` of `[Spec k/G]` whose scheme is
`Spec R`, the class of `x` in `H¹` has finite order: `R` is a two dimensional regular Noetherian
domain, so Stacks 0AF9 and 0AFA apply. -/
theorem isOfFinAddOrder_quotientStackTrivialActionClass_of_iso_spec_triangleCompletion
    (K : Type u) [Field K]
    (x : (Stack.quotientStackOfAction ⟨baseS 𝒞 _ hk, isAlgebraicSpace_baseS 𝒞 _ hk⟩
      (ofGroupScheme (hS := hk) A hA).obj.X (𝟙_ (Over (baseS 𝒞 _ hk)))
      (ofGroupScheme (hS := hk) A hA).property (isAlgebraicSpace_baseS 𝒞 _ hk)).obj)
    (e : BigFppfOver.objScheme 𝒞 _ hk
        ((Stack.quotientStackOfAction ⟨baseS 𝒞 _ hk, isAlgebraicSpace_baseS 𝒞 _ hk⟩
          (ofGroupScheme (hS := hk) A hA).obj.X (𝟙_ (Over (baseS 𝒞 _ hk)))
          (ofGroupScheme (hS := hk) A hA).property (isAlgebraicSpace_baseS 𝒞 _ hk)).p.obj x) ≅
      Spec (.of (Deformation.Artin.triangleCompletion K))) :
    IsOfFinAddOrder (quotientStackTrivialActionClass (ofGroupScheme (hS := hk) A hA) x) := by
  let U := (Stack.quotientStackOfAction ⟨baseS 𝒞 _ hk, isAlgebraicSpace_baseS 𝒞 _ hk⟩
    (ofGroupScheme (hS := hk) A hA).obj.X (𝟙_ (Over (baseS 𝒞 _ hk)))
    (ofGroupScheme (hS := hk) A hA).property (isAlgebraicSpace_baseS 𝒞 _ hk)).p.obj x
  have : IsIntegral (BigFppfOver.objScheme 𝒞 _ hk U) := IsIntegral.of_isIso e.inv
  have : IsLocallyNoetherian (BigFppfOver.objScheme 𝒞 _ hk U) :=
    isLocallyNoetherian_of_isOpenImmersion e.hom
  have : CompactSpace (BigFppfOver.objScheme 𝒞 _ hk U) := (Scheme.homeoOfIso e).symm.compactSpace
  have : AlgebraicGeometry.IsNoetherian (BigFppfOver.objScheme 𝒞 _ hk U) := ⟨⟩
  refine isOfFinAddOrder_h1_over_of_isRegular A hA U
    (isRegular_of_iso e (Stacks.isRegular_spec_of_isRegularRing _)) ?_ _
  rw [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph]
  exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).trans
    (Deformation.Artin.ringKrullDim_triangleCompletion K)

end AlgebraicGeometry.Space.GroupAlgebraicSpace

end
