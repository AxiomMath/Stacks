module

public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureQuotientChart
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalRepresentableSource
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteDMEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningOpenImmersionIsomorphism

/-!
# A quotient chart through every point of a quasi-DM stack with separated diagonal

The first part of the proofs of **Stacks 0DU3** and **Stacks 0DU4**: for an algebraic stack `𝒳`
which is quasi-DM with separated diagonal and a point `x ∈ |𝒳|`, there is an affine scheme `U`
with a flat, locally finitely presented, locally quasi-finite chart `U ⟶ 𝒳` through `x`
(**Stacks 06MF**); replacing `𝒳` by the open substack of the image of `U` (**Stacks 04XL**,
**06FJ**) the chart becomes surjective, `R = U ×_𝒳 U` is a scheme (**Stacks 03XX**) and
`[U/R] ⟶ 𝒳` is an open immersion onto that open substack (**Stacks 04WY**). The result is a
`AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid` of `𝒳` through whose quotient
stack `x` factors.

## Main results

* `AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid.compOpenSubstack`: a quotient chart
  of an open substack is a quotient chart of the stack.
* `AlgebraicGeometry.Stack.EtaleLocalStructure.exists_chartGroupoid`: the quotient chart through
  a point.
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack.EtaleLocalStructure

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A quotient chart of an open substack is a quotient chart of the stack**: the inclusion of an
open substack is representable, étale and fully faithful. -/
noncomputable def ChartGroupoid.compOpenSubstack {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (𝒳' : OpenSubstack 𝒳) (K : ChartGroupoid B S hS 𝒳'.toAlgebraicStack) :
    ChartGroupoid B S hS 𝒳 where
  U := K.U
  V := K.V
  s := K.s
  t := K.t
  c := K.c
  hG := K.hG
  isAffine_U := K.isAffine_U
  flat_s := K.flat_s
  lfp_s := K.lfp_s
  flat_t := K.flat_t
  lfp_t := K.lfp_t
  separated_s := K.separated_s
  separated_t := K.separated_t
  lft_s := K.lft_s
  lft_t := K.lft_t
  lqf_s := K.lqf_s
  alg := K.alg
  map := K.map ≫ 𝒳'.inclusion B S hS
  etale := isRelativelyEtale_comp B S hS _ _ K.etale
    (isRelativelyEtale_of_isOpenImmersion B S hS (𝒳'.inclusion B S hS).hom
      𝒳'.isOpenImmersion.1 𝒳'.isOpenImmersion.2)
  full := by
    have := K.full
    change (CatFiberedInGroupoids.homFunctor K.map.hom ⋙
      (𝒳'.inclusion B S hS).hom.hom.toFunctor).Full
    infer_instance
  faithful := by
    have := K.faithful
    change (CatFiberedInGroupoids.homFunctor K.map.hom ⋙
      (𝒳'.inclusion B S hS).hom.hom.toFunctor).Faithful
    infer_instance

/-- The points of the composite chart. -/
theorem ChartGroupoid.pointsMap_compOpenSubstack {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (𝒳' : OpenSubstack 𝒳) (K : ChartGroupoid B S hS 𝒳'.toAlgebraicStack)
    (z : Space.points B S hS (yoneda.obj K.U)) :
    AlgebraicStacks.pointsMap B S hS (K.compOpenSubstack 𝒳').map ((K.compOpenSubstack 𝒳').point z) =
      AlgebraicStacks.pointsMap B S hS (𝒳'.inclusion B S hS)
        (AlgebraicStacks.pointsMap B S hS K.map (K.point z)) :=
  congrFun (AlgebraicStacks.pointsMap_comp B S hS K.map (𝒳'.inclusion B S hS)) _

/-- **A quotient chart through every point of a quasi-DM stack with separated diagonal.** For an
algebraic stack `𝒳` over `S` which is quasi-DM (Stacks 050D) with separated diagonal `Δ_{𝒳/S}`
(Stacks 04XB) and a point `x ∈ |𝒳|`, there are a quotient chart of `𝒳` and a point of its object
scheme whose image in `|𝒳|` is `x`. -/
theorem exists_chartGroupoid (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hQ : AlgebraicStacks.IsAbsolutelyQuasiDM B S hS B.contains_terminal 𝒳)
    (hΔ : Stack.IsSeparated.{u, u, u + 1} B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (structureMorphism B S hS 𝒳).hom))
    (x : AlgebraicStacks.points B S hS 𝒳) :
    ∃ (K : ChartGroupoid B S hS 𝒳) (z : Space.points B S hS (yoneda.obj K.U)),
      AlgebraicStacks.pointsMap B S hS K.map (K.point z) = x := by
  obtain ⟨U, f, hU, hflat, hlfp, hlqf, hx⟩ :=
    exists_isAffine_chart B S hS B.contains_terminal 𝒳 hQ x
  let 𝒳' := imageSubstack f hflat hlfp
  have hrepι : IsRepresentableByAlgebraicSpaces B S hS (𝒳'.inclusion B S hS).hom.hom :=
    𝒳'.isOpenImmersion.1
  have hQ' : IsQuasiDMOver B S hS 𝒳'.toAlgebraicStack :=
    (AlgebraicStacks.isAbsolutelyQuasiDM_iff_isQuasiDMOver B S hS B.contains_terminal _).1
      (AlgebraicStacks.isAbsolutelyQuasiDM_of_isMonomorphism B S hS B.contains_terminal
        (𝒳'.inclusion B S hS)
        (AlgebraicStacks.isMonomorphism_of_isOpenImmersion B S hS _ 𝒳'.isOpenImmersion) hQ)
  have hΔ' := AlgebraicStacks.isSeparated_relativeDiagonal_structureMorphism_of_isRepresentable
    B S hS (𝒳'.inclusion B S hS) hrepι hΔ
  have := hU
  obtain ⟨K', hK'⟩ := exists_chartGroupoid_of_isSurjective (imageChart f hflat hlfp)
    (@isAffineOpen_top _ hU) (isSurjective_imageChart f hflat hlfp)
    (isFlat_imageChart f hflat hlfp) (isLocallyOfFinitePresentation_imageChart f hflat hlfp)
    (isLocallyQuasiFinite_imageChart f hflat hlfp hlqf) hQ' hΔ'
  obtain ⟨p, hp⟩ := exists_point_imageChart f hflat hlfp x hx
  obtain ⟨z, hz⟩ := hK' p
  refine ⟨K'.compOpenSubstack 𝒳', z, ?_⟩
  rw [ChartGroupoid.pointsMap_compOpenSubstack, hz, ← hp]
  exact (congrFun (AlgebraicStacks.pointsMap_comp B S hS _ _) p).symm

end AlgebraicGeometry.Stack.EtaleLocalStructure

end
