module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesRefinement
public import StacksFrontier.CategoryTheory.Sites.Stack.EffectiveDescentRefinement
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge

/-!
# The category of smooth lifts is a stack in groupoids (Stacks 0CJU)

Let `ι : 𝒳 ⟶ 𝒳'` be a thickening of algebraic stacks, `W` an algebraic space and `x : W ⟶ 𝒳` a
smooth 1-morphism. The category `p : 𝒞 ⟶ W_{spaces, étale}` of smooth lifts of Stacks 0CJP is a
stack in groupoids over the spaces-étale site of `W`.

## Main results

* `AlgebraicGeometry.Stack.EtaleSmoothLift.isStack_proj`: `p` is a stack (the three conditions
  of Stacks 026F).
* `AlgebraicGeometry.Stack.EtaleSmoothLift.isStackInGroupoids_proj`: **Stacks 0CJU**, `p` is a
  stack in groupoids (the three conditions of Stacks 02ZI), for covering families indexed by an
  arbitrary universe.

## Proof

Condition (1) of Stacks 02ZI is `AlgebraicGeometry.Stack.EtaleSmoothLift.isFiberedInGroupoids_proj`
(**Stacks 0CJT**). Condition (2), the descent of morphisms that the source leaves to the reader,
is `AlgebraicGeometry.Stack.EtaleSmoothLift.isMorSheaf_proj`. Condition (3) follows the source.
"In order to prove effectivity we may first refine the covering"
(`CategoryTheory.Functor.hasEffectiveDescent_of_familyRefinements`): every covering sieve is
refined by a jointly surjective family of affine schemes, indexed by the points of an étale chart
`T₀` of the base and each of size at most that of `T₀`
(`AlgebraicGeometry.Space.SpacesEtale.exists_affine_refinement`). The ambient spaces `U'_k` of a
descent datum over such a family are affine schemes too (Stacks 05ZR and the affine case of
Stacks 0BPG), of size bounded by `2 ^ 2 ^ size Y₀` for a smooth chart `Y₀` of `𝒳'`
(`AlgebraicGeometry.Stack.EtaleSmoothLift.size_ambient_le`). Since the cutoff of the site is a
strong limit cardinal, the disjoint unions `∐ U_k` and `∐ U'_k` are objects of the site, the
lifts glue over `∐ U_k` with ambient space `∐ U'_k`, and the source's quotient of `∐ U'_k` by
the étale equivalence relation `∐ U'_{kk'}` (Stacks 02WW) descends the glued lift along
`∐ U_k ⟶ U` (`AlgebraicGeometry.Stack.EtaleSmoothLift.isEffective_of_sigma`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Cardinal

universe u w t

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

namespace EtaleSmoothLift

attribute [local instance] isFibered_proj

/-- **The ambient space of a smooth lift of an affine scheme is an affine scheme of bounded
size.** It is representable by Stacks 05ZR, affine by the affine case of Stacks 0BPG, and of
size at most `2 ^ 2 ^ size Y₀` for a smooth surjective chart `Y₀` of `𝒳'`. -/
theorem exists_ambient_representative (ξ : EtaleSmoothLift B S hS ι hι W x hx)
    (hbase : Space.IsAffineSpace B S hS ξ.base.obj.left.obj) (Y₀ : BigFppfOver B S hS)
    (b : (algebraicSpaceStackFunctor.{u, w} B S hS).obj
      ⟨yoneda.obj Y₀, isAlgebraicSpace_yoneda B S hS Y₀⟩ ⟶ 𝒳')
    (hb : AlgebraicStacks.IsSmooth B S hS b) (hbs : IsSurjective B S hS b) :
    ∃ (A : BigFppfOver B S hS) (_ : yoneda.obj A ≅ ξ.ambient.obj),
      ((BigFppfOver.toScheme B S hS).obj A).size ≤
        (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ ((BigFppfOver.toScheme B S hS).obj Y₀).size := by
  obtain ⟨T, -, ⟨eT⟩⟩ := id hbase
  have hrepB : ξ.base.obj.left.obj.IsRepresentable :=
    isRepresentable_of_natIso (yoneda.obj T) eT.symm
  have hrep : ξ.ambient.obj.IsRepresentable := isRepresentable_ambient ξ hrepB
  obtain ⟨T', hT', ⟨e⟩⟩ := Space.isAffineSpace_of_isClosedImmersion_of_isSurjective_of_isAffineSpace
    B S hS ξ.inclusion.hom ξ.base.obj.left.property ξ.ambient.property
    (isThickeningHom_inclusion ξ).isClosedImmersion
    (isThickeningHom_inclusion ξ).surjective_pointsMap hbase
  let iA : ξ.ambient.obj.reprX ≅ T' := yoneda.preimageIso (ξ.ambient.obj.reprW ≪≫ e)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.ambient.obj.reprX) :=
    IsAffine.of_isIso ((BigFppfOver.toScheme B S hS).mapIso iA).hom
  exact ⟨ξ.ambient.obj.reprX, ξ.ambient.obj.reprW, size_ambient_le Y₀ b hb hbs ξ hrep⟩

/-- **The category of smooth lifts is a stack over the spaces-étale site of `W`**: the three
conditions of Stacks 026F. It is fibred (Stacks 0CJT), its morphism presheaves are sheaves (the
descent of morphisms), and every descent datum relative to a covering sieve is effective: refine
the sieve to a jointly surjective family of affine schemes of bounded size, form the disjoint
unions of the members and of the ambient spaces of the datum in the site, and descend along the
single étale surjection from the disjoint union. -/
theorem isStack_proj :
    (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsStack
      (Space.SpacesEtale.topology B S hS W) where
  isFibered := isFibered_proj
  isMorSheaf := fun U => isMorSheaf_proj U
  hasEffectiveDescent := by
    refine Functor.hasEffectiveDescent_of_familyRefinements (fun U => isMorSheaf_proj U) ?_
    intro U R hR
    obtain ⟨T₀, nN, N, iN, f, hfR, hA, hsz, hjs⟩ :=
      Space.SpacesEtale.exists_affine_refinement U R hR
    refine ⟨_, N, f, hfR, ?_, fun D => ?_⟩
    · rw [Space.SpacesEtale.mem_topology_iff_sievePointwiseCover]
      intro p
      obtain ⟨τ, z, hz⟩ := hjs p
      exact ⟨N τ, f τ, Sieve.ofArrows_mk _ _ τ, z, hz⟩
    obtain ⟨Y₀, b, hb, hbs⟩ := exists_smooth_surjective_spaceChart 𝒳'
    set κ := max ((BigFppfOver.toScheme B S hS).obj T₀).size
      ((BigFppfOver.toScheme B S hS).obj Y₀).size with hκdef
    have hκ : κ < B.cutoff := max_lt T₀.left.property Y₀.left.property
    have hμ : (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ κ < B.cutoff :=
      B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit hκ)
    have hle : κ ≤ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ κ :=
      (cantor κ).le.trans (cantor _).le
    have hℵ : ℵ₀ ≤ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ κ :=
      ((Scheme.aleph0_le_size _).trans (le_max_left _ _)).trans hle
    have hK : #((BigFppfOver.toScheme B S hS).obj T₀) ≤
        (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ κ :=
      (Scheme.mk_le_two_pow_size _).trans
        ((power_le_power_left two_ne_zero (le_max_left _ _)).trans (cantor _).le)
    have hsizeN : ∀ τ, ((BigFppfOver.toScheme B S hS).obj (nN τ)).size ≤
        (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ κ :=
      fun τ => ((hsz τ).trans (le_max_left _ _)).trans hle
    obtain ⟨VN, cN, ⟨hVN⟩⟩ := BigFppfOver.exists_isColimit_cofan_of_size_sigma_lt B S hS nN
      ((schemeSize_coproduct_le _ _ hℵ hK hsizeN).trans_lt hμ)
    have hbase : ∀ τ, Space.IsAffineSpace B S hS (famObj D τ).1.base.obj.left.obj := by
      intro τ
      have e : (famObj D τ).1.base = N τ := (famObj D τ).2
      rw [e]
      exact ⟨nN τ, hA τ, ⟨(iN τ).symm⟩⟩
    choose nA iA hnA using fun τ =>
      exists_ambient_representative (famObj D τ).1 (hbase τ) Y₀ b hb hbs
    have hsizeA : ∀ τ, ((BigFppfOver.toScheme B S hS).obj (nA τ)).size ≤
        (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ κ :=
      fun τ => (hnA τ).trans (power_le_power_left two_ne_zero
        (power_le_power_left two_ne_zero (le_max_right _ _)))
    obtain ⟨VA, cA, ⟨hVA⟩⟩ := BigFppfOver.exists_isColimit_cofan_of_size_sigma_lt B S hS nA
      ((schemeSize_coproduct_le _ _ hℵ hK hsizeA).trans_lt hμ)
    exact isEffective_of_sigma D nN iN cN hVN hjs nA iA cA hVA

/-- **Stacks 0CJU.** The category `p : 𝒞 ⟶ W_{spaces, étale}` of smooth lifts constructed in
Stacks 0CJP is a stack in groupoids: the three conditions of Stacks 02ZI, for covering families
indexed by an arbitrary universe `t`.

There is no hypothesis beyond those of Stacks 0CJP. Condition (1) is
`AlgebraicGeometry.Stack.EtaleSmoothLift.isFiberedInGroupoids_proj` (Stacks 0CJT); conditions
(2) and (3) come from `AlgebraicGeometry.Stack.EtaleSmoothLift.isStack_proj` through
`CategoryTheory.Functor.IsStack.isStackInGroupoids`. See the module docstring for the proof of
effectivity. -/
@[stacks 0CJU]
theorem isStackInGroupoids_proj :
    Functor.IsStackInGroupoids.{t} (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _)
      (Space.SpacesEtale.topology B S hS W) :=
  isStack_proj.isStackInGroupoids isFiberedInGroupoids_proj

end EtaleSmoothLift

end AlgebraicGeometry.Stack
