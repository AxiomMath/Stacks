module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentFilteredColimitNoetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctorExtension

/-!
# Extending right exact tensor functors from coherent to quasi-coherent modules (Stacks 0GRJ)

**Stacks 0GRJ**: *Let `𝒳` and `𝒴` be Noetherian algebraic stacks. Given a right exact tensor
functor `F' : Coh(𝒪_𝒳) ⟶ Coh(𝒪_𝒴)` there exists a unique (up to unique isomorphism) right exact
tensor functor `F : QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_𝒴)` commuting with direct sums whose restriction to
`Coh(𝒪_𝒳)` is `F'`.*

`AlgebraicGeometry.Stack.existsUnique_tensorExtension_of_coherentGeneration` proves this from
the single input that every quasi-coherent `𝒪_𝒳`-module is a filtered colimit of coherent ones,
which is Stacks 0GRF
(`AlgebraicGeometry.Stack.AlgebraicStacks.isFiltered_coherentSubobject_and_isColimit`), in the form
`AlgebraicGeometry.Stack.ind_coherentQuasicoherent`.  This file combines the two.

## Main results

* `AlgebraicGeometry.Stack.existsUnique_tensorExtension_coherent`: **Stacks 0GRJ**.

## References

* [Stacks Project, Tag 0GRJ](https://stacks.math.columbia.edu/tag/0GRJ)
* [Stacks Project, Tag 0GRF](https://stacks.math.columbia.edu/tag/0GRF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u w w'

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] FibredSite.monoidalCategoryQuasicoherentModules

/-- **Stacks 0GRJ.** Let `𝒳` and `𝒴` be Noetherian algebraic stacks.  Any right exact tensor
functor `F' : Coh(𝒪_𝒳) ⟶ Coh(𝒪_𝒴)` — additive, preserving finite colimits, and a functor of
monoidal categories (Stacks 0FFL) — extends to a right exact tensor functor
`F : QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_𝒴)` commuting with all (small) colimits, in particular with direct
sums: there is an identification `e` of the restriction of `F` to `Coh(𝒪_𝒳)` with `F'`
(followed by the inclusion of `Coh(𝒪_𝒴)`), compatible with the tensor structures.  The extension
is unique up to unique isomorphism: for any other functor `G` commuting with filtered colimits and
identification `e'`, there is a unique isomorphism `F ≅ G` restricting to `e' ⁻¹ ∘ e` on coherent
modules, and it is compatible with any tensor structure on `G` for which `e'` is.

The input "every quasi-coherent module is a filtered colimit of coherent ones" is Stacks 0GRF
(`AlgebraicGeometry.Stack.AlgebraicStacks.isFiltered_coherentSubobject_and_isColimit`), in the form
`AlgebraicGeometry.Stack.ind_coherentQuasicoherent`. -/
@[stacks 0GRJ]
theorem existsUnique_tensorExtension_coherent
    (𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsNoetherianStack.{u, w, w'} B S hS 𝒳)
    (h𝒴 : IsNoetherianStack.{u, w, w'} B S hS 𝒴) :
    haveI := coherentQuasicoherent_isMonoidal B S hS 𝒳 h𝒳.2.2
    haveI := coherentQuasicoherent_isMonoidal B S hS 𝒴 h𝒴.2.2
    ∀ (F' : (coherentQuasicoherent B S hS 𝒳).FullSubcategory ⥤
        (coherentQuasicoherent B S hS 𝒴).FullSubcategory) [F'.Additive]
      [PreservesFiniteColimits F'] (hF' : F'.TensorStructure),
      ∃ (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids ⥤
          FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒴.val.val.p
            𝒴.val.isFiberedInGroupoids)
        (e : (coherentQuasicoherent B S hS 𝒳).ι ⋙ F ≅ F' ⋙ (coherentQuasicoherent B S hS 𝒴).ι)
        (hF : F.TensorStructure),
        (F.Additive ∧ PreservesFiniteColimits F ∧ PreservesColimitsOfSize.{u, u} F ∧
          (hF.restrict (coherentQuasicoherent B S hS 𝒳)).IsCompatible
            (hF'.compι (coherentQuasicoherent B S hS 𝒴)) e) ∧
        ∀ (G : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
            𝒳.val.isFiberedInGroupoids ⥤
            FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒴.val.val.p
              𝒴.val.isFiberedInGroupoids),
          PreservesFilteredColimitsOfSize.{u, u} G →
            ∀ (e' : (coherentQuasicoherent B S hS 𝒳).ι ⋙ G ≅
                F' ⋙ (coherentQuasicoherent B S hS 𝒴).ι),
              ∃! φ : F ≅ G, Functor.whiskerLeft (coherentQuasicoherent B S hS 𝒳).ι φ.hom =
                  (e ≪≫ e'.symm).hom ∧
                ∀ hG : G.TensorStructure,
                  (hG.restrict (coherentQuasicoherent B S hS 𝒳)).IsCompatible
                    (hF'.compι (coherentQuasicoherent B S hS 𝒴)) e' →
                    hF.IsCompatible hG φ :=
  existsUnique_tensorExtension_of_coherentGeneration B S hS 𝒳 𝒴 h𝒳 h𝒴
    (ind_coherentQuasicoherent B S hS 𝒳 h𝒳)

end AlgebraicGeometry.Stack

end
