module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSmoothModel

/-!
# The derived lower shriek along an integral cartesian morphism of compactifications

Let `φ : X ⟶ S` be a morphism of schemes and let `c`, `c'` be two compactifications of `X` over
`S`, with ambient schemes `X̄` and `X̄'`.  Suppose given a morphism `g : X̄ ⟶ X̄'` over `S`
extending the identity of `X` which is integral (finite, for instance) and such that
`X = g⁻¹(X)`, i.e. the square formed by the two open immersions, `g` and the identity of `X` is
cartesian.  Then the two derived lower shriek functors
`Rφ_! = R(f̄)_* ∘ j_!` and `R(f̄')_* ∘ j'_!` are isomorphic:

* `R(f̄)_* = R(f̄')_* ∘ Rg_*` because `f̄ = g ≫ f̄'`;
* `g_*` is exact, `g` being integral, so `Rg_* ∘ Rj_! = R(g_* ∘ j_!)`;
* `g_* ∘ j_! ≅ j'_!` because extension by zero commutes with an integral direct image along a
  cartesian square.

This is the comparison of [Stacks, Tag 0F7I] along such a morphism, obtained without the proper
base change theorem: the integral direct image is exact and commutes with base change
([Stacks, Tag 0EYP]).

## Main definitions

* `Stacks.EtaleCohomology.extensionByZeroIntegralDirectImageNatTrans` — the transformation
  `f_* ∘ j_! ⟶ f̄_* ∘ j'_!` whose components are
  `Stacks.EtaleCohomology.extensionByZeroIntegralDirectImageMap`.
* `Stacks.EtaleCohomology.extensionByZeroIntegralCartesianIso` — `j'_! ⋙ g_* ≅ j_!` for an
  integral `g` with `X = g⁻¹(X)`.
* `Stacks.EtaleCohomology.derivedLowerShriekIsoOfIntegral` — the isomorphism of the derived lower
  shriek functors of two compactifications related by such a `g`.

## References

* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
* [Stacks Project, Tag 0EYP](https://stacks.math.columbia.edu/tag/0EYP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section NatTrans

variable (Λ : Type) [Ring Λ] {U Ub V Vb : Scheme.{u}} (j : U ⟶ Ub) [Etale j] [Mono j]
  (j' : V ⟶ Vb) [Etale j'] [Mono j'] (f : V ⟶ U) (fb : Vb ⟶ Ub) [IsIntegralHom fb]
  (sq : IsPullback f j' j fb)

/-- **The transformation `f_* ∘ j_! ⟶ f̄_* ∘ j'_!`** for a cartesian square with `j`, `j'` étale
monomorphisms and `f̄` integral: the transformation adjoint, under `j_! ⊣ j^{-1}`, to the unit of
`j'_! ⊣ j'^{-1}` followed by the integral base change isomorphism
`Stacks.EtaleCohomology.restrictionIntegralDirectImageIso`. -/
def extensionByZeroIntegralDirectImageNatTrans :
    etaleModuleDirectImage.{u, 0} Λ f ⋙ etaleModuleExtensionByZero.{u, 0} Λ j ⟶
      etaleModuleExtensionByZero.{u, 0} Λ j' ⋙ etaleModuleDirectImage.{u, 0} Λ fb :=
  Functor.whiskerRight
      (Functor.whiskerRight (etaleModuleExtensionByZeroAdj.{u, 0} Λ j').unit
          (etaleModuleDirectImage.{u, 0} Λ f) ≫
        Functor.whiskerLeft (etaleModuleExtensionByZero.{u, 0} Λ j')
          (restrictionIntegralDirectImageIso Λ j j' f fb sq).hom)
      (etaleModuleExtensionByZero.{u, 0} Λ j) ≫
    Functor.whiskerLeft (etaleModuleExtensionByZero.{u, 0} Λ j' ⋙
      etaleModuleDirectImage.{u, 0} Λ fb) (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit

omit [Mono j] [Mono j'] in
/-- The components of `extensionByZeroIntegralDirectImageNatTrans` are the maps
`Stacks.EtaleCohomology.extensionByZeroIntegralDirectImageMap`. -/
theorem extensionByZeroIntegralDirectImageNatTrans_app (M : EtaleModules.{u, 0} Λ V) :
    (extensionByZeroIntegralDirectImageNatTrans Λ j j' f fb sq).app M =
      extensionByZeroIntegralDirectImageMap Λ j j' f fb sq M := by
  rw [extensionByZeroIntegralDirectImageMap, Adjunction.homEquiv_counit]
  simp [extensionByZeroIntegralDirectImageNatTrans]

end NatTrans

section Cartesian

variable (Λ : Type) [Ring Λ] {X Xb Xb' : Scheme.{u}} (t : X ⟶ Xb) [IsOpenImmersion t]
  (j : X ⟶ Xb') [IsOpenImmersion j] (g : Xb ⟶ Xb') [IsIntegralHom g]
  (sq : IsPullback (𝟙 X) t j g)

omit [IsOpenImmersion t] [IsOpenImmersion j] [IsIntegralHom g] in
include sq in
/-- The image of the open immersion `t` is the preimage under `g` of the image of `j`, for a
cartesian square `𝟙 ≫ j = t ≫ g`. -/
theorem range_eq_preimage_range_of_isPullback :
    Set.range t.base = g.base ⁻¹' Set.range j.base := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, by rw [← Scheme.Hom.comp_apply, ← sq.w, Category.id_comp]⟩
  · intro hx
    obtain ⟨z, rfl⟩ : x ∈ Set.range (pullback.fst g j).base := by
      rwa [Scheme.Pullback.range_fst]
    exact ⟨sq.flip.isoPullback.inv z, by
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]⟩

include sq in
/-- **`j'_! ⋙ g_* ≅ j_!`** for an integral morphism `g : X̄ ⟶ X̄'` and open immersions
`t : X ⟶ X̄`, `j : X ⟶ X̄'` with `X = g⁻¹(X)`: extension by zero commutes with the integral direct
image (the closed complements being the reduced complement of `j` and its preimage). -/
def extensionByZeroIntegralCartesianIso :
    etaleModuleExtensionByZero.{u, 0} Λ t ⋙ etaleModuleDirectImage.{u, 0} Λ g ≅
      etaleModuleExtensionByZero.{u, 0} Λ j :=
  let ι := openImmersionReducedComplementι j
  haveI : ∀ M, IsIso ((extensionByZeroIntegralDirectImageNatTrans Λ j t (𝟙 X) g sq).app M) :=
    fun M => by
      rw [extensionByZeroIntegralDirectImageNatTrans_app]
      refine isIso_extensionByZeroIntegralDirectImageMap Λ j t (𝟙 X) g sq ι
        (by rw [range_openImmersionReducedComplementι, compl_compl]) (pullback.snd ι g) ?_
        (pullback.fst ι g) (IsPullback.of_hasPullback ι g) M
      rw [Scheme.Pullback.range_snd, range_openImmersionReducedComplementι, Set.preimage_compl,
        compl_compl]
      exact range_eq_preimage_range_of_isPullback t j g sq
  haveI := NatIso.isIso_of_isIso_app (extensionByZeroIntegralDirectImageNatTrans Λ j t (𝟙 X) g sq)
  (asIso (extensionByZeroIntegralDirectImageNatTrans Λ j t (𝟙 X) g sq)).symm ≪≫
    Functor.isoWhiskerRight (etaleModuleDirectImageIdIso Λ X) _ ≪≫ Functor.leftUnitor _

end Cartesian

section Compactification

variable (Λ : Type) [Ring Λ] {X S : Scheme.{u}} {φ : X ⟶ S}
  (c c' : CompactificationOf (Over.mk φ)) (g : c.space ⟶ c'.space) [IsIntegralHom g]
  (hbase : g ≫ c'.toBase = c.toBase) (sq : IsPullback (𝟙 X) c.immersion c'.immersion g)

/-- **The derived lower shriek functors of two compactifications related by an integral
cartesian morphism are isomorphic.**  For compactifications `c`, `c'` of `X` over `S` and an
integral morphism `g : X̄ ⟶ X̄'` over `S` with `X = g⁻¹(X)`,
`R(f̄)_* ∘ j_! ≅ R(f̄')_* ∘ Rg_* ∘ j_! ≅ R(f̄')_* ∘ j'_!`: the first because `f̄ = g ≫ f̄'`, the
second because `g_*` is exact and `g_* ∘ j_! ≅ j'_!`
(`Stacks.EtaleCohomology.extensionByZeroIntegralCartesianIso`). -/
def derivedLowerShriekIsoOfIntegral :
    derivedLowerShriek.{u, 0} φ c Λ ≅ derivedLowerShriek.{u, 0} φ c' Λ :=
  Functor.isoWhiskerLeft (etaleModuleDerivedExtensionByZero.{u, 0} Λ c.immersion)
      (etaleModuleDerivedDirectImageComp.{u, 0} Λ g c'.toBase c.toBase hbase.symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.rightDerivedFunctorPlusCompIsoOfExact
        (etaleModuleExtensionByZero.{u, 0} Λ c.immersion) (etaleModuleDirectImage.{u, 0} Λ g)
        (etaleModuleExtensionByZero.{u, 0} Λ c'.immersion)
        (extensionByZeroIntegralCartesianIso Λ c.immersion c'.immersion g sq))
      (etaleModuleDerivedDirectImage.{u, 0} Λ c'.toBase)

end Compactification

end Stacks.EtaleCohomology

end
