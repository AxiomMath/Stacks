module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.EssentiallySmallInjectives
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainCoreflection
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineAdequatorVanishing
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.PairsDomainSite
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.PairsScalingOn
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance

/-!
# The vanishing of `Ext` from linearly adequate functors over the algebras of a big site

`AdequateFunctor.subsingleton_zExt_isLinearlyAdequate_moduleExtensionOn` proves, on a domain of
algebras with a base object and a domain of pairs on which the adjunctions `ψ_N ⊣ φ_N` restrict,
that `Ext^i(L, M̲) = 0` for `i > 0` and `L` linearly adequate, as soon as the module-valued
functors on both domains have enough injectives. This file applies it to the algebras of a big
site with cutoff `κ` and the pairs `AdequateFunctor.sitePairs κ`, with module values in the
universe of the site.

Both domains are essentially small: an algebra or a module of cardinality below `κ` is isomorphic
to one carried by a subset of `κ.out`. So their module-valued functors have enough injectives
(`PresheafOfModules.enoughInjectives_of_essentiallySmall`).

## Main results

* `AdequateFunctor.essentiallySmall_sitePairs`: the pairs `AdequateFunctor.sitePairs κ` are
  essentially small, as the algebras of the site are
  (`AdequateFunctor.essentiallySmall_algebraInSite`).
* `Stacks.Adequate.subsingleton_zExt_siteModuleFunctors_isLinearlyAdequate`: in the module-valued
  functors on the `A`-algebras of a big site over `Spec A`, `Ext^i(L, M̲) = 0` for every linearly
  adequate `L`, every `A`-module `M` and every `i > 0`. This is the input of
  `Stacks.Adequate.bijective_mapExtAddHom_ι_adequate_of_siteZExt`.

## References

* [Stacks Project, Tag 06ZH](https://stacks.math.columbia.edu/tag/06ZH)
* [Stacks Project, Tag 06ZW](https://stacks.math.columbia.edu/tag/06ZW)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Cardinal

universe u

namespace AdequateFunctor

variable {A : Type u} [CommRing A]

/-- An isomorphism of pairs from an algebra isomorphism and a semilinear additive isomorphism. -/
def AlgebraModulePair.isoMk {X Y : AlgebraModulePair.{u} A} (eC : X.algebra ≃ₐ[A] Y.algebra)
    (eV : X.module ≃+ Y.module) (h : ∀ (c : X.algebra) (v : X.module), eV (c • v) = eC c • eV v) :
    X ≅ Y where
  hom :=
    { base := eC.toAlgHom
      linear :=
        { toFun := eV
          map_add' := map_add eV
          map_smul' := h } }
  inv :=
    { base := eC.symm.toAlgHom
      linear :=
        { toFun := eV.symm
          map_add' := map_add eV.symm
          map_smul' := fun c v => eV.injective (by
            change eV (eV.symm (c • v)) = eV (eC.symm c • eV.symm v)
            rw [h, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
              AlgEquiv.apply_symm_apply]) } }
  hom_inv_id := AlgebraModulePair.Hom.ext _ _ (AlgHom.ext fun c => eC.symm_apply_apply c)
    fun v => eV.symm_apply_apply v
  inv_hom_id := AlgebraModulePair.Hom.ext _ _ (AlgHom.ext fun c => eC.apply_symm_apply c)
    fun v => eV.apply_symm_apply v

/-- **The pairs `AdequateFunctor.sitePairs κ` are essentially small**: the algebra and the module
of such a pair have cardinality below `κ`, so the pair is isomorphic to one carried by subsets of
`κ.out`. -/
theorem essentiallySmall_sitePairs {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) :
    ObjectProperty.EssentiallySmall.{u} (sitePairs (A := A) κ) := by
  classical
  let model (p : Σ T W : Set κ.out, Σ (_ : CommRing T) (_ : Algebra A T) (_ : AddCommGroup W),
      Module T W) : AlgebraModulePair.{u} A :=
    let := p.2.2.1
    let := p.2.2.2.1
    let := p.2.2.2.2.1
    let := p.2.2.2.2.2
    { algebra := p.1, module := p.2.1 }
  refine ⟨ObjectProperty.ofObj model, inferInstance, fun X hX ↦ ?_⟩
  have hC : #X.algebra < κ := (schemeSizeBelow_spec_iff hκ X.algebra).1 hX.1
  obtain ⟨f⟩ : Nonempty (X.algebra ↪ κ.out) := hC.le.trans_eq (Cardinal.mk_out κ).symm
  obtain ⟨g⟩ : Nonempty (X.module ↪ κ.out) := hX.2.le.trans_eq (Cardinal.mk_out κ).symm
  let e : Set.range f ≃ X.algebra := (Equiv.ofInjective f f.injective).symm
  let d : Set.range g ≃ X.module := (Equiv.ofInjective g g.injective).symm
  let : CommRing (Set.range f) := e.commRing
  let : Algebra A (Set.range f) := e.algebra A
  let : AddCommGroup (Set.range g) := d.addCommGroup
  let eC : Set.range f ≃ₐ[A] X.algebra := e.algEquiv A
  let eV : Set.range g ≃+ X.module := d.addEquiv
  let : Module X.algebra (Set.range g) := eV.module X.algebra
  let : Module (Set.range f) (Set.range g) := Module.compHom _ eC.toRingEquiv.toRingHom
  let p : Σ T W : Set κ.out, Σ (_ : CommRing T) (_ : Algebra A T) (_ : AddCommGroup W),
      Module T W := ⟨Set.range f, Set.range g, inferInstance, inferInstance, inferInstance,
        inferInstance⟩
  refine ⟨model p, ObjectProperty.ofObj_apply model p, ⟨(AlgebraModulePair.isoMk
    (X := model p) (Y := X) eC eV fun c v => ?_).symm⟩⟩
  exact (eV.linearEquiv X.algebra).map_smul (eC c) v

end AdequateFunctor

namespace Stacks.Adequate

open AdequateFunctor

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

attribute [local instance] HasDerivedCategory.standard in
/-- **`Ext^i(L, M̲) = 0` over the algebras of a big site.** In the module-valued functors on the
`A`-algebras of a big site over `Spec A`, for every linearly adequate `L`, every `A`-module `M`
and every `i > 0`, `Ext^i(L, M̲) = 0`. This is the hypothesis of
`Stacks.Adequate.bijective_mapExtAddHom_ι_adequate_of_siteZExt`. -/
public theorem subsingleton_zExt_siteModuleFunctors_isLinearlyAdequate :
    ∀ X : siteModuleFunctors B,
      IsLinearlyAdequate (siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) X →
      ∀ (M : ModuleCat.{u} A) (i : ℤ), 0 < i →
        Subsingleton (Abelian.zExt X
          ((moduleExtensionFunctorOn.{u, u}
            (siteAlgebraInclusion A (schemeSizeBelow B.cutoff))).obj M) i) := by
  intro X hX M i hi
  have hκ : ℵ₀ < B.cutoff := (Spec A).aleph0_le_size.trans_lt B.base_mem
  have := essentiallySmall_algebraInSite (A : Type u) B.cutoff
  have := essentiallySmall_sitePairs (A := A) hκ
  have : EnoughInjectives (PresheafOfModules.{u} (pairRingDiagramOn (sitePairs (A := A)
      B.cutoff))) := PresheafOfModules.enoughInjectives_of_essentiallySmall _
  have : EnoughInjectives (siteModuleFunctors B) :=
    PresheafOfModules.enoughInjectives_of_essentiallySmall _
  exact subsingleton_zExt_isLinearlyAdequate_moduleExtensionOn
    (BaseAlgebraObject.siteOfSpecMem (schemeSizeBelow B.cutoff) B.base_mem)
    (fun N _ _ _ => pairsDomainClosed_site hκ B.base_mem N) X hX M i hi

end Stacks.Adequate

end
