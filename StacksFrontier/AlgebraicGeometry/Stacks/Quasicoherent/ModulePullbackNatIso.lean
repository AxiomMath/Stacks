module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentPullback

/-!
# Inverse images of modules along 2-isomorphic 1-morphisms

Let `f, f' : 𝒳 ⥤ 𝒴` be two 1-morphisms of categories fibred in groupoids over the big fppf site
of `S`, both strictly over the site (`f ⋙ q = p = f' ⋙ q`), and let `e : f ≅ f'` be a
2-isomorphism, that is a natural isomorphism whose components lie over identities
(**Stacks 02XS**). The inverse images of sheaves of modules along `f` and `f'`
(**Stacks 06WE**) are then isomorphic: on sections at `x` the isomorphism is the restriction
map along `e_x`, which is linear over the structure sheaf because `q(e_x)` is an identity.

The proofs of **Stacks 07AQ** part (2) and **Stacks 07AP** identify the inverse image of a module
along a 1-morphism `(Sch/U) ⟶ 𝒳` with its inverse image along another 1-morphism known only up to
2-isomorphism (for instance one produced by the 2-Yoneda lemma, **Stacks 004B**), which is what
this file supplies.

## Main definitions

* `AlgebraicGeometry.Stack.modulePullbackIsoOfNatIso`: the isomorphism of inverse-image functors
  attached to a natural isomorphism over the identities, in any topology and module universe.
* `AlgebraicGeometry.Stack.fppfModulesPullbackIsoOfIso`: the same for a 2-isomorphism of
  1-morphisms of algebraic stacks, on modules on the fppf sites at module universe `u`.

## Implementation notes

The isomorphism is `SheafOfModules.pushforwardCongr₂`. Its compatibility hypothesis compares the
two identifications of the structure sheaf of `𝒳` with restrictions of the one of `𝒴`; both are
`CategoryTheory.eqToHom`s, and the comparison of the two restrictions induced by `e` is the
structure sheaf of the site applied to `q(e_x)`, which is an `CategoryTheory.eqToHom` too.

## References

* [Stacks Project, Tag 02XS](https://stacks.math.columbia.edu/tag/02XS)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 07AQ](https://stacks.math.columbia.edu/tag/07AQ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w m v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  {f f' : 𝒳 ⥤ 𝒴} (hf : f ⋙ q = p) (hf' : f' ⋙ q = p)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- **The inverse images of modules along two 2-isomorphic 1-morphisms are isomorphic.** For
1-morphisms `f, f' : 𝒳 ⥤ 𝒴` of categories fibred in groupoids with `f ⋙ q = p = f' ⋙ q` and a
natural isomorphism `e : f ≅ f'` whose components lie over identities, the inverse images
`f^*, f'^*` of sheaves of modules (**Stacks 06WE**) are isomorphic, by restriction along the
components of `e`. -/
noncomputable def modulePullbackIsoOfNatIso (e : f ≅ f')
    (he : ∀ x, q.IsHomLift (𝟙 (p.obj x)) (e.hom.app x)) :
    modulePullback.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ ≅
      modulePullback.{u, v, w, m, v', w'} B S hS p q hp hq f' hf' τ hτ := by
  have : p.IsFibered := hp.isFibered
  have : q.IsFibered := hq.isFibered
  have := ((hq.isFibredOneMorphism hf).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  have := ((hq.isFibredOneMorphism hf').isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  have hobj : ∀ x, q.obj (f'.obj x) = q.obj (f.obj x) := fun x => by
    rw [← Functor.comp_obj, ← Functor.comp_obj, hf, hf']
  have hhom : ∀ x, q.map (e.hom.app x) = eqToHom (hobj x).symm := fun x => by
    simpa using IsHomLift.fac' q (𝟙 (p.obj x)) (e.hom.app x)
  have hinv : ∀ x, q.map (e.inv.app x) = eqToHom (hobj x) := fun x => by
    rw [← cancel_epi (q.map (e.hom.app x)), ← q.map_comp, e.hom_inv_id_app, q.map_id, hhom,
      eqToHom_trans, eqToHom_refl]
  have hh : f.op ⋙ (ringStructureSheafCore B S hS q hq τ hτ).obj =
      f'.op ⋙ (ringStructureSheafCore B S hS q hq τ hτ).obj :=
    (ringStructureSheafCore_obj_eq B S hS p q hp hq f hf τ hτ).symm.trans
      (ringStructureSheafCore_obj_eq B S hS p q hp hq f' hf' τ hτ)
  have hw : Functor.whiskerRight (NatTrans.op e.inv)
      (ringStructureSheafCore B S hS q hq τ hτ).obj = eqToHom hh := by
    refine NatTrans.ext (funext fun x => ?_)
    rw [eqToHom_app]
    change (BigFppfOver.structureSheaf B S hS).obj.map (q.map (e.inv.app x.unop)).op = _
    rw [hinv, eqToHom_op, eqToHom_map]
    rfl
  dsimp only [modulePullback]
  refine SheafOfModules.pushforwardCongr₂ _ e.symm ?_
  apply Sheaf.hom_ext
  change eqToHom (ringStructureSheafCore_obj_eq B S hS p q hp hq f hf τ hτ) ≫
    Functor.whiskerRight (NatTrans.op e.inv) (ringStructureSheafCore B S hS q hq τ hτ).obj =
      eqToHom (ringStructureSheafCore_obj_eq B S hS p q hp hq f' hf' τ hτ)
  rw [hw, eqToHom_trans]

section AlgebraicStacks

variable {B S hS} {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f g : 𝒳 ⟶ 𝒴}

/-- The natural isomorphism of underlying functors of a 2-isomorphism of 1-morphisms of algebraic
stacks. -/
@[simps]
def homFunctorIsoOfIso (e : f ≅ g) :
    CatFiberedInGroupoids.homFunctor f.hom ≅ CatFiberedInGroupoids.homFunctor g.hom where
  hom := e.hom.hom.hom.toNatTrans
  inv := e.inv.hom.hom.toNatTrans
  hom_inv_id := congrArg (fun t : f ⟶ f => t.hom.hom.toNatTrans) e.hom_inv_id
  inv_hom_id := congrArg (fun t : g ⟶ g => t.hom.hom.toNatTrans) e.inv_hom_id

variable (B S hS)

/-- **The inverse images of modules along two 2-isomorphic 1-morphisms of algebraic stacks are
isomorphic**, for modules on the fppf sites at module universe `u`. -/
noncomputable def fppfModulesPullbackIsoOfIso (e : f ≅ g) :
    fppfModulesPullback B S hS f ≅ fppfModulesPullback B S hS g :=
  modulePullbackIsoOfNatIso.{u, u + 1, u, u, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p g.hom) B.topology le_rfl (homFunctorIsoOfIso e)
    (fun x => CatFiberedInGroupoids.isHomLift_app e.hom.hom x)

end AlgebraicStacks

end AlgebraicGeometry.Stack
