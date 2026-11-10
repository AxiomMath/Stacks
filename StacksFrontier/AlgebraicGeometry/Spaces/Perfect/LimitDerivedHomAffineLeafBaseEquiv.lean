module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomAffineLeafHomEquivFactor
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsCompOfEqConjugate

/-!
# The base-ring bijection of a derived pullback between represented affines, on a factorisation

`AlgebraicGeometry.Space.representedAffineDerivedPullbackHomEquivBase` moves a homomorphism group
between derived pullbacks of associated modules over an affine representable to a homomorphism
group over the ring of the *target*,

`Hom_{D(𝒪_{h_{U'}})}(Lg^*(Φ_R M), Lg^*(Φ_R N)) ≃ Hom_{D(R)}(M, N ⊗^𝐋_R R')`,

for arbitrary `M`, `N` in `D(R)`, `R = Γ(U, 𝒪)`.  It is
`AlgebraicGeometry.Space.representedAffineDerivedPullbackHomEquiv` followed by the adjunction of
[stacks 0GMT].  This file proves that it intertwines the maps of homomorphism groups attached to
a factorisation: the map `CategoryTheory.PullbackData.factorHom` of
`AlgebraicGeometry.Space.canonicalPullbackData` along `g₂ : U'' ⟶ U'` becomes, on the module
side, **post-composition with a single morphism of `D(R)`** — the unit of [stacks 0GMT] along
`g₂`, restricted along `g` — rather than the conjugation by the composition law of derived
extensions of scalars that
`AlgebraicGeometry.Space.representedAffineDerivedPullbackHomEquiv_factorHom` produces.

That is the shape the system of [stacks 09RI] is consumed in over an affine leaf: the first
argument stays over the fixed ring `R` while only the second argument varies with the stage, and
the transition maps are induced by maps `A_i ⊗^𝐋_R N ⟶ A_j ⊗^𝐋_R N` of the second argument
alone.

## Main definitions

* `AlgebraicGeometry.Space.representedAffineDerivedBaseTransition`: the morphism
  `N ⊗^𝐋_R R' ⟶ N ⊗^𝐋_R R''` of `D(R)` attached to a factorisation — the unit of [stacks 0GMT]
  along `g₂` at `N ⊗^𝐋_R R'`, followed by the composition law of the derived extensions and the
  merge of the two derived restrictions of scalars.

## Main results

* `CategoryTheory.Adjunction.homEquiv_conjHom_of_conjugateEquiv`: the abstract computation — for
  a composite of two adjunctions whose right adjoints are merged by `Ψ` and a third adjunction
  with right adjoint the target of `Ψ`, if the composition law `T` of the left adjoints is the
  conjugate of `Ψ` then conjugation by `T` becomes, under the transposes, post-composition with
  one morphism.  Only the mate relation is used, so nothing about derived categories enters.
* `AlgebraicGeometry.Space.representedAffineDerivedPullbackHomEquivBase_factorHom`: **the
  base-ring bijection intertwines the maps attached to a factorisation.**

## Implementation notes

The one non-formal input is the compatibility of the adjunction of [stacks 0GMT] with the
composition law of the chosen derived extensions of scalars — that the mate of
`RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq` under the composite adjunction
is the merge of the two derived restrictions of scalars.  That is
`StacksDraft.DerivedInverseLimit.conjugateEquiv_totalDerivedExtensionScalarsCompOfEq_inv`, and it
is already stated at the `CategoryTheory.HasDerivedCategory.standard` model, which is the model
the affine leaf is spelled at; `Mathlib`'s `CategoryTheory.unit_conjugateEquiv` turns that mate
relation into the unit identity the computation needs.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 08H1](https://stacks.math.columbia.edu/tag/08H1)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v₀ v₁ v₂ t₀ t₁ t₂ u

namespace CategoryTheory.Adjunction

section ConjHom

variable {C₀ : Type t₀} {C₁ : Type t₁} {C₂ : Type t₂} [Category.{v₀} C₀] [Category.{v₁} C₁]
  [Category.{v₂} C₂] {E₁ : C₀ ⥤ C₁} {R₁ : C₁ ⥤ C₀} {E₂ : C₁ ⥤ C₂} {R₂ : C₂ ⥤ C₁}
  {Ec : C₀ ⥤ C₂} {Rc : C₂ ⥤ C₀} (a₁ : E₁ ⊣ R₁) (a₂ : E₂ ⊣ R₂) (ac : Ec ⊣ Rc)
  (T : E₁ ⋙ E₂ ≅ Ec) (Ψ : R₂ ⋙ R₁ ≅ Rc)

/-- **Under the transposes, conjugation by a composition law of left adjoints is
post-composition with one morphism.**  Let `a₁ : E₁ ⊣ R₁` and `a₂ : E₂ ⊣ R₂` compose, let
`Ψ : R₂ ⋙ R₁ ≅ Rc` merge the two right adjoints and let `ac : Ec ⊣ Rc` be a third adjunction
with that right adjoint.  Suppose the composition law `T : E₁ ⋙ E₂ ≅ Ec` is the conjugate of
`Ψ` (the hypothesis `hmate`, which says that `T` is the identification of the two left adjoints
of `Rc`).  Then the `ac`-transpose of `CategoryTheory.Functor.conjHom` of `α` by `T` is the
`a₁`-transpose of `α` followed by a morphism that does not depend on `α` — the unit of `a₂` at
`E₁ N`, read through `R₂`, `T` and `Ψ`.

This is what replaces a conjugation by the composition law of the derived extensions of scalars
with a map of the second argument alone. -/
theorem homEquiv_conjHom_of_conjugateEquiv
    (hmate : conjugateEquiv (a₁.comp a₂) ac T.inv = Ψ.hom)
    {M N : C₀} (α : E₁.obj M ⟶ E₁.obj N) :
    ac.homEquiv M (Ec.obj N) (Functor.conjHom T.symm α) =
      a₁.homEquiv M (E₁.obj N) α ≫
        R₁.map (a₂.unit.app (E₁.obj N) ≫ R₂.map (T.hom.app N)) ≫ Ψ.hom.app (Ec.obj N) := by
  have hΨ : ∀ {X Y : C₂} (v : X ⟶ Y),
      R₁.map (R₂.map v) ≫ Ψ.hom.app Y = Ψ.hom.app X ≫ Rc.map v := fun v => Ψ.hom.naturality v
  have hnat : a₂.unit.app (E₁.obj M) ≫ R₂.map (E₂.map α) = α ≫ a₂.unit.app (E₁.obj N) :=
    (a₂.unit.naturality α).symm
  have hnat' : R₁.map (a₂.unit.app (E₁.obj M)) ≫ R₁.map (R₂.map (E₂.map α)) =
      R₁.map α ≫ R₁.map (a₂.unit.app (E₁.obj N)) := by
    rw [← R₁.map_comp, ← R₁.map_comp, hnat]
  have key : ac.unit.app M ≫ Rc.map (T.inv.app M) =
      a₁.unit.app M ≫ R₁.map (a₂.unit.app (E₁.obj M)) ≫ Ψ.hom.app (E₂.obj (E₁.obj M)) := by
    rw [← hmate, ← unit_conjugateEquiv (a₁.comp a₂) ac T.inv M]
    simp only [Adjunction.comp_unit_app, Category.assoc, Functor.comp_obj]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.conjHom, Iso.symm_hom, Iso.symm_inv, Functor.map_comp, Category.assoc]
  rw [reassoc_of% key, ← Category.assoc (Ψ.hom.app (E₂.obj (E₁.obj M))), ← hΨ (E₂.map α),
    hΨ (T.hom.app N)]
  simp only [Category.assoc]
  rw [← Category.assoc (R₁.map (a₂.unit.app (E₁.obj M))), hnat']
  simp only [Category.assoc, Functor.comp_obj]

end ConjHom

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

/- The filtered colimits used to form the étale sheafification, through Mathlib's instance, so that
the categories of `𝒪`-modules below are spelled as in the files of the derived pullback. -/
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance] additive_extendScalars_representedAffineRingHom
  additive_pullbackModules_representedSpaceMap

attribute [local instance 6000] preadditive_smallEtaleModules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U U' U'' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'')]

/-- **The transition map of the second argument attached to a factorisation of affine
representables.**  For `g : U' ⟶ U`, `g₂ : U'' ⟶ U'` and `N` in `D(R)`, `R = Γ(U, 𝒪)`, this is
the morphism

`N ⊗^𝐋_R R' ⟶ N ⊗^𝐋_R R''`

of `D(R)`: the unit of [stacks 0GMT] along `g₂` at `N ⊗^𝐋_R R'`, then the composition law
`RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq` of the derived extensions of
scalars restricted along `g₂`, and finally the merge
`StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp` of the two derived restrictions of
scalars — all read inside derived restriction of scalars along `g`, which is what keeps the
result over the fixed ring `R`. -/
def representedAffineDerivedBaseTransition (g : U' ⟶ U) (g₂ : U'' ⟶ U')
    (N : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) :
    (ModuleCat.restrictScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS g).hom).mapDerivedCategory.obj
        ((representedAffineDerivedExtension B S hS g).functor.obj N) ⟶
      (ModuleCat.restrictScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom).mapDerivedCategory.obj
        ((representedAffineDerivedExtension B S hS (g₂ ≫ g)).functor.obj N) :=
  (ModuleCat.restrictScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS g).hom).mapDerivedCategory.map
      ((representedAffineDerivedExtensionAdjunction B S hS g₂).unit.app
          ((representedAffineDerivedExtension B S hS g).functor.obj N) ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g₂).hom).mapDerivedCategory.map
          ((RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
            (representedAffineCommRingCatHom B S hS g).hom
            (representedAffineCommRingCatHom B S hS g₂).hom
            (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom
            (representedAffineRingHom_comp B S hS g₂ g).symm).hom.app N)) ≫
    (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u}
        (representedAffineCommRingCatHom B S hS g).hom
        (representedAffineCommRingCatHom B S hS g₂).hom
        (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom
        (representedAffineRingHom_comp B S hS g₂ g)).hom.app
      ((representedAffineDerivedExtension B S hS (g₂ ≫ g)).functor.obj N)

/-- **The bijection of [stacks 08H1] over an affine representable, read over the base ring,
intertwines the maps attached to a factorisation.**  For `g : U' ⟶ U` and `g₂ : U'' ⟶ U'` of
affine representables and arbitrary `M`, `N` in `D(R)`, `R = Γ(U, 𝒪)`, the map of homomorphism
groups attached to the factorisation `g₂ ≫ g`, followed by
`AlgebraicGeometry.Space.representedAffineDerivedPullbackHomEquivBase` at `g₂ ≫ g`, is the
bijection at `g` followed by post-composition with
`AlgebraicGeometry.Space.representedAffineDerivedBaseTransition`.

So the system of [stacks 09RI] over an affine leaf is read — at an arbitrary object of `D(R)`,
with no flatness, boundedness or perfectness hypothesis — as a system of homomorphism groups
`Hom_{D(R)}(M, N ⊗^𝐋_R A_j)` over the *one* ring `R`, whose transition maps move the second
argument only.  This is the shape
`Stacks.LimitHomDescent.Affine.RingSystem.isColim_toSchemeSystem` produces on the ring side,
and the shape `AlgebraicGeometry.Space.DescentSituation.RingModel.stageEquiv` asks for. -/
theorem representedAffineDerivedPullbackHomEquivBase_factorHom (g : U' ⟶ U) (g₂ : U'' ⟶ U')
    (M N : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
    (φ : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
          ((representedAffineDerivedAssociated B S hS U).obj M) ⟶
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
          ((representedAffineDerivedAssociated B S hS U).obj N)) :
    representedAffineDerivedPullbackHomEquivBase B S hS (g₂ ≫ g) M N
        ((canonicalPullbackData B S hS).factorHom
          (representedSpaceMap_comp B S hS g₂ g) φ) =
      representedAffineDerivedPullbackHomEquivBase B S hS g M N φ ≫
        representedAffineDerivedBaseTransition B S hS g g₂ N := by
  change (representedAffineDerivedExtensionAdjunction B S hS (g₂ ≫ g)).homEquiv M _
      (representedAffineDerivedPullbackHomEquiv B S hS (g₂ ≫ g) M N
        ((canonicalPullbackData B S hS).factorHom
          (representedSpaceMap_comp B S hS g₂ g) φ)) = _
  rw [representedAffineDerivedPullbackHomEquiv_factorHom]
  exact Adjunction.homEquiv_conjHom_of_conjugateEquiv
    (representedAffineDerivedExtensionAdjunction B S hS g)
    (representedAffineDerivedExtensionAdjunction B S hS g₂)
    (representedAffineDerivedExtensionAdjunction B S hS (g₂ ≫ g)) _ _
    (StacksDraft.DerivedInverseLimit.conjugateEquiv_totalDerivedExtensionScalarsCompOfEq_inv
      (representedAffineCommRingCatHom B S hS g).hom
      (representedAffineCommRingCatHom B S hS g₂).hom
      (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom
      (representedAffineRingHom_comp B S hS g₂ g).symm) _

end AlgebraicGeometry.Space

end
