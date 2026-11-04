module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.Obstruction

/-!
# Infinitesimal automorphisms of a lift of an object of `Coh_{X/Y}`

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB), `h : T ⟶ T'` a first order thickening
of schemes over `Y`, and `L = (𝒢', (X_h)^*𝒢' ≅ 𝒢)` a lift of `ξ` across `h`. The automorphisms
of `L` — automorphisms of `𝒢'` compatible with the comparison, that is, automorphisms of the
object `(T', 𝒢')` of `Coh_{X/Y}` over the identity of `T'` and under `ξ` — are the automorphisms of
`𝒢'` pulling back to the identity across `X_T ⊂ X_{T'}`, and by Stacks 08VW, part (3), they are
`Ext⁰_{𝒪_{X_T}}(𝒢, f^*𝒥 ⊗ 𝒢)` (with `𝒢` written as `i^*𝒢'`). These are the infinitesimal
automorphisms of the proof of Stacks 08W8.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.ThickeningLift.Aut`: the automorphisms of a lift,
  with its group structure.
* `AlgebraicGeometry.Space.CoherentSituation.ThickeningLift.autEquivAutOverIdentity`: they are
  the automorphisms of the lifted module over the identity of `i^*𝒢'`.
* `AlgebraicGeometry.Space.CoherentSituation.ThickeningLift.extZeroEquivAut`: the bijection with
  `Ext⁰(i^*𝒢', f^*𝒥 ⊗ i^*𝒢')` of Stacks 08VW, part (3).

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.ThickeningLift.autEquivAutOverIdentity_mul`: the
  identification with the automorphisms over the identity carries composition to composition;
  with `Deformation.ToposThickening.autOverIdentityExtZeroEquiv_spec` (Stacks 08VW, part (3)) the
  bijection with `Ext⁰` carries addition to composition.

## References

* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 08W8](https://stacks.math.columbia.edu/tag/08W8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Deformation.ToposThickening

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

universe e u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  {ξ : CoherentObject D} {T' : SchemesOver D.Y} {h : ξ.T ⟶ T'}

/-- **The automorphisms of a lift of `ξ`**: the automorphisms of the lifted module compatible
with the comparison `(X_h)^*𝒢' ≅ 𝒢`, i.e. the automorphisms of the object `(T', 𝒢')` of
`Coh_{X/Y}` over the identity of `T'` and under `ξ`. -/
def ThickeningLift.Aut (L : D.ThickeningLift ξ h) : Type _ :=
  { θ : L.F ≅ L.F // (modulePullback B S hS (D.relativeMap h)).map θ.hom ≫ L.fibre = L.fibre }

namespace ThickeningLift

variable (L : D.ThickeningLift ξ h)

/-- An automorphism of the lifted module is compatible with the comparison exactly when its
inverse image along `X_h` is the identity, the comparison being an isomorphism. -/
theorem map_comp_fibre_eq_iff (θ : L.F ⟶ L.F) :
    (modulePullback B S hS (D.relativeMap h)).map θ ≫ L.fibre = L.fibre ↔
      (modulePullback B S hS (D.relativeMap h)).map θ = 𝟙 _ :=
  ⟨fun hθ => by rw [← cancel_mono L.fibre, hθ, Category.id_comp],
    fun hθ => by rw [hθ, Category.id_comp]⟩

/-- **The automorphisms of a lift are a group**, under composition written in diagrammatic order
(`θ * σ` is `θ` followed by `σ`). -/
instance Aut.instGroup : Group L.Aut where
  mul θ σ := ⟨θ.1 ≪≫ σ.1, by
    rw [Iso.trans_hom, CategoryTheory.Functor.map_comp, Category.assoc, σ.2, θ.2]⟩
  one := ⟨Iso.refl L.F, by rw [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp]⟩
  inv θ := ⟨θ.1.symm,
    ((modulePullback B S hS (D.relativeMap h)).mapIso θ.1).inv_comp_eq.2 θ.2.symm⟩
  mul_assoc θ σ τ := Subtype.ext (Iso.ext (Category.assoc θ.1.hom σ.1.hom τ.1.hom))
  one_mul θ := Subtype.ext (Iso.ext (Category.id_comp θ.1.hom))
  mul_one θ := Subtype.ext (Iso.ext (Category.comp_id θ.1.hom))
  inv_mul_cancel θ := Subtype.ext (Iso.ext θ.1.inv_hom_id)

/-- The pullback of modules along the morphism of small étale ringed topoi of `X_h`, conjugated
by `AlgebraicGeometry.Space.CoherentSituation.relativeMapPullbackIso`, is the inverse image of
`𝒪`-modules along `X_h`. -/
theorem toposPullback_map_eq (θ : L.F ⟶ L.F) :
    (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h)).toRingedToposModulesHom.pullbackModules.map θ =
      (D.relativeMapPullbackIso h).inv.app L.F ≫
        (modulePullback B S hS (D.relativeMap h)).map θ ≫
          (D.relativeMapPullbackIso h).hom.app L.F :=
  ((D.relativeMapPullbackIso h).inv_hom_id_app_assoc _ _).symm.trans
    (congrArg ((D.relativeMapPullbackIso h).inv.app L.F ≫ ·)
      ((D.relativeMapPullbackIso h).hom.naturality θ).symm)

/-- An automorphism compatible with the comparison pulls back to the identity along the morphism of
small étale ringed topoi of `X_h`. -/
theorem toposPullback_map_eq_id (θ : L.F ⟶ L.F)
    (hθ : (modulePullback B S hS (D.relativeMap h)).map θ = 𝟙 _) :
    (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h)).toRingedToposModulesHom.pullbackModules.map θ =
      𝟙 _ := by
  rw [L.toposPullback_map_eq, hθ, Category.id_comp]
  exact (D.relativeMapPullbackIso h).inv_hom_id_app L.F

/-- An automorphism pulling back to the identity along the morphism of small étale ringed topoi
of `X_h` has inverse image the identity along `X_h`. -/
theorem modulePullback_map_eq_id (θ : L.F ⟶ L.F)
    (hθ : (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h)).toRingedToposModulesHom.pullbackModules.map θ =
      𝟙 _) :
    (modulePullback B S hS (D.relativeMap h)).map θ = 𝟙 _ :=
  (Iso.cancel_iso_hom_right _ _ ((D.relativeMapPullbackIso h).app L.F)).1
    (((D.relativeMapPullbackIso h).hom.naturality θ).trans
      ((congrArg ((D.relativeMapPullbackIso h).hom.app L.F ≫ ·) hθ).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))

/-- **The automorphisms of a lift are the automorphisms of the lifted module over the identity**
across the thickening `X_T ⊂ X_{T'}`. -/
def autEquivAutOverIdentity :
    L.Aut ≃ AutOverIdentity.{u, u + 1, u, u, u + 1}
      (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h))
      L.toposModule where
  toFun θ := ⟨θ.1, L.toposPullback_map_eq_id θ.1.hom ((L.map_comp_fibre_eq_iff θ.1.hom).1 θ.2)⟩
  invFun θ := ⟨θ.1, (L.map_comp_fibre_eq_iff θ.1.hom).2 (L.modulePullback_map_eq_id θ.1.hom θ.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The identification of the automorphisms of a lift with those over the identity carries
composition to composition. -/
theorem autEquivAutOverIdentity_mul (θ σ : L.Aut) :
    L.autEquivAutOverIdentity (θ * σ) = L.autEquivAutOverIdentity θ * L.autEquivAutOverIdentity σ :=
  rfl

variable (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))]

/-- **The infinitesimal automorphisms of a lift are `Ext⁰(𝒢, f^*𝒥 ⊗ 𝒢)`** (Stacks 08VW,
part (3)), with `𝒢` written as `i^*𝒢'` and `f^*𝒥` the pullback of the ideal of the thickening of
the base of the relative square: `α` corresponds to the automorphism `1 + α` of `𝒢'`, compatible
with the comparison. -/
def extZeroEquivAut :=
  (autOverIdentityExtZeroEquiv.{u, u + 1, u, u, u + 1, u, u + 1, u, u, u + 1, u, e}
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h))
    (D.relativeSquareSituation.relativeSquareThickening h)
    (D.relativeSquareSituation.relativeSquareLeft h)
    (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T')))
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
    (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h hh)
    (D.relativeSquareSituation.relativeSquare_comm h) (thickenedModule ξ h)
    (D.relativeSquareSituation.isStrict_relativeSquare h hh)
    (L.toFlatLift h hh)).trans L.autEquivAutOverIdentity.symm

end ThickeningLift

end AlgebraicGeometry.Space.CoherentSituation

end
