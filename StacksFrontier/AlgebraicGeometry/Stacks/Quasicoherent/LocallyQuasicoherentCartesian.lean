module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LocallyQuasiCoherentModulesAndAffines

/-!
# Local quasi-coherence is the cartesian condition along étale maps of affines

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `𝒢` a sheaf of `𝒪_𝒳`-modules
on `𝒳_{étale}`, with sections in the universe `u` of the schemes. Then `𝒢` is locally
quasi-coherent (**Stacks 06WJ**) if and only if for every arrow `φ : y ⟶ y'` of `𝒳` lying over an
étale morphism of affine schemes the comparison `𝒪(y) ⊗_{𝒪(y')} 𝒢(y') ⟶ 𝒢(y)` is an
isomorphism.

This is the "(1) ⇔ (3)" of **Stacks 0H0F** read on `𝒳` itself rather than on its affine
subcategory, using Descent, Proposition 03DX. It is the form in which local quasi-coherence is
transported along direct images in the affine case of **Stacks 075Z**.

## Main results

* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_iff_forall_isIso_restrictionBaseChange`: a
  sheaf of modules on `𝒳_{étale}` is locally quasi-coherent if and only if it is cartesian along
  every arrow lying over an étale morphism of affine schemes.

## References

* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0H0F](https://stacks.math.columbia.edu/tag/0H0F)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 075Z](https://stacks.math.columbia.edu/tag/075Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.PresheafOfModules

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- **A sheaf of modules on `𝒳_{étale}` is locally quasi-coherent if and only if it is cartesian
along every arrow lying over an étale morphism of affine schemes**: for `φ : y ⟶ y'` with `p(y)`,
`p(y')` affine and `p(φ)` étale, `𝒪(y) ⊗_{𝒪(y')} 𝒢(y') ⟶ 𝒢(y)` is an isomorphism. -/
theorem isLocallyQuasicoherent_iff_forall_isIso_restrictionBaseChange
    (G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))) :
    IsLocallyQuasicoherent B E h S hS p hp G.val ↔
      ∀ ⦃y y' : 𝒳⦄ (φ : y ⟶ y'), IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y)) →
        IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y')) →
          Etale ((p ⋙ BigFppfOver.toScheme B S hS).map φ) →
            IsIso (restrictionBaseChange.{v, w, u, u}
              (R := (structureSheaf B S hS p hp (etaleTopology B)
                (etaleTopology_le_topology B)).obj) G.val φ.op) :=
  ⟨fun hG y y' φ hy hy' hφ ↦
    isIso_restrictionBaseChange_of_isLocallyQuasicoherent B E h S hS p hp G.val hG
      (y := ⟨y, hy⟩) (y' := ⟨y', hy'⟩) (ObjectProperty.homMk φ) hφ,
   fun hG ↦ ⟨G.isSheaf, fun x ↦ ⟨restrictModuleToSmallEtale_isSheaf B E h S hS p hp x G.val
      G.isSheaf, SmallEtale.isQuasicoherentOnSite_of_isCartesianOnAffines E _ _ _
        (isCartesianOnAffines_restrictModuleToSmallEtale B E h S hS p hp G _ (Iso.refl _)
          (fun y y' f hf ↦ hG f.hom y.property y'.property hf) x)⟩⟩⟩

end AlgebraicGeometry.Stack
