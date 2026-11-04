module

public import StacksFrontier.AlgebraicGeometry.Modules.TildeAssociatedSheaf
public import StacksFrontier.AlgebraicGeometry.Scheme.Affine.GlobalSectionsIsoSpec
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafScalarNormalisation
public import StacksFrontier.Topology.Sheaves.Modules.AssociatedSheaf.Pullback

/-!
# The associated sheaf on an affine open is the pullback of the affine one

Let `V` be an affine open of a scheme `X`. The sheaf of `𝒪_V`-modules attached to a
`Γ(X, V)`-module by the construction of Stacks 01BH along the restriction map
`Γ(X, V) → Γ(V, 𝒪_V)` is the pullback along `V ≅ Spec Γ(X, V)` of the affine construction
`M ↦ M̃` on `Spec Γ(X, V)`, naturally in the module.

## Main definitions

* `AlgebraicGeometry.IsAffineOpen.associatedSheafPullbackIso`: tensor sheafification on `V` along
  `Γ(X, V) → Γ(V, 𝒪_V)` is the pullback along `V ≅ Spec Γ(X, V)` of tensor sheafification along
  `Γ(X, V) → Γ(Spec Γ(X, V), 𝒪)`.
* `AlgebraicGeometry.IsAffineOpen.tildePullbackIsoAssociatedSheafFunctor`:
  `M̃ ↦ (V ≅ Spec Γ(X, V))^* M̃` is the associated-sheaf functor on `V`.

## Implementation notes

The comparison is the composite of four identifications. On `Spec Γ(X, V)` the affine
construction is tensor sheafification along `Γ(X, V) → Γ(Spec Γ(X, V), 𝒪)`, by Stacks 01I7
(`AlgebraicGeometry.tilde.associatedSheafNatIso`); tensor sheafification along a ring map is
extension of scalars followed by tensor sheafification along the identity, by
`Stacks.AssociatedSheaf.associatedSheafFunctorIsoExtendScalars`; pullback of a sheaf associated
to a module is the sheaf associated to the extension of scalars along global sections, by Stacks
01BJ; and the two extensions of scalars so produced compose, by
`ModuleCat.extendScalarsComp`, to extension of scalars along the restriction map of `𝒪_X`,
by `AlgebraicGeometry.IsAffineOpen.Γ_map_isoSpec_hom_comp_ΓSpecIso_inv_hom`.

The affine comparison is read as a morphism of ringed spaces, `V.toRingedSpace ⟶
(Spec Γ(X, V)).toRingedSpace`, because Stacks 01BJ is stated for ringed spaces.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 01BJ](https://stacks.math.columbia.edu/tag/01BJ)
* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace ModuleCat

/-- Extension of scalars along equal ring maps is the same functor. -/
theorem extendScalars_eq_of_eq {R S : Type u} [CommRing R] [CommRing S] {f f' : R →+* S}
    (h : f = f') :
    ModuleCat.extendScalars.{u, u, u} f = ModuleCat.extendScalars.{u, u, u} f' := by
  subst h; rfl

end ModuleCat

namespace AlgebraicGeometry.IsAffineOpen

variable {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)

/-- The isomorphism `V ≅ Spec Γ(X, V)` of an affine open, as a morphism of ringed spaces. -/
abbrev isoSpecRingedSpaceHom :
    V.toScheme.toRingedSpace ⟶ (Spec Γ(X, V)).toRingedSpace :=
  hV.isoSpec.hom.toLRSHom.toShHom

/-- The isomorphism `V ≅ Spec Γ(X, V)` of an affine open is invertible as a morphism of ringed
spaces. -/
instance isIso_isoSpecRingedSpaceHom : IsIso hV.isoSpecRingedSpaceHom :=
  inferInstanceAs (IsIso ((Scheme.forgetToLocallyRingedSpace ⋙
    LocallyRingedSpace.forgetToSheafedSpace).map hV.isoSpec.hom))

/-- **Tensor sheafification on an affine open is the pullback of tensor sheafification on
`Spec Γ(X, V)` along `V ≅ Spec Γ(X, V)`.** -/
def associatedSheafPullbackIso :
    Stacks.AssociatedSheaf.associatedSheafFunctor.{u, u} (Spec Γ(X, V)).toRingedSpace
          (Scheme.ΓSpecIso Γ(X, V)).inv.hom ⋙ modulePullback hV.isoSpecRingedSpaceHom ≅
      Stacks.AssociatedSheaf.associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace
        V.topIso.inv.hom := by
  refine Functor.isoWhiskerRight (Stacks.AssociatedSheaf.associatedSheafFunctorIsoExtendScalars
      (Scheme.ΓSpecIso Γ(X, V)).inv.hom) (modulePullback hV.isoSpecRingedSpaceHom) ≪≫ ?_
  refine Functor.associator _ _ _ ≪≫ ?_
  refine Functor.isoWhiskerLeft (ModuleCat.extendScalars (Scheme.ΓSpecIso Γ(X, V)).inv.hom)
      (Stacks.AssociatedSheaf.ringedSpacePullbackAssociatedSheafIso
        hV.isoSpecRingedSpaceHom) ≪≫ ?_
  refine (Functor.associator _ _ _).symm ≪≫ ?_
  refine Functor.isoWhiskerRight (ModuleCat.extendScalarsComp
      (Scheme.ΓSpecIso Γ(X, V)).inv.hom
      (SheafedSpace.Γ.map hV.isoSpecRingedSpaceHom.op).hom).symm _ ≪≫ ?_
  refine Functor.isoWhiskerRight (eqToIso (ModuleCat.extendScalars_eq_of_eq
      hV.Γ_map_isoSpec_hom_comp_ΓSpecIso_inv_hom)) _ ≪≫ ?_
  exact (Stacks.AssociatedSheaf.associatedSheafFunctorIsoExtendScalars V.topIso.inv.hom).symm

/-- **The associated-sheaf functor on an affine open is the pullback of the affine
associated-sheaf functor along `V ≅ Spec Γ(X, V)`.** -/
def tildePullbackIsoAssociatedSheafFunctor :
    tilde.functor Γ(X, V) ⋙ modulePullback hV.isoSpecRingedSpaceHom ≅
      Stacks.AssociatedSheaf.associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace
        V.topIso.inv.hom :=
  Functor.isoWhiskerRight (tilde.associatedSheafNatIso Γ(X, V))
      (modulePullback hV.isoSpecRingedSpaceHom) ≪≫ hV.associatedSheafPullbackIso

end AlgebraicGeometry.IsAffineOpen

end
