module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeSpecOpenRestriction.InverseImageIso
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraSheafIsomorphism

/-!
# Restriction of a quasi-coherent algebra to an open subscheme

Let `j : U ⟶ T` be an open immersion of schemes and let `B` be a sheaf of commutative
`𝒪_T`-algebras.  The base change `(algebraPullback j).obj B = j⁻¹B ⊗_{j⁻¹𝒪_T} 𝒪_U` ought to be
the restriction of `B` to `U`, and this file proves it: the extension of scalars is along the
structural map `j⁻¹𝒪_T ⟶ 𝒪_U`, which is an isomorphism by
`AlgebraicGeometry.isIso_inverseImageStructureMap_of_isOpenImmersion`, so no tensor product is
computed.

The restriction is given its own name `Stacks.AffineAlgebraEquivalence.restrictAlgebra`, built
from the *naive* inverse image, whose sections over an open `W` of `U` are the sections of `B`
over `j(W)`.  Its underlying `𝒪_U`-module is then *equal*, not merely isomorphic, to the
restriction `Scheme.Modules.restrictFunctor j` of the underlying `𝒪_T`-module of `B`, because
Mathlib defines that restriction by the same naive formula.  Quasi-coherence of the restriction
is therefore Mathlib's `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor`, and
quasi-coherence of the base change follows by transport along the isomorphism.

## Main definitions

* `Stacks.AffineAlgebraEquivalence.restrictAlgebraStructureMap` is the inverse of the naive
  structural map, i.e. the morphism `𝒪_U ⟶ j⁻¹𝒪_T` whose sections are the inverses of
  `AlgebraicGeometry.Scheme.Hom.appIso`.
* `Stacks.AffineAlgebraEquivalence.restrictAlgebra` is the restriction of an algebra sheaf to an
  open subscheme, built from the naive inverse image.
* `Stacks.AffineAlgebraEquivalence.algebraPullbackIsoRestrictAlgebra` identifies the base change
  of an algebra sheaf along an open immersion with its restriction.

## Main results

* `Stacks.AffineAlgebraEquivalence.underlyingModule_restrictAlgebra`: the underlying module of
  the restriction of an algebra sheaf is the restriction of its underlying module, by `rfl`.
* `Stacks.AffineAlgebraEquivalence.isQuasicoherent_algebraPullback_of_isOpenImmersion`:
  **Stacks Tag 01LX part (2) for an open immersion.**  The base change of a quasi-coherent
  `𝒪_T`-algebra along an open immersion is quasi-coherent.
* `Stacks.AffineAlgebraEquivalence.isQuasicoherent_restrict_underlyingModule`: conversely, if the
  base change of `B` along `j` is quasi-coherent then the restriction to `U` of the underlying
  module of `B` is quasi-coherent.  This is the form in which the locality of quasi-coherence is
  applied.

## Implementation notes

The comparison of the two inverse images is never computed.  `algebraPullbackIsoRestrictAlgebra`
uses the canonical isomorphism `CategoryTheory.Adjunction.leftAdjointUniq` between the sheafified
inverse image and the naive one, and the only property of it that is used is the identity
`CategoryTheory.Adjunction.homEquiv_symm_eq_leftAdjointUniq_comp` relating the two adjuncts of
the comorphism `j.c`, together with its naturality.  The leg
`Stacks.AffineAlgebraEquivalence.algebraPullbackMap` of the defining pushout square is an
isomorphism by `CategoryTheory.IsPushout.isIso_inl_of_isIso`, the other leg being the structural
map.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.RelativeSpec.AlgebraSheaf

universe u

namespace Stacks.AffineAlgebraEquivalence

variable {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]

/-! ### The restriction of an algebra sheaf to an open subscheme -/

/-- The morphism `𝒪_U ⟶ j⁻¹𝒪_T` to the naive inverse image of the structure sheaf whose sections
over an open `W` of `U` are the inverse of the canonical isomorphism `Γ(T, j(W)) ≅ Γ(U, W)`. -/
public noncomputable def restrictAlgebraStructureMap :
    U.sheaf ⟶ (j.isOpenEmbedding.sheafPullback CommRingCat.{u}).obj T.sheaf :=
  ⟨{ app := fun W ↦ (j.appIso W.unop).inv
     naturality := fun {_ _} i ↦ j.appIso_inv_naturality i }⟩

/-- **The restriction of an algebra sheaf to an open subscheme.** Its sections over an open `W`
of `U` are the sections of `B` over `j(W)`, with the `Γ(U, W)`-algebra structure transported
along `AlgebraicGeometry.Scheme.Hom.appIso`. -/
public noncomputable def restrictAlgebra (B : Stacks.RelativeSpec.AlgebraSheaf.{u} T) :
    Stacks.RelativeSpec.AlgebraSheaf.{u} U :=
  Under.mk (restrictAlgebraStructureMap j ≫
    (j.isOpenEmbedding.sheafPullback CommRingCat.{u}).map B.hom)

/-- **The underlying module of the restriction of an algebra sheaf is the restriction of its
underlying module.** Both are the sections of `B` over the images `j(W)`, regarded as modules
over `Γ(U, W)` through `AlgebraicGeometry.Scheme.Hom.appIso` and the structure morphism of `B`;
the two are equal by definition. -/
public theorem underlyingModule_restrictAlgebra (B : Stacks.RelativeSpec.AlgebraSheaf.{u} T) :
    underlyingModule (restrictAlgebra j B) =
      (Scheme.Modules.restrictFunctor j).obj (underlyingModule B) :=
  rfl

/-- The restriction of a quasi-coherent algebra sheaf to an open subscheme is
quasi-coherent. -/
public instance isQuasicoherent_restrictAlgebra (B : Stacks.RelativeSpec.AlgebraSheaf.{u} T)
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent B] :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (restrictAlgebra j B) :=
  Scheme.Modules.isQuasicoherent_restrictFunctor j (underlyingModule B)

/-! ### Identification of the base change with the restriction -/

/-- Composing `Stacks.AffineAlgebraEquivalence.restrictAlgebraStructureMap` with the naive
structural map gives the identity: on sections it is the composite of the two directions of
`AlgebraicGeometry.Scheme.Hom.appIso`. -/
public theorem restrictAlgebraStructureMap_comp_naive :
    restrictAlgebraStructureMap j ≫ naiveInverseImageStructureMap j = 𝟙 U.sheaf := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun V ↦ ?_)
  obtain ⟨W⟩ := V
  exact appIso_inv_comp_naiveInverseImageStructureMap_app j W

/-- The canonical isomorphism between the sheafified inverse image of sheaves of commutative
rings along `j` and the naive one, obtained from uniqueness of left adjoints. -/
public noncomputable abbrev inverseImageUniq :
    TopCat.Sheaf.pullback CommRingCat.{u} j.base ≅
      j.isOpenEmbedding.sheafPullback CommRingCat.{u} :=
  Adjunction.leftAdjointUniq (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} j.base)
    (naiveInverseImageAdjunction j)

/-- Transporting the structural map `j⁻¹𝒪_T ⟶ 𝒪_U` to the naive inverse image gives the naive
structural map. -/
public theorem inverseImageUniq_inv_comp_inverseImageStructureMap :
    (inverseImageUniq j).inv.app T.sheaf ≫ inverseImageStructureMap j =
      naiveInverseImageStructureMap j := by
  refine Eq.trans (congrArg (fun k ↦ (inverseImageUniq j).inv.app T.sheaf ≫ k)
    (Adjunction.homEquiv_symm_eq_leftAdjointUniq_comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} j.base)
      (naiveInverseImageAdjunction j) (comorphismSheafHom j))) ?_
  rw [← Category.assoc, (inverseImageUniq j).inv_hom_id_app, Category.id_comp]
  rfl

/-- The canonical map from the inverse image of an algebra sheaf to its base change along an open
immersion is an isomorphism: it is one leg of a pushout square whose other leg is the structural
map, which is an isomorphism. -/
public theorem isIso_algebraPullbackMap_app_of_isOpenImmersion
    (B : Stacks.RelativeSpec.AlgebraSheaf.{u} T) : IsIso ((algebraPullbackMap j).app B) :=
  (algebraPullback_isPushout j B).isIso_inl_of_isIso

/-- The canonical map from the inverse image of an algebra sheaf to its base change along an open
immersion, as an isomorphism. -/
public noncomputable def algebraPullbackMapIso
    (B : Stacks.RelativeSpec.AlgebraSheaf.{u} T) :
    (TopCat.Sheaf.pullback CommRingCat.{u} j.base).obj B.right ≅
      ((algebraPullback j).obj B).right :=
  @asIso _ _ _ _ _ (isIso_algebraPullbackMap_app_of_isOpenImmersion j B)

/-- The isomorphism of sheaves of rings between the restriction of `B` to `U` and the base change
of `B` along `j`: the comparison of the two inverse images, followed by the canonical map of the
defining pushout square. -/
public noncomputable def restrictAlgebraRingIso
    (B : Stacks.RelativeSpec.AlgebraSheaf.{u} T) :
    (restrictAlgebra j B).right ≅ ((algebraPullback j).obj B).right :=
  ((inverseImageUniq j).app B.right).symm ≪≫ algebraPullbackMapIso j B

/-- The structure morphisms are compatible with
`Stacks.AffineAlgebraEquivalence.restrictAlgebraRingIso`. -/
public theorem restrictAlgebra_hom_comp_restrictAlgebraRingIso
    (B : Stacks.RelativeSpec.AlgebraSheaf.{u} T) :
    (restrictAlgebraStructureMap j ≫
          (j.isOpenEmbedding.sheafPullback CommRingCat.{u}).map B.hom) ≫
        ((inverseImageUniq j).inv.app B.right ≫ (algebraPullbackMap j).app B) =
      ((algebraPullback j).obj B).hom := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun k ↦ restrictAlgebraStructureMap j ≫ k)
    (Category.assoc ((j.isOpenEmbedding.sheafPullback CommRingCat.{u}).map B.hom)
      ((inverseImageUniq j).inv.app B.right) ((algebraPullbackMap j).app B)).symm) ?_
  refine Eq.trans (congrArg (fun k ↦ restrictAlgebraStructureMap j ≫
      k ≫ (algebraPullbackMap j).app B) ((inverseImageUniq j).inv.naturality B.hom)) ?_
  refine Eq.trans (congrArg (fun k ↦ restrictAlgebraStructureMap j ≫ k)
    (Category.assoc ((inverseImageUniq j).inv.app T.sheaf)
      ((TopCat.Sheaf.pullback CommRingCat.{u} j.base).map B.hom)
      ((algebraPullbackMap j).app B))) ?_
  refine Eq.trans (congrArg (fun k ↦ restrictAlgebraStructureMap j ≫
      (inverseImageUniq j).inv.app T.sheaf ≫ k) (algebraPullback_isPushout j B).w) ?_
  refine Eq.trans (congrArg (fun k ↦ restrictAlgebraStructureMap j ≫ k)
    (Category.assoc ((inverseImageUniq j).inv.app T.sheaf) (inverseImageStructureMap j)
      ((algebraPullback j).obj B).hom).symm) ?_
  refine Eq.trans (congrArg (fun k ↦ restrictAlgebraStructureMap j ≫
      k ≫ ((algebraPullback j).obj B).hom)
    (inverseImageUniq_inv_comp_inverseImageStructureMap j)) ?_
  refine Eq.trans (Category.assoc (restrictAlgebraStructureMap j)
    (naiveInverseImageStructureMap j) ((algebraPullback j).obj B).hom).symm ?_
  refine Eq.trans (congrArg (fun k ↦ k ≫ ((algebraPullback j).obj B).hom)
    (restrictAlgebraStructureMap_comp_naive j)) ?_
  exact Category.id_comp _

/-- **The base change of an algebra sheaf along an open immersion is its restriction.** -/
public noncomputable def algebraPullbackIsoRestrictAlgebra
    (B : Stacks.RelativeSpec.AlgebraSheaf.{u} T) :
    restrictAlgebra j B ≅ (algebraPullback j).obj B :=
  Under.isoMk (restrictAlgebraRingIso j B)
    (restrictAlgebra_hom_comp_restrictAlgebraRingIso j B)

/-- **Stacks Tag 01LX part (2) for an open immersion.** The base change along an open immersion
of a quasi-coherent sheaf of commutative `𝒪_T`-algebras is a quasi-coherent sheaf of commutative
`𝒪_U`-algebras. -/
public theorem isQuasicoherent_algebraPullback_of_isOpenImmersion
    (B : Stacks.RelativeSpec.AlgebraSheaf.{u} T)
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent B] :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent ((algebraPullback j).obj B) :=
  Stacks.RelativeSpec.AlgebraSheaf.isQuasicoherent_of_iso
    (algebraPullbackIsoRestrictAlgebra j B) (isQuasicoherent_restrictAlgebra j B)

/-- Conversely, if the base change of `B` along an open immersion is quasi-coherent, then the
restriction to `U` of the underlying module of `B` is quasi-coherent.  This is the form in which
quasi-coherence on the members of an open covering is fed to
`Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_of_presentations`. -/
public theorem isQuasicoherent_restrict_underlyingModule
    (B : Stacks.RelativeSpec.AlgebraSheaf.{u} T)
    (h : Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent ((algebraPullback j).obj B)) :
    ((Scheme.Modules.restrictFunctor j).obj (underlyingModule B)).IsQuasicoherent :=
  Stacks.RelativeSpec.AlgebraSheaf.isQuasicoherent_of_iso
    (algebraPullbackIsoRestrictAlgebra j B).symm h

end Stacks.AffineAlgebraEquivalence

end
