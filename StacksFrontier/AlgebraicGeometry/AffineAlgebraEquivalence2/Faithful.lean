module

public import Mathlib.AlgebraicGeometry.Gluing
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.Basic

/-!
# Faithfulness of the pushforward functor on schemes affine over a base

Let `S` be a scheme. A morphism `u : X ⟶ Y` of schemes over `S` whose target is affine over `S`
is determined by the induced map `Y.hom_* 𝒪_Y ⟶ X.hom_* 𝒪_X` of pushed-forward structure
sheaves. Consequently the functor `X ↦ f_* 𝒪_X` of Stacks Tag 01SA is faithful.

## Main results

* `left_eq_of_pushforwardAlgebraMap_eq`: a morphism over `S` into a scheme affine over `S` is
  determined by the canonical map on pushed-forward structure sheaves.
* `faithful_affinePushforwardAlgebraFunctor` and
  `faithful_affineQuasicoherentPushforwardFunctor`: the functor `X ↦ f_* 𝒪_X` is faithful.

## Implementation notes

The argument is local on `S`. Let `V` be an affine open of `S`, let `W = X.hom ⁻¹ᵁ V` and let
`U = Y.hom ⁻¹ᵁ V`; the latter is affine because `Y.hom` is an affine morphism. The sections over
`V` of the map on pushed-forward structure sheaves are `u.left.appLE U W`
(`pushforwardAlgebraMap_app`), which by `AlgebraicGeometry.Scheme.Hom.resLE_app_top` are, up to
the canonical identifications `Scheme.Opens.topIso`, the global sections of the restricted
morphism `u.left.resLE U W : W.toScheme ⟶ U.toScheme`. Since `U.toScheme` is affine,
`AlgebraicGeometry.ext_of_isAffine` identifies the restricted morphisms, hence the composites
`W.ι ≫ u.left`, and `AlgebraicGeometry.Scheme.hom_ext_of_forall` glues these identifications
over an affine open cover of `S`.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.AffineAlgebraEquivalence

/-! ### Restriction of a morphism over the base to an affine open of the base -/

variable {S : Scheme.{u}}

/-- The restriction of a morphism `u` of schemes over `S` to the preimages of an open `V` of the
base. -/
public noncomputable abbrev resLEOver {X Y : Over S} (u : X ⟶ Y) (V : S.Opens) :
    (X.hom ⁻¹ᵁ V).toScheme ⟶ (Y.hom ⁻¹ᵁ V).toScheme :=
  u.left.resLE (Y.hom ⁻¹ᵁ V) (X.hom ⁻¹ᵁ V) (preimage_le_preimage_preimage u V)

/-- The global sections of the restriction `resLEOver u V` are, up to the canonical
identifications of the sections of a scheme over an open with the global sections of the
corresponding open subscheme, the sections over `V` of the canonical map on pushed-forward
structure sheaves. -/
public theorem resLEOver_appTop {X Y : Over S} (u : X ⟶ Y) (V : S.Opens) :
    (resLEOver u V).appTop =
      (Y.hom ⁻¹ᵁ V).topIso.hom ≫ (pushforwardAlgebraMap u).right.hom.app (op V) ≫
        (X.hom ⁻¹ᵁ V).topIso.inv := by
  rw [pushforwardAlgebraMap_app u V (preimage_le_preimage_preimage u V)]
  exact Scheme.Hom.resLE_app_top _ _

/-- A morphism of schemes over `S` whose target is affine over `S` is determined by the
canonical map it induces on pushed-forward structure sheaves. -/
public theorem left_eq_of_pushforwardAlgebraMap_eq {X Y : Over S} [IsAffineHom Y.hom]
    {u v : X ⟶ Y} (h : pushforwardAlgebraMap u = pushforwardAlgebraMap v) :
    u.left = v.left := by
  refine Scheme.hom_ext_of_forall u.left v.left fun x ↦ ?_
  have hx : X.hom.base x ∈ (⨆ i : S.affineOpens, (i : S.Opens)) := by
    rw [iSup_affineOpens_eq_top S]; trivial
  obtain ⟨V, hxV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨X.hom ⁻¹ᵁ (V : S.Opens), hxV, ?_⟩
  have hU : IsAffineOpen (Y.hom ⁻¹ᵁ (V : S.Opens)) := V.2.preimage Y.hom
  have hres : resLEOver u (V : S.Opens) = resLEOver v (V : S.Opens) := by
    have : IsAffine (Y.hom ⁻¹ᵁ (V : S.Opens)).toScheme := hU
    refine ext_of_isAffine ?_
    rw [resLEOver_appTop, resLEOver_appTop, h]
  rw [← Scheme.Hom.resLE_comp_ι u.left (preimage_le_preimage_preimage u (V : S.Opens)),
    ← Scheme.Hom.resLE_comp_ι v.left (preimage_le_preimage_preimage v (V : S.Opens))]
  exact congrArg (· ≫ _) hres

/-- A morphism of schemes over `S` whose target is affine over `S` is determined by the
canonical map it induces on pushed-forward structure sheaves. -/
public theorem eq_of_pushforwardAlgebraMap_eq {X Y : Over S} [IsAffineHom Y.hom]
    {u v : X ⟶ Y} (h : pushforwardAlgebraMap u = pushforwardAlgebraMap v) : u = v :=
  Over.OverMorphism.ext (left_eq_of_pushforwardAlgebraMap_eq h)

/-! ### Faithfulness of the pushforward functor -/

/-- The functor `X ↦ f_* 𝒪_X` on the schemes affine over `S` is faithful. -/
public instance faithful_affinePushforwardAlgebraFunctor (S : Scheme.{u}) :
    (affinePushforwardAlgebraFunctor S).Faithful where
  map_injective {X Y} {f g} h := by
    have hX : IsAffineHom (unop X).obj.hom := X.unop.property
    have hfg : f.unop = g.unop :=
      ObjectProperty.hom_ext _ (eq_of_pushforwardAlgebraMap_eq h)
    exact Quiver.Hom.unop_inj hfg

/-- The functor `X ↦ f_* 𝒪_X` from the schemes affine over `S` to the quasi-coherent
`𝒪_S`-algebras is faithful. -/
public instance faithful_affineQuasicoherentPushforwardFunctor (S : Scheme.{u}) :
    (affineQuasicoherentPushforwardFunctor S).Faithful :=
  Functor.Faithful.of_comp_iso (affineQuasicoherentPushforwardFunctorCompι S)

end Stacks.AffineAlgebraEquivalence

end
