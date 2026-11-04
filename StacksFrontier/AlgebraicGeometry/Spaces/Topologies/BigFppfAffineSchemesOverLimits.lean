module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfAffineSchemesOverDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ChangeOfBigSites
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FiniteCoproducts
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoveringDisjointUnion

/-!
# Finite limits and finite coproducts of affine schemes over an affine scheme

Let `T` be a big fppf site of algebraic spaces over a scheme `S` and `Ŵ` an affine scheme of its
big fppf site of schemes. The affine schemes over `Ŵ` form a full subcategory of the schemes over
`Ŵ` closed under fibre products, finite coproducts and the terminal object, so they have finite
limits and are finitary extensive. When an object `V` of `(Spaces/X)_fppf` is identified with
the algebraic space represented by an affine scheme `V₀`, the affine schemes over `V` of
`AlgebraicGeometry.BigFppfSpaceSite.AffineSchemesOver` are equivalent to the affine schemes over
`V₀`, so they too have finite limits and are finitary extensive.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.isAffineOverScheme`: affineness of a scheme over `Ŵ`.
* `AlgebraicGeometry.BigFppfSpaceSite.AffineSchemesOver.toAffineOverScheme`: the functor reading
  an affine scheme over `V` as an affine scheme over `V₀`, an equivalence by
  `AlgebraicGeometry.BigFppfSpaceSite.AffineSchemesOver.toAffineOverScheme_isEquivalence`.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.AffineSchemesOver.hasFiniteLimits`: the affine schemes over
  an object `V` identified with an affine scheme have finite limits.
* `AlgebraicGeometry.BigFppfSpaceSite.AffineSchemesOver.finitaryExtensive`: the affine schemes
  over such an object `V` are finitary extensive.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S)

attribute [local instance] BigFppfSite.hasPullbacks_schemes

/-- The big fppf site of schemes of `T` has finite limits. -/
instance hasFiniteLimits_schemes : HasFiniteLimits T.schemeSite.Schemes :=
  schemeSizeBelow_hasFiniteLimits _ T.schemeSite.aleph0_lt_cutoff

/-- The property of a scheme over `Ŵ` that its underlying scheme is affine. -/
def isAffineOverScheme (Ŵ : T.Schemes) : ObjectProperty (Over Ŵ) :=
  fun Y ↦ IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj Y.left)

variable {T}

/-- Affineness of a scheme over `Ŵ` is invariant under isomorphism. -/
instance isAffineOverScheme_isClosedUnderIsomorphisms (Ŵ : T.Schemes) :
    (isAffineOverScheme T Ŵ).IsClosedUnderIsomorphisms where
  of_iso e h :=
    .of_isIso ((Over.forget Ŵ ⋙ BigFppfOver.toScheme T.schemeSite S T.scheme_mem).mapIso e).inv
      (h := h)

/-- A fibre product of affine schemes over `Ŵ` is affine. -/
lemma isAffineOverScheme_pullback {Ŵ : T.Schemes} {Y₀ Y₁ Y₂ : Over Ŵ} (f : Y₁ ⟶ Y₀)
    (g : Y₂ ⟶ Y₀) (h₀ : isAffineOverScheme T Ŵ Y₀) (h₁ : isAffineOverScheme T Ŵ Y₁)
    (h₂ : isAffineOverScheme T Ŵ Y₂) : isAffineOverScheme T Ŵ (pullback f g) := by
  have key {Y : Over Ŵ} (h : isAffineOverScheme T Ŵ Y) :
      IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj ((Over.forget Ŵ).obj Y)) :=
    h
  have := key h₀
  have := key h₁
  have := key h₂
  exact .of_isPullback (((IsPullback.of_hasPullback f g).map (Over.forget Ŵ)).map
    (BigFppfOver.toScheme T.schemeSite S T.scheme_mem))

/-- Affineness of schemes over `Ŵ` is closed under limits of cospans. -/
instance isAffineOverScheme_isClosedUnderPullbacks (Ŵ : T.Schemes) :
    (isAffineOverScheme T Ŵ).IsClosedUnderLimitsOfShape WalkingCospan := by
  refine .mk' ?_
  rintro _ ⟨F, hF⟩
  exact (isAffineOverScheme T Ŵ).prop_of_iso
    (HasLimit.isoOfNatIso (diagramIsoCospan F)).symm
    (isAffineOverScheme_pullback _ _ (hF WalkingCospan.one) (hF WalkingCospan.left)
      (hF WalkingCospan.right))

/-- A finite coproduct of affine schemes over `Ŵ` is affine. -/
instance isAffineOverScheme_isClosedUnderFiniteCoproducts (Ŵ : T.Schemes) :
    (isAffineOverScheme T Ŵ).IsClosedUnderFiniteCoproducts := by
  refine .of_isClosedUnderColimitsOfShape fun J _ ↦ .mk' ?_
  rintro _ ⟨F, hF⟩
  let G := Over.forget Ŵ ⋙ BigFppfOver.toScheme T.schemeSite S T.scheme_mem
  have : ∀ j, IsAffine ((F ⋙ G).obj ⟨j⟩) := fun j => hF ⟨j⟩
  have e : G.obj (colimit F) ≅ ∐ fun j => (F ⋙ G).obj ⟨j⟩ :=
    preservesColimitIso G F ≪≫ HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := F ⋙ G))
  exact .of_isIso e.hom

/-- The affine schemes over `Ŵ` have fibre products. -/
instance hasPullbacks_isAffineOverScheme (Ŵ : T.Schemes) :
    HasPullbacks (isAffineOverScheme T Ŵ).FullSubcategory := inferInstance

/-- The affine schemes over `Ŵ` have finite coproducts. -/
instance hasFiniteCoproducts_isAffineOverScheme (Ŵ : T.Schemes) :
    HasFiniteCoproducts (isAffineOverScheme T Ŵ).FullSubcategory := inferInstance

/-- **The affine schemes over `Ŵ` are finitary extensive.** -/
instance finitaryExtensive_isAffineOverScheme (Ŵ : T.Schemes) :
    FinitaryExtensive (isAffineOverScheme T Ŵ).FullSubcategory :=
  finitaryExtensive_of_preserves_and_reflects_isomorphism (isAffineOverScheme T Ŵ).ι

/-- The identity of an affine scheme `Ŵ` is a terminal affine scheme over `Ŵ`. -/
noncomputable def isTerminalAffineOverScheme {Ŵ : T.Schemes}
    (hŴ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj Ŵ)) :
    IsTerminal (⟨Over.mk (𝟙 Ŵ), hŴ⟩ : (isAffineOverScheme T Ŵ).FullSubcategory) :=
  IsTerminal.ofUniqueHom (fun Y => ObjectProperty.homMk (Over.homMk Y.obj.hom))
    (fun Y f => ObjectProperty.hom_ext _ (Over.OverMorphism.ext (by
      simpa using Over.w f.hom)))

/-- The affine schemes over an affine scheme `Ŵ` have finite limits. -/
instance hasFiniteLimits_isAffineOverScheme {Ŵ : T.Schemes}
    [hŴ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj Ŵ)] :
    HasFiniteLimits (isAffineOverScheme T Ŵ).FullSubcategory :=
  haveI : HasTerminal (isAffineOverScheme T Ŵ).FullSubcategory :=
    (isTerminalAffineOverScheme hŴ).hasTerminal
  hasFiniteLimits_of_hasTerminal_and_pullbacks

namespace AffineSchemesOver

variable {X : T.Spaces} {V : BigFppfSpaceOver T X} (V₀ : T.Schemes)
  (e : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ V.left)

/-- An affine scheme over `V`, read as an affine scheme over `V₀` through `e`. -/
noncomputable def toAffineOverScheme :
    AffineSchemesOver T V ⥤ (isAffineOverScheme T V₀).FullSubcategory where
  obj A := ⟨Over.mk ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).preimage
    (A.obj.hom ≫ e.inv)), A.property⟩
  map {A A'} f := ObjectProperty.homMk (Over.homMk f.hom.left (by
    apply (schemeSpaceFunctor T.schemeSite S T.scheme_mem).map_injective
    simp only [Functor.map_comp, Functor.map_preimage, Over.mk_hom]
    rw [← Category.assoc, CostructuredArrow.w f.hom]))
  map_id A := rfl
  map_comp f g := rfl

/-- The functor `toAffineOverScheme V₀ e` is faithful. -/
instance toAffineOverScheme_faithful : (toAffineOverScheme V₀ e).Faithful where
  map_injective h := ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _
    (congrArg (fun q => q.hom.left) h))

/-- The functor `toAffineOverScheme V₀ e` is full. -/
instance toAffineOverScheme_full : (toAffineOverScheme V₀ e).Full where
  map_surjective {A A'} g := by
    refine ⟨ObjectProperty.homMk (CostructuredArrow.homMk g.hom.left ?_), rfl⟩
    have h := congrArg (schemeSpaceFunctor T.schemeSite S T.scheme_mem).map (Over.w g.hom)
    simp only [toAffineOverScheme, Over.mk_hom, Functor.map_comp, Functor.map_preimage] at h
    simpa using congrArg (· ≫ e.hom) h

/-- The functor `toAffineOverScheme V₀ e` is essentially surjective. -/
instance toAffineOverScheme_essSurj : (toAffineOverScheme V₀ e).EssSurj where
  mem_essImage Y := ⟨⟨CostructuredArrow.mk
      ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).map Y.obj.hom ≫ e.hom), Y.property⟩,
    ⟨ObjectProperty.isoMk _ (Over.isoMk (Iso.refl _) (by
      apply (schemeSpaceFunctor T.schemeSite S T.scheme_mem).map_injective
      simp [toAffineOverScheme]))⟩⟩

/-- The functor `toAffineOverScheme V₀ e` is an equivalence of categories. -/
instance toAffineOverScheme_isEquivalence : (toAffineOverScheme V₀ e).IsEquivalence where

include e in
/-- The affine schemes over an object identified with an affine scheme have finite limits. -/
theorem hasFiniteLimits
    (hV₀ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj V₀)) :
    HasFiniteLimits (AffineSchemesOver T V) :=
  ⟨fun _ _ _ => Adjunction.hasLimitsOfShape_of_equivalence (toAffineOverScheme V₀ e)⟩

include e in
/-- **The affine schemes over an object identified with an affine scheme are finitary
extensive.** -/
theorem finitaryExtensive
    (hV₀ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj V₀)) :
    FinitaryExtensive (AffineSchemesOver T V) :=
  have := hasFiniteLimits V₀ e hV₀
  have : HasFiniteCoproducts (AffineSchemesOver T V) :=
    ⟨fun _ => Adjunction.hasColimitsOfShape_of_equivalence (toAffineOverScheme V₀ e)⟩
  finitaryExtensive_of_preserves_and_reflects_isomorphism (toAffineOverScheme V₀ e)

end AffineSchemesOver

end AlgebraicGeometry.BigFppfSpaceSite

end
