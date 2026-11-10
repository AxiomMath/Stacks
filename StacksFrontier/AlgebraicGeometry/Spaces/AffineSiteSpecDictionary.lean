module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Spaces.PrimeResidueFieldSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# The dictionary between affine objects of a big fppf site and commutative rings

Let `B` be a big fppf site and let `Spec R` be one of its objects. An object of the big fppf
category over `Spec R` whose underlying scheme is affine is the spectrum of a commutative ring,
and a morphism between two such objects is a ring map commuting with the two structure
morphisms. This file makes that dictionary explicit and records how it interacts with base
change: the fibre product of `Spec A` over `Spec R` with `Spec R₂` is the spectrum of the
pushout ring, both as an object of the site and as a presheaf of points.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.specOver`: the object `Spec A` of the site, regarded as an
  object over `Spec R` by way of a ring map `φ : R ⟶ A`.
* `AlgebraicGeometry.BigFppfOver.specOverHomEquiv`: the hom dictionary, identifying the
  morphisms `specOver φ ⟶ specOver ψ` with the ring maps `χ` satisfying `ψ ≫ χ = φ`.
* `AlgebraicGeometry.BigFppfOver.pullbackSpecOverIso`: base change of `specOver φ` along
  `Spec.map ρ` is `specOver` of the opposite leg of the pushout square.
* `AlgebraicGeometry.BigFppfOver.relocalizeRestrictSpecOverIso`: the same statement read on
  presheaves of points, that is for the associated algebraic spaces.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_specOver`: every object of the site over `Spec R` whose
  underlying scheme is affine is isomorphic to one of the form `specOver φ`.
* `AlgebraicGeometry.BigFppfOver.isPullback_specOver`: a pushout square of commutative rings
  gives a fibre product square of objects of the site.
* `AlgebraicGeometry.BigFppfOver.relocalizeRestrictSpecOverIso_naturality`: the presheaf-level
  base change isomorphism is natural in the ring over `R`.
* `AlgebraicGeometry.BigFppfSite.contains_spec_of_injective` and
  `AlgebraicGeometry.BigFppfSite.contains_spec_prod`: two size estimates the dictionary needs,
  for a ring embedded in a contained ring and for a product of two contained rings.

## Implementation notes

An object of the big fppf category over `Spec R` is an object of the full subcategory
`B.Schemes` together with a morphism to `B.obj hX`, so all three layers — schemes, the size-cut
full subcategory, and the slice — have to be crossed. The full subcategory inclusion
`B.inclusion` is fully faithful and *creates* fibre products
(`AlgebraicGeometry.schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan`), and `Spec` is
fully faithful, so each layer is crossed by the corresponding reflection lemma:
`CategoryTheory.ObjectProperty.hom_ext` and `AlgebraicGeometry.BigFppfOver.map_toScheme_injective`
for morphisms, `CategoryTheory.IsPullback.of_map_of_faithful` for fibre products, and
`AlgebraicGeometry.Spec.map_injective` for ring maps.

Base change is obtained from Mathlib's `AlgebraicGeometry.isPullback_SpecMap_of_isPushout`
rather than from a tensor product: the pushout is given abstractly as a
`CategoryTheory.IsPushout` square in `CommRingCat`, which is what a consumer gluing algebras
has at hand, and no identification of `A₂` with `A ⊗[R] R₂` is needed anywhere.

The presheaf-level statement is phrased with
`CategoryTheory.OverShriek.relocalizeRestrict` directly, not with the base change functor on
algebraic spaces, so that this file is independent of the algebraic space machinery; the
algebraic space over `Spec R` attached to `specOver φ` is `AlgebraicGeometry.schemeSpace`
of it, whose underlying presheaf is the Yoneda image appearing here by definition.

The two size estimates are proved through the cardinality bridge
`AlgebraicGeometry.BigFppfSite.contains_spec_of_mk_lt_cutoff` and its converse, so neither
re-derives a closure property of the cutoff.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Size estimates -/

namespace BigFppfSite

/-- **A ring that embeds in a contained ring is contained.** Stacks 000R (9): passing to a
subring cannot increase the cardinality. -/
theorem contains_spec_of_injective (B : BigFppfSite.{u}) {A : Type u} [CommRing A]
    {D : Type u} [CommRing D] (hD : B.Contains (Spec (.of D)))
    (ι : A →+* D) (hι : Function.Injective ι) : B.Contains (Spec (.of A)) :=
  contains_spec_of_mk_lt_cutoff B
    ((Cardinal.mk_le_of_injective hι).trans_lt (mk_lt_cutoff_of_contains_spec B hD))

/-- **The spectrum of a product of two contained rings is contained.** Stacks 000R (9): the
cardinality of a product of two rings is below `max {ℵ₀, #A, #C}`, and the cutoff is
uncountable. -/
theorem contains_spec_prod (B : BigFppfSite.{u}) {A C : Type u} [CommRing A]
    [CommRing C] (hA : B.Contains (Spec (.of A))) (hC : B.Contains (Spec (.of C))) :
    B.Contains (Spec (.of (A × C))) := by
  refine contains_spec_of_mk_lt_cutoff B ?_
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  exact (Cardinal.mul_le_max _ _).trans_lt (max_lt (max_lt
    (mk_lt_cutoff_of_contains_spec B hA) (mk_lt_cutoff_of_contains_spec B hC))
    B.aleph0_lt_cutoff)

end BigFppfSite

/-! ### The spectrum of a ring as an object of the site -/

namespace BigFppfOver

/-- The object `Spec A` of a big fppf site, regarded as an object over `Spec R` by way of a
ring map `φ : R ⟶ A`. -/
noncomputable def specOver (B : BigFppfSite.{u}) {R A : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A)) (φ : R ⟶ A) :
    BigFppfOver B (Spec R) hX :=
  BigFppfOver.mk B (Spec R) hX hA (Spec.map φ)

/-- The scheme underlying `AlgebraicGeometry.BigFppfOver.specOver` is `Spec A`. -/
theorem toScheme_obj_specOver (B : BigFppfSite.{u}) {R A : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A)) (φ : R ⟶ A) :
    (BigFppfOver.toScheme B (Spec R) hX).obj (specOver B hX hA φ) = Spec A :=
  rfl

/-- The structure morphism of `AlgebraicGeometry.BigFppfOver.specOver`, read in schemes, is
`Spec.map φ`. -/
theorem inclusion_map_specOver_hom (B : BigFppfSite.{u}) {R A : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A)) (φ : R ⟶ A) :
    B.inclusion.map (specOver B hX hA φ).hom = Spec.map φ :=
  rfl

/-- The structure morphism of `AlgebraicGeometry.BigFppfOver.specOver`, as a morphism of the
size-cut full subcategory. -/
theorem specOver_hom (B : BigFppfSite.{u}) {R A : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A)) (φ : R ⟶ A) :
    (specOver B hX hA φ).hom = (ObjectProperty.homMk (Spec.map φ) : B.obj hA ⟶ B.obj hX) :=
  rfl

/-- The scheme underlying `AlgebraicGeometry.BigFppfOver.specOver` is affine. -/
instance isAffine_toScheme_obj_specOver (B : BigFppfSite.{u}) {R A : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A)) (φ : R ⟶ A) :
    IsAffine ((BigFppfOver.toScheme B (Spec R) hX).obj (specOver B hX hA φ)) :=
  inferInstanceAs (IsAffine (Spec A))

/-- **Every affine object of the site over an affine base is the spectrum of a ring.** The ring
is the ring of global sections of the underlying scheme, and the structure map is read off from
the structure morphism through `AlgebraicGeometry.Scheme.isoSpec`. -/
theorem exists_specOver (B : BigFppfSite.{u}) {R : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (T : BigFppfOver B (Spec R) hX)
    (hT : IsAffine ((BigFppfOver.toScheme B (Spec R) hX).obj T)) :
    ∃ (A : CommRingCat.{u}) (hA : B.Contains (Spec A)) (φ : R ⟶ A),
      Nonempty (T ≅ specOver B hX hA φ) := by
  have : IsAffine T.left.obj := hT
  have hA : B.Contains (Spec Γ(T.left.obj, ⊤)) := by
    change (Spec Γ(T.left.obj, ⊤)).size < B.cutoff
    rw [← Scheme.size_congr T.left.obj.isoSpec]
    exact T.left.property
  refine ⟨Γ(T.left.obj, ⊤), hA,
    Spec.preimage (T.left.obj.isoSpec.inv ≫ B.inclusion.map T.hom), ⟨?_⟩⟩
  refine Over.isoMk (ObjectProperty.isoMk _ T.left.obj.isoSpec) ?_
  apply ObjectProperty.hom_ext
  change T.left.obj.isoSpec.hom ≫
      Spec.map (Spec.preimage (T.left.obj.isoSpec.inv ≫ B.inclusion.map T.hom)) =
    B.inclusion.map T.hom
  rw [Spec.map_preimage, Iso.hom_inv_id_assoc]

/-! ### The hom dictionary -/

/-- The morphism of schemes underlying a morphism of
`AlgebraicGeometry.BigFppfOver.specOver` objects, with its source and target displayed as
spectra.

The underlying morphism is of course just the image under
`AlgebraicGeometry.BigFppfOver.toScheme`; naming it is what makes its source and target
*syntactically* spectra, which is what the `Spec` dictionary below needs in order to rewrite. -/
noncomputable def specOverHomMap (B : BigFppfSite.{u}) {R A C : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A)) (hC : B.Contains (Spec C))
    (φ : R ⟶ A) (ψ : R ⟶ C) (f : specOver B hX hA φ ⟶ specOver B hX hC ψ) :
    Spec A ⟶ Spec C :=
  (BigFppfOver.toScheme B (Spec R) hX).map f

/-- `AlgebraicGeometry.BigFppfOver.specOverHomMap` is the underlying morphism of schemes. -/
theorem toScheme_map_eq_specOverHomMap (B : BigFppfSite.{u}) {R A C : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A)) (hC : B.Contains (Spec C))
    (φ : R ⟶ A) (ψ : R ⟶ C) (f : specOver B hX hA φ ⟶ specOver B hX hC ψ) :
    (BigFppfOver.toScheme B (Spec R) hX).map f = specOverHomMap B hX hA hC φ ψ f :=
  rfl

/-- The triangle satisfied by a morphism of `AlgebraicGeometry.BigFppfOver.specOver` objects,
read in schemes. -/
theorem specOverHomMap_comp (B : BigFppfSite.{u}) {R A C : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A)) (hC : B.Contains (Spec C))
    (φ : R ⟶ A) (ψ : R ⟶ C) (f : specOver B hX hA φ ⟶ specOver B hX hC ψ) :
    specOverHomMap B hX hA hC φ ψ f ≫ Spec.map ψ = Spec.map φ :=
  B.inclusion.congr_map (Over.w f)

/-- **The hom dictionary.** A morphism of the big fppf category over `Spec R` between two
objects of the form `AlgebraicGeometry.BigFppfOver.specOver` is the same thing as a ring map
commuting with the two structure maps. -/
noncomputable def specOverHomEquiv (B : BigFppfSite.{u}) {R A C : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A)) (hC : B.Contains (Spec C))
    (φ : R ⟶ A) (ψ : R ⟶ C) :
    (specOver B hX hA φ ⟶ specOver B hX hC ψ) ≃ { χ : C ⟶ A // ψ ≫ χ = φ } where
  toFun f := ⟨Spec.preimage (specOverHomMap B hX hA hC φ ψ f), by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact specOverHomMap_comp B hX hA hC φ ψ f⟩
  invFun χ := BigFppfOver.homMk B (Spec R) hX hC (Spec.map ψ) (Spec.map χ.1) (by
    change Spec.map χ.1 ≫ Spec.map ψ = Spec.map φ
    rw [← Spec.map_comp, χ.2])
  left_inv f := BigFppfOver.map_toScheme_injective B (Spec R) hX (by
    change Spec.map (Spec.preimage (specOverHomMap B hX hA hC φ ψ f)) =
      specOverHomMap B hX hA hC φ ψ f
    rw [Spec.map_preimage])
  right_inv χ := Subtype.ext (Spec.preimage_map χ.1)

/-- The underlying ring map of a morphism of `AlgebraicGeometry.BigFppfOver.specOver` objects
is the preimage under `Spec` of the underlying morphism of schemes. -/
theorem specOverHomEquiv_coe (B : BigFppfSite.{u}) {R A C : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A)) (hC : B.Contains (Spec C))
    (φ : R ⟶ A) (ψ : R ⟶ C) (f : specOver B hX hA φ ⟶ specOver B hX hC ψ) :
    (specOverHomEquiv B hX hA hC φ ψ f).1 = Spec.preimage (specOverHomMap B hX hA hC φ ψ f) :=
  rfl

/-- The morphism of the site attached to a ring map by
`AlgebraicGeometry.BigFppfOver.specOverHomEquiv` is `Spec.map` of that ring map. -/
theorem toScheme_map_specOverHomEquiv_symm (B : BigFppfSite.{u}) {R A C : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A)) (hC : B.Contains (Spec C))
    (φ : R ⟶ A) (ψ : R ⟶ C) (χ : { χ : C ⟶ A // ψ ≫ χ = φ }) :
    (BigFppfOver.toScheme B (Spec R) hX).map ((specOverHomEquiv B hX hA hC φ ψ).symm χ) =
      Spec.map χ.1 :=
  rfl

/-- `AlgebraicGeometry.BigFppfOver.toScheme_map_specOverHomEquiv_symm` one layer up: the
morphism of the size-cut full subcategory attached to a ring map. -/
theorem specOverHomEquiv_symm_left (B : BigFppfSite.{u}) {R A C : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A)) (hC : B.Contains (Spec C))
    (φ : R ⟶ A) (ψ : R ⟶ C) (χ : { χ : C ⟶ A // ψ ≫ χ = φ }) :
    ((specOverHomEquiv B hX hA hC φ ψ).symm χ).left =
      (ObjectProperty.homMk (Spec.map χ.1) : B.obj hA ⟶ B.obj hC) :=
  rfl

/-! ### Base change -/

/-- **A pushout square of commutative rings gives a fibre product square of objects of the
site.** The corresponding square of schemes is a fibre product square by
`AlgebraicGeometry.isPullback_SpecMap_of_isPushout`, and the inclusion of the size-cut full
subcategory is fully faithful and creates fibre products. -/
theorem isPullback_specOver (B : BigFppfSite.{u}) {R A R₂ A₂ : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A))
    (hX₂ : B.Contains (Spec R₂)) (hA₂ : B.Contains (Spec A₂))
    (φ : R ⟶ A) (ρ : R ⟶ R₂) (φ₂ : R₂ ⟶ A₂) (ψ : A ⟶ A₂)
    (hpo : IsPushout φ ρ ψ φ₂) :
    IsPullback (ObjectProperty.homMk (Spec.map ψ) : B.obj hA₂ ⟶ B.obj hA)
      (specOver B hX₂ hA₂ φ₂).hom (specOver B hX hA φ).hom
      (ObjectProperty.homMk (Spec.map ρ) : B.obj hX₂ ⟶ B.obj hX) :=
  IsPullback.of_map_of_faithful B.inclusion
    (isPullback_SpecMap_of_isPushout φ ρ ψ φ₂ hpo)

/-- **Base change of `Spec A` over `Spec R` along `Spec R₂ ⟶ Spec R` is the spectrum of the
pushout.** -/
noncomputable def pullbackSpecOverIso (B : BigFppfSite.{u}) {R A R₂ A₂ : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A))
    (hX₂ : B.Contains (Spec R₂)) (hA₂ : B.Contains (Spec A₂))
    (φ : R ⟶ A) (ρ : R ⟶ R₂) (φ₂ : R₂ ⟶ A₂) (ψ : A ⟶ A₂)
    (hpo : IsPushout φ ρ ψ φ₂) :
    (Over.pullback (ObjectProperty.homMk (Spec.map ρ) : B.obj hX₂ ⟶ B.obj hX)).obj
        (specOver B hX hA φ) ≅
      specOver B hX₂ hA₂ φ₂ :=
  Over.isoMk (isPullback_specOver B hX hA hX₂ hA₂ φ ρ φ₂ ψ hpo).isoPullback.symm
    (isPullback_specOver B hX hA hX₂ hA₂ φ ρ φ₂ ψ hpo).isoPullback_inv_snd

/-- The morphism of the size-cut full subcategory underlying
`AlgebraicGeometry.BigFppfOver.pullbackSpecOverIso`. -/
theorem pullbackSpecOverIso_hom_left (B : BigFppfSite.{u}) {R A R₂ A₂ : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A))
    (hX₂ : B.Contains (Spec R₂)) (hA₂ : B.Contains (Spec A₂))
    (φ : R ⟶ A) (ρ : R ⟶ R₂) (φ₂ : R₂ ⟶ A₂) (ψ : A ⟶ A₂)
    (hpo : IsPushout φ ρ ψ φ₂) :
    (pullbackSpecOverIso B hX hA hX₂ hA₂ φ ρ φ₂ ψ hpo).hom.left =
      (isPullback_specOver B hX hA hX₂ hA₂ φ ρ φ₂ ψ hpo).isoPullback.inv :=
  rfl

/-- The morphism of the size-cut full subcategory underlying the inverse of
`AlgebraicGeometry.BigFppfOver.pullbackSpecOverIso`. -/
theorem pullbackSpecOverIso_inv_left (B : BigFppfSite.{u}) {R A R₂ A₂ : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A))
    (hX₂ : B.Contains (Spec R₂)) (hA₂ : B.Contains (Spec A₂))
    (φ : R ⟶ A) (ρ : R ⟶ R₂) (φ₂ : R₂ ⟶ A₂) (ψ : A ⟶ A₂)
    (hpo : IsPushout φ ρ ψ φ₂) :
    (pullbackSpecOverIso B hX hA hX₂ hA₂ φ ρ φ₂ ψ hpo).inv.left =
      (isPullback_specOver B hX hA hX₂ hA₂ φ ρ φ₂ ψ hpo).isoPullback.hom :=
  rfl

/-- **The base change isomorphism realizes the ring map `ψ`.** Composing its inverse with the
first projection of the fibre product gives `Spec.map ψ`. -/
theorem toScheme_map_pullbackSpecOverIso_inv_fst (B : BigFppfSite.{u})
    {R A R₂ A₂ : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A))
    (hX₂ : B.Contains (Spec R₂)) (hA₂ : B.Contains (Spec A₂))
    (φ : R ⟶ A) (ρ : R ⟶ R₂) (φ₂ : R₂ ⟶ A₂) (ψ : A ⟶ A₂)
    (hpo : IsPushout φ ρ ψ φ₂) :
    (BigFppfOver.toScheme B (Spec R₂) hX₂).map
          (pullbackSpecOverIso B hX hA hX₂ hA₂ φ ρ φ₂ ψ hpo).inv ≫
        B.inclusion.map (pullback.fst (specOver B hX hA φ).hom
          (ObjectProperty.homMk (Spec.map ρ) : B.obj hX₂ ⟶ B.obj hX)) =
      Spec.map ψ :=
  B.inclusion.congr_map
    (isPullback_specOver B hX hA hX₂ hA₂ φ ρ φ₂ ψ hpo).isoPullback_hom_fst

/-- **The base change isomorphism is a morphism over `Spec R₂`.** Composing its inverse with
the second projection of the fibre product gives `Spec.map φ₂`. -/
theorem toScheme_map_pullbackSpecOverIso_inv_snd (B : BigFppfSite.{u})
    {R A R₂ A₂ : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A))
    (hX₂ : B.Contains (Spec R₂)) (hA₂ : B.Contains (Spec A₂))
    (φ : R ⟶ A) (ρ : R ⟶ R₂) (φ₂ : R₂ ⟶ A₂) (ψ : A ⟶ A₂)
    (hpo : IsPushout φ ρ ψ φ₂) :
    (BigFppfOver.toScheme B (Spec R₂) hX₂).map
          (pullbackSpecOverIso B hX hA hX₂ hA₂ φ ρ φ₂ ψ hpo).inv ≫
        B.inclusion.map (pullback.snd (specOver B hX hA φ).hom
          (ObjectProperty.homMk (Spec.map ρ) : B.obj hX₂ ⟶ B.obj hX)) =
      Spec.map φ₂ :=
  B.inclusion.congr_map
    (isPullback_specOver B hX hA hX₂ hA₂ φ ρ φ₂ ψ hpo).isoPullback_hom_snd

/-! ### Base change of the presheaves of points -/

/-- **Base change at the level of algebraic spaces.** Restriction of the presheaf of points of
`specOver φ` along the localization at `Spec.map ρ` is the presheaf of points of `specOver φ₂`.

This is `AlgebraicGeometry.BigFppfOver.pullbackSpecOverIso` transported through
`CategoryTheory.OverShriek.restrictYonedaIso`. -/
noncomputable def relocalizeRestrictSpecOverIso (B : BigFppfSite.{u})
    {R A R₂ A₂ : CommRingCat.{u}}
    (hX : B.Contains (Spec R)) (hA : B.Contains (Spec A))
    (hX₂ : B.Contains (Spec R₂)) (hA₂ : B.Contains (Spec A₂))
    (φ : R ⟶ A) (ρ : R ⟶ R₂) (φ₂ : R₂ ⟶ A₂) (ψ : A ⟶ A₂)
    (hpo : IsPushout φ ρ ψ φ₂) :
    (CategoryTheory.OverShriek.relocalizeRestrict
          (ObjectProperty.homMk (Spec.map ρ) : B.obj hX₂ ⟶ B.obj hX)).obj
          (yoneda.obj (specOver B hX hA φ)) ≅
      yoneda.obj (specOver B hX₂ hA₂ φ₂) :=
  (CategoryTheory.OverShriek.restrictYonedaIso
      (ObjectProperty.homMk (Spec.map ρ) : B.obj hX₂ ⟶ B.obj hX) (specOver B hX hA φ)).symm ≪≫
    yoneda.mapIso (pullbackSpecOverIso B hX hA hX₂ hA₂ φ ρ φ₂ ψ hpo)

end BigFppfOver

end AlgebraicGeometry

end
