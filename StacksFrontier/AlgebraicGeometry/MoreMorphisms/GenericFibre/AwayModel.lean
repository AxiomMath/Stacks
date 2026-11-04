module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.OpenPushforward
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ModelAssembly

/-!
# Steps D, E and F of Stacks Tag 0559 from a model over a principal open of the base

Steps D, E and F of the first proof of Stacks Tag 0559, assembled over the original base. The
join of those three steps
(`AlgebraicGeometry.exists_open_geometricallyIrreducible_of_specModel`) is stated over a base
whose spectrum carries the affine model, and the model only exists after inverting one nonzero
element `a` of the base ring `R`; so it applies to the restriction of `f : X ⟶ Spec R` over the
principal open `D(a)`, read through Mathlib's identification
`AlgebraicGeometry.basicOpenIsoSpecAway` of `D(a)` with `Spec R_a`. This module performs that
application and pushes the conclusion back to `Spec R`.

## The compatibility hypothesis

The model enters as a domain `S` with a map `φ : R_a ⟶ S` and an `S`-algebra structure on the
residue field `κ(ηₓ)` of `X` at its generic point exhibiting `κ(ηₓ)` as a field of fractions of
`S`. What has to be checked is that the two `R`-algebra structures on `κ(ηₓ)` agree: the one
through the model and the one through `f`. That is the hypothesis `hmodel`, stated on global
sections, where `(Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.Γevaluation (genericPoint X)` is the
canonical map of `R` into `κ(ηₓ)`. It is the hypothesis `hcompat` of
`AlgebraicGeometry.exists_open_geometricallyIrreducible_of_specModel` precomposed with the
localization map of `R`, and that is all that is needed: agreement over `R` gives agreement over
`R_a` because `R_a` is a localization of `R` (`IsLocalization.ringHom_ext`).

The rest of the transport is a chain of identities.

* `basicOpenIsoSpecAway_hom_SpecMap` and `morphismRestrict_ι` together say that the restricted
  morphism followed by the open immersion `Spec R_a ⟶ Spec R` is the open immersion
  `f ⁻¹ᵁ D(a) ⟶ X` followed by `f`.
* `Scheme.ΓSpecIso_inv_naturality` and `Scheme.comp_appTop` turn the canonical map of `R_a` into
  global sections into the canonical map of `R`.
* `Scheme.Γevaluation_naturality` turns evaluation on `f ⁻¹ᵁ D(a)` into evaluation on `X`
  followed by the residue field map of the open immersion.

The residue field map of an open immersion is an isomorphism, so the field of fractions property
transports from `κ(ηₓ)` to the residue field of `f ⁻¹ᵁ D(a)` at its generic point, which is the
one the consumer reads.

## Main results

* `AlgebraicGeometry.exists_open_geometricallyIrreducible_of_awayModel`: **Steps D, E and F of
  Stacks Tag 0559 over a domain base**, from an affine model of the function field defined after
  inverting one element of the base.

## Implementation notes

`MorphismProperty.RespectsIso @GeometricallyIrreducible` is not found by instance search even
though `MorphismProperty.IsStableUnderBaseChange @GeometricallyIrreducible` is, so it is supplied
by hand, as in `AlgebraicGeometry.geometricallyIrreducible_morphismRestrict_iff_forall`.

Points of the open subschemes are bound as points of `W.toScheme`, which is the form the
instances about an open subscheme are stated for.

No Stacks tag is attached: Steps D, E and F are not themselves tags of the source.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559), Steps D, E and F of the
  first proof
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Two morphisms out of a localization away from `a` agree as soon as they agree after
precomposition with the localization map. -/
private theorem hom_ext_of_away {R T : CommRingCat.{u}} (a : R)
    {u w : CommRingCat.of (Localization.Away a) ⟶ T}
    (h : CommRingCat.ofHom (algebraMap ↥R (Localization.Away a)) ≫ u =
      CommRingCat.ofHom (algebraMap ↥R (Localization.Away a)) ≫ w) : u = w :=
  CommRingCat.hom_ext (IsLocalization.ringHom_ext (Submonoid.powers a)
    (congrArg CommRingCat.Hom.hom h))

/-- **Steps D, E and F of Stacks Tag 0559 over a domain base.** Let `R` be a domain and let
`f : X ⟶ Spec R` be a finite type morphism with `X` integral, whose generic point lies over the
generic point of `Spec R` and whose fibre there is geometrically irreducible. Let `a : R` be
nonzero, let `S` be a domain with an injective map `φ : R_a ⟶ S` which is locally of finite type
and geometrically irreducible on spectra, and let the residue field of `X` at its generic point
be a field of fractions of `S` compatibly with the canonical map of `R`. Then `X` has
geometrically irreducible fibres over a nonempty open subscheme of `Spec R`. -/
theorem exists_open_geometricallyIrreducible_of_awayModel {R : CommRingCat.{u}} [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec R) [IsIntegral X] [LocallyOfFiniteType f] [QuasiCompact f]
    (hgen : f (genericPoint X) = genericPoint (Spec R))
    (hgi : GeometricallyIrreducible (f.fiberToSpecResidueField (genericPoint (Spec R))))
    {a : R} (ha : a ≠ 0) {S : CommRingCat.{u}} [IsDomain S]
    (φ : CommRingCat.of (Localization.Away a) ⟶ S) (hφ : Function.Injective φ.hom)
    [LocallyOfFiniteType (Spec.map φ)] [GeometricallyIrreducible (Spec.map φ)]
    [Algebra ↥S ↥(X.residueField (genericPoint X))]
    (hfrac : IsFractionRing ↥S ↥(X.residueField (genericPoint X)))
    (hmodel : CommRingCat.ofHom (algebraMap ↥R (Localization.Away a)) ≫ φ ≫
        CommRingCat.ofHom (algebraMap ↥S ↥(X.residueField (genericPoint X))) =
      (Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.Γevaluation (genericPoint X)) :
    ∃ V : (Spec R).Opens, Nonempty V ∧ GeometricallyIrreducible (f ∣_ V) := by
  have hri : MorphismProperty.RespectsIso @GeometricallyIrreducible.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : IsDomain ↥(CommRingCat.of (Localization.Away a)) :=
    IsLocalization.Away.isDomain (S := Localization.Away a) (x := a) ha
  set W : (Spec R).Opens := PrimeSpectrum.basicOpen a with hWdef
  set e : W.toScheme ≅ Spec (CommRingCat.of (Localization.Away a)) :=
    basicOpenIsoSpecAway a with hedef
  set κ : R ⟶ CommRingCat.of (Localization.Away a) :=
    CommRingCat.ofHom (algebraMap ↥R (Localization.Away a)) with hκdef
  -- Both open subschemes are nonempty, hence irreducible, hence integral.
  have hWmem : genericPoint (Spec R) ∈ W := genericPoint_mem_basicOpen R ha
  have hmem : genericPoint X ∈ f ⁻¹ᵁ W := by
    show f (genericPoint X) ∈ W
    rw [hgen]
    exact hWmem
  have hWne : Nonempty W.toScheme := ⟨⟨genericPoint (Spec R), hWmem⟩⟩
  have hXne : Nonempty (f ⁻¹ᵁ W).toScheme := ⟨⟨genericPoint X, hmem⟩⟩
  -- The generic points of the two open subschemes, and of `Spec R_a`.
  have hj : (f ⁻¹ᵁ W).ι (genericPoint (f ⁻¹ᵁ W).toScheme) = genericPoint X :=
    (f ⁻¹ᵁ W).ι_genericPoint
  have hgW : W.ι (genericPoint W.toScheme) = genericPoint (Spec R) := W.ι_genericPoint
  have hstar : (f ∣_ W ≫ e.hom) ≫ Spec.map κ = (f ⁻¹ᵁ W).ι ≫ f := by
    rw [Category.assoc, hedef, hκdef, basicOpenIsoSpecAway_hom_SpecMap, morphismRestrict_ι]
  have hrestrict : (f ∣_ W) (genericPoint (f ⁻¹ᵁ W).toScheme) = genericPoint W.toScheme := by
    refine W.ι.isOpenEmbedding.injective ?_
    rw [hgW, ← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, hj, hgen]
  have hgA : (f ∣_ W ≫ e.hom) (genericPoint (f ⁻¹ᵁ W).toScheme) =
      genericPoint (Spec (CommRingCat.of (Localization.Away a))) := by
    rw [Scheme.Hom.comp_apply, hrestrict]
    exact apply_genericPoint_of_isIso e
  -- The residue field of the restricted source at its generic point, identified with `κ(ηₓ)`.
  set ε : X.residueField (genericPoint X) ≅
      (f ⁻¹ᵁ W).toScheme.residueField (genericPoint (f ⁻¹ᵁ W).toScheme) :=
    (X.residueFieldCongr hj).symm ≪≫
      asIso (((f ⁻¹ᵁ W).ι).residueFieldMap (genericPoint (f ⁻¹ᵁ W).toScheme)) with hεdef
  have hεhom : ε.hom = (X.residueFieldCongr hj).inv ≫
      ((f ⁻¹ᵁ W).ι).residueFieldMap (genericPoint (f ⁻¹ᵁ W).toScheme) := by
    rw [hεdef]
    simp
  let algSL' : Algebra ↥S
      ↥((f ⁻¹ᵁ W).toScheme.residueField (genericPoint (f ⁻¹ᵁ W).toScheme)) :=
    (CommRingCat.ofHom (algebraMap ↥S ↥(X.residueField (genericPoint X))) ≫ ε.hom).hom.toAlgebra
  have hmapS : CommRingCat.ofHom (algebraMap ↥S
      ↥((f ⁻¹ᵁ W).toScheme.residueField (genericPoint (f ⁻¹ᵁ W).toScheme))) =
      CommRingCat.ofHom (algebraMap ↥S ↥(X.residueField (genericPoint X))) ≫ ε.hom := rfl
  have hfrac' : IsFractionRing ↥S
      ↥((f ⁻¹ᵁ W).toScheme.residueField (genericPoint (f ⁻¹ᵁ W).toScheme)) :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors ↥S)
      (AlgEquiv.ofRingEquiv (f := ε.commRingCatIsoToRingEquiv) fun _ ↦ rfl)
  -- The two `R_a`-algebra structures on the generic residue field agree.
  have hcompat : φ ≫ CommRingCat.ofHom (algebraMap ↥S
        ↥((f ⁻¹ᵁ W).toScheme.residueField (genericPoint (f ⁻¹ᵁ W).toScheme))) =
      (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away a))).inv ≫
        (f ∣_ W ≫ e.hom).appTop ≫
          (f ⁻¹ᵁ W).toScheme.Γevaluation (genericPoint (f ⁻¹ᵁ W).toScheme) := by
    refine hom_ext_of_away a ?_
    have hcongr : X.Γevaluation (genericPoint X) ≫ ε.hom =
        X.Γevaluation ((f ⁻¹ᵁ W).ι (genericPoint (f ⁻¹ᵁ W).toScheme)) ≫
          ((f ⁻¹ᵁ W).ι).residueFieldMap (genericPoint (f ⁻¹ᵁ W).toScheme) := by
      rw [hεhom, ← Category.assoc, Scheme.Γevaluation_residueFieldCongr_inv hj]
    have hRHS : ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.Γevaluation (genericPoint X)) ≫ ε.hom =
        (Scheme.ΓSpecIso R).inv ≫ f.appTop ≫
          X.Γevaluation ((f ⁻¹ᵁ W).ι (genericPoint (f ⁻¹ᵁ W).toScheme)) ≫
            ((f ⁻¹ᵁ W).ι).residueFieldMap (genericPoint (f ⁻¹ᵁ W).toScheme) := by
      rw [Category.assoc, Category.assoc, hcongr]
    rw [← hκdef, Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop_assoc, hstar,
      Scheme.Hom.comp_appTop_assoc, ← Scheme.Γevaluation_naturality, hmapS]
    refine Eq.trans ?_ hRHS
    rw [← hmodel]
    simp only [Category.assoc]
  -- The geometrically irreducible generic fibre, read over `Spec R_a`.
  have hfib : GeometricallyIrreducible ((f ∣_ W ≫ e.hom).fiberToSpecResidueField
      (genericPoint (Spec (CommRingCat.of (Localization.Away a))))) := by
    rw [← apply_genericPoint_of_isIso e]
    refine (prop_fiberToSpecResidueField_comp_iso_iff (P := @GeometricallyIrreducible)
      (f ∣_ W) e _).mpr ((prop_fiberToSpecResidueField_of_morphismRestrict
        (P := @GeometricallyIrreducible) f W _).mpr ?_)
    rwa [hgW]
  obtain ⟨V, hVne, hV⟩ := exists_open_geometricallyIrreducible_of_specModel φ hφ
    (f ∣_ W ≫ e.hom) hgA hfrac' hcompat hfib
  exact exists_open_geometricallyIrreducible_of_restrictIsoSpec f e hVne hV

end AlgebraicGeometry

end
