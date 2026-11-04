module

public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.SpecialFibreTransport
public import StacksFrontier.Deformation.Examples.Geometric.OpenSubschemes
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSourceFaithful
public import StacksFrontier.Examples.Deformations.Schemes.SpecialFibre

/-!
# The special fibre of a family, and the faithfulness half of Tag 0E3X

For a morphism `f : X ⟶ Y` of schemes over the residue field and a deformation of it, the two
identifications of the special fibres are cut out by the ideal sheaf `𝔪 𝒪` of the maximal ideal of
the base (`Stacks.BaseAdicFiltration.baseIdeal`). Consequently, if `f_*𝒪_X = 𝒪_Y` and
`R¹f_*𝒪_X = 0`, the source-forgetful functor on deformations of `f` is faithful, which is the
faithfulness half of [Stacks, Tag 0E3X].

## Main results

* `Deformation.Examples.ker_residueSpecMap` — the kernel ideal sheaf of the closed point of the
  spectrum of an object of `𝒞_Λ`.
* `Deformation.Examples.ker_eq_baseIdeal_of_isPullback` — a base change of the closed point cuts
  out the special fibre.
* `Deformation.Examples.ker_specialTarget` and `Deformation.Examples.ker_specialSource` — the two
  identifications of the special fibres of a deformation of a morphism are cut out by `𝔪 𝒪`.
* `Deformation.Examples.isIso_unitToPushforwardUnit_of_deformation` — **`g_*𝒪_U = 𝒪_V` for every
  deformation** `g : U ⟶ V` of `f`, if `f_*𝒪_X = 𝒪_Y` and `R¹f_*𝒪_X = 0`.
* `Deformation.Examples.schemeMorphismSourceForgetful_faithful_of_specialFibre` — **the
  faithfulness half of [Stacks, Tag 0E3X]**.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
* [Stacks Project, Tag 0E3T](https://stacks.math.columbia.edu/tag/0E3T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The ideal sheaf of the closed point of the spectrum of an object of `𝒞_Λ`. -/
theorem ker_residueSpecMap (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    (residueSpecMap A).ker =
      Scheme.IdealSheafData.ofIdealTop
        ((IsLocalRing.maximalIdeal A).map (Scheme.ΓSpecIso (.of A)).inv.hom) := by
  rw [Scheme.ker_of_isAffine]
  congr 1
  have hnat := Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom (Deformation.Artin.residueMap A))
  have happ : (residueSpecMap A).appTop =
      (Scheme.ΓSpecIso (.of A)).hom ≫
        CommRingCat.ofHom (Deformation.Artin.residueMap A) ≫
        (Scheme.ΓSpecIso (.of k)).inv := by
    rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).1
  rw [happ, CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.comp_assoc,
    RingHom.ker_comp_of_injective _ hinj, ← RingHom.comap_ker, CommRingCat.hom_ofHom,
    residueMap_ker]
  exact (Ideal.map_symm (I := IsLocalRing.maximalIdeal (A : Type u))
    (Scheme.ΓSpecIso (CommRingCat.of (A : Type u))).commRingCatIsoToRingEquiv).symm

/-- **A base change of the closed point cuts out the special fibre.** -/
theorem ker_eq_baseIdeal_of_isPullback {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {W Z : Scheme.{u}} (pW : W ⟶ baseSpec A) {i : Z ⟶ W} {q : Z ⟶ Spec (.of k)}
    (h : IsPullback i q pW (residueSpecMap A)) :
    i.ker = Stacks.BaseAdicFiltration.baseIdeal pW (IsLocalRing.maximalIdeal A) := by
  have := residueSpecMap_isClosedImmersion A
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ker_residueSpecMap]
  rfl

section Transport

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-- The identification of the special fibre of the target family is cut out by the maximal
ideal of the base. -/
theorem ker_specialTarget (Q : schemeMorphismDeformationCategory f pX pY hf) :
    Q.hom.target.ker = Stacks.BaseAdicFiltration.baseIdeal Q.left.targetToBase
      (IsLocalRing.maximalIdeal Q.left.base) :=
  ker_eq_baseIdeal_of_isPullback Q.left.targetToBase
    ((specialTargetBaseSpecMap_eq f pX pY hf Q) ▸ Q.hom.target_pullback)

/-- The identification of the special fibre of the source family is cut out by the maximal
ideal of the base. -/
theorem ker_specialSource (Q : schemeMorphismDeformationCategory f pX pY hf) :
    Q.hom.source.ker = Stacks.BaseAdicFiltration.baseIdeal Q.left.sourceToBase
      (IsLocalRing.maximalIdeal Q.left.base) := by
  have hpaste := Q.hom.source_pullback.flip.paste_vert Q.hom.target_pullback
  rw [(schemeMorphismFamilySpecialFiber f pX pY hf).over_base, Q.left.over_base,
    specialTargetBaseSpecMap_eq f pX pY hf Q] at hpaste
  exact ker_eq_baseIdeal_of_isPullback Q.left.sourceToBase hpaste

/-- **[Stacks, Tag 0E3X], the faithfulness input, for a deformation of `f`.** For every
deformation `Q` of a morphism `f : X ⟶ Y` of schemes over the residue field, the comparison
`𝒪 ⟶ (Q.morphism)_* 𝒪` is an isomorphism as soon as `f_*𝒪_X = 𝒪_Y` and `R¹f_*𝒪_X = 0`. -/
theorem isIso_unitToPushforwardUnit_of_deformation
    (h0 : IsIso (C := Y.Modules) (Scheme.Modules.unitToPushforwardUnit f))
    (hR : IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    (Q : schemeMorphismDeformationCategory f pX pY hf) :
    IsIso (C := Q.left.target.Modules)
      (Scheme.Modules.unitToPushforwardUnit Q.left.morphism) := by
  have := Q.left.source_flat
  have := Q.left.target_flat
  have ht : IsClosedImmersion Q.hom.target := specialTarget_isClosedImmersion f pX pY hf Q
  have : IsClosedImmersion Q.hom.source :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion)
      Q.hom.source_pullback ht
  exact Stacks.BaseAdicFiltration.isIso_unitToPushforwardUnit_of_specialFibre
    Q.left.sourceToBase Q.hom.source Q.left.targetToBase Q.left.over_base Q.hom.target f
    (ker_specialSource f pX pY hf Q) (ker_specialTarget f pX pY hf Q)
    Q.hom.source_pullback.w.symm h0 hR

/-- **The comparison on sections is a monomorphism over every open** once the comparison of
structure sheaves is invertible. -/
theorem mono_app_of_isIso_unitToPushforwardUnit {W Z : Scheme.{u}} (g : W ⟶ Z)
    (h : IsIso (C := Z.Modules) (Scheme.Modules.unitToPushforwardUnit g))
    (O : Z.Opens) : Mono (g.app O) := by
  exact ConcreteCategory.mono_of_injective _
    (ConcreteCategory.bijective_of_isIso
      ((Scheme.Modules.unitToPushforwardUnit g).app O)).1

/-- **[Stacks, Tag 0E3X], the faithfulness half.** If `f_*𝒪_X = 𝒪_Y` and `R¹f_*𝒪_X = 0`, then
the source-forgetful functor on deformations of `f` is faithful. -/
theorem schemeMorphismSourceForgetful_faithful_of_specialFibre
    (h0 : IsIso (C := Y.Modules) (Scheme.Modules.unitToPushforwardUnit f))
    (hR : IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    (schemeMorphismSourceForgetful f pX pY hf).Faithful :=
  schemeMorphismSourceForgetful_faithful_of_mono_app f pX pY hf fun Q O =>
    mono_app_of_isIso_unitToPushforwardUnit Q.left.morphism
      (isIso_unitToPushforwardUnit_of_deformation f pX pY hf h0 hR Q) O

end Transport

end Deformation.Examples

end
