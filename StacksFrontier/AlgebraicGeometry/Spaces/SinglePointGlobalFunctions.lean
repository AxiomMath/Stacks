module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidueFieldDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.SinglePointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceGammaFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers

/-!
# Global functions on a reduced algebraic space with one point

A reduced decent algebraic space over `S` whose space of points is a subsingleton is the
spectrum of a field, Stacks 047Z, so the monomorphism from the spectrum of its residue field is
an isomorphism and its ring of global regular functions is that residue field. For a morphism
between two such spaces the degree of the residue field extension is therefore the dimension of
the global functions of the source over the global functions of the target.

## Main definitions

* `AlgebraicGeometry.Space.globalFunctionsResidueFieldEquiv`: the ring of global regular
  functions of an algebraic space at a point whose residue field spectrum is the space itself,
  identified with that residue field.

## Main results

* `AlgebraicGeometry.Space.isIso_residueFieldMorphism_of_subsingleton_points`: on a reduced
  decent algebraic space with a subsingleton space of points the monomorphism from the spectrum
  of the residue field at a point is an isomorphism.
* `AlgebraicGeometry.Space.residueDegree_eq_finrank_globalFunctions`: the degree of the residue
  field extension of a morphism of such spaces is the dimension of the global functions of the
  source over the global functions of the target.

## References

* [Stacks Project, Tag 047Z](https://stacks.math.columbia.edu/tag/047Z)
* [Stacks Project, Tag 06MG](https://stacks.math.columbia.edu/tag/06MG)
* [Stacks Project, Tag 0EMW](https://stacks.math.columbia.edu/tag/0EMW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

/-- A bijective homomorphism of fields presents an extension of degree one. -/
theorem degreeOfFieldHom_eq_one_of_bijective {K L : Type u} [Field K] [Field L] {φ : K →+* L}
    (hφ : Function.Bijective φ) : degreeOfFieldHom φ = 1 := by
  let : Algebra K L := φ.toAlgebra
  have h : Module.finrank K K = Module.finrank K L :=
    (LinearEquiv.ofBijective (Algebra.linearMap K L) hφ).finrank_eq
  rw [Module.finrank_self] at h
  exact h.symm

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Shortcut instance: instance search for products of presheaves on the big fppf site times
out in Lean v4.35.0. -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_singlePointGlobalFunctions
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (J : Type) : Limits.HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

/-- Shortcut instance: `u`-small products of presheaves on the big fppf site. -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_singlePointGlobalFunctions'
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (J : Type u) : Limits.HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

/-- On a reduced decent algebraic space whose space of points is a subsingleton the
monomorphism from the spectrum of the residue field at a point is an isomorphism.

Such a space is the spectrum of a field by Stacks 047Z, and a monomorphism into the spectrum of
a field with a nonempty source is an isomorphism by Stacks 06MG. -/
theorem isIso_residueFieldMorphism_of_subsingleton_points
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hdec : IsDecentSpace B S hS F) (hsub : Subsingleton (points B S hS F))
    (hred : HasEtaleLocalProperty B S hS F (fun T : Scheme.{u} => IsReduced T))
    (x : points B S hS F) : IsIso (residueFieldMorphism B S hS F hdec x) := by
  obtain ⟨M, k, hk, ⟨e⟩, ⟨ε⟩⟩ :=
    exists_iso_yoneda_spec_of_subsingleton_points B S hS hF hdec ⟨x⟩ hsub hred
  let _ : Field k := hk
  let P := (residueFieldRepresentative B S hS F hdec x).1
  have hmono : Mono (residueFieldMorphism B S hS F hdec x) :=
    (residueFieldRepresentative B S hS F hdec x).2.2
  have hε : Mono ε.hom := ⟨fun g h w => by simpa using congrArg (· ≫ ε.inv) w⟩
  have : Mono (residueFieldMorphism B S hS F hdec x ≫ ε.hom) :=
    @mono_comp _ _ _ _ _ _ hmono _ hε
  have hne : Nonempty (points B S hS (yoneda.obj (P.siteObject B S hS F))) :=
    ⟨(P.tautologicalPoint B S hS F).class B S hS (yoneda.obj (P.siteObject B S hS F))⟩
  rcases isEmpty_points_or_isIso_of_mono_to_fieldSpectrum B S hS M e
      (isAlgebraicSpace_yoneda B S hS (P.siteObject B S hS F))
      (residueFieldMorphism B S hS F hdec x ≫ ε.hom) with hempty | hiso
  · exact absurd hne (not_nonempty_iff.mpr hempty)
  · have hcomp : IsIso ((residueFieldMorphism B S hS F hdec x ≫ ε.hom) ≫ ε.inv) :=
      inferInstance
    rwa [Category.assoc, ε.hom_inv_id, Category.comp_id] at hcomp

/-- **The global functions of an algebraic space which is the spectrum of a residue field.**
When the monomorphism from the spectrum of the residue field at a point of an algebraic space
is an isomorphism, the ring of global regular functions of the space is that residue field. -/
def globalFunctionsResidueFieldEquiv (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hdec : IsDecentSpace B S hS F) (x : points B S hS F)
    (hiso : IsIso (residueFieldMorphism B S hS F hdec x)) :
    globalFunctions' B S hS F ≃+* residueField B S hS F hdec x :=
  (globalFunctionsMapEquiv B S hS
      (ObjectProperty.isoMk _ (asIso (residueFieldMorphism B S hS F hdec x)) :
        representedAlgebraicSpace B S hS
            ((residueFieldRepresentative B S hS F hdec x).1.siteObject B S hS F) ≅
          (⟨F, hF⟩ : AlgebraicSpaces B S hS))).trans
    ((reprGlobalFunctionsEquiv B S hS
        ((residueFieldRepresentative B S hS F hdec x).1.siteObject B S hS F)).trans
      (Scheme.ΓSpecIso (.of (residueField B S hS F hdec x))).commRingCatIsoToRingEquiv)

/-- A global regular function is read in the residue field by restricting it along the
isomorphism from the spectrum of that field. -/
theorem globalFunctionsResidueFieldEquiv_apply (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hdec : IsDecentSpace B S hS F) (x : points B S hS F)
    (hiso : IsIso (residueFieldMorphism B S hS F hdec x)) (a : globalFunctions' B S hS F) :
    globalFunctionsResidueFieldEquiv B S hS F hF hdec x hiso a =
      (Scheme.ΓSpecIso (.of (residueField B S hS F hdec x))).hom.hom
        (reprGlobalFunctionsRestriction B S hS
          ((residueFieldRepresentative B S hS F hdec x).1.siteObject B S hS F)
          (globalFunctionsMap B S hS
            (ObjectProperty.homMk (residueFieldMorphism B S hS F hdec x) :
              representedAlgebraicSpace B S hS
                  ((residueFieldRepresentative B S hS F hdec x).1.siteObject B S hS F) ⟶
                (⟨F, hF⟩ : AlgebraicSpaces B S hS)) a)) :=
  rfl

/-- **The degree of a morphism of one-point reduced algebraic spaces.** For a morphism
`f : Z ⟶ Y` of reduced decent algebraic spaces over `S` whose spaces of points are
subsingletons, the degree of the residue field extension of `f` at a point of `Z` is the
dimension of the ring of global regular functions of `Z` over that of `Y`.

Both spaces are spectra of their residue fields, and the square over `Y` characterizing the
induced homomorphism of residue fields becomes, after taking global functions, the square
identifying the two readings of the extension. -/
theorem residueDegree_eq_finrank_globalFunctions (Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hZ : IsAlgebraicSpace B S hS Z) (hY : IsAlgebraicSpace B S hS Y)
    (hZdec : IsDecentSpace B S hS Z) (hYdec : IsDecentSpace B S hS Y)
    (hZsub : Subsingleton (points B S hS Z)) (hYsub : Subsingleton (points B S hS Y))
    (hZred : HasEtaleLocalProperty B S hS Z (fun T : Scheme.{u} => IsReduced T))
    (hYred : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsReduced T))
    (f : Z ⟶ Y) (z : points B S hS Z) :
    letI : Algebra (globalFunctions' B S hS Y) (globalFunctions' B S hS Z) :=
      (globalFunctionsMap B S hS
        (ObjectProperty.homMk f : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)).toAlgebra
    residueDegree B S hS Z Y hY hZdec hYdec f z =
      Module.finrank (globalFunctions' B S hS Y) (globalFunctions' B S hS Z) := by
  let : Algebra (globalFunctions' B S hS Y) (globalFunctions' B S hS Z) :=
    (globalFunctionsMap B S hS
      (ObjectProperty.homMk f : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)).toAlgebra
  have hZiso := isIso_residueFieldMorphism_of_subsingleton_points B S hS Z hZ hZdec hZsub hZred z
  have hYiso := isIso_residueFieldMorphism_of_subsingleton_points B S hS Y hY hYdec hYsub hYred
    (pointsMap B S hS Z f z)
  set φ := residueFieldHom B S hS Z Y hY hZdec hYdec f z with hφ
  set eZ := globalFunctionsResidueFieldEquiv B S hS Z hZ hZdec z hZiso with heZ
  set eY := globalFunctionsResidueFieldEquiv B S hS Y hY hYdec
    (pointsMap B S hS Z f z) hYiso with heY
  let : Algebra (residueField B S hS Y hYdec (pointsMap B S hS Z f z))
      (residueField B S hS Z hZdec z) := φ.toAlgebra
  have hcompat : ∀ a : globalFunctions' B S hS Y,
      eZ (globalFunctionsMap B S hS
          (ObjectProperty.homMk f : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) a) =
        φ (eY a) := by
    intro a
    have hspec := residueFieldHom_spec B S hS Z Y hY hZdec hYdec f z
    change ∃ _, _ ∧ _ at hspec
    obtain ⟨g, hgspec, hgcomm⟩ := hspec
    have hsq : (ObjectProperty.homMk (yoneda.map g) :
          representedAlgebraicSpace B S hS _ ⟶ representedAlgebraicSpace B S hS _) ≫
        (ObjectProperty.homMk
          (residueFieldMorphism B S hS Y hYdec (pointsMap B S hS Z f z)) :
            representedAlgebraicSpace B S hS _ ⟶ (⟨Y, hY⟩ : AlgebraicSpaces B S hS)) =
        (ObjectProperty.homMk (residueFieldMorphism B S hS Z hZdec z) :
            representedAlgebraicSpace B S hS _ ⟶ (⟨Z, hZ⟩ : AlgebraicSpaces B S hS)) ≫
          ObjectProperty.homMk f :=
      ObjectProperty.hom_ext _ hgcomm
    have hring : globalFunctionsMap B S hS
          (ObjectProperty.homMk (residueFieldMorphism B S hS Z hZdec z) :
            representedAlgebraicSpace B S hS _ ⟶ (⟨Z, hZ⟩ : AlgebraicSpaces B S hS))
          (globalFunctionsMap B S hS
            (ObjectProperty.homMk f : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) a) =
        globalFunctionsMap B S hS (ObjectProperty.homMk (yoneda.map g) :
            representedAlgebraicSpace B S hS _ ⟶ representedAlgebraicSpace B S hS _)
          (globalFunctionsMap B S hS
            (ObjectProperty.homMk
              (residueFieldMorphism B S hS Y hYdec (pointsMap B S hS Z f z)) :
                representedAlgebraicSpace B S hS _ ⟶ (⟨Y, hY⟩ : AlgebraicSpaces B S hS)) a) := by
      rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← globalFunctionsMap_comp,
        ← globalFunctionsMap_comp, hsq]
    have hnat := reprGlobalFunctionsRestriction_naturality B S hS g
      (globalFunctionsMap B S hS
        (ObjectProperty.homMk
          (residueFieldMorphism B S hS Y hYdec (pointsMap B S hS Z f z)) :
            representedAlgebraicSpace B S hS _ ⟶ (⟨Y, hY⟩ : AlgebraicSpaces B S hS)) a)
    have hgmap : (BigFppfOver.toScheme B S hS).map g = Spec.map (CommRingCat.ofHom φ) := hgspec
    have hΓ : ∀ b : Γ(Spec (.of (residueField B S hS Y hYdec (pointsMap B S hS Z f z))), ⊤),
        (Scheme.ΓSpecIso (.of (residueField B S hS Z hZdec z))).hom.hom
            ((Spec.map (CommRingCat.ofHom φ)).appTop.hom b) =
          φ ((Scheme.ΓSpecIso
            (.of (residueField B S hS Y hYdec (pointsMap B S hS Z f z)))).hom.hom b) :=
      fun b => RingHom.congr_fun (congrArg CommRingCat.Hom.hom
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))) b
    rw [heZ, heY, globalFunctionsResidueFieldEquiv_apply, globalFunctionsResidueFieldEquiv_apply,
      hring, hnat, hgmap]
    exact hΓ _
  refine Eq.symm (Algebra.finrank_eq_of_equiv_equiv eY eZ ?_)
  exact RingHom.ext fun a => (hcompat a).symm

end AlgebraicGeometry.Space

end
