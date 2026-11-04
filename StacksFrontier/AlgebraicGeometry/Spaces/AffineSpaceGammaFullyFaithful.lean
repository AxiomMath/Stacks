module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GlobalFunctionsColimit

/-!
# Global functions are fully faithful on affine algebraic spaces

Let `X` and `Y` be affine algebraic spaces over a scheme `S` of a big fppf site. A morphism
`f : X ⟶ Y` of algebraic spaces over `S` which induces a bijection
`Γ(Y, 𝒪_Y) → Γ(X, 𝒪_X)` on rings of global regular functions is an isomorphism.

## Main results

* `AlgebraicGeometry.Space.pullbackToGlobalFunctions_eq`: pullback of regular functions along a
  morphism into a representable algebraic space is
  `AlgebraicGeometry.Space.globalFunctionsMap` read through
  `AlgebraicGeometry.Space.reprGlobalFunctionsEquiv`.
* `AlgebraicGeometry.Space.reprGlobalFunctionsRestriction_naturality`: restriction to the
  identity chart intertwines `AlgebraicGeometry.Space.globalFunctionsMap` along a morphism of
  the site with pullback of regular functions along the underlying morphism of schemes.
* `AlgebraicGeometry.Space.isIso_of_bijective_globalFunctionsMap`: a morphism of affine
  algebraic spaces which is bijective on global regular functions is an isomorphism.

## References

* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- A morphism of affine schemes which is bijective on global regular functions is an
isomorphism. -/
theorem isIso_of_bijective_appTop {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (k : X ⟶ Y)
    (hk : Function.Bijective k.appTop.hom) : IsIso k := by
  have _ : IsIso k.appTop := (ConcreteCategory.isIso_iff_bijective k.appTop).mpr hk
  have _ : IsIso X.toSpecΓ := IsAffine.affine
  have _ : IsIso Y.toSpecΓ := IsAffine.affine
  have heq : k = X.toSpecΓ ≫ Spec.map k.appTop ≫ inv Y.toSpecΓ := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality k, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  rw [heq]
  infer_instance

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Pullback of regular functions against `globalFunctionsMap` -/

/-- Pullback of regular functions along a morphism into a representable algebraic space is
`AlgebraicGeometry.Space.globalFunctionsMap`, read through the identification
`AlgebraicGeometry.Space.reprGlobalFunctionsEquiv` of the global functions of a representable
algebraic space with the regular functions on the representing scheme. -/
theorem pullbackToGlobalFunctions_eq (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (f : X ⟶ representedAlgebraicSpace B S hS T) :
    pullbackToGlobalFunctions B S hS X T f =
      (globalFunctionsMap B S hS f).comp
        (reprGlobalFunctionsEquiv B S hS T).symm.toRingHom := by
  refine RingHom.ext fun s => Subtype.ext (funext fun V => ?_)
  have hval : ((reprGlobalFunctionsEquiv B S hS T).symm s).val (op (idChart B S hS T)) = s :=
    (reprGlobalFunctionsEquiv B S hS T).apply_symm_apply s
  have h : (globalFunctionsMap B S hS f
        ((reprGlobalFunctionsEquiv B S hS T).symm s)).val (op V.unop)
      = ((BigFppfOver.toScheme B S hS).map
          (yoneda.preimage (V.unop.obj.hom ≫ f.hom))).appTop.hom s := by
    have h0 := globalFunctionsMap_val_of_chartHom B S hS
      (U := representedAlgebraicSpace B S hS T) (V := X) f
      ((reprGlobalFunctionsEquiv B S hS T).symm s) V.unop (idChart B S hS T)
      (CostructuredArrow.homMk (yoneda.preimage (V.unop.obj.hom ≫ f.hom))
        (show yoneda.map (yoneda.preimage (V.unop.obj.hom ≫ f.hom)) ≫ 𝟙 (yoneda.obj T)
            = V.unop.obj.hom ≫ f.hom by
          rw [Category.comp_id]; exact yoneda.map_preimage _))
    rwa [hval] at h0
  exact ((pullbackToGlobalFunctions_apply_chart B S hS X T f V.unop s).trans
    (RingHom.congr_fun rfl _)).trans h.symm

/-- Restriction to the identity chart is natural in the representing object: for a morphism
`g : T ⟶ T'` of the site, restriction to the identity chart intertwines pullback of global
functions along the Yoneda image of `g` with pullback of regular functions along the underlying
morphism of schemes. -/
theorem reprGlobalFunctionsRestriction_naturality {T T' : BigFppfOver B S hS} (g : T ⟶ T')
    (s : globalFunctions B S hS (yoneda.obj T')) :
    reprGlobalFunctionsRestriction B S hS T
        (globalFunctionsMap B S hS
          (ObjectProperty.homMk (yoneda.map g) :
            representedAlgebraicSpace B S hS T ⟶ representedAlgebraicSpace B S hS T') s)
      = ((BigFppfOver.toScheme B S hS).map g).appTop.hom
          (reprGlobalFunctionsRestriction B S hS T' s) :=
  globalFunctionsMap_val_of_chartHom B S hS
    (U := representedAlgebraicSpace B S hS T') (V := representedAlgebraicSpace B S hS T)
    (ObjectProperty.homMk (yoneda.map g)) s (idChart B S hS T) (idChart B S hS T')
    (CostructuredArrow.homMk g
      (show yoneda.map g ≫ 𝟙 (yoneda.obj T') = 𝟙 (yoneda.obj T) ≫ yoneda.map g by
        rw [Category.comp_id, Category.id_comp]))

/-! ### The criterion -/

/-- Pullback of global functions along an isomorphism of algebraic spaces is bijective. -/
theorem bijective_globalFunctionsMap_of_isIso {X Y : AlgebraicSpaces B S hS} (e : X ≅ Y) :
    Function.Bijective (globalFunctionsMap B S hS e.hom) :=
  (globalFunctionsMapEquiv B S hS e).bijective

/-- The Yoneda image of an isomorphism of the site is an isomorphism of algebraic spaces. -/
theorem isIso_homMk_yoneda_map {T T' : BigFppfOver B S hS} (g : T ⟶ T') [IsIso g] :
    IsIso (ObjectProperty.homMk (yoneda.map g) :
      representedAlgebraicSpace B S hS T ⟶ representedAlgebraicSpace B S hS T') := by
  refine ⟨⟨ObjectProperty.homMk (yoneda.map (inv g)), ?_, ?_⟩⟩ <;>
    apply ObjectProperty.hom_ext <;>
    show yoneda.map _ ≫ yoneda.map _ = _ <;>
    rw [← yoneda.map_comp] <;>
    simp

/-- A morphism between the algebraic spaces represented by two affine objects of the site which is
bijective on global regular functions is an isomorphism. -/
theorem isIso_of_bijective_globalFunctionsMap_repr {T T' : BigFppfOver B S hS}
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (f : representedAlgebraicSpace B S hS T ⟶ representedAlgebraicSpace B S hS T')
    (hf : Function.Bijective (globalFunctionsMap B S hS f)) : IsIso f := by
  have _ := hT
  have _ := hT'
  set g : T ⟶ T' := yoneda.preimage f.hom with hgdef
  have hgmap : yoneda.map g = f.hom := yoneda.map_preimage _
  have hfeq : f = (ObjectProperty.homMk (yoneda.map g) :
      representedAlgebraicSpace B S hS T ⟶ representedAlgebraicSpace B S hS T') :=
    ObjectProperty.hom_ext _ hgmap.symm
  have hΓ : Function.Bijective ((BigFppfOver.toScheme B S hS).map g).appTop.hom := by
    have hcoe : (((BigFppfOver.toScheme B S hS).map g).appTop.hom : _ → _)
        = (reprGlobalFunctionsEquiv B S hS T) ∘ (globalFunctionsMap B S hS f) ∘
          (reprGlobalFunctionsEquiv B S hS T').symm := by
      funext x
      have h := reprGlobalFunctionsRestriction_naturality B S hS g
        ((reprGlobalFunctionsEquiv B S hS T').symm x)
      rw [← hfeq] at h
      have hval : reprGlobalFunctionsRestriction B S hS T'
          ((reprGlobalFunctionsEquiv B S hS T').symm x) = x :=
        (reprGlobalFunctionsEquiv B S hS T').apply_symm_apply x
      rw [hval] at h
      exact h.symm
    rw [hcoe]
    exact (reprGlobalFunctionsEquiv B S hS T).bijective.comp
      (hf.comp (reprGlobalFunctionsEquiv B S hS T').symm.bijective)
  have : IsIso ((BigFppfOver.toScheme B S hS).map g) := isIso_of_bijective_appTop _ hΓ
  have : IsIso g := isIso_of_reflects_iso g (BigFppfOver.toScheme B S hS)
  rw [hfeq]
  exact isIso_homMk_yoneda_map B S hS g

/-- A morphism of affine algebraic spaces over `S` which induces a bijection on rings of global
regular functions is an isomorphism. -/
theorem isIso_of_bijective_globalFunctionsMap {X Y : AlgebraicSpaces B S hS}
    (hX : IsAffineSpace B S hS X.obj) (hY : IsAffineSpace B S hS Y.obj) (f : X ⟶ Y)
    (hf : Function.Bijective (globalFunctionsMap B S hS f)) : IsIso f := by
  obtain ⟨TX, hTX, ⟨eX⟩⟩ := hX
  obtain ⟨TY, hTY, ⟨eY⟩⟩ := hY
  let EX : X ≅ representedAlgebraicSpace B S hS TX :=
    Functor.preimageIso (ObjectProperty.ι _) eX
  let EY : Y ≅ representedAlgebraicSpace B S hS TY :=
    Functor.preimageIso (ObjectProperty.ι _) eY
  have hbij' : Function.Bijective
      (globalFunctionsMap B S hS (EX.inv ≫ f ≫ EY.hom)) := by
    have hcoe : (globalFunctionsMap B S hS (EX.inv ≫ f ≫ EY.hom) : _ → _)
        = (globalFunctionsMap B S hS EX.inv) ∘ (globalFunctionsMap B S hS f) ∘
          (globalFunctionsMap B S hS EY.hom) := by
      rw [globalFunctionsMap_comp, globalFunctionsMap_comp]
      rfl
    rw [hcoe]
    exact (bijective_globalFunctionsMap_of_isIso B S hS EX.symm).comp
      (hf.comp (bijective_globalFunctionsMap_of_isIso B S hS EY))
  have hiso : IsIso (EX.inv ≫ f ≫ EY.hom) :=
    isIso_of_bijective_globalFunctionsMap_repr B S hS hTX hTY _ hbij'
  rw [show f = EX.hom ≫ (EX.inv ≫ f ≫ EY.hom) ≫ EY.inv by simp]
  infer_instance

/-- A morphism of affine algebraic spaces over `S` which is bijective on global regular functions
has an underlying morphism of presheaves which is an isomorphism. -/
theorem isIso_hom_of_bijective_globalFunctionsMap {X Y : AlgebraicSpaces B S hS}
    (hX : IsAffineSpace B S hS X.obj) (hY : IsAffineSpace B S hS Y.obj) (f : X ⟶ Y)
    (hf : Function.Bijective (globalFunctionsMap B S hS f)) : IsIso f.hom := by
  have := isIso_of_bijective_globalFunctionsMap B S hS hX hY f hf
  infer_instance

end Space

end AlgebraicGeometry

end
