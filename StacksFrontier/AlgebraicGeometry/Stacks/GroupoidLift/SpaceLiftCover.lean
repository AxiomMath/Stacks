module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.SpaceLift
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.ChartRefinement
public import StacksFrontier.AlgebraicGeometry.Smooth.ThickeningRestriction
public import StacksFrontier.RingTheory.Etale.Lifting

/-!
# The faithfully flat étale cover of the thickened base

Let `i : T ⟶ T'` be a square-zero closed immersion of affine objects of the big fppf site over
`S`, `A' = Γ(T', ⊤)` and `I` the kernel of `A' → Γ(T, ⊤)`. An affine `c` surjective and étale over
`T` is, by Stacks 04D1, the reduction modulo `I` of a faithfully flat étale `A'`-algebra `C'`.

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.exists_etale_lift_of_etale`: an affine étale surjective
  `c ⟶ T` is the reduction modulo `I` of a faithfully flat étale `A'`-algebra.
* `AlgebraicGeometry.Stack.GroupoidLift.exists_lift_of_chart_cover`: a point of a sheaf over `T`
  lying over `i` extends over `T'`, given an affine étale chart and an affine étale cover.
* `AlgebraicGeometry.Stack.GroupoidLift.exists_lift_of_isSmooth`: a point over `T` of an
  algebraic space smooth over `T'` lying over `i` extends to a section over `T'`.
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory Opposite Limits
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]

/-- **The étale cover of `T'` lifting an étale cover of `T`** (Stacks 04D1). -/
theorem exists_etale_lift_of_etale {T c : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj c)] (i : T ⟶ T')
    (hi : Space.IsSquareZeroClosedImmersion B S hS i) (g : c ⟶ T)
    (hgs : Surjective ((BigFppfOver.toScheme B S hS).map g))
    (hge : Etale ((BigFppfOver.toScheme B S hS).map g)) :
    ∃ (C' : Type u) (_ : CommRing C') (_ : Algebra (ringOf B S hS T') C')
      (hC : Cardinal.mk C' < B.cutoff), Algebra.Etale (ringOf B S hS T') C' ∧
      Module.FaithfullyFlat (ringOf B S hS T') C' ∧
      Nonempty (sectionsAlg c (g ≫ i) ⟶
        red (RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom)
          (nerve (A' := ringOf B S hS T') B.aleph0_lt_cutoff C' hC 0)) := by
  set A' := ringOf B S hS T'
  set iS := (BigFppfOver.toScheme B S hS).map i
  set gS := (BigFppfOver.toScheme B S hS).map g
  set I := RingHom.ker iS.appTop.hom
  have hthick : Stacks.Thickenings.IsFirstOrderThickening iS := ⟨hi.1, hi.2⟩
  have hsurj : Function.Surjective iS.appTop.hom :=
    Stacks.Smooth.surjective_appTop_of_isFirstOrderThickening hthick
  have hI : I ^ 2 = ⊥ := Stacks.Smooth.ker_appTop_sq_eq_bot hthick
  let : Algebra A' Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) := iS.appTop.hom.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj c, ⊤) := gS.appTop.hom.toAlgebra
  let : Algebra A' Γ((BigFppfOver.toScheme B S hS).obj c, ⊤) :=
    ((BigFppfOver.toScheme B S hS).map (g ≫ i)).appTop.hom.toAlgebra
  have : IsScalarTower A' Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj c, ⊤) := .of_algebraMap_eq fun r ↦ by
    change ((BigFppfOver.toScheme B S hS).map (g ≫ i)).appTop.hom r =
      gS.appTop.hom (iS.appTop.hom r)
    rw [Functor.map_comp, Scheme.Hom.comp_appTop]
    rfl
  have hgEt : gS.appTop.hom.Etale := HasRingHomProperty.appTop (P := @Etale) gS hge
  have : Algebra.Etale Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj c, ⊤) := RingHom.etale_algebraMap.mp hgEt
  have hgFF : gS.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine gS).mp ⟨inferInstance, hgs⟩
  obtain ⟨C', _, _, hEt, ψ, hψs, hψk⟩ := etale_lift_along_surjection A'
    Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) Γ((BigFppfOver.toScheme B S hS).obj c, ⊤) hsurj
  have hC : Cardinal.mk C' < B.cutoff :=
    (Cardinal.mk_le_of_algebra_finiteType A' C').trans_lt (max_lt B.aleph0_lt_cutoff
      (card_sections_lt T'))
  have hkerI : RingHom.ker (algebraMap A' Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) = I := rfl
  rw [hkerI] at hψk
  refine ⟨C', inferInstance, inferInstance, hC, hEt, ?_, ⟨SmallAlg.homMk ?_⟩⟩
  · refine Module.FaithfullyFlat.of_comap_surjective fun 𝔭 ↦ ?_
    have hI𝔭 : I ≤ 𝔭.asIdeal := fun a ha ↦ 𝔭.isPrime.mem_of_pow_mem 2 <| by
      have := Ideal.pow_mem_pow ha 2
      rw [hI, Ideal.mem_bot] at this
      exact this ▸ 𝔭.asIdeal.zero_mem
    obtain ⟨𝔮, rfl⟩ : 𝔭 ∈ Set.range (PrimeSpectrum.comap iS.appTop.hom) := by
      rw [range_comap_of_surjective _ _ hsurj]
      exact hI𝔭
    obtain ⟨𝔯, rfl⟩ := (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hgFF).2 𝔮
    refine ⟨PrimeSpectrum.comap (ψ : C' →+* Γ((BigFppfOver.toScheme B S hS).obj c, ⊤)) 𝔯, ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
    congr 1
    ext a
    change ψ (algebraMap A' C' a) = _
    rw [ψ.commutes]
    rfl
  · exact ((Ideal.quotientEquivAlgOfEq A' hψk).symm.trans
      (Ideal.quotientKerAlgEquivOfSurjective hψs)).symm.toAlgHom

/-- Two algebra maps out of an algebra whose structure map is surjective agree. -/
theorem SmallAlg.hom_ext_of_surjective {A' : Type u} [CommRing A'] {κ : Cardinal.{u}}
    {N N' : SmallAlg A' κ} (h : Function.Surjective (algebraMap A' N.obj)) (f g : N ⟶ N') :
    f = g := by
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  ext n
  obtain ⟨a, rfl⟩ := h n
  rw [f.hom.hom.commutes, g.hom.hom.commutes]

/-- `specOverMap` sends an isomorphism of small `Γ(T')`-algebras to an isomorphism. -/
theorem isIso_specOverMap {N N' : SmallAlg (ringOf B S hS T') B.cutoff} (f : N ⟶ N') [IsIso f] :
    IsIso (specOverMap (T' := T') f) :=
  ⟨specOverMap (inv f), by rw [← specOverMap_comp, IsIso.inv_hom_id, specOverMap_id],
    by rw [← specOverMap_comp, IsIso.hom_inv_id, specOverMap_id]⟩

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (π : X ⟶ yoneda.obj T')

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- Naturality of `π`: the image under `π` of the restriction of `ξ` along `h` is `h ≫ π ξ`. -/
theorem app_map_eq {V W : BigFppfOver B S hS} (h : V ⟶ W) (ξ : X.obj (op W)) :
    π.app (op V) (X.map h.op ξ) = h ≫ π.app (op W) ξ :=
  NatTrans.naturality_apply π h.op ξ

/-- The ideal of a square-zero thickening of affines in `Γ(T')`. -/
abbrev kerIdeal {T : BigFppfOver B S hS} (i : T ⟶ T') : Ideal (ringOf B S hS T') :=
  RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- The image of `kerIdeal i` under the identity of `Γ(T')` is the kernel of the structure map
`Γ(T') → Γ(T)`. -/
theorem map_algebraMap_self_kerIdeal {T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (i : T ⟶ T') :
    (kerIdeal i).map (algebraMap (ringOf B S hS T') (ringOf B S hS T')) =
      RingHom.ker (Algebra.ofId (ringOf B S hS T') (sectionsAlg T i).obj) := by
  rw [Algebra.algebraMap_self, Ideal.map_id]
  rfl

/-- `Γ(T) ≅ A' ⧸ I` for a closed immersion `T ⟶ T'` of affines. -/
noncomputable def redEquiv {T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (i : T ⟶ T') (hsurj : Function.Surjective (algebraMap (ringOf B S hS T') (sectionsAlg T i).obj))
    (hA : Cardinal.mk (ringOf B S hS T') < B.cutoff) :
    (red (kerIdeal i) (baseAlg hA)).obj ≃ₐ[ringOf B S hS T'] (sectionsAlg T i).obj :=
  (Ideal.quotientEquivAlgOfEq (ringOf B S hS T') (map_algebraMap_self_kerIdeal i)).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := Algebra.ofId (ringOf B S hS T') (sectionsAlg T i).obj) hsurj)

/-- The identification `Spec (A' ⧸ I) ⟶ T` over `T'`. -/
noncomputable def redToBase {T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (i : T ⟶ T') (hsurj : Function.Surjective (algebraMap (ringOf B S hS T') (sectionsAlg T i).obj))
    (hA : Cardinal.mk (ringOf B S hS T') < B.cutoff) :
    specOver (red (kerIdeal i) (baseAlg hA)) ⟶ T :=
  specOverMap (SmallAlg.homMk (redEquiv i hsurj hA).symm.toAlgHom) ≫ sectionsHom T i

/-- The composite of `redToBase i hsurj hA` with `i` is the structure morphism of
`Spec (A' ⧸ I)` over `T'`. -/
theorem redToBase_comp {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (i : T ⟶ T') (hsurj : Function.Surjective (algebraMap (ringOf B S hS T') (sectionsAlg T i).obj))
    (hA : Cardinal.mk (ringOf B S hS T') < B.cutoff) :
    redToBase i hsurj hA ≫ i = specOverToBase (red (kerIdeal i) (baseAlg hA)) := by
  rw [redToBase, Category.assoc, sectionsHom_comp, specOverMap_comp_toBase]

/-- The morphism `redToBase i hsurj hA : Spec (A' ⧸ I) ⟶ T` is an isomorphism. -/
instance {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (i : T ⟶ T') (hsurj : Function.Surjective (algebraMap (ringOf B S hS T') (sectionsAlg T i).obj))
    (hA : Cardinal.mk (ringOf B S hS T') < B.cutoff) : IsIso (redToBase i hsurj hA) := by
  have : IsIso (SmallAlg.homMk (R := sectionsAlg T i) (R' := red (kerIdeal i) (baseAlg hA))
      (redEquiv i hsurj hA).symm.toAlgHom) :=
    ⟨SmallAlg.homMk (redEquiv i hsurj hA).toAlgHom, SmallAlg.hom_ext_of_surjective hsurj _ _,
      SmallAlg.hom_ext_of_surjective (fun y ↦ by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
        exact ⟨a, rfl⟩) _ _⟩
  have := isIso_specOverMap (T' := T') (SmallAlg.homMk (redEquiv i hsurj hA).symm.toAlgHom)
  rw [redToBase]
  infer_instance

/-- An étale morphism of the site is étale after Yoneda. -/
private theorem presheaf_etale_yoneda_map {U V : BigFppfOver B S hS} {φ : U ⟶ V}
    (h : Etale ((BigFppfOver.toScheme B S hS).map φ)) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map φ) :=
  (Space.presheaf_yoneda_map_iff B S hS (P := @Etale.{u}) inferInstance _).mpr h

/-- The point over `Γ(U₁)` of a point `ξ` of `X` over an affine `U₁`. -/
noncomputable def sectionsPoint {U₁ : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U₁)] (ξ : X.obj (op U₁)) :
    (relPoints T' π).obj (sectionsAlg U₁ (π.app (op U₁) ξ)) :=
  ⟨X.map (sectionsHom U₁ (π.app (op U₁) ξ)).op ξ, by
    rw [app_map_eq]
    exact sectionsHom_comp U₁ _⟩

/-- If `ξ` is étale as a map from `U₁`, then the point `sectionsPoint π ξ` over `Γ(U₁)` is
formally étale. -/
theorem formallyEtale_sectionsPoint {U₁ : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U₁)] (ξ : X.obj (op U₁))
    (hξ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yonedaEquiv.symm ξ)) :
    Space.FormallyEtale (yonedaEquiv.symm (sectionsPoint π ξ).1) := by
  refine Space.formallyEtale_of_etale B S hS _ ?_
  change (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf
      (yonedaEquiv.symm (X.map (sectionsHom U₁ (π.app (op U₁) ξ)).op ξ))
  rw [← yonedaEquiv_symm_naturality_left]
  refine MorphismProperty.comp_mem _ _ _ ?_ hξ
  refine presheaf_etale_yoneda_map ?_
  have : IsIso ((BigFppfOver.toScheme B S hS).map (sectionsHom U₁ (π.app (op U₁) ξ))) :=
    (Scheme.isoSpec ((BigFppfOver.toScheme B S hS).obj U₁)).isIso_inv
  infer_instance

/-- **The lifting step for a sheaf over an affine base, from an affine chart and an affine étale
cover.** Let `X` be an fppf sheaf over an affine `T'` and `x` a point of `X` over a square-zero
thickening `i : T ⟶ T'` of affines. Suppose given an affine `c` surjective and étale over `T` by
`g` and a point `ξ` of `X` over an affine `U₁`, étale as a map from `U₁` and smooth over `T'`,
through which `x` factors over `c`. Then `x` extends to a point of `X` over `T'`. -/
theorem exists_lift_of_chart_cover (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    {T c U₁ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj c)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U₁)] (i : T ⟶ T')
    (hi : Space.IsSquareZeroClosedImmersion B S hS i) (x : X.obj (op T))
    (hx : π.app (op T) x = i) (g : c ⟶ T)
    (hgs : Surjective ((BigFppfOver.toScheme B S hS).map g))
    (hge : Etale ((BigFppfOver.toScheme B S hS).map g)) (ξ : X.obj (op U₁))
    (hξ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yonedaEquiv.symm ξ))
    (hsm : Smooth ((BigFppfOver.toScheme B S hS).map (π.app (op U₁) ξ)))
    (m : c ⟶ U₁) (hm : X.map m.op ξ = X.map g.op x) :
    ∃ z : X.obj (op T'), X.map i.op z = x ∧ π.app (op T') z = 𝟙 T' := by
  classical
  set A' := ringOf B S hS T'
  have hA : Cardinal.mk A' < B.cutoff := card_sections_lt T'
  set I := RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom
  have hthick : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map i) := ⟨hi.1, hi.2⟩
  have hsurjI : Function.Surjective (algebraMap A' (sectionsAlg T i).obj) :=
    Stacks.Smooth.surjective_appTop_of_isFirstOrderThickening hthick
  have hI : I ^ 2 = ⊥ := Stacks.Smooth.ker_appTop_sq_eq_bot hthick
  obtain ⟨C', _, _, hC, hEt, hFF, ⟨γ⟩⟩ := exists_etale_lift_of_etale i hi g hgs hge
  set j₁ : U₁ ⟶ T' := π.app (op U₁) ξ
  set P := sectionsAlg U₁ j₁
  have hPsm : RingHom.Smooth ((BigFppfOver.toScheme B S hS).map j₁).appTop.hom :=
    HasRingHomProperty.appTop (P := @Smooth) _ hsm
  have : Algebra.Smooth A' P.obj := hPsm
  let p := sectionsPoint π ξ
  let φ := redToBase i hsurjI hA
  have hφ : φ ≫ i = specOverToBase (red I (baseAlg hA)) := redToBase_comp i hsurjI hA
  have hmono : Mono i := by
    have : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) := hi.1
    exact (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  let x' : (relPoints T' π).obj (red I (baseAlg hA)) := ⟨X.map φ.op x, by
    rw [app_map_eq, hx, hφ]⟩
  have hmj : m ≫ j₁ = g ≫ i := by simpa only [app_map_eq, hx] using congrArg (π.app (op c)) hm
  let ubar : P.obj →ₐ[A'] (red I (nerve (A' := A') B.aleph0_lt_cutoff C' hC 0)).obj :=
    (sectionsMap m hmj ≫ γ).hom.hom
  have hkey : specOverMap γ ≫ sectionsHom c (g ≫ i) ≫ g =
      specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot ≫ φ := by
    rw [← cancel_mono i, Category.assoc, Category.assoc, Category.assoc, hφ,
      sectionsHom_comp, specOverMap_comp_toBase, specOverMap_comp_toBase]
  have hubar : (relChart π P p).app _ ubar =
      (relPoints T' π).map (baseThk B.aleph0_lt_cutoff hC hI hA).bot x' := by
    apply Subtype.ext
    change X.map (specOverMap (sectionsMap m hmj ≫ γ)).op (X.map (sectionsHom U₁ j₁).op ξ) =
      X.map (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot).op (X.map φ.op x)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      specOverMap_comp, Category.assoc, specOverMap_sectionsMap, ← hkey, op_comp, op_comp,
      op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply,
      Functor.map_comp_apply, Functor.map_comp_apply, hm]
  obtain ⟨x'', hx''⟩ := exists_relPoints_lift π hX hA hC hI P p
    (formallyEtale_sectionsPoint π ξ hξ) x' ubar hubar
  have := isIso_specOverToBase_baseAlg (T' := T') hA
  refine ⟨X.map (inv (specOverToBase (T' := T') (baseAlg hA))).op x''.1, ?_, ?_⟩
  · have hi' : i ≫ inv (specOverToBase (T' := T') (baseAlg hA)) =
        inv φ ≫ specOverMap (thk I hI (baseAlg hA)).q := by
      rw [← cancel_mono (specOverToBase (T' := T') (baseAlg hA)), Category.assoc,
        IsIso.inv_hom_id, Category.comp_id, Category.assoc, specOverMap_comp_toBase, ← hφ,
        IsIso.inv_hom_id_assoc]
    have hx''1 : X.map (specOverMap (thk I hI (baseAlg hA)).q).op x''.1 = X.map φ.op x :=
      congrArg Subtype.val hx''
    rw [← Functor.map_comp_apply, ← op_comp, hi', op_comp, Functor.map_comp_apply,
      hx''1, ← Functor.map_comp_apply, ← op_comp, IsIso.inv_hom_id, op_id,
      Functor.map_id_apply]
  · rw [app_map_eq]
    exact (congrArg (inv (specOverToBase (T' := T') (baseAlg hA)) ≫ ·) x''.2).trans
      (IsIso.inv_hom_id _)

/-- Under the Yoneda equivalence, the point `a.app (op V) s` of `X` corresponds to
`yoneda.map s ≫ a`. -/
theorem yonedaEquiv_symm_app_eq {U V : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X) (s : V ⟶ U) :
    yonedaEquiv.symm (a.app (op V) s) = yoneda.map s ≫ a := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/-- **The lifting property of an algebraic space smooth over an affine base.** Let `X` be an
algebraic space over `S` with a smooth morphism `π` to the affine object `T'`, and let
`i : T ⟶ T'` be a square-zero closed immersion of affines. Every point of `X` over `T` lying over
`i` extends to a section of `π` over `T'`. -/
theorem exists_lift_of_isSmooth (hX : IsAlgebraicSpace B S hS X)
    (hπ : Space.IsSmooth B S hS π) {T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (i : T ⟶ T')
    (hi : Space.IsSquareZeroClosedImmersion B S hS i) (x : X.obj (op T))
    (hx : π.app (op T) x = i) :
    ∃ z : X.obj (op T'), X.map i.op z = x ∧ π.app (op T') z = 𝟙 T' := by
  obtain ⟨U, a, haS, haE⟩ := hX.exists_atlas
  set g : yoneda.obj T ⟶ X := yonedaEquiv.symm x
  set hrep := haS.rep
  set q : hrep.pullback g ⟶ T := hrep.snd g
  set k : hrep.pullback g ⟶ U := hrep.fst' g
  have hqs : Surjective ((BigFppfOver.toScheme B S hS).map q) := haS.property_snd g
  have hqe : Etale ((BigFppfOver.toScheme B S hS).map q) :=
    haE.2 g (hrep.fst g) q (hrep.isPullback g)
  obtain ⟨c', U₁, r, s, m, hc', hU₁, hrs, hre, hse, hms⟩ :=
    BigFppfOver.exists_affine_surjective_etale_refinement_factor inferInstance q hqs hqe k
  set ξ : X.obj (op U₁) := a.app (op U₁) s
  have hξ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yonedaEquiv.symm ξ) := by
    rw [yonedaEquiv_symm_app_eq]
    exact MorphismProperty.comp_mem _ _ _ (presheaf_etale_yoneda_map hse) haE
  have hid : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj T')) := by
    rw [← yoneda.map_id]
    refine presheaf_etale_yoneda_map ?_
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  have hsm : Smooth ((BigFppfOver.toScheme B S hS).map (π.app (op U₁) ξ)) := by
    refine hπ U₁ T' (yonedaEquiv.symm ξ) (𝟙 _) (π.app (op U₁) ξ) hξ hid ?_
    apply yonedaEquiv.injective
    rw [Category.comp_id, yonedaEquiv_yoneda_map, yonedaEquiv_comp, Equiv.apply_symm_apply]
  have hk : a.app _ k = X.map q.op x := by
    have h := Space.app_tautological_section_representing B S hS (hrep.isPullback g)
    have hf : (hrep.fst g).app (op (hrep.pullback g)) (𝟙 _) = k := by
      rw [← hrep.map_fst']
      exact Category.id_comp (obj := BigFppfOver B S hS) k
    rwa [hf] at h
  have hm : X.map m.op ξ = X.map (r ≫ q).op x := by
    have h1 : X.map m.op ξ = a.app _ (m ≫ s) := (NatTrans.naturality_apply a m.op s).symm
    rw [h1, hms]
    have h2 : a.app _ (r ≫ k) = X.map r.op (a.app _ k) := NatTrans.naturality_apply a r.op k
    rw [h2, hk, ← Functor.map_comp_apply, ← op_comp]
  exact exists_lift_of_chart_cover π hX.isSheaf i hi x hx (r ≫ q) hrs hre ξ hξ hsm m hm

end AlgebraicGeometry.Stack.GroupoidLift

end
