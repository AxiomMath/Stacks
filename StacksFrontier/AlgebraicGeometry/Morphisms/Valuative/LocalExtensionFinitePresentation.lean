module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.SpreadingOut
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.LocalExtension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending a local homomorphism: the finite-presentation case

A local homomorphism between the local rings at two points over the same point of a base scheme
is induced by a morphism on an open neighbourhood of the source point when the target is locally
of finite presentation, with no condition on the source.

The finite-type case for a source with injective germ maps is Mathlib's
`AlgebraicGeometry.spread_out_of_isGermInjective`, and the finite-type case for a reduced source
with finitely many irreducible components is
`AlgebraicGeometry.exists_open_morphism_inducing_localHom_of_isReduced` in
`StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.LocalExtension`. This module supplies the
remaining case, which needs no germ injectivity: a finitely presented algebra map out of the
stalk descends to one of the sections over an affine open, because the stalk is a filtered
colimit of those section rings.

## Main results

* `AlgebraicGeometry.exists_open_morphism_inducing_localHom_of_locallyOfFinitePresentation`
  gives the finite-presentation case without a condition on the source.

## Implementation notes

The statement records the image of the source point and the equality of stalk maps explicitly;
the equality uses the canonical stalk isomorphism for an open subscheme. Compatibility over the
base, and the assertion that the resulting morphism is over the base, are explicit.

The stalk-descent step is `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit` applied to
the colimit cocone of sections over the open neighbourhoods of the point.

The declaration carries no `@[stacks]` attribute: Tag 0BX6's "local_extension" subname is
already placed, on the finite-type case in the module named above.

## References

* [Stacks Project, Tag 0BX6](https://stacks.math.columbia.edu/tag/0BX6)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry


private lemma exists_germ_comp_of_finitePresentation
    {X : Scheme.{u}} {x : X} {R A : CommRingCat.{u}}
    (φ : A →+* X.presheaf.stalk x) (φRA : R →+* A) (φRX : R →+* Γ(X, ⊤))
    (hfp : φRA.FinitePresentation)
    (e : φ.comp φRA = (X.presheaf.germ ⊤ x trivial).hom.comp φRX) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (ψ : A →+* Γ(X, U)),
      φ = (X.presheaf.germ U x hxU).hom.comp ψ ∧
      ψ.comp φRA = (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp φRX := by
  classical
  let D := (OpenNhds.inclusion x).op ⋙ X.presheaf
  let c : CategoryTheory.Limits.Cocone D :=
    { pt := X.presheaf.stalk x
      ι :=
        { app i := X.presheaf.germ ((OpenNhds.inclusion x).obj i.unop) x i.unop.2
          naturality := by
            intro i j f
            simpa [D] using X.presheaf.germ_res
              ((OpenNhds.inclusion x).map f.unop) x j.unop.2 } }
  let hc : Limits.IsColimit c :=
    .ofIsoColimit (Limits.colimit.isColimit D) (Limits.Cocone.ext (Iso.refl _))
  let top : OpenNhds x := ⟨⊤, trivial⟩
  let d (i : ((OpenNhds x)ᵒᵖ)) :
      (Opposite.op top : (OpenNhds x)ᵒᵖ) ⟶ i :=
    Opposite.op (homOfLE (show i.unop ≤ (⊤ : OpenNhds x) from le_top))
  have hmap (i : (OpenNhds x)ᵒᵖ) :
      (D.map (d i)).hom =
        (X.presheaf.map (homOfLE (show (OpenNhds.inclusion x).obj i.unop ≤ ⊤
          from le_top)).op).hom := rfl
  let α : (Functor.const ((OpenNhds x)ᵒᵖ)).obj R ⟶ D :=
    { app i := CommRingCat.ofHom ((D.map (d i)).hom.comp φRX)
      naturality := by
        intro i j f
        have hD : D.map (d i ≫ f) = D.map (d j) := congrArg D.map (Subsingleton.elim _ _)
        rw [Functor.map_comp] at hD
        apply CommRingCat.hom_ext
        change (D.map (d j)).hom.comp φRX =
          (D.map f).hom.comp ((D.map (d i)).hom.comp φRX)
        exact congrArg (fun k : D.obj (Opposite.op (⊤ : OpenNhds x)) ⟶ D.obj j =>
          k.hom.comp φRX) hD.symm }
  have hcompat (i : (OpenNhds x)ᵒᵖ) :
      CommRingCat.ofHom φRA ≫ CommRingCat.ofHom φ = α.app i ≫ c.ι.app i := by
    apply CommRingCat.hom_ext
    calc
      φ.comp φRA = (X.presheaf.germ ⊤ x trivial).hom.comp φRX := e
      _ = (c.ι.app (Opposite.op top)).hom.comp φRX := rfl
      _ = ((c.ι.app i).hom.comp (D.map (d i)).hom).comp φRX := by
        rw [← CommRingCat.hom_comp, c.w (d i)]
      _ = (c.ι.app i).hom.comp (α.app i).hom := by
            simp only [α]
            rfl
  obtain ⟨i, ψ, hψ, hφ⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
      (R := R) (F := D) (α := α) (f := CommRingCat.ofHom φRA)
      (c := c) (hc := hc) hfp (CommRingCat.ofHom φ) (fun i ↦ hcompat i)
  have hh := congrArg CommRingCat.Hom.hom hψ
  simp only [α, hmap i] at hh
  exact ⟨i.unop.1, i.unop.2, ψ.hom, congrArg CommRingCat.Hom.hom hφ, hh⟩

private lemma exists_lift_of_finitePresentation
    {X : Scheme.{u}} {x : X} {R A : CommRingCat.{u}}
    (φ : A →+* X.presheaf.stalk x) (φRA : R →+* A) (φRX : R →+* Γ(X, ⊤))
    (hfp : φRA.FinitePresentation)
    (e : φ.comp φRA = (X.presheaf.germ ⊤ x trivial).hom.comp φRX) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (φ' : A →+* Γ(X, V)),
      φ = (X.presheaf.germ V x hxV).hom.comp φ' ∧
      (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op).hom.comp φRX =
        φ'.comp φRA ∧ IsAffineOpen V := by
  obtain ⟨V₀, hxV₀, ψ, h₁, h₂⟩ := exists_germ_comp_of_finitePresentation φ φRA φRX hfp e
  obtain ⟨_, ⟨V : X.Opens, hV, rfl⟩, hxV, iVV₀⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV₀ V₀.2
  refine ⟨V, hxV, (X.presheaf.map (homOfLE iVV₀).op).hom.comp ψ, ?_, ?_, hV⟩
  · calc
      φ = (X.presheaf.germ V₀ x hxV₀).hom.comp ψ := h₁
      _ = (X.presheaf.map (homOfLE iVV₀).op ≫ X.presheaf.germ V x hxV).hom.comp ψ :=
        congrArg (fun k => k.comp ψ)
          (congrArg CommRingCat.Hom.hom (X.presheaf.germ_res (homOfLE iVV₀) x hxV)).symm
      _ = (X.presheaf.germ V x hxV).hom.comp
          ((X.presheaf.map (homOfLE iVV₀).op).hom.comp ψ) := by
        simp only [CommRingCat.hom_comp, RingHom.comp_assoc]
  · have hmapcomp : (X.presheaf.map (homOfLE iVV₀).op).hom.comp
          (X.presheaf.map (homOfLE (show V₀ ≤ ⊤ from le_top)).op).hom =
          (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op).hom := by
      rw [← CommRingCat.hom_comp, ← X.presheaf.map_comp (homOfLE _).op (homOfLE iVV₀).op]; rfl
    rw [← hmapcomp, RingHom.comp_assoc, RingHom.comp_assoc, h₂]

private lemma fromSpecStalk_comp_of_SpecMap_germ_eq {Y Z : Scheme.{u}} {V : Y.Opens}
    (hV : IsAffineOpen V) {y : Y} (hyV : y ∈ V) {z : Z} {W : Z.Opens} (hzW : z ∈ W)
    (χ : Γ(Y, V) ⟶ Γ(Z, W)) (θ : Y.presheaf.stalk y ⟶ Z.presheaf.stalk z)
    (hSpecRing : Spec.map θ ≫ Spec.map (Y.presheaf.germ V y hyV) =
      Spec.map (Z.presheaf.germ W z hzW) ≫ Spec.map χ) :
    Spec.map θ ≫ Y.fromSpecStalk y =
      W.fromSpecStalkOfMem z hzW ≫ (W.toSpecΓ ≫ Spec.map χ ≫ hV.fromSpec) := by
  calc
    _ = Spec.map θ ≫ hV.fromSpecStalk hyV := by
      rw [hV.fromSpecStalk_eq_fromSpecStalk]
    _ = Spec.map θ ≫ Spec.map (Y.presheaf.germ V y hyV) ≫ hV.fromSpec := by
      simp [IsAffineOpen.fromSpecStalk]
    _ = Spec.map (Z.presheaf.germ W z hzW) ≫ Spec.map χ ≫ hV.fromSpec :=
      congrArg (· ≫ hV.fromSpec) hSpecRing
    _ = _ := by rw [← W.fromSpecStalkOfMem_toSpecΓ_assoc z hzW]

/-- The germ at `x` over an open `U`, followed by the inverse of the stalk isomorphism of the open
subscheme `U`, is the germ over `⊤` of `U` precomposed with the restriction along `U.ι`. -/
lemma Scheme.Opens.germ_comp_stalkIso_inv_eq_appLE {X : Scheme.{u}} (U : X.Opens) {x : X}
    (hx : x ∈ U) (eU : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U) :
    X.presheaf.germ U x hx ≫ (U.stalkIso ⟨x, hx⟩).inv =
      U.ι.appLE U ⊤ eU ≫ U.toScheme.presheaf.germ ⊤ ⟨x, hx⟩ trivial := by
  calc
    _ = X.presheaf.germ U x hx ≫ U.ι.stalkMap ⟨x, hx⟩ := by rw [U.stalkIso_inv]
    _ = U.ι.app U ≫ U.toScheme.presheaf.germ (U.ι ⁻¹ᵁ U) ⟨x, hx⟩ hx := by
      simpa using Scheme.Hom.germ_stalkMap U.ι U ⟨x, hx⟩ hx
    _ = _ := by
      simpa only [Scheme.Hom.appLE, Category.assoc] using
        (congrArg (U.ι.app U ≫ ·)
          (U.toScheme.presheaf.germ_res (homOfLE eU) ⟨x, hx⟩ trivial)).symm

/-- For an open subscheme `U`, the stalk isomorphism intertwines `U.fromSpecStalk x ≫ U.ι` with
`X.fromSpecStalk x`. -/
lemma Scheme.Opens.SpecMap_stalkIso_hom_fromSpecStalk_ι {X : Scheme.{u}} (U : X.Opens) (x : U) :
    Spec.map (U.stalkIso x).hom ≫ U.toScheme.fromSpecStalk x ≫ U.ι =
      X.fromSpecStalk (U.ι x) := by
  have hcomp : U.ι.stalkMap x ≫ (U.stalkIso x).hom = 𝟙 _ := by
    rw [← U.stalkIso_inv]
    exact (U.stalkIso x).inv_hom_id
  have hcancel : Spec.map (U.stalkIso x).hom ≫ Spec.map (U.ι.stalkMap x) = 𝟙 _ := by
    rw [← Spec.map_comp, hcomp]
    simp
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk (f := U.ι) (x := x), ← Category.assoc, hcancel]
  simp

/-- Over an affine base, a morphism `W ⟶ Y` built from a ring map `ψ : Γ(Y, V) ⟶ Γ(X, W)`
compatible with the base is a morphism over the base. -/
lemma toSpecΓ_SpecMap_fromSpec_comp_of_appLE_eq {S X Y : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    {T : S.Opens} (hT : IsAffineOpen T) {V : Y.Opens} (hV : IsAffineOpen V) (hVT : V ≤ q ⁻¹ᵁ T)
    {W : X.Opens} (hW : IsAffineOpen W) (hWT : W ≤ p ⁻¹ᵁ T) (ψ : Γ(Y, V) ⟶ Γ(X, W))
    (h : p.appLE T W hWT = q.appLE T V hVT ≫ ψ) :
    W.toSpecΓ ≫ Spec.map ψ ≫ hV.fromSpec ≫ q = W.ι ≫ p := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec q hT hV hVT, ← Spec.map_comp_assoc, ← h,
    IsAffineOpen.SpecMap_appLE_fromSpec p hT hW hWT, ← Category.assoc, hW.toSpecΓ_fromSpec]

/-- A map of stalks compatible over the base `S` matches the germs over an affine open `T` of `S`
and an open `V ≤ pY ⁻¹ᵁ T`. -/
lemma appLE_germ_comp_eq_app_germ {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) {x : X} {y : Y}
    (e : pX x = pY y) (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x)
    (hφ : pY.stalkMap y ≫ φ =
      S.presheaf.stalkSpecializes (Inseparable.of_eq e).specializes ≫ pX.stalkMap x)
    {T : S.Opens} (hxT : pX x ∈ T) {V : Y.Opens} (hyV : y ∈ V) (hVT : V ≤ pY ⁻¹ᵁ T) :
    pY.appLE T V hVT ≫ Y.presheaf.germ V y hyV ≫ φ =
      pX.app T ≫ X.presheaf.germ (pX ⁻¹ᵁ T) x hxT := by
  have hyT : pY y ∈ T := hVT hyV
  rw [Scheme.Hom.appLE, Category.assoc, Y.presheaf.germ_res_assoc]
  calc
    _ = S.presheaf.germ T (pY y) hyT ≫ pY.stalkMap y ≫ φ := by
      simpa only [Category.assoc] using (Scheme.Hom.germ_stalkMap_assoc pY T y hyT φ).symm
    _ = _ := by
      rw [hφ, TopCat.Presheaf.germ_stalkSpecializes_assoc]
      exact Scheme.Hom.germ_stalkMap pX T x hxT

/-- Composing with the inverse of the stalk isomorphism of `pX ⁻¹ᵁ T`, a map of stalks compatible
over the base matches the germs over `V` and over the whole open subscheme `pX ⁻¹ᵁ T`. -/
lemma appLE_germ_comp_stalkIso_inv_eq_appLE_germ {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    {x : X} {y : Y} (e : pX x = pY y) (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x)
    (hφ : pY.stalkMap y ≫ φ =
      S.presheaf.stalkSpecializes (Inseparable.of_eq e).specializes ≫ pX.stalkMap x)
    {T : S.Opens} (hxT : pX x ∈ T) {V : Y.Opens} (hyV : y ∈ V) (hVT : V ≤ pY ⁻¹ᵁ T) :
    pY.appLE T V hVT ≫ Y.presheaf.germ V y hyV ≫ φ ≫ ((pX ⁻¹ᵁ T).stalkIso ⟨x, hxT⟩).inv =
      ((pX ⁻¹ᵁ T).ι ≫ pX).appLE T ⊤ (fun z _ ↦ z.2) ≫
        (pX ⁻¹ᵁ T).toScheme.presheaf.germ ⊤ ⟨x, hxT⟩ trivial := by
  calc
    _ = (pY.appLE T V hVT ≫ Y.presheaf.germ V y hyV ≫ φ) ≫
        ((pX ⁻¹ᵁ T).stalkIso ⟨x, hxT⟩).inv := by
      simp only [Category.assoc]
    _ = _ := by
      rw [appLE_germ_comp_eq_app_germ pX pY e φ hφ hxT hyV hVT, pX.app_eq_appLE, Category.assoc,
        Scheme.Opens.germ_comp_stalkIso_inv_eq_appLE (pX ⁻¹ᵁ T) hxT (fun z _ ↦ z.2),
        ← Category.assoc]
      exact congrArg (· ≫ _)
        (Scheme.Hom.appLE_comp_appLE (pX ⁻¹ᵁ T).ι pX T (pX ⁻¹ᵁ T) ⊤ le_rfl _)

/-- A factorisation of `Spec.map (φ ≫ (U.stalkIso x).inv) ≫ Y.fromSpecStalk y` through an open
`W` of the open subscheme `U` transports to the image of `W` in `X`. -/
lemma SpecMap_fromSpecStalk_eq_isoImage_inv_comp {X Y : Scheme.{u}} {U : X.Opens} {x : U}
    {W : U.toScheme.Opens} (hxW : x ∈ W) (hxU : x.1 ∈ U.ι ''ᵁ W) {y : Y}
    (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x.1) (f : W.toScheme ⟶ Y)
    (h : Spec.map (φ ≫ (U.stalkIso x).inv) ≫ Y.fromSpecStalk y =
      W.fromSpecStalkOfMem x hxW ≫ f) :
    Spec.map φ ≫ Y.fromSpecStalk y =
      (U.ι ''ᵁ W).fromSpecStalkOfMem x.1 hxU ≫ (U.ι.isoImage W).inv ≫ f := by
  have hfrom : Spec.map (U.stalkIso x).hom ≫ W.fromSpecStalkOfMem x hxW ≫
      (U.ι.isoImage W).hom = (U.ι ''ᵁ W).fromSpecStalkOfMem x.1 hxU := by
    apply (cancel_mono (U.ι ''ᵁ W).ι).mp
    calc
      _ = Spec.map (U.stalkIso x).hom ≫ W.fromSpecStalkOfMem x hxW ≫
          ((U.ι.isoImage W).hom ≫ (U.ι ''ᵁ W).ι) := by simp [Category.assoc]
      _ = Spec.map (U.stalkIso x).hom ≫ (W.fromSpecStalkOfMem x hxW ≫ W.ι) ≫ U.ι := by
        rw [Scheme.Hom.isoImage_hom_ι, Category.assoc]
      _ = X.fromSpecStalk x.1 := by
        rw [Scheme.Opens.fromSpecStalkOfMem_ι W x hxW]
        exact Scheme.Opens.SpecMap_stalkIso_hom_fromSpecStalk_ι U x
      _ = _ := (Scheme.Opens.fromSpecStalkOfMem_ι _ _ hxU).symm
  have hspecMap : Spec.map φ =
      Spec.map (U.stalkIso x).hom ≫ Spec.map (φ ≫ (U.stalkIso x).inv) := by
    rw [← Spec.map_comp]
    congr 1
    simp
  have hfrom' : Spec.map (U.stalkIso x).hom ≫ W.fromSpecStalkOfMem x hxW =
      (U.ι ''ᵁ W).fromSpecStalkOfMem x.1 hxU ≫ (U.ι.isoImage W).inv := by
    rw [← hfrom]
    simp
  rw [hspecMap, Category.assoc, h, ← Category.assoc, hfrom', Category.assoc]

/-- **Stacks Project, Tag 0BX6 (local extension), finite-presentation case.** A compatible
local homomorphism of local rings is induced by a morphism on an open neighbourhood. -/
@[stacks 0BX6 "local_extension", ega "I 6.5.1" "(ii)"]
public lemma exists_open_morphism_inducing_localHom_of_locallyOfFinitePresentation
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    (s : S) (x : X) (y : Y) (hx : pX x = s) (hy : pY y = s)
    (phi : Y.presheaf.stalk y →+* X.presheaf.stalk x)
    (hphi : IsLocalHom phi)
    (hphiS : phi.comp
        ((pY.stalkMap y).hom.comp
          (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hy).symm).hom) =
      (pX.stalkMap x).hom.comp
        (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hx).symm).hom)
    (hfin : LocallyOfFinitePresentation pY) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (f : (U : Scheme.{u}) ⟶ Y)
      (_hf : f ≫ pY = U.ι ≫ pX)
      (hfy : f ⟨x, hxU⟩ = y),
      ((U.stalkIso ⟨x, hxU⟩).hom.hom.comp
          ((f.stalkMap ⟨x, hxU⟩).hom.comp
            (eqToHom (congrArg (fun z ↦ Y.presheaf.stalk z) hfy).symm).hom)) = phi := by
  have e : pX x = pY y := hx.trans hy.symm
  let φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x := CommRingCat.ofHom phi
  obtain ⟨_, ⟨T, hT, rfl⟩, hsT, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  have hxT : pX x ∈ T := by rwa [hx]
  have hyT : pY y ∈ T := by rwa [hy]
  obtain ⟨_, ⟨V : Y.Opens, hVaff : IsAffineOpen V, rfl⟩, hyV, iVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyT (pY ⁻¹ᵁ T).2
  let U₀ : X.Opens := pX ⁻¹ᵁ T
  let x₀ : U₀ := ⟨x, hxT⟩
  let pX₀ : U₀.toScheme ⟶ S := U₀.ι ≫ pX
  let φ₀ : Y.presheaf.stalk y ⟶ U₀.toScheme.presheaf.stalk x₀ := φ ≫ (U₀.stalkIso x₀).inv
  have iVU' : V ≤ pY ⁻¹ᵁ T := fun _ hz ↦ iVU hz
  let β := pY.appLE T V iVU'
  have eXT : ⊤ ≤ pX₀ ⁻¹ᵁ T := fun z _ ↦ z.2
  let α := pX₀.appLE T ⊤ eXT
  have hbase₀ : β ≫ Y.presheaf.germ V y hyV ≫ φ₀ =
      α ≫ U₀.toScheme.presheaf.germ ⊤ x₀ trivial :=
    appLE_germ_comp_stalkIso_inv_eq_appLE_germ pX pY e φ
      (localHom_compat pX pY x y hx hy phi hphiS) hxT hyV iVU'
  obtain ⟨W, hxW, ψ, h₁, h₂, hW⟩ := exists_lift_of_finitePresentation
    (φ₀.hom.comp (Y.presheaf.germ V y hyV).hom) β.hom α.hom
    (hfin.finitePresentation_appLE hT hVaff iVU')
    (by simpa only [CommRingCat.hom_comp] using congrArg CommRingCat.Hom.hom hbase₀)
  have iW : W ≤ pX₀ ⁻¹ᵁ T := fun z _ ↦ z.2
  have happW : α ≫ U₀.toScheme.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op =
      pX₀.appLE T W iW := by
    simpa [α] using pX₀.appLE_map eXT (homOfLE (show W ≤ ⊤ from le_top)).op
  have hbaseW : pX₀.appLE T W iW = β ≫ CommRingCat.ofHom ψ := by
    rw [← happW]
    exact CommRingCat.hom_ext h₂
  let f₀ : W.toScheme ⟶ Y := W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ hVaff.fromSpec
  have h₁cat : Y.presheaf.germ V y hyV ≫ φ₀ =
      CommRingCat.ofHom ψ ≫ U₀.toScheme.presheaf.germ W x₀ hxW := CommRingCat.hom_ext h₁
  have hSpecRing : Spec.map φ₀ ≫ Spec.map (Y.presheaf.germ V y hyV) =
      Spec.map (U₀.toScheme.presheaf.germ W x₀ hxW) ≫ Spec.map (CommRingCat.ofHom ψ) :=
    (Spec.map_comp _ _).symm.trans ((congrArg Spec.map h₁cat).trans (Spec.map_comp _ _))
  have hspec₀ : Spec.map φ₀ ≫ Y.fromSpecStalk y = W.fromSpecStalkOfMem x₀ hxW ≫ f₀ :=
    fromSpecStalk_comp_of_SpecMap_germ_eq hVaff hyV hxW (CommRingCat.ofHom ψ) φ₀ hSpecRing
  have hxU : x ∈ U₀.ι ''ᵁ W := ⟨x₀, hxW, rfl⟩
  have hf : ((U₀.ι.isoImage W).inv ≫ f₀) ≫ pY = (U₀.ι ''ᵁ W).ι ≫ pX := by
    have hf₀ : f₀ ≫ pY = W.ι ≫ pX₀ := by
      simp only [f₀, Category.assoc]
      exact toSpecΓ_SpecMap_fromSpec_comp_of_appLE_eq pX₀ pY hT hVaff iVU' hW iW _ hbaseW
    rw [Category.assoc, hf₀]
    simp [pX₀]
  exact ⟨_, hxU, _, hf, finish_local_extension_of_spec_eq pX pY x y φ hphi _ hxU _
    (SpecMap_fromSpecStalk_eq_isoImage_inv_comp hxW hxU φ f₀ hspec₀) hf⟩

end AlgebraicGeometry
