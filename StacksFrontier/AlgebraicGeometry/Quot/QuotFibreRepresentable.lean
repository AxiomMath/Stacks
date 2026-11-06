module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackKernelInjective
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFibreProductMorphism
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoClassClassifier
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Characterization

/-!
# The 2-fibre product of `Quot_{F/X/B} ⟶ Coh_{X/B}` with a point, classified by surjections

Let `y : (Sch/V)_{fppf} ⟶ Coh_{X/B}` be a scheme-valued point and let `H` be an algebraic space
over the test scheme of `y(V)` representing the relative Hom functor of Stacks 08JT.  The
sections of `H` attached to the objects of the 2-fibre product
`(Sch/V) ×_{Coh_{X/B}} Quot_{F/X/B}` classify its isomorphism classes by the locus of
surjections in `H`; this is the description of the 2-fibre product in the proof of Stacks 09TU.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.fibreCls`: the section of the locus of surjections
  attached to an object of a fibre of the 2-fibre product.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.fibreCls_map`: compatibility with morphisms.
* `AlgebraicGeometry.Space.QuotSituation.fibreCls_injective`: two objects of a fibre with the
  same section are isomorphic.

## References

* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local implicit_reducible] AlgebraicGeometry.Space.QuotSituation.toCoherentSituation

namespace CategoryTheory

/-- **The category fibred in groupoids attached to a presheaf of sets is fibred in setoids**, in
any universe of values: its fibres are the discrete groupoids of the sections. -/
theorem presheafOfGroupoids_typeToGrpd_isFiberedInSetoids {C : Type*} [Category* C]
    (F : Cᵒᵖ ⥤ Type*) : (presheafOfGroupoids (F ⋙ typeToGrpd)).p.IsFiberedInSetoids := by
  let p := (presheafOfGroupoids (F ⋙ typeToGrpd)).p
  have hgrp : ∀ U, IsGroupoid (p.Fiber U) := fun U =>
    isGroupoid_fiber_presheafOfGroupoids (F ⋙ typeToGrpd) U
  have hthin : ∀ U, Quiver.IsThin (p.Fiber U) := by
    intro U
    let PF := ((F ⋙ typeToGrpd) ⋙ Grpd.forgetToCat).toPseudofunctor'
    let j := Functor.Fiber.inducedFunctor (Pseudofunctor.CoGrothendieck.comp_const PF U)
    let : j.IsEquivalence := inferInstance
    let e := j.asEquivalence
    let hff := e.symm.fullyFaithfulFunctor
    let : e.symm.functor.FullyFaithful := hff
    intro x y
    refine ⟨fun a b => ?_⟩
    have hdis : Subsingleton (e.symm.functor.obj x ⟶ e.symm.functor.obj y) := by
      show Subsingleton (Discrete.mk _ ⟶ Discrete.mk _)
      infer_instance
    exact (Functor.map_injective e.symm.functor) (hdis.allEq _ _)
  exact ⟨isFiberedInGroupoids_presheafOfGroupoids (F ⋙ typeToGrpd), hthin⟩

/-- A morphism lying over `f` up to identifications of its endpoints, rearranged. -/
theorem eqToHom_comp_eq_comp_eqToHom_of_fac {C : Type*} [Category* C] {X Y X' Y' : C}
    (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X' = X) (hY : Y' = Y)
    (h : g = eqToHom hX ≫ f ≫ eqToHom hY.symm) : eqToHom hX.symm ≫ g = f ≫ eqToHom hY.symm := by
  subst hX hY
  simpa using h

/-- Three identifications compose to an identity conjugated by two. -/
theorem eqToHom_comp_eqToHom_comp_eqToHom_eq_id {C : Type*} [Category* C] {X Y Z W U : C}
    (h₁ : X = Y) (h₂ : Y = Z) (h₃ : Z = W) (h₄ : X = U) (h₅ : W = U) :
    eqToHom h₁ ≫ eqToHom h₂ ≫ eqToHom h₃ = eqToHom h₄ ≫ 𝟙 U ≫ eqToHom h₅.symm := by
  subst h₁ h₂ h₃ h₅
  simp

/-- A morphism conjugated by identifications, with the two on the right cancelling. -/
theorem eqToHom_comp_comp_eqToHom_eqToHom {C : Type*} [Category* C] {X X' Y Z : C}
    (f : X ⟶ Y) (h₁ : X' = X) (h₂ : Y = Z) (h₃ : Z = Y) (h₄ : X' = X) :
    eqToHom h₁ ≫ (f ≫ eqToHom h₂) ≫ eqToHom h₃ = eqToHom h₄ ≫ f := by
  subst h₁ h₂
  simp

/-- Transport along three identifications composing to the identity is the identity. -/
theorem presheaf_map_eqToHom_three {C : Type*} [Category* C] (F : Cᵒᵖ ⥤ Type*) {A U : C}
    (h₁ : U = U) (h₂ : U = A) (h₃ : A = U) (a : F.obj (op U)) :
    F.map (eqToHom h₁).op (F.map (eqToHom h₂).op (F.map (eqToHom h₃).op a)) = a := by
  subst h₃
  simp

/-- An identity conjugated by an identification and its inverse. -/
theorem eqToHom_comp_id_comp_eqToHom {C : Type*} [Category* C] {X U : C} (h : X = U) :
    𝟙 X = eqToHom h ≫ 𝟙 U ≫ eqToHom h.symm := by
  subst h
  simp

/-- Cancelling identifications on both sides of an equation of conjugated morphisms. -/
theorem eq_eqToHom_comp_of_conj {C : Type*} [Category* C] {X X' Y Y' Z Z' : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) (hX : X' = X) (hY : Y' = Y) (hZ : Z = Z') (e : X' = Y')
    (h : eqToHom hX ≫ f ≫ eqToHom hZ = eqToHom e ≫ eqToHom hY ≫ g ≫ eqToHom hZ) :
    f = eqToHom (hX.symm.trans (e.trans hY)) ≫ g := by
  subst hX hY e hZ
  simpa using h

/-- Two elements of a presheaf of sets which agree after transport along identifications to a
common object are related by the composite identification. -/
theorem presheaf_eq_map_eqToHom_of {C : Type*} [Category* C] (F : Cᵒᵖ ⥤ Type*)
    {A A' B B' U : C} (hA : A = A') (hA' : A' = U) (hB : B = B') (hB' : B' = U)
    (a : F.obj (op A)) (b : F.obj (op B))
    (h : F.map (eqToHom hA'.symm).op (F.map (eqToHom hA.symm).op a) =
      F.map (eqToHom hB'.symm).op (F.map (eqToHom hB.symm).op b)) :
    a = F.map (eqToHom (hA.trans (hA'.trans (hB'.symm.trans hB.symm)))).op b := by
  subst hA hA' hB hB'
  simpa using h

end CategoryTheory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSituation

variable (D : QuotSituation B S hS) {V : BigFppfOver B S hS}
  (y : (Stack.schemeFibredCategory B S hS V).val ⥤ᵇ D.toCoherentSituation.coherentCFG.val)
  {H : AlgebraicSpaces B S hS} (p : H ⟶ (D.fibreHomSituation (D.fibreBase y)).base)
  (c : spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅
    (D.fibreHomSituation (D.fibreBase y)).homFunctor (modulePushforwardCoherence B S hS))

/-- The locus of surjections in `H`. -/
abbrev fibreSurjLocus : Subfunctor H.1 :=
  (D.fibreHomSituation (D.fibreBase y)).surjLocus (modulePushforwardCoherence B S hS) p c

/-- **The section of the locus of surjections attached to an object of a fibre of the 2-fibre
product.** -/
def fibreCls (U : BigFppfOver B S hS) (x : (D.fibreProduct y).val.p.Fiber U) :
    (D.fibreSurjLocus y p c).toFunctor.obj (op U) :=
  ⟨H.1.map (eqToHom x.2.symm).op (D.fibreClassValue y p c x.1),
    (D.fibreSurjLocus y p c).map (eqToHom x.2.symm).op (D.fibreClassValue_mem y p c x.1)⟩

/-- The underlying section of `fibreCls` is the section of `H` attached to the object,
transported along the equality of its base with `U`. -/
theorem fibreCls_val (U : BigFppfOver B S hS) (x : (D.fibreProduct y).val.p.Fiber U) :
    (D.fibreCls y p c U x).1 = H.1.map (eqToHom x.2.symm).op (D.fibreClassValue y p c x.1) :=
  rfl

/-- **The sections attached to the objects of the fibres are compatible with the morphisms of the
2-fibre product.** -/
theorem fibreCls_map {V' U : BigFppfOver B S hS} (f : V' ⟶ U)
    (x' : (D.fibreProduct y).val.p.Fiber V') (x : (D.fibreProduct y).val.p.Fiber U)
    (φ : x'.1 ⟶ x.1) (hφ : (D.fibreProduct y).val.p.IsHomLift f φ) :
    D.fibreCls y p c V' x' =
      (D.fibreSurjLocus y p c).toFunctor.map f.op (D.fibreCls y p c U x) := by
  apply Subtype.ext
  show H.1.map (eqToHom x'.2.symm).op (D.fibreClassValue y p c x'.1) =
    H.1.map f.op (H.1.map (eqToHom x.2.symm).op (D.fibreClassValue y p c x.1))
  have hmor : eqToHom x'.2.symm ≫ φ.hbase = f ≫ eqToHom x.2.symm :=
    eqToHom_comp_eq_comp_eqToHom_of_fac f ((D.fibreProduct y).val.p.map φ) x'.2 x.2
      (IsHomLift.fac' _ f φ)
  rw [D.fibreClassValue_map y p c φ]
  calc H.1.map (eqToHom x'.2.symm).op (H.1.map φ.hbase.op (D.fibreClassValue y p c x.1))
      = H.1.map (φ.hbase.op ≫ (eqToHom x'.2.symm).op) (D.fibreClassValue y p c x.1) :=
        (H.1.map_comp_apply φ.hbase.op (eqToHom x'.2.symm).op _).symm
    _ = H.1.map ((eqToHom x.2.symm).op ≫ f.op) (D.fibreClassValue y p c x.1) :=
        congrArg (fun g => H.1.map g (D.fibreClassValue y p c x.1)) (congrArg Quiver.Hom.op hmor)
    _ = H.1.map f.op (H.1.map (eqToHom x.2.symm).op (D.fibreClassValue y p c x.1)) :=
        H.1.map_comp_apply (eqToHom x.2.symm).op f.op _

/-- The image in the base of the point attached to an object of the 2-fibre product is the
morphism of schemes underlying `y(x) ⟶ y(V)`. -/
theorem p_fibrePoint (P : (D.fibreProduct y).val.obj) :
    p.hom.app (op (D.fibreTest y P).left.left) (D.fibrePoint y p c P).1 =
      (D.fibreArrow y P.x).base.left :=
  (D.fibrePoint y p c P).2.trans (yonedaEquiv_yoneda_map _)

/-- Transporting a section of `H` along an identification of schemes precomposes its image in
the base. -/
private theorem p_app_map_eqToHom {A A' : BigFppfOver B S hS} (e : A' = A)
    (a : H.1.obj (op A)) (g : A ⟶ (D.fibreBase y).T.left) (ha : p.hom.app (op A) a = g) :
    p.hom.app (op A') (H.1.map (eqToHom e).op a) = eqToHom e ≫ g :=
  (NatTrans.naturality_apply p.hom (eqToHom e).op a).trans
    (congrArg (fun t => (D.fibreHomSituation (D.fibreBase y)).base.1.map (eqToHom e).op t) ha)

/-- **Equal points give equal surjections**: if the point of `P` is the restriction of the point
of `Q` along `y(a)`, the surjection of `P` is the pullback of the surjection of `Q`. -/
theorem fibreClassMap_eq_of_fibrePoint {P Q : (D.fibreProduct y).val.obj} (a : P.x ⟶ Q.x)
    (h₁ : (D.fibrePoint y p c P).1 =
      H.1.map ((D.fibreMapHom y a).base.left).op (D.fibrePoint y p c Q).1) :
    D.fibreClassMap y P = D.pullMapOf (D.fibreMapHom y a).base (D.fibreMapHom y a).fibre
      (D.fibreClassMap y Q) := by
  have hΦ : (D.fibrePointIso y p c).hom.app (op (D.fibreTest y P))
        (D.fibreClassHom y (modulePushforwardCoherence B S hS) P) =
      (D.fibrePointIso y p c).hom.app (op (D.fibreTest y P))
        ((D.fibreHomFunctor (D.fibreBase y) (modulePushforwardCoherence B S hS)).map
          (D.fibreOverHomOf y a).op (D.fibreClassHom y (modulePushforwardCoherence B S hS) Q)) := by
    have h₂ : (D.fibrePoint y p c P).1 = ((D.fibrePointIso y p c).hom.app (op (D.fibreTest y P))
        ((D.fibreHomFunctor (D.fibreBase y) (modulePushforwardCoherence B S hS)).map
          (D.fibreOverHomOf y a).op
          (D.fibreClassHom y (modulePushforwardCoherence B S hS) Q))).down.1 :=
      h₁.trans (congrArg (fun z => z.down.1) (NatTrans.naturality_apply (D.fibrePointIso y p c).hom
        (D.fibreOverHomOf y a).op (D.fibreClassHom y (modulePushforwardCoherence B S hS) Q))).symm
    exact ULift.ext (Subtype.ext h₂)
  have hcH := ((D.fibrePointIso y p c).app (op (D.fibreTest y P))).toEquiv.injective hΦ
  exact D.homOfPullMap_injective _ _
    (hcH.trans (D.fibreHomFunctor_map_fibreClassHom y (modulePushforwardCoherence B S hS) a))

/-- The morphism of schemes underlying `y(x) ⟶ y(V)`. -/
theorem fibreArrow_base_left (x : Over V) :
    (D.fibreArrow y x).base.left = eqToHom (Functor.congr_obj y.w x) ≫ x.hom ≫
      eqToHom (Functor.congr_obj y.w (Over.mk (𝟙 V))).symm :=
  D.fibreMapHom_base_left_of y (Over.homMk x.hom (Category.comp_id _) : x ⟶ Over.mk (𝟙 V))

/-- **Two objects of a fibre of the 2-fibre product with the same section are isomorphic.** -/
theorem fibreCls_injective (U : BigFppfOver B S hS) (x z : (D.fibreProduct y).val.p.Fiber U)
    (h : D.fibreCls y p c U x = D.fibreCls y p c U z) : Nonempty (x ≅ z) := by
  have hv := congrArg Subtype.val h
  have h₀ := presheaf_eq_map_eqToHom_of H.1 (D.fibreBaseEq y x.1) x.2 (D.fibreBaseEq y z.1) z.2
    (D.fibrePoint y p c x.1).1 (D.fibrePoint y p c z.1).1 hv
  set E := (D.fibreBaseEq y x.1).trans (x.2.trans (z.2.symm.trans (D.fibreBaseEq y z.1).symm))
  have hp' : (D.fibreArrow y x.1.x).base.left =
      eqToHom E ≫ (D.fibreArrow y z.1.x).base.left :=
    (D.p_fibrePoint y p c x.1).symm.trans ((congrArg _ h₀).trans
      (D.p_app_map_eqToHom y p E _ _ (D.p_fibrePoint y p c z.1)))
  rw [D.fibreArrow_base_left y x.1.x, D.fibreArrow_base_left y z.1.x] at hp'
  have hx := eq_eqToHom_comp_of_conj _ _ _ _ _ _ hp'
  have hxz : x.1.x.left = z.1.x.left :=
    (Functor.congr_obj y.w x.1.x).symm.trans (E.trans (Functor.congr_obj y.w z.1.x))
  have hx' : eqToHom hxz ≫ z.1.x.hom = x.1.x.hom := hx.symm
  let a : x.1.x ⟶ z.1.x := Over.homMk (eqToHom hxz) hx'
  have hal0 : a.left = eqToHom hxz := rfl
  have hal : (D.fibreMapHom y a).base.left = eqToHom E := by
    rw [D.fibreMapHom_base_left_of y a, hal0]
    exact eqToHom_comp_eqToHom_comp_eqToHom_eq _ _ _ _
  have h₁ : (D.fibrePoint y p c x.1).1 =
      H.1.map ((D.fibreMapHom y a).base.left).op (D.fibrePoint y p c z.1).1 := by
    rw [hal]
    exact h₀
  obtain ⟨m, hm⟩ := D.exists_hom_of_fibreClassMap_eq y a
    (D.fibreClassMap_eq_of_fibrePoint y p c a h₁)
  have hlift : (D.fibreProduct y).val.p.IsHomLift (𝟙 U) m := by
    refine IsHomLift.of_fac' _ (𝟙 U) m x.2 z.2 ?_
    show m.hbase = _
    rw [TwoFibreProductOver.Hom.hbase_eq m, hm]
    exact eqToHom_comp_eqToHom_comp_eqToHom_eq_id x.1.hx.symm hxz z.1.hx x.2 z.2
  have hgpd : IsGroupoid ((D.fibreProduct y).val.p.Fiber U) :=
    TwoFibreProductOver.fiber_isGroupoid
      (Stack.schemeFibredCategory B S hS V).isFiberedInGroupoids
      D.quotCatFiberedInGroupoids.isFiberedInGroupoids U
      (p𝒮 := D.toCoherentSituation.coherentCFG.val.p)
      (F := y.toFunctor) (G := D.quotToCoherentCFG.hom.toFunctor)
  have : IsIso (⟨m, hlift⟩ : x ⟶ z) := hgpd.all_isIso _
  exact ⟨asIso (⟨m, hlift⟩ : x ⟶ z)⟩

/-- **The kernel of a surjection from `F_T` onto the module of an object of `Coh_{X/B}` is a
quotient classified by `Quot_{F/X/B}`.** -/
theorem kernelSubobject_mem_properlySupportedQuotients (E : CoherentObject D.toCoherentSituation)
    (v : D.baseChangeModule E.T ⟶ E.F) (hv : Epi v) :
    kernelSubobject v ∈ D.properlySupportedQuotients E.T := by
  let e : D.quotientModule E.T (kernelSubobject v) ≅ E.F := Abelian.cokernelKernelSubobjectIso v
  obtain ⟨_, hU, hP⟩ := E.properSupport
  exact ⟨⟨⟨SheafOfModules.IsQuasicoherentOnSite.of_iso e.symm E.quasicoherent,
      IsFlatOver.of_iso B S hS _ e.symm E.flat⟩,
    SheafOfModules.IsFinitePresentationOnSite.of_iso e.symm E.finitePresentation⟩,
    D.isProperlySupportedOver_of_iso e.symm ⟨hU, hP⟩⟩

/-- **Every section of the locus of surjections is the section attached to an object of the
2-fibre product.** -/
theorem fibreCls_surjective (U : BigFppfOver B S hS)
    (σ : (D.fibreSurjLocus y p c).toFunctor.obj (op U)) :
    ∃ x : (D.fibreProduct y).val.p.Fiber U, D.fibreCls y p c U x = σ := by
  obtain ⟨h, hh⟩ := σ
  have cA : (D.fibreBase y).T.left = V := Functor.congr_obj y.w (Over.mk (𝟙 V))
  let t : U ⟶ (D.fibreBase y).T.left := p.hom.app (op U) h
  let x : Over V := Over.mk (t ≫ eqToHom cA)
  have cx : (y.obj x).T.left = U := Functor.congr_obj y.w x
  let h' : H.1.obj (op (y.obj x).T.left) := H.1.map (eqToHom cx).op h
  have hh' : h' ∈ (D.fibreSurjLocus y p c).obj (op (y.obj x).T.left) :=
    (D.fibreSurjLocus y p c).map (eqToHom cx).op hh
  have hfa : (D.fibreArrow y x).base.left = eqToHom cx ≫ t := by
    rw [D.fibreArrow_base_left y x]
    show eqToHom (Functor.congr_obj y.w x) ≫ (t ≫ eqToHom cA) ≫
      eqToHom (Functor.congr_obj y.w (Over.mk (𝟙 V))).symm = _
    exact eqToHom_comp_comp_eqToHom_eqToHom _ _ _ _ _
  let Z : Over (D.fibreBase y).T := Over.mk (D.fibreArrow y x).base
  have hph' : p.hom.app (op (y.obj x).T.left) h' =
      testPoint ((D.fibreTestFunctor (D.fibreBase y)).obj Z) := by
    refine (D.p_app_map_eqToHom y p cx h t rfl).trans ?_
    exact hfa.symm.trans (yonedaEquiv_yoneda_map _).symm
  let pt : spacePointsOverObj p ((D.fibreTestFunctor (D.fibreBase y)).obj Z) := ⟨h', hph'⟩
  let u := (D.fibrePointIso y p c).inv.app (op Z) (ULift.up pt)
  have hpu : (D.fibrePointIso y p c).hom.app (op Z) u = ULift.up pt :=
    (D.fibrePointIso y p c).inv_hom_id_app_apply (op Z) _
  have hpH : (D.fibreHomSituation (D.fibreBase y)).pointHom (modulePushforwardCoherence B S hS)
        p c pt =
      (D.fibreHomIso (D.fibreBase y) (modulePushforwardCoherence B S hS)).hom.app (op Z) u := by
    have h₁ := congrArg (c.hom.app (op ((D.fibreTestFunctor (D.fibreBase y)).obj Z))) hpu.symm
    exact h₁.trans (c.inv_hom_id_app_apply _ _)
  have hu : Epi u := by
    have h₁ := (D.fibreHomSituation (D.fibreBase y)).epi_pointHom_of_mem
      (modulePushforwardCoherence B S hS) p c pt hh'
    rw [hpH, D.fibreHomIso_hom_app] at h₁
    have : IsIso ((D.fibreRelativeIso (D.fibreBase y)).inv.app Z).op.unop.left :=
      (Over.forget (D.space (D.fibreBase y).T)).map_isIso
        ((D.fibreRelativeIso (D.fibreBase y)).inv.app Z)
    exact (D.fibreHomSituation (D.fibreBase y)).epi_of_epi_toModuleHom_moduleHomOver_map
      (modulePushforwardCoherence B S hS) _ u h₁
  have hc := modulePushforwardCoherence B S hS
  let e := D.fibreArrow y x
  let v : D.baseChangeModule (y.obj x).T ⟶ (y.obj x).F :=
    (D.baseChangeComparison e.base).hom.app D.F ≫ u ≫ (D.cohFibreIso e).hom
  have hv : Epi v :=
    epi_iso_hom_comp_comp_iso_hom ((D.baseChangeComparison e.base).app D.F) u (D.cohFibreIso e) hu
  let K := kernelSubobject v
  have hK := D.kernelSubobject_mem_properlySupportedQuotients (y.obj x) v hv
  let T₀ : SchemesOver D.Y := CostructuredArrow.mk (y.obj x).T.hom
  let ι : T₀ ⟶ (y.obj x).T := CostructuredArrow.homMk (𝟙 _) (by simp [T₀])
  let κ : (y.obj x).T ⟶ T₀ := CostructuredArrow.homMk (𝟙 _) (by simp [T₀])
  have hικ : κ ≫ ι = 𝟙 _ := CostructuredArrow.hom_ext _ _ (Category.id_comp _)
  let K₀ := D.quotientPullback ι K
  have hK₀ : K₀ ∈ D.properlySupportedQuotients T₀ :=
    D.quotientPullback_mem_properlySupportedQuotients ι K hK
  have hKK : D.quotientPullback κ K₀ = K := by
    rw [← D.quotientPullback_comp hc, hικ, D.quotientPullback_id hc]
  let q : QuotFamilyOver D (y.obj x).T.left := ⟨(y.obj x).T.hom, K₀, hK₀⟩
  let eK : (D.cohObject (y.obj x).T K hK).F ≅ (y.obj x).F := Abelian.cokernelKernelSubobjectIso v
  let χ := D.cohHomOfData κ hKK hK₀ hK
  let φ₀ : CoherentHom (y.obj x) (D.cohObject T₀ K₀ hK₀) :=
    { base := κ, fibre := χ.fibre ≫ eK.hom
      isIso_fibre := @IsIso.comp_isIso _ _ _ _ _ _ _ χ.isIso_fibre (Iso.isIso_hom eK) }
  let φ' : (y.obj x : D.toCoherentSituation.coherentCFG.val.obj) ⟶ D.cohObject T₀ K₀ hK₀ := φ₀
  have hpφ : D.toCoherentSituation.coherentCFG.val.p.map φ' = 𝟙 (y.obj x).T.left := rfl
  have hφiso : IsIso φ' := by
    have := IsHomLift.map D.toCoherentSituation.coherentCFG.val.p φ'
    have := D.toCoherentSituation.coherentCFG.isFiberedInGroupoids.isStronglyCartesian_homLift
      (D.toCoherentSituation.coherentCFG.val.p.map φ') φ'
    have : IsIso (D.toCoherentSituation.coherentCFG.val.p.map φ') := by
      rw [hpφ]
      exact IsIso.id _
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso
      (p := D.toCoherentSituation.coherentCFG.val.p)
      (f := D.toCoherentSituation.coherentCFG.val.p.map φ') φ'
  have hvert : D.toCoherentSituation.coherentCFG.val.p.IsHomLift (𝟙 U) φ' :=
    IsHomLift.of_fac' _ (𝟙 U) φ' cx cx (hpφ.trans (eqToHom_comp_id_comp_eqToHom cx))
  let Qy : D.quotCatFiberedInGroupoids.val.obj := ⟨(y.obj x).T.left, ⟨q⟩⟩
  let P₀ : (D.fibreProduct y).val.obj :=
    { base := U
      x := x
      y := Qy
      hx := rfl
      hy := cx
      iso := @asIso _ _ _ _ φ' hφiso
      vertical := hvert }
  have hcm : D.fibreClassMap y P₀ = v := by
    have e1 : D.fibreClassMap y P₀ = D.pullMapOf κ (χ.fibre ≫ eK.hom)
        (D.quotientProjection T₀ K₀) := rfl
    have e2 : D.pullMapOf κ χ.fibre (D.quotientProjection T₀ K₀) =
        D.quotientProjection (y.obj x).T K :=
      D.pullMapOf_quotientFibreIso_quotientProjection κ hKK
    have e3 : v ≫ eK.inv = D.quotientProjection (y.obj x).T K :=
      Abelian.cokernelKernelSubobjectIso_inv_comp v
    have e4 : D.quotientProjection (y.obj x).T K ≫ eK.hom = v := by
      rw [← e3]
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun w => v ≫ w) eK.inv_hom_id).trans (Category.comp_id v))
    exact e1.trans ((D.pullMapOf_comp_right κ χ.fibre eK.hom (D.quotientProjection T₀ K₀)).trans
      ((congrArg (fun w => w ≫ eK.hom) e2).trans e4))
  have hch : D.fibreClassHom y hc P₀ = u :=
    (D.homOfPullMap_unique e.base (D.cohFibreIso e) (D.fibreClassMap y P₀) u hcm.symm).symm
  have hpt : (D.fibrePoint y p c P₀).1 = h' :=
    congrArg (fun w => w.down.1) ((congrArg ((D.fibrePointIso y p c).hom.app (op Z)) hch).trans hpu)
  refine ⟨⟨P₀, rfl⟩, Subtype.ext ?_⟩
  show H.1.map (eqToHom rfl).op (H.1.map (eqToHom (D.fibreBaseEq y P₀).symm).op
    (D.fibrePoint y p c P₀).1) = h
  rw [hpt]
  exact presheaf_map_eqToHom_three H.1 (A := (y.obj x).T.left) rfl (D.fibreBaseEq y P₀).symm cx h

/-- **The isomorphism classes of the 2-fibre product are classified by the locus of
surjections.** -/
def fibreClassifier :
    (D.fibreProduct y).val.p.IsoClassClassifier (D.fibreSurjLocus y p c).toFunctor where
  cls := D.fibreCls y p c
  cls_map := D.fibreCls_map y p c
  injective := D.fibreCls_injective y p c
  surjective := D.fibreCls_surjective y p c

/-- **The 2-fibre product of `Quot_{F/X/B} ⟶ Coh_{X/B}` with a scheme-valued point is
representable by an algebraic space**, given an algebraic space representing the relative Hom
functor of `y(V)` whose locus of surjections is open. -/
theorem isRepresentableByAlgebraicSpace_fibreProduct_of_homRepresentation
    (hopen : IsOpenSubspace B S hS (D.fibreSurjLocus y p c)) :
    IsRepresentableByAlgebraicSpace B S hS (D.fibreProduct y) := by
  rw [isRepresentableByAlgebraicSpace_iff]
  have hset : (D.fibreProduct y).val.p.IsFiberedInSetoids :=
    TwoFibreProductOver.structureFunctor_isFiberedInSetoids _ _ _ _ _
      (StacksRepresentableCFG.over_isFiberedInSetoids V)
      (presheafOfGroupoids_typeToGrpd_isFiberedInSetoids D.quotSitePresheaf)
      D.toCoherentSituation.coherentCFG.isFiberedInGroupoids y.w D.quotToCoherentCFG.hom.w
  refine ⟨hset, ?_⟩
  let : (D.fibreProduct y).val.p.IsFibered := (D.fibreProduct y).2.isFibered
  exact ⟨_, hopen.1, (D.fibreClassifier y p c).equiv,
    fun U V f a => (D.fibreClassifier y p c).equiv_naturality f a⟩

end QuotSituation

end AlgebraicGeometry.Space

end
