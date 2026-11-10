module

public import
  StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.RepresentedC3TensorCompatAssembly
public import
    StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.RepresentedC3UnitCompatProof

/-!
# The compatibility of the unit identification of Stacks 03DX (2) with inverse images

For a morphism `g : V ⟶ U` of the big fppf site over `S`, the identification
`(𝒪_U)_{yoneda U} ≅ 𝒪_{yoneda U}` of Stacks 03DX (2)
(`AlgebraicGeometry.Space.representedQuasicoherentSchemeUnitIso`) is compatible with inverse
images along `g` (`AlgebraicGeometry.Space.RepresentedC3UnitCompat`).

## Main results

* `AlgebraicGeometry.Space.representedC3UnitCompat`: the compatibility.
* `AlgebraicGeometry.Space.unitCompat_of_readings_of_heq`: its abstract shape, at variables.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u uCV vCV

namespace AlgebraicGeometry.Space

section Abstract

/-- An equation `x ≫ y = z ≫ w ≫ v` transported along equalities of the objects and
heterogeneous equalities of the morphisms. -/
theorem comp_eq_comp_comp_of_heq {C : Type*} [Category C] {A B D E F A₂ B₂ D₂ E₂ F₂ : C}
    (hA : A₂ = A) (hB : B₂ = B) (hD : D₂ = D) (hE : E₂ = E) (hF : F₂ = F)
    {x₂ : A₂ ⟶ B₂} {y₂ : B₂ ⟶ F₂} {z₂ : A₂ ⟶ D₂} {w₂ : D₂ ⟶ E₂} {v₂ : E₂ ⟶ F₂}
    {x : A ⟶ B} {y : B ⟶ F} {z : A ⟶ D} {w : D ⟶ E} {v : E ⟶ F}
    (hx : HEq x₂ x) (hy : HEq y₂ y) (hz : HEq z₂ z) (hw : HEq w₂ w) (hv : HEq v₂ v)
    (h : x₂ ≫ y₂ = z₂ ≫ w₂ ≫ v₂) : x ≫ y = z ≫ w ≫ v := by
  subst hA hB hD hE hF
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hy
  obtain rfl := eq_of_heq hz
  obtain rfl := eq_of_heq hw
  obtain rfl := eq_of_heq hv
  exact h

/-- `AlgebraicGeometry.Space.unitCompat_of_readings` with the description `hC₀` of `c` after `θ`
taken at its own object `X₀`, and with the square `h₂` of the identifications `p₁` taken in its
own category `CX₂` and spelling, linked to the slots of the compatibility by equalities of
categories and objects and by heterogeneous equalities of morphisms. -/
theorem unitCompat_of_readings_of_heq {ZU ZV CU DU DV : Type*} {CV : Type uCV} [Category ZU]
    [Category ZV] [Category CU] [instCV : Category.{vCV} CV] [Category DU] [Category DV]
    {Ac : CU ⥤ CV} {EU : CU ⥤ DU} {EV : CV ⥤ DV} {Phi : DU ⥤ DV} (θ : Ac ⋙ EV ⟶ EU ⋙ Phi)
    (hθ : IsIso θ) {OCU : CU} {OCV : CV} {ODU : DU} {ODV : DV}
    (k₁ : EV.obj (Ac.obj OCU) ⟶ EV.obj OCV) (k₂ : EV.obj OCV ⟶ ODV)
    (k₃ : EV.obj (Ac.obj OCU) ⟶ Phi.obj (EU.obj OCU)) (k₄ : Phi.obj (EU.obj OCU) ⟶ Phi.obj ODU)
    (k₅ : Phi.obj ODU ⟶ ODV) (hKF1 : k₁ ≫ k₂ = k₃ ≫ k₄ ≫ k₅)
    (q : Ac.obj OCU ⟶ OCV) (hk₁ : k₁ = EV.map q) (p₂U : EU.obj OCU ≅ ODU) (p₂V : EV.obj OCV ≅ ODV)
    (hk₂ : k₂ = p₂V.hom) (hk₃ : k₃ = θ.app OCU) (hk₄ : k₄ = Phi.map p₂U.hom)
    (mU : Phi.obj ODU ⟶ ODV) (hk₅ : k₅ = mU)
    (LU : ZU ⥤ CU) (LV : ZV ⥤ CV) (Rz : ZU ⥤ ZV) (β : Rz ⋙ LV ≅ LU ⋙ Ac) {OZU : ZU} {OZV : ZV}
    (p₁U : LU.obj OZU ≅ OCU) (uU : EU.obj (LU.obj OZU) ≅ ODU) (huU : uU = EU.mapIso p₁U ≪≫ p₂U)
    (p₁V : LV.obj OZV ≅ OCV) (uV : EV.obj (LV.obj OZV) ≅ ODV) (huV : uV = EV.mapIso p₁V ≪≫ p₂V)
    (pb pb₀ : Rz.obj OZU ⟶ OZV) (hpb : pb₀ = pb)
    (c : Phi.obj (EU.obj (LU.obj OZU)) ⟶ EV.obj (LV.obj (Rz.obj OZU)))
    (mid : EV.obj (LV.obj (Rz.obj OZU)) ⟶ EV.obj (LV.obj OZV)) (hmid : mid = EV.map (LV.map pb))
    (X₀ : CU) (c₀ : Phi.obj (EU.obj X₀) ⟶ EV.obj (LV.obj (Rz.obj OZU)))
    (b₀ : Ac.obj X₀ ⟶ LV.obj (Rz.obj OZU)) (hC₀ : θ.app X₀ ≫ c₀ = EV.map b₀)
    (hX₀ : X₀ = LU.obj OZU) (hc : HEq c₀ c) (hb : HEq b₀ (β.inv.app OZU))
    (Z₂ : Type*) (instZ₂ : Category Z₂) (Y₁₂ : Type*) (instY₁₂ : Category Y₁₂) (Y₂₂ : Type*)
    (instY₂₂ : Category Y₂₂) (CX₂ : Type uCV) (instCX₂ : Category.{vCV} CX₂)
    (Lψ₁ : Z₂ ⥤ Y₁₂) (Lφ₁ : Y₁₂ ⥤ CX₂) (Lψ₂ : Z₂ ⥤ Y₂₂) (Lφ₂ : Y₂₂ ⥤ CX₂)
    (t₂ : Lψ₁ ⋙ Lφ₁ ⟶ Lψ₂ ⋙ Lφ₂) (O₂ : Z₂) (P₁ : Y₁₂) (P₂ : Y₂₂) (Q₂ : CX₂)
    (a₂ : Lψ₁.obj O₂ ⟶ P₁) (b₂ : Lφ₁.obj P₁ ⟶ Q₂) (c₂ : Lψ₂.obj O₂ ⟶ P₂) (d₂ : Lφ₂.obj P₂ ⟶ Q₂)
    (h₂ : Lφ₁.map a₂ ≫ b₂ = t₂.app O₂ ≫ Lφ₂.map c₂ ≫ d₂)
    (hCX : CX₂ = CV) (hinst : HEq instCX₂ instCV)
    (hA : HEq (Lφ₁.obj (Lψ₁.obj O₂)) (LV.obj (Rz.obj OZU))) (hB : HEq (Lφ₁.obj P₁) (LV.obj OZV))
    (hQ : HEq Q₂ OCV) (hD : HEq (Lφ₂.obj (Lψ₂.obj O₂)) (Ac.obj (LU.obj OZU)))
    (hE : HEq (Lφ₂.obj P₂) (Ac.obj OCU))
    (h1 : HEq (Lφ₁.map a₂) (LV.map pb₀)) (h2 : HEq b₂ p₁V.hom)
    (h3 : HEq (t₂.app O₂) (β.hom.app OZU)) (h4 : HEq (Lφ₂.map c₂) (Ac.map p₁U.hom))
    (h5 : HEq d₂ q) :
    Phi.map uU.hom ≫ mU = c ≫ mid ≫ uV.hom := by
  subst hCX
  obtain rfl := eq_of_heq hinst
  subst hX₀
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hb
  exact unitCompat_of_readings θ hθ k₁ k₂ k₃ k₄ k₅ hKF1 q hk₁ p₂U p₂V hk₂ hk₃ hk₄ mU hk₅ LU LV Rz
    β p₁U uU huU p₁V uV huV pb pb₀ hpb c₀ mid hmid hC₀
    (comp_eq_comp_comp_of_heq (eq_of_heq hA) (eq_of_heq hB) (eq_of_heq hD) (eq_of_heq hE)
      (eq_of_heq hQ) h1 h2 h3 h4 h5 h₂)

end Abstract

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The statement of `unitCompat_of_readings_of_heq` with Stacks 03LU round the square of `g`,
the identifications of the structure sheaves and Stacks 03LU on schemes supplied. -/
theorem representedC3UnitCompat_reduction_square {V U : BigFppfOver B S hS} (g : V ⟶ U) :
    type_of% (unitCompat_of_readings_of_heq (representedSquareMate B S hS g)
    (isIso_representedSquareMate B S hS g) _ _ _ _ _
    (representedSquare_pullbackUnitIsoTransport_representedSquareMate B S hS g)
    _ rfl _ _ rfl rfl rfl
    (modulePullbackUnitIso B S hS (representedSpaceMap B S hS g)).hom (Category.id_comp _)
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj V) V.left.property)
    (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
      (associatedBigEtaleSite B) g.left))
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso (associatedBigEtaleSite B)
      g.left)
    (OZU := (quasicoherentUnitObj B S hS U).obj) (OZV := (quasicoherentUnitObj B S hS V).obj)
    (Stacks.SheafOfModules.pullbackUnitIsoTransport
      (_root_.AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
      (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property))
    (representedQuasicoherentSchemeUnitIso B S hS U)
    (representedQuasicoherentSchemeUnitIso_eq_representedReindexPullbackIso B S hS U)
    (Stacks.SheafOfModules.pullbackUnitIsoTransport
      (_root_.AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property)
      (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property))
    (representedQuasicoherentSchemeUnitIso B S hS V)
    (representedQuasicoherentSchemeUnitIso_eq_representedReindexPullbackIso B S hS V)
    (Stacks.PullbackAlgebra.pullbackUnitIso (_root_.AlgebraicGeometry.SmallEtale.schemeHom
      (associatedBigEtaleSite B) g.left).toLRSHom.toShHom).hom
    (Stacks.SheafOfModules.pullbackUnitIsoTransport
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        g.left).zariskiRingedToposModulesHom
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        g.left).zariskiPullbackModulesIso).hom
    ((_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        g.left).pullbackUnitIsoTransport_zariskiPullbackModulesIso_hom)
    (modulePullbackRepresentedQuasicoherentIso B S hS g (quasicoherentUnitObj B S hS U)).hom
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
      (quasicoherentPullbackUnitIso B S hS g).hom).hom
    (representedQuasicoherentSchemeEquivalence_map_quasicoherentPullbackUnitIso_hom B S hS g)) :=
  unitCompat_of_readings_of_heq (representedSquareMate B S hS g)
    (isIso_representedSquareMate B S hS g) _ _ _ _ _
    (representedSquare_pullbackUnitIsoTransport_representedSquareMate B S hS g)
    _ rfl _ _ rfl rfl rfl
    (modulePullbackUnitIso B S hS (representedSpaceMap B S hS g)).hom (Category.id_comp _)
    _ _ _ _
    (OZU := (quasicoherentUnitObj B S hS U).obj) (OZV := (quasicoherentUnitObj B S hS V).obj)
    _ _
    (representedQuasicoherentSchemeUnitIso_eq_representedReindexPullbackIso B S hS U)
    _ _
    (representedQuasicoherentSchemeUnitIso_eq_representedReindexPullbackIso B S hS V)
    _ _
    ((_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        g.left).pullbackUnitIsoTransport_zariskiPullbackModulesIso_hom)
    _ _
    (representedQuasicoherentSchemeEquivalence_map_quasicoherentPullbackUnitIso_hom B S hS g)

/-- The statement of `representedC3UnitCompat_reduction_square` with the identification
`g^*((𝒪_U)^a) ≅ (g^*𝒪_U)^a` on the small étale site supplied. -/
theorem representedC3UnitCompat_reduction_reading {V U : BigFppfOver B S hS} (g : V ⟶ U) :
    type_of% (representedC3UnitCompat_reduction_square B S hS g _ _ _
      (representedSquareMate_app_comp_modulePullbackRepresentedQuasicoherentIso_hom B S hS g
        (quasicoherentUnitObj B S hS U))) :=
  representedC3UnitCompat_reduction_square B S hS g _ _ _
    (representedSquareMate_app_comp_modulePullbackRepresentedQuasicoherentIso_hom B S hS g
      (quasicoherentUnitObj B S hS U))

/-- The statement of `representedC3UnitCompat_reduction_reading` with the object and the
morphisms of the identification `g^*((𝒪_U)^a) ≅ (g^*𝒪_U)^a` identified with those of the
compatibility. -/
theorem representedC3UnitCompat_reduction_readingHeq {V U : BigFppfOver B S hS} (g : V ⟶ U) :
    type_of% (representedC3UnitCompat_reduction_reading B S hS g rfl HEq.rfl HEq.rfl) :=
  representedC3UnitCompat_reduction_reading B S hS g rfl HEq.rfl HEq.rfl

/-- The statement of `representedC3UnitCompat_reduction_readingHeq` with Stacks 03LU round the
square of the scheme morphism underlying `g` supplied. -/
theorem representedC3UnitCompat_reduction_zariskiSquare {V U : BigFppfOver B S hS} (g : V ⟶ U) :
    type_of% (representedC3UnitCompat_reduction_readingHeq B S hS g _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ (_root_.AlgebraicGeometry.SmallEtale.zariskiSquare_pullbackUnitIsoTransport
        (associatedBigEtaleSite B) g.left)) :=
  representedC3UnitCompat_reduction_readingHeq B S hS g _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (_root_.AlgebraicGeometry.SmallEtale.zariskiSquare_pullbackUnitIsoTransport
      (associatedBigEtaleSite B) g.left)

/-- The statement of `representedC3UnitCompat_reduction_zariskiSquare` with the category of the
square of schemes identified with that of the compatibility. -/
theorem representedC3UnitCompat_reduction_category {V U : BigFppfOver B S hS} (g : V ⟶ U) :
    type_of% (representedC3UnitCompat_reduction_zariskiSquare B S hS g rfl HEq.rfl) :=
  representedC3UnitCompat_reduction_zariskiSquare B S hS g rfl HEq.rfl

/-- The statement of `representedC3UnitCompat_reduction_category` with the objects of the square
of schemes identified with those of the compatibility. -/
theorem representedC3UnitCompat_reduction_objects {V U : BigFppfOver B S hS} (g : V ⟶ U) :
    type_of% (representedC3UnitCompat_reduction_category B S hS g HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      HEq.rfl) :=
  representedC3UnitCompat_reduction_category B S hS g HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl

/-- The statement of `representedC3UnitCompat_reduction_objects` with the morphisms on `V` of the
square of schemes identified with those of the compatibility. -/
theorem representedC3UnitCompat_reduction_heqV {V U : BigFppfOver B S hS} (g : V ⟶ U) :
    type_of% (representedC3UnitCompat_reduction_objects B S hS g HEq.rfl HEq.rfl) :=
  representedC3UnitCompat_reduction_objects B S hS g HEq.rfl HEq.rfl

/-- The statement of `representedC3UnitCompat_reduction_heqV` with the comparison of the two
routes round the square of schemes identified with that of the compatibility. -/
theorem representedC3UnitCompat_reduction_heqComparison {V U : BigFppfOver B S hS} (g : V ⟶ U) :
    type_of% (representedC3UnitCompat_reduction_heqV B S hS g HEq.rfl) :=
  representedC3UnitCompat_reduction_heqV B S hS g HEq.rfl

/-- The statement of `representedC3UnitCompat_reduction_heqComparison` with the morphisms on `U`
of the square of schemes identified with those of the compatibility. -/
theorem representedC3UnitCompat_reduction_heqU {V U : BigFppfOver B S hS} (g : V ⟶ U) :
    type_of% (representedC3UnitCompat_reduction_heqComparison B S hS g HEq.rfl HEq.rfl) :=
  representedC3UnitCompat_reduction_heqComparison B S hS g HEq.rfl HEq.rfl

/-- The identification of Stacks 03DX (2) of the structure sheaf is compatible with inverse
images: for a morphism `g : V ⟶ U` of the big fppf site over `S`, the identification
`(𝒪_U)_{yoneda U} ≅ 𝒪_{yoneda U}` followed by Stacks 03LU for the represented morphism of
algebraic spaces agrees with `g^*((𝒪_U)_{yoneda U}) ≅ (g^*𝒪_U)_{yoneda V} ≅ (𝒪_V)_{yoneda V}`
followed by the identification on `V`. -/
theorem representedC3UnitCompat {V U : BigFppfOver B S hS} (g : V ⟶ U) :
    RepresentedC3UnitCompat B S hS g :=
  representedC3UnitCompat_reduction_heqU B S hS g

end AlgebraicGeometry.Space

end
