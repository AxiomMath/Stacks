module

public import StacksFrontier.AlgebraicGeometry.ProperFiniteness.GlobalSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalFunctionsFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.PhCoveringProperSurjective

/-!
# Global functions of a reduced algebraic space proper over a Noetherian ring

Let `R` be a Noetherian ring and let `X` be a *reduced* algebraic space proper over `Spec R`.
Then the ring `Γ(X, 𝒪_X)` of global regular functions on `X` is a finite `R`-module. If moreover
`R` is reduced and `X ⟶ Spec R` is surjective, then `R ⟶ Γ(X, 𝒪_X)` is injective.

## Main definitions

* `AlgebraicGeometry.Space.chartFunctionsEval`: evaluation of a compatible family of regular
  functions on all scheme charts at one chart.
* `AlgebraicGeometry.Space.globalFunctionsToChart`: the pullback of global regular functions of
  an algebraic space along an arbitrary scheme chart, not necessarily étale.

## Main results

* `AlgebraicGeometry.Space.algebraMap_globalFunctionsToChart`: the pullback is compatible with
  the base ring.
* `AlgebraicGeometry.Space.injective_globalFunctionsToChart_of_isSurjective`: pullback of global
  functions of a reduced algebraic space along a surjective scheme chart is injective.
* `AlgebraicGeometry.Space.module_finite_globalFunctions_of_isProper`: the global functions of a
  reduced algebraic space proper over a Noetherian ring form a finite module.
* `AlgebraicGeometry.Space.injective_algebraMap_globalFunctions_of_isProper`: for a proper
  surjective morphism onto `Spec R` with `R` reduced, `R ⟶ Γ(X, 𝒪_X)` is injective.

## References

* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- Pullback of global functions along a surjective morphism to a reduced scheme is injective.
-/
theorem Scheme.Hom.appTop_injective_of_surjective_of_isReduced {P W : Scheme.{u}} (h : P ⟶ W)
    [Surjective h] [IsReduced W] : Function.Injective h.appTop.hom := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  apply eq_zero_of_basicOpen_eq_bot
  ext x
  simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hx
  obtain ⟨y, rfl⟩ := h.surjective x
  have hy : y ∈ h ⁻¹ᵁ W.basicOpen t := hx
  rw [Scheme.preimage_basicOpen_top, ht, Scheme.basicOpen_zero] at hy
  exact hy

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- Evaluation of a compatible family of regular functions on all scheme charts at one chart. -/
def chartFunctionsEval (j : CostructuredArrow yoneda F) :
    chartFunctions B S hS F →+* Γ((BigFppfOver.toScheme B S hS).obj j.left, ⊤) where
  toFun c := c.val (op j)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **Pullback of global regular functions along a scheme chart.** For an algebraic space `X`
and an arbitrary morphism `ρ : h_V ⟶ X` from a represented presheaf, the value at `ρ` of the
extension of a global function to all scheme charts. -/
def globalFunctionsToChart (X : AlgebraicSpaces B S hS) {V : BigFppfOver B S hS}
    (ρ : yoneda.obj V ⟶ X.obj) :
    globalFunctions B S hS X.obj →+* Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
  (chartFunctionsEval B S hS X.obj (CostructuredArrow.mk ρ)).comp
    (globalFunctionsChartEquiv B S hS X).val.toRingHom

/-- If a morphism `k` of representable presheaves, equal to `yoneda.map m`, has a property after
pullback to schemes, then `toScheme.map m` has that property. -/
private theorem map_of_presheaf_yoneda_map (P : MorphismProperty Scheme.{u})
    {V W : BigFppfOver B S hS} (m : V ⟶ W) (k : yoneda.obj V ⟶ yoneda.obj W)
    (hm : yoneda.map m = k)
    (h : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf k) :
    P ((BigFppfOver.toScheme B S hS).map m) := by
  subst hm
  change (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).relative yoneda
    (yoneda.map m) at h
  have := MorphismProperty.of_relative_map h
  exact this

/-- The extension of a global function to all scheme charts restricts to it on an étale
chart. -/
theorem globalFunctionsChartEquiv_val_etale (X : AlgebraicSpaces B S hS)
    (s : globalFunctions B S hS X.obj) (U : SmallEtale B S hS X.obj) :
    ((globalFunctionsChartEquiv B S hS X).val s).val
        ((SmallEtale.inclusion B S hS X.obj).op.obj (op U)) = s.val (op U) :=
  congrArg (fun t : globalFunctions' B S hS X.obj => t.val (op U))
    ((globalFunctionsChartEquiv B S hS X).property s)

/-- **Pullback of global functions of a reduced algebraic space along a surjective scheme chart
is injective.** Let `X` be an algebraic space which is reduced, and let `ρ : h_V ⟶ X` be
surjective. Then pullback of global functions along `ρ` is injective. -/
theorem injective_globalFunctionsToChart_of_isSurjective (X : AlgebraicSpaces B S hS)
    (hred : HasEtaleLocalProperty B S hS X.obj
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced T))
    {V : BigFppfOver B S hS} (ρ : yoneda.obj V ⟶ X.obj) (hρ : IsSurjective B S hS ρ) :
    Function.Injective (globalFunctionsToChart B S hS X ρ) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro s hs
  obtain ⟨U, φ, hφsurj, hφet, hUred⟩ := hred
  let Uc : SmallEtale B S hS X.obj := ⟨CostructuredArrow.mk φ, hφet⟩
  apply injective_globalFunctions_val_of_isSurjective B S hS X.obj X.property Uc
    ((presheafSurjective_iff_isSurjective_yoneda B S hS X.obj X.property U φ).1 hφsurj)
  change s.val (op Uc) = (0 : globalFunctions B S hS X.obj).val (op Uc)
  obtain ⟨P, α, p, hpb⟩ := hφet.1 ρ
  let pHom : P ⟶ U := Yoneda.fullyFaithful.preimage p
  have hpHom : yoneda.map pHom = p := Yoneda.fullyFaithful.map_preimage p
  have hpSurj : IsSurjective B S hS p := by
    have hfst : IsSurjective B S hS (pullback.fst φ ρ) :=
      isSurjective_pullback_fst B S hS (isAlgebraicSpace_yoneda B S hS U) X.property
        (isAlgebraicSpace_yoneda B S hS V) φ ρ hρ
    rw [← hpb.isoPullback_hom_fst]
    exact isSurjective_comp B S hS (isSurjective_of_isIso B S hS _) hfst
  have hpSurj' : _root_.AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map pHom) :=
    map_of_presheaf_yoneda_map B S hS _ pHom p hpHom
      ((presheafSurjective_iff_isSurjective_yoneda B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U) P p).mpr hpSurj)
  let c := (globalFunctionsChartEquiv B S hS X).val s
  let jU : CostructuredArrow yoneda X.obj := CostructuredArrow.mk φ
  let jV : CostructuredArrow yoneda X.obj := CostructuredArrow.mk ρ
  let jP : CostructuredArrow yoneda X.obj := CostructuredArrow.mk (yoneda.map pHom ≫ φ)
  let gPU : jP ⟶ jU := CostructuredArrow.homMk pHom (by simp [jP, jU])
  let gPV : jP ⟶ jV := CostructuredArrow.homMk α (by
    change yoneda.map α ≫ ρ = yoneda.map pHom ≫ φ
    rw [hpHom]
    exact hpb.w.symm)
  have hPU : (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map pHom).op).hom (c.val (op jU)) =
      c.val (op jP) := c.property gPU.op
  have hPV : (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map α).op).hom (c.val (op jV)) =
      c.val (op jP) := c.property gPV.op
  have hV0 : c.val (op jV) = 0 := hs
  have hU : c.val (op jU) = s.val (op Uc) :=
    globalFunctionsChartEquiv_val_etale B S hS X s Uc
  have _ : _root_.AlgebraicGeometry.IsReduced ((BigFppfOver.toScheme B S hS).obj U) := hUred
  have hinj := Scheme.Hom.appTop_injective_of_surjective_of_isReduced
    ((BigFppfOver.toScheme B S hS).map pHom)
  rw [← hU]
  refine hinj ?_
  change (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map pHom).op).hom (c.val (op jU)) =
    ((BigFppfOver.toScheme B S hS).map pHom).appTop.hom 0
  rw [hPU, ← hPV, hV0, map_zero, map_zero]
  rfl

/-! ### Over an affine base -/

section Base

variable (R : Type u) [CommRing R] (hR : B.Contains (Spec (.of R)))

/-- The constant family of regular functions on all scheme charts of a presheaf over `Spec R`
given by a scalar: its value on a chart is the pullback of the scalar along the structure
morphism. -/
def chartFunctionsOfBase (X : (BigFppfOver B (Spec (.of R)) hR)ᵒᵖ ⥤ Type u) (r : R) :
    chartFunctions B (Spec (.of R)) hR X :=
  ⟨fun j => (((Scheme.ΓSpecIso (.of R)).inv ≫
      Scheme.Γ.map ((B.inclusion.map j.unop.left.hom).op)).hom r), by
    intro j k g
    have hw : B.inclusion.map g.unop.left.left ≫ B.inclusion.map j.unop.left.hom =
        B.inclusion.map k.unop.left.hom := by
      simpa only [← Functor.map_comp] using congrArg B.inclusion.map (Over.w g.unop.left)
    change (((Scheme.ΓSpecIso (.of R)).inv ≫
      (B.inclusion.map j.unop.left.hom).appTop ≫
      (B.inclusion.map g.unop.left.left).appTop).hom r) =
      (((Scheme.ΓSpecIso (.of R)).inv ≫ (B.inclusion.map k.unop.left.hom).appTop).hom r)
    rw [← Scheme.Hom.comp_appTop, hw]⟩

/-- The extension to all scheme charts of the image of a scalar is the constant family. -/
theorem globalFunctionsChartEquiv_algebraMap
    (X : AlgebraicSpaces B (Spec (.of R)) hR) (r : R) :
    (globalFunctionsChartEquiv B (Spec (.of R)) hR X).val
        (algebraMap R (globalFunctions B (Spec (.of R)) hR X.obj) r) =
      chartFunctionsOfBase B R hR X.obj r := by
  apply chartFunctionsToSmall_injective B (Spec (.of R)) hR X.obj X.property
  rw [(globalFunctionsChartEquiv B (Spec (.of R)) hR X).property]
  rfl

/-- **Pullback of global functions along a scheme chart is compatible with the base ring.** -/
theorem algebraMap_globalFunctionsToChart (X : AlgebraicSpaces B (Spec (.of R)) hR)
    {V : BigFppfOver B (Spec (.of R)) hR} (ρ : yoneda.obj V ⟶ X.obj) (r : R) :
    globalFunctionsToChart B (Spec (.of R)) hR X ρ
        (algebraMap R (globalFunctions B (Spec (.of R)) hR X.obj) r) =
      @algebraMap R _ _ _ (siteObjSectionsAlgebra R V) r := by
  change ((globalFunctionsChartEquiv B (Spec (.of R)) hR X).val
    (algebraMap R (globalFunctions B (Spec (.of R)) hR X.obj) r)).val
      (op (CostructuredArrow.mk ρ)) = _
  rw [globalFunctionsChartEquiv_algebraMap]
  rfl

/-- Pullback along a scheme chart, as a homomorphism of `R`-algebras. -/
def globalFunctionsToChartAlgHom (X : AlgebraicSpaces B (Spec (.of R)) hR)
    {V : BigFppfOver B (Spec (.of R)) hR} (ρ : yoneda.obj V ⟶ X.obj) :
    letI := siteObjSectionsAlgebra R V
    globalFunctions B (Spec (.of R)) hR X.obj →ₐ[R]
      Γ((BigFppfOver.toScheme B (Spec (.of R)) hR).obj V, ⊤) :=
  letI := siteObjSectionsAlgebra R V
  { globalFunctionsToChart B (Spec (.of R)) hR X ρ with
    commutes' := algebraMap_globalFunctionsToChart B R hR X ρ }

/-- **Chow's lemma over `Spec R`.** For an algebraic space `X` proper over `Spec R` there is an
object `V` of the site and a proper surjective `ρ : h_V ⟶ X` whose underlying scheme is proper
over `Spec R`. -/
theorem exists_isProper_chowChart (X : AlgebraicSpaces B (Spec (.of R)) hR)
    (g : X.obj ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hR)))) (hg : IsProper B (Spec (.of R)) hR g) :
    ∃ (V : BigFppfOver B (Spec (.of R)) hR) (ρ : yoneda.obj V ⟶ X.obj),
      IsSurjective B (Spec (.of R)) hR ρ ∧
      _root_.AlgebraicGeometry.IsProper (B.inclusion.map V.hom) := by
  have hUaff : IsAffine ((BigFppfOver.toScheme B (Spec (.of R)) hR).obj
      (Over.mk (𝟙 (B.obj hR)))) := inferInstanceAs (IsAffine (Spec (.of R)))
  obtain ⟨V, ρ, hρP, hρS⟩ :=
    exists_properSurjective_schemeCover_of_isProper_toAffine B (Spec (.of R)) hR _ hUaff
      X.property g hg
  have hT := isAlgebraicSpace_yoneda B (Spec (.of R)) hR (Over.mk (𝟙 (B.obj hR)))
  have hVsp := isAlgebraicSpace_yoneda B (Spec (.of R)) hR V
  let m : V ⟶ Over.mk (𝟙 (B.obj hR)) := yoneda.preimage (ρ ≫ g)
  have hm : yoneda.map m = ρ ≫ g := yoneda.map_preimage _
  have hcompP : IsProper B (Spec (.of R)) hR (ρ ≫ g) :=
    isProper_comp B (Spec (.of R)) hR hVsp X.property hT ρ g hρP hg
  have hmProper : _root_.AlgebraicGeometry.IsProper
      ((BigFppfOver.toScheme B (Spec (.of R)) hR).map m) :=
    map_of_presheaf_yoneda_map B (Spec (.of R)) hR _ m (ρ ≫ g) hm
      ((presheaf_isProper_iff B (Spec (.of R)) hR (ρ ≫ g) hVsp hT
        (by rw [← hm]; exact Functor.relativelyRepresentable.map yoneda m)).mp hcompP)
  have hmV : m.left = V.hom := by simpa using Over.w m
  refine ⟨V, ρ, hρS, ?_⟩
  rw [← hmV]
  exact hmProper

/-- A morphism `h_V ⟶ h_{Spec R}` which is surjective on points has surjective underlying
morphism of schemes. -/
theorem surjective_structureHom_of_isSurjective {V : BigFppfOver B (Spec (.of R)) hR}
    (k : yoneda.obj V ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hR))))
    (hk : IsSurjective B (Spec (.of R)) hR k) :
    _root_.AlgebraicGeometry.Surjective (B.inclusion.map V.hom) := by
  have hT := isAlgebraicSpace_yoneda B (Spec (.of R)) hR (Over.mk (𝟙 (B.obj hR)))
  let m : V ⟶ Over.mk (𝟙 (B.obj hR)) := yoneda.preimage k
  have hm : yoneda.map m = k := yoneda.map_preimage _
  have hmV : m.left = V.hom := by simpa using Over.w m
  change _root_.AlgebraicGeometry.Surjective (B.inclusion.map V.hom)
  rw [← hmV]
  exact map_of_presheaf_yoneda_map B (Spec (.of R)) hR _ m k hm
    ((presheafSurjective_iff_isSurjective_yoneda B (Spec (.of R)) hR _ hT V k).mpr hk)

/-- The structure map of the `R`-algebra of regular functions of an object of the site is
finite when the structure morphism is proper and `R` is Noetherian. -/
theorem module_finite_siteObjFunctions [IsNoetherianRing R] (V : BigFppfOver B (Spec (.of R)) hR)
    (hV : _root_.AlgebraicGeometry.IsProper (B.inclusion.map V.hom)) :
    @Module.Finite R Γ((BigFppfOver.toScheme B (Spec (.of R)) hR).obj V, ⊤) _ _
      (siteObjSectionsAlgebra R V).toModule := by
  have h0 : ((B.inclusion.map V.hom).appTop.hom).Finite :=
    finiteGlobalSectionsOfProper R inferInstance (B.inclusion.map V.hom) hV
  have hc : (((Scheme.ΓSpecIso (.of R)).inv ≫ (B.inclusion.map V.hom).appTop).hom).Finite :=
    h0.comp (RingHom.Finite.of_surjective ((Scheme.ΓSpecIso (.of R)).inv.hom)
      (fun x => ⟨(Scheme.ΓSpecIso (.of R)).hom.hom x, by simp⟩))
  exact hc

/-- The structure map of the regular functions of an object of the site over `Spec R` is
injective when the structure morphism is surjective and `R` is reduced. -/
theorem injective_algebraMap_siteObjFunctions [_root_.IsReduced R]
    (V : BigFppfOver B (Spec (.of R)) hR)
    (hV : _root_.AlgebraicGeometry.Surjective (B.inclusion.map V.hom)) :
    Function.Injective (@algebraMap R Γ((BigFppfOver.toScheme B (Spec (.of R)) hR).obj V, ⊤) _ _
      (siteObjSectionsAlgebra R V)) := by
  have _ : _root_.AlgebraicGeometry.IsReduced (B.inclusion.obj (B.obj hR)) :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsReduced (Spec (.of R)))
  have h1 : Function.Injective (B.inclusion.map V.hom).appTop.hom :=
    Scheme.Hom.appTop_injective_of_surjective_of_isReduced (B.inclusion.map V.hom)
  have h2 : Function.Injective (Scheme.ΓSpecIso (.of R)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).1
  exact h1.comp h2

/-- **The global functions of a reduced algebraic space proper over a Noetherian ring form a
finite module.** Let `R` be a Noetherian ring and let `X` be an algebraic space over `Spec R`
whose structure morphism `g` is proper and which is reduced. Then `Γ(X, 𝒪_X)` is a finite
`R`-module. -/
theorem module_finite_globalFunctions_of_isProper [IsNoetherianRing R]
    (X : AlgebraicSpaces B (Spec (.of R)) hR)
    (g : X.obj ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hR)))) (hg : IsProper B (Spec (.of R)) hR g)
    (hred : HasEtaleLocalProperty B (Spec (.of R)) hR X.obj
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced T)) :
    Module.Finite R (globalFunctions B (Spec (.of R)) hR X.obj) := by
  obtain ⟨V, ρ, hρS, hVP⟩ := exists_isProper_chowChart B R hR X g hg
  let := siteObjSectionsAlgebra R V
  have := module_finite_siteObjFunctions B R hR V hVP
  exact Module.Finite.of_injective (globalFunctionsToChartAlgHom B R hR X ρ).toLinearMap
    (injective_globalFunctionsToChart_of_isSurjective B (Spec (.of R)) hR X hred ρ hρS)

/-- **A reduced base ring injects into the global functions of a proper algebraic space
surjecting onto its spectrum.** Let `R` be a reduced ring and let `g : X ⟶ Spec R` be proper and
surjective. Then `R ⟶ Γ(X, 𝒪_X)` is injective. -/
theorem injective_algebraMap_globalFunctions_of_isProper [_root_.IsReduced R]
    (X : AlgebraicSpaces B (Spec (.of R)) hR)
    (g : X.obj ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hR)))) (hg : IsProper B (Spec (.of R)) hR g)
    (hgs : IsSurjective B (Spec (.of R)) hR g) :
    Function.Injective (algebraMap R (globalFunctions B (Spec (.of R)) hR X.obj)) := by
  obtain ⟨V, ρ, hρS, -⟩ := exists_isProper_chowChart B R hR X g hg
  let := siteObjSectionsAlgebra R V
  have hinj := injective_algebraMap_siteObjFunctions B R hR V
    (surjective_structureHom_of_isSurjective B R hR (ρ ≫ g)
      (isSurjective_comp B (Spec (.of R)) hR hρS hgs))
  have hc : (globalFunctionsToChartAlgHom B R hR X ρ : _ →+* _).comp
      (algebraMap R (globalFunctions B (Spec (.of R)) hR X.obj)) =
      @algebraMap R _ _ _ (siteObjSectionsAlgebra R V) :=
    (globalFunctionsToChartAlgHom B R hR X ρ).comp_algebraMap
  rw [← hc, RingHom.coe_comp] at hinj
  exact Function.Injective.of_comp hinj

end Base

end Space

end AlgebraicGeometry

end
