module

public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingComposition.RetargetLocalization
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ChartInfrastructure
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModuleDataOfFinite

/-!
# Chart data of the relative dualizing module on an open of the source

Let `f : Y ⟶ X` be a locally quasi-finite morphism of locally Noetherian schemes and `V₀ ⊆ Y` an
open. Chart data (Tag 0BVG) for `V₀ → X` on a sheaf `D ≅ N|_{V₀}` gives the affine
identifications of `N` on the charts `(U, V)` of `f` with `V ⊆ V₀`: the chart `V₀ ∩ V` of
`V₀ → X` has ring `Γ(V₀, V₀ ∩ V) ≅ Γ(Y, V)`, and the relative dualizing modules are compared by
transport along that isomorphism. The identifications so obtained are independent of the
factorization and compatible with both principal localizations of Tag 0BT2.

## Main definitions

* `Stacks.Discriminant.OpenChart.ringEquiv`: `Γ(Y, V) ≅ Γ(V₀, V₀ ∩ V)` over `Γ(X, U)`.
* `Stacks.Discriminant.OpenChart.localEquiv`: the affine identification `Γ(N, V) ≅ ω_F`.

## Main results

* `Stacks.Discriminant.OpenChart.localEquiv_natural`,
  `Stacks.Discriminant.OpenChart.localEquiv_baseBasicOpen`,
  `Stacks.Discriminant.OpenChart.localEquiv_basicOpen`: the three compatibilities of
  `Stacks.Discriminant.RelativeDualizingModuleData`, for charts inside `V₀`.
* `Stacks.Discriminant.OpenChart.localEquiv_ofFiniteTrace_restrictIso`: for chart data given by
  a finite trace on a factorization of `V₀ → X`, the identifications agree with those of its
  restriction to an open `W₀ ⊆ V₀`.

## References

* [Stacks Project, Tag 0BVG](https://stacks.math.columbia.edu/tag/0BVG)
* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Discriminant

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

section Trans

attribute [local instance] algebraDualModule

variable {X Y Y' : Scheme.{u}} {f : Y ⟶ X} {g : Y' ⟶ X} {i : Y ⟶ Y'} [IsOpenImmersion i]
  (hig : i ≫ g = f) [IsFinite g] (M : Y'.Modules) [M.IsQuasicoherent]
  (t : (Scheme.Modules.pushforward g).obj M ⟶ SheafOfModules.unit X.ringCatSheaf)
  (hbij : ∀ U : X.affineOpens, Function.Bijective (traceDual g t U.1))
  {N N' : Y.Modules} (e : N ≅ M.restrict i) (α : N' ≅ N)

/-- The chart identification of `ofFiniteTrace` through `α ≪≫ e` is the one through `e`
followed by `α⁻¹`. -/
theorem chartEquiv_trans (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (z : letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
      dualizingModule (chartFactorization hig U V hVU)) :
    chartEquiv hig M t hbij (α ≪≫ e) U V hVU z =
      α.inv.app V.1 (chartEquiv hig M t hbij e U V hVU z) := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  induction z using dualizingModule.induction_on with
  | zero => simp only [map_zero]
  | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul φ b =>
    rw [chartEquiv_tmul, chartEquiv_tmul, Scheme.Modules.Hom.app_smul]
    rfl

/-- Precomposing the identification `N ≅ M|_Y` with `α : N' ≅ N` precomposes the affine
identifications of `ofFiniteTrace` with the sections of `α`. -/
theorem ofFiniteTraceLocalEquiv_trans [IsLocallyNoetherian X] (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    ∀ (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1)) (s : Γ(N', V.1)),
      ofFiniteTraceLocalEquiv hig M t hbij (α ≪≫ e) U V hVU F s =
        ofFiniteTraceLocalEquiv hig M t hbij e U V hVU F (α.hom.app V.1 s) := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  intro F s
  change dualizingModuleEquiv _ F ((chartEquiv hig M t hbij (α ≪≫ e) U V hVU).symm s) =
    dualizingModuleEquiv _ F ((chartEquiv hig M t hbij e U V hVU).symm (α.hom.app V.1 s))
  congr 1
  rw [LinearEquiv.symm_apply_eq, chartEquiv_trans, LinearEquiv.apply_symm_apply]
  exact (congrArg (fun φ => φ s) (congrArg (fun φ => Scheme.Modules.Hom.app φ V.1)
    α.hom_inv_id)).symm

end Trans

namespace OpenChart

variable {X Y : Scheme.{u}} {V₀ : Y.Opens}

/-- For `V ⊆ V₀`, the image in `Y` of `V₀ ∩ V` is `V`. -/
theorem image_eq {V : Y.Opens} (hV : V ≤ V₀) {V' : V₀.toScheme.Opens}
    (h : V₀.ι ⁻¹ᵁ V = V') : V₀.ι ''ᵁ V' = V := by
  subst h
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr hV

/-- For `V ⊆ V₀`, the inclusion `V₀.ι ''ᵁ (V₀ ∩ V) ≤ V` is the identification `image_eq`. -/
private theorem homOfLE_image_eq {V : Y.Opens} (hV : V ≤ V₀) {V' : V₀.toScheme.Opens}
    (h : V₀.ι ⁻¹ᵁ V = V') :
    homOfLE (image_le_of_le_preimage h.ge) = eqToHom (image_eq hV h) :=
  Subsingleton.elim _ _

/-- For `V ⊆ V₀`, restriction `Γ(Y, V) → Γ(V₀, V₀ ∩ V)` is an isomorphism. -/
theorem isIso_appLE {V : Y.Opens} (hV : V ≤ V₀) {V' : V₀.toScheme.Opens}
    (h : V₀.ι ⁻¹ᵁ V = V') : IsIso (V₀.ι.appLE V V' h.ge) := by
  rw [appLE_eq_map_comp_appIso h.ge, homOfLE_image_eq hV h, eqToHom_op, eqToHom_map]
  infer_instance

/-- `V₀ ∩ V` lies over `U` when `V` does. -/
theorem preimage_le (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (hVU : V ≤ f ⁻¹ᵁ U)
    {V' : V₀.toScheme.Opens} (h : V₀.ι ⁻¹ᵁ V = V') : V' ≤ (V₀.ι ≫ f) ⁻¹ᵁ U :=
  h.ge.trans (Scheme.Hom.preimage_mono _ hVU)

/-- The identification `Γ(Y, V) ≅ Γ(V₀, V₀ ∩ V)` for `V ⊆ V₀`, as algebras over `Γ(X, U)`. -/
def ringEquiv (f : Y ⟶ X) (U : X.Opens) {V : Y.Opens} (hVU : V ≤ f ⁻¹ᵁ U) (hV : V ≤ V₀)
    {V' : V₀.toScheme.Opens} (h : V₀.ι ⁻¹ᵁ V = V') :
    letI : Algebra Γ(X, U) Γ(Y, V) := (f.appLE U V hVU).hom.toAlgebra
    letI : Algebra Γ(X, U) Γ(V₀, V') := ((V₀.ι ≫ f).appLE U V' (preimage_le f hVU h)).hom.toAlgebra
    Γ(Y, V) ≃ₐ[Γ(X, U)] Γ(V₀, V') :=
  letI : Algebra Γ(X, U) Γ(Y, V) := (f.appLE U V hVU).hom.toAlgebra
  letI : Algebra Γ(X, U) Γ(V₀, V') := ((V₀.ι ≫ f).appLE U V' (preimage_le f hVU h)).hom.toAlgebra
  haveI := isIso_appLE hV h
  AlgEquiv.ofBijective
    { toRingHom := (V₀.ι.appLE V V' h.ge).hom
      commutes' := fun a => by
        change (f.appLE U V hVU ≫ V₀.ι.appLE V V' h.ge).hom a = _
        rw [Scheme.Hom.appLE_comp_appLE]
        rfl }
    (ConcreteCategory.bijective_of_isIso (V₀.ι.appLE V V' h.ge))

/-- The value of `ringEquiv`. -/
theorem ringEquiv_apply (f : Y ⟶ X) (U : X.Opens) {V : Y.Opens} (hVU : V ≤ f ⁻¹ᵁ U)
    (hV : V ≤ V₀) {V' : V₀.toScheme.Opens} (h : V₀.ι ⁻¹ᵁ V = V') (b : Γ(Y, V)) :
    ringEquiv f U hVU hV h b = (V₀.ι.appLE V V' h.ge).hom b :=
  rfl

/-- `ringEquiv` commutes with restriction. -/
theorem ringEquiv_map (f : Y ⟶ X) (U : X.Opens) {V W : Y.Opens} (hWV : W ≤ V)
    (hVU : V ≤ f ⁻¹ᵁ U) (hWU : W ≤ f ⁻¹ᵁ U) (hV : V ≤ V₀) (hW0 : W ≤ V₀)
    {V' W' : V₀.toScheme.Opens} (h : V₀.ι ⁻¹ᵁ V = V') (hW : V₀.ι ⁻¹ᵁ W = W') (hW'V' : W' ≤ V')
    (b : Γ(Y, V)) :
    ringEquiv f U hWU hW0 hW ((Y.presheaf.map (homOfLE hWV).op).hom b) =
      (V₀.toScheme.presheaf.map (homOfLE hW'V').op).hom (ringEquiv f U hVU hV h b) := by
  rw [ringEquiv_apply, ringEquiv_apply, ← RingHom.comp_apply, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

/-- For `V ⊆ V₀`, restriction `Γ(M, V) → Γ(N, V₀ ∩ V)` along `N ≅ M|_{V₀}` is bijective. -/
theorem bijective_chartRestrict (M : Y.Modules) {N : V₀.toScheme.Modules}
    (e : N ≅ M.restrict V₀.ι) {V : Y.Opens} (hV : V ≤ V₀) {V' : V₀.toScheme.Opens}
    (h : V₀.ι ⁻¹ᵁ V = V') : Function.Bijective (chartRestrict M e h.ge) := by
  have h3 : Function.Bijective (M.presheaf.map (homOfLE (image_le_of_le_preimage h.ge)).op) := by
    rw [homOfLE_image_eq hV h, eqToHom_op, eqToHom_map]
    exact ConcreteCategory.bijective_of_isIso _
  exact ((ConcreteCategory.bijective_of_isIso (e.inv.app V')).comp
    (ConcreteCategory.bijective_of_isIso (M.restrictAppIso V₀.ι V').inv)).comp h3

/-- The trace on `V₀` of a principal open of `V` is the principal open of the restricted
function. -/
theorem preimage_basicOpen_eq {V : Y.Opens} {V' : V₀.toScheme.Opens} (h : V₀.ι ⁻¹ᵁ V = V')
    (g : Γ(Y, V)) :
    V₀.ι ⁻¹ᵁ Y.basicOpen g = V₀.toScheme.basicOpen ((V₀.ι.appLE V V' h.ge).hom g) := by
  subst h
  rw [Scheme.preimage_basicOpen, Scheme.Hom.app_eq_appLE]

variable (f : Y ⟶ X) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyQuasiFinite f]
  (V₀ : Y.Opens) (D : RelativeDualizingModuleData (V₀.ι ≫ f)) {N : Y.Modules}
  (e : D.sheaf ≅ N.restrict V₀.ι)

/-- The affine identification of `N` on a chart of `f` inside `V₀`, read off from chart data of
`V₀ → X` on `D.sheaf ≅ N|_{V₀}`. -/
def localEquiv (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (hV : V.1 ≤ V₀)
    (V' : V₀.toScheme.affineOpens) (h : V₀.ι ⁻¹ᵁ V.1 = V'.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
      Γ(N, V.1) ≃ₗ[Γ(Y, V.1)] dualizingModule F :=
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  letI : Algebra Γ(X, U.1) Γ(V₀, V'.1) :=
    ((V₀.ι ≫ f).appLE U V' (preimage_le f hVU h)).hom.toAlgebra
  fun F =>
    let σ := ringEquiv f U.1 hVU hV h
    let RE := AddEquiv.ofBijective (dualizingModule.retargetDualizingMap F σ)
      (dualizingModule.retargetDualizingMap_bijective F σ)
    let L := D.localEquiv U V' (preimage_le f hVU h) (dualizingModule.retargetFactorization F σ)
    LinearEquiv.ofBijective
      { toFun := fun s => RE.symm (L (chartRestrict N e h.ge s))
        map_add' := fun s t => by simp only [map_add]
        map_smul' := fun b s => by
          change RE.symm (L (chartRestrict N e h.ge (b • s))) =
            b • RE.symm (L (chartRestrict N e h.ge s))
          rw [chartRestrict_smul, ← ringEquiv_apply f U.1 hVU hV h, LinearEquiv.map_smul,
            AddEquiv.symm_apply_eq]
          change _ = dualizingModule.retargetDualizingMap F σ (b • RE.symm _)
          rw [dualizingModule.retargetDualizingMap_smul]
          exact congrArg (σ b • ·) (RE.apply_symm_apply _).symm }
      (RE.symm.bijective.comp (L.bijective.comp (bijective_chartRestrict N e hV h)))

/-- `localEquiv` followed by transport is the chart identification of `V₀ → X`. -/
theorem localEquiv_apply (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (hV : V.1 ≤ V₀) (V' : V₀.toScheme.affineOpens) (h : V₀.ι ⁻¹ᵁ V.1 = V'.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(V₀, V'.1) :=
      ((V₀.ι ≫ f).appLE U V' (preimage_le f hVU h)).hom.toAlgebra
    ∀ (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1)) (s : Γ(N, V.1)),
      dualizingModule.retargetDualizingMap F (ringEquiv f U.1 hVU hV h)
          (localEquiv f V₀ D e U V hVU hV V' h F s) =
        D.localEquiv U V' (preimage_le f hVU h)
          (dualizingModule.retargetFactorization F (ringEquiv f U.1 hVU hV h))
          (chartRestrict N e h.ge s) := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(V₀, V'.1) :=
    ((V₀.ι ≫ f).appLE U V' (preimage_le f hVU h)).hom.toAlgebra
  intro F s
  exact (AddEquiv.ofBijective _ (dualizingModule.retargetDualizingMap_bijective F
    (ringEquiv f U.1 hVU hV h))).apply_symm_apply _

/-- `localEquiv` depends on the chart data of `V₀ → X` only through its affine identifications
on the charts used. -/
theorem localEquiv_congr (D D' : RelativeDualizingModuleData (V₀.ι ≫ f))
    (e : D.sheaf ≅ N.restrict V₀.ι) (e' : D'.sheaf ≅ N.restrict V₀.ι) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (hV : V.1 ≤ V₀) (V' : V₀.toScheme.affineOpens)
    (h : V₀.ι ⁻¹ᵁ V.1 = V'.1)
    (hL : letI : Algebra Γ(X, U.1) Γ(V₀, V'.1) :=
        ((V₀.ι ≫ f).appLE U V' (preimage_le f hVU h)).hom.toAlgebra
      ∀ (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(V₀, V'.1)) (x : Γ(N, V.1)),
        D.localEquiv U V' (preimage_le f hVU h) F (chartRestrict N e h.ge x) =
          D'.localEquiv U V' (preimage_le f hVU h) F (chartRestrict N e' h.ge x)) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
      localEquiv f V₀ D e U V hVU hV V' h F = localEquiv f V₀ D' e' U V hVU hV V' h F := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(V₀, V'.1) :=
    ((V₀.ι ≫ f).appLE U V' (preimage_le f hVU h)).hom.toAlgebra
  intro F
  refine LinearEquiv.ext fun x => ?_
  apply (dualizingModule.retargetDualizingMap_bijective F (ringEquiv f U.1 hVU hV h)).1
  rw [localEquiv_apply, localEquiv_apply]
  exact hL _ x

/-- `localEquiv` is independent of the factorization (Tag 0BT1). -/
theorem localEquiv_natural (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (hV : V.1 ≤ V₀) (V' : V₀.toScheme.affineOpens) (h : V₀.ι ⁻¹ᵁ V.1 = V'.1) :
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    ∀ (F G : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1)) (s : Γ(N, V.1)),
      localEquiv f V₀ D e U V hVU hV V' h G s =
        dualizingModuleEquiv F G (localEquiv f V₀ D e U V hVU hV V' h F s) := by
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(V₀, V'.1) :=
    ((V₀.ι ≫ f).appLE U V' (preimage_le f hVU h)).hom.toAlgebra
  intro F G s
  apply (dualizingModule.retargetDualizingMap_bijective G (ringEquiv f U.1 hVU hV h)).1
  rw [localEquiv_apply, dualizingModule.retargetDualizingMap_naturality, localEquiv_apply,
    D.localEquiv_natural U V' (preimage_le f hVU h)]

/-- `localEquiv` is compatible with localizing the base chart (Tag 0BT2 part (1)). -/
theorem localEquiv_baseBasicOpen (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (a : Γ(X, U.1)) (hVa : V.1 ≤ f ⁻¹ᵁ (X.basicOpen a))
    (hV : V.1 ≤ V₀) (V' : V₀.toScheme.affineOpens) (h : V₀.ι ⁻¹ᵁ V.1 = V'.1) :
    let Ua : X.affineOpens := ⟨X.basicOpen a, U.2.basicOpen a⟩
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : Algebra Γ(X, Ua.1) Γ(Y, V.1) := (f.appLE Ua V hVa).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(X, Ua.1) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom.toAlgebra
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    letI : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
    letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
      (RingHom.quasiFinite_algebraMap).mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
    letI : IsLocalization.Away a Γ(X, Ua.1) := U.2.isLocalization_basicOpen a
    letI : IsScalarTower Γ(X, U.1) Γ(X, Ua.1) Γ(Y, V.1) :=
      IsScalarTower.of_algebraMap_eq' (by
        change (f.appLE U V hVU).hom =
          ((f.appLE Ua V hVa).hom).comp (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom
        rw [← CommRingCat.hom_comp, f.map_appLE hVa (homOfLE (X.basicOpen_le a)).op])
    ∀ (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
      (G : FiniteOpenFactorization.{u, u, u} Γ(X, Ua.1) Γ(Y, V.1)) (s : Γ(N, V.1)),
      localEquiv f V₀ D e Ua V hVa hV V' h G s =
        dualizingModule_equiv_of_isLocalization_away a F G
          (localEquiv f V₀ D e U V hVU hV V' h F s) := by
  intro Ua F G s
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra Γ(X, Ua.1) Γ(Y, V.1) := (f.appLE Ua V hVa).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(X, Ua.1) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsLocalization.Away a Γ(X, Ua.1) := U.2.isLocalization_basicOpen a
  let : Algebra Γ(X, U.1) Γ(V₀, V'.1) :=
    ((V₀.ι ≫ f).appLE U V' (preimage_le f hVU h)).hom.toAlgebra
  let : Algebra Γ(X, Ua.1) Γ(V₀, V'.1) :=
    ((V₀.ι ≫ f).appLE Ua V' (preimage_le f hVa h)).hom.toAlgebra
  let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    (RingHom.quasiFinite_algebraMap).mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  let : IsScalarTower Γ(X, U.1) Γ(X, Ua.1) Γ(Y, V.1) :=
    IsScalarTower.of_algebraMap_eq' (by
      change (f.appLE U V hVU).hom =
        ((f.appLE Ua V hVa).hom).comp (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom
      rw [← CommRingCat.hom_comp, f.map_appLE hVa (homOfLE (X.basicOpen_le a)).op])
  let : IsNoetherianRing Γ(V₀, V'.1) := IsLocallyNoetherian.component_noetherian V'
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(V₀, V'.1) :=
    (RingHom.quasiFinite_algebraMap).mp
      (LocallyQuasiFinite.quasiFinite_appLE U.2 V'.2 (preimage_le f hVU h))
  let : IsScalarTower Γ(X, U.1) Γ(X, Ua.1) Γ(V₀, V'.1) :=
    IsScalarTower.of_algebraMap_eq' (by
      change ((V₀.ι ≫ f).appLE U V' (preimage_le f hVU h)).hom =
        (((V₀.ι ≫ f).appLE Ua V' (preimage_le f hVa h)).hom).comp
          (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom
      rw [← CommRingCat.hom_comp, (V₀.ι ≫ f).map_appLE (preimage_le f hVa h)
        (homOfLE (X.basicOpen_le a)).op])
  have hD := D.localEquiv_baseBasicOpen U V' (preimage_le f hVU h) a (preimage_le f hVa h)
    (dualizingModule.retargetFactorization F (ringEquiv f U.1 hVU hV h))
    (dualizingModule.retargetFactorization G (ringEquiv f Ua.1 hVa hV h))
    (chartRestrict N e h.ge s)
  apply (dualizingModule.retargetDualizingMap_bijective G (ringEquiv f Ua.1 hVa hV h)).1
  rw [localEquiv_apply]
  refine hD.trans ?_
  rw [retargetDualizingMap_dualizingModule_equiv_of_isLocalization_away a F G
    (ringEquiv f U.1 hVU hV h) (ringEquiv f Ua.1 hVa hV h) (fun _ => rfl), localEquiv_apply]

/-- `localEquiv` is compatible with localizing the source chart (Tag 0BT2 part (2)). -/
theorem localEquiv_basicOpen (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (g : Γ(Y, V.1)) (hV : V.1 ≤ V₀) (V' : V₀.toScheme.affineOpens) (h : V₀.ι ⁻¹ᵁ V.1 = V'.1) :
    let W : Y.affineOpens := ⟨Y.basicOpen g, V.2.basicOpen g⟩
    let hWU : W.1 ≤ f ⁻¹ᵁ U.1 := (Y.basicOpen_le g).trans hVU
    let W' : V₀.toScheme.affineOpens :=
      ⟨V₀.toScheme.basicOpen ((V₀.ι.appLE V V' h.ge).hom g), V'.2.basicOpen _⟩
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(Y, W.1) := (f.appLE U W hWU).hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Y, W.1) :=
      (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom.toAlgebra
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    letI : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
    letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
      (RingHom.quasiFinite_algebraMap).mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
    letI : IsLocalization.Away g Γ(Y, W.1) := V.2.isLocalization_basicOpen g
    letI : IsScalarTower Γ(X, U.1) Γ(Y, V.1) Γ(Y, W.1) :=
      IsScalarTower.of_algebraMap_eq' (by
        change (f.appLE U W hWU).hom =
          ((Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom).comp (f.appLE U V hVU).hom
        rw [← CommRingCat.hom_comp, ← f.appLE_map hVU (homOfLE (Y.basicOpen_le g)).op])
    ∀ (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
      (G : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, W.1)),
      letI : Module Γ(Y, V.1) (dualizingModule G) :=
        Module.compHom (dualizingModule G) (algebraMap Γ(Y, V.1) Γ(Y, W.1))
      letI : IsScalarTower Γ(Y, V.1) Γ(Y, W.1) (dualizingModule G) :=
        IsScalarTower.of_compHom Γ(Y, V.1) Γ(Y, W.1) _
      ∃ (r : dualizingModule F →ₗ[Γ(Y, V.1)] dualizingModule G)
        (hr : IsLocalizedModule (Submonoid.powers g) r),
        (∀ s : Γ(N, V.1),
            localEquiv f V₀ D e U W hWU ((Y.basicOpen_le g).trans hV) W'
                (preimage_basicOpen_eq h g) G ((restrictₗ N (Y.basicOpen_le g)) s) =
              r (localEquiv f V₀ D e U V hVU hV V' h F s)) ∧
          (∀ m : dualizingModule G,
            localizedModule_dualizingModule_equiv g F G r hr m = m) := by
  intro W hWU W' F G
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(Y, W.1) := (f.appLE U W hWU).hom.toAlgebra
  let : Algebra Γ(Y, V.1) Γ(Y, W.1) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    (RingHom.quasiFinite_algebraMap).mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  let : IsLocalization.Away g Γ(Y, W.1) := V.2.isLocalization_basicOpen g
  let : IsScalarTower Γ(X, U.1) Γ(Y, V.1) Γ(Y, W.1) :=
    IsScalarTower.of_algebraMap_eq' (by
      change (f.appLE U W hWU).hom =
        ((Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom).comp (f.appLE U V hVU).hom
      rw [← CommRingCat.hom_comp, ← f.appLE_map hVU (homOfLE (Y.basicOpen_le g)).op])
  let : Module Γ(Y, V.1) (dualizingModule G) :=
    Module.compHom (dualizingModule G) (algebraMap Γ(Y, V.1) Γ(Y, W.1))
  let : IsScalarTower Γ(Y, V.1) Γ(Y, W.1) (dualizingModule G) :=
    IsScalarTower.of_compHom Γ(Y, V.1) Γ(Y, W.1) _
  have hW0 : W.1 ≤ V₀ := (Y.basicOpen_le g).trans hV
  have hW := preimage_basicOpen_eq h g
  let : Algebra Γ(X, U.1) Γ(V₀, V'.1) :=
    ((V₀.ι ≫ f).appLE U V' (preimage_le f hVU h)).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(V₀, W'.1) :=
    ((V₀.ι ≫ f).appLE U W' (preimage_le f hWU hW)).hom.toAlgebra
  let : Algebra Γ(V₀, V'.1) Γ(V₀, W'.1) :=
    (V₀.toScheme.presheaf.map (homOfLE (V₀.toScheme.basicOpen_le _)).op).hom.toAlgebra
  let : IsLocalization.Away ((V₀.ι.appLE V V' h.ge).hom g) Γ(V₀, W'.1) :=
    V'.2.isLocalization_basicOpen _
  let : IsScalarTower Γ(X, U.1) Γ(V₀, V'.1) Γ(V₀, W'.1) :=
    IsScalarTower.of_algebraMap_eq' (by
      change ((V₀.ι ≫ f).appLE U W' (preimage_le f hWU hW)).hom =
        ((V₀.toScheme.presheaf.map (homOfLE (V₀.toScheme.basicOpen_le _)).op).hom).comp
          ((V₀.ι ≫ f).appLE U V' (preimage_le f hVU h)).hom
      rw [← CommRingCat.hom_comp, ← (V₀.ι ≫ f).appLE_map (preimage_le f hVU h)
        (homOfLE (V₀.toScheme.basicOpen_le _)).op])
  obtain ⟨r, hr, hid⟩ := exists_localizedDualizingModuleMap_eq_id' g F G
  refine ⟨r, hr, fun s => ?_, hid⟩
  rw [localizationMap_eq_of_localizedModule_dualizingModule_equiv_eq_id g F G r hr hid]
  apply (dualizingModule.retargetDualizingMap_bijective G (ringEquiv f U.1 hWU hW0 hW)).1
  refine (localEquiv_apply f V₀ D e U W hWU hW0 W' hW G _).trans ?_
  have hc : chartRestrict N e hW.ge ((restrictₗ N (Y.basicOpen_le g)) s) =
      (restrictₗ D.sheaf (V₀.toScheme.basicOpen_le _)) (chartRestrict N e h.ge s) := by
    change chartRestrict N e hW.ge (N.presheaf.map (homOfLE (Y.basicOpen_le g)).op s) =
      D.sheaf.presheaf.map (homOfLE (V₀.toScheme.basicOpen_le _)).op (chartRestrict N e h.ge s)
    rw [chartRestrict_restrict_target, chartRestrict_restrict_source]
  rw [hc]
  let : Module Γ(V₀, V'.1) (dualizingModule
      (dualizingModule.retargetFactorization G (ringEquiv f U.1 hWU hW0 hW))) :=
    Module.compHom _ (algebraMap Γ(V₀, V'.1) Γ(V₀, W'.1))
  let : IsScalarTower Γ(V₀, V'.1) Γ(V₀, W'.1) (dualizingModule
      (dualizingModule.retargetFactorization G (ringEquiv f U.1 hWU hW0 hW))) :=
    IsScalarTower.of_compHom _ _ _
  let : IsNoetherianRing Γ(V₀, V'.1) := IsLocallyNoetherian.component_noetherian V'
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(V₀, V'.1) :=
    (RingHom.quasiFinite_algebraMap).mp
      (LocallyQuasiFinite.quasiFinite_appLE U.2 V'.2 (preimage_le f hVU h))
  obtain ⟨r', hr', hD1, hD2⟩ := D.localEquiv_basicOpen U V' (preimage_le f hVU h)
    ((V₀.ι.appLE V V' h.ge).hom g)
    (dualizingModule.retargetFactorization F (ringEquiv f U.1 hVU hV h))
    (dualizingModule.retargetFactorization G (ringEquiv f U.1 hWU hW0 hW))
  refine (hD1 _).trans ?_
  refine (localizationMap_eq_of_localizedModule_dualizingModule_equiv_eq_id _ _ _ r' hr' hD2
    _).trans ?_
  rw [← localEquiv_apply f V₀ D e U V hVU hV V' h F s]
  have : IsLocalization.Away (ringEquiv f U.1 hVU hV h g) Γ(V₀, W'.1) :=
    (inferInstance : IsLocalization.Away ((V₀.ι.appLE V V' h.ge).hom g) Γ(V₀, W'.1))
  refine (retargetDualizingMap_dualizingModuleEquiv_locFact g (ringEquiv f U.1 hVU hV h)
    (ringEquiv f U.1 hWU hW0 hW) (fun b => ?_) F G _).symm
  exact ringEquiv_map f U.1 (Y.basicOpen_le g) hVU hWU hV hW0 h hW
    (V₀.toScheme.basicOpen_le _) b

section FiniteTrace

attribute [local instance] algebraDualModule

variable {X Y P : Scheme.{u}} (f : Y ⟶ X) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  [LocallyQuasiFinite f] {V₀ : Y.Opens} {i : V₀.toScheme ⟶ P} [IsOpenImmersion i]
  {π : P ⟶ X} [IsFinite π] (hig : i ≫ π = V₀.ι ≫ f) (M : P.Modules) [M.IsQuasicoherent]
  (t : (Scheme.Modules.pushforward π).obj M ⟶ SheafOfModules.unit X.ringCatSheaf)
  (hbij : ∀ U : X.affineOpens, Function.Bijective (traceDual π t U.1))
  {N : Y.Modules} (ε : N.restrict V₀.ι ≅ M.restrict i)

/-- On chart data given by a finite trace, `localEquiv` sends the restriction of a section `s`
of `M` to `(t_s ⊗ 1)` read through the comparison of Tag 0BT1. -/
theorem localEquiv_ofFiniteTrace (U : X.affineOpens) (T : Y.affineOpens)
    (hTU : T.1 ≤ f ⁻¹ᵁ U.1) (hT : T.1 ≤ V₀) (T' : V₀.toScheme.affineOpens)
    (h : V₀.ι ⁻¹ᵁ T.1 = T'.1) (s : Γ(M, π ⁻¹ᵁ U.1)) (x : Γ(N, T.1))
    (hx : chartRestrict N (Iso.refl _) h.ge x =
      chartRestrict M ε (le_preimage_preimage hig (preimage_le f hTU h)) s) :
    letI : Algebra Γ(X, U.1) Γ(Y, T.1) := (f.appLE U T hTU).hom.toAlgebra
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    letI : Algebra Γ(X, U.1) Γ(V₀, T'.1) :=
      ((V₀.ι ≫ f).appLE U T' (preimage_le f hTU h)).hom.toAlgebra
    ∀ G : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, T.1),
      localEquiv f V₀ (RelativeDualizingModuleData.ofFiniteTrace hig M t hbij ε) (Iso.refl _)
          U T hTU hT T' h G x =
        dualizingModuleEquiv (dualizingModule.retargetFactorization
            (chartFactorization hig U T' (preimage_le f hTU h)) (ringEquiv f U.1 hTU hT h).symm) G
          (dualizingModule.tmul (dualizingModule.retargetFactorization
            (chartFactorization hig U T' (preimage_le f hTU h)) (ringEquiv f U.1 hTU hT h).symm)
            (traceDual π t U.1 s) 1) := by
  let : Algebra Γ(X, U.1) Γ(Y, T.1) := (f.appLE U T hTU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : Algebra Γ(X, U.1) Γ(V₀, T'.1) :=
    ((V₀.ι ≫ f).appLE U T' (preimage_le f hTU h)).hom.toAlgebra
  intro G
  apply (dualizingModule.retargetDualizingMap_bijective G (ringEquiv f U.1 hTU hT h)).1
  refine (localEquiv_apply f V₀ _ _ U T hTU hT T' h G x).trans ?_
  have hx' : chartRestrict (e := Iso.refl
      (RelativeDualizingModuleData.ofFiniteTrace hig M t hbij ε).sheaf) N h.ge x =
      chartRestrict M ε (le_preimage_preimage hig (preimage_le f hTU h)) s := hx
  rw [hx', RelativeDualizingModuleData.ofFiniteTrace_localEquiv,
    dualizingModule.retargetDualizingMap_naturality]
  refine Eq.trans ?_ (congrArg (dualizingModuleEquiv _ _)
    ((dualizingModule.retargetDualizingMap_tmul _ _ _ _).trans
      (congrArg (dualizingModule.tmul _ _) (map_one (ringEquiv f U.1 hTU hT h))))).symm
  rw [← dualizingModuleEquiv_trans _ (dualizingModule.retargetFactorization
      (dualizingModule.retargetFactorization (chartFactorization hig U T' (preimage_le f hTU h))
        (ringEquiv f U.1 hTU hT h).symm) (ringEquiv f U.1 hTU hT h)), LinearEquiv.trans_apply]
  exact congrArg (dualizingModuleEquiv _ _) ((comparison_restrict_of_equiv
    (dualizingModule.retargetFactorization (dualizingModule.retargetFactorization
      (chartFactorization hig U T' (preimage_le f hTU h)) (ringEquiv f U.1 hTU hT h).symm)
      (ringEquiv f U.1 hTU hT h))
    (chartFactorization hig U T' (preimage_le f hTU h)) AlgEquiv.refl
    (fun c => ((ringEquiv f U.1 hTU hT h).apply_symm_apply _).symm) _ _).trans rfl)

section Restrict

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyQuasiFinite f] in
/-- `appLE` of equal morphisms. -/
theorem appLE_congr_apply {A B : Scheme.{u}} {a b : A ⟶ B} (hab : a = b) (Q : B.Opens)
    (R : A.Opens) (e : R ≤ a ⁻¹ᵁ Q) (e' : R ≤ b ⁻¹ᵁ Q) (c : Γ(B, Q)) :
    (a.appLE Q R e).hom c = (b.appLE Q R e').hom c := by
  subst hab
  rfl

variable {W₀ : Y.Opens} (hW : W₀ ≤ V₀)

include hig in
omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyQuasiFinite f] [IsFinite π]
  [IsOpenImmersion i] in
/-- The restriction to `W₀` of a factorization of `V₀ → X`. -/
theorem restrict_fac : (Y.homOfLE hW ≫ i) ≫ π = W₀.ι ≫ f := by
  rw [Category.assoc, hig, ← Category.assoc, Scheme.homOfLE_ι]

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyQuasiFinite f] in
/-- The chart of `W₀` lies over the chart of `V₀`. -/
theorem preimage_homOfLE {T : Y.Opens} {T'V : V₀.toScheme.Opens} {T'W : W₀.toScheme.Opens}
    (hV : V₀.ι ⁻¹ᵁ T = T'V) (hWT : W₀.ι ⁻¹ᵁ T = T'W) : T'W ≤ Y.homOfLE hW ⁻¹ᵁ T'V := by
  rw [← hV, ← hWT, ← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι]

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyQuasiFinite f] in
/-- `ringEquiv` for `W₀ ⊆ V₀` is `ringEquiv` for `V₀` followed by restriction. -/
theorem ringEquiv_restrict (U : X.Opens) {T : Y.Opens} (hTU : T ≤ f ⁻¹ᵁ U) (hT : T ≤ W₀)
    {T'V : V₀.toScheme.Opens} {T'W : W₀.toScheme.Opens}
    (hV : V₀.ι ⁻¹ᵁ T = T'V) (hWT : W₀.ι ⁻¹ᵁ T = T'W) (b : Γ(Y, T)) :
    ringEquiv f U hTU hT hWT b = ((Y.homOfLE hW).appLE T'V T'W (preimage_homOfLE hW hV hWT)).hom
      (ringEquiv f U hTU (hT.trans hW) hV b) := by
  rw [ringEquiv_apply, ringEquiv_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp,
    Scheme.Hom.appLE_comp_appLE]
  exact appLE_congr_apply (Scheme.homOfLE_ι Y hW).symm _ _ _ _ b

/-- The restriction to `W₀ ⊆ V₀` of an identification `N|_{V₀} ≅ M|_{V₀}`. -/
def restrictIso : N.restrict W₀.ι ≅ M.restrict (Y.homOfLE hW ≫ i) :=
  (Scheme.Modules.restrictFunctorCongr (Y.homOfLE_ι hW)).symm.app N ≪≫
    (Scheme.Modules.restrictFunctorComp (Y.homOfLE hW) V₀.ι).app N ≪≫
    (Scheme.Modules.restrictFunctor (Y.homOfLE hW)).mapIso ε ≪≫
    ((Scheme.Modules.restrictFunctorComp (Y.homOfLE hW) i).app M).symm

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyQuasiFinite f] [IsFinite π]
  [M.IsQuasicoherent] in
/-- Restriction of sections through `restrictIso` is restriction through the original
identification. -/
theorem chartRestrict_restrictIso {Q : P.Opens} {T : Y.Opens} {T'V : V₀.toScheme.Opens}
    {T'W : W₀.toScheme.Opens} (hV : V₀.ι ⁻¹ᵁ T = T'V) (hWT : W₀.ι ⁻¹ᵁ T = T'W)
    (hQ : T'V ≤ i ⁻¹ᵁ Q) (hQ' : T'W ≤ (Y.homOfLE hW ≫ i) ⁻¹ᵁ Q) (s : Γ(M, Q)) (x : Γ(N, T))
    (hx : chartRestrict N (Iso.refl _) hV.ge x = chartRestrict M ε hQ s) :
    chartRestrict N (Iso.refl _) hWT.ge x = chartRestrict M (restrictIso M ε hW) hQ' s := by
  have hA : Y.homOfLE hW ''ᵁ T'W ≤ T'V := image_le_of_le_preimage (preimage_homOfLE hW hV hWT)
  have h1 := congrArg ((N.restrict V₀.ι).presheaf.map (homOfLE hA).op) hx
  rw [chartRestrict_restrict_source, chartRestrict_restrict_source, chartRestrict_apply,
    chartRestrict_apply] at h1
  rw [chartRestrict_apply, chartRestrict_apply]
  simp only [restrictIso, Iso.trans_inv, Iso.symm_inv, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_inv, Scheme.Modules.Hom.comp_app, Iso.refl_inv, Scheme.Modules.Hom.id_app,
    ConcreteCategory.id_apply, Scheme.Modules.restrictFunctorComp_hom_app_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app,
    Scheme.Modules.restrictAppIso] at h1 ⊢
  change N.presheaf.map _ x = ε.inv.app _ (M.presheaf.map _ s) at h1
  change N.presheaf.map _ x = N.presheaf.map _ (N.presheaf.map _
    (ε.inv.app (Y.homOfLE hW ''ᵁ T'W) (M.presheaf.map _ (M.presheaf.map _ s))))
  rw [Stacks.Modules.res_comp M _ _ (homOfLE (image_le_of_le_preimage (hA.trans hQ))), ← h1]
  simp only [← ConcreteCategory.comp_apply]
  have key : ∀ {A B C D : Y.Opensᵒᵖ} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (d : A ⟶ D),
      (N.presheaf.map a ≫ N.presheaf.map b) ≫ N.presheaf.map c = N.presheaf.map d := by
    intro A B C D a b c d
    rw [← Functor.map_comp, ← Functor.map_comp, Subsingleton.elim ((a ≫ b) ≫ c) d]
  exact (congrArg (fun φ : N.presheaf.obj _ ⟶ N.presheaf.obj _ => ConcreteCategory.hom φ x)
    (key _ _ _ _)).symm

variable {ε' : N.restrict W₀.ι ≅ M.restrict (Y.homOfLE hW ≫ i)}

/-- Two finite-trace data on `V₀` and `W₀ ⊆ V₀` with compatible identifications give the same
affine identifications on the charts inside `W₀`. -/
theorem localEquiv_ofFiniteTrace_restrict (U : X.affineOpens) (T : Y.affineOpens)
    (hTU : T.1 ≤ f ⁻¹ᵁ U.1) (hT : T.1 ≤ W₀) (T'V : V₀.toScheme.affineOpens)
    (hV : V₀.ι ⁻¹ᵁ T.1 = T'V.1) (T'W : W₀.toScheme.affineOpens) (hWT : W₀.ι ⁻¹ᵁ T.1 = T'W.1)
    (hε : ∀ (s : Γ(M, π ⁻¹ᵁ U.1)) (x : Γ(N, T.1)),
      chartRestrict N (Iso.refl _) hV.ge x =
          chartRestrict M ε (le_preimage_preimage hig (preimage_le f hTU hV)) s →
        chartRestrict N (Iso.refl _) hWT.ge x =
          chartRestrict M ε' (le_preimage_preimage (restrict_fac f hig hW)
            (preimage_le f hTU hWT)) s) :
    letI : Algebra Γ(X, U.1) Γ(Y, T.1) := (f.appLE U T hTU).hom.toAlgebra
    ∀ G : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, T.1),
      localEquiv f V₀ (RelativeDualizingModuleData.ofFiniteTrace hig M t hbij ε) (Iso.refl _)
          U T hTU (hT.trans hW) T'V hV G =
        localEquiv f W₀ (RelativeDualizingModuleData.ofFiniteTrace (restrict_fac f hig hW) M t
          hbij ε') (Iso.refl _) U T hTU hT T'W hWT G := by
  let : Algebra Γ(X, U.1) Γ(Y, T.1) := (f.appLE U T hTU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : Algebra Γ(X, U.1) Γ(V₀, T'V.1) :=
    ((V₀.ι ≫ f).appLE U T'V (preimage_le f hTU hV)).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(W₀, T'W.1) :=
    ((W₀.ι ≫ f).appLE U T'W (preimage_le f hTU hWT)).hom.toAlgebra
  intro G
  refine LinearEquiv.ext fun x => ?_
  let ρ := AddEquiv.ofBijective (chartRestrict N (Iso.refl (N.restrict V₀.ι)) hV.ge)
    (bijective_chartRestrict N (Iso.refl _) (hT.trans hW) hV)
  rw [← ρ.symm_apply_apply x]
  generalize ρ x = y
  obtain ⟨z, rfl⟩ := (chartEquiv hig M t hbij ε U T'V (preimage_le f hTU hV)).surjective y
  induction z using dualizingModule.induction_on with
  | zero => simp only [map_zero]
  | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul φ b =>
    rw [chartEquiv_tmul]
    set s₀ := (traceDualEquiv M t hbij U).symm φ
    set y₀ := chartRestrict M ε (le_preimage_preimage hig (preimage_le f hTU hV)) s₀
    have hρ : ∀ (c : Γ(Y, T.1)) (x : Γ(N, T.1)),
        ρ (c • x) = ringEquiv f U.1 hTU (hT.trans hW) hV c • ρ x := fun c x =>
      chartRestrict_smul N (Iso.refl _) hV.ge c x
    have hsmul : ρ.symm (b • y₀) = (ringEquiv f U.1 hTU (hT.trans hW) hV).symm b • ρ.symm y₀ := by
      apply ρ.injective
      rw [hρ, AlgEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    have hx₀ : chartRestrict N (Iso.refl _) hV.ge (ρ.symm y₀) =
        chartRestrict M ε (le_preimage_preimage hig (preimage_le f hTU hV)) s₀ :=
      ρ.apply_symm_apply y₀
    rw [hsmul, LinearEquiv.map_smul, LinearEquiv.map_smul,
      localEquiv_ofFiniteTrace f hig M t hbij ε U T hTU (hT.trans hW) T'V hV s₀ _ hx₀,
      localEquiv_ofFiniteTrace f (restrict_fac f hig hW) M t hbij ε' U T hTU hT T'W hWT s₀ _
        (hε s₀ _ hx₀), ← dualizingModuleEquiv_trans _ (dualizingModule.retargetFactorization
        (chartFactorization (restrict_fac f hig hW) U T'W (preimage_le f hTU hWT))
        (ringEquiv f U.1 hTU hT hWT).symm), LinearEquiv.trans_apply]
    refine congrArg _ (congrArg _ ((comparison_restrict_of_equiv
        (dualizingModule.retargetFactorization
        (chartFactorization (restrict_fac f hig hW) U T'W (preimage_le f hTU hWT))
        (ringEquiv f U.1 hTU hT hWT).symm) (dualizingModule.retargetFactorization
        (chartFactorization hig U T'V (preimage_le f hTU hV))
        (ringEquiv f U.1 hTU (hT.trans hW) hV).symm) AlgEquiv.refl
      (fun c => ?_) _ _).trans rfl))
    apply (ringEquiv f U.1 hTU hT hWT).injective
    change ringEquiv f U.1 hTU hT hWT ((ringEquiv f U.1 hTU (hT.trans hW) hV).symm
        ((i.appLE (π ⁻¹ᵁ U.1) T'V.1 (le_preimage_preimage hig (preimage_le f hTU hV))).hom c)) =
      ringEquiv f U.1 hTU hT hWT ((ringEquiv f U.1 hTU hT hWT).symm
        (((Y.homOfLE hW ≫ i).appLE (π ⁻¹ᵁ U.1) T'W.1 (le_preimage_preimage (restrict_fac f hig hW)
          (preimage_le f hTU hWT))).hom c))
    rw [AlgEquiv.apply_symm_apply, ringEquiv_restrict f hW U.1 hTU hT hV hWT,
      AlgEquiv.apply_symm_apply]
    exact congrArg (fun φ => (CommRingCat.Hom.hom φ) (show Γ(P, π ⁻¹ᵁ U.1) from c))
      (Scheme.Hom.appLE_comp_appLE (Y.homOfLE hW) i _ _ _ _ _)

/-- **Restricting a finite-trace datum to a smaller open.** The affine identifications of `N` on
the charts of `f` inside `W₀ ⊆ V₀` read off from a factorization `V₀ → P → X` agree with those
read off from its restriction `W₀ → V₀ → P → X`. -/
theorem localEquiv_ofFiniteTrace_restrictIso (U : X.affineOpens) (T : Y.affineOpens)
    (hTU : T.1 ≤ f ⁻¹ᵁ U.1) (hT : T.1 ≤ W₀) (T'V : V₀.toScheme.affineOpens)
    (hV : V₀.ι ⁻¹ᵁ T.1 = T'V.1) (T'W : W₀.toScheme.affineOpens) (hWT : W₀.ι ⁻¹ᵁ T.1 = T'W.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, T.1) := (f.appLE U T hTU).hom.toAlgebra
    ∀ G : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, T.1),
      localEquiv f V₀ (RelativeDualizingModuleData.ofFiniteTrace hig M t hbij ε) (Iso.refl _)
          U T hTU (hT.trans hW) T'V hV G =
        localEquiv f W₀ (RelativeDualizingModuleData.ofFiniteTrace (restrict_fac f hig hW) M t
          hbij (restrictIso M ε hW)) (Iso.refl _) U T hTU hT T'W hWT G :=
  localEquiv_ofFiniteTrace_restrict f hig M t hbij ε hW U T hTU hT T'V hV T'W hWT
    (fun s x hx => chartRestrict_restrictIso M ε hW hV hWT _ _ s x hx)

end Restrict

end FiniteTrace

end OpenChart

end Stacks.Discriminant
