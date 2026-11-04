module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PointClassNonzeroLowerShriek
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopLowerShriekTraceExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIso

/-!
# The class of a point through a family of curves, given a class on the fibre

Let `g : U → S` and `q : S → Spec k` be separated of finite type with compactifications, the
fibres of the compactification of `g` of dimension at most one, `Λ = ℤ/ℓ`, and let
`ν : R²g_! g⁻¹ ≅ 𝟭` identify the top direct image (`Stacks.EtaleCohomology.lowerShriekTopTrace`
is the induced top-degree trace `t_X : Rg_!(g⁻¹ X) ⟶ X[-2]`). Let `p : P → U` and `i' : P → S` be
points, `X = i'_* Λ_P`. Suppose:

* the class of `i'` in `H^{2e}_c(S)` is nonzero;
* some `δ ∈ Ext²_U(p_* Λ_P, g⁻¹ X)` has `t_X ∘ Rg_!(δ) : Rg_!(p_* Λ_P) ⟶ X` split by some
  `σ : X ⟶ Rg_!(p_* Λ_P)` (on the fibre curve `g⁻¹(s)` this is the class of the point `p` in
  `H²_c`, which is a unit multiple of the top-degree trace).

Then the class of `p` in `H^{2e+2}_c(U)`, for any compactification of `g ≫ q`, is nonzero
(`Stacks.EtaleCohomology.pointClassNonzeroAt_of_fibration_of_section`). Indeed, for the class
`β ∈ Ext^{2e}_S(X, Λ_S)` of `i'` and `γ = g⁻¹ β ∘ δ ∈ Ext^{2e+2}_U(p_* Λ_P, Λ_U)`, the Leray
isomorphism `R(g ≫ q)_! ≅ Rq_! ∘ Rg_!` (Tag 0F7J), applied in degree zero to `γ` read as a morphism
`(p_* Λ_P)[0] ⟶ Λ_U[0][2e + 2]`, carries `R(g ≫ q)_!(γ)` to `Rq_!(Rg_!(γ))`, and the top-degree
trace commutes with `g⁻¹ β` (`Stacks.EtaleCohomology.map_comp_lowerShriekTopTrace`):
`t ∘ Rg_!(γ) = β ∘ t_X ∘ Rg_!(δ)`, so `Rq_!(t ∘ Rg_!(γ) ∘ σ) = Rq_!(β)`. No compatibility of the
Leray isomorphism with shifts is used.

This is the step of the class of a point through an elementary fibration, in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The statements consume `Rf_!`, defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main results

* `Stacks.EtaleCohomology.pointClassNonzeroAt_of_fibration_of_section`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

open ExtensionTorsor

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

-- `Stacks.EtaleCohomology.PointClassNonzeroAt` reads `ZMod ℓ` as a ring through `ZMod.commRing`.
attribute [-instance] ZMod.instField

variable (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] {k : Type u} [Field k] {U S : Scheme.{u}}
  (g : U ⟶ S) (q : S ⟶ Spec (.of k))
  [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace S] [QuasiSeparatedSpace S]
  [IsSeparated g] [LocallyOfFiniteType g] [IsSeparated q] [LocallyOfFiniteType q]
  (jg : CompactificationOf (Over.mk g)) (jS : CompactificationOf (Over.mk q))
  (jU : CompactificationOf (Over.mk (g ≫ q)))
  (hf : ∀ y : S, topologicalKrullDim (jg.toBase.fiber y) ≤ 1)
  (ν : etaleModuleInverseImage.{u, 0} (ZMod ℓ) g ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
    derivedLowerShriek.{u, 0} g jg (ZMod ℓ) ⋙ DerivedCategory.Plus.homologyFunctor _ 2 ≅
      𝟭 (EtaleModules.{u, 0} (ZMod ℓ) S))

/-- Reassociating a composite of shifted morphisms `a`, `b`, `c` followed by a trace `t₁` of
degree `-2`, given that `c` carries `t₁` to `t₂` and that `b` intertwines `t₂` with `tX`. -/
theorem shiftedHom_comp_comp_eq_of_comp_eq {C : Type*} [Category* C] [HasShift C ℤ] (e : ℕ)
    {X₁ X₂ X₃ X₄ X₅ X₆ : C}
    (a : ShiftedHom X₁ X₂ ((2 : ℕ) : ℤ)) (b : ShiftedHom X₂ X₃ ((2 * e : ℕ) : ℤ))
    (c : ShiftedHom X₃ X₄ ((0 : ℕ) : ℤ)) (t₁ : ShiftedHom X₄ X₆ (-2))
    (t₂ : ShiftedHom X₃ X₆ (-2)) (tX : ShiftedHom X₂ X₅ (-2))
    (βh : ShiftedHom X₅ X₆ ((2 * e : ℕ) : ℤ))
    (hct : c.comp t₁ (show (-2 : ℤ) + ((0 : ℕ) : ℤ) = -2 by simp) = t₂)
    (htr : b.comp t₂ (show (-2 : ℤ) + ((2 * e : ℕ) : ℤ) = ((2 * e : ℕ) : ℤ) - 2 by ring) =
      tX.comp βh (show ((2 * e : ℕ) : ℤ) + -2 = ((2 * e : ℕ) : ℤ) - 2 by ring))
    (h₁ : ((0 : ℕ) : ℤ) + ((2 * e : ℕ) : ℤ) = ((2 * e : ℕ) : ℤ))
    (h₂ : ((2 * e : ℕ) : ℤ) + ((2 : ℕ) : ℤ) = ((2 * (e + 1) : ℕ) : ℤ))
    (h₃ : (-2 : ℤ) + ((2 * (e + 1) : ℕ) : ℤ) = ((2 * e : ℕ) : ℤ)) :
    (a.comp (b.comp c h₁) h₂).comp t₁ h₃ =
      (a.comp tX (show (-2 : ℤ) + ((2 : ℕ) : ℤ) = 0 by norm_num)).comp βh
        (show ((2 * e : ℕ) : ℤ) + 0 = ((2 * e : ℕ) : ℤ) by simp) := by
  rw [ShiftedHom.comp_assoc a (b.comp c h₁) t₁ h₂
      (show (-2 : ℤ) + ((2 * e : ℕ) : ℤ) = ((2 * e : ℕ) : ℤ) - 2 by ring) (by push_cast; ring),
    ShiftedHom.comp_assoc b c t₁ h₁ (show (-2 : ℤ) + ((0 : ℕ) : ℤ) = -2 by simp)
      (by push_cast; ring), hct, htr,
    ShiftedHom.comp_assoc a tX βh (show (-2 : ℤ) + ((2 : ℕ) : ℤ) = 0 by norm_num)
      (show ((2 * e : ℕ) : ℤ) + -2 = ((2 * e : ℕ) : ℤ) - 2 by ring) (by push_cast; ring)]

/-- **The class of a point through a family of curves.** If the class of `i' : P → S` is nonzero
in `H^{2e}_c(S)`, and some `δ ∈ Ext²_U(p_* Λ_P, g⁻¹ i'_* Λ_P)` has `t ∘ Rg_!(δ)` split, then the
class of `p : P → U` is nonzero in `H^{2e+2}_c(U)`. -/
theorem pointClassNonzeroAt_of_fibration_of_section (e : ℕ) {P : Scheme.{u}} (p : P ⟶ U)
    (i' : P ⟶ S) (hS : PointClassNonzeroAt ℓ e q jS (𝟙 S) i')
    (δ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) p).obj (unitSheaf (X := P) ℓ))
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) g).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i').obj (unitSheaf (X := P) ℓ))) 2)
    (σ : (DerivedCategory.singleFunctor _ 0).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i').obj (unitSheaf (X := P) ℓ)) ⟶
      DerivedCategory.Plus.ι.obj ((derivedLowerShriek.{u, 0} g jg (ZMod ℓ)).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) p).obj (unitSheaf (X := P) ℓ)))))
    (hσ : σ ≫ ((Stacks.TopTruncationExt.extPlus δ).map
        (derivedLowerShriek.{u, 0} g jg (ZMod ℓ) ⋙ DerivedCategory.Plus.ι)).comp
          (lowerShriekTopTrace g jg ℓ hf ν _) (show (-2 : ℤ) + ((2 : ℕ) : ℤ) = 0 by norm_num) =
      ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 _)) :
    PointClassNonzeroAt ℓ (e + 1) (g ≫ q) jU (𝟙 U) p := by
  have hℓ : 0 < ℓ := NeZero.pos ℓ
  rw [pointClassNonzeroAt_id_iff] at hS ⊢
  obtain ⟨β, zS, hzS⟩ := hS
  let Φ := derivedLowerShriek.{u, 0} g jg (ZMod ℓ) ⋙ DerivedCategory.Plus.ι
  let ηU : (etaleModuleInverseImage.{u, 0} (ZMod ℓ) g).obj (unitSheaf (X := S) ℓ) ≅
      unitSheaf (X := U) ℓ :=
    (etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) g).app
      (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))
  let gβ := β.mapExactFunctor (etaleModuleInverseImage.{u, 0} (ZMod ℓ) g)
  let γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) p).obj (unitSheaf (X := P) ℓ))
      (unitSheaf (X := U) ℓ) (2 * (e + 1)) :=
    δ.comp (gβ.comp (Ext.mk₀ ηU.hom) (add_zero _)) (by omega)
  let A := (DerivedCategory.Plus.singleFunctor _ 0).obj
    ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) p).obj (unitSheaf (X := P) ℓ))
  let B := ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := U) ℓ))⟦
    ((2 * (e + 1) : ℕ) : ℤ)⟧
  have hT (K : DerivedCategory.Plus (EtaleModules.{u, 0} (ZMod ℓ) U)) :
      isTorsionPlus.{u, 0} (ZMod ℓ) U K := fun _ =>
    isTorsionEtaleModule_of_natCast_eq_zero (ZMod ℓ) ℓ hℓ (ZMod.natCast_self ℓ) _
  let L := derivedLowerShriekCompIso (ZMod ℓ) g q jg jS jU
  -- the top-degree trace, read on `Λ_U`
  let t := lowerShriekTopTrace g jg ℓ hf ν (unitSheaf (X := S) ℓ)
  let t'' : ShiftedHom (Φ.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
      (unitSheaf (X := U) ℓ))) ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))
        (-2) :=
    Φ.map ((DerivedCategory.Plus.singleFunctor _ 0).map ηU.inv) ≫ t
  let ΘD : Φ.obj B ⟶ ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))⟦
      ((2 * e : ℕ) : ℤ)⟧ :=
    (Φ.commShiftIso (((2 * (e + 1) : ℕ) : ℤ))).hom.app _ ≫ t''⟦((2 * (e + 1) : ℕ) : ℤ)⟧' ≫
      (shiftFunctorAdd' _ (-2) ((2 * (e + 1) : ℕ) : ℤ) ((2 * e : ℕ) : ℤ)
        (by push_cast; ring)).inv.app _
  obtain ⟨Θ, hΘ⟩ := (DerivedCategory.Plus.ι.map_surjective : Function.Surjective
    (DerivedCategory.Plus.ι.map : ((derivedLowerShriek.{u, 0} g jg (ZMod ℓ)).obj B ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))⟦
        ((2 * e : ℕ) : ℤ)⟧) → _))
      (ΘD ≫ (DerivedCategory.Plus.ι.commShiftIso (((2 * e : ℕ) : ℤ))).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)))
  obtain ⟨σ', hσ'⟩ := (DerivedCategory.Plus.ι.map_surjective : Function.Surjective
    (DerivedCategory.Plus.ι.map : ((DerivedCategory.Plus.singleFunctor _ 0).obj
      ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i').obj (unitSheaf (X := P) ℓ)) ⟶
        (derivedLowerShriek.{u, 0} g jg (ZMod ℓ)).obj A) → _)) σ
  -- the main identity, in `D(S)`
  have hd₃ : (-2 : ℤ) + ((2 * (e + 1) : ℕ) : ℤ) = ((2 * e : ℕ) : ℤ) := by push_cast; ring
  have hcomp : Φ.map (Stacks.TopTruncationExt.extPlus γ) ≫ ΘD =
      ((Stacks.TopTruncationExt.extPlus γ).map Φ).comp t'' hd₃ := by
    simp only [ΘD, ShiftedHom.comp, ShiftedHom.map, Category.assoc]
  have hη : ((Stacks.TopTruncationExt.extPlus (Ext.mk₀ ηU.hom)).map Φ).comp t''
      (show (-2 : ℤ) + ((0 : ℕ) : ℤ) = -2 by simp) = t := by
    rw [Stacks.TopTruncationExt.extPlus_mk₀, ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp]
    simp only [t'', ← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hmain : ((Stacks.TopTruncationExt.extPlus γ).map Φ).comp t'' hd₃ =
      (((Stacks.TopTruncationExt.extPlus δ).map Φ).comp
        (lowerShriekTopTrace g jg ℓ hf ν _) (show (-2 : ℤ) + ((2 : ℕ) : ℤ) = 0 by norm_num)).comp
          β.hom (show ((2 * e : ℕ) : ℤ) + 0 = ((2 * e : ℕ) : ℤ) by simp) := by
    simp only [γ]
    rw [Stacks.TopTruncationExt.extPlus_comp, Stacks.TopTruncationExt.extPlus_comp,
      ShiftedHom.map_comp, ShiftedHom.map_comp]
    exact shiftedHom_comp_comp_eq_of_comp_eq e _ _ _ _ _ _ _ hη
      (map_comp_lowerShriekTopTrace g jg ℓ hf ν β (((2 * e : ℕ) : ℤ) - 2) (by ring) (by ring)) _ _ _
  have key : σ' ≫ (derivedLowerShriek.{u, 0} g jg (ZMod ℓ)).map
      (Stacks.TopTruncationExt.extPlus γ) ≫ Θ = Stacks.TopTruncationExt.extPlus β := by
    apply DerivedCategory.Plus.ι.map_injective
    have hβ : DerivedCategory.Plus.ι.map (Stacks.TopTruncationExt.extPlus β) =
        β.hom ≫ (DerivedCategory.Plus.ι.commShiftIso (((2 * e : ℕ) : ℤ))).inv.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) :=
      DerivedCategory.Plus.ι.map_preimage _
    rw [hβ, Functor.map_comp, Functor.map_comp, hΘ, hσ']
    have step : σ ≫ Φ.map (Stacks.TopTruncationExt.extPlus γ) ≫ ΘD = β.hom := by
      rw [hcomp, hmain]
      have h2 := congrArg (fun w => ShiftedHom.comp w β.hom
        (show ((2 * e : ℕ) : ℤ) + 0 = ((2 * e : ℕ) : ℤ) by simp)) hσ
      exact (Category.assoc _ _ _).symm.trans (h2.trans (ShiftedHom.mk₀_id_comp _ _ _))
    have h3 := congrArg (fun w => w ≫ (DerivedCategory.Plus.ι.commShiftIso
      (((2 * e : ℕ) : ℤ))).inv.app ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (unitSheaf (X := S) ℓ))) step
    exact (congrArg (σ ≫ ·) (Category.assoc _ _ _).symm).trans
      ((Category.assoc _ _ _).symm.trans h3)
  have hnat' : L.inv.app ⟨A, hT A⟩ ≫ (derivedLowerShriek.{u, 0} (g ≫ q) jU (ZMod ℓ)).map
      (Stacks.TopTruncationExt.extPlus γ) ≫ L.hom.app ⟨B, hT B⟩ =
      (derivedLowerShriek.{u, 0} q jS (ZMod ℓ)).map ((derivedLowerShriek.{u, 0} g jg (ZMod ℓ)).map
        (Stacks.TopTruncationExt.extPlus γ)) :=
    NatIso.naturality_1 L (ObjectProperty.homMk (P := isTorsionPlus.{u, 0} (ZMod ℓ) U)
      (X := ⟨A, hT A⟩) (Y := ⟨B, hT B⟩) (Stacks.TopTruncationExt.extPlus γ))
  refine ⟨γ, zS ≫ (derivedLowerShriek.{u, 0} q jS (ZMod ℓ)).map σ' ≫ L.inv.app ⟨A, hT A⟩,
    fun h0 => hzS ?_⟩
  rw [← key, Functor.map_comp, Functor.map_comp, ← hnat']
  have h1 := congrArg (· ≫ L.hom.app ⟨B, hT B⟩ ≫ (derivedLowerShriek.{u, 0} q jS (ZMod ℓ)).map Θ) h0
  simpa only [Category.assoc, zero_comp] using h1

end Stacks.EtaleCohomology

end
