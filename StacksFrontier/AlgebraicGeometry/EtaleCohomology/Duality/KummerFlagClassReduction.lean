module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerUnitClassReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.UnitSheafEndomorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportRestrictScalarsComp
public import StacksFrontier.CategoryTheory.Abelian.ExtReductionSquare

/-!
# Kummer divisor and flag classes under reduction of the level

Let `N = e N'`, `res` restriction of scalars along `ℤ/N → ℤ/N'` and `ζ` a primitive `N`-th root
of unity. The constructions of `Stacks.EtaleCohomology.KummerFlag` are natural in the
coefficients, in the sense of commuting squares of `Ext` classes along `res`
(`Stacks.ExtReduction.ExtSq`: `x ∘ β = α ∘ res(x')`):

* `res` commutes with `j_!` and with `i_* i⁻¹` compatibly with the units and counits of the
  adjunctions (`Stacks.EtaleCohomology.etaleModuleExtensionByZeroRestrictScalars_counit`,
  `Stacks.EtaleCohomology.unit_comp_closedRestrictionRestrictScalars`), so every
  `w : Λ_U ⟶ res Λ'_U` induces a morphism from the sequence
  `0 → j_! j⁻¹ Λ_U → Λ_U → i_* i⁻¹ Λ_U → 0` of Tag 095L at level `N` to `res` of the one at level
  `N'` (`Stacks.EtaleCohomology.divisorShortComplexReduction`);
* on a preconnected `V` every `w : Λ_V ⟶ res Λ'_V` is a multiple of the reduction, so by
  `Stacks.EtaleCohomology.ExtensionTorsor.kummerUnitClass_comp_unitSheafReduction` the Kummer
  classes `κ_N(a)` (root `ζ`) and `κ_{N'}(a)` (root `ζ^e`) form the square `(w, w)`
  (`Stacks.EtaleCohomology.extSq_kummerUnitClass`); this absorbs all identifications
  `j⁻¹ Λ ≅ Λ`;
* hence the Kummer divisor classes form a square
  (`Stacks.EtaleCohomology.extSq_kummerDivisorClass`), and, by induction along the flag, so do
  the Kummer flag classes, through a reduction of the flag sheaves compatible with the canonical
  maps (`Stacks.EtaleCohomology.flagSheafReduction`,
  `Stacks.EtaleCohomology.flagUnit_comp_flagSheafReduction`,
  `Stacks.EtaleCohomology.extSq_kummerFlagClass`).

## Main definitions

* `Stacks.EtaleCohomology.closedRestrictionRestrictScalars`
* `Stacks.EtaleCohomology.divisorShortComplexReduction`
* `Stacks.EtaleCohomology.flagSheafReduction`

## Main results

* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroRestrictScalars_counit`
* `Stacks.EtaleCohomology.extSq_kummerUnitClass`
* `Stacks.EtaleCohomology.extSq_kummerDivisorClass`
* `Stacks.EtaleCohomology.flagUnit_comp_flagSheafReduction`
* `Stacks.EtaleCohomology.extSq_kummerFlagClass`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.ExtensionTorsor Stacks.ExtReduction

universe u

namespace Stacks.EtaleCohomology

-- see `Stacks.EtaleCohomology.ExtensionTorsor.kummerUnitClass_comp_unitSheafReduction`
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

section Counit

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

/-- **The comparison of extension by zero with `res_ρ` is compatible with the counits** of
`j_! ⊣ j⁻¹`: `j_! (res j⁻¹ G) ⟶ res (j_! j⁻¹ G) ⟶ res G` is the counit at `res G`. -/
theorem etaleModuleExtensionByZeroRestrictScalars_counit {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
    (G : EtaleModules.{u, 0} Λ' X) :
    (etaleModuleExtensionByZeroRestrictScalars ρ j).hom.app
        ((etaleModuleRestriction.{u, 0} Λ' j).obj G) ≫
      (etaleModuleRestrictScalars ρ X).map
        ((etaleModuleExtensionByZeroAdj.{u, 0} Λ' j).counit.app G) =
    (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit.app
      ((etaleModuleRestrictScalars ρ X).obj G) := by
  apply ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).homEquiv _ _).injective
  have e2 := ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).homEquiv_unit _ _ _).trans
    ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).right_triangle_components
      ((etaleModuleRestrictScalars ρ X).obj G))
  refine Eq.trans ?_ e2.symm
  rw [Adjunction.homEquiv_unit]
  have hu := etaleModuleExtensionByZeroRestrictScalars_unit ρ j
    ((etaleModuleRestriction.{u, 0} Λ' j).obj G)
  refine (congrArg ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.app _ ≫ ·)
    ((etaleModuleRestriction.{u, 0} Λ j).map_comp _ _)).trans ((Category.assoc _ _ _).symm.trans ?_)
  refine (congrArg (· ≫ (etaleModuleRestriction.{u, 0} Λ j).map
    ((etaleModuleRestrictScalars ρ X).map
      ((etaleModuleExtensionByZeroAdj.{u, 0} Λ' j).counit.app G))) hu).trans ?_
  exact ((etaleModuleRestrictScalars ρ U).map_comp _ _).symm.trans
    ((congrArg (etaleModuleRestrictScalars ρ U).map
      ((etaleModuleExtensionByZeroAdj.{u, 0} Λ' j).right_triangle_components G)).trans
        ((etaleModuleRestrictScalars ρ U).map_id _))

end Counit

variable {N N' : ℕ} (h : N' ∣ N)

/-- **`res` commutes with `E_W = i_* i⁻¹`**, through the comparison of inverse image with `res`
and the strict commutation of direct image with `res`. -/
def closedRestrictionRestrictScalars {U W : Scheme.{u}} (i : W ⟶ U) :
    etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) U ⋙
        KummerFlag.closedRestriction (N := N) i ⟶
      KummerFlag.closedRestriction (N := N') i ⋙
        etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) U where
  app G := (etaleModuleDirectImage.{u, 0} (ZMod N) i).map
    ((etaleModuleInverseImageRestrictScalars (ZMod.castHom h (ZMod N')) i).hom.app G)
  naturality _ _ f :=
    (((etaleModuleDirectImage.{u, 0} (ZMod N) i).map_comp _ _).symm.trans
      (congrArg (etaleModuleDirectImage.{u, 0} (ZMod N) i).map
        ((etaleModuleInverseImageRestrictScalars (ZMod.castHom h (ZMod N')) i).hom.naturality
          f))).trans ((etaleModuleDirectImage.{u, 0} (ZMod N) i).map_comp _ _)

/-- **The comparison of `E_W` with `res` is compatible with the units** of `i⁻¹ ⊣ i_*`. -/
@[reassoc]
theorem unit_comp_closedRestrictionRestrictScalars {U W : Scheme.{u}} (i : W ⟶ U)
    {M : EtaleModules.{u, 0} (ZMod N) U} {G : EtaleModules.{u, 0} (ZMod N') U}
    (w : M ⟶ (etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) U).obj G) :
    (etaleModuleInverseImageAdj.{u, 0} (ZMod N) i).unit.app M ≫
        (KummerFlag.closedRestriction (N := N) i).map w ≫
          (closedRestrictionRestrictScalars h i).app G =
      w ≫ (etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) U).map
        ((etaleModuleInverseImageAdj.{u, 0} (ZMod N') i).unit.app G) := by
  have hn := (etaleModuleInverseImageAdj.{u, 0} (ZMod N) i).unit_naturality w
  have hu := etaleModuleInverseImageRestrictScalars_unit (ZMod.castHom h (ZMod N')) i G
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ (closedRestrictionRestrictScalars h i).app G) hn).trans ?_
  exact (Category.assoc _ _ _).trans (congrArg (w ≫ ·) hu)

/-- The restriction `j⁻¹ w : j⁻¹ M ⟶ res (j⁻¹ G)` of `w : M ⟶ res G` along an étale `j`
(restriction commutes with `res` on the nose). -/
def restrictionReduction {U V : Scheme.{u}} (j : V ⟶ U) [Etale j]
    {M : EtaleModules.{u, 0} (ZMod N) U} {G : EtaleModules.{u, 0} (ZMod N') U}
    (w : M ⟶ (etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) U).obj G) :
    (etaleModuleRestriction.{u, 0} (ZMod N) j).obj M ⟶
      (etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) V).obj
        ((etaleModuleRestriction.{u, 0} (ZMod N') j).obj G) :=
  (etaleModuleRestriction.{u, 0} (ZMod N) j).map w

/-- **The reduction of the sequence of Tag 095L** along `w : Λ_U ⟶ res Λ'_U`: the morphism
`(j_! j⁻¹ w, w, i_* i⁻¹ w)` from the sequence `0 → j_! j⁻¹ Λ_U → Λ_U → i_* i⁻¹ Λ_U → 0` at level
`N` to `res` of the sequence at level `N'`. -/
def divisorShortComplexReduction {U V W : Scheme.{u}} (j : V ⟶ U) [IsOpenImmersion j]
    (i : W ⟶ U) [IsClosedImmersion i] (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (w : ExtensionTorsor.unitSheaf (X := U) N ⟶
      (etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) U).obj
        (ExtensionTorsor.unitSheaf (X := U) N')) :
    KummerFlag.divisorShortComplex (N := N) j i hij ⟶
      (KummerFlag.divisorShortComplex (N := N') j i hij).map
        (etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) U) where
  τ₁ := (etaleModuleExtensionByZero.{u, 0} (ZMod N) j).map (restrictionReduction h j w) ≫
    (etaleModuleExtensionByZeroRestrictScalars (ZMod.castHom h (ZMod N')) j).hom.app
      ((etaleModuleRestriction.{u, 0} (ZMod N') j).obj (ExtensionTorsor.unitSheaf (X := U) N'))
  τ₂ := w
  τ₃ := (KummerFlag.closedRestriction (N := N) i).map w ≫
    (closedRestrictionRestrictScalars h i).app (ExtensionTorsor.unitSheaf (X := U) N')
  comm₁₂ := (Category.assoc _ _ _).trans
    ((congrArg ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).map (restrictionReduction h j w) ≫ ·)
      (etaleModuleExtensionByZeroRestrictScalars_counit (ZMod.castHom h (ZMod N')) j
        (ExtensionTorsor.unitSheaf (X := U) N'))).trans
      ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) j).counit_naturality w))
  comm₂₃ := (unit_comp_closedRestrictionRestrictScalars h i w).symm

/-- **Kummer classes on a preconnected scheme form a square along any `w : Λ_V ⟶ res Λ'_V`**:
`κ_N(a) ∘ w = w ∘ res(κ_{N'}(a))`, for `N = e N'`, `ζ` a primitive `N`-th root of unity and roots
`ζ` and `ζ^e`. Indeed `w` is `c` times the reduction, `V` being preconnected. -/
theorem extSq_kummerUnitClass {k : Type u} [Field k] {V : Scheme.{u}} [PreconnectedSpace V]
    (fV : V ⟶ Spec (.of k)) {e : ℕ} (he : e * N' = N) {ζ : k} (hζ : IsPrimitiveRoot ζ N)
    (hζ' : IsPrimitiveRoot (ζ ^ e) N') (hN : IsUnit (N : k)) (hN' : IsUnit (N' : k))
    (a : (Γ(V, ⊤))ˣ)
    (w : ExtensionTorsor.unitSheaf (X := V) N ⟶
      (etaleModuleRestrictScalars (ZMod.castHom (Dvd.intro_left e he) (ZMod N')) V).obj
        (ExtensionTorsor.unitSheaf (X := V) N')) :
    ExtSq (etaleModuleRestrictScalars (ZMod.castHom (Dvd.intro_left e he) (ZMod N')) V) w w
      (KummerFlag.kummerUnitClass hζ hN fV a) (KummerFlag.kummerUnitClass hζ' hN' fV a) := by
  have : NeZero N' := ⟨KummerFlag.ne_zero_of_isUnit hN'⟩
  obtain ⟨y, hy⟩ := (bijective_mk₀CompMapExactFunctor_unitSheafReduction_zero
    (Dvd.intro_left e he) (ExtensionTorsor.unitSheaf (X := V) N')).2 (Ext.mk₀ w)
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).2 y
  rw [mk₀CompMapExactFunctor_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀] at hy
  have hw := (Ext.mk₀_bijective _ _).1 hy
  obtain ⟨c, rfl⟩ := KummerFlag.exists_eq_smul_id g
  have hc : c • 𝟙 (ExtensionTorsor.unitSheaf (X := V) N') = c.val • 𝟙 _ := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod N'), ZMod.natCast_zmod_val]
  rw [hc, CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id,
    Preadditive.comp_nsmul, Category.comp_id] at hw
  subst hw
  exact ExtSq.nsmul
    (R := etaleModuleRestrictScalars (ZMod.castHom (Dvd.intro_left e he) (ZMod N')) V)
    (kummerUnitClass_comp_unitSheafReduction fV he hζ hζ' hN hN' a) c.val

/-- **Kummer divisor classes form a square** along any `w : Λ_U ⟶ res Λ'_U`, with left side
`i_* i⁻¹ w` (read through the comparison of `E_W` with `res`), when the open part `V` is
preconnected. -/
theorem extSq_kummerDivisorClass {k : Type u} [Field k] {U V W : Scheme.{u}}
    (fU : U ⟶ Spec (.of k)) (j : V ⟶ U) [IsOpenImmersion j] [PreconnectedSpace V] (i : W ⟶ U)
    [IsClosedImmersion i] (hij : Set.range j.base = (Set.range i.base)ᶜ) {e : ℕ}
    (he : e * N' = N) {ζ : k} (hζ : IsPrimitiveRoot ζ N) (hζ' : IsPrimitiveRoot (ζ ^ e) N')
    (hN : IsUnit (N : k)) (hN' : IsUnit (N' : k)) (a : (Γ(V, ⊤))ˣ)
    (w : ExtensionTorsor.unitSheaf (X := U) N ⟶
      (etaleModuleRestrictScalars (ZMod.castHom (Dvd.intro_left e he) (ZMod N')) U).obj
        (ExtensionTorsor.unitSheaf (X := U) N')) :
    ExtSq (etaleModuleRestrictScalars (ZMod.castHom (Dvd.intro_left e he) (ZMod N')) U)
      ((KummerFlag.closedRestriction (N := N) i).map w ≫
        (closedRestrictionRestrictScalars (Dvd.intro_left e he) i).app
          (ExtensionTorsor.unitSheaf (X := U) N')) w
      (KummerFlag.kummerDivisorClass hζ hN fU j i hij a)
      (KummerFlag.kummerDivisorClass hζ' hN' fU j i hij a) := by
  let RV := etaleModuleRestrictScalars (ZMod.castHom (Dvd.intro_left e he) (ZMod N')) V
  let ι := KummerFlag.restrictionUnitSheafIso (N := N) j
  let ι' := KummerFlag.restrictionUnitSheafIso (N := N') j
  let jw := restrictionReduction (Dvd.intro_left e he) j w
  let w' : ExtensionTorsor.unitSheaf (X := V) N ⟶ RV.obj (ExtensionTorsor.unitSheaf (X := V) N') :=
    ι.inv ≫ jw ≫ RV.map ι'.hom
  have h₁ : ι.hom ≫ w' = jw ≫ RV.map ι'.hom := ι.hom_inv_id_assoc _
  have h₂ : ι.inv ≫ jw = w' ≫ RV.map ι'.inv := by
    show ι.inv ≫ jw = (ι.inv ≫ jw ≫ RV.map ι'.hom) ≫ RV.map ι'.inv
    rw [Category.assoc, Category.assoc, ← CategoryTheory.Functor.map_comp, ι'.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have hK : ExtSq RV jw jw
      ((Ext.mk₀ ι.hom).comp ((KummerFlag.kummerUnitClass hζ hN (j ≫ fU) a).comp
        (Ext.mk₀ ι.inv) (add_zero 1)) (zero_add 1))
      ((Ext.mk₀ ι'.hom).comp ((KummerFlag.kummerUnitClass hζ' hN' (j ≫ fU) a).comp
        (Ext.mk₀ ι'.inv) (add_zero 1)) (zero_add 1)) :=
    (ExtSq.mk₀ h₁).comp ((extSq_kummerUnitClass (j ≫ fU) he hζ hζ' hN hN' a w').comp
      (ExtSq.mk₀ h₂) (add_zero 1)) (zero_add 1)
  exact (ExtSq.extClass (KummerFlag.divisorShortComplex_shortExact (N := N) j i hij)
    (KummerFlag.divisorShortComplex_shortExact (N := N') j i hij)
    (divisorShortComplexReduction (Dvd.intro_left e he) j i hij w)).comp
      ((ExtSq.map (etaleModuleExtensionByZero.{u, 0} (ZMod N) j)
        (etaleModuleExtensionByZero.{u, 0} (ZMod N') j)
        (etaleModuleExtensionByZeroRestrictScalars (ZMod.castHom (Dvd.intro_left e he)
          (ZMod N')) j).hom hK).comp
        (ExtSq.mk₀ (divisorShortComplexReduction (Dvd.intro_left e he) j i hij w).comm₁₂.symm)
        (add_zero 1)) (by norm_num)

/-- **The reduction of the flag sheaf** `E_0 ⋯ E_{d-1} Λ_U ⟶ res(E_0 ⋯ E_{d-1} Λ'_U)` along
`w : Λ_U ⟶ res Λ'_U`: `E_0 ⋯ E_{d-1} w`, read through the comparisons of the `E_m` with `res`. -/
def flagSheafReduction {U : Scheme.{u}} : {d : ℕ} → (D : Fin d → KummerFlag.DivisorDatum U) →
    (ExtensionTorsor.unitSheaf (X := U) N ⟶
      (etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) U).obj
        (ExtensionTorsor.unitSheaf (X := U) N')) →
    (KummerFlag.flagSheaf (N := N) D ⟶
      (etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) U).obj
        (KummerFlag.flagSheaf (N := N') D))
  | 0, _, w => w
  | _ + 1, D, w => (KummerFlag.closedRestriction (N := N) (D 0).i).map
      (flagSheafReduction (fun m => D m.succ) w) ≫
    (closedRestrictionRestrictScalars h (D 0).i).app
      (KummerFlag.flagSheaf (N := N') fun m => D m.succ)

/-- **The reduction of the flag sheaf is compatible with the canonical maps**:
`Λ_U ⟶ E_0 ⋯ E_{d-1} Λ_U ⟶ res(E_0 ⋯ E_{d-1} Λ'_U)` is `w` followed by `res` of the canonical
map. -/
theorem flagUnit_comp_flagSheafReduction {U : Scheme.{u}} : ∀ {d : ℕ}
    (D : Fin d → KummerFlag.DivisorDatum U)
    (w : ExtensionTorsor.unitSheaf (X := U) N ⟶
      (etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) U).obj
        (ExtensionTorsor.unitSheaf (X := U) N')),
    KummerFlag.flagUnit (N := N) D ≫ flagSheafReduction h D w =
      w ≫ (etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) U).map
        (KummerFlag.flagUnit (N := N') D)
  | 0, _, w => by
    show 𝟙 _ ≫ w = w ≫ (etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) U).map (𝟙 _)
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  | d + 1, D, w => by
    have ih := flagUnit_comp_flagSheafReduction (fun m => D m.succ) w
    have hn : (KummerFlag.closedRestriction (N := N) (D 0).i).map
          ((etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) U).map
            (KummerFlag.flagUnit (N := N') fun m => D m.succ)) ≫
          (closedRestrictionRestrictScalars h (D 0).i).app
            (KummerFlag.flagSheaf (N := N') fun m => D m.succ) =
        (closedRestrictionRestrictScalars h (D 0).i).app (ExtensionTorsor.unitSheaf (X := U) N') ≫
          (etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) U).map
            ((KummerFlag.closedRestriction (N := N') (D 0).i).map
              (KummerFlag.flagUnit (N := N') fun m => D m.succ)) :=
      (closedRestrictionRestrictScalars h (D 0).i).naturality
        (KummerFlag.flagUnit (N := N') fun m => D m.succ)
    have e1 := congrArg (fun t => (etaleModuleInverseImageAdj.{u, 0} (ZMod N) (D 0).i).unit.app
        (ExtensionTorsor.unitSheaf (X := U) N) ≫
          (KummerFlag.closedRestriction (N := N) (D 0).i).map t ≫
          (closedRestrictionRestrictScalars h (D 0).i).app
            (KummerFlag.flagSheaf (N := N') fun m => D m.succ)) ih
    simp only [KummerFlag.flagUnit, flagSheafReduction]
    refine Eq.trans ?_ (e1.trans ?_)
    · exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) ((KummerFlag.closedRestriction (N := N) (D 0).i).map_comp _ _).symm)))
    · simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      rw [hn]
      exact (unit_comp_closedRestrictionRestrictScalars_assoc h (D 0).i w _).trans
        (congrArg (w ≫ ·)
          ((etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) U).map_comp _ _).symm)

/-- **Kummer flag classes form a square** along any `w : Λ_U ⟶ res Λ'_U`, with left side the
reduction of the flag sheaf, when the open parts of the divisor data are preconnected. -/
theorem extSq_kummerFlagClass {k : Type u} [Field k] {U : Scheme.{u}} (fU : U ⟶ Spec (.of k))
    {e : ℕ} (he : e * N' = N) {ζ : k} (hζ : IsPrimitiveRoot ζ N)
    (hζ' : IsPrimitiveRoot (ζ ^ e) N') (hN : IsUnit (N : k)) (hN' : IsUnit (N' : k)) :
    ∀ {d : ℕ} (D : Fin d → KummerFlag.DivisorDatum U) [∀ m, PreconnectedSpace (D m).V]
      (w : ExtensionTorsor.unitSheaf (X := U) N ⟶
        (etaleModuleRestrictScalars (ZMod.castHom (Dvd.intro_left e he) (ZMod N')) U).obj
          (ExtensionTorsor.unitSheaf (X := U) N')),
      ExtSq (etaleModuleRestrictScalars (ZMod.castHom (Dvd.intro_left e he) (ZMod N')) U)
        (flagSheafReduction (Dvd.intro_left e he) D w) w
        (KummerFlag.kummerFlagClass hζ hN fU D) (KummerFlag.kummerFlagClass hζ' hN' fU D)
  | 0, _, _, w => by
    show ExtSq _ w w (Ext.mk₀ (𝟙 _)) (Ext.mk₀ (𝟙 _))
    exact ExtSq.mk₀ (by rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id])
  | d + 1, D, _, w => by
    have : ∀ m : Fin d, PreconnectedSpace (D m.succ).V := fun m => inferInstance
    exact (ExtSq.map (KummerFlag.closedRestriction (N := N) (D 0).i)
      (KummerFlag.closedRestriction (N := N') (D 0).i)
      (closedRestrictionRestrictScalars (Dvd.intro_left e he) (D 0).i)
      (extSq_kummerFlagClass fU he hζ hζ' hN hN' (fun m => D m.succ) w)).comp
        (extSq_kummerDivisorClass fU (D 0).j (D 0).i (D 0).range_eq he hζ hζ' hN hN' (D 0).a w)
        (by ring)

end Stacks.EtaleCohomology

end
