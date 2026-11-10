module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerFlagTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification

/-!
# The Kummer point class under inverse image

Let `π : Y ⟶ Y` be a morphism over `k`, `n : U ⟶ Y` an open immersion and `U' = π⁻¹(U)`, with
`g : U' ⟶ U`. The adjunction map of `n_! ⊣ n⁻¹` commutes with inverse image along `π`
(`Stacks.EtaleCohomology.KummerFlag.transport_extMap`, an abstract statement about two adjunctions
and a comparison of the restrictions), so the restriction along `π` of a Kummer point class on `U`
is a Kummer point class on `U'` of the transported flag
(`Stacks.EtaleCohomology.KummerFlag.constantExtRestriction_kummerPointClass`).

## Main results

* `Stacks.EtaleCohomology.KummerFlag.transport_extMap`
* `Stacks.EtaleCohomology.KummerFlag.transport_pointClass`
* `Stacks.EtaleCohomology.KummerFlag.constantExtRestriction_kummerPointClass`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.ExtensionTorsor Stacks.ExtTransport

universe u

namespace Stacks.EtaleCohomology.KummerFlag

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section ExtMap

/-- The image of a sandwich under the adjunction map. -/
theorem extMap_sandwich {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D] [HasExt C]
    [HasExt D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.Additive] [PreservesFiniteLimits L]
    [PreservesFiniteColimits L] {A A' : C} {B : D} {X : C} (u : A' ⟶ A) (v : X ⟶ R.obj B) {m : ℕ}
    (y : Ext A X m) :
    Stacks.ExtAdjunction.extMap adj A' B m (sandwich u v m y) =
      (Ext.mk₀ (L.map u)).comp
        (Stacks.ExtAdjunction.extMap adj A B m (y.comp (Ext.mk₀ v) (add_zero m))) (zero_add m) := by
  rw [Stacks.ExtAdjunction.extMap_apply, Stacks.ExtAdjunction.extMap_apply, sandwich_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]

/-- The adjunction map is `ℤ/N`-linear. -/
theorem extMap_smul_zmod {N : ℕ} [NeZero N] {C D : Type*} [Category C] [Abelian C] [Category D]
    [Abelian D] [HasExt C] [HasExt D] [Linear (ZMod N) C] [Linear (ZMod N) D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {A : C} {B : D} {m : ℕ} (c : ZMod N) (y : Ext A (R.obj B) m) :
    Stacks.ExtAdjunction.extMap adj A B m (c • y) =
      c • Stacks.ExtAdjunction.extMap adj A B m y := by
  rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

end ExtMap

section Abstract

variable {CY CY' CU CU' : Type*} [Category CY] [Abelian CY] [Category CY'] [Abelian CY']
  [Category CU] [Abelian CU] [Category CU'] [Abelian CU'] [HasExt CY] [HasExt CY'] [HasExt CU]
  [HasExt CU'] [EnoughInjectives CY] [EnoughInjectives CY'] [EnoughInjectives CU]
  [EnoughInjectives CU']
  {L : CU ⥤ CY} {R : CY ⥤ CU} (adj : L ⊣ R) {L' : CU' ⥤ CY'} {R' : CY' ⥤ CU'} (adj' : L' ⊣ R')
  [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [L'.Additive] [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [R'.Additive] [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  (F : CY ⥤ CY') [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (G : CU ⥤ CU') [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (θ : R ⋙ G ≅ F ⋙ R')

/-- Transporting the adjunction map along `R` and precomposing with the unit recovers the class. -/
private theorem transport_unit_extMap_adj {C D : Type*} [Category C] [Abelian C] [Category D]
    [Abelian D] [HasExt C] [HasExt D] [EnoughInjectives C] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] {A : C} {B : D} {m : ℕ}
    (y : Ext A (R.obj B) m) :
    transport R (adj.unit.app A) (𝟙 _) m (Stacks.ExtAdjunction.extMap adj A B m y) = y := by
  rw [transport_apply, sandwich_apply, Ext.comp_mk₀_id]
  exact unit_comp_mapExactFunctor_extMap adj A B m y

include adj adj' θ in
/-- **The adjunction map commutes with inverse image**: for any `e : L' P' ⟶ F(L P)` and
`c : F O ⟶ O'`, the transport of the image of `x` under `L ⊣ R` is the image under `L' ⊣ R'` of
the transport of `x` along `G`, through the comparison `θ` of the restrictions. -/
theorem transport_extMap {P : CU} {P' : CU'} {O : CY} {O' : CY'} [IsIso (adj.unit.app P)]
    (e : L'.obj P' ⟶ F.obj (L.obj P)) (c : F.obj O ⟶ O') {m : ℕ} (x : Ext P (R.obj O) m) :
    transport F e c m (Stacks.ExtAdjunction.extMap adj P O m x) =
      Stacks.ExtAdjunction.extMap adj' P' O' m
        (transport G ((adj'.unit.app P' ≫ R'.map e ≫ θ.inv.app (L.obj P)) ≫
          G.map (inv (adj.unit.app P))) (θ.hom.app O ≫ R'.map c) m x) := by
  have hinj : Function.Injective (transport R' (adj'.unit.app P') (𝟙 (R'.obj O')) m) := by
    intro y₁ y₂ h
    have hb := Stacks.ExtAdjunction.extMap_bijective adj' P' O' m
    obtain ⟨e₁, rfl⟩ := hb.2 y₁
    obtain ⟨e₂, rfl⟩ := hb.2 y₂
    rw [transport_unit_extMap_adj, transport_unit_extMap_adj] at h
    rw [h]
  have hstep : ∀ (P₀ : P' ⟶ (R ⋙ G).obj (L.obj P)) (Q₀ : (R ⋙ G).obj O ⟶ R'.obj O')
      (a₂ : P' ⟶ G.obj P) (b₂ : G.obj (R.obj O) ⟶ R'.obj O')
      (_ : a₂ ≫ G.map (adj.unit.app P) = P₀) (_ : b₂ = Q₀) (y : Ext (L.obj P) O m),
      transport (R ⋙ G) P₀ Q₀ m y =
        transport G a₂ b₂ m (transport R (adj.unit.app P) (𝟙 _) m y) := by
    intro P₀ Q₀ a₂ b₂ h₁ h₂ y
    subst h₁ h₂
    rw [transport_transport R G (R ⋙ G) (Iso.refl _)]
    simp
  apply hinj
  rw [transport_unit_extMap_adj adj', transport_transport F R' (F ⋙ R') (Iso.refl _),
    transport_iso θ,
    hstep _ _ ((adj'.unit.app P' ≫ R'.map e ≫ θ.inv.app (L.obj P)) ≫ G.map (inv (adj.unit.app P)))
      (θ.hom.app O ≫ R'.map c) (by simp) (by simp), transport_unit_extMap_adj adj]

omit [Abelian CY] [Abelian CY'] [Abelian CU] [Abelian CU'] [HasExt CY] [HasExt CY'] [HasExt CU]
  [HasExt CU'] [EnoughInjectives CY] [EnoughInjectives CY'] [EnoughInjectives CU]
  [EnoughInjectives CU'] [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [L'.Additive] [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [R'.Additive] [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] in
include adj adj' θ in
/-- The comparison of `transport_extMap` composed with its expected inverse is the unit. -/
theorem comparison_comp {P : CU} {P' : CU'} [IsIso (adj.unit.app P)]
    (e : L'.obj P' ≅ F.obj (L.obj P)) :
    ((adj'.unit.app P' ≫ R'.map e.hom ≫ θ.inv.app (L.obj P)) ≫ G.map (inv (adj.unit.app P))) ≫
        (G.map (adj.unit.app P) ≫ θ.hom.app (L.obj P) ≫ R'.map e.inv) = adj'.unit.app P' := by
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

include adj adj' θ in
/-- **The point class under inverse image, abstractly.** Let `L ⊣ R` and `L' ⊣ R'` be adjunctions
of exact functors (extension by zero and restriction along `n` and `n'`), `F` and `G` exact
functors (inverse images) with `θ : R ⋙ G ≅ F ⋙ R'`, and `e : L' P' ≅ F (L P)`. Suppose the
transport of `γ ∈ Ext^m(P, Λ_U)` along `G` is `s • γ'`, the canonical maps `u, u'` agree through
`P' ≅ G P`, and every endomorphism of `Λ_{U'}` is a scalar. Then for `z : Λ_Y ⟶ L P` adapted to
`u`, the transport along `F` of the class `z ∘ L(γ) ∘ counit` is `s` times the class of some
`z' : Λ_{Y'} ⟶ L' P'` adapted to `u'`. -/
theorem transport_pointClass {N : ℕ} [NeZero N] [Linear (ZMod N) CU'] [Linear (ZMod N) CY']
    {P : CU} {P' : CU'} {ΛY : CY} {ΛY' : CY'} {ΛU : CU} {ΛU' : CU'} [IsIso (adj.unit.app P)]
    [IsIso (adj'.unit.app P')]
    (e : L'.obj P' ≅ F.obj (L.obj P)) (cY : ΛY' ≅ F.obj ΛY) (cU : ΛU' ≅ G.obj ΛU)
    (rn : R.obj ΛY ≅ ΛU) (rn' : R'.obj ΛY' ≅ ΛU') (eP : P' ≅ G.obj P)
    (u : ΛU ⟶ P) (u' : ΛU' ⟶ P') (hu : u' ≫ eP.hom = cU.hom ≫ G.map u)
    {m : ℕ} (γ : Ext P ΛU m) (γ' : Ext P' ΛU' m) (s : ℕ)
    (hγ : transport G eP.hom cU.inv m γ = s • γ')
    (hscal : ∀ w : ΛU' ⟶ ΛU', ∃ c : ZMod N, w = c • 𝟙 _)
    (z : ΛY ⟶ L.obj P) (hz : R.map z = rn.hom ≫ u ≫ adj.unit.app P) :
    ∃ z' : ΛY' ⟶ L'.obj P', R'.map z' = rn'.hom ≫ u' ≫ adj'.unit.app P' ∧
      transport F cY.hom cY.inv m ((Ext.mk₀ z).comp
          (Stacks.ExtAdjunction.extMap adj P ΛY m (γ.comp (Ext.mk₀ rn.inv) (add_zero m)))
          (zero_add m)) =
        s • (Ext.mk₀ z').comp
          (Stacks.ExtAdjunction.extMap adj' P' ΛY' m (γ'.comp (Ext.mk₀ rn'.inv) (add_zero m)))
          (zero_add m) := by
  obtain ⟨c, hc⟩ := hscal ((cU.hom ≫ G.map rn.inv ≫ θ.hom.app ΛY ≫ R'.map cY.inv) ≫ rn'.hom)
  have hv : cU.hom ≫ G.map rn.inv ≫ θ.hom.app ΛY ≫ R'.map cY.inv = c • rn'.inv := by
    calc _ = ((cU.hom ≫ G.map rn.inv ≫ θ.hom.app ΛY ≫ R'.map cY.inv) ≫ rn'.hom) ≫ rn'.inv := by
          rw [Category.assoc _ rn'.hom, rn'.hom_inv_id, Category.comp_id]
      _ = c • rn'.inv := by rw [hc, Linear.smul_comp, Category.id_comp]
  have hvw : (cU.hom ≫ G.map rn.inv ≫ θ.hom.app ΛY ≫ R'.map cY.inv) ≫
      (R'.map cY.hom ≫ θ.inv.app ΛY ≫ G.map rn.hom ≫ cU.inv) = 𝟙 _ := by
    simp only [Category.assoc]
    rw [← R'.map_comp_assoc, cY.inv_hom_id, R'.map_id, Category.id_comp,
      Iso.hom_inv_id_app_assoc, ← G.map_comp_assoc, rn.inv_hom_id, G.map_id, Category.id_comp,
      cU.hom_inv_id]
  have hw : c • (R'.map cY.hom ≫ θ.inv.app ΛY ≫ G.map rn.hom ≫ cU.inv) = rn'.hom := by
    calc c • (R'.map cY.hom ≫ θ.inv.app ΛY ≫ G.map rn.hom ≫ cU.inv)
        = rn'.hom ≫ (c • rn'.inv) ≫ (R'.map cY.hom ≫ θ.inv.app ΛY ≫ G.map rn.hom ≫ cU.inv) := by
          rw [Linear.smul_comp, Linear.comp_smul, Iso.hom_inv_id_assoc]
      _ = rn'.hom := by rw [← hv, hvw, Category.comp_id]
  obtain ⟨a₂, ha₂⟩ : ∃ a₂ : P' ⟶ G.obj P,
      a₂ = (adj'.unit.app P' ≫ R'.map e.hom ≫ θ.inv.app (L.obj P)) ≫ G.map (inv (adj.unit.app P)) :=
    ⟨_, rfl⟩
  have hcomp : a₂ ≫ (G.map (adj.unit.app P) ≫ θ.hom.app (L.obj P) ≫ R'.map e.inv) =
      adj'.unit.app P' := by
    rw [ha₂]
    exact comparison_comp adj adj' F G θ e
  have : IsIso a₂ := by
    rw [ha₂]
    infer_instance
  have hkey : G.map (adj.unit.app P) ≫ θ.hom.app (L.obj P) ≫ R'.map e.inv =
      inv a₂ ≫ adj'.unit.app P' :=
    (IsIso.eq_inv_comp _).mpr hcomp
  have hres : R'.map (cY.hom ≫ F.map z ≫ e.inv ≫ L'.map (a₂ ≫ eP.inv)) =
      (R'.map cY.hom ≫ θ.inv.app ΛY ≫ G.map rn.hom ≫ cU.inv) ≫ u' ≫ adj'.unit.app P' := by
    have hθz : R'.map (F.map z) = θ.inv.app ΛY ≫ G.map (R.map z) ≫ θ.hom.app (L.obj P) := by
      have h := θ.hom.naturality z
      simp only [Functor.comp_map] at h
      rw [h, Iso.inv_hom_id_app_assoc]
    have hGu : G.map u = cU.inv ≫ u' ≫ eP.hom := by
      rw [hu, Iso.inv_hom_id_assoc]
    have hun := (adj'.unit.naturality (a₂ ≫ eP.inv)).symm
    simp only [Functor.id_obj, Functor.id_map, Functor.comp_map] at hun
    rw [R'.map_comp, R'.map_comp, R'.map_comp, hθz, hz, G.map_comp, G.map_comp, hGu]
    simp only [Category.assoc]
    rw [reassoc_of% hkey, hun]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  have hR : ∀ {X X' : CY'} (f : X ⟶ X'), R'.map (c • f) = c • R'.map f := fun f => by
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul,
      Functor.map_nsmul]
  refine ⟨c • (cY.hom ≫ F.map z ≫ e.inv ≫ L'.map (a₂ ≫ eP.inv)), ?_, ?_⟩
  · rw [hR, hres, ← Linear.smul_comp, hw]
  · have hx : transport G a₂ (θ.hom.app ΛY ≫ R'.map cY.inv) m
        (γ.comp (Ext.mk₀ rn.inv) (add_zero m)) =
        transport G a₂ (G.map rn.inv ≫ θ.hom.app ΛY ≫ R'.map cY.inv) m γ := by
      rw [transport_apply, transport_apply, sandwich_apply, sandwich_apply,
        Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero,
        Ext.mk₀_comp_mk₀]
    have hy : transport G a₂ (G.map rn.inv ≫ θ.hom.app ΛY ≫ R'.map cY.inv) m γ =
        sandwich (a₂ ≫ eP.inv) (cU.hom ≫ G.map rn.inv ≫ θ.hom.app ΛY ≫ R'.map cY.inv) m
          (transport G eP.hom cU.inv m γ) := by
      rw [sandwich_transport, Category.assoc, eP.inv_hom_id, Category.comp_id,
        cU.inv_hom_id_assoc]
    have H : (Ext.mk₀ (cY.hom ≫ F.map z ≫ e.inv)).comp (Stacks.ExtAdjunction.extMap adj' P' ΛY' m
        (sandwich (a₂ ≫ eP.inv) (c • rn'.inv) m γ')) (zero_add m) =
        (Ext.mk₀ (c • (cY.hom ≫ F.map z ≫ e.inv ≫ L'.map (a₂ ≫ eP.inv)))).comp
          (Stacks.ExtAdjunction.extMap adj' P' ΛY' m (γ'.comp (Ext.mk₀ rn'.inv) (add_zero m)))
          (zero_add m) := by
      rw [extMap_sandwich, Ext.mk₀_smul, Ext.comp_smul, extMap_smul_zmod, Ext.comp_smul,
        Ext.comp_smul, Ext.mk₀_smul, Ext.smul_comp, Ext.mk₀_comp_mk₀_assoc]
      simp only [Category.assoc]
    rw [transport_mk₀_comp, ← Category.comp_id (cY.hom ≫ F.map z), ← e.inv_hom_id,
      ← Category.assoc (cY.hom ≫ F.map z), Category.assoc cY.hom, transport_comp_left,
      transport_extMap adj adj' F G θ e.hom cY.inv, ← ha₂, hx, hy, hγ, hv, map_nsmul, map_nsmul,
      ← H,
      ← Nat.cast_smul_eq_nsmul (ZMod N), ← Nat.cast_smul_eq_nsmul (ZMod N), Ext.comp_smul]

end Abstract

section Flag

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable {N : ℕ} {U U' : Scheme.{u}} (g : U' ⟶ U)

/-- **The canonical maps `Λ ⟶ E_0 ⋯ E_{d-1} Λ` are compatible with inverse image.** -/
theorem flagUnit_comp_flagSheafIso : ∀ {d : ℕ} (D : Fin d → DivisorDatum U)
    (D' : Fin d → DivisorDatum U') (gV : ∀ m, (D' m).V ⟶ (D m).V)
    (hV : ∀ m, (D' m).j ≫ g = gV m ≫ (D m).j) (gW : ∀ m, (D' m).W ⟶ (D m).W)
    (hW : ∀ m, (D' m).i ≫ g = gW m ≫ (D m).i),
    flagUnit (N := N) D' ≫ (flagSheafIso N g D D' gV hV gW hW).hom =
      (constantInverseImageIso (ZMod N) g).hom ≫
        (etaleModuleInverseImage.{u, 0} (ZMod N) g).map (flagUnit (N := N) D)
  | 0, _, _, _, _, _, _ => by
    change 𝟙 _ ≫ (constantInverseImageIso (ZMod N) g).hom =
      (constantInverseImageIso (ZMod N) g).hom ≫
        (etaleModuleInverseImage.{u, 0} (ZMod N) g).map (𝟙 _)
    rw [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
  | d + 1, D, D', gV, hV, gW, hW => by
    have ih := flagUnit_comp_flagSheafIso (fun m => D m.succ) (fun m => D' m.succ)
      (fun m => gV m.succ) (fun m => hV m.succ) (fun m => gW m.succ) (fun m => hW m.succ)
    set E := closedRestriction (N := N) (D 0).i
    set E' := closedRestriction (N := N) (D' 0).i
    set G := etaleModuleInverseImage.{u, 0} (ZMod N) g
    set c := constantInverseImageIso (ZMod N) g
    set β := closedRestrictionInverseImageIso (ZMod N) g (D 0).i (D 0).j (D 0).range_eq (D' 0).i
      (D' 0).j (D' 0).range_eq (gW 0) (hW 0) (gV 0) (hV 0)
    set f := flagUnit (N := N) (fun m => D m.succ)
    set f' := flagUnit (N := N) (fun m => D' m.succ)
    set e := flagSheafIso N g (fun m => D m.succ) (fun m => D' m.succ) (fun m => gV m.succ)
      (fun m => hV m.succ) (fun m => gW m.succ) (fun m => hW m.succ)
    set u := (etaleModuleInverseImageAdj.{u, 0} (ZMod N) (D 0).i).unit
    set u' := (etaleModuleInverseImageAdj.{u, 0} (ZMod N) (D' 0).i).unit
    have hb :
        G.map (u.app (unitSheaf N)) ≫ (β.app (unitSheaf N)).hom = u'.app (G.obj (unitSheaf N)) :=
      inverseImage_map_unit_comp_closedRestrictionInverseImageIsoApp_hom (ZMod N) g (D 0).i (D 0).j
        (D 0).range_eq (D' 0).i (D' 0).j (D' 0).range_eq (gW 0) (hW 0) (gV 0) (hV 0) _
    have natβ : G.map (E.map f) ≫ (β.app (flagSheaf (N := N) (fun m => D m.succ))).hom =
        (β.app (unitSheaf N)).hom ≫ E'.map (G.map f) := β.hom.naturality f
    have natu : c.hom ≫ u'.app (G.obj (unitSheaf N)) = u'.app (unitSheaf N) ≫ E'.map c.hom :=
      u'.naturality c.hom
    change (u'.app (unitSheaf N) ≫ E'.map f') ≫ (E'.map e.hom ≫
        (β.app (flagSheaf (N := N) (fun m => D m.succ))).inv) =
      c.hom ≫ G.map (u.app (unitSheaf N) ≫ E.map f)
    rw [← Category.assoc, Category.assoc (u'.app _), ← E'.map_comp, Iso.comp_inv_eq]
    calc u'.app (unitSheaf N) ≫ E'.map (f' ≫ e.hom)
        = (u'.app (unitSheaf N) ≫ E'.map c.hom) ≫ E'.map (G.map f) := by
          rw [ih, E'.map_comp, Category.assoc]
      _ = c.hom ≫ (G.map (u.app (unitSheaf N)) ≫ (β.app (unitSheaf N)).hom) ≫ E'.map (G.map f) := by
          rw [← natu, hb, Category.assoc]
      _ = (c.hom ≫ G.map (u.app (unitSheaf N) ≫ E.map f)) ≫
            (β.app (flagSheaf (N := N) (fun m => D m.succ))).hom := by
          rw [Category.assoc, ← natβ, G.map_comp]
          simp only [Category.assoc]

end Flag

section Point

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable {N : ℕ}

/-- The comparison `j⁻¹ ∘ g⁻¹ ≅ g_V⁻¹ ∘ j⁻¹` around a square `j' ≫ g = g_V ≫ j` of an open
immersion. -/
def etaleRestrictionInverseImageIso {V U V' U' : Scheme.{u}} (j : V ⟶ U) [IsOpenImmersion j]
    (j' : V' ⟶ U') [IsOpenImmersion j'] (g : U' ⟶ U) (gV : V' ⟶ V) (h : j' ≫ g = gV ≫ j) :
    etaleModuleRestriction.{u, 0} (ZMod N) j ⋙ etaleModuleInverseImage.{u, 0} (ZMod N) gV ≅
      etaleModuleInverseImage.{u, 0} (ZMod N) g ⋙ etaleModuleRestriction.{u, 0} (ZMod N) j' :=
  Functor.isoWhiskerRight (etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod N) j).symm _ ≪≫
    (etaleModuleInverseImageCompIso.{u, 0} (ZMod N) gV j).symm ≪≫
    eqToIso (congrArg (etaleModuleInverseImage.{u, 0} (ZMod N)) h.symm) ≪≫
    etaleModuleInverseImageCompIso.{u, 0} (ZMod N) j' g ≪≫
    Functor.isoWhiskerLeft _ (etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod N) j')

end Point

section PointClass

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable {k : Type u} [Field k] {N : ℕ} {ζ : k} (hζ : IsPrimitiveRoot ζ N) (hN : IsUnit (N : k))
  {Y U U' : Scheme.{u}} (fY : Y ⟶ Spec (.of k)) (π : Y ⟶ Y) (hπ : π ≫ fY = fY) (n : U ⟶ Y)
  [IsOpenImmersion n] (n' : U' ⟶ Y) [IsOpenImmersion n'] (g : U' ⟶ U) (sq : IsPullback g n' n π)
  {d : ℕ} (D : Fin d → DivisorDatum U) (D' : Fin d → DivisorDatum U')
  (gV : ∀ m, (D' m).V ⟶ (D m).V) (hV : ∀ m, (D' m).j ≫ g = gV m ≫ (D m).j)
  (gW : ∀ m, (D' m).W ⟶ (D m).W) (hW : ∀ m, (D' m).i ≫ g = gW m ≫ (D m).i)

/-- The identification `n'_!(E'_0 ⋯ Λ_{U'}) ≅ π⁻¹ n_!(E_0 ⋯ Λ_U)`. -/
def pointSheafIso :
    (etaleModuleExtensionByZero.{u, 0} (ZMod N) n').obj (flagSheaf (N := N) D') ≅
      (etaleModuleInverseImage.{u, 0} (ZMod N) π).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod N) n).obj (flagSheaf (N := N) D)) :=
  (etaleModuleExtensionByZero.{u, 0} (ZMod N) n').mapIso (flagSheafIso N g D D' gV hV gW hW) ≪≫
    (etaleModuleInverseImageExtensionByZeroIso (ZMod N) sq).app (flagSheaf (N := N) D)

include hζ hπ sq hV hW in
/-- **The Kummer point class under inverse image along `π`.** Let `π : Y ⟶ Y` be a morphism over
`k`, `n : U ⟶ Y` an open immersion with preimage `n' : U' ⟶ Y` (`sq` cartesian), and `D`, `D'`
flags of divisor data on `U` and `U'` with `g(V'_m) ⊆ V_m`, `g(W'_m) ⊆ W_m` and
`g^♯ a_m = a'_m ^ q`. Then for every `z` adapted to the canonical map of `D`, the restriction
along `π` of the Kummer point class of `(D, z)` is `q^d` times the Kummer point class of `D'`
through some `z'` adapted to the canonical map of `D'`. -/
theorem constantExtRestriction_kummerPointClass [NeZero N] [PreconnectedSpace U']
    [∀ m, PreconnectedSpace (D' m).V] (q : ℕ)
    (ha : ∀ m, Units.map (gV m).appTop.hom (D m).a = (D' m).a ^ q)
    (z : unitSheaf (X := Y) N ⟶
      (etaleModuleExtensionByZero.{u, 0} (ZMod N) n).obj (flagSheaf (N := N) D))
    (hz : IsAdapted n (flagUnit (N := N) D) z) :
    ∃ z', IsAdapted n' (flagUnit (N := N) D') z' ∧
      constantExtRestriction (ZMod N) π (2 * d) (kummerPointClass hζ hN fY n D z) =
        (q ^ d) • kummerPointClass hζ hN fY n' D' z' := by
  have := etaleModules_enoughInjectives.{u, 0} (ZMod N) Y
  have := etaleModules_enoughInjectives.{u, 0} (ZMod N) U
  have := etaleModules_enoughInjectives.{u, 0} (ZMod N) U'
  have hg : g ≫ n ≫ fY = n' ≫ fY := by rw [← Category.assoc, sq.w, Category.assoc, hπ]
  have hK3 := transport_kummerFlagClass hζ hN (n ≫ fY) (n' ≫ fY) g hg q D D' gV hV gW hW ha
  rw [kummerFlagClassPow_eq] at hK3
  have hT : constantExtRestriction (ZMod N) π (2 * d) (kummerPointClass hζ hN fY n D z) =
      transport (etaleModuleInverseImage.{u, 0} (ZMod N) π) (constantInverseImageIso (ZMod N) π).hom
        (constantInverseImageIso (ZMod N) π).inv (2 * d) (kummerPointClass hζ hN fY n D z) := by
    rw [constantExtRestriction_apply, Ext.comp_assoc_of_third_deg_zero]
    rfl
  rw [hT]
  exact transport_pointClass (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) n)
    (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) n') _ _
    (etaleRestrictionInverseImageIso (N := N) n n' π g sq.w.symm)
    (pointSheafIso (N := N) π n n' g sq D D' gV hV gW hW) (constantInverseImageIso (ZMod N) π)
    (constantInverseImageIso (ZMod N) g) (restrictionUnitSheafIso (N := N) n)
    (restrictionUnitSheafIso (N := N) n') (flagSheafIso N g D D' gV hV gW hW)
    (flagUnit (N := N) D) (flagUnit (N := N) D')
    (flagUnit_comp_flagSheafIso (N := N) g D D' gV hV gW hW)
    _ _ _ hK3 (fun w => exists_eq_smul_id w) z hz

end PointClass

end Stacks.EtaleCohomology.KummerFlag

end
