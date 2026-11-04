module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerFlagBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ClosedRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.UnitSheafEndomorphism

/-!
# The Kummer divisor class under inverse image

Let `g : U' ⟶ U` be a morphism of `k`-schemes, `(j : V ⟶ U, i : W ⟶ U, a)` divisor data on `U`
and `(j', i', a')` divisor data on `U'` with `g(V') ⊆ V`, `g(W') ⊆ W` and `a' = g^♯ a`. The
square need not be cartesian: `W'` may be the zero locus of `g^♯ φ = φ'^q`, a thickening of the
zero locus of `φ'`. Then the inverse image of the Kummer divisor class of `a`, read through
`g⁻¹ Λ_U ≅ Λ_{U'}` and `g⁻¹(i_* i⁻¹ Λ_U) ≅ i'_* i'⁻¹ Λ_{U'}`, is the Kummer divisor class of `a'`
(`Stacks.EtaleCohomology.KummerFlag.transport_kummerDivisorClass`).

The class of the sequence of Tag 095L is carried to the class of the sequence on `U'`, the two
sequences being identified by `Stacks.EtaleCohomology.inverseImageExtensionByZeroCounitIso` and
`Stacks.EtaleCohomology.closedRestrictionInverseImageIso`. The second factor, the extension by
zero of the Kummer class, is recognised after restriction to `V'`, where it is the Kummer class
itself and the Kummer class is natural (`constantExtRestriction_kummerUnitClass`). The
identifications of constant sheaves met on the way compose to an endomorphism of `Λ_{V'}`
conjugating the Kummer class by itself and its inverse, which does nothing on a preconnected `V'`
(`Stacks.EtaleCohomology.KummerFlag.sandwich_eq_self_of_comp_eq_id`).

## Main results

* `Stacks.EtaleCohomology.KummerFlag.transport_kummerDivisorClass`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.ExtensionTorsor Stacks.ExtTransport

universe u

namespace Stacks.EtaleCohomology.KummerFlag

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-- `x ↦ a ∘ (x ∘ y) ∘ b` splits through any identification of the middle object. -/
theorem transport_comp {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [HasExt C] [HasExt D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {A X B : C} {A' X' B' : D} (a : A' ⟶ F.obj A)
    (e : X' ≅ F.obj X) (b : F.obj B ⟶ B') {m n p : ℕ} (x : Ext A X m) (y : Ext X B n)
    (h : m + n = p) :
    transport F a b p (x.comp y h) =
      (transport F a e.inv m x).comp (transport F e.hom b n y) h := by
  simp only [transport_apply, sandwich_apply, Ext.mapExactFunctor_comp]
  rw [Ext.comp_assoc_of_third_deg_zero]
  symm
  rw [Ext.comp_assoc (Ext.mk₀ a) _ _ (zero_add m) h (by omega), Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]

/-- **Transport along isomorphic functors**: transport along `F'` is transport along `F` with
the ends composed with the components of `θ : F ≅ F'`. -/
theorem transport_iso {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [HasExt C] [HasExt D] [EnoughInjectives C] {F F' : C ⥤ D} [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F'.Additive]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F'] (θ : F ≅ F') {A B : C} {A' B' : D}
    (a : A' ⟶ F'.obj A) (b : F'.obj B ⟶ B') (n : ℕ) (x : Ext A B n) :
    transport F' a b n x = transport F (a ≫ θ.inv.app A) (θ.hom.app B ≫ b) n x := by
  have hθ := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor θ.hom A n x
  have hx :
      x.mapExactFunctor F' = sandwich (θ.inv.app A) (θ.hom.app B) n (x.mapExactFunctor F) := by
    rw [sandwich_apply, ← hθ, ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      ← NatTrans.comp_app, θ.inv_hom_id, NatTrans.id_app, Ext.mk₀_id_comp]
  rw [transport_apply, hx, sandwich_sandwich, ← transport_apply]

variable {k : Type u} [Field k] {N : ℕ} {ζ : k} (hζ : IsPrimitiveRoot ζ N) (hN : IsUnit (N : k))
  {U U' : Scheme.{u}} (fU : U ⟶ Spec (.of k)) (fU' : U' ⟶ Spec (.of k)) (g : U' ⟶ U)
  (hg : g ≫ fU = fU') (D : DivisorDatum U) (D' : DivisorDatum U') (gV : D'.V ⟶ D.V)
  (hV : D'.j ≫ g = gV ≫ D.j) (gW : D'.W ⟶ D.W) (hW : D'.i ≫ g = gW ≫ D.i)

/-- The identification `j'_! j'⁻¹ Λ_{U'} ≅ g⁻¹(j_! j⁻¹ Λ_U)` of the first terms of the sequences
of Tag 095L. -/
def divisorFirstIso :
    (divisorShortComplex (N := N) D'.j D'.i D'.range_eq).X₁ ≅
      (etaleModuleInverseImage.{u, 0} (ZMod N) g).obj
        (divisorShortComplex (N := N) D.j D.i D.range_eq).X₁ :=
  (etaleModuleExtensionByZero.{u, 0} (ZMod N) D'.j).mapIso
      ((etaleModuleRestriction.{u, 0} (ZMod N) D'.j).mapIso
        (constantInverseImageIso (ZMod N) g)) ≪≫
    (inverseImageExtensionByZeroCounitIso (ZMod N) g D.i D.j D.range_eq D'.i D'.j D'.range_eq
      gW hW gV hV (unitSheaf N)).symm

/-- The identification `i'_* i'⁻¹ Λ_{U'} ≅ g⁻¹(i_* i⁻¹ Λ_U)` of the third terms. -/
def divisorThirdIso :
    (divisorShortComplex (N := N) D'.j D'.i D'.range_eq).X₃ ≅
      (etaleModuleInverseImage.{u, 0} (ZMod N) g).obj
        (divisorShortComplex (N := N) D.j D.i D.range_eq).X₃ :=
  (closedRestrictionFunctor (ZMod N) D'.i).mapIso (constantInverseImageIso (ZMod N) g) ≪≫
    (closedRestrictionInverseImageIsoApp (ZMod N) g D.i D.j D.range_eq D'.i D'.j D'.range_eq
      gW hW gV hV (unitSheaf N)).symm

/-- `divisorFirstIso` is compatible with the counits `j_! j⁻¹ Λ ⟶ Λ`. -/
theorem divisorFirstIso_hom_comp :
    (divisorFirstIso (N := N) g D D' gV hV gW hW).hom ≫
        (etaleModuleInverseImage.{u, 0} (ZMod N) g).map
          ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) D.j).counit.app (unitSheaf N)) =
      (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) D'.j).counit.app (unitSheaf N) ≫
        (constantInverseImageIso (ZMod N) g).hom := by
  have h1 := inverseImageExtensionByZeroCounitIso_hom_comp_counit (ZMod N) g D.i D.j D.range_eq
    D'.i D'.j D'.range_eq gW hW gV hV (unitSheaf N)
  rw [divisorFirstIso, Iso.trans_hom, Category.assoc, Iso.symm_hom, ← h1, Iso.inv_hom_id_assoc]
  exact (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) D'.j).counit.naturality
    (constantInverseImageIso (ZMod N) g).hom

/-- `divisorThirdIso` is compatible with the units `Λ ⟶ i_* i⁻¹ Λ`. -/
theorem comp_divisorThirdIso_hom :
    (constantInverseImageIso (ZMod N) g).hom ≫
        (etaleModuleInverseImage.{u, 0} (ZMod N) g).map
          ((etaleModuleInverseImageAdj.{u, 0} (ZMod N) D.i).unit.app (unitSheaf N)) =
      (etaleModuleInverseImageAdj.{u, 0} (ZMod N) D'.i).unit.app (unitSheaf N) ≫
        (divisorThirdIso (N := N) g D D' gV hV gW hW).hom := by
  have hn : (constantInverseImageIso (ZMod N) g).hom ≫
      (etaleModuleInverseImageAdj.{u, 0} (ZMod N) D'.i).unit.app
        ((etaleModuleInverseImage.{u, 0} (ZMod N) g).obj (unitSheaf N)) =
      (etaleModuleInverseImageAdj.{u, 0} (ZMod N) D'.i).unit.app (unitSheaf N) ≫
        (closedRestrictionFunctor (ZMod N) D'.i).map (constantInverseImageIso (ZMod N) g).hom :=
    (etaleModuleInverseImageAdj.{u, 0} (ZMod N) D'.i).unit.naturality
      (constantInverseImageIso (ZMod N) g).hom
  have hb := inverseImage_map_unit_comp_closedRestrictionInverseImageIsoApp_hom (ZMod N) g D.i D.j
    D.range_eq D'.i D'.j D'.range_eq gW hW gV hV (unitSheaf N)
  rw [divisorThirdIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, ← Category.assoc, ← hn,
    ← hb, Category.assoc, Category.assoc]
  simp only [Iso.symm_hom, Iso.hom_inv_id, Category.comp_id]

/-- The identification of the two sequences of Tag 095L. -/
def divisorShortComplexHom :
    divisorShortComplex (N := N) D'.j D'.i D'.range_eq ⟶
      (divisorShortComplex (N := N) D.j D.i D.range_eq).map
        (etaleModuleInverseImage.{u, 0} (ZMod N) g) where
  τ₁ := (divisorFirstIso (N := N) g D D' gV hV gW hW).hom
  τ₂ := (constantInverseImageIso (ZMod N) g).hom
  τ₃ := (divisorThirdIso (N := N) g D D' gV hV gW hW).hom
  comm₁₂ := divisorFirstIso_hom_comp (N := N) g D D' gV hV gW hW
  comm₂₃ := comp_divisorThirdIso_hom (N := N) g D D' gV hV gW hW

/-- **The class of the sequence of Tag 095L is natural.** -/
theorem transport_extClass :
    transport (etaleModuleInverseImage.{u, 0} (ZMod N) g)
        (divisorThirdIso (N := N) g D D' gV hV gW hW).hom
        (divisorFirstIso (N := N) g D D' gV hV gW hW).inv 1
        (divisorShortComplex_shortExact (N := N) D.j D.i D.range_eq).extClass =
      (divisorShortComplex_shortExact (N := N) D'.j D'.i D'.range_eq).extClass := by
  have hS := divisorShortComplex_shortExact (N := N) D.j D.i D.range_eq
  have hS' := divisorShortComplex_shortExact (N := N) D'.j D'.i D'.range_eq
  have key := hS'.extClass_naturality (hS.map_of_exact (etaleModuleInverseImage.{u, 0} (ZMod N) g))
    (divisorShortComplexHom g D D' gV hV gW hW)
  have key' : (Ext.mk₀ (divisorThirdIso (N := N) g D D' gV hV gW hW).hom).comp
      (hS.map_of_exact (etaleModuleInverseImage.{u, 0} (ZMod N) g)).extClass (zero_add 1) =
      hS'.extClass.comp (Ext.mk₀ (divisorFirstIso (N := N) g D D' gV hV gW hW).hom) (add_zero 1) :=
    key.symm
  rw [transport_apply, Ext.mapExactFunctor_extClass, sandwich_apply,
    ← Ext.comp_assoc_of_third_deg_zero, key', Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    Iso.hom_inv_id, Ext.comp_mk₀_id]

section Kummer

variable {V : Scheme.{u}} {U₀ : Scheme.{u}} (f₀ : U₀ ⟶ Spec (.of k)) (j : V ⟶ U₀)
  [IsOpenImmersion j]

/-- The second factor of the Kummer divisor class: `j_!(κ(a))` followed by the counit
`j_! j⁻¹ Λ ⟶ Λ`, i.e. the image of `κ(a)` under the adjunction `j_! ⊣ j⁻¹`. -/
def kummerExtensionClass (a : (Γ(V, ⊤))ˣ) :
    Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj
      ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj (unitSheaf (X := U₀) N)))
      (unitSheaf (X := U₀) N) 1 :=
  Stacks.ExtAdjunction.extMap (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) j) _ _ 1
    (sandwich (restrictionUnitSheafIso (N := N) j).hom (restrictionUnitSheafIso (N := N) j).inv 1
      (kummerUnitClass hζ hN (j ≫ f₀) a))

/-- The Kummer divisor class is the class of the sequence of Tag 095L composed with
`kummerExtensionClass`. -/
theorem kummerDivisorClass_eq {W₀ : Scheme.{u}} (i : W₀ ⟶ U₀) [IsClosedImmersion i]
    (hij : Set.range j.base = (Set.range i.base)ᶜ) (a : (Γ(V, ⊤))ˣ) :
    kummerDivisorClass hζ hN f₀ j i hij a =
      (divisorShortComplex_shortExact (N := N) j i hij).extClass.comp
        (kummerExtensionClass hζ hN f₀ j a) (by norm_num) :=
  rfl

/-- The class `kummerExtensionClass` of `a ^ m` is `m` times that of `a`. -/
theorem kummerExtensionClass_pow (a : (Γ(V, ⊤))ˣ) (m : ℕ) :
    kummerExtensionClass hζ hN f₀ j (a ^ m) = m • kummerExtensionClass hζ hN f₀ j a := by
  rw [kummerExtensionClass, kummerExtensionClass, kummerUnitClass_pow, map_nsmul, map_nsmul]

/-- The Kummer divisor class of `a ^ m` is `m` times that of `a`. -/
theorem kummerDivisorClass_pow {W₀ : Scheme.{u}} (i : W₀ ⟶ U₀) [IsClosedImmersion i]
    (hij : Set.range j.base = (Set.range i.base)ᶜ) (a : (Γ(V, ⊤))ˣ) (m : ℕ) :
    kummerDivisorClass hζ hN f₀ j i hij (a ^ m) = m • kummerDivisorClass hζ hN f₀ j i hij a := by
  rw [kummerDivisorClass_eq, kummerDivisorClass_eq, kummerExtensionClass_pow]
  exact map_nsmul ((divisorShortComplex_shortExact (N := N) j i hij).extClass.precomp _
    (by norm_num)) m _

end Kummer

/-- The comparison `j⁻¹ ∘ g⁻¹ ≅ g_V⁻¹ ∘ j⁻¹` of restrictions and inverse images around the
square `j' ≫ g = g_V ≫ j`. -/
def restrictionInverseImageIso :
    etaleModuleRestriction.{u, 0} (ZMod N) D.j ⋙ etaleModuleInverseImage.{u, 0} (ZMod N) gV ≅
      etaleModuleInverseImage.{u, 0} (ZMod N) g ⋙ etaleModuleRestriction.{u, 0} (ZMod N) D'.j :=
  Functor.isoWhiskerRight (etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod N) D.j).symm _ ≪≫
    (etaleModuleInverseImageCompIso.{u, 0} (ZMod N) gV D.j).symm ≪≫
    eqToIso (congrArg (etaleModuleInverseImage.{u, 0} (ZMod N)) hV.symm) ≪≫
    etaleModuleInverseImageCompIso.{u, 0} (ZMod N) D'.j g ≪≫
    Functor.isoWhiskerLeft _ (etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod N) D'.j)

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- `y ↦ unit ∘ R(y)` is a left inverse of the adjunction map of `L ⊣ R`. -/
private theorem transport_unit_extMap_aux {C D : Type*} [Category C] [Abelian C] [Category D]
    [Abelian D] [HasExt C] [HasExt D] [EnoughInjectives C] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (A : C) (B : D) {n : ℕ} (e : Ext A (R.obj B) n) :
    transport R (adj.unit.app A) (𝟙 _) n (Stacks.ExtAdjunction.extMap adj A B n e) = e := by
  rw [transport_apply, sandwich_apply, Ext.comp_mk₀_id]
  exact unit_comp_mapExactFunctor_extMap adj A B n e

/-- `y ↦ unit ∘ R(y)` is injective, being left inverse to the adjunction map of `L ⊣ R`. -/
private theorem injective_transport_unit_aux {C D : Type*} [Category C] [Abelian C] [Category D]
    [Abelian D] [HasExt C] [HasExt D] [EnoughInjectives C] [EnoughInjectives D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) [L.Additive] [PreservesFiniteLimits L]
    [PreservesFiniteColimits L] [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] (A : C) (B : D) (n : ℕ) :
    Function.Injective (transport R (adj.unit.app A) (𝟙 (R.obj B)) n) := by
  intro y₁ y₂ h
  have hb := Stacks.ExtAdjunction.extMap_bijective adj A B n
  obtain ⟨e₁, rfl⟩ := hb.2 y₁
  obtain ⟨e₂, rfl⟩ := hb.2 y₂
  rw [transport_unit_extMap_aux, transport_unit_extMap_aux] at h
  rw [h]

/-- `y ↦ unit ∘ j⁻¹(y)` is a left inverse of the adjunction map of `j_! ⊣ j⁻¹`. -/
theorem transport_unit_extMap {V₀ U₀ : Scheme.{u}} (j : V₀ ⟶ U₀) [IsOpenImmersion j]
    (A : EtaleModules.{u, 0} (ZMod N) V₀) (B : EtaleModules.{u, 0} (ZMod N) U₀) {n : ℕ}
    (e : Ext A ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj B) n) :
    transport (etaleModuleRestriction.{u, 0} (ZMod N) j)
        ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) j).unit.app A) (𝟙 _) n
        (Stacks.ExtAdjunction.extMap (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) j) A B n e) =
      e := by
  have := etaleModules_enoughInjectives.{u, 0} (ZMod N) V₀
  exact transport_unit_extMap_aux _ A B e

/-- The map `y ↦ unit ∘ j⁻¹(y)`, the left inverse of the adjunction map of `j_! ⊣ j⁻¹`, is
injective. -/
theorem injective_transport_unit {V₀ U₀ : Scheme.{u}} (j : V₀ ⟶ U₀) [IsOpenImmersion j]
    (A : EtaleModules.{u, 0} (ZMod N) V₀) (B : EtaleModules.{u, 0} (ZMod N) U₀) (n : ℕ) :
    Function.Injective (transport (etaleModuleRestriction.{u, 0} (ZMod N) j)
        ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) j).unit.app A)
        (𝟙 ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj B)) n) := by
  have := etaleModules_enoughInjectives.{u, 0} (ZMod N) V₀
  have := etaleModules_enoughInjectives.{u, 0} (ZMod N) U₀
  exact injective_transport_unit_aux _ A B n

section Abstract

variable {CU CU' CV CV' : Type*} [Category CU] [Abelian CU] [Category CU'] [Abelian CU']
  [Category CV] [Abelian CV] [Category CV'] [Abelian CV'] [HasExt CU] [HasExt CU'] [HasExt CV]
  [HasExt CV'] [EnoughInjectives CU] [EnoughInjectives CU'] [EnoughInjectives CV]
  [EnoughInjectives CV']
  {L : CV ⥤ CU} {R : CU ⥤ CV} (adj : L ⊣ R) {L' : CV' ⥤ CU'} {R' : CU' ⥤ CV'} (adj' : L' ⊣ R')
  [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [L'.Additive] [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [R'.Additive] [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  (G : CU ⥤ CU') [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (GV : CV ⥤ CV') [GV.Additive] [PreservesFiniteLimits GV] [PreservesFiniteColimits GV]
  (θ : R ⋙ GV ≅ G ⋙ R') {O : CU} {O' : CU'} {P : CV} {P' : CV'}
  (c : O' ≅ G.obj O) (cV : P' ≅ GV.obj P) (r : R.obj O ≅ P) (r' : R'.obj O' ≅ P')
  (τ₁ : L'.obj (R'.obj O') ≅ G.obj (L.obj (R.obj O)))

include adj adj' θ in
/-- **The adjunction map is natural, abstractly.** Given a comparison `θ` of the two composites
of restrictions and inverse images, an identification `τ₁` of the first terms compatible with the
counits, and a class `κ'` transported from `κ` and unchanged by conjugation by endomorphisms of
`P'`, the image of `κ` under `L ⊣ R` is transported to the image of `κ'` under `L' ⊣ R'`. -/
theorem transport_extMap_of_conj [IsIso (adj.unit.app (R.obj O))]
    (hτ : τ₁.hom ≫ G.map (adj.counit.app O) = adj'.counit.app O' ≫ c.hom)
    (κ : Ext P P 1) (κ' : Ext P' P' 1) (hK : transport GV cV.hom cV.inv 1 κ = κ')
    (hconj : ∀ w w' : P' ⟶ P', w' ≫ w = 𝟙 _ → sandwich w' w 1 κ' = κ') :
    transport G τ₁.hom c.inv 1
        (Stacks.ExtAdjunction.extMap adj (R.obj O) O 1 (sandwich r.hom r.inv 1 κ)) =
      Stacks.ExtAdjunction.extMap adj' (R'.obj O') O' 1 (sandwich r'.hom r'.inv 1 κ') := by
  have hinj := injective_transport_unit_aux adj' (R'.obj O') O' 1
  have hinv : inv (adj.unit.app (R.obj O)) = R.map (adj.counit.app O) :=
    IsIso.inv_eq_of_hom_inv_id (adj.right_triangle_components O)
  have hθ : R'.map (G.map (adj.counit.app O)) ≫ θ.inv.app O =
      θ.inv.app (L.obj (R.obj O)) ≫ GV.map (R.map (adj.counit.app O)) :=
    θ.inv.naturality (adj.counit.app O)
  have hfirst : τ₁.hom ≫ G.map (adj.counit.app O) ≫ c.inv = adj'.counit.app O' := by
    rw [← Category.assoc, hτ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hC3 : ((adj'.unit.app (R'.obj O') ≫ R'.map τ₁.hom) ≫ θ.inv.app (L.obj (R.obj O)) ≫
      GV.map (inv (adj.unit.app (R.obj O)))) ≫ θ.hom.app O ≫ R'.map c.inv = 𝟙 _ := by
    simp only [Category.assoc, hinv]
    rw [← Category.assoc (θ.inv.app (L.obj (R.obj O))), ← hθ, Category.assoc,
      Iso.inv_hom_id_app_assoc, ← R'.map_comp, ← R'.map_comp, hfirst]
    exact adj'.right_triangle_components O'
  apply hinj
  conv_rhs => rw [transport_unit_extMap_aux]
  have hstep : ∀ (P₀ : R'.obj O' ⟶ (R ⋙ GV).obj (L.obj (R.obj O)))
      (Q₀ : (R ⋙ GV).obj O ⟶ R'.obj O') (a₂ : R'.obj O' ⟶ GV.obj (R.obj O))
      (b₂ : GV.obj (R.obj O) ⟶ R'.obj O') (_ : a₂ ≫ GV.map (adj.unit.app (R.obj O)) = P₀)
      (_ : b₂ = Q₀) (y : Ext (L.obj (R.obj O)) O 1),
      transport (R ⋙ GV) P₀ Q₀ 1 y =
        transport GV a₂ b₂ 1 (transport R (adj.unit.app (R.obj O)) (𝟙 _) 1 y) := by
    intro P₀ Q₀ a₂ b₂ h₁ h₂ y
    subst h₁ h₂
    rw [transport_transport R GV (R ⋙ GV) (Iso.refl _)]
    simp
  set a₂ := (adj'.unit.app (R'.obj O') ≫ R'.map τ₁.hom) ≫ θ.inv.app (L.obj (R.obj O)) ≫
    GV.map (inv (adj.unit.app (R.obj O))) with ha₂
  set b₂ := θ.hom.app O ≫ R'.map c.inv with hb₂
  rw [transport_transport G R' (G ⋙ R') (Iso.refl _), transport_iso θ,
    hstep _ _ a₂ b₂ (by simp [ha₂]) (by simp [hb₂]), transport_unit_extMap_aux, transport_sandwich]
  have hsw : transport GV (a₂ ≫ GV.map r.hom) (GV.map r.inv ≫ b₂) 1 κ =
      sandwich ((a₂ ≫ GV.map r.hom) ≫ cV.inv) (cV.hom ≫ GV.map r.inv ≫ b₂) 1
        (transport GV cV.hom cV.inv 1 κ) := by
    rw [sandwich_transport]
    simp
  rw [hsw, hK]
  have hw : (r'.inv ≫ (a₂ ≫ GV.map r.hom) ≫ cV.inv) ≫ (cV.hom ≫ GV.map r.inv ≫ b₂) ≫ r'.hom =
      𝟙 _ := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← GV.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
      ← Category.assoc a₂, hC3, Category.id_comp, Iso.inv_hom_id]
  conv_rhs => rw [← hconj _ _ hw]
  rw [sandwich_sandwich]
  congr 1
  simp

end Abstract

include hζ hg in
/-- **The extension by zero of the Kummer class is natural.** -/
theorem transport_kummerExtensionClass [NeZero N] [PreconnectedSpace D'.V] :
    transport (etaleModuleInverseImage.{u, 0} (ZMod N) g)
        (divisorFirstIso (N := N) g D D' gV hV gW hW).hom (constantInverseImageIso (ZMod N) g).inv 1
        (kummerExtensionClass hζ hN fU D.j D.a) =
      kummerExtensionClass hζ hN fU' D'.j (Units.map gV.appTop.hom D.a) := by
  have := etaleModules_enoughInjectives.{u, 0} (ZMod N) U
  have := etaleModules_enoughInjectives.{u, 0} (ZMod N) U'
  have := etaleModules_enoughInjectives.{u, 0} (ZMod N) D.V
  have := etaleModules_enoughInjectives.{u, 0} (ZMod N) D'.V
  have hfV : gV ≫ D.j ≫ fU = D'.j ≫ fU' := by
    rw [← Category.assoc, ← hV, Category.assoc, hg]
  have hK1 := constantExtRestriction_kummerUnitClass hζ hN (D.j ≫ fU) (D'.j ≫ fU') gV hfV D.a
  rw [constantExtRestriction_apply, Ext.comp_assoc_of_third_deg_zero, ← sandwich_apply,
    ← transport_apply] at hK1
  exact transport_extMap_of_conj (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) D.j)
    (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) D'.j) _ _
    (restrictionInverseImageIso (N := N) g D D' gV hV) (constantInverseImageIso (ZMod N) g)
    (constantInverseImageIso (ZMod N) gV) (restrictionUnitSheafIso (N := N) D.j)
    (restrictionUnitSheafIso (N := N) D'.j) (divisorFirstIso (N := N) g D D' gV hV gW hW)
    (divisorFirstIso_hom_comp (N := N) g D D' gV hV gW hW) _ _ hK1
    (fun _ _ h => sandwich_eq_self_of_comp_eq_id h _)

include hζ hg in
/-- **The Kummer divisor class is natural under inverse image**: for divisor data `D` on `U` and
`D'` on `U'` with `g(V') ⊆ V`, `g(W') ⊆ W`, the inverse image along `g` of `δ(a)` is `δ(g^♯ a)`. -/
theorem transport_kummerDivisorClass [NeZero N] [PreconnectedSpace D'.V] :
    transport (etaleModuleInverseImage.{u, 0} (ZMod N) g)
        (divisorThirdIso (N := N) g D D' gV hV gW hW).hom (constantInverseImageIso (ZMod N) g).inv 2
        (kummerDivisorClass hζ hN fU D.j D.i D.range_eq D.a) =
      kummerDivisorClass hζ hN fU' D'.j D'.i D'.range_eq (Units.map gV.appTop.hom D.a) := by
  rw [kummerDivisorClass_eq, kummerDivisorClass_eq,
    transport_comp _ _ (divisorFirstIso (N := N) g D D' gV hV gW hW),
    transport_extClass, transport_kummerExtensionClass hζ hN fU fU' g hg D D' gV hV gW hW]

end Stacks.EtaleCohomology.KummerFlag

end
