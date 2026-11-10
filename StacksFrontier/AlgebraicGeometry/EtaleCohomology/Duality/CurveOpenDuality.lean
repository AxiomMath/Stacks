module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurvePointDuality

/-!
# Poincaré duality for `ℤ/ℓ` on an open of a smooth proper curve

Let `Y` be a smooth proper curve over an algebraically closed field `k`, `ℓ` a prime invertible
in `k`, `Λ = ℤ/ℓ` and `t : H²(Y, Λ) → Λ` an injective trace. For a nonempty open `V ⊆ Y` whose
complement is a finite set of closed points, duality holds on `Y` at `j_{V!} Λ_V`:

`Ext^i(Λ_Y, j_{V!} Λ_V) × Ext^{2-i}(j_{V!} Λ_V, Λ_Y) → H²(Y, Λ) → Λ`

is perfect, that is `H^i_c(V, Λ) × H^{2-i}(V, Λ) → Λ` is perfect, and
`Ext^q(j_{V!} Λ_V, Λ_Y) = 0` for `q > 2`. This is by induction on the number of missing points:
for `V = Y` it is `Stacks.EtaleCohomology.ExtensionTorsor.isDualityPerfect_unitSheaf`, and removing
a closed point `z` from an open `V'` gives the short exact sequence
`0 → j_{V!} Λ_V → j_{V'!} Λ_{V'} → C_z → 0` with `C_z` the skyscraper of `z`
(`Stacks.EtaleCohomology.exists_shortExact_extensionByZero_sup_stratum`), at which duality holds
(`Stacks.EtaleCohomology.isDualityPerfect_extensionByZero_directImage_point`, from local purity at
`z`); the five lemma `CategoryTheory.Abelian.Ext.isDualityPerfect_X₁` concludes.

## Main results

* `Stacks.EtaleCohomology.isDualityPerfect_extensionByZeroOfRestriction_unitSheaf_of_curve`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

variable {ℓ : ℕ} [Fact ℓ.Prime]

end Stacks.EtaleCohomology

namespace CategoryTheory.Abelian.Ext

/-- If `Ext^q(X₂, Z) = 0` and `Ext^{q+1}(X₃, Z) = 0` for a short exact sequence
`0 → X₁ → X₂ → X₃ → 0`, then `Ext^q(X₁, Z) = 0`. -/
theorem subsingleton_ext_left_X₁_of_shortExact {C : Type*} [Category C] [Abelian C]
    [HasExt.{u + 1} C] {S : ShortComplex C} (hS : S.ShortExact) (Z : C) (q : ℕ)
    (h₂ : Subsingleton (Ext S.X₂ Z q)) (h₃ : Subsingleton (Ext S.X₃ Z (q + 1))) :
    Subsingleton (Ext S.X₁ Z q) := by
  refine ⟨fun a b => ?_⟩
  suffices h : ∀ x : Ext S.X₁ Z q, x = 0 by rw [h a, h b]
  intro x
  obtain ⟨x₂, hx₂⟩ := Ext.contravariant_sequence_exact₁ hS Z x (add_comm 1 q)
    (Subsingleton.elim _ _)
  rw [← hx₂, Subsingleton.elim x₂ 0, Ext.comp_zero]

end CategoryTheory.Abelian.Ext

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

variable {ℓ : ℕ} [Fact ℓ.Prime]

section Helpers

/-- `j_{a!} L|_a ≅ j_{b!} L|_b` for equal étale morphisms `a = b`. -/
theorem nonempty_extensionByZeroOfRestriction_iso_of_eq {U W : Scheme.{u}} (a b : U ⟶ W)
    [Etale a] [Etale b] (h : a = b) (L : EtaleModules.{u, 0} (ZMod ℓ) W) :
    Nonempty ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) a).obj L ≅
      (etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) b).obj L) := by
  subst h
  exact ⟨Iso.refl _⟩

/-- The counit `φ_! φ^{-1} F → F` is an isomorphism for an isomorphism of schemes `φ`. -/
theorem isIso_etaleModuleExtensionByZeroAdj_counit_app_of_isIso_zmod {A B : Scheme.{u}} (φ : A ⟶ B)
    [IsIso φ] (F : EtaleModules.{u, 0} (ZMod ℓ) B) :
    IsIso ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) φ).counit.app F) :=
  isIso_of_isIso_etaleModuleInverseImage_family (ZMod ℓ) (T := fun _ : PUnit.{u + 1} => A)
    (fun _ => φ) (Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨PUnit.unit,
      (inv φ).base x, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩) _
    fun _ => isIso_etaleModuleInverseImage_map_counit_of_factors (ZMod ℓ) φ φ (𝟙 A)
      (Category.id_comp φ) F

/-- `j_! j^{-1} F ≅ W_! W^{-1} F` for an open immersion `j` with image `W`. -/
theorem nonempty_extensionByZeroOfRestriction_iso_opensRange {U W : Scheme.{u}} (j : U ⟶ W)
    [IsOpenImmersion j] (F : EtaleModules.{u, 0} (ZMod ℓ) W) :
    Nonempty ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) j).obj F ≅
      (etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) j.opensRange.ι).obj F) := by
  let φ := j.isoOpensRange
  obtain ⟨e₀⟩ := nonempty_extensionByZeroOfRestriction_iso_of_eq (ℓ := ℓ) j (φ.hom ≫ j.opensRange.ι)
    (Scheme.Hom.isoOpensRange_hom_ι j).symm F
  have := isIso_etaleModuleExtensionByZeroAdj_counit_app_of_isIso_zmod (ℓ := ℓ) φ.hom
    ((etaleModuleRestriction.{u, 0} (ZMod ℓ) j.opensRange.ι).obj F)
  exact ⟨e₀ ≪≫
    (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (φ.hom ≫ j.opensRange.ι)).mapIso
      ((etaleModuleRestrictionCompIso.{u, 0} (ZMod ℓ) φ.hom j.opensRange.ι).app F).symm ≪≫
    (etaleModuleExtensionByZeroCompIso.{u, 0} (ZMod ℓ) φ.hom j.opensRange.ι).app _ ≪≫
    (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j.opensRange.ι).mapIso
      (asIso ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) φ.hom).counit.app _))⟩

/-- `Ext^q(-, Z)` vanishes on `X` if it vanishes on `Y` and `X ⟶ Y` is an isomorphism. -/
private theorem subsingleton_ext_of_isIso_left {C : Type*} [Category C] [Abelian C]
    [HasExt.{u + 1} C] {X Y Z : C} (g : X ⟶ Y) [IsIso g] (q : ℕ) [Subsingleton (Ext Y Z q)] :
    Subsingleton (Ext X Z q) :=
  (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso (Z := Z) g q).2.subsingleton

end Helpers

section Curve

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsProper f]

include f in
/-- **Poincaré duality for `ℤ/ℓ` on an open of a smooth proper curve.** For a nonempty open `V`
of `Y` whose complement is a finite set `S` of closed points, and an injective trace `t` on
`H²(Y, Λ)`, duality holds on `Y` at `j_{V!} Λ_V` and `Ext^q(j_{V!} Λ_V, Λ_Y) = 0` for `q > 2`,
given local purity. -/
theorem isDualityPerfect_extensionByZeroOfRestriction_unitSheaf_of_curve (hℓ : IsUnit (ℓ : k))
    (hpurity : LocalPurity ℓ k) (t : Ext (unitSheaf (X := Y) ℓ) (unitSheaf ℓ) 2 →+ ZMod ℓ)
    (ht : Function.Injective t) (S : Finset Y) (hS : ∀ y ∈ S, IsClosed ({y} : Set Y))
    (V : Y.Opens) (hV : (V : Set Y) = (↑S : Set Y)ᶜ) [Nonempty V] :
    Ext.IsDualityPerfect (unitSheaf (X := Y) ℓ) (unitSheaf ℓ) 2 t
        ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) V.ι).obj (unitSheaf (X := Y) ℓ)) ∧
      ∀ q, 2 < q → Subsingleton (Ext ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ)
        V.ι).obj (unitSheaf (X := Y) ℓ)) (unitSheaf (X := Y) ℓ) q) := by
  classical
  have hp : ℓ.Prime := Fact.out
  have hdim : topologicalKrullDim Y ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  induction S using Finset.induction_on generalizing V with
  | empty =>
    have hVtop : V = ⊤ := by
      ext x
      simp [hV]
    subst hVtop
    have := isIso_etaleModuleExtensionByZeroAdj_counit_app_top (ZMod ℓ) (unitSheaf (X := Y) ℓ)
    let e := asIso ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) (⊤ : Y.Opens).ι).counit.app
      (unitSheaf (X := Y) ℓ))
    refine ⟨Ext.isDualityPerfect_of_iso e.symm (isDualityPerfect_unitSheaf f hℓ t ht),
      fun q hq => ?_⟩
    have : Subsingleton (Ext ((𝟭 _).obj (unitSheaf (X := Y) ℓ)) (unitSheaf (X := Y) ℓ) q) :=
      subsingleton_ext_unitSheaf_of_curve f hdim (unitSheaf (X := Y) ℓ) q hq
    exact subsingleton_ext_of_isIso_left e.hom q
  | insert z s hzs ih =>
    have hzcl : IsClosed ({z} : Set Y) := hS z (Finset.mem_insert_self z s)
    have hscl : ∀ y ∈ s, IsClosed ({y} : Set Y) := fun y hy => hS y (Finset.mem_insert_of_mem hy)
    have hsclosed : IsClosed (↑s : Set Y) := by
      rw [← Set.biUnion_of_singleton (↑s : Set Y)]
      exact s.finite_toSet.isClosed_biUnion fun y hy => hscl y hy
    let V' : Y.Opens := ⟨(↑s : Set Y)ᶜ, hsclosed.isOpen_compl⟩
    have hV'set : (V' : Set Y) = (↑s : Set Y)ᶜ := rfl
    have hVV' : V ≤ V' := by
      intro x hx
      have hx' : x ∈ (V : Set Y) := hx
      rw [hV] at hx'
      change x ∈ (↑s : Set Y)ᶜ
      simp only [Finset.coe_insert, Set.mem_compl_iff, Set.mem_insert_iff, not_or] at hx'
      exact hx'.2
    obtain ⟨x₀, hx₀⟩ := (‹Nonempty V›)
    have : Nonempty V' := ⟨⟨x₀, hVV' hx₀⟩⟩
    obtain ⟨ih₁, ih₂⟩ := ih hscl V' hV'set
    have hzV' : z ∈ V' := hzs
    have hzV : z ∉ V := by
      intro h
      have h' : z ∈ (V : Set Y) := h
      rw [hV] at h'
      simp at h'
    -- the point `z` of `V'`
    let z' : V' := ⟨z, hzV'⟩
    have hz' : IsClosed ({z'} : Set V') := by
      have : ({z'} : Set V') = V'.ι.base ⁻¹' {z} := by
        ext x
        simp only [Set.mem_singleton_iff, Set.mem_preimage, z']
        exact Subtype.ext_iff
      rw [this]
      exact hzcl.preimage V'.ι.base.hom.continuous
    let p := V'.ι ≫ f
    let i := pointOfClosedPoint p z' hz'
    have hip : i ≫ p = 𝟙 _ := pointOfClosedPoint_comp p z' hz'
    have : IsClosedImmersion i := isClosedImmersion_of_comp_eq_id p i hip
    have : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_one_of_isCurve k f
    have : SmoothOfRelativeDimension (0 + 1) p := inferInstance
    have : SmoothOfRelativeDimension 0 (i ≫ p) := by rw [hip]; infer_instance
    obtain ⟨N, hzN, γ, hγ⟩ := hpurity V' (Spec (.of k)) p i 0 1 (Classical.arbitrary _)
    let i' := i ∣_ N
    let n : (N : Scheme) ⟶ Y := N.ι ≫ V'.ι
    have hiN : i ⁻¹ᵁ N = ⊤ := by
      refine eq_top_iff.2 fun a _ => ?_
      change i.base a ∈ N
      rwa [Subsingleton.elim a (Classical.arbitrary _)]
    let g : (i ⁻¹ᵁ N : Scheme) ⟶ Spec (.of k) := (i ⁻¹ᵁ N).ι
    have : IsIso g := isIso_of_isOpenImmersion_of_opensRange_eq_top g
      (by rw [Scheme.Opens.opensRange_ι, hiN])
    have : Nonempty (i ⁻¹ᵁ N) := ⟨(inv g).base (Classical.arbitrary _)⟩
    have : ConnectedSpace (i ⁻¹ᵁ N) := inferInstance
    let eN := unitSheafIsoRestrictionOfIsOpenImmersion (ℓ := ℓ) n
    have hγ' := hγ.comp_mk₀ eN
    have hgi : i' ≫ n = g ≫ (i ≫ V'.ι) := by
      simp only [i', n, g, ← Category.assoc, morphismRestrict_ι]
    have : IsClosedImmersion (i ≫ V'.ι) :=
      isClosedImmersion_of_comp_eq_id f (i ≫ V'.ι) (by rw [Category.assoc]; exact hip)
    have : IsClosedImmersion (i' ≫ n) := by rw [hgi]; infer_instance
    have hiz : ∀ a, (i ≫ V'.ι).base a = z := fun a => by
      rw [Scheme.Hom.comp_apply, show i.base a = z' from pointOfClosedPoint_apply p z' hz' a]
      rfl
    have hrange : Set.range (i' ≫ n).base = {z} := by
      rw [hgi]
      ext y
      simp only [Set.mem_range, Set.mem_singleton_iff, Scheme.Hom.comp_apply]
      constructor
      · rintro ⟨a, rfl⟩
        exact hiz _
      · rintro rfl
        obtain ⟨b⟩ := ‹Nonempty (i ⁻¹ᵁ N)›
        exact ⟨b, hiz _⟩
    have hzn : z ∈ Set.range n.base := by
      obtain ⟨b⟩ := ‹Nonempty (i ⁻¹ᵁ N)›
      refine ⟨i'.base b, ?_⟩
      rw [← Scheme.Hom.comp_apply]
      exact (Set.ext_iff.1 hrange _).1 ⟨b, rfl⟩
    have hnV' : Set.range n.base ⊆ (V' : Set Y) := by
      rintro y ⟨b, rfl⟩
      exact (N.ι.base b).2
    -- duality at the skyscraper of `z`
    let Vz : Y.Opens := ⟨{z}ᶜ, hzcl.isOpen_compl⟩
    have : Nonempty Vz := ⟨⟨x₀, fun h => hzV (by rw [Set.mem_singleton_iff.1 h] at hx₀; exact hx₀)⟩⟩
    have hVzt : Vz ≠ ⊤ := fun h => by
      have : z ∈ Vz := h ▸ trivial
      exact this rfl
    have hiz' : Set.range (i' ≫ n).base = Set.range n.base \ (Vz : Set Y) := by
      rw [hrange]
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_sdiff, Vz]
      change y = z ↔ y ∈ Set.range n.base ∧ ¬ y ∈ ({z}ᶜ : Set Y)
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not]
      exact ⟨fun h => ⟨h ▸ hzn, h⟩, fun h => h.2⟩
    have htopz : Vz ⊔ n.opensRange = ⊤ := by
      refine eq_top_iff.2 fun y _ => ?_
      by_cases hy : y = z
      · exact Or.inr (hy ▸ hzn)
      · exact Or.inl hy
    obtain ⟨hPt₁, hPt₂⟩ := isDualityPerfect_extensionByZero_directImage_point f hℓ t ht n i' g
      _ hγ' Vz hVzt hiz' htopz
    -- the short exact sequence `0 → j_{V!} Λ_V → j_{V'!} Λ_{V'} → C_z → 0`
    have hiV : Set.range (i' ≫ n).base = Set.range n.base \ (V : Set Y) := by
      rw [hrange]
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_sdiff]
      constructor
      · rintro rfl
        exact ⟨hzn, hzV⟩
      · rintro ⟨hy, hyV⟩
        have hyV' := hnV' hy
        rw [hV'set, Set.mem_compl_iff] at hyV'
        have hyV'' : y ∉ (V : Set Y) := hyV
        rw [hV] at hyV''
        simp only [Finset.coe_insert, Set.mem_compl_iff, Set.mem_insert_iff, not_or, not_and,
          not_not] at hyV''
        by_contra hne
        exact hyV' (hyV'' hne)
    obtain ⟨S', hS', ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
      exists_shortExact_extensionByZero_sup_stratum (ZMod ℓ) V n i' hiV (unitSheaf (X := Y) ℓ)
    have hsup : V ⊔ n.opensRange = V' := by
      refine le_antisymm (sup_le hVV' fun y hy => hnV' hy) fun y hy => ?_
      by_cases hyz : y = z
      · exact Or.inr (hyz ▸ hzn)
      · refine Or.inl ?_
        change y ∈ (V : Set Y)
        rw [hV]
        simp only [Finset.coe_insert, Set.mem_compl_iff, Set.mem_insert_iff, not_or]
        exact ⟨hyz, hy⟩
    rw [hsup] at e₂
    have h₂ := Ext.isDualityPerfect_of_iso e₂.symm ih₁
    have h₃ := Ext.isDualityPerfect_of_iso e₃.symm hPt₁
    have hv₃ : Subsingleton (Ext S'.X₃ (unitSheaf (X := Y) ℓ) (2 + 1)) :=
      have := hPt₂ (2 + 1) (by omega)
      subsingleton_ext_of_isIso_left e₃.hom (2 + 1)
    refine ⟨Ext.isDualityPerfect_of_iso e₁ (Ext.isDualityPerfect_X₁ hS' h₂ h₃ hv₃
      (fun M j H φ => exists_extend_zmod H φ)), fun q hq => ?_⟩
    have hX₂ : Subsingleton (Ext S'.X₂ (unitSheaf (X := Y) ℓ) q) :=
      have := ih₂ q hq
      subsingleton_ext_of_isIso_left e₂.hom q
    have hX₃ : Subsingleton (Ext S'.X₃ (unitSheaf (X := Y) ℓ) (q + 1)) :=
      have := hPt₂ (q + 1) (by omega)
      subsingleton_ext_of_isIso_left e₃.hom (q + 1)
    have := Ext.subsingleton_ext_left_X₁_of_shortExact hS' (unitSheaf (X := Y) ℓ) q hX₂ hX₃
    exact subsingleton_ext_of_isIso_left e₁.inv q

include f in
/-- **`H²(Y, Λ)` has an injective trace**: it has `ℓ` elements, so it is isomorphic to `ℤ/ℓ`. -/
theorem exists_injective_trace_of_curve (hℓ : IsUnit (ℓ : k)) :
    ∃ t : Ext (unitSheaf (X := Y) ℓ) (unitSheaf ℓ) 2 →+ ZMod ℓ, Function.Injective t := by
  have hp : ℓ.Prime := Fact.out
  have h2 := natCard_ext_two_unitSheaf f hℓ
  have : Finite (Ext (unitSheaf (X := Y) ℓ) (unitSheaf (X := Y) ℓ) 2) :=
    Nat.finite_of_card_ne_zero (by rw [h2]; exact hp.ne_zero)
  have : Module.Finite (ZMod ℓ) (Ext (unitSheaf (X := Y) ℓ) (unitSheaf (X := Y) ℓ) 2) :=
    Module.Finite.of_finite
  have hr : Module.finrank (ZMod ℓ) (Ext (unitSheaf (X := Y) ℓ) (unitSheaf (X := Y) ℓ) 2) =
      Module.finrank (ZMod ℓ) (ZMod ℓ) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod ℓ)
      (V := Ext (unitSheaf (X := Y) ℓ) (unitSheaf (X := Y) ℓ) 2)
    rw [h2, Nat.card_zmod] at h
    rw [Module.finrank_self]
    exact (Nat.pow_eq_self_iff hp.one_lt).1 h.symm
  exact ⟨(LinearEquiv.ofFinrankEq _ _ hr).toLinearMap.toAddMonoidHom,
    (LinearEquiv.ofFinrankEq _ _ hr).injective⟩

include f in
/-- **Poincaré duality for `ℤ/ℓ` on an open of a smooth proper curve**, for an open immersion
`j : U → Y` from a nonempty `U` whose image has finite complement of closed points. -/
theorem isDualityPerfect_extensionByZeroOfRestriction_unitSheaf_of_isOpenImmersion
    (hℓ : IsUnit (ℓ : k)) (hpurity : LocalPurity ℓ k)
    (t : Ext (unitSheaf (X := Y) ℓ) (unitSheaf ℓ) 2 →+ ZMod ℓ) (ht : Function.Injective t)
    (S : Finset Y) (hS : ∀ y ∈ S, IsClosed ({y} : Set Y))
    {U : Scheme.{u}} (V : U ⟶ Y) [IsOpenImmersion V] (hV : Set.range V.base = (↑S : Set Y)ᶜ)
    [Nonempty U] :
    Ext.IsDualityPerfect (unitSheaf (X := Y) ℓ) (unitSheaf ℓ) 2 t
        ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) V).obj (unitSheaf (X := Y) ℓ)) ∧
      ∀ q, 2 < q → Subsingleton (Ext ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ)
        V).obj (unitSheaf (X := Y) ℓ)) (unitSheaf (X := Y) ℓ) q) := by
  obtain ⟨e⟩ := nonempty_extensionByZeroOfRestriction_iso_opensRange (ℓ := ℓ) V
    (unitSheaf (X := Y) ℓ)
  obtain ⟨x⟩ := ‹Nonempty U›
  have : Nonempty V.opensRange := ⟨⟨V.base x, x, rfl⟩⟩
  obtain ⟨h₁, h₂⟩ := isDualityPerfect_extensionByZeroOfRestriction_unitSheaf_of_curve f hℓ hpurity
    t ht S hS V.opensRange (by rw [Scheme.Hom.coe_opensRange]; exact hV)
  exact ⟨Ext.isDualityPerfect_of_iso e.symm h₁, fun q hq =>
    have := h₂ q hq
    subsingleton_ext_of_isIso_left e.hom q⟩

include f in
/-- **Excision in the top degree**: for an open immersion `j : U → Y` from a nonempty `U` whose
image has finite complement of closed points, `H²_c(U) → H²(Y)`, `x ↦ x ∘ ε` with
`ε : j_! j^{-1} Λ_Y → Λ_Y` the counit, is bijective. Both sides have `ℓ` elements by Poincaré
duality, and the map is injective, `ε` generating `Hom(j_! j^{-1} Λ_Y, Λ_Y) = End(Λ_U)`. -/
theorem bijective_comp_counit_ext_two_of_curve (hℓ : IsUnit (ℓ : k)) (hpurity : LocalPurity ℓ k)
    (S : Finset Y) (hS : ∀ y ∈ S, IsClosed ({y} : Set Y))
    {U : Scheme.{u}} (V : U ⟶ Y) [IsOpenImmersion V] (hV : Set.range V.base = (↑S : Set Y)ᶜ)
    [Nonempty U] :
    Function.Bijective (fun x : Ext (unitSheaf (X := Y) ℓ)
        ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) V).obj (unitSheaf (X := Y) ℓ))
          2 =>
      x.comp (Ext.mk₀ ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) V).counit.app
        (unitSheaf (X := Y) ℓ))) (add_zero 2)) := by
  have hp : ℓ.Prime := Fact.out
  obtain ⟨t₁, ht₁⟩ := exists_injective_trace_of_curve f hℓ
  have hPD := (isDualityPerfect_extensionByZeroOfRestriction_unitSheaf_of_isOpenImmersion f hℓ
    hpurity t₁ ht₁ S hS V hV).1 2 0 rfl
  let ΛY := unitSheaf (X := Y) ℓ
  let F := (etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) V).obj ΛY
  let A := (etaleModuleRestriction.{u, 0} (ZMod ℓ) V).obj ΛY
  let adj := etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) V
  let c := adj.counit.app ΛY
  have : IsIntegral Y := IsCurve.toIsVariety.toIsIntegral (k := k) (f := f)
  have : IsIntegral U := isIntegral_of_isOpenImmersion V
  have : ConnectedSpace U := inferInstance
  let eA := unitSheafIsoRestrictionOfIsOpenImmersion (ℓ := ℓ) V
  -- `Ext⁰(F, Λ_Y) ≅ End(A)` has `ℓ` elements
  have hA0 : Nat.card (Ext A A 0) = ℓ := by
    rw [Nat.card_congr (Ext.homEquiv₀ (X := A) (Y := A)),
      ← Nat.card_congr (Iso.homCongr eA eA)]
    exact natCard_end_unitSheaf (X := U) ℓ
  have hF0 : Nat.card (Ext F ΛY 0) = ℓ :=
    (Nat.card_eq_of_bijective _ (Stacks.ExtAdjunction.extMap_bijective adj A ΛY 0)).symm.trans hA0
  have hY2 : Nat.card (Ext ΛY ΛY 2) = ℓ := natCard_ext_two_unitSheaf f hℓ
  have : Finite (Ext F ΛY 0) := Nat.finite_of_card_ne_zero (by rw [hF0]; exact hp.ne_zero)
  have hc2 : Nat.card (Ext ΛY F 2) = ℓ := by
    rw [Nat.card_eq_of_bijective _ hPD, ExtensionTorsor.natCard_addMonoidHom_zmod, hF0]
  have : Finite (Ext ΛY ΛY 2) := Nat.finite_of_card_ne_zero (by rw [hY2]; exact hp.ne_zero)
  -- every class in `Ext⁰(F, Λ_Y)` is a multiple of `ε`
  have hgen : ∀ y : Ext F ΛY 0, ∃ a : ℕ, y = a • Ext.mk₀ c := by
    intro y
    obtain ⟨w, rfl⟩ := (Stacks.ExtAdjunction.extMap_bijective adj A ΛY 0).2 y
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective A A).2 w
    have hcard : Nat.card (A ⟶ A) = ℓ := (Nat.card_congr Ext.homEquiv₀.symm).trans hA0
    have : Finite (A ⟶ A) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
    have hid : (𝟙 A) ≠ 0 := by
      intro h0
      have : Subsingleton (A ⟶ A) := ⟨fun g g' => by
        rw [← Category.comp_id g, ← Category.comp_id g', h0, comp_zero, comp_zero]⟩
      exact hp.one_lt.ne ((Nat.card_unique (α := A ⟶ A)).symm.trans hcard)
    have hinj : Function.Injective (fun a : ZMod ℓ => a • (𝟙 A)) := by
      intro a a' haa
      by_contra hne
      apply hid
      have h1 : (a - a') • (𝟙 A) = 0 := by
        rw [sub_smul]
        exact sub_eq_zero.2 haa
      have := congrArg (fun g => (a - a')⁻¹ • g) h1
      simpa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hne)] using this
    obtain ⟨a, rfl⟩ := (hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_zmod])).2 g
    refine ⟨a.val, ?_⟩
    change Stacks.ExtAdjunction.extMap adj A ΛY 0 (Ext.mk₀ (a • 𝟙 A)) = _
    have hval : a • (Ext.mk₀ (𝟙 A) : Ext A A 0) = a.val • Ext.mk₀ (𝟙 A) := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ), ZMod.natCast_zmod_val]
    rw [Ext.mk₀_smul, hval, map_nsmul, Stacks.ExtAdjunction.extMap_apply, Ext.mapExactFunctor_mk₀,
      (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) V).map_id, Ext.mk₀_id_comp]
  have : Finite (Ext ΛY ((𝟭 _).obj ΛY) 2) := ‹Finite (Ext ΛY ΛY 2)›
  refine (Function.Injective.bijective_of_nat_card_le ?_
    (by rw [hc2, show Nat.card (Ext ΛY ((𝟭 _).obj ΛY) 2) = ℓ from hY2]))
  change Function.Injective ((Ext.mk₀ c).postcomp ΛY (add_zero 2))
  rw [injective_iff_map_eq_zero]
  intro x hx
  change x.comp (Ext.mk₀ c) (add_zero 2) = 0 at hx
  apply hPD.1
  rw [map_zero]
  ext y
  obtain ⟨a, rfl⟩ := hgen y
  rw [Ext.dualityPairing_apply, AddMonoidHom.zero_apply]
  have hsm : x.comp (a • Ext.mk₀ c) (add_zero 2) = a • x.comp (Ext.mk₀ c) (add_zero 2) := by
    have := map_nsmul (Ext.bilinearComp ΛY F ΛY 2 0 2 (add_zero 2) x) a (Ext.mk₀ c)
    simpa using this
  rw [hsm, hx, smul_zero, map_zero]

end Curve

end Stacks.EtaleCohomology

end
