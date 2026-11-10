module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.GysinGoodness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeMayerVietoris
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CyclicCoverSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantModuleSheafIrreducibleSectionsRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction

/-!
# Gluing purity classes over a union of two opens

Let `i : T ⟶ Y` be a closed immersion and `Λ = ℤ/N`. For an open `O ⊆ T` write
`Λ_O^! = j_{O!} Λ_T|_O` (`Stacks.EtaleCohomology.Purity.localUnit`). A class
`a ∈ Ext^c_Y(i_* Λ_O^!, Λ_Y)` is a **local purity class over `O`**
(`Stacks.EtaleCohomology.Purity.IsLocalPurityClass`) if it is good, in the sense of
`Stacks.EtaleCohomology.Purity.Gysin.IsGoodAt`, at every sheaf `j_{O!} H` supported on `O`: the
Gysin maps `Ext^q_T(j_{O!} H, Λ_O^!) → Ext^{q+c}_Y(i_* j_{O!} H, Λ_Y)` are bijective and
`Ext^q_Y(i_* j_{O!} H, Λ_Y) = 0` for `q < c`. For `O = i⁻¹(U)` this is purity of `T ∩ U ⊆ U`,
read on `Y` through extension by zero.

* Local purity classes restrict to smaller opens
  (`Stacks.EtaleCohomology.Purity.IsLocalPurityClass.restrict`).
* Two local purity classes over `O₁` and `O₂` agreeing on `O₁ ∩ O₂` glue to one over `O₁ ∪ O₂`
  (`Stacks.EtaleCohomology.Purity.IsLocalPurityClass.glue`).
* If `O₁ ∩ O₂` is irreducible, two local purity classes over `O₁` and `O₂` always glue after
  rescaling one of them by a unit of `ℤ/N`
  (`Stacks.EtaleCohomology.Purity.IsLocalPurityClass.exists_glue`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.EtaleCohomology.ExtensionTorsor
open Stacks.EtaleCohomology.Purity.Gysin

universe u

namespace Stacks.EtaleCohomology.Purity

attribute [local instance] moduleCat_hasLimitsOfSize

/-! ### Ext out of an extension by zero -/

section ExtensionByZero

variable (Λ : Type) [Ring Λ] {X : Scheme.{u}}

/-- **Composition with a map that becomes invertible on `W` is bijective on `Ext` out of
`j_{W!} H`.** -/
theorem bijective_comp_mk₀_of_isIso_restriction (W : X.Opens) (H : EtaleModules.{u, 0} Λ W)
    {Z Z' : EtaleModules.{u, 0} Λ X} (φ : Z ⟶ Z')
    [IsIso ((etaleModuleRestriction.{u, 0} Λ W.ι).map φ)] (n : ℕ) :
    Function.Bijective (fun w : Ext ((etaleModuleExtensionByZero.{u, 0} Λ W.ι).obj H) Z n =>
      w.comp (Ext.mk₀ φ) (add_zero n)) := by
  let adj := etaleModuleExtensionByZeroAdj.{u, 0} Λ W.ι
  have hZ := Stacks.ExtAdjunction.extMap_bijective adj H Z n
  have hZ' := Stacks.ExtAdjunction.extMap_bijective adj H Z' n
  have hpost := Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso (X := H)
    ((etaleModuleRestriction.{u, 0} Λ W.ι).map φ) n
  have e : (fun w : Ext ((etaleModuleExtensionByZero.{u, 0} Λ W.ι).obj H) Z n =>
      w.comp (Ext.mk₀ φ) (add_zero n)) ∘ Stacks.ExtAdjunction.extMap adj H Z n =
      Stacks.ExtAdjunction.extMap adj H Z' n ∘
        (Ext.mk₀ ((etaleModuleRestriction.{u, 0} Λ W.ι).map φ)).postcomp H (add_zero n) := by
    funext y
    exact (Stacks.ExtAdjunction.extMap_naturality_mk₀ adj H φ n y).symm
  exact (Function.Bijective.of_comp_iff _ hZ).1 (e ▸ hZ'.comp hpost)

/-- The counit of `j_! ⊣ j⁻¹` is invertible at an extension by zero. -/
instance isIso_counit_app_extensionByZero (W : X.Opens) (H : EtaleModules.{u, 0} Λ W) :
    IsIso ((etaleModuleExtensionByZeroAdj.{u, 0} Λ W.ι).counit.app
      ((etaleModuleExtensionByZero.{u, 0} Λ W.ι).obj H)) := by
  have h := (etaleModuleExtensionByZeroAdj.{u, 0} Λ W.ι).left_triangle_components H
  have : IsIso ((etaleModuleExtensionByZero.{u, 0} Λ W.ι).map
      ((etaleModuleExtensionByZeroAdj.{u, 0} Λ W.ι).unit.app H)) := inferInstance
  exact IsIso.of_isIso_fac_left h

/-- Extension by zero along equal étale morphisms. -/
def extensionByZeroCongr {A : Scheme.{u}} {f g : A ⟶ X} [Etale f] [Etale g] (h : f = g)
    (H : EtaleModules.{u, 0} Λ A) :
    (etaleModuleExtensionByZero.{u, 0} Λ f).obj H ≅
      (etaleModuleExtensionByZero.{u, 0} Λ g).obj H := by
  subst h
  exact Iso.refl _

/-- Extension by zero from an open `W' ≤ W` factors through `W`. -/
def extensionByZeroOfLEIso {W' W : X.Opens} (h : W' ≤ W) (H : EtaleModules.{u, 0} Λ W') :
    (etaleModuleExtensionByZero.{u, 0} Λ W'.ι).obj H ≅
      (etaleModuleExtensionByZero.{u, 0} Λ W.ι).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ (X.homOfLE h)).obj H) :=
  extensionByZeroCongr Λ (X.homOfLE_ι h).symm H ≪≫
    (etaleModuleExtensionByZeroCompIso.{u, 0} Λ (X.homOfLE h) W.ι).app H

end ExtensionByZero

/-! ### Scalars -/

section Scalars

variable {N : ℕ}

/-- An additive functor between `ℤ/N`-linear categories is `ℤ/N`-linear. -/
theorem map_zmod_smul [NeZero N] {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] [Linear (ZMod N) C] [Linear (ZMod N) D] (F : C ⥤ D) [F.Additive] {X Y : C}
    (r : ZMod N) (f : X ⟶ Y) : F.map (r • f) = r • F.map f := by
  rw [← ZMod.natCast_zmod_val r, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul,
    Functor.map_nsmul]

variable [NeZero N]

/-- The section `1` of `Λ_S` over the final object of `S_étale`. -/
def unitSection (S : Scheme.{u}) :
    (unitSheaf (X := S) N).obj.obj (op (etaleSiteTerminal S)) :=
  ((constantSheafAdj S.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))
    (etaleSiteTerminalIsTerminal S)).unit.app (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N))))
      (ULift.up 1)

omit [NeZero N] in
/-- The equivalence `homUnitSheafEquiv` sends an endomorphism `v` of `Λ_S` to the image of
`unitSection S` under `v` over the final object of `S_étale`. -/
theorem homUnitSheafEquiv_apply_eq (S : Scheme.{u}) (v : unitSheaf (X := S) N ⟶ unitSheaf N) :
    homUnitSheafEquiv N (unitSheaf (X := S) N) v = v.hom.app (op (etaleSiteTerminal S))
      (unitSection S) := by
  simp only [homUnitSheafEquiv, Equiv.trans_apply, AddEquiv.toEquiv_eq_coe,
    AddEquiv.coe_toEquiv, Stacks.Cohomology.GlobalSections.moduleULiftHomAddEquiv_apply,
    Adjunction.homEquiv_unit]
  rfl

omit [NeZero N] in
/-- On an irreducible scheme, the map `ℤ/N → Γ(S, Λ_S)` is bijective. -/
theorem bijective_constantSheafAdj_unit (S : Scheme.{u}) [IrreducibleSpace S] :
    Function.Bijective ((constantSheafAdj S.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))
      (etaleSiteTerminalIsTerminal S)).unit.app
        (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N)))) := by
  have : IrreducibleSpace (etaleSiteTerminal S).left := inferInstanceAs (IrreducibleSpace S)
  exact AlgebraicGeometry.Scheme.bijective_toSheafify_const_app_of_irreducibleSpace (ZMod N)
    (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N))) (etaleSiteTerminal S)

/-- The endomorphism `r • 𝟙` of `Λ_S` sends `unitSection S` to the global section of `Λ_S`
determined by `r`. -/
theorem smul_id_val_app_unitSection (S : Scheme.{u}) (r : ZMod N) :
    (r • 𝟙 (unitSheaf (X := S) N)).hom.app (op (etaleSiteTerminal S)) (unitSection S) =
      ((constantSheafAdj S.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))
        (etaleSiteTerminalIsTerminal S)).unit.app
          (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N)))) (ULift.up r) := by
  rw [← ZMod.natCast_zmod_val r, Nat.cast_smul_eq_nsmul]
  have h1 : (r.val • 𝟙 (unitSheaf (X := S) N)).hom = r.val • 𝟙 _ := by
    change (sheafToPresheaf _ _).map (r.val • 𝟙 (unitSheaf (X := S) N)) = _
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    rfl
  rw [h1, NatTrans.app_nsmul, NatTrans.id_app]
  change r.val • unitSection S = _
  rw [unitSection, ← map_nsmul]
  congr 1
  apply ULift.ext
  change r.val • (1 : ZMod N) = ((r.val : ℕ) : ZMod N)
  rw [nsmul_eq_mul, mul_one]

/-- **On an irreducible scheme every endomorphism of `Λ_S = ℤ/N` is a scalar.** -/
theorem exists_eq_smul_id_unitSheaf (S : Scheme.{u}) [IrreducibleSpace S]
    (v : unitSheaf (X := S) N ⟶ unitSheaf N) : ∃ r : ZMod N, v = r • 𝟙 _ := by
  obtain ⟨⟨r⟩, hr⟩ := (bijective_constantSheafAdj_unit S).2
    (homUnitSheafEquiv N (unitSheaf (X := S) N) v)
  refine ⟨r, (homUnitSheafEquiv N (unitSheaf (X := S) N)).injective ?_⟩
  rw [homUnitSheafEquiv_apply_eq, homUnitSheafEquiv_apply_eq, smul_id_val_app_unitSection,
    ← homUnitSheafEquiv_apply_eq, ← hr]

/-- On an irreducible scheme `r • 𝟙 = 0` on `Λ_S` only for `r = 0`. -/
theorem eq_zero_of_smul_id_unitSheaf (S : Scheme.{u}) [IrreducibleSpace S] (r : ZMod N)
    (h : r • 𝟙 (unitSheaf (X := S) N) = 0) : r = 0 := by
  have h1 := smul_id_val_app_unitSection S r
  rw [h] at h1
  have hz : (ConcreteCategory.hom ((constantSheafAdj S.smallEtaleTopology
      (ModuleCat.{u + 1} (ZMod N)) (etaleSiteTerminalIsTerminal S)).unit.app
        (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N))))) 0 = 0 := map_zero _
  exact congrArg ULift.down ((bijective_constantSheafAdj_unit S).1 (h1.symm.trans hz.symm))

end Scalars

/-! ### Local purity classes -/

section LocalPurity

variable {N : ℕ} {T Y : Scheme.{u}} (i : T ⟶ Y) [IsClosedImmersion i]

/-- `Λ_O^! = j_{O!} Λ_T|_O` for an open `O ⊆ T`, `Λ = ℤ/N`. -/
abbrev localUnit (O : T.Opens) : EtaleModules.{u, 0} (ZMod N) T :=
  (etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod N) O.ι).obj (unitSheaf (X := T) N)

/-- **A local purity class over `O`**: a class `a ∈ Ext^c_Y(i_* Λ_O^!, Λ_Y)` which is good, for
the functor `i_*`, at every sheaf `j_{O!} H` supported on `O`. -/
def IsLocalPurityClass (O : T.Opens) {c : ℕ}
    (a : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) i).obj (localUnit (N := N) O))
      (unitSheaf (X := Y) N) c) : Prop :=
  ∀ H : EtaleModules.{u, 0} (ZMod N) O,
    IsGoodAt (etaleModuleDirectImage.{u, 0} (ZMod N) i) a
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) O.ι).obj H)

/-- **Local purity classes restrict to smaller opens**, along the comparison
`Λ_{O'}^! ⟶ Λ_O^!`. -/
theorem IsLocalPurityClass.restrict {O O' : T.Opens} (h : O' ≤ O) {c : ℕ}
    {a : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) i).obj (localUnit (N := N) O))
      (unitSheaf (X := Y) N) c} (ha : IsLocalPurityClass i O a) :
    IsLocalPurityClass i O' ((Ext.mk₀ ((etaleModuleDirectImage.{u, 0} (ZMod N) i).map
      ((openComparison (ZMod N) h).app (unitSheaf (X := T) N)))).comp a (zero_add c)) := by
  intro H
  have := isIso_restriction_openComparison (ZMod N) h le_rfl (unitSheaf (X := T) N)
  rw [isGoodAt_comp_mk₀_iff _ a _ _
    (fun q => bijective_comp_mk₀_of_isIso_restriction (ZMod N) O' H _ q)]
  exact (ha _).of_iso _ _ (extensionByZeroOfLEIso (ZMod N) h H).symm

/-- **Two local purity classes agreeing on `O₁ ∩ O₂` glue to one over `O₁ ∪ O₂`.** -/
theorem IsLocalPurityClass.glue {O₁ O₂ : T.Opens} {c : ℕ}
    {a₁ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) i).obj (localUnit (N := N) O₁))
      (unitSheaf (X := Y) N) c}
    {a₂ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) i).obj (localUnit (N := N) O₂))
      (unitSheaf (X := Y) N) c}
    (h₁ : IsLocalPurityClass i O₁ a₁) (h₂ : IsLocalPurityClass i O₂ a₂)
    (hcomp : (Ext.mk₀ ((etaleModuleDirectImage.{u, 0} (ZMod N) i).map
        ((openComparison (ZMod N) (inf_le_left : O₁ ⊓ O₂ ≤ O₁)).app (unitSheaf (X := T) N)))).comp
          a₁ (zero_add c) =
      (Ext.mk₀ ((etaleModuleDirectImage.{u, 0} (ZMod N) i).map
        ((openComparison (ZMod N) (inf_le_right : O₁ ⊓ O₂ ≤ O₂)).app (unitSheaf (X := T) N)))).comp
          a₂ (zero_add c)) :
    ∃ γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) i).obj (localUnit (N := N) (O₁ ⊔ O₂)))
      (unitSheaf (X := Y) N) c, IsLocalPurityClass i (O₁ ⊔ O₂) γ := by
  let P := etaleModuleDirectImage.{u, 0} (ZMod N) i
  let Λ := unitSheaf (X := T) N
  obtain ⟨γ, hγ₁, hγ₂⟩ := exists_comp_eq_of_shortExact P _ _ _ _ _
    (shortExact_relativeCover (ZMod N) O₁ O₂ Λ) a₁ a₂ hcomp
  refine ⟨γ, fun H => ?_⟩
  let X := (etaleModuleExtensionByZero.{u, 0} (ZMod N) (O₁ ⊔ O₂).ι).obj H
  have hS := shortExact_relativeCover (ZMod N) O₁ O₂ X
  have := isIso_restriction_openComparison (ZMod N) (le_sup_left : O₁ ≤ O₁ ⊔ O₂) le_rfl Λ
  have := isIso_restriction_openComparison (ZMod N) (le_sup_right : O₂ ≤ O₁ ⊔ O₂) le_rfl Λ
  have := isIso_restriction_openComparison (ZMod N) (le_sup_left : O₁ ≤ O₁ ⊔ O₂)
    (inf_le_left : O₁ ⊓ O₂ ≤ O₁) Λ
  have hU₁ : IsGoodAt P γ ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod N) O₁.ι).obj X) :=
    (isGoodAt_comp_mk₀_iff P γ _ _
      (fun q => bijective_comp_mk₀_of_isIso_restriction (ZMod N) O₁ _ _ q)).1
      (hγ₁ ▸ h₁ ((etaleModuleRestriction.{u, 0} (ZMod N) O₁.ι).obj X))
  have hU₂ : IsGoodAt P γ ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod N) O₂.ι).obj X) :=
    (isGoodAt_comp_mk₀_iff P γ _ _
      (fun q => bijective_comp_mk₀_of_isIso_restriction (ZMod N) O₂ _ _ q)).1
      (hγ₂ ▸ h₂ ((etaleModuleRestriction.{u, 0} (ZMod N) O₂.ι).obj X))
  have h₁₂ : IsGoodAt P a₁
      ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod N) (O₁ ⊓ O₂).ι).obj X) :=
    (h₁ _).of_iso _ _ (extensionByZeroOfLEIso (ZMod N) (inf_le_left : O₁ ⊓ O₂ ≤ O₁) _).symm
  have hU₁₂ : IsGoodAt P γ
      ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod N) (O₁ ⊓ O₂).ι).obj X) :=
    (isGoodAt_comp_mk₀_iff P γ _ _
      (fun q => bijective_comp_mk₀_of_isIso_restriction (ZMod N) (O₁ ⊓ O₂) _ _ q)).1
      (hγ₁ ▸ h₁₂)
  have h₃ := IsGoodAt.of_shortExact P γ hS hU₁₂ (IsGoodAt.biprod P γ hU₁ hU₂)
  exact h₃.of_iso _ _
    (asIso ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) (O₁ ⊔ O₂).ι).counit.app X))

/-- `Λ_T|_O ≅ Λ_O`. -/
def unitSheafRestrictionIso {T : Scheme.{u}} (O : T.Opens) :
    (etaleModuleRestriction.{u, 0} (ZMod N) O.ι).obj (unitSheaf (X := T) N) ≅
      unitSheaf (X := O) N :=
  ((etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod N) O.ι).app _).symm ≪≫
    (etaleModuleInverseImageConstantIso.{u, 0} (ZMod N) O.ι).app
      (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N)))

variable [NeZero N] in
/-- **On an irreducible open every endomorphism of `Λ_O^!` is a scalar.** -/
theorem exists_eq_smul_id_localUnit {T : Scheme.{u}} (O : T.Opens) [IrreducibleSpace O]
    (v : localUnit (N := N) O ⟶ localUnit O) : ∃ r : ZMod N, v = r • 𝟙 _ := by
  let adj := etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) O.ι
  let hL := adj.fullyFaithfulLOfIsIsoUnit
  let e := unitSheafRestrictionIso (N := N) O
  obtain ⟨r, hr⟩ := exists_eq_smul_id_unitSheaf O (e.inv ≫ hL.preimage v ≫ e.hom)
  refine ⟨r, ?_⟩
  have hw : hL.preimage v = r • 𝟙 _ := by
    have : hL.preimage v = e.hom ≫ (e.inv ≫ hL.preimage v ≫ e.hom) ≫ e.inv := by simp
    rw [this, hr, Linear.smul_comp, Linear.comp_smul, Category.id_comp, e.hom_inv_id]
  rw [← hL.map_preimage v, hw, map_zmod_smul, CategoryTheory.Functor.map_id]
  rfl

variable [NeZero N] in
/-- On an irreducible open `r • 𝟙 = 0` on `Λ_O^!` only for `r = 0`. -/
theorem eq_zero_of_smul_id_localUnit {T : Scheme.{u}} (O : T.Opens) [IrreducibleSpace O]
    (r : ZMod N) (h : r • 𝟙 (localUnit (N := N) O) = 0) : r = 0 := by
  let adj := etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) O.ι
  let hL := adj.fullyFaithfulLOfIsIsoUnit
  let e := unitSheafRestrictionIso (N := N) O
  have h1 : (etaleModuleExtensionByZero.{u, 0} (ZMod N) O.ι).map
      (r • 𝟙 ((etaleModuleRestriction.{u, 0} (ZMod N) O.ι).obj (unitSheaf (X := T) N))) =
      (etaleModuleExtensionByZero.{u, 0} (ZMod N) O.ι).map 0 := by
    rw [map_zmod_smul, CategoryTheory.Functor.map_id, Functor.map_zero]
    exact h
  have h2 := hL.map_injective h1
  apply eq_zero_of_smul_id_unitSheaf O r
  have : r • 𝟙 (unitSheaf (X := O) N) = e.inv ≫ (r • 𝟙 _) ≫ e.hom := by
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, e.inv_hom_id]
  rw [this, h2, zero_comp, comp_zero]

variable [NeZero N] in
/-- **Two local purity classes over `O₁` and `O₂` glue to one over `O₁ ∪ O₂` after rescaling the
second by a unit of `ℤ/N`**, when `O₁ ∩ O₂` is irreducible. -/
theorem IsLocalPurityClass.exists_glue {O₁ O₂ : T.Opens} [IrreducibleSpace (O₁ ⊓ O₂ : T.Opens)]
    {c : ℕ}
    {a₁ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) i).obj (localUnit (N := N) O₁))
      (unitSheaf (X := Y) N) c}
    {a₂ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) i).obj (localUnit (N := N) O₂))
      (unitSheaf (X := Y) N) c}
    (h₁ : IsLocalPurityClass i O₁ a₁) (h₂ : IsLocalPurityClass i O₂ a₂) :
    ∃ γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod N) i).obj (localUnit (N := N) (O₁ ⊔ O₂)))
      (unitSheaf (X := Y) N) c, IsLocalPurityClass i (O₁ ⊔ O₂) γ := by
  let P := etaleModuleDirectImage.{u, 0} (ZMod N) i
  let Λ := unitSheaf (X := T) N
  let κ₁ := (openComparison (ZMod N) (inf_le_left : O₁ ⊓ O₂ ≤ O₁)).app Λ
  let κ₂ := (openComparison (ZMod N) (inf_le_right : O₁ ⊓ O₂ ≤ O₂)).app Λ
  have hb₁ := h₁.restrict i (inf_le_left : O₁ ⊓ O₂ ≤ O₁)
  have hb₂ := h₂.restrict i (inf_le_right : O₁ ⊓ O₂ ≤ O₂)
  obtain ⟨r, hr, hrb⟩ := exists_isUnit_eq_mk₀_smul_comp P (R := ZMod N)
    (hb₁ ((etaleModuleRestriction.{u, 0} (ZMod N) (O₁ ⊓ O₂).ι).obj Λ))
    (hb₂ ((etaleModuleRestriction.{u, 0} (ZMod N) (O₁ ⊓ O₂).ι).obj Λ))
    (exists_eq_smul_id_localUnit (O₁ ⊓ O₂)) (eq_zero_of_smul_id_localUnit (O₁ ⊓ O₂))
  let a₂' := (Ext.mk₀ (P.map (r • 𝟙 (localUnit (N := N) O₂)))).comp a₂ (zero_add c)
  have h₂' : IsLocalPurityClass i O₂ a₂' := fun H =>
    (isGoodAt_comp_mk₀_iff P a₂ _ _ (fun q => bijective_comp_mk₀_smul_id r hr q)).2 (h₂ H)
  refine IsLocalPurityClass.glue i h₁ h₂' ?_
  change (Ext.mk₀ (P.map κ₁)).comp a₁ (zero_add c) =
    (Ext.mk₀ (P.map κ₂)).comp ((Ext.mk₀ (P.map (r • 𝟙 (localUnit (N := N) O₂)))).comp a₂
      (zero_add c)) (zero_add c)
  rw [hrb, Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc, ← P.map_comp, ← P.map_comp,
    Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]

end LocalPurity

end Stacks.EtaleCohomology.Purity

end
