module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerFlagClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.RootOfUnityTwist

/-!
# Kummer classes under pullback

Let `k` be a field, `N` invertible in `k` and `ζ` a primitive `N`-th root of unity of `k`. For a
morphism `g : V' ⟶ V` of `k`-schemes and a unit `a` on `V`, the restriction along `g` of the
Kummer class `κ(a) ∈ H¹(V, ℤ/N)` is the Kummer class of the pulled back unit `g^♯ a`, and
`κ(a^m) = m κ(a)`.

## Main results

* `Stacks.EtaleCohomology.KummerFlag.unitH0Class_restriction`: restriction on `H⁰(-, 𝐆_m)` is the
  pullback of units.
* `Stacks.EtaleCohomology.KummerFlag.constantExtRestriction_kummerUnitClass`: `g^* κ(a) = κ(g^♯ a)`
  for `g` over `k`.
* `Stacks.EtaleCohomology.KummerFlag.kummerUnitClass_pow`: `κ(a^m) = m κ(a)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology.KummerFlag

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- The global section of `𝐆_m` attached to `unitH0Class a` is `a`. -/
theorem equiv₀_unitH0Class {V : Scheme.{u}} (a : (Γ(V, ⊤))ˣ) :
    Sheaf.H.equiv₀ (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} V) (isTerminalEtaleMkId V)
        (unitH0Class a) = Stacks.Kummer.ofUnit.{u, u + 1} (U := Scheme.Etale.mk (𝟙 V)) a :=
  Equiv.apply_symm_apply _ _

/-- **Restriction on `H⁰(-, 𝐆_m)` is the pullback of units.** -/
theorem unitH0Class_restriction {X Y : Scheme.{u}} (π : X ⟶ Y) (a : (Γ(Y, ⊤))ˣ) :
    Sheaf.H.map (Stacks.Kummer.multiplicativeInverseImageComparison.{u, u + 1} π) 0
        (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} π
          (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} Y) 0 (unitH0Class a)) =
      unitH0Class (Units.map π.appTop.hom a) := by
  apply (Sheaf.H.equiv₀ _ (isTerminalEtaleMkId X)).injective
  rw [equiv₀_unitH0Class, ← Sheaf.H.equiv₀_naturality,
    equiv₀_etaleCohomologyRestrictionMap_zero, equiv₀_unitH0Class]
  set b := ((isTerminalEtaleMkId Y).isTerminalObj (smallEtaleBaseChange π)).from
    (Scheme.Etale.mk (𝟙 X))
  have h3 := ConcreteCategory.congr_hom
    ((Stacks.Kummer.multiplicativeInverseImageComparison.{u, u + 1} π).hom.naturality b.op)
    (((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} π).unit.app
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} Y)).hom.app (op (Scheme.Etale.mk (𝟙 Y)))
        (Stacks.Kummer.ofUnit.{u, u + 1} (U := Scheme.Etale.mk (𝟙 Y)) a))
  refine h3.trans ((ConcreteCategory.comp_apply _ _ _).trans ?_)
  refine (congrArg (ConcreteCategory.hom
    ((Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X).obj.map b.op))
    (Stacks.Kummer.multiplicativeInverseImageComparison_app_ofUnit.{u, u + 1} π
      (Scheme.Etale.mk (𝟙 Y)) a)).trans ?_
  refine (Stacks.Kummer.map_ofUnit.{u, u + 1} b _).trans ?_
  have hb : b.left ≫ pullback.fst (Scheme.Etale.mk (𝟙 Y)).hom π = π := by
    have hw : b.left ≫ pullback.snd (Scheme.Etale.mk (𝟙 Y)).hom π = 𝟙 X :=
      MorphismProperty.Over.w b
    have hc : pullback.fst (Scheme.Etale.mk (𝟙 Y)).hom π =
        pullback.snd (Scheme.Etale.mk (𝟙 Y)).hom π ≫ π :=
      (Category.comp_id _).symm.trans pullback.condition
    refine (congrArg (fun h => b.left ≫ h) hc).trans ?_
    change (b.left ≫ pullback.snd (Scheme.Etale.mk (𝟙 Y)).hom π) ≫ π = π
    rw [hw]
    exact Category.id_comp π
  congr 1
  ext
  change b.left.appTop.hom ((pullback.fst (Scheme.Etale.mk (𝟙 Y)).hom π).appTop.hom _) =
    π.appTop.hom _
  exact congrArg (fun f : X ⟶ Y => f.appTop.hom (a : Γ(Y, ⊤))) hb

variable {k : Type u} [Field k] {N : ℕ} {ζ : k} (hζ : IsPrimitiveRoot ζ N) (hN : IsUnit (N : k))

include hζ in
/-- **The Kummer class is natural**: for `g : V' ⟶ V` over `k`, `g^* κ(a) = κ(g^♯ a)`. -/
theorem constantExtRestriction_kummerUnitClass {V V' : Scheme.{u}} (fV : V ⟶ Spec (.of k))
    (fV' : V' ⟶ Spec (.of k)) (g : V' ⟶ V) (hg : g ≫ fV = fV') (a : (Γ(V, ⊤))ˣ) :
    constantExtRestriction (ZMod N) g 1 (kummerUnitClass hζ hN fV a) =
      kummerUnitClass hζ hN fV' (Units.map g.appTop.hom a) := by
  have hN0 := ne_zero_of_isUnit hN
  apply (Stacks.Picard.extRootsOfUnityAddEquiv fV' hζ hN0 1).injective
  conv_rhs => rw [kummerUnitClass, AddEquiv.apply_symm_apply]
  have hg' : g ≫ fV = fV' ≫ Spec.map (CommRingCat.ofHom (RingHom.id k)) := by
    rw [hg, show CommRingCat.ofHom (RingHom.id k) = 𝟙 _ from rfl, Spec.map_id, Category.comp_id]
  have key := rootsOfUnityPullbackMap_extForgetSheafH hζ hN0 fV fV' g (RingHom.id k) 1 hg'
    (by simp) (kummerUnitClass hζ hN fV a)
  rw [Nat.cast_one, one_smul] at key
  rw [Stacks.Picard.extRootsOfUnityAddEquiv_apply, ← key, kummerUnitClass,
    ← Stacks.Picard.extRootsOfUnityAddEquiv_apply, AddEquiv.apply_symm_apply]
  have h := Stacks.Kummer.etaleCohomologyRestrictionMap_kummerExtClass.{u, u + 1, u + 1} g hN0
    (Stacks.Kummer.isUnit_natCast_globalSections V N fV hN) 0 1 rfl (unitH0Class a)
  refine h.trans ?_
  rw [unitH0Class_restriction]
  rfl

/-- The class in `H⁰(V, 𝐆_m)` of a power is the multiple. -/
theorem unitH0Class_pow {V : Scheme.{u}} (a : (Γ(V, ⊤))ˣ) (m : ℕ) :
    unitH0Class (a ^ m) = m • unitH0Class a := by
  rw [unitH0Class, unitH0Class, ← map_nsmul]
  rfl

/-- **The Kummer class is a homomorphism**: `κ(a^m) = m κ(a)`. -/
theorem kummerUnitClass_pow {V : Scheme.{u}} (fV : V ⟶ Spec (.of k)) (a : (Γ(V, ⊤))ˣ) (m : ℕ) :
    kummerUnitClass hζ hN fV (a ^ m) = m • kummerUnitClass hζ hN fV a := by
  rw [kummerUnitClass, kummerUnitClass, unitH0Class_pow, map_nsmul, map_nsmul]

end Stacks.EtaleCohomology.KummerFlag

end
