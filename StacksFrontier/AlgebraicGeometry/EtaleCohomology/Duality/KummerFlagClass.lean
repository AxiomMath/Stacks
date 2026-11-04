module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.WeilPairingCurve
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Kummer flag classes of points

Let `k` be a field, `N` an integer invertible in `k`, `ζ ∈ k` a primitive `N`-th root of unity and
`Λ = ℤ/N`. This file builds, out of Kummer theory alone, the class of a point of a smooth
`k`-scheme in top degree, in a form that is visibly functorial.

* For a unit `a` on a `k`-scheme `V`, the **Kummer class** `κ(a) ∈ H¹(V, Λ) = Ext¹(Λ_V, Λ_V)` is
  the Kummer coboundary of `a ∈ H⁰(V, 𝐆_m)`, read through `μ_N ≅ Λ`, `ζ ↦ 1`
  (`Stacks.EtaleCohomology.KummerFlag.kummerUnitClass`).
* For an open immersion `j : V ⟶ U` with closed complement `i : W ⟶ U` and a unit `a` on `V`,
  the **Kummer divisor class** `δ(a) ∈ Ext²_U(i_* i⁻¹ Λ_U, Λ_U)` is the Yoneda product of the class
  of the sequence `0 → j_! j⁻¹ Λ_U → Λ_U → i_* i⁻¹ Λ_U → 0` of Tag 095L with `j_!(κ(a))`
  followed by the counit `j_! j⁻¹ Λ_U ⟶ Λ_U`
  (`Stacks.EtaleCohomology.KummerFlag.kummerDivisorClass`). For `a = φ|_V` with `V = D(φ)` this
  is the class of the divisor of `φ`.
* For `d` such data `(j_m, i_m, a_m)` on the same `U`, the **Kummer flag class**
  `γ ∈ Ext^{2d}_U(E_0 ⋯ E_{d-1} Λ_U, Λ_U)`, `E_m = i_{m*} i_m⁻¹`, is
  `γ = E_0(γ') ∘ δ(a_0)` with `γ'` the class of the remaining `d - 1` data
  (`Stacks.EtaleCohomology.KummerFlag.kummerFlagClass`); it is supported on the intersection of
  the closed sets `W_m`.
* For an open immersion `n : U ⟶ Y` and a map `z : Λ_Y ⟶ n_!(E_0 ⋯ E_{d-1} Λ_U)` restricting on
  `U` to the canonical map, the **Kummer point class** is
  `z ∘ n_!(γ) ∘ (n_! Λ_U ⟶ Λ_Y) ∈ H^{2d}(Y, Λ)`
  (`Stacks.EtaleCohomology.KummerFlag.kummerPointClass`).

When the `a_m = φ_m|_{D(φ_m)}` come from an étale coordinate system `φ : U ⟶ 𝐀^d` whose zero set
is one closed point `y`, the Kummer point class is the cycle class of `y`. That it does not depend
on `y` nor on the coordinates, and generates `H^{2d}(Y, Λ)` for `Y` connected, smooth and proper
of dimension `d` over an algebraically closed field, is the statement
`Stacks.EtaleCohomology.KummerFlag.PointClassIndependence`.

## Main definitions

* `Stacks.EtaleCohomology.KummerFlag.kummerUnitClass`
* `Stacks.EtaleCohomology.KummerFlag.kummerDivisorClass`
* `Stacks.EtaleCohomology.KummerFlag.flagSheaf`, `Stacks.EtaleCohomology.KummerFlag.flagUnit`
* `Stacks.EtaleCohomology.KummerFlag.kummerFlagClass`
* `Stacks.EtaleCohomology.KummerFlag.kummerPointClass`
* `Stacks.EtaleCohomology.KummerFlag.PointClassIndependence`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology.KummerFlag

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

section Kummer

variable {k : Type u} [Field k] {N : ℕ} {ζ : k} (hζ : IsPrimitiveRoot ζ N) (hN : IsUnit (N : k))

include hN in
/-- An integer invertible in a field is nonzero. -/
theorem ne_zero_of_isUnit : N ≠ 0 := by
  rintro rfl
  simp at hN

/-- The class in `H⁰(V, 𝐆_m)` of a unit `a` of `Γ(V, 𝒪_V)`. -/
def unitH0Class {V : Scheme.{u}} (a : (Γ(V, ⊤))ˣ) :
    Sheaf.H.{u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} V) 0 :=
  (Sheaf.H.equiv₀ (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} V) (isTerminalEtaleMkId V)).symm
    (Stacks.Kummer.ofUnit.{u, u + 1} (U := Scheme.Etale.mk (𝟙 V)) a)

/-- **The Kummer class `κ(a) ∈ H¹(V, ℤ/N)` of a unit `a`**: the Kummer coboundary of
`a ∈ H⁰(V, 𝐆_m)` in `H¹(V, μ_N)`, read in `Ext¹(Λ_V, Λ_V)` through `μ_N ≅ ℤ/N`, `ζ ↦ 1`. -/
@[sga "7 IX 9.4.3" "special case"]
def kummerUnitClass {V : Scheme.{u}} (fV : V ⟶ Spec (.of k)) (a : (Γ(V, ⊤))ˣ) :
    Ext (unitSheaf (X := V) N) (unitSheaf (X := V) N) 1 :=
  (Stacks.Picard.extRootsOfUnityAddEquiv fV hζ (ne_zero_of_isUnit hN) 1).symm
    (Stacks.Kummer.kummerδ.{u + 1, u, u + 1} V (ne_zero_of_isUnit hN)
      (Stacks.Kummer.isUnit_natCast_globalSections V N fV hN) 0 (unitH0Class a))

end Kummer

section Divisor

variable {k : Type u} [Field k] {N : ℕ} {ζ : k} (hζ : IsPrimitiveRoot ζ N) (hN : IsUnit (N : k))
  {U V W : Scheme.{u}} (fU : U ⟶ Spec (.of k)) (j : V ⟶ U) [IsOpenImmersion j]
  (i : W ⟶ U) [IsClosedImmersion i] (hij : Set.range j.base = (Set.range i.base)ᶜ)

/-- The restriction `E_W = i_* i⁻¹` to a closed subscheme `i : W ⟶ U`, an exact endofunctor of
`Λ`-modules on `U_étale`. -/
abbrev closedRestriction : EtaleModules.{u, 0} (ZMod N) U ⥤ EtaleModules.{u, 0} (ZMod N) U :=
  etaleModuleInverseImage.{u, 0} (ZMod N) i ⋙ etaleModuleDirectImage.{u, 0} (ZMod N) i

include hij in
/-- The sequence `0 → j_! j⁻¹ Λ_U → Λ_U → i_* i⁻¹ Λ_U → 0` of Tag 095L, as a short complex. -/
abbrev divisorShortComplex : ShortComplex (EtaleModules.{u, 0} (ZMod N) U) :=
  ShortComplex.mk ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) j).counit.app (unitSheaf N))
    ((etaleModuleInverseImageAdj.{u, 0} (ZMod N) i).unit.app (unitSheaf N))
    (etaleModuleExtensionByZero_counit_comp_inverseImage_unit (ZMod N) i j hij _)

/-- The sequence `0 → j_! j⁻¹ Λ_U → Λ_U → i_* i⁻¹ Λ_U → 0` is short exact. -/
theorem divisorShortComplex_shortExact : (divisorShortComplex (N := N) j i hij).ShortExact :=
  (shortExact_etaleModuleExtensionByZero_directImage (ZMod N) i j hij _).choose_spec

/-- `j⁻¹ Λ_U ≅ Λ_V` for the restriction along an étale `j`. -/
abbrev restrictionUnitSheafIso :
    (etaleModuleRestriction.{u, 0} (ZMod N) j).obj (unitSheaf (X := U) N) ≅ unitSheaf (X := V) N :=
  ((etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod N) j).app (unitSheaf (X := U) N)).symm ≪≫
    (etaleModuleInverseImageConstantIso.{u, 0} (ZMod N) j).app
      (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N)))

/-- **The Kummer divisor class** `δ(a) ∈ Ext²_U(i_* i⁻¹ Λ_U, Λ_U)` of a unit `a` on the open
`j : V ⟶ U` with closed complement `i : W ⟶ U`: the class of the sequence
`0 → j_! j⁻¹ Λ_U → Λ_U → i_* i⁻¹ Λ_U → 0` followed by `j_!(κ(a))` and the counit
`j_! j⁻¹ Λ_U ⟶ Λ_U`. -/
def kummerDivisorClass (a : (Γ(V, ⊤))ˣ) :
    Ext ((closedRestriction (N := N) i).obj (unitSheaf N)) (unitSheaf (X := U) N) 2 :=
  (divisorShortComplex_shortExact j i hij).extClass.comp
    ((((Ext.mk₀ (restrictionUnitSheafIso (N := N) j).hom).comp
        ((kummerUnitClass hζ hN (j ≫ fU) a).comp
          (Ext.mk₀ (restrictionUnitSheafIso (N := N) j).inv) (add_zero 1))
          (zero_add 1)).mapExactFunctor
        (etaleModuleExtensionByZero.{u, 0} (ZMod N) j)).comp
      (Ext.mk₀ ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) j).counit.app (unitSheaf N)))
      (add_zero 1)) (by norm_num)

end Divisor

section Flag

variable {k : Type u} [Field k] {N : ℕ} {ζ : k} (hζ : IsPrimitiveRoot ζ N) (hN : IsUnit (N : k))
  {U : Scheme.{u}} (fU : U ⟶ Spec (.of k))

/-- **Divisor data on `U`**: an open immersion `j : V ⟶ U`, a closed immersion `i : W ⟶ U` onto
the complement, and a unit `a` on `V`. -/
structure DivisorDatum (U : Scheme.{u}) where
  /-- The open part. -/
  V : Scheme.{u}
  /-- The closed part. -/
  W : Scheme.{u}
  /-- The open immersion. -/
  j : V ⟶ U
  [isOpenImmersion : IsOpenImmersion j]
  /-- The closed immersion. -/
  i : W ⟶ U
  [isClosedImmersion : IsClosedImmersion i]
  /-- The open part is the complement of the closed part. -/
  range_eq : Set.range j.base = (Set.range i.base)ᶜ
  /-- The unit on the open part. -/
  a : (Γ(V, ⊤))ˣ

attribute [instance] DivisorDatum.isOpenImmersion DivisorDatum.isClosedImmersion

/-- A function `φ` is a unit on its basic open `D(φ)`. -/
theorem isUnit_ι_appTop_basicOpen (φ : Γ(U, ⊤)) : IsUnit ((U.basicOpen φ).ι.appTop φ) := by
  rw [Scheme.Opens.ι_appTop]
  have key : ∀ (O : U.Opens) (_ : O = U.basicOpen φ) (hle : O ≤ ⊤),
      IsUnit (U.presheaf.map (homOfLE hle).op φ) := by
    rintro O rfl hle
    exact U.toRingedSpace.isUnit_res_basicOpen φ
  exact key _ (by simp) _

/-- **The divisor datum of a function** `φ` on `U`: the basic open `D(φ)` with the unit
`φ|_{D(φ)}`, and a closed immersion `i : W ⟶ U` onto the zero set of `φ`. -/
def DivisorDatum.ofFunction (φ : Γ(U, ⊤)) {W : Scheme.{u}} (i : W ⟶ U) [IsClosedImmersion i]
    (hi : Set.range (U.basicOpen φ).ι.base = (Set.range i.base)ᶜ) : DivisorDatum U where
  V := U.basicOpen φ
  W := W
  j := (U.basicOpen φ).ι
  i := i
  range_eq := hi
  a := (isUnit_ι_appTop_basicOpen φ).unit

/-- The sheaf `E_0 ⋯ E_{d-1} Λ_U` on which a flag of `d` divisor data is supported. -/
def flagSheaf : {d : ℕ} → (Fin d → DivisorDatum U) → EtaleModules.{u, 0} (ZMod N) U
  | 0, _ => unitSheaf N
  | _ + 1, D => (closedRestriction (N := N) (D 0).i).obj (flagSheaf (fun m => D m.succ))

/-- The canonical map `Λ_U ⟶ E_0 ⋯ E_{d-1} Λ_U`, a composite of units of adjunctions. -/
def flagUnit : {d : ℕ} → (D : Fin d → DivisorDatum U) → (unitSheaf N ⟶ flagSheaf (N := N) D)
  | 0, _ => 𝟙 _
  | _ + 1, D => (etaleModuleInverseImageAdj.{u, 0} (ZMod N) (D 0).i).unit.app (unitSheaf N) ≫
      (closedRestriction (N := N) (D 0).i).map (flagUnit (fun m => D m.succ))

/-- **The Kummer flag class** `γ ∈ Ext^{2d}_U(E_0 ⋯ E_{d-1} Λ_U, Λ_U)` of `d` divisor data:
`γ = E_0(γ') ∘ δ(a_0)`, with `γ'` the class of the remaining data and `δ(a_0)` the Kummer
divisor class of the first. -/
def kummerFlagClass : {d : ℕ} → (D : Fin d → DivisorDatum U) →
    Ext (flagSheaf (N := N) D) (unitSheaf (X := U) N) (2 * d)
  | 0, _ => Ext.mk₀ (𝟙 _)
  | d + 1, D => ((kummerFlagClass (fun m => D m.succ)).mapExactFunctor
      (closedRestriction (N := N) (D 0).i)).comp
        (kummerDivisorClass hζ hN fU (D 0).j (D 0).i (D 0).range_eq (D 0).a) (by ring)

end Flag

section Point

variable {k : Type u} [Field k] {N : ℕ} {ζ : k} (hζ : IsPrimitiveRoot ζ N) (hN : IsUnit (N : k))
  {Y U : Scheme.{u}} (fY : Y ⟶ Spec (.of k)) (n : U ⟶ Y) [IsOpenImmersion n]

/-- A map `z : Λ_Y ⟶ n_! P` is **adapted** to `u : Λ_U ⟶ P` if its restriction to `U` is `u`,
through `n⁻¹ Λ_Y ≅ Λ_U` and the unit `P ≅ n⁻¹ n_! P`. -/
def IsAdapted {P : EtaleModules.{u, 0} (ZMod N) U} (u : unitSheaf N ⟶ P)
    (z : unitSheaf (X := Y) N ⟶ (etaleModuleExtensionByZero.{u, 0} (ZMod N) n).obj P) : Prop :=
  (etaleModuleRestriction.{u, 0} (ZMod N) n).map z =
    (restrictionUnitSheafIso (N := N) n).hom ≫ u ≫
      (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) n).unit.app P

/-- **The Kummer point class** in `H^{2d}(Y, Λ) = Ext^{2d}(Λ_Y, Λ_Y)` of a flag of `d` divisor
data on an open `n : U ⟶ Y`, through a map `z : Λ_Y ⟶ n_!(E_0 ⋯ E_{d-1} Λ_U)`: the Yoneda product
of `z` with the image of the Kummer flag class under the adjunction `n_! ⊣ n⁻¹`. -/
def kummerPointClass {d : ℕ} (D : Fin d → DivisorDatum U)
    (z : unitSheaf (X := Y) N ⟶
      (etaleModuleExtensionByZero.{u, 0} (ZMod N) n).obj (flagSheaf (N := N) D)) :
    Ext (unitSheaf (X := Y) N) (unitSheaf (X := Y) N) (2 * d) :=
  (Ext.mk₀ z).comp (Stacks.ExtAdjunction.extMap
    (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) n) _ _ (2 * d)
    ((kummerFlagClass hζ hN (n ≫ fY) D).comp
      (Ext.mk₀ (restrictionUnitSheafIso (N := N) n).inv) (add_zero _))) (zero_add _)

end Point

/-- **Independence and generation of Kummer point classes** at level `ℤ/N`, over the field `k`.
For every connected `Y` smooth of relative dimension `d` and proper over `k` and every primitive
`N`-th root of unity `ζ` with `N` invertible in `k`, there is a class `η ∈ H^{2d}(Y, ℤ/N)` which
generates `H^{2d}(Y, ℤ/N)` and is the Kummer point class of every point with respect to every
étale coordinate system: for an open `n : U ⟶ Y`, functions `φ : Fin d → Γ(U, 𝒪_U)` defining an
étale morphism `U ⟶ 𝐀^d_k` whose zero set is a single point, and closed immersions
`i_m : W_m ⟶ U` onto the zero sets of the `φ_m`, a map `z : Λ_Y ⟶ n_!(E_0 ⋯ E_{d-1} Λ_U)`
adapted to the canonical one exists, and the Kummer point class through any such `z` is `η`.

This is the top-degree cycle class of a point (SGA 4½, *Cycle*): the Kummer flag class of an
étale coordinate system centred at `y` is the local fundamental class of `y`, and on a connected
smooth proper `Y` all points have the same class, which generates `H^{2d}(Y, ℤ/N)`. -/
def PointClassIndependence (k : Type u) [Field k] (N : ℕ) : Prop :=
  ∀ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of k)) [IsProper g] (d : ℕ) [SmoothOfRelativeDimension d g]
    [ConnectedSpace Y] {ζ : k} (hζ : IsPrimitiveRoot ζ N) (hN : IsUnit (N : k)),
    ∃ η : Ext (unitSheaf (X := Y) N) (unitSheaf (X := Y) N) (2 * d),
      (∀ x : Ext (unitSheaf (X := Y) N) (unitSheaf (X := Y) N) (2 * d), ∃ c : ZMod N, x = c • η) ∧
      ∀ (U : Scheme.{u}) (n : U ⟶ Y) [IsOpenImmersion n] (φ : Fin d → Γ(U, ⊤)),
        Etale (U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
          (MvPolynomial.eval₂Hom ((Scheme.ΓSpecIso (.of k)).inv ≫ (n ≫ g).appTop).hom φ))) →
        ∀ y : U, (∀ x : U, (∀ m, x ∉ U.basicOpen (φ m)) ↔ x = y) →
        ∀ (W : Fin d → Scheme.{u}) (i : ∀ m, W m ⟶ U) [∀ m, IsClosedImmersion (i m)]
          (hi : ∀ m, Set.range (U.basicOpen (φ m)).ι.base = (Set.range (i m).base)ᶜ),
          (∃ z, IsAdapted n (flagUnit (N := N)
              (fun m => DivisorDatum.ofFunction (φ m) (i m) (hi m))) z) ∧
          ∀ z, IsAdapted n (flagUnit (N := N)
              (fun m => DivisorDatum.ofFunction (φ m) (i m) (hi m))) z →
            kummerPointClass hζ hN g n (fun m => DivisorDatum.ofFunction (φ m) (i m) (hi m)) z = η

end Stacks.EtaleCohomology.KummerFlag

end
