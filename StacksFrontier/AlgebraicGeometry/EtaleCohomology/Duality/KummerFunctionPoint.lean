module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerPointTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerPointAdapted

/-!
# Kummer point classes of functions fixed up to a power

Let `U` be an affine irreducible scheme, `φ_0, …, φ_{d-1}` functions on `U` and `D` the flag of
divisor data of the `φ_m` (`D(φ_m)` with the unit `φ_m`, and the zero scheme
`Spec(Γ(U)/φ_m)`: `Stacks.EtaleCohomology.KummerFlag.functionDatum`). Let `π : Y ⟶ Y` be a
morphism over `k` restricting to `g : U ⟶ U` along an open immersion `n : U ⟶ Y`, cartesian, with
`g^♯ φ_m = φ_m^e`. Then `g` preserves the open and closed parts of every datum and raises the
units to the `e`-th power, so the transport of Kummer point classes
(`Stacks.EtaleCohomology.KummerFlag.constantExtRestriction_kummerPointClass`) applies with
`D' = D`; if the adapted map `z` is unique, the restriction along `π` of the Kummer point class
of `(D, z)` is `e^d` times itself
(`Stacks.EtaleCohomology.KummerFlag.constantExtRestriction_kummerPointClass_functionDatum`).

## Main definitions

* `Stacks.EtaleCohomology.KummerFlag.zeroSchemeι`: `Spec(Γ(U)/φ) ⟶ U`.
* `Stacks.EtaleCohomology.KummerFlag.functionDatum`

## Main results

* `Stacks.EtaleCohomology.KummerFlag.constantExtRestriction_kummerPointClass_functionDatum`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology.KummerFlag

section Zero

variable {U : Scheme.{u}} [IsAffine U]

/-- The closed immersion of the zero scheme `Spec(Γ(U, 𝒪)/φ) ⟶ U` of a function `φ` on an
affine scheme `U`. -/
def zeroSchemeι (φ : Γ(U, ⊤)) : Spec (.of (Γ(U, ⊤) ⧸ Ideal.span {φ})) ⟶ U :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ U.isoSpec.inv

/-- The zero scheme of a function is a closed subscheme. -/
instance (φ : Γ(U, ⊤)) : IsClosedImmersion (zeroSchemeι φ) := by
  have := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {φ}))) Ideal.Quotient.mk_surjective
  unfold zeroSchemeι
  infer_instance

/-- The zero scheme of `φ` has support the complement of `D(φ)`. -/
theorem range_zeroSchemeι (φ : Γ(U, ⊤)) :
    Set.range (zeroSchemeι φ).base = ((U.basicOpen φ : U.Opens) : Set U)ᶜ := by
  have h : Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {φ})))).base =
      _root_.PrimeSpectrum.zeroLocus {φ} :=
    (_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective).trans (by simp)
  rw [zeroSchemeι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, h,
    Scheme.isoSpec_inv_image_zeroLocus, Scheme.zeroLocus_singleton]

/-- `D(φ)` is the complement of the zero scheme of `φ`. -/
theorem range_basicOpen_ι_eq_compl (φ : Γ(U, ⊤)) :
    Set.range (U.basicOpen φ).ι.base = (Set.range (zeroSchemeι φ).base)ᶜ := by
  rw [range_zeroSchemeι, compl_compl]
  exact Scheme.Opens.range_ι _

/-- **The divisor datum of a function** on an affine scheme: `D(φ)` with the unit `φ`, and the
zero scheme `Spec(Γ(U)/φ)`. -/
def functionDatum (φ : Γ(U, ⊤)) : DivisorDatum U :=
  DivisorDatum.ofFunction φ (zeroSchemeι φ) (range_basicOpen_ι_eq_compl φ)

end Zero

section Power

variable {U : Scheme.{u}} [IsAffine U] (g : U ⟶ U) {e : ℕ} (he : 0 < e) (φ : Γ(U, ⊤))
  (hφ : g.appTop φ = φ ^ e)

omit [IsAffine U] in
include he hφ in
/-- If `g^♯ φ = φ^e` with `e > 0`, then `g` maps `D(φ)` into `D(φ)`. -/
theorem basicOpen_le_preimage_basicOpen :
    U.basicOpen φ ≤ g ⁻¹ᵁ U.basicOpen φ := by
  rw [Scheme.preimage_basicOpen_top, hφ]
  exact (Scheme.basicOpen_pow (X := U) (f := φ) he).ge

omit [IsAffine U] in
include he hφ in
/-- If `g^♯ φ = φ^e` with `e > 0`, then `g^♯` maps the ideal `(φ)` into `(φ)`. -/
theorem span_le_comap_span :
    Ideal.span {φ} ≤ (Ideal.span {φ}).comap g.appTop.hom := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  show g.appTop φ ∈ Ideal.span {φ}
  rw [hφ]
  exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self φ) e he

/-- The map induced by `g` on the zero scheme of `φ`. -/
def zeroSchemeMap : Spec (.of (Γ(U, ⊤) ⧸ Ideal.span {φ})) ⟶
    Spec (.of (Γ(U, ⊤) ⧸ Ideal.span {φ})) :=
  Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ g.appTop.hom (span_le_comap_span g he φ hφ)))

/-- The map induced by `g` on the zero scheme of `φ` lies over `g`. -/
theorem zeroSchemeMap_comp :
    zeroSchemeMap g he φ hφ ≫ zeroSchemeι φ = zeroSchemeι φ ≫ g := by
  rw [zeroSchemeMap, zeroSchemeι, Category.assoc, ← Scheme.isoSpec_inv_naturality,
    ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2

/-- The map induced by `g` on `D(φ)`. -/
abbrev basicOpenMap : (functionDatum φ).V ⟶ (functionDatum φ).V :=
  g.resLE _ _ (basicOpen_le_preimage_basicOpen g he φ hφ)

/-- The map induced by `g` on `D(φ)` lies over `g`. -/
theorem basicOpenMap_comp :
    (functionDatum φ).j ≫ g = basicOpenMap g he φ hφ ≫ (functionDatum φ).j :=
  (Scheme.Hom.resLE_comp_ι _ _).symm

/-- The map induced by `g` on `D(φ)` raises the unit `φ` to the power `e`. -/
theorem units_map_basicOpenMap :
    Units.map (basicOpenMap g he φ hφ).appTop.hom (functionDatum φ).a =
      (functionDatum φ).a ^ e := by
  ext
  show (basicOpenMap g he φ hφ).appTop ((functionDatum φ).j.appTop φ) =
    ((functionDatum φ).j.appTop φ) ^ e
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← basicOpenMap_comp g he φ hφ,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hφ, map_pow]

end Power

/-- A basic open of an irreducible scheme is preconnected. -/
theorem preconnectedSpace_basicOpen {U : Scheme.{u}} [IrreducibleSpace U] (φ : Γ(U, ⊤)) :
    PreconnectedSpace (U.basicOpen φ).toScheme :=
  Subtype.preconnectedSpace ((IrreducibleSpace.isIrreducible_univ U).isPreirreducible.open_subset
    (U.basicOpen φ).isOpen (Set.subset_univ _)).isPreconnected

section Point

variable {k : Type u} [Field k] {N : ℕ} {ζ : k} (hζ : IsPrimitiveRoot ζ N) (hN : IsUnit (N : k))
  {Y U : Scheme.{u}} [IsAffine U] [IrreducibleSpace U] (fY : Y ⟶ Spec (.of k)) (π : Y ⟶ Y)
  (hπ : π ≫ fY = fY) (n : U ⟶ Y) [IsOpenImmersion n] (g : U ⟶ U) (sq : IsPullback g n n π)

include hπ sq in
/-- **The Kummer point class of functions fixed up to an `e`-th power.** If `g^♯ φ_m = φ_m^e` and
the adapted map `z` is unique, the restriction along `π` of the Kummer point class of the
function data of the `φ_m` through `z` is `e^d` times itself. -/
theorem constantExtRestriction_kummerPointClass_functionDatum [NeZero N] {d : ℕ}
    (φ : Fin d → Γ(U, ⊤)) {e : ℕ} (he : 0 < e) (hφ : ∀ m, g.appTop (φ m) = φ m ^ e)
    (z : unitSheaf (X := Y) N ⟶
      (etaleModuleExtensionByZero.{u, 0} (ZMod N) n).obj
        (flagSheaf (N := N) fun m => functionDatum (φ m)))
    (hz : IsAdapted n (flagUnit (N := N) fun m => functionDatum (φ m)) z)
    (huniq : ∀ z', IsAdapted n (flagUnit (N := N) fun m => functionDatum (φ m)) z' → z' = z) :
    constantExtRestriction (ZMod N) π (2 * d)
        (kummerPointClass hζ hN fY n (fun m => functionDatum (φ m)) z) =
      (e ^ d) • kummerPointClass hζ hN fY n (fun m => functionDatum (φ m)) z := by
  have : ∀ m, PreconnectedSpace (functionDatum (φ m)).V := fun m =>
    preconnectedSpace_basicOpen (φ m)
  have : PreconnectedSpace U := (IrreducibleSpace.connectedSpace U).toPreconnectedSpace
  obtain ⟨z', hz', h⟩ := Stacks.EtaleCohomology.KummerFlag.constantExtRestriction_kummerPointClass
    hζ hN fY π hπ n n g sq (D := fun m => functionDatum (φ m))
    (D' := fun m => functionDatum (φ m))
    (gV := fun m => basicOpenMap g he (φ m) (hφ m))
    (hV := fun m => basicOpenMap_comp g he (φ m) (hφ m))
    (gW := fun m => zeroSchemeMap g he (φ m) (hφ m))
    (hW := fun m => (zeroSchemeMap_comp g he (φ m) (hφ m)).symm)
    (q := e) (ha := fun m => units_map_basicOpenMap g he (φ m) (hφ m)) (z := z) (hz := hz)
  rw [h, huniq z' hz']

end Point

end Stacks.EtaleCohomology.KummerFlag

end
