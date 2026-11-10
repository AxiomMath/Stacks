module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.BrutalTruncation
public import StacksFrontier.Algebra.Homology.DerivedCategory.HomEqualDegree
public import StacksFrontier.Cotangent.NaiveComparisonChainMap
public import StacksFrontier.Cotangent.NaiveComparisonIndependence
public import StacksFrontier.Cotangent.NaiveComplexFunctoriality

/-!
# The explicit chain map of Tag 08UP is the comparison map of Lemma 08RB

`CommAlgCat.explicitNaiveComparison` is the map of complexes `L_{B/A} ⟶ NL_{B/A}` displayed by
Remark 08UP: the identity in cohomological degree `0`, the explicit arrow
`d f ⊗ b ↦ (d₀ f - d₁ f) b` in degree `-1`, and zero elsewhere.  The remark ends "We omit the
verification that this is the same as the map of Lemma 92.11.3", that is, that this chain map
induces an inverse of the canonical comparison map `c : NL_{B/A} ⟶ τ_{≥ -1} L_{B/A}` of Tag 08R9
at the object `A[B] → B`.  This file proves that assertion, in the form of the single equation in
`D(B)`

`Q(explicitNaiveComparison) ≫ c = (truncGEπ (-1)).app (Q L_{B/A})`.

## Main results

* `Stacks.Cotangent.explicitNaiveComparison_comp_comparison` and
  `Stacks.Cotangent.explicitNaiveComparison_comp_comparisonAtNaive`: **the equation**, which is
  the verification Tag 08UP omits — once with `Stacks.Cotangent.comparison`, the tagged map of
  Tag 08R9 at the object `A[B] → B` of `C_{B/A}`, and once with
  `Stacks.Cotangent.comparisonAtNaive`.
* `Stacks.Cotangent.exists_eq_cotangentComplex_add_faceSumTwo`:
  `Ω[P₁⁄A] ⊗[P₁] B = Im(d₁) + Im(δ₀ - δ₁ + δ₂)`, the module statement the proof rests on.
* `Stacks.Cotangent.toKaehler_comp_cotangentSpaceMap`: `Algebra.Extension.toKaehler` is natural
  in the extension.

## Implementation notes

**The reduction.**  Write `f` for `CommAlgCat.explicitNaiveComparison`, `e` for
`Stacks.Cotangent.evalCone` at `A[B] → B` along the morphism of extensions given by the identity
of `A[B]` — legitimate by `Stacks.Cotangent.comparison_eq_comparisonOfHom`, the comparison map not
depending on the chosen morphism — and `ι` for `Stacks.Cotangent.cotangentConeInr`.  Since
`Stacks.Cotangent.truncGEConeIso` is `τ_{≥ -1}` of `Q ι`, the naturality of `truncGEπ` turns the
equation into

`Q(f ≫ e) ≫ (truncGEπ (-1)).app (Q cone(d)) = Q(ι) ≫ (truncGEπ (-1)).app (Q cone(d))`,

that is, into the vanishing of `Q(g) ≫ (truncGEπ (-1)).app (Q cone(d))` for the difference
`g := f ≫ e - ι`.  Composing with `truncGEπ` is what puts the target in `D^{≥ -1}(B)` —
`CategoryTheory.Triangulated.TStructure.isGE_truncGE_obj` — so no cohomological vanishing for
`cone(d)` itself is needed.

**Why that vanishes.**  `g` is zero in cohomological degree `0`, both maps being the identity of
`Ω[P₀⁄A] ⊗[P₀] B` there, so it factors through the brutal quotient
`CochainComplex.brutalTrunc (cotangentComplex A B) 0`, which is strictly supported in degrees
`≤ -1`.  A map of `D(B)` from an object of `D^{≤ -1}` to an object of `D^{≥ -1}` is zero as soon
as it is zero on `H^{-1}`
(`DerivedCategory.eq_zero_of_isLE_of_isGE_of_homologyFunctor_map_eq_zero`), and the brutal
quotient has a zero term in degree `0`, so its `H^{-1}` is its own degree `-1` term modulo
boundaries; the whole matter is therefore the vanishing of
`g_{-1} ≫ (cotangentCone A B).pOpcycles (-1)`.

**That vanishing, concretely.**  In degree `-1` the difference is `inl ∘ c - inr`, with `c` the
explicit arrow `CommAlgCat.naiveCotangentComparison`.  Mathlib's cone differential sends `(y, ξ)`
to `(-(δ₀ - δ₁) y, d₁ y + (δ₀ - δ₁ + δ₂) ξ)`, so for `ω` in `Ω[P₁⁄A] ⊗[P₁] B` written as
`ω = d₁ y + (δ₀ - δ₁ + δ₂) ξ` the element `(-y, -ξ)` is carried to `((δ₀ - δ₁) y, -ω)`, which is
the value of the difference at `ω`: the arrow `c` agrees with `δ₀ - δ₁` on the image of `d₁`
(`Algebra.Extension.Cotangent.map_sub_map`) and annihilates `δ₀ - δ₁ + δ₂`
(`CommAlgCat.naiveCotangentComparison_faceSum`).  The decomposition of `ω` is
`Stacks.Cotangent.exists_hub_decomposition`; it requires a *choice* of `y` and `ξ` and is not
linear in `ω`, which is why the argument has to pass through `H^{-1}` and cannot be replaced by a
chain homotopy.

**The two spellings of `NL_{B/A}`.**  `CommAlgCat.explicitNaiveComparison` lands in
`Algebra.Extension.naiveComplex (CommAlgCat.standardResolutionExtension A B 0)` while
`Stacks.Cotangent.comparisonAtNaive` starts at
`Algebra.Extension.naiveComplex (Stacks.Cotangent.conormalExtension A B (op ⦋0⦌))`.  The two
extensions have the same ring and the same augmentation and differ only in their set-theoretic
section — the iterated variables of `CommAlgCat.standardResolutionSection` against a
`Classical.choice` of a preimage — and the section is *not* invisible to Mathlib's
`Algebra.Extension`: `Algebra.Extension.Cotangent.module` is defined through `σ`, so the two
conormal modules are different objects of `ModuleCat ↥B`, carrying the same underlying group with
two scalar actions that agree only up to the relation `σ(r) - σ'(r) ∈ ker`.  The two complexes are
therefore *not* equal, and the identity of `A[B]` is used as a morphism of extensions both ways
(`Stacks.Cotangent.toConormalExtension`, `Stacks.Cotangent.ofConormalExtension`); it induces the
isomorphism `Stacks.Cotangent.naiveSpellingIso` of the two spellings, which is what the second
form of the equation inserts.  All identifications below are made in an arbitrary simplicial
degree, where they hold by `rfl` without asking the unifier to evaluate the standard resolution at
a simplex.

## References

* [Stacks Project, Tag 08UP](https://stacks.math.columbia.edu/tag/08UP)
* [Stacks Project, Tag 08RB](https://stacks.math.columbia.edu/tag/08RB)
* [Stacks Project, Tag 08R9](https://stacks.math.columbia.edu/tag/08R9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology
open scoped TensorProduct

universe u v

/-- A transport along an equality of modules, evaluated at an element: if `x` and `y` correspond
under `h`, then `eqToHom h` carries `x` to `y`. -/
theorem ModuleCat.eqToHom_apply_of_heq {R : Type*} [Ring R] {X Y : ModuleCat.{v} R} (h : X = Y)
    (x : X) (y : Y) (hxy : HEq x y) : eqToHom h x = y := by
  subst h
  rw [eqToHom_refl, ModuleCat.id_apply]
  exact eq_of_heq hxy

/-- Transporting forwards and back is the identity. -/
theorem ModuleCat.eqToHom_symm_eqToHom_apply {R : Type*} [Ring R] {X Y : ModuleCat.{v} R}
    (h : X = Y) (x : X) : eqToHom h.symm (eqToHom h x) = x := by
  rw [← ModuleCat.comp_apply, eqToHom_trans, eqToHom_refl, ModuleCat.id_apply]

namespace Stacks.Cotangent

open CommAlgCat

attribute [local instance] HasDerivedCategory.standard

/-! ### Naturality of `Algebra.Extension.toKaehler` -/

/-- **`Algebra.Extension.toKaehler` is natural in the extension**: a morphism of extensions of the
same algebra `S` over the same base `R` commutes with the projections onto `Ω[S⁄R]`.  Both maps
send a pure differential `1 ⊗ d x` to `d` of the image of `x` in `S`, and a morphism of extensions
does not change that image. -/
theorem toKaehler_comp_cotangentSpaceMap {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {P P' : Algebra.Extension R S} (f : P.Hom P') :
    P'.toKaehler ∘ₗ Algebra.Extension.CotangentSpace.map f = P.toKaehler := by
  refine Algebra.Extension.cotangentSpace_hom_ext P _ _ fun x => ?_
  rw [LinearMap.comp_apply, Algebra.Extension.CotangentSpace.map_tmul, map_one,
    toKaehler_one_tmul_D, toKaehler_one_tmul_D, Algebra.Extension.Hom.toAlgHom_apply]
  simp

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)

/-! ### The two spellings of the extension `Pₙ → B` -/

/-- The identity of `Pₙ`, read as a morphism from `CommAlgCat.standardResolutionExtension A B n`
to `Stacks.Cotangent.conormalExtension A B (op ⦋n⦌)`: the two extensions have the same ring and
the same augmentation, and differ only in their set-theoretic section. -/
def toConormalExtension (n : ℕ) :
    (standardResolutionExtension A B n).Hom (conormalExtension A B (op ⦋n⦌)) where
  toRingHom := RingHom.id _
  toRingHom_algebraMap _ := rfl
  algebraMap_toRingHom _ := rfl

/-- The identity of `Pₙ`, read in the other direction. -/
def ofConormalExtension (n : ℕ) :
    (conormalExtension A B (op ⦋n⦌)).Hom (standardResolutionExtension A B n) where
  toRingHom := RingHom.id _
  toRingHom_algebraMap _ := rfl
  algebraMap_toRingHom _ := rfl

/-- `ofConormalExtension` is a left inverse of `toConormalExtension`. -/
theorem ofConormalExtension_comp_toConormalExtension (n : ℕ) :
    (ofConormalExtension A B n).comp (toConormalExtension A B n) =
      Algebra.Extension.Hom.id (standardResolutionExtension A B n) := by
  apply Algebra.Extension.Hom.ext
  rfl

/-- `ofConormalExtension` is a right inverse of `toConormalExtension`. -/
theorem toConormalExtension_comp_ofConormalExtension (n : ℕ) :
    (toConormalExtension A B n).comp (ofConormalExtension A B n) =
      Algebra.Extension.Hom.id (conormalExtension A B (op ⦋n⦌)) := by
  apply Algebra.Extension.Hom.ext
  rfl

/-- The identity of `Pₙ` commutes with the faces of the standard resolution, read in the two
spellings. -/
theorem toConormalExtension_comp_face (n : ℕ) (i : Fin (n + 2)) :
    (toConormalExtension A B n).comp (standardResolutionExtensionFace A B n i) =
      (conormalExtensionHom A B (SimplexCategory.δ i).op).comp
        (toConormalExtension A B (n + 1)) := by
  apply Algebra.Extension.Hom.ext
  rfl

/-- Every term of the standard resolution is a polynomial algebra over `A`, in the spelling
`CommAlgCat.standardResolutionExtension` uses. -/
theorem isPolynomialAlgebra_standardResolutionExtension_ring (n : ℕ) :
    Algebra.IsPolynomialAlgebra A (standardResolutionExtension A B n).Ring :=
  isPolynomialAlgebra_conormalExtension_ring A B (op ⦋n⦌)

/-- **The identification of the two spellings of `NL_{B/A}`**, induced by the identity of
`A[B]`. -/
def naiveSpellingIso (n : ℕ) :
    Algebra.Extension.naiveComplex (standardResolutionExtension A B n) ≅
      Algebra.Extension.naiveComplex (conormalExtension A B (op ⦋n⦌)) :=
  haveI := Algebra.Extension.isIso_naiveComplexMap (toConormalExtension A B n)
    (ofConormalExtension A B n) (ofConormalExtension_comp_toConormalExtension A B n)
    (toConormalExtension_comp_ofConormalExtension A B n)
  asIso (Algebra.Extension.naiveComplexMap (toConormalExtension A B n))

/-- The forward map of `naiveSpellingIso` is the map of naive cotangent complexes induced by
`toConormalExtension`. -/
theorem naiveSpellingIso_hom (n : ℕ) :
    (naiveSpellingIso A B n).hom =
      Algebra.Extension.naiveComplexMap (toConormalExtension A B n) := rfl

/-! ### `Ω[P₁⁄A] ⊗[P₁] B = Im(d₁) + Im(δ₀ - δ₁ + δ₂)` -/

/-- The differential of `L_{B/A}` out of simplicial degree two, read on the cotangent spaces of
the extensions `Pₙ → B`: the alternating sum `δ₀ - δ₁ + δ₂` of the three faces `P₂ → P₁`. -/
def faceSumTwo :
    (standardResolutionExtension A B 2).CotangentSpace →ₗ[B]
      (standardResolutionExtension A B 1).CotangentSpace :=
  Algebra.Extension.CotangentSpace.map (standardResolutionExtensionFace A B 1 0) -
    Algebra.Extension.CotangentSpace.map (standardResolutionExtensionFace A B 1 1) +
    Algebra.Extension.CotangentSpace.map (standardResolutionExtensionFace A B 1 2)

/-- `Algebra.Extension.toKaehler` is unchanged by `δ₀ - δ₁ + δ₂`: being natural in the extension
it is carried to itself by each of the three faces, and the three signs add up to one. -/
theorem toKaehler_faceSumTwo (ξ : (standardResolutionExtension A B 2).CotangentSpace) :
    (standardResolutionExtension A B 1).toKaehler (faceSumTwo A B ξ) =
      (standardResolutionExtension A B 2).toKaehler ξ := by
  have h : ∀ i : Fin 3, (standardResolutionExtension A B 1).toKaehler
      (Algebra.Extension.CotangentSpace.map (standardResolutionExtensionFace A B 1 i) ξ) =
      (standardResolutionExtension A B 2).toKaehler ξ := fun i => by
    have h' := LinearMap.congr_fun
      (toKaehler_comp_cotangentSpaceMap (standardResolutionExtensionFace A B 1 i)) ξ
    simpa using h'
  rw [faceSumTwo, LinearMap.add_apply, LinearMap.sub_apply, map_add, map_sub, h 0, h 1, h 2]
  abel

/-- **`Ω[P₁⁄A] ⊗[P₁] B = Im(d₁) + Im(δ₀ - δ₁ + δ₂)`.**  Every base-changed differential in
simplicial degree one is the sum of something in the image of `d : 𝒥₁/𝒥₁² → Ω[P₁⁄A] ⊗[P₁] B` and
something in the image of the differential of `L_{B/A}` out of simplicial degree two.

The reason is that `Coker(d)` is the constant simplicial module on `Ω[B⁄A]`, whose differential
out of degree two is the identity: concretely, `Algebra.Extension.toKaehler` is natural in the
extension, so it carries `δ₀ - δ₁ + δ₂` to itself and is surjective already on
`Ω[P₂⁄A] ⊗[P₂] B`, and the kernel of `toKaehler` is the image of `d`. -/
theorem exists_eq_cotangentComplex_add_faceSumTwo
    (ω : (standardResolutionExtension A B 1).CotangentSpace) :
    ∃ (y : (standardResolutionExtension A B 1).Cotangent)
      (ξ : (standardResolutionExtension A B 2).CotangentSpace),
      ω = (standardResolutionExtension A B 1).cotangentComplex y + faceSumTwo A B ξ := by
  obtain ⟨ξ, hξ⟩ := Algebra.Extension.toKaehler_surjective
    (P := standardResolutionExtension A B 2)
    ((standardResolutionExtension A B 1).toKaehler ω)
  have h0 : (standardResolutionExtension A B 1).toKaehler (ω - faceSumTwo A B ξ) = 0 := by
    rw [map_sub, toKaehler_faceSumTwo, hξ, sub_self]
  have hmem : ω - faceSumTwo A B ξ ∈
      LinearMap.range (standardResolutionExtension A B 1).cotangentComplex := by
    rw [← LinearMap.exact_iff.mp (Algebra.Extension.exact_cotangentComplex_toKaehler
      (P := standardResolutionExtension A B 1)), LinearMap.mem_ker]
    exact h0
  obtain ⟨y, hy⟩ := hmem
  refine ⟨y, ξ, ?_⟩
  rw [hy]
  abel

/-! ### The explicit arrow on the two pieces of that decomposition -/

/-- The explicit arrow `c` of Tag 08UP agrees with `δ₀ - δ₁` on the image of
`d : 𝒥₁/𝒥₁² → Ω[P₁⁄A] ⊗[P₁] B`.  This is `Algebra.Extension.Cotangent.map_sub_map` for the two
faces `P₁ → P₀`, `c` being `Algebra.Extension.Hom.sub` of them. -/
theorem naiveCotangentComparison_cotangentComplex_apply
    (y : (standardResolutionExtension A B 1).Cotangent) :
    naiveCotangentComparison A B
        ((standardResolutionExtension A B 1).cotangentComplex y) =
      Algebra.Extension.Cotangent.map (standardResolutionExtensionFace A B 0 0) y -
        Algebra.Extension.Cotangent.map (standardResolutionExtensionFace A B 0 1) y := by
  have h := LinearMap.congr_fun (Algebra.Extension.Cotangent.map_sub_map
    (standardResolutionExtensionFace A B 0 0) (standardResolutionExtensionFace A B 0 1)) y
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply] at h
  exact h.symm

/-! ### The identification of `CommAlgCat.cotangentTerm` with the two cotangent spaces -/

/-- The transport of `CommAlgCat.cotangentTerm_eq_cotangentSpace`, evaluated on a pure
differential. -/
theorem eqToHom_cotangentTermDifferential (n : ℕ)
    (p : (standardResolutionExtension A B n).Ring) :
    eqToHom (cotangentTerm_eq_cotangentSpace A B n)
        (cotangentTermDifferential A B (op ⦋n⦌) p) =
      (1 : (B : Type (max u v))) ⊗ₜ[(standardResolutionExtension A B n).Ring]
        KaehlerDifferential.D A (standardResolutionExtension A B n).Ring p :=
  ModuleCat.eqToHom_apply_of_heq _ _ _ HEq.rfl

/-- Mutually inverse morphisms of extensions give mutually inverse maps on conormal modules. -/
private theorem ofHom_cotangentMap_comp_ofHom_cotangentMap {R : Type u} {S : Type (max u v)}
    [CommRing R] [CommRing S] [Algebra R S] {P Q : Algebra.Extension.{max u v, u, max u v} R S}
    (f : P.Hom Q) (g : Q.Hom P)
    (h : f.comp g = Algebra.Extension.Hom.id Q) :
    ModuleCat.ofHom (Algebra.Extension.Cotangent.map g) ≫
      ModuleCat.ofHom (Algebra.Extension.Cotangent.map f) = 𝟙 _ := by
  refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, ModuleCat.hom_id,
    LinearMap.id_coe, id_eq]
  rw [← Algebra.Extension.Cotangent.map_comp_apply, h, Algebra.Extension.Cotangent.map_id_apply]

/-- The conormal module of `Pₙ → B`, read in the two spellings: the identity in one direction
followed by the identity in the other is the identity. -/
theorem cotangentMapBridge_comp (n : ℕ) :
    ModuleCat.ofHom (Algebra.Extension.Cotangent.map (ofConormalExtension A B n)) ≫
      ModuleCat.ofHom (Algebra.Extension.Cotangent.map (toConormalExtension A B n)) = 𝟙 _ :=
  ofHom_cotangentMap_comp_ofHom_cotangentMap _ _
    (toConormalExtension_comp_ofConormalExtension A B n)

/-- The conormal module of `Pₙ → B`, read in the two spellings, the other way round. -/
theorem cotangentMapBridge_comp' (n : ℕ) :
    ModuleCat.ofHom (Algebra.Extension.Cotangent.map (toConormalExtension A B n)) ≫
      ModuleCat.ofHom (Algebra.Extension.Cotangent.map (ofConormalExtension A B n)) = 𝟙 _ :=
  ofHom_cotangentMap_comp_ofHom_cotangentMap _ _
    (ofConormalExtension_comp_toConormalExtension A B n)

/-- The map `d` in simplicial degree `n`, read through the identification of
`CommAlgCat.cotangentTerm` with the cotangent space of
`CommAlgCat.standardResolutionExtension`. -/
theorem conormalToCotangentApp_comp_eqToHom (n : ℕ) :
    conormalToCotangentApp A B (op ⦋n⦌) ≫ eqToHom (cotangentTerm_eq_cotangentSpace A B n) =
      ModuleCat.ofHom (Algebra.Extension.Cotangent.map (ofConormalExtension A B n)) ≫
        ModuleCat.ofHom (standardResolutionExtension A B n).cotangentComplex := by
  refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective y
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
  rw [Algebra.Extension.Cotangent.map_mk, Algebra.Extension.cotangentComplex_mk]
  exact ModuleCat.eqToHom_apply_of_heq _ _ _ HEq.rfl

/-- The map `d` in simplicial degree `n`, read in the cotangent-space spelling of
`CommAlgCat.standardResolutionExtension` on both sides. -/
theorem cotangentMapBridge_comp_conormalToCotangentApp (n : ℕ) :
    ModuleCat.ofHom (Algebra.Extension.Cotangent.map (toConormalExtension A B n)) ≫
        conormalToCotangentApp A B (op ⦋n⦌) ≫
        eqToHom (cotangentTerm_eq_cotangentSpace A B n) =
      ModuleCat.ofHom (standardResolutionExtension A B n).cotangentComplex := by
  rw [conormalToCotangentApp_comp_eqToHom, ← Category.assoc, cotangentMapBridge_comp',
    Category.id_comp]

/-- `d` in simplicial degree `n`, with the transport on the right. -/
theorem cotangentMapBridge_comp_conormalToCotangentApp' (n : ℕ) :
    ModuleCat.ofHom (Algebra.Extension.Cotangent.map (toConormalExtension A B n)) ≫
        conormalToCotangentApp A B (op ⦋n⦌) =
      ModuleCat.ofHom (standardResolutionExtension A B n).cotangentComplex ≫
        eqToHom (cotangentTerm_eq_cotangentSpace A B n).symm := by
  rw [← cotangentMapBridge_comp_conormalToCotangentApp, Category.assoc, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]

/-! ### The arrow of Tag 08UP, read between the two spellings -/

/-- The explicit arrow of Tag 08UP, read as a map from `CommAlgCat.cotangentTerm` in simplicial
degree one to `Stacks.Cotangent.conormalTerm` in simplicial degree zero. -/
def bridgedComparison : cotangentTerm A B (op ⦋1⦌) ⟶ conormalTerm A B (op ⦋0⦌) :=
  eqToHom (cotangentTerm_eq_cotangentSpace A B 1) ≫
    ModuleCat.ofHom (naiveCotangentComparison A B) ≫
    evalCotangent A B (standardResolutionExtension A B 0) (toConormalExtension A B 0)

/-- **The arrow agrees with `δ₀ - δ₁` on the image of `d`**, read on an element. -/
theorem bridgedComparison_conormalToCotangentApp (y : conormalTerm A B (op ⦋1⦌)) :
    bridgedComparison A B (conormalToCotangentApp A B (op ⦋1⦌) y) =
      conormalMap A B (SimplexCategory.δ (0 : Fin 2)).op y -
        conormalMap A B (SimplexCategory.δ (1 : Fin 2)).op y := by
  have key : ∀ (i : Fin 2) (w : (standardResolutionExtension A B 1).Cotangent),
      Algebra.Extension.Cotangent.map (toConormalExtension A B 0)
          (Algebra.Extension.Cotangent.map (standardResolutionExtensionFace A B 0 i) w) =
        Algebra.Extension.Cotangent.map (conormalExtensionHom A B (SimplexCategory.δ i).op)
          (Algebra.Extension.Cotangent.map (toConormalExtension A B 1) w) := by
    intro i w
    rw [← Algebra.Extension.Cotangent.map_comp_apply,
      ← Algebra.Extension.Cotangent.map_comp_apply, toConormalExtension_comp_face]
  have hbr : Algebra.Extension.Cotangent.map (toConormalExtension A B 1)
      (Algebra.Extension.Cotangent.map (ofConormalExtension A B 1) y) = y := by
    rw [← Algebra.Extension.Cotangent.map_comp_apply,
      toConormalExtension_comp_ofConormalExtension, Algebra.Extension.Cotangent.map_id_apply]
  have h0 := ConcreteCategory.congr_hom (conormalToCotangentApp_comp_eqToHom A B 1) y
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h0
  rw [bridgedComparison]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
  rw [h0]
  change Algebra.Extension.Cotangent.map (toConormalExtension A B 0)
      (naiveCotangentComparison A B
        ((standardResolutionExtension A B 1).cotangentComplex
          (Algebra.Extension.Cotangent.map (ofConormalExtension A B 1) y))) = _
  rw [naiveCotangentComparison_cotangentComplex_apply, map_sub, key 0, key 1, hbr]
  rfl

/-- The composite of `conormalToCotangentApp` in degree one with `bridgedComparison` is the
difference `δ₀ - δ₁` of the face maps on the conormal terms. -/
theorem conormalToCotangentApp_comp_bridgedComparison :
    conormalToCotangentApp A B (op ⦋1⦌) ≫ bridgedComparison A B =
      conormalMap A B (SimplexCategory.δ (0 : Fin 2)).op -
        conormalMap A B (SimplexCategory.δ (1 : Fin 2)).op := by
  refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sub, LinearMap.sub_apply]
    using bridgedComparison_conormalToCotangentApp A B y

/-- **The arrow annihilates the image of `δ₀ - δ₁ + δ₂`.**  This is the upper square
`CommAlgCat.core_upper` of the diagram of Tag 08UP. -/
theorem faceAsTermMap_sum_comp_bridgedComparison :
    (faceAsTermMap A B 1 0 - faceAsTermMap A B 1 1 + faceAsTermMap A B 1 2) ≫
      bridgedComparison A B = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun ξ => ?_)
  have h := ConcreteCategory.congr_hom (core_upper A B) ξ
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, ModuleCat.hom_zero,
    LinearMap.zero_apply] at h
  rw [bridgedComparison]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, ModuleCat.hom_zero,
    LinearMap.zero_apply]
  rw [h, map_zero]

/-! ### The decomposition, read on `CommAlgCat.cotangentTerm` -/

/-- The differential of `L_{B/A}` out of simplicial degree two, read through the identification
of `CommAlgCat.cotangentTerm` with the cotangent spaces of the extensions. -/
theorem faceAsTermMap_sum_comp_eqToHom :
    (faceAsTermMap A B 1 0 - faceAsTermMap A B 1 1 + faceAsTermMap A B 1 2) ≫
        eqToHom (cotangentTerm_eq_cotangentSpace A B 1) =
      eqToHom (cotangentTerm_eq_cotangentSpace A B 2) ≫
        ModuleCat.ofHom (faceSumTwo A B) := by
  rw [Preadditive.add_comp, Preadditive.sub_comp, faceAsTermMap_comp_eqToHom,
    faceAsTermMap_comp_eqToHom, faceAsTermMap_comp_eqToHom, ← Preadditive.comp_sub,
    ← Preadditive.comp_add]
  rfl

/-- The differential of `L_{B/A}` out of simplicial degree two, read in the cotangent-space
spelling on both sides. -/
theorem eqToHom_symm_comp_faceAsTermMap_sum_comp_eqToHom :
    eqToHom (cotangentTerm_eq_cotangentSpace A B 2).symm ≫
        (faceAsTermMap A B 1 0 - faceAsTermMap A B 1 1 + faceAsTermMap A B 1 2) ≫
        eqToHom (cotangentTerm_eq_cotangentSpace A B 1) =
      ModuleCat.ofHom (faceSumTwo A B) := by
  rw [faceAsTermMap_sum_comp_eqToHom, ← Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp]

/-- The differential of `L_{B/A}` out of simplicial degree two, with the transport on the
right. -/
theorem eqToHom_symm_comp_faceAsTermMap_sum :
    eqToHom (cotangentTerm_eq_cotangentSpace A B 2).symm ≫
        (faceAsTermMap A B 1 0 - faceAsTermMap A B 1 1 + faceAsTermMap A B 1 2) =
      ModuleCat.ofHom (faceSumTwo A B) ≫
        eqToHom (cotangentTerm_eq_cotangentSpace A B 1).symm := by
  rw [← eqToHom_symm_comp_faceAsTermMap_sum_comp_eqToHom, Category.assoc, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- **The decomposition of Tag 08UP's degree-one term, on `CommAlgCat.cotangentTerm`.**  Every
element is the image of something under `d` plus the image of something under the differential of
`L_{B/A}` out of simplicial degree two. -/
theorem exists_hub_decomposition (ω : cotangentTerm A B (op ⦋1⦌)) :
    ∃ (y : conormalTerm A B (op ⦋1⦌)) (ξ : cotangentTerm A B (op ⦋2⦌)),
      ω = conormalToCotangentApp A B (op ⦋1⦌) y +
        (faceAsTermMap A B 1 0 - faceAsTermMap A B 1 1 + faceAsTermMap A B 1 2) ξ := by
  obtain ⟨y₁, ξ₁, hyξ⟩ := exists_eq_cotangentComplex_add_faceSumTwo A B
    (eqToHom (cotangentTerm_eq_cotangentSpace A B 1) ω)
  refine ⟨Algebra.Extension.Cotangent.map (toConormalExtension A B 1) y₁,
    eqToHom (cotangentTerm_eq_cotangentSpace A B 2).symm ξ₁, ?_⟩
  have e1 := ConcreteCategory.congr_hom
    (cotangentMapBridge_comp_conormalToCotangentApp' A B 1) y₁
  have e2 := ConcreteCategory.congr_hom (eqToHom_symm_comp_faceAsTermMap_sum A B) ξ₁
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at e1 e2
  rw [e1, e2, ← map_add, ← hyξ]
  exact (ModuleCat.eqToHom_symm_eqToHom_apply (cotangentTerm_eq_cotangentSpace A B 1) ω).symm

/-! ### The conormal complex in cohomological degrees `-1` and `0` -/

/-- In cohomological degree `-1` the conormal complex is `𝒥₁/𝒥₁²`. -/
def conormalComplexXNegOneIso :
    (conormalComplex A B).X (-1) ≅ conormalTerm A B (op ⦋1⦌) :=
  HomologicalComplex.extendXIso _ (ComplexShape.embeddingUpIntLE (0 : ℤ)) (i := 1) (by simp)

/-- The differential of the conormal simplicial module out of simplicial degree one is
`δ₀ - δ₁`. -/
theorem objD_conormal_zero :
    AlternatingFaceMapComplex.objD (conormalSimplicialModule A B) 0 =
      conormalMap A B (SimplexCategory.δ (0 : Fin 2)).op -
        conormalMap A B (SimplexCategory.δ (1 : Fin 2)).op := by
  change ∑ i : Fin 2, ((-1 : ℤ) ^ (i : ℕ)) • _ = _
  rw [Fin.sum_univ_two]
  simp [SimplicialObject.δ, conormalSimplicialModule, sub_eq_add_neg]
  abel

/-- The differential of the conormal complex from cohomological degree `-1` to `0`, as
`δ₀ - δ₁`. -/
theorem conormalComplex_d_negOne_zero :
    (conormalComplex A B).d (-1) 0 =
      (conormalComplexXNegOneIso A B).hom ≫
        (conormalMap A B (SimplexCategory.δ (0 : Fin 2)).op -
          conormalMap A B (SimplexCategory.δ (1 : Fin 2)).op) ≫
        (conormalComplexXZeroIso A B).inv := by
  rw [← objD_conormal_zero]
  change ((conormalMooreComplex A B).extend (ComplexShape.embeddingUpIntLE (0 : ℤ))).d _ _ = _
  rw [HomologicalComplex.extend_d_eq _ (ComplexShape.embeddingUpIntLE (0 : ℤ))
    (i := 1) (j := 0) (by simp) (by simp), alternatingFaceMapComplex_obj_d]
  rfl

/-- In cohomological degree `-1` the map `𝒥/𝒥² → Ω` is `d` in simplicial degree one. -/
theorem conormalToCotangentComplex_f_negOne :
    (conormalToCotangentComplex A B).f (-1) =
      (conormalComplexXNegOneIso A B).hom ≫ conormalToCotangentApp A B (op ⦋1⦌) ≫
        (cotangentComplex_degreeIso A B 1).inv := by
  rw [conormalToCotangentComplex,
    HomologicalComplex.extendMap_f _ (ComplexShape.embeddingUpIntLE (0 : ℤ))
      (i := 1) (i' := -1) (by simp)]
  rfl

/-! ### The difference of the two maps into the cone -/

/-- The evaluation at `A[B] → B` along the identity of `A[B]`, read on the spelling of
`NL_{B/A}` that `CommAlgCat.explicitNaiveComparison` lands in. -/
abbrev evalConeSelf :
    Algebra.Extension.naiveComplex (standardResolutionExtension A B 0) ⟶ cotangentCone A B :=
  evalCone A B (standardResolutionExtension A B 0) (toConormalExtension A B 0)

/-- The difference `f ≫ e - ι`: the explicit chain map followed by the evaluation at
`A[B] → B`, against the cone inclusion of `L_{B/A}`. -/
def coneDiff : cotangentComplex A B ⟶ cotangentCone A B :=
  explicitNaiveComparison A B ≫ evalConeSelf A B - cotangentConeInr A B

/-- The identity of `Pₙ`, read on cotangent spaces, sends a pure differential to the pure
differential of the image. -/
theorem cotangentSpaceMap_tmul (n : ℕ) (p : (standardResolutionExtension A B n).Ring) :
    Algebra.Extension.CotangentSpace.map (toConormalExtension A B n)
        ((1 : (B : Type (max u v))) ⊗ₜ[(standardResolutionExtension A B n).Ring]
          KaehlerDifferential.D A (standardResolutionExtension A B n).Ring p) =
      (1 : (B : Type (max u v))) ⊗ₜ[(conormalExtension A B (op ⦋n⦌)).Ring]
        KaehlerDifferential.D A (conormalExtension A B (op ⦋n⦌)).Ring
          ((toConormalExtension A B n).toRingHom p) := by
  have h := Algebra.Extension.CotangentSpace.map_tmul (toConormalExtension A B n)
    (1 : (B : Type (max u v))) p
  rw [map_one] at h
  exact h

/-- `CommAlgCat.cotangentTermDifferential` is the pure differential of the cotangent space of
`CommAlgCat.standardResolutionExtension`. -/
theorem heq_cotangentTermDifferential_tmul (n : ℕ)
    (p : (standardResolutionExtension A B n).Ring) :
    HEq (cotangentTermDifferential A B (op ⦋n⦌) p)
      ((1 : (B : Type (max u v))) ⊗ₜ[(standardResolutionExtension A B n).Ring]
        KaehlerDifferential.D A (standardResolutionExtension A B n).Ring p) := HEq.rfl

/-- The pure differentials of the two spellings of the cotangent space of `Pₙ → B` agree. -/
theorem heq_tmul_conormal (n : ℕ) (p : (standardResolutionExtension A B n).Ring) :
    HEq ((1 : (B : Type (max u v))) ⊗ₜ[(standardResolutionExtension A B n).Ring]
        KaehlerDifferential.D A (standardResolutionExtension A B n).Ring p)
      ((1 : (B : Type (max u v))) ⊗ₜ[(conormalExtension A B (op ⦋n⦌)).Ring]
        KaehlerDifferential.D A (conormalExtension A B (op ⦋n⦌)).Ring
          ((toConormalExtension A B n).toRingHom p)) := HEq.rfl

/-- The identification of `CommAlgCat.cotangentTerm` in simplicial degree zero with the cotangent
space, followed by the evaluation at the identity of `A[B]`, is the identity. -/
theorem eqToHom_comp_evalCotangentSpace :
    eqToHom (cotangentTerm_eq_cotangentSpace A B 0) ≫
        evalCotangentSpace A B (standardResolutionExtension A B 0)
          (toConormalExtension A B 0) = 𝟙 (cotangentTerm A B (op ⦋0⦌)) := by
  refine cotangentTerm_hom_ext A B (op ⦋0⦌) _ _ fun p => ?_
  rw [ModuleCat.comp_apply, ModuleCat.id_apply, eqToHom_cotangentTermDifferential A B 0 p]
  refine Eq.trans ?_ (eq_of_heq ((heq_cotangentTermDifferential_tmul A B 0 p).trans
    (heq_tmul_conormal A B 0 p)).symm)
  exact cotangentSpaceMap_tmul A B 0 p

/-- Precomposing a morphism `g` out of `CommAlgCat.cotangentTerm` in degree zero with the
identification with the cotangent space and the evaluation at the identity of `A[B]` gives `g`. -/
theorem eqToHom_comp_evalCotangentSpace_comp {Z : ModuleCat.{max u v} B}
    (g : cotangentTerm A B (op ⦋0⦌) ⟶ Z) :
    eqToHom (cotangentTerm_eq_cotangentSpace A B 0) ≫
        evalCotangentSpace A B (standardResolutionExtension A B 0)
          (toConormalExtension A B 0) ≫ g = g := by
  rw [← Category.assoc, eqToHom_comp_evalCotangentSpace, Category.id_comp]

/-- The degree-zero term of `L_{B/A}` is identified with `Ω[P₀⁄A] ⊗[P₀] B` in only one way. -/
theorem cotangentComplex_degreeIso_zero :
    cotangentComplex_degreeIso A B 0 = cotangentComplexXZeroIso A B := rfl

/-- **The difference vanishes in cohomological degree `0`**: both maps are the identity of
`Ω[P₀⁄A] ⊗[P₀] B` followed by the cone inclusion there. -/
theorem coneDiff_f_zero : (coneDiff A B).f 0 = 0 := by
  rw [coneDiff, HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f,
    explicitNaiveComparison_f, comparisonComponent_zero, comparisonDegreeZero,
    evalCone_f_zero, evalConeZero]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [eqToHom_comp_evalCotangentSpace_comp, cotangentComplex_degreeIso_zero,
    Iso.hom_inv_id_assoc, sub_self]

/-- The difference in cohomological degree `-1`: the explicit arrow into the `𝒥₀/𝒥₀²` summand of
the cone, minus the cone inclusion of `L_{B/A}`. -/
theorem coneDiff_f_negOne :
    (coneDiff A B).f (-1) =
      (cotangentComplex_degreeIso A B 1).hom ≫ bridgedComparison A B ≫
          (conormalComplexXZeroIso A B).inv ≫
          (CochainComplex.mappingCone.inl (conormalToCotangentComplex A B)).v 0 (-1)
            (by norm_num) -
        (CochainComplex.mappingCone.inr (conormalToCotangentComplex A B)).f (-1) := by
  rw [coneDiff, HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f,
    explicitNaiveComparison_f, comparisonComponent_negOne, comparisonDegreeNegOne,
    evalCone_f_negOne, evalConeNegOne, bridgedComparison]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- **In cohomological degree `-1` the difference lands in the image of the differential of the
cone out of degree `-2`.**  Writing `ω = d₁ y + (δ₀ - δ₁ + δ₂) ξ` by
`Stacks.Cotangent.exists_hub_decomposition`, the element `(-y, -ξ)` of
`𝒥₁/𝒥₁² ⊕ (Ω[P₂⁄A] ⊗[P₂] B)` is carried by the cone differential to the value of the difference
at `ω`. -/
theorem exists_d_eq_coneDiff_f_negOne (ω : (cotangentComplex A B).X (-1)) :
    ∃ z : (cotangentCone A B).X (-2),
      (coneDiff A B).f (-1) ω = (cotangentCone A B).d (-2) (-1) z := by
  obtain ⟨y, ξ, hyξ⟩ := exists_hub_decomposition A B ((cotangentComplex_degreeIso A B 1).hom ω)
  refine ⟨-((CochainComplex.mappingCone.inl (conormalToCotangentComplex A B)).v (-1) (-2)
      (by norm_num) ((conormalComplexXNegOneIso A B).inv y))
    - (CochainComplex.mappingCone.inr (conormalToCotangentComplex A B)).f (-2)
      ((cotangentComplex_degreeIso A B 2).inv ξ), ?_⟩
  have hy : (conormalComplex A B).d (-1) 0 ((conormalComplexXNegOneIso A B).inv y) =
      (conormalComplexXZeroIso A B).inv
        (bridgedComparison A B ((cotangentComplex_degreeIso A B 1).hom ω)) := by
    have e1 := ConcreteCategory.congr_hom (conormalToCotangentApp_comp_bridgedComparison A B) y
    have e2 := ConcreteCategory.congr_hom (faceAsTermMap_sum_comp_bridgedComparison A B) ξ
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at e1 e2
    rw [conormalComplex_d_negOne_zero, ModuleCat.comp_apply, ModuleCat.comp_apply,
      ModuleCat.hom_inv_apply, hyξ, map_add, e1, e2, add_zero]
  have hω : (conormalToCotangentComplex A B).f (-1) ((conormalComplexXNegOneIso A B).inv y) +
      (cotangentComplex A B).d (-2) (-1) ((cotangentComplex_degreeIso A B 2).inv ξ) = ω := by
    rw [conormalToCotangentComplex_f_negOne, cotangentComplex_d_negTwo_negOne,
      ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.comp_apply,
      ModuleCat.hom_inv_apply, ModuleCat.hom_inv_apply, ← map_add, ← hyξ,
      ModuleCat.inv_hom_apply]
  have hd : (cotangentCone A B).d (-2) (-1)
        (-((CochainComplex.mappingCone.inl (conormalToCotangentComplex A B)).v (-1) (-2)
            (by norm_num) ((conormalComplexXNegOneIso A B).inv y))
          - (CochainComplex.mappingCone.inr (conormalToCotangentComplex A B)).f (-2)
            ((cotangentComplex_degreeIso A B 2).inv ξ)) =
      (CochainComplex.mappingCone.inl (conormalToCotangentComplex A B)).v 0 (-1) (by norm_num)
          ((conormalComplex A B).d (-1) 0 ((conormalComplexXNegOneIso A B).inv y)) -
        (CochainComplex.mappingCone.inr (conormalToCotangentComplex A B)).f (-1)
          ((conormalToCotangentComplex A B).f (-1) ((conormalComplexXNegOneIso A B).inv y) +
            (cotangentComplex A B).d (-2) (-1)
              ((cotangentComplex_degreeIso A B 2).inv ξ)) := by
    have e3 : ∀ z : (conormalComplex A B).X (-1), (cotangentCone A B).d (-2) (-1)
        ((CochainComplex.mappingCone.inl (conormalToCotangentComplex A B)).v (-1) (-2)
          (by norm_num) z) =
        (CochainComplex.mappingCone.inr (conormalToCotangentComplex A B)).f (-1)
            ((conormalToCotangentComplex A B).f (-1) z) -
          (CochainComplex.mappingCone.inl (conormalToCotangentComplex A B)).v 0 (-1)
            (by norm_num) ((conormalComplex A B).d (-1) 0 z) := by
      intro z
      have h := ConcreteCategory.congr_hom (CochainComplex.mappingCone.inl_v_d
        (conormalToCotangentComplex A B) (-1) (-2) 0 (by norm_num) (by norm_num)) z
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sub,
        LinearMap.sub_apply] using h
    have e4 : ∀ z : (cotangentComplex A B).X (-2), (cotangentCone A B).d (-2) (-1)
        ((CochainComplex.mappingCone.inr (conormalToCotangentComplex A B)).f (-2) z) =
        (CochainComplex.mappingCone.inr (conormalToCotangentComplex A B)).f (-1)
          ((cotangentComplex A B).d (-2) (-1) z) := by
      intro z
      have h := ConcreteCategory.congr_hom (CochainComplex.mappingCone.inr_f_d
        (conormalToCotangentComplex A B) (-2) (-1)) z
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
    rw [map_sub, map_neg, e3, e4, map_add]
    abel
  rw [coneDiff_f_negOne]
  simp only [ModuleCat.hom_sub, LinearMap.sub_apply, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [hd, hy, hω]

/-! ### The factorisation through the brutal quotient -/

/-- The cotangent complex is concentrated in nonpositive cohomological degrees. -/
instance cotangentComplex_isStrictlyLE_zero' : (cotangentComplex A B).IsStrictlyLE 0 :=
  (CochainComplex.isStrictlyLE_iff _ 0).2 fun _ hi => cotangentComplex_isZero_pos A B _ hi

/-- The brutal truncation of the cotangent complex at degree `0` is concentrated in cohomological
degrees at most `-1`. -/
instance cotangentBrutalTrunc_isStrictlyLE :
    (CochainComplex.brutalTrunc (cotangentComplex A B) 0).IsStrictlyLE (-1) :=
  CochainComplex.isStrictlyLE_of_le _ (0 - 1) (-1) (by norm_num)

/-- The difference kills the degree-zero subcomplex of `L_{B/A}`. -/
theorem topSingleHom_comp_coneDiff :
    CochainComplex.topSingleHom (cotangentComplex A B) 0 ≫ coneDiff A B = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
  by_cases hi : i = 0
  · rw [hi, coneDiff_f_zero, comp_zero]
  · rw [CochainComplex.topSingleHom_f_of_ne _ _ i hi, zero_comp]

/-- The difference, factored through the brutal quotient. -/
def coneDiffDesc :
    CochainComplex.brutalTrunc (cotangentComplex A B) 0 ⟶ cotangentCone A B :=
  cokernel.desc (CochainComplex.topSingleHom (cotangentComplex A B) 0) (coneDiff A B)
    (topSingleHom_comp_coneDiff A B)

/-- The projection to the brutal quotient followed by `coneDiffDesc` is `coneDiff`. -/
theorem brutalTruncπ_comp_coneDiffDesc :
    CochainComplex.brutalTruncπ (cotangentComplex A B) 0 ≫ coneDiffDesc A B = coneDiff A B :=
  cokernel.π_desc _ _ _

/-- The factorisation dies in the opcycles of the cone in degree `-1`. -/
theorem coneDiffDesc_f_negOne_comp_pOpcycles :
    (coneDiffDesc A B).f (-1) ≫ (cotangentCone A B).pOpcycles (-1) = 0 := by
  have : IsIso ((CochainComplex.brutalTruncπ (cotangentComplex A B) 0).f (-1)) :=
    CochainComplex.isIso_brutalTruncπ_f _ _ (-1) (by norm_num)
  rw [← cancel_epi ((CochainComplex.brutalTruncπ (cotangentComplex A B) 0).f (-1)), comp_zero,
    ← Category.assoc, ← HomologicalComplex.comp_f, brutalTruncπ_comp_coneDiffDesc]
  refine ModuleCat.hom_ext (LinearMap.ext fun ω => ?_)
  obtain ⟨z, hz⟩ := exists_d_eq_coneDiff_f_negOne A B ω
  rw [ModuleCat.comp_apply, hz, ← ModuleCat.comp_apply, HomologicalComplex.d_pOpcycles]
  simp

/-- The factorisation is zero on `H^{-1}`. -/
theorem homologyMap_coneDiffDesc_negOne :
    HomologicalComplex.homologyMap (coneDiffDesc A B) (-1) = 0 := by
  have h : HomologicalComplex.opcyclesMap (coneDiffDesc A B) (-1) = 0 :=
    (cancel_epi ((CochainComplex.brutalTrunc (cotangentComplex.{u, v} A B) 0).pOpcycles
      (-1))).1 (by
        rw [HomologicalComplex.p_opcyclesMap, coneDiffDesc_f_negOne_comp_pOpcycles]
        exact comp_zero.symm)
  exact (cancel_mono ((cotangentCone A B).homologyι (-1))).1 (by
    rw [HomologicalComplex.homologyι_naturality, h, zero_comp]
    exact comp_zero)

/-! ### The vanishing in `D(B)` -/

/-- The factorisation vanishes in `D(B)` after the truncation `τ_{≥ -1}`: its source lies in
`D^{≤ -1}(B)`, its target in `D^{≥ -1}(B)`, and it is zero on `H^{-1}`. -/
theorem Q_coneDiffDesc_comp_truncGEπ :
    DerivedCategory.Q.map (coneDiffDesc A B) ≫
        (DerivedCategory.TStructure.t.truncGEπ (-1)).app
          (DerivedCategory.Q.obj (cotangentCone A B)) = 0 := by
  refine DerivedCategory.eq_zero_of_isLE_of_isGE_of_homologyFunctor_map_eq_zero (-1) _ ?_
  have h2 := DerivedCategory.homologyFunctorFactors_hom_naturality (coneDiffDesc A B) (-1)
  have h4 : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) (-1)).map
      (DerivedCategory.Q.map (coneDiffDesc A B)) ≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} B) (-1)).hom.app
        (cotangentCone A B) = 0 := by
    rw [h2, homologyMap_coneDiffDesc_negOne]
    exact comp_zero
  have h3 : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) (-1)).map
      (DerivedCategory.Q.map (coneDiffDesc A B)) = 0 :=
    (cancel_mono ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} B)
      (-1)).hom.app (cotangentCone A B))).1 (h4.trans zero_comp.symm)
  rw [Functor.map_comp, h3, zero_comp]

/-- The difference vanishes in `D(B)` after the truncation `τ_{≥ -1}`. -/
theorem Q_coneDiff_comp_truncGEπ :
    DerivedCategory.Q.map (coneDiff A B) ≫
        (DerivedCategory.TStructure.t.truncGEπ (-1)).app
          (DerivedCategory.Q.obj (cotangentCone A B)) = 0 := by
  rw [← brutalTruncπ_comp_coneDiffDesc, Functor.map_comp, Category.assoc,
    Q_coneDiffDesc_comp_truncGEπ, comp_zero]

/-- The two maps `f ≫ e` and `ι` into the cone agree in `D(B)` after the truncation `τ_{≥ -1}`. -/
private theorem Q_explicitNaiveComparison_comp_evalConeSelf_comp_truncGEπ :
    DerivedCategory.Q.map (explicitNaiveComparison A B ≫ evalConeSelf A B) ≫
        (DerivedCategory.TStructure.t.truncGEπ (-1)).app
          (DerivedCategory.Q.obj (cotangentCone A B)) =
      DerivedCategory.Q.map (cotangentConeInr A B) ≫
        (DerivedCategory.TStructure.t.truncGEπ (-1)).app
          (DerivedCategory.Q.obj (cotangentCone A B)) := by
  have h := Q_coneDiff_comp_truncGEπ A B
  rw [coneDiff, Functor.map_sub, Preadditive.sub_comp, sub_eq_zero] at h
  exact h

/-- The evaluation at the identity of `A[B]` on conormal modules, after the identity of `A[B]`
read in the other spelling. -/
theorem cotangentMap_comp_evalCotangent_id :
    ModuleCat.ofHom (Algebra.Extension.Cotangent.map (toConormalExtension A B 0)) ≫
        evalCotangent A B (conormalExtension A B (op ⦋0⦌))
          (Algebra.Extension.Hom.id (conormalExtension A B (op ⦋0⦌))) =
      evalCotangent A B (standardResolutionExtension A B 0) (toConormalExtension A B 0) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  change Algebra.Extension.Cotangent.map
      (Algebra.Extension.Hom.id (conormalExtension A B (op ⦋0⦌)))
      (Algebra.Extension.Cotangent.map (toConormalExtension A B 0) x) =
    Algebra.Extension.Cotangent.map (toConormalExtension A B 0) x
  rw [Algebra.Extension.Cotangent.map_id_apply]

/-- The evaluation at the identity of `A[B]` on cotangent spaces, after the identity of `A[B]`
read in the other spelling. -/
theorem cotangentSpaceMap_comp_evalCotangentSpace_id :
    ModuleCat.ofHom (Algebra.Extension.CotangentSpace.map (toConormalExtension A B 0)) ≫
        evalCotangentSpace A B (conormalExtension A B (op ⦋0⦌))
          (Algebra.Extension.Hom.id (conormalExtension A B (op ⦋0⦌))) =
      evalCotangentSpace A B (standardResolutionExtension A B 0)
        (toConormalExtension A B 0) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  change Algebra.Extension.CotangentSpace.map
      (Algebra.Extension.Hom.id (conormalExtension A B (op ⦋0⦌)))
      (Algebra.Extension.CotangentSpace.map (toConormalExtension A B 0) x) =
    Algebra.Extension.CotangentSpace.map (toConormalExtension A B 0) x
  rw [Algebra.Extension.cotangentSpace_map_id_apply]

/-! ### The equation of Tag 08UP -/

/-- `Stacks.Cotangent.truncGEConeIso` is `τ_{≥ -1}` of the cone inclusion. -/
theorem truncGEConeIso_hom :
    (truncGEConeIso A B).hom =
      (DerivedCategory.TStructure.t.truncGE (-1)).map
        (DerivedCategory.Q.map (cotangentConeInr A B)) := rfl

/-- **Stacks Project, Tag 08UP.** The explicit chain map `L_{B/A} ⟶ NL_{B/A}` of the remark
induces, in `D(B)`, a map inverse to the comparison map `c` of Lemma 08RB: composed with `c` it is
the truncation map `L_{B/A} ⟶ τ_{≥ -1} L_{B/A}`.  This is the verification the source omits ("We
omit the verification that this is the same as the map of Lemma 92.11.3"), with `c` the tagged map
`Stacks.Cotangent.comparison` of Tag 08R9 at the object `A[B] → B` of `C_{B/A}`.

The proof reduces the equation, by the naturality of `truncGEπ` and the definition of
`Stacks.Cotangent.truncGEConeIso`, to the vanishing of the difference `f ≫ e - ι` in `D(B)` after
`τ_{≥ -1}`; see the module docstring for the route. -/
@[stacks 08UP "the chain map of the remark induces the comparison map of Lemma 08RB: composed \
  with the map of Tag 08R9 at the object A[B] → B it is the truncation map \
  L_{B/A} → τ_{≥ -1} L_{B/A} in D(B)"]
theorem explicitNaiveComparison_comp_comparison :
    DerivedCategory.Q.map (explicitNaiveComparison A B) ≫
        comparison A B (standardResolutionExtension A B 0)
          (isPolynomialAlgebra_standardResolutionExtension_ring A B 0) =
      (DerivedCategory.TStructure.t.truncGEπ (-1)).app
        (DerivedCategory.Q.obj (cotangentComplex A B)) := by
  rw [comparison_eq_comparisonOfHom A B (standardResolutionExtension A B 0)
      (toConormalExtension A B 0) (isPolynomialAlgebra_standardResolutionExtension_ring A B 0),
    ← cancel_mono (truncGEConeIso A B).hom, Category.assoc,
    comparisonOfHom_comp_truncGEConeIso, truncGEConeIso_hom,
    DerivedCategory.TStructure.t.truncGEπ_naturality, ← Category.assoc, ← Functor.map_comp]
  exact Q_explicitNaiveComparison_comp_evalConeSelf_comp_truncGEπ A B

/-- **Stacks Project, Tag 08UP.** The same equation with `Stacks.Cotangent.comparisonAtNaive`,
the comparison map of Lemma 08RB at the spelling `Stacks.Cotangent.conormalExtension A B (op ⦋0⦌)`
of the presentation `A[B] → B`: the two spellings of `NL_{B/A}` differ only by the section of the
augmentation they carry, and `Stacks.Cotangent.naiveSpellingIso` is the isomorphism between them
induced by the identity of `A[B]`. -/
@[stacks 08UP "the chain map of the remark induces the comparison map of Lemma 08RB: composed \
  with comparisonAtNaive it is the truncation map L_{B/A} → τ_{≥ -1} L_{B/A} in D(B), after the \
  isomorphism naiveSpellingIso identifying the two spellings of NL_{B/A}"]
theorem explicitNaiveComparison_comp_comparisonAtNaive :
    DerivedCategory.Q.map (explicitNaiveComparison A B ≫ (naiveSpellingIso A B 0).hom) ≫
        comparisonAtNaive A B =
      (DerivedCategory.TStructure.t.truncGEπ (-1)).app
        (DerivedCategory.Q.obj (cotangentComplex A B)) := by
  have hcomp : (naiveSpellingIso A B 0).hom ≫
      evalCone A B (conormalExtension A B (op ⦋0⦌))
        (Algebra.Extension.Hom.id (conormalExtension A B (op ⦋0⦌))) = evalConeSelf A B := by
    refine HomologicalComplex.hom_ext _ _ fun i => ?_
    rw [HomologicalComplex.comp_f, naiveSpellingIso_hom, Algebra.Extension.naiveComplexMap_f,
      evalCone_f, evalCone_f]
    by_cases h1 : i = -1
    · subst h1
      rw [Algebra.Extension.naiveComplexMapComponent_negOne, evalConeComponent_negOne,
        evalConeComponent_negOne, Algebra.Extension.naiveComplexMapNegOne, evalConeNegOne,
        evalConeNegOne]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc (ModuleCat.ofHom
        (Algebra.Extension.Cotangent.map (toConormalExtension A B 0))),
        cotangentMap_comp_evalCotangent_id]
    · by_cases h2 : i = 0
      · subst h2
        rw [Algebra.Extension.naiveComplexMapComponent_zero, evalConeComponent_zero,
          evalConeComponent_zero, Algebra.Extension.naiveComplexMapZero, evalConeZero,
          evalConeZero]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [← Category.assoc (ModuleCat.ofHom
          (Algebra.Extension.CotangentSpace.map (toConormalExtension A B 0))),
          cotangentSpaceMap_comp_evalCotangentSpace_id]
      · rw [Algebra.Extension.naiveComplexMapComponent_eq_zero _ i h1 h2, zero_comp,
          evalConeComponent_eq_zero _ _ _ _ i h1 h2]
  rw [comparisonAtNaive, comparison_eq_comparisonOfHom A B (conormalExtension A B (op ⦋0⦌))
      (Algebra.Extension.Hom.id (conormalExtension A B (op ⦋0⦌))),
    ← cancel_mono (truncGEConeIso A B).hom, Category.assoc,
    comparisonOfHom_comp_truncGEConeIso, truncGEConeIso_hom,
    DerivedCategory.TStructure.t.truncGEπ_naturality, ← Category.assoc, ← Functor.map_comp,
    Category.assoc, hcomp]
  exact Q_explicitNaiveComparison_comp_evalConeSelf_comp_truncGEπ A B

end Stacks.Cotangent

end
