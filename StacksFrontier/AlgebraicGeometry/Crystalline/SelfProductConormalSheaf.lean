module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SelfProductConormalIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.DifferentialsLocallyQuasicoherent

/-!
# The isomorphism of sheaves `(Ω_{X/S})_T ≅ K/K^{[2]}`

Fix a global crystalline situation `(p, (S, I, γ), X)`, an object `(U, T, δ)` of the small
crystalline site `Cris(X/S)` and a product `(U(1), T(1), δ(1))` of it with itself, presented by a
limit binary fan with projections `pr₀, pr₁`.  Let `K ⊆ 𝒪_{T(1)}` be the ideal of the diagonal
`Δ : T ⟶ T(1)`.  This module proves the second assertion of [Stacks, Tag 07J1],
`(Ω_{X/S})_T = K/K^{[2]}`, as an isomorphism of sheaves of `𝒪_T`-modules.

The diagonal is a homeomorphism on underlying spaces, and the open of `T(1)` lying over an open
`V` of `T` is `p₀⁻¹V ⊓ p₁⁻¹V`.  The conormal modules `K/K^{[2]}` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SelfProductConormal.lean` over these opens, with the
maps induced by restriction of sections of `𝒪_{T(1)}`, form a presheaf of `𝒪_T`-modules (the
scalars act through the first coprojection, and modulo `K^{[2]}` through either); the sheaf
`K/K^{[2]}` is the sheaf of `𝒪_T`-modules it generates.  The comparison maps
`(Ω_{X/S})_T(V) → K/K^{[2]}(V)`, `d f ↦ [p₁^♯ f - p₀^♯ f]`, are compatible with restriction, so
they form a morphism of presheaves of modules, and its sheafification is a morphism of sheaves of
`𝒪_T`-modules `(Ω_{X/S})_T ⟶ K/K^{[2]}`.  It is an isomorphism because the comparison is bijective
on the affine opens of `T` lying over an affine open of `S`, which form a basis of the topology of
`T`: a morphism of presheaves that is bijective on a basis is locally injective and locally
surjective, hence inverted by sheafification.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.smallSelfProductConormalPresheaf` — the presheaf of
  `𝒪_T`-modules `V ↦ K/K^{[2]}` over `p₀⁻¹V ⊓ p₁⁻¹V`.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductConormalSheaf` — the sheaf of
  `𝒪_T`-modules `K/K^{[2]}` it generates.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductConormalPresheafComparison` and
  `restrictedCrysDifferentialsConormalPresheafComparison` — the comparison maps, as morphisms of
  presheaves of modules out of `Ω_{T/S,δ}` and out of `(Ω_{X/S})_T`.
* `Crystalline.GlobalCrystallineSituation.dpDifferentialsSheafIsoConormalSheaf` — the isomorphism
  `Ω_{T/S,δ} ≅ K/K^{[2]}` of sheaves of `𝒪_T`-modules.
* `Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentialsSheafIsoConormalSheaf` —
  **Stacks, Tag 07J1**, second assertion: `(Ω_{X/S})_T ≅ K/K^{[2]}` as sheaves of `𝒪_T`-modules.

## Main results

* `AlgebraicGeometry.Scheme.isIso_sheafification_map_of_bijective_nhds` — a morphism of presheaves
  of modules on a scheme that is bijective on a neighbourhood basis of opens becomes an
  isomorphism after sheafification.

## References

* [Stacks Project, Tag 07J1](https://stacks.math.columbia.edu/tag/07J1)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite PresheafOfModules
open scoped AlgebraicGeometry

universe u

/-! ### Morphisms bijective on a basis are inverted by sheafification -/

namespace AlgebraicGeometry.Scheme

/-- **A morphism of presheaves of modules on a scheme which is bijective on a neighbourhood basis
of opens is inverted by sheafification.**  Bijectivity on the opens of a basis makes the
underlying morphism of presheaves of abelian groups locally injective and locally surjective. -/
theorem isIso_sheafification_map_of_bijective_nhds {X : Scheme.{u}} {P Q : X.PresheafOfModules}
    (φ : P ⟶ Q)
    (hφ : ∀ (W : X.Opens) (x : X), x ∈ W →
      ∃ V : X.Opens, x ∈ V ∧ V ≤ W ∧ Function.Bijective (φ.app (op V)).hom) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map φ) := by
  have hinj : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map φ) := by
    constructor
    intro U s t hst x hx
    obtain ⟨V, hxV, hVU, hbij⟩ := hφ U.unop x hx
    refine ⟨V, homOfLE hVU, hbij.1 ?_, hxV⟩
    have hs := PresheafOfModules.naturality_apply φ (homOfLE hVU).op s
    have ht := PresheafOfModules.naturality_apply φ (homOfLE hVU).op t
    exact hs.trans ((congrArg (Q.map (homOfLE hVU).op) hst).trans ht.symm)
  have hsurj : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map φ) := by
    constructor
    intro U s x hx
    obtain ⟨V, hxV, hVU, hbij⟩ := hφ U x hx
    obtain ⟨t, ht⟩ := hbij.2 (Q.map (homOfLE hVU).op s)
    exact ⟨V, homOfLE hVU, ⟨t, ht⟩, hxV⟩
  have hW : (Opens.grothendieckTopology X).W ((PresheafOfModules.toPresheaf _).map φ) :=
    (Opens.grothendieckTopology X).W_of_isLocallyBijective _
  have h : (MorphismProperty.isomorphisms _).inverseImage
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) φ := by
    rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
    exact hW
  exact h

end AlgebraicGeometry.Scheme

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}} {B D : CrystallineThickening S} {pr₀ pr₁ : D ⟶ B}

/-! ### The presheaf of conormal modules on `T` -/

section Presheaf

/-- **Restriction of a section of the diagonal ideal**, as a map semilinear over the restriction
of sections of `𝒪_{T(1)}` from `p₀⁻¹V ⊓ p₁⁻¹V` to `p₀⁻¹V' ⊓ p₁⁻¹V'`. -/
def smallSelfProductRestrictIdealₛₗ (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    {V V' : B.obj.thickening.target.scheme.Opens} (hle : V' ≤ V) :
    ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V)) →ₛₗ[
      (smallSelfProductRestrict pr₀ pr₁ hle).hom]
      ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V')) where
  toFun := smallSelfProductRestrictIdeal h hle
  map_add' := map_add _
  map_smul' c y := Subtype.ext (map_mul (smallSelfProductRestrict pr₀ pr₁ hle).hom c y)

/-- Restriction carries the divided square into the divided square, on representatives. -/
theorem smallSelfProductDiagonalRelations_le_comap (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    {V V' : B.obj.thickening.target.scheme.Opens} (hle : V' ≤ V) :
    smallSelfProductDiagonalRelations h V ≤
      (smallSelfProductDiagonalRelations h V').comap (smallSelfProductRestrictIdealₛₗ h hle) :=
  fun _ hy ↦ map_smallSelfProductDividedSquare_le h hle (Ideal.mem_map_of_mem _ hy)

/-- Restriction of representatives, on the quotients `K/K^{[2]}`, as a map semilinear over the
restriction of sections of `𝒪_{T(1)}`. -/
def smallSelfProductConormalMapₛₗ (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    {V V' : B.obj.thickening.target.scheme.Opens} (hle : V' ≤ V) :
    (↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V)) ⧸
        smallSelfProductDiagonalRelations h V) →ₛₗ[(smallSelfProductRestrict pr₀ pr₁ hle).hom]
      (↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V')) ⧸
        smallSelfProductDiagonalRelations h V') :=
  (smallSelfProductDiagonalRelations h V).mapQ (smallSelfProductDiagonalRelations h V')
    (smallSelfProductRestrictIdealₛₗ h hle) (smallSelfProductDiagonalRelations_le_comap h hle)

/-- **The restriction map of the conormal presheaf** `K/K^{[2]}(V) → K/K^{[2]}(V')`, induced by
restriction of sections of the diagonal ideal.  It is linear over the restriction of sections of
`𝒪_T`, since the first coprojection commutes with restriction. -/
def smallSelfProductConormalMap (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    {V V' : B.obj.thickening.target.scheme.Opens} (hle : V' ≤ V) :
    smallSelfProductConormal h V ⟶
      (ModuleCat.restrictScalars
        (B.obj.thickening.target.scheme.presheaf.map (homOfLE hle).op).hom).obj
        (smallSelfProductConormal h V') :=
  ModuleCat.ofHom (X := smallSelfProductConormal h V)
    (Y := (ModuleCat.restrictScalars
        (B.obj.thickening.target.scheme.presheaf.map (homOfLE hle).op).hom).obj
        (smallSelfProductConormal h V'))
    ({
      toFun := smallSelfProductConormalMapₛₗ h hle
      map_add' := map_add _
      map_smul' := fun c m ↦ by
        have hc := congrArg
          (fun φ : Γ(B.obj.thickening.target.scheme, V) ⟶
              Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V') ↦ φ c)
          (firstCoprojectionSection_restrict pr₀ pr₁ hle)
        simp only [CommRingCat.comp_apply] at hc
        change smallSelfProductConormalMapₛₗ h hle
            (firstCoprojectionSection pr₀ pr₁ V c •
              (id m : ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V)) ⧸
                smallSelfProductDiagonalRelations h V)) =
          firstCoprojectionSection pr₀ pr₁ V'
              (B.obj.thickening.target.scheme.presheaf.map (homOfLE hle).op c) •
            smallSelfProductConormalMapₛₗ h hle m
        rw [LinearMap.map_smulₛₗ, ← hc]
        rfl } : smallSelfProductConormal h V →ₗ[Γ(B.obj.thickening.target.scheme, V)]
          (ModuleCat.restrictScalars
            (B.obj.thickening.target.scheme.presheaf.map (homOfLE hle).op).hom).obj
            (smallSelfProductConormal h V'))

/-- The restriction map of the conormal presheaf on classes. -/
theorem smallSelfProductConormalMap_class (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    {V V' : B.obj.thickening.target.scheme.Opens} (hle : V' ≤ V)
    (y : ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V))) :
    (smallSelfProductConormalMap h hle).hom (smallSelfProductClass h V y) =
      smallSelfProductClass h V' (smallSelfProductRestrictIdeal h hle y) :=
  rfl

/-- Two representatives of classes in the conormal module over `V'` with the same underlying
section give the same class. -/
private theorem smallSelfProductClass_congr (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens)
    {y z : ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V))}
    (hyz : (y : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) = z) :
    smallSelfProductClass h V y = smallSelfProductClass h V z :=
  congrArg _ (Subtype.ext hyz)

/-- **The conormal presheaf `K/K^{[2]}` on `T`.**  Over an open `V` of `T` its sections are the
conormal module `K/K^{[2]}` of the diagonal over the open `p₀⁻¹V ⊓ p₁⁻¹V` of `T(1)`, a module
over `Γ(V, 𝒪_T)` through the first coprojection, and its restriction maps are induced by those of
`𝒪_{T(1)}`. -/
def smallSelfProductConormalPresheaf (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    B.obj.thickening.target.scheme.PresheafOfModules where
  obj V := smallSelfProductConormal h V.unop
  map {V V'} i := smallSelfProductConormalMap h i.unop.le
  map_id V := by
    ext m
    induction m using Submodule.Quotient.induction_on with
    | H y =>
      change smallSelfProductClass h V.unop (smallSelfProductRestrictIdeal h (𝟙 V).unop.le y) =
        smallSelfProductClass h V.unop y
      refine smallSelfProductClass_congr h V.unop ?_
      change D.obj.thickening.target.scheme.presheaf.map _ y.1 = y.1
      rw [Subsingleton.elim (homOfLE _) (𝟙 _), op_id,
        D.obj.thickening.target.scheme.presheaf.map_id]
      rfl
  map_comp {V V' V''} i j := by
    ext m
    induction m using Submodule.Quotient.induction_on with
    | H y =>
      change smallSelfProductClass h V''.unop
          (smallSelfProductRestrictIdeal h (i ≫ j).unop.le y) =
        smallSelfProductClass h V''.unop
          (smallSelfProductRestrictIdeal h j.unop.le (smallSelfProductRestrictIdeal h i.unop.le y))
      refine smallSelfProductClass_congr h V''.unop ?_
      change D.obj.thickening.target.scheme.presheaf.map _ y.1 =
        D.obj.thickening.target.scheme.presheaf.map _
          (D.obj.thickening.target.scheme.presheaf.map _ y.1)
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl

/-- The sections of the conormal presheaf over `V` are the conormal module over `V`. -/
theorem smallSelfProductConormalPresheaf_obj (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    (smallSelfProductConormalPresheaf h).obj (op V) = smallSelfProductConormal h V :=
  rfl

end Presheaf

/-! ### The comparison as a morphism of presheaves of modules -/

section Comparison

/-- **The comparison `Ω_{T/S,δ} ⟶ K/K^{[2]}` as a morphism of presheaves of `𝒪_T`-modules.**  Its
component over `V` is `smallSelfProductConormalComparison`, `d f ↦ [p₁^♯ f - p₀^♯ f]`; these are
compatible with restriction because the difference of the two coprojections is. -/
def smallSelfProductConormalPresheafComparison (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    dpDifferentialsPresheaf B.obj.thickening.target S.S.scheme B.obj.toBase.hom ⟶
      smallSelfProductConormalPresheaf h where
  app V := smallSelfProductConormalComparison h V.unop
  naturality {V V'} i := by
    refine dpConstDifferentials_ext fun b ↦ ?_
    have h1 := dpDifferentialsPresheaf_map B.obj.thickening.target S.S.scheme
      B.obj.toBase.hom i b
    change (smallSelfProductConormalComparison h V'.unop).hom
        ((dpDifferentialsPresheaf B.obj.thickening.target S.S.scheme B.obj.toBase.hom).map i
          ((presheafD B.obj.thickening.target S.S.scheme B.obj.toBase.hom V.unop).d b)) =
      (smallSelfProductConormalMap h i.unop.le).hom
        ((smallSelfProductConormalComparison h V.unop).hom
          ((presheafD B.obj.thickening.target S.S.scheme B.obj.toBase.hom V.unop).d b))
    rw [h1, smallSelfProductConormalComparison_d]
    refine Eq.trans ?_ (congrArg (smallSelfProductConormalMap h i.unop.le).hom
      (smallSelfProductConormalComparison_d h V.unop b)).symm
    change smallSelfProductClass h V'.unop (smallSelfProductDifferenceHom h V'.unop _) =
      (smallSelfProductConormalMap h i.unop.le).hom
        (smallSelfProductClass h V.unop (smallSelfProductDifferenceHom h V.unop b))
    rw [smallSelfProductConormalMap_class]
    exact congrArg (smallSelfProductClass h V'.unop)
      (smallSelfProductDifferenceHom_restrict h i.unop.le b).symm

/-- The component of the comparison morphism over `V` is the comparison map over `V`. -/
@[simp]
theorem smallSelfProductConormalPresheafComparison_app (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    (smallSelfProductConormalPresheafComparison h).app (op V) =
      smallSelfProductConormalComparison h V :=
  rfl

/-- **The comparison `(Ω_{X/S})_T ⟶ K/K^{[2]}` as a morphism of presheaves of `𝒪_T`-modules**:
the comparison out of `Ω_{T/S,δ}` read through the identification of [Stacks, Tag 07IZ]. -/
def restrictedCrysDifferentialsConormalPresheafComparison (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    restrictedCrysDifferentials S B.obj ⟶ smallSelfProductConormalPresheaf h :=
  (comparisonIso B.obj).inv ≫ smallSelfProductConormalPresheafComparison h

/-- The component of the comparison morphism out of `(Ω_{X/S})_T` over `V` is
`restrictedCrysDifferentialsConormalComparison`. -/
theorem restrictedCrysDifferentialsConormalPresheafComparison_app
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) (V : B.obj.thickening.target.scheme.Opens) :
    (restrictedCrysDifferentialsConormalPresheafComparison h).app (op V) =
      restrictedCrysDifferentialsConormalComparison h V :=
  rfl

end Comparison

/-! ### The sheaf `K/K^{[2]}` and the isomorphism -/

section Sheaf

/-- **The sheaf of `𝒪_T`-modules `K/K^{[2]}`**: the sheaf associated with the conormal presheaf
`V ↦ K/K^{[2]}` over `p₀⁻¹V ⊓ p₁⁻¹V`.  The diagonal is a homeomorphism `T ≅ T(1)` on spaces, so
this is the quotient of the ideal sheaf `K` of `Δ` by its divided square, read on `T`, with
`𝒪_T`-module structure through `Δ`. -/
@[stacks 07J1 "the sheaf of 𝒪_T-modules K/K^{[2]} of the second assertion, the sheaf associated \
with the conormal modules over the opens p₀⁻¹V ⊓ p₁⁻¹V of T(1)"]
def smallSelfProductConormalSheaf (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    SheafOfModules.{u} B.obj.thickening.target.scheme.ringCatSheaf :=
  (PresheafOfModules.sheafification (𝟙 B.obj.thickening.target.scheme.ringCatSheaf.obj)).obj
    (smallSelfProductConormalPresheaf h)

/-- The comparison out of `Ω_{T/S,δ}` is bijective on a neighbourhood of every point inside every
open of `T`. -/
theorem exists_bijective_smallSelfProductConormalPresheafComparison_app
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) (W : B.obj.thickening.target.scheme.Opens)
    (x : B.obj.thickening.target.scheme) (hx : x ∈ W) :
    ∃ V : B.obj.thickening.target.scheme.Opens, x ∈ V ∧ V ≤ W ∧
      Function.Bijective ((smallSelfProductConormalPresheafComparison h).app (op V)).hom := by
  obtain ⟨V, VS, hVaff, hVSaff, hxV, hVW, hVpre⟩ :=
    exists_isAffineOpen_over_isAffineOpen B.obj.toBase.hom W x hx
  exact ⟨V, hxV, hVW, bijective_smallSelfProductConormalComparison hVaff hVpre hVSaff h⟩

/-- The sheafified comparison out of `Ω_{T/S,δ}` is an isomorphism. -/
theorem isIso_sheafification_map_smallSelfProductConormalPresheafComparison
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    IsIso ((PresheafOfModules.sheafification
      (𝟙 B.obj.thickening.target.scheme.ringCatSheaf.obj)).map
        (smallSelfProductConormalPresheafComparison h)) :=
  Scheme.isIso_sheafification_map_of_bijective_nhds _
    (exists_bijective_smallSelfProductConormalPresheafComparison_app h)

/-- The sheafified comparison out of `(Ω_{X/S})_T` is an isomorphism. -/
theorem isIso_sheafification_map_restrictedCrysDifferentialsConormalPresheafComparison
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    IsIso ((PresheafOfModules.sheafification
      (𝟙 B.obj.thickening.target.scheme.ringCatSheaf.obj)).map
        (restrictedCrysDifferentialsConormalPresheafComparison h)) := by
  have := isIso_sheafification_map_smallSelfProductConormalPresheafComparison h
  rw [restrictedCrysDifferentialsConormalPresheafComparison, Functor.map_comp]
  infer_instance

/-- **`Ω_{T/S,δ} ≅ K/K^{[2]}` as sheaves of `𝒪_T`-modules**: the sheafification of the comparison
`d f ↦ [p₁^♯ f - p₀^♯ f]`. -/
def dpDifferentialsSheafIsoConormalSheaf (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    (dpDifferentialsSheaf B.obj.thickening.target S.S.scheme B.obj.toBase.hom :
        SheafOfModules.{u} B.obj.thickening.target.scheme.ringCatSheaf) ≅
      smallSelfProductConormalSheaf h :=
  @asIso _ _ _ _ _ (isIso_sheafification_map_smallSelfProductConormalPresheafComparison h)

/-- **Stacks Project, Tag 07J1, second assertion.**  For a self-product
`(U(1), T(1), δ(1))` of an object `(U, T, δ)` of `Cris(X/S)`, with `K` the ideal of the diagonal
`Δ : T ⟶ T(1)`, the sheaf of `𝒪_T`-modules `(Ω_{X/S})_T` is isomorphic to `K/K^{[2]}`.  The
isomorphism is the sheafification of the comparison morphism, which sends `d f` to the class of
`p₁^♯ f - p₀^♯ f` (`smallSelfProductConormalComparison_d`). -/
@[stacks 07J1 "second assertion: (Ω_{X/S})_T ≅ K/K^{[2]} as sheaves of 𝒪_T-modules, d f ↦ \
[p₁^♯ f - p₀^♯ f]; the first assertion is smallSelfProductDiagonalIdeal_le and \
smallSelfProductDiagonalIdeal_isSubDPIdeal"]
def restrictedCrysDifferentialsSheafIsoConormalSheaf (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    restrictedCrysDifferentialsSheaf S B.obj ≅ smallSelfProductConormalSheaf h :=
  @asIso _ _ _ _ _
    (isIso_sheafification_map_restrictedCrysDifferentialsConormalPresheafComparison h)

/-- The isomorphism `(Ω_{X/S})_T ≅ K/K^{[2]}` is the sheafification of the comparison morphism. -/
theorem restrictedCrysDifferentialsSheafIsoConormalSheaf_hom
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    (restrictedCrysDifferentialsSheafIsoConormalSheaf h).hom =
      (PresheafOfModules.sheafification
        (𝟙 B.obj.thickening.target.scheme.ringCatSheaf.obj)).map
          (restrictedCrysDifferentialsConormalPresheafComparison h) :=
  rfl

end Sheaf

end Crystalline.GlobalCrystallineSituation

end
