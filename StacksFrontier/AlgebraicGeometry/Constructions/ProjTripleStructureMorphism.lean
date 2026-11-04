module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.MorphismToProjUniversal
public import StacksFrontier.AlgebraicGeometry.SectionRingProjMorphism.ToSpecZero

/-!
# The structure morphism recovered from the degree-zero part of a triple

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `X = Proj(A)`, let `d ≥ 1`, let `Y` be a scheme, `L` an
invertible `𝒪_Y`-module and `ψ : A^{(d)} ⟶ Γ_*(Y, L)` a graded ring map. [Stacks, Tag 01N8]
attaches to such a triple a morphism `φ : Y ⟶ U_d ⊆ X`. This file constructs the ring map
`A_0 → Γ(Y, 𝒪_Y)` given by the degree-zero part of `ψ` divided by the unit section of `L^{⊗ 0}`,
and proves that `φ` followed by the structure morphism `X → Spec(A_0)` is the morphism this ring
map determines through the affine adjunction of [Stacks, Tag 01I1]. Over an affine base
`S = Spec(R)` this is the compatibility with `φ` of the structure morphism `Y → S` recovered in
the proof of [Stacks, Tag 01NU].

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTripleStructureMorphism.unitGlobal`: **the unit section of
  `L^{⊗ 0}`**, the global section of the monoidal unit attached to its identity.
* `Stacks.AlgebraicGeometry.ProjTripleStructureMorphism.divUnit`: division by the unit section,
  the identification `Γ(L^{⊗ 0}, W) ≅ Γ(Y, W)`.
* `Stacks.AlgebraicGeometry.ProjTripleStructureMorphism.degreeZeroHom`: **the ring map
  `A_0 ⟶ Γ(Y, 𝒪_Y)` of a triple**, the degree-zero component of `ψ` divided by the unit section.

## Main results

* `Stacks.AlgebraicGeometry.ProjTripleStructureMorphism.toSpecZero_appLE`: the structure morphism
  `Proj(A) ⟶ Spec(A_0)` of Mathlib's `AlgebraicGeometry.Proj.toSpecZero`, read on sections over a
  standard open `D₊(g)` of a homogeneous `g` of positive degree, is the inclusion
  `A_0 → A_{(g)}` of the degree-zero part into the degree-zero localization.
* `Stacks.AlgebraicGeometry.ProjTripleStructureMorphism.toProj_comp_toSpecZero`: **the morphism
  classified by a triple is compatible with the structure morphism to `Spec(A_0)`**: for a pair
  `(φ, α)` compatible with `ψ`, the composite of `φ : Y ⟶ X` with `Proj(A) ⟶ Spec(A_0)` is the
  morphism `Y ⟶ Spec(A_0)` that the ring map `degreeZeroHom` determines.
* `Stacks.AlgebraicGeometry.ProjTripleStructureMorphism.toProj_comp_toSpecZero_over_affine`: the
  same over an affine base: for `S` affine and `c` a ring map `Γ(S, 𝒪_S) → A_0`, the composite of
  `φ` with `X → Spec(A_0) → S` is the morphism `Y → S` that `c` followed by `degreeZeroHom`
  determines through the affine adjunction of [Stacks, Tag 01I1].
* `Stacks.AlgebraicGeometry.ProjTripleStructureMorphism.comp_eq_of_appTop_eq`: the same read
  against a morphism `q : Y ⟶ S` presented by its effect on global sections.

## Implementation notes

`Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections` does not require `ψ(1) = 1`, but
a triple's `ψ` is a homomorphism of graded rings, so the unit axiom is carried as the explicit
hypothesis `hone`: every element of `A_{0 · d}` whose underlying element of `A` is `1` is carried
to the unit section. Without it the degree-zero component is a possibly non-unital ring map.

The degree-zero piece of the Veronese regrading is `A_{0 · d}`, not `A_0`; the two exponents are
equal but not definitionally so, and `zeroVeronese` is the resulting transport. It is defined by
rewriting the membership proof rather than through an `eqToHom`, so that it commutes with the
ring operations by `rfl`.

## References

* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open HomogeneousLocalization
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.MorphismToProjUniversal
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.ProjSectionsUnique (Pair eq_of_smul_restrict_eq)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.SectionProduct (globalSection)
open Stacks.SectionRingProjMorphism.ToSpecZero (resTop_top unitSec nvOpen_unitSec mul_unitSec)
open Stacks.TensorPowerTrivialize (resTop trivEquiv)
open Stacks.TensorPowers (natTensorPow)

universe u w

namespace Stacks.AlgebraicGeometry.ProjTripleStructureMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {d : ℕ} {Y : Scheme.{u}} {L : Y.Modules}
  [Stacks.Ample.IsInvertibleModule Y L]

/-! ### The unit section of the zeroth tensor power -/

/-- **The unit section `1` of `L^{⊗ 0}`.** The zeroth tensor power of `L` is the monoidal unit of
`Y.Modules`, that is, the structure sheaf, and this is the global section attached to its
identity. -/
abbrev unitGlobal (L : Y.Modules) : Γ(natTensorPow L 0, ⊤) :=
  globalSection Y (natTensorPow L 0) (unitSec L)

/-- **The unit section vanishes nowhere**, so every open lies inside its nonvanishing open. -/
theorem le_nonvanishingOpen_unitGlobal (W : Y.Opens) :
    W ≤ nonvanishingOpen Y (natTensorPow L 0) (unitGlobal L) :=
  le_top.trans (nvOpen_unitSec L).ge

/-- **Division by the unit section**, the identification `Γ(L^{⊗ 0}, W) ≅ Γ(Y, W)` of [Stacks,
Tag 01CY] at the nowhere-vanishing section `1`. -/
abbrev divUnit {W : Y.Opens} (x : Γ(natTensorPow L 0, W)) : Γ(Y, W) :=
  (trivEquiv (natTensorPow L 0) (unitGlobal L) (le_nonvanishingOpen_unitGlobal W)).symm x

/-- The ratio by the unit section, multiplied back by the unit section, is the section. -/
theorem divUnit_smul {W : Y.Opens} (x : Γ(natTensorPow L 0, W)) :
    divUnit x • resTop (natTensorPow L 0) (unitGlobal L) W = x :=
  Stacks.TensorPowerTrivialize.trivEquiv_symm_smul _ _ _ x

/-- The ratio by the unit section is the *only* scalar multiplying the unit section to the given
section. -/
theorem divUnit_eq_of_smul {W : Y.Opens} {x : Γ(natTensorPow L 0, W)} {c : Γ(Y, W)}
    (h : x = c • resTop (natTensorPow L 0) (unitGlobal L) W) : divUnit x = c :=
  eq_of_smul_restrict_eq (natTensorPow L 0) (unitGlobal L)
    (le_nonvanishingOpen_unitGlobal W) (divUnit_smul x).symm h

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- Restricting a global section to `⊤` changes nothing. -/
theorem resTop_eq_self {M : Y.Modules} (u : Γ(M, ⊤)) : resTop M u ⊤ = u := resTop_top u

/-- Division by the unit section sends `0` to `0`. -/
@[simp] theorem divUnit_zero {W : Y.Opens} :
    divUnit (0 : Γ(natTensorPow L 0, W)) = 0 := map_zero _

/-- Division by the unit section is additive. -/
@[simp] theorem divUnit_add {W : Y.Opens} (x y : Γ(natTensorPow L 0, W)) :
    divUnit (x + y) = divUnit x + divUnit y := map_add _ _ _

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- **The unit section is idempotent** for the product of global sections of the tensor
powers. -/
theorem mulSections_unitGlobal_self :
    mulSections L (unitGlobal L) (unitGlobal L) = unitGlobal L := by
  rw [show unitGlobal L = globalSection Y (natTensorPow L 0) (unitSec L) from rfl,
    mulSections_globalSection, mul_unitSec]

/-- The defining identity of the ratio by the unit section, over `⊤`. -/
theorem divUnit_resTop_top (x : Γ(natTensorPow L 0, ⊤)) :
    resTop (natTensorPow L 0) x ⊤
      = divUnit x • resTop (natTensorPow L 0) (unitGlobal L) ⊤ := by
  rw [resTop_eq_self, resTop_eq_self]
  exact (divUnit_smul x).symm.trans (congrArg _ (resTop_eq_self (unitGlobal L)))

/-- **Division by the unit section is multiplicative**: the product of global sections of
`L^{⊗ 0}` becomes the product of functions. -/
theorem divUnit_mulSections (s t : Γ(natTensorPow L 0, ⊤)) :
    divUnit (mulSections L s t) = divUnit s * divUnit t := by
  have h1 := resTop_mulSections_smul_right L s (divUnit_resTop_top t)
  have h2 := resTop_mulSections_smul_left L (unitGlobal L) (divUnit_resTop_top s)
  rw [resTop_eq_self, resTop_eq_self] at h1 h2
  refine divUnit_eq_of_smul ?_
  rw [h1, h2, mulSections_unitGlobal_self, resTop_eq_self, smul_smul, mul_comm]

/-- Division of the unit section by itself is `1`. -/
theorem divUnit_unitGlobal : divUnit (unitGlobal L) = 1 := by
  refine divUnit_eq_of_smul ?_
  rw [resTop_eq_self, one_smul]

/-! ### The degree-zero part of a triple -/

/-- **A degree-zero homogeneous element read in degree `0 · d` of the Veronese regrading**, where
the degree-zero component of a triple is defined. The two exponents `0` and `0 · d` are equal but
not definitionally so. -/
def zeroVeronese (d : ℕ) (z : 𝒜 0) : 𝒜 (0 * d) :=
  ⟨(z : A), by rw [Nat.zero_mul]; exact z.2⟩

omit [CommRing A] [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- `zeroVeronese` does not change the underlying element of `A`. -/
@[simp] theorem coe_zeroVeronese (d : ℕ) (z : 𝒜 0) :
    ((zeroVeronese 𝒜 d z : 𝒜 (0 * d)) : A) = (z : A) := rfl

/-- **The ring map `A_0 ⟶ Γ(Y, 𝒪_Y)` of a triple**: the degree-zero component of `ψ`, with values
in the global sections of `L^{⊗ 0}`, divided by the unit section. The hypothesis `hone` is the unit
condition of the graded ring map `ψ`. -/
def degreeZeroHom (ψ : VeroneseSections 𝒜 d L)
    (hone : ∀ a : 𝒜 (0 * d), (a : A) = 1 → ψ.toFun 0 a = unitGlobal L) :
    (𝒜 0) →+* Γ(Y, ⊤) where
  toFun z := divUnit (ψ.toFun 0 (zeroVeronese 𝒜 d z))
  map_zero' := (congrArg divUnit (map_zero (ψ.toFun 0))).trans divUnit_zero
  map_add' z z' := (congrArg divUnit (map_add (ψ.toFun 0) (zeroVeronese 𝒜 d z)
    (zeroVeronese 𝒜 d z'))).trans (divUnit_add _ _)
  map_one' := (congrArg divUnit (hone _ rfl)).trans divUnit_unitGlobal
  map_mul' z z' := by
    change divUnit (ψ.toFun 0 (zeroVeronese 𝒜 d (z * z'))) = _
    rw [ψ.map_mul 0 0 (zeroVeronese 𝒜 d z) (zeroVeronese 𝒜 d z') (zeroVeronese 𝒜 d (z * z')) rfl,
      divUnit_mulSections]

/-- `degreeZeroHom` sends `z` to the degree-zero component of `ψ` at `z` divided by the unit
section. -/
theorem degreeZeroHom_apply (ψ : VeroneseSections 𝒜 d L)
    (hone : ∀ a : 𝒜 (0 * d), (a : A) = 1 → ψ.toFun 0 a = unitGlobal L) (z : 𝒜 0) :
    degreeZeroHom 𝒜 ψ hone z = divUnit (ψ.toFun 0 (zeroVeronese 𝒜 d z)) := rfl

/-- **The degree-zero part of `ψ`, as the defining identity.** The degree-zero component of `ψ`
is the ring map times the unit section. -/
theorem toFun_zero_eq_smul (ψ : VeroneseSections 𝒜 d L)
    (hone : ∀ a : 𝒜 (0 * d), (a : A) = 1 → ψ.toFun 0 a = unitGlobal L) (z : 𝒜 0) :
    ψ.toFun 0 (zeroVeronese 𝒜 d z)
      = degreeZeroHom 𝒜 ψ hone z • resTop (natTensorPow L 0) (unitGlobal L) ⊤ :=
  (divUnit_smul (ψ.toFun 0 (zeroVeronese 𝒜 d z))).symm

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- **`ψ` carries the zeroth power of an element of `A_d` to the unit section.** -/
theorem pow_zero_eq_unitGlobal (ψ : VeroneseSections 𝒜 d L)
    (hone : ∀ a : 𝒜 (0 * d), (a : A) = 1 → ψ.toFun 0 a = unitGlobal L) {g : A}
    (hg : g ∈ 𝒜 d) : ψ.pow hg 0 = unitGlobal L :=
  hone _ (pow_zero g)

/-! ### The structure morphism of `Proj A` on a standard open -/

section ToSpecZero

variable {m : ℕ} {g : A}

/-- **The structure morphism of `Proj A` on the standard open of a homogeneous `g` of positive
degree** is `Spec` of the inclusion of the degree-zero part of `A` into the degree-zero
localization `A_{(g)}`, composed with the identification of `D₊(g)` with `Spec A_{(g)}`. -/
theorem ι_basicOpen_comp_toSpecZero (hg : g ∈ 𝒜 m) (hm : 0 < m) :
    (Proj.basicOpen 𝒜 g).ι ≫ Proj.toSpecZero 𝒜 =
      Proj.basicOpenToSpec 𝒜 g ≫
        Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers g))) := by
  have h := Proj.awayι_toSpecZero 𝒜 g hg hm
  rw [← Proj.basicOpenIsoSpec_inv_ι 𝒜 g hg hm, Category.assoc] at h
  have hι := (Iso.inv_comp_eq _).mp h
  rwa [Proj.basicOpenIsoSpec_hom 𝒜 g hg hm] at hι

/-- **A degree-zero element, read in `A_{(g)}`, is the fraction `z / g^0`.** -/
theorem fromZeroRingHom_eq_awayMk (hg : g ∈ 𝒜 m) (z : 𝒜 0) (hz : (z : A) ∈ 𝒜 (0 • m)) :
    fromZeroRingHom 𝒜 (Submonoid.powers g) z = Away.mk 𝒜 hg 0 (z : A) hz := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk]
  exact congrArg (Localization.mk (z : A)) (Subtype.ext (pow_zero g).symm)

end ToSpecZero

/-! ### Sections over an open and over its restriction -/

/-- An open of the source of a morphism lies inside the preimage of the whole target. -/
theorem le_preimage_top {X Z : Scheme.{u}} (k : X ⟶ Z) (U : X.Opens) : U ≤ k ⁻¹ᵁ ⊤ :=
  le_top.trans (Scheme.Hom.preimage_top k).ge

/-- **Reading a morphism on sections over an open, and reading it over the restriction of the
source to that open, agree.** The two differ by the identification `Γ(X, U) ≅ Γ(U, ⊤)` of the
sections of `X` over `U` with the global sections of the open subscheme. -/
theorem appLE_comp_topIso_inv {X Z : Scheme.{u}} (k : X ⟶ Z) (U : X.Opens) :
    k.appLE ⊤ U (le_preimage_top k U) ≫ U.topIso.inv = k.appTop ≫ U.ι.appTop :=
  Scheme.Hom.appLE_map (f := k) (le_preimage_top k U) ((eqToHom (Scheme.Opens.ι_image_top U)).op)

section ToSpecZeroSections

variable {m : ℕ} {g : A}

/-- **The structure morphism `Proj A ⟶ Spec A_0` on sections over the standard open `D₊(g)`** is
the inclusion of the degree-zero part of `A` into the degree-zero localization `A_{(g)}`,
followed by the identification of `A_{(g)}` with `Γ(Proj A, D₊(g))`. -/
theorem toSpecZero_appLE (hg : g ∈ 𝒜 m) (hm : 0 < m) :
    (Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv ≫
        (Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 g)
          (le_preimage_top (Proj.toSpecZero 𝒜) (Proj.basicOpen 𝒜 g))
      = CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers g)) ≫
          Proj.awayToSection 𝒜 g := by
  have hcomp := congrArg
    (fun k : (Proj.basicOpen 𝒜 g).toScheme ⟶ Spec (CommRingCat.of (𝒜 0)) => k.appTop)
    (ι_basicOpen_comp_toSpecZero 𝒜 hg hm)
  simp only [Scheme.Hom.comp_appTop, Proj.basicOpenToSpec_app_top] at hcomp
  rw [← cancel_mono ((Proj.basicOpen 𝒜 g).topIso.inv), Category.assoc,
    appLE_comp_topIso_inv, hcomp, ← Scheme.ΓSpecIso_inv_naturality_assoc]
  simp only [Iso.inv_hom_id_assoc, Category.assoc]

/-- The structure morphism `Proj A ⟶ Spec A_0` pulls a degree-zero element of `A` back to the
fraction `z / g^0` on the standard open `D₊(g)`. -/
theorem toSpecZero_appLE_apply (hg : g ∈ 𝒜 m) (hm : 0 < m) (z : 𝒜 0) :
    (Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 g)
        (le_preimage_top (Proj.toSpecZero 𝒜) (Proj.basicOpen 𝒜 g))
        ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv z)
      = Proj.awayToSection 𝒜 g (fromZeroRingHom 𝒜 (Submonoid.powers g) z) := by
  simpa using DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (toSpecZero_appLE 𝒜 hg hm)) z

end ToSpecZeroSections

/-! ### The compatibility -/

section Compatibility

variable (ψ : VeroneseSections 𝒜 d L)
  (hone : ∀ a : 𝒜 (0 * d), (a : A) = 1 → ψ.toFun 0 a = unitGlobal L)

/-- **The degree-zero clause of the compatibility of [Stacks, Tag 01N8].** On the nonvanishing
open `Y_{ψ(f)}`, which is the preimage of `D₊(f)`, the morphism `φ` carries the degree-zero
fraction `z / 1` to the restriction of `degreeZeroHom z`. -/
theorem appLE_awayToSection_zero {p : Pair 𝒜 L d} (hp : IsCompatible 𝒜 ψ p) (f : 𝒜 d)
    (z : 𝒜 0) (hz : (z : A) ∈ 𝒜 (0 • d)) :
    (toProj 𝒜 p.1).appLE (Proj.basicOpen 𝒜 (f : A))
        (nonvanishingOpen Y L (psiSection 𝒜 ψ f)) (preimage_basicOpen_eq 𝒜 hp f).ge
        (Proj.awayToSection 𝒜 (f : A) (Away.mk 𝒜 f.2 0 (z : A) hz))
      = Y.presheaf.map
          (homOfLE (le_top : nonvanishingOpen Y L (psiSection 𝒜 ψ f) ≤ ⊤)).op
          (degreeZeroHom 𝒜 ψ hone z) := by
  have hcl := hp.2 f (nonvanishingOpen Y L (psiSection 𝒜 ψ f))
    (preimage_basicOpen_eq 𝒜 hp f).ge 0 (z : A) hz (zeroVeronese 𝒜 d z) rfl
  rw [pow_zero_eq_unitGlobal 𝒜 ψ hone f.2] at hcl
  have hres : resTop (natTensorPow L 0) (ψ.toFun 0 (zeroVeronese 𝒜 d z))
        (nonvanishingOpen Y L (psiSection 𝒜 ψ f))
      = Y.presheaf.map
            (homOfLE (le_top : nonvanishingOpen Y L (psiSection 𝒜 ψ f) ≤ ⊤)).op
            (degreeZeroHom 𝒜 ψ hone z)
          • resTop (natTensorPow L 0) (unitGlobal L)
              (nonvanishingOpen Y L (psiSection 𝒜 ψ f)) := by
    rw [toFun_zero_eq_smul 𝒜 ψ hone z]
    exact Stacks.TensorPowerTrivialize.map_smul_resTop (natTensorPow L 0) (unitGlobal L)
      (homOfLE (le_top : nonvanishingOpen Y L (psiSection 𝒜 ψ f) ≤ ⊤)) _
  exact eq_of_smul_restrict_eq (natTensorPow L 0) (unitGlobal L)
    (le_nonvanishingOpen_unitGlobal _) hcl hres

/-- **The morphism classified by a triple is compatible with the structure morphism of
`Proj A`.** For a pair `(φ, α)` compatible with `ψ` in the sense of [Stacks, Tag 01N8], the
composite of `φ : Y ⟶ Proj A` with the structure morphism `Proj A ⟶ Spec A_0` is the morphism
`Y ⟶ Spec A_0` that the degree-zero ring map `A_0 ⟶ Γ(Y, 𝒪_Y)` of the triple determines through
the affine adjunction of [Stacks, Tag 01I1]. -/
theorem toProj_comp_toSpecZero (hd : 0 < d)
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤)
    {p : Pair 𝒜 L d} (hp : IsCompatible 𝒜 ψ p) :
    toProj 𝒜 p.1 ≫ Proj.toSpecZero 𝒜
      = Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (degreeZeroHom 𝒜 ψ hone)) := by
  have hrhs : (Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv ≫
      (Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (degreeZeroHom 𝒜 ψ hone))).appTop
      = CommRingCat.ofHom (degreeZeroHom 𝒜 ψ hone) := by
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
      Category.assoc, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]
  refine AlgebraicGeometry.ext_to_Spec ?_
  show (Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv ≫
      (toProj 𝒜 p.1 ≫ Proj.toSpecZero 𝒜).appTop
    = (Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv ≫
      (Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (degreeZeroHom 𝒜 ψ hone))).appTop
  rw [hrhs]
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  refine TopCat.Sheaf.eq_of_locally_eq' Y.sheaf
    (fun f : 𝒜 d => nonvanishingOpen Y L (psiSection 𝒜 ψ f)) ⊤
    (fun _ => homOfLE le_top) hgen.ge _ _ (fun f => ?_)
  have hz : (z : A) ∈ 𝒜 (0 • d) := by simp
  have hstep : (Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 (f : A))
          (le_preimage_top (Proj.toSpecZero 𝒜) (Proj.basicOpen 𝒜 (f : A))) ≫
        (toProj 𝒜 p.1).appLE (Proj.basicOpen 𝒜 (f : A))
          (nonvanishingOpen Y L (psiSection 𝒜 ψ f)) (preimage_basicOpen_eq 𝒜 hp f).ge
      = (toProj 𝒜 p.1 ≫ Proj.toSpecZero 𝒜).appLE ⊤
          (nonvanishingOpen Y L (psiSection 𝒜 ψ f))
          (le_preimage_top (toProj 𝒜 p.1 ≫ Proj.toSpecZero 𝒜)
            (nonvanishingOpen Y L (psiSection 𝒜 ψ f))) :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  show (toProj 𝒜 p.1 ≫ Proj.toSpecZero 𝒜).appLE ⊤
        (nonvanishingOpen Y L (psiSection 𝒜 ψ f))
        (le_preimage_top (toProj 𝒜 p.1 ≫ Proj.toSpecZero 𝒜)
          (nonvanishingOpen Y L (psiSection 𝒜 ψ f)))
        ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv z)
      = Y.presheaf.map
          (homOfLE (le_top : nonvanishingOpen Y L (psiSection 𝒜 ψ f) ≤ ⊤)).op
          (degreeZeroHom 𝒜 ψ hone z)
  rw [← hstep]
  show (toProj 𝒜 p.1).appLE (Proj.basicOpen 𝒜 (f : A))
        (nonvanishingOpen Y L (psiSection 𝒜 ψ f)) (preimage_basicOpen_eq 𝒜 hp f).ge
        ((Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 (f : A))
          (le_preimage_top (Proj.toSpecZero 𝒜) (Proj.basicOpen 𝒜 (f : A)))
          ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv z)) = _
  rw [toSpecZero_appLE_apply 𝒜 f.2 hd z, fromZeroRingHom_eq_awayMk 𝒜 f.2 z hz]
  exact appLE_awayToSection_zero 𝒜 ψ hone hp f z hz

/-- **The structure morphism recovered from the degree-zero part of a triple, over an affine
base.** Let `S` be an affine scheme and `c : Γ(S, 𝒪_S) ⟶ A_0` a ring map. Then the morphism `φ`
classified by the triple, followed by `Proj A ⟶ Spec A_0 ⟶ S`, is the morphism `Y ⟶ S` that the
composite ring map `Γ(S, 𝒪_S) → A_0 → Γ(Y, 𝒪_Y)` determines through the affine adjunction of
[Stacks, Tag 01I1], namely `Y ⟶ Spec Γ(Y, 𝒪_Y) ⟶ Spec Γ(S, 𝒪_S) ≅ S`. -/
theorem toProj_comp_toSpecZero_over_affine (hd : 0 < d)
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤)
    {p : Pair 𝒜 L d} (hp : IsCompatible 𝒜 ψ p) {S : Scheme.{u}} [IsAffine S]
    (c : Γ(S, ⊤) ⟶ CommRingCat.of (𝒜 0)) :
    toProj 𝒜 p.1 ≫ Proj.toSpecZero 𝒜 ≫ Spec.map c ≫ S.isoSpec.inv
      = Y.toSpecΓ ≫ Spec.map (c ≫ CommRingCat.ofHom (degreeZeroHom 𝒜 ψ hone))
          ≫ S.isoSpec.inv := by
  rw [← Category.assoc (toProj 𝒜 p.1), toProj_comp_toSpecZero 𝒜 ψ hone hd hgen hp,
    Category.assoc, ← Category.assoc (Spec.map (CommRingCat.ofHom (degreeZeroHom 𝒜 ψ hone))),
    ← Spec.map_comp]

/-- If a morphism `q : Y ⟶ S` into an affine scheme induces `c` followed by `degreeZeroHom` on
global sections, then the morphism classified by the triple, followed by `Proj A ⟶ Spec A_0 ⟶ S`,
is `q`. -/
theorem comp_eq_of_appTop_eq (hd : 0 < d)
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤)
    {p : Pair 𝒜 L d} (hp : IsCompatible 𝒜 ψ p) {S : Scheme.{u}} [IsAffine S]
    (c : Γ(S, ⊤) ⟶ CommRingCat.of (𝒜 0)) (q : Y ⟶ S)
    (hq : q.appTop = c ≫ CommRingCat.ofHom (degreeZeroHom 𝒜 ψ hone)) :
    toProj 𝒜 p.1 ≫ Proj.toSpecZero 𝒜 ≫ Spec.map c ≫ S.isoSpec.inv = q := by
  rw [toProj_comp_toSpecZero_over_affine 𝒜 ψ hone hd hgen hp, ← hq,
    ← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]

end Compatibility

end Stacks.AlgebraicGeometry.ProjTripleStructureMorphism

end
