module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.AmbientKernelLift
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupDualCan

/-!
# The section of `(p^*M)^∨(q)` attached to a homomorphism `M → I^q/I^{q+n}`

Let `p : X → Spec(A)` be the blowup of `Spec(A)` in `I`, `Yₙ` the `n`-th thickening of the
exceptional divisor, `n = m + 1`, and `M` an `A/Iⁿ`-module with dual
`(p^*M)^∨ = SheafHom(p^*M, 𝒪_{Yₙ})` (`blowupDual`). The duality step of [Stacks, Tag 0GAC]
starts from an `A`-linear map `φ : M → I^q/I^{q+n}` and reads it as a section
`σ ∈ Γ(X, (p^*M)^∨(q))`: "since `𝒪_{Yₙ}(q)` is invertible on `Yₙ` the linear map `χ` determines a
section". This file constructs that section, `A`-linearly in `φ`, and proves that its
evaluation against the elements of `M` (`blowupEvDual`) is `φ` for `q ≥ q₀`.

## The construction

The invertibility of `𝒪_X(q)` enters through the multiplication of twists
`𝒪_X(a) ⊗ 𝒪_X(b) ⟶ 𝒪_X(a + b)`, an isomorphism on the blowup
(`Stacks.Blowup.isIso_twistMultiplicationMap_reesGrading`), at `a + b = 0`
(`blowupTwistMul`). With `ε : 𝒪_X ≅ 𝒪_X(-q) ⊗ 𝒪_X(q)` and `η : 𝒪_X(q) ⊗ 𝒪_X(-q) ≅ 𝒪_X`:

* each `φ(z) ∈ I^q/I^{q+n}` is a class in `H⁰(X, 𝒪_{Yₙ}(q))` (Tag 0GA7(2), `cdivMod`), i.e. a
  map `𝒪_X ⟶ 𝒪_{Yₙ}(q)` (`thickeningPointHom`, through `blowupUnitHomH0Equiv`);
* contracting with `η` turns it into a map `𝒪_X(-q) ⟶ 𝒪_{Yₙ}` (`thickeningContract`), and the
  resulting `A`-linear family `z ↦ (𝒪_X(-q) ⟶ 𝒪_{Yₙ})` is one map
  `𝒪_X(-q) ⟶ (p^*M)^∨` with these evaluations (`blowupDualLift`);
* tensoring with `𝒪_X(q)` and precomposing with `ε` gives `𝒪_X ⟶ (p^*M)^∨(q)`, a section.

Contracting with `η` and expanding with `ε` is the identity only up to an automorphism of
`𝒪_{Yₙ}(q)`, since the two isomorphisms need not satisfy the zigzag identities; this
automorphism (`tensorRoundTrip`) is computed once in an arbitrary monoidal category
(`comp_tensorRoundTrip`) and inverted beforehand, so no compatibility between `ε` and `η` is
needed.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.tensorContract`, `tensorRoundTrip`: contraction along a
  pairing, and the round trip automorphism, in an arbitrary monoidal category.
* `Stacks.LocalCohomology.UniformityIII.blowupTwistMul`: `𝒪_X(a) ⊗ 𝒪_X(b) ≅ 𝒪_X` for
  `a + b = 0`.
* `Stacks.LocalCohomology.UniformityIII.blowupUnitHomH0Equiv`: `H⁰(X, F)` is the group of maps
  `𝒪_X ⟶ F`.
* `Stacks.LocalCohomology.UniformityIII.blowupSecDual`: **the section `σ` of `(p^*M)^∨(q)`
  attached to `φ`**, as an `A`-linear map; the field `secDual` of `CanDualSituation`.

## Main results

* `Stacks.LocalCohomology.UniformityIII.comp_tensorRoundTrip`: expanding the contraction of
  `t : 𝟙 ⟶ Y ⊗ L` returns `t` followed by the round trip automorphism.
* `Stacks.LocalCohomology.UniformityIII.blowupEvDual_blowupSecDual`: **evaluating `σ` against
  the elements of `M` returns `φ`**, for `q ≥ q₀`; the field `evDual_secDual` of
  `CanDualSituation`.

## References

* [Stacks Project, Tag 0GAC](https://stacks.math.columbia.edu/tag/0GAC)
* [Stacks Project, Tag 0GA7](https://stacks.math.columbia.edu/tag/0GA7)
* [Stacks Project, Tag 01CR](https://stacks.math.columbia.edu/tag/01CR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry
open Stacks.RegularSequence (globalSmulCenter)
open Stacks.AlgebraicGeometry.ProjInvertibleLocus (twistMultiplicationMap)

universe u

namespace Stacks.LocalCohomology.UniformityIII


section Monoidal

variable {C : Type*} [Category C] [MonoidalCategory C] {L L' : C}

/-- The contraction `(Y ⊗ L) ⊗ L' ≅ Y ⊗ (L ⊗ L') ⟶ Y ⊗ 𝟙 ≅ Y` along a pairing
`η : L ⊗ L' ⟶ 𝟙`. -/
def tensorContract (η : L ⊗ L' ⟶ 𝟙_ C) (Y : C) : (Y ⊗ L) ⊗ L' ⟶ Y :=
  (α_ Y L L').hom ≫ (Y ◁ η) ≫ (ρ_ Y).hom

/-- The contraction is natural in `Y`. -/
theorem tensorContract_naturality (η : L ⊗ L' ⟶ 𝟙_ C) {Y Y' : C} (f : Y ⟶ Y') :
    ((f ▷ L) ▷ L') ≫ tensorContract η Y' = tensorContract η Y ≫ f := by
  unfold tensorContract
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, rightUnitor_naturality]
  simp only [Category.assoc]

/-- The endomorphism `Y ⊗ L ≅ (Y ⊗ L) ⊗ 𝟙 ⟶ (Y ⊗ L) ⊗ (L' ⊗ L) ≅ ((Y ⊗ L) ⊗ L') ⊗ L ⟶ Y ⊗ L`
attached to `ε : 𝟙 ⟶ L' ⊗ L` and `η : L ⊗ L' ⟶ 𝟙`; an isomorphism when both are. -/
def tensorRoundTrip (ε : 𝟙_ C ⟶ L' ⊗ L) (η : L ⊗ L' ⟶ 𝟙_ C) (Y : C) : Y ⊗ L ⟶ Y ⊗ L :=
  (ρ_ (Y ⊗ L)).inv ≫ ((Y ⊗ L) ◁ ε) ≫ (α_ (Y ⊗ L) L' L).inv ≫ (tensorContract η Y ▷ L)

/-- `tensorRoundTrip ε η Y` is an isomorphism when `ε` and `η` are isomorphisms. -/
instance isIso_tensorRoundTrip (ε : 𝟙_ C ⟶ L' ⊗ L) (η : L ⊗ L' ⟶ 𝟙_ C) [IsIso ε] [IsIso η]
    (Y : C) : IsIso (tensorRoundTrip ε η Y) := by
  unfold tensorRoundTrip tensorContract
  infer_instance

/-- **A morphism `𝟙 ⟶ Y ⊗ L` is recovered from its contraction `L' ⟶ Y`**, up to the
isomorphism `tensorRoundTrip`. -/
theorem comp_tensorRoundTrip (ε : 𝟙_ C ⟶ L' ⊗ L) (η : L ⊗ L' ⟶ 𝟙_ C) (Y : C)
    (t : 𝟙_ C ⟶ Y ⊗ L) :
    t ≫ tensorRoundTrip ε η Y =
      ε ≫ (((λ_ L').inv ≫ (t ▷ L') ≫ tensorContract η Y) ▷ L) := by
  unfold tensorRoundTrip
  symm
  calc ε ≫ (((λ_ L').inv ≫ (t ▷ L') ≫ tensorContract η Y) ▷ L)
      = ε ≫ ((λ_ L').inv ▷ L) ≫ ((t ▷ L') ▷ L) ≫ (tensorContract η Y ▷ L) := by
        simp only [comp_whiskerRight]
    _ = ε ≫ (λ_ (L' ⊗ L)).inv ≫ (α_ (𝟙_ C) L' L).inv ≫ ((t ▷ L') ▷ L) ≫
          (tensorContract η Y ▷ L) := by
        rw [leftUnitor_inv_whiskerRight, Category.assoc]
    _ = (λ_ (𝟙_ C)).inv ≫ (𝟙_ C ◁ ε) ≫ (α_ (𝟙_ C) L' L).inv ≫ ((t ▷ L') ▷ L) ≫
          (tensorContract η Y ▷ L) := by
        rw [leftUnitor_inv_naturality_assoc]
    _ = (λ_ (𝟙_ C)).inv ≫ (𝟙_ C ◁ ε) ≫ (t ▷ (L' ⊗ L)) ≫ (α_ (Y ⊗ L) L' L).inv ≫
          (tensorContract η Y ▷ L) := by
        rw [← associator_inv_naturality_left_assoc]
    _ = (λ_ (𝟙_ C)).inv ≫ (t ▷ 𝟙_ C) ≫ ((Y ⊗ L) ◁ ε) ≫ (α_ (Y ⊗ L) L' L).inv ≫
          (tensorContract η Y ▷ L) := by
        rw [whisker_exchange_assoc]
    _ = t ≫ (ρ_ (Y ⊗ L)).inv ≫ ((Y ⊗ L) ◁ ε) ≫ (α_ (Y ⊗ L) L' L).inv ≫
          (tensorContract η Y ▷ L) := by
        rw [unitors_inv_equal, ← rightUnitor_inv_naturality_assoc]

end Monoidal

attribute [local instance] modulesMonoidal modulesMonoidal'

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### `𝒪_X(t)` is invertible -/

/-- The multiplication `𝒪_X(a) ⊗ 𝒪_X(b) ⟶ 𝒪_X(a + b) = 𝒪_X(0) ≅ 𝒪_X` for `a + b = 0`. -/
def blowupTwistMul {a b : ℤ} (h : a + b = 0) :
    blowupTwistInt I a ⊗ blowupTwistInt I b ⟶ blowupUnit I :=
  twistMultiplicationMap (Stacks.Blowup.reesGrading I) a b ≫
    eqToHom (congrArg (blowupTwistInt I) h) ≫
    (Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit
      (Stacks.Blowup.reesGrading I)).hom

/-- `𝒪_X(a) ⊗ 𝒪_X(-a) ≅ 𝒪_X`: the multiplication of twists on the blowup is an isomorphism. -/
instance isIso_blowupTwistMul {a b : ℤ} (h : a + b = 0) : IsIso (blowupTwistMul I h) :=
  IsIso.comp_isIso' (Stacks.Blowup.isIso_twistMultiplicationMap_reesGrading I a b)
    (IsIso.comp_isIso' (Iso.isIso_hom (eqToIso (congrArg (blowupTwistInt I) h)))
      (Iso.isIso_hom _))

/-! ### Cohomology classes in degree zero as maps out of the structure sheaf -/

/-- `blowupUnitHomSection` is injective: a map `𝒪_X ⟶ F` is determined by the image of `1`. -/
theorem blowupUnitHomSection_injective (F : (blowupScheme I).Modules) :
    Function.Injective (blowupUnitHomSection I (H := F)) := by
  intro g g' h
  have h' : (blowupPullbackAdjunction I).homEquiv (ModuleCat.of A A) F
      ((blowupPullbackSelfIso I).hom ≫ g) =
      (blowupPullbackAdjunction I).homEquiv (ModuleCat.of A A) F
        ((blowupPullbackSelfIso I).hom ≫ g') := by
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    rw [blowupPullbackAdjunction_homEquiv_selfIso_apply_one,
      blowupPullbackAdjunction_homEquiv_selfIso_apply_one]
    exact h
  exact (cancel_epi _).1 (((blowupPullbackAdjunction I).homEquiv _ _).injective h')

/-- `blowupUnitHomSection` is surjective: every global section is the image of `1` under a map
`𝒪_X ⟶ F`. -/
theorem blowupUnitHomSection_surjective (F : (blowupScheme I).Modules) :
    Function.Surjective (blowupUnitHomSection I (H := F)) := by
  intro σ
  refine ⟨(blowupPullbackSelfIso I).inv ≫
    ((blowupPullbackAdjunction I).homEquiv (ModuleCat.of A A) F).symm
      (ModuleCat.ofHom (X := A) (Y := (blowupΓmod I).obj F)
        (LinearMap.toSpanSingleton A _ σ)), ?_⟩
  rw [← blowupPullbackAdjunction_homEquiv_selfIso_apply_one, Iso.hom_inv_id_assoc]
  exact (congrArg (fun φ : ModuleCat.of A A ⟶ (blowupΓmod I).obj F => ModuleCat.Hom.hom φ (1 : A))
    (Equiv.apply_symm_apply ((blowupPullbackAdjunction I).homEquiv (ModuleCat.of A A) F)
      (ModuleCat.ofHom (X := A) (Y := (blowupΓmod I).obj F)
        (LinearMap.toSpanSingleton A _ σ)))).trans (one_smul A σ)

/-- The class in `H⁰(X, F)` of the global section attached to a map `𝒪_X ⟶ F`. -/
def blowupUnitHomH0 {F : (blowupScheme I).Modules} (g : blowupUnit I ⟶ F) : blowupHmod I 0 F :=
  blowupΓmodToH0 I F (blowupUnitHomSection I g)

/-- A map `𝒪_X ⟶ F` is determined by its class in `H⁰(X, F)`. -/
theorem blowupUnitHomH0_injective (F : (blowupScheme I).Modules) :
    Function.Injective (blowupUnitHomH0 I (F := F)) :=
  (injective_blowupΓmodToH0 I F).comp (blowupUnitHomSection_injective I F)

/-- Every class in `H⁰(X, F)` comes from a map `𝒪_X ⟶ F`. -/
theorem blowupUnitHomH0_surjective (F : (blowupScheme I).Modules) :
    Function.Surjective (blowupUnitHomH0 I (F := F)) :=
  (surjective_blowupΓmodToH0 I F).comp (blowupUnitHomSection_surjective I F)

/-- The class of a sum of maps is the sum of the classes. -/
theorem blowupUnitHomH0_add {F : (blowupScheme I).Modules} (g g' : blowupUnit I ⟶ F) :
    blowupUnitHomH0 I (g + g') = blowupUnitHomH0 I g + blowupUnitHomH0 I g' :=
  (congrArg (blowupΓmodToH0 I F) (blowupUnitHomSection_add I g g')).trans (map_add _ _ _)

/-- The class of the zero map is zero. -/
theorem blowupUnitHomH0_zero (F : (blowupScheme I).Modules) :
    blowupUnitHomH0 I (0 : blowupUnit I ⟶ F) = 0 := by
  have h := blowupUnitHomH0_add I (0 : blowupUnit I ⟶ F) 0
  rw [add_zero] at h
  exact left_eq_add.1 h

/-- The class of a map precomposed with multiplication by the pulled back function `a` is `a`
times the class. -/
theorem blowupUnitHomH0_globalSmulCenter {F : (blowupScheme I).Modules}
    (g : blowupUnit I ⟶ F) (a : A) :
    blowupUnitHomH0 I ((globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app _ ≫ g) =
      a • blowupUnitHomH0 I g :=
  (congrArg (blowupΓmodToH0 I F) (blowupUnitHomSection_globalSmulCenter I g a)).trans
    (map_smul _ _ _)

/-- `H⁰` of a map `F ⟶ G` on the class of `g : 𝒪_X ⟶ F` is the class of the composite. -/
theorem blowupHmodMap_blowupUnitHomH0 {F G : (blowupScheme I).Modules} (g : blowupUnit I ⟶ F)
    (f : F ⟶ G) :
    blowupHmodMap I 0 f (blowupUnitHomH0 I g) = blowupUnitHomH0 I (g ≫ f) :=
  (blowupΓmodToH0_naturality I f (blowupUnitHomSection I g)).symm

/-- The map `(blowupUnit ⟶ F) → H⁰(X, F)` as an additive equivalence. -/
def blowupUnitHomH0Equiv (F : (blowupScheme I).Modules) : (blowupUnit I ⟶ F) ≃+ blowupHmod I 0 F :=
  AddEquiv.ofBijective (AddMonoidHom.mk' (blowupUnitHomH0 I) (blowupUnitHomH0_add I))
    ⟨blowupUnitHomH0_injective I F, blowupUnitHomH0_surjective I F⟩

/-- The forward map of `blowupUnitHomH0Equiv`. -/
theorem blowupUnitHomH0Equiv_apply {F : (blowupScheme I).Modules} (g : blowupUnit I ⟶ F) :
    blowupUnitHomH0Equiv I F g = blowupUnitHomH0 I g := rfl

/-- The map `𝒪_X ⟶ F` attached to `a • x` is the one attached to `x`, precomposed with
multiplication by the pulled back function `a`. -/
theorem blowupUnitHomH0Equiv_symm_smul {F : (blowupScheme I).Modules} (a : A)
    (x : blowupHmod I 0 F) :
    (blowupUnitHomH0Equiv I F).symm (a • x) =
      (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app _ ≫
        (blowupUnitHomH0Equiv I F).symm x := by
  apply (blowupUnitHomH0Equiv I F).injective
  rw [AddEquiv.apply_symm_apply, blowupUnitHomH0Equiv_apply, blowupUnitHomH0_globalSmulCenter,
    ← blowupUnitHomH0Equiv_apply, AddEquiv.apply_symm_apply]

/-! ### The section attached to a homomorphism -/


variable (m q : ℕ)

/-- `ε : 𝒪_X ≅ 𝒪_X(-q) ⊗ 𝒪_X(q)`. -/
abbrev blowupTwistCoev : blowupUnit I ⟶ blowupTwistInt I (-(q : ℤ)) ⊗ blowupTwistInt I q :=
  inv (blowupTwistMul I (neg_add_cancel (q : ℤ)))

/-- `η : 𝒪_X(q) ⊗ 𝒪_X(-q) ≅ 𝒪_X`. -/
abbrev blowupTwistEv : blowupTwistInt I q ⊗ blowupTwistInt I (-(q : ℤ)) ⟶ blowupUnit I :=
  blowupTwistMul I (add_neg_cancel (q : ℤ))

/-- The map `𝒪_X ⟶ 𝒪_{Yₙ}(q)` attached to an element of `I^q/I^{q+n}`, `n = m + 1`: the class
`cdiv(y) ∈ H⁰(X, 𝒪_{Yₙ}(q))` read as a map out of `𝒪_X`. -/
def thickeningPointHom (y : powQuot I q (m + 1)) :
    blowupUnit I ⟶ thickeningSheaf I (m + 1) ⊗ blowupTwistInt I q :=
  (blowupUnitHomH0Equiv I (thickeningTwist I (m + 1) q)).symm (cdivMod I m q y)

/-- The class of the map attached to `y` is `cdiv(y)`. -/
theorem blowupUnitHomH0_thickeningPointHom (y : powQuot I q (m + 1)) :
    blowupUnitHomH0 I (thickeningPointHom I m q y) = cdivMod I m q y :=
  (blowupUnitHomH0Equiv I (thickeningTwist I (m + 1) q)).apply_symm_apply _

/-- `thickeningPointHom` is additive. -/
theorem thickeningPointHom_add (y y' : powQuot I q (m + 1)) :
    thickeningPointHom I m q (y + y') =
      thickeningPointHom I m q y + thickeningPointHom I m q y' := by
  unfold thickeningPointHom
  rw [map_add, map_add]

/-- `thickeningPointHom` carries `a • y` to the map attached to `y` precomposed with
multiplication by the pulled back function `a`. -/
theorem thickeningPointHom_smul (a : A) (y : powQuot I q (m + 1)) :
    thickeningPointHom I m q (a • y) =
      (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app _ ≫
        thickeningPointHom I m q y := by
  unfold thickeningPointHom
  rw [map_smul]
  exact blowupUnitHomH0Equiv_symm_smul I a _

/-- The contraction `𝒪_X(-q) ⟶ 𝒪_{Yₙ}` of a map `t : 𝒪_X ⟶ 𝒪_{Yₙ}(q)`:
`𝒪_X(-q) ≅ 𝒪_X ⊗ 𝒪_X(-q) ⟶ 𝒪_{Yₙ}(q) ⊗ 𝒪_X(-q) ⟶ 𝒪_{Yₙ}`. -/
def thickeningContract (t : blowupUnit I ⟶ thickeningSheaf I (m + 1) ⊗ blowupTwistInt I q) :
    blowupTwistInt I (-(q : ℤ)) ⟶ thickeningSheaf I (m + 1) :=
  (λ_ (blowupTwistInt I (-(q : ℤ)))).inv ≫ (t ▷ blowupTwistInt I (-(q : ℤ))) ≫
    tensorContract (blowupTwistEv I q) (thickeningSheaf I (m + 1))

/-- The contraction is additive. -/
theorem thickeningContract_add
    (t t' : blowupUnit I ⟶ thickeningSheaf I (m + 1) ⊗ blowupTwistInt I q) :
    thickeningContract I m q (t + t') =
      thickeningContract I m q t + thickeningContract I m q t' := by
  unfold thickeningContract
  rw [add_whiskerRight_blowupTwistInt, Preadditive.add_comp, Preadditive.comp_add]

/-- The contraction commutes with multiplication by the pulled back function `a`. -/
theorem thickeningContract_globalSmulCenter (a : A)
    (t : blowupUnit I ⟶ thickeningSheaf I (m + 1) ⊗ blowupTwistInt I q) :
    thickeningContract I m q ((globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app _ ≫ t) =
      (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app _ ≫
        thickeningContract I m q t := by
  unfold thickeningContract
  rw [comp_whiskerRight, globalSmulCenter_app_whiskerRight, Category.assoc,
    CatCenter.naturality_assoc]

/-- The round trip isomorphism of `𝒪_{Yₙ}(q)`. -/
abbrev thickeningRoundTrip : thickeningSheaf I (m + 1) ⊗ blowupTwistInt I q ⟶
    thickeningSheaf I (m + 1) ⊗ blowupTwistInt I q :=
  tensorRoundTrip (blowupTwistCoev I q) (blowupTwistEv I q) (thickeningSheaf I (m + 1))

variable {I m q}
variable {N : ModuleCat.{u} (A ⧸ I ^ (m + 1))}

/-- The family of maps `𝒪_X(-q) ⟶ 𝒪_{Yₙ}` attached to `φ : M → I^q/I^{q+n}`. -/
def homContractFamily (φ : resModule I (m + 1) N →ₗ[A] powQuot I q (m + 1))
    (z : resModule I (m + 1) N) : blowupTwistInt I (-(q : ℤ)) ⟶ thickeningSheaf I (m + 1) :=
  thickeningContract I m q (thickeningPointHom I m q (φ z) ≫ inv (thickeningRoundTrip I m q))

/-- The family attached to `φ + φ'` is the sum of the families. -/
theorem homContractFamily_add_left (φ φ' : resModule I (m + 1) N →ₗ[A] powQuot I q (m + 1))
    (z : resModule I (m + 1) N) :
    homContractFamily (φ + φ') z = homContractFamily φ z + homContractFamily φ' z := by
  unfold homContractFamily
  rw [LinearMap.add_apply, thickeningPointHom_add, Preadditive.add_comp, thickeningContract_add]

/-- The family attached to `a • φ` is the family attached to `φ`, precomposed with
multiplication by `a`. -/
theorem homContractFamily_smul_left (a : A) (φ : resModule I (m + 1) N →ₗ[A] powQuot I q (m + 1))
    (z : resModule I (m + 1) N) :
    homContractFamily (a • φ) z =
      (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app _ ≫ homContractFamily φ z := by
  unfold homContractFamily
  rw [LinearMap.smul_apply, thickeningPointHom_smul, Category.assoc,
    thickeningContract_globalSmulCenter]

/-- The family is additive in the element of `M`. -/
theorem homContractFamily_add (φ : resModule I (m + 1) N →ₗ[A] powQuot I q (m + 1))
    (z z' : resModule I (m + 1) N) :
    homContractFamily φ (z + z') = homContractFamily φ z + homContractFamily φ z' := by
  unfold homContractFamily
  rw [map_add, thickeningPointHom_add, Preadditive.add_comp, thickeningContract_add]

/-- The family is `A`-linear in the element of `M`. -/
theorem homContractFamily_smul (φ : resModule I (m + 1) N →ₗ[A] powQuot I q (m + 1)) (a : A)
    (z : resModule I (m + 1) N) :
    homContractFamily φ (a • z) =
      (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app _ ≫ homContractFamily φ z := by
  unfold homContractFamily
  rw [map_smul, thickeningPointHom_smul, Category.assoc, thickeningContract_globalSmulCenter]

/-- The map `𝒪_X(-q) ⟶ (p^*M)^∨` attached to `φ`. -/
def homContractDual (φ : resModule I (m + 1) N →ₗ[A] powQuot I q (m + 1)) :
    blowupTwistInt I (-(q : ℤ)) ⟶ blowupDual I (m + 1) N :=
  blowupDualLift I (m + 1) (homContractFamily φ) (homContractFamily_add φ)
    (homContractFamily_smul φ)

/-- The evaluations of `homContractDual φ` are the maps of the family. -/
theorem homContractDual_comp_blowupDualEval (φ : resModule I (m + 1) N →ₗ[A] powQuot I q (m + 1))
    (z : resModule I (m + 1) N) :
    homContractDual φ ≫ blowupDualEval I (m + 1) N z = homContractFamily φ z :=
  blowupDualLift_comp_blowupDualEval I (m + 1) _ _ _ z

/-- `homContractDual` is additive in `φ`. -/
theorem homContractDual_add (φ φ' : resModule I (m + 1) N →ₗ[A] powQuot I q (m + 1)) :
    homContractDual (φ + φ') = homContractDual φ + homContractDual φ' :=
  blowupDual_hom_ext I (m + 1) fun z => by
    rw [Preadditive.add_comp, homContractDual_comp_blowupDualEval,
      homContractDual_comp_blowupDualEval, homContractDual_comp_blowupDualEval,
      homContractFamily_add_left]

/-- `homContractDual` carries `a • φ` to multiplication by `a` followed by
`homContractDual φ`. -/
theorem homContractDual_smul (a : A) (φ : resModule I (m + 1) N →ₗ[A] powQuot I q (m + 1)) :
    homContractDual (a • φ) =
      (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app _ ≫ homContractDual φ :=
  blowupDual_hom_ext I (m + 1) fun z => by
    rw [Category.assoc, homContractDual_comp_blowupDualEval,
      homContractDual_comp_blowupDualEval, homContractFamily_smul_left]

/-- The map `𝒪_X ⟶ (p^*M)^∨(q)` attached to `φ`. -/
def homDualTwist (φ : resModule I (m + 1) N →ₗ[A] powQuot I q (m + 1)) :
    blowupUnit I ⟶ blowupDual I (m + 1) N ⊗ blowupTwistInt I q :=
  blowupTwistCoev I q ≫ (homContractDual φ ▷ blowupTwistInt I q)

/-- `homDualTwist` is additive in `φ`. -/
theorem homDualTwist_add (φ φ' : resModule I (m + 1) N →ₗ[A] powQuot I q (m + 1)) :
    homDualTwist (φ + φ') = homDualTwist φ + homDualTwist φ' := by
  unfold homDualTwist
  rw [homContractDual_add, add_whiskerRight_blowupTwistInt, Preadditive.comp_add]

/-- `homDualTwist` carries `a • φ` to multiplication by `a` followed by `homDualTwist φ`. -/
theorem homDualTwist_smul (a : A) (φ : resModule I (m + 1) N →ₗ[A] powQuot I q (m + 1)) :
    homDualTwist (a • φ) =
      (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app _ ≫ homDualTwist φ := by
  unfold homDualTwist
  rw [homContractDual_smul, comp_whiskerRight, globalSmulCenter_app_whiskerRight,
    ← Category.assoc, CatCenter.naturality, Category.assoc]

/-- **The evaluations of the map attached to `φ`**: `𝒪_X ⟶ (p^*M)^∨(q) ⟶ 𝒪_{Yₙ}(q)`, the
second map being `e_{p^*z}` twisted, is the map attached to `φ(z)`. The automorphism
`tensorRoundTrip` inverted in `homContractFamily` cancels against `comp_tensorRoundTrip`. -/
theorem homDualTwist_comp_blowupDualEval (φ : resModule I (m + 1) N →ₗ[A] powQuot I q (m + 1))
    (z : resModule I (m + 1) N) :
    homDualTwist φ ≫ (blowupDualEval I (m + 1) N z ▷ blowupTwistInt I q) =
      thickeningPointHom I m q (φ z) := by
  unfold homDualTwist
  rw [Category.assoc, ← comp_whiskerRight, homContractDual_comp_blowupDualEval]
  unfold homContractFamily thickeningContract
  rw [← comp_tensorRoundTrip, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

variable (I m q N)

/-- **The section `σ ∈ H⁰(X, (p^*M)^∨(q))` attached to `φ : M → I^q/I^{q+n}`.** -/
def blowupSecDual :
    (resModule I (m + 1) N →ₗ[A] powQuot I q (m + 1)) →ₗ[A]
      blowupHmod I 0 (blowupDual I (m + 1) N ⊗ blowupTwistInt I q) where
  toFun φ := blowupUnitHomH0 I (homDualTwist φ)
  map_add' φ φ' := by rw [homDualTwist_add, blowupUnitHomH0_add]
  map_smul' a φ := by rw [homDualTwist_smul, blowupUnitHomH0_globalSmulCenter]; rfl

variable [IsNoetherianRing A]

/-- **Evaluating the section attached to `φ` returns `φ`** (the field `evDual_secDual` of
`CanDualSituation`), for `q ≥ q₀` with `q₀` having the defining property of `q(S)`. -/
theorem blowupEvDual_blowupSecDual {q₀ : ℕ} (h : IsBaseThreshold I q₀) (hq : q₀ ≤ q)
    (φ : resModule I (m + 1) N →ₗ[A] powQuot I q (m + 1)) :
    blowupEvDual I m h hq N (blowupSecDual I m q N φ) = φ := by
  refine LinearMap.ext fun z => ?_
  rw [blowupEvDual_apply]
  refine (congrArg (LinearEquiv.ofBijective (cdivMod I m q)
    (bijective_cdivMod_of_le I h hq)).symm ?_).trans (LinearEquiv.symm_apply_apply _ (φ z))
  exact ((blowupHmodMap_blowupUnitHomH0 I _ _).trans
    (congrArg (blowupUnitHomH0 I) (homDualTwist_comp_blowupDualEval φ z))).trans
    (blowupUnitHomH0_thickeningPointHom I m q _)

end Stacks.LocalCohomology.UniformityIII

end
