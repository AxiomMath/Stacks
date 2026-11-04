module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatEffectiveSystem
public import StacksFrontier.AlgebraicGeometry.Quot.SpacesDefoThickeningTower
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFlatPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStack
public import StacksFrontier.AlgebraicGeometry.Spaces.InverseImageStructureSheafMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FirstOrderAlgebraExtension
public import StacksFrontier.Deformation.RingThickening.SquareZeroTowerKernels

/-!
# The algebraic spaces of a square-zero tower of proper flat families

Let `ξ : ℕ ⥤ Spaces'_{fp, flat, proper}` be a system of finitely presented, flat and proper
algebraic spaces `Xₙ ⟶ Yₙ`, the transition morphisms being cartesian squares, and suppose the
bases are identified with the spectra of a tower of rings `(Rₙ)` whose transition maps are
surjective with square-zero kernel, as in the opening of the body of the proof of
[Stacks Project, Tag 0D3X]. This file sets up the algebraic spaces of the proof:

* `Xₘ ⟶ Xₙ` lies over `Yₘ ⟶ Yₙ` in a cartesian square;
* `Y₀ ⟶ Yₙ` is a closed immersion of affine schemes, surjective with square-zero kernel on
  global functions, so that `X₀ ⊂ Xₙ` is a first order thickening ("We may think of
  `(X₁ ⊂ Xₙ) → (Spec(R₁) ⊂ Spec(Rₙ))` as a morphism of first order thickenings");
* `X₀` is the inverse image `g⁻¹(Y₀)` of `Y₀` in `Xₙ`, and the conormal module of `X₀ ⊂ Xₙ` is
  `𝒪_{X₀} ⊗_{R₀} Iₙ`, `Iₙ = Ker(Rₙ → R₀)`: the kernel of the extension
  `0 → 𝒪_{X₁} ⊗_{R₁} Iₙ → 𝒪_{Xₙ} → 𝒪_{X₁} → 0` of the source (06BH).

## Main definitions

* `AlgebraicGeometry.ProperFlatFibre.towerSpace`, `towerStructureMap`, `towerTransition`: the
  algebraic spaces `Xₙ`, their structure morphisms `Xₙ ⟶ Yₙ` and the transition morphisms.
* `AlgebraicGeometry.ProperFlatFibre.towerFibre`: the inverse image `g⁻¹(Y₀) ⊆ Xₙ`.
* `AlgebraicGeometry.ProperFlatFibre.towerFibreIso`: `X₀ ≅ g⁻¹(Y₀)`, over the transition
  morphism `X₀ ⟶ Xₙ`.
* `AlgebraicGeometry.ProperFlatFibre.towerFibreConormalIso`: the conormal module of
  `g⁻¹(Y₀) ⊆ Xₙ` is `𝒪 ⊗_{Γ(Y₀)} Ker(Γ(Yₙ) → Γ(Y₀))`, and
  `AlgebraicGeometry.ProperFlatFibre.towerFibreConormalKernelIso` its form `𝒪 ⊗_{R₀} Iₙ` with
  `Iₙ` the tower of kernels `CommAlgCat.towerKernelSystem`.
* `AlgebraicGeometry.ProperFlatFibre.towerRingSystem`: the tower of sheaves of rings
  `Aₙ = aₙ⁻¹𝒪_{Xₙ}` on the small étale site of `X₀`, `aₙ : X₀ ⟶ Xₙ`, with
  `AlgebraicGeometry.ProperFlatFibre.towerRingReduction` its cone of reductions `Aₙ ⟶ 𝒪_{X₀}`.

## Main results

* `AlgebraicGeometry.ProperFlatFibre.isPullback_towerTransition`: the transition squares are
  cartesian.
* `AlgebraicGeometry.ProperFlatFibre.isFirstOrderThickening_towerFibre`.
* `AlgebraicGeometry.ProperFlatFibre.isLocallySurjective_towerRingReduction_app`: each reduction
  `Aₙ ⟶ 𝒪_{X₀}` is locally surjective.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.ProperFlatFibre

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (ξ : ℕ ⥤ CartesianProperFlatSpaces B S hS)

/-- The algebraic space `Xₙ` of the `n`-th family of the system. -/
abbrev towerSpace (n : ℕ) : AlgebraicSpaces B S hS :=
  ((comma B S hS).obj (ξ.obj n)).left

/-- The base `Yₙ` of the `n`-th family of the system. -/
abbrev towerBase (n : ℕ) : BigFppfOver B S hS :=
  (ξ ⋙ cartesianProperFlatProjection B S hS).obj n

/-- The structure morphism `Xₙ ⟶ Yₙ` of the `n`-th family, as a morphism of algebraic spaces. -/
abbrev towerStructureMap (n : ℕ) : towerSpace ξ n ⟶ schemeSpace (towerBase ξ n) :=
  commaHomAsSpaceMap ((comma B S hS).obj (ξ.obj n))

/-- The transition morphism `Xₘ ⟶ Xₙ` of the system. -/
abbrev towerTransition {m n : ℕ} (k : m ⟶ n) : towerSpace ξ m ⟶ towerSpace ξ n :=
  ((comma B S hS).map (ξ.map k)).left

/-- **The transition squares of the system are cartesian**: `Xₘ = Xₙ ×_{Yₙ} Yₘ`. -/
theorem isPullback_towerTransition {m n : ℕ} (k : m ⟶ n) :
    IsPullback (towerTransition ξ k) (towerStructureMap ξ m) (towerStructureMap ξ n)
      (schemeSpaceMap ((ξ ⋙ cartesianProperFlatProjection B S hS).map k)) :=
  isPullback_commaHomAsSpaceMap_of_isStronglyCartesian B S hS ((comma B S hS).map (ξ.map k))
    (ξ.map k).2

/-- The transition morphisms of the system compose. -/
theorem towerTransition_comp {l m n : ℕ} (k : l ⟶ m) (k' : m ⟶ n) :
    towerTransition ξ k ≫ towerTransition ξ k' = towerTransition ξ (k ≫ k') := by
  simp only [towerTransition, Functor.map_comp, Comma.comp_left]

/-- The structure morphism of `Xₙ` is flat. -/
theorem isFlat_towerStructureMap (n : ℕ) : Space.IsFlat B S hS (towerStructureMap ξ n).hom :=
  (ξ.obj n).obj.property.2.1

variable {Λ : Type u} [CommRing Λ] {R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ}
  (hsurj : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
  (hsq : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), RingHom.ker (R.map f).hom.toRingHom ^ 2 = ⊥)
  (e : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).obj (towerBase ξ n) ≅
    Spec (.of (R.obj (.op n))))
  (he : ∀ {i j : ℕ} (f : i ⟶ j),
    (BigFppfOver.toScheme B S hS).map ((ξ ⋙ cartesianProperFlatProjection B S hS).map f) ≫
      (e j).hom = (e i).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (R.map f.op).hom.toRingHom).op)

include hsurj hsq he in
/-- **The transition morphisms of the bases are closed immersions.** -/
theorem isClosedImmersion_towerBase_map {m n : ℕ} (k : m ⟶ n) :
    AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map ((ξ ⋙ cartesianProperFlatProjection B S hS).map k)) :=
  (isSquareZeroClosedImmersion_of_squareZeroTower R hsurj hsq _ e he k).1

include e in
/-- The bases of the system are affine. -/
theorem isAffine_towerBase (n : ℕ) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (towerBase ξ n)) :=
  .of_isIso (e n).hom

include hsurj hsq he in
/-- **`Γ(Yₙ) ⟶ Γ(Yₘ)` is surjective with square-zero kernel.** -/
theorem surjective_and_ker_sq_eq_bot_towerBase_map {m n : ℕ} (k : m ⟶ n) :
    Function.Surjective (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        ((ξ ⋙ cartesianProperFlatProjection B S hS).map k)).op).hom ∧
      RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        ((ξ ⋙ cartesianProperFlatProjection B S hS).map k)).op).hom ^ 2 = ⊥ :=
  surjective_and_ker_sq_eq_bot_Γ_map_of_specIso (CommRingCat.ofHom (R.map k.op).hom.toRingHom)
    (hsurj k.op) (hsq k.op) _ (e m) (e n) (he k)

/-- **The inverse image `g⁻¹(Y₀) ⊆ Xₙ`** of the closed subscheme `Y₀ ⊆ Yₙ` under the structure
morphism `g : Xₙ ⟶ Yₙ`. -/
abbrev towerFibre (n : ℕ) : Space.ClosedSubspaces B S hS (towerSpace ξ n).1 :=
  Space.preimageSubspace B S hS (towerStructureMap ξ n)
    (Space.rangeSubspace B S hS ((ξ ⋙ cartesianProperFlatProjection B S hS).map
      (homOfLE (Nat.zero_le n))) (isClosedImmersion_towerBase_map ξ hsurj hsq e he _))

include hsurj hsq he in
/-- **`g⁻¹(Y₀) ⊆ Xₙ` is a first order thickening.** -/
theorem isFirstOrderThickening_towerFibre (n : ℕ) :
    Space.IsFirstOrderThickening B S hS (towerSpace ξ n) (towerFibre ξ hsurj hsq e he n).1 :=
  Space.isFirstOrderThickening_preimage_squareZeroSubspace B S hS _
    (isSquareZeroClosedImmersion_of_squareZeroTower R hsurj hsq _ e he _) (towerStructureMap ξ n)

/-- The algebraic space underlying `g⁻¹(Y₀) ⊆ Xₙ`. -/
abbrev towerFibreSpace (n : ℕ) : AlgebraicSpaces B S hS :=
  ⟨(towerFibre ξ hsurj hsq e he n).1.toFunctor, (towerFibre ξ hsurj hsq e he n).2.1⟩

/-- `g⁻¹(Y₀) = Xₙ ×_{Yₙ} Y₀`: the inclusion of `g⁻¹(Y₀)` and its projection to `Y₀` form a
cartesian square over `Xₙ ⟶ Yₙ ⟵ Y₀`. -/
theorem isPullback_towerFibre (n : ℕ) :
    IsPullback (Space.subspaceInclusion B S hS (towerSpace ξ n) (towerFibre ξ hsurj hsq e he n))
      (Space.preimageRangeProjection B S hS (towerStructureMap ξ n) _
        (isClosedImmersion_towerBase_map ξ hsurj hsq e he (homOfLE (Nat.zero_le n))))
      (towerStructureMap ξ n)
      (schemeSpaceMap ((ξ ⋙ cartesianProperFlatProjection B S hS).map
        (homOfLE (Nat.zero_le n)))) := by
  have hj := isClosedImmersion_towerBase_map ξ hsurj hsq e he (homOfLE (Nat.zero_le n))
  have hB := Space.isPullback_preimageSubspace B S hS (towerStructureMap ξ n)
    (Space.rangeSubspace B S hS _ hj)
  have key : (Space.rangeIsoPresheaf B S hS _ hj).inv ≫
      yoneda.map ((ξ ⋙ cartesianProperFlatProjection B S hS).map (homOfLE (Nat.zero_le n))) =
      (Space.rangeSubspace B S hS _ hj).1.ι :=
    (Iso.inv_comp_eq _).2 (Subfunctor.toRange_ι _).symm
  refine IsPullback.of_map (ObjectProperty.ι _)
    (Space.preimageRangeProjection_comp B S hS (towerStructureMap ξ n) _ hj).symm ?_
  exact hB.of_iso (Iso.refl _) (Iso.refl _) (Space.rangeIsoPresheaf B S hS _ hj).symm
    (Iso.refl _) (Category.id_comp _).symm (Category.id_comp _).symm
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    (by rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id]; exact key.symm)

/-- **`X₀ ≅ g⁻¹(Y₀)`**: the transition morphism `X₀ ⟶ Xₙ` identifies `X₀` with the inverse
image of `Y₀` in `Xₙ`. -/
def towerFibreIso (n : ℕ) : towerSpace ξ 0 ≅ towerFibreSpace ξ hsurj hsq e he n :=
  (isPullback_towerTransition ξ (homOfLE (Nat.zero_le n))).isoIsPullback _ _
    (isPullback_towerFibre ξ hsurj hsq e he n)

/-- The isomorphism `X₀ ≅ g⁻¹(Y₀)` followed by the inclusion `g⁻¹(Y₀) ⟶ Xₙ` is the transition
morphism `X₀ ⟶ Xₙ`. -/
@[reassoc (attr := simp)]
theorem towerFibreIso_hom_comp_subspaceInclusion (n : ℕ) :
    (towerFibreIso ξ hsurj hsq e he n).hom ≫
        Space.subspaceInclusion B S hS (towerSpace ξ n) (towerFibre ξ hsurj hsq e he n) =
      towerTransition ξ (homOfLE (Nat.zero_le n)) :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- **The conormal module of `X₀ ⊂ Xₙ`** is `𝒪 ⊗_{Γ(Y₀)} Iₙ` with
`Iₙ = Ker(Γ(Yₙ) → Γ(Y₀))`, a module over `Γ(Y₀)` because it has square zero, the base ring acting
through the projection `g⁻¹(Y₀) ⟶ Y₀` (06BH, flat clause of 04CQ). -/
def towerFibreConormalIso (n : ℕ) :
    Space.conormalModule B S hS (towerSpace ξ n) (towerFibre ξ hsurj hsq e he n) ≅
      (Space.baseRingTensorModule B S hS _ (Space.baseRingHomOfMap
          (Space.preimageRangeProjection B S hS (towerStructureMap ξ n) _
            (isClosedImmersion_towerBase_map ξ hsurj hsq e he (homOfLE (Nat.zero_le n)))))).obj
        (RingHom.squareZeroKer _
          (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he
            (homOfLE (Nat.zero_le n))).1
          (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he
            (homOfLE (Nat.zero_le n))).2) :=
  Space.conormalModulePreimageSquareZeroIso B S hS (towerStructureMap ξ n) _
    (isClosedImmersion_towerBase_map ξ hsurj hsq e he _) (isFlat_towerStructureMap ξ n)
    (isAffine_towerBase ξ e n)
    (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he _).2

include e in
/-- **`Γ(Yₙ) ≅ Rₙ`**, through the identification `Yₙ ≅ Spec(Rₙ)`. -/
def towerBaseΓIso (n : ℕ) :
    Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj (towerBase ξ n))) ≅
      CommRingCat.of (R.obj (op n)) :=
  (Scheme.Γ.mapIso (e n).op).symm ≪≫ Scheme.ΓSpecIso _

/-- The isomorphism `Γ(Yₙ) ≅ Rₙ` is the pullback of functions along `Spec(Rₙ) ≅ Yₙ` followed by
`Γ(Spec(Rₙ)) ≅ Rₙ`. -/
theorem towerBaseΓIso_hom (n : ℕ) :
    (towerBaseΓIso ξ e n).hom = (e n).inv.appTop ≫ (Scheme.ΓSpecIso _).hom :=
  rfl

include he in
/-- Pullback of functions along `Yₘ ⟶ Yₙ` is `Rₙ ⟶ Rₘ` under `Γ(Y) ≅ R`. -/
theorem towerBaseΓIso_naturality {m n : ℕ} (k : m ⟶ n) :
    (towerBaseΓIso ξ e n).inv ≫ Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        ((ξ ⋙ cartesianProperFlatProjection B S hS).map k)).op =
      CommRingCat.ofHom (R.map k.op).hom.toRingHom ≫ (towerBaseΓIso ξ e m).inv := by
  have hf : (BigFppfOver.toScheme B S hS).map ((ξ ⋙ cartesianProperFlatProjection B S hS).map k) =
      (e m).hom ≫ Spec.map (CommRingCat.ofHom (R.map k.op).hom.toRingHom) ≫ (e n).inv := by
    rw [← Category.assoc]
    exact (Iso.eq_comp_inv _).2 (he k)
  have hc : (e m).hom.appTop ≫ (e m).inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id]
    rfl
  have key : ((BigFppfOver.toScheme B S hS).map
      ((ξ ⋙ cartesianProperFlatProjection B S hS).map k)).appTop ≫ (towerBaseΓIso ξ e m).hom =
      (towerBaseΓIso ξ e n).hom ≫ CommRingCat.ofHom (R.map k.op).hom.toRingHom := by
    rw [towerBaseΓIso_hom, towerBaseΓIso_hom, hf, Scheme.Hom.comp_appTop,
      Scheme.Hom.comp_appTop]
    simp only [Category.assoc]
    rw [reassoc_of% hc, Scheme.ΓSpecIso_naturality]
    exact (Category.assoc _ _ _).symm
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact key

include hsurj hsq he in
/-- **The tower kernel `Iₙ = Ker(Rₙ → R₀)` is `Ker(Γ(Yₙ) → Γ(Y₀))`**, as `R₀`-modules, the latter
read over `R₀` through `R₀ ≅ Γ(Y₀)`. -/
def towerKernelIso (n : ℕ) :
    (CommAlgCat.towerKernelSystem R hsurj hsq).obj (op n) ≅
      (ModuleCat.restrictScalars.{u} (towerBaseΓIso ξ e 0).inv.hom).obj
        (RingHom.squareZeroKer _
          (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he
            (homOfLE (Nat.zero_le n))).1
          (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he
            (homOfLE (Nat.zero_le n))).2) :=
  RingHom.squareZeroKerRestrictScalarsIso _ (hsurj _) (hsq _) _ _ _
    (towerBaseΓIso ξ e n).symm.commRingCatIsoToRingEquiv
    (towerBaseΓIso ξ e 0).inv.hom
    (congrArg CommRingCat.Hom.hom (towerBaseΓIso_naturality ξ e he (homOfLE (Nat.zero_le n))))
    (ConcreteCategory.bijective_of_isIso (towerBaseΓIso ξ e 0).inv).1

/-- **The conormal module of `X₀ ⊂ Xₙ` is `𝒪 ⊗_{R₀} Iₙ`**, `Iₙ = Ker(Rₙ → R₀)` the `n`-th term
of the tower of kernels, the base ring `R₀ ≅ Γ(Y₀)` acting through the projection
`g⁻¹(Y₀) ⟶ Y₀`. This is the kernel `𝒪_{X₁} ⊗_{R₁} Iₙ` of `𝒪_{Xₙ} ⟶ 𝒪_{X₁}` in the body of
[Stacks Project, Tag 0D3X] (there indexed from `1`). -/
def towerFibreConormalKernelIso (n : ℕ) :
    Space.conormalModule B S hS (towerSpace ξ n) (towerFibre ξ hsurj hsq e he n) ≅
      (Space.baseRingTensorModule B S hS _ ((Space.baseRingHomOfMap
          (Space.preimageRangeProjection B S hS (towerStructureMap ξ n) _
            (isClosedImmersion_towerBase_map ξ hsurj hsq e he (homOfLE (Nat.zero_le n))))).comp
          (towerBaseΓIso ξ e 0).inv.hom)).obj
        ((CommAlgCat.towerKernelSystem R hsurj hsq).obj (op n)) :=
  towerFibreConormalIso ξ hsurj hsq e he n ≪≫
    ((Space.baseRingTensorModuleRestrictScalarsIso B S hS (towerFibreSpace ξ hsurj hsq e he n)
      (towerBaseΓIso ξ e 0).inv.hom (Space.baseRingHomOfMap
          (Space.preimageRangeProjection B S hS (towerStructureMap ξ n) _
            (isClosedImmersion_towerBase_map ξ hsurj hsq e he (homOfLE (Nat.zero_le n)))))
      (ConcreteCategory.bijective_of_isIso (towerBaseΓIso ξ e 0).inv).2).app
        (RingHom.squareZeroKer _
          (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he
            (homOfLE (Nat.zero_le n))).1
          (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he
            (homOfLE (Nat.zero_le n))).2)).symm ≪≫
    (Space.baseRingTensorModule B S hS (towerFibreSpace ξ hsurj hsq e he n)
      ((Space.baseRingHomOfMap
          (Space.preimageRangeProjection B S hS (towerStructureMap ξ n) _
            (isClosedImmersion_towerBase_map ξ hsurj hsq e he (homOfLE (Nat.zero_le n))))).comp
          (towerBaseΓIso ξ e 0).inv.hom)).mapIso (towerKernelIso ξ hsurj hsq e he n).symm

/-! ### The tower of ring sheaves `Aₙ = aₙ⁻¹𝒪_{Xₙ}` on `X₀` -/

/-- The transition morphism `aₙ : X₀ ⟶ Xₙ`. -/
abbrev towerInclusion (n : ℕ) : towerSpace ξ 0 ⟶ towerSpace ξ n :=
  towerTransition ξ (homOfLE (Nat.zero_le n))

/-- The composite of `aₙ : X₀ ⟶ Xₙ` with the transition morphism `Xₙ ⟶ X_{n+1}` is `a_{n+1}`. -/
theorem towerInclusion_comp_towerTransition (n : ℕ) :
    towerInclusion ξ n ≫ towerTransition ξ (homOfLE (Nat.le_succ n)) = towerInclusion ξ (n + 1) :=
  (towerTransition_comp ξ _ _).trans (congrArg (towerTransition ξ) (Subsingleton.elim _ _))

/-- **The tower of sheaves of rings `Aₙ = aₙ⁻¹𝒪_{Xₙ}`** on the small étale site of `X₀`, with
transition maps `A_{n+1} = aₙ⁻¹t⁻¹𝒪_{X_{n+1}} ⟶ aₙ⁻¹𝒪_{Xₙ} = Aₙ` the inverse images along `aₙ`
of the structure maps of the transition morphisms `t : Xₙ ⟶ X_{n+1}` (Stacks 03G8). These are the
sheaves `𝒪_{Xₙ}` of the body of the proof of [Stacks Project, Tag 0D3X], read on the étale site
of `X₁` (there indexed from `1`) by the topological invariance of the étale site. -/
def towerRingSystem :
    ℕᵒᵖ ⥤ Sheaf (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) CommRingCat.{u} :=
  Functor.ofOpSequence (X := fun n => Space.inverseImageStructureSheaf B S hS (towerInclusion ξ n))
    fun n => Space.inverseImageStructureSheafMapOfEq B S hS
    (towerInclusion ξ n) (towerTransition ξ (homOfLE (Nat.le_succ n)))
    (towerInclusion_comp_towerTransition ξ n)

/-- The `n`-th term of the tower of ring sheaves is `aₙ⁻¹𝒪_{Xₙ}`. -/
theorem towerRingSystem_obj (n : ℕ) :
    (towerRingSystem ξ).obj (op n) = Space.inverseImageStructureSheaf B S hS (towerInclusion ξ n) :=
  rfl

/-- The transition map `A_{n+1} ⟶ Aₙ` of the tower of ring sheaves is the inverse image along `aₙ`
of the structure map of the transition morphism `Xₙ ⟶ X_{n+1}`. -/
theorem towerRingSystem_map_succ (n : ℕ) :
    (towerRingSystem ξ).map (homOfLE (Nat.le_succ n)).op =
      Space.inverseImageStructureSheafMapOfEq B S hS (towerInclusion ξ n)
        (towerTransition ξ (homOfLE (Nat.le_succ n))) (towerInclusion_comp_towerTransition ξ n) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- **The reductions `Aₙ ⟶ 𝒪_{X₀}`**, the inverse-image forms `aₙ^♯` of the structure maps of
`aₙ`, as a cone over the tower with vertex `𝒪_{X₀}`. -/
def towerRingReduction :
    towerRingSystem ξ ⟶
      (Functor.const _).obj (Space.smallEtaleRingedTopos B S hS (towerSpace ξ 0)).O :=
  NatTrans.ofOpSequence (F := towerRingSystem ξ)
    (G := (Functor.const _).obj (Space.smallEtaleRingedTopos B S hS (towerSpace ξ 0)).O)
    (fun n => Space.structureSharpInverseImage B S hS (towerInclusion ξ n)) fun n =>
      (congrArg (· ≫ Space.structureSharpInverseImage B S hS (towerInclusion ξ n))
        (towerRingSystem_map_succ ξ n)).trans
      ((Space.inverseImageStructureSheafMapOfEq_comp_structureSharpInverseImage B S hS
        (towerInclusion ξ n) (towerTransition ξ (homOfLE (Nat.le_succ n)))
        (towerInclusion_comp_towerTransition ξ n)).trans (Category.comp_id _).symm)

/-- The `n`-th reduction `Aₙ ⟶ 𝒪_{X₀}` is the inverse-image form `aₙ^♯` of the structure map of
`aₙ`. -/
theorem towerRingReduction_app (n : ℕ) :
    (towerRingReduction ξ).app (op n) =
      Space.structureSharpInverseImage B S hS (towerInclusion ξ n) :=
  rfl

include hsurj hsq he in
/-- **`aₙ : X₀ ⟶ Xₙ` is a closed immersion**, the base change of `Y₀ ⟶ Yₙ`. -/
theorem isClosedImmersion_towerInclusion (n : ℕ) :
    Space.IsClosedImmersion B S hS (towerInclusion ξ n).hom := by
  have hb : Space.IsClosedImmersion B S hS
      (schemeSpaceMap ((ξ ⋙ cartesianProperFlatProjection B S hS).map
        (homOfLE (Nat.zero_le n)))).hom :=
    (Space.presheaf_yoneda_map_iff B S hS
      AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange
        ((ξ ⋙ cartesianProperFlatProjection B S hS).map (homOfLE (Nat.zero_le n)))).2
      (isClosedImmersion_towerBase_map ξ hsurj hsq e he (homOfLE (Nat.zero_le n)))
  exact (Space.isClosedImmersion_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_hom B S hS
      (isPullback_towerTransition ξ (homOfLE (Nat.zero_le n))).flip) hb

include hsurj hsq he in
/-- **Each reduction `Aₙ ⟶ 𝒪_{X₀}` is locally surjective**, `aₙ` being a closed immersion (the
surjectivity clause of Stacks 03MB). -/
theorem isLocallySurjective_towerRingReduction_app (n : ℕ) :
    Presheaf.IsLocallySurjective (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
      ((towerRingReduction ξ).app (op n)).hom :=
  Space.isLocallySurjective_structureSharpInverseImage B S hS (towerInclusion ξ n)
    (isClosedImmersion_towerInclusion ξ hsurj hsq e he n)

end AlgebraicGeometry.ProperFlatFibre

end
