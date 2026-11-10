module

public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleComplex
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Sections of a fibre product over a product of affine opens

Let `f : X ⟶ Spec R` and `g : Y ⟶ Spec R` be morphisms of schemes and let `U ⊆ X`, `V ⊆ Y` be
affine opens. The open `U ×_R V = fst⁻¹ U ∩ snd⁻¹ V` of `X ×_R Y` is affine and its ring of
sections is the tensor product `Γ(X, U) ⊗_R Γ(Y, V)`, through the canonical map
`a ⊗ b ↦ fst^* a · snd^* b`.

The `R`-algebra structures on rings of sections are those given by `Stacks.Cech.baseRingHom`.

## Main results

* `Stacks.AffineProduct.isAffineOpen_prodOpen`: `U ×_R V` is affine.
* `Stacks.AffineProduct.isPushout_prodOpen`: the square of rings of sections is a pushout.
* `Stacks.AffineProduct.prodSectionsEquiv`: the `R`-linear isomorphism
  `Γ(X, U) ⊗_R Γ(Y, V) ≃ Γ(X ×_R Y, U ×_R V)`, with `prodSectionsEquiv_tmul` describing it.

## References

* [Stacks Project, Tag 01JQ](https://stacks.math.columbia.edu/tag/01JQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.AffineProduct

variable {R : Type u} [CommRing R] {X Y T : Scheme.{u}} {f : X ⟶ Spec (.of R)}
  {g : Y ⟶ Spec (.of R)} (p : T ⟶ X) (q : T ⟶ Y)

/-- The open `U ×_R V = fst⁻¹ U ∩ snd⁻¹ V` of the fibre product. -/
noncomputable def prodOpen (U : X.Opens) (V : Y.Opens) : T.Opens :=
  p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V

/-- `U ×_R V` is contained in the preimage of `U` under the first projection. -/
theorem prodOpen_le_fst (U : X.Opens) (V : Y.Opens) :
    prodOpen p q U V ≤ p ⁻¹ᵁ U := inf_le_left

/-- `U ×_R V` is contained in the preimage of `V` under the second projection. -/
theorem prodOpen_le_snd (U : X.Opens) (V : Y.Opens) :
    prodOpen p q U V ≤ q ⁻¹ᵁ V := inf_le_right

/-- The open `U ×_R V` is monotone in `U` and in `V`. -/
theorem prodOpen_mono {U U' : X.Opens} {V V' : Y.Opens} (hU : U ≤ U') (hV : V ≤ V') :
    prodOpen p q U V ≤ prodOpen p q U' V' :=
  inf_le_inf (Scheme.Hom.preimage_mono _ hU) (Scheme.Hom.preimage_mono _ hV)

/-- `(U ∩ U') ×_R (V ∩ V') = (U ×_R V) ∩ (U' ×_R V')`. -/
theorem prodOpen_inf (U U' : X.Opens) (V V' : Y.Opens) :
    prodOpen p q (U ⊓ U') (V ⊓ V') = prodOpen p q U V ⊓ prodOpen p q U' V' := by
  ext x
  simp only [prodOpen, Opens.coe_inf, Scheme.Hom.coe_preimage, Set.preimage_inter,
    Set.mem_inter_iff]
  tauto

/-- The restricted square `U ×_R V ⟶ U, V ⟶ Spec R` is cartesian. -/
theorem isPullback_prodOpen (H : IsPullback p q f g) (U : X.Opens) (V : Y.Opens) :
    IsPullback (p.resLE U (prodOpen p q U V) (prodOpen_le_fst p q U V))
      (q.resLE V (prodOpen p q U V) (prodOpen_le_snd p q U V))
      (f.resLE ⊤ U (by simp)) (g.resLE ⊤ V (by simp)) :=
  Scheme.Hom.isPullback_resLE H (US := ⊤) (by simp) (by simp) rfl

/-- If `U` and `V` are affine opens, then `U ×_R V` is an affine open. -/
theorem isAffineOpen_prodOpen (H : IsPullback p q f g) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) : IsAffineOpen (prodOpen p q U V) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : IsAffine (⊤ : (Spec (.of R)).Opens).toScheme := isAffineOpen_top _
  exact IsAffine.of_isPullback (isPullback_prodOpen p q H U V)

/-- **The square of rings of sections over `U ×_R V` is a pushout.** -/
theorem isPushout_prodOpen (H : IsPullback p q f g) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) :
    IsPushout (f.appLE ⊤ U (by simp)) (g.appLE ⊤ V (by simp))
      (p.appLE U (prodOpen p q U V) (prodOpen_le_fst p q U V))
      (q.appLE V (prodOpen p q U V) (prodOpen_le_snd p q U V)) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : IsAffine (⊤ : (Spec (.of R)).Opens).toScheme := isAffineOpen_top _
  have h := isPushout_appTop_of_isPullback (isPullback_prodOpen p q H U V)
  exact h.of_iso (Scheme.Opens.topIso _) (Scheme.Opens.topIso _) (Scheme.Opens.topIso _)
    (Scheme.Opens.topIso _)
    (arrowResLEAppIso f ⊤ U _).hom.w.symm
    (arrowResLEAppIso g ⊤ V _).hom.w.symm
    (arrowResLEAppIso p U _ _).hom.w.symm
    (arrowResLEAppIso q V _ _).hom.w.symm

/-! ### The tensor product description -/

/-- The `R`-algebra structure on sections over `U`, as in the Čech complexes over `Spec R`. -/
@[instance_reducible]
noncomputable def sectionsAlgebra {Z : Scheme.{u}} (h : Z ⟶ Spec (.of R)) (W : Z.Opens) :
    Algebra R Γ(Z, W) :=
  (Stacks.Cech.baseRingHom h W).hom.toAlgebra

/-- Every open is contained in the preimage of the top open. -/
theorem le_preimage_top {Z Z' : Scheme.{u}} (h : Z' ⟶ Z) (W : Z'.Opens) : W ≤ h ⁻¹ᵁ ⊤ := by
  rw [Scheme.Hom.preimage_top]; exact le_top

/-- The structure map `R → Γ(Z, W)` followed by the pullback of sections along `p : Z' ⟶ Z`
is the structure map `R → Γ(Z', W')` of `p ≫ h`. -/
theorem baseRingHom_comp_appLE {Z Z' : Scheme.{u}} (h : Z ⟶ Spec (.of R)) (p : Z' ⟶ Z)
    (W : Z.Opens) (W' : Z'.Opens) (e : W' ≤ p ⁻¹ᵁ W) :
    Stacks.Cech.baseRingHom h W ≫ p.appLE W W' e = Stacks.Cech.baseRingHom (p ≫ h) W' := by
  have key : Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫ p.appLE W W' e =
      p.appTop ≫ Z'.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE]
    rfl
  simp only [Stacks.Cech.baseRingHom, Stacks.Cech.globalRingHom, Category.assoc,
    Scheme.Hom.comp_appTop, key]
  rfl

/-- The algebra structure on `Γ(U ×_R V)` over `Γ(X, U)` given by the first projection. -/
@[instance_reducible]
noncomputable def fstAlgebra (U : X.Opens) (V : Y.Opens) :
    Algebra Γ(X, U) Γ(T, prodOpen p q U V) :=
  (p.appLE U (prodOpen p q U V) (prodOpen_le_fst p q U V)).hom.toAlgebra

/-- The algebra structure on `Γ(U ×_R V)` over `Γ(Y, V)` given by the second projection. -/
@[instance_reducible]
noncomputable def sndAlgebra (U : X.Opens) (V : Y.Opens) :
    Algebra Γ(Y, V) Γ(T, prodOpen p q U V) :=
  (q.appLE V (prodOpen p q U V) (prodOpen_le_snd p q U V)).hom.toAlgebra

/-- `R → Γ(X, U) → Γ(U ×_R V)` is a scalar tower. -/
theorem isScalarTower_fst (U : X.Opens) (V : Y.Opens) :
    letI := sectionsAlgebra f U
    letI := sectionsAlgebra (p ≫ f) (prodOpen p q U V)
    letI := fstAlgebra p q U V
    IsScalarTower R Γ(X, U) Γ(T, prodOpen p q U V) :=
  let := sectionsAlgebra f U
  let := sectionsAlgebra (p ≫ f) (prodOpen p q U V)
  let := fstAlgebra p q U V
  IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom
    (baseRingHom_comp_appLE f p U (prodOpen p q U V)
      (prodOpen_le_fst p q U V))).symm

/-- `R → Γ(Y, V) → Γ(U ×_R V)` is a scalar tower. -/
theorem isScalarTower_snd (H : IsPullback p q f g) (U : X.Opens) (V : Y.Opens) :
    letI := sectionsAlgebra g V
    letI := sectionsAlgebra (p ≫ f) (prodOpen p q U V)
    letI := sndAlgebra p q U V
    IsScalarTower R Γ(Y, V) Γ(T, prodOpen p q U V) := by
  let := sectionsAlgebra g V
  let := sectionsAlgebra (p ≫ f) (prodOpen p q U V)
  let := sndAlgebra p q U V
  have hsnd := baseRingHom_comp_appLE g q V (prodOpen p q U V)
    (prodOpen_le_snd p q U V)
  rw [← H.w] at hsnd
  exact IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hsnd).symm

variable {p q}

/-- The pushout of rings over `U ×_R V`, as an `Algebra.IsPushout` over `R`. -/
theorem algebraIsPushout (H : IsPullback p q f g) {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) :
    letI := sectionsAlgebra f U
    letI := sectionsAlgebra g V
    letI := sectionsAlgebra (p ≫ f) (prodOpen p q U V)
    letI := fstAlgebra p q U V
    letI := sndAlgebra p q U V
    haveI := isScalarTower_fst (f := f) p q U V
    haveI := isScalarTower_snd p q H U V
    Algebra.IsPushout R Γ(X, U) Γ(Y, V) Γ(T, prodOpen p q U V) := by
  let := sectionsAlgebra f U
  let := sectionsAlgebra g V
  let := sectionsAlgebra (p ≫ f) (prodOpen p q U V)
  let := fstAlgebra p q U V
  let := sndAlgebra p q U V
  have := isScalarTower_fst (f := f) p q U V
  have := isScalarTower_snd p q H U V
  rw [← CommRingCat.isPushout_iff_isPushout]
  have h := isPushout_prodOpen p q H hU hV
  refine h.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  all_goals first | rfl | rw [Iso.refl_hom, Category.comp_id, ← Iso.inv_comp_eq]; rfl

/-- **The sections of `X ×_R Y` over `U ×_R V` are `Γ(X, U) ⊗_R Γ(Y, V)`.** -/
noncomputable def prodSectionsEquiv (H : IsPullback p q f g) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) :
    letI := sectionsAlgebra f U
    letI := sectionsAlgebra g V
    letI := sectionsAlgebra (p ≫ f) (prodOpen p q U V)
    Γ(X, U) ⊗[R] Γ(Y, V) ≃ₗ[R] Γ(T, prodOpen p q U V) :=
  letI := sectionsAlgebra f U
  letI := sectionsAlgebra g V
  letI := sectionsAlgebra (p ≫ f) (prodOpen p q U V)
  letI := fstAlgebra p q U V
  letI := sndAlgebra p q U V
  haveI := isScalarTower_fst (f := f) p q U V
  haveI := isScalarTower_snd p q H U V
  haveI := algebraIsPushout H hU hV
  (Algebra.IsPushout.equiv R Γ(X, U) Γ(Y, V) Γ(T, prodOpen p q U V)).restrictScalars R

/-- `prodSectionsEquiv` sends `a ⊗ b` to `fst^* a · snd^* b`. -/
theorem prodSectionsEquiv_tmul (H : IsPullback p q f g) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (a : Γ(X, U)) (b : Γ(Y, V)) :
    letI := sectionsAlgebra f U
    letI := sectionsAlgebra g V
    prodSectionsEquiv H hU hV (a ⊗ₜ b) =
      p.appLE U (prodOpen p q U V) (prodOpen_le_fst p q U V) a *
        q.appLE V (prodOpen p q U V) (prodOpen_le_snd p q U V) b := by
  let := sectionsAlgebra f U
  let := sectionsAlgebra g V
  let := sectionsAlgebra (p ≫ f) (prodOpen p q U V)
  let := fstAlgebra p q U V
  let := sndAlgebra p q U V
  have := isScalarTower_fst (f := f) p q U V
  have := isScalarTower_snd p q H U V
  have := algebraIsPushout H hU hV
  change Algebra.IsPushout.equiv R Γ(X, U) Γ(Y, V) _ (a ⊗ₜ b) = _
  rw [Algebra.IsPushout.equiv_tmul]
  rfl

end Stacks.AffineProduct

end
