module

public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedCoherent
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.CoherentSubcategoryShortExact
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.CoherentLeadingTerm
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.WeightSeparation
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.DevissageFiltration
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support

/-!
# Coherent modules with supports, their cycles, and injectivity given a weight operator

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be a
Noetherian scheme locally of finite type over `S`, with relative dimension function
`δ = δ_{X/S}`. For a closed subset `Z ⊆ X` write `Coh_Z(X)` for the coherent `𝒪_X`-modules whose
support lies in `Z`; it is a Serre subcategory of `Coh(X)`, and

  `G(Z) = 𝐐 ⊗ K₀(Coh_Z(X))`

is a functor of `Z` for inclusions, with `G(∅) = 0` and `G(X) = K'₀(X) ⊗ 𝐐`.

If every point of `Z` has `δ ≤ k`, the `k`-cycle `[F]_k` of an object of `Coh_Z(X)` is defined,
and it is additive, so it induces a homomorphism `G(Z) ⟶ Z_k(X) ⊗ 𝐐`. An element of its kernel
comes from `G(Z')` for a single closed `Z' ⊆ Z` on which `δ ≤ k - 1`. By the dévissage
of Stacks 01YF a coherent module supported in `Z` has the class, modulo modules supported in
closed subsets of `δ ≤ k - 1`, of a combination of the structure sheaves `𝒪_{\overline{ξ}}` of
the points `ξ ∈ Z` with `δ(ξ) = k`: for the direct image of an ideal sheaf on an integral closed
subscheme with generic point `ξ` this is a length count at `ξ`. The `k`-cycle of such a
combination reads off its coefficients, and a finite sum of classes from closed subsets of
`δ ≤ k - 1` comes from their union.

Combined with the separation of weights over a Noetherian space
(`Stacks.Chow.WeightSeparation.eq_zero_of_forall_mem_iSup`), this shows that for a closed
immersion `i : X ⟶ Y` into a regular quasi-compact `Y` the map `K'₀(X) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐` of
Stacks 0FEW is injective as soon as `G` carries a natural endomorphism `Ψ` which, on every `Z`
with `δ ≤ k`, acts on `k`-cycles as multiplication by `ℓ^{-k}` for a fixed `ℓ > 1`: an element
of `K'₀(X)` lying rationally in every step of the filtration by dimension of supports is torsion.

## Main definitions

* `Stacks.Chow.coherentSupportedIn` — the coherent modules whose support lies in a given set.
* `Stacks.Chow.supportedCoherentKZero` — the Grothendieck group `K₀(Coh_Z(X))`.
* `Stacks.Chow.supportedCoherentKZeroRat` — the functor `Z ↦ 𝐐 ⊗ K₀(Coh_Z(X))` on closed subsets.
* `Stacks.Chow.supportedCoherentKZeroRatToCoherent` — the comparison `G(Z) ⟶ K'₀(X) ⊗ 𝐐`.
* `Stacks.Chow.supportedCoherentKZeroCycle`, `Stacks.Chow.supportedCoherentKZeroRatCycle` — the
  `k`-cycle of an element of `K₀(Coh_Z(X))`, resp. of `G(Z)`, when `δ ≤ k` on `Z`.

## Main results

* `Stacks.Chow.bijective_supportedCoherentKZeroRatToCoherent_top` — `G(X) = K'₀(X) ⊗ 𝐐`.
* `Stacks.Chow.subsingleton_supportedCoherentKZeroRat_bot` — `G(∅) = 0`.
* `Stacks.Chow.mem_supportedCoherentKZeroLowerPart_of_cycle_eq_zero` — an element of
  `K₀(Coh_Z(X))` with zero `k`-cycle comes from closed subsets of `Z` on which `δ ≤ k - 1`.
* `Stacks.Chow.exists_mem_range_of_supportedCoherentKZeroRatCycle_eq_zero` — the same for `G(Z)`,
  with a single closed subset.
* `Stacks.Chow.exists_lt_sub_smul_mem_range_of_supportedWeightOperator` — an endomorphism `Ψ`
  acting on `k`-cycles as `ℓ^{-k}` satisfies the hypothesis of the separation of weights.
* `Stacks.Chow.exists_zsmul_eq_zero_of_supportedWeightOperator` — given such a `Ψ`, the
  filtration of `K'₀(X)` by dimension of supports is separated up to torsion.
* `Stacks.Chow.injective_liftBaseChange_coherentChowCharacter_of_supportedWeightOperator` —
  injectivity in Stacks 0FEW, given the endomorphism `Ψ`.

## Implementation notes

The support condition is a condition on sets, `supp F ⊆ Z`; on a closed `Z` it is the condition of
`AlgebraicGeometry.supportedCoherentProperty` for the reduced closed subscheme carried by `Z`,
whose Serre property is reused.

The weight of a point `z` in the separation argument is `-δ(z)`, and the scalar attached to the
weight `n` is `ℓ^n`. On a nonempty closed `Z` the point `z₀` of the separation argument is a point
of maximal `δ`; it does not lie in the closed subset `Z'` produced by the cycle computation, so
`Z' ⊊ Z`.

## References

* [Stacks Project, Tag 0FEW](https://stacks.math.columbia.edu/tag/0FEW)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
* [Stacks Project, Tag 0FDT](https://stacks.math.columbia.edu/tag/0FDT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-! ### Coherent modules supported in a set -/

/-- The property of a coherent `𝒪_X`-module that its support lies in a given set `T`. -/
abbrev coherentSupportedIn (T : Set X) :
    ObjectProperty (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) :=
  fun F => SheafOfModules.supp F.obj ⊆ T

/-- On a closed subset `Z`, the support condition is the one of the reduced closed subscheme
carried by `Z`. -/
theorem coherentSupportedIn_eq_supportedCoherentProperty (Z : Closeds X) :
    coherentSupportedIn (Z : Set X) =
      supportedCoherentProperty (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι := by
  have h : Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.base = (Z : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  funext F
  simp only [coherentSupportedIn, supportedCoherentProperty, h]
  rfl

/-- **Stacks 0FEP** for supports in a closed subset: the coherent modules supported in a closed
subset form a Serre subcategory of the coherent modules. -/
instance coherentSupportedIn_isSerreClass [IsLocallyNoetherian X] (Z : Closeds X) :
    (coherentSupportedIn (Z : Set X)).IsSerreClass := by
  rw [coherentSupportedIn_eq_supportedCoherentProperty]
  infer_instance

/-! ### The Grothendieck group of `Coh_Z(X)` -/

section KGroup

variable [IsLocallyNoetherian X]

/-- The Grothendieck group `K₀(Coh_Z(X))` of the coherent `𝒪_X`-modules supported in a closed
subset `Z`. -/
abbrev supportedCoherentKZero (Z : Closeds X) : Type (u + 1) :=
  KZero (coherentSupportedIn (Z : Set X)).FullSubcategory

/-- **Additivity of classes in `K₀(Coh_Z(X))`, read on the underlying `𝒪_X`-modules.** A short
exact sequence of `𝒪_X`-modules whose three terms are objects of `Coh_Z(X)` is a short exact
sequence of `Coh_Z(X)`, the inclusion into all `𝒪_X`-modules being fully faithful and exact. -/
theorem supportedCoherentKZero_mk_add {Z : Closeds X}
    (A₁ A₂ A₃ : (coherentSupportedIn (Z : Set X)).FullSubcategory)
    (u : A₁.obj.obj ⟶ A₂.obj.obj) (v : A₂.obj.obj ⟶ A₃.obj.obj) (w : u ≫ v = 0)
    (hS : (ShortComplex.mk u v w).ShortExact) :
    KZero.mk _ A₂ = KZero.mk _ A₁ + KZero.mk _ A₃ := by
  obtain ⟨u', v', w', hT⟩ := exists_shortExact_of_shortExact_obj A₁ A₂ A₃ u v w hS
  exact KZero.mk_of_shortExact _ hT

/-- Objects of `Coh_Z(X)` with isomorphic underlying `𝒪_X`-modules have the same class in
`K₀(Coh_Z(X))`. -/
theorem supportedCoherentKZero_mk_eq_of_iso {Z : Closeds X}
    (A B : (coherentSupportedIn (Z : Set X)).FullSubcategory) (e : A.obj.obj ≅ B.obj.obj) :
    KZero.mk _ A = KZero.mk _ B :=
  KZero.mk_eq_of_iso
    (((ObjectProperty.fullyFaithfulι _).comp (ObjectProperty.fullyFaithfulι _)).preimageIso
      (F := (coherentSupportedIn (Z : Set X)).ι ⋙
        (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι) e)

/-- An object of `Coh_Z(X)` whose underlying `𝒪_X`-module is zero has zero class. -/
theorem supportedCoherentKZero_mk_eq_zero {Z : Closeds X}
    (A : (coherentSupportedIn (Z : Set X)).FullSubcategory) (h : IsZero A.obj.obj) :
    KZero.mk _ A = 0 :=
  KZero.mk_eq_zero_of_isZero (IsZero.of_full_of_faithful_of_isZero
    ((coherentSupportedIn (Z : Set X)).ι ⋙
      (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι) A h)

/-- The homomorphism `K₀(Coh_{Z'}(X)) ⟶ K₀(Coh_Z(X))` induced by the inclusion `Z' ⊆ Z`. -/
def supportedCoherentKZeroMap {Z' Z : Closeds X} (h : Z' ≤ Z) :
    supportedCoherentKZero Z' →+ supportedCoherentKZero Z :=
  KZero.lift (fun A => KZero.mk _ ⟨A.obj, A.property.trans h⟩) fun _ hS =>
    supportedCoherentKZero_mk_add _ _ _ _ _ _
      ((Stacks.SheafOfModules.coherentModules X.ringCatSheaf).shortExact_map_ι
        ((coherentSupportedIn (Z' : Set X)).shortExact_map_ι hS))

/-- The map induced by `Z' ⊆ Z` sends the class of an object of `Coh_{Z'}(X)` to its class in
`K₀(Coh_Z(X))`. -/
@[simp]
theorem supportedCoherentKZeroMap_mk {Z' Z : Closeds X} (h : Z' ≤ Z)
    (A : (coherentSupportedIn (Z' : Set X)).FullSubcategory) :
    supportedCoherentKZeroMap h (KZero.mk _ A) = KZero.mk _ ⟨A.obj, A.property.trans h⟩ :=
  KZero.lift_mk _ _ _

/-- The inclusion of a closed subset in itself induces the identity. -/
theorem supportedCoherentKZeroMap_refl (Z : Closeds X) :
    supportedCoherentKZeroMap (le_refl Z) = AddMonoidHom.id _ :=
  KZero.hom_ext fun A => supportedCoherentKZeroMap_mk _ A

/-- The homomorphisms induced by inclusions compose. -/
theorem supportedCoherentKZeroMap_comp {Z'' Z' Z : Closeds X} (h₁ : Z'' ≤ Z') (h₂ : Z' ≤ Z) :
    (supportedCoherentKZeroMap h₂).comp (supportedCoherentKZeroMap h₁) =
      supportedCoherentKZeroMap (h₁.trans h₂) :=
  KZero.hom_ext fun A => by
    rw [AddMonoidHom.comp_apply, supportedCoherentKZeroMap_mk, supportedCoherentKZeroMap_mk,
      supportedCoherentKZeroMap_mk]

/-- The homomorphism `K₀(Coh_Z(X)) ⟶ K'₀(X)` induced by the inclusion `Coh_Z(X) ⊆ Coh(X)`. -/
def supportedCoherentKZeroToCoherentKZero (Z : Closeds X) :
    supportedCoherentKZero Z →+ CoherentKZero X :=
  KZero.lift (fun A => KZero.mk _ A.obj) fun _ hS =>
    KZero.mk_of_shortExact _ ((coherentSupportedIn (Z : Set X)).shortExact_map_ι hS)

/-- The comparison with `K'₀(X)` sends the class of an object of `Coh_Z(X)` to the class of the
underlying coherent module. -/
@[simp]
theorem supportedCoherentKZeroToCoherentKZero_mk (Z : Closeds X)
    (A : (coherentSupportedIn (Z : Set X)).FullSubcategory) :
    supportedCoherentKZeroToCoherentKZero Z (KZero.mk _ A) = KZero.mk _ A.obj :=
  KZero.lift_mk _ _ _

/-- The comparison with `K'₀(X)` is compatible with the maps induced by inclusions. -/
theorem supportedCoherentKZeroToCoherentKZero_comp_map {Z' Z : Closeds X} (h : Z' ≤ Z) :
    (supportedCoherentKZeroToCoherentKZero Z).comp (supportedCoherentKZeroMap h) =
      supportedCoherentKZeroToCoherentKZero Z' :=
  KZero.hom_ext fun A => by
    rw [AddMonoidHom.comp_apply, supportedCoherentKZeroMap_mk,
      supportedCoherentKZeroToCoherentKZero_mk, supportedCoherentKZeroToCoherentKZero_mk]

/-- The homomorphism `K'₀(X) ⟶ K₀(Coh_X(X))` reading a coherent module as supported in `X`. -/
def coherentKZeroToSupportedCoherentKZeroTop :
    CoherentKZero X →+ supportedCoherentKZero (⊤ : Closeds X) :=
  KZero.lift (fun F => KZero.mk _ ⟨F, fun _ _ => trivial⟩) fun _ hS =>
    supportedCoherentKZero_mk_add _ _ _ _ _ _
      ((Stacks.SheafOfModules.coherentModules X.ringCatSheaf).shortExact_map_ι hS)

/-- For `Z = X` the comparison `K₀(Coh_X(X)) ⟶ K'₀(X)` is an isomorphism: every coherent module is
supported in `X`. -/
def supportedCoherentKZeroTopEquiv : supportedCoherentKZero (⊤ : Closeds X) ≃+ CoherentKZero X where
  toFun := supportedCoherentKZeroToCoherentKZero ⊤
  invFun := coherentKZeroToSupportedCoherentKZeroTop (X := X)
  left_inv a := by
    have h : (coherentKZeroToSupportedCoherentKZeroTop (X := X)).comp
        (supportedCoherentKZeroToCoherentKZero ⊤) = AddMonoidHom.id _ :=
      KZero.hom_ext fun A => by
        rw [AddMonoidHom.comp_apply, supportedCoherentKZeroToCoherentKZero_mk]
        exact KZero.lift_mk _ _ _
    exact DFunLike.congr_fun h a
  right_inv b := by
    have h : (supportedCoherentKZeroToCoherentKZero ⊤).comp
        (coherentKZeroToSupportedCoherentKZeroTop (X := X)) = AddMonoidHom.id _ :=
      KZero.hom_ext fun F => by
        rw [AddMonoidHom.comp_apply, coherentKZeroToSupportedCoherentKZeroTop, KZero.lift_mk,
          supportedCoherentKZeroToCoherentKZero_mk]
        rfl
    exact DFunLike.congr_fun h b
  map_add' := map_add _

/-- The isomorphism `K₀(Coh_X(X)) ≃ K'₀(X)` is the comparison with `K'₀(X)`. -/
@[simp]
theorem supportedCoherentKZeroTopEquiv_apply (a : supportedCoherentKZero (⊤ : Closeds X)) :
    supportedCoherentKZeroTopEquiv a = supportedCoherentKZeroToCoherentKZero ⊤ a :=
  rfl

/-- The inverse of `K₀(Coh_X(X)) ≃ K'₀(X)` reads a coherent module as supported in `X`. -/
@[simp]
theorem supportedCoherentKZeroTopEquiv_symm_mk
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) :
    supportedCoherentKZeroTopEquiv.symm (KZero.mk _ F) = KZero.mk _ ⟨F, fun _ _ => trivial⟩ :=
  show coherentKZeroToSupportedCoherentKZeroTop (KZero.mk _ F) = _ from KZero.lift_mk _ _ _

/-- `K₀(Coh_∅(X)) = 0`: a coherent module supported in the empty set is zero. -/
theorem subsingleton_supportedCoherentKZero_bot :
    Subsingleton (supportedCoherentKZero (⊥ : Closeds X)) := by
  have h : (0 : supportedCoherentKZero (⊥ : Closeds X) →+ _) = AddMonoidHom.id _ :=
    KZero.hom_ext fun A => (supportedCoherentKZero_mk_eq_zero A
      (Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty _
        (Set.subset_empty_iff.1 A.property))).symm
  exact ⟨fun a b => by
    rw [← AddMonoidHom.id_apply _ a, ← AddMonoidHom.id_apply _ b, ← h]
    rfl⟩

/-! ### The functor `Z ↦ 𝐐 ⊗ K₀(Coh_Z(X))` -/

variable (X) in
/-- The functor `Z ↦ 𝐐 ⊗ K₀(Coh_Z(X))` on the closed subsets of `X`, with the maps induced by
the inclusions `Coh_{Z'}(X) ⊆ Coh_Z(X)`. -/
def supportedCoherentKZeroRat : Closeds X ⥤ ModuleCat.{u + 1} ℚ where
  obj Z := ModuleCat.of ℚ (ℚ ⊗[ℤ] supportedCoherentKZero Z)
  map f := ModuleCat.ofHom ((supportedCoherentKZeroMap (leOfHom f)).toIntLinearMap.baseChange ℚ)
  map_id Z := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul q a =>
      simp only [ModuleCat.hom_ofHom, ModuleCat.hom_id, LinearMap.id_apply,
        LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap, supportedCoherentKZeroMap_refl,
        AddMonoidHom.id_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  map_comp f g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul q a =>
      simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, LinearMap.comp_apply,
        LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap]
      rw [← supportedCoherentKZeroMap_comp (leOfHom f) (leOfHom g), AddMonoidHom.comp_apply]
    | add x y hx hy => simp only [map_add, hx, hy]

/-- The map of `Z ↦ 𝐐 ⊗ K₀(Coh_Z(X))` along `Z' ⊆ Z` on a pure tensor. -/
@[simp]
theorem supportedCoherentKZeroRat_map_tmul {Z' Z : Closeds X} (f : Z' ⟶ Z) (q : ℚ)
    (a : supportedCoherentKZero Z') :
    ((supportedCoherentKZeroRat X).map f).hom (q ⊗ₜ[ℤ] a) =
      q ⊗ₜ[ℤ] supportedCoherentKZeroMap (leOfHom f) a :=
  rfl

/-- `𝐐 ⊗ K₀(Coh_∅(X)) = 0`. -/
theorem subsingleton_supportedCoherentKZeroRat_bot :
    Subsingleton ((supportedCoherentKZeroRat X).obj ⊥) := by
  have := subsingleton_supportedCoherentKZero_bot (X := X)
  have h : ∀ x : ℚ ⊗[ℤ] supportedCoherentKZero (⊥ : Closeds X), x = 0 := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul q a => rw [Subsingleton.elim a 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y => (h x).trans (h y).symm⟩

/-- The comparison `𝐐 ⊗ K₀(Coh_Z(X)) ⟶ 𝐐 ⊗ K'₀(X)` induced by the inclusion `Coh_Z(X) ⊆ Coh(X)`. -/
def supportedCoherentKZeroRatToCoherent (Z : Closeds X) :
    (supportedCoherentKZeroRat X).obj Z →ₗ[ℚ] ℚ ⊗[ℤ] CoherentKZero X :=
  (supportedCoherentKZeroToCoherentKZero Z).toIntLinearMap.baseChange ℚ

/-- The comparison with `𝐐 ⊗ K'₀(X)` on a pure tensor. -/
@[simp]
theorem supportedCoherentKZeroRatToCoherent_tmul (Z : Closeds X) (q : ℚ)
    (a : supportedCoherentKZero Z) :
    supportedCoherentKZeroRatToCoherent Z (q ⊗ₜ[ℤ] a) =
      q ⊗ₜ[ℤ] supportedCoherentKZeroToCoherentKZero Z a :=
  rfl

/-- The comparison with `𝐐 ⊗ K'₀(X)` is compatible with the maps of the functor. -/
theorem supportedCoherentKZeroRatToCoherent_map {Z' Z : Closeds X} (f : Z' ⟶ Z)
    (x : (supportedCoherentKZeroRat X).obj Z') :
    supportedCoherentKZeroRatToCoherent Z (((supportedCoherentKZeroRat X).map f).hom x) =
      supportedCoherentKZeroRatToCoherent Z' x := by
  induction x using TensorProduct.induction_on with
  | zero =>
    exact (congrArg (supportedCoherentKZeroRatToCoherent Z) (map_zero _)).trans
      ((map_zero _).trans (map_zero _).symm)
  | tmul q a =>
    exact congrArg (q ⊗ₜ[ℤ] ·)
      (DFunLike.congr_fun (supportedCoherentKZeroToCoherentKZero_comp_map (leOfHom f)) a)
  | add x y hx hy =>
    exact ((congrArg (supportedCoherentKZeroRatToCoherent Z) (map_add _ _ _)).trans
      (map_add _ _ _)).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

/-- For `Z = X` the comparison `𝐐 ⊗ K₀(Coh_X(X)) ⟶ 𝐐 ⊗ K'₀(X)` is bijective. -/
theorem bijective_supportedCoherentKZeroRatToCoherent_top :
    Function.Bijective (supportedCoherentKZeroRatToCoherent (⊤ : Closeds X)) :=
  (LinearEquiv.baseChange ℤ ℚ _ _
    (supportedCoherentKZeroTopEquiv (X := X)).toIntLinearEquiv).bijective

/-- The comparison `K'₀(X) ⟶ 𝐐 ⊗ K₀(Coh_X(X))`, `b ↦ 1 ⊗ b`. -/
def coherentKZeroToSupportedCoherentKZeroRatTop :
    CoherentKZero X →+ (supportedCoherentKZeroRat X).obj ⊤ :=
  (TensorProduct.mk ℤ ℚ (supportedCoherentKZero (⊤ : Closeds X)) 1).toAddMonoidHom.comp
    (supportedCoherentKZeroTopEquiv (X := X)).symm.toAddMonoidHom

/-- Following `b ↦ 1 ⊗ b` by the comparison with `𝐐 ⊗ K'₀(X)` is `b ↦ 1 ⊗ b`. -/
theorem supportedCoherentKZeroRatToCoherent_coherentKZeroToSupportedCoherentKZeroRatTop
    (b : CoherentKZero X) :
    supportedCoherentKZeroRatToCoherent ⊤ (coherentKZeroToSupportedCoherentKZeroRatTop b) =
      (1 : ℚ) ⊗ₜ[ℤ] b := by
  change (1 : ℚ) ⊗ₜ[ℤ] supportedCoherentKZeroTopEquiv (supportedCoherentKZeroTopEquiv.symm b) = _
  rw [AddEquiv.apply_symm_apply]

end KGroup

/-! ### The `k`-cycle of an element of `K₀(Coh_Z(X))` -/

section Cycle

variable (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]

/-- If every point of `T` has relative dimension at most `k`, a coherent module supported in `T`
has support of delta-dimension at most `k`. -/
theorem coherentSupportedIn_le_coherentModulesDimLE {T : Set X} {k : ℤ}
    (hT : ∀ z ∈ T, relativeDimension C.dimensionFunction f z ≤ k) :
    coherentSupportedIn T ≤ coherentModulesDimLE C f k := fun F hF =>
  have : _root_.SheafOfModules.IsCoherent F.obj :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent F.property
  schemeDeltaDimension_reducedSupport_le C f F.obj fun x hx => hT x (hF hx)

/-- The closure of a point of a closed subset `Z` lies in `Z`. -/
private theorem closure_singleton_subset_of_mem {Z : Closeds X} {ξ : X} (hξ : ξ ∈ Z) :
    closure {ξ} ⊆ (Z : Set X) :=
  closure_minimal (Set.singleton_subset_iff.2 hξ) Z.isClosed

/-- For a nonzero quasi-coherent ideal sheaf `I ⊆ 𝒪_W`, the point `i(η)` is in the support of
`i_*I`. -/
private theorem mem_supp_pushforward_of_not_isZero {W : Scheme.{u}} (i : W ⟶ X)
    [IsClosedImmersion i] [IsIntegral W] (I : (SheafOfModules.unit W.ringCatSheaf).Submodule)
    (hI : I.toSheafOfModules.IsQuasicoherent) (hIz : ¬IsZero I.toSheafOfModules) :
    i (genericPoint W) ∈
      SheafOfModules.supp ((Scheme.Modules.pushforward i).obj I.toSheafOfModules) :=
  (mem_supp_pushforward_iff i _ (genericPoint W)).mpr
    (Stacks.AlgebraicGeometry.Tag01YHFullSupport.genericPoint_mem_supp_of_not_isZero I hI hIz)

variable [IsLocallyNoetherian X]

/-- **The `k`-cycle on `K₀(Coh_Z(X))`.** If every point of `Z` has relative dimension at most `k`,
every object of `Coh_Z(X)` is an object of `Coh_{≤k}(X)`, and its `k`-cycle `[F]_k`
(`Stacks.Chow.dimensionLayerCycle`, Stacks 02QZ) is additive along short exact sequences. -/
def supportedCoherentKZeroCycle (Z : Closeds X) (k : ℤ)
    (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k) :
    supportedCoherentKZero Z →+ CycleGroup C f k :=
  KZero.lift (fun A => dimensionLayerCycle C f k
      ⟨A.obj, coherentSupportedIn_le_coherentModulesDimLE C f (T := (Z : Set X)) hZ _
        A.property⟩) fun _ hS =>
    dimensionLayerCycle_add_of_shortExact C f k _ _ _ _ _ _
      ((Stacks.SheafOfModules.coherentModules X.ringCatSheaf).shortExact_map_ι
        ((coherentSupportedIn (Z : Set X)).shortExact_map_ι hS))

/-- The `k`-cycle of the class of an object of `Coh_Z(X)` is its cycle `[F]_k`. -/
@[simp]
theorem supportedCoherentKZeroCycle_mk (Z : Closeds X) (k : ℤ)
    (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k)
    (A : (coherentSupportedIn (Z : Set X)).FullSubcategory) :
    supportedCoherentKZeroCycle C f Z k hZ (KZero.mk _ A) =
      dimensionLayerCycle C f k ⟨A.obj, coherentSupportedIn_le_coherentModulesDimLE C f
        (T := (Z : Set X)) hZ _ A.property⟩ :=
  KZero.lift_mk _ _ _

/-- At a point of relative dimension `k`, the coefficient of the `k`-cycle of the class of an
object of `Coh_Z(X)` is the length of its stalk there (Stacks 02QX). -/
theorem supportedCoherentKZeroCycle_mk_apply_of_eq (Z : Closeds X) (k : ℤ)
    (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k)
    (A : (coherentSupportedIn (Z : Set X)).FullSubcategory) {x : X}
    (hx : relativeDimension C.dimensionFunction f x = k) :
    (supportedCoherentKZeroCycle C f Z k hZ (KZero.mk _ A)).1 x =
      sheafMultiplicity A.obj.obj x := by
  rw [supportedCoherentKZeroCycle_mk]
  exact dimensionLayerCycle_apply_of_relativeDimension_eq C f k _ hx

/-- The `k`-cycle vanishes on classes coming from a closed subset of `Z` on which the relative
dimension is at most `k - 1`. -/
theorem supportedCoherentKZeroCycle_comp_map_eq_zero {Z' Z : Closeds X} (h : Z' ≤ Z) (k : ℤ)
    (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k)
    (hZ' : ∀ z ∈ Z', relativeDimension C.dimensionFunction f z ≤ k - 1) :
    (supportedCoherentKZeroCycle C f Z k hZ).comp (supportedCoherentKZeroMap h) = 0 :=
  KZero.hom_ext fun A => by
    rw [AddMonoidHom.comp_apply, supportedCoherentKZeroMap_mk, supportedCoherentKZeroCycle_mk,
      AddMonoidHom.zero_apply]
    exact dimensionLayerCycle_eq_zero_of_dimensionLayerClass C f k
      ⟨⟨A.obj, coherentSupportedIn_le_coherentModulesDimLE C f (T := (Z : Set X)) hZ _
          (A.property.trans h)⟩,
        coherentSupportedIn_le_coherentModulesDimLE C f (T := (Z' : Set X)) hZ' _ A.property⟩

/-- The `k`-cycle on `𝐐 ⊗ K₀(Coh_Z(X))`, with values in `Z_k(X) ⊗ 𝐐`, when every point of `Z` has
relative dimension at most `k`. -/
def supportedCoherentKZeroRatCycle (Z : Closeds X) (k : ℤ)
    (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k) :
    (supportedCoherentKZeroRat X).obj Z →ₗ[ℚ] ℚ ⊗[ℤ] CycleGroup C f k :=
  (supportedCoherentKZeroCycle C f Z k hZ).toIntLinearMap.baseChange ℚ

/-- The `k`-cycle on `𝐐 ⊗ K₀(Coh_Z(X))` on a pure tensor. -/
@[simp]
theorem supportedCoherentKZeroRatCycle_tmul (Z : Closeds X) (k : ℤ)
    (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k) (q : ℚ)
    (a : supportedCoherentKZero Z) :
    supportedCoherentKZeroRatCycle C f Z k hZ (q ⊗ₜ[ℤ] a) =
      q ⊗ₜ[ℤ] supportedCoherentKZeroCycle C f Z k hZ a :=
  rfl

/-! ### Classes from closed subsets of smaller dimension -/

/-- The subgroup of `K₀(Coh_Z(X))` of the classes coming from `K₀(Coh_{Z'}(X))` for the closed
subsets `Z' ⊆ Z` on which the relative dimension is at most `c`. -/
def supportedCoherentKZeroLowerPart (Z : Closeds X) (c : ℤ) :
    AddSubgroup (supportedCoherentKZero Z) :=
  ⨆ Z' : {Z' : Closeds X // Z' ≤ Z ∧ ∀ z ∈ Z', relativeDimension C.dimensionFunction f z ≤ c},
    (supportedCoherentKZeroMap Z'.2.1).range

omit [LocallyOfFiniteType f] in
/-- An element of `Stacks.Chow.supportedCoherentKZeroLowerPart` comes from a single closed subset:
the classes from `Z₁` and from `Z₂` both come from `Z₁ ∪ Z₂`. -/
theorem mem_supportedCoherentKZeroLowerPart_iff {Z : Closeds X} {c : ℤ}
    {a : supportedCoherentKZero Z} :
    a ∈ supportedCoherentKZeroLowerPart C f Z c ↔
      ∃ (Z' : Closeds X) (h : Z' ≤ Z),
        (∀ z ∈ Z', relativeDimension C.dimensionFunction f z ≤ c) ∧
          a ∈ (supportedCoherentKZeroMap h).range := by
  constructor
  · intro ha
    have : Nonempty {Z' : Closeds X // Z' ≤ Z ∧
        ∀ z ∈ Z', relativeDimension C.dimensionFunction f z ≤ c} :=
      ⟨⟨⊥, bot_le, fun z hz => (Set.notMem_empty z hz).elim⟩⟩
    have hdir : Directed (· ≤ ·) fun Z' : {Z' : Closeds X // Z' ≤ Z ∧
        ∀ z ∈ Z', relativeDimension C.dimensionFunction f z ≤ c} =>
          (supportedCoherentKZeroMap Z'.2.1).range := by
      rintro ⟨Z₁, h₁, d₁⟩ ⟨Z₂, h₂, d₂⟩
      refine ⟨⟨Z₁ ⊔ Z₂, sup_le h₁ h₂, fun z hz => ?_⟩, ?_, ?_⟩
      · have hz' : z ∈ (Z₁ : Set X) ∪ Z₂ := by rwa [← Closeds.coe_sup]
        rcases hz' with hz' | hz'
        exacts [d₁ z hz', d₂ z hz']
      · dsimp only
        rw [← supportedCoherentKZeroMap_comp (le_sup_left : Z₁ ≤ Z₁ ⊔ Z₂) (sup_le h₁ h₂)]
        rintro _ ⟨x, rfl⟩
        exact ⟨_, rfl⟩
      · dsimp only
        rw [← supportedCoherentKZeroMap_comp (le_sup_right : Z₂ ≤ Z₁ ⊔ Z₂) (sup_le h₁ h₂)]
        rintro _ ⟨x, rfl⟩
        exact ⟨_, rfl⟩
    obtain ⟨⟨Z', h, d⟩, hmem⟩ := (AddSubgroup.mem_iSup_of_directed hdir).1 ha
    exact ⟨Z', h, d, hmem⟩
  · rintro ⟨Z', h, d, hmem⟩
    exact AddSubgroup.mem_iSup_of_mem
      (⟨Z', h, d⟩ : {Z' : Closeds X // Z' ≤ Z ∧
        ∀ z ∈ Z', relativeDimension C.dimensionFunction f z ≤ c}) hmem

/-- The `k`-cycle kills the classes coming from closed subsets of `Z` on which the relative
dimension is at most `k - 1`. -/
theorem supportedCoherentKZeroLowerPart_le_ker (Z : Closeds X) (k : ℤ)
    (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k) :
    supportedCoherentKZeroLowerPart C f Z (k - 1) ≤ (supportedCoherentKZeroCycle C f Z k hZ).ker :=
  iSup_le fun Z' => by
    rintro _ ⟨b, rfl⟩
    exact DFunLike.congr_fun (supportedCoherentKZeroCycle_comp_map_eq_zero C f Z'.2.1 k hZ Z'.2.2) b

/-! ### The class of the structure sheaf of a point closure -/

/-- The class in `K₀(Coh_Z(X))` of the structure sheaf `𝒪_{\overline{ξ}}` of the integral closed
subscheme with generic point `ξ ∈ Z`. -/
def supportedCoherentKZeroPoint (Z : Closeds X) {ξ : X} (hξ : ξ ∈ Z) : supportedCoherentKZero Z :=
  KZero.mk _ ⟨⟨integralComponentStructureSheaf ξ,
      AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent inferInstance⟩,
    (supp_integralComponentStructureSheaf ξ).trans_subset
      (closure_minimal (Set.singleton_subset_iff.2 hξ) Z.isClosed)⟩

/-- **Stacks 02QY** in `K₀(Coh_Z(X))`. For `ξ ∈ Z` of relative dimension `k`, the `k`-cycle of
the class of `𝒪_{\overline{ξ}}` is the prime cycle `[\overline{ξ}]`. -/
theorem supportedCoherentKZeroCycle_point_apply (Z : Closeds X) (k : ℤ)
    (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k) {ξ : X} (hξ : ξ ∈ Z)
    (hξk : relativeDimension C.dimensionFunction f ξ = k) (y : X) :
    (supportedCoherentKZeroCycle C f Z k hZ (supportedCoherentKZeroPoint Z hξ)).1 y =
      singlePointCoeff ξ y := by
  have hsupp : SheafOfModules.supp
      (cycleStructureSheafDimLE C f k (pointCoefficients C f k ξ hξk)).obj.obj ⊆ (Z : Set X) :=
    (supp_subset_of_mono (cycleStructureSheafPointIso ξ).hom).trans
      ((supp_integralComponentStructureSheaf ξ).trans_subset
        (closure_minimal (Set.singleton_subset_iff.2 hξ) Z.isClosed))
  have hmk : supportedCoherentKZeroPoint Z hξ =
      KZero.mk _ (⟨(cycleStructureSheafDimLE C f k (pointCoefficients C f k ξ hξk)).obj, hsupp⟩ :
        (coherentSupportedIn (Z : Set X)).FullSubcategory) :=
    supportedCoherentKZero_mk_eq_of_iso _ _ (cycleStructureSheafPointIso ξ).symm
  rw [hmk, supportedCoherentKZeroCycle_mk]
  exact (dimensionLayerCycle_cycleStructureSheafDimLE_apply C f k
    (pointCoefficients C f k ξ hξk) y).trans rfl

/-! ### Dévissage in `K₀(Coh_Z(X))` -/

omit [LocallyOfFiniteType f] in
/-- The class of a coherent module supported in a closed subset `Z' ⊆ Z` on which the relative
dimension is at most `c` lies in `Stacks.Chow.supportedCoherentKZeroLowerPart`. -/
theorem mk_mem_supportedCoherentKZeroLowerPart {Z : Closeds X} (Z' : Closeds X) {c : ℤ}
    (hZ' : Z' ≤ Z) (hd : ∀ z ∈ Z', relativeDimension C.dimensionFunction f z ≤ c)
    (M : X.Modules) (hc : _root_.SheafOfModules.IsCoherent M)
    (hs : SheafOfModules.supp M ⊆ (Z : Set X)) (hs' : SheafOfModules.supp M ⊆ (Z' : Set X)) :
    KZero.mk _ (⟨⟨M, AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent hc⟩, hs⟩ :
      (coherentSupportedIn (Z : Set X)).FullSubcategory) ∈
        supportedCoherentKZeroLowerPart C f Z c :=
  (mem_supportedCoherentKZeroLowerPart_iff C f).2 ⟨Z', hZ', hd,
    KZero.mk _ (⟨⟨M, AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent hc⟩, hs'⟩ :
      (coherentSupportedIn (Z' : Set X)).FullSubcategory),
    supportedCoherentKZeroMap_mk _ _⟩

omit [IsLocallyNoetherian X] in
/-- For a morphism `i : W ⟶ X` and an ideal sheaf `I ⊆ 𝒪_W`, the map `i_*I ⟶ i_*𝒪_W` is a
monomorphism. -/
private theorem mono_pushforward_map_ι {W : Scheme.{u}} (i : W ⟶ X)
    (I : (SheafOfModules.unit W.ringCatSheaf).Submodule) :
    Mono ((Scheme.Modules.pushforward i).map I.ι) :=
  have : Mono (C := W.Modules) I.ι :=
    ⟨fun g h hcomp =>
      (_root_.SheafOfModules.Submodule.instMonoι I).right_cancellation g h hcomp⟩
  CategoryTheory.preserves_mono_of_preservesLimit (Scheme.Modules.pushforward i) I.ι

omit [IsLocallyNoetherian X] in
/-- For a closed immersion `i : W ⟶ X` of an integral scheme with generic point `η`, the support
of `i_*𝒪_W` is the closure of `i(η)`. -/
private theorem supp_pushforward_unitModule {W : Scheme.{u}} (i : W ⟶ X) [IsClosedImmersion i]
    [IsIntegral W] :
    SheafOfModules.supp ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule W)) =
      closure {i (genericPoint W)} := by
  rw [supp_pushforwardStructureSheaf, range_eq_closure_singleton i]

omit [IsLocallyNoetherian X] in
/-- For a closed immersion `i : W ⟶ X` of an integral scheme with generic point `η` and an ideal
sheaf `I ⊆ 𝒪_W`, the cokernel of `i_*I ⟶ i_*𝒪_W` is supported in the closure of `i(η)`. -/
theorem supp_cokernel_pushforward_ι_subset {W : Scheme.{u}} (i : W ⟶ X) [IsClosedImmersion i]
    [IsIntegral W] (I : (SheafOfModules.unit W.ringCatSheaf).Submodule) :
    SheafOfModules.supp (cokernel ((Scheme.Modules.pushforward i).map I.ι)) ⊆
      closure {i (genericPoint W)} := by
  have := mono_pushforward_map_ι i I
  have hepi : Epi (cokernel.π ((Scheme.Modules.pushforward i).map I.ι)) :=
    (shortExact_mk_cokernel ((Scheme.Modules.pushforward i).map I.ι)).epi_g
  exact (@supp_subset_of_epi X _ _ (cokernel.π ((Scheme.Modules.pushforward i).map I.ι))
    hepi).trans (supp_pushforward_unitModule i).le

/-- The cokernel of `i_*I ⟶ i_*𝒪_W` is coherent as soon as `i_*I` is. -/
private theorem isCoherent_cokernel_pushforward_ι {W : Scheme.{u}} (i : W ⟶ X)
    [IsClosedImmersion i] [IsIntegral W] (I : (SheafOfModules.unit W.ringCatSheaf).Submodule)
    (hc : _root_.SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)) :
    _root_.SheafOfModules.IsCoherent (cokernel ((Scheme.Modules.pushforward i).map I.ι)) :=
  Stacks.AlgebraicGeometry.ProperMapping.isCoherent_cokernel_modules hc inferInstance _

/-- The class in `K₀(Coh_Z(X))` of a coherent module supported in `Z`. -/
private abbrev supportedCoherentMk {Z : Closeds X} (M : X.Modules)
    (hc : _root_.SheafOfModules.IsCoherent M) (hs : SheafOfModules.supp M ⊆ (Z : Set X)) :
    supportedCoherentKZero Z :=
  KZero.mk _ (⟨⟨M, AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent hc⟩, hs⟩ :
    (coherentSupportedIn (Z : Set X)).FullSubcategory)

/-- For `i : W ⟶ X` and `I` as in `Stacks.Chow.supp_cokernel_pushforward_ι_subset`, with `i_*I`
supported in `Z` and `ξ = i(η) ∈ Z`, in `K₀(Coh_Z(X))` the class of `𝒪_{\overline{ξ}}` is the sum
of the classes of `i_*I` and of the cokernel of `i_*I ⟶ i_*𝒪_W`. -/
private theorem point_eq_mk_pushforward_add_mk_cokernel {Z : Closeds X} {W : Scheme.{u}}
    (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
    (I : (SheafOfModules.unit W.ringCatSheaf).Submodule)
    (hc : _root_.SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward i).obj I.toSheafOfModules))
    (hs : SheafOfModules.supp ((Scheme.Modules.pushforward i).obj I.toSheafOfModules) ⊆
      (Z : Set X)) (hξZ : i (genericPoint W) ∈ Z) :
    supportedCoherentKZeroPoint Z hξZ =
      supportedCoherentMk _ hc hs +
        supportedCoherentMk (cokernel ((Scheme.Modules.pushforward i).map I.ι))
          (isCoherent_cokernel_pushforward_ι i I hc)
          ((supp_cokernel_pushforward_ι_subset i I).trans
            (closure_singleton_subset_of_mem hξZ)) := by
  have := mono_pushforward_map_ι i I
  have hOZ : SheafOfModules.supp
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule W)) ⊆ (Z : Set X) :=
    (supp_pushforward_unitModule i).le.trans (closure_singleton_subset_of_mem hξZ)
  have hpt : supportedCoherentMk ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule W))
      inferInstance hOZ = supportedCoherentKZeroPoint Z hξZ :=
    supportedCoherentKZero_mk_eq_of_iso _ _ (pushforwardUnitIsoIntegralComponent i)
  rw [← hpt]
  exact supportedCoherentKZero_mk_add _ _ _ _ _ _
    (shortExact_mk_cokernel ((Scheme.Modules.pushforward i).map I.ι))

/-- For `i : W ⟶ X` and `I` as in `Stacks.Chow.supp_cokernel_pushforward_ι_subset`, with `i_*I`
supported in `Z` and `ξ = i(η) ∈ Z` of relative dimension `k`, the multiplicities at `ξ` of `i_*I`
and of the cokernel of `i_*I ⟶ i_*𝒪_W` add up to `1`. -/
theorem one_eq_sheafMultiplicity_pushforward_add_cokernel (Z : Closeds X) (k : ℤ)
    (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k) {W : Scheme.{u}}
    (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
    (I : (SheafOfModules.unit W.ringCatSheaf).Submodule)
    (hc : _root_.SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward i).obj I.toSheafOfModules))
    (hs : SheafOfModules.supp ((Scheme.Modules.pushforward i).obj I.toSheafOfModules) ⊆
      (Z : Set X)) (hξZ : i (genericPoint W) ∈ Z)
    (heq : relativeDimension C.dimensionFunction f (i (genericPoint W)) = k) :
    (1 : ℤ) = sheafMultiplicity ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)
        (i (genericPoint W)) +
      sheafMultiplicity (cokernel ((Scheme.Modules.pushforward i).map I.ι))
        (i (genericPoint W)) := by
  have hQc := isCoherent_cokernel_pushforward_ι i I hc
  have hQZ := (supp_cokernel_pushforward_ι_subset i I).trans
    (closure_singleton_subset_of_mem hξZ)
  have hsum : (supportedCoherentKZeroCycle C f Z k hZ (supportedCoherentKZeroPoint Z hξZ)).1
        (i (genericPoint W)) =
      (supportedCoherentKZeroCycle C f Z k hZ (supportedCoherentMk _ hc hs)).1
          (i (genericPoint W)) +
        (supportedCoherentKZeroCycle C f Z k hZ (supportedCoherentMk _ hQc hQZ)).1
          (i (genericPoint W)) := by
    rw [point_eq_mk_pushforward_add_mk_cokernel i I hc hs hξZ, map_add]
    rfl
  rwa [supportedCoherentKZeroCycle_point_apply C f Z k hZ hξZ heq, singlePointCoeff_self,
    Nat.cast_one, supportedCoherentKZeroCycle_mk_apply_of_eq C f Z k hZ _ heq,
    supportedCoherentKZeroCycle_mk_apply_of_eq C f Z k hZ _ heq] at hsum

/-- For `i : W ⟶ X` and `I ≠ 0` as in `Stacks.Chow.supp_cokernel_pushforward_ι_subset`, with
`i_*I` supported in `Z`, on which `δ ≤ k`, and `δ(i(η)) = k`, the relative dimension is at most
`k - 1` on the support of the cokernel of `i_*I ⟶ i_*𝒪_W`. -/
theorem relativeDimension_le_of_mem_supp_cokernel_pushforward_ι (Z : Closeds X) (k : ℤ)
    (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k) {W : Scheme.{u}}
    (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
    (I : (SheafOfModules.unit W.ringCatSheaf).Submodule)
    (hI : I.toSheafOfModules.IsQuasicoherent) (hIz : ¬IsZero I.toSheafOfModules)
    (hc : _root_.SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward i).obj I.toSheafOfModules))
    (hs : SheafOfModules.supp ((Scheme.Modules.pushforward i).obj I.toSheafOfModules) ⊆
      (Z : Set X))
    (heq : relativeDimension C.dimensionFunction f (i (genericPoint W)) = k) :
    ∀ y ∈ SheafOfModules.supp (cokernel ((Scheme.Modules.pushforward i).map I.ι)),
      relativeDimension C.dimensionFunction f y ≤ k - 1 := by
  have hξM := mem_supp_pushforward_of_not_isZero i I hI hIz
  have hξZ : i (genericPoint W) ∈ Z := hs hξM
  have hQc := isCoherent_cokernel_pushforward_ι i I hc
  have hQZ := (supp_cokernel_pushforward_ι_subset i I).trans
    (closure_singleton_subset_of_mem hξZ)
  have hMpos := sheafMultiplicity_pos_of_mem_supp
    ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)
    (isFiniteLength_stalk_of_forall_relativeDimension_le C f k _ hc
      (fun y hy => hZ y (hs hy)) heq) hξM
  have hξQ : i (genericPoint W) ∉
      SheafOfModules.supp (cokernel ((Scheme.Modules.pushforward i).map I.ι)) := by
    intro hmem
    have hQpos := sheafMultiplicity_pos_of_mem_supp
      (cokernel ((Scheme.Modules.pushforward i).map I.ι))
      (isFiniteLength_stalk_of_forall_relativeDimension_le C f k _ hQc
        (fun y hy => hZ y (hQZ hy)) heq) hmem
    have h1 := one_eq_sheafMultiplicity_pushforward_add_cokernel C f Z k hZ i I hc hs hξZ heq
    omega
  intro y hy
  have := relativeDimension_lt_of_mem_closure_of_ne C f
    (supp_cokernel_pushforward_ι_subset i I hy) fun h => hξQ (h ▸ hy)
  omega

/-- The dévissage step of `Stacks.Chow.mem_span_supportedCoherentKZeroPoint_sup_lowerPart` for
`i_*I` with `I ≠ 0` when `ξ = i(η)` has relative dimension `k`: `[i_*I] = [𝒪_{\overline{ξ}}] - [Q]`
for the cokernel `Q` of `i_*I ⟶ i_*𝒪_W`, supported where `δ ≤ k - 1`. -/
theorem mk_pushforward_mem_span_supportedCoherentKZeroPoint_sup_lowerPart_of_eq (Z : Closeds X)
    (k : ℤ) (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k) {W : Scheme.{u}}
    (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
    (I : (SheafOfModules.unit W.ringCatSheaf).Submodule)
    (hI : I.toSheafOfModules.IsQuasicoherent) (hIz : ¬IsZero I.toSheafOfModules)
    (hc : _root_.SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward i).obj I.toSheafOfModules))
    (hs : SheafOfModules.supp ((Scheme.Modules.pushforward i).obj I.toSheafOfModules) ⊆
      (Z : Set X))
    (heq : relativeDimension C.dimensionFunction f (i (genericPoint W)) = k) :
    KZero.mk _ (⟨⟨(Scheme.Modules.pushforward i).obj I.toSheafOfModules,
        AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent hc⟩, hs⟩ :
          (coherentSupportedIn (Z : Set X)).FullSubcategory) ∈
      (Submodule.span ℤ (Set.range fun ξ : {ξ : X // ξ ∈ Z ∧
        relativeDimension C.dimensionFunction f ξ = k} =>
          supportedCoherentKZeroPoint Z ξ.2.1)).toAddSubgroup ⊔
        supportedCoherentKZeroLowerPart C f Z (k - 1) := by
  change supportedCoherentMk _ hc hs ∈ _
  have hξZ : i (genericPoint W) ∈ Z := hs (mem_supp_pushforward_of_not_isZero i I hI hIz)
  have hQc := isCoherent_cokernel_pushforward_ι i I hc
  have hQZ := (supp_cokernel_pushforward_ι_subset i I).trans
    (closure_singleton_subset_of_mem hξZ)
  rw [eq_sub_of_add_eq (point_eq_mk_pushforward_add_mk_cokernel i I hc hs hξZ).symm]
  refine sub_mem (AddSubgroup.mem_sup_left (Submodule.subset_span
    ⟨⟨i (genericPoint W), hξZ, heq⟩, rfl⟩)) (AddSubgroup.mem_sup_right ?_)
  exact mk_mem_supportedCoherentKZeroLowerPart C f
    ⟨_, Stacks.AlgebraicGeometry.DevissageNoetherian.isClosed_supp_of_isCoherent _ hQc⟩ hQZ
    (relativeDimension_le_of_mem_supp_cokernel_pushforward_ι C f Z k hZ i I hI hIz hc hs heq)
    _ hQc hQZ subset_rfl

/-- The dévissage step of `Stacks.Chow.mem_span_supportedCoherentKZeroPoint_sup_lowerPart` for
`i_*I`, where `i : W ⟶ X` is a closed immersion of an integral scheme into `X` and `I ⊆ 𝒪_W` a
quasi-coherent ideal sheaf. -/
theorem mk_pushforward_mem_span_supportedCoherentKZeroPoint_sup_lowerPart (Z : Closeds X)
    (k : ℤ) (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k) {W : Scheme.{u}}
    (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
    (I : (SheafOfModules.unit W.ringCatSheaf).Submodule)
    (hI : I.toSheafOfModules.IsQuasicoherent)
    (hc : _root_.SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward i).obj I.toSheafOfModules))
    (hs : SheafOfModules.supp ((Scheme.Modules.pushforward i).obj I.toSheafOfModules) ⊆
      (Z : Set X)) :
    KZero.mk _ (⟨⟨(Scheme.Modules.pushforward i).obj I.toSheafOfModules,
        AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent hc⟩, hs⟩ :
          (coherentSupportedIn (Z : Set X)).FullSubcategory) ∈
      (Submodule.span ℤ (Set.range fun ξ : {ξ : X // ξ ∈ Z ∧
        relativeDimension C.dimensionFunction f ξ = k} =>
          supportedCoherentKZeroPoint Z ξ.2.1)).toAddSubgroup ⊔
        supportedCoherentKZeroLowerPart C f Z (k - 1) := by
  change supportedCoherentMk _ hc hs ∈ _
  by_cases hIz : IsZero I.toSheafOfModules
  · rw [show supportedCoherentMk _ hc hs = 0 from supportedCoherentKZero_mk_eq_zero _
      (Functor.map_isZero (Scheme.Modules.pushforward i) hIz)]
    exact zero_mem _
  have hξZ : i (genericPoint W) ∈ Z := hs (mem_supp_pushforward_of_not_isZero i I hI hIz)
  rcases (hZ _ hξZ).lt_or_eq with hlt | heq
  · have := mono_pushforward_map_ι i I
    refine AddSubgroup.mem_sup_right (mk_mem_supportedCoherentKZeroLowerPart C f
      (Closeds.closure {i (genericPoint W)})
      (closure_singleton_subset_of_mem hξZ) (fun z hz => ?_) _ hc hs
      ((supp_subset_of_mono ((Scheme.Modules.pushforward i).map I.ι)).trans
        (supp_pushforward_unitModule i).le))
    have := relativeDimension_le_of_mem_closure C f hz
    omega
  exact mk_pushforward_mem_span_supportedCoherentKZeroPoint_sup_lowerPart_of_eq C f Z k hZ i I hI
    hIz hc hs heq

/-- **Dévissage in `K₀(Coh_Z(X))`.** If every point of `Z` has relative dimension at most `k`,
every element of `K₀(Coh_Z(X))` is, modulo classes from closed subsets of `Z` on which the
relative dimension is at most `k - 1`, an integral combination of the classes `[𝒪_{\overline{ξ}}]`
of the points `ξ ∈ Z` of relative dimension `k`.

By Stacks 01YF it suffices to treat `i_*I` for `i : W ⟶ X` a closed immersion of an integral
scheme with generic point `η` and `I ⊆ 𝒪_W` a quasi-coherent ideal sheaf, `I ≠ 0`; put
`ξ = i(η) ∈ Z`. If `δ(ξ) < k`, `i_*I` is supported in `\overline{ξ}`, on which `δ ≤ k - 1`. If
`δ(ξ) = k`, the cokernel `Q` of `i_*I ⟶ i_*𝒪_W` has length `1 - length(i_*I)_ξ ≤ 0` at `ξ`, so its
support is a closed subset of `\overline{ξ} ∖ {ξ}`, on which `δ ≤ k - 1`, and
`[i_*I] = [𝒪_{\overline{ξ}}] - [Q]`. -/
theorem mem_span_supportedCoherentKZeroPoint_sup_lowerPart [IsNoetherian X] (Z : Closeds X)
    (k : ℤ) (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k)
    (a : supportedCoherentKZero Z) :
    a ∈ (Submodule.span ℤ (Set.range fun ξ : {ξ : X // ξ ∈ Z ∧
        relativeDimension C.dimensionFunction f ξ = k} =>
          supportedCoherentKZeroPoint Z ξ.2.1)).toAddSubgroup ⊔
      supportedCoherentKZeroLowerPart C f Z (k - 1) := by
  set N := (Submodule.span ℤ (Set.range fun ξ : {ξ : X // ξ ∈ Z ∧
        relativeDimension C.dimensionFunction f ξ = k} =>
          supportedCoherentKZeroPoint Z ξ.2.1)).toAddSubgroup ⊔
      supportedCoherentKZeroLowerPart C f Z (k - 1) with hN
  have key : ∀ M : X.Modules, _root_.SheafOfModules.IsCoherent M →
      ∀ (hc : _root_.SheafOfModules.IsCoherent M) (hs : SheafOfModules.supp M ⊆ (Z : Set X)),
        supportedCoherentMk M hc hs ∈ N := by
    refine Stacks.AlgebraicGeometry.CoherentDevissage.property_of_forall_hasIdealFiltration
      (fun M => ∀ (hc : _root_.SheafOfModules.IsCoherent M)
        (hs : SheafOfModules.supp M ⊆ (Z : Set X)), supportedCoherentMk M hc hs ∈ N)
      (fun F hF => let := hF; Stacks.AlgebraicGeometry.CoherentDevissage.hasIdealFiltration X F)
      ?_ ?_ ?_
    · intro hc hs
      rw [show supportedCoherentMk _ hc hs = 0 from supportedCoherentKZero_mk_eq_zero _
        Stacks.AlgebraicGeometry.CoherentDevissage.isZero_terminal]
      exact zero_mem _
    · intro S hS hc₁ _ hc₃ h₁ h₃ hc hs
      have hm := hS.mono_f
      have he := hS.epi_g
      have hs₁ : SheafOfModules.supp S.X₁ ⊆ (Z : Set X) := (supp_subset_of_mono S.f).trans hs
      have hs₃ : SheafOfModules.supp S.X₃ ⊆ (Z : Set X) := (supp_subset_of_epi S.g).trans hs
      rw [show supportedCoherentMk _ hc hs =
          supportedCoherentMk _ hc₁ hs₁ + supportedCoherentMk _ hc₃ hs₃ from
        supportedCoherentKZero_mk_add _ _ _ S.f S.g S.zero hS]
      exact add_mem (h₁ hc₁ hs₁) (h₃ hc₃ hs₃)
    · intro W i _ _ I hI hc hs
      exact mk_pushforward_mem_span_supportedCoherentKZeroPoint_sup_lowerPart C f Z k hZ i I hI
        hc hs
  have hc' : ∀ A : (coherentSupportedIn (Z : Set X)).FullSubcategory,
      _root_.SheafOfModules.IsCoherent A.obj.obj := fun A =>
    AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent A.obj.property
  obtain ⟨⟨b, hb⟩, rfl⟩ := KZero.surjective_of_mk_mem_range N.subtype
    (fun A => ⟨⟨_, key A.obj.obj (hc' A) (hc' A) A.property⟩, rfl⟩) a
  exact hb

/-! ### Elements with vanishing `k`-cycle -/

/-- **An element of `K₀(Coh_Z(X))` with zero `k`-cycle comes from smaller dimension.** If every
point of `Z` has relative dimension at most `k` and `a ∈ K₀(Coh_Z(X))` has `k`-cycle zero, then
`a` is a sum of classes from closed subsets of `Z` on which the relative dimension is at most
`k - 1`. By dévissage `a = ∑ n_ξ [𝒪_{\overline{ξ}}] + b` with `b` such a sum, and the coefficient
of the `k`-cycle of `a` at `ξ` is `n_ξ`. -/
theorem mem_supportedCoherentKZeroLowerPart_of_cycle_eq_zero [IsNoetherian X] (Z : Closeds X)
    (k : ℤ) (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k)
    (a : supportedCoherentKZero Z) (ha : supportedCoherentKZeroCycle C f Z k hZ a = 0) :
    a ∈ supportedCoherentKZeroLowerPart C f Z (k - 1) := by
  classical
  obtain ⟨y, hy, b, hb, rfl⟩ :=
    AddSubgroup.mem_sup.1 (mem_span_supportedCoherentKZeroPoint_sup_lowerPart C f Z k hZ a)
  obtain ⟨n, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hy
  have hb0 : supportedCoherentKZeroCycle C f Z k hZ b = 0 :=
    supportedCoherentKZeroLowerPart_le_ker C f Z k hZ hb
  suffices hn : n = 0 by rwa [hn, Finsupp.sum_zero_index, zero_add]
  ext ξ
  let ev : CycleGroup C f k →+ ℤ :=
    { toFun := fun c => c.1 ξ.1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hev : ∀ η : {ξ : X // ξ ∈ Z ∧ relativeDimension C.dimensionFunction f ξ = k},
      ev (supportedCoherentKZeroCycle C f Z k hZ (supportedCoherentKZeroPoint Z η.2.1)) =
        if η = ξ then 1 else 0 := fun η => by
    change (supportedCoherentKZeroCycle C f Z k hZ (supportedCoherentKZeroPoint Z η.2.1)).1 ξ.1 = _
    rw [supportedCoherentKZeroCycle_point_apply C f Z k hZ η.2.1 η.2.2]
    by_cases h : η = ξ
    · rw [ite_eq_left h, h, singlePointCoeff_self, Nat.cast_one]
    · rw [ite_eq_right h, singlePointCoeff_of_ne (fun h' => h (Subtype.ext h'.symm)), Nat.cast_zero]
  have h := congrArg ev ha
  simp only [map_add, hb0, add_zero, map_zero, map_finsuppSum, map_zsmul, hev,
    smul_eq_mul] at h
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  by_contra hne
  simp [hne] at h

/-- **(P2'') for `𝐐 ⊗ K₀(Coh_Z(X))`.** If every point of `Z` has relative dimension at most `k`
and `y ∈ 𝐐 ⊗ K₀(Coh_Z(X))` has `k`-cycle zero in `Z_k(X) ⊗ 𝐐`, then `y` comes from
`𝐐 ⊗ K₀(Coh_{Z'}(X))` for a single closed subset `Z' ⊆ Z` on which the relative dimension is at
most `k - 1`. -/
theorem exists_mem_range_of_supportedCoherentKZeroRatCycle_eq_zero [IsNoetherian X]
    (Z : Closeds X) (k : ℤ) (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k)
    (y : (supportedCoherentKZeroRat X).obj Z)
    (hy : supportedCoherentKZeroRatCycle C f Z k hZ y = 0) :
    ∃ (Z' : Closeds X) (h : Z' ≤ Z),
      (∀ z ∈ Z', relativeDimension C.dimensionFunction f z ≤ k - 1) ∧
        y ∈ LinearMap.range ((supportedCoherentKZeroRat X).map (homOfLE h)).hom := by
  let g := TensorProduct.mk ℤ ℚ (supportedCoherentKZero Z) 1
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (nonZeroDivisors ℤ) g y
  rw [Function.uncurry_apply_pair] at hy ⊢
  have hs' : ((s : ℤ) : ℚ) • IsLocalizedModule.mk' g a s = (1 : ℚ) ⊗ₜ[ℤ] a := by
    rw [Int.cast_smul_eq_zsmul]
    exact IsLocalizedModule.mk'_cancel' g a s
  have h1 : (1 : ℚ) ⊗ₜ[ℤ] supportedCoherentKZeroCycle C f Z k hZ a = 0 := by
    have h := congrArg (supportedCoherentKZeroRatCycle C f Z k hZ) hs'
    have h2 := congrArg (((s : ℤ) : ℚ) • ·) hy
    simp only [smul_zero] at h2
    exact h.symm.trans ((LinearMap.map_smul _ _ _).trans h2)
  obtain ⟨m, hm, hma⟩ := exists_zsmul_eq_zero_of_one_tmul_eq_zero h1
  obtain ⟨Z', h, hZ', b, hb⟩ := (mem_supportedCoherentKZeroLowerPart_iff C f).1
    (mem_supportedCoherentKZeroLowerPart_of_cycle_eq_zero C f Z k hZ (m • a)
      (by rw [map_zsmul, hma]))
  refine ⟨Z', h, hZ', ((m : ℚ) * ((s : ℤ) : ℚ))⁻¹ ⊗ₜ[ℤ] b, ?_⟩
  have hs0 : ((s : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero s
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  change ((m : ℚ) * ((s : ℤ) : ℚ))⁻¹ ⊗ₜ[ℤ] supportedCoherentKZeroMap (leOfHom (homOfLE h)) b = _
  rw [show supportedCoherentKZeroMap (leOfHom (homOfLE h)) b = m • a from hb,
    TensorProduct.tmul_smul, ← Int.cast_smul_eq_zsmul ℚ,
    show ((m : ℚ) * ((s : ℤ) : ℚ))⁻¹ ⊗ₜ[ℤ] a =
      ((m : ℚ) * ((s : ℤ) : ℚ))⁻¹ • ((1 : ℚ) ⊗ₜ[ℤ] a) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    ← hs', smul_smul, smul_smul,
    show (m : ℚ) * ((m : ℚ) * ((s : ℤ) : ℚ))⁻¹ * ((s : ℤ) : ℚ) = 1 by field_simp, one_smul]

/-- **The `k`-th step of the filtration comes from supports of dimension `≤ k`.** The image of
`F_k K'₀(X)` in `𝐐 ⊗ K₀(Coh_X(X))` lies in the span of the images of `𝐐 ⊗ K₀(Coh_Z(X))` over the
closed subsets `Z` on which the relative dimension is at most `k`: the class of a coherent module
of support dimension at most `k` comes from its support. -/
theorem coherentKZeroToSupportedCoherentKZeroRatTop_mem_iSup (k : ℤ) {b : CoherentKZero X}
    (hb : b ∈ coherentKZeroFiltration C f k) :
    coherentKZeroToSupportedCoherentKZeroRatTop b ∈
      ⨆ (Z : Closeds X) (_ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k),
        LinearMap.range ((supportedCoherentKZeroRat X).map (homOfLE (le_top : Z ≤ ⊤))).hom := by
  refine (AddSubgroup.closure_le (K := (⨆ (Z : Closeds X)
      (_ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k),
        LinearMap.range ((supportedCoherentKZeroRat X).map
          (homOfLE (le_top : Z ≤ ⊤))).hom).toAddSubgroup.comap
      coherentKZeroToSupportedCoherentKZeroRatTop)).2 ?_ hb
  rintro _ ⟨F, rfl⟩
  have hc : _root_.SheafOfModules.IsCoherent F.obj.obj :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent F.obj.property
  let ZF : Closeds X := ⟨SheafOfModules.supp F.obj.obj,
    Stacks.AlgebraicGeometry.DevissageNoetherian.isClosed_supp_of_isCoherent _ hc⟩
  refine Submodule.mem_iSup_of_mem ZF (Submodule.mem_iSup_of_mem
    (relativeDimension_le_of_mem_supp_dimLE C f k F)
    ⟨(1 : ℚ) ⊗ₜ[ℤ] KZero.mk _ (⟨F.obj, subset_rfl⟩ :
      (coherentSupportedIn (ZF : Set X)).FullSubcategory), ?_⟩)
  rw [supportedCoherentKZeroRat_map_tmul, supportedCoherentKZeroMap_mk]
  change _ = (1 : ℚ) ⊗ₜ[ℤ] supportedCoherentKZeroTopEquiv.symm (KZero.mk _ F.obj)
  rw [supportedCoherentKZeroTopEquiv_symm_mk]

end Cycle

/-! ### Separation of the filtration by dimension of supports, given a weight operator -/

section Separation

variable (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
  [AlgebraicGeometry.IsNoetherian X]

/-- **(P2') from (P2'').** Let `Ψ` be a natural endomorphism of `Z ↦ 𝐐 ⊗ K₀(Coh_Z(X))` which,
whenever every point of `Z` has relative dimension at most `k`, satisfies `[Ψ x - ℓ^{-k} x]_k = 0`.
Then on every nonempty closed `Z` there are a point `z₀ ∈ Z` and a closed `Z' ⊊ Z` with
`Ψ x - ℓ^{-δ(z₀)} x` coming from `Z'`: take `z₀` of maximal relative dimension `k` on `Z`, and
`Z'` with relative dimension at most `k - 1`, which does not contain `z₀`. -/
theorem exists_lt_sub_smul_mem_range_of_supportedWeightOperator {ℓ : ℚ}
    (Ψ : supportedCoherentKZeroRat X ⟶ supportedCoherentKZeroRat X)
    (hΨ : ∀ (Z : Closeds X) (k : ℤ)
      (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k)
      (x : (supportedCoherentKZeroRat X).obj Z),
      supportedCoherentKZeroRatCycle C f Z k hZ ((Ψ.app Z).hom x - ℓ ^ (-k) • x) = 0)
    (Z : Closeds X) (x : (supportedCoherentKZeroRat X).obj Z) (hZ : Z ≠ ⊥) :
    ∃ z₀ ∈ Z, ∃ (Z' : Closeds X) (h : Z' < Z),
      (Ψ.app Z).hom x - ℓ ^ (-relativeDimension C.dimensionFunction f z₀) • x ∈
        LinearMap.range ((supportedCoherentKZeroRat X).map (homOfLE h.le)).hom := by
  obtain ⟨z₁, hz₁⟩ : (Z : Set X).Nonempty :=
    Set.nonempty_iff_ne_empty.2 fun h => hZ (Closeds.ext h)
  obtain ⟨hi, hhi⟩ := exists_relativeDimension_le C f
  obtain ⟨k, ⟨z₀, hz₀, rfl⟩, hk⟩ := Int.exists_greatest_of_bdd
    (P := fun k : ℤ => ∃ z ∈ Z, relativeDimension C.dimensionFunction f z = k)
    ⟨hi, fun _ ⟨z, _, hz⟩ => hz ▸ hhi z⟩ ⟨_, z₁, hz₁, rfl⟩
  have hZk : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤
      relativeDimension C.dimensionFunction f z₀ := fun z hz => hk _ ⟨z, hz, rfl⟩
  obtain ⟨Z', h, hZ', hmem⟩ := exists_mem_range_of_supportedCoherentKZeroRatCycle_eq_zero C f Z
    _ hZk _ (hΨ Z _ hZk x)
  have hlt : Z' < Z := lt_of_le_of_ne h fun he => by
    have := hZ' z₀ (he ▸ hz₀)
    omega
  exact ⟨z₀, hz₀, Z', hlt, hmem⟩

/-- **Separation of the filtration by dimension of supports, given a weight operator.** Let
`ℓ > 1` and let `Ψ` be a natural endomorphism of `Z ↦ 𝐐 ⊗ K₀(Coh_Z(X))` which, whenever every
point of `Z` has relative dimension at most `k`, satisfies `[Ψ x - ℓ^{-k} x]_k = 0`. Then an
element of `K'₀(X)` with a nonzero multiple in every `F_k K'₀(X)` is torsion.

Its class `1 ⊗ b ∈ 𝐐 ⊗ K₀(Coh_X(X))` comes, for every `c`, from closed subsets on which the
weight `-δ` is at least `c`
(`Stacks.Chow.coherentKZeroToSupportedCoherentKZeroRatTop_mem_iSup`), and `Ψ` satisfies the
hypothesis of the separation of weights with scalars `ℓ^n`
(`Stacks.Chow.exists_lt_sub_smul_mem_range_of_supportedWeightOperator`), so
`Stacks.Chow.WeightSeparation.eq_zero_of_forall_mem_iSup` gives `1 ⊗ b = 0`. -/
theorem exists_zsmul_eq_zero_of_supportedWeightOperator {ℓ : ℚ} (hℓ : 1 < ℓ)
    (Ψ : supportedCoherentKZeroRat X ⟶ supportedCoherentKZeroRat X)
    (hΨ : ∀ (Z : Closeds X) (k : ℤ)
      (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k)
      (x : (supportedCoherentKZeroRat X).obj Z),
      supportedCoherentKZeroRatCycle C f Z k hZ ((Ψ.app Z).hom x - ℓ ^ (-k) • x) = 0)
    (b : CoherentKZero X)
    (hb : ∀ k : ℤ, ∃ m : ℤ, m ≠ 0 ∧ m • b ∈ coherentKZeroFiltration C f k) :
    ∃ m : ℤ, m ≠ 0 ∧ m • b = 0 := by
  have hx : ∀ c : ℤ, coherentKZeroToSupportedCoherentKZeroRatTop b ∈
      ⨆ (Z : Closeds X) (_ : ∀ z ∈ Z, c ≤ -relativeDimension C.dimensionFunction f z),
        LinearMap.range ((supportedCoherentKZeroRat X).map (homOfLE (le_top : Z ≤ ⊤))).hom := by
    intro c
    obtain ⟨m, hm, hmb⟩ := hb (-c)
    have h1 := coherentKZeroToSupportedCoherentKZeroRatTop_mem_iSup C f (-c) hmb
    have hle : (⨆ (Z : Closeds X) (_ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ -c),
        LinearMap.range ((supportedCoherentKZeroRat X).map (homOfLE (le_top : Z ≤ ⊤))).hom) ≤
        ⨆ (Z : Closeds X) (_ : ∀ z ∈ Z, c ≤ -relativeDimension C.dimensionFunction f z),
          LinearMap.range ((supportedCoherentKZeroRat X).map (homOfLE (le_top : Z ≤ ⊤))).hom :=
      iSup₂_le fun Z hZ => le_iSup₂_of_le (f := fun (Z : Closeds X)
        (_ : ∀ z ∈ Z, c ≤ -relativeDimension C.dimensionFunction f z) =>
          LinearMap.range ((supportedCoherentKZeroRat X).map (homOfLE (le_top : Z ≤ ⊤))).hom)
        Z (fun z hz => by have := hZ z hz; omega) le_rfl
    have h2 := hle h1
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℚ] at h2
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm
    have h3 := Submodule.smul_mem _ (m : ℚ)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hm0, one_smul] at h3
  have hx0 : coherentKZeroToSupportedCoherentKZeroRatTop b = 0 :=
    WeightSeparation.eq_zero_of_forall_mem_iSup Ψ (w := fun z => -relativeDimension
      C.dimensionFunction f z) (μ := fun n : ℤ => ℓ ^ n) (zpow_right_strictMono₀ hℓ).injective
      subsingleton_supportedCoherentKZeroRat_bot
      (exists_lt_sub_smul_mem_range_of_supportedWeightOperator C f Ψ hΨ) _ hx
  refine exists_zsmul_eq_zero_of_one_tmul_eq_zero ?_
  rw [← supportedCoherentKZeroRatToCoherent_coherentKZeroToSupportedCoherentKZeroRatTop, hx0,
    map_zero]

end Separation

/-! ### Injectivity in Stacks 0FEW, given a weight operator -/

section Composite

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (a : Y ⟶ C.S) [LocallyOfFiniteType a]
  (i : X ⟶ Y) [IsClosedImmersion i] (hY : IsRegular Y) [CompactSpace Y]

/-- **Injectivity in Stacks 0FEW, given a weight operator on `𝐐 ⊗ K₀(Coh_Z(X))`.** Let
`i : X ⟶ Y` be a closed immersion with `Y` regular and quasi-compact, and let `ℓ > 1`. Suppose
`Ψ` is a natural endomorphism of `Z ↦ 𝐐 ⊗ K₀(Coh_Z(X))` such that, whenever every point of `Z`
has `δ ≤ k`, the `k`-cycle of `Ψ x - ℓ^{-k} x` vanishes for every `x`. Then
`K'₀(X) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`, `[ℱ] ↦ ch(X ⟶ Y, ℱ[0]) ∩ [Y]`, is injective: the filtration by
dimension of supports is separated (`Stacks.Chow.exists_zsmul_eq_zero_of_supportedWeightOperator`),
which is all of injectivity
(`Stacks.Chow.injective_liftBaseChange_coherentChowCharacter_of_separated`). -/
theorem injective_liftBaseChange_coherentChowCharacter_of_supportedWeightOperator
    {ℓ : ℚ} (hℓ : 1 < ℓ) :
    haveI := isNoetherian_of_isClosedImmersion_of_compactSpace C a i
    ∀ Ψ : supportedCoherentKZeroRat X ⟶ supportedCoherentKZeroRat X,
      (∀ (Z : Closeds X) (k : ℤ)
          (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction (i ≫ a) z ≤ k)
          (x : (supportedCoherentKZeroRat X).obj Z),
          supportedCoherentKZeroRatCycle C (i ≫ a) Z k hZ ((Ψ.app Z).hom x - ℓ ^ (-k) • x) = 0) →
        Function.Injective ((coherentChowCharacter C a i hY).toIntLinearMap.liftBaseChange ℚ) := by
  have := isNoetherian_of_isClosedImmersion_of_compactSpace C a i
  intro Ψ hΨ
  exact injective_liftBaseChange_coherentChowCharacter_of_separated C a i hY
    (exists_zsmul_eq_zero_of_supportedWeightOperator C (i ≫ a) hℓ Ψ hΨ)

end Composite

end Stacks.Chow

end
