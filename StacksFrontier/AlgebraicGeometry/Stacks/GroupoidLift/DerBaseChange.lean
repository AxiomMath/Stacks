module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.LeftExact
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartDescent.Torsor

/-!
# Flat base change of derivations into an ideal

Let `P` be an `A'`-algebra whose module of Kähler differentials is finitely presented (for
instance a finitely presented `A'`-algebra, or a formally smooth one of finite type), let
`ref : P → N` be a map of `A'`-algebras and let `J ⊆ N` be an ideal. The derivations of `P` along
`ref` with values in `J` are `AlgebraicGeometry.Space.ChartDescent.sqDer J ref`. For a flat
`A'`-module `F` this file shows that `D ⊗ f ↦ (x ↦ D x ⊗ f)` identifies `sqDer J ref ⊗[A'] F` with
the derivations of `P` along `includeLeft ∘ ref` with values in the extended ideal of `N ⊗[A'] F`.

The derivations are `Hom_P(Ω[P⁄A'], J)`, and `Hom_P(Ω, -)` commutes with `- ⊗[A'] F` because
`Ω[P⁄A']` is finitely presented and `F` is flat (`homTensor_bijective_of_flat`, reduced to the
finite free case `homTensor_bijective` along a presentation); flatness of `F` also identifies
`J ⊗[A'] F` with the extended ideal.

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.homTensor_bijective`: `Hom_P(Ω, M) ⊗[A'] F` is
  `Hom_P(Ω, M ⊗[A'] F)` for a finite projective `Ω`.
* `AlgebraicGeometry.Stack.GroupoidLift.homTensor_bijective_of_flat`: the same for a finitely
  presented `Ω` and a flat `F`.
* `AlgebraicGeometry.Stack.GroupoidLift.derBaseChange_bijective`: the flat base change of
  derivations.
-/

@[expose] public section

open scoped TensorProduct
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

section HomTensor

variable {A' P : Type u} [CommRing A'] [CommRing P] [Algebra A' P]
  {Ω M F : Type u} [AddCommGroup Ω] [Module P Ω]
  [AddCommGroup M] [Module P M] [Module A' M] [IsScalarTower A' P M]
  [AddCommGroup F] [Module A' F]

variable (P) in
/-- `m ↦ m ⊗ f`, a `P`-linear map. -/
def tmulRight (f : F) : M →ₗ[P] M ⊗[A'] F where
  toFun m := m ⊗ₜ f
  map_add' m m' := TensorProduct.add_tmul m m' f
  map_smul' p m := (TensorProduct.smul_tmul' p m f).symm

variable (A' P Ω M F) in
/-- `φ ⊗ f ↦ (ω ↦ φ ω ⊗ f)`. -/
noncomputable def homTensor : (Ω →ₗ[P] M) ⊗[A'] F →ₗ[A'] (Ω →ₗ[P] M ⊗[A'] F) :=
  TensorProduct.lift
    { toFun := fun φ ↦
        { toFun := fun f ↦ (tmulRight P f).comp φ
          map_add' := fun f g ↦ by ext; simp [tmulRight, TensorProduct.tmul_add]
          map_smul' := fun a f ↦ by ext; simp [tmulRight, TensorProduct.tmul_smul] }
      map_add' := fun φ ψ ↦ by ext; simp [tmulRight, TensorProduct.add_tmul]
      map_smul' := fun a φ ↦ by
        ext
        simp [tmulRight, TensorProduct.smul_tmul'] }

/-- `homTensor` sends `φ ⊗ f` to `ω ↦ φ ω ⊗ f`. -/
@[simp] theorem homTensor_tmul_apply (φ : Ω →ₗ[P] M) (f : F) (ω : Ω) :
    homTensor A' P Ω M F (φ ⊗ₜ f) ω = φ ω ⊗ₜ f := rfl

/-- **`Hom_P(Ω, -)` commutes with `- ⊗[A'] F` for a finite projective `Ω`.** -/
theorem homTensor_bijective [Module.Finite P Ω] [Module.Projective P Ω] :
    Function.Bijective (homTensor A' P Ω M F) := by
  let eA :=
    (LinearEquiv.ofBijective (dualTensorHom P Ω M) dualTensorHom_bijective).restrictScalars A'
  let eB := (LinearEquiv.ofBijective (dualTensorHom P Ω (M ⊗[A'] F))
    dualTensorHom_bijective).restrictScalars A'
  let as :=
    (TensorProduct.AlgebraTensorModule.assoc A' P P (Module.Dual P Ω) M F).restrictScalars A'
  have hcomm : (homTensor A' P Ω M F) ∘ₗ (LinearEquiv.rTensor F eA).toLinearMap =
      (as.trans eB).toLinearMap := by
    refine LinearMap.ext fun x ↦ ?_
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul φ m =>
      induction φ using TensorProduct.inductionOn with
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
      | tmul g n =>
        ext ω
        simp [eA, eB, as, TensorProduct.smul_tmul']
  have h : homTensor A' P Ω M F = (as.trans eB).toLinearMap ∘ₗ
      (LinearEquiv.rTensor F eA).symm.toLinearMap := by
    rw [← hcomm, LinearMap.comp_assoc, ← LinearEquiv.coe_trans, LinearEquiv.symm_trans_self]
    rfl
  rw [h, LinearMap.coe_comp]
  exact (LinearEquiv.bijective _).comp (LinearEquiv.bijective _)

variable (A' P M) in
/-- Precomposition with a `P`-linear map, as an `A'`-linear map of `Hom` modules. -/
def preComp {X Y : Type u} [AddCommGroup X] [Module P X] [AddCommGroup Y] [Module P Y]
    (h : X →ₗ[P] Y) : (Y →ₗ[P] M) →ₗ[A'] (X →ₗ[P] M) where
  toFun φ := φ ∘ₗ h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `homTensor` commutes with precomposition by a `P`-linear map `h : X →ₗ[P] Y`. -/
theorem homTensor_preComp {X Y : Type u} [AddCommGroup X] [Module P X] [AddCommGroup Y]
    [Module P Y] (h : X →ₗ[P] Y) (z : (Y →ₗ[P] M) ⊗[A'] F) :
    homTensor A' P X M F ((preComp A' P M h).rTensor F z) =
      preComp A' P (M ⊗[A'] F) h (homTensor A' P Y M F z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ f => rfl

/-- **`Hom_P(Ω, -)` commutes with `- ⊗[A'] F` for a finitely presented `Ω` and a flat `F`.** -/
theorem homTensor_bijective_of_flat [Module.FinitePresentation P Ω] [Module.Flat A' F] :
    Function.Bijective (homTensor A' P Ω M F) := by
  obtain ⟨n, m, g, f, hg, hfg⟩ := Module.FinitePresentation.exists_fin' P Ω
  have e₁ : Function.Exact (preComp A' P M g) (preComp A' P M f) :=
    LinearMap.exact_lcomp_of_exact_of_surjective (N := M) hfg hg
  have e₂ : Function.Exact (preComp A' P (M ⊗[A'] F) g) (preComp A' P (M ⊗[A'] F) f) :=
    LinearMap.exact_lcomp_of_exact_of_surjective (N := M ⊗[A'] F) hfg hg
  have i₂ : Function.Injective (preComp A' P (M ⊗[A'] F) g) :=
    LinearMap.lcomp_injective_of_surjective (S := P) (N := M ⊗[A'] F) g hg
  have ti : Function.Injective ((preComp A' P M g).rTensor F) :=
    Module.Flat.rTensor_preserves_injective_linearMap _
      (LinearMap.lcomp_injective_of_surjective (S := P) (N := M) g hg)
  have hn := homTensor_bijective (A' := A') (P := P) (Ω := Fin n → P) (M := M) (F := F)
  have hm := homTensor_bijective (A' := A') (P := P) (Ω := Fin m → P) (M := M) (F := F)
  refine ⟨fun x y hxy ↦ ti (hn.1 ?_), fun φ ↦ ?_⟩
  · rw [homTensor_preComp, homTensor_preComp, hxy]
  · obtain ⟨z, hz⟩ := hn.2 (preComp A' P (M ⊗[A'] F) g φ)
    have hz0 : (preComp A' P M f).rTensor F z = 0 := hm.1 (by
      rw [homTensor_preComp, hz, map_zero]
      exact (e₂ _).mpr ⟨φ, rfl⟩)
    obtain ⟨x, hx⟩ := (Module.Flat.rTensor_exact F e₁ z).mp hz0
    exact ⟨x, i₂ (by rw [← homTensor_preComp, hx, hz])⟩

end HomTensor

section Derivations

variable {A' P N F : Type u} [CommRing A'] [CommRing P] [Algebra A' P] [CommRing N]
  [Algebra A' N] [CommRing F] [Algebra A' F]

variable (A') in
/-- The ideal `J`, with `P` acting through `ref`. -/
def RefMod (J : Ideal N) (_ref : P →ₐ[A'] N) : Type u := J

namespace RefMod

variable (J : Ideal N) (ref : P →ₐ[A'] N)

/-- The additive group structure of `J`. -/
instance : AddCommGroup (RefMod A' J ref) := inferInstanceAs (AddCommGroup J)
/-- The `N`-module structure of `J`. -/
instance : Module N (RefMod A' J ref) := inferInstanceAs (Module N J)
/-- The `P`-module structure on `J` obtained by restricting scalars along `ref`. -/
instance : Module P (RefMod A' J ref) := Module.compHom _ (ref : P →+* N)
/-- The `A'`-module structure on `J` obtained by restricting scalars along `algebraMap A' N`. -/
instance : Module A' (RefMod A' J ref) := Module.compHom _ (algebraMap A' N)
/-- The `A'`- and `P`-actions on `RefMod A' J ref` form a scalar tower. -/
instance : IsScalarTower A' P (RefMod A' J ref) :=
  ⟨fun a p m ↦ by
    change (ref (a • p)) • m = (algebraMap A' N a) • (ref p • m)
    rw [map_smul, Algebra.smul_def, mul_smul]⟩

/-- The underlying element of `N`. -/
def val (m : RefMod A' J ref) : N := Subtype.val (show J from m)

/-- An element of `J` as an element of `RefMod`. -/
def mk (j : J) : RefMod A' J ref := j

/-- The underlying element of `mk J ref j` is `j`. -/
@[simp] theorem val_mk (j : J) : val J ref (mk J ref j) = j := rfl

/-- The underlying element of `m : RefMod A' J ref` lies in `J`. -/
theorem val_mem (m : RefMod A' J ref) : val J ref m ∈ J := (show J from m).2

/-- `val` is additive. -/
theorem val_add (m m' : RefMod A' J ref) : val J ref (m + m') = val J ref m + val J ref m' := rfl

/-- `p : P` acts on the underlying element by multiplication by `ref p`. -/
theorem val_smul (p : P) (m : RefMod A' J ref) : val J ref (p • m) = ref p * val J ref m := rfl

/-- `a : A'` acts on the underlying element by multiplication by `algebraMap A' N a`. -/
theorem val_smul_A' (a : A') (m : RefMod A' J ref) :
    val J ref (a • m) = algebraMap A' N a * val J ref m := rfl

/-- `val` is injective. -/
theorem val_injective : Function.Injective (val J ref) := Subtype.val_injective

end RefMod

variable (J : Ideal N) (ref : P →ₐ[A'] N)

/-- A derivation into `J`, read as a derivation into `RefMod`. -/
def toDerivation (D : sqDer J ref) : Derivation A' P (RefMod A' J ref) :=
  Derivation.mk'
    { toFun := fun x ↦ RefMod.mk J ref ⟨(D : P →ₗ[A'] N) x, sqDer_mem D x⟩
      map_add' := fun x y ↦ Subtype.ext (map_add (D : P →ₗ[A'] N) x y)
      map_smul' := fun a x ↦ Subtype.ext (by
        change (D : P →ₗ[A'] N) (a • x) = algebraMap A' N a * (D : P →ₗ[A'] N) x
        rw [map_smul, Algebra.smul_def]) }
    fun x y ↦ Subtype.ext (by
      change (D : P →ₗ[A'] N) (x * y) = ref x * (D : P →ₗ[A'] N) y + ref y * (D : P →ₗ[A'] N) x
      exact sqDer_leibniz D x y)

/-- The underlying element of `toDerivation J ref D x` is `D x`. -/
theorem val_toDerivation (D : sqDer J ref) (x : P) :
    RefMod.val J ref (toDerivation J ref D x) = (D : P →ₗ[A'] N) x := rfl

/-- `toDerivation` as a linear map. -/
def toDerivationₗ : sqDer J ref →ₗ[A'] Derivation A' P (RefMod A' J ref) where
  toFun := toDerivation J ref
  map_add' D E := by ext x; exact Subtype.ext rfl
  map_smul' a D := by ext x; exact Subtype.ext (Algebra.smul_def _ _)

/-- Derivations into `J` as `P`-linear maps out of the Kähler differentials. -/
noncomputable def derToHom : sqDer J ref →ₗ[A'] (Ω[P⁄A'] →ₗ[P] RefMod A' J ref) :=
  ((KaehlerDifferential.linearMapEquivDerivation A' P).symm.restrictScalars A').toLinearMap ∘ₗ
    toDerivationₗ J ref

/-- The `P`-linear map `derToHom J ref D` sends `KaehlerDifferential.D A' P x` to `D x`. -/
theorem derToHom_D (D : sqDer J ref) (x : P) :
    RefMod.val J ref (derToHom J ref D (KaehlerDifferential.D A' P x)) =
      (D : P →ₗ[A'] N) x := by
  change RefMod.val J ref ((toDerivation J ref D).liftKaehlerDifferential
    (KaehlerDifferential.D A' P x)) = _
  rw [Derivation.liftKaehlerDifferential_comp_D]
  rfl

/-- `derToHom` is bijective. -/
theorem derToHom_bijective : Function.Bijective (derToHom J ref) := by
  refine ⟨fun D E h ↦ ?_, fun φ ↦ ?_⟩
  · apply Subtype.ext
    ext x
    simpa only [derToHom_D] using
      congrArg (fun φ ↦ RefMod.val J ref (φ (KaehlerDifferential.D A' P x))) h
  · let δ := KaehlerDifferential.linearMapEquivDerivation A' P φ
    let L : P →ₗ[A'] N :=
      { toFun := fun x ↦ RefMod.val J ref (δ x)
        map_add' := fun x y ↦ by rw [map_add, RefMod.val_add]
        map_smul' := fun a x ↦ by
          rw [Derivation.map_smul, RefMod.val_smul_A', RingHom.id_apply, Algebra.smul_def] }
    have hL : L ∈ sqDer J ref := ⟨fun x ↦ RefMod.val_mem J ref (δ x), fun x y ↦ by
      change RefMod.val J ref (δ (x * y)) = _
      rw [δ.leibniz x y, RefMod.val_add, RefMod.val_smul, RefMod.val_smul]
      rfl⟩
    refine ⟨⟨L, hL⟩, ?_⟩
    have hδ : toDerivation J ref ⟨L, hL⟩ = δ := by
      ext x
      exact Subtype.ext rfl
    change (KaehlerDifferential.linearMapEquivDerivation A' P).symm
      (toDerivation J ref ⟨L, hL⟩) = φ
    rw [hδ, LinearEquiv.symm_apply_apply]

/-! ### The base change -/

variable (F)

/-- The extension of `J` to `N ⊗[A'] F`. -/
abbrev extIdeal : Ideal (N ⊗[A'] F) :=
  J.map (Algebra.TensorProduct.includeLeft : N →ₐ[A'] N ⊗[A'] F)

/-- The base change of `ref`. -/
abbrev extRef : P →ₐ[A'] N ⊗[A'] F := (Algebra.TensorProduct.includeLeft).comp ref

variable {F}

/-- For `j ∈ J` and `f : F`, the element `j ⊗ f` lies in the extended ideal `extIdeal F J`. -/
theorem tmul_mem_extIdeal {j : N} (hj : j ∈ J) (f : F) : j ⊗ₜ[A'] f ∈ extIdeal F J := by
  rw [show j ⊗ₜ[A'] f = (Algebra.TensorProduct.includeLeft (S := A') j : N ⊗[A'] F) *
      ((1 : N) ⊗ₜ[A'] f) by simp]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hj)

variable (N) in
/-- `n ↦ n ⊗ f`. -/
def tmulF (f : F) : N →ₗ[A'] N ⊗[A'] F where
  toFun n := n ⊗ₜ f
  map_add' n n' := TensorProduct.add_tmul n n' f
  map_smul' a n := (TensorProduct.smul_tmul' a n f).symm

/-- For a derivation `D` into `J` along `ref` and `f : F`, the map `x ↦ D x ⊗ f` is a derivation
into `extIdeal F J` along `extRef F ref`. -/
theorem tmul_mem_sqDer (D : sqDer J ref) (f : F) :
    tmulF N f ∘ₗ (D : P →ₗ[A'] N) ∈ sqDer (extIdeal F J) (extRef F ref) := by
  refine ⟨fun x ↦ tmul_mem_extIdeal J (sqDer_mem D x) f, fun x y ↦ ?_⟩
  simp only [LinearMap.comp_apply, tmulF, LinearMap.coe_mk, AddHom.coe_mk,
    sqDer_leibniz D x y, AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
    TensorProduct.add_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- **The base change of derivations**: `D ⊗ f ↦ (x ↦ D x ⊗ f)`. -/
noncomputable def derBaseChange :
    sqDer J ref ⊗[A'] F →ₗ[A'] sqDer (extIdeal F J) (extRef F ref) :=
  TensorProduct.lift
    { toFun := fun D ↦
        { toFun := fun f ↦ ⟨_, tmul_mem_sqDer J ref D f⟩
          map_add' := fun f g ↦ Subtype.ext (LinearMap.ext fun x ↦ TensorProduct.tmul_add _ _ _)
          map_smul' := fun a f ↦ Subtype.ext (LinearMap.ext fun x ↦ TensorProduct.tmul_smul _ _ _) }
      map_add' := fun D E ↦ by
        ext f x
        exact TensorProduct.add_tmul _ _ _
      map_smul' := fun a D ↦ by
        ext f x
        exact (TensorProduct.smul_tmul' _ _ _).symm }

/-- `derBaseChange J ref (D ⊗ f)` sends `x` to `D x ⊗ f`. -/
@[simp] theorem derBaseChange_tmul_apply (D : sqDer J ref) (f : F) (x : P) :
    ((derBaseChange J ref (D ⊗ₜ f) : sqDer _ _) : P →ₗ[A'] N ⊗[A'] F) x = (D : P →ₗ[A'] N) x ⊗ₜ f :=
  rfl

namespace RefMod

/-- `val` as an `A'`-linear map. -/
def valₗ : RefMod A' J ref →ₗ[A'] N where
  toFun := val J ref
  map_add' := val_add J ref
  map_smul' a m := by rw [val_smul_A', RingHom.id_apply, Algebra.smul_def]

end RefMod

/-- The comparison `RefMod J ⊗[A'] F → RefMod (extIdeal F J)`, `j ⊗ f ↦ j ⊗ f`. -/
noncomputable def refTensor :
    RefMod A' J ref ⊗[A'] F →ₗ[P] RefMod A' (extIdeal F J) (extRef F ref) :=
  { toFun := fun z ↦ RefMod.mk _ _ ⟨TensorProduct.map (RefMod.valₗ J ref) LinearMap.id z, by
      induction z using TensorProduct.inductionOn with
      | tmul j f => exact tmul_mem_extIdeal J (RefMod.val_mem J ref j) f
      | add x y hx hy =>
        rw [map_add]
        exact Ideal.add_mem _ hx hy⟩
    map_add' := fun x y ↦ Subtype.ext (map_add _ x y)
    map_smul' := fun p z ↦ by
      apply Subtype.ext
      change TensorProduct.map (RefMod.valₗ J ref) LinearMap.id (p • z) =
        (ref p ⊗ₜ[A'] (1 : F)) * TensorProduct.map (RefMod.valₗ J ref) LinearMap.id z
      induction z using TensorProduct.inductionOn with
      | tmul j f =>
        rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        rfl
      | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, mul_add] }

/-- The underlying element of `refTensor J ref (j ⊗ f)` is `val j ⊗ f`. -/
theorem val_refTensor_tmul (j : RefMod A' J ref) (f : F) :
    RefMod.val _ _ (refTensor J ref (j ⊗ₜ f)) = RefMod.val J ref j ⊗ₜ f := rfl

/-- **Flatness**: the comparison is bijective. -/
theorem refTensor_bijective [Module.Flat A' F] : Function.Bijective (refTensor J ref (F := F)) := by
  refine ⟨fun x y h ↦ ?_, fun z ↦ ?_⟩
  · have hinj : Function.Injective
        (TensorProduct.map (RefMod.valₗ J ref) (LinearMap.id : F →ₗ[A'] F)) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (RefMod.val_injective J ref)
    exact hinj (congrArg (fun m ↦ RefMod.val _ _ m) h)
  · let S := LinearMap.range (TensorProduct.map (RefMod.valₗ J ref) (LinearMap.id : F →ₗ[A'] F))
    let I₀ : Ideal (N ⊗[A'] F) :=
      { S.toAddSubmonoid with
        smul_mem' := by
          rintro c _ ⟨a, rfl⟩
          induction c using TensorProduct.inductionOn with
          | add c d hc hd => rw [add_smul]; exact S.add_mem hc hd
          | tmul n f =>
            induction a using TensorProduct.inductionOn with
            | add a b ha hb => rw [map_add, smul_add]; exact S.add_mem ha hb
            | tmul j g =>
              refine ⟨(RefMod.mk J ref ⟨n * RefMod.val J ref j,
                Ideal.mul_mem_left _ _ (RefMod.val_mem J ref j)⟩) ⊗ₜ (f * g), ?_⟩
              simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq, smul_eq_mul,
                Algebra.TensorProduct.tmul_mul_tmul]
              rfl }
    have hle : extIdeal F J ≤ I₀ :=
      Ideal.map_le_iff_le_comap.mpr fun j hj ↦ ⟨RefMod.mk J ref ⟨j, hj⟩ ⊗ₜ 1, rfl⟩
    obtain ⟨x, hx⟩ := hle (RefMod.val_mem _ _ z)
    exact ⟨x, RefMod.val_injective _ _ hx⟩

/-- Postcomposition with the comparison. -/
noncomputable def postRefTensor :
    (Ω[P⁄A'] →ₗ[P] RefMod A' J ref ⊗[A'] F) →ₗ[A']
      (Ω[P⁄A'] →ₗ[P] RefMod A' (extIdeal F J) (extRef F ref)) where
  toFun φ := refTensor J ref ∘ₗ φ
  map_add' φ ψ := LinearMap.comp_add _ _ _
  map_smul' a φ := LinearMap.ext fun ω ↦ by
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply]
    rw [← IsScalarTower.algebraMap_smul P a (φ ω), map_smul, IsScalarTower.algebraMap_smul]

/-- For a flat `F`, postcomposition with `refTensor` is bijective. -/
theorem postRefTensor_bijective [Module.Flat A' F] :
    Function.Bijective (postRefTensor J ref (F := F)) := by
  let e := LinearEquiv.ofBijective (refTensor J ref (F := F)) (refTensor_bijective J ref)
  exact ⟨fun φ ψ h ↦ LinearMap.ext fun ω ↦ e.injective (LinearMap.congr_fun h ω),
    fun χ ↦ ⟨e.symm.toLinearMap ∘ₗ χ, LinearMap.ext fun ω ↦ e.apply_symm_apply (χ ω)⟩⟩

variable [Module.FinitePresentation P Ω[P⁄A']]

omit [Module.FinitePresentation P Ω[P⁄A']] in
/-- Under `derToHom`, `derBaseChange` corresponds to `postRefTensor ∘ homTensor`. -/
theorem derBaseChange_square :
    (derToHom (extIdeal F J) (extRef F ref)) ∘ₗ derBaseChange J ref =
      postRefTensor J ref ∘ₗ homTensor A' P Ω[P⁄A'] (RefMod A' J ref) F ∘ₗ
        (derToHom J ref).rTensor F := by
  refine TensorProduct.ext' fun D f ↦ ?_
  refine LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation A' P) fun x ↦ ?_
  apply RefMod.val_injective
  have lhs := derToHom_D (extIdeal F J) (extRef F ref) (derBaseChange J ref (D ⊗ₜ f)) x
  have rhs := val_refTensor_tmul J ref (derToHom J ref D (KaehlerDifferential.D A' P x)) f
  rw [derToHom_D] at rhs
  simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul]
  exact lhs.trans ((derBaseChange_tmul_apply J ref D f x).trans rhs.symm)

/-- **The flat base change of derivations is bijective.** -/
theorem derBaseChange_bijective [Module.Flat A' F] :
    Function.Bijective (derBaseChange J ref (F := F)) := by
  refine (Function.Bijective.of_comp_iff' (derToHom_bijective _ _) _).mp ?_
  rw [← LinearMap.coe_comp, derBaseChange_square]
  exact (postRefTensor_bijective J ref).comp (homTensor_bijective_of_flat.comp
    (LinearEquiv.rTensor F (LinearEquiv.ofBijective _ (derToHom_bijective J ref))).bijective)

end Derivations

end AlgebraicGeometry.Stack.GroupoidLift

end
