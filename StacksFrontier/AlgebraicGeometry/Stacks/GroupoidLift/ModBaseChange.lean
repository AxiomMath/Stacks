module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.Calculus
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.DerBaseChange

/-!
# Flat base change of the deformation modules

Let `e : C' → C` be a square-zero thickening of small `A'`-algebras, `F` a flat `A'`-algebra,
and `e₂ : C' ⊗[A'] F → D` a thickening whose kernel is the extension of the kernel of `e`,
receiving `e` through `includeLeft`. For an `A'`-algebra `P` with finitely presented Kähler
differentials (a finitely presented one, or a formally smooth one of finite type) and a point `w`,
the derivations satisfy `F ⊗[A'] Der e w ≅ Der e₂ w₂`
(`AlgebraicGeometry.Stack.GroupoidLift.derBC_bijective`); with a formally étale chart near the
identities the same holds for the module `Mod`
(`AlgebraicGeometry.Stack.GroupoidLift.modBC_bijective`).
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable {A' : Type u} [CommRing A'] {κ : Cardinal.{u}}

section DerEq

variable {C' C : SmallAlg A' κ} {e : SqZero C' C} {P : Type u} [CommRing P] [Algebra A' P]

/-- The derivations along a point are the derivations along any of its lifts. -/
theorem Der_eq_sqDer {w : P →ₐ[A'] C.obj} {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w) :
    Der e w = sqDer (RingHom.ker (e.q.hom.hom : C'.obj →+* C.obj)) ℓ := by
  ext D
  refine ⟨fun hD ↦ ⟨fun x ↦ hD.1 x, fun x y ↦ Der.leibniz hD ℓ hℓ x y⟩, fun hD ↦ ⟨fun x ↦ hD.1 x,
    fun x y a b ha hb ↦ ?_⟩⟩
  have hℓx : e.q.hom.hom (ℓ x) = w x := congrArg (fun f : P →ₐ[A'] C.obj ↦ f x) hℓ
  have hℓy : e.q.hom.hom (ℓ y) = w y := congrArg (fun f : P →ₐ[A'] C.obj ↦ f y) hℓ
  have z₁ := e.mul_eq_zero (x := a - ℓ x) (y := D y) (by rw [map_sub, ha, hℓx, sub_self])
    (hD.1 y)
  have z₂ := e.mul_eq_zero (x := b - ℓ y) (y := D x) (by rw [map_sub, hb, hℓy, sub_self])
    (hD.1 x)
  rw [hD.2 x y]
  linear_combination -z₁ - z₂

end DerEq

/-- A base change of thickenings along the flat algebra `F`. -/
structure IsBaseChange {X' X Y : SmallAlg A' κ} (e : SqZero X' X) (F : Type u) [CommRing F]
    [Algebra A' F] {hY : Cardinal.mk (X'.obj ⊗[A'] F) < κ}
    (e₂ : SqZero (SmallAlg.mk (X'.obj ⊗[A'] F) hY) Y) (φ : SqZero.Hom e e₂) : Prop where
  ker_eq : RingHom.ker (e₂.q.hom.hom : (X'.obj ⊗[A'] F) →+* Y.obj) =
    extIdeal F (RingHom.ker (e.q.hom.hom : X'.obj →+* X.obj))
  top_apply : ∀ x : X'.obj, φ.top.hom.hom x = (x ⊗ₜ[A'] (1 : F) : X'.obj ⊗[A'] F)

section DerBC

variable {X' X Y : SmallAlg A' κ} {e : SqZero X' X} {F : Type u} [CommRing F] [Algebra A' F]
  {hY : Cardinal.mk (X'.obj ⊗[A'] F) < κ} {e₂ : SqZero (SmallAlg.mk (X'.obj ⊗[A'] F) hY) Y}
  {φ : SqZero.Hom e e₂}
  {P : Type u} [CommRing P] [Algebra A' P]

variable (hB : IsBaseChange e F e₂ φ)

include hB in
/-- Composing a lift `ℓ` with the top map `φ.top` gives its extension `extRef F ℓ`. -/
theorem top_comp_eq (ℓ : P →ₐ[A'] X'.obj) : φ.top.hom.hom.comp ℓ = extRef F ℓ := by
  ext x
  exact hB.top_apply (ℓ x)

variable [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' F]

/-- **The flat base change of derivations along a thickening.** -/
noncomputable def derBC {w : P →ₐ[A'] X.obj} (ℓ : P →ₐ[A'] X'.obj) (hℓ : e.q.hom.hom.comp ℓ = w)
    {w₂ : P →ₐ[A'] Y.obj} (hw : φ.bot.hom.hom.comp w = w₂) :
    F ⊗[A'] Der e w →ₗ[A'] Der e₂ w₂ :=
  have h₂ : Der e₂ w₂ = sqDer (extIdeal F (RingHom.ker (e.q.hom.hom : X'.obj →+* X.obj)))
      (extRef F ℓ) := by
    rw [Der_eq_sqDer (e := e₂) (ℓ := φ.top.hom.hom.comp ℓ) (by rw [SqZero.Hom.w_comp, hℓ, hw]),
      hB.ker_eq, top_comp_eq hB]
  ((LinearEquiv.ofEq _ _ h₂.symm).restrictScalars A').toLinearMap ∘ₗ
    derBaseChange (RingHom.ker (e.q.hom.hom : X'.obj →+* X.obj)) ℓ ∘ₗ
    ((LinearEquiv.ofEq _ _ (Der_eq_sqDer hℓ)).restrictScalars A').toLinearMap.rTensor F ∘ₗ
    (TensorProduct.comm A' F (Der e w)).toLinearMap

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' F] in
/-- `derBC` sends `f ⊗ D` to `(1 ⊗ f) • postcomp φ D`. -/
theorem derBC_tmul {w : P →ₐ[A'] X.obj} (ℓ : P →ₐ[A'] X'.obj) (hℓ : e.q.hom.hom.comp ℓ = w)
    {w₂ : P →ₐ[A'] Y.obj} (hw : φ.bot.hom.hom.comp w = w₂) (f : F) (D : Der e w) :
    ((derBC hB ℓ hℓ hw (f ⊗ₜ D) : Der e₂ w₂) : P →ₗ[A'] (X'.obj ⊗[A'] F)) =
      ((1 : X'.obj) ⊗ₜ[A'] f : X'.obj ⊗[A'] F) • postcomp φ D.1 := by
  ext x
  show (D.1 x) ⊗ₜ[A'] f = ((1 : X'.obj) ⊗ₜ[A'] f) * φ.top.hom.hom (D.1 x)
  rw [hB.top_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

/-- The flat base change of derivations `derBC` is bijective. -/
theorem derBC_bijective {w : P →ₐ[A'] X.obj} (ℓ : P →ₐ[A'] X'.obj)
    (hℓ : e.q.hom.hom.comp ℓ = w) {w₂ : P →ₐ[A'] Y.obj} (hw : φ.bot.hom.hom.comp w = w₂) :
    Function.Bijective (derBC hB ℓ hℓ hw) := by
  unfold derBC
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe]
  refine (LinearEquiv.bijective _).comp ((derBaseChange_bijective
    (RingHom.ker (e.q.hom.hom : X'.obj →+* X.obj)) ℓ).comp ?_)
  exact (LinearEquiv.rTensor F
    ((LinearEquiv.ofEq _ _ (Der_eq_sqDer hℓ)).restrictScalars A')).bijective.comp
    (LinearEquiv.bijective _)

end DerBC

/-! ### Linear maps out of a quotient by a submodule over a larger ring -/

section LiftQ

variable {R M M₂ : Type u} [CommRing R] [Algebra A' R] [AddCommGroup M] [Module R M]
  [Module A' M] [IsScalarTower A' R M] [AddCommGroup M₂] [Module A' M₂]

/-- An `A'`-linear map killing an `R`-submodule factors through the quotient. -/
noncomputable def liftQA' (p : Submodule R M) (f : M →ₗ[A'] M₂) (h : ∀ x ∈ p, f x = 0) :
    M ⧸ p →ₗ[A'] M₂ :=
  (p.restrictScalars A').liftQ f (fun x hx ↦ h x hx) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv A' p).symm.toLinearMap

/-- `liftQA' p f h` sends the class of `x` to `f x`. -/
@[simp] theorem liftQA'_mk (p : Submodule R M) (f : M →ₗ[A'] M₂) (h : ∀ x ∈ p, f x = 0) (x : M) :
    liftQA' p f h (Submodule.Quotient.mk x) = f x := rfl

variable (A') in
/-- The quotient map, as an `A'`-linear map. -/
abbrev mkQA' (p : Submodule R M) : M →ₗ[A'] M ⧸ p := (p.mkQ).restrictScalars A'

end LiftQ

/-! ### The base change of `Mod` -/

section ModBC

variable {X' X Y : SmallAlg A' κ} {e : SqZero X' X} {F : Type u} [CommRing F] [Algebra A' F]
  {hY : Cardinal.mk (X'.obj ⊗[A'] F) < κ} {e₂ : SqZero (SmallAlg.mk (X'.obj ⊗[A'] F) hY) Y}
  {φ : SqZero.Hom e e₂} (hB : IsBaseChange e F e₂ φ)
  {P : Type u} [CommRing P] [Algebra A' P] {G : Groupoid A' κ P}
  [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' F]

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' F] in
/-- Equal derivations have equal classes in `Mod`. -/
theorem mkMod_congr {C' C : SmallAlg A' κ} {e : SqZero C' C} {w : P →ₐ[A'] C.obj}
    {D D' : P →ₗ[A'] C'.obj} (h : D = D') (hD : D ∈ Der e w) (hD' : D' ∈ Der e w) :
    (mkMod (G := G) D hD : Mod G e w) = mkMod D' hD' := by
  subst h
  rfl

variable (G) in
/-- The quotient map onto `Mod`, as an `A'`-linear map. -/
noncomputable def modπ {C' C : SmallAlg A' κ} (e : SqZero C' C) (w : P →ₐ[A'] C.obj) :
    Der e w →ₗ[A'] Mod G e w :=
  (((S G e w).comap (Der e w).subtype).mkQ).restrictScalars A'

omit [Module.FinitePresentation P Ω[P⁄A']] in
/-- `modπ` sends a derivation `D` to its class `mkMod D.1 D.2`. -/
theorem modπ_apply {C' C : SmallAlg A' κ} (e : SqZero C' C) (w : P →ₐ[A'] C.obj)
    (D : Der e w) : modπ G e w D = mkMod D.1 D.2 := rfl

omit [Module.FinitePresentation P Ω[P⁄A']] in
/-- The quotient map `modπ` onto `Mod` is surjective. -/
theorem modπ_surjective {C' C : SmallAlg A' κ} (e : SqZero C' C) (w : P →ₐ[A'] C.obj) :
    Function.Surjective (modπ G e w) := fun y ↦ by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨x, rfl⟩

omit [Module.FinitePresentation P Ω[P⁄A']] in
/-- A derivation lies in the kernel of `modπ` if and only if it lies in `S`. -/
theorem modπ_eq_zero_iff {C' C : SmallAlg A' κ} (e : SqZero C' C) (w : P →ₐ[A'] C.obj)
    (D : Der e w) : modπ G e w D = 0 ↔ D.1 ∈ S G e w :=
  mkMod_eq_zero_iff D.2

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' F] in
/-- `derBC` carries `f ⊗ D` into `S G e₂ w₂` whenever `D` lies in `S G e w`. -/
theorem derBC_mem_S {w : P →ₐ[A'] X.obj} (ℓ : P →ₐ[A'] X'.obj) (hℓ : e.q.hom.hom.comp ℓ = w)
    {w₂ : P →ₐ[A'] Y.obj} (hw : φ.bot.hom.hom.comp w = w₂) (f : F) (D : Der e w)
    (hD : D.1 ∈ S G e w) : (derBC hB ℓ hℓ hw (f ⊗ₜ D)).1 ∈ S G e₂ w₂ := by
  rw [derBC_tmul]
  exact Submodule.smul_mem _ _ (mem_S_postcomp φ hw hD)

/-- `m ↦ (1 ⊗ f) • φ(m)`. -/
noncomputable def modBCAt {w : P →ₐ[A'] X.obj} {w₂ : P →ₐ[A'] Y.obj}
    (hw : φ.bot.hom.hom.comp w = w₂) (f : F) : Mod G e w →ₗ[A'] Mod G e₂ w₂ where
  toFun m := ((1 : X'.obj) ⊗ₜ[A'] f : X'.obj ⊗[A'] F) • modMap φ hw m
  map_add' m m' := by rw [map_add, smul_add]
  map_smul' a m := by
    have h1 : modMap φ hw (a • m) =
        (algebraMap A' (X'.obj ⊗[A'] F) a) • modMap φ hw m := by
      rw [← IsScalarTower.algebraMap_smul (A := (X'.obj : Type u)) a m, map_smulₛₗ]
      congr 1
      exact φ.top.hom.hom.commutes a
    have h2 : ∀ z : Mod G e₂ w₂, (algebraMap A' (X'.obj ⊗[A'] F) a) • z = a • z := fun z ↦
      IsScalarTower.algebraMap_smul (A := (X'.obj ⊗[A'] F : Type u)) a z
    rw [RingHom.id_apply, h1, smul_comm, h2]

/-- **The base change of `Mod`**: `f ⊗ m ↦ (1 ⊗ f) • φ(m)`. -/
noncomputable def modBC {w : P →ₐ[A'] X.obj} {w₂ : P →ₐ[A'] Y.obj}
    (hw : φ.bot.hom.hom.comp w = w₂) : F ⊗[A'] Mod G e w →ₗ[A'] Mod G e₂ w₂ :=
  TensorProduct.lift
    { toFun := fun f ↦ modBCAt (G := G) (hY := hY) hw f
      map_add' := fun f f' ↦ LinearMap.ext fun m ↦ by
        change ((1 : X'.obj) ⊗ₜ[A'] (f + f') : X'.obj ⊗[A'] F) • modMap φ hw m =
          ((1 : X'.obj) ⊗ₜ[A'] f : X'.obj ⊗[A'] F) • modMap φ hw m +
            ((1 : X'.obj) ⊗ₜ[A'] f' : X'.obj ⊗[A'] F) • modMap φ hw m
        rw [TensorProduct.tmul_add, add_smul]
      map_smul' := fun a f ↦ LinearMap.ext fun m ↦ by
        change ((1 : X'.obj) ⊗ₜ[A'] (a • f) : X'.obj ⊗[A'] F) • modMap φ hw m =
          a • (((1 : X'.obj) ⊗ₜ[A'] f : X'.obj ⊗[A'] F) • modMap φ hw m)
        rw [TensorProduct.tmul_smul, smul_assoc] }

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' F] in
/-- `modBC` sends `f ⊗ m` to `(1 ⊗ f) • modMap φ hw m`. -/
theorem modBC_tmul {w : P →ₐ[A'] X.obj} {w₂ : P →ₐ[A'] Y.obj}
    (hw : φ.bot.hom.hom.comp w = w₂) (f : F) (m : Mod G e w) :
    modBC (G := G) (hY := hY) hw (f ⊗ₜ m) =
      ((1 : X'.obj) ⊗ₜ[A'] f : X'.obj ⊗[A'] F) • modMap φ hw m := rfl

include hB in
omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' F] in
/-- `modBC` and `derBC` commute with the quotient maps `modπ`. -/
theorem modBC_comp_mk {w : P →ₐ[A'] X.obj} (ℓ : P →ₐ[A'] X'.obj) (hℓ : e.q.hom.hom.comp ℓ = w)
    {w₂ : P →ₐ[A'] Y.obj} (hw : φ.bot.hom.hom.comp w = w₂) (x : F ⊗[A'] Der e w) :
    modBC (G := G) (hY := hY) hw (LinearMap.lTensor F (modπ G e w) x) =
      modπ G e₂ w₂ (derBC hB ℓ hℓ hw x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul f D =>
    exact (congrArg (fun z : Der e₂ w₂ ↦ (Submodule.Quotient.mk z : Mod G e₂ w₂))
      (Subtype.ext (derBC_tmul hB ℓ hℓ hw f D))).symm

variable {Q : Type u} [CommRing Q] [Algebra A' Q] [Module.FinitePresentation Q Ω[Q⁄A']]

/-- Precomposition, as a linear map of derivation modules. -/
def precompDer {C' C : SmallAlg A' κ} (e : SqZero C' C) (σ : P →ₐ[A'] Q) {v : Q →ₐ[A'] C.obj}
    {w : P →ₐ[A'] C.obj} (h : v.comp σ = w) : Der e v →ₗ[C'.obj] Der e w :=
  (precomp C' σ).restrict fun _ hE ↦ Der.comp hE σ h

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' F]
  [Module.FinitePresentation Q Ω[Q⁄A']] in
/-- Postcomposition with `φ` commutes with precomposition by `σ`. -/
theorem postcomp_comp (σ : P →ₐ[A'] Q) (E : Q →ₗ[A'] X'.obj) :
    postcomp φ (E.comp σ.toLinearMap) = (postcomp φ E).comp σ.toLinearMap := rfl

include hB in
omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' F]
  [Module.FinitePresentation Q Ω[Q⁄A']] in
/-- `derBC` commutes with precomposition by `σ`. -/
theorem derBC_precomp (σ : P →ₐ[A'] Q) {v : Q →ₐ[A'] X.obj} {w : P →ₐ[A'] X.obj}
    (h : v.comp σ = w) (m : Q →ₐ[A'] X'.obj) (hm : e.q.hom.hom.comp m = v)
    {v₂ : Q →ₐ[A'] Y.obj} (hv : φ.bot.hom.hom.comp v = v₂)
    {w₂ : P →ₐ[A'] Y.obj} (hw : φ.bot.hom.hom.comp w = w₂) (h₂ : v₂.comp σ = w₂)
    (x : F ⊗[A'] Der e v) :
    derBC hB (m.comp σ) (by rw [← AlgHom.comp_assoc, hm, h]) hw
        ((precompDer e σ h).restrictScalars A' |>.lTensor F x) =
      precompDer e₂ σ h₂ (derBC hB m hm hv x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul f E =>
    apply Subtype.ext
    rw [LinearMap.lTensor_tmul, derBC_tmul]
    show _ = ((derBC hB m hm hv (f ⊗ₜ E) : Der e₂ v₂) : Q →ₗ[A'] (X'.obj ⊗[A'] F)).comp
      σ.toLinearMap
    rw [derBC_tmul]
    rfl

include hB in
omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' F]
  [Module.FinitePresentation Q Ω[Q⁄A']] in
/-- `derBC` does not depend on the lift. -/
theorem derBC_congr {w : P →ₐ[A'] X.obj} (ℓ ℓ' : P →ₐ[A'] X'.obj)
    (hℓ : e.q.hom.hom.comp ℓ = w) (hℓ' : e.q.hom.hom.comp ℓ' = w)
    {w₂ : P →ₐ[A'] Y.obj} (hw : φ.bot.hom.hom.comp w = w₂) :
    derBC hB ℓ hℓ hw = derBC hB ℓ' hℓ' hw := by
  refine TensorProduct.ext' fun f D ↦ Subtype.ext ?_
  rw [derBC_tmul, derBC_tmul]

variable {b : Chart G.arr Q} (hb : b.IsFormallyEtale) {sV tV : P →ₐ[A'] Q}
  (hsV : ∀ (C : SmallAlg A' κ) (v : Q →ₐ[A'] C.obj), G.src (b.app C v) = v.comp sV)
  (htV : ∀ (C : SmallAlg A' κ) (v : Q →ₐ[A'] C.obj), G.tgt (b.app C v) = v.comp tV)

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' F] in
/-- `F ⊗ modπ` vanishes on the image of `F ⊗ S`. -/
theorem lTensor_modπ_S {w : P →ₐ[A'] X.obj}
    (z₁ : F ⊗[A'] ((S G e w).comap (Der e w).subtype)) :
    LinearMap.lTensor F (modπ G e w)
      (LinearMap.lTensor F (((S G e w).comap (Der e w).subtype).subtype.restrictScalars A') z₁) =
      0 := by
  induction z₁ using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  | tmul f sv =>
    rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
    have : modπ G e w (((S G e w).comap (Der e w).subtype).subtype.restrictScalars A' sv) = 0 :=
      (modπ_eq_zero_iff e w _).mpr sv.2
    rw [this, TensorProduct.tmul_zero]

include hB in
/-- Injectivity of `modBC` from the comparison of the submodules `S`. -/
theorem modBC_injective_of {w : P →ₐ[A'] X.obj} (ℓ : P →ₐ[A'] X'.obj)
    (hℓ : e.q.hom.hom.comp ℓ = w) {w₂ : P →ₐ[A'] Y.obj} (hw : φ.bot.hom.hom.comp w = w₂)
    (key : ∀ d : Der e₂ w₂, d.1 ∈ S G e₂ w₂ → ∃ z₀ ∈ LinearMap.range
      (LinearMap.lTensor F (((S G e w).comap (Der e w).subtype).subtype.restrictScalars A')),
        derBC hB ℓ hℓ hw z₀ = d) :
    Function.Injective (modBC (G := G) (hY := hY) hw) := by
  refine LinearMap.ker_eq_bot.mp ((LinearMap.ker_eq_bot').mpr fun x hx ↦ ?_)
  obtain ⟨z, rfl⟩ := LinearMap.lTensor_surjective F (modπ_surjective (G := G) e w) x
  obtain ⟨z₀, ⟨z₁, rfl⟩, hβ⟩ :=
    key _ ((modπ_eq_zero_iff e₂ w₂ _).mp ((modBC_comp_mk hB ℓ hℓ hw z).symm.trans hx))
  rw [← (derBC_bijective hB ℓ hℓ hw).1 hβ]
  exact lTensor_modπ_S z₁

include hB hb hsV htV in
/-- The differences of related lifts upstairs come from downstairs. -/
theorem modBC_key {w : P →ₐ[A'] X.obj} (ℓ : P →ₐ[A'] X'.obj)
    (hℓ : e.q.hom.hom.comp ℓ = w) {w₂ : P →ₐ[A'] Y.obj} (hw : φ.bot.hom.hom.comp w = w₂)
    {v : Q →ₐ[A'] X.obj} (hv : b.app X v = G.idt w) (m : Q →ₐ[A'] X'.obj)
    (hm : e.q.hom.hom.comp m = v) :
    ∀ d : Der e₂ w₂, d.1 ∈ S G e₂ w₂ → ∃ z₀ ∈ LinearMap.range
      (LinearMap.lTensor F (((S G e w).comap (Der e w).subtype).subtype.restrictScalars A')),
        derBC hB ℓ hℓ hw z₀ = d := by
  have hv₂ : b.app Y (φ.bot.hom.hom.comp v) = G.idt w₂ := by
    rw [← b.natural, hv, G.idt_map, hw]
  have hsv : v.comp sV = w := by rw [← hsV, hv, G.src_idt]
  have htv : v.comp tV = w := by rw [← htV, hv, G.tgt_idt]
  have hsv₂ : (φ.bot.hom.hom.comp v).comp sV = w₂ := by rw [← hsV, hv₂, G.src_idt]
  have htv₂ : (φ.bot.hom.hom.comp v).comp tV = w₂ := by rw [← htV, hv₂, G.tgt_idt]
  have hℓ₂ : e₂.q.hom.hom.comp (φ.top.hom.hom.comp ℓ) = w₂ := by
    rw [SqZero.Hom.w_comp, hℓ, hw]
  intro d hd
  rw [S_eq_map_K b hb sV tV hsV htV hv₂ hℓ₂] at hd
  obtain ⟨k, hk, hkd⟩ := hd
  obtain ⟨zQ, hzQ⟩ := (derBC_bijective hB m hm (rfl : φ.bot.hom.hom.comp v = _)).2 ⟨k, hk.1⟩
  have hker : LinearMap.lTensor F ((precompDer e sV hsv).restrictScalars A') zQ = 0 := by
    apply (derBC_bijective hB (m.comp sV) (by rw [← AlgHom.comp_assoc, hm, hsv]) hw).1
    rw [derBC_precomp hB sV hsv m hm rfl hw hsv₂, hzQ, map_zero]
    exact Subtype.ext (LinearMap.mem_ker.mp hk.2)
  have hex := Module.Flat.lTensor_exact F
    (LinearMap.exact_subtype_ker_map ((precompDer e sV hsv).restrictScalars A'))
  obtain ⟨zK, hzK⟩ := (hex zQ).mp hker
  have hS : ∀ E ∈ LinearMap.ker ((precompDer e sV hsv).restrictScalars A'),
      ((precompDer e tV htv) E).1 ∈ S G e w := by
    intro E hE
    rw [S_eq_map_K b hb sV tV hsV htV hv hℓ]
    exact ⟨E.1, ⟨E.2, LinearMap.mem_ker.mpr (congrArg Subtype.val (LinearMap.mem_ker.mp hE))⟩,
      rfl⟩
  let μ : LinearMap.ker ((precompDer e sV hsv).restrictScalars A') →ₗ[A']
      ((S G e w).comap (Der e w).subtype) :=
    { toFun := fun E ↦ ⟨(precompDer e tV htv) E.1, hS E.1 E.2⟩
      map_add' := fun E E' ↦ Subtype.ext (map_add _ _ _)
      map_smul' := fun a E ↦ Subtype.ext (by
        show (precompDer e tV htv) (a • E.1) = a • (precompDer e tV htv) E.1
        rw [← IsScalarTower.algebraMap_smul (A := (X'.obj : Type u)) a E.1, map_smul,
          IsScalarTower.algebraMap_smul]) }
  refine ⟨LinearMap.lTensor F (((S G e w).comap (Der e w).subtype).subtype.restrictScalars A')
    (LinearMap.lTensor F μ zK), ⟨_, rfl⟩, ?_⟩
  rw [← LinearMap.comp_apply (LinearMap.lTensor F _), ← LinearMap.lTensor_comp]
  have hfac : (((S G e w).comap (Der e w).subtype).subtype.restrictScalars A') ∘ₗ μ =
      ((precompDer e tV htv).restrictScalars A') ∘ₗ
        (LinearMap.ker ((precompDer e sV hsv).restrictScalars A')).subtype := rfl
  rw [hfac, LinearMap.lTensor_comp, LinearMap.comp_apply, hzK,
    derBC_congr hB ℓ (m.comp tV) hℓ (by rw [← AlgHom.comp_assoc, hm, htv]) hw,
    derBC_precomp hB tV htv m hm rfl hw htv₂, hzQ]
  exact Subtype.ext hkd

include hB hb hsV htV in
/-- **The flat base change of `Mod` is bijective**, given the chart near the identity. -/
theorem modBC_bijective {w : P →ₐ[A'] X.obj} (ℓ : P →ₐ[A'] X'.obj)
    (hℓ : e.q.hom.hom.comp ℓ = w) {w₂ : P →ₐ[A'] Y.obj} (hw : φ.bot.hom.hom.comp w = w₂)
    {v : Q →ₐ[A'] X.obj} (hv : b.app X v = G.idt w) (m : Q →ₐ[A'] X'.obj)
    (hm : e.q.hom.hom.comp m = v) :
    Function.Bijective (modBC (G := G) (hY := hY) hw) := by
  refine ⟨modBC_injective_of hB ℓ hℓ hw (modBC_key hB hb hsV htV ℓ hℓ hw hv m hm), fun y ↦ ?_⟩
  obtain ⟨d, rfl⟩ := modπ_surjective e₂ w₂ y
  obtain ⟨z, rfl⟩ := (derBC_bijective hB ℓ hℓ hw).2 d
  exact ⟨_, modBC_comp_mk (G := G) hB ℓ hℓ hw z⟩

end ModBC

end AlgebraicGeometry.Stack.GroupoidLift

end
