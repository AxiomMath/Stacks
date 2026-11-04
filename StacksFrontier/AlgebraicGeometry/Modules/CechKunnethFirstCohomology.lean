module

public import StacksFrontier.LinearAlgebra.TensorProduct.FirstCohomologyKunneth
public import StacksFrontier.AlgebraicGeometry.Pushout.FlatSectionsDescent
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleBaseRing
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleDegreeZero

/-!
# Künneth injectivity on first Čech cohomology for a product cover

Let `X` and `Y` be schemes over a ring `A`, let `P = X ×_A Y` with projections `r` and `q`, and
let `U` and `V` be covers of `X` and `Y` by affine opens all of whose finite intersections are
affine. The opens `r⁻¹ U_a ∩ q⁻¹ V_b` cover `P`, and the sections of `𝒪_P` over them are the
tensor products `Γ(U_a) ⊗_A Γ(V_b)`.

## Main results

* `Stacks.Cech.Kunneth.bijective_productMap`: over affine opens `U ⊆ X`, `V ⊆ Y` with affine
  `r⁻¹ U ∩ q⁻¹ V`, the map `Γ(U) ⊗_A Γ(V) → Γ(r⁻¹ U ∩ q⁻¹ V)`, `s ⊗ t ↦ r^* s · q^* t`, is
  bijective.
* `Stacks.Cech.Kunneth.bijective_psi`, `psi_rTensor`, `psi_lTensor`: the tensor product of the Čech
  complexes of `U` and `V` is the bicomplex of sections over the boxes, compatibly with both
  differentials.
* `Stacks.Cech.Kunneth.exists_cechD_eq_of_faces`: over a field, with `Γ(X, 𝒪) = k = Γ(Y, 𝒪)` and
  rational points, a Čech `1`-cocycle of `𝒪_P` on the box cover whose pullbacks to the two faces
  through the points are coboundaries is a coboundary. This is the injectivity of
  `H¹(X × Y, 𝒪) → H¹(X, 𝒪) ⊕ H¹(Y, 𝒪)` of [Stacks, Tag 0BED] which the proof of
  [Stacks, Tag 0BF3] uses, on Čech cocycles.

## Implementation notes

The proof passes from the diagonal Čech complex of the box cover to the bicomplex of sections over
pairs of tuples, `Bi r q U V m n`, only in degrees at most one (`to10`, `to01`, `from00`, with
`dh_to10`, `dv_to10`, `cechD_from00`), and from the bicomplex to the tensor product of the two
Čech complexes through `psi`; the algebra is then
`StacksDraft.KunnethOne.exists_eq_of_faces`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

namespace Stacks.Cech.Kunneth

section General

variable {A : Type u} [CommRing A]

/-- The structural map of the source of a composite is the composite of the structural map with
the restriction. -/
theorem baseRingHom_comp_appLE {X P : Scheme.{u}} (r : P ⟶ X) (f : X ⟶ Spec (.of A))
    (U : X.Opens) (W : P.Opens) (h : W ≤ r ⁻¹ᵁ U) :
    baseRingHom f U ≫ r.appLE U W h = baseRingHom (r ≫ f) W := by
  rw [baseRingHom_eq_appLE f U (by simp), baseRingHom_eq_appLE (r ≫ f) W (by simp)]
  exact (Category.assoc _ _ _).trans (congrArg (toSpecΓ (CommRingCat.of A) ≫ ·)
    (Scheme.Hom.appLE_comp_appLE r f ⊤ U W _ h))

/-- The restriction `Γ(X, U) ⟶ Γ(P, W)` along `r`, as a homomorphism of algebras over the base,
for a structure map `fP` of `P` equal to `r ≫ f`. -/
def appLEAlgHom {X P : Scheme.{u}} (r : P ⟶ X) (f : X ⟶ Spec (.of A)) (fP : P ⟶ Spec (.of A))
    (hr : r ≫ f = fP) (U : X.Opens) (W : P.Opens) (h : W ≤ r ⁻¹ᵁ U) :
    letI := baseAlgebra f U
    letI := baseAlgebra fP W
    Γ(X, U) →ₐ[A] Γ(P, W) :=
  letI := baseAlgebra f U
  letI := baseAlgebra fP W
  { (r.appLE U W h).hom with
    commutes' := fun a => by
      subst hr
      exact congrArg (fun φ : CommRingCat.of A ⟶ Γ(P, W) => φ.hom a)
        (baseRingHom_comp_appLE r f U W h) }

/-- `appLEAlgHom` is the restriction map `r.appLE U W h` on elements. -/
@[simp]
theorem appLEAlgHom_apply {X P : Scheme.{u}} (r : P ⟶ X) (f : X ⟶ Spec (.of A))
    (fP : P ⟶ Spec (.of A)) (hr : r ≫ f = fP) (U : X.Opens) (W : P.Opens) (h : W ≤ r ⁻¹ᵁ U)
    (s : Γ(X, U)) :
    letI := baseAlgebra f U
    letI := baseAlgebra fP W
    appLEAlgHom r f fP hr U W h s = (r.appLE U W h).hom s := rfl

variable {X Y P : Scheme.{u}} {f : X ⟶ Spec (.of A)} {g : Y ⟶ Spec (.of A)} {r : P ⟶ X}
  {q : P ⟶ Y} (H : IsPullback r q f g)

/-- **Sections of a fibre product over a product of affine opens.** For affine opens `U ⊆ X` and
`V ⊆ Y` such that `W = r⁻¹ U ∩ q⁻¹ V` is affine, `s ⊗ t ↦ r^* s · q^* t` is a bijection
`Γ(X, U) ⊗_A Γ(Y, V) → Γ(P, W)`. -/
def productMap (U : X.Opens) (V : Y.Opens) (W : P.Opens) (hU : W ≤ r ⁻¹ᵁ U)
    (hV : W ≤ q ⁻¹ᵁ V) :
    letI := baseAlgebra f U
    letI := baseAlgebra g V
    letI := baseAlgebra (r ≫ f) W
    Γ(X, U) ⊗[A] Γ(Y, V) →ₐ[A] Γ(P, W) :=
  letI := baseAlgebra f U
  letI := baseAlgebra g V
  letI := baseAlgebra (r ≫ f) W
  Algebra.TensorProduct.productMap (appLEAlgHom r f (r ≫ f) rfl U W hU)
    (appLEAlgHom q g (r ≫ f) H.w.symm V W hV)

/-- `productMap` on pure tensors. -/
theorem productMap_tmul (U : X.Opens) (V : Y.Opens) (W : P.Opens) (hU : W ≤ r ⁻¹ᵁ U)
    (hV : W ≤ q ⁻¹ᵁ V) (s : Γ(X, U)) (t : Γ(Y, V)) :
    letI := baseAlgebra f U
    letI := baseAlgebra g V
    letI := baseAlgebra (r ≫ f) W
    productMap H U V W hU hV (s ⊗ₜ t) = (r.appLE U W hU).hom s * (q.appLE V W hV).hom t := rfl

/-- **`productMap` is bijective** over affine opens with affine intersection. -/
theorem bijective_productMap (U : X.Opens) (V : Y.Opens) (W : P.Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hWUV : W = r ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V) :
    Function.Bijective (productMap H U V W (hWUV ▸ inf_le_left) (hWUV ▸ inf_le_right)) := by
  let := baseAlgebra f U
  let := baseAlgebra g V
  let := baseAlgebra (r ≫ f) W
  let : Algebra Γ(X, U) Γ(P, W) := (r.appLE U W (hWUV ▸ inf_le_left)).hom.toAlgebra
  let : Algebra Γ(Y, V) Γ(P, W) := (q.appLE V W (hWUV ▸ inf_le_right)).hom.toAlgebra
  have : IsScalarTower A Γ(X, U) Γ(P, W) := IsScalarTower.of_algebraMap_eq' (by
    have := congrArg CommRingCat.Hom.hom (baseRingHom_comp_appLE r f U W (hWUV ▸ inf_le_left))
    rw [CommRingCat.hom_comp] at this
    exact this.symm)
  have : IsScalarTower A Γ(Y, V) Γ(P, W) := IsScalarTower.of_algebraMap_eq' (by
    have := congrArg CommRingCat.Hom.hom (baseRingHom_comp_appLE q g V W (hWUV ▸ inf_le_right))
    rw [CommRingCat.hom_comp, ← H.w] at this
    exact this.symm)
  have hpush := isPushout_appLE_of_isPullback_of_isAffineOpen H ⊤ (isAffineOpen_top _) V hV
    (by simp) U hU (by simp) W hWUV hW
  have hps : Algebra.IsPushout A Γ(X, U) Γ(Y, V) Γ(P, W) := by
    refine (CommRingCat.isPushout_iff_isPushout (R := A) (R' := Γ(X, U)) (S := Γ(Y, V))
      (S' := Γ(P, W))).mp ?_
    refine hpush.flip.of_iso (Scheme.ΓSpecIso (CommRingCat.of A)) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ ?_ ?_
    · change _ ≫ 𝟙 _ = (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U _)
      rw [Iso.hom_inv_id_assoc, Category.comp_id]
      rfl
    · change _ ≫ 𝟙 _ = (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g.appLE ⊤ V _)
      rw [Iso.hom_inv_id_assoc, Category.comp_id]
      rfl
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
  have heq : ∀ x, productMap H U V W (hWUV ▸ inf_le_left) (hWUV ▸ inf_le_right) x =
      Algebra.IsPushout.equiv A Γ(X, U) Γ(Y, V) Γ(P, W) x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s t => rw [Algebra.IsPushout.equiv_tmul, productMap_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [show ⇑(productMap H U V W (hWUV ▸ inf_le_left) (hWUV ▸ inf_le_right)) =
    ⇑(Algebra.IsPushout.equiv A Γ(X, U) Γ(Y, V) Γ(P, W)) from funext heq]
  exact (Algebra.IsPushout.equiv A Γ(X, U) Γ(Y, V) Γ(P, W)).bijective

/-! ### Sections of `𝒪` as modules over the base, two ways -/

/-- The structure sheaf of a scheme, as a module over itself. -/
abbrev OM (T : Scheme.{u}) : T.Modules := SheafOfModules.unit T.ringCatSheaf

/-- The sections of `𝒪_T` with the module structure of `Stacks.Cech.sectionsModule` are the
sections of the ring `Γ(T, W)` with the module structure of `Stacks.Cech.baseAlgebra`. -/
def secEquiv {T : Scheme.{u}} (h : T ⟶ Spec (.of A)) (W : T.Opens) :
    letI := sectionsModule h (OM T) W
    letI := baseAlgebra h W
    Γ(OM T, W) ≃ₗ[A] Γ(T, W) :=
  letI := sectionsModule h (OM T) W
  letI := baseAlgebra h W
  { toFun := fun x => x
    invFun := fun x => x
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- `productMap` on sections of the structure modules. -/
def productMap' (U : X.Opens) (V : Y.Opens) (W : P.Opens) (hU : W ≤ r ⁻¹ᵁ U)
    (hV : W ≤ q ⁻¹ᵁ V) :
    letI := sectionsModule f (OM X) U
    letI := sectionsModule g (OM Y) V
    letI := sectionsModule (r ≫ f) (OM P) W
    Γ(OM X, U) ⊗[A] Γ(OM Y, V) →ₗ[A]
      Γ(OM P, W) :=
  letI := sectionsModule f (OM X) U
  letI := sectionsModule g (OM Y) V
  letI := sectionsModule (r ≫ f) (OM P) W
  letI := baseAlgebra f U
  letI := baseAlgebra g V
  letI := baseAlgebra (r ≫ f) W
  (secEquiv (r ≫ f) W).symm.toLinearMap ∘ₗ (productMap H U V W hU hV).toLinearMap ∘ₗ
    (TensorProduct.congr (secEquiv f U) (secEquiv g V)).toLinearMap

/-- `productMap'` sends `s ⊗ₜ t` to the product of the restriction of `s` along `r` and the
restriction of `t` along `q`. -/
theorem productMap'_tmul (U : X.Opens) (V : Y.Opens) (W : P.Opens) (hU : W ≤ r ⁻¹ᵁ U)
    (hV : W ≤ q ⁻¹ᵁ V) (s : Γ(OM X, U))
    (t : Γ(OM Y, V)) :
    letI := sectionsModule f (OM X) U
    letI := sectionsModule g (OM Y) V
    letI := sectionsModule (r ≫ f) (OM P) W
    productMap' H U V W hU hV (s ⊗ₜ t) =
      (show Γ(P, W) from (r.appLE U W hU).hom s * (q.appLE V W hV).hom t) := rfl

/-- For affine opens `U`, `V` and an affine `W = r⁻¹ U ⊓ q⁻¹ V`, `productMap'` is bijective. -/
theorem bijective_productMap' (U : X.Opens) (V : Y.Opens) (W : P.Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hWUV : W = r ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V) :
    Function.Bijective (productMap' H U V W (hWUV ▸ inf_le_left) (hWUV ▸ inf_le_right)) := by
  let := sectionsModule f (OM X) U
  let := sectionsModule g (OM Y) V
  let := sectionsModule (r ≫ f) (OM P) W
  let := baseAlgebra f U
  let := baseAlgebra g V
  let := baseAlgebra (r ≫ f) W
  exact (secEquiv (r ≫ f) W).symm.bijective.comp ((bijective_productMap H U V W hU hV hW hWUV).comp
    (TensorProduct.congr (secEquiv f U) (secEquiv g V)).bijective)

/-! ### The bicomplex of a product cover -/

variable (r q) {I J : Type u} (U : I → X.Opens) (V : J → Y.Opens)

/-- The box `r⁻¹ U_a ∩ q⁻¹ V_b` over a pair of tuples of indices. -/
abbrev box {m n : ℕ} (a : Fin m → I) (b : Fin n → J) : P.Opens :=
  r ⁻¹ᵁ CechCochains.inter U a ⊓ q ⁻¹ᵁ CechCochains.inter V b

/-- The terms of the bicomplex: sections of `𝒪_P` over all boxes of bidegree `(m, n)`. -/
abbrev Bi (m n : ℕ) : Type u :=
  ∀ (a : Fin (m + 1) → I) (b : Fin (n + 1) → J),
    Γ(OM P, box r q U V a b)

/-- The terms of the bicomplex are abelian groups under pointwise addition. -/
instance (m n : ℕ) : AddCommGroup (Bi r q U V m n) := by unfold Bi; infer_instance

/-- The module structure on the bicomplex over the base. -/
@[instance_reducible]
def biModule (fP : P ⟶ Spec (.of A)) (m n : ℕ) : Module A (Bi r q U V m n) :=
  letI : ∀ (a : Fin (m + 1) → I) (b : Fin (n + 1) → J),
      Module A Γ(OM P, box r q U V a b) :=
    fun _ _ => sectionsModule fP _ _
  inferInstanceAs (Module A (∀ (a : Fin (m + 1) → I) (b : Fin (n + 1) → J),
    Γ(OM P, box r q U V a b)))

variable {r q}

/-- **The comparison `Č^m(U) ⊗ Č^n(V) → Bi^{m,n}`**, `c ⊗ d ↦ (r^* c_a · q^* d_b)_{a,b}`. -/
def psi (m n : ℕ) :
    letI := cochainModule f U (OM X) m
    letI := cochainModule g V (OM Y) n
    letI := biModule r q U V (r ≫ f) m n
    CechCochains.Cochain U (OM X).presheaf m ⊗[A]
      CechCochains.Cochain V (OM Y).presheaf n →ₗ[A]
      Bi r q U V m n :=
  letI := cochainModule f U (OM X) m
  letI := cochainModule g V (OM Y) n
  letI : ∀ (a : Fin (m + 1) → I) (b : Fin (n + 1) → J),
      Module A Γ(OM P, box r q U V a b) :=
    fun _ _ => sectionsModule (r ≫ f) _ _
  letI : ∀ a : Fin (m + 1) → I,
      Module A Γ(OM X, CechCochains.inter U a) :=
    fun _ => sectionsModule f _ _
  letI : ∀ b : Fin (n + 1) → J,
      Module A Γ(OM Y, CechCochains.inter V b) :=
    fun _ => sectionsModule g _ _
  LinearMap.pi fun a => LinearMap.pi fun b =>
    productMap' H (CechCochains.inter U a) (CechCochains.inter V b) (box r q U V a b)
      inf_le_left inf_le_right ∘ₗ TensorProduct.map (LinearMap.proj a) (LinearMap.proj b)

/-- `psi` sends `c ⊗ₜ d` to the family whose component over the box at `(a, b)` is the product of
the restriction of `c a` along `r` and the restriction of `d b` along `q`. -/
theorem psi_tmul (m n : ℕ) (c : CechCochains.Cochain U (OM X).presheaf m)
    (d : CechCochains.Cochain V (OM Y).presheaf n)
    (a : Fin (m + 1) → I) (b : Fin (n + 1) → J) :
    letI := cochainModule f U (OM X) m
    letI := cochainModule g V (OM Y) n
    psi H U V m n (c ⊗ₜ d) a b = (show Γ(P, box r q U V a b) from
      (r.appLE _ _ inf_le_left).hom (c a) * (q.appLE _ _ inf_le_right).hom (d b)) := rfl

/-- For finite index types, with affine intersections in `U` and `V` and affine boxes, `psi` is
bijective. -/
theorem bijective_psi [Finite I] [Finite J] (m n : ℕ)
    (hU : ∀ a : Fin (m + 1) → I, IsAffineOpen (CechCochains.inter U a))
    (hV : ∀ b : Fin (n + 1) → J, IsAffineOpen (CechCochains.inter V b))
    (hW : ∀ (a : Fin (m + 1) → I) (b : Fin (n + 1) → J), IsAffineOpen (box r q U V a b)) :
    Function.Bijective (psi H U V m n) := by
  classical
  have := Fintype.ofFinite I
  have := Fintype.ofFinite J
  let := cochainModule f U (OM X) m
  let := cochainModule g V (OM Y) n
  let : ∀ (a : Fin (m + 1) → I) (b : Fin (n + 1) → J),
      Module A Γ(OM P, box r q U V a b) :=
    fun _ _ => sectionsModule (r ≫ f) _ _
  let : ∀ a : Fin (m + 1) → I,
      Module A Γ(OM X, CechCochains.inter U a) :=
    fun _ => sectionsModule f _ _
  let : ∀ b : Fin (n + 1) → J,
      Module A Γ(OM Y, CechCochains.inter V b) :=
    fun _ => sectionsModule g _ _
  let e := (TensorProduct.piLeft (R := A)
      (N := CechCochains.Cochain V (OM Y).presheaf n)
      (M := fun a : Fin (m + 1) → I =>
        Γ(OM X, CechCochains.inter U a))).trans
    (LinearEquiv.piCongrRight fun a => TensorProduct.piRight (R := A) (S := A)
      (N := Γ(OM X, CechCochains.inter U a))
      (M := fun b : Fin (n + 1) → J =>
        Γ(OM Y, CechCochains.inter V b)))
  have hΦ : psi H U V m n = (LinearMap.pi fun a => LinearMap.pi fun b =>
      productMap' H (CechCochains.inter U a) (CechCochains.inter V b) (box r q U V a b)
        inf_le_left inf_le_right ∘ₗ (LinearMap.proj b ∘ₗ LinearMap.proj a)) ∘ₗ e.toLinearMap :=
    TensorProduct.ext' fun c d => rfl
  have hout : Function.Bijective (fun (y : ∀ (a : Fin (m + 1) → I) (b : Fin (n + 1) → J),
      Γ(OM X, CechCochains.inter U a) ⊗[A] Γ(OM Y, CechCochains.inter V b)) a b =>
      productMap' H (CechCochains.inter U a) (CechCochains.inter V b) (box r q U V a b)
        inf_le_left inf_le_right (y a b)) := by
    refine ⟨fun x y hxy => funext fun a => funext fun b =>
      (bijective_productMap' H _ _ _ (hU a) (hV b) (hW a b) rfl).1
        (congrFun (congrFun hxy a) b), fun z => ?_⟩
    choose w hw using fun a b =>
      (bijective_productMap' H _ _ _ (hU a) (hV b) (hW a b) rfl).2 (z a b)
    exact ⟨w, funext fun a => funext fun b => hw a b⟩
  have h2 := hout.comp e.bijective
  exact hΦ ▸ h2

/-! ### The differentials of the bicomplex -/

/-- If every index of `a'` occurs in `a`, then the intersection over `a` is contained in the
intersection over `a'`. -/
theorem inter_le_inter {T : Scheme.{u}} {K : Type u} (W : K → T.Opens) {m m' : ℕ}
    {a : Fin m → K} {a' : Fin m' → K} (h : ∀ k', ∃ k, a k = a' k') :
    CechCochains.inter W a ≤ CechCochains.inter W a' :=
  le_iInf fun k' => by
    obtain ⟨k, hk⟩ := h k'
    exact (iInf_le _ k).trans (le_of_eq (congrArg W hk))

variable (r q) in
/-- If every index of `a'` occurs in `a` and every index of `b'` occurs in `b`, then the box over
`(a, b)` is contained in the box over `(a', b')`. -/
theorem box_mono {m n m' n' : ℕ} {a : Fin m → I} {b : Fin n → J} {a' : Fin m' → I}
    {b' : Fin n' → J} (ha : ∀ k', ∃ k, a k = a' k') (hb : ∀ k', ∃ k, b k = b' k') :
    box r q U V a b ≤ box r q U V a' b' :=
  inf_le_inf (fun _ hx => inter_le_inter U ha hx) (fun _ hx => inter_le_inter V hb hx)

/-- Restriction of sections of `𝒪` is restriction of sections of the ring. -/
theorem restr_unit {T : Scheme.{u}} {W W' : T.Opens} (h : W' ≤ W) (s : Γ(OM T, W)) :
    CechCochains.restr (OM T).presheaf h s = (T.presheaf.map (homOfLE h).op).hom s := rfl

variable (r q) in
/-- The horizontal differential of the bicomplex. -/
def dh (m n : ℕ) : Bi r q U V m n →+ Bi r q U V (m + 1) n where
  toFun x a b := ∑ j : Fin (m + 2), ((-1 : ℤ) ^ (j : ℕ)) • CechCochains.restr (OM P).presheaf
    (box_mono r q U V (a := a) (b := b) (a' := a ∘ j.succAbove) (b' := b)
      (fun k => ⟨j.succAbove k, rfl⟩) (fun k => ⟨k, rfl⟩)) (x (a ∘ j.succAbove) b)
  map_zero' := by
    funext a b
    exact Finset.sum_eq_zero fun j _ => by rw [Pi.zero_apply, Pi.zero_apply, map_zero, smul_zero]
  map_add' x y := by
    funext a b
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]

variable (r q) in
/-- The vertical differential of the bicomplex. -/
def dv (m n : ℕ) : Bi r q U V m n →+ Bi r q U V m (n + 1) where
  toFun x a b := ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) • CechCochains.restr (OM P).presheaf
    (box_mono r q U V (a := a) (b := b) (a' := a) (b' := b ∘ j.succAbove)
      (fun k => ⟨k, rfl⟩) (fun k => ⟨j.succAbove k, rfl⟩)) (x a (b ∘ j.succAbove))
  map_zero' := by
    funext a b
    exact Finset.sum_eq_zero fun j _ => by rw [Pi.zero_apply, Pi.zero_apply, map_zero, smul_zero]
  map_add' x y := by
    funext a b
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]

/-- The component of `dh x` at `(a, b)` is the alternating sum over `j` of the restrictions of
`x (a ∘ j.succAbove) b`. -/
theorem dh_apply {m n : ℕ} (x : Bi r q U V m n) (a : Fin (m + 2) → I) (b : Fin (n + 1) → J) :
    dh r q U V m n x a b = ∑ j : Fin (m + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      CechCochains.restr (OM P).presheaf
        (box_mono r q U V (a := a) (b := b) (a' := a ∘ j.succAbove) (b' := b)
          (fun k => ⟨j.succAbove k, rfl⟩) (fun k => ⟨k, rfl⟩)) (x (a ∘ j.succAbove) b) := rfl

/-- The component of `dv x` at `(a, b)` is the alternating sum over `j` of the restrictions of
`x a (b ∘ j.succAbove)`. -/
theorem dv_apply {m n : ℕ} (x : Bi r q U V m n) (a : Fin (m + 1) → I) (b : Fin (n + 2) → J) :
    dv r q U V m n x a b = ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      CechCochains.restr (OM P).presheaf
        (box_mono r q U V (a := a) (b := b) (a' := a) (b' := b ∘ j.succAbove)
          (fun k => ⟨k, rfl⟩) (fun k => ⟨j.succAbove k, rfl⟩)) (x a (b ∘ j.succAbove)) := rfl

/-- Restricting a section commutes with `p.appLE`, in both the source and the target open. -/
private theorem appLE_restr_apply {T S : Scheme.{u}} (p : S ⟶ T) {O O' : T.Opens}
    {W W' : S.Opens} (hO : O ≤ O') (hW : W ≤ W') (h : W ≤ p ⁻¹ᵁ O) (h' : W' ≤ p ⁻¹ᵁ O')
    (x : Γ(T, O')) :
    (p.appLE O W h).hom ((T.presheaf.map (homOfLE hO).op).hom x) =
      (S.presheaf.map (homOfLE hW).op).hom ((p.appLE O' W' h').hom x) := by
  have e := congrArg (fun φ => φ.hom x) ((Scheme.Hom.map_appLE p (V := W) h
    (homOfLE hO).op).trans (Scheme.Hom.appLE_map p (V := W') h' (homOfLE hW).op).symm)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

/-- Restricting the target open of `p.appLE` commutes with restriction of sections. -/
private theorem appLE_apply_eq_restr {T S : Scheme.{u}} (p : S ⟶ T) {O : T.Opens}
    {W W' : S.Opens} (hW : W ≤ W') (h : W ≤ p ⁻¹ᵁ O) (h' : W' ≤ p ⁻¹ᵁ O) (x : Γ(T, O)) :
    (p.appLE O W h).hom x = (S.presheaf.map (homOfLE hW).op).hom ((p.appLE O W' h').hom x) :=
  congrArg (fun φ => φ.hom x) (Scheme.Hom.appLE_map p h' (homOfLE hW).op).symm

/-- For `x` over `U_{a ∘ j.succAbove}` and `y` over `V_b`, the product over the box at `(a, b)` of
the pullback along `r` of `z • x` restricted to `U_a` and the pullback of `y` along `q` is `z`
times the restriction of the product of the pullbacks of `x` and `y` over the box at
`(a ∘ j.succAbove, b)`. -/
theorem term_h {m n : ℕ} (a : Fin (m + 2) → I) (b : Fin (n + 1) → J) (j : Fin (m + 2))
    (x : Γ(X, CechCochains.inter U (a ∘ j.succAbove))) (y : Γ(Y, CechCochains.inter V b))
    (z : ℤ) :
    (r.appLE _ (box r q U V a b) inf_le_left).hom
        (z • (X.presheaf.map (homOfLE (CechCochains.inter_le_omit U a j)).op).hom x) *
      (q.appLE _ (box r q U V a b) inf_le_right).hom y =
    z • (P.presheaf.map (homOfLE (box_mono r q U V (a := a) (b := b) (a' := a ∘ j.succAbove)
        (b' := b) (fun k => ⟨j.succAbove k, rfl⟩) (fun k => ⟨k, rfl⟩))).op).hom
      ((r.appLE _ (box r q U V (a ∘ j.succAbove) b) inf_le_left).hom x *
        (q.appLE _ (box r q U V (a ∘ j.succAbove) b) inf_le_right).hom y) := by
  rw [map_zsmul, smul_mul_assoc, map_mul,
    appLE_restr_apply r (CechCochains.inter_le_omit U a j) _ inf_le_left inf_le_left,
    appLE_apply_eq_restr q _ inf_le_right inf_le_right]

/-- For `x` over `U_a` and `y` over `V_{b ∘ j.succAbove}`, the product over the box at `(a, b)` of
the pullback of `x` along `r` and the pullback along `q` of `z • y` restricted to `V_b` is `z`
times the restriction of the product of the pullbacks of `x` and `y` over the box at
`(a, b ∘ j.succAbove)`. -/
theorem term_v {m n : ℕ} (a : Fin (m + 1) → I) (b : Fin (n + 2) → J) (j : Fin (n + 2))
    (x : Γ(X, CechCochains.inter U a)) (y : Γ(Y, CechCochains.inter V (b ∘ j.succAbove)))
    (z : ℤ) :
    (r.appLE _ (box r q U V a b) inf_le_left).hom x *
      (q.appLE _ (box r q U V a b) inf_le_right).hom
        (z • (Y.presheaf.map (homOfLE (CechCochains.inter_le_omit V b j)).op).hom y) =
    z • (P.presheaf.map (homOfLE (box_mono r q U V (a := a) (b := b) (a' := a)
        (b' := b ∘ j.succAbove) (fun k => ⟨k, rfl⟩) (fun k => ⟨j.succAbove k, rfl⟩))).op).hom
      ((r.appLE _ (box r q U V a (b ∘ j.succAbove)) inf_le_left).hom x *
        (q.appLE _ (box r q U V a (b ∘ j.succAbove)) inf_le_right).hom y) := by
  rw [map_zsmul, mul_smul_comm, map_mul,
    appLE_restr_apply q (CechCochains.inter_le_omit V b j) _ inf_le_right inf_le_right,
    appLE_apply_eq_restr r _ inf_le_left inf_le_left]

/-- `psi` carries the Čech differential of `U`, tensored with the identity, to the horizontal
differential `dh`. -/
theorem psi_rTensor (m n : ℕ) :
    letI := cochainModule f U (OM X) m
    letI := cochainModule f U (OM X) (m + 1)
    letI := cochainModule g V (OM Y) n
    ∀ x : CechCochains.Cochain U (OM X).presheaf m ⊗[A] CechCochains.Cochain V (OM Y).presheaf n,
    psi H U V (m + 1) n ((cechModuleD f U (OM X) m).rTensor _ x) =
      dh r q U V m n (psi H U V m n x) := by
  let := cochainModule f U (OM X) m
  let := cochainModule f U (OM X) (m + 1)
  let := cochainModule g V (OM Y) n
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul c d =>
    funext a b
    rw [LinearMap.rTensor_tmul, psi_tmul]
    change (r.appLE _ (box r q U V a b) inf_le_left).hom (∑ j : Fin (m + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        (X.presheaf.map (homOfLE (CechCochains.inter_le_omit U a j)).op).hom
          (c (a ∘ j.succAbove))) * (q.appLE _ (box r q U V a b) inf_le_right).hom (d b) =
      ∑ j : Fin (m + 2), ((-1 : ℤ) ^ (j : ℕ)) • (P.presheaf.map (homOfLE _).op).hom
        ((r.appLE _ _ inf_le_left).hom (c (a ∘ j.succAbove)) *
          (q.appLE _ _ inf_le_right).hom (d b))
    exact (congrArg (· * _) (map_sum _ _ _)).trans ((Finset.sum_mul _ _ _).trans
      (Finset.sum_congr rfl fun j _ => term_h (r := r) (q := q) U V a b j _ _ _))

/-- `psi` carries the identity tensored with the Čech differential of `V` to the vertical
differential `dv`. -/
theorem psi_lTensor (m n : ℕ) :
    letI := cochainModule f U (OM X) m
    letI := cochainModule g V (OM Y) n
    letI := cochainModule g V (OM Y) (n + 1)
    ∀ x : CechCochains.Cochain U (OM X).presheaf m ⊗[A] CechCochains.Cochain V (OM Y).presheaf n,
    psi H U V m (n + 1) ((cechModuleD g V (OM Y) n).lTensor _ x) =
      dv r q U V m n (psi H U V m n x) := by
  let := cochainModule f U (OM X) m
  let := cochainModule g V (OM Y) n
  let := cochainModule g V (OM Y) (n + 1)
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul c d =>
    funext a b
    rw [LinearMap.lTensor_tmul, psi_tmul]
    change (r.appLE _ (box r q U V a b) inf_le_left).hom (c a) *
        (q.appLE _ (box r q U V a b) inf_le_right).hom (∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        (Y.presheaf.map (homOfLE (CechCochains.inter_le_omit V b j)).op).hom
          (d (b ∘ j.succAbove))) =
      ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) • (P.presheaf.map (homOfLE _).op).hom
        ((r.appLE _ _ inf_le_left).hom (c a) *
          (q.appLE _ _ inf_le_right).hom (d (b ∘ j.succAbove)))
    exact (congrArg (_ * ·) (map_sum _ _ _)).trans ((Finset.mul_sum _ _ _).trans
      (Finset.sum_congr rfl fun j _ => term_v (r := r) (q := q) U V a b j _ _ _))

/-! ### Diagonal Čech cochains and the bicomplex, in degrees at most one -/

section Diagonal

variable (r q) (W' : I × J → P.Opens)
  (hle : ∀ t : I × J, box r q U V ![t.1] ![t.2] ≤ W' t)
  (hge : ∀ t : I × J, W' t ≤ box r q U V ![t.1] ![t.2])

include hle in
/-- The box over the coordinates of a tuple `t` of pairs is contained in the intersection of the
`W' (t i)`. -/
theorem box_le_inter {p : ℕ} (t : Fin (p + 1) → I × J) :
    box r q U V (Prod.fst ∘ t) (Prod.snd ∘ t) ≤ CechCochains.inter W' t :=
  le_iInf fun i => (box_mono r q U V (a' := ![(t i).1]) (b' := ![(t i).2])
    (fun k' => ⟨i, by rw [Fin.fin_one_eq_zero k']; rfl⟩)
    (fun k' => ⟨i, by rw [Fin.fin_one_eq_zero k']; rfl⟩)).trans (hle (t i))

include hge in
/-- The intersection of the `W' (t i)` is contained in the box over the coordinates of the tuple
`t` of pairs. -/
theorem inter_le_box {p : ℕ} (t : Fin (p + 1) → I × J) :
    CechCochains.inter W' t ≤ box r q U V (Prod.fst ∘ t) (Prod.snd ∘ t) := by
  have h1 : ∀ i, CechCochains.inter W' t ≤ box r q U V ![(t i).1] ![(t i).2] :=
    fun i => (iInf_le (fun i => W' (t i)) i).trans (hge (t i))
  refine le_inf ?_ ?_
  · rw [show r ⁻¹ᵁ CechCochains.inter U (Prod.fst ∘ t) = ⨅ k, r ⁻¹ᵁ U (t k).1 from
      preimage_iInf r _]
    exact le_iInf fun i => (h1 i).trans (inf_le_left.trans
      (r.preimage_mono (iInf_le (fun k => U (![(t i).1] k)) 0)))
  · rw [show q ⁻¹ᵁ CechCochains.inter V (Prod.snd ∘ t) = ⨅ k, q ⁻¹ᵁ V (t k).2 from
      preimage_iInf q _]
    exact le_iInf fun i => (h1 i).trans (inf_le_right.trans
      (q.preimage_mono (iInf_le (fun k => V (![(t i).2] k)) 0)))

/-- The horizontal part `(z_{(a_0,b),(a_1,b)})` of a diagonal `1`-cochain. -/
def to10 (z : CechCochains.Cochain W' (OM P).presheaf 1) : Bi r q U V 1 0 := fun a b =>
  CechCochains.restr (OM P).presheaf ((box_mono r q U V (a' := a) (b' := fun _ => b 0)
    (fun k => ⟨k, rfl⟩) (fun _ => ⟨0, rfl⟩)).trans (box_le_inter r q U V W' hle
      (fun i => (a i, b 0)))) (z fun i => (a i, b 0))

/-- The vertical part `(z_{(a,b_0),(a,b_1)})` of a diagonal `1`-cochain. -/
def to01 (z : CechCochains.Cochain W' (OM P).presheaf 1) : Bi r q U V 0 1 := fun a b =>
  CechCochains.restr (OM P).presheaf ((box_mono r q U V (a' := fun _ => a 0) (b' := b)
    (fun _ => ⟨0, rfl⟩) (fun k => ⟨k, rfl⟩)).trans (box_le_inter r q U V W' hle
      (fun i => (a 0, b i)))) (z fun i => (a 0, b i))

/-- A diagonal `0`-cochain as an element of the bicomplex. -/
def to00 (e : CechCochains.Cochain W' (OM P).presheaf 0) : Bi r q U V 0 0 := fun a b =>
  CechCochains.restr (OM P).presheaf ((box_mono r q U V (a' := fun _ => a 0) (b' := fun _ => b 0)
    (fun _ => ⟨0, rfl⟩) (fun _ => ⟨0, rfl⟩)).trans (box_le_inter r q U V W' hle
      (fun _ => (a 0, b 0)))) (e fun _ => (a 0, b 0))

/-- Restrictions of the values of a cochain at equal tuples to a common open agree. -/
theorem restr_congr' {p : ℕ} (z : CechCochains.Cochain W' (OM P).presheaf p)
    {t t' : Fin (p + 1) → I × J} (h : t = t') {O : P.Opens} (h₁ : O ≤ CechCochains.inter W' t)
    (h₂ : O ≤ CechCochains.inter W' t') :
    CechCochains.restr (OM P).presheaf h₁ (z t) = CechCochains.restr (OM P).presheaf h₂ (z t') := by
  subst h
  rfl

/-- The Čech differential of a `0`-cochain, restricted. -/
theorem cechD_zero_restr (e : CechCochains.Cochain W' (OM P).presheaf 0) (t : Fin 2 → I × J)
    {O : P.Opens} (hO : O ≤ CechCochains.inter W' t) :
    CechCochains.restr (OM P).presheaf hO (CechCochains.cechD W' (OM P).presheaf 0 e t) =
      CechCochains.restr (OM P).presheaf (hO.trans (CechCochains.inter_le_omit W' t 0))
          (e (t ∘ Fin.succAbove 0)) -
        CechCochains.restr (OM P).presheaf (hO.trans (CechCochains.inter_le_omit W' t 1))
          (e (t ∘ Fin.succAbove 1)) := by
  change CechCochains.restr _ hO (∑ j : Fin 2, ((-1 : ℤ) ^ (j : ℕ)) •
    CechCochains.restr _ (CechCochains.inter_le_omit W' t j) (e (t ∘ j.succAbove))) = _
  rw [map_sum, Fin.sum_univ_two]
  simp only [CechCochains.restr_restr, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_smul, neg_smul, sub_eq_add_neg, map_neg]

/-- The Čech differential of a `1`-cochain, restricted. -/
theorem cechD_one_restr (z : CechCochains.Cochain W' (OM P).presheaf 1) (t : Fin 3 → I × J)
    {O : P.Opens} (hO : O ≤ CechCochains.inter W' t) :
    CechCochains.restr (OM P).presheaf hO (CechCochains.cechD W' (OM P).presheaf 1 z t) =
      CechCochains.restr (OM P).presheaf (hO.trans (CechCochains.inter_le_omit W' t 0))
          (z (t ∘ Fin.succAbove 0)) -
        CechCochains.restr (OM P).presheaf (hO.trans (CechCochains.inter_le_omit W' t 1))
          (z (t ∘ Fin.succAbove 1)) +
        CechCochains.restr (OM P).presheaf (hO.trans (CechCochains.inter_le_omit W' t 2))
          (z (t ∘ Fin.succAbove 2)) := by
  change CechCochains.restr _ hO (∑ j : Fin 3, ((-1 : ℤ) ^ (j : ℕ)) •
    CechCochains.restr _ (CechCochains.inter_le_omit W' t j) (z (t ∘ j.succAbove))) = _
  rw [map_sum, Fin.sum_univ_three]
  simp only [CechCochains.restr_restr, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one, one_smul, neg_smul, sub_eq_add_neg, neg_one_sq, map_neg]

/-- In an additive commutative group, `0 = x1 - y + x2` and `0 = u - y + v` give
`u + -x2 = x1 + -v`. -/
theorem aux_abel {G : Type*} [AddCommGroup G] {x1 y x2 u v : G} (h1 : 0 = x1 - y + x2)
    (h2 : 0 = u - y + v) : u + -x2 = x1 + -v := by
  rw [← sub_eq_zero]
  have h3 : (u - y + v) - (x1 - y + x2) = 0 := by rw [← h1, ← h2, sub_self]
  rw [← h3]
  abel

/-- In an additive commutative group, if `0 = X0 - Z + X2`, `e11 + -e10 = X0` and
`e10 + -e00 = X2`, then `e11 - e00 = Z`. -/
theorem aux_abel2 {G : Type*} [AddCommGroup G] {e11 e10 e00 X0 X2 Z : G}
    (h1 : 0 = X0 - Z + X2) (hv : e11 + -e10 = X0) (hh : e10 + -e00 = X2) : e11 - e00 = Z := by
  rw [← hv, ← hh] at h1
  have h2 : e11 - e00 - Z = (e11 + -e10 - Z + (e10 + -e00)) := by abel
  rw [← sub_eq_zero, h2, ← h1]

/-- Restrictions of the components of an element of the bicomplex at equal pairs of tuples to a
common open agree. -/
theorem bi_congr {m n : ℕ} (x : Bi r q U V m n) {a a' : Fin (m + 1) → I} {b b' : Fin (n + 1) → J}
    (ha : a = a') (hb : b = b') {O : P.Opens} (h₁ : O ≤ box r q U V a b)
    (h₂ : O ≤ box r q U V a' b') :
    CechCochains.restr (OM P).presheaf h₁ (x a b) =
      CechCochains.restr (OM P).presheaf h₂ (x a' b') := by
  subst ha hb
  rfl

include hle in
/-- If `a` contains every first coordinate and `b` every second coordinate of a tuple `t` of pairs,
then the box over `(a, b)` is contained in the intersection of the `W' (t i)`. -/
theorem box_le_inter' {p m n : ℕ} (t : Fin (p + 1) → I × J) (a : Fin m → I) (b : Fin n → J)
    (ha : ∀ k', ∃ k, a k = (t k').1) (hb : ∀ k', ∃ k, b k = (t k').2) :
    box r q U V a b ≤ CechCochains.inter W' t :=
  (box_mono r q U V ha hb).trans (box_le_inter r q U V W' hle t)

/-- **The horizontal part of a cocycle is a horizontal cocycle.** -/
theorem dh_to10 (z : CechCochains.Cochain W' (OM P).presheaf 1)
    (hz : CechCochains.cechD W' (OM P).presheaf 1 z = 0) :
    dh r q U V 1 0 (to10 r q U V W' hle z) = 0 := by
  funext a b
  have h := cechD_one_restr W' z (fun i => (a i, b 0)) (O := box r q U V a b)
    (box_le_inter' r q U V W' hle _ a b (fun k' => ⟨k', rfl⟩) (fun _ => ⟨0, rfl⟩))
  rw [congrFun hz, CechCochains.Cochain.zero_apply, map_zero] at h
  rw [dh_apply, Fin.sum_univ_three]
  simp only [to10]
  simp only [CechCochains.restr_restr, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
    one_smul, neg_smul, neg_one_sq]
  rw [Pi.zero_apply, Pi.zero_apply, ← sub_eq_add_neg]
  exact h.symm

/-- **The two mixed parts of a cocycle agree.** -/
theorem dv_to10 (z : CechCochains.Cochain W' (OM P).presheaf 1)
    (hz : CechCochains.cechD W' (OM P).presheaf 1 z = 0) :
    dv r q U V 1 0 (to10 r q U V W' hle z) = dh r q U V 0 1 (to01 r q U V W' hle z) := by
  funext a b
  let T : Fin 3 → I × J := ![(a 0, b 0), (a 1, b 0), (a 1, b 1)]
  let T' : Fin 3 → I × J := ![(a 0, b 0), (a 0, b 1), (a 1, b 1)]
  have hT : box r q U V a b ≤ CechCochains.inter W' T :=
    box_le_inter' r q U V W' hle T a b
      (fun k' => by fin_cases k' <;> exact ⟨_, rfl⟩) (fun k' => by fin_cases k' <;> exact ⟨_, rfl⟩)
  have hT' : box r q U V a b ≤ CechCochains.inter W' T' :=
    box_le_inter' r q U V W' hle T' a b
      (fun k' => by fin_cases k' <;> exact ⟨_, rfl⟩) (fun k' => by fin_cases k' <;> exact ⟨_, rfl⟩)
  have h1 := cechD_one_restr W' z T hT
  have h2 := cechD_one_restr W' z T' hT'
  rw [congrFun hz, CechCochains.Cochain.zero_apply, map_zero] at h1 h2
  rw [dv_apply, dh_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [to10, to01]
  simp only [CechCochains.restr_restr, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_smul, neg_smul]
  rw [restr_congr' W' z (t := fun i => (a i, (b ∘ Fin.succAbove 0) 0))
      (t' := T' ∘ Fin.succAbove 0) (by funext i; fin_cases i <;> rfl) _
      (hT'.trans (CechCochains.inter_le_omit W' T' 0)),
    restr_congr' W' z (t := fun i => (a i, (b ∘ Fin.succAbove 1) 0))
      (t' := T ∘ Fin.succAbove 2) (by funext i; fin_cases i <;> rfl) _
      (hT.trans (CechCochains.inter_le_omit W' T 2)),
    restr_congr' W' z (t := fun i => ((a ∘ Fin.succAbove 0) 0, b i))
      (t' := T ∘ Fin.succAbove 0) (by funext i; fin_cases i <;> rfl) _
      (hT.trans (CechCochains.inter_le_omit W' T 0)),
    restr_congr' W' z (t := fun i => ((a ∘ Fin.succAbove 1) 0, b i))
      (t' := T' ∘ Fin.succAbove 2) (by funext i; fin_cases i <;> rfl) _
      (hT'.trans (CechCochains.inter_le_omit W' T' 2))]
  have h12 : CechCochains.restr (OM P).presheaf (hT.trans (CechCochains.inter_le_omit W' T 1))
      (z (T ∘ Fin.succAbove 1)) = CechCochains.restr (OM P).presheaf
        (hT'.trans (CechCochains.inter_le_omit W' T' 1)) (z (T' ∘ Fin.succAbove 1)) :=
    restr_congr' W' z (by funext i; fin_cases i <;> rfl) _ _
  rw [h12] at h1
  exact aux_abel h1 h2

/-- Every entry of the one-element tuple `![c]` is `c`. -/
theorem fin1 {α : Type*} (c : α) (k : Fin 1) : ![c] k = c := by
  rw [Fin.fin_one_eq_zero k]
  rfl

/-- A `0`-cochain of the bicomplex as a diagonal `0`-cochain. -/
def from00 (E : Bi r q U V 0 0) : CechCochains.Cochain W' (OM P).presheaf 0 := fun t =>
  CechCochains.restr (OM P).presheaf (inter_le_box r q U V W' hge t)
    (E (Prod.fst ∘ t) (Prod.snd ∘ t))

/-- For opens `O ≤ O'` with `O' ≤ O`, restriction of sections of `𝒪_P` from `O'` to `O` is
injective. -/
theorem restr_injective {O O' : P.Opens} (h : O ≤ O') (h' : O' ≤ O) :
    Function.Injective (CechCochains.restr (OM P).presheaf h) := fun x y hxy => by
  have := congrArg (CechCochains.restr (OM P).presheaf h') hxy
  rwa [CechCochains.restr_restr, CechCochains.restr_restr, restr_self, restr_self] at this

include hle in
/-- **A diagonal cocycle whose horizontal and vertical parts are the differentials of one
`0`-cochain of the bicomplex is a coboundary.** -/
theorem cechD_from00 (z : CechCochains.Cochain W' (OM P).presheaf 1)
    (hz : CechCochains.cechD W' (OM P).presheaf 1 z = 0) (E : Bi r q U V 0 0)
    (hEh : dh r q U V 0 0 E = to10 r q U V W' hle z)
    (hEv : dv r q U V 0 0 E = to01 r q U V W' hle z) :
    CechCochains.cechD W' (OM P).presheaf 0 (from00 r q U V W' hge E) = z := by
  funext s
  set a : Fin 2 → I := Prod.fst ∘ s
  set b : Fin 2 → J := Prod.snd ∘ s
  have hO : box r q U V a b ≤ CechCochains.inter W' s := box_le_inter r q U V W' hle s
  refine restr_injective hO (inter_le_box r q U V W' hge s) ?_
  let T : Fin 3 → I × J := ![(a 0, b 0), (a 1, b 0), (a 1, b 1)]
  have hT : box r q U V a b ≤ CechCochains.inter W' T :=
    box_le_inter' r q U V W' hle T a b
      (fun k' => by fin_cases k' <;> exact ⟨_, rfl⟩) (fun k' => by fin_cases k' <;> exact ⟨_, rfl⟩)
  have h1 := cechD_one_restr W' z T hT
  rw [congrFun hz, CechCochains.Cochain.zero_apply, map_zero] at h1
  -- the horizontal and vertical parts at `(a, b₀)` and `(a₁, b)`
  have hh := congrArg (CechCochains.restr (OM P).presheaf
    (box_mono r q U V (a := a) (b := b) (a' := a) (b' := ![b 0]) (fun k => ⟨k, rfl⟩)
      (fun k => ⟨0, (fin1 _ k).symm⟩))) (congrFun (congrFun hEh a) ![b 0])
  have hv := congrArg (CechCochains.restr (OM P).presheaf
    (box_mono r q U V (a := a) (b := b) (a' := ![a 1]) (b' := b) (fun k => ⟨1, (fin1 _ k).symm⟩)
      (fun k => ⟨k, rfl⟩))) (congrFun (congrFun hEv ![a 1]) b)
  rw [dh_apply, Fin.sum_univ_two] at hh
  rw [dv_apply, Fin.sum_univ_two] at hv
  simp only [to10, to01, map_add, CechCochains.restr_restr, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, one_smul, neg_smul, map_neg] at hh hv
  rw [cechD_zero_restr]
  simp only [from00, CechCochains.restr_restr]
  rw [restr_congr' W' z (t := fun i => (a i, ![b 0] 0)) (t' := T ∘ Fin.succAbove 2)
    (by funext i; fin_cases i <;> rfl) _ (hT.trans (CechCochains.inter_le_omit W' T 2))] at hh
  rw [restr_congr' W' z (t := fun i => (![a 1] 0, b i)) (t' := T ∘ Fin.succAbove 0)
    (by funext i; fin_cases i <;> rfl) _ (hT.trans (CechCochains.inter_le_omit W' T 0))] at hv
  rw [restr_congr' W' z (t := T ∘ Fin.succAbove 1) (t' := s)
    (by funext i; fin_cases i <;> rfl) _ hO] at h1
  rw [bi_congr r q U V E (a := ![a 1]) (b := b ∘ Fin.succAbove 1)
      (a' := a ∘ Fin.succAbove 0) (b' := ![b 0]) (by funext i; fin_cases i; rfl)
      (by funext i; fin_cases i; rfl) _
      (box_mono r q U V (fun k => ⟨1, by rw [Fin.fin_one_eq_zero k]; rfl⟩)
        (fun k => ⟨0, (fin1 _ k).symm⟩))] at hv
  rw [bi_congr r q U V E (a := Prod.fst ∘ s ∘ Fin.succAbove 0) (b := Prod.snd ∘ s ∘ Fin.succAbove 0)
      (a' := ![a 1]) (b' := b ∘ Fin.succAbove 0)
      (by funext i; fin_cases i; rfl) (by funext i; fin_cases i; rfl) _
      (box_mono r q U V (fun k => ⟨1, (fin1 _ k).symm⟩)
        (fun k => ⟨1, by rw [Fin.fin_one_eq_zero k]; rfl⟩)),
    bi_congr r q U V E (a := Prod.fst ∘ s ∘ Fin.succAbove 1) (b := Prod.snd ∘ s ∘ Fin.succAbove 1)
      (a' := a ∘ Fin.succAbove 1) (b' := ![b 0])
      (by funext i; fin_cases i; rfl) (by funext i; fin_cases i; rfl) _
      (box_mono r q U V (fun k => ⟨0, by rw [Fin.fin_one_eq_zero k]; rfl⟩)
        (fun k => ⟨0, (fin1 _ k).symm⟩))]
  exact aux_abel2 h1 hv hh

/-- **A diagonal coboundary gives a coboundary of the bicomplex.** -/
theorem dh_to00 (e : CechCochains.Cochain W' (OM P).presheaf 0) :
    dh r q U V 0 0 (to00 r q U V W' hle e) =
      to10 r q U V W' hle (CechCochains.cechD W' (OM P).presheaf 0 e) := by
  funext a b
  rw [dh_apply, Fin.sum_univ_two]
  simp only [to00, to10, cechD_zero_restr, CechCochains.restr_restr, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, one_smul, neg_smul, sub_eq_add_neg]
  congr 1
  · exact restr_congr' W' e (by funext i; fin_cases i; rfl) _ _
  · exact congrArg Neg.neg (restr_congr' W' e (by funext i; fin_cases i; rfl) _ _)

/-- The vertical differential of `to00 e` is the vertical part of the Čech differential of `e`. -/
theorem dv_to00 (e : CechCochains.Cochain W' (OM P).presheaf 0) :
    dv r q U V 0 0 (to00 r q U V W' hle e) =
      to01 r q U V W' hle (CechCochains.cechD W' (OM P).presheaf 0 e) := by
  funext a b
  rw [dv_apply, Fin.sum_univ_two]
  simp only [to00, to01, cechD_zero_restr, CechCochains.restr_restr, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, one_smul, neg_smul, sub_eq_add_neg]
  congr 1
  · exact restr_congr' W' e (by funext i; fin_cases i; rfl) _ _
  · exact congrArg Neg.neg (restr_congr' W' e (by funext i; fin_cases i; rfl) _ _)

end Diagonal

end General

/-! ### Points and faces -/

section Faces

variable {k : Type u} [Field k] {X Y P : Scheme.{u}} {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of k)}
  {r : P ⟶ X} {q : P ⟶ Y} (H : IsPullback r q f g) {I J : Type u} (U : I → X.Opens)
  (V : J → Y.Opens)

/-- The intersection over the one-element tuple `![c]` is `W c`. -/
theorem inter_fin1 {T : Scheme.{u}} {K : Type u} (W : K → T.Opens) (c : K) :
    CechCochains.inter W ![c] = W c := by
  refine le_antisymm (iInf_le_of_le 0 le_rfl) (le_iInf fun k => ?_)
  rw [fin1]

/-- The isomorphism `Scheme.ΓSpecIso` sends the image of `c` under `baseRingHom (𝟙 (Spec k)) ⊤`
back to `c`. -/
theorem ΓSpecIso_hom_baseRingHom_id (c : k) :
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
      ((baseRingHom (𝟙 (Spec (CommRingCat.of k))) ⊤).hom c) = c := by
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
    (((Spec (CommRingCat.of k)).presheaf.map (homOfLE le_top).op).hom
      ((toSpecΓ (CommRingCat.of k) ≫ Scheme.Hom.appTop (𝟙 (Spec (CommRingCat.of k)))).hom c)) = c
  rw [show (homOfLE le_top : (⊤ : (Spec (CommRingCat.of k)).Opens) ⟶ ⊤).op = 𝟙 _ from rfl,
    CategoryTheory.Functor.map_id, Scheme.Hom.id_appTop]
  exact congrArg (fun φ : CommRingCat.of k ⟶ CommRingCat.of k => φ.hom c)
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv_hom_id

/-- The global sections of `Spec k` are `k`, linearly. -/
def specLin : letI := baseAlgebra (𝟙 (Spec (CommRingCat.of k))) ⊤
    Γ(Spec (CommRingCat.of k), ⊤) →ₗ[k] k :=
  letI := baseAlgebra (𝟙 (Spec (CommRingCat.of k))) ⊤
  { toFun := fun t => (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom t
    map_add' := fun _ _ => map_add _ _ _
    map_smul' := fun c t => by
      change (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
        ((baseRingHom (𝟙 (Spec (CommRingCat.of k))) ⊤).hom c * t) = c * _
      rw [map_mul, ΓSpecIso_hom_baseRingHom_id] }

/-- **Evaluation at a rational point**, on degree-zero Čech cochains, at one member of the
cover containing the point. -/
def ev {T : Scheme.{u}} {gT : T ⟶ Spec (.of k)} {K : Type u} (V : K → T.Opens)
    (y : Spec (.of k) ⟶ T) (hy : y ≫ gT = 𝟙 _) (b0 : K) (hyb : y ⁻¹ᵁ V b0 = ⊤) :
    letI := cochainModule gT V (OM T) 0
    CechCochains.Cochain V (OM T).presheaf 0 →ₗ[k] k :=
  letI : ∀ i : Fin 1 → K, Module k Γ(OM T, CechCochains.inter V i) :=
    fun _ => sectionsModule gT _ _
  letI := baseAlgebra gT (CechCochains.inter V ![b0])
  letI := baseAlgebra (𝟙 (Spec (CommRingCat.of k))) ⊤
  specLin ∘ₗ (appLEAlgHom y gT (𝟙 _) hy (CechCochains.inter V ![b0]) ⊤
    (by rw [inter_fin1, hyb])).toLinearMap ∘ₗ (secEquiv gT _).toLinearMap ∘ₗ
    LinearMap.proj (R := k) (φ := fun i : Fin 1 → K => Γ(OM T, CechCochains.inter V i)) ![b0]

/-- `ev V y hy b0 hyb d` is the image under `Scheme.ΓSpecIso` of the pullback along `y` of the
component `d ![b0]`. -/
theorem ev_apply {T : Scheme.{u}} {gT : T ⟶ Spec (.of k)} {K : Type u} (V : K → T.Opens)
    (y : Spec (.of k) ⟶ T) (hy : y ≫ gT = 𝟙 _) (b0 : K) (hyb : y ⁻¹ᵁ V b0 = ⊤)
    (d : CechCochains.Cochain V (OM T).presheaf 0) :
    ev V y hy b0 hyb d = (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
      ((y.appLE (CechCochains.inter V ![b0]) ⊤ (by rw [inter_fin1, hyb])).hom (d ![b0])) := rfl

/-- The unit cochain `(1)_a`. -/
def unitCochain0 {T : Scheme.{u}} {K : Type u} (V : K → T.Opens) :
    CechCochains.Cochain V (OM T).presheaf 0 :=
  fun i => (show Γ(T, CechCochains.inter V i) from 1)

/-- **Degree-zero cocycles are constant** on a scheme over a field with only constant functions. -/
theorem ker_cechD_zero_le {T : Scheme.{u}} (gT : T ⟶ Spec (.of k)) {K : Type u}
    (V : K → T.Opens) (hV : ⊤ ≤ ⨆ b, V b) (hΓ : Function.Bijective (globalRingHom gT).hom) :
    letI := cochainModule gT V (OM T) 0
    letI := cochainModule gT V (OM T) 1
    LinearMap.ker (cechModuleD gT V (OM T) 0) ≤ k ∙ unitCochain0 V := by
  let := cochainModule gT V (OM T) 0
  let := cochainModule gT V (OM T) 1
  let := sectionsModule gT (OM T) ⊤
  intro d hd
  have hdalt : d ∈ alternatingSubmodule gT V (OM T) 0 :=
    ⟨fun i hi => absurd (fun x y _ => Subsingleton.elim (α := Fin 1) x y) hi,
      fun i a b hab => absurd (Subsingleton.elim (α := Fin 1) a b) hab⟩
  have hker : (⟨d, hdalt⟩ : alternatingSubmodule gT V (OM T) 0) ∈
      LinearMap.ker (alternatingCechModuleD gT V (OM T) 0) :=
    Subtype.ext (LinearMap.mem_ker.1 hd)
  rw [← range_sectionsToAlternatingₗ gT V (OM T) (fun _ => le_top) hV] at hker
  obtain ⟨sec, hsec⟩ := hker
  obtain ⟨c, hc⟩ := hΓ.2 (show Γ(T, ⊤) from sec)
  refine Submodule.mem_span_singleton.2 ⟨c, funext fun i => ?_⟩
  have := congrArg (fun x : alternatingSubmodule gT V (OM T) 0 =>
    (x : CechCochains.Cochain V (OM T).presheaf 0) i) hsec
  simp only [sectionsToAlternatingₗ_apply_coe] at this
  rw [← this, cochain_smul_apply]
  change (show Γ(T, CechCochains.inter V i) from
      (baseRingHom gT (CechCochains.inter V i)).hom c * 1) =
    (T.presheaf.map (homOfLE _).op).hom (show Γ(T, ⊤) from sec)
  rw [mul_one]
  refine Eq.trans ?_ (congrArg (T.presheaf.map (homOfLE (le_top :
    CechCochains.inter V i ≤ ⊤)).op).hom hc)
  have ht : (baseRingHom gT ⊤).hom c = (globalRingHom gT).hom c := by
    change (T.presheaf.map (homOfLE le_top).op).hom ((globalRingHom gT).hom c) = _
    rw [show (homOfLE (le_top : (⊤ : T.Opens) ≤ ⊤)).op = 𝟙 _ from rfl,
      CategoryTheory.Functor.map_id]
    rfl
  exact (map_baseRingHom_apply gT (homOfLE (le_top : CechCochains.inter V i ≤ ⊤)).op c).symm.trans
    (congrArg _ ht)

/-- The unit cochain is a Čech cocycle. -/
theorem cechD_unitCochain0 {T : Scheme.{u}} {K : Type u} (V : K → T.Opens) :
    CechCochains.cechD V (OM T).presheaf 0 (unitCochain0 V) = 0 := by
  funext i
  change ∑ j : Fin 2, ((-1 : ℤ) ^ (j : ℕ)) • (T.presheaf.map (homOfLE _).op).hom
    (show Γ(T, _) from 1) = (0 : Γ(T, CechCochains.inter V i))
  rw [Fin.sum_univ_two, map_one, map_one]
  simp

/-- Evaluation of the unit cochain at the rational point `y` is `1`. -/
theorem ev_unitCochain0 {T : Scheme.{u}} {gT : T ⟶ Spec (.of k)} {K : Type u} (V : K → T.Opens)
    (y : Spec (.of k) ⟶ T) (hy : y ≫ gT = 𝟙 _) (b0 : K) (hyb : y ⁻¹ᵁ V b0 = ⊤) :
    ev V y hy b0 hyb (unitCochain0 V) = 1 := by
  rw [ev_apply]
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
    ((y.appLE (CechCochains.inter V ![b0]) ⊤ _).hom 1) = 1
  rw [map_one, map_one]

/-- Pullback of a Čech cochain of `𝒪` along a morphism, on sections of the rings. -/
def ringPullback {T S : Scheme.{u}} (j : T ⟶ S) {K : Type u} (W : K → S.Opens) (p : ℕ)
    (c : CechCochains.Cochain W (OM S).presheaf p) :
    CechCochains.Cochain (fun t => j ⁻¹ᵁ W t) (OM T).presheaf p := fun t =>
  (j.appLE (CechCochains.inter W t) (CechCochains.inter (fun t => j ⁻¹ᵁ W t) t)
    (le_of_eq (preimage_iInf j _).symm)).hom (c t)

/-- Restriction along `𝟙` on the rings of sections. -/
theorem id_appLE_apply {T : Scheme.{u}} (O : T.Opens) (h : O ≤ (𝟙 T) ⁻¹ᵁ O) (x : Γ(T, O)) :
    (Scheme.Hom.appLE (𝟙 T) O O h).hom x = x := by
  have : Scheme.Hom.appLE (𝟙 T) O O h = 𝟙 _ := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    rw [show (homOfLE h).op = 𝟙 (Opposite.op O) from rfl]
    exact T.presheaf.map_id _
  rw [this]
  rfl

/-- A section of `Spec k` pulled back to a scheme over `k` is the structural image of its value. -/
theorem appLE_eq_baseRingHom {T : Scheme.{u}} (gT : T ⟶ Spec (.of k)) (O : T.Opens)
    (h : O ≤ gT ⁻¹ᵁ ⊤) (s : Γ(Spec (CommRingCat.of k), ⊤)) :
    (gT.appLE ⊤ O h).hom s =
      (baseRingHom gT O).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom s) := by
  refine Eq.trans ?_ (congrArg (fun φ : CommRingCat.of k ⟶ Γ(T, O) =>
    φ.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom s)) (baseRingHom_eq_appLE gT O h)).symm
  exact congrArg (gT.appLE ⊤ O h).hom (congrArg (fun φ => φ.hom s)
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id).symm

/-- If `j ≫ p = 𝟙`, restricting along `p` and then along `j` is the identity on sections. -/
private theorem appLE_appLE_apply_of_comp_eq_id {S P : Scheme.{u}} (j : S ⟶ P) (p : P ⟶ S)
    (hj : j ≫ p = 𝟙 S) (O : S.Opens) (W : P.Opens) (h : W ≤ p ⁻¹ᵁ O) (hle : O ≤ j ⁻¹ᵁ W)
    (x : Γ(S, O)) : (j.appLE W O hle).hom ((p.appLE O W h).hom x) = x := by
  have e := Scheme.Hom.appLE_comp_appLE j p O W O h hle
  rw [Scheme.Hom.appLE_congr_hom hj O O _ le_rfl] at e
  exact (congrArg (fun φ => φ.hom x) e).trans (id_appLE_apply _ _ x)

/-- If `j ≫ p = s ≫ y` with `y` a rational point, restricting along `p` and then along `j` factors
through evaluation at `y` and the structural map of `s`. -/
private theorem appLE_appLE_apply_of_comp_eq {S P T : Scheme.{u}} (s : S ⟶ Spec (.of k))
    (y : Spec (.of k) ⟶ T) (j : S ⟶ P) (p : P ⟶ T) (hj : j ≫ p = s ≫ y) (O : S.Opens)
    (V : T.Opens) (W : P.Opens) (h : W ≤ p ⁻¹ᵁ V) (hle : O ≤ j ⁻¹ᵁ W) (hy : ⊤ ≤ y ⁻¹ᵁ V)
    (x : Γ(T, V)) :
    (j.appLE W O hle).hom ((p.appLE V W h).hom x) =
      (baseRingHom s O).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
        ((y.appLE V ⊤ hy).hom x)) := by
  have e := Scheme.Hom.appLE_comp_appLE j p V W O h hle
  have e' := Scheme.Hom.appLE_comp_appLE s y V ⊤ O hy le_top
  rw [Scheme.Hom.appLE_congr_hom hj V O _
    (by rw [← hj]; exact hle.trans (j.preimage_mono h))] at e
  exact (congrArg (fun φ => φ.hom x) (e.trans e'.symm)).trans (appLE_eq_baseRingHom s _ le_top _)

variable (y0 : Spec (.of k) ⟶ Y) (hy0 : y0 ≫ g = 𝟙 _) (b0 : J) (hb0 : y0 ⁻¹ᵁ V b0 = ⊤)
  (j2 : X ⟶ P) (hj2r : j2 ≫ r = 𝟙 X) (hj2q : j2 ≫ q = f ≫ y0)

include hj2r hj2q hb0 in
/-- The face `j2 : X ⟶ P` maps `U_a` into the box over `(a, ![b0])`. -/
theorem le_face2 {m : ℕ} (a : Fin m → I) :
    CechCochains.inter U a ≤ j2 ⁻¹ᵁ box r q U V a ![b0] := by
  change _ ≤ j2 ⁻¹ᵁ (r ⁻¹ᵁ CechCochains.inter U a) ⊓ j2 ⁻¹ᵁ (q ⁻¹ᵁ CechCochains.inter V ![b0])
  refine le_inf ?_ ?_
  · rw [← Scheme.Hom.comp_preimage, hj2r]
    exact le_rfl
  · rw [← Scheme.Hom.comp_preimage, hj2q, Scheme.Hom.comp_preimage, inter_fin1, hb0,
      Scheme.Hom.preimage_top]
    exact le_top

include hj2r hj2q in
/-- **The face `X ⟶ P` at `y₀`, on the bicomplex: evaluation of the `V`-factor at `y₀`.** -/
theorem face2_tmul {m : ℕ} (a : Fin (m + 1) → I)
    (c : CechCochains.Cochain U (OM X).presheaf m) (d : CechCochains.Cochain V (OM Y).presheaf 0) :
    letI := cochainModule f U (OM X) m
    letI := cochainModule g V (OM Y) 0
    (j2.appLE (box r q U V a ![b0]) (CechCochains.inter U a)
      (le_face2 U V y0 b0 hb0 j2 hj2r hj2q a)).hom (psi H U V m 0 (c ⊗ₜ d) a ![b0]) =
      (ev V y0 hy0 b0 hb0 d • c) a := by
  let := cochainModule f U (OM X) m
  let := cochainModule g V (OM Y) 0
  have hle := le_face2 U V y0 b0 hb0 j2 hj2r hj2q a
  have hy : (⊤ : (Spec (CommRingCat.of k)).Opens) ≤ y0 ⁻¹ᵁ CechCochains.inter V ![b0] := by
    rw [inter_fin1, hb0]
  rw [psi_tmul, cochain_smul_apply]
  change (j2.appLE _ _ hle).hom ((r.appLE _ _ inf_le_left).hom (c a) *
      (q.appLE _ _ inf_le_right).hom (d ![b0])) =
    (baseRingHom f (CechCochains.inter U a)).hom (ev V y0 hy0 b0 hb0 d) *
      (show Γ(X, CechCochains.inter U a) from c a)
  rw [map_mul]
  exact (congrArg₂ (· * ·) (appLE_appLE_apply_of_comp_eq_id j2 r hj2r _ _ inf_le_left hle (c a))
    (appLE_appLE_apply_of_comp_eq f y0 j2 q hj2q _ _ _ inf_le_right hle hy (d ![b0]))).trans
    (mul_comm _ _)

include hj2r hj2q in
/-- Pulling `psi x` back along the face `j2 : X ⟶ P` at `(a, ![b0])` is the component at `a` of the
image of `x` under evaluation of the `V`-factor at `y0`. -/
theorem face2 {m : ℕ} (a : Fin (m + 1) → I) :
    letI := cochainModule f U (OM X) m
    letI := cochainModule g V (OM Y) 0
    ∀ x : CechCochains.Cochain U (OM X).presheaf m ⊗[k] CechCochains.Cochain V (OM Y).presheaf 0,
    (j2.appLE (box r q U V a ![b0]) (CechCochains.inter U a)
      (le_face2 U V y0 b0 hb0 j2 hj2r hj2q a)).hom (psi H U V m 0 x a ![b0]) =
      TensorProduct.rid k _ ((ev V y0 hy0 b0 hb0).lTensor _ x) a := by
  let := cochainModule f U (OM X) m
  let := cochainModule g V (OM Y) 0
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; exact map_zero _
  | add x y hx hy =>
    rw [map_add, map_add, map_add]
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) hx hy)
  | tmul c d =>
    rw [face2_tmul H U V y0 hy0 b0 hb0 j2 hj2r hj2q a c d, LinearMap.lTensor_tmul,
      TensorProduct.rid_tmul]

variable (x0 : Spec (.of k) ⟶ X) (hx0 : x0 ≫ f = 𝟙 _) (a0 : I) (ha0 : x0 ⁻¹ᵁ U a0 = ⊤)
  (j1 : Y ⟶ P) (hj1r : j1 ≫ r = g ≫ x0) (hj1q : j1 ≫ q = 𝟙 Y)

include hj1r hj1q ha0 in
/-- The face `j1 : Y ⟶ P` maps `V_b` into the box over `(![a0], b)`. -/
theorem le_face1 {n : ℕ} (b : Fin n → J) :
    CechCochains.inter V b ≤ j1 ⁻¹ᵁ box r q U V ![a0] b := by
  change _ ≤ j1 ⁻¹ᵁ (r ⁻¹ᵁ CechCochains.inter U ![a0]) ⊓ j1 ⁻¹ᵁ (q ⁻¹ᵁ CechCochains.inter V b)
  refine le_inf ?_ ?_
  · rw [← Scheme.Hom.comp_preimage, hj1r, Scheme.Hom.comp_preimage, inter_fin1, ha0,
      Scheme.Hom.preimage_top]
    exact le_top
  · rw [← Scheme.Hom.comp_preimage, hj1q]
    exact le_rfl

include hj1r hj1q in
/-- Pulling `psi (c ⊗ₜ d)` back along the face `j1 : Y ⟶ P` at `(![a0], b)` is the component at `b`
of `d` scaled by the evaluation `ev U x0 hx0 a0 ha0 c` of `c` at `x0`. -/
theorem face1_tmul {n : ℕ} (b : Fin (n + 1) → J)
    (c : CechCochains.Cochain U (OM X).presheaf 0) (d : CechCochains.Cochain V (OM Y).presheaf n) :
    letI := cochainModule f U (OM X) 0
    letI := cochainModule g V (OM Y) n
    (j1.appLE (box r q U V ![a0] b) (CechCochains.inter V b)
      (le_face1 U V x0 a0 ha0 j1 hj1r hj1q b)).hom (psi H U V 0 n (c ⊗ₜ d) ![a0] b) =
      (ev U x0 hx0 a0 ha0 c • d) b := by
  let := cochainModule f U (OM X) 0
  let := cochainModule g V (OM Y) n
  have hle := le_face1 U V x0 a0 ha0 j1 hj1r hj1q b
  have hx : (⊤ : (Spec (CommRingCat.of k)).Opens) ≤ x0 ⁻¹ᵁ CechCochains.inter U ![a0] := by
    rw [inter_fin1, ha0]
  rw [psi_tmul, cochain_smul_apply]
  change (j1.appLE _ _ hle).hom ((r.appLE _ _ inf_le_left).hom (c ![a0]) *
      (q.appLE _ _ inf_le_right).hom (d b)) =
    (baseRingHom g (CechCochains.inter V b)).hom (ev U x0 hx0 a0 ha0 c) *
      (show Γ(Y, CechCochains.inter V b) from d b)
  rw [map_mul]
  exact congrArg₂ (· * ·)
    (appLE_appLE_apply_of_comp_eq g x0 j1 r hj1r _ _ _ inf_le_left hle hx (c ![a0]))
    (appLE_appLE_apply_of_comp_eq_id j1 q hj1q _ _ inf_le_right hle (d b))

include hj1r hj1q in
/-- Pulling `psi x` back along the face `j1 : Y ⟶ P` at `(![a0], b)` is the component at `b` of the
image of `x` under evaluation of the `U`-factor at `x0`. -/
theorem face1 {n : ℕ} (b : Fin (n + 1) → J) :
    letI := cochainModule f U (OM X) 0
    letI := cochainModule g V (OM Y) n
    ∀ x : CechCochains.Cochain U (OM X).presheaf 0 ⊗[k] CechCochains.Cochain V (OM Y).presheaf n,
    (j1.appLE (box r q U V ![a0] b) (CechCochains.inter V b)
      (le_face1 U V x0 a0 ha0 j1 hj1r hj1q b)).hom (psi H U V 0 n x ![a0] b) =
      TensorProduct.lid k _ ((ev U x0 hx0 a0 ha0).rTensor _ x) b := by
  let := cochainModule f U (OM X) 0
  let := cochainModule g V (OM Y) n
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; exact map_zero _
  | add x y hx hy =>
    rw [map_add, map_add, map_add]
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) hx hy)
  | tmul c d =>
    rw [face1_tmul H U V x0 hx0 a0 ha0 j1 hj1r hj1q b c d, LinearMap.rTensor_tmul,
      TensorProduct.lid_tmul]

include H hx0 hy0 in
/-- **Künneth injectivity on first Čech cohomology.** Let `k` be a field, `P = X ×_k Y` with
projections `r`, `q`, and let `U`, `V` be finite covers of `X`, `Y` by affine opens with affine
finite intersections, with `Γ(X, 𝒪) = k = Γ(Y, 𝒪)`. Let `x₀ ∈ U_{a₀}` and `y₀ ∈ V_{b₀}` be
rational points with faces `j₁ : Y ⟶ P`, `j₂ : X ⟶ P` through them. Then a Čech `1`-cocycle `z`
of `𝒪_P` for the cover `W` by the boxes `r⁻¹ U_a ∩ q⁻¹ V_b` is a coboundary as soon as its
pullbacks along the two faces are coboundaries. -/
theorem exists_cechD_eq_of_faces [Finite I] [Finite J] (W' : I × J → P.Opens)
    (hle : ∀ t : I × J, box r q U V ![t.1] ![t.2] ≤ W' t)
    (hge : ∀ t : I × J, W' t ≤ box r q U V ![t.1] ![t.2])
    (hUa : ∀ (m : ℕ) (a : Fin (m + 1) → I), IsAffineOpen (CechCochains.inter U a))
    (hVa : ∀ (n : ℕ) (b : Fin (n + 1) → J), IsAffineOpen (CechCochains.inter V b))
    (hWa : ∀ (m n : ℕ) (a : Fin (m + 1) → I) (b : Fin (n + 1) → J),
      IsAffineOpen (box r q U V a b))
    (hU : ⊤ ≤ ⨆ a, U a) (hV : ⊤ ≤ ⨆ b, V b)
    (hΓX : Function.Bijective (globalRingHom f).hom)
    (hΓY : Function.Bijective (globalRingHom g).hom)
    (z : CechCochains.Cochain W' (OM P).presheaf 1)
    (hz : CechCochains.cechD W' (OM P).presheaf 1 z = 0)
    (h2 : ∃ t : CechCochains.Cochain U (OM X).presheaf 0,
      CechCochains.cechD U (OM X).presheaf 0 t = fun a =>
        (j2.appLE (box r q U V a ![b0]) (CechCochains.inter U a)
          (le_face2 U V y0 b0 hb0 j2 hj2r hj2q a)).hom (to10 r q U V W' hle z a ![b0]))
    (h1 : ∃ t : CechCochains.Cochain V (OM Y).presheaf 0,
      CechCochains.cechD V (OM Y).presheaf 0 t = fun b =>
        (j1.appLE (box r q U V ![a0] b) (CechCochains.inter V b)
          (le_face1 U V x0 a0 ha0 j1 hj1r hj1q b)).hom (to01 r q U V W' hle z ![a0] b)) :
    ∃ e : CechCochains.Cochain W' (OM P).presheaf 0,
      CechCochains.cechD W' (OM P).presheaf 0 e = z := by
  let := cochainModule f U (OM X) 0
  let := cochainModule f U (OM X) 1
  let := cochainModule f U (OM X) 2
  let := cochainModule g V (OM Y) 0
  let := cochainModule g V (OM Y) 1
  let := fun m n => biModule r q U V (r ≫ f) m n
  have hψ := fun m n => bijective_psi H U V m n (hUa m) (hVa n) (hWa m n)
  obtain ⟨α, hα⟩ := (hψ 1 0).2 (to10 r q U V W' hle z)
  obtain ⟨β, hβ⟩ := (hψ 0 1).2 (to01 r q U V W' hle z)
  have hα' : (cechModuleD f U (OM X) 1).rTensor _ α = 0 := (hψ 2 0).1 (by
    rw [psi_rTensor, hα, dh_to10 r q U V W' hle z hz, map_zero])
  have hαβ : (cechModuleD g V (OM Y) 0).lTensor _ α = (cechModuleD f U (OM X) 0).rTensor _ β :=
    (hψ 1 1).1 (by rw [psi_lTensor, psi_rTensor, hα, hβ, dv_to10 r q U V W' hle z hz])
  obtain ⟨e, he1, he2⟩ := StacksDraft.KunnethOne.exists_eq_of_faces
    (dC0 := cechModuleD f U (OM X) 0) (dC1 := cechModuleD f U (OM X) 1)
    (dD0 := cechModuleD g V (OM Y) 0) (dCp := (0 : k →ₗ[k] k)) (η0 := ev U x0 hx0 a0 ha0)
    (η1 := (0 : CechCochains.Cochain U (OM X).presheaf 1 →ₗ[k] k))
    (by rw [LinearMap.zero_comp, LinearMap.zero_comp]) (ev V y0 hy0 b0 hb0)
    (LinearMap.ext fun t => CechCochains.cechD_cechD U _ 0 t) (unitCochain0 U)
    (ker_cechD_zero_le f U hU hΓX) (cechD_unitCochain0 U)
    (by
      rw [ev_unitCochain0]
      intro t _
      exact Submodule.mem_span_singleton.2 ⟨t, by rw [smul_eq_mul, mul_one]⟩)
    (by rw [ev_unitCochain0]; exact one_ne_zero) (unitCochain0 V)
    (ker_cechD_zero_le g V hV hΓY) (by rw [ev_unitCochain0]; exact one_ne_zero) α β hα' hαβ
    (by
      obtain ⟨t, ht⟩ := h2
      refine ⟨t ⊗ₜ 1, (TensorProduct.rid k _).injective ?_⟩
      rw [LinearMap.rTensor_tmul, TensorProduct.rid_tmul, one_smul]
      change CechCochains.cechD U _ 0 t = _
      rw [ht]
      funext a
      rw [← face2 H U V y0 hy0 b0 hb0 j2 hj2r hj2q a α, hα])
    (by
      obtain ⟨t, ht⟩ := h1
      refine ⟨1 ⊗ₜ t, by rw [LinearMap.rTensor_zero, LinearMap.rTensor_zero,
        LinearMap.zero_apply, LinearMap.zero_apply], (TensorProduct.lid k _).injective ?_⟩
      rw [LinearMap.lTensor_tmul, TensorProduct.lid_tmul, one_smul]
      change CechCochains.cechD V _ 0 t = _
      rw [ht]
      funext b
      rw [← face1 H U V x0 hx0 a0 ha0 j1 hj1r hj1q b β, hβ])
  refine ⟨from00 r q U V W' hge (psi H U V 0 0 e), cechD_from00 r q U V W' hle hge z hz _ ?_ ?_⟩
  · rw [← psi_rTensor, he1, hα]
  · rw [← psi_lTensor, he2, hβ]

end Faces

end Stacks.Cech.Kunneth

end
