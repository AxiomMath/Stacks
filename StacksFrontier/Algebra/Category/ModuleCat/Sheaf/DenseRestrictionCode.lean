module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasiIsoOfLocalSections

/-!
# Codes for complexes of sheaves of modules through their sections over a dense family

Let `(C, J)` be a site, `R` a sheaf of rings on it and `c : ι → C` a dense family of objects.  A
cochain complex `M` of sheaves of `R`-modules is determined up to isomorphism by its sections
over the objects `c i` together with their module structures, the restriction maps along the
arrows between the `c i` and the differentials: restriction to the dense subsite spanned by the
family is fully faithful (`Stacks.DenseSubsiteModules.moduleRestriction`).

This file records that data, after embedding the sections into a fixed type `L`, as a *code*,
and proves that two complexes with the same code are isomorphic.  Counting codes then bounds the
number of isomorphism classes of complexes whose sections over the family are bounded.

## Main definitions

* `Stacks.SheafOfModules.DenseCode.Code`: the type of codes.
* `Stacks.SheafOfModules.DenseCode.code`: the code of a complex along embeddings of its
  sections over the family.

## Main results

* `Stacks.SheafOfModules.DenseCode.nonempty_iso_of_code_eq`: complexes with equal codes are
  isomorphic.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t u'

namespace Stacks.SheafOfModules.DenseCode

variable {C : Type u'} [Category.{t} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {ι : Type t} (c : ι → C) (L : Type t)

/-- **Codes**: in every degree and over every object of the family, a subset of `L` (the
sections), an addition and a scalar multiplication on `L`, the restriction maps to the other
objects of the family, and the differential. -/
abbrev Code := ∀ (_ : ℤ) (i : ι), Set L × (L → L → L) × (R.obj.obj (op (c i)) → L → L) ×
    (∀ j : ι, (c j ⟶ c i) → L → L) × (L → L)

variable {c L}

/-- **The code of a complex** along maps of its sections over the family into `L`. -/
def code (M : CochainComplex (_root_.SheafOfModules.{t} R) ℤ)
    (e : ∀ (n : ℤ) (i : ι), (M.X n).val.obj (op (c i)) → L) : Code (R := R) c L :=
  fun n i =>
    (Set.range (e n i),
      fun a b => e n i (Function.invFun (e n i) a + Function.invFun (e n i) b),
      fun r a => e n i (r • Function.invFun (e n i) a),
      fun j h a => e n j ((M.X n).val.map h.op (Function.invFun (e n i) a)),
      fun a => e (n + 1) i ((M.d n (n + 1)).val.app _ (Function.invFun (e n i) a)))

section Cardinal

open Cardinal

/-- A dependent product over a type bounded by an infinite cardinal `λ` of types bounded by
`2 ^ λ` is bounded by `2 ^ λ`. -/
theorem mk_pi_le_two_power {α : Type t} {β : α → Type t} {μ : Cardinal.{t}} (hμ : ℵ₀ ≤ μ)
    (hα : #α ≤ μ) (hβ : ∀ a, #(β a) ≤ 2 ^ μ) : #(∀ a, β a) ≤ 2 ^ μ := by
  rw [Cardinal.mk_pi]
  refine (Cardinal.prod_le_prod _ _ hβ).trans ?_
  rw [Cardinal.prod_const']
  calc (2 ^ μ) ^ #α ≤ (2 ^ μ) ^ μ :=
        Cardinal.power_le_power_left (Cardinal.power_ne_zero _ two_ne_zero) hα
    _ = 2 ^ μ := by rw [← Cardinal.power_mul, Cardinal.mul_eq_self hμ]

/-- A dependent product over `ℤ` of types bounded by `2 ^ λ`, for an infinite cardinal `λ`, is
bounded by `2 ^ λ`. -/
theorem mk_pi_int_le_two_power {β : ℤ → Type t} {μ : Cardinal.{t}} (hμ : ℵ₀ ≤ μ)
    (hβ : ∀ n, #(β n) ≤ 2 ^ μ) : #(∀ n, β n) ≤ 2 ^ μ := by
  rw [← Cardinal.mk_congr (Equiv.piCongrLeft β (Equiv.ulift.{t} (α := ℤ)))]
  refine mk_pi_le_two_power hμ ?_ (fun n => hβ n.down)
  rwa [Cardinal.mk_uLift, Cardinal.mk_int, Cardinal.lift_aleph0]

/-- A product of two types bounded by `2 ^ λ` is bounded by `2 ^ λ`. -/
theorem mk_prod_le_two_power {A B : Type t} {μ : Cardinal.{t}} (hμ : ℵ₀ ≤ μ)
    (hA : #A ≤ 2 ^ μ) (hB : #B ≤ 2 ^ μ) : #(A × B) ≤ 2 ^ μ := by
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  exact (mul_le_mul' hA hB).trans (Cardinal.mul_eq_self (hμ.trans (Cardinal.cantor μ).le)).le

/-- **The codes are bounded by `2 ^ λ`** when `L`, the family, its arrows and its rings of
sections are bounded by an infinite cardinal `λ`. -/
theorem mk_code_le {μ : Cardinal.{t}} (hμ : ℵ₀ ≤ μ) (hL : #L ≤ μ) (hι : #ι ≤ μ)
    (hHom : ∀ i j : ι, #(c j ⟶ c i) ≤ μ) (hR : ∀ i : ι, #(R.obj.obj (op (c i))) ≤ μ) :
    #(Code (R := R) c L) ≤ 2 ^ μ := by
  have hLL : #L ≤ 2 ^ μ := hL.trans (Cardinal.cantor μ).le
  have harr : ∀ (A : Type t), #A ≤ μ → #(A → L) ≤ 2 ^ μ := fun A hA =>
    mk_pi_le_two_power hμ hA (fun _ => hLL)
  refine mk_pi_int_le_two_power hμ (fun n => mk_pi_le_two_power hμ hι (fun i => ?_))
  refine mk_prod_le_two_power hμ ?_ (mk_prod_le_two_power hμ ?_ (mk_prod_le_two_power hμ ?_
    (mk_prod_le_two_power hμ ?_ (harr L hL))))
  · rw [Cardinal.mk_set]
    exact Cardinal.power_le_power_left two_ne_zero hL
  · exact mk_pi_le_two_power hμ hL (fun _ => harr L hL)
  · exact mk_pi_le_two_power hμ (hR i) (fun _ => harr L hL)
  · exact mk_pi_le_two_power hμ hι (fun j => mk_pi_le_two_power hμ (hHom i j) (fun _ => harr L hL))

end Cardinal

section Transfer

variable {A B : Type*} [Nonempty B] {eA : A → L} {eB : B → L}

/-- Along embeddings with the same range, the comparison map from `A` to `B`. -/
def transfer (eA : A → L) (eB : B → L) : A → B := fun a => Function.invFun eB (eA a)

/-- If `eA` and `eB` have the same range, then `eB (transfer eA eB a) = eA a`. -/
theorem eB_transfer (hr : Set.range eA = Set.range eB) (a : A) : eB (transfer eA eB a) = eA a :=
  Function.invFun_eq (show eA a ∈ Set.range eB from hr ▸ ⟨a, rfl⟩)

/-- If `eB` is injective and `eA a = eB b`, then `transfer eA eB a = b`. -/
theorem transfer_eq_of_eq (hB : Function.Injective eB) {a : A} {b : B} (h : eA a = eB b) :
    transfer eA eB a = b := by
  simp only [transfer, h, Function.leftInverse_invFun hB b]

end Transfer

/-- `transfer` commutes with maps `F` and `G` that agree after composing with the embeddings. -/
private theorem transfer_comp_of_eq {A A' B B' : Type*} [Nonempty A] [Nonempty B] [Nonempty B']
    {eA : A → L} {eB : B → L} {eA' : A' → L} {eB' : B' → L} (hA : Function.Injective eA)
    (hB' : Function.Injective eB') (F : A → A') (G : B → B')
    (h : ∀ l, eA' (F (Function.invFun eA l)) = eB' (G (Function.invFun eB l))) (a : A) :
    transfer eA' eB' (F a) = G (transfer eA eB a) := by
  refine transfer_eq_of_eq hB' ?_
  simpa only [transfer, Function.leftInverse_invFun hA a] using h (eA a)

variable [hc : (inducedFunctor c).IsCoverDense J]

include hc in
/-- **Complexes with equal codes are isomorphic.**  The sections over the family are identified
along the embeddings; equality of the codes says that this identification respects the module
structures, the restriction maps between the objects of the family and the differentials, so it
is an isomorphism of the restrictions to the dense subsite spanned by the family, and restriction
to that subsite is fully faithful. -/
theorem nonempty_iso_of_code_eq {M N : CochainComplex (_root_.SheafOfModules.{t} R) ℤ}
    (eM : ∀ (n : ℤ) (i : ι), (M.X n).val.obj (op (c i)) → L)
    (eN : ∀ (n : ℤ) (i : ι), (N.X n).val.obj (op (c i)) → L)
    (hM : ∀ n i, Function.Injective (eM n i)) (hN : ∀ n i, Function.Injective (eN n i))
    (h : code M eM = code N eN) : Nonempty (M ≅ N) := by
  have hr : ∀ n i, Set.range (eM n i) = Set.range (eN n i) :=
    fun n i => congrArg Prod.fst (congrFun (congrFun h n) i)
  have hadd := fun n i => congrArg (fun q => q.2.1) (congrFun (congrFun h n) i)
  have hsmul := fun n i => congrArg (fun q => q.2.2.1) (congrFun (congrFun h n) i)
  have hres := fun n i => congrArg (fun q => q.2.2.2.1) (congrFun (congrFun h n) i)
  have hd := fun n i => congrArg (fun q => q.2.2.2.2) (congrFun (congrFun h n) i)
  simp only [code] at hadd hsmul hres hd
  -- the comparison maps and their properties
  have hinv : ∀ n i x, Function.invFun (eM n i) (eM n i x) = x :=
    fun n i x => Function.leftInverse_invFun (hM n i) x
  let φ : ∀ n i, (M.X n).val.obj (op (c i)) → (N.X n).val.obj (op (c i)) :=
    fun n i => transfer (eM n i) (eN n i)
  let ψ : ∀ n i, (N.X n).val.obj (op (c i)) → (M.X n).val.obj (op (c i)) :=
    fun n i => transfer (eN n i) (eM n i)
  have hφψ : ∀ n i y, φ n i (ψ n i y) = y := fun n i y =>
    transfer_eq_of_eq (hN n i) (eB_transfer (hr n i).symm y)
  have hψφ : ∀ n i x, ψ n i (φ n i x) = x := fun n i x =>
    transfer_eq_of_eq (hM n i) (eB_transfer (hr n i) x)
  have φ_add : ∀ n i x y, φ n i (x + y) = φ n i x + φ n i y := fun n i x y =>
    transfer_eq_of_eq (hN n i) (by
      simpa only [hinv, φ, transfer] using congrFun (congrFun (hadd n i) (eM n i x)) (eM n i y))
  have φ_smul : ∀ n i (r : R.obj.obj (op (c i))) x, φ n i (r • x) = r • φ n i x :=
    fun n i r x => transfer_comp_of_eq (hM n i) (hN n i) (r • ·) (r • ·)
      (congrFun (congrFun (hsmul n i) r)) x
  have φ_res : ∀ n i j (f : c j ⟶ c i) x,
      φ n j ((M.X n).val.map f.op x) = (N.X n).val.map f.op (φ n i x) :=
    fun n i j f x => transfer_comp_of_eq (hM n i) (hN n j) _ _
      (congrFun (congrFun (congrFun (hres n i) j) f)) x
  have φ_d : ∀ n i x, φ (n + 1) i ((M.d n (n + 1)).val.app _ x) =
      (N.d n (n + 1)).val.app _ (φ n i x) :=
    fun n i x => transfer_comp_of_eq (hM n i) (hN (n + 1) i) _ _ (congrFun (hd n i)) x
  let Fr := DenseSubsiteModules.moduleRestriction ((inducedFunctor c).inducedTopology J) J
    (inducedFunctor c) R
  have : Fr.Additive := ⟨fun {_ _ _ _} => rfl⟩
  have ψ_smul : ∀ n i (r : R.obj.obj (op (c i))) y, ψ n i (r • y) = r • ψ n i y :=
    fun n i r y => transfer_comp_of_eq (hN n i) (hM n i) (r • ·) (r • ·)
      (fun l => (congrFun (congrFun (hsmul n i) r) l).symm) y
  have ψ_add : ∀ n i x y, ψ n i (x + y) = ψ n i x + ψ n i y := by
    intro n i x y
    have hφinj : Function.Injective (φ n i) := Function.LeftInverse.injective (hψφ n i)
    apply hφinj
    rw [hφψ, φ_add, hφψ, hφψ]
  have ψ_res : ∀ n i j (f : c j ⟶ c i) y,
      ψ n j ((N.X n).val.map f.op y) = (M.X n).val.map f.op (ψ n i y) :=
    fun n i j f y => transfer_comp_of_eq (hN n i) (hM n j) _ _
      (fun l => (congrFun (congrFun (congrFun (hres n i) j) f) l).symm) y
  let e : ∀ n, Fr.obj (M.X n) ≅ Fr.obj (N.X n) := by
    intro n
    let φn : (Fr.obj (M.X n)).val.presheaf ⟶ (Fr.obj (N.X n)).val.presheaf :=
      { app := fun i => AddCommGrpCat.ofHom (AddMonoidHom.mk' (φ n i.unop) (φ_add n i.unop))
        naturality := fun i i' f => by
          ext x
          exact φ_res n i.unop i'.unop f.unop.hom x }
    let ψn : (Fr.obj (N.X n)).val.presheaf ⟶ (Fr.obj (M.X n)).val.presheaf :=
      { app := fun i => AddCommGrpCat.ofHom (AddMonoidHom.mk' (ψ n i.unop) (ψ_add n i.unop))
        naturality := fun i i' f => by
          ext y
          exact ψ_res n i.unop i'.unop f.unop.hom y }
    refine (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso
      { hom := PresheafOfModules.homMk φn (fun i r x => φ_smul n i.unop r x)
        inv := PresheafOfModules.homMk ψn (fun i r y => ψ_smul n i.unop r y)
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · ext i x
      exact hψφ n i.unop x
    · ext i y
      exact hφψ n i.unop y
  let E : (Fr.mapHomologicalComplex (ComplexShape.up ℤ)).obj M ≅
      (Fr.mapHomologicalComplex (ComplexShape.up ℤ)).obj N :=
    HomologicalComplex.Hom.isoOfComponents e (fun n n' hnn' => by
      change n + 1 = n' at hnn'
      subst hnn'
      apply _root_.SheafOfModules.hom_ext
      ext i x
      rw [_root_.SheafOfModules.comp_val_app_apply, _root_.SheafOfModules.comp_val_app_apply]
      show (N.d n (n + 1)).val.app _ (φ n i.unop x) =
        φ (n + 1) i.unop ((M.d n (n + 1)).val.app _ x)
      exact (φ_d n i.unop x).symm)
  exact ⟨(Functor.FullyFaithful.ofFullyFaithful
    (Fr.mapHomologicalComplex (ComplexShape.up ℤ))).preimageIso E⟩

end Stacks.SheafOfModules.DenseCode
