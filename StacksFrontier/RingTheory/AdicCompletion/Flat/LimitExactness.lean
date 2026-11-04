module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Logic.Small.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Jacobson.Ring
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Tor.ProZero
public import StacksFrontier.RingTheory.AdicCompletion.KerEval
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Coherent.Flat
public import StacksFrontier.RingTheory.Flat.TorCriterion
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
public import StacksFrontier.RingTheory.Tor.Balancing
public import StacksFrontier.RingTheory.Ideal.SmulTop
public import StacksFrontier.CategoryTheory.MittagLefflerSections
public import StacksFrontier.RingTheory.UniversallyExact
public import StacksFrontier.RingTheory.Flat.FibreCriterionNilpotent

/-!
# Exactness of adic completion and of limits of towers of modules

For `R` Noetherian, this file proves that `R → R^∧` is faithfully flat when `I` is contained in
the Jacobson radical, and that completion carries short exact sequences with finite middle term to
short exact sequences. It then gives the auxiliary results for
`flat_limit_and_tensor_limit_of_flat_quotients`: levelwise tensor products of towers, pro-zero
towers of `Tor₁`, Mittag-Leffler towers, and criteria for the induced map on limits of a map of
towers of modules to be injective, surjective or right exact.

## Main results

* `AdicCompletion.faithfullyFlat_of_le_ringJacobson`
* `adicCompletion_shortExact`
-/

@[expose] public section

universe u v

/-- Let `I` be an ideal of a Noetherian ring `R` and let `R^∧` be the `I`-adic completion of `R`.
If `I` is contained in the Jacobson radical of `R`, then the ring map `R → R^∧` is faithfully flat.
In particular, if `(R, 𝔪)` is a Noetherian local ring, then the completion `lim_n R/𝔪ⁿ` is
faithfully flat over `R`. -/
@[stacks 00MC "Stated as the class `Module.FaithfullyFlat R (AdicCompletion I R)`, the shape of the
flatness half `AdicCompletion.flat_of_isNoetherian`; the `in particular` is the case `I = 𝔪`. See
the module docstring.", ega "0 7.3.5" "(a) => (b)", sga "1 IV 3.2" "if direction", sga "1 IV 3.1"
  "flatness, I ⊆ rad", sga "1 IV 3.1" "flatness, I ⊆ rad", sga "3 VIIB 5.5.2" "partial"]
public theorem AdicCompletion.faithfullyFlat_of_le_ringJacobson {R : Type*} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) (hI : I ≤ Ring.jacobson R) :
    Module.FaithfullyFlat R (AdicCompletion I R) := by
  rw [Module.faithfullyFlat_iff]
  refine ⟨AdicCompletion.flat_of_isNoetherian I, fun {m} hm => ?_⟩
  refine smul_top_ne_top_of_surjective m
    (f := (AdicCompletion.evalOneₐ I).toLinearMap) (AdicCompletion.evalOneₐ_surjective I) ?_
  rw [ne_eq, smul_top_quotient_eq_top_iff,
    sup_eq_left.mpr (hI.trans (Ring.jacobson_le_of_isMaximal m))]
  exact hm.ne_top

/-! For an ideal `I` of a Noetherian ring `R`, completion preserves injectivity of a map into a
finite module (`AdicCompletion.map_injective`), carries a short exact sequence of finite modules
to a short exact sequence (together with `AdicCompletion.map_surjective` and
`AdicCompletion.map_exact`), and satisfies `M^∧ = M ⊗_R R^∧` for finite `M`
(`AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian`). -/

add_to_stacks 00MA "(1), and the injectivity half of (2)" AdicCompletion.map_injective
add_to_stacks 00MA "(2): surjectivity of the completed second map"
  AdicCompletion.map_surjective
add_to_ega "0 7.3.1" "v̂ surjective" AdicCompletion.map_surjective
add_to_stacks 00MA "(2): exactness in the middle of the completed sequence"
  AdicCompletion.map_exact
add_to_sga "3 VIIB 5.5.2" "partial" AdicCompletion.map_exact
add_to_ega "0 7.3.3" "partial" AdicCompletion.map_exact
add_to_ega "0 7.3.1" "Noetherian, finite mods" AdicCompletion.map_exact
add_to_stacks 00MA "(3)" AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian
add_to_ega "0 7.3.3" AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian
add_to_ega "0 7.7.8" "B = Â" AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian

/-! Part (1) of Stacks 00MB, that for a Noetherian ring `R` and any ideal `I` the canonical ring
map `R → R^∧` is flat, is Mathlib's instance `AdicCompletion.flat_of_isNoetherian`. -/

add_to_stacks 00MB "(1)" AdicCompletion.flat_of_isNoetherian
add_to_sga "1 IV 3.1" AdicCompletion.flat_of_isNoetherian
add_to_sga "3 VIIB 5.5.2" "flatness of Â over A" AdicCompletion.flat_of_isNoetherian
add_to_ega "0 7.3.3" AdicCompletion.flat_of_isNoetherian
add_to_ega "IV 7.8.3" "(v)" AdicCompletion.flat_of_isNoetherian
add_to_ega "IV 8.11.4" "partial" AdicCompletion.flat_of_isNoetherian

/-- For a Noetherian ring $R$, every short exact sequence $0 \to M' \to M \to M'' \to 0$ of
$R$-modules with $M$ finitely generated completes to a short exact sequence
$0 \to (M')^\wedge \to M^\wedge \to (M'')^\wedge \to 0$. -/
@[stacks 00MB "(2)", ega "0 7.3.1" "special case", ega "0 7.3.3", sga "3 VIIB 5.5.2" "partial"]
theorem adicCompletion_shortExact {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {M' M M'' : Type u} [AddCommGroup M'] [Module R M'] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [AddCommGroup M''] [Module R M'']
    {f : M' →ₗ[R] M} {g : M →ₗ[R] M''} (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    Function.Injective (AdicCompletion.map I f) ∧
    Function.Surjective (AdicCompletion.map I g) ∧
    Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) :=
  ⟨AdicCompletion.map_injective I hf, AdicCompletion.map_surjective I hg,
    AdicCompletion.map_exact hf hfg hg⟩

section FlatLimit

set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits

/-- Tensor a tower levelwise with a fixed module. -/
private abbrev tensorTower {A : Type u} [CommRing A]
    (Q : ModuleCat.{u} A) (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) :
    ℕᵒᵖ ⥤ ModuleCat.{u} A :=
  M ⋙ (MonoidalCategory.tensoringLeft (ModuleCat.{u} A)).obj Q

/-- Surjective transition maps stay surjective after levelwise tensoring. -/
private theorem tensorTower_successor_surjective
    {A : Type u} [CommRing A] (Q : ModuleCat.{u} A)
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hsurj : ∀ n : ℕ, Function.Surjective
      (M.map (homOfLE (Nat.le_succ n)).op))
    (n : ℕ) : Function.Surjective
      ((tensorTower Q M).map (homOfLE (Nat.le_succ n)).op) := by
  show Function.Surjective
    (LinearMap.lTensor (Q : Type u) (M.map (homOfLE (Nat.le_succ n)).op).hom)
  exact LinearMap.lTensor_surjective _ (hsurj n)

/-- Tensoring with a finite free module is a finite product. -/
private noncomputable def finiteFreeTensorEquiv
    {A : Type u} [CommRing A] (r : ℕ) (N : ModuleCat.{u} A) :
    TensorProduct A (Fin r → A) N ≃ₗ[A] (Fin r → N) :=
  TensorProduct.comm A (Fin r → A) N ≪≫ₗ
    TensorProduct.piScalarRight A A N (Fin r)

/-- The finite free tensor identification commutes with maps in the second factor. -/
private theorem finiteFreeTensorEquiv_natural
    {A : Type u} [CommRing A] (r : ℕ)
    (N P : ModuleCat.{u} A) (f : N ⟶ P)
    (x : TensorProduct A (Fin r → A) N) :
    finiteFreeTensorEquiv r P (LinearMap.lTensor (Fin r → A) f.hom x) =
      fun i => f (finiteFreeTensorEquiv r N x i) := by
  induction x using TensorProduct.induction_on with
  | zero => ext; simp
  | tmul a n => ext; simp [finiteFreeTensorEquiv, TensorProduct.piScalarRightHom_tmul]
  | add x y hx hy => ext; simp [map_add, hx, hy]

/-- The canonical tower of quotients by the powers of an ideal. -/
private noncomputable def idealQuotientTower {A : Type u} [CommRing A]
    (I : Ideal A) : ℕᵒᵖ ⥤ ModuleCat.{u} A where
  obj n := torProZeroQuot I n.unop
  map {i j} f := torProZeroTransition I (leOfHom f.unop)
  map_id i := by
    ext x
    induction x using Quotient.inductionOn' with
    | _ x => simp [torProZeroTransition, torProZeroQuot]
  map_comp f g := by
    ext x
    induction x using Quotient.inductionOn' with
    | _ x => simp [torProZeroTransition, torProZeroQuot]

/-- The first Tor groups against ideal-power quotients form a tower. -/
private noncomputable def torOneTower {A : Type u} [CommRing A]
    (I : Ideal A) (Q : ModuleCat.{u} A) : ℕᵒᵖ ⥤ ModuleCat.{u} A :=
  idealQuotientTower I ⋙ (Tor (ModuleCat.{u} A) 1).obj Q

/-- For a finite module `Q` over a Noetherian ring `A`, the tower `Tor₁(Q, A/Iⁿ)` is pro-zero:
for every `n` there is `m ≥ n` such that the transition map `Tor₁(Q, A/Iᵐ) → Tor₁(Q, A/Iⁿ)` is
zero. -/
private theorem torOneTower_prozero
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (Q : ModuleCat.{u} A) [Module.Finite A Q] :
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      (torOneTower I Q).map (homOfLE h).op = 0 := by
  obtain ⟨c, hcpos, hc⟩ := tor_pro_zero I Q (p := 1) (by omega)
  intro n
  let m := n + c + 1
  have hmn : n ≤ m := by omega
  have hmk : m - c ≤ m := Nat.sub_le m c
  have hkn : n ≤ m - c := by omega
  refine ⟨m, hmn, ?_⟩
  have heq : (homOfLE hmn).op =
      (homOfLE hmk).op ≫ (homOfLE hkn).op := Subsingleton.elim _ _
  rw [heq, (torOneTower I Q).map_comp]
  show ((Tor (ModuleCat.{u} A) 1).obj Q).map
      (torProZeroTransition I hmk) ≫ _ = 0
  rw [hc m (by omega)]
  exact zero_comp

/-- The levelwise tensor product of two towers. -/
private abbrev tensorPairTower {A : Type u} [CommRing A]
    (F G : ℕᵒᵖ ⥤ ModuleCat.{u} A) : ℕᵒᵖ ⥤ ModuleCat.{u} A :=
  F.prod' G ⋙ MonoidalCategory.tensor (ModuleCat.{u} A)

/-- Tensoring a pro-zero tower levelwise with an arbitrary tower is still pro-zero. -/
private theorem tensorPairTower_prozero_left
    {A : Type u} [CommRing A] (F G : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hzero : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      F.map (homOfLE h).op = 0) :
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      (tensorPairTower F G).map (homOfLE h).op = 0 := by
  intro n
  obtain ⟨m, h, hz⟩ := hzero n
  refine ⟨m, h, ?_⟩
  show MonoidalCategoryStruct.tensorHom
    (F.map (homOfLE h).op) (G.map (homOfLE h).op) = 0
  rw [hz, MonoidalPreadditive.zero_tensor]

/-- The pro-zero tower `Tor₁(Q, A/Iⁿ)` remains pro-zero after tensoring levelwise with a given
tower. -/
private theorem torOneTensorTower_prozero
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (Q : ModuleCat.{u} A) [Module.Finite A Q]
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) :
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      (tensorPairTower (torOneTower I Q) M).map (homOfLE h).op = 0 :=
  tensorPairTower_prozero_left _ _ (torOneTower_prozero I Q)

/-- A finite module `Q` over a Noetherian ring `A` has an exact sequence
`A^{r₂} → A^{r₁} → A^{r₀} → Q → 0`. -/
private theorem finite_free_resolution_three
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (Q : ModuleCat.{u} A) [Module.Finite A Q] :
    ∃ (r₂ r₁ r₀ : ℕ)
      (d₂ : (Fin r₂ → A) →ₗ[A] (Fin r₁ → A))
      (d₁ : (Fin r₁ → A) →ₗ[A] (Fin r₀ → A))
      (q : (Fin r₀ → A) →ₗ[A] Q),
      Function.Exact d₂ d₁ ∧ Function.Exact d₁ q ∧
        Function.Surjective q := by
  let : Module.FinitePresentation A Q :=
    Module.finitePresentation_of_finite A Q
  obtain ⟨r₀, r₁, q, d₁, hq, hex₁⟩ :=
    Module.FinitePresentation.exists_fin' A Q
  let : Module.Finite A (LinearMap.ker d₁) := inferInstance
  obtain ⟨r₂, d, hd⟩ := Module.Finite.exists_fin' A (LinearMap.ker d₁)
  let d₂ : (Fin r₂ → A) →ₗ[A] (Fin r₁ → A) :=
    (LinearMap.ker d₁).subtype.comp d
  refine ⟨r₂, r₁, r₀, d₂, d₁, q, ?_, hex₁, hq⟩
  rw [LinearMap.exact_iff, LinearMap.range_comp, LinearMap.range_eq_top.mpr hd]
  simp

/-- Surjectivity of the successor maps gives surjectivity of every transition map
in a tower of modules. -/
private theorem transition_surjective
    {A : Type u} [CommRing A] (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hsurj : ∀ n : ℕ, Function.Surjective
      (M.map (homOfLE (Nat.le_succ n)).op))
    {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (M.map (homOfLE h).op) := by
  induction n, h using Nat.le_induction with
  | base =>
      rw [show (homOfLE (le_refl m)).op = 𝟙 (Opposite.op m) from
        Subsingleton.elim _ _, M.map_id]
      exact fun x => ⟨x, rfl⟩
  | @succ n h ih =>
      have heq : ((homOfLE (Nat.le_succ n)).op : Opposite.op (n + 1) ⟶
          Opposite.op n) ≫ (homOfLE h).op =
          (homOfLE (h.trans (Nat.le_succ n))).op := Subsingleton.elim _ _
      rw [← heq, M.map_comp]
      exact ih.comp (hsurj n)

/-- A tower of modules with surjective successor transition maps is Mittag-Leffler. -/
private theorem tower_isMittagLeffler
    {A : Type u} [CommRing A] (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hsurj : ∀ n : ℕ, Function.Surjective
      (M.map (homOfLE (Nat.le_succ n)).op)) :
    (M ⋙ forget (ModuleCat.{u} A)).IsMittagLeffler := by
  apply CategoryTheory.Functor.isMittagLeffler_of_surjective
  intro i j f
  show Function.Surjective (M.map f)
  rw [show f = (homOfLE (leOfHom f.unop)).op from Subsingleton.elim _ _]
  exact transition_surjective M hsurj (leOfHom f.unop)

private theorem limit_projection_zero_surjective
    {A : Type u} [CommRing A] (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hsurj : ∀ n : ℕ, Function.Surjective
      (M.map (homOfLE (Nat.le_succ n)).op)) :
    Function.Surjective (limit.π M (Opposite.op 0)) :=
  Concrete.surjective_π_app_zero_of_surjective_map (limit.isLimit M) hsurj

/-- The tower of levelwise lifts of one element of an inverse limit. -/
private noncomputable def fiberTower
    {A : Type u} [CommRing A] {F G : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (α : F ⟶ G) (g : (limit G : ModuleCat.{u} A)) : ℕᵒᵖ ⥤ Type u where
  obj i := {x : F.obj i // (α.app i) x = (limit.π G i) g}
  map {i j} f := ↾fun x => ⟨(F.map f) x.1, by
    calc
      (α.app j) ((F.map f) x.1) = (G.map f) ((α.app i) x.1) := by
        have h := congrArg (fun k : F.obj i ⟶ G.obj j => k x.1) (α.naturality f)
        exact h
      _ = (G.map f) ((limit.π G i) g) := by rw [x.2]
      _ = (limit.π G j) g := by
        have h := congrArg (fun k : (limit G : ModuleCat.{u} A) ⟶ G.obj j => k g)
          (limit.w G f)
        exact h⟩
  map_id i := by
    ext x
    simp
  map_comp f h := by
    ext x
    simp

private theorem fiberTower_successor_surjective
    {A : Type u} [CommRing A] {F G : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (α : F ⟶ G) (g : (limit G : ModuleCat.{u} A))
    (hpoint : ∀ n : ℕ, Function.Surjective (α.app (Opposite.op n)))
    (hkernel : ∀ (n : ℕ) (x : F.obj (Opposite.op n)),
      (α.app (Opposite.op n)) x = 0 →
      ∃ y : F.obj (Opposite.op (n + 1)),
        (α.app (Opposite.op (n + 1))) y = 0 ∧
        (F.map (homOfLE (Nat.le_succ n)).op) y = x)
    (n : ℕ) : Function.Surjective
      ((fiberTower α g).map (homOfLE (Nat.le_succ n)).op) := by
  intro x
  let f : Opposite.op (n + 1) ⟶ Opposite.op n :=
    (homOfLE (Nat.le_succ n)).op
  obtain ⟨t, ht⟩ := hpoint (n + 1) ((limit.π G (Opposite.op (n + 1))) g)
  have hnat (y : F.obj (Opposite.op (n + 1))) :
      (α.app (Opposite.op n)) ((F.map f) y) =
        (G.map f) ((α.app (Opposite.op (n + 1))) y) :=
    congrArg (fun k : F.obj (Opposite.op (n + 1)) ⟶ G.obj (Opposite.op n) => k y)
      (α.naturality f)
  have hw : (G.map f) ((limit.π G (Opposite.op (n + 1))) g) =
      (limit.π G (Opposite.op n)) g :=
    congrArg (fun k : (limit G : ModuleCat.{u} A) ⟶ G.obj (Opposite.op n) => k g)
      (limit.w G f)
  have hy : (α.app (Opposite.op n)) ((F.map f) t) =
      (limit.π G (Opposite.op n)) g := by rw [hnat, ht, hw]
  have hd : (α.app (Opposite.op n)) (x.1 - (F.map f) t) = 0 := by
    rw [map_sub, x.2, hy, sub_self]
  obtain ⟨z, hz0, hz⟩ := hkernel n (x.1 - (F.map f) t) hd
  refine ⟨⟨t + z, ?_⟩, ?_⟩
  · rw [map_add, ht, hz0, add_zero]
  · apply Subtype.ext
    show (F.map f) (t + z) = x.1
    rw [map_add, hz]
    abel

/-- A pro-zero kernel makes the fiber tower Mittag--Leffler: sufficiently late
fibers have a single image at every fixed level. -/
private theorem fiberTower_isMittagLeffler_of_prozero_kernel
    {A : Type u} [CommRing A] {F G : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (α : F ⟶ G) (g : (limit G : ModuleCat.{u} A))
    (hpoint : ∀ n : ℕ, Function.Surjective (α.app (Opposite.op n)))
    (hkerzero : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      ∀ x : F.obj (Opposite.op m),
        (α.app (Opposite.op m)) x = 0 →
        (F.map (homOfLE h).op) x = 0) :
    (fiberTower α g).IsMittagLeffler := by
  apply CategoryTheory.Functor.isMittagLeffler_of_exists_finite_range
  intro i
  obtain ⟨m, h, hzero⟩ := hkerzero i.unop
  let f : Opposite.op m ⟶ i := (homOfLE h).op
  refine ⟨Opposite.op m, f, ?_⟩
  obtain ⟨a, ha⟩ := hpoint m ((limit.π G (Opposite.op m)) g)
  let a₀ : (fiberTower α g).obj (Opposite.op m) := ⟨a, ha⟩
  have hconst (x : (fiberTower α g).obj (Opposite.op m)) :
      ((fiberTower α g).map f) x = ((fiberTower α g).map f) a₀ := by
    apply Subtype.ext
    show (F.map f) x.1 = (F.map f) a₀.1
    have hd : (α.app (Opposite.op m)) (x.1 - a₀.1) = 0 := by
      rw [map_sub, x.2, a₀.2, sub_self]
    have hz := hzero (x.1 - a₀.1) hd
    change (F.map f) (x.1 - a₀.1) = 0 at hz
    rwa [map_sub, sub_eq_zero] at hz
  have hrange : Set.range ((fiberTower α g).map f) =
      {((fiberTower α g).map f) a₀} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Set.mem_singleton_iff.mpr (hconst x)
    · intro hy
      rw [Set.mem_singleton_iff.mp hy]
      exact ⟨a₀, rfl⟩
  exact hrange ▸ Set.finite_singleton _

/-- The fiber tower is Mittag--Leffler when the homology of a preceding
surjective tower is pro-zero. Only the fibres over the chosen limit point need
to be nonempty; the map itself need not be pointwise surjective. -/
private theorem fiberTower_isMittagLeffler_of_prozero_homology
    {A : Type u} [CommRing A] {H F G : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (β : H ⟶ F) (α : F ⟶ G) (g₀ : (limit G : ModuleCat.{u} A))
    (hcomp : ∀ i, β.app i ≫ α.app i = 0)
    (hHsurj : ∀ n : ℕ, Function.Surjective
      (H.map (homOfLE (Nat.le_succ n)).op))
    (hne : ∀ i : ℕᵒᵖ, ∃ x : F.obj i, (α.app i) x = (limit.π G i) g₀)
    (hhomzero : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      ∀ x : F.obj (Opposite.op m),
        (α.app (Opposite.op m)) x = 0 →
        ∃ y : H.obj (Opposite.op n),
          (β.app (Opposite.op n)) y = (F.map (homOfLE h).op) x) :
    (fiberTower α g₀).IsMittagLeffler := by
  let E := fiberTower α g₀
  apply (CategoryTheory.Functor.isMittagLeffler_iff_subset_range_comp E).2
  intro i
  obtain ⟨m, h, hhom⟩ := hhomzero i.unop
  let f : Opposite.op m ⟶ i := (homOfLE h).op
  refine ⟨Opposite.op m, f, ?_⟩
  intro k g
  rintro z ⟨x, rfl⟩
  obtain ⟨a, ha⟩ := hne k
  let w : E.obj k := ⟨a, ha⟩
  have hnatα (v : F.obj k) :
      (α.app (Opposite.op m)) ((F.map g) v) =
        (G.map g) ((α.app k) v) :=
    congrArg (fun q : F.obj k ⟶ G.obj (Opposite.op m) => q v) (α.naturality g)
  have hw : (G.map g) ((limit.π G k) g₀) =
      (limit.π G (Opposite.op m)) g₀ :=
    congrArg (fun q : (limit G : ModuleCat.{u} A) ⟶ G.obj (Opposite.op m) => q g₀)
      (limit.w G g)
  have hαw : (α.app (Opposite.op m)) ((F.map g) w.1) =
      (limit.π G (Opposite.op m)) g₀ := by rw [hnatα, w.2, hw]
  have hd : (α.app (Opposite.op m)) (x.1 - (F.map g) w.1) = 0 := by
    rw [map_sub, x.2, hαw, sub_self]
  obtain ⟨b, hb⟩ := hhom (x.1 - (F.map g) w.1) hd
  have hk : i.unop ≤ k.unop := h.trans (leOfHom g.unop)
  have hs : Function.Surjective (H.map (g ≫ f)) := by
    rw [show g ≫ f = (homOfLE hk).op from Subsingleton.elim _ _]
    exact transition_surjective H hHsurj hk
  obtain ⟨c, hc⟩ := hs b
  have hβzero : (α.app k) ((β.app k) c) = 0 := by
    simpa using congrArg (fun q : H.obj k ⟶ G.obj k => q c) (hcomp k)
  have hnatβ : (F.map (g ≫ f)) ((β.app k) c) =
      (β.app i) ((H.map (g ≫ f)) c) :=
    (congrArg (fun q : H.obj k ⟶ F.obj i => q c) (β.naturality (g ≫ f))).symm
  refine ⟨⟨w.1 + (β.app k) c, ?_⟩, ?_⟩
  · rw [map_add, w.2, hβzero, add_zero]
  · apply Subtype.ext
    show (F.map (g ≫ f)) (w.1 + (β.app k) c) = (F.map f) x.1
    rw [map_add, hnatβ, hc, hb, map_sub, F.map_comp]
    simp only [comp_apply]
    abel

/-- A section of the fiber tower over `g` gives a preimage of `g` under the map on limits. -/
private theorem limMap_eq_of_fiberTower_section
    {A : Type u} [CommRing A] {F G : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (α : F ⟶ G) (g : (limit G : ModuleCat.{u} A)) (σ : (fiberTower α g).sections) :
    ∃ x : (limit F : ModuleCat.{u} A), (limMap α) x = g := by
  let τ : (F ⋙ forget (ModuleCat.{u} A)).sections :=
    ⟨fun i => (σ.val i).val, fun f => congrArg Subtype.val (σ.property f)⟩
  let e := Types.isLimitEquivSections
    (isLimitOfPreserves (forget (ModuleCat.{u} A)) (limit.isLimit F))
  let x : (limit F : ModuleCat.{u} A) := e.symm τ
  refine ⟨x, ?_⟩
  apply Concrete.limit_ext G
  intro i
  have hπ : (limit.π F i) x = τ.val i := by
    have h := Types.isLimitEquivSections_symm_apply
      (isLimitOfPreserves (forget (ModuleCat.{u} A)) (limit.isLimit F)) τ i
    simp only [Functor.mapCone_π_app, limit.cone_π] at h
    exact h
  calc
    (limit.π G i) ((limMap α) x) = (α.app i) ((limit.π F i) x) :=
      congrArg (fun k : (limit F : ModuleCat.{u} A) ⟶ G.obj i => k x) (limMap_π α i)
    _ = (limit.π G i) g := by rw [hπ]; exact (σ.val i).property

/-- A levelwise surjection with a pro-zero kernel is surjective on inverse
limits. -/
private theorem limMap_surjective_of_prozero_kernel
    {A : Type u} [CommRing A] {F G : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (α : F ⟶ G)
    (hpoint : ∀ n : ℕ, Function.Surjective (α.app (Opposite.op n)))
    (hkerzero : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      ∀ x : F.obj (Opposite.op m),
        (α.app (Opposite.op m)) x = 0 →
        (F.map (homOfLE h).op) x = 0) :
    Function.Surjective (limMap α) := by
  intro g
  let E := fiberTower α g
  have hML : E.IsMittagLeffler :=
    fiberTower_isMittagLeffler_of_prozero_kernel α g hpoint hkerzero
  have hne : ∀ i, Nonempty (E.obj i) := by
    intro i
    obtain ⟨x, hx⟩ := hpoint i.unop ((limit.π G i) g)
    exact ⟨⟨x, hx⟩⟩
  obtain ⟨σ⟩ := nonempty_sections_of_isMittagLeffler hML hne
  exact limMap_eq_of_fiberTower_section α g σ

/-- Compatible pointwise lifts glue to a lift in the inverse limit when the
preceding tower is surjective and the intervening homology is pro-zero. -/
private theorem limMap_lift_of_prozero_homology
    {A : Type u} [CommRing A] {H F G : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (β : H ⟶ F) (α : F ⟶ G) (g : (limit G : ModuleCat.{u} A))
    (hcomp : ∀ i, β.app i ≫ α.app i = 0)
    (hHsurj : ∀ n : ℕ, Function.Surjective
      (H.map (homOfLE (Nat.le_succ n)).op))
    (hne : ∀ i : ℕᵒᵖ, ∃ x : F.obj i, (α.app i) x = (limit.π G i) g)
    (hhomzero : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      ∀ x : F.obj (Opposite.op m),
        (α.app (Opposite.op m)) x = 0 →
        ∃ y : H.obj (Opposite.op n),
          (β.app (Opposite.op n)) y = (F.map (homOfLE h).op) x) :
    ∃ x : (limit F : ModuleCat.{u} A), (limMap α) x = g := by
  let E := fiberTower α g
  have hML : E.IsMittagLeffler :=
    fiberTower_isMittagLeffler_of_prozero_homology β α g hcomp hHsurj hne hhomzero
  have hne : ∀ i, Nonempty (E.obj i) := by
    intro i
    obtain ⟨x, hx⟩ := hne i
    exact ⟨⟨x, hx⟩⟩
  obtain ⟨σ⟩ := nonempty_sections_of_isMittagLeffler hML hne
  exact limMap_eq_of_fiberTower_section α g σ

/-- A levelwise surjection induces a surjection on limits if the homology of a
surjective preceding tower eventually vanishes at every fixed level. -/
private theorem limMap_surjective_of_prozero_homology
    {A : Type u} [CommRing A] {H F G : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (β : H ⟶ F) (α : F ⟶ G)
    (hcomp : ∀ i, β.app i ≫ α.app i = 0)
    (hHsurj : ∀ n : ℕ, Function.Surjective
      (H.map (homOfLE (Nat.le_succ n)).op))
    (hpoint : ∀ n : ℕ, Function.Surjective (α.app (Opposite.op n)))
    (hhomzero : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      ∀ x : F.obj (Opposite.op m),
        (α.app (Opposite.op m)) x = 0 →
        ∃ y : H.obj (Opposite.op n),
          (β.app (Opposite.op n)) y = (F.map (homOfLE h).op) x) :
    Function.Surjective (limMap α) := fun g =>
  limMap_lift_of_prozero_homology β α g hcomp hHsurj (fun i => hpoint i.unop _) hhomzero

/-- A four-term complex of module towers remains right exact after taking limits when the first
homology is pro-zero and the preceding towers have surjective transitions. -/
private theorem limMap_rightExact_of_prozero_homology
    {A : Type u} [CommRing A] {F₂ F₁ F₀ C : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (d₂ : F₂ ⟶ F₁) (d₁ : F₁ ⟶ F₀) (q : F₀ ⟶ C)
    (hd₂₁ : ∀ i, d₂.app i ≫ d₁.app i = 0)
    (hd₁q : ∀ i, d₁.app i ≫ q.app i = 0)
    (hF₂ : ∀ n : ℕ, Function.Surjective
      (F₂.map (homOfLE (Nat.le_succ n)).op))
    (hF₁ : ∀ n : ℕ, Function.Surjective
      (F₁.map (homOfLE (Nat.le_succ n)).op))
    (hq : ∀ n : ℕ, Function.Surjective (q.app (Opposite.op n)))
    (hex : ∀ i (x : F₀.obj i), (q.app i) x = 0 →
      ∃ y : F₁.obj i, (d₁.app i) y = x)
    (hhomzero : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      ∀ x : F₁.obj (Opposite.op m),
        (d₁.app (Opposite.op m)) x = 0 →
        ∃ y : F₂.obj (Opposite.op n),
          (d₂.app (Opposite.op n)) y = (F₁.map (homOfLE h).op) x) :
    Function.Surjective (limMap q) ∧
      ∀ x : (limit F₀ : ModuleCat.{u} A), (limMap q) x = 0 →
        ∃ y : (limit F₁ : ModuleCat.{u} A), (limMap d₁) y = x := by
  constructor
  · refine limMap_surjective_of_prozero_homology d₁ q hd₁q hF₁ hq fun n => ⟨n, le_rfl, ?_⟩
    intro x hx
    obtain ⟨y, hy⟩ := hex (Opposite.op n) x hx
    refine ⟨y, ?_⟩
    simpa only [show (homOfLE (le_refl n)).op = 𝟙 (Opposite.op n) from
      Subsingleton.elim _ _, F₀.map_id, id_apply] using hy
  · intro x hx
    apply limMap_lift_of_prozero_homology d₂ d₁ x hd₂₁ hF₂
    · intro i
      apply hex i
      have hπ := congrArg (fun z : (limit C : ModuleCat.{u} A) => (limit.π C i) z) hx
      have hcomp := congrArg
        (fun f : (limit F₀ : ModuleCat.{u} A) ⟶ C.obj i => f x)
        (limMap_π q i)
      simpa only [comp_apply, map_zero] using hcomp.symm.trans hπ
    · exact hhomzero

/-- Inverse limits preserve a levelwise surjection when its kernel tower has
surjective successor transitions. -/
private theorem limMap_surjective_of_kernel_surjective
    {A : Type u} [CommRing A] {F G : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (α : F ⟶ G)
    (hpoint : ∀ n : ℕ, Function.Surjective (α.app (Opposite.op n)))
    (hkernel : ∀ (n : ℕ) (x : F.obj (Opposite.op n)),
      (α.app (Opposite.op n)) x = 0 →
      ∃ y : F.obj (Opposite.op (n + 1)),
        (α.app (Opposite.op (n + 1))) y = 0 ∧
        (F.map (homOfLE (Nat.le_succ n)).op) y = x) :
    Function.Surjective (limMap α) := by
  intro g
  let E := fiberTower α g
  have hs : ∀ n : ℕ, Function.Surjective
      (E.map (homOfLE (Nat.le_succ n)).op) :=
    fiberTower_successor_surjective α g hpoint hkernel
  obtain ⟨x₀, hx₀⟩ := hpoint 0 ((limit.π G (Opposite.op 0)) g)
  obtain ⟨s, -⟩ := Types.surjective_π_app_zero_of_surjective_map
    (limit.isLimit E) hs (⟨x₀, hx₀⟩ : E.obj (Opposite.op 0))
  let σ := Types.limitEquivSections E s
  exact limMap_eq_of_fiberTower_section α g σ

/-- A tower whose transition maps are eventually zero at every fixed level has
zero inverse limit. -/
private theorem limit_isZero_of_prozero
    {A : Type u} [CommRing A] (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hzero : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      M.map (homOfLE h).op = 0) : IsZero (limit M) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun x y => ?_⟩
  apply Concrete.limit_ext M
  intro i
  obtain ⟨m, h, hz⟩ := hzero i.unop
  have hp (z : (limit M : ModuleCat.{u} A)) : (limit.π M i) z = 0 := by
    have hw := congrArg (fun k : (limit M : ModuleCat.{u} A) ⟶ M.obj i => k z)
      (limit.w M (homOfLE h).op)
    rw [hz] at hw
    simpa using hw.symm
  rw [hp x, hp y]

/-- The levelwise tensor product of the tower `Tor₁(Q, A/Iⁿ)` with a given tower has zero
limit. -/
private theorem torOneTensorTower_limit_isZero
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (Q : ModuleCat.{u} A) [Module.Finite A Q]
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) :
    IsZero (limit (tensorPairTower (torOneTower I Q) M)) :=
  limit_isZero_of_prozero _ (torOneTensorTower_prozero I Q M)

/-- Inverse limits preserve injections of towers of modules. -/
private theorem limMap_injective_of_pointwise_injective
    {A : Type u} [CommRing A] {F G : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (α : F ⟶ G)
    (hα : ∀ n : ℕ, Function.Injective (α.app (Opposite.op n))) :
    Function.Injective (limMap α) := by
  intro x y hxy
  apply Concrete.limit_ext F
  intro i
  apply hα i.unop
  have h := congrArg (fun z : (limit G : ModuleCat.{u} A) => (limit.π G i) z) hxy
  simpa only [← comp_apply, limMap_π] using h

/-- A kernel tower with eventually zero transition maps has no nonzero
element in the kernel of the induced limit map. -/
private theorem limMap_injective_of_prozero_kernel
    {A : Type u} [CommRing A] {F G : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (α : F ⟶ G)
    (hkerzero : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      ∀ x : F.obj (Opposite.op m),
        (α.app (Opposite.op m)) x = 0 →
        (F.map (homOfLE h).op) x = 0) :
    Function.Injective (limMap α) := by
  intro x y hxy
  apply Concrete.limit_ext F
  intro i
  obtain ⟨m, h, hz⟩ := hkerzero i.unop
  have hw (z : (limit F : ModuleCat.{u} A)) :
      (F.map (homOfLE h).op) ((limit.π F (Opposite.op m)) z) =
        (limit.π F i) z :=
    congrArg (fun k : (limit F : ModuleCat.{u} A) ⟶ F.obj i => k z) (limit.w F (homOfLE h).op)
  have hk : (α.app (Opposite.op m))
      ((limit.π F (Opposite.op m)) x - (limit.π F (Opposite.op m)) y) = 0 := by
    rw [map_sub]
    have hx := congrArg
      (fun z : (limit G : ModuleCat.{u} A) => (limit.π G (Opposite.op m)) z) hxy
    have hπ (z : (limit F : ModuleCat.{u} A)) :
        (α.app (Opposite.op m)) ((limit.π F (Opposite.op m)) z) =
          (limit.π G (Opposite.op m)) ((limMap α) z) :=
      (congrArg (fun k : (limit F : ModuleCat.{u} A) ⟶ G.obj (Opposite.op m) => k z)
        (limMap_π α (Opposite.op m))).symm
    rw [hπ, hπ, hx, sub_self]
  have hd := hz _ hk
  rwa [map_sub, hw, hw, sub_eq_zero] at hd

/-- If the kernel of a morphism of towers is covered by the image of a pro-zero tower, then its
map on limits is injective. -/
private theorem limMap_injective_of_prozero_image
    {A : Type u} [CommRing A] {H F G : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (β : H ⟶ F) (α : F ⟶ G)
    (hex : ∀ i (x : F.obj i), (α.app i) x = 0 →
      ∃ y : H.obj i, (β.app i) y = x)
    (hHzero : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      H.map (homOfLE h).op = 0) :
    Function.Injective (limMap α) := by
  apply limMap_injective_of_prozero_kernel α
  intro n
  obtain ⟨m, h, hz⟩ := hHzero n
  refine ⟨m, h, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := hex (Opposite.op m) x hx
  let f : Opposite.op m ⟶ Opposite.op n := (homOfLE h).op
  have hnat : (F.map f) ((β.app (Opposite.op m)) y) =
      (β.app (Opposite.op n)) ((H.map f) y) :=
    (congrArg (fun q : H.obj (Opposite.op m) ⟶ F.obj (Opposite.op n) => q y)
      (β.naturality f)).symm
  rw [← hy, hnat, hz]
  simp

end FlatLimit

end
