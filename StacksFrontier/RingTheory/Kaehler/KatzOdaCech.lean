module

public import StacksFrontier.RingTheory.Kaehler.KatzOdaCommRingCat
public import StacksFrontier.CategoryTheory.Sites.CechComplexConcreteTotalGraded
public import StacksFrontier.RingTheory.Kaehler.DeRhamShiftedSum

/-!
# The filtration by forms from the base, on the Čech intersections

Let `R ⟶ A` be a map of commutative rings and let `U : ι → C` be a finite family of objects of a
category with finite products. Suppose that over each Čech intersection `U_t` we are given an
`A`-algebra `B_t`, formally smooth over `A`, with restriction maps `B_{t ∘ ∂_j} ⟶ B_t` along the
face maps (`Stacks.KatzOda.Cech.ChartData`), and complexes of presheaves `P` over `R` and `Q`
over `A` whose values on `U_t` are identified with `Ω^•[B_t⁄R]` and `Ω^•[B_t⁄A]`, compatibly with
the actions, the restrictions and the differentials (`Stacks.KatzOda.Cech.FormsData`). This is the
situation of the de Rham complexes of a smooth morphism `X ⟶ Y` over `S` with `Y` and `S`
affine, on a cover of `X` by affine opens.

The filtration of `Ω^•[B_t⁄R]` by the forms from `A` (`Stacks.KatzOda.step`) then gives a
filtration of `P` on the Čech intersections, whose graded pieces are
`gr^k P^{k+b}(U_t) ≅ Ω^k[A⁄R] ⊗_A Q^b(U_t)`, compatibly with the restrictions and the
differentials. Hence `gr^k Tot(Č(U, P))` is `Tot(Č(U, Ω^k[A⁄R] ⊗_A Q))` moved up by `k` degrees.

## Main definitions

* `Stacks.KatzOda.Cech.filtration`: the filtration of `P` on the Čech intersections.
* `Stacks.KatzOda.Cech.gradedTensorData`: the identification of its graded pieces.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open Stacks.CategoryTheory.CechComplex
open scoped TensorProduct

universe w v u

namespace Stacks.KatzOda.Cech

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {ι : Type w} [Fintype ι]
  [DecidableEq ι] (U : ι → C) {R A : CommRingCat.{w}} (gR : R ⟶ A)

/-- **Algebras over the Čech intersections**: an `A`-algebra `B_t` over each intersection `U_t`,
formally smooth over `A`, with restriction maps along the face maps. -/
structure ChartData where
  /-- The algebra over the intersection selected by `t`. -/
  B : ∀ {m : ℕ}, (Fin (m + 1) → ι) → CommRingCat.{w}
  /-- The structure map from `A`. -/
  φ : ∀ {m : ℕ} (t : Fin (m + 1) → ι), A ⟶ B t
  /-- The structure map from `R`. -/
  ψ : ∀ {m : ℕ} (t : Fin (m + 1) → ι), R ⟶ B t
  comp_φ : ∀ {m : ℕ} (t : Fin (m + 1) → ι), gR ≫ φ t = ψ t
  /-- The restriction along the face map omitting `j`. -/
  ρ : ∀ {m : ℕ} (t : Fin (m + 2) → ι) (j : Fin (m + 2)), B (t ∘ Fin.succAbove j) ⟶ B t
  φ_ρ : ∀ {m : ℕ} (t : Fin (m + 2) → ι) (j : Fin (m + 2)), φ (t ∘ Fin.succAbove j) ≫ ρ t j = φ t
  ψ_ρ : ∀ {m : ℕ} (t : Fin (m + 2) → ι) (j : Fin (m + 2)), ψ (t ∘ Fin.succAbove j) ≫ ρ t j = ψ t
  /-- Each `B_t` is formally smooth over `A`. -/
  formallySmooth : ∀ {m : ℕ} (t : Fin (m + 1) → ι), (φ t).hom.FormallySmooth

variable {gR} (D : ChartData (ι := ι) gR)

/-- **A complex of presheaves of forms over the Čech intersections**: a complex `P` of presheaves
of modules over a ring `T` mapping to the algebras `B_t` by `σ_t`, together with identifications
`P^a(U_t) ≅ ⋀^a Ω[B_t⁄T]` compatible with the actions of `T`, with the restrictions along the face
maps and with the differentials. The identifications are given as composites
`P^a(U_t) ≅ L ≅ ⋀^a Ω[B_t⁄T]` of a `T`-linear one and an additive one compatible with the actions,
through any `T`-module `L`. -/
structure FormsData {T : CommRingCat.{w}} (σ : ∀ {m : ℕ} (t : Fin (m + 1) → ι), T ⟶ D.B t)
    (σ_ρ : ∀ {m : ℕ} (t : Fin (m + 2) → ι) (j : Fin (m + 2)),
      σ (t ∘ Fin.succAbove j) ≫ D.ρ t j = σ t)
    (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} T) ℕ) where
  /-- An intermediate module over the intersection selected by `t`, in degree `a`. -/
  L : ℕ → ∀ {m : ℕ}, (Fin (m + 1) → ι) → Type w
  /-- The additive group structure on the intermediate module. -/
  instAddCommGroup : ∀ (a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι), AddCommGroup (L a t)
  /-- The `T`-module structure on the intermediate module. -/
  instModule : ∀ (a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι),
    letI := instAddCommGroup a t
    Module T (L a t)
  /-- The linear identification with the intermediate module. -/
  s : ∀ (a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι),
    letI := instAddCommGroup a t
    letI := instModule a t
    (P.X a).obj (op (inter U t)) ≃ₗ[T] L a t
  /-- The identification of the intermediate module with the forms. -/
  e' : ∀ (a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι),
    letI := instAddCommGroup a t
    L a t ≃+ ⋀[D.B t]^a ↑(CommRingCat.KaehlerDifferential (σ t))
  /-- The identification with the forms carries the action of `T` to the action of `T` through
  `σ_t`. -/
  e'_smul : ∀ (a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι) (r : T) (l : L a t),
    letI := instAddCommGroup a t
    letI := instModule a t
    e' a t (r • l) = σ t r • e' a t l
  e'_cres : ∀ (a : ℕ) {m : ℕ} (t : Fin (m + 2) → ι) (j : Fin (m + 2))
    (y : (P.X a).obj (op (inter U (t ∘ Fin.succAbove j)))),
    e' a t (s a t (cres U (P.X a) (Fin.succAbove j) t y)) =
      Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap (σ (t ∘ Fin.succAbove j)) (σ t)
        (D.ρ t j) (σ_ρ t j) a (e' a (t ∘ Fin.succAbove j) (s a (t ∘ Fin.succAbove j) y))
  e'_d : ∀ (a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι) (y : (P.X a).obj (op (inter U t))),
    e' (a + 1) t (s (a + 1) t (((P.d a (a + 1)).app (op (inter U t))).hom y)) =
      dForms (σ t) a (e' a t (s a t y))

namespace FormsData

variable {U D} {T : CommRingCat.{w}} {σ : ∀ {m : ℕ} (t : Fin (m + 1) → ι), T ⟶ D.B t}
  {σ_ρ : ∀ {m : ℕ} (t : Fin (m + 2) → ι) (j : Fin (m + 2)),
    σ (t ∘ Fin.succAbove j) ≫ D.ρ t j = σ t}
  {P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} T) ℕ} (E : FormsData U D σ σ_ρ P)

/-- **The identification `P^a(U_t) ≅ ⋀^a Ω[B_t⁄T]`.** -/
def e (a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι) :
    (P.X a).obj (op (inter U t)) ≃+ ⋀[D.B t]^a ↑(CommRingCat.KaehlerDifferential (σ t)) :=
  letI := E.instAddCommGroup a t
  letI := E.instModule a t
  (E.s a t).toAddEquiv.trans (E.e' a t)

omit [Fintype ι] [DecidableEq ι] in
/-- The identification `e` is the composite of `s` and `e'`. -/
theorem e_apply (a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι) (y : (P.X a).obj (op (inter U t))) :
    E.e a t y = E.e' a t (E.s a t y) :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The identification `e` carries the action of `T` to the action of `T` through `σ_t`. -/
theorem e_smul (a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι) (r : T) (y : (P.X a).obj (op (inter U t))) :
    E.e a t (r • y) = σ t r • E.e a t y := by
  let := E.instAddCommGroup a t
  let := E.instModule a t
  rw [e_apply, e_apply, LinearEquiv.map_smul]
  exact E.e'_smul a t r (E.s a t y)

omit [Fintype ι] [DecidableEq ι] in
/-- The identification `e` carries the restriction along the face map omitting `j` to the map
of forms induced by `ρ_{t,j}`. -/
theorem e_cres (a : ℕ) {m : ℕ} (t : Fin (m + 2) → ι) (j : Fin (m + 2))
    (y : (P.X a).obj (op (inter U (t ∘ Fin.succAbove j)))) :
    E.e a t (cres U (P.X a) (Fin.succAbove j) t y) =
      Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap (σ (t ∘ Fin.succAbove j)) (σ t)
        (D.ρ t j) (σ_ρ t j) a (E.e a (t ∘ Fin.succAbove j) y) :=
  E.e'_cres a t j y

omit [Fintype ι] [DecidableEq ι] in
/-- The identification `e` carries the differential of `P` to the de Rham differential. -/
theorem e_d (a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι) (y : (P.X a).obj (op (inter U t))) :
    E.e (a + 1) t (((P.d a (a + 1)).app (op (inter U t))).hom y) = dForms (σ t) a (E.e a t y) :=
  E.e'_d a t y

end FormsData

variable {U} {P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ} (EP : FormsData U D D.ψ D.ψ_ρ P)

/-- The `k`-th step of the filtration of `P^a(U_t)` by the forms from `A`. -/
abbrev stepAt (k a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι) :
    Submodule R ((P.X a).obj (op (inter U t))) :=
  comapStep gR (D.φ t) (D.ψ t) (D.comp_φ t) (D.ψ t).hom (EP.e a t) (EP.e_smul a t) k

/-- **The filtration of `P` by the forms from `A`**, on the Čech intersections. -/
def filtration : InterFiltration U P where
  step k a m t := stepAt D EP k a t
  map_le k a m t j := by
    rintro _ ⟨y, hy, rfl⟩
    refine (mem_comapStep _ _ _ _ _ _ _).2 ?_
    rw [EP.e_cres a t j y]
    exact formsMap_mem gR (D.φ _) (D.ψ _) (D.comp_φ _) (D.φ t) (D.ψ t) (D.comp_φ t) (D.ρ t j)
      (D.φ_ρ t j) (D.ψ_ρ t j) ((mem_comapStep _ _ _ _ _ _ _).1 hy)
  d_le k a m t := by
    rintro _ ⟨y, hy, rfl⟩
    refine (mem_comapStep _ _ _ _ _ _ _).2 ?_
    rw [EP.e_d a t y]
    exact dForms_mem gR (D.φ t) (D.ψ t) (D.comp_φ t) ((mem_comapStep _ _ _ _ _ _ _).1 hy)
  step_succ_le k a m t y hy := (mem_comapStep _ _ _ _ _ _ _).2
    (step_succ_le gR (D.φ t) (D.ψ t) (D.comp_φ t) k a ((mem_comapStep _ _ _ _ _ _ _).1 hy))
  step_zero a m t := eq_top_iff.2 fun y _ => (mem_comapStep _ _ _ _ _ _ _).2 (by
    rw [step_zero]
    trivial)
  step_eq_bot k a m t hk := eq_bot_iff.2 fun y hy => by
    have hy' := (mem_comapStep _ _ _ _ _ _ _).1 hy
    rw [step_eq_bot gR (D.φ t) (D.ψ t) (D.comp_φ t) hk, Submodule.mem_bot] at hy'
    exact (Submodule.mem_bot _).2 ((EP.e a t).map_eq_zero_iff.1 hy')

omit [Fintype ι] [DecidableEq ι] in
/-- The `k`-th step of `filtration` on `P^a(U_t)` is `stepAt`. -/
theorem filtration_step (k a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι) :
    (filtration D EP).step k a t = stepAt D EP k a t :=
  rfl

/-- The graded pieces of the filtration of `P`, identified with those of the filtration of the
forms. -/
def gradedTransport (k a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι) :
    (filtration D EP).GradedValue (U := U) k a t ≃+
      gradedQuot gR (D.φ t) (D.ψ t) (D.comp_φ t) k a :=
  comapGradedEquiv gR (D.φ t) (D.ψ t) (D.comp_φ t) (D.ψ t).hom (EP.e a t) (EP.e_smul a t) k

omit [Fintype ι] [DecidableEq ι] in
/-- `gradedTransport` sends the class of `y` to the class of its image under `e`. -/
theorem gradedTransport_mk (k a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι)
    (y : (filtration D EP).step k a t) :
    gradedTransport D EP k a t (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ⟨EP.e a t y, y.2⟩ :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- `gradedTransport` carries the restriction of graded pieces along the face map omitting `j`
to the map of graded pieces of forms induced by `ρ_{t,j}`. -/
theorem gradedTransport_gradedCres (k a : ℕ) {m : ℕ} (t : Fin (m + 2) → ι) (j : Fin (m + 2))
    (w : (filtration D EP).GradedValue (U := U) k a (t ∘ Fin.succAbove j)) :
    gradedTransport D EP k a t ((filtration D EP).gradedCres k a t j w) =
      gradedQuotMap gR (D.φ _) (D.ψ _) (D.comp_φ _) (D.φ t) (D.ψ t) (D.comp_φ t) (D.ρ t j)
        (D.φ_ρ t j) (D.ψ_ρ t j) k a (gradedTransport D EP k a (t ∘ Fin.succAbove j) w) := by
  induction w using Submodule.Quotient.induction_on with | H y =>
  refine (gradedTransport_mk D EP k a t _).trans ?_
  refine Eq.trans ?_ (congrArg (gradedQuotMap gR (D.φ _) (D.ψ _) (D.comp_φ _) (D.φ t) (D.ψ t)
    (D.comp_φ t) (D.ρ t j) (D.φ_ρ t j) (D.ψ_ρ t j) k a)
      (gradedTransport_mk D EP k a (t ∘ Fin.succAbove j) y)).symm
  exact congrArg Submodule.Quotient.mk (Subtype.ext (EP.e_cres a t j y))

omit [Fintype ι] [DecidableEq ι] in
/-- `gradedTransport` carries the differential of graded pieces of `P` to that of the graded
pieces of forms. -/
theorem gradedTransport_gradedD (k a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι)
    (w : (filtration D EP).GradedValue (U := U) k a t) :
    gradedTransport D EP k (a + 1) t ((filtration D EP).gradedD k a t w) =
      gradedQuotD gR (D.φ t) (D.ψ t) (D.comp_φ t) k a (gradedTransport D EP k a t w) := by
  induction w using Submodule.Quotient.induction_on with | H y =>
  refine (gradedTransport_mk D EP k (a + 1) t _).trans ?_
  refine Eq.trans ?_ (congrArg (gradedQuotD gR (D.φ t) (D.ψ t) (D.comp_φ t) k a)
      (gradedTransport_mk D EP k a t y)).symm
  refine Eq.trans ?_ (gradedQuotD_mk gR (D.φ t) (D.ψ t) (D.comp_φ t) k a _).symm
  exact congrArg Submodule.Quotient.mk (Subtype.ext (EP.e_d a t y))

/-! ### The graded pieces as tensor products -/

variable {Q : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} A) ℕ} (EQ : FormsData U D D.φ D.φ_ρ Q)

/-- The module `Ω^k[A⁄R]`. -/
abbrev formsN (g : R ⟶ A) (k : ℕ) : ModuleCat.{w} A :=
  ShiftedSum.formsN g k

/-- **The graded pieces over an intersection as tensor products**:
`Ω^k[A⁄R] ⊗_A Q^b(U_t) ≅ gr^k Ω^{k+b}[B_t⁄R]`. -/
def gradedOpen (k b : ℕ) {m : ℕ} (t : Fin (m + 1) → ι) :
    ((tensorCoeff (formsN gR k) Q).X b).obj (op (inter U t)) ≃+
      gradedQuot gR (D.φ t) (D.ψ t) (D.comp_φ t) k (k + b) :=
  gradedTensor gR (D.φ t) (D.ψ t) (D.comp_φ t) (M := (Q.X b).obj (op (inter U t))) (EQ.e b t)
    (EQ.e_smul b t) (D.formallySmooth t) k

omit [Fintype ι] [DecidableEq ι] in
/-- The restriction on `Ω^k[A⁄R] ⊗_A Q^b` is the identity tensored with the restriction on
`Q^b`. -/
theorem cres_tensorCoeff (k b : ℕ) {m : ℕ} (t : Fin (m + 2) → ι) (j : Fin (m + 2))
    (z : ((tensorCoeff (formsN gR k) Q).X b).obj (op (inter U (t ∘ Fin.succAbove j)))) :
    cres U ((tensorCoeff (formsN gR k) Q).X b) (Fin.succAbove j) t z =
      TensorProduct.map LinearMap.id (cres U (Q.X b) (Fin.succAbove j) t) z := by
  exact LinearMap.congr_fun (TensorProduct.ext' fun _ _ => rfl) z

omit [Fintype ι] [DecidableEq ι] in
/-- The differential on `Ω^k[A⁄R] ⊗_A Q^•` is the identity tensored with the differential of
`Q`. -/
theorem d_tensorCoeff (k b : ℕ) {m : ℕ} (t : Fin (m + 1) → ι)
    (z : ((tensorCoeff (formsN gR k) Q).X b).obj (op (inter U t))) :
    (((tensorCoeff (formsN gR k) Q).d b (b + 1)).app (op (inter U t))).hom z =
      TensorProduct.map LinearMap.id ((Q.d b (b + 1)).app (op (inter U t))).hom z := by
  exact LinearMap.congr_fun (TensorProduct.ext' fun _ _ => rfl) z

omit [Fintype ι] [DecidableEq ι] in
/-- `gradedOpen` carries the restriction along the face map omitting `j` to the map of graded
pieces of forms induced by `ρ_{t,j}`. -/
theorem gradedOpen_cres (k b : ℕ) {m : ℕ} (t : Fin (m + 2) → ι) (j : Fin (m + 2))
    (z : ((tensorCoeff (formsN gR k) Q).X b).obj (op (inter U (t ∘ Fin.succAbove j)))) :
    gradedOpen D EQ k b t (cres U ((tensorCoeff (formsN gR k) Q).X b) (Fin.succAbove j) t z) =
      gradedQuotMap gR (D.φ _) (D.ψ _) (D.comp_φ _) (D.φ t) (D.ψ t) (D.comp_φ t) (D.ρ t j)
        (D.φ_ρ t j) (D.ψ_ρ t j) k (k + b) (gradedOpen D EQ k b (t ∘ Fin.succAbove j) z) := by
  rw [cres_tensorCoeff]
  exact gradedTensor_map gR (D.φ _) (D.ψ _) (D.comp_φ _) (EQ.e b _) (EQ.e_smul b _)
    (D.formallySmooth _) (D.φ t) (D.ψ t) (D.comp_φ t) (D.ρ t j) (D.φ_ρ t j) (D.ψ_ρ t j)
    (EQ.e b t) (EQ.e_smul b t) (D.formallySmooth t) (cres U (Q.X b) (Fin.succAbove j) t)
    (EQ.e_cres b t j) k z

omit [Fintype ι] [DecidableEq ι] in
/-- `gradedOpen` carries the differential of `Ω^k[A⁄R] ⊗_A Q^•` to the differential of the
graded pieces of forms. -/
theorem gradedOpen_d (k b : ℕ) {m : ℕ} (t : Fin (m + 1) → ι)
    (z : ((tensorCoeff (formsN gR k) Q).X b).obj (op (inter U t))) :
    gradedOpen D EQ k (b + 1) t
        ((((tensorCoeff (formsN gR k) Q).d b (b + 1)).app (op (inter U t))).hom z) =
      gradedQuotD gR (D.φ t) (D.ψ t) (D.comp_φ t) k (k + b) (gradedOpen D EQ k b t z) := by
  rw [d_tensorCoeff]
  exact gradedTensor_d gR (D.φ t) (D.ψ t) (D.comp_φ t) (EQ.e b t) (EQ.e_smul b t)
    (D.formallySmooth t) (EQ.e (b + 1) t) (EQ.e_smul (b + 1) t)
    ((Q.d b (b + 1)).app (op (inter U t))).hom (EQ.e_d b t) k z

/-- **The graded pieces of the filtration of `P` over an intersection as tensor products**:
`Ω^k[A⁄R] ⊗_A Q^b(U_t) ≅ gr^k P^{k+b}(U_t)`. -/
def gradedPiece (k b : ℕ) {m : ℕ} (t : Fin (m + 1) → ι) :
    ((tensorCoeff (formsN gR k) Q).X b).obj (op (inter U t)) ≃+
      (filtration D EP).GradedValue (U := U) k (k + b) t :=
  (gradedOpen D EQ k b t).trans (gradedTransport D EP k (k + b) t).symm

omit [Fintype ι] [DecidableEq ι] in
/-- `gradedTransport` composed with `gradedPiece` is `gradedOpen`. -/
theorem gradedTransport_gradedPiece (k b : ℕ) {m : ℕ} (t : Fin (m + 1) → ι)
    (z : ((tensorCoeff (formsN gR k) Q).X b).obj (op (inter U t))) :
    gradedTransport D EP k (k + b) t (gradedPiece D EP EQ k b t z) = gradedOpen D EQ k b t z :=
  AddEquiv.apply_symm_apply _ _

omit [Fintype ι] [DecidableEq ι] in
/-- `gradedPiece` commutes with the restrictions along the face maps. -/
theorem gradedPiece_cres (k b : ℕ) {m : ℕ} (t : Fin (m + 2) → ι) (j : Fin (m + 2))
    (z : ((tensorCoeff (formsN gR k) Q).X b).obj (op (inter U (t ∘ Fin.succAbove j)))) :
    gradedPiece D EP EQ k b t (cres U ((tensorCoeff (formsN gR k) Q).X b) (Fin.succAbove j) t z) =
      (filtration D EP).gradedCres k (k + b) t j
        (gradedPiece D EP EQ k b (t ∘ Fin.succAbove j) z) := by
  refine (gradedTransport D EP k (k + b) t).injective ?_
  refine (gradedTransport_gradedPiece D EP EQ k b t _).trans ?_
  refine (gradedOpen_cres D EQ k b t j z).trans ?_
  refine Eq.trans ?_ (gradedTransport_gradedCres D EP k (k + b) t j _).symm
  exact congrArg _ (gradedTransport_gradedPiece D EP EQ k b (t ∘ Fin.succAbove j) z).symm

omit [Fintype ι] [DecidableEq ι] in
/-- `gradedPiece` commutes with the differentials. -/
theorem gradedPiece_d (k b : ℕ) {m : ℕ} (t : Fin (m + 1) → ι)
    (z : ((tensorCoeff (formsN gR k) Q).X b).obj (op (inter U t))) :
    gradedPiece D EP EQ k (b + 1) t
        ((((tensorCoeff (formsN gR k) Q).d b (b + 1)).app (op (inter U t))).hom z) =
      (filtration D EP).gradedD k (k + b) t (gradedPiece D EP EQ k b t z) := by
  refine (gradedTransport D EP k (k + b + 1) t).injective ?_
  refine (gradedTransport_gradedPiece D EP EQ k (b + 1) t _).trans ?_
  refine (gradedOpen_d D EQ k b t z).trans ?_
  refine Eq.trans ?_ (gradedTransport_gradedD D EP k (k + b) t _).symm
  exact congrArg _ (gradedTransport_gradedPiece D EP EQ k b t z).symm

/-- **The graded pieces of the filtration of `P` as tensor products**:
`Ω^k[A⁄R] ⊗_A Q^b(U_t) ≅ gr^k P^{k+b}(U_t)`, compatibly with the restrictions and the
differentials. -/
def gradedTensorData (k : ℕ) :
    GradedTensorData U (formsN gR k) Q (filtration D EP) k where
  Φ b _ t := gradedPiece D EP EQ k b t
  map_cres b _ t j z := gradedPiece_cres D EP EQ k b t j z
  map_d b _ t z := gradedPiece_d D EP EQ k b t z

/-- **The graded pieces of `Tot(Č(U, P))` as tensor products**:
`gr^k Tot(Č(U, P)) ≅ Ω^k[A⁄R] ⊗_A Tot(Č(U, Q))` moved up by `k` degrees, as complexes of abelian
groups. -/
def gradedIso (k : ℕ) :
    (CochainComplex.SubmoduleFiltration.forgetAb R).obj
        (((filtration D EP).totFiltration (U := U)).graded k) ≅
      (CochainComplex.SubmoduleFiltration.forgetAb A).obj
        (CochainComplex.reindex
          (((tensorLeft (formsN gR k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (cechTot U Q)) k) :=
  (gradedTensorData D EP EQ k).gradedTotIso ≪≫
    (CochainComplex.SubmoduleFiltration.forgetAb A).mapIso
      (CochainComplex.reindexIso (tensorTotIso U (formsN gR k) Q).symm k)

end Stacks.KatzOda.Cech

end
