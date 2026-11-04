module

public import StacksFrontier.Homology.Perfect.MinimalRepresentative.ElementarySplitting

/-!
# Minimal representatives: solving equations between homomorphisms after localization

A finite system of equations between module homomorphisms which holds after localizing at a prime
holds after inverting a single element outside it. The equations are recorded syntactically by
`HomExpression`; the result used downstream is that a homotopy equivalence defined over the
localization at a prime is the localization of one defined over a principal localization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

open scoped TensorProduct ChangeOfRings

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-! ### Solving equations between homomorphisms after a further localization

A homotopy equivalence defined over the localization of `R` at a prime is a finite list of
homomorphisms satisfying a finite list of polynomial identities in the composition algebra. Each
homomorphism has a denominator and each identity fails only up to a denominator, so inverting one
element of `R` outside the prime makes the whole list defined and the whole list of identities
hold. The identities are recorded syntactically by `HomExpression`, whose `numerator` clears
denominators while `degree` records how many were cleared.
-/

section HomEquations

open scoped ModuleCat.Algebra

universe uI uJ

/-- A formal expression in a family of module homomorphisms: the identities satisfied by a
homotopy equivalence are of this shape, and clearing denominators is an operation on the
expression rather than on any particular interpretation of it. -/
private inductive HomExpression
    {R : Type u} [CommRing R] {I : Type uI} {J : Type uJ}
    (M : I → ModuleCat.{v} R) (src tgt : J → I) : I → I → Type (max u v uI uJ) where
  | identity (i : I) : HomExpression M src tgt i i
  | const {i j} (f : M i ⟶ M j) : HomExpression M src tgt i j
  | var (k : J) : HomExpression M src tgt (src k) (tgt k)
  | add {i j} (f g : HomExpression M src tgt i j) : HomExpression M src tgt i j
  | neg {i j} (f : HomExpression M src tgt i j) : HomExpression M src tgt i j
  | comp {i j k} (f : HomExpression M src tgt i j)
      (g : HomExpression M src tgt j k) : HomExpression M src tgt i k

/-- Interpret an expression in the image of an additive functor, with prescribed values for the
variables. -/
private def HomExpression.eval
    {R : Type u} [CommRing R] {I : Type uI} {J : Type uJ}
    {M : I → ModuleCat.{v} R} {src tgt : J → I}
    {C : Type*} [Category C] [Preadditive C]
    (F : ModuleCat.{v} R ⥤ C)
    (x : ∀ k, F.obj (M (src k)) ⟶ F.obj (M (tgt k)))
    {i j} : HomExpression M src tgt i j → (F.obj (M i) ⟶ F.obj (M j))
  | .identity i => 𝟙 (F.obj (M i))
  | .const f => F.map f
  | .var k => x k
  | .add f g => f.eval F x + g.eval F x
  | .neg f => -f.eval F x
  | .comp f g => f.eval F x ≫ g.eval F x

/-- The number of variable occurrences, counted so that it matches the power of the denominator
cleared by `HomExpression.numerator`. -/
private def HomExpression.degree
    {R : Type u} [CommRing R] {I : Type uI} {J : Type uJ}
    {M : I → ModuleCat.{v} R} {src tgt : J → I}
    {i j} : HomExpression M src tgt i j → ℕ
  | .identity _ => 0
  | .const _ => 0
  | .var _ => 1
  | .add f g => f.degree + g.degree
  | .neg f => f.degree
  | .comp f g => f.degree + g.degree

/-- Clear a common denominator `s` from an expression, given numerators for the variables. -/
private def HomExpression.numerator
    {R : Type u} [CommRing R] {I : Type uI} {J : Type uJ}
    {M : I → ModuleCat.{v} R} {src tgt : J → I}
    (s : R) (x : ∀ k, M (src k) ⟶ M (tgt k))
    {i j} : HomExpression M src tgt i j → (M i ⟶ M j)
  | .identity i => 𝟙 (M i)
  | .const f => f
  | .var k => x k
  | .add f g => s ^ g.degree • f.numerator s x + s ^ f.degree • g.numerator s x
  | .neg f => -f.numerator s x
  | .comp f g => f.numerator s x ≫ g.numerator s x

private theorem HomExpression.map_numerator
    {R : Type u} [CommRing R] {I : Type uI} {J : Type uJ}
    {M : I → ModuleCat.{v} R} {src tgt : J → I}
    {C : Type*} [Category C] [Preadditive C] [Linear R C]
    (F : ModuleCat.{v} R ⥤ C) [F.Additive] [F.Linear R]
    (s : R) (x : ∀ k, M (src k) ⟶ M (tgt k))
    (y : ∀ k, F.obj (M (src k)) ⟶ F.obj (M (tgt k)))
    (hxy : ∀ k, F.map (x k) = s • y k)
    {i j} (e : HomExpression M src tgt i j) :
    F.map (e.numerator s x) = s ^ e.degree • e.eval F y := by
  induction e with
  | identity i => simp [numerator, degree, eval]
  | const f => simp [numerator, degree, eval]
  | var k => simpa [numerator, degree, eval] using hxy k
  | add f g hf hg =>
    simp only [numerator, degree, eval, Functor.map_add, Functor.map_smul, hf, hg,
      smul_smul, pow_add, smul_add]
    rw [mul_comm (s ^ g.degree) (s ^ f.degree)]
  | neg f hf => simp [numerator, degree, eval, hf]
  | comp f g hf hg =>
    simp [numerator, degree, eval, hf, hg, Linear.smul_comp, Linear.comp_smul,
      smul_smul, pow_add, mul_comm]

private theorem localizedModuleFunctor_linear
    {R : Type u} [CommRing R] [Small.{v} R] (S : Submonoid R) :
    (ModuleCat.localizedModuleFunctor.{v} S).Linear R where
  map_smul {M N} f r := by
    apply ModuleCat.hom_ext
    let L := IsLocalizedModule.mapExtendScalars S (M.localizedModuleMkLinearMap S)
      (N.localizedModuleMkLinearMap S) (Localization S)
    show L (r • f.hom) = algebraMap R (Localization S) r • L f.hom
    rw [IsScalarTower.algebraMap_smul]
    exact L.map_smul r f.hom

private theorem exists_common_denominator
    {R : Type*} [CommSemiring R] (S : Submonoid R)
    {ι : Type*} [Finite ι] {M N : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M i →ₗ[R] N i) [∀ i, IsLocalizedModule S (f i)]
    (x : ∀ i, N i) : ∃ s : S, ∃ y : ∀ i, M i, ∀ i, f i (y i) = s • x i := by
  classical
  let := Fintype.ofFinite ι
  choose y hy using fun i => IsLocalizedModule.surj S (f i) (x i)
  refine ⟨∏ i, (y i).2, fun i => (∏ j ∈ Finset.univ.erase i, (y j).2) • (y i).1, ?_⟩
  intro i
  rw [LinearMap.map_smul_of_tower, ← hy i, smul_smul,
    Finset.prod_erase_mul _ _ (Finset.mem_univ i)]

private theorem exists_common_annihilator
    {R : Type*} [CommSemiring R] (S : Submonoid R)
    {ι : Type*} [Finite ι] {M N : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M i →ₗ[R] N i) [∀ i, IsLocalizedModule S (f i)]
    (x : ∀ i, M i) (hx : ∀ i, f i (x i) = 0) :
    ∃ s : S, ∀ i, s • x i = 0 := by
  classical
  let := Fintype.ofFinite ι
  have h (i : ι) : ∃ s : S, s • x i = 0 := by
    obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f i)
      ((hx i).trans (map_zero (f i)).symm)
    exact ⟨s, by simpa using hs⟩
  choose s hs using h
  refine ⟨∏ i, s i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul, hs, smul_zero]

private theorem localizedModuleFunctor_smul
    {R : Type u} [CommRing R] [Small.{v} R] (S : Submonoid R)
    (M N : ModuleCat.{v} R) (r : R)
    (f : (ModuleCat.localizedModuleFunctor.{v} S).obj M ⟶
      (ModuleCat.localizedModuleFunctor.{v} S).obj N) :
    r • f = algebraMap R (Localization S) r • f :=
  rfl

private theorem localizedModuleFunctor_hom_isLocalizedModule
    {R : Type u} [CommRing R] [Small.{v} R] (S : Submonoid R)
    (M N : ModuleCat.{v} R) [Module.FinitePresentation R M] :
    letI : (ModuleCat.localizedModuleFunctor.{v} S).Linear R :=
      localizedModuleFunctor_linear.{u, v} S
    IsLocalizedModule S ((ModuleCat.localizedModuleFunctor.{v} S).mapLinearMap R
      (X := M) (Y := N)) := by
  let : (ModuleCat.localizedModuleFunctor.{v} S).Linear R :=
    localizedModuleFunctor_linear.{u, v} S
  let F := ModuleCat.localizedModuleFunctor.{v} S
  let L := IsLocalizedModule.mapExtendScalars S (M.localizedModuleMkLinearMap S)
    (N.localizedModuleMkLinearMap S) (Localization S)
  constructor
  · intro s
    rw [Module.End.isUnit_iff]
    show Function.Bijective
      (fun f : F.obj M ⟶ F.obj N => algebraMap R (Localization S) (s : R) • f)
    exact (IsLocalization.map_units (Localization S) s).smul_bijective
  · intro x
    obtain ⟨⟨y, s⟩, hy⟩ := IsLocalizedModule.surj S L x.hom
    refine ⟨⟨ModuleCat.ofHom y, s⟩, ?_⟩
    ext z
    show algebraMap R (Localization S) (s : R) • x z = (L y) z
    exact (IsScalarTower.algebraMap_smul (Localization S) (s : R)
      (show N.localizedModule S from x z)).trans (LinearMap.congr_fun hy z)
  · intro x y h
    obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := L)
      (congrArg ModuleCat.Hom.hom h)
    exact ⟨s, ModuleCat.hom_ext hs⟩

/-- A finite system of equations between homomorphisms, solvable after localizing at a submonoid,
is solvable after inverting a single element of that submonoid. -/
private theorem exists_away_solution_of_localized_hom_equations
    {R : Type u} [CommRing R] [Small.{v} R] (S : Submonoid R)
    {I J E : Type*} [Finite J] [Finite E]
    (M : I → ModuleCat.{v} R) [∀ i, Module.FinitePresentation R (M i)]
    (src tgt : J → I) (es et : E → I)
    (eqs : ∀ k, HomExpression M src tgt (es k) (et k))
    (x : ∀ k, (ModuleCat.localizedModuleFunctor.{v} S).obj (M (src k)) ⟶
      (ModuleCat.localizedModuleFunctor.{v} S).obj (M (tgt k)))
    (hx : ∀ k, (eqs k).eval (ModuleCat.localizedModuleFunctor S) x = 0) :
    ∃ s : S, ∃ y : ∀ k,
      (ModuleCat.localizedModuleFunctor.{v} (Submonoid.powers (s : R))).obj (M (src k)) ⟶
        (ModuleCat.localizedModuleFunctor.{v} (Submonoid.powers (s : R))).obj (M (tgt k)),
      ∀ k, (eqs k).eval (ModuleCat.localizedModuleFunctor (Submonoid.powers (s : R))) y = 0 := by
  classical
  let F := ModuleCat.localizedModuleFunctor.{v} S
  let : F.Linear R := localizedModuleFunctor_linear.{u, v} S
  have hloc (i j : I) : IsLocalizedModule S (F.mapLinearMap R (X := M i) (Y := M j)) :=
    localizedModuleFunctor_hom_isLocalizedModule.{u, v} S (M i) (M j)
  obtain ⟨s, n, hn⟩ := exists_common_denominator S
    (fun k => F.mapLinearMap R (X := M (src k)) (Y := M (tgt k))) x
  have hz (k : E) : F.map ((eqs k).numerator (s : R) n) = 0 := by
    rw [(eqs k).map_numerator F (s : R) n x hn, hx, smul_zero]
  obtain ⟨t, ht⟩ := exists_common_annihilator S
    (fun k => F.mapLinearMap R (X := M (es k)) (Y := M (et k)))
    (fun k => (eqs k).numerator (s : R) n) hz
  let a : S := s * t
  let A := Localization.Away (a : R)
  let G := ModuleCat.localizedModuleFunctor.{v} (Submonoid.powers (a : R))
  let : G.Linear R := localizedModuleFunctor_linear.{u, v} _
  have hg (i j : I) : IsLocalizedModule (Submonoid.powers (a : R))
      (G.mapLinearMap R (X := M i) (Y := M j)) :=
    localizedModuleFunctor_hom_isLocalizedModule.{u, v} _ _ _
  have hs : IsUnit (algebraMap R A (s : R)) :=
    IsLocalization.Away.isUnit_of_dvd (a : R) (show (s : R) ∣ (a : R) from ⟨t, rfl⟩)
  have hy (k : J) : ∃ y : G.obj (M (src k)) ⟶ G.obj (M (tgt k)),
      (s : R) • y = G.map (n k) := by
    obtain ⟨y, hy⟩ := hs.smul_bijective.surjective (G.map (n k))
    exact ⟨y, (localizedModuleFunctor_smul.{u, v} _ _ _ _ y).trans hy⟩
  choose y hy using hy
  refine ⟨a, y, fun k => ?_⟩
  have hnum : G.map ((eqs k).numerator (s : R) n) = 0 := by
    apply IsLocalizedModule.smul_injective (f := G.mapLinearMap R)
      (⟨(a : R), Submonoid.mem_powers _⟩ : Submonoid.powers (a : R))
    show (a : R) • G.map ((eqs k).numerator (s : R) n) = (a : R) • 0
    rw [← Functor.map_smul, smul_zero]
    have hzero : (a : R) • (eqs k).numerator (s : R) n = 0 := by
      show ((s : R) * (t : R)) • _ = 0
      rw [mul_smul, show (t : R) • (eqs k).numerator (s : R) n = 0 from ht k, smul_zero]
    rw [hzero, Functor.map_zero]
  have hinj : Function.Injective (fun z : G.obj (M (es k)) ⟶ G.obj (M (et k)) =>
      (s : R) ^ (eqs k).degree • z) := by
    have hi := (hs.pow (eqs k).degree).smul_bijective.injective
      (β := G.obj (M (es k)) ⟶ G.obj (M (et k)))
    intro z z' h
    exact hi (by rwa [← map_pow])
  apply hinj
  show (s : R) ^ (eqs k).degree • (eqs k).eval G y = _
  rw [← (eqs k).map_numerator G (s : R) n y (fun k => (hy k).symm), hnum]
  exact (smul_zero _).symm

/-- Discard the variables whose source module vanishes. -/
private def HomExpression.restrictVariables
    {R : Type u} [CommRing R] {I J : Type*}
    {M : I → ModuleCat.{v} R} {src tgt : J → I}
    (T : Set J) [DecidablePred (· ∈ T)] {i j} :
    HomExpression M src tgt i j →
      HomExpression M (fun k : T => src k) (fun k : T => tgt k) i j
  | .identity i => .identity i
  | .const f => .const f
  | .var k => if h : k ∈ T then .var (⟨k, h⟩ : T) else .const 0
  | .add f g => .add (f.restrictVariables T) (g.restrictVariables T)
  | .neg f => .neg (f.restrictVariables T)
  | .comp f g => .comp (f.restrictVariables T) (g.restrictVariables T)

private theorem HomExpression.eval_restrictVariables
    {R : Type u} [CommRing R] {I J : Type*}
    {M : I → ModuleCat.{v} R} {src tgt : J → I}
    {C : Type*} [Category C] [Preadditive C]
    (F : ModuleCat.{v} R ⥤ C) [F.Additive]
    (T : Set J) [DecidablePred (· ∈ T)]
    (x : ∀ k, F.obj (M (src k)) ⟶ F.obj (M (tgt k)))
    (hx : ∀ k, k ∉ T → x k = 0)
    {i j} (e : HomExpression M src tgt i j) :
    (e.restrictVariables T).eval F (fun k : T => x k.val) = e.eval F x := by
  induction e with
  | identity i => rfl
  | const f => rfl
  | var k => by_cases h : k ∈ T <;> simp [restrictVariables, eval, h, hx]
  | add f g hf hg => simp only [restrictVariables, eval, hf, hg]
  | neg f hf => simp only [restrictVariables, eval, hf]
  | comp f g hf hg => simp only [restrictVariables, eval, hf, hg]

/-- The same as `exists_away_solution_of_localized_hom_equations`, with the finiteness of the
index sets replaced by the vanishing of all but finitely many of the modules involved. -/
private theorem exists_away_solution_of_supported_hom_equations
    {R : Type u} [CommRing R] [Small.{v} R] (S : Submonoid R)
    {I J E : Type*} (M : I → ModuleCat.{v} R)
    [∀ i, Module.FinitePresentation R (M i)]
    (src tgt : J → I) (es et : E → I)
    (eqs : ∀ k, HomExpression M src tgt (es k) (et k))
    (TJ : Set J) (TE : Set E) (hTJ : TJ.Finite) (hTE : TE.Finite)
    (hJ : ∀ k, k ∉ TJ → IsZero (M (src k)))
    (hE : ∀ k, k ∉ TE → IsZero (M (es k)))
    (x : ∀ k, (ModuleCat.localizedModuleFunctor.{v} S).obj (M (src k)) ⟶
      (ModuleCat.localizedModuleFunctor.{v} S).obj (M (tgt k)))
    (hx : ∀ k, (eqs k).eval (ModuleCat.localizedModuleFunctor S) x = 0) :
    ∃ s : S, ∃ y : ∀ k,
      (ModuleCat.localizedModuleFunctor.{v} (Submonoid.powers (s : R))).obj (M (src k)) ⟶
        (ModuleCat.localizedModuleFunctor.{v} (Submonoid.powers (s : R))).obj (M (tgt k)),
      ∀ k, (eqs k).eval (ModuleCat.localizedModuleFunctor (Submonoid.powers (s : R))) y = 0 := by
  classical
  let := hTJ.to_subtype
  let := hTE.to_subtype
  let F := ModuleCat.localizedModuleFunctor.{v} S
  have hx0 (k : J) (hk : k ∉ TJ) : x k = 0 :=
    (F.map_isZero (hJ k hk)).eq_of_src _ _
  obtain ⟨s, y, hy⟩ := exists_away_solution_of_localized_hom_equations.{u, v} S M
    (fun k : TJ => src k) (fun k : TJ => tgt k)
    (fun k : TE => es k) (fun k : TE => et k)
    (fun k : TE => (eqs k).restrictVariables TJ) (fun k => x k)
    (fun k => ((eqs k).eval_restrictVariables F TJ x hx0).trans (hx k))
  let G := ModuleCat.localizedModuleFunctor.{v} (Submonoid.powers (s : R))
  let y' (k : J) : G.obj (M (src k)) ⟶ G.obj (M (tgt k)) :=
    if h : k ∈ TJ then y ⟨k, h⟩ else 0
  refine ⟨s, y', fun k => ?_⟩
  by_cases hk : k ∈ TE
  · have hh := (eqs k).eval_restrictVariables G TJ y' (by intros; simp_all [y'])
    rw [← hh]
    have hres : (fun j : TJ => y' j) = y := by funext j; simp [y']
    rw [hres]
    exact hy ⟨k, hk⟩
  · exact (G.map_isZero (hE k hk)).eq_of_src _ _

/-- A homotopy between maps of `ℤ`-indexed cochain complexes, as an equation in components. -/
private theorem homotopy_comm_apply_up_int
    {C : Type*} [Category C] [Preadditive C]
    {P Q : CochainComplex C ℤ} {f g : P ⟶ Q} (h : Homotopy f g) (i : ℤ) :
    f.f i = P.d i (i + 1) ≫ h.hom (i + 1) i + h.hom i (i - 1) ≫ Q.d (i - 1) i + g.f i := by
  rw [h.comm i, dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)]

private theorem exists_homotopy_of_consecutive_components
    {C : Type*} [Category C] [Preadditive C]
    {P Q : CochainComplex C ℤ} (f g : P ⟶ Q)
    (h : ∀ i, P.X i ⟶ Q.X (i - 1))
    (hc : ∀ i, f.f i =
      P.d i (i + 1) ≫ h (i + 1) ≫ eqToHom (by congr 1; omega) +
        h i ≫ Q.d (i - 1) i + g.f i) : Nonempty (Homotopy f g) := by
  classical
  let H (i j : ℤ) : P.X i ⟶ Q.X j :=
    if e : i - 1 = j then h i ≫ eqToHom (congrArg Q.X e) else 0
  refine ⟨{ hom := H, zero := ?_, comm := ?_ }⟩
  · intro i j hij
    simp only [ComplexShape.up_Rel] at hij
    simp only [H, dite_eq_right (by omega : i - 1 ≠ j)]
  · intro i
    rw [dNext_eq H (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq H (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)]
    simpa [H] using hc i

private theorem hom_comp_eqToHom_add_sub_one
    {C : Type*} [Category C] (X : ℤ → C) {A : C}
    (f : ∀ i, A ⟶ X i) (i : ℤ) :
    f (i + 1 - 1) ≫ eqToHom (congrArg X (by omega : i + 1 - 1 = i)) = f i := by
  simp

-- The five families of dependent equations recording a homotopy equivalence are elaborated
-- against a dependent index type, which exceeds the default budget; this is the only
-- heartbeat raise in the module.
set_option backward.isDefEq.respectTransparency false in
/-- A homotopy equivalence, over the localization of `R` at a submonoid `S`, between a complex
with prescribed terms and the localization of a complex over `R`, descends to a homotopy
equivalence after inverting a single element of `S`. -/
private theorem exists_away_homotopy_model
    {R : Type u} [CommRing R] [Small.{v} R] (S : Submonoid R)
    (L : CochainComplex (ModuleCat.{v} R) ℤ)
    (X : ℤ → ModuleCat.{v} R)
    [∀ i, Module.FinitePresentation R (L.X i)]
    [∀ i, Module.FinitePresentation R (X i)]
    (T : Set ℤ) (hT : T.Finite)
    (hX : ∀ i, i ∉ T → IsZero (X i))
    (hL : ∀ i, i ∉ T → IsZero (L.X i))
    (d : ∀ i, (ModuleCat.localizedModuleFunctor.{v} S).obj (X i) ⟶
      (ModuleCat.localizedModuleFunctor.{v} S).obj (X (i + 1)))
    (hd : ∀ i, d i ≫ d (i + 1) = 0)
    (e : HomotopyEquiv (CochainComplex.of _ d hd)
      (((ModuleCat.localizedModuleFunctor.{v} S).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L)) :
    ∃ s : S, ∃ Q : CochainComplex (ModuleCat.{v} (Localization.Away (s : R))) ℤ,
      (∀ i, Q.X i = (ModuleCat.localizedModuleFunctor.{v}
        (Submonoid.powers (s : R))).obj (X i)) ∧
      Nonempty (HomotopyEquiv Q
        (((ModuleCat.localizedModuleFunctor.{v}
          (Submonoid.powers (s : R))).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) := by
  classical
  let F := ModuleCat.localizedModuleFunctor.{v} S
  let M : Bool × ℤ → ModuleCat.{v} R := fun k =>
    match k.1 with
    | false => X k.2
    | true => L.X k.2
  have (k : Bool × ℤ) : Module.FinitePresentation R (M k) := by
    rcases k with ⟨b, i⟩; cases b <;> dsimp [M] <;> infer_instance
  let src : Fin 5 × ℤ → Bool × ℤ := fun ⟨k, i⟩ =>
    match k with
    | 0 => (false, i)
    | 1 => (false, i)
    | 2 => (true, i)
    | 3 => (false, i)
    | 4 => (true, i)
  let tgt : Fin 5 × ℤ → Bool × ℤ := fun ⟨k, i⟩ =>
    match k with
    | 0 => (false, i + 1)
    | 1 => (true, i)
    | 2 => (false, i)
    | 3 => (false, i - 1)
    | 4 => (true, i - 1)
  let es : Fin 5 × ℤ → Bool × ℤ := src
  let et : Fin 5 × ℤ → Bool × ℤ := fun ⟨k, i⟩ =>
    match k with
    | 0 => (false, i + 1 + 1)
    | 1 => (true, i + 1)
    | 2 => (false, i + 1)
    | 3 => (false, i)
    | 4 => (true, i)
  let Dv (i : ℤ) : HomExpression M src tgt (false, i) (false, i + 1) :=
    HomExpression.var (M := M) (src := src) (tgt := tgt) (0, i)
  let Av (i : ℤ) : HomExpression M src tgt (false, i) (true, i) :=
    HomExpression.var (M := M) (src := src) (tgt := tgt) (1, i)
  let Bv (i : ℤ) : HomExpression M src tgt (true, i) (false, i) :=
    HomExpression.var (M := M) (src := src) (tgt := tgt) (2, i)
  let Hv (i : ℤ) : HomExpression M src tgt (false, i) (false, i - 1) :=
    HomExpression.var (M := M) (src := src) (tgt := tgt) (3, i)
  let Jv (i : ℤ) : HomExpression M src tgt (true, i) (true, i - 1) :=
    HomExpression.var (M := M) (src := src) (tgt := tgt) (4, i)
  let cX (i : ℤ) : HomExpression M src tgt (false, i + 1 - 1) (false, i) :=
    .const (eqToHom (by dsimp [M]; congr 1; omega))
  let cX' (i : ℤ) : HomExpression M src tgt (false, i - 1 + 1) (false, i) :=
    .const (eqToHom (by dsimp [M]; congr 1; omega))
  let cL (i : ℤ) : HomExpression M src tgt (true, i + 1 - 1) (true, i) :=
    .const (eqToHom (by dsimp [M]; congr 1; omega))
  let ld (i j : ℤ) : HomExpression M src tgt (true, i) (true, j) := .const (L.d i j)
  let idX (i : ℤ) : HomExpression M src tgt (false, i) (false, i) := .identity (false, i)
  let idL (i : ℤ) : HomExpression M src tgt (true, i) (true, i) := .identity (true, i)
  let eqs : ∀ k : Fin 5 × ℤ, HomExpression M src tgt (es k) (et k) := fun ⟨k, i⟩ => by
    match k with
    | 0 => exact (Dv i).comp (Dv (i + 1))
    | 1 => exact ((Av i).comp (ld i (i + 1))).add (.neg ((Dv i).comp (Av (i + 1))))
    | 2 => exact ((Bv i).comp (Dv i)).add (.neg ((ld i (i + 1)).comp (Bv (i + 1))))
    | 3 =>
      exact ((Av i).comp (Bv i)).add (.neg
        (((((Dv i).comp (Hv (i + 1))).comp (cX i)).add
          ((Hv i).comp ((Dv (i - 1)).comp (cX' i)))).add (idX i)))
    | 4 =>
      exact ((Bv i).comp (Av i)).add (.neg
        (((((ld i (i + 1)).comp (Jv (i + 1))).comp (cL i)).add
          ((Jv i).comp (ld (i - 1) i))).add (idL i)))
  let x : ∀ k : Fin 5 × ℤ, F.obj (M (src k)) ⟶ F.obj (M (tgt k)) := fun ⟨k, i⟩ => by
    match k with
    | 0 => exact d i
    | 1 => exact e.hom.f i
    | 2 => exact e.inv.f i
    | 3 => exact e.homotopyHomInvId.hom i (i - 1)
    | 4 => exact e.homotopyInvHomId.hom i (i - 1)
  have hx (k : Fin 5 × ℤ) : (eqs k).eval F x = 0 := by
    rcases k with ⟨k, i⟩
    fin_cases k
    · exact hd i
    all_goals dsimp only [M, src, tgt, es, et, eqs, HomExpression.eval, ld, idX, idL,
      Av, Bv, Dv, Hv, Jv, cX, cX', cL, x]
    all_goals rw [add_neg_eq_zero]
    · simpa [F, CochainComplex.of_d] using e.hom.comm i (i + 1)
    · simpa [F, CochainComplex.of_d] using e.inv.comm i (i + 1)
    · have hh := homotopy_comm_apply_up_int e.homotopyHomInvId i
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
        Functor.map_id, eqToHom_map, hom_comp_eqToHom_add_sub_one,
        F.map_id (X i), F, CochainComplex.of.d,
        add_sub_cancel_right, sub_add_cancel, dite_true, eqToHom_refl, Category.comp_id,
        Category.assoc] using hh
    · have hh := homotopy_comm_apply_up_int e.homotopyInvHomId i
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
        Functor.map_id, eqToHom_map, hom_comp_eqToHom_add_sub_one,
        Functor.mapHomologicalComplex_obj_X, Functor.mapHomologicalComplex_obj_d,
        F.map_id (L.X i), F, add_sub_cancel_right,
        eqToHom_refl, Category.comp_id, Category.assoc] using hh
  have hz (k : Fin 5 × ℤ) (hk : k ∉ Set.univ ×ˢ T) : IsZero (M (src k)) := by
    have hi : k.2 ∉ T := by simpa using hk
    rcases k with ⟨k, i⟩
    fin_cases k <;> dsimp [src, M] <;> first | exact hX i hi | exact hL i hi
  obtain ⟨s, y, hy⟩ := exists_away_solution_of_supported_hom_equations.{u, v} S M src tgt es et
    eqs (Set.univ ×ˢ T) (Set.univ ×ˢ T) (Set.toFinite _ |>.prod hT)
    (Set.toFinite _ |>.prod hT) hz hz x hx
  let G := ModuleCat.localizedModuleFunctor.{v} (Submonoid.powers (s : R))
  let d' (i : ℤ) : G.obj (X i) ⟶ G.obj (X (i + 1)) := y (0, i)
  have hd' (i : ℤ) : d' i ≫ d' (i + 1) = 0 := hy (0, i)
  let Q := CochainComplex.of (fun i => G.obj (X i)) d' hd'
  let LG := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  have hy' (k : Fin 5) (i : ℤ) := hy (k, i)
  let f : Q ⟶ LG := CochainComplex.ofHom (fun i => y (1, i)) (fun i => by
    have hh := hy' 1 i
    dsimp only [M, src, tgt, es, et, eqs, HomExpression.eval, ld, Av, Dv] at hh
    simpa [G, Q, LG, d', M, src, tgt, es, et, CochainComplex.of_d] using add_neg_eq_zero.mp hh)
  let g : LG ⟶ Q := CochainComplex.ofHom (fun i => y (2, i)) (fun i => by
    have hh := hy' 2 i
    dsimp only [M, src, tgt, es, et, eqs, HomExpression.eval, ld, Bv, Dv] at hh
    simpa [G, Q, LG, d', M, src, tgt, es, et, CochainComplex.of_d] using add_neg_eq_zero.mp hh)
  obtain ⟨hfg⟩ := exists_homotopy_of_consecutive_components (f ≫ g) (𝟙 Q)
    (fun i => y (3, i)) (fun i => by
      have hh := hy' 3 i
      dsimp only [M, src, tgt, es, et, eqs, HomExpression.eval, idX, Av, Bv, Dv, Hv,
        cX, cX'] at hh
      rw [add_neg_eq_zero] at hh
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
        Functor.mapHomologicalComplex_obj_X, Functor.mapHomologicalComplex_obj_d,
        Functor.map_id, eqToHom_map, G.map_id (X i), f, g, Q, d',
        HomologicalComplex.comp_f, HomologicalComplex.id_f, CochainComplex.of.d,
        sub_add_cancel, dite_true, eqToHom_refl, Category.comp_id, Category.assoc] using hh)
  obtain ⟨hgf⟩ := exists_homotopy_of_consecutive_components (g ≫ f) (𝟙 LG)
    (fun i => y (4, i)) (fun i => by
      have hh := hy' 4 i
      dsimp only [M, src, tgt, es, et, eqs, HomExpression.eval, ld, idL, Av, Bv, Jv, cL] at hh
      rw [add_neg_eq_zero] at hh
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
        Functor.mapHomologicalComplex_obj_X, Functor.mapHomologicalComplex_obj_d,
        Functor.map_id, eqToHom_map, G.map_id (L.X i), LG, f, g,
        HomologicalComplex.comp_f, HomologicalComplex.id_f, Category.assoc] using hh)
  exact ⟨s, Q, fun _ => rfl, ⟨⟨f, g, hfg, hgf⟩⟩⟩

end HomEquations

end StacksDraft.Perfect
