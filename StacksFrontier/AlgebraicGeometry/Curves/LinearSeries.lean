module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.AlgebraicGeometry.AmpleH1Vanishing.Sections
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.CurveFiniteMorphism.Ample
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequence
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequenceTwist
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.TwoOutOfThree
public import StacksFrontier.AlgebraicGeometry.FiniteTrivialize.TargetCover
public import StacksFrontier.AlgebraicGeometry.Meromorphic.RegularSectionExistence
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestriction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison

/-!
# Linear series on a proper curve

A *linear series* of degree `d` and dimension `r`, classically a `𝔤^r_d`, on a proper scheme of
dimension at most one over a field `k` is an invertible sheaf of degree `d` together with an
`(r + 1)`-dimensional subspace of its space of global sections. Passing to a subspace of a linear
series produces a linear series of the same degree and any smaller dimension.

## Main definitions

* `AlgebraicGeometry.LinearSeries`: a linear series on a proper curve.
* `AlgebraicGeometry.tensorPowSucc`: the tensor powers `ℒ^{⊗ n}` of a module on a scheme.

## Main results

* `AlgebraicGeometry.finrank_cohomologyOverField_unit_zero_eq_one`: on a scheme over `k` whose only
  global functions are the constants, `dim_k H⁰(X, 𝒪_X) = 1`.
* `AlgebraicGeometry.linearSeries_nonempty_of_le`: a linear series of dimension `r` yields one of
  the same degree and every dimension at most `r`.
* `AlgebraicGeometry.linearSeries_dimension_le_degree`: on a proper curve whose only global regular
  functions are the constants, a `𝔤^r_d` has `r ≤ d`.
* `AlgebraicGeometry.genus_eq_zero_of_linearSeries_dimension_eq_degree`: such a curve carrying a
  `𝔤^d_d` of positive degree `d` has genus zero.
* `AlgebraicGeometry.linearSeries_dimension_le_degree_and_genus_eq_zero`: both of these statements
  together.
* `AlgebraicGeometry.nonempty_linearSeries_zero_zero`: such a curve carries a `𝔤^0_0`.
* `AlgebraicGeometry.exists_counterexample_to_displayed_statement_of_tag_0CCS_at_zero`: such a
  curve of nonzero genus carries a `𝔤^r_d` with `r = d`.
* `AlgebraicGeometry.tensorPowSuccIsoTensorPowModule`: the tensor powers above agree with
  `Stacks.Ample.tensorPowModule` in nonnegative degree.
* `AlgebraicGeometry.exists_isZero_cohomologyOverField_one_tensorPowSucc_of_isAmple`: an ample
  invertible module on a scheme proper over a field has a tensor power with vanishing `H¹`.

## References

* [Stacks Project, Tag 0CCN](https://stacks.math.columbia.edu/tag/0CCN)
* [Stacks Project, Tag 0CCQ](https://stacks.math.columbia.edu/tag/0CCQ)
* [Stacks Project, Tag 0CCS](https://stacks.math.columbia.edu/tag/0CCS)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/


@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A linear series of degree `d` and dimension `r` on a proper scheme of dimension at most one
over a field: an invertible sheaf of degree `d` together with an `(r + 1)`-dimensional space of
global sections. -/
@[stacks 0CCN]
structure LinearSeries (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1) (d r : ℕ) where
  /-- The underlying sheaf of the linear series. -/
  L : X.Modules
  /-- The underlying sheaf is invertible. -/
  isInvertible : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L
  /-- The underlying sheaf has degree `d`. -/
  degree_eq : (letI := isInvertible; invertibleCurveDegree k f hdim L) = (d : ℤ)
  /-- The chosen space of global sections. -/
  V : Submodule k (cohomologyOverField k f L 0)
  /-- The chosen space of sections has dimension `r + 1`. -/
  finrank_eq : Module.finrank k V = r + 1

/-- A linear series of degree `d` and dimension `r` yields one of degree `d` and dimension `s` for
every `s ≤ r`. -/
@[stacks 0CCQ]
lemma linearSeries_nonempty_of_le
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (d r s : ℕ)
    (h : Nonempty (LinearSeries k f hdim d r)) (hs : s ≤ r) :
    Nonempty (LinearSeries k f hdim d s) := by
  classical
  obtain ⟨series⟩ := h
  obtain ⟨e, he⟩ := exists_linearIndependent_of_le_finrank
    (R := k) (M := series.V) (n := s + 1) (by rw [series.finrank_eq]; omega)
  refine ⟨{ L := series.L
            isInvertible := series.isInvertible
            degree_eq := series.degree_eq
            V := (Submodule.span k (Set.range e)).map series.V.subtype
            finrank_eq := ?_ }⟩
  simp [Submodule.finrank_map_subtype_eq, finrank_span_eq_card he]

/-! ### Degree-zero cohomology as global sections -/

/-- Degree-zero cohomology over the base field is the module of global sections, with scalars
restricted along the structure morphism. -/
private def cohomologyOverFieldZeroIsoEvaluation (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (F : X.Modules) :
    cohomologyOverField k f F 0 ≅
      (ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).obj
        ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op (⊤ : X.Opens))).obj F) :=
  (ModuleCat.restrictScalars _).mapIso
    ((SheafOfModules.evaluation X.ringCatSheaf
      (Opposite.op (⊤ : X.Opens))).rightDerivedZeroIsoSelf.app F)

/-- On a scheme over a field whose only global functions are the constants, the degree-zero
cohomology of the structure sheaf is one-dimensional. -/
public theorem finrank_cohomologyOverField_unit_zero_eq_one {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] :
    Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) = 1 := by
  have happ : (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp) =
      (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop := by
    rw [show f.appLE ⊤ ⊤ (by simp) = f.appTop from by
      simpa [Scheme.Hom.appTop] using f.appLE_eq_app (U := ⊤)]
  have hρ :
      Function.Bijective ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom := by
    rw [happ]
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  set ρ := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom
  let φ : k →ₗ[k] (ModuleCat.restrictScalars ρ).obj
      ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op (⊤ : X.Opens))).obj
        (SheafOfModules.unit X.ringCatSheaf)) :=
    { toFun := fun a => ρ a
      map_add' := fun a b => map_add ρ a b
      map_smul' := fun a b => map_mul ρ a b }
  rw [(cohomologyOverFieldZeroIsoEvaluation k f
      (SheafOfModules.unit X.ringCatSheaf)).toLinearEquiv.finrank_eq,
    ← (LinearEquiv.ofBijective φ hρ).finrank_eq, Module.finrank_self]

/-! ### Two pieces of linear algebra about exact sequences -/

/-- The dimension of the middle term of a left exact sequence is at most the sum of the dimensions
of the outer two. -/
private lemma finrank_le_add_of_exact {k A B C : Type*} [Field k]
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
    [Module.Finite k A] [Module.Finite k B] [Module.Finite k C]
    (u : A →ₗ[k] B) (v : B →ₗ[k] C) (hu : Function.Injective u) (huv : Function.Exact u v) :
    Module.finrank k B ≤ Module.finrank k A + Module.finrank k C := by
  have hker := LinearMap.finrank_range_add_finrank_ker v
  rw [huv.linearMap_ker_eq, LinearMap.finrank_range_of_inj hu] at hker
  have hv : Module.finrank k (LinearMap.range v) ≤ Module.finrank k C :=
    Submodule.finrank_le _
  omega

/-- In a left exact sequence whose middle dimension is the sum of the outer two, the second map is
surjective. -/
private lemma surjective_of_exact_of_finrank_eq {k A B C : Type*} [Field k]
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
    [Module.Finite k A] [Module.Finite k B] [Module.Finite k C]
    (u : A →ₗ[k] B) (v : B →ₗ[k] C) (hu : Function.Injective u) (huv : Function.Exact u v)
    (h : Module.finrank k B = Module.finrank k A + Module.finrank k C) :
    Function.Surjective v := by
  have hker := LinearMap.finrank_range_add_finrank_ker v
  rw [huv.linearMap_ker_eq, LinearMap.finrank_range_of_inj hu, h] at hker
  exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq (by omega))

/-! ### The exact sequence of a nonzero section of a linear series -/

/-- A module whose degree-zero cohomology over the base field is nontrivial has a section that is
nonzero on `⊤`. -/
lemma exists_eval_top_ne_zero_of_nontrivial_cohomologyOverField_zero {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (L : X.Modules)
    (h : Nontrivial (cohomologyOverField k f L 0)) :
    ∃ s : L.sections, s.eval (Opposite.op ⊤) ≠ 0 := by
  have := h
  have : Nontrivial Γ(L, ⊤) :=
    (cohomologyOverFieldZeroEquivSections k f L).injective.nontrivial
  obtain ⟨t, ht⟩ := exists_ne (0 : Γ(L, ⊤))
  exact ⟨Stacks.PresheafOfModules.sectionOfTop L.val t,
    (Stacks.PresheafOfModules.sectionOfTop_val_top L.val t).trans_ne ht⟩

/-- The sheaf of a linear series has a section that is nonzero on `⊤`. -/
private lemma LinearSeries.exists_eval_top_ne_zero {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} [IsProper f] {hdim : topologicalKrullDim X ≤ 1} {d r : ℕ}
    (series : LinearSeries k f hdim d r) :
    ∃ s : series.L.sections, s.eval (Opposite.op ⊤) ≠ 0 := by
  have hV : Nontrivial series.V := Module.nontrivial_of_finrank_eq_succ series.finrank_eq
  obtain ⟨v, hv⟩ := exists_ne (0 : series.V)
  exact exists_eval_top_ne_zero_of_nontrivial_cohomologyOverField_zero f series.L
    ⟨(v : cohomologyOverField k f series.L 0), 0, fun h => hv (Submodule.coe_eq_zero.mp h)⟩

/-! ### The dimension of the space of sections of a linear series -/

/-- Let `s` be a section of the sheaf `ℒ` of a linear series of degree `d`, nonzero on `⊤`, with
zero scheme `D`. Then `H⁰(X, ℒ)` is finite dimensional of dimension at most `d + 1`, and if the
dimension is `d + 1` then `H⁰(X, ℒ) ⟶ H⁰(D, ℒ|_D)` is surjective. -/
private lemma LinearSeries.finrank_cohomologyOverField_zero_le_succ
    {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
    [IsCurve k f] [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    {hdim : topologicalKrullDim X ≤ 1} {d r : ℕ} (series : LinearSeries k f hdim d r)
    (s : series.L.sections) (hs : s.eval (Opposite.op ⊤) ≠ 0)
    (hL' : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property series.L) :
    FiniteDimensional k (cohomologyOverField k f series.L 0) ∧
      Module.finrank k (cohomologyOverField k f series.L 0) ≤ d + 1 ∧
      (Module.finrank k (cohomologyOverField k f series.L 0) = d + 1 →
        Function.Surjective (cohomologyOverFieldMap k f
          ((Scheme.Modules.pullbackPushforwardAdjunction
            (@zeroScheme X series.L hL' (s.eval (Opposite.op ⊤))).subschemeι).unit.app
              series.L) 0)) := by
  have hunit : ∀ n, FiniteDimensional k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n) :=
    forall_finiteDimensional_cohomologyOverField_unit k f
  have hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 series.L :=
    series.isInvertible
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : series.L.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X series.L
  have hfinD : IsFinite ((@zeroScheme X series.L hL' (s.eval (Opposite.op ⊤))).subschemeι ≫ f) :=
    isFinite_zeroScheme_of_eval_top_ne_zero k f hdim series.L s hs
  have : IsLocallyNoetherian
      (@zeroScheme X series.L hL' (s.eval (Opposite.op ⊤))).subscheme :=
    isLocallyNoetherian_of_isFinite
      ((@zeroScheme X series.L hL' (s.eval (Opposite.op ⊤))).subschemeι ≫ f)
  have hFD : ((Scheme.Modules.pullback
      (@zeroScheme X series.L hL' (s.eval (Opposite.op ⊤))).subschemeι).obj
        series.L).IsCoherent :=
    isCoherent_pullback _ series.L
  obtain ⟨hzero, hSE⟩ := shortExact_zeroScheme_of_isRegularSection X series.L s
    (isRegularSection_of_eval_top_ne_zero series.L s hs)
  have hSE' : (ShortComplex.mk (series.L.unitHomEquiv.symm s)
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (@zeroScheme X series.L hL' (s.eval (Opposite.op ⊤))).subschemeι).unit.app series.L)
      hzero).ShortExact := hSE
  obtain ⟨-, hinj, hex, -, -⟩ := exists_cohomologyOverField_longExactSequence k f hSE'
  have h3 : FiniteDimensional k (cohomologyOverField k f ((Scheme.Modules.pushforward
      (@zeroScheme X series.L hL' (s.eval (Opposite.op ⊤))).subschemeι).obj
        ((Scheme.Modules.pullback
          (@zeroScheme X series.L hL' (s.eval (Opposite.op ⊤))).subschemeι).obj
            series.L)) 0) :=
    finiteDimensional_cohomologyOverField_pushforward_of_isFinite k _ f _ 0
  have h2 : FiniteDimensional k (cohomologyOverField k f series.L 0) :=
    finiteDimensional_cohomologyOverField_of_shortExact k f hSE' 0 (hunit 0) h3
  have h1dim : Module.finrank k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) = 1 :=
    finrank_cohomologyOverField_unit_zero_eq_one f
  have h3dim : Module.finrank k (cohomologyOverField k f ((Scheme.Modules.pushforward
      (@zeroScheme X series.L hL' (s.eval (Opposite.op ⊤))).subschemeι).obj
        ((Scheme.Modules.pullback
          (@zeroScheme X series.L hL' (s.eval (Opposite.op ⊤))).subschemeι).obj
            series.L)) 0) = d := by
    have hdeg := invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_zeroScheme
      k f hdim series.L s hs hunit
    rw [series.degree_eq] at hdeg
    rw [← (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k
      (@zeroScheme X series.L hL' (s.eval (Opposite.op ⊤))).subschemeι f
      ((Scheme.Modules.pullback
        (@zeroScheme X series.L hL' (s.eval (Opposite.op ⊤))).subschemeι).obj series.L)
      0).toLinearEquiv.finrank_eq]
    exact_mod_cast hdeg.symm
  have hb : Module.finrank k (cohomologyOverField k f series.L 0) ≤
      Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) +
        Module.finrank k (cohomologyOverField k f ((Scheme.Modules.pushforward
          (@zeroScheme X series.L hL' (s.eval (Opposite.op ⊤))).subschemeι).obj
            ((Scheme.Modules.pullback
              (@zeroScheme X series.L hL' (s.eval (Opposite.op ⊤))).subschemeι).obj
                series.L)) 0) :=
    finrank_le_add_of_exact _ _ hinj (hex 0)
  refine ⟨h2, by omega, fun heq => ?_⟩
  refine surjective_of_exact_of_finrank_eq
    (A := (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0 : Type u))
    (B := (cohomologyOverField k f series.L 0 : Type u))
    (C := (cohomologyOverField k f ((Scheme.Modules.pushforward
      (@zeroScheme X series.L hL' (s.eval (Opposite.op ⊤))).subschemeι).obj
        ((Scheme.Modules.pullback
          (@zeroScheme X series.L hL' (s.eval (Opposite.op ⊤))).subschemeι).obj
            series.L)) 0 : Type u))
    _ _ hinj (hex 0) ?_
  rw [h1dim, h3dim]
  omega

/-! ### Stacks Tag 0CCS -/

/-- Let `X` be a proper curve over a field `k` with `H⁰(X, 𝒪_X) = k`, spelled as invertibility of
the canonical map from `k`. A `𝔤^r_d` on `X` satisfies `r ≤ d`. -/
theorem linearSeries_dimension_le_degree {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    {hdim : topologicalKrullDim X ≤ 1} {d r : ℕ} (series : LinearSeries k f hdim d r) :
    r ≤ d := by
  have hL' : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property series.L :=
    series.isInvertible
  obtain ⟨s, hs⟩ := series.exists_eval_top_ne_zero
  obtain ⟨hfin, hbound, -⟩ :=
    series.finrank_cohomologyOverField_zero_le_succ s hs hL'
  have hV := Submodule.finrank_le series.V
  rw [series.finrank_eq] at hV
  omega

/-! ### Tensor powers and the twisted sequence of a regular section -/

section Twist

open MonoidalCategory Opposite CategoryTheory.Limits

attribute [local instance] schemeModulesMonoidal

/-- The tensor power `ℒ^{⊗ n}` of a module on a scheme: the structure sheaf for `n = 0` and
`ℒ^{⊗ n} ⊗ ℒ` for `n + 1`. -/
def tensorPowSucc {X : Scheme.{u}} (L : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | n + 1 => tensorPowSucc L n ⊗ L

/-- Every tensor power of an invertible module is invertible. -/
instance isInvertible_tensorPowSucc {X : Scheme.{u}} (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (n : ℕ) :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (tensorPowSucc L n) := by
  induction n with
  | zero =>
      exact (Stacks.SheafOfModules.isInvertible_unit X.sheaf.obj
        X.ringCatSheaf.property).toAlgebraicGeometry
  | succ n ih =>
      have h₁ : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
          (tensorPowSucc L n) :=
        Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ ih
      have h₂ : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
        Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ ‹_›
      exact (Stacks.SheafOfModules.isInvertible_tensorSheaf X.sheaf.obj X.ringCatSheaf.property
        (tensorPowSucc L n) L).toAlgebraicGeometry

/-! ### The tensor powers of the ampleness theory -/

/-- `AlgebraicGeometry.tensorPowSucc L n` is isomorphic to `Stacks.Ample.tensorPowModule X L n` for
every `n : ℕ`. -/
def tensorPowSuccIsoTensorPowModule {X : Scheme.{u}} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] :
    (n : ℕ) → tensorPowSucc L n ≅ Stacks.Ample.tensorPowModule X L (n : ℤ)
  | 0 => (Stacks.Ample.tensorPowModuleZeroIso X L).symm
  | n + 1 =>
      Stacks.RelativeVeryAmple.tensorModulesMapIso X
          (tensorPowSuccIsoTensorPowModule L n)
          (Stacks.Ample.tensorPowModuleOneIso X L).symm ≪≫
        Stacks.Ample.tensorPowModuleAddIso X L (n : ℤ) 1 ≪≫
          Stacks.RelativeVeryAmple.tensorPowModuleCongr X L (by push_cast; ring)

/-- An ample invertible module `ℒ` on a scheme proper over a field has a tensor power `ℒ^{⊗ N}`
with `H¹(X, ℒ^{⊗ N}) = 0`. -/
theorem exists_isZero_cohomologyOverField_one_tensorPowSucc_of_isAmple {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Scheme.Modules.IsAmple X L) :
    ∃ N : ℕ, IsZero (cohomologyOverField k f (tensorPowSucc L N) 1) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hcoh : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  obtain ⟨N, hN⟩ :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist f
      (SheafOfModules.unit X.ringCatSheaf) L
      (Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple X L hL)
  have hzero : IsZero (cohomologyOverField k f
      (Stacks.RelativeVeryAmple.tensorModules X (SheafOfModules.unit X.ringCatSheaf)
        (Stacks.Ample.tensorPowModule X L (N : ℤ))) 1) :=
    (isZero_cohomologyOverField_iff_isZero_hgroup k f _ 1).mpr (hN N 1 le_rfl Nat.one_pos)
  exact ⟨N, hzero.of_iso (cohomologyOverFieldIso k f
    ((tensorPowSuccIsoTensorPowModule L N).trans
      (λ_ (Stacks.Ample.tensorPowModule X L (N : ℤ))).symm) 1)⟩

/-- If `h^* g` is an isomorphism, then so is `h^* (N ◁ g)`. -/
private theorem isIso_pullback_whiskerLeft {X Z : Scheme.{u}} (h : Z ⟶ X) (N : X.Modules)
    {A B : X.Modules} (g : A ⟶ B) (hg : IsIso ((Scheme.Modules.pullback h).map g)) :
    IsIso ((Scheme.Modules.pullback h).map (N ◁ g)) := by
  have hXmap : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
      ((𝟙 N, g) : ((N, A) : X.Modules × X.Modules) ⟶ (N, B)) = N ◁ g :=
    Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map _ (𝟙 N) g
  have hZid : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩)).map
        (((Scheme.Modules.pullback h).map (𝟙 N), (Scheme.Modules.pullback h).map g) :
          (((Scheme.Modules.pullback h).obj N, (Scheme.Modules.pullback h).obj A) :
            Z.Modules × Z.Modules) ⟶
              ((Scheme.Modules.pullback h).obj N, (Scheme.Modules.pullback h).obj B)) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩)).map
        ((𝟙 ((Scheme.Modules.pullback h).obj N), (Scheme.Modules.pullback h).map g) :
          (((Scheme.Modules.pullback h).obj N, (Scheme.Modules.pullback h).obj A) :
            Z.Modules × Z.Modules) ⟶
              ((Scheme.Modules.pullback h).obj N, (Scheme.Modules.pullback h).obj B)) :=
    congrArg (fun k => (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩)).map
        ((k, (Scheme.Modules.pullback h).map g) :
          (((Scheme.Modules.pullback h).obj N, (Scheme.Modules.pullback h).obj A) :
            Z.Modules × Z.Modules) ⟶
              ((Scheme.Modules.pullback h).obj N, (Scheme.Modules.pullback h).obj B)))
      (CategoryTheory.Functor.map_id (Scheme.Modules.pullback h) N)
  have hZwhisker : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩)).map
        ((𝟙 ((Scheme.Modules.pullback h).obj N), (Scheme.Modules.pullback h).map g) :
          (((Scheme.Modules.pullback h).obj N, (Scheme.Modules.pullback h).obj A) :
            Z.Modules × Z.Modules) ⟶
              ((Scheme.Modules.pullback h).obj N, (Scheme.Modules.pullback h).obj B)) =
      (Scheme.Modules.pullback h).obj N ◁ (Scheme.Modules.pullback h).map g :=
    Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map _
      (𝟙 ((Scheme.Modules.pullback h).obj N)) ((Scheme.Modules.pullback h).map g)
  have hmid : IsIso ((Scheme.Modules.pullback h).obj N ◁ (Scheme.Modules.pullback h).map g) :=
    Functor.map_isIso (MonoidalCategory.tensorLeft ((Scheme.Modules.pullback h).obj N)) _
  have hnat : (Scheme.Modules.pullback h).map (N ◁ g) ≫
        (Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom).app
          ((N, B) : X.Modules × X.Modules) =
      (Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom).app
          ((N, A) : X.Modules × X.Modules) ≫
        ((Scheme.Modules.pullback h).obj N ◁ (Scheme.Modules.pullback h).map g) :=
    (congrArg (fun k => (Scheme.Modules.pullback h).map k ≫
          (Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom).app
            ((N, B) : X.Modules × X.Modules)) hXmap).symm.trans
      (((Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom).naturality
          (X := ((N, A) : X.Modules × X.Modules)) (Y := ((N, B) : X.Modules × X.Modules))
          (𝟙 N, g)).trans
        (congrArg (fun k => (Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom).app
          ((N, A) : X.Modules × X.Modules) ≫ k) (hZid.trans hZwhisker)))
  have hA : IsIso ((Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom).app
      ((N, A) : X.Modules × X.Modules)) :=
    Stacks.RingedSpace.comparisonNatTrans_app_isIso h.toLRSHom.toShHom
      ((N, A) : X.Modules × X.Modules)
  have hB : IsIso ((Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom).app
      ((N, B) : X.Modules × X.Modules)) :=
    Stacks.RingedSpace.comparisonNatTrans_app_isIso h.toLRSHom.toShHom
      ((N, B) : X.Modules × X.Modules)
  have hcomp : IsIso ((Scheme.Modules.pullback h).map (N ◁ g) ≫
      (Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom).app
        ((N, B) : X.Modules × X.Modules)) := by
    rw [hnat]
    exact IsIso.comp_isIso' hA hmid
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _
    ((Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom).app
      ((N, B) : X.Modules × X.Modules)) hB hcomp

/-- If `i^* t` is an isomorphism, then so is `i^* ((ρ_ N).inv ≫ N ◁ t)`. -/
private theorem isIso_pullback_tensorSection {X Z : Scheme.{u}} (i : Z ⟶ X) (N L : X.Modules)
    (t : SheafOfModules.unit X.ringCatSheaf ⟶ L)
    (ht : IsIso ((Scheme.Modules.pullback i).map t)) :
    IsIso ((Scheme.Modules.pullback i).map ((ρ_ N).inv ≫ N ◁ t)) := by
  rw [CategoryTheory.Functor.map_comp]
  exact IsIso.comp_isIso' (Functor.map_isIso (Scheme.Modules.pullback i) (ρ_ N).inv)
    (isIso_pullback_whiskerLeft i N t ht)

/-- Cohomology over the base field carries an isomorphism of modules to a bijection. -/
private lemma bijective_cohomologyOverFieldMap_of_isIso {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {F G : X.Modules} (φ : F ⟶ G) (hφ : IsIso φ) (n : ℕ) :
    Function.Bijective (cohomologyOverFieldMap k f φ n) := by
  have := hφ
  have h₁ : cohomologyOverFieldMap k f φ n ≫ cohomologyOverFieldMap k f (inv φ) n = 𝟙 _ := by
    rw [← cohomologyOverFieldMap_comp, IsIso.hom_inv_id, cohomologyOverFieldMap_id]
  have h₂ : cohomologyOverFieldMap k f (inv φ) n ≫ cohomologyOverFieldMap k f φ n = 𝟙 _ := by
    rw [← cohomologyOverFieldMap_comp, IsIso.inv_hom_id, cohomologyOverFieldMap_id]
  have : IsIso (cohomologyOverFieldMap k f φ n) := ⟨⟨_, h₁, h₂⟩⟩
  exact (ConcreteCategory.isIso_iff_bijective _).mp this

/-- Let `φ : ℱ ⟶ 𝒢` be a morphism with `i_* i^* φ` an isomorphism. If `H⁰` of the unit of
`i^* ⊣ i_*` at `ℱ` is surjective, then so is `H⁰` of the unit at `𝒢`. -/
private lemma surjective_cohomologyOverFieldMap_unit_of_isIso {k : Type u} [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) (i : Z ⟶ X) {A B : X.Modules} (φ : A ⟶ B)
    (hφ : IsIso ((Scheme.Modules.pullback i).map φ))
    (h : Function.Surjective (cohomologyOverFieldMap k f
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app A) 0)) :
    Function.Surjective (cohomologyOverFieldMap k f
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app B) 0) := by
  have hφ' : IsIso ((Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map φ)) :=
    Functor.map_isIso _ _
  have hnat : (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app A ≫
      (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map φ) =
      φ ≫ (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app B :=
    Adjunction.unit_naturality _ φ
  have hmap := congrArg (fun ψ => cohomologyOverFieldMap k f ψ 0) hnat
  rw [cohomologyOverFieldMap_comp, cohomologyOverFieldMap_comp] at hmap
  have hpt : ∀ x, cohomologyOverFieldMap k f
        ((Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map φ)) 0
        (cohomologyOverFieldMap k f
          ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app A) 0 x) =
      cohomologyOverFieldMap k f
        ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app B) 0
        (cohomologyOverFieldMap k f φ 0 x) :=
    fun x => DFunLike.congr_fun (congrArg ConcreteCategory.hom hmap) x
  intro w
  obtain ⟨v, hv⟩ := (bijective_cohomologyOverFieldMap_of_isIso f _ hφ' 0).2 w
  obtain ⟨x, hx⟩ := h v
  exact ⟨cohomologyOverFieldMap k f φ 0 x, ((hpt x).symm.trans (by rw [hx])).trans hv⟩

/-- If `H⁰` of `φ : ℱ ⟶ 𝒢` is surjective, then every morphism `𝒪_X ⟶ 𝒢` factors through `φ`. -/
private lemma exists_comp_eq_of_surjective_cohomologyOverFieldMap {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {F G : X.Modules} (φ : F ⟶ G)
    (h : Function.Surjective (cohomologyOverFieldMap k f φ 0))
    (q : SheafOfModules.unit X.ringCatSheaf ⟶ G) :
    ∃ p : SheafOfModules.unit X.ringCatSheaf ⟶ F, p ≫ φ = q := by
  obtain ⟨b, hb⟩ := h ((cohomologyOverFieldZeroEquivSections k f G).symm
    ((G.unitHomEquiv q).eval (op ⊤)))
  have hval : (G.unitHomEquiv q).eval (op ⊤) =
      φ.val.app (op ⊤) (cohomologyOverFieldZeroEquivSections k f F b) :=
    ((cohomologyOverFieldZeroEquivSections k f G).apply_symm_apply _).symm.trans
      ((congrArg (cohomologyOverFieldZeroEquivSections k f G) hb.symm).trans
        (cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap k f φ b))
  obtain ⟨x, hxtop⟩ : ∃ x : F.sections, x.eval (op ⊤) =
      cohomologyOverFieldZeroEquivSections k f F b :=
    ⟨Stacks.PresheafOfModules.sectionOfTop F.val _,
      Stacks.PresheafOfModules.sectionOfTop_val_top _ _⟩
  have hstep : F.unitHomEquiv.symm x ≫ φ
      = G.unitHomEquiv.symm (SheafOfModules.sectionsMap φ x) :=
    SheafOfModules.unitHomEquiv_symm_comp x φ
  have hsec : SheafOfModules.sectionsMap φ x = G.unitHomEquiv q :=
    Stacks.PresheafOfModules.sections_ext_top (by simpa [hxtop] using hval.symm)
  exact ⟨F.unitHomEquiv.symm x, hstep.trans
    ((congrArg G.unitHomEquiv.symm hsec).trans (G.unitHomEquiv.symm_apply_apply q))⟩

/-- A module on a scheme whose restriction to the open subscheme `⊤` is trivial is trivial. -/
private lemma isTrivial_of_isTrivial_restrict_top (X : Scheme.{u}) (F : X.Modules)
    (hF : Stacks.SheafOfModules.IsTrivial (⊤ : X.Opens).toScheme.presheaf
      (⊤ : X.Opens).toScheme.ringCatSheaf.2 (F.restrict (Scheme.Opens.ι (⊤ : X.Opens)))) :
    Stacks.SheafOfModules.IsTrivial X.presheaf X.ringCatSheaf.2 F := by
  obtain ⟨e⟩ := hF
  let g := (Scheme.topIso X).symm
  let eF := (Scheme.Modules.pullback g.hom).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback (Scheme.topIso X).hom).app F) ≪≫
    (Scheme.Modules.pullbackComp g.hom (Scheme.topIso X).hom).app F ≪≫
    (Scheme.Modules.pullbackCongr (Scheme.topIso X).inv_hom_id).app F ≪≫
    (Scheme.Modules.pullbackId X).app F
  let eUnit := ((Scheme.Modules.restrictFunctorIsoPullback g.hom).app
      (SheafOfModules.unit (⊤ : X.Opens).toScheme.ringCatSheaf)).symm ≪≫
    Scheme.Modules.restrictUnitIso g.hom
  exact ⟨eF.symm ≪≫ (Scheme.Modules.pullback g.hom).mapIso e ≪≫ eUnit⟩

/-- An invertible module on a scheme finite over a field is isomorphic to the structure sheaf. -/
private lemma nonempty_iso_unit_of_isFinite_over_field {k : Type u} [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) [IsFinite p] (F : Z.Modules)
    (hF : Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 F) :
    Nonempty (F ≅ SheafOfModules.unit Z.ringCatSheaf) := by
  obtain ⟨V, hyV, hV⟩ := @Stacks.Divisors.exists_isTrivial_restrict_preimage_of_isFinite
    Z (Spec (.of k)) p inferInstance F hF (default : Spec (.of k))
  have hVtop : V = ⊤ := by
    ext z
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have hzy : z = (default : Spec (.of k)) := Subsingleton.elim _ _
    simpa [hzy] using hyV
  have hWtop : p ⁻¹ᵁ V = ⊤ := by rw [hVtop]; ext z; simp
  rw [hWtop] at hV
  exact isTrivial_of_isTrivial_restrict_top Z F (by simpa using hV)

/-- Let `F ⊣ G` with unit `η`, and let `e : F U ≅ F L`. If every morphism `U ⟶ G (F L)` factors as
`p ≫ η L`, then there is `p : U ⟶ L` with `F.map p` an isomorphism. -/
private lemma exists_isIso_map_of_surjective_comp_unit {C : Type*} {D : Type*} [Category C]
    [Category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (U L : C) (e : F.obj U ≅ F.obj L)
    (h : ∀ q : U ⟶ G.obj (F.obj L), ∃ p : U ⟶ L, p ≫ adj.unit.app L = q) :
    ∃ p : U ⟶ L, IsIso (F.map p) := by
  obtain ⟨p, hp⟩ := h (adj.homEquiv U (F.obj L) e.hom)
  refine ⟨p, ?_⟩
  have he : F.map p = e.hom := by
    apply (adj.homEquiv U (F.obj L)).injective
    simpa only [adj.homEquiv_unit, adj.unit_naturality] using hp
  rw [he]
  infer_instance

/-- In an exact pair whose first map vanishes identically, the second map is injective. -/
private lemma injective_of_exact_of_eq_zero {k A B C : Type*} [Field k]
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
    (u : A →ₗ[k] B) (v : B →ₗ[k] C) (hu : ∀ a, u a = 0) (huv : Function.Exact u v) :
    Function.Injective v := by
  intro x y hxy
  obtain ⟨a, ha⟩ := (huv (x - y)).mp (by rw [map_sub, hxy, sub_self])
  exact sub_eq_zero.mp (((hu a).symm.trans ha).symm)

/-- For a short exact sequence whose second map is surjective on `H⁰`, the first map is injective
on `H¹`. -/
private lemma injective_cohomologyOverFieldMap_one_of_surjective_zero {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (hsurj : Function.Surjective (cohomologyOverFieldMap k f S.g 0)) :
    Function.Injective (cohomologyOverFieldMap k f S.f 1) := by
  obtain ⟨c, -, -, hex₂, hex₃⟩ := exists_cohomologyOverField_longExactSequence k f hS
  refine injective_of_exact_of_eq_zero
    (A := (cohomologyOverField k f S.X₃ 0 : Type u))
    (B := (cohomologyOverField k f S.X₁ 1 : Type u))
    (C := (cohomologyOverField k f S.X₂ 1 : Type u))
    _ _ (fun a => ?_) (hex₃ 0)
  obtain ⟨x, hx⟩ := hsurj a
  exact (hex₂ 0 a).mpr ⟨x, hx⟩

/-- Let `s` be a section of `ℒ` with zero scheme `D`, and `t : 𝒪_X ⟶ ℒ` with `t|_D` an isomorphism.
If `H⁰` of the unit of `i^* ⊣ i_*` at `ℒ` is surjective, then so is `H⁰` of the unit at
`ℒ^{⊗ (n + 1)}` for every `n`. -/
private lemma surjective_cohomologyOverFieldMap_unit_tensorPowSucc {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (t : SheafOfModules.unit X.ringCatSheaf ⟶ L)
    (ht : IsIso ((Scheme.Modules.pullback
      (zeroScheme X L (s.eval (op ⊤))).subschemeι).map t))
    (h : Function.Surjective (cohomologyOverFieldMap k f
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (zeroScheme X L (s.eval (op ⊤))).subschemeι).unit.app L) 0)) (n : ℕ) :
    Function.Surjective (cohomologyOverFieldMap k f
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (zeroScheme X L (s.eval (op ⊤))).subschemeι).unit.app (tensorPowSucc L (n + 1))) 0) := by
  induction n with
  | zero =>
      exact surjective_cohomologyOverFieldMap_unit_of_isIso f
        (zeroScheme X L (s.eval (op ⊤))).subschemeι (λ_ L).inv
        (Functor.map_isIso (Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι)
          (λ_ L).inv) h
  | succ n ih =>
      exact surjective_cohomologyOverFieldMap_unit_of_isIso f
        (zeroScheme X L (s.eval (op ⊤))).subschemeι
        ((ρ_ (tensorPowSucc L (n + 1))).inv ≫ tensorPowSucc L (n + 1) ◁ t)
        (isIso_pullback_tensorSection (zeroScheme X L (s.eval (op ⊤))).subschemeι
          (tensorPowSucc L (n + 1)) L t ht) ih

/-- Let `s` be a regular section of an invertible module `ℒ` with zero scheme `D`, and
`t : 𝒪_X ⟶ ℒ` with `t|_D` an isomorphism, such that `H⁰` of the unit of `i^* ⊣ i_*` at `ℒ` is
surjective. If `H¹(X, ℒ^{⊗ N}) = 0` for some `N`, then `H¹(X, 𝒪_X) = 0`. -/
private lemma subsingleton_cohomologyOverField_one_unit {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hreg : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s)
    (t : SheafOfModules.unit X.ringCatSheaf ⟶ L)
    (ht : IsIso ((Scheme.Modules.pullback
      (zeroScheme X L (s.eval (op ⊤))).subschemeι).map t))
    (h : Function.Surjective (cohomologyOverFieldMap k f
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (zeroScheme X L (s.eval (op ⊤))).subschemeι).unit.app L) 0)) (N : ℕ)
    (hN : IsZero (cohomologyOverField k f (tensorPowSucc L N) 1)) :
    Subsingleton (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) := by
  have hstep : ∀ n : ℕ, Function.Injective (cohomologyOverFieldMap k f
      ((ρ_ (tensorPowSucc L n)).inv ≫ tensorPowSucc L n ◁ L.unitHomEquiv.symm s) 1) := by
    intro n
    obtain ⟨hz, hSE⟩ :=
      shortExact_zeroScheme_twist_of_isRegularSection X L s hreg (tensorPowSucc L n)
    have hSE' : (ShortComplex.mk
        ((ρ_ (tensorPowSucc L n)).inv ≫ tensorPowSucc L n ◁ L.unitHomEquiv.symm s)
        ((Scheme.Modules.pullbackPushforwardAdjunction
          (zeroScheme X L (s.eval (op ⊤))).subschemeι).unit.app
            (tensorPowSucc L n ⊗ L)) hz).ShortExact := hSE
    exact injective_cohomologyOverFieldMap_one_of_surjective_zero f hSE'
      (surjective_cohomologyOverFieldMap_unit_tensorPowSucc f L s t ht h n)
  have key : ∀ n : ℕ, Subsingleton (cohomologyOverField k f (tensorPowSucc L n) 1) →
      Subsingleton (cohomologyOverField k f (tensorPowSucc L 0) 1) := by
    intro n
    induction n with
    | zero => exact id
    | succ n ih =>
        intro hsub
        exact ih ⟨fun a b => hstep n (@Subsingleton.elim _ hsub _ _)⟩
  exact key N (ModuleCat.subsingleton_of_isZero hN)

/-! ### Ampleness of the sheaf of the series -/

/-- If `H⁰` of `φ` is surjective, then `φ` is surjective on global sections. -/
private lemma epi_moduleGlobalSections_map_of_surjective_cohomologyOverFieldMap {k : Type u}
    [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {F G : X.Modules} (φ : F ⟶ G)
    (h : Function.Surjective (cohomologyOverFieldMap k f φ 0)) :
    Epi ((moduleGlobalSections X).map φ) := by
  rw [ModuleCat.epi_iff_surjective]
  intro y
  obtain ⟨p, hp⟩ := exists_comp_eq_of_surjective_cohomologyOverFieldMap f φ h
    (G.unitHomEquiv.symm (Stacks.PresheafOfModules.sectionOfTop G.val y))
  refine ⟨(F.unitHomEquiv p).eval (op ⊤), ?_⟩
  have h1 : SheafOfModules.sectionsMap φ (F.unitHomEquiv p) =
      Stacks.PresheafOfModules.sectionOfTop G.val y := by
    rw [← SheafOfModules.unitHomEquiv_comp_apply p φ, hp, Equiv.apply_symm_apply]
  exact (congrArg (fun z : G.sections => z.eval (op ⊤)) h1).trans
    (Stacks.PresheafOfModules.sectionOfTop_val_top _ _)

/-- Let `i : Z ⟶ X` be a morphism with `i^* ℒ ≅ 𝒪_Z` and `H⁰(X, ℒ) ⟶ H⁰(Z, i^* ℒ)` surjective. Then
`ℒ` has a global section vanishing at no point of the image of `i`. -/
private lemma exists_sections_range_subset_nonvanishingLocus_of_iso_unit {k : Type u} [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) (i : Z ⟶ X) (L : X.Modules)
    (eD : (RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).obj L ≅
      SheafOfModules.unit Z.ringCatSheaf)
    (hsurj : Function.Surjective (cohomologyOverFieldMap k f
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L) 0)) :
    ∃ σ : L.sections, Set.range i.base ⊆
      Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) L σ := by
  have hτ := (Stacks.SheafOfModules.nonvanishingLocus_sectionsMap Z.toRingedSpace eD.symm
      (Stacks.SheafOfModules.unitSections Z.toRingedSpace)).trans
    (Stacks.SheafOfModules.nonvanishingLocus_unitSections Z.toRingedSpace)
  obtain ⟨σ, hσ⟩ := Stacks.Cohomology.AmpleH1.surjective_modulePullbackSection i L
    (epi_moduleGlobalSections_map_of_surjective_cohomologyOverFieldMap f _ hsurj)
    (SheafOfModules.sectionsMap eD.symm.hom
      (Stacks.SheafOfModules.unitSections Z.toRingedSpace))
  refine ⟨σ, ?_⟩
  rintro x ⟨z, rfl⟩
  change z ∈ i.base ⁻¹' Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) L σ
  rw [Stacks.SheafOfModules.preimage_nonvanishingLocus i.toLRSHom L σ, hσ, hτ]
  exact Set.mem_univ z

/-- Let `X` be a proper curve over a field `k` with `H⁰(X, 𝒪_X) = k`, spelled as invertibility of
the canonical map from `k`. If `X` carries a `𝔤^d_d` with `0 < d`, then `X` has genus zero. -/
theorem genus_eq_zero_of_linearSeries_dimension_eq_degree {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    {hdim : topologicalKrullDim X ≤ 1} {d r : ℕ} (series : LinearSeries k f hdim d r)
    (hr : r = d) (hd : 0 < d) :
    genus f = 0 := by
  have hamp : Stacks.Ample.IsInvertibleModule X series.L := series.isInvertible
  have hL' : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property series.L :=
    series.isInvertible
  have hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 series.L :=
    series.isInvertible
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : series.L.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X series.L
  obtain ⟨s, hs⟩ := series.exists_eval_top_ne_zero
  obtain ⟨hfin, hbound, hsurj⟩ :=
    series.finrank_cohomologyOverField_zero_le_succ s hs hL'
  have hVle := Submodule.finrank_le series.V
  rw [series.finrank_eq] at hVle
  have hsurjL := hsurj (by omega)
  have hfinD : IsFinite ((zeroScheme X series.L (s.eval (op ⊤))).subschemeι ≫ f) :=
    isFinite_zeroScheme_of_eval_top_ne_zero k f hdim series.L s hs
  have hLs : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 series.L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL'
  have hinvD := Stacks.Modules.isInvertible_pullback
    (zeroScheme X series.L (s.eval (op ⊤))).subschemeι series.L
  obtain ⟨eD⟩ := nonempty_iso_unit_of_isFinite_over_field
    ((zeroScheme X series.L (s.eval (op ⊤))).subschemeι ≫ f) _ hinvD
  obtain ⟨t, ht⟩ := exists_isIso_map_of_surjective_comp_unit
    (Scheme.Modules.pullbackPushforwardAdjunction
      (zeroScheme X series.L (s.eval (op ⊤))).subschemeι)
    (SheafOfModules.unit X.ringCatSheaf) series.L
    (Scheme.Modules.pullbackUnitIso (zeroScheme X series.L (s.eval (op ⊤))).subschemeι ≪≫
      eD.symm)
    (fun q => exists_comp_eq_of_surjective_cohomologyOverFieldMap f _ hsurjL q)
  have hisAmple : Scheme.Modules.IsAmple X series.L := by
    obtain ⟨σ, hσ⟩ := exists_sections_range_subset_nonvanishingLocus_of_iso_unit f
      (zeroScheme X series.L (s.eval (op ⊤))).subschemeι series.L eD hsurjL
    have hcompl : Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) series.L s =
        (zeroScheme X series.L (s.eval (op ⊤))).supportSetᶜ :=
      nonvanishingLocus_eq_compl_supportSet_zeroScheme series.L s hs
    have hne : Stacks.ProjectiveSpaceSections.nonvanishingChart series.L s ≠ ⊤ := by
      intro htop
      have huniv : Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) series.L s
          = Set.univ := congrArg (fun U : X.Opens => (U : Set X)) htop
      have hiso : IsIso (series.L.unitHomEquiv.symm s) :=
        isIso_unitHomEquiv_symm_of_nonvanishingLocus_eq_univ series.L s huniv
      have hdeg : invertibleCurveDegree k f hdim series.L = 0 :=
        invertibleCurveDegree_eq_zero_of_iso_unit k f hdim series.L
          (@asIso _ _ _ _ (series.L.unitHomEquiv.symm s) hiso).symm
      rw [series.degree_eq] at hdeg
      omega
    refine modulesIsAmple_of_iSup_nonvanishingChart_eq_top f ‹IsProper f› ‹IsCurve k f›
      series.L (n := 1) (fun j => if j = 0 then s else σ) ?_ 0 (by simpa using hne) ?_
    · refine top_unique fun x _ => TopologicalSpace.Opens.mem_iSup.2 ?_
      by_cases hx : x ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) series.L s
      · exact ⟨0, hx⟩
      · refine ⟨1, ?_⟩
        rw [hcompl] at hx
        have hxr : x ∈ Set.range (zeroScheme X series.L (s.eval (op ⊤))).subschemeι.base := by
          rw [Scheme.IdealSheafData.range_subschemeι]
          simpa using hx
        exact hσ hxr
    · change (Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) series.L s).Nonempty
      exact nonempty_nonvanishingLocus_of_eval_top_ne_zero series.L s hs
  obtain ⟨N, hN⟩ :=
    exists_isZero_cohomologyOverField_one_tensorPowSucc_of_isAmple f series.L hisAmple
  have hsub := subsingleton_cohomologyOverField_one_unit f series.L s
    (isRegularSection_of_eval_top_ne_zero series.L s hs) t ht hsurjL N hN
  change Module.finrank k (structureSheafCohomology f 1) = 0
  rw [(structureSheafCohomologyIsoCohomologyOverField k f 1).toLinearEquiv.finrank_eq]
  exact Module.finrank_zero_of_subsingleton

/-! ### The source's statement at `r = d = 0` -/

/-- A proper scheme of dimension at most one over `k` with `H⁰(X, 𝒪_X) = k` carries a `𝔤^0_0`. -/
theorem nonempty_linearSeries_zero_zero {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hdim : topologicalKrullDim X ≤ 1) :
    Nonempty (LinearSeries k f hdim 0 0) :=
  ⟨{ L := SheafOfModules.unit X.ringCatSheaf
     isInvertible := SheafOfModules.isInvertible_unit X.presheaf X.ringCatSheaf.2
     degree_eq := by simpa using invertibleCurveDegree_unit_eq_zero k f hdim
     V := ⊤
     finrank_eq := by
       simpa [finrank_top] using finrank_cohomologyOverField_unit_zero_eq_one f }⟩

/-- On a proper scheme of dimension at most one over `k` with `H⁰(X, 𝒪_X) = k` and nonzero genus,
there is a `𝔤^r_d` with `r = d`. -/
theorem exists_counterexample_to_displayed_statement_of_tag_0CCS_at_zero {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hdim : topologicalKrullDim X ≤ 1) (hg : genus f ≠ 0) :
    ∃ (d r : ℕ) (_ : LinearSeries k f hdim d r), r = d ∧ genus f ≠ 0 :=
  ⟨0, 0, (nonempty_linearSeries_zero_zero f hdim).some, rfl, hg⟩

/-! ### Stacks Tag 0CCS, whole -/

/-- Let `X` be a proper curve over a field `k` with `H⁰(X, 𝒪_X) = k`, spelled as invertibility of
the canonical map from `k`. If `X` has a `𝔤^r_d`, then `r ≤ d`, and if moreover `0 < d` and
`r = d`, then the genus of `X` is zero. -/
@[stacks 0CCS "both assertions, under the source's own hypotheses. Tag 02O6 at the structure \
sheaf, Tag 0B5T clause (4) and the ampleness of `ℒ` that the latter consumes are all proved \
here. `0 < d` is assumed for the equality clause because the source's statement is false \
at `r = d = 0`, \
by `AlgebraicGeometry.exists_counterexample_to_displayed_statement_of_tag_0CCS_at_zero`"]
theorem linearSeries_dimension_le_degree_and_genus_eq_zero {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    {hdim : topologicalKrullDim X ≤ 1} {d r : ℕ} (series : LinearSeries k f hdim d r) :
    r ≤ d ∧ (0 < d → r = d → genus f = 0) :=
  ⟨linearSeries_dimension_le_degree f series,
    fun hd hr => genus_eq_zero_of_linearSeries_dimension_eq_degree f series hr hd⟩

end Twist

end AlgebraicGeometry

end
