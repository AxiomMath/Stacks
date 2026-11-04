module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.SquareZero.Torsor
public import StacksFrontier.Homology.TwoTermComplex.IdealPower
public import StacksFrontier.RingTheory.NaiveCotangent.PresentationHomology
public import StacksFrontier.RingTheory.Support.FiniteDimensional
public import StacksFrontier.Homology.DoubleExtend

/-!
# Finite-dimensionality of `Ext¹(NL_{P/k}, P)` for isolated singularities (Stacks 0DY4)

Let `k` be a field and `P` a `k`-algebra of finite type which is smooth over `k` outside a
finite set of primes. Then the first Ext module `Ext¹_P(NL_{P/k}, P)` of the naive cotangent
complex is a finite-dimensional `k`-vector space.

The proof has two halves. First, `NL_{P/k}` is a two-term object of the derived category of
`P`-modules whose two cohomology modules are `H₁(L_{P/k})` and `Ω[P⁄k]`, both finite over `P`;
so it has a two-term representative with finite degree-minus-one term and finite free
degree-zero term (Stacks 0G9E), and the first Ext module of such a representative sits between
two finite modules in the long exact sequence of the triangle `P₀[0] → NL → P₁[-1]`, hence is
itself a finite `P`-module. Second, on a principal open on which `P` is smooth the first
cohomology vanishes and `Ω` becomes projective, so Stacks 0G9K makes a power of the defining
element annihilate the whole first Ext module; therefore the support of that module is
contained in the non-smooth locus, which is assumed finite. A finite closed set of points of
the spectrum of a Jacobson ring consists of closed points, so the support criterion
`Module.finiteDimensional_iff_support_finite_subset_closedPoints` applies.

## Main results

* `Deformation.Examples.finiteDimensional_naiveCotangentExtOne`: **Stacks 0DY4(2)** for the Ext
  module, the stated finite-dimensionality.
* `Deformation.Examples.finiteDimensional_naiveCotangentExtOne_compHom`: the same statement for
  the restriction of scalars along `algebraMap k P`.

## Implementation notes

Tag 0DY4(2) is stated in the source for the tangent space `T𝓓_P` of the deformation category
of `P`. That tangent space is identified with `Ext¹_P(NL_{P/k}, P)` by **Stacks 0DY3**, so the
finite-dimensionality of the Ext module recorded here is the whole mathematical content of
0DY4(2).

The Ext module is `Stacks.Deformation.naiveCotangentExtOne k P P`, i.e. the object of the
derived category obtained by universe-lifting the naive cotangent complex termwise and reading
its two terms in cohomological degrees `-1` and `0`. The lift is isomorphic to the identity on
a module category of a fixed universe, so the lifted complex is isomorphic to the unlifted one
and the two cohomology computations are performed on the latter, where
`HomologicalComplex.doubleHomologyIsoKernel` and `HomologicalComplex.doubleHomologyIsoCokernel`
apply directly.

`NaiveCotangent.naiveCotangentObject` is the same object of the derived category up to
isomorphism, but spelled as the mapping cone of a map of single complexes and without the
universe lift; the two-term `HomologicalComplex.double` of the lifted differential used here is
the spelling occurring in `Stacks.Deformation.naiveCotangentExtOne`, which is the group being
computed, so that is the spelling the cohomology computations are carried out in.

The `k`-module structure on the Ext module is taken as a hypothesis compatible with the
`P`-action rather than installed as the restriction of scalars along `algebraMap k P`: the two
agree by `Module.ext'`, and the hypothesis form is the one a structure arising in nature
satisfies.

## References

* [Stacks Project, Tag 0DY4](https://stacks.math.columbia.edu/tag/0DY4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w

namespace Deformation.Examples

attribute [local instance] HasDerivedCategory.standard

/-! ### Finiteness of the first Ext module of a two-term object -/

/-- Over a Noetherian ring, a module `N` which receives a finite module `M` onto the kernel of
a map to a finite module `Q` is finite: the kernel is Noetherian because it is contained in the
range of `M → N`, and the quotient by it is a submodule of `Q`. -/
private theorem finite_of_ker_le_range {R : Type*} [CommRing R] [IsNoetherianRing R]
    {M N Q : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup Q] [Module R Q] [Module.Finite R M] [Module.Finite R Q]
    (f : M →ₗ[R] N) (g : N →ₗ[R] Q) (hker : LinearMap.ker g ≤ LinearMap.range f) :
    Module.Finite R N := by
  have : IsNoetherian R (LinearMap.ker g) := isNoetherian_of_le hker
  have : Module.Finite R (N ⧸ LinearMap.ker g) :=
    Module.Finite.equiv g.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker g)

/-- If the two outer vertices of a distinguished triangle have finite modules of maps into `Y`,
so does the middle vertex: the three modules form an exact sequence. -/
private theorem finite_hom_of_distTriang {R : Type w} [CommRing R] [IsNoetherianRing R]
    (Y : DerivedCategory (ModuleCat.{w} R))
    (T : Triangle (DerivedCategory (ModuleCat.{w} R))) (hT : T ∈ distTriang _)
    (h₁ : Module.Finite R (T.obj₁ ⟶ Y)) (h₃ : Module.Finite R (T.obj₃ ⟶ Y)) :
    Module.Finite R (T.obj₂ ⟶ Y) := by
  refine finite_of_ker_le_range (Linear.leftComp R Y T.mor₂)
    (Linear.leftComp R Y T.mor₁) fun x hx => ?_
  obtain ⟨y, hy⟩ := Triangle.yoneda_exact₂ T hT x (LinearMap.mem_ker.mp hx)
  exact LinearMap.mem_range.mpr ⟨y, hy.symm⟩

/-- For finite modules `M` and `N` over a Noetherian ring, the maps in the derived category
from `M` placed in degree `-1` to the shift of `N` placed in degree `0` form a finite module:
shifting by `-1` identifies them with `Hom_R(M, N)`, which is `Ext⁰_R(M, N)`. -/
private theorem finite_hom_single_neg_one {R : Type w} [CommRing R] [IsNoetherianRing R]
    (M N : ModuleCat.{w} R) [Module.Finite R M] [Module.Finite R N] :
    Module.Finite R (((DerivedCategory.singleFunctor (ModuleCat.{w} R) (-1)).obj M) ⟶
      (((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj N)⟦(1 : ℤ)⟧)) := by
  let C := DerivedCategory (ModuleCat.{w} R)
  let A := (DerivedCategory.singleFunctor (ModuleCat.{w} R) (-1)).obj M
  let B := ((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj N)⟦(1 : ℤ)⟧
  let F := shiftFunctor C (-1 : ℤ)
  let hF := Functor.FullyFaithful.ofFullyFaithful F
  let eF : (A ⟶ B) ≃ₗ[R] (F.obj A ⟶ F.obj B) :=
    { toFun := F.map
      invFun := hF.homEquiv.symm
      left_inv := hF.preimage_map
      right_inv := hF.map_preimage
      map_add' := fun f g => Functor.map_add F
      map_smul' := fun r f => Functor.map_smul F r f }
  let eA : F.obj A ≅ (DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj M :=
    ((DerivedCategory.singleFunctors (ModuleCat.{w} R)).shiftIso
      (-1 : ℤ) 0 (-1 : ℤ) (by omega)).app M
  let eB : F.obj B ≅ (DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj N :=
    (shiftFunctorCompIsoId C 1 (-1 : ℤ) (by omega)).app
      ((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj N)
  have h : Module.Finite R
      (((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj M) ⟶
        ((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj N)) := by
    have hShift : Module.Finite R (ShiftedHom
        ((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj M)
        ((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj N) (0 : ℤ)) :=
      Module.Finite.equiv
        (Abelian.Ext.homLinearEquiv (R := R) (X := M) (Y := N) (n := 0))
    let e₀ : (((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj M) ⟶
        ((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj N)) ≃ₗ[R]
        ShiftedHom ((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj M)
          ((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj N) (0 : ℤ) :=
      { toFun := ShiftedHom.homEquiv (0 : ℤ) rfl
        invFun := (ShiftedHom.homEquiv (0 : ℤ) rfl).symm
        left_inv := (ShiftedHom.homEquiv (0 : ℤ) rfl).left_inv
        right_inv := (ShiftedHom.homEquiv (0 : ℤ) rfl).right_inv
        map_add' := fun f g => by simp [ShiftedHom.homEquiv]
        map_smul' := fun r f => by simp [ShiftedHom.homEquiv] }
    exact Module.Finite.equiv e₀.symm
  exact Module.Finite.equiv (eF.trans (Linear.homCongr R eA eB)).symm

/-- The two-term complex of a module map sits in a short exact sequence between its degree-`0`
term and its degree-minus-one term, each placed in a single degree. -/
private theorem shortExact_single_double {R : Type*} [CommRing R] {X₁ X₀ : ModuleCat R}
    (d : X₁ ⟶ X₀) :
    let K := HomologicalComplex.double d (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)
    ∃ (i : (CochainComplex.singleFunctor (ModuleCat R) 0).obj X₀ ⟶ K)
      (p : K ⟶ (CochainComplex.singleFunctor (ModuleCat R) (-1)).obj X₁)
      (h : i ≫ p = 0), (ShortComplex.mk i p h).ShortExact := by
  classical
  intro K
  let hd : (ComplexShape.up ℤ).Rel (-1) 0 := rfl
  let i : (CochainComplex.singleFunctor (ModuleCat R) 0).obj X₀ ⟶ K :=
    HomologicalComplex.mkHomFromSingle (HomologicalComplex.doubleXIso₁ d hd (by omega)).inv
      fun k hk => by
        rw [HomologicalComplex.double_d_eq_zero₀ d hd 0 k (by omega), Limits.comp_zero]
  let p : K ⟶ (CochainComplex.singleFunctor (ModuleCat R) (-1)).obj X₁ :=
    HomologicalComplex.mkHomToSingle (HomologicalComplex.doubleXIso₀ d hd).hom
      fun j hj => by
        rw [HomologicalComplex.double_d_eq_zero₁ d hd j (-1) (by omega), Limits.zero_comp]
  have hi : IsIso (i.f 0) := by
    rw [show i.f 0 = _ from HomologicalComplex.mkHomFromSingle_f _ _]
    infer_instance
  have hp : IsIso (p.f (-1)) := by
    rw [show p.f (-1) = _ from HomologicalComplex.mkHomToSingle_f _ _]
    infer_instance
  have hip : i ≫ p = 0 := by
    apply HomologicalComplex.from_single_hom_ext
    exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (-1) X₁ 0
      (by omega)).eq_of_tgt _ _
  refine ⟨i, p, hip, HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => ?_⟩
  let S := (ShortComplex.mk i p hip).map (HomologicalComplex.eval (ModuleCat R) _ n)
  change S.ShortExact
  have hm : Mono S.f := by
    rcases eq_or_ne n 0 with rfl | hn
    · exact inferInstanceAs (Mono (i.f 0))
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 X₀ n hn).mono _
  have he : Epi S.g := by
    rcases eq_or_ne n (-1) with rfl | hn
    · exact inferInstanceAs (Epi (p.f (-1)))
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (-1) X₁ n hn).epi _
  refine { exact := ?_, mono_f := hm, epi_g := he }
  rcases eq_or_ne n 0 with rfl | hn
  · rw [ShortComplex.moduleCat_exact_iff]
    exact fun x _ => (ModuleCat.epi_iff_surjective (i.f 0)).1 inferInstance x
  · rcases eq_or_ne n (-1) with rfl | hn'
    · rw [ShortComplex.moduleCat_exact_iff]
      exact fun x hx => ⟨0, (map_zero _).trans ((ModuleCat.mono_iff_injective (p.f (-1))).1
        inferInstance (hx.trans (map_zero _).symm)).symm⟩
    · exact S.exact_of_isZero_X₂ (HomologicalComplex.isZero_double_X d hd n hn' hn)

/-- There are no nonzero first Ext classes out of a projective module, so the maps from a
projective module placed in degree `0` to the shift of any module placed in degree `0` all
agree. -/
private theorem subsingleton_hom_single_shift_of_projective {R : Type w} [CommRing R]
    (M N : ModuleCat.{w} R) [Module.Projective R M] :
    Subsingleton (((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj M) ⟶
      (((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj N)⟦(1 : ℤ)⟧)) := by
  have hs : Subsingleton (Abelian.Ext M N 1) :=
    Abelian.Ext.subsingleton_of_projective M N 0
  change Subsingleton (ShiftedHom
    ((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj M)
    ((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj N) (1 : ℤ))
  exact ⟨fun x y =>
    (Abelian.Ext.homLinearEquiv (R := R) (X := M) (Y := N) (n := 1)).symm.injective
      (Subsingleton.elim _ _)⟩

/-- The first Ext module of the two-term complex of a map from a finite module to a projective
module, with coefficients in a finite module, is finite over a Noetherian ring. -/
private theorem finite_ext_one_double {R : Type w} [CommRing R] [IsNoetherianRing R]
    (M₁ M₀ N : ModuleCat.{w} R)
    [Module.Finite R M₁] [Module.Finite R N] [Module.Projective R M₀] (d : M₁ ⟶ M₀) :
    Module.Finite R
      (DerivedCategory.Ext (DerivedCategory.Q.obj (HomologicalComplex.double d
          (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)))
        ((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj N) 1) := by
  obtain ⟨i, p, hip, hS⟩ := shortExact_single_double d
  let T := DerivedCategory.triangleOfSES hS
  let Y := ((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj N)⟦(1 : ℤ)⟧
  have : Subsingleton (T.obj₁ ⟶ Y) := subsingleton_hom_single_shift_of_projective M₀ N
  exact finite_hom_of_distTriang Y T (DerivedCategory.triangleOfSES_distinguished hS)
    Module.Finite.of_finite (finite_hom_single_neg_one M₁ N)

/-- A two-term cochain complex is the two-term complex of its only differential. -/
private def doubleIsoOfTwoTerm {R : Type w} [CommRing R] (C : CochainComplex (ModuleCat.{w} R) ℤ)
    [C.IsStrictlyGE (-1)] [C.IsStrictlyLE 0] :
    HomologicalComplex.double (C.d (-1) 0)
      (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl) ≅ C :=
  HomologicalComplex.doubleIsoOfIsZero (C.d (-1) 0) rfl (by decide) C (Iso.refl _) (Iso.refl _)
    (by simp)
    (fun j hj => by
      have hj' : j = 1 := by
        change (0 : ℤ) + 1 = j at hj
        omega
      subst j
      exact (C.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt _ _)
    (fun j hj₀ hj₁ => by
      rcases lt_or_gt_of_ne hj₁ with h | h
      · exact C.isZero_of_isStrictlyGE (-1) j (by omega)
      · exact C.isZero_of_isStrictlyLE 0 j h)

/-- **Stacks 0G9E** makes the first Ext module of a two-term derived object with finite
cohomology into a finite module: a two-term representative with finite degree-minus-one term
and finite free degree-zero term computes it. -/
private theorem finite_ext_one_of_twoTerm {R : Type w} [CommRing R] [IsNoetherianRing R]
    (K : DerivedCategory (ModuleCat.{w} R))
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).obj K))
    [Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) (-1)).obj K)]
    [Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) 0).obj K)]
    (N : ModuleCat.{w} R) [Module.Finite R N] :
    Module.Finite R (DerivedCategory.Ext K
      ((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj N) 1) := by
  obtain ⟨L, hge, hle, h₁, h₀, hfree, ⟨e⟩⟩ :=
    (TwoTermComplex.exists_twoTerm_representative_free_zero_and_finite K hK).2
      inferInstance inferInstance inferInstance
  have := finite_ext_one_double (L.X (-1)) (L.X 0) N (L.d (-1) 0)
  exact Module.Finite.equiv (Linear.homCongr R
    (DerivedCategory.Q.mapIso (doubleIsoOfTwoTerm L) ≪≫ e) (Iso.refl _))

/-! ### The naive cotangent complex as a two-term object -/

/-- The differential of the naive cotangent complex of `P` over `k`, the conormal map
`I/I² → Ω_{k[P]/k} ⊗ P` of the canonical presentation. -/
private abbrev cotangentDifferential (k P : Type w) [CommRing k] [CommRing P] [Algebra k P] :
    ModuleCat.of P (Algebra.Generators.self k P).toExtension.Cotangent ⟶
      ModuleCat.of P (Algebra.Generators.self k P).toExtension.CotangentSpace :=
  ModuleCat.ofHom (Algebra.Generators.self k P).toExtension.cotangentComplex

/-- Degree `1` of the naive cotangent complex is the conormal module `I/I²`. -/
private def naiveCotangentXOneIso (k P : Type w) [CommRing k] [CommRing P] [Algebra k P] :
    (Algebra.naiveCotangentComplex k P).X 1 ≅
      ModuleCat.of P (Algebra.Generators.self k P).toExtension.Cotangent :=
  HomologicalComplex.doubleXIso₀ (cotangentDifferential k P) ComplexShape.downNatRelOneZero

/-- Degree `0` of the naive cotangent complex is `Ω_{k[P]/k} ⊗ P`. -/
private def naiveCotangentXZeroIso (k P : Type w) [CommRing k] [CommRing P] [Algebra k P] :
    (Algebra.naiveCotangentComplex k P).X 0 ≅
      ModuleCat.of P (Algebra.Generators.self k P).toExtension.CotangentSpace :=
  HomologicalComplex.doubleXIso₁ (cotangentDifferential k P) ComplexShape.downNatRelOneZero
    (by omega)

/-- The only differential of the naive cotangent complex is the conormal map, read through the
identifications of its two terms. -/
private theorem naiveCotangentComplex_d (k P : Type w) [CommRing k] [CommRing P] [Algebra k P] :
    (Algebra.naiveCotangentComplex k P).d 1 0 =
      (naiveCotangentXOneIso k P).hom ≫ cotangentDifferential k P ≫
        (naiveCotangentXZeroIso k P).inv :=
  HomologicalComplex.double_d _ _ (by omega)

/-- Lifting modules into their own universe is isomorphic to the identity functor. -/
private def uliftFunctorIsoId (P : Type w) [Ring P] :
    ModuleCat.uliftFunctor.{w, w} P ≅ 𝟭 (ModuleCat.{w} P) :=
  NatIso.ofComponents (fun _ => ULift.moduleEquiv.toModuleIso) (fun _ => by ext; rfl)

/-- The universe-lifted naive cotangent complex, as it appears in
`Stacks.Deformation.naiveCotangentExtOne`, is isomorphic to the naive cotangent complex
itself. -/
private def liftedNaiveCotangentComplexIso (k P : Type w) [CommRing k] [CommRing P]
    [Algebra k P] :
    ((ModuleCat.uliftFunctor.{w} P).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (Algebra.naiveCotangentComplex k P) ≅ Algebra.naiveCotangentComplex k P :=
  (NatIso.mapHomologicalComplex (uliftFunctorIsoId P) (ComplexShape.down ℕ)).app _ ≪≫
    (Functor.mapHomologicalComplexIdIso (ModuleCat.{w} P) (ComplexShape.down ℕ)).app _

/-- The naive cotangent complex `NL_{P/k}`, universe-lifted termwise and read as a cochain
complex in degrees `-1` and `0`. This is the complex whose first Ext module is
`Stacks.Deformation.naiveCotangentExtOne k P P`. -/
private abbrev liftedNaiveCotangentDouble (k P : Type w) [CommRing k] [CommRing P] [Algebra k P] :
    CochainComplex (ModuleCat.{w} P) ℤ :=
  HomologicalComplex.double
    ((((ModuleCat.uliftFunctor.{w} P).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Algebra.naiveCotangentComplex k P)).d 1 0)
    (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)

/-- The object of the derived category of `P`-modules represented by the naive cotangent
complex of `P` over `k`. -/
private abbrev liftedNaiveCotangentObject (k P : Type w) [CommRing k] [CommRing P] [Algebra k P] :
    DerivedCategory (ModuleCat.{w} P) :=
  DerivedCategory.Q.obj (liftedNaiveCotangentDouble k P)

/-- The two-term cochain complex of the universe-lifted naive cotangent complex is isomorphic
to the two-term complex of the conormal map itself. -/
private def liftedNaiveCotangentDoubleIso (k P : Type w) [CommRing k] [CommRing P] [Algebra k P] :
    liftedNaiveCotangentDouble k P ≅
      HomologicalComplex.double (cotangentDifferential k P)
        (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl) :=
  Stacks.Deformation.doubleIsoOfSquare _ ((Algebra.naiveCotangentComplex k P).d 1 0)
      ((HomologicalComplex.eval (ModuleCat.{w} P) (ComplexShape.down ℕ) 1).mapIso
        (liftedNaiveCotangentComplexIso k P))
      ((HomologicalComplex.eval (ModuleCat.{w} P) (ComplexShape.down ℕ) 0).mapIso
        (liftedNaiveCotangentComplexIso k P))
      ((liftedNaiveCotangentComplexIso k P).hom.comm 1 0) ≪≫
    Stacks.Deformation.doubleIsoOfSquare _ (cotangentDifferential k P)
      (naiveCotangentXOneIso k P) (naiveCotangentXZeroIso k P)
      (by rw [naiveCotangentComplex_d]; simp)

/-- The naive cotangent complex has no cohomology outside degrees `-1` and `0`. -/
private theorem isZero_homology_liftedNaiveCotangentObject (k P : Type w) [CommRing k] [CommRing P]
    [Algebra k P] (i : ℤ) (hi : i ≠ -1) (hi' : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} P) i).obj
      (liftedNaiveCotangentObject k P)) :=
  IsZero.of_iso
    ((HomologicalComplex.ExactAt.of_isZero
      (HomologicalComplex.isZero_double_X _ _ i hi hi')).isZero_homology)
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{w} P) i).app _)

/-- The degree-minus-one cohomology of the naive cotangent complex is `H₁(L_{P/k})`. -/
private def homologyNegOneLinearEquiv (k P : Type w) [CommRing k] [CommRing P] [Algebra k P] :
    ((DerivedCategory.homologyFunctor (ModuleCat.{w} P) (-1)).obj
      (liftedNaiveCotangentObject k P)) ≃ₗ[P] Algebra.H1Cotangent k P :=
  (((DerivedCategory.homologyFunctorFactors (ModuleCat.{w} P) (-1)).app
        (liftedNaiveCotangentDouble k P) ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{w} P) (ComplexShape.up ℤ) (-1)).mapIso
        (liftedNaiveCotangentDoubleIso k P) ≪≫
      HomologicalComplex.doubleHomologyIsoKernel (cotangentDifferential k P) rfl
        (by decide) ≪≫
      ModuleCat.kernelIsoKer (cotangentDifferential k P)).toLinearEquiv).trans
    ((Algebra.Extension.h1CotangentEquivKer _).symm.trans
      (Algebra.Generators.self k P).equivH1Cotangent)

/-- The degree-zero cohomology of the naive cotangent complex is `Ω[P⁄k]`. -/
private def homologyZeroLinearEquiv (k P : Type w) [CommRing k] [CommRing P] [Algebra k P] :
    ((DerivedCategory.homologyFunctor (ModuleCat.{w} P) 0).obj
      (liftedNaiveCotangentObject k P)) ≃ₗ[P] Ω[P⁄k] :=
  (((DerivedCategory.homologyFunctorFactors (ModuleCat.{w} P) 0).app
        (liftedNaiveCotangentDouble k P) ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{w} P) (ComplexShape.up ℤ) 0).mapIso
        (liftedNaiveCotangentDoubleIso k P) ≪≫
      HomologicalComplex.doubleHomologyIsoCokernel (cotangentDifferential k P) rfl
        (by decide) ≪≫
      ModuleCat.cokernelIsoRangeQuotient (cotangentDifferential k P)).toLinearEquiv).trans
    (Algebra.Extension.quotRangeCotangentComplexEquivKaehler _)

/-- `H₁(L_{P/k})` is a finite `P`-module for `P` of finite presentation over `k`: it is a
submodule of the conormal module of a finite presentation. -/
private theorem finite_h1Cotangent (k P : Type w) [CommRing k] [CommRing P] [Algebra k P]
    [IsNoetherianRing P] [Algebra.FinitePresentation k P] :
    Module.Finite P (Algebra.H1Cotangent k P) := by
  let A := Algebra.Presentation.ofFinitePresentation k P
  have : Module.Finite P A.toExtension.Cotangent := Algebra.Extension.Cotangent.finite A.fg_ker
  have : Module.Finite P A.toExtension.H1Cotangent :=
    Module.Finite.of_injective A.toExtension.h1Cotangentι Subtype.val_injective
  exact Module.Finite.equiv A.equivH1Cotangent

/-- Both cohomology modules of the naive cotangent complex are finite for `P` of finite
presentation over `k`. -/
private theorem finite_homology_liftedNaiveCotangentObject (k P : Type w) [CommRing k] [CommRing P]
    [Algebra k P] [IsNoetherianRing P] [Algebra.FinitePresentation k P] :
    Module.Finite P ((DerivedCategory.homologyFunctor (ModuleCat.{w} P) (-1)).obj
        (liftedNaiveCotangentObject k P)) ∧
      Module.Finite P ((DerivedCategory.homologyFunctor (ModuleCat.{w} P) 0).obj
        (liftedNaiveCotangentObject k P)) := by
  have := finite_h1Cotangent k P
  exact ⟨Module.Finite.equiv (homologyNegOneLinearEquiv k P).symm,
    Module.Finite.equiv (homologyZeroLinearEquiv k P).symm⟩

/-! ### Annihilation of the first Ext module away from the non-smooth locus -/

/-- **Stacks 0G9K** for a single element: if a power of `f` annihilates the degree-minus-one
cohomology of a two-term derived object and its degree-zero cohomology becomes projective after
inverting `f`, then a power of `f` annihilates every first Ext module of the object. -/
private theorem exists_pow_smul_ext_one_eq_zero {R : Type w} [CommRing R] [IsNoetherianRing R]
    (K : DerivedCategory (ModuleCat.{w} R))
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).obj K))
    [Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) (-1)).obj K)]
    [Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) 0).obj K)]
    (f : R)
    (ht : IsIPowerTorsion R
      ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) (-1)).obj K) (Ideal.span {f}))
    (hp : Module.Projective (Localization.Away f) (LocalizedModule.Away f
      ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) 0).obj K))) :
    ∃ n : ℕ, ∀ (N : ModuleCat.{w} R) (ξ : DerivedCategory.Ext K
      ((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj N) 1), f ^ n • ξ = 0 := by
  have hall := (TwoTermComplex.exists_power_ext_one_annihilated_iff_cohomology_conditions
    (Ideal.span {f}) K hK).2 inferInstance inferInstance inferInstance
  obtain ⟨n, hn⟩ := hall.1.mpr (hall.2.1.mpr
    ⟨ht, 1, fun _ => f, by rw [Set.range_const], fun _ => hp⟩)
  exact ⟨n, fun N ξ => hn N (f ^ n) (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self f) n) ξ⟩

/-- On a principal open on which `P` is smooth over `k`, a power of the defining element
annihilates every first Ext module of the naive cotangent complex: there the degree-minus-one
cohomology vanishes and the module of differentials is projective. -/
private theorem exists_pow_smul_ext_one_eq_zero_of_smooth (k P : Type w) [CommRing k]
    [CommRing P] [Algebra k P] [IsNoetherianRing P] [Algebra.FinitePresentation k P] (f : P)
    (hf : Algebra.Smooth k (Localization.Away f)) :
    ∃ n : ℕ, ∀ (N : ModuleCat.{w} P) (ξ : DerivedCategory.Ext (liftedNaiveCotangentObject k P)
      ((DerivedCategory.singleFunctor (ModuleCat.{w} P) 0).obj N) 1), f ^ n • ξ = 0 := by
  obtain ⟨_, _⟩ := finite_homology_liftedNaiveCotangentObject k P
  have := finite_h1Cotangent k P
  have hs : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum P)) ⊆
      (Module.support P (Algebra.H1Cotangent k P))ᶜ ∩ Module.freeLocus P Ω[P⁄k] := by
    rw [← Algebra.smoothLocus_eq_compl_support_inter]
    exact Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hf
  have ht : IsIPowerTorsion P
      ((DerivedCategory.homologyFunctor (ModuleCat.{w} P) (-1)).obj
        (liftedNaiveCotangentObject k P)) (Ideal.span {f}) := by
    apply isIPowerTorsion_of_support_subset (Submodule.fg_span_singleton f)
    rw [(homologyNegOneLinearEquiv k P).support_eq]
    intro q hq
    change Ideal.span {f} ≤ q.asIdeal
    rw [Ideal.span_singleton_le_iff_mem]
    by_contra h
    exact (hs (show q ∈ PrimeSpectrum.basicOpen f from h)).1 hq
  have hp : Module.Projective (Localization.Away f) (LocalizedModule.Away f
      ((DerivedCategory.homologyFunctor (ModuleCat.{w} P) 0).obj
        (liftedNaiveCotangentObject k P))) := by
    have hfree : Module.Projective (Localization.Away f)
        (LocalizedModule.Away f Ω[P⁄k]) :=
      Module.basicOpen_subset_freeLocus_iff.mp fun q hq => (hs hq).2
    exact Module.Projective.of_equiv (IsLocalizedModule.mapEquiv (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) _)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) Ω[P⁄k]) (Localization.Away f)
      (homologyZeroLinearEquiv k P)).symm
  exact exists_pow_smul_ext_one_eq_zero (liftedNaiveCotangentObject k P)
    (isZero_homology_liftedNaiveCotangentObject k P) f ht hp

/-- A finite closed set of points of a Jacobson space consists of closed points: the subspace
is discrete, so each of its points is closed in it, hence closed in the ambient space. -/
private theorem subset_closedPoints_of_finite_of_isClosed {X : Type*} [TopologicalSpace X]
    [JacobsonSpace X] {s : Set X} (hs : s.Finite) (hc : IsClosed s) : s ⊆ closedPoints X := by
  classical
  let := hs.fintype
  have : JacobsonSpace s := JacobsonSpace.of_isClosedEmbedding hc.isClosedEmbedding_subtypeVal
  intro x hx
  apply mem_closedPoints_iff.mpr
  simpa only [Set.image_singleton] using
    hc.isClosedEmbedding_subtypeVal.isClosedMap {⟨x, hx⟩}
      (isClosed_discrete _ : IsClosed ({⟨x, hx⟩} : Set s))

/-- For `P` of finite type over a field `k` and a finite `P`-module `N`, the first Ext module of
the naive cotangent complex with coefficients in `N` is a finite `P`-module. -/
private theorem finite_ext_one_liftedNaiveCotangentObject (k P : Type w) [Field k] [CommRing P]
    [Algebra k P] [Algebra.FiniteType k P] (N : ModuleCat.{w} P) [Module.Finite P N] :
    Module.Finite P (DerivedCategory.Ext (liftedNaiveCotangentObject k P)
      ((DerivedCategory.singleFunctor (ModuleCat.{w} P) 0).obj N) 1) := by
  have : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
  have : Algebra.FinitePresentation k P :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨_, _⟩ := finite_homology_liftedNaiveCotangentObject k P
  exact finite_ext_one_of_twoTerm (liftedNaiveCotangentObject k P)
    (isZero_homology_liftedNaiveCotangentObject k P) N

/-- The support of a first Ext module of the naive cotangent complex is contained in the
non-smooth locus of `P` over `k`. -/
private theorem support_ext_one_subset (k P : Type w) [Field k] [CommRing P] [Algebra k P]
    [Algebra.FiniteType k P] (N : ModuleCat.{w} P) [Module.Finite P N] :
    Module.support P (DerivedCategory.Ext (liftedNaiveCotangentObject k P)
        ((DerivedCategory.singleFunctor (ModuleCat.{w} P) 0).obj N) 1) ⊆
      {q : PrimeSpectrum P | ¬ Algebra.IsSmoothAt k q.asIdeal} := by
  have := finite_ext_one_liftedNaiveCotangentObject k P N
  have : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
  have : Algebra.FinitePresentation k P :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  intro q hq _
  obtain ⟨f, hf, hfs⟩ := Algebra.IsSmoothAt.exists_notMem_smooth k q.asIdeal
  obtain ⟨n, hn⟩ := exists_pow_smul_ext_one_eq_zero_of_smooth k P f hfs
  rw [Module.support_eq_zeroLocus] at hq
  exact (q.asIdeal.primeCompl.pow_mem hf n) (hq (Module.mem_annihilator.mpr (hn N)))

/-! ### Finite-dimensionality over the base field -/

/-- **Stacks 0DY4(2)** for the Ext module. Let `k` be a field and `P` a `k`-algebra of finite
type which is smooth over `k` outside a finite set of primes. Then the first Ext module
`Ext¹_P(NL_{P/k}, P)` of the naive cotangent complex is finite-dimensional over `k`, for any
`k`-module structure on it compatible with the `P`-action. Through the identification of that
Ext module with the tangent space `T𝓓_P` of the deformation category of `P`, which is Tag
0DY3, this is the finite-dimensionality of the tangent space. -/
@[stacks 0DY4 "part (2) for the Ext group", sga "7 VI 4.14" "more general"]
theorem finiteDimensional_naiveCotangentExtOne (k P : Type w) [Field k] [CommRing P]
    [Algebra k P] [Algebra.FiniteType k P]
    [Module k (Stacks.Deformation.naiveCotangentExtOne k P P)]
    [IsScalarTower k P (Stacks.Deformation.naiveCotangentExtOne k P P)]
    (hfinite : {q : PrimeSpectrum P | ¬ Algebra.IsSmoothAt k q.asIdeal}.Finite) :
    FiniteDimensional k (Stacks.Deformation.naiveCotangentExtOne k P P) := by
  have : IsJacobsonRing P := isJacobsonRing_of_finiteType (A := k)
  have hN : Module.Finite P ((ModuleCat.uliftFunctor.{w} P).obj (ModuleCat.of P P)) :=
    Module.Finite.equiv (ULift.moduleEquiv (R := P) (M := P)).symm
  have hfin : Module.Finite P (Stacks.Deformation.naiveCotangentExtOne k P P) :=
    finite_ext_one_liftedNaiveCotangentObject k P
      ((ModuleCat.uliftFunctor.{w} P).obj (ModuleCat.of P P))
  have hsupp := hfinite.subset
    (support_ext_one_subset k P ((ModuleCat.uliftFunctor.{w} P).obj (ModuleCat.of P P)))
  exact (Module.finiteDimensional_iff_support_finite_subset_closedPoints k P
      (Stacks.Deformation.naiveCotangentExtOne k P P)).mpr
    ⟨hsupp, subset_closedPoints_of_finite_of_isClosed hsupp Module.isClosed_support⟩

/-- **Stacks 0DY4(2)** for the Ext module, for the restriction of scalars along
`algebraMap k P`. This is `Deformation.Examples.finiteDimensional_naiveCotangentExtOne` for the
canonical `k`-module structure on the Ext module, which in particular exhibits a structure
satisfying the scalar-tower hypothesis of that statement. -/
theorem finiteDimensional_naiveCotangentExtOne_compHom (k P : Type w) [Field k] [CommRing P]
    [Algebra k P] [Algebra.FiniteType k P]
    (hfinite : {q : PrimeSpectrum P | ¬ Algebra.IsSmoothAt k q.asIdeal}.Finite) :
    letI : Module k (Stacks.Deformation.naiveCotangentExtOne k P P) :=
      Module.compHom _ (algebraMap k P)
    FiniteDimensional k (Stacks.Deformation.naiveCotangentExtOne k P P) := by
  let : Module k (Stacks.Deformation.naiveCotangentExtOne k P P) :=
    Module.compHom _ (algebraMap k P)
  have : IsScalarTower k P (Stacks.Deformation.naiveCotangentExtOne k P P) :=
    ⟨fun a b x => by
      rw [Algebra.smul_def]
      exact mul_smul (algebraMap k P a) b x⟩
  exact finiteDimensional_naiveCotangentExtOne k P hfinite

end Deformation.Examples

end
