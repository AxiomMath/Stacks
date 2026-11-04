module

public import StacksFrontier.RingTheory.Tor.LongExactSequence
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# The six term `Tor₁`-tensor exact sequence of a short exact sequence

Let `R` be a commutative ring, let `M` be an `R`-module and let `0 → N' → N → N'' → 0` be a short
exact sequence of `R`-modules. There is an exact sequence

  `Tor₁(M, N') → Tor₁(M, N) → Tor₁(M, N'') → M ⊗ N' → M ⊗ N → M ⊗ N'' → 0`

whose first two and last three maps are the functorial ones induced by `N' → N` and `N → N''`,
and whose middle map is a connecting homomorphism. Here `Tor₁(M, N)` is the first homology of
`P_• ⊗ N` for a projective resolution `P_•` of `M`, that is
`((CategoryTheory.Tor' (ModuleCat R) 1).obj M).obj N`.

Since each `P_n` is projective, hence flat, `0 → P_• ⊗ N' → P_• ⊗ N → P_• ⊗ N'' → 0` is a short
exact sequence of chain complexes. Its homology sequence in degrees `1` and `0` is the six term
sequence, once `H_n(P_• ⊗ N)` is identified with `Tor_n(M, N)`: in degree `1` this is the
definition of the left derived functor of `- ⊗ N`, and in degree `0` it is the right exactness of
`- ⊗ N`. The argument is carried out for an arbitrary short exact sequence of additive, right
exact functors which stays short exact on each term of a projective resolution.

## Main definitions

* `Stacks.Tor.SixTermSequence.homologyZeroIso`: for a right exact additive functor `F` and a
  projective resolution `P` of `M`, the isomorphism `H_0(F(P_•)) ≅ F(M)`.

## Main results

* `Stacks.Tor.SixTermSequence.homologyMap_comp_fromLeftDerivedZero'`: the canonical map
  `H_0(F(P_•)) ⟶ F(M)` is natural in the functor `F`.
* `Stacks.Tor.SixTermSequence.solution`,
  `CategoryTheory.ShortComplex.ShortExact.exists_Tor'_one_composableArrows_exact_and_epi`: the
  exact sequence above, for a short exact sequence in `ModuleCat R`.

## Implementation notes

The long exact sequence is a `ComposableArrows (ModuleCat R) 5` which is `Exact`, that is, exact
at its four interior terms; the final `→ 0`, the surjectivity of `M ⊗ N → M ⊗ N''`, is the
second conjunct `Epi (M ◁ S.g)`. The connecting homomorphism is existentially quantified, and
the other five maps are the functorial ones.

## References

* [Stacks Project, Tag 00M0](https://stacks.math.columbia.edu/tag/00M0)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

namespace Stacks.Tor.SixTermSequence

section LeftDerived

variable {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D] [Abelian D]

/-- Naturality in the *functor* variable of the canonical map
`H_0((F.mapHomologicalComplex _).obj P.complex) ⟶ F.obj X` attached to a projective resolution
`P` of `X`, that is, of `ProjectiveResolution.fromLeftDerivedZero'` read on homology rather than
on opcycles. -/
lemma homologyMap_comp_fromLeftDerivedZero' {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ⟶ G) {X : C} (P : ProjectiveResolution X) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 ≫
      (ChainComplex.isoHomologyι₀ ((G.mapHomologicalComplex _).obj P.complex)).hom ≫
        P.fromLeftDerivedZero' G =
      (ChainComplex.isoHomologyι₀ ((F.mapHomologicalComplex _).obj P.complex)).hom ≫
        P.fromLeftDerivedZero' F ≫ α.app X := by
  simp only [HomologicalComplex.isoHomologyι_hom, HomologicalComplex.homologyι_naturality_assoc]
  congr 1
  simp only [← cancel_epi (HomologicalComplex.pOpcycles _ 0),
    HomologicalComplex.p_opcyclesMap_assoc,
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero',
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero'_assoc]
  exact (α.naturality (P.π.f 0)).symm

variable [HasProjectiveResolutions C]

/-- For a right exact additive functor `F` and a projective resolution `P` of `M`, the
identification `H_0((F.mapHomologicalComplex _).obj P.complex) ≅ F.obj M`: the degree `0` homology
computes the zeroth left derived functor, which for a right exact `F` is `F` itself. -/
noncomputable def homologyZeroIso (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    {M : C} (P : ProjectiveResolution M) :
    (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) 0).obj
        ((F.mapHomologicalComplex _).obj P.complex) ≅ F.obj M :=
  (P.isoLeftDerivedObj F 0).symm ≪≫ F.leftDerivedZeroIsoSelf.app M

/-- Naturality in the *functor* variable of `homologyZeroIso`. -/
lemma homologyFunctor_map_comp_homologyZeroIso_hom {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteColimits F] [PreservesFiniteColimits G]
    (α : F ⟶ G) {M : C} (P : ProjectiveResolution M) :
    (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) 0).map
        ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) ≫
        (homologyZeroIso G P).hom = (homologyZeroIso F P).hom ≫ α.app M := by
  simp only [homologyZeroIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.leftDerivedZeroIsoSelf_hom, P.fromLeftDerivedZero_eq, Iso.inv_hom_id_assoc]
  exact (homologyMap_comp_fromLeftDerivedZero' α P).trans (Category.assoc _ _ _).symm

open ComposableArrows in
/-- The six term exact sequence attached to a short exact sequence `T` of additive right exact
functors `C ⥤ D` and an object `M` of `C` with projective resolution `P`, on the assumption that
`T` stays short exact after evaluation at each `P_n`. It is the homology sequence in degrees `1`
and `0` of the short exact sequence of chain complexes `T(P_•)`. -/
private lemma exists_δ_composableArrows_mk₅_exact (T : ShortComplex (C ⥤ D))
    [T.X₁.Additive] [T.X₂.Additive] [T.X₃.Additive]
    [PreservesFiniteColimits T.X₁] [PreservesFiniteColimits T.X₂] [PreservesFiniteColimits T.X₃]
    {M : C} (P : ProjectiveResolution M)
    (hT : ∀ n : ℕ, (T.map ((evaluation C D).obj (P.complex.X n))).ShortExact) :
    ∃ δ : (T.X₃.leftDerived 1).obj M ⟶ T.X₁.obj M,
      (mk₅ ((NatTrans.leftDerived T.f 1).app M) ((NatTrans.leftDerived T.g 1).app M) δ
        (T.f.app M) (T.g.app M)).Exact := by
  have hU := HomologicalComplex.shortExact_of_degreewise_shortExact
    (ShortComplex.mk ((NatTrans.mapHomologicalComplex T.f (ComplexShape.down ℕ)).app P.complex)
      ((NatTrans.mapHomologicalComplex T.g (ComplexShape.down ℕ)).app P.complex) (by
        rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, T.zero]
        ext n
        simp)) hT
  refine ⟨(P.isoLeftDerivedObj T.X₃ 1).hom ≫ hU.δ 1 0 rfl ≫ (homologyZeroIso T.X₁ P).hom,
    ComposableArrows.exact_of_iso (isoMk₅
      (P.isoLeftDerivedObj T.X₁ 1).symm (P.isoLeftDerivedObj T.X₂ 1).symm
      (P.isoLeftDerivedObj T.X₃ 1).symm
      (homologyZeroIso T.X₁ P) (homologyZeroIso T.X₂ P) (homologyZeroIso T.X₃ P)
      (FunctorSequence.homologyFunctor_map_comp_isoLeftDerivedObj_inv T.f P 1)
      (FunctorSequence.homologyFunctor_map_comp_isoLeftDerivedObj_inv T.g P 1)
      (Iso.inv_hom_id_assoc (P.isoLeftDerivedObj T.X₃ 1) _).symm
      (homologyFunctor_map_comp_homologyZeroIso_hom T.f P)
      (homologyFunctor_map_comp_homologyZeroIso_hom T.g P))
      (HomologicalComplex.HomologySequence.composableArrows₅_exact hU 1 0 rfl)⟩

end LeftDerived

/-- For a short exact sequence `S : 0 → N' → N → N'' → 0` of `R`-modules and an `R`-module `M`,
there is a map `δ : Tor₁(M, N'') ⟶ M ⊗ N'` making
`Tor₁(M, N') → Tor₁(M, N) → Tor₁(M, N'') → M ⊗ N' → M ⊗ N → M ⊗ N''` exact, and
`M ⊗ N → M ⊗ N''` is surjective. -/
public theorem solution {R : Type u} [CommRing R]
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) (M : ModuleCat.{u} R) :
    (∃ δ : ((Tor' (ModuleCat.{u} R) 1).obj M).obj S.X₃ ⟶ M ⊗ S.X₁,
        (ComposableArrows.mk₅ (((Tor' (ModuleCat.{u} R) 1).obj M).map S.f)
          (((Tor' (ModuleCat.{u} R) 1).obj M).map S.g) δ (M ◁ S.f) (M ◁ S.g)).Exact) ∧
      Epi (M ◁ S.g) := by
  refine ⟨exists_δ_composableArrows_mk₅_exact
    (ShortComplex.mk ((tensoringRight (ModuleCat.{u} R)).map S.f)
      ((tensoringRight (ModuleCat.{u} R)).map S.g)
      (by rw [← Functor.map_comp, S.zero, Functor.map_zero]))
    (projectiveResolution M)
    (fun n => hS.map_of_exact (tensorLeft ((projectiveResolution M).complex.X n))), ?_⟩
  have := hS.epi_g
  exact preserves_epi_of_preservesColimit (tensorLeft M) S.g

end Stacks.Tor.SixTermSequence

open CategoryTheory MonoidalCategory

namespace CategoryTheory.ShortComplex.ShortExact

/-- Let `R` be a commutative ring, let `M` be an `R`-module and let
`S : 0 → N' → N → N'' → 0` be a short exact sequence of `R`-modules. Then there is a connecting
homomorphism `δ : Tor₁(M, N'') ⟶ M ⊗ N'` making

  `Tor₁(M, N') → Tor₁(M, N) → Tor₁(M, N'') →δ M ⊗ N' → M ⊗ N → M ⊗ N''`

exact, and `M ⊗ N → M ⊗ N''` is surjective. Here `Tor₁(M, -)` is `(Tor' (ModuleCat R) 1).obj M`,
the first left derived functor of `- ⊗ N` evaluated at `M`, and the maps other than `δ` are the
functorial ones. -/
@[stacks 00M0]
public theorem exists_Tor'_one_composableArrows_exact_and_epi {R : Type u} [CommRing R]
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) (M : ModuleCat.{u} R) :
    (∃ δ : ((Tor' (ModuleCat.{u} R) 1).obj M).obj S.X₃ ⟶ M ⊗ S.X₁,
        (ComposableArrows.mk₅ (((Tor' (ModuleCat.{u} R) 1).obj M).map S.f)
          (((Tor' (ModuleCat.{u} R) 1).obj M).map S.g) δ (M ◁ S.f) (M ◁ S.g)).Exact) ∧
      Epi (M ◁ S.g) :=
  Stacks.Tor.SixTermSequence.solution hS M

end CategoryTheory.ShortComplex.ShortExact
