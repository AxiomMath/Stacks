module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Flat.CategoryTheory
public import StacksFrontier.CategoryTheory.Abelian.Projective.Horseshoe
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The long exact sequences of `Tor` in all degrees

Let `R` be a commutative ring and let `S : 0 → X₁ → X₂ → X₃ → 0` be a short exact sequence of
`R`-modules. For `Tor_i(M, N) = ((Tor' (ModuleCat R) i).obj M).obj N`, the `i`-th homology of
`P_• ⊗ N` for a projective resolution `P_•` of `M`, there are two long exact sequences, one for
each variable, and in every degree `n`:

  `Tor_{n+1}(M, X₁) → Tor_{n+1}(M, X₂) → Tor_{n+1}(M, X₃) → Tor_n(M, X₁) → ⋯`
  `Tor_{n+1}(X₁, N) → Tor_{n+1}(X₂, N) → Tor_{n+1}(X₃, N) → Tor_n(X₁, N) → ⋯`

The second variable is not derived, so the first sequence is the homology sequence of the short
exact sequence of complexes `P_• ⊗ X₁ → P_• ⊗ X₂ → P_• ⊗ X₃`, which is short exact because each
`P_n` is projective, hence flat. The first variable *is* derived, so the second sequence is the
long exact sequence of a left derived functor, which needs the horseshoe lemma.

## Main definitions

* `Stacks.Tor.FunctorSequence.δ`: the connecting morphism of the homology sequence of a short
  exact sequence of additive functors evaluated on a projective resolution.
* `Stacks.Tor.Tor'δSecond`, `Stacks.Tor.Tor'δFirst`, `Stacks.Tor.Tor'δFirstZero`: the connecting
  morphisms of the two sequences above.

## Main results

* `Stacks.Tor.FunctorSequence.composableArrows_exact`: exactness of the six term sequence of
  left derived functors in degrees `n + 1` and `n` attached to a short exact sequence of functors.
* `Stacks.Tor.Tor'_composableArrows_exact_second` and
  `Stacks.Tor.Tor'_composableArrows_exact_first`: the two long exact sequences above.
* `Stacks.Tor.Tor'_composableArrows_exact_first_zero`: the bottom of the second sequence,
  `Tor₁(X₁, N) → Tor₁(X₂, N) → Tor₁(X₃, N) → X₁ ⊗ N → X₂ ⊗ N → X₃ ⊗ N → 0`.
* `Stacks.Tor.Tor'δSecondIso`: the dimension shift `Tor_{n+1}(M, X₃) ≅ Tor_n(M, X₁)` when
  `Tor_{n+1}(M, X₂)` and `Tor_n(M, X₂)` vanish.

## Implementation notes

The degree `n + 1` to `n` part of the first sequence is stated for an arbitrary short exact
sequence `T` of additive functors `C ⥤ D` out of a category with projective resolutions, under
the hypothesis that `T` stays short exact after evaluation at each term of a projective
resolution `P` of `M`; for `C = D = ModuleCat R` and `T = (- ⊗ X₁ → - ⊗ X₂ → - ⊗ X₃)` that
hypothesis is the flatness of the projective modules `P_n`. Only the comparison
`ProjectiveResolution.isoLeftDerivedObj` is needed to turn the homology sequence into a sequence
of derived functors, because in degrees `n + 1` and `n` with `n` arbitrary no term has to be
identified with the functor itself; that identification, which is needed at the bottom of the
sequence, is the subject of the six term sequence of Tag 00M0.

The second sequence is the long exact sequence of `Functor.leftDerived` for the additive functor
`- ⊗ N`, specialized from `CategoryTheory.Functor.leftDerivedδ` and its exactness statements. At
its bottom the terms are the tensor products themselves rather than the zeroth derived functors,
the two being identified by `Functor.leftDerivedZeroIsoSelf`, whose naturality in the object
variable is exactly what makes the bottom squares commute.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

namespace Stacks.Tor.FunctorSequence

section LeftDerived

variable {C : Type*} [Category* C] [Abelian C] [HasProjectiveResolutions C]
  {D : Type*} [Category* D] [Abelian D]

/-- Naturality in the *functor* variable of `ProjectiveResolution.isoLeftDerivedObj`. -/
lemma homologyFunctor_map_comp_isoLeftDerivedObj_inv
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) {X : C} (P : ProjectiveResolution X)
    (n : ℕ) :
    (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map
        ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) ≫
        (P.isoLeftDerivedObj G n).inv =
      (P.isoLeftDerivedObj F n).inv ≫ (NatTrans.leftDerived α n).app X := by
  rw [P.leftDerived_app_eq α n, Iso.inv_hom_id_assoc]

/-- An exact functor has no higher left derived functors. -/
lemma isZero_leftDerived_succ_obj_of_exact (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (n : ℕ) (X : C) : IsZero ((G.leftDerived (n + 1)).obj X) := by
  refine IsZero.of_iso ?_ ((projectiveResolution X).isoLeftDerivedObj G (n + 1))
  have h : ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (projectiveResolution X).complex).ExactAt (n + 1) :=
    ((projectiveResolution X).complex_exactAt_succ n).map G
  simpa only [HomologicalComplex.homologyFunctor_obj] using
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp h

variable (T : ShortComplex (C ⥤ D)) [T.X₁.Additive] [T.X₂.Additive] [T.X₃.Additive]
  {M : C} (P : ProjectiveResolution M)

/-- The short complex of chain complexes `T(P_•)` obtained by evaluating a short complex `T` of
additive functors on a projective resolution `P`. -/
noncomputable def resolutionShortComplex :
    ShortComplex (HomologicalComplex D (ComplexShape.down ℕ)) :=
  ShortComplex.mk ((NatTrans.mapHomologicalComplex T.f (ComplexShape.down ℕ)).app P.complex)
    ((NatTrans.mapHomologicalComplex T.g (ComplexShape.down ℕ)).app P.complex) (by
      rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, T.zero]
      ext n
      simp)

variable (hT : ∀ k : ℕ, (T.map ((evaluation C D).obj (P.complex.X k))).ShortExact)

include hT

omit [HasProjectiveResolutions C] in
/-- If `T` stays short exact after evaluation at each term of the projective resolution `P`,
then `T(P_•)` is a short exact sequence of chain complexes. -/
lemma shortExact_resolutionShortComplex : (resolutionShortComplex T P).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ hT

/-- The connecting morphism `L_{n+1} T.X₃ (M) ⟶ L_n T.X₁ (M)` of the homology sequence of
`T(P_•)`, read on left derived functors through `ProjectiveResolution.isoLeftDerivedObj`. -/
noncomputable def δ (n : ℕ) : (T.X₃.leftDerived (n + 1)).obj M ⟶ (T.X₁.leftDerived n).obj M :=
  (P.isoLeftDerivedObj T.X₃ (n + 1)).hom ≫
    (shortExact_resolutionShortComplex T P hT).δ (n + 1) n rfl ≫
      (P.isoLeftDerivedObj T.X₁ n).inv

open ComposableArrows in
/-- The six term exact sequence in degrees `n + 1` and `n` attached to a short exact sequence `T`
of additive functors and an object `M` with projective resolution `P`, on the assumption that `T`
stays short exact after evaluation at each `P_k`. -/
theorem composableArrows_exact (n : ℕ) :
    (mk₅ ((NatTrans.leftDerived T.f (n + 1)).app M) ((NatTrans.leftDerived T.g (n + 1)).app M)
      (δ T P hT n) ((NatTrans.leftDerived T.f n).app M)
      ((NatTrans.leftDerived T.g n).app M)).Exact :=
  ComposableArrows.exact_of_iso (isoMk₅
    (P.isoLeftDerivedObj T.X₁ (n + 1)).symm (P.isoLeftDerivedObj T.X₂ (n + 1)).symm
    (P.isoLeftDerivedObj T.X₃ (n + 1)).symm (P.isoLeftDerivedObj T.X₁ n).symm
    (P.isoLeftDerivedObj T.X₂ n).symm (P.isoLeftDerivedObj T.X₃ n).symm
    (homologyFunctor_map_comp_isoLeftDerivedObj_inv T.f P (n + 1))
    (homologyFunctor_map_comp_isoLeftDerivedObj_inv T.g P (n + 1))
    (Iso.inv_hom_id_assoc (P.isoLeftDerivedObj T.X₃ (n + 1)) _).symm
    (homologyFunctor_map_comp_isoLeftDerivedObj_inv T.f P n)
    (homologyFunctor_map_comp_isoLeftDerivedObj_inv T.g P n))
    (HomologicalComplex.HomologySequence.composableArrows₅_exact
      (shortExact_resolutionShortComplex T P hT) (n + 1) n rfl)

/-- The connecting morphism is an isomorphism as soon as both middle terms flanking it vanish. -/
theorem isIso_δ (n : ℕ) (h : IsZero ((T.X₂.leftDerived (n + 1)).obj M))
    (h' : IsZero ((T.X₂.leftDerived n).obj M)) : IsIso (δ T P hT n) := by
  have hex := composableArrows_exact T P hT n
  have : Mono (δ T P hT n) := (hex.exact' 1 2 3).mono_g (h.eq_of_src _ _)
  have : Epi (δ T P hT n) := (hex.exact' 2 3 4).epi_f (h'.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- The dimension shift `L_{n+1} T.X₃ (M) ≅ L_n T.X₁ (M)` given by the connecting morphism when
both middle terms flanking it vanish. -/
@[ega "III 7.6.11" "more general"]
noncomputable def δIso (n : ℕ) (h : IsZero ((T.X₂.leftDerived (n + 1)).obj M))
    (h' : IsZero ((T.X₂.leftDerived n).obj M)) :
    (T.X₃.leftDerived (n + 1)).obj M ≅ (T.X₁.leftDerived n).obj M :=
  haveI := isIso_δ T P hT n h h'
  asIso (δ T P hT n)

end LeftDerived

end Stacks.Tor.FunctorSequence

namespace Stacks.Tor

variable {R : Type u} [CommRing R] {S : ShortComplex (ModuleCat.{u} R)}

/-- The short complex of functors `- ⊗ X₁ → - ⊗ X₂ → - ⊗ X₃` attached to a short complex `S`. -/
noncomputable abbrev tensoringRightShortComplex (S : ShortComplex (ModuleCat.{u} R)) :
    ShortComplex (ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
  ShortComplex.mk ((tensoringRight (ModuleCat.{u} R)).map S.f)
    ((tensoringRight (ModuleCat.{u} R)).map S.g)
    (by rw [← Functor.map_comp, S.zero, Functor.map_zero])

/-- Tensoring a short exact sequence with a projective module is short exact. -/
lemma shortExact_map_tensorLeft (hS : S.ShortExact) (M : ModuleCat.{u} R) (k : ℕ) :
    ((tensoringRightShortComplex S).map
      ((evaluation (ModuleCat.{u} R) (ModuleCat.{u} R)).obj
        ((projectiveResolution M).complex.X k))).ShortExact :=
  hS.map_of_exact (tensorLeft ((projectiveResolution M).complex.X k))

/-- The connecting morphism `Tor_{n+1}(M, X₃) ⟶ Tor_n(M, X₁)` of the long exact sequence of
`Tor_•(M, -)` attached to a short exact sequence `S : 0 → X₁ → X₂ → X₃ → 0`. -/
noncomputable def Tor'δSecond (hS : S.ShortExact) (M : ModuleCat.{u} R) (n : ℕ) :
    ((Tor' (ModuleCat.{u} R) (n + 1)).obj M).obj S.X₃ ⟶
      ((Tor' (ModuleCat.{u} R) n).obj M).obj S.X₁ :=
  FunctorSequence.δ (tensoringRightShortComplex S) (projectiveResolution M)
    (shortExact_map_tensorLeft hS M) n

open ComposableArrows in
/-- The long exact sequence of `Tor_•(M, -)` in the underived variable: for a short exact
sequence `S : 0 → X₁ → X₂ → X₃ → 0` and every `n`, the sequence
`Tor_{n+1}(M, X₁) → Tor_{n+1}(M, X₂) → Tor_{n+1}(M, X₃) → Tor_n(M, X₁) → Tor_n(M, X₂) →
Tor_n(M, X₃)` is exact. -/
theorem Tor'_composableArrows_exact_second (hS : S.ShortExact) (M : ModuleCat.{u} R) (n : ℕ) :
    (mk₅ (((Tor' (ModuleCat.{u} R) (n + 1)).obj M).map S.f)
      (((Tor' (ModuleCat.{u} R) (n + 1)).obj M).map S.g) (Tor'δSecond hS M n)
      (((Tor' (ModuleCat.{u} R) n).obj M).map S.f)
      (((Tor' (ModuleCat.{u} R) n).obj M).map S.g)).Exact :=
  FunctorSequence.composableArrows_exact (tensoringRightShortComplex S) (projectiveResolution M)
    (shortExact_map_tensorLeft hS M) n

/-- The dimension shift `Tor_{n+1}(M, X₃) ≅ Tor_n(M, X₁)` for a short exact sequence
`S : 0 → X₁ → X₂ → X₃ → 0` whose middle term has vanishing `Tor_{n+1}(M, -)` and
`Tor_n(M, -)`. -/
@[ega "III 7.6.11" "more general"]
noncomputable def Tor'δSecondIso (hS : S.ShortExact) (M : ModuleCat.{u} R) (n : ℕ)
    (h : IsZero (((Tor' (ModuleCat.{u} R) (n + 1)).obj M).obj S.X₂))
    (h' : IsZero (((Tor' (ModuleCat.{u} R) n).obj M).obj S.X₂)) :
    ((Tor' (ModuleCat.{u} R) (n + 1)).obj M).obj S.X₃ ≅
      ((Tor' (ModuleCat.{u} R) n).obj M).obj S.X₁ :=
  FunctorSequence.δIso (tensoringRightShortComplex S) (projectiveResolution M)
    (shortExact_map_tensorLeft hS M) n h h'

/-- The connecting morphism `Tor_{n+1}(X₃, N) ⟶ Tor_n(X₁, N)` of the long exact sequence of
`Tor_•(-, N)` attached to a short exact sequence `S : 0 → X₁ → X₂ → X₃ → 0`. -/
noncomputable def Tor'δFirst (hS : S.ShortExact) (N : ModuleCat.{u} R) (n : ℕ) :
    ((Tor' (ModuleCat.{u} R) (n + 1)).obj S.X₃).obj N ⟶
      ((Tor' (ModuleCat.{u} R) n).obj S.X₁).obj N :=
  ((tensoringRight (ModuleCat.{u} R)).obj N).leftDerivedδ hS n

open ComposableArrows in
/-- The long exact sequence of `Tor_•(-, N)` in the derived variable: for a short exact sequence
`S : 0 → X₁ → X₂ → X₃ → 0` and every `n`, the sequence
`Tor_{n+1}(X₁, N) → Tor_{n+1}(X₂, N) → Tor_{n+1}(X₃, N) → Tor_n(X₁, N) → Tor_n(X₂, N) →
Tor_n(X₃, N)` is exact. -/
theorem Tor'_composableArrows_exact_first (hS : S.ShortExact) (N : ModuleCat.{u} R) (n : ℕ) :
    (mk₅ (((Tor' (ModuleCat.{u} R) (n + 1)).map S.f).app N)
      (((Tor' (ModuleCat.{u} R) (n + 1)).map S.g).app N) (Tor'δFirst hS N n)
      (((Tor' (ModuleCat.{u} R) n).map S.f).app N)
      (((Tor' (ModuleCat.{u} R) n).map S.g).app N)).Exact :=
  exact_of_δ₀
    ((((tensoringRight (ModuleCat.{u} R)).obj N).leftDerived_exact hS
      (n + 1)).exact_toComposableArrows)
    (exact_of_δ₀
      ((((tensoringRight (ModuleCat.{u} R)).obj N).leftDerived_exact_δ₁ hS
        n).exact_toComposableArrows)
      (exact_of_δ₀
        ((((tensoringRight (ModuleCat.{u} R)).obj N).leftDerived_exact_δ₂ hS
          n).exact_toComposableArrows)
        ((((tensoringRight (ModuleCat.{u} R)).obj N).leftDerived_exact hS
          n).exact_toComposableArrows)))

/-- The connecting morphism `Tor₁(X₃, N) ⟶ X₁ ⊗ N` at the bottom of the long exact sequence of
`Tor_•(-, N)`, with the zeroth derived functor identified with the tensor product. -/
noncomputable def Tor'δFirstZero (hS : S.ShortExact) (N : ModuleCat.{u} R) :
    ((Tor' (ModuleCat.{u} R) 1).obj S.X₃).obj N ⟶ S.X₁ ⊗ N :=
  Tor'δFirst hS N 0 ≫
    (((tensoringRight (ModuleCat.{u} R)).obj N).leftDerivedZeroIsoSelf.app S.X₁).hom

open ComposableArrows in
/-- The bottom of the long exact sequence of `Tor_•(-, N)`: for a short exact sequence
`S : 0 → X₁ → X₂ → X₃ → 0` the sequence
`Tor₁(X₁, N) → Tor₁(X₂, N) → Tor₁(X₃, N) → X₁ ⊗ N → X₂ ⊗ N → X₃ ⊗ N` is exact. -/
theorem Tor'_composableArrows_exact_first_zero (hS : S.ShortExact) (N : ModuleCat.{u} R) :
    (mk₅ (((Tor' (ModuleCat.{u} R) 1).map S.f).app N) (((Tor' (ModuleCat.{u} R) 1).map S.g).app N)
      (Tor'δFirstZero hS N) (S.f ▷ N) (S.g ▷ N)).Exact := by
  refine ComposableArrows.exact_of_iso ?_ (Tor'_composableArrows_exact_first hS N 0)
  exact isoMk₅ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (((tensoringRight (ModuleCat.{u} R)).obj N).leftDerivedZeroIsoSelf.app S.X₁)
    (((tensoringRight (ModuleCat.{u} R)).obj N).leftDerivedZeroIsoSelf.app S.X₂)
    (((tensoringRight (ModuleCat.{u} R)).obj N).leftDerivedZeroIsoSelf.app S.X₃)
    (by cat_disch) (by cat_disch) (Category.id_comp _).symm
    (((tensoringRight (ModuleCat.{u} R)).obj N).leftDerivedZeroIsoSelf.hom.naturality S.f)
    (((tensoringRight (ModuleCat.{u} R)).obj N).leftDerivedZeroIsoSelf.hom.naturality S.g)

/-- The last map of the long exact sequence of `Tor_•(-, N)` is surjective. -/
theorem epi_whiskerRight_g (hS : S.ShortExact) (N : ModuleCat.{u} R) : Epi (S.g ▷ N) := by
  have := hS.epi_g
  exact preserves_epi_of_preservesColimit (tensorRight N) S.g

/-- `Tor₁(X₃, N) ⟶ X₁ ⊗ N` is injective as soon as `Tor₁(X₂, N)` vanishes. -/
theorem mono_Tor'δFirstZero (hS : S.ShortExact) (N : ModuleCat.{u} R)
    (h : IsZero (((Tor' (ModuleCat.{u} R) 1).obj S.X₂).obj N)) : Mono (Tor'δFirstZero hS N) :=
  ((Tor'_composableArrows_exact_first_zero hS N).exact' 1 2 3).mono_g (h.eq_of_src _ _)

/-- `Tor_i(M, N) = 0` for `i > 0` when `N` is flat. -/
theorem isZero_Tor'_succ_obj_of_flat (M N : ModuleCat.{u} R) [Module.Flat R N] (n : ℕ) :
    IsZero (((Tor' (ModuleCat.{u} R) (n + 1)).obj M).obj N) :=
  FunctorSequence.isZero_leftDerived_succ_obj_of_exact
    ((tensoringRight (ModuleCat.{u} R)).obj N) n M

end Stacks.Tor

end
