module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ComplexChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DerivedChernClasses
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeChern
public import StacksFrontier.AlgebraicGeometry.Chow.ChowGroupsEnvelopes.BirationalModification
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantStalkRank
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Chern classes of a perfect object, computed on a modification of an integral scheme

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, let `X` be
locally of finite type over `S` and let `E` be an object of `D(𝒪_X)` whose Chern classes are
defined, Stacks 0F9E (1). For `g : W ⟶ X` locally of finite type with `W` integral, Stacks 0GUF
produces an integral `W'` and a proper birational `b : W' ⟶ W` such that, for `g' = b ≫ g`, the
derived pullback `L(g')^*E` is represented by a bounded complex `ℰ^•` of finite locally free
`𝒪_{W'}`-modules of constant ranks, and

  `res_{g'}(c_p(E)) = c_p(ℰ^•)` in `A^p(W')`.

## Main results

* `Stacks.Chow.exists_fiberRank_eq_of_irreducibleSpace` — on an irreducible scheme a locally
  bounded complex of finite locally free modules has constant ranks.
* `Stacks.Chow.exists_properBirational_res_perfectChernClass_eq` — **Stacks 0GUF**.

## Implementation notes

The proof is the source's. Choose an envelope presentation `(f : Y ⟶ X, ℰ_Y^•)` of `E`, and let
`b : W' ⟶ W` together with the lift `a : W' ⟶ Y`, `b ≫ g = a ≫ f`, be the modification of
`AlgebraicGeometry.IsEnvelope.exists_properBirational_modification`. The complex is
`ℰ^• = a^*ℰ_Y^•`.

* It represents `L(g')^*E`: `Stacks.Chow.EnvelopePresentation.pullbackRepresentation` identifies
  `a^*ℰ_Y^•` with `L(a ≫ f)^*E`, the complex `ℰ_Y^•` being K-flat, and `a ≫ f = g'`.
* Its terms have constant ranks: their fibre ranks are locally constant and `W'` is irreducible,
  hence connected. Constant ranks `ρ` force the complex to be bounded, a term of rank `0` being
  zero and `ρ` finitely supported.
* The classes: `c(E)` is the library's `Stacks.Chow.perfectChernClass` of Stacks 0F9E (2), whose
  restriction along `f` is `c(ℰ_Y^•)` by `Stacks.Chow.res_perfectChernClass`. Restricting further
  along `a`, the restriction of `c(ℰ_Y^•)` along a morphism over which the pulled back complex has
  constant ranks `ρ` is the class `∏_n c(ℰ^n)^{(-1)^n}` of the bounded complex,
  `Stacks.Chow.res_complexChern_eq_complexChernBounded`. Composing the restrictions is
  `Stacks.Chow.TotalChowClass.res_res`.

The class `c_p(ℰ^•)` of a bounded complex of finite locally free modules of constant ranks is the
degree-`p` component of `Stacks.Chow.complexChernBounded`, the alternating product of the total
Chern classes of the terms, which is how the source constructs it (Stacks 0ESZ).

## References

* [Stacks Project, Tag 0GUF](https://stacks.math.columbia.edu/tag/0GUF)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0GUD](https://stacks.math.columbia.edu/tag/0GUD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-- **A locally bounded complex of finite locally free modules on an irreducible scheme has
constant ranks**: there is a finitely supported `ρ` with the `n`-th term finite locally free of
rank `ρ n` for every `n`. The fibre ranks of the terms are locally constant, and an irreducible
space is connected. -/
@[ega "II 6.4.8" "special case"]
theorem exists_fiberRank_eq_of_irreducibleSpace {Y : Scheme.{u}} [IrreducibleSpace Y]
    {P : CochainComplex Y.Modules ℤ} (hP : IsLocallyBoundedFiniteLocallyFree P) :
    ∃ ρ : ℤ →₀ ℕ, ∀ n,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n) := by
  let y : Y := _root_.genericPoint Y
  refine ⟨complexRank hP y, fun n ↦ ?_⟩
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (P.X n) := hP.1 n
  exact Scheme.Modules.isFiniteLocallyFreeOfRank_of_forall_fiberRank_eq (P.X n) _ fun x ↦
    ((isLocallyConstant_fiberRank_X hP n).apply_eq_of_preconnectedSpace x y).trans
      (complexRank_apply hP y n).symm

/-- A complex whose terms are finite locally free of ranks `ρ`, with `ρ` finitely supported, is
bounded: its terms vanish outside a finite range of degrees. -/
theorem exists_isZero_X_of_isFiniteLocallyFreeOfRank {Y : Scheme.{u}}
    (P : CochainComplex Y.Modules ℤ) (ρ : ℤ →₀ ℕ)
    (hρ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n)
      (ρ n)) :
    ∃ lo hi : ℤ, ∀ n, (n < lo ∨ hi < n) → IsZero (P.X n) := by
  have hfin := finite_not_isZero_of_isFiniteLocallyFreeOfRank P ρ hρ
  obtain ⟨lo, hlo⟩ := hfin.bddBelow
  obtain ⟨hi, hhi⟩ := hfin.bddAbove
  refine ⟨lo, hi, fun n hn ↦ ?_⟩
  by_contra h
  rcases hn with hn | hn
  · exact (hlo h).not_gt hn
  · exact (hhi h).not_gt hn

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {E : DerivedCategory X.Modules}

/-- **Stacks 0GUF.** Let `X` be locally of finite type over the base and let `E` be an object of
`D(𝒪_X)` whose Chern classes are defined. For `g : W ⟶ X` locally of finite type with `W`
integral there are an integral scheme `W'` and a proper birational morphism `b : W' ⟶ W` such
that, for `g' = b ≫ g`, the derived pullback `L(g')^*E` is represented by a bounded complex `ℰ^•`
of finite locally free `𝒪_{W'}`-modules of constant ranks `ρ`, and

  `res_{g'}(c_p(E)) = c_p(ℰ^•)` in `A^p(W')` for every `p`,

where `c_p(E)` is the degree-`p` component of the total Chern class `c(E)` of Stacks 0F9E (2) and
`c_p(ℰ^•)` that of `∏_n c(ℰ^n)^{(-1)^n}`.

Perfectness of `E` is not used: the Chern classes being defined is the only hypothesis on `E`
the construction needs. -/
@[stacks 0GUF "the full lemma: an integral W' with b : W' -> W proper birational, a bounded \
complex E^bullet of finite locally free O_{W'}-modules of constant ranks representing L(g')^*E \
for g' = b . g, and res_{g'}(c_p(E)) = c_p(E^bullet) in A^p(W') for the Chern classes c_p(E) of \
Tag 0F9E (2), Stacks.Chow.perfectChernClass. The perfectness of E is not needed"]
theorem exists_properBirational_res_perfectChernClass_eq (hE : HasDefinedChernClasses E)
    {W : Scheme.{u}} [IsIntegral W] (g : W ⟶ X) [LocallyOfFiniteType g] :
    ∃ (W' : Scheme.{u}) (b : W' ⟶ W) (_ : IsIntegral W') (_ : IsProper b),
      IsBirational b ∧
      ∃ (ℰ : CochainComplex W'.Modules ℤ) (ρ : ℤ →₀ ℕ)
        (hρ : ∀ n,
          AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (ℰ.X n) (ρ n)),
        (∃ lo hi : ℤ, ∀ n, (n < lo ∨ hi < n) → IsZero (ℰ.X n)) ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (b ≫ g).toLRSHom.toShHom).obj E ≅ DerivedCategory.Q.obj ℰ) ∧
        ∀ p : ℕ, chowCohomologyRestriction C (gysinSystemOfInvertible C) sX (b ≫ g) (p : ℤ)
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
            (perfectChernClass C sX hE p) =
          complexChernBounded C ((b ≫ g) ≫ sX) ℰ ρ hρ p := by
  let H := hE.some
  obtain ⟨W', b, a, hW', hb, hbir, hfac⟩ := H.envelope.exists_properBirational_modification g
  have : LocallyOfFiniteType (a ≫ H.f) := hfac ▸ inferInstance
  have : LocallyOfFiniteType a := locallyOfFiniteType_of_comp a H.f
  have hP := Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback a H.P
    H.locallyBounded
  obtain ⟨ρ, hρ⟩ := exists_fiberRank_eq_of_irreducibleSpace hP
  refine ⟨W', b, hW', hb, hbir, pullbackComplex a H.P, ρ, hρ,
    exists_isZero_X_of_isFiniteLocallyFreeOfRank _ ρ hρ,
    ⟨(eqToIso (Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq
      (congrArg (fun m : W' ⟶ X ↦ m.toLRSHom.toShHom) hfac))).app E ≪≫
        H.pullbackRepresentation a⟩, fun p ↦ ?_⟩
  have hs : a ≫ (H.f ≫ sX) = (b ≫ g) ≫ sX := by rw [← Category.assoc, hfac]
  rw [← TotalChowClass.res_rfl_apply, TotalChowClass.res_congr hfac rfl (by rw [← hs,
      Category.assoc]), ← TotalChowClass.res_res H.f rfl a hs, res_perfectChernClass C sX hE H,
    res_complexChern_eq_complexChernBounded C (H.f ≫ sX) H.locallyBounded a hs ρ hρ]

end Stacks.Chow

end
