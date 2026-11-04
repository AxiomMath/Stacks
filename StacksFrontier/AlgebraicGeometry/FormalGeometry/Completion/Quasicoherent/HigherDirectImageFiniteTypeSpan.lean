module

public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Pieces
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.ChartIdealSheaf
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.ChartSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Modules.GradedFiniteTypeAffine
public import StacksFrontier.RingTheory.Filtration.IdealPowerSystemNoetherian
public import StacksCore.Tactic.StacksAttribute

/-!
# `⨁ₙ R ᵖ f_*(ℐⁿℱ)` is a quasi-coherent graded `⨁ₙ ℐⁿ`-module of finite type

Let `f : X ⟶ Y` be a morphism of schemes, `ℱ` an `𝒪_X`-module and `ℐ ⊆ 𝒪_Y` a quasi-coherent
sheaf of ideals, with `Y` locally Noetherian, `f` proper and `ℱ` coherent. [Stacks, Tag 02O9]
asserts that the graded `𝒜 = ⨁ₙ ℐⁿ`-module `ℳ = ⨁ₙ R ᵖ f_*(ℐⁿℱ)` — which is
`Stacks.Blowup.pushforwardReesGradedModulePlus`, the structure [Stacks, Tag 02O7] builds — is
quasi-coherent and of finite type. This file proves both clauses, in the shape the tag's own
words ask for, and registers the tag.

The source's proof is two sentences: the statement is local on `Y`, so one may assume `Y`
affine, and over an affine base it is [Stacks, Tag 02O8]. Finite type for a graded module is
`SheafOfModules.GradedModule.IsFiniteType`, a covering-sieve condition, and the bridge from the
affine-local statement to it is `SheafOfModules.GradedModule.isFiniteType_of_affine_span`: over
each affine open `V ⊆ Y` one must exhibit finitely many homogeneous sections of `ℳ` over `V`
finitely many of whose products with homogeneous sections of `𝒜` span `Γ(V, ℳₖ)` over `Γ(Y, V)`,
in every degree `k`. That is what this file produces.

## Main results

* `Stacks.Algebraization.exists_affine_span_pushforwardReesGradedModulePlus`: **the span.** The
  spanning family demanded by the affine criterion, over an arbitrary affine open of the base.
* `Stacks.Algebraization.isQuasicoherent_and_isFiniteType_pushforwardReesGradedModulePlus`:
  **[Stacks, Tag 02O9].** Both clauses, at the source's hypotheses.
* `Stacks.Algebraization.exists_chartHomogeneousGenerators`: [Stacks, Tag 02O8] on a chart of
  the base, read as finitely many homogeneous generators with degreewise coefficients.
* `Stacks.Algebraization.moduleFinite_reesGradedAlgebra_piece_sections`: the homogeneous
  sections of `𝒜` over an affine open of a locally Noetherian scheme are a finite module.

## Implementation notes

**Where the generators come from.** On the chart `f⁻¹(V) ⟶ Spec Γ(Y, V)`, [Stacks, Tag 02O8] is
`Stacks.Algebraization.isCohomologyReesFiniteOfGradedModule_affineBaseChart`: the graded module
`⨁ₙ Hᵖ(f⁻¹V, (ℐⁿℱ)|_{f⁻¹V})` is finite over the *ring* Rees algebra `⨁ₙ ℐ(V)ⁿ`. Finiteness is
upgraded to finitely many *homogeneous* generators with degreewise coefficients by
`Stacks.RingTheory.exists_homogeneous_generators`, instantiated at the full graded submodule
`T n = ⊤` — the acting ring is Noetherian by
`Stacks.RingTheory.isNoetherianRing_reesGradingDirectSum`. The generators are transported to
sections of `ℳ` by `Stacks.Algebraization.chartSections`, which is onto
(`chartSections_surjective`), additive (`chartSections_add`) and semilinear
(`chartSections_actHom`); **no `Γ(Y, V)`-linearity of the comparison is used**, and that is why
the affine criterion is stated in terms of a spanning family of *products* rather than of
`Module.Finite`.

**Why a second cut is needed.** The affine criterion wants a family of products fixed *before*
the section it is asked to express, while the generator expansion produces coefficients
depending on that section. The gap is closed by the linearity of the action in the *algebra*
variable (`SheafOfModules.GradedModule.smulSection_smul_right`): a finite generating family of
the `Γ(Y, V)`-module `Γ(V, 𝒜_{k-d})` suffices, and there is one because `Γ(V, 𝒜_j)` embeds
`Γ(Y, V)`-linearly into the Noetherian ring `Γ(Y, V)` by
`Stacks.Blowup.reesAmbientLinearMap`. The blocks are padded with zeros to a common length, as
`SheafOfModules.GradedModule.isFiniteType_of_affine_span` expects.

**The `ℕ`/`ℤ` degree reconciliation.** `Stacks.RingTheory.exists_homogeneous_generators` indexes
degrees by `ℕ` and `SheafOfModules.GradedModule` by `ℤ`, so a generator of degree `d` and a
coefficient of degree `n - d` (truncated subtraction) must be matched with the degrees
`(d : ℤ)` and `k - (d : ℤ)`. Both transports are performed by stating the step at *variable*
degrees carrying their own equality proofs and substituting them away:
`Stacks.Algebraization.smul_chartSections` does this for the action on sections and
`Stacks.Algebraization.of_actHom_gradedCohomologySmul` for the `ℕ`-degree of the direct sum.
The coefficient in degrees above `n` is zero, which is what makes the truncated subtraction
harmless.

**Negative degrees are free.** In a negative degree the piece of `ℳ` is `R ᵖ f_*(⊥)`:
`Stacks.Blowup.reesMultiple_eq_bot_of_neg` and `Stacks.Blowup.isZero_toSheafOfModules_bot`
make the argument of the higher direct image a zero object, so the piece is one too and all of
its sections vanish, whence any family spans.

**Why quasi-coherence is read on the pieces.** A graded module in this formalism is its family
of homogeneous pieces together with the action, so `ℳ` is quasi-coherent exactly when each
`ℳₙ` is; that is
`Stacks.Blowup.isQuasicoherent_piece_pushforwardReesGradedModulePlus`. The quasi-coherence of
the direct sum itself, in the `ℕ`-indexed coproduct model the quasi-coherence clause was first
proved in, remains available as
`Stacks.Algebraization.isQuasicoherent_sigma_higherDirectImage_idealPowerMultiple`; it follows
from the clause proved here because quasi-coherence is stable under colimits.

## References

* [Stacks Project, Tag 02O9](https://stacks.math.columbia.edu/tag/02O9)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
* [Stacks Project, Tag 02O7](https://stacks.math.columbia.edu/tag/02O7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.FormalFunctions
open SheafOfModules.GradedModule
open DirectSum

universe u

namespace Stacks.Algebraization

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Y.IdealSheafData) (F : X.Modules) (p : ℕ)

/-! ### The homogeneous sections of the Rees algebra over an affine open -/

/-- **The degree-`j` sections of the Rees algebra of `ℐ` over an affine open `V` of a locally
Noetherian scheme are a finite `Γ(Y, V)`-module.** In nonnegative degrees they embed
`Γ(Y, V)`-linearly into `Γ(Y, V)` as the ideal `ℐ(V)^j` (`Stacks.Blowup.reesAmbientLinearMap`,
injective by `Stacks.Blowup.reesPieceAmbient_injective`), which is Noetherian; in negative
degrees the piece vanishes.

This is the finiteness that cuts the coefficients of the generator expansion down to a finite
family, in the implementation notes of this file. -/
public theorem moduleFinite_reesGradedAlgebra_piece_sections [IsLocallyNoetherian Y]
    (V : Y.affineOpens) (j : ℤ) :
    Module.Finite ↥(Y.ringCatSheaf.obj.obj (op V.1))
      (((Stacks.Blowup.reesGradedAlgebra I).piece j).val.obj (op V.1)) := by
  have : IsNoetherianRing ↥Γ(Y, V.1) := isNoetherianRing_sections_affineOpens V
  rcases le_or_gt 0 j with hj | hj
  · have : _root_.IsNoetherian ↥Γ(Y, V.1) Γ(Stacks.Conormal.reesModule I j, V.1) :=
      isNoetherian_of_injective (Stacks.Blowup.reesAmbientLinearMap I j V.1)
        (Stacks.Blowup.reesPieceAmbient_injective I j hj V.1)
    have : Module.Finite ↥Γ(Y, V.1) Γ(Stacks.Conormal.reesModule I j, V.1) := inferInstance
    exact this
  · have : Subsingleton (((Stacks.Blowup.reesGradedAlgebra I).piece j).val.obj (op V.1)) :=
      Stacks.subsingleton_of_isZero (Stacks.Blowup.reesPiece_negative_isZero I j hj) (op V.1)
    have h0 : (⊤ : Submodule ↥(Y.ringCatSheaf.obj.obj (op V.1))
        (((Stacks.Blowup.reesGradedAlgebra I).piece j).val.obj (op V.1))) = ⊥ :=
      Submodule.eq_bot_of_subsingleton
    refine ⟨?_⟩
    rw [h0]
    exact Submodule.fg_bot

/-! ### The vanishing of the negative pieces -/

/-- **In a negative degree the piece of `⨁ₙ R ᵖ f_*(ℐⁿℱ)` is a zero object**, because `ℐⁿℱ` is
the zero subsheaf of `ℱ` there and the higher direct image preserves zero objects. -/
public theorem isZero_piece_pushforwardReesGradedModulePlus_of_neg (k : ℤ) (hk : k < 0) :
    IsZero ((Stacks.Blowup.pushforwardReesGradedModulePlus f I F p).piece k) := by
  have he : Stacks.Blowup.reesMultiple (I.comap f) k F = ⊥ :=
    Stacks.Blowup.reesMultiple_eq_bot_of_neg (I.comap f) k F hk
  have h0 : IsZero (Stacks.Blowup.reesComapMod f I F k) := by
    change IsZero ((Stacks.Blowup.reesMultiple (I.comap f) k F).toSheafOfModules : X.Modules)
    rw [he]
    exact Stacks.Blowup.isZero_toSheafOfModules_bot F
  exact ((Scheme.Modules.pushforward f).rightDerived p).map_isZero h0

/-! ### The degree transports -/

section Transport

variable [QuasiCompact f] [QuasiSeparated f] [F.IsQuasicoherent]

/-- **The comparison carries the action of the ring Rees algebra to the graded action on
sections**, at target degrees reached by arithmetic. This is
`Stacks.Algebraization.chartSections_actHom` with the two degrees that the generator expansion
arrives at — the degree `j` of the coefficient and the total degree `K` — taken as arguments
together with proofs of their values, so that a consumer does not have to transport afterwards.

Both proofs are substituted away, which is why only `chartSections_actHom` is needed; crossing
the two spellings of a degree by `rfl` instead is the whnf wall recorded in the implementation
notes of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.ChartActionSquare`. -/
public theorem smul_chartSections (V : Y.affineOpens) (dd : ℕ) {kk : ℕ}
    (b : ↥(Stacks.Blowup.reesGrading (I.ideal V) kk))
    (z : (cohomologyFunctor (affineBaseChart f V) p).obj
      ((reesFiltrationModule (I.ideal V) (affineBaseChart f V)
        (affineBaseChartModule f F V)).piece (dd : ℤ)))
    {j : ℤ} (hj : (kk : ℤ) = j) {K : ℤ} (hK : (dd : ℤ) + j = K)
    (hK' : (dd : ℤ) + (kk : ℤ) = K) :
    SheafOfModules.castHom
        (Stacks.Blowup.pushforwardReesGradedModulePlus f I F p).piece hK (op V.1)
        ((Stacks.Blowup.pushforwardReesGradedModulePlus f I F p).smul (dd : ℤ) j (op V.1)
          (chartSections f I F p V (dd : ℤ) z) (chartReesSection I V b hj)) =
      chartSections f I F p V K
        (((cohomologyFunctor (affineBaseChart f V) p).map
          (actHom (I.ideal V) (affineBaseChart f V)
            (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
              (affineBaseChartModule f F V)) b (dd : ℤ) hK')).hom z) := by
  subst hj
  subst hK
  exact (chartSections_actHom f I F p V b (dd : ℤ) z).symm

end Transport

/-- **The `ℕ`-degree transport.** Acting by a homogeneous element of degree `kk` on the
degree-`dd` cohomology lands, as a summand of `⨁ₙ Hᵖ(f⁻¹V, ℐⁿℱ)`, in degree `kk + dd`; read as a
morphism it is the action into any degree `n` with `(dd : ℤ) + (kk : ℤ) = (n : ℤ)`. The two
agree as elements of the direct sum.

This is what reconciles the `ℕ`-indexed degrees of
`Stacks.RingTheory.exists_homogeneous_generators` with the `ℤ`-indexed ones of
`SheafOfModules.GradedModule`. -/
public theorem of_actHom_gradedCohomologySmul (V : Y.affineOpens) {dd kk n : ℕ}
    (hn : kk + dd = n) (b : ↥(Stacks.Blowup.reesGrading (I.ideal V) kk))
    (z : gradedCohomologyPiece (I.ideal V) (affineBaseChart f V)
      (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
        (affineBaseChartModule f F V)) p dd)
    (hK : (dd : ℤ) + (kk : ℤ) = (n : ℤ)) :
    DirectSum.of (gradedCohomologyPiece (I.ideal V) (affineBaseChart f V)
        (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
          (affineBaseChartModule f F V)) p) n
        (((cohomologyFunctor (affineBaseChart f V) p).map
          (actHom (I.ideal V) (affineBaseChart f V)
            (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
              (affineBaseChartModule f F V)) b (dd : ℤ) hK)).hom z) =
      DirectSum.of (gradedCohomologyPiece (I.ideal V) (affineBaseChart f V)
          (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
            (affineBaseChartModule f F V)) p) (kk + dd)
        (gradedCohomologySmul (I.ideal V) (affineBaseChart f V)
          (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
            (affineBaseChartModule f F V)) p b z) := by
  subst hn
  rfl

/-! ### [Stacks, Tag 02O8] on a chart, as homogeneous generators -/

/-- **[Stacks, Tag 02O8] on an affine chart of the base, read as homogeneous generators.** The
graded module `⨁ₙ Hᵖ(f⁻¹V, ℐⁿℱ)` is generated over the ring Rees algebra `⨁ₙ ℐ(V)ⁿ` by finitely
many homogeneous elements `x' i` of degrees `d' i`, with the coefficients of a degree-`n`
element read off degreewise: the coefficient of `x' i` is homogeneous of degree `n - d' i` and
vanishes when `d' i` exceeds `n`.

This is `Stacks.Algebraization.isCohomologyReesFiniteOfGradedModule_affineBaseChart` fed to
`Stacks.RingTheory.exists_homogeneous_generators` at the graded submodule `T n = ⊤`, whose
closure hypothesis is then trivial. The acting ring is Noetherian because `Γ(Y, V)` is. -/
@[ega "III 2.4.2" "special case"]
public theorem exists_chartHomogeneousGenerators [IsLocallyNoetherian Y] [IsProper f]
    [F.IsCoherent] (V : Y.affineOpens) :
    ∃ (t : ℕ) (d' : Fin t → ℕ)
      (x' : ∀ i, gradedCohomologyPiece (I.ideal V) (affineBaseChart f V)
        (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
          (affineBaseChartModule f F V)) p (d' i)),
      ∀ (n : ℕ) (z : gradedCohomologyPiece (I.ideal V) (affineBaseChart f V)
          (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
            (affineBaseChartModule f F V)) p n),
        ∃ c : ∀ i : Fin t, ↥(Stacks.Blowup.reesGrading (I.ideal V) (n - d' i)),
          (∀ i, n < d' i → c i = 0) ∧
          DirectSum.of (gradedCohomologyPiece (I.ideal V) (affineBaseChart f V)
              (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
                (affineBaseChartModule f F V)) p) n z =
            ∑ i, DirectSum.of (gradedCohomologyPiece (I.ideal V) (affineBaseChart f V)
                (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
                  (affineBaseChartModule f F V)) p) (n - d' i + d' i)
              (gradedCohomologySmul (I.ideal V) (affineBaseChart f V)
                (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
                  (affineBaseChartModule f F V)) p (c i) (x' i)) := by
  let inst := cohomologyGradedModule (I.ideal V) (affineBaseChart f V)
    (reesFiltrationModule (I.ideal V) (affineBaseChart f V) (affineBaseChartModule f F V)) p
  have : IsNoetherianRing ↥Γ(Y, V.1) := isNoetherianRing_sections_affineOpens V
  have hfin : Module.Finite (⨁ n, ↥(Stacks.Blowup.reesGrading (I.ideal V) n))
      (⨁ n, gradedCohomologyPiece (I.ideal V) (affineBaseChart f V)
        (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
          (affineBaseChartModule f F V)) p n) :=
    isCohomologyReesFiniteOfGradedModule_affineBaseChart I f F V p
  have hnoeth : IsNoetherianRing (⨁ n, ↥(Stacks.Blowup.reesGrading (I.ideal V) n)) :=
    Stacks.RingTheory.isNoetherianRing_reesGradingDirectSum (I.ideal V)
  obtain ⟨t, d', x', -, hcoef⟩ :=
    Stacks.RingTheory.exists_homogeneous_generators (R := ℤ)
      (A := fun n => ↥(Stacks.Blowup.reesGrading (I.ideal V) n))
      (M := fun n => gradedCohomologyPiece (I.ideal V) (affineBaseChart f V)
        (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
          (affineBaseChartModule f F V)) p n)
      (fun _ => ⊤) (fun _ _ _ _ _ => Submodule.mem_top)
  exact ⟨t, d', x', fun n z => hcoef n z Submodule.mem_top⟩

/-! ### The span, and [Stacks, Tag 02O9] -/

section Span

variable [QuasiCompact f] [QuasiSeparated f] [F.IsQuasicoherent]

/-- **The spanning family of [Stacks, Tag 02O9], over an affine open of the base.** There are
finitely many homogeneous sections of `ℳ = ⨁ₙ R ᵖ f_*(ℐⁿℱ)` over `V`, of degrees `d`, such that
in every degree `k` finitely many of their products with homogeneous sections of `𝒜 = ⨁ₙ ℐⁿ`
span `Γ(V, ℳₖ)` over `Γ(Y, V)`.

This is the hypothesis of `SheafOfModules.GradedModule.isFiniteType_of_affine_span`; see the
implementation notes of this file for the three steps. -/
@[ega "III 2.4.2" "special case"]
public theorem exists_affine_span_pushforwardReesGradedModulePlus [IsLocallyNoetherian Y]
    [IsProper f] [F.IsCoherent] (V : Y.affineOpens) :
    ∃ (m : ℕ) (d : Fin m → ℤ)
      (s : ∀ i, ((Stacks.Blowup.pushforwardReesGradedModulePlus f I F p).piece
        (d i)).val.obj (op V.1)),
      ∀ k : ℤ, ∃ (q : ℕ)
          (c : ∀ i : Fin m, Fin q →
            ((Stacks.Blowup.reesGradedAlgebra I).piece (k - d i)).val.obj (op V.1)),
        Submodule.span ↥(Y.ringCatSheaf.obj.obj (op V.1))
          (Set.range fun ij : Fin m × Fin q =>
            (Stacks.Blowup.pushforwardReesGradedModulePlus f I F p).smulSection k
              (s ij.1) (c ij.1 ij.2)) = ⊤ := by
  classical
  obtain ⟨t, d', x', hcoef⟩ := exists_chartHomogeneousGenerators f I F p V
  refine ⟨t, fun i => (d' i : ℤ), fun i => chartSections f I F p V (d' i : ℤ) (x' i), ?_⟩
  intro k
  -- every homogeneous section over `V` is a sum of products of the transported generators
  have hsum : ∀ w : ((Stacks.Blowup.pushforwardReesGradedModulePlus f I F p).piece k).val.obj
        (op V.1),
      ∃ y : ∀ i : Fin t, ((Stacks.Blowup.reesGradedAlgebra I).piece
          (k - (d' i : ℤ))).val.obj (op V.1),
        w = ∑ i, (Stacks.Blowup.pushforwardReesGradedModulePlus f I F p).smulSection k
          (chartSections f I F p V (d' i : ℤ) (x' i)) (y i) := by
    rcases le_or_gt 0 k with hk | hk
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
      intro w
      obtain ⟨z, rfl⟩ := chartSections_surjective f I F p V (n : ℤ) w
      obtain ⟨c, hc0, heq⟩ := hcoef n z
      let Φ := AddMonoidHom.mk' (chartSections f I F p V (n : ℤ))
        (chartSections_add f I F p V (n : ℤ))
      -- the degree-`n` summand each generator contributes, and the coefficient it becomes
      have hukey : ∀ i : Fin t, ∃ ui : gradedCohomologyPiece (I.ideal V) (affineBaseChart f V)
          (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
            (affineBaseChartModule f F V)) p n,
          DirectSum.of (gradedCohomologyPiece (I.ideal V) (affineBaseChart f V)
              (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
                (affineBaseChartModule f F V)) p) n ui =
            DirectSum.of (gradedCohomologyPiece (I.ideal V) (affineBaseChart f V)
                (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
                  (affineBaseChartModule f F V)) p) (n - d' i + d' i)
              (gradedCohomologySmul (I.ideal V) (affineBaseChart f V)
                (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
                  (affineBaseChartModule f F V)) p (c i) (x' i)) ∧
          ∃ yi : ((Stacks.Blowup.reesGradedAlgebra I).piece
              ((n : ℤ) - (d' i : ℤ))).val.obj (op V.1),
            chartSections f I F p V (n : ℤ) ui =
              (Stacks.Blowup.pushforwardReesGradedModulePlus f I F p).smulSection (n : ℤ)
                (chartSections f I F p V (d' i : ℤ) (x' i)) yi := by
        intro i
        by_cases h : d' i ≤ n
        · refine ⟨((cohomologyFunctor (affineBaseChart f V) p).map
              (actHom (I.ideal V) (affineBaseChart f V)
                (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
                  (affineBaseChartModule f F V)) (c i) (d' i : ℤ)
                (by rw [Nat.cast_sub h]; ring))).hom (x' i), ?_,
            ⟨chartReesSection I V (c i) (Nat.cast_sub h), ?_⟩⟩
          · exact of_actHom_gradedCohomologySmul f I F p V
              (show (n - d' i) + d' i = n by omega) (c i) (x' i) _
          · exact ((smul_chartSections f I F p V (d' i) (c i) (x' i) (Nat.cast_sub h)
              (by ring) (by rw [Nat.cast_sub h]; ring)).symm).trans
              (smulSection_apply (Stacks.Blowup.pushforwardReesGradedModulePlus f I F p) (n : ℤ)
                (chartSections f I F p V (d' i : ℤ) (x' i))
                (chartReesSection I V (c i) (Nat.cast_sub h))).symm
        · have hzero : gradedCohomologySmul (I.ideal V) (affineBaseChart f V)
              (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
                (affineBaseChartModule f F V)) p (c i) (x' i) = 0 := by
            rw [hc0 i (not_le.1 h)]
            exact (congrArg (fun φ => ((cohomologyFunctor (affineBaseChart f V) p).map φ).hom
                (x' i))
              (actHom_zero (I.ideal V) (affineBaseChart f V)
                (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
                  (affineBaseChartModule f F V)) (d' i : ℤ)
                (degree_add_eq (n - d' i) (d' i)))).trans
              (cohomologyFunctor_map_zero_apply (affineBaseChart f V) p (x' i))
          refine ⟨0, ?_, ⟨0, ?_⟩⟩
          · rw [hzero, map_zero, map_zero]
          · rw [show chartSections f I F p V (n : ℤ) 0 = 0 from map_zero Φ]
            exact (map_zero ((Stacks.Blowup.pushforwardReesGradedModulePlus f I F p).smulSection
              (n : ℤ) (chartSections f I F p V (d' i : ℤ) (x' i)))).symm
      choose u hu1 hu2 using hukey
      choose y hy2 using hu2
      have hz : z = ∑ i, u i := by
        refine DirectSum.of_injective (β := gradedCohomologyPiece (I.ideal V)
          (affineBaseChart f V) (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
            (affineBaseChartModule f F V)) p) n ?_
        rw [heq, map_sum]
        exact (Finset.sum_congr rfl fun i _ => hu1 i).symm
      exact ⟨y, by
        rw [hz]; exact (map_sum Φ u _).trans (Finset.sum_congr rfl fun i _ => hy2 i)⟩
    · have : Subsingleton (((Stacks.Blowup.pushforwardReesGradedModulePlus f I F p).piece
          k).val.obj (op V.1)) :=
        Stacks.subsingleton_of_isZero
          (isZero_piece_pushforwardReesGradedModulePlus_of_neg f I F p k hk) (op V.1)
      exact fun w => ⟨fun _ => 0, Subsingleton.elim _ _⟩
  -- a finite generating family of the coefficient module in the degree asked for
  have hex : ∀ i : Fin t, ∃ (q : ℕ) (g : Fin q →
      ((Stacks.Blowup.reesGradedAlgebra I).piece (k - (d' i : ℤ))).val.obj (op V.1)),
      Submodule.span ↥(Y.ringCatSheaf.obj.obj (op V.1)) (Set.range g) = ⊤ := fun i =>
    Submodule.fg_iff_exists_fin_generating_family.mp
      (moduleFinite_reesGradedAlgebra_piece_sections I V (k - (d' i : ℤ))).fg_top
  choose qi gi hgi using hex
  refine ⟨Finset.univ.sup qi, fun i j => if h : (j : ℕ) < qi i then gi i ⟨j, h⟩ else 0, ?_⟩
  refine Submodule.eq_top_iff'.2 fun w => ?_
  obtain ⟨y, hy⟩ := hsum w
  rw [hy]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hmem : y i ∈ Submodule.span ↥(Y.ringCatSheaf.obj.obj (op V.1)) (Set.range (gi i)) := by
    rw [hgi i]; exact Submodule.mem_top
  obtain ⟨a, ha⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ↥(Y.ringCatSheaf.obj.obj (op V.1))).1 hmem
  have hexp : (Stacks.Blowup.pushforwardReesGradedModulePlus f I F p).smulSection k
        (chartSections f I F p V (d' i : ℤ) (x' i)) (y i) =
      ∑ jj, a jj • (Stacks.Blowup.pushforwardReesGradedModulePlus f I F p).smulSection k
        (chartSections f I F p V (d' i : ℤ) (x' i)) (gi i jj) := by
    rw [← ha, map_sum]
    exact Finset.sum_congr rfl fun jj _ =>
      smulSection_smul_right (Stacks.Blowup.pushforwardReesGradedModulePlus f I F p) k
        (a jj) (chartSections f I F p V (d' i : ℤ) (x' i)) (gi i jj)
  rw [hexp]
  refine Submodule.sum_mem _ fun jj _ => Submodule.smul_mem _ _ ?_
  refine Submodule.subset_span
    ⟨(i, Fin.castLE (Finset.le_sup (Finset.mem_univ i)) jj), ?_⟩
  simp only [Fin.val_castLE, dite_eq_left jj.isLt]

end Span

/-- **Stacks Project, Tag 02O9.** Let `f : X ⟶ Y` be a morphism of schemes, `ℱ` an `𝒪_X`-module
and `ℐ ⊆ 𝒪_Y` a quasi-coherent sheaf of ideals, and assume `Y` locally Noetherian, `f` proper
and `ℱ` coherent. Then the graded `𝒜 = ⨁ₙ ℐⁿ`-module
`ℳ = ⨁ₙ R ᵖ f_*(ℐⁿℱ) = Stacks.Blowup.pushforwardReesGradedModulePlus f ℐ ℱ p`
is **quasi-coherent** — every homogeneous piece is — and **of finite type** over `𝒜`.

This is the source's own argument. Quasi-coherence of a piece is [Stacks, Tag 01XJ] applied to
`ℐⁿℱ`. Finite type is local on `Y`, and over an affine open `V` it is [Stacks, Tag 02O8] on the
chart `f⁻¹(V) ⟶ Spec Γ(Y, V)`, turned into the spanning family the affine criterion
`SheafOfModules.GradedModule.isFiniteType_of_affine_span` consumes by
`Stacks.Algebraization.exists_affine_span_pushforwardReesGradedModulePlus`.

Quasi-compactness and quasi-separatedness of `f` and quasi-coherence of `ℱ` are consequences of
the source's hypotheses and are derived, not assumed. -/
@[stacks 02O9, ega "III 2.4.2" "special case", sga "2 XII 5.8" "(ii), special case"]
public theorem isQuasicoherent_and_isFiniteType_pushforwardReesGradedModulePlus
    [IsLocallyNoetherian Y] [IsProper f] [F.IsCoherent] :
    (∀ n : ℤ, ((Stacks.Blowup.pushforwardReesGradedModulePlus f I F p).piece n).IsQuasicoherent) ∧
      (Stacks.Blowup.pushforwardReesGradedModulePlus f I F p).IsFiniteType
        (J := Opens.grothendieckTopology Y) := by
  obtain ⟨hqc, -⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  have := hqc
  exact ⟨Stacks.Blowup.isQuasicoherent_piece_pushforwardReesGradedModulePlus f I F p,
    isFiniteType_of_affine_span (Stacks.Blowup.pushforwardReesGradedModulePlus f I F p)
      (Stacks.Blowup.isQuasicoherent_piece_pushforwardReesGradedModulePlus f I F p)
      (exists_affine_span_pushforwardReesGradedModulePlus f I F p)⟩

end Stacks.Algebraization

end
