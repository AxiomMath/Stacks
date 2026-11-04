module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.Embedding.AreComplementary
public import Mathlib.Algebra.Homology.Embedding.TruncLEHomology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.DistinguishedTriangles
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tor amplitude starting at the top degree makes the top cohomology flat

Let `(C, O)` be a ringed site, let `T` be a derived tensor product on `D(O)` and let `E` be an
object of `D(O)` with no cohomology above `n` whose Tor amplitude starts at `n`. Then the
cohomology sheaf `H^n(E)` is a flat `O`-module. In particular an `O`-module `N` placed in degree
`n` whose Tor amplitude is `[n, b]` is flat.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.isFlat_homology_of_hasTorAmplitude_of_isLE`: if
  `E` is `≤ n` and has Tor amplitude in `[n, b]` then `H^n(E)` is flat.
* `Stacks.SheafOfModules.DerivedTensorProduct.isFlat_of_hasTorAmplitude_single`: a module whose
  Tor amplitude starts at the degree it sits in is flat.
* `Stacks.SheafOfModules.DerivedTensorProduct.isFlat_cycles_of_hasTorAmplitude_truncGE`: the
  bottom cycles `Z^n(P)` of a complex `P` of flat `O`-modules concentrated in `[n, b]` are flat
  when `τ_{≥ n+1}P` has Tor amplitude in `[n + 1, b]`.

## Implementation notes

Stacks 08G1 represents `E` by a complex `K` of flat `O`-modules concentrated in `[n, b]`; the
hypothesis that `E` has no cohomology above `n` then makes
`0 ⟶ Z^n(K) ⟶ K^n ⟶ K^{n + 1} ⟶ … ⟶ K^b ⟶ 0` an exact sequence of `O`-modules whose terms
other than the first are flat, and `H^n(E) ≅ Z^n(K)` because `K` vanishes below `n`.

Flatness of `Z^n(K)` is read off that sequence by a downward induction on the finitely many
degrees between `n` and `b`: above `b` the cycles vanish, and
`0 ⟶ Z^i(K) ⟶ K^i ⟶ Z^{i + 1}(K) ⟶ 0` is short exact for every `i ≥ n`, exact at the middle
because the cycles are the kernel of the differential and surjective on the right because
`H^{i + 1}(K)` vanishes. So Stacks 03EY (2),
`Stacks.SheafOfModules.FlatTwoOutOfThree.isFlat_left_of_shortExact`, carries flatness from
`Z^{i + 1}(K)` and `K^i` to `Z^i(K)`.

No hypothesis `n ≤ b` is needed: for `b < n` the interval is empty, so the Tor amplitude
hypothesis is the stronger statement for the interval `[n, n]`, and the upper bound is replaced
by `max b n` at the start of the proof.

The universe of the sections is `max u v`, as for Stacks 08G1 itself: the representative is
produced there, and that is where the unit law which bounds the cohomology of `E` lives.

## References

* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 03EY](https://stacks.math.columbia.edu/tag/03EY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v d

namespace Stacks.SheafOfModules.DerivedTensorProduct

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {Y : RingedSite.{u, v, max u v}}
  [HasSheafify Y.J AddCommGrpCat.{max u v}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, max u v} Y)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} Y.O).obj
    M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, max u v} Y) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

omit [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, max u v} Y)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} Y.O).obj
    M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, max u v} Y) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- The cycles in degree `i` of a complex of flat `O`-modules concentrated in `[n, b]` whose
cohomology vanishes above `n` are a flat `O`-module, for every `i ≥ n`.

The induction runs downwards from `b + 1`, where the cycles vanish, through the short exact
sequences `0 ⟶ Z^i ⟶ K^i ⟶ Z^{i + 1} ⟶ 0`. -/
@[sga "4 XVII 4.1.1" "(i), special case"]
private theorem isFlat_cycles_of_isZero_homology
    (K : CochainComplex (RingedSite.Modules.{u, v, max u v} Y) ℤ) (n b : ℤ)
    (hflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v, max u v} (O := Y.O) (K.X i))
    (hLE : ∀ i : ℤ, b < i → IsZero (K.X i))
    (hhom : ∀ i : ℤ, n < i → IsZero (K.homology i)) :
    ∀ (j : ℕ) (i : ℤ), n ≤ i → b + 1 - (j : ℤ) ≤ i →
      AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v, max u v} (O := Y.O)
        (K.cycles i) := by
  intro j
  induction j with
  | zero =>
    intro i _ hi
    exact isFlat_of_isZero _ (IsZero.of_mono (K.iCycles i) (hLE i (by omega)))
  | succ j ih =>
    intro i hni hi
    rcases le_or_gt (b + 1 - (j : ℤ)) i with h | h
    · exact ih i hni h
    · have hiz : K.iCycles i ≫ K.toCycles i (i + 1) = 0 := by
        rw [← cancel_mono (K.iCycles (i + 1)), Category.assoc, K.toCycles_i, zero_comp,
          K.iCycles_d i (i + 1)]
      have hepi : Epi (K.toCycles i (i + 1)) :=
        Preadditive.epi_of_isZero_cokernel' _ (K.homologyIsCokernel i (i + 1) (by simp))
          (hhom (i + 1) (by omega))
      have hker : IsLimit (KernelFork.ofι (K.iCycles i) hiz) :=
        KernelFork.IsLimit.ofι' _ _ fun {_} k hk =>
          ⟨K.liftCycles k (i + 1) (by simp)
            (by rw [← K.toCycles_i i (i + 1), ← Category.assoc, hk, zero_comp]),
            K.liftCycles_i _ _ _ _⟩
      exact FlatTwoOutOfThree.isFlat_left_of_shortExact Y.O
        (ShortComplex.mk (K.iCycles i) (K.toCycles i (i + 1)) hiz)
        { exact := ShortComplex.exact_of_f_is_kernel _ hker } (hflat i)
        (ih (i + 1) (by omega) (by omega))

/-- An object with no cohomology above `n` whose Tor amplitude starts at `n` has flat top
cohomology: if `E` is `≤ n` for the canonical t-structure and has Tor amplitude in `[n, b]`
for a derived tensor product `T`, then `H^n(E)` is a flat `O`-module.

Stacks 08G1 gives a complex `K` of flat `O`-modules concentrated in `[n, b]` representing `E`;
its cohomology vanishes above `n`, so `Z^n(K) ≅ H^n(K) ≅ H^n(E)` is flat by the downward
induction through the short exact sequences `0 ⟶ Z^i ⟶ K^i ⟶ Z^{i + 1} ⟶ 0`. -/
theorem isFlat_homology_of_hasTorAmplitude_of_isLE
    (T : DerivedTensorProduct.{u, v, max u v, d} Y)
    (E : RingedSite.DerivedModules.{u, v, max u v, d} Y) (n b : ℤ) [E.IsLE n]
    (hamp : HasTorAmplitude T E n b) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v, max u v} (O := Y.O)
      ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, max u v} Y) n).obj E) := by
  have hamp' : HasTorAmplitude T E n (max b n) := fun F i hi =>
    hamp F i (by simp only [Set.mem_Icc, not_and_or, not_le, le_max_iff] at hi ⊢; omega)
  obtain ⟨K, hflat, hzero, ⟨e⟩⟩ :=
    exists_flatRepresentative_of_hasTorAmplitude T E n (max b n) (le_max_right b n) hamp'
  have eH (i : ℤ) : K.homology i ≅
      (DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, max u v} Y) i).obj E :=
    ((DerivedCategory.homologyFunctorFactors
        (RingedSite.Modules.{u, v, max u v} Y) i).app K).symm ≪≫
      (DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, max u v} Y) i).mapIso e
  have hGE : K.IsStrictlyGE n := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi => hzero i (Set.notMem_Icc_of_lt hi)
  have hcyc := isFlat_cycles_of_isZero_homology K n (max b n) hflat
    (fun i hi => hzero i (Set.notMem_Icc_of_gt hi))
    (fun i hi => (E.isZero_of_isLE n i hi).of_iso (eH i))
    (max b n + 1 - n).toNat n le_rfl (by omega)
  exact FlatRetract.isFlat_of_iso Y.O
    (K.isoHomologyπ (n - 1) n (by simp)
        ((K.isZero_of_isStrictlyGE n (n - 1) (by omega)).eq_of_src _ _) ≪≫ eH n) hcyc

/-- A module whose Tor amplitude starts at the degree it sits in is flat: if the `O`-module
`N`, placed in degree `n`, has Tor amplitude in `[n, b]` for a derived tensor product `T`, then
`N` is flat.

This is `isFlat_homology_of_hasTorAmplitude_of_isLE` read through
`DerivedCategory.singleFunctorCompHomologyFunctorIso`, which identifies the degree-`n`
cohomology of `N[-n]` with `N`. -/
theorem isFlat_of_hasTorAmplitude_single (T : DerivedTensorProduct.{u, v, max u v, d} Y)
    (N : RingedSite.Modules.{u, v, max u v} Y) (n b : ℤ)
    (hamp : HasTorAmplitude T
      ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, max u v} Y) n).obj N) n b) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v, max u v} (O := Y.O) N :=
  FlatRetract.isFlat_of_iso Y.O
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (RingedSite.Modules.{u, v, max u v} Y) n).app N)
    (isFlat_homology_of_hasTorAmplitude_of_isLE T _ n b hamp)

/-- The bottom cycles of a bounded complex of flat `O`-modules are flat as soon as the
canonical truncation above the bottom degree has Tor amplitude starting one degree higher.

Let `P` be a complex of flat `O`-modules concentrated in `[n, b]` and suppose `τ_{≥ n+1}P` has
Tor amplitude in `[n + 1, b]`. Then `Z^n(P)` is a flat `O`-module.

This is the step which makes `Ker(d_P^{a-1})` flat in the source's proof of Stacks 08G7, with
`n = a - 1`: the canonical truncation triangle
`τ_{≤ n}P ⟶ P ⟶ τ_{≥ n+1}P ⟶ (τ_{≤ n}P)[1]`, which is
`DerivedCategory.triangleOfSES` of the cokernel sequence of `P.ιTruncLE n`, carries the Tor
amplitude of `P` — in `[n, b + 1]`, by the easy direction of Stacks 08G1 — and of
`τ_{≥ n+1}P` onto `τ_{≤ n}P` by Stacks 08G2 (3); and `τ_{≤ n}P` is concentrated in degree `n`
with `H^n` the cycles `Z^n(P)`, so `isFlat_homology_of_hasTorAmplitude_of_isLE` applies. -/
theorem isFlat_cycles_of_hasTorAmplitude_truncGE
    (T : DerivedTensorProduct.{u, v, max u v, d} Y)
    (P : CochainComplex (RingedSite.Modules.{u, v, max u v} Y) ℤ) (n b : ℤ)
    [P.IsStrictlyGE n] [P.IsStrictlyLE b]
    (hflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v, max u v} (O := Y.O) (P.X i))
    (hamp : HasTorAmplitude T (DerivedCategory.Q.obj (P.truncGE (n + 1))) (n + 1) b) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v, max u v} (O := Y.O)
      (P.cycles n) := by
  have hSE := P.shortComplexTruncLE_shortExact n
  have hP : HasTorAmplitude T (DerivedCategory.Q.obj P) (n - 1 + 1) (b + 1) :=
    hasTorAmplitude_of_flatRepresentative T _ (n - 1 + 1) (b + 1) P hflat
      (fun i hi => by
        simp only [Set.mem_Icc, not_and_or, not_le] at hi
        rcases hi with h | h
        · exact P.isZero_of_isStrictlyGE n i (by omega)
        · exact P.isZero_of_isStrictlyLE b i (by omega))
      (Iso.refl _)
  have hX₃ : HasTorAmplitude T
      (DerivedCategory.Q.obj (P.shortComplexTruncLE n).X₃) (n - 1) b := by
    refine (hamp.mono (by omega) le_rfl).of_iso ?_
    let φ := P.shortComplexTruncLEX₃ToTruncGE n (n + 1) (by omega)
    have : IsIso (DerivedCategory.Q.map φ) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso
        (C := RingedSite.Modules.{u, v, max u v} Y) φ).2 inferInstance
    exact (asIso (DerivedCategory.Q.map φ)).symm
  have h₁ : HasTorAmplitude T (DerivedCategory.Q.obj (P.truncLE n)) n (b + 1) := by
    have h := hasTorAmplitude_obj₁ T (DerivedCategory.triangleOfSES hSE)
      (DerivedCategory.triangleOfSES_distinguished hSE) (n - 1) b hP hX₃
    rwa [show n - 1 + 1 = n by omega] at h
  have hdnext : (P.truncLE n).d n (n + 1) = 0 :=
    IsZero.eq_of_tgt ((P.truncLE n).isZero_of_isStrictlyLE n (n + 1) (by omega)) _ _
  have hdprev : (P.truncLE n).d (n - 1) n = 0 :=
    IsZero.eq_of_src
      ((P.isZero_of_isStrictlyGE n (n - 1) (by omega)).of_iso (P.truncLEXIso n (n - 1))) _ _
  exact FlatRetract.isFlat_of_iso Y.O
    (((DerivedCategory.homologyFunctorFactors
        (RingedSite.Modules.{u, v, max u v} Y) n).app (P.truncLE n)) ≪≫
      (P.truncLE n).isoHomologyι n (n + 1) (by simp) hdnext ≪≫
      ((P.truncLE n).pOpcyclesIso (n - 1) n (by simp) hdprev).symm ≪≫
      P.truncLEXIsoCycles n)
    (isFlat_homology_of_hasTorAmplitude_of_isLE T _ n (b + 1) h₁)

end Stacks.SheafOfModules.DerivedTensorProduct

end
