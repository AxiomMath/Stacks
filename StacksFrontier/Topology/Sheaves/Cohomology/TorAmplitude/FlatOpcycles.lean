module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.Embedding.AreComplementary
public import Mathlib.Algebra.Homology.Embedding.TruncLEHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatTwoOutOfThree
public import StacksFrontier.Algebra.Homology.MappingConeDegreewiseIso
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedFlatRepresentative
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatCokernel
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.Triangles

/-!
# The boundary terms of a bounded flat complex on a ringed space are flat

Let `(X, O_X)` be a ringed space and let `P` be a complex of flat `O_X`-modules concentrated in
degrees `[n, b]`. If the canonical truncation `τ_{≥ n+1}P` has Tor amplitude in `[n + 1, b]`,
then both boundary terms of `P` at the bottom of its range are flat `O_X`-modules: the
degree-`n` *cycles* `Ker(P^n ⟶ P^{n+1})`, and the degree-`(n + 1)` *opcycles*
`Coker(P^n ⟶ P^{n+1})`, which is the lowest term of `τ_{≥ n+1}P`.

## Main results

* `Stacks.Cohomology.TorAmplitude.FlatOpcycles.isFlat_homology_of_hasTorAmplitude_of_isLE`: an
  object of `D(O_X)` with no cohomology above `n` whose Tor amplitude starts at `n` has flat
  degree-`n` cohomology.
* `Stacks.Cohomology.TorAmplitude.FlatOpcycles.isFlat_of_hasTorAmplitude_single`: an
  `O_X`-module whose Tor amplitude starts at the degree it sits in is flat.
* `Stacks.Cohomology.TorAmplitude.FlatOpcycles.isFlat_cycles_of_hasTorAmplitude_truncGE`:
  `Z^n(P)` is flat.
* `Stacks.Cohomology.TorAmplitude.FlatOpcycles.isFlat_opcycles_of_hasTorAmplitude_truncGE`:
  `Coker(P^n ⟶ P^{n+1})` is flat.

## Implementation notes

This is the pair of sentences "hence `Ker(d^{a-1})` is flat" and "it follows that
`Tor_1(E', F) = 0` where `E' = Coker(E^{a-1} ⟶ E^a)`, hence `E'` is flat" of the source's proof
of Stacks 08CP, with `a = n + 1`. The ringed-site development runs the same two steps in
`StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/FlatModuleOfTorAmplitude.lean` and
`StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/FlatOpcycles.lean`; the two are kept apart there and together here, because on a ringed
space the two statements share the whole of their input — Tag 08CI and Tag 08CJ (3) at the
ringed-space Tor-amplitude predicate — and neither is used without the other.

The *cycles* half is read off the representative Tag 08CI produces: a complex `K` of flat
`O_X`-modules concentrated in `[n, b]` with `H^i(K) = 0` for `i > n` makes
`0 ⟶ Z^i(K) ⟶ K^i ⟶ Z^{i+1}(K) ⟶ 0` short exact for every `i ≥ n`, and above `b` the cycles
vanish, so Tag 03EY (2) carries flatness down the finitely many degrees from `b + 1` to `n`.
That is `isFlat_cycles_of_isZero_homology`. The canonical truncation triangle
`τ_{≤ n}P ⟶ P ⟶ τ_{≥ n+1}P ⟶ (τ_{≤ n}P)[1]` then carries the Tor amplitude of `P` — in
`[n, b + 1]`, by the easy direction of Tag 08CI — and that of `τ_{≥ n+1}P` onto `τ_{≤ n}P` by
Tag 08CJ (3); and `τ_{≤ n}P` is concentrated in degree `n` with `H^n` the cycles `Z^n(P)`.

The *opcycles* half needs the flat-cokernel criterion of Tag 08CH,
`Stacks.Cohomology.TorAmplitude.FlatCokernel.isFlat_cokernel_of_hasTorAmplitude`, which
produces the flatness of `Coker(d^{a-1})` for a bounded above complex of flat modules whose
image in `D(O_X)` has Tor amplitude in `[a, b]`. None of the complexes already at hand
satisfies all three conditions at once: `P` itself has the right terms but the wrong Tor
amplitude (its cohomology in degree `n` does not vanish after tensoring), while `τ_{≥ n+1}P`
has the right Tor amplitude and the term whose flatness is in question, so applying the
criterion to it would be circular.

The complex that does work is the mapping cone of `P.ιTruncLE n`. Its terms are `Z^n(P)` in
degree `n - 1`, flat by the cycles half, and `P^m` in every degree `m ≥ n`, by
`CochainComplex.mappingCone.isIso_inl_v` and `CochainComplex.mappingCone.isIso_inr_f` — the two
summands `(τ_{≤ n}P)^{m+1}` and `P^m` of the degree-`m` term of the cone vanish for `m ≠ n - 1`
and `m < n` respectively, because `P` is concentrated in degrees `≥ n`. So the cone is a bounded
complex of flat modules, and `CategoryTheory.DerivedCategory.triangleOfSESIso` identifies it in
`D(O_X)` with the third term of the cokernel sequence of `P.ιTruncLE n`, that is with
`τ_{≥ n+1}P`, which is where the Tor-amplitude hypothesis is. Finally `mappingCone.inr` is an
isomorphism in the two degrees `n` and `n + 1`, so the two differentials `P^n ⟶ P^{n+1}` and
`Cone^n ⟶ Cone^{n+1}` have isomorphic cokernels.

Tag 08CJ is available only for the Tor-amplitude predicate of an abstract abelian category with
an abstract triangulated tensoring family (`TorAmplitude.HasTorAmplitude`). The family that
specialises it to a ringed space is `tensorSingleFunctor`, which fixes the second variable of
the derived tensor product at a module placed in degree zero; the two instances the abstract
statement asks of it are the `commShift_left` and `exact_left` fields of the derived tensor
product datum of Tag 06YU.

All three universes of the ringed space coincide, as they already must for
`Stacks.Cohomology.TorAmplitude.HasTorAmplitude`; the derived category's own hom universe stays
independent.

## References

* [Stacks Project, Tag 08CP](https://stacks.math.columbia.edu/tag/08CP)
* [Stacks Project, Tag 08CH](https://stacks.math.columbia.edu/tag/08CH)
* [Stacks Project, Tag 08CI](https://stacks.math.columbia.edu/tag/08CI)
* [Stacks Project, Tag 08CJ](https://stacks.math.columbia.edu/tag/08CJ)
* [Stacks Project, Tag 03EY](https://stacks.math.columbia.edu/tag/03EY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open TopologicalSpace
open StrictlyPerfect AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

namespace Stacks.Cohomology.TorAmplitude.FlatOpcycles

universe u d

variable {X : RingedSpace.{u, u}}

/-- `HasBinaryBiproducts` at the spelling the derived tensor product is stated at. The type is
`OXMod X` by `rfl`, but an instance proved at one spelling does not fire at the other; the
mapping cone below needs it. -/
local instance hasBinaryBiproductsModules : HasBinaryBiproducts (Modules X) :=
  inferInstanceAs (HasBinaryBiproducts (OXMod.{u, u} X))

/-- A zero `O_X`-module is flat. -/
theorem isFlat_of_isZero (M : Modules X) (hM : IsZero M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) M :=
  BoundedFlatRepresentative.isFlat_of_iso
    (IsZero.iso (isZero_kernel_of_mono
      (𝟙 (BoundedFlatRepresentative.structureSheafModule X))) hM)
    (BoundedFlatRepresentative.isFlat_kernel_id_structureSheafModule X)

/-- The cycles in degree `i` of a complex of flat `O_X`-modules vanishing above `b` whose
cohomology vanishes above `n` are a flat `O_X`-module, for every `i ≥ n`.

The induction runs downwards from `b + 1`, where the cycles vanish, through the short exact
sequences `0 ⟶ Z^i ⟶ K^i ⟶ Z^{i + 1} ⟶ 0`. -/
private theorem isFlat_cycles_of_isZero_homology
    (K : CochainComplex (Modules X) ℤ) (n b : ℤ)
    (hflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (K.X i))
    (hLE : ∀ i : ℤ, b < i → IsZero (K.X i))
    (hhom : ∀ i : ℤ, n < i → IsZero (K.homology i)) :
    ∀ (j : ℕ) (i : ℤ), n ≤ i → b + 1 - (j : ℤ) ≤ i →
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (K.cycles i) := by
  intro j
  induction j with
  | zero =>
    intro i _ hi
    exact isFlat_of_isZero _ (IsZero.of_mono (K.iCycles i) (hLE i (by push_cast at hi; omega)))
  | succ j ih =>
    intro i hni hi
    rcases le_or_gt (b + 1 - (j : ℤ)) i with h | h
    · exact ih i hni h
    · have hnext : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
          (K.cycles (i + 1)) :=
        ih (i + 1) (by omega) (by push_cast at hi h ⊢; omega)
      have hiz : K.iCycles i ≫ K.toCycles i (i + 1) = 0 := by
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
      have := hepi
      exact Stacks.SheafOfModules.FlatTwoOutOfThree.isFlat_left_of_shortExact X.sheaf
        (ShortComplex.mk (K.iCycles i) (K.toCycles i (i + 1)) hiz)
        { exact := ShortComplex.exact_of_f_is_kernel _ hker } (hflat i) hnext

variable [HasDerivedCategory.{d} (OXMod.{u} X)]

-- `HasDerivedCategory` at the spelling of Stacks 06YU: the type is `OXMod X` by `rfl`, but
-- `structureSheafOfRings` is not reducible, so an instance proved at one spelling does not fire
-- at the other. Seated here, not restated.
attribute [local instance] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

/-! ### Formal properties of the Tor-amplitude predicate -/

/-- **Widening the interval weakens Tor amplitude.** -/
theorem hasTorAmplitude_mono {E : DerivedCategory (Modules X)} {a b a' b' : ℤ}
    (h : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X E a b) (ha : a' ≤ a) (hb : b ≤ b') :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X E a' b' := fun F i hi =>
  h F i (by simp only [Set.mem_Icc, not_and_or, not_le] at hi ⊢; omega)

/-- **Tor amplitude is invariant under isomorphism in `D(O_X)`.** -/
theorem hasTorAmplitude_of_iso {E E' : DerivedCategory (Modules X)} {a b : ℤ}
    (h : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X E a b) (e : E' ≅ E) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X E' a b := fun F i hi =>
  (h F i hi).of_iso
    ((DerivedCategory.homologyFunctor (Modules X) i).mapIso
      (((Stacks.Cohomology.TorAmplitude.derTensor X).tensor.mapIso e).app
        ((DerivedCategory.singleFunctor (Modules X) 0).obj F)))

/-- **Derived tensoring with a module placed in degree zero, as an endofunctor of `D(O_X)`.**
This is the second variable of the derived tensor product of Tag 06YU fixed at `F[0]`; it is
the family at which the abstract form of Tag 08CJ is stated. -/
abbrev tensorSingleFunctor (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u} X)]
    (F : Modules X) : DerivedCategory (Modules X) ⥤ DerivedCategory (Modules X) :=
  (Stacks.Cohomology.TorAmplitude.derTensor X).tensor.flip.obj
    ((DerivedCategory.singleFunctor (Modules X) 0).obj F)

/-- **Tag 08CJ (3) at the ringed-space Tor-amplitude predicate.** In a distinguished triangle
`K ⟶ L ⟶ M ⟶ K[1]` of `D(O_X)`, if `L` has Tor amplitude in `[a + 1, b + 1]` and `M` has Tor
amplitude in `[a, b]`, then `K` has Tor amplitude in `[a + 1, b + 1]`.

This is `TorAmplitude.hasTorAmplitude_obj₁` read through `tensorSingleFunctor`; the only
content is the translation between the two encodings of "outside `[a, b]`". -/
theorem hasTorAmplitude_obj₁ (T : Triangle (DerivedCategory (Modules X)))
    (hT : T ∈ distinguishedTriangles) (a b : ℤ)
    (hL : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X T.obj₂ (a + 1) (b + 1))
    (hM : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X T.obj₃ a b) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X T.obj₁ (a + 1) (b + 1) := by
  have h := @TorAmplitude.hasTorAmplitude_obj₁ (Modules X) _ _ _ (tensorSingleFunctor X)
    (fun F => (Stacks.Cohomology.TorAmplitude.derTensor X).commShift_left
      ((DerivedCategory.singleFunctor (Modules X) 0).obj F))
    (fun F => (Stacks.Cohomology.TorAmplitude.derTensor X).exact_left
      ((DerivedCategory.singleFunctor (Modules X) 0).obj F))
    T hT a b
    (fun F i hi => hL F i (by simp only [Set.mem_Icc, not_and_or, not_le]; omega))
    (fun F i hi => hM F i (by simp only [Set.mem_Icc, not_and_or, not_le]; omega))
  exact fun F i hi => h F i (by simp only [Set.mem_Icc, not_and_or, not_le] at hi; omega)

/-- The third term of the cokernel sequence of `P.ιTruncLE n` is isomorphic in `D(O_X)` to
`τ_{≥ n+1}P`, so it inherits its Tor amplitude. -/
private theorem hasTorAmplitude_shortComplexTruncLE_X₃
    (P : CochainComplex (Modules X) ℤ) (n a b : ℤ)
    (hamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X
      (DerivedCategory.Q.obj (P.truncGE (n + 1))) a b) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X
      (DerivedCategory.Q.obj (P.shortComplexTruncLE n).X₃) a b := by
  have hφ : IsIso (DerivedCategory.Q.map (P.shortComplexTruncLEX₃ToTruncGE n (n + 1) rfl)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := Modules X) _).2 inferInstance
  exact hasTorAmplitude_of_iso hamp (@asIso _ _ _ _ _ hφ)

/-! ### The cycles -/

/-- **An object with no cohomology above `n` whose Tor amplitude starts at `n` has flat top
cohomology.** If `E` is `≤ n` for the canonical t-structure and has Tor amplitude in `[n, b]`,
then `H^n(E)` is a flat `O_X`-module.

Tag 08CI gives a complex `K` of flat `O_X`-modules concentrated in `[n, b]` representing `E`;
its cohomology vanishes above `n`, so `Z^n(K) ≅ H^n(K) ≅ H^n(E)` is flat by the downward
induction through the short exact sequences `0 ⟶ Z^i ⟶ K^i ⟶ Z^{i + 1} ⟶ 0`. -/
theorem isFlat_homology_of_hasTorAmplitude_of_isLE
    (E : DerivedCategory (Modules X)) (n b : ℤ) [E.IsLE n]
    (hamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X E n b) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      ((DerivedCategory.homologyFunctor (Modules X) n).obj E) := by
  have hamp' : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X E n (max b n) :=
    hasTorAmplitude_mono hamp le_rfl (le_max_left b n)
  obtain ⟨K, hflat, hzero, ⟨e⟩⟩ :=
    BoundedFlatRepresentative.exists_flat_representative_of_hasTorAmplitude E n (max b n)
      (le_max_right b n) hamp'
  have hhom : ∀ i : ℤ, n < i → IsZero (K.homology i) := by
    intro i hi
    exact (E.isZero_of_isLE n i hi).of_iso
      (((DerivedCategory.homologyFunctorFactors (Modules X) i).app K).symm ≪≫
        (DerivedCategory.homologyFunctor (Modules X) i).mapIso e)
  have hGE : K.IsStrictlyGE n := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi => hzero i (by simp only [Set.mem_Icc, not_and_or, not_le]; omega)
  have hd : K.d (n - 1) n = 0 :=
    (K.isZero_of_isStrictlyGE n (n - 1) (by omega)).eq_of_src _ _
  have hcyc := isFlat_cycles_of_isZero_homology K n (max b n) hflat
    (fun i hi => hzero i (by simp only [Set.mem_Icc, not_and_or, not_le]; omega)) hhom
    (max b n + 1 - n).toNat n le_rfl (by omega)
  exact BoundedFlatRepresentative.isFlat_of_iso
    (K.isoHomologyπ (n - 1) n (by simp) hd ≪≫
      ((DerivedCategory.homologyFunctorFactors (Modules X) n).app K).symm ≪≫
      (DerivedCategory.homologyFunctor (Modules X) n).mapIso e) hcyc

/-- **A module whose Tor amplitude starts at the degree it sits in is flat.** If the
`O_X`-module `N`, placed in degree `n`, has Tor amplitude in `[n, b]`, then `N` is flat.

This is `isFlat_homology_of_hasTorAmplitude_of_isLE` read through
`DerivedCategory.singleFunctorCompHomologyFunctorIso`, which identifies the degree-`n`
cohomology of `N[-n]` with `N`. -/
theorem isFlat_of_hasTorAmplitude_single (N : Modules X) (n b : ℤ)
    (hamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X
      ((DerivedCategory.singleFunctor (Modules X) n).obj N) n b) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) N :=
  BoundedFlatRepresentative.isFlat_of_iso
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules X) n).app N)
    (isFlat_homology_of_hasTorAmplitude_of_isLE _ n b hamp)

/-- **The bottom cycles of a bounded complex of flat `O_X`-modules are flat as soon as the
canonical truncation above the bottom degree has Tor amplitude starting one degree higher.**

Let `P` be a complex of flat `O_X`-modules concentrated in `[n, b]` and suppose `τ_{≥ n+1}P` has
Tor amplitude in `[n + 1, b]`. Then `Z^n(P)` is a flat `O_X`-module.

This is the step which makes `Ker(d_P^{a-1})` flat in the source's proof of Stacks 08CP, with
`n = a - 1`: the canonical truncation triangle
`τ_{≤ n}P ⟶ P ⟶ τ_{≥ n+1}P ⟶ (τ_{≤ n}P)[1]`, which is `DerivedCategory.triangleOfSES` of the
cokernel sequence of `P.ιTruncLE n`, carries the Tor amplitude of `P` — in `[n, b + 1]`, by the
easy direction of Tag 08CI — and of `τ_{≥ n+1}P` onto `τ_{≤ n}P` by Tag 08CJ (3); and
`τ_{≤ n}P` is concentrated in degree `n` with `H^n` the cycles `Z^n(P)`. -/
theorem isFlat_cycles_of_hasTorAmplitude_truncGE
    (P : CochainComplex (Modules X) ℤ) (n b : ℤ)
    [P.IsStrictlyGE n] [P.IsStrictlyLE b]
    (hflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (P.X i))
    (hamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X
      (DerivedCategory.Q.obj (P.truncGE (n + 1))) (n + 1) b) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (P.cycles n) := by
  have hSE := P.shortComplexTruncLE_shortExact n
  have hP : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X
      (DerivedCategory.Q.obj P) (n - 1 + 1) (b + 1) :=
    Stacks.TorAmplitude.FlatRepresentative.hasTorAmplitude_of_flat_representative
      _ (n - 1 + 1) (b + 1) P hflat
      (fun i hi => by
        simp only [Set.mem_Icc, not_and_or, not_le] at hi
        rcases hi with h | h
        · exact P.isZero_of_isStrictlyGE n i (by omega)
        · exact P.isZero_of_isStrictlyLE b i (by omega))
      (Iso.refl _)
  have hX₃ := hasTorAmplitude_shortComplexTruncLE_X₃ P n (n - 1) b
    (hasTorAmplitude_mono hamp (by omega) le_rfl)
  have h₁ : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X
      (DerivedCategory.Q.obj (P.truncLE n)) n (b + 1) := by
    have h := hasTorAmplitude_obj₁ (DerivedCategory.triangleOfSES hSE)
      (DerivedCategory.triangleOfSES_distinguished hSE) (n - 1) b hP hX₃
    rw [show n - 1 + 1 = n by omega] at h
    exact h
  have hdnext : (P.truncLE n).d n (n + 1) = 0 :=
    IsZero.eq_of_tgt ((P.truncLE n).isZero_of_isStrictlyLE n (n + 1) (by omega)) _ _
  have hdprev : (P.truncLE n).d (n - 1) n = 0 :=
    IsZero.eq_of_src
      ((P.isZero_of_isStrictlyGE n (n - 1) (by omega)).of_iso (P.truncLEXIso n (n - 1))) _ _
  exact BoundedFlatRepresentative.isFlat_of_iso
    (((DerivedCategory.homologyFunctorFactors (Modules X) n).app (P.truncLE n)) ≪≫
      (P.truncLE n).isoHomologyι n (n + 1) (by simp) hdnext ≪≫
      ((P.truncLE n).pOpcyclesIso (n - 1) n (by simp) hdprev).symm ≪≫
      P.truncLEXIsoCycles n)
    (isFlat_homology_of_hasTorAmplitude_of_isLE _ n (b + 1) h₁)

/-! ### The opcycles -/

/-- **The opcycles in the bottom degree of the canonical truncation of a bounded complex of flat
`O_X`-modules are flat, as soon as that truncation has Tor amplitude starting there.**

Let `P` be a complex of flat `O_X`-modules concentrated in degrees `[n, b]` and suppose that
`τ_{≥ n+1}P` has Tor amplitude in `[n + 1, b]`. Then `Coker(P^n ⟶ P^{n+1})` is a flat
`O_X`-module.

This is the step which makes the lowest term of the complex
`Coker(E^{a-1} ⟶ E^a) ⟶ E^{a+1} ⟶ … ⟶ E^b` of the source's proof of Stacks 08CP flat, with
`n = a - 1`. -/
theorem isFlat_opcycles_of_hasTorAmplitude_truncGE
    (P : CochainComplex (Modules X) ℤ) (n b : ℤ)
    [P.IsStrictlyGE n] [P.IsStrictlyLE b]
    (hflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (P.X i))
    (hamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X
      (DerivedCategory.Q.obj (P.truncGE (n + 1))) (n + 1) b) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      (P.opcycles (n + 1)) := by
  have hcyc := isFlat_cycles_of_hasTorAmplitude_truncGE P n b hflat hamp
  have hSE := P.shortComplexTruncLE_shortExact n
  -- the truncation `τ_{≤ n}P` is concentrated in the single degree `n`
  have hFzero : ∀ i : ℤ, i ≠ n → IsZero ((P.truncLE n).X i) := by
    intro i hi
    rcases lt_or_gt_of_ne hi with h | h
    · exact (P.isZero_of_isStrictlyGE n i h).of_iso (P.truncLEXIso n i h)
    · exact (P.truncLE n).isZero_of_isStrictlyLE n i h
  -- away from degree `n - 1` the cone is the complex `P` itself
  have hinr : ∀ m : ℤ, m ≠ n - 1 →
      IsIso ((CochainComplex.mappingCone.inr (P.ιTruncLE n)).f m) := fun m hm =>
    CochainComplex.mappingCone.isIso_inr_f _ m (hFzero (m + 1) (by omega))
  -- the cone has flat terms
  have hpq : n + (-1) = n - 1 := by omega
  have hextflat : ∀ m : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
        ((CochainComplex.mappingCone (P.ιTruncLE n)).X m) := by
    intro m
    by_cases hm : m = n - 1
    · subst hm
      have hiso : IsIso ((CochainComplex.mappingCone.inl (P.ιTruncLE n)).v n (n - 1) hpq) :=
        CochainComplex.mappingCone.isIso_inl_v _ n (n - 1) hpq
          (P.isZero_of_isStrictlyGE n (n - 1) (by omega))
      exact BoundedFlatRepresentative.isFlat_of_iso
        ((P.truncLEXIsoCycles n).symm ≪≫ @asIso _ _ _ _ _ hiso) hcyc
    · exact BoundedFlatRepresentative.isFlat_of_iso
        (@asIso _ _ _ _ _ (hinr m hm)) (hflat m)
  -- the cone is bounded above
  have hextLE : (CochainComplex.mappingCone (P.ιTruncLE n)).IsStrictlyLE (max b n) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro m hm
    rw [max_lt_iff] at hm
    exact (P.isZero_of_isStrictlyLE b m (by omega)).of_iso
      (@asIso _ _ _ _ _ (hinr m (by omega))).symm
  -- in `D(O_X)` the cone is the canonical truncation, which carries the Tor-amplitude hypothesis
  have hampCone : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X
      ((DerivedCategory.Q (C := Modules X)).obj
        (CochainComplex.mappingCone (P.ιTruncLE n))) (n + 1) b := by
    exact hasTorAmplitude_of_iso (hasTorAmplitude_shortComplexTruncLE_X₃ P n (n + 1) b hamp)
      (Triangle.π₃.mapIso (DerivedCategory.triangleOfSESIso hSE)).symm
  have hcoker := FlatCokernel.isFlat_cokernel_of_hasTorAmplitude
    (CochainComplex.mappingCone (P.ιTruncLE n)) (n + 1) b ⟨max b n, hextLE⟩ hextflat hampCone
  rw [show n + 1 - 1 = n from by omega] at hcoker
  -- the two differentials out of degree `n` have isomorphic cokernels
  have ecoker : cokernel (P.d n (n + 1)) ≅
      cokernel ((CochainComplex.mappingCone (P.ιTruncLE n)).d n (n + 1)) :=
    cokernel.mapIso (f := P.d n (n + 1))
      (f' := (CochainComplex.mappingCone (P.ιTruncLE n)).d n (n + 1))
      (p := @asIso _ _ _ _ _ (hinr n (by omega)))
      (q := @asIso _ _ _ _ _ (hinr (n + 1) (by omega)))
      (w := ((CochainComplex.mappingCone.inr (P.ιTruncLE n)).comm n (n + 1)).symm)
  have eop : P.opcycles (n + 1) ≅ cokernel (P.d n (n + 1)) :=
    IsColimit.coconePointUniqueUpToIso (P.opcyclesIsCokernel n (n + 1) (by simp))
      (colimit.isColimit _)
  exact BoundedFlatRepresentative.isFlat_of_iso (ecoker.symm ≪≫ eop.symm) hcoker

end Stacks.Cohomology.TorAmplitude.FlatOpcycles

end
