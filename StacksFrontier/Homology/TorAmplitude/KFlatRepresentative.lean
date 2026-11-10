module

public import StacksFrontier.Homology.KFlat.Basic
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Homology.TorAmplitude.FlatResolution
public import StacksFrontier.Homology.TorAmplitude.Termwise
import StacksCore.Tactic.EgaSgaAttribute

/-!
# One-sided Tor amplitude and K-flat representatives

An object `K` of `D(R)` has Tor amplitude in `[a, ∞]` exactly when it is represented by a K-flat
complex of flat modules concentrated in degrees at least `a`. This is Stacks 0BYL.

## Main results

* `StacksDraft.TorAmplitude.hasTorAmplitudeAbove_iff_exists_kFlat_flat_representative_canonical`:
  Stacks 0BYL, stated for the canonical derived tensor product
  `CochainComplex.DerivedTensor.canonicalDerivedTensorProduct` of Stacks 0BYI.
* `StacksDraft.TorAmplitude.hasTorAmplitudeAbove_iff_exists_kFlat_flat_representative`: the same
  equivalence for an arbitrary certified derived tensor bifunctor. The endpoint above is this
  helper instantiated at the canonical bifunctor.

## Implementation notes

Tor amplitude in `[a, ∞]` is spelled out directly as the vanishing, below `a`, of the cohomology
of `K ⊗ᴸ M[0]` for every module `M`; there is no interval to hand to
`StacksDraft.TorAmplitude.HasTorAmplitude` of Stacks 0652, which is indexed by a finite `[a, b]`.

The argument is carried out for an arbitrary
`CochainComplex.DerivedTensor.DerivedTensorProduct R`, the certified bifunctor of Stacks 064M and
0BYI, rather than for the certified triple of Stacks 0652. The reason is that 0652's certificate
constrains the bifunctor only through its comparison with *termwise* tensoring by a module, and
that comparison is known to be invertible only at a K-projective complex or at a complex which is
bounded **above** with flat terms
(`StacksDraft.TorAmplitude.isIso_comparison_app_of_isKProjective` and
`isIso_comparison_app_of_flat`). The representative produced here is bounded **below**, so neither
applies. A `DerivedTensorProduct` instead carries a comparison at every pair of K-flat complexes,
which is exactly what the representative supplies; the module in the second variable is resolved
by a bounded above complex of projectives, which is K-flat, and K-flatness of the representative
is what lets that resolution be undone again.

Everything is stated over `CochainComplex.KFlat`, which since the collapse of the former
`DerivedTensorProduct.comparison` is itself stated over `CochainComplex.KFlat`, as are the
Tor-amplitude layer's own K-flat helpers, so the whole argument lives at a single universe. The
`KFlatLarge` onto it is the two-universe predicate itself, so no transport across
`CochainComplex.KFlat`, which is that predicate itself.

`tensorSingleIso` below is the value at a single complex of
`StacksDraft.Homology.TorAmplitude.Comparison.termwiseTensorSingleIso`.

## References

* [Stacks Project, Tag 0BYL](https://stacks.math.columbia.edu/tag/0BYL)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

namespace StacksDraft.TorAmplitude

universe u

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-! ### Termwise tensoring versus tensoring with a module in degree zero -/

/-- Termwise tensoring by `M` is naturally isomorphic to the total tensor product with `M`
placed in cohomological degree `0`. -/
private noncomputable def tensorSingleIso (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    StacksDraft.TorAmplitude.Termwise.tensorComplex K M ≅
      (tensorRight ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)).obj K :=
  letI := tensorSingleInclusion_isIso (R := R) M K
  asIso (tensorSingleInclusion M K)

/-! ### Computing the derived tensor product at a K-flat complex -/

/-- At a K-flat complex `E`, a certified derived tensor product agrees with the termwise tensor
product: resolve the module `M` by a bounded above complex `P` of projectives, which is K-flat,
compare `E ⊗ᴸ M[0]` with `E ⊗ P` through the K-flat comparison of the bifunctor, and undo the
resolution using that tensoring on the left with a K-flat complex preserves
quasi-isomorphisms. -/
private theorem isZero_derivedTensor_iff_termwise_of_kFlat
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (K : DerivedCategory (ModuleCat.{u} R)) (E : CochainComplex (ModuleCat.{u} R) ℤ)
    (hE : E.KFlat) (e : K ≅ DerivedCategory.Q.obj E) (M : ModuleCat.{u} R) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        ((T.tensor.obj K).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M))) ↔
      IsZero ((StacksDraft.TorAmplitude.Termwise.tensorComplex E M).homology i) := by
  obtain ⟨P, m, π, hPLE, hPproj, hπ⟩ :=
    exists_projective_resolution ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) 0
  have hPKF : P.KFlat := kFlat_of_isStrictlyLE_projective P m hPproj
  have : QuasiIso ((tensorLeft E).map π) := quasiIso_tensorLeft_map E hE π
  let eM : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) :=
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app M
  let eP : DerivedCategory.Q.obj P ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M :=
    asIso (DerivedCategory.Q.map π) ≪≫ eM.symm
  let iso : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        ((T.tensor.obj K).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)) ≅
      (StacksDraft.TorAmplitude.Termwise.tensorComplex E M).homology i :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
        ((T.tensor.mapIso e).app _ ≪≫ ((T.tensor.obj (DerivedCategory.Q.obj E)).mapIso eP).symm ≪≫
          T.comparison E P hE hPKF) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app ((tensorLeft E).obj P) ≪≫
      asIso (HomologicalComplex.homologyMap ((tensorLeft E).map π) i) ≪≫
      ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).mapIso
        (tensorSingleIso M E)).symm
  exact ⟨fun h => h.of_iso iso.symm, fun h => h.of_iso iso⟩

/-! ### Stacks 0BYL -/

/-- A complex concentrated in degrees at least `a` has termwise tensor products concentrated in
degrees at least `a`, hence no cohomology below `a`. -/
private theorem isZero_termwise_homology_of_isStrictlyGE
    (E : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) [E.IsStrictlyGE a]
    (M : ModuleCat.{u} R) (i : ℤ) (hi : i < a) :
    IsZero ((StacksDraft.TorAmplitude.Termwise.tensorComplex E M).homology i) := by
  apply ShortComplex.isZero_homology_of_isZero_X₂
  exact (tensorRight M).map_isZero (E.isZero_of_isStrictlyGE a i hi)

/-- Vanishing of the termwise tensor cohomology below `a` for every module forces the complex
itself to have no cohomology below `a`: take the module to be `R`, for which termwise tensoring
is the identity. -/
private theorem isGE_of_termwise_vanishing (E : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ)
    (h : ∀ (M : ModuleCat.{u} R) (i : ℤ), i < a →
      IsZero ((StacksDraft.TorAmplitude.Termwise.tensorComplex E M).homology i)) : E.IsGE a := by
  rw [CochainComplex.isGE_iff]
  intro i hi
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  let e : StacksDraft.TorAmplitude.Termwise.tensorComplex E (𝟙_ (ModuleCat.{u} R)) ≅ E :=
    (NatIso.mapHomologicalComplex (rightUnitorNatIso (ModuleCat.{u} R))
      (ComplexShape.up ℤ)).app E ≪≫ (Functor.mapHomologicalComplexIdIso _ _).app E
  exact (h _ i hi).of_iso
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).mapIso e).symm

/-- If the termwise tensor cohomology of a complex of flat modules vanishes in degree `a - 1` for
every module, then the degree-`a` opcycles are flat. -/
private theorem flat_opcycles_of_termwise_vanishing (E : CochainComplex (ModuleCat.{u} R) ℤ)
    (a : ℤ) [Module.Flat R (E.X a)]
    (h : ∀ M : ModuleCat.{u} R, IsZero ((StacksDraft.TorAmplitude.Termwise.tensorComplex E
      M).homology (a - 1))) :
    Module.Flat R (E.opcycles a) := by
  have hinj : ∀ (M : Type u) [AddCommGroup M] [Module R M],
      Function.Injective
        (LinearMap.rTensor M (LinearMap.range (E.d (a - 1) a).hom).subtype) := by
    intro M _ _
    have he := (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (h (ModuleCat.of R M))
    rw [HomologicalComplex.exactAt_iff,
      ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at he
    have he' : Function.Exact
        (LinearMap.rTensor M (E.d ((ComplexShape.up ℤ).prev (a - 1)) (a - 1)).hom)
        (LinearMap.rTensor M (E.d (a - 1) ((ComplexShape.up ℤ).next (a - 1))).hom) := he
    rw [show (ComplexShape.up ℤ).next (a - 1) = a by simp] at he'
    apply StacksDraft.TorAmplitude.Termwise.rTensor_range_subtype_injective_of_exact _ _ _ M he'
    rw [← ModuleCat.hom_comp, E.d_comp_d, ModuleCat.hom_zero]
  have : Module.Flat R
      ((E.X a : ModuleCat.{u} R) ⧸ LinearMap.range (E.d (a - 1) a).hom) :=
    StacksDraft.TorAmplitude.Termwise.flat_quotient_of_rTensor_subtype_injective
      (LinearMap.range (E.d (a - 1) a).hom) hinj
  have : Module.Flat R (cokernel (E.d (a - 1) a) : ModuleCat.{u} R) :=
    Module.Flat.of_linearEquiv
      (ModuleCat.cokernelIsoRangeQuotient (E.d (a - 1) a)).toLinearEquiv
  have e : E.opcycles a ≅ (cokernel (E.d (a - 1) a) : ModuleCat.{u} R) :=
    (E.opcyclesIsCokernel (a - 1) a (by simp)).coconePointUniqueUpToIso
      (colimit.isColimit _)
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

/-- The canonical truncation of a K-flat complex of flat modules with flat opcycles is
K-flat: the kernel of the truncation map is bounded above with flat terms, hence K-flat by
Stacks 064K, and K-flatness passes across the short exact sequence. -/
private theorem kFlat_truncGE (E : CochainComplex (ModuleCat.{u} R) ℤ)
    (hE : E.KFlat) (a : ℤ) [∀ i, Module.Flat R (E.X i)]
    [Module.Flat R (E.opcycles a)] : (E.truncGE a).KFlat := by
  have : Epi (E.πTruncGE a) := by
    dsimp [CochainComplex.πTruncGE]
    infer_instance
  let S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
    ShortComplex.mk (kernel.ι (E.πTruncGE a)) (E.πTruncGE a) (kernel.condition _)
  have hS : S.ShortExact := { exact := S.exact_of_f_is_kernel (kernelIsKernel _) }
  have hf := flat_truncGE E a
  have hL : ∀ i : ℤ, Module.Flat R (S.X₁.X i) := by
    intro i
    have : Module.Flat R ((S.map (HomologicalComplex.eval _ _ i)).X₂) := by
      change Module.Flat R (E.X i)
      infer_instance
    have : Module.Flat R ((S.map (HomologicalComplex.eval _ _ i)).X₃) := hf i
    exact flat_of_shortExact_left (S.map (HomologicalComplex.eval _ _ i)) (hS.map_of_exact _)
  have : S.X₁.IsStrictlyLE a := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    have := isIso_πTruncGE_f E a i hi
    have hSi := hS.map_of_exact (HomologicalComplex.eval _ _ i)
    have := hSi.mono_f
    exact IsZero.of_mono_eq_zero _ (hSi.exact.mono_g_iff.mp (by dsimp [S]; infer_instance))
  exact KFlatTwoOutOfThree.kFlat_X₃ S hS hf (CochainComplex.KFlat.kFlat_of_flat S.X₁ a) hE

/-- An object `K` of `D(R)` has Tor amplitude in `[a, ∞]` if and only if it is represented by a
K-flat complex of flat modules concentrated in degrees at least `a`.

This is the helper quantified over an *arbitrary* certified derived tensor bifunctor `T` in the
sense of Stacks 064M, and it is **not** the Stacks 0BYL endpoint: a statement of the form
`∀ T, P T` does not assert `P` of the canonical derived tensor product. The endpoint is
`StacksDraft.TorAmplitude.hasTorAmplitudeAbove_iff_exists_kFlat_flat_representative_canonical`,
which instantiates this helper at
`CochainComplex.DerivedTensor.canonicalDerivedTensorProduct` (Stacks 0BYI).

See the module docstring for why the certified triple of Stacks 0652 is not used here. -/
public theorem hasTorAmplitudeAbove_iff_exists_kFlat_flat_representative
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (K : DerivedCategory (ModuleCat.{u} R)) (a : ℤ) :
    (∀ (M : ModuleCat.{u} R) (i : ℤ), i < a →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
          ((T.tensor.obj K).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)))) ↔
      ∃ E : CochainComplex (ModuleCat.{u} R) ℤ,
        E.KFlat ∧
          (∀ n : ℤ, Module.Flat R (E.X n)) ∧
          E.IsStrictlyGE a ∧
          Nonempty (K ≅ DerivedCategory.Q.obj E) := by
  constructor
  · intro h
    obtain ⟨P, f, hPlarge, hflat, hf, -⟩ :=
      CochainComplex.KFlat.exists_kFlat_resolution.{u, u}
        (DerivedCategory.Q.objPreimage K)
    have hP : P.KFlat := hPlarge
    have : ∀ i, Module.Flat R (P.X i) := hflat
    let e : K ≅ DerivedCategory.Q.obj P :=
      (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫ (asIso (DerivedCategory.Q.map f)).symm
    have ht : ∀ (M : ModuleCat.{u} R) (i : ℤ), i < a →
        IsZero ((StacksDraft.TorAmplitude.Termwise.tensorComplex P M).homology i) := by
      intro M i hi
      exact (isZero_derivedTensor_iff_termwise_of_kFlat T K P hP e M i).mp (h M i hi)
    have : Module.Flat R (P.opcycles a) :=
      flat_opcycles_of_termwise_vanishing P a (fun M => ht M (a - 1) (by omega))
    have : P.IsGE a := isGE_of_termwise_vanishing P a ht
    exact ⟨P.truncGE a, kFlat_truncGE P hP a, flat_truncGE P a, inferInstance,
      ⟨e ≪≫ asIso (DerivedCategory.Q.map (P.πTruncGE a))⟩⟩
  · rintro ⟨E, hE, hflat, hGE, ⟨e⟩⟩ M i hi
    exact (isZero_derivedTensor_iff_termwise_of_kFlat T K E hE e M i).mpr
      (isZero_termwise_homology_of_isStrictlyGE E a M i hi)

/-- **Stacks 0BYL.** An object `K` of `D(R)` has Tor amplitude in `[a, ∞]` — that is, the derived
tensor product of `K` with any module `M` placed in cohomological degree zero has vanishing
cohomology in all degrees below `a` — if and only if `K` is represented by a K-flat complex of
flat modules concentrated in degrees at least `a`.

The derived tensor product here is *the* canonical one,
`CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R` of Stacks 0BYI, so the statement
is an assertion about a specific bifunctor rather than a claim quantified over certificates.
It is obtained by instantiating
`StacksDraft.TorAmplitude.hasTorAmplitudeAbove_iff_exists_kFlat_flat_representative`, which
proves the equivalence for an arbitrary certified derived tensor bifunctor, at that canonical
choice. -/
@[stacks 0BYL, sga "4 XVII 4.1.9" "ring case, one-sided"]
public theorem hasTorAmplitudeAbove_iff_exists_kFlat_flat_representative_canonical
    (K : DerivedCategory (ModuleCat.{u} R)) (a : ℤ) :
    (∀ (M : ModuleCat.{u} R) (i : ℤ), i < a →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
          (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.obj K).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)))) ↔
      ∃ E : CochainComplex (ModuleCat.{u} R) ℤ,
        E.KFlat ∧
          (∀ n : ℤ, Module.Flat R (E.X n)) ∧
          E.IsStrictlyGE a ∧
          Nonempty (K ≅ DerivedCategory.Q.obj E) :=
  hasTorAmplitudeAbove_iff_exists_kFlat_flat_representative
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R) K a

end StacksDraft.TorAmplitude
