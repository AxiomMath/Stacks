module

public import StacksFrontier.AlgebraicGeometry.Algebraization.ClosedFibreMixedComponents
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceOneImmediateSpecialization
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumSpecialization
public import StacksFrontier.RingTheory.Catenary.Formal
public import StacksFrontier.RingTheory.Dualizing.UniversallyCatenary
public import StacksFrontier.RingTheory.Spectrum.Prime.NestedQuotientZeroLocus

/-!
# The closed fibre of a closure, read in `Y` and read in `Spec(A/𝔭)`

Work in the standing situation of [Stacks, Tag 0EHC]: a Noetherian ring `A` with ideals
`I ⊆ 𝔞`, `X = Spec(A)`, `Y = V(I)`, `Z = V(𝔞)` and `U = X ∖ Z`. Fix a point `x` of `U` and let
`𝔭` be the prime of `A` it names, so that `W = V(𝔭)` is the closure of `x` in `X`.

The crossing-point lemma
`Stacks.Algebraization.exists_specializes_krullDimToEInt_le_of_mixed_irreducibleComponents`
reads the closed fibre `W ∩ Y` *inside* `W = Spec(A/𝔭)`, as the zero locus of `I(A/𝔭)`, whereas
the statement of [Stacks, Tag 0EJ5] reads it *inside* `Y`, as the closed fibre
`Yι⁻¹(closure {x})`. This file supplies the identification of the two readings and runs the rest
of the proof of [Stacks, Tag 0EJ5] through it, up to the point of `U` at distance one.

## Main results

* `Stacks.Algebraization.closedFibre_closure_eq_zeroLocus` — the closed fibre of the closure of
  `x`, read in `Y`, is the zero locus of `𝔭(A/I)`.
* `Stacks.Algebraization.closedFibreClosureHomeo` — the homeomorphism from the closed fibre read
  in `Spec(A/𝔭)` to the closed fibre read in `Y`.
* `Stacks.Algebraization.closedFibreClosureHomeo_mem_closedSubsetZ_iff` — it carries the locus
  cut out by `𝔞(A/𝔭)` to the trace of `Z`.
* `Stacks.Algebraization.mixed_irreducibleComponents_of_closure_closedFibre` — the transfer of
  the mixed-components hypothesis from the `Y` framing to the `Spec(A/𝔭)` framing.
* `Stacks.Algebraization.exists_distanceToZ_eq_one_specializes_of_mixed_irreducibleComponents` —
  mixed components on the closed fibre of `closure {x}` produce a point `y` of `U`
  specializing from `x`, lying over a point of `Y` at distance exactly `1` from `Z`, with
  `height(𝔭_y(A/𝔭_x)) ≤ d`.

## Implementation notes

### Two readings of one closed fibre

The closed fibre of `closure {x} = V(𝔭)` is the set of primes of `A` containing `I ⊔ 𝔭`. Read in
`Y = Spec(A/I)` it is `V(𝔭(A/I))`, and read in `W = Spec(A/𝔭)` it is `V(I(A/𝔭))`; these are the
two nested quotients of `PrimeSpectrum.nestedQuotientZeroLocusHomeo`, which is a homeomorphism
that does not move the underlying prime of `A`. Composing it with the identification of
`Yι⁻¹(closure {x})` with `V(𝔭(A/I))` gives `closedFibreClosureHomeo`, and the fact that the
underlying prime does not move is what makes
`closedFibreClosureHomeo_mem_closedSubsetZ_iff` — and with it the transfer of the
mixed-components hypothesis — a statement about one containment of ideals read two ways, via
`Ideal.map_le_iff_le_comap`.

### Why the height bound, and why `d` rather than `d + 1`

The crossing point `z` produced over `A/𝔭` has `dim((A/𝔭)_z) ≤ cd(A, I) + 1 ≤ d + 1`. The point
actually wanted is the immediate generalization `r` of `z` inside the closed fibre but outside
`Z` supplied by [Stacks, Tag 02IM]; since `r < z` strictly, its height is at most `d`. That is
the bound the depth inequalities of chapter 52 are fed, and it is stated here as a height in
`A/𝔭_x`, i.e. as the codimension of `y` inside `closure {x}`.

### No `@[stacks 0EJ5]` attribute

This is the geometric half of the glue for [Stacks, Tag 0EJ5]: it produces the point of `U` at
distance one, but not the identification of `depth(ℱ_x)` with a depth of the completed stalk
that the tag also needs. The attribute is therefore placed elsewhere.

## References

* [Stacks Project, Tag 0EJ5](https://stacks.math.columbia.edu/tag/0EJ5), the statement being
  assembled.
* [Stacks Project, Tag 0EG5](https://stacks.math.columbia.edu/tag/0EG5), the connectedness
  lemma behind the crossing point.
* [Stacks Project, Tag 02IM](https://stacks.math.columbia.edu/tag/02IM), the immediate
  generalization inside a locally closed set.
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC), the standing
  situation.
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-! ### The closed fibre of a closure, read in `Y` -/

/-- **The closed fibre of the closure of a point of `U`, read in `Y`, is a zero locus.** For
`x ∈ U` with underlying prime `𝔭`, the closure of `x` in `X = Spec(A)` is `V(𝔭)`, so a point `y`
of `Y = Spec(A/I)` lies over it exactly when `𝔭` is contained in the contraction of `y` to `A`,
which by `Ideal.map_le_iff_le_comap` says that `y` lies in the zero locus of `𝔭(A/I)`. -/
public theorem closedFibre_closure_eq_zeroLocus (S : AlgebraizationSituation.{u})
    (x : S.U.toScheme) :
    S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X) =
      PrimeSpectrum.zeroLocus
        (((S.U.ι.base x).asIdeal.map (Ideal.Quotient.mk S.I) : Ideal (S.A ⧸ S.I)) :
          Set (S.A ⧸ S.I)) := by
  have hclos : closure ({S.U.ι.base x} : Set S.X) =
      PrimeSpectrum.zeroLocus ((S.U.ι.base x).asIdeal : Set S.A) :=
    PrimeSpectrum.closure_singleton _
  rw [hclos]
  ext y
  have hmemL : S.Yι.base y ∈ PrimeSpectrum.zeroLocus ((S.U.ι.base x).asIdeal : Set S.A) ↔
      (S.U.ι.base x).asIdeal ≤
        Ideal.comap (Ideal.Quotient.mk S.I) (y : PrimeSpectrum (S.A ⧸ S.I)).asIdeal := Iff.rfl
  have hmemR : y ∈ PrimeSpectrum.zeroLocus
      (((S.U.ι.base x).asIdeal.map (Ideal.Quotient.mk S.I) : Ideal (S.A ⧸ S.I)) :
        Set (S.A ⧸ S.I)) ↔
      (S.U.ι.base x).asIdeal.map (Ideal.Quotient.mk S.I) ≤
        (y : PrimeSpectrum (S.A ⧸ S.I)).asIdeal := Iff.rfl
  exact hmemL.trans (hmemR.trans Ideal.map_le_iff_le_comap).symm

/-- **The closed fibre of `closure {x}` is homeomorphic read in `Spec(A/𝔭_x)` and read in `Y`.**
Both describe the primes of `A` containing `I ⊔ 𝔭_x`: the first as the zero locus of `I(A/𝔭_x)`,
the second — by `Stacks.Algebraization.closedFibre_closure_eq_zeroLocus` — as the zero locus of
`𝔭_x(A/I)`. The identification is `PrimeSpectrum.nestedQuotientZeroLocusHomeo`, which leaves the
underlying prime of `A` unchanged. -/
public def closedFibreClosureHomeo (S : AlgebraizationSituation.{u}) (x : S.U.toScheme) :
    ↥(PrimeSpectrum.zeroLocus ((S.I.map (Ideal.Quotient.mk (S.U.ι.base x).asIdeal) :
        Ideal (S.A ⧸ (S.U.ι.base x).asIdeal)) : Set (S.A ⧸ (S.U.ι.base x).asIdeal)))
      ≃ₜ ↥(S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)) :=
  (PrimeSpectrum.nestedQuotientZeroLocusHomeo S.I (S.U.ι.base x).asIdeal).trans
    (Homeomorph.setCongr (closedFibre_closure_eq_zeroLocus S x).symm)

/-- **`closedFibreClosureHomeo` does not move the underlying prime of `A`.** A point `w` of the
closed fibre read in `Spec(A/𝔭_x)` and its image in `Y` contract to the same prime of `A`; this
is `PrimeSpectrum.nestedQuotientZeroLocusHomeo_comap`, the identification of
`closedFibre_closure_eq_zeroLocus` being a mere change of the ambient set. -/
public theorem comap_closedFibreClosureHomeo (S : AlgebraizationSituation.{u})
    (x : S.U.toScheme)
    (w : ↥(PrimeSpectrum.zeroLocus ((S.I.map (Ideal.Quotient.mk (S.U.ι.base x).asIdeal) :
      Ideal (S.A ⧸ (S.U.ι.base x).asIdeal)) : Set (S.A ⧸ (S.U.ι.base x).asIdeal)))) :
    ((closedFibreClosureHomeo S x w).1 : PrimeSpectrum (S.A ⧸ S.I)).asIdeal.comap
        (Ideal.Quotient.mk S.I) =
      w.1.asIdeal.comap (Ideal.Quotient.mk (S.U.ι.base x).asIdeal) :=
  PrimeSpectrum.nestedQuotientZeroLocusHomeo_comap S.I (S.U.ι.base x).asIdeal w

/-- **`closedFibreClosureHomeo` carries the locus cut out by `𝔞(A/𝔭_x)` to the trace of `Z`.** A
point `w` of the closed fibre read in `Spec(A/𝔭_x)` satisfies `𝔞(A/𝔭_x) ≤ w` exactly when its
image in `Y` lies in the closed subset `Z = V(𝔞(A/I))`: both say that `𝔞` is contained in the
prime of `A` that `w` and its image both name, which is `comap_closedFibreClosureHomeo` read
through `Ideal.map_le_iff_le_comap`. -/
public theorem closedFibreClosureHomeo_mem_closedSubsetZ_iff (S : AlgebraizationSituation.{u})
    (x : S.U.toScheme)
    (w : ↥(PrimeSpectrum.zeroLocus ((S.I.map (Ideal.Quotient.mk (S.U.ι.base x).asIdeal) :
      Ideal (S.A ⧸ (S.U.ι.base x).asIdeal)) : Set (S.A ⧸ (S.U.ι.base x).asIdeal)))) :
    (closedFibreClosureHomeo S x w).1 ∈ (S.closedSubsetZ : Set S.Y) ↔
      S.a.map (Ideal.Quotient.mk (S.U.ι.base x).asIdeal) ≤ w.1.asIdeal := by
  have hL : (closedFibreClosureHomeo S x w).1 ∈ (S.closedSubsetZ : Set S.Y) ↔
      S.a.map (Ideal.Quotient.mk S.I) ≤
        ((closedFibreClosureHomeo S x w).1 : PrimeSpectrum (S.A ⧸ S.I)).asIdeal :=
    Iff.rfl
  rw [hL, Ideal.map_le_iff_le_comap, comap_closedFibreClosureHomeo,
    ← Ideal.map_le_iff_le_comap]

/-- **The trace of `Z` on the closed fibre pulls back to the locus cut out by `𝔞(A/𝔭_x)`.** The
set form of `Stacks.Algebraization.closedFibreClosureHomeo_mem_closedSubsetZ_iff`, with
membership of `Z` phrased — as in the statement of [Stacks, Tag 0EJ5] — as lying in the image of
the closed immersion `Z ⟶ X` after pushing forward to `X`. -/
public theorem preimage_closedFibreClosureHomeo_range_Zι (S : AlgebraizationSituation.{u})
    (x : S.U.toScheme) :
    closedFibreClosureHomeo S x ⁻¹' {y | S.Yι.base y.1 ∈ Set.range S.Zι.base} =
      {w | S.a.map (Ideal.Quotient.mk (S.U.ι.base x).asIdeal) ≤ w.1.asIdeal} := by
  ext w
  exact (mem_closedSubsetZ_iff_mem_range_Zι S (closedFibreClosureHomeo S x w).1).symm.trans
    (closedFibreClosureHomeo_mem_closedSubsetZ_iff S x w)

/-- Pulling an irreducible component back along a homeomorphism gives an irreducible
component. -/
private lemma preimage_mem_irreducibleComponents_of_homeomorph {T T' : Type*}
    [TopologicalSpace T] [TopologicalSpace T'] (e : T ≃ₜ T') (C : Set T')
    (hC : C ∈ irreducibleComponents T') : e ⁻¹' C ∈ irreducibleComponents T := by
  obtain ⟨t, ht⟩ := hC.1.nonempty
  exact preimage_mem_irreducibleComponents hC e.isOpenEmbedding
    ⟨t, ht, e.symm t, e.apply_symm_apply t⟩

/-- **The mixed-components hypothesis of [Stacks, Tag 0EJ5] transferred to `Spec(A/𝔭_x)`.** If
some irreducible component of the closed fibre of `closure {x}`, read in `Y`, lies inside `Z` and
some does not, then the same holds for the closed fibre read in `Spec(A/𝔭_x)` and the locus cut
out there by `𝔞(A/𝔭_x)`. Components are carried back along `closedFibreClosureHomeo`, under which
the trace of `Z` pulls back to that locus. -/
public theorem mixed_irreducibleComponents_of_closure_closedFibre
    (S : AlgebraizationSituation.{u}) (x : S.U.toScheme)
    (hmixed :
      (∃ C : Set ↥(S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)),
          C ∈ irreducibleComponents ↥(S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)) ∧
            C ⊆ {y | S.Yι.base y.1 ∈ Set.range S.Zι.base}) ∧
        ∃ C : Set ↥(S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)),
          C ∈ irreducibleComponents ↥(S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)) ∧
            ¬ C ⊆ {y | S.Yι.base y.1 ∈ Set.range S.Zι.base}) :
    (let W : Set (PrimeSpectrum (S.A ⧸ (S.U.ι.base x).asIdeal)) :=
        PrimeSpectrum.zeroLocus ((S.I.map (Ideal.Quotient.mk (S.U.ι.base x).asIdeal) :
          Ideal (S.A ⧸ (S.U.ι.base x).asIdeal)) : Set (S.A ⧸ (S.U.ι.base x).asIdeal))
      let Zc : Set W :=
        {w | S.a.map (Ideal.Quotient.mk (S.U.ι.base x).asIdeal) ≤ w.1.asIdeal}
      (∃ C, C ∈ irreducibleComponents W ∧ C ⊆ Zc) ∧
        ∃ C, C ∈ irreducibleComponents W ∧ ¬ C ⊆ Zc) := by
  have hpre := preimage_closedFibreClosureHomeo_range_Zι S x
  refine ⟨?_, ?_⟩
  · obtain ⟨C, hC, hCZ⟩ := hmixed.1
    refine ⟨closedFibreClosureHomeo S x ⁻¹' C,
      preimage_mem_irreducibleComponents_of_homeomorph _ C hC, ?_⟩
    rw [← hpre]
    exact Set.preimage_mono hCZ
  · obtain ⟨C, hC, hCZ⟩ := hmixed.2
    refine ⟨closedFibreClosureHomeo S x ⁻¹' C,
      preimage_mem_irreducibleComponents_of_homeomorph _ C hC, fun hsub => hCZ ?_⟩
    rw [← hpre] at hsub
    exact (closedFibreClosureHomeo S x).surjective.preimage_subset_preimage_iff.mp hsub

/-! ### The point of `U` at distance one -/

/-- A Krull dimension bounded in the extended integers by an ordinary integer `m` is finite and
at most `m.toNat`: the value `⊤` is excluded because `⊤ ≤ m` fails in the extended integers. -/
private lemma le_toNat_of_krullDimToEInt_le {h : ℕ∞} {m : ℤ}
    (hle : krullDimToEInt ((h : ℕ∞) : WithBot ℕ∞) ≤ ((m : ℤ) : EInt)) :
    h ≤ (m.toNat : ℕ∞) := by
  induction h using ENat.recTopCoe with
  | top =>
    rw [show krullDimToEInt ((⊤ : ℕ∞) : WithBot ℕ∞) = (⊤ : EInt) from rfl] at hle
    simp at hle
  | coe n =>
    rw [show krullDimToEInt (((n : ℕ) : ℕ∞) : WithBot ℕ∞) = ((n : ℤ) : EInt) from rfl] at hle
    have := WithBotTop.coe_le_coe.mp hle
    exact_mod_cast (show n ≤ m.toNat by omega)

/-- **Stacks 0EJ5, the point of `U` at distance one.** Let `I ⊆ 𝔞` be ideals of a Noetherian
ring `A` which is `I`-adically complete and has a dualizing complex with `cd(A, I) ≤ d`, and let
`x` be a point of `U = Spec(A) ∖ V(𝔞)`. Suppose that on the closed fibre of `closure {x}` — the
part of `Y = V(I)` lying over `closure {x}` — some irreducible component lies inside `Z = V(𝔞)`
and some does not. Then there is a point `y` of `U` with `x ⤳ y`, lying over a point `r` of `Y`
at distance exactly `1` from `Z`, whose codimension in `closure {x}` is at most `d`.

The crossing point `z` over `A/𝔭_x` of
`Stacks.Algebraization.exists_specializes_krullDimToEInt_le_of_mixed_irreducibleComponents`,
together with the generic point `η` of a component avoiding `Z`, is transported into `Y` along
`Stacks.Algebraization.closedFibreClosureHomeo`. Applying [Stacks, Tag 02IM] to the locally
closed set "closed fibre minus `Z`", which contains `η` and whose closure contains `z`, produces
an immediate generalization `r` of `z` there; it is at distance exactly `1` from `Z` by
`Stacks.Algebraization.distanceFunction_eq_one_of_isImmediateSpecialization_of_notMem`, whose
catenary hypothesis comes from the dualizing complex through [Stacks, Tag 0A80]. Since `r` is a
*strict* generalization of `z` and `dim((A/𝔭_x)_z) ≤ d + 1`, the height of `r` in `A/𝔭_x` is at
most `d`. -/
public theorem exists_distanceToZ_eq_one_specializes_of_mixed_irreducibleComponents
    (S : AlgebraizationSituation.{u}) [IsAdicComplete S.I S.A]
    (K : DerivedCategory (ModuleCat.{u} S.A)) (hK : Dualizing.IsDualizingComplex K)
    (d : ℤ)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      S.I.fg_of_isNoetherianRing ≤ d)
    (x : S.U.toScheme)
    (hmixed :
      (∃ C : Set ↥(S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)),
          C ∈ irreducibleComponents ↥(S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)) ∧
            C ⊆ {y | S.Yι.base y.1 ∈ Set.range S.Zι.base}) ∧
        ∃ C : Set ↥(S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)),
          C ∈ irreducibleComponents ↥(S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)) ∧
            ¬ C ⊆ {y | S.Yι.base y.1 ∈ Set.range S.Zι.base}) :
    ∃ (y : S.U.toScheme) (r : S.Y),
      S.U.ι.base y = S.Yι.base r ∧
      S.distanceToZ r = 1 ∧
      x ⤳ y ∧
      Ideal.height ((S.U.ι.base y).asIdeal.map
        (Ideal.Quotient.mk (S.U.ι.base x).asIdeal)) ≤ (d.toNat : ℕ∞) := by
  classical
  have : ((S.U.ι.base x).asIdeal).IsPrime := (S.U.ι.base x).2
  obtain ⟨z, η, hIη, hηa, hηz, haz, hzdim⟩ :=
    exists_specializes_krullDimToEInt_le_of_mixed_irreducibleComponents S.A S.I S.a
      (S.U.ι.base x).asIdeal K hK d hcd
      (mixed_irreducibleComponents_of_closure_closedFibre S x hmixed)
  have : z.asIdeal.IsPrime := z.2
  have hηmem : η ∈ PrimeSpectrum.zeroLocus
      ((S.I.map (Ideal.Quotient.mk (S.U.ι.base x).asIdeal) :
        Ideal (S.A ⧸ (S.U.ι.base x).asIdeal)) : Set (S.A ⧸ (S.U.ι.base x).asIdeal)) :=
    (PrimeSpectrum.mem_zeroLocus _ _).mpr hIη
  have hzmem := ((PrimeSpectrum.le_iff_specializes η z).mp hηz).mem_closed
    (PrimeSpectrum.isClosed_zeroLocus _) hηmem
  -- The crossing point and the generic point, read in `Y`.
  have hzZ : (closedFibreClosureHomeo S x ⟨z, hzmem⟩).1 ∈ (S.closedSubsetZ : Set S.Y) :=
    (closedFibreClosureHomeo_mem_closedSubsetZ_iff S x ⟨z, hzmem⟩).mpr haz
  have hηZ : (closedFibreClosureHomeo S x ⟨η, hηmem⟩).1 ∉ (S.closedSubsetZ : Set S.Y) :=
    fun hmem => hηa ((closedFibreClosureHomeo_mem_closedSubsetZ_iff S x ⟨η, hηmem⟩).mp hmem)
  have hspec : (closedFibreClosureHomeo S x ⟨η, hηmem⟩).1 ⤳
      (closedFibreClosureHomeo S x ⟨z, hzmem⟩).1 :=
    (((subtype_specializes_iff ⟨η, hηmem⟩ ⟨z, hzmem⟩).2
      ((PrimeSpectrum.le_iff_specializes η z).mp hηz)).map
        (closedFibreClosureHomeo S x).continuous).map continuous_subtype_val
  have hne : (closedFibreClosureHomeo S x ⟨η, hηmem⟩).1 ≠
      (closedFibreClosureHomeo S x ⟨z, hzmem⟩).1 := fun hEq => hηZ (hEq ▸ hzZ)
  -- The closed fibre minus `Z` is locally closed, so [Stacks, Tag 02IM] applies inside it.
  have hWY : IsClosed (S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)) :=
    isClosed_closure.preimage S.Yι.continuous
  have hE : IsLocallyClosed ((S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)) \
      (S.closedSubsetZ : Set S.Y)) := by
    rw [Set.sdiff_eq]
    exact hWY.isLocallyClosed.inter S.closedSubsetZ.isClosed.isOpen_compl.isLocallyClosed
  obtain ⟨r, hrE, hrimm⟩ :=
    AlgebraicGeometry.exists_isImmediateSpecialization_mem_of_isLocallyClosed S.Y hE
      ⟨(closedFibreClosureHomeo S x ⟨η, hηmem⟩).2, hηZ⟩ hspec hne
  -- The distance of `r` from `Z` is exactly one.
  have : Algebra.FiniteType S.A (S.A ⧸ S.I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ S.A S.I) Ideal.Quotient.mk_surjective
  have hYcat : IrreducibleClosedsCodim.IsCatenarySpace S.Y :=
    isCatenarySpace_of_isCatenary
      (Dualizing.isUniversallyCatenary_of_isDualizingComplex hK (S.A ⧸ S.I))
  have hdist : S.distanceToZ r = 1 :=
    distanceFunction_eq_one_of_isImmediateSpecialization_of_notMem S.Y S.closedSubsetZ hYcat
      hrimm hzZ hrE.2
  -- Outside `Z`, the image of `r` in `X` lies in `U`.
  have hrange : Set.range S.Zι.base = PrimeSpectrum.zeroLocus (S.a : Set S.A) := by
    have h := _root_.range_comap_of_surjective (S.A ⧸ S.a) (Ideal.Quotient.mk S.a)
      Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker] at h
    exact h
  have hrU : S.Yι.base r ∈ S.U := by
    have hnot : S.Yι.base r ∉ Set.range S.Zι.base := fun hmem =>
      hrE.2 ((mem_closedSubsetZ_iff_mem_range_Zι S r).mpr hmem)
    rw [hrange] at hnot
    exact hnot
  -- `r`, read back in `Spec(A/𝔭_x)`.
  obtain ⟨rB, hrB⟩ : ∃ w, closedFibreClosureHomeo S x w = ⟨r, hrE.1⟩ :=
    ⟨(closedFibreClosureHomeo S x).symm _, (closedFibreClosureHomeo S x).apply_symm_apply _⟩
  have hrBr : (closedFibreClosureHomeo S x rB).1 = r := congrArg Subtype.val hrB
  refine ⟨⟨S.Yι.base r, hrU⟩, r, rfl, hdist, ?_, ?_⟩
  · exact S.U.ι.isOpenEmbedding.isEmbedding.specializes_iff.mp
      (specializes_iff_mem_closure.mpr hrE.1)
  -- The height bound: `r` is a strict generalization of the crossing point `z`.
  have hrz : rB.1.asIdeal < z.asIdeal := by
    have hspecB : rB ⤳ ⟨z, hzmem⟩ := by
      have h := ((subtype_specializes_iff (closedFibreClosureHomeo S x rB)
        (closedFibreClosureHomeo S x ⟨z, hzmem⟩)).2 (hrBr ▸ hrimm.1)).map
          (closedFibreClosureHomeo S x).symm.continuous
      rwa [(closedFibreClosureHomeo S x).symm_apply_apply,
        (closedFibreClosureHomeo S x).symm_apply_apply] at h
    refine lt_of_le_of_ne
      ((PrimeSpectrum.le_iff_specializes rB.1 z).mpr
        ((subtype_specializes_iff rB ⟨z, hzmem⟩).1 hspecB)) fun hEq => hrimm.2.1 ?_
    rw [← hrBr, show rB = (⟨z, hzmem⟩ : _) from Subtype.ext (PrimeSpectrum.ext hEq)]
  have hzheight : z.asIdeal.height ≤ ((d.toNat + 1 : ℕ) : ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height z.asIdeal
      (Localization.AtPrime z.asIdeal)] at hzdim
    refine (le_toNat_of_krullDimToEInt_le hzdim).trans ?_
    exact Nat.cast_le.mpr (by omega)
  have hrheight := (Ideal.height_le_iff.mp hzheight) rB.1.asIdeal rB.1.2 hrz
  have hfinal : rB.1.asIdeal.height ≤ (d.toNat : ℕ∞) :=
    (ENat.lt_add_one_iff (ENat.natCast_ne_top d.toNat)).mp (by simpa using hrheight)
  have hmap : (S.U.ι.base (⟨S.Yι.base r, hrU⟩ : S.U.toScheme)).asIdeal.map
      (Ideal.Quotient.mk (S.U.ι.base x).asIdeal) = rB.1.asIdeal := by
    have hcm : ((closedFibreClosureHomeo S x rB).1 : PrimeSpectrum (S.A ⧸ S.I)).asIdeal.comap
        (Ideal.Quotient.mk S.I) =
        rB.1.asIdeal.comap (Ideal.Quotient.mk (S.U.ι.base x).asIdeal) :=
      comap_closedFibreClosureHomeo S x rB
    rw [hrBr] at hcm
    have hy : (S.U.ι.base (⟨S.Yι.base r, hrU⟩ : S.U.toScheme)).asIdeal =
        rB.1.asIdeal.comap (Ideal.Quotient.mk (S.U.ι.base x).asIdeal) := hcm
    rw [hy, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  rw [hmap]
  exact hfinal

end Stacks.Algebraization

end
