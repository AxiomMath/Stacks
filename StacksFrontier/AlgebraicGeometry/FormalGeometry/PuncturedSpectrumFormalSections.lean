module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AssociatedPointInductionComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonLinearity
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalLocusTagInjectivity
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationMaximalIdeal
import StacksCore.Tactic.StacksAttribute

/-!
# Formal sections of a coherent module on the punctured spectrum of a local ring

Let `(A, 𝔪)` be a Noetherian local ring which has a dualizing complex and is complete with
respect to an ideal `I`. Put `X = Spec(A)`, `Y = V(I)` and `U = X ∖ {𝔪}`, and let `ℱ` be a
coherent module on `U`. Stacks 0DXR asserts that, when every associated point `x ∈ U` of `ℱ`
satisfies `dim(closure {x}) > cd(A, I) + 1` with the closure taken in `X`, the canonical map

`colim_V H⁰(V, ℱ) ⟶ lim_n H⁰(U, ℱ / Iⁿ ℱ)`,

the colimit being over the opens `V ⊆ U` containing `U ∩ Y`, is an isomorphism of finite
`A`-modules.

This file is the part of that statement which is available without any unproved input. The
open `U` of the source is `Stacks.LocalCohomology.complementZeroLocus A 𝔪`, the two sides of
the displayed map are `Stacks.Algebraization.sectionsNearVanishing` and
`Stacks.Algebraization.formalSections` at `𝔞 = 𝔪`, and the map itself is
`Stacks.Algebraization.comparisonMap`.

Four things are proved here. First, that the substrate really is the source's `U`: the
complement of `V(𝔪)` is the complement of the closed point. Second, that the source's
dimension hypothesis, stated with `dim(closure {x}) = dim(A/𝔭)` exactly as the source states
it, is condition (2) of Stacks 0EG2 at `𝔞 = 𝔪` — the two differ by the local dimension
`dim(𝒪_{closure {x}, z})` at the points `z` of `closure {x} ∩ V(𝔪)`, and in a local ring the
only such `z` is the closed point, where the two agree. Third, the injectivity half of the
conclusion, which holds with no hypothesis beyond `A` Noetherian and `ℱ` coherent. Fourth, that
the conclusion holds in the category of `A`-modules and not merely in the category of abelian
groups: the source asserts an isomorphism *of finite `A`-modules*, the two sides of the
displayed map are `A`-modules by
`StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonLinearity`, the displayed map is
`A`-linear, and it is injective as a map of `A`-modules.

## Main definitions

None; this file only proves statements about the existing substrate.

## Main results

* `Stacks.Algebraization.closureLocalDimension_closedPoint` — in a local ring the local
  dimension of `closure {x}` at the closed point is `dim(A/𝔭)`.
* `Stacks.Algebraization.associatedPointsClosureDimensionBound_maximalIdeal` — the source's
  dimension hypothesis gives condition (2) of Stacks 0EG2 at `𝔞 = 𝔪`.
* `Stacks.Algebraization.bootstrapHypotheses_maximalIdeal` — the hypotheses of Stacks 0DXR
  give the hypotheses of Stacks 0EG2 at `𝔞 = 𝔪`.
* `Stacks.Algebraization.mono_comparisonMap_maximalIdeal` — the injectivity half of the
  conclusion of Stacks 0DXR.
* `Stacks.Algebraization.mono_comparisonModuleMap_maximalIdeal` — the injectivity half again,
  in the category of `A`-modules: the two sides of the displayed map are `A`-modules and the
  map is `A`-linear, which is the form the source's conclusion takes.
* `Stacks.Algebraization.isIso_comparisonMap_maximalIdeal_iff_realized` — the other half
  of the conclusion, reduced to the realization of every formal section on a single
  neighbourhood of `U ∩ Y`.

## Implementation notes

The source proves Stacks 0DXR by applying Stacks 0DXQ with `s = 1`, which also yields the
finiteness of the two modules. The *hypothesis* half of that application is carried out, at the
source's own hypotheses, in
`StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedSpectrumFormalSectionsFiniteness`: with
`ℱ = M̃|_U` for a finite module `M` as in Stacks 0BK0 (1), 0DXR's dimension hypothesis gives the
hypotheses of Stacks 0DXP and of Stacks 0DXQ at `s = 1` and `d = cd(A, I)`, together with the
extra finiteness assumption of the latter. Both conclusions follow there: the ideal `J₀` of
Stacks 0DXP, so that `H^i_J(M) ⟶ H^i(RΓ_𝔪(M)^∧)` is an isomorphism in degrees `i ≤ 1` for every
`J ⊆ J₀` with `V(J) ∩ V(I) = {𝔪}`, and the finiteness of `H⁰(X ∖ V(J), M̃)` for every such `J`.
The finiteness clause of Stacks 0DXQ is unconditional —
`Stacks.Algebraization.PuncturedNeighbourhood.finite_neighbourhoodCohomology` *constructs* the
stabilizing data of Stacks 0EFI from assumption (1) rather than assuming it.

The other half of the conclusion rests on one statement, the *comparison* clause of
Stacks 0DXQ at `i = 0`: that the comparison at a single small neighbourhood,
`Stacks.Algebraization.comparisonAt A I 𝔪 ℱ V`, is surjective for some
`V : Stacks.Algebraization.OpensNearVanishing A I (maximalIdeal A)`. Everything else is formal.
That clause is
`Stacks.Algebraization.surjective_comparisonAt_ofZeroLocusInter` of
`ComparisonAtAdicLimit.lean`, and with it the whole of Stacks 0DXR is
`Stacks.Algebraization.isIso_comparisonModuleMap_and_finite_maximalIdeal` of
`PuncturedSpectrumFormalSectionsWhole.lean`.
That map factors `Stacks.Algebraization.comparisonMap` through the colimit inclusion, by
`Stacks.Algebraization.colimit_ι_comp_comparisonMap`, so its surjectivity makes the displayed
map surjective; with the injectivity proved here the displayed map is an isomorphism; each
transition map `H⁰(V, ℱ) ⟶ H⁰(V', ℱ)` below `V` is then an isomorphism, because both legs to
the limit are; the colimit therefore collapses onto `H⁰(V, ℱ)`, whose finiteness is the
statement proved in the module named above; and the finiteness of the limit follows across the
isomorphism.

The route through Stacks 0EG2 at `𝔞 = 𝔪` is prepared here as well: everything on the hypothesis
side of it is discharged, so along that route the isomorphism needs exactly the three inputs
`Stacks.Algebraization.isIso_comparisonMap` carries — Stacks 0EIF, the middle clause of
Stacks 0H48, and the associated-point splitting.

What the `A`-module structures add is the *statability* of the finiteness clause, not the
clause itself: before them the two sides of the displayed map were objects of `Ab`, about which
`Module.Finite A` is not a statement. They are not enough to prove it. The finiteness clause of
Stacks 0DXQ with `s = 1` is about `H⁰(V, ℱ)` for a single small `V`, and a filtered colimit of
finite `A`-modules along injective maps need not be finite, so neither the injectivity proved
here nor that finiteness substitutes for the collapse of the colimit described above.

By `Stacks.Algebraization.isIso_comparisonModuleMap_iff` the `A`-module isomorphism of the
source follows from the isomorphism of abelian groups with no further work, so the surjectivity
half is the whole of what the conclusion turns on; it is proved in
`PuncturedSpectrumFormalSectionsWhole.lean`.

The comparison of a Krull dimension with an integer bound goes through
`Stacks.Algebraization.krullDimToEInt`, which is the idiom condition (2) of Stacks 0EG2 is
already phrased with.

## References

* [Stacks Project, Tag 0DXR](https://stacks.math.columbia.edu/tag/0DXR)
* [Stacks Project, Tag 0DXQ](https://stacks.math.columbia.edu/tag/0DXQ)
* [Stacks Project, Tag 0DXP](https://stacks.math.columbia.edu/tag/0DXP)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-! ### The punctured spectrum as the complement of a zero locus -/

/-- The open `U = Spec(A) ∖ V(𝔪)` of the algebraization statements is the punctured spectrum
of the local ring `A`: the zero locus of the maximal ideal is the closed point. -/
public theorem coe_complementZeroLocus_maximalIdeal (A : Type u) [CommRing A] [IsLocalRing A] :
    ((complementZeroLocus A (maximalIdeal A) : (Spec (.of A)).Opens) : Set (Spec (.of A))) =
      {closedPoint A}ᶜ :=
  congrArg compl zeroLocus_maximalIdeal

/-! ### The local dimension of a closure at the closed point -/

/-- In a local ring the primes lying between `𝔭` and the maximal ideal are exactly the primes
containing `𝔭`, the upper bound being automatic. -/
private def closedPointIntervalOrderIso (A : Type u) [CommRing A] [IsLocalRing A]
    (x : PrimeSpectrum A) :
    {p : PrimeSpectrum A //
        x.asIdeal ≤ p.asIdeal ∧ p.asIdeal ≤ (closedPoint A).asIdeal} ≃o
      (PrimeSpectrum.zeroLocus (R := A) (x.asIdeal : Set A)) where
  toFun p := ⟨p.1, (PrimeSpectrum.mem_zeroLocus _ _).2 p.2.1⟩
  invFun p := ⟨p.1, (PrimeSpectrum.mem_zeroLocus _ _).1 p.2,
    IsLocalRing.le_maximalIdeal_of_isPrime p.1.asIdeal⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- **The local dimension of a closure at the closed point of a local ring.** For a prime `𝔭`
of a local ring `A` the dimension `dim(𝒪_{closure {𝔭}, 𝔪})` of the local ring of
`closure {𝔭} = V(𝔭)` at the closed point is the dimension `dim(A/𝔭)` of the whole of
`closure {𝔭}`, because every prime of `A` is contained in `𝔪`. -/
public theorem closureLocalDimension_closedPoint (A : Type u) [CommRing A] [IsLocalRing A]
    (x : PrimeSpectrum A) :
    closureLocalDimension A x (closedPoint A) = ringKrullDim (A ⧸ x.asIdeal) := by
  rw [ringKrullDim,
    Order.krullDim_eq_of_orderIso x.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus]
  exact Order.krullDim_eq_of_orderIso (closedPointIntervalOrderIso A x)

/-! ### The hypotheses of Stacks 0DXR give those of Stacks 0EG2 at `𝔞 = 𝔪` -/

/-- An `I`-adically complete local ring has `I` inside its maximal ideal: `I` is contained in
the Jacobson radical, which is the maximal ideal. -/
public theorem le_maximalIdeal_of_isAdicComplete (A : Type u) [CommRing A] [IsLocalRing A]
    (I : Ideal A) (hcomplete : IsAdicComplete I A) : I ≤ maximalIdeal A := by
  have := hcomplete
  exact (IsAdicComplete.le_jacobson_bot I).trans (sInf_le ⟨bot_le, inferInstance⟩)

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (I : Ideal A)
  (F : (complementZeroLocus A (maximalIdeal A) : Scheme).Modules)

/-- **The dimension hypothesis of Stacks 0DXR is condition (2) of Stacks 0EG2 at `𝔞 = 𝔪`.**
Condition (2) asks for `dim(𝒪_{closure {x}, z}) > cd(A, I) + 1` at every point `z` of
`closure {x} ∩ V(𝔪)`; in a local ring the only such `z` is the closed point, and there that
local dimension is the dimension `dim(A/𝔭)` of the whole closure, which is the invariant the
source's hypothesis is stated with. -/
public theorem associatedPointsClosureDimensionBound_maximalIdeal
    (hdim : ∀ x : (complementZeroLocus A (maximalIdeal A) : Scheme),
      x ∈ Stacks.Divisors.associatedPoints F →
      ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
        krullDimToEInt (ringKrullDim (A ⧸ x.1.asIdeal))) :
    AssociatedPointsClosureDimensionBound A I (maximalIdeal A) F := by
  intro x hx _ _ z _ hmz
  have hz : z = closedPoint A :=
    eq_closedPoint_of_mem_zeroLocus_maximalIdeal
      ((PrimeSpectrum.mem_zeroLocus _ _).2 hmz)
  subst hz
  exact (hdim x hx).trans_eq (congrArg krullDimToEInt (closureLocalDimension_closedPoint A _).symm)

/-- **The hypotheses of Stacks 0DXR give the hypotheses of Stacks 0EG2 at `𝔞 = 𝔪`.** The
standing inclusion `I ⊆ 𝔞` is automatic here, because an `I`-adically complete local ring has
`I ⊆ 𝔪`; completeness and the dualizing complex are condition (1) verbatim; and the source's
dimension hypothesis is condition (2) by
`Stacks.Algebraization.associatedPointsClosureDimensionBound_maximalIdeal`. -/
public theorem bootstrapHypotheses_maximalIdeal
    (hcomplete : IsAdicComplete I A)
    (hdualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (hdim : ∀ x : (complementZeroLocus A (maximalIdeal A) : Scheme),
      x ∈ Stacks.Divisors.associatedPoints F →
      ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
        krullDimToEInt (ringKrullDim (A ⧸ x.1.asIdeal))) :
    BootstrapHypotheses A I (maximalIdeal A) F :=
  ⟨le_maximalIdeal_of_isAdicComplete A I hcomplete, hcomplete, hdualizing,
    associatedPointsClosureDimensionBound_maximalIdeal A I F hdim⟩

/-! ### The conclusion of Stacks 0DXR: the injectivity half, and what the other half turns on -/

/-- **Stacks 0DXR, the injectivity half.** The canonical map from the sections of a coherent
module `ℱ` on the punctured spectrum `U = Spec(A) ∖ {𝔪}` defined near `U ∩ V(I)` to the
compatible families of sections of `ℱ / Iⁿ ℱ` on all of `U` is injective. No hypothesis beyond
`A` Noetherian and `ℱ` coherent is used: neither completeness, nor the dualizing complex, nor
the dimension bound at the associated points.

The surjectivity half, and with it the whole of the source's conclusion — the map is an
isomorphism and both of its sides are finite `A`-modules — is
`Stacks.Algebraization.isIso_comparisonModuleMap_and_finite_maximalIdeal` of
`PuncturedSpectrumFormalSectionsWhole.lean`, at the source's own hypotheses. -/
@[stacks 0DXR "the injectivity half of the displayed map, proved with none of the source's \
hypotheses beyond Noetherian and coherent; the surjectivity half and the finiteness of the two \
modules hold at the source's own hypotheses, by \
`Stacks.Algebraization.isIso_comparisonModuleMap_and_finite_maximalIdeal`"]
public theorem mono_comparisonMap_maximalIdeal [F.IsCoherent] :
    Mono (comparisonMap A I (maximalIdeal A) F) :=
  mono_comparisonMap A I (maximalIdeal A) F

/-- **Stacks 0DXR, the `A`-module structures and the `A`-linearity of the displayed map.** The
source states its conclusion as an isomorphism *of finite `A`-modules*, so the two sides carry
`A`-module structures and the map between them is `A`-linear. The two sides of
`Stacks.Algebraization.comparisonMap` are a colimit and a limit of groups of sections, hence
abelian groups; the `A`-module structures are
`Stacks.Algebraization.sectionsNearVanishingColimit` and
`Stacks.Algebraization.formalSectionsLimit`, obtained from the multiplication by `A` on
sections induced by `A ⟶ Γ(U, 𝒪_U)`, and the displayed map is `A`-linear for them, by
`Stacks.Algebraization.comparisonMap_comp_smul`. The statement below is that this `A`-linear
map — whose underlying map of abelian groups is the tag's map, by
`Stacks.Algebraization.forget₂_comparisonModuleMap` — is injective, that is, that the
injectivity half holds in the category of `A`-modules.

The source's surjectivity half and the finiteness of the two `A`-modules are supplied, for this
same `A`-linear map and at the source's own hypotheses, by
`Stacks.Algebraization.isIso_comparisonModuleMap_and_finite_maximalIdeal` of
`PuncturedSpectrumFormalSectionsWhole.lean`. -/
@[stacks 0DXR "the two sides of the displayed map are A-modules and the map is A-linear, and \
injective as a map of A-modules; its underlying map of abelian groups is the tag's map, by \
forget₂_comparisonModuleMap. The surjectivity half and the finiteness of the two A-modules hold \
at the source's own hypotheses, by \
`Stacks.Algebraization.isIso_comparisonModuleMap_and_finite_maximalIdeal`"]
public theorem mono_comparisonModuleMap_maximalIdeal [F.IsCoherent] :
    Mono (comparisonModuleMap A I (maximalIdeal A) F) := by
  rw [ModuleCat.mono_iff_injective]
  exact (AddCommGrpCat.mono_iff_injective _).1 (mono_comparisonMap_maximalIdeal A I F)

/-- **A criterion for the conclusion of Stacks 0DXR.** Since the map is always injective, it
is an isomorphism exactly when every compatible family of sections of `ℱ / Iⁿ ℱ` on `U` is the
image of an honest section of `ℱ` over a single open `V ⊆ U` containing `U ∩ V(I)`. This is
the specialization to `𝔞 = 𝔪` of
`Stacks.Algebraization.isIso_comparisonMap_iff_realized`, and it is an equivalence, not a
proof of either side. -/
public theorem isIso_comparisonMap_maximalIdeal_iff_realized [F.IsCoherent] :
    IsIso (comparisonMap A I (maximalIdeal A) F) ↔
      ∀ s : ToType (limit (formalSections A I (maximalIdeal A) F)),
        ∃ (V : OpensNearVanishing A I (maximalIdeal A))
          (t : ToType ((sectionsNearVanishing A I (maximalIdeal A) F).obj V)),
          ConcreteCategory.hom (comparisonAt A I (maximalIdeal A) F V) t = s :=
  isIso_comparisonMap_iff_realized A I (maximalIdeal A) F

end Stacks.Algebraization

end
