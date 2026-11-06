module

public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenAffine
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.AffineAvatar
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Invertible
public import StacksFrontier.Homology.Perfect.BettiConstructible
public import StacksFrontier.Homology.Perfect.Local

/-!
# A pseudo-coherent object whose derived fibres are a shifted line

Let `X` be a scheme and `E` a pseudo-coherent object of `D(𝒪_X)`. Suppose that at a point `x` the
derived fibre `Li_x^* E` has cohomology only in degree `i`, of dimension `r` over `κ(x)`, i.e. the
derived-fibre Betti numbers of [stacks 0BDI] satisfy `β_j(x) = 0` for `j ≠ i` and `β_i(x) = r`.
This file proves that, under either of the two hypotheses below, `E` is a finite locally free
module of rank `r` placed in degree `i` near `x`; for `(i, r) = (-1, 1)` it is `𝒪_U[1]` on a
neighbourhood `U` of `x`.

* **Bounded below near `x`.** If `E|_V ∈ D^{≥ c}` on an open `V ∋ x`, the bounded-below form of
  the local structure theorem for pseudo-coherent complexes ([stacks 0BYP]) makes `E` perfect on
  a principal open of an affine chart around `x`, and [stacks 0BDK] applies there.
* **The hypothesis at every point.** If the Betti numbers are concentrated in degree `i` with
  value `r` at *every* point, then [stacks 068V] makes `E` perfect on every affine chart, without
  any boundedness assumption, and the open of [stacks 0BDK] is all of `X`: the cohomology sheaves
  of `E` vanish outside degree `i`, `Hⁱ(E)` is finite locally free of rank `r` (invertible when
  `r = 1`), and `E ≅ Hⁱ(E)[-i]` globally.

## Main results

All in the namespace `AlgebraicGeometry.PseudoCoherentFibreInvertible`.

* `exists_derivedPullback_iso_singleFunctor_unit_of_isGE`: the pointwise statement, under a
  bounded-below hypothesis on a neighbourhood of `x`: `E|_U ≅ 𝒪_U[1]` on an open `U ∋ x`.
* `exists_derivedPullback_iso_singleFunctor_unit_of_forall`: the same conclusion at every point,
  with the hypothesis at every point and no boundedness.
* `isZero_homology_of_forall_derivedFiberBetti`,
  `isFiniteLocallyFreeOfRank_homology_of_forall_derivedFiberBetti`,
  `isInvertible_homology_of_forall_derivedFiberBetti` and
  `nonempty_iso_singleFunctor_homology_of_forall_derivedFiberBetti`: corollaries (a) and (b) —
  the global shape of `E`.
* `isRelativeDualizingComplex_shape_of_forall_derivedFiberBetti`: the same corollaries for the
  first component `K` of a relative dualizing complex
  (`AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex`), whose relative perfectness supplies
  the pseudo-coherence.

## Implementation notes

*Why a hypothesis beyond pseudo-coherence is needed in the pointwise statement.* The pointwise
statement is false for a merely pseudo-coherent `E`. On `X = 𝔸¹_k` over an infinite field, with
`x` the generic point, take `E = 𝒪_X[1] ⊕ ⊕_{n ≥ 1} (𝒪_X/(t - aₙ))[n]` for distinct `aₙ ∈ k`; each
degree involves a single coherent summand, so `E` is pseudo-coherent, and the derived fibre at the
generic point is `κ(x)[1]`. But every nonempty open contains some closed point `t = aₙ`, at which
`E` has nonzero cohomology in degree `-n`, so `E|_U ≇ 𝒪_U[1]` for every open `U ∋ x`. The
pseudo-coherent local structure theorem only splits off a perfect summand `τ_{≥ a}` near `x`; the
complementary summand `τ_{≤ a - 1}` has zero derived fibre at `x` but need not vanish near `x`.
Either of the two hypotheses kills it: bounded below by making it zero after shrinking, the
hypothesis at every point by making all its derived fibres zero.

*The route.* Both statements reduce to the perfect case
`AlgebraicGeometry.Scheme.Modules.mem_singleDegreeRankOpen_of_derivedFiberBetti` of [stacks 0BDK]
on an open `W` mapping to `X` by an open immersion on which `E` becomes perfect
(`mem_singleDegreeRankOpen_of_isPerfect_derivedPullback`); membership in the open subscheme of the
tag then comes back along the open immersion (`mem_singleDegreeRankOpen_of_mem_derivedPullback`).
On an affine chart `Spec R`, `E` is `M̃` for a pseudo-coherent `M ∈ D(R)`
(`AlgebraicGeometry.RingedSpace.exists_isPseudoCoherent_iso_mapDerivedCategory_tilde`), its
derived-fibre Betti numbers are those of `M`, and perfectness of `M` (from [stacks 068V] or
[stacks 0BYP]) crosses back by [stacks 08EB]. The only ring-theoretic input added here is that a
vanishing Betti number of a pseudo-coherent object is a vanishing derived-fibre cohomology
(`fibreCohomologyVanishes_of_fibreBetti_eq_zero`): the cohomology is finite dimensional, being
computed on a bounded-above complex of finite free modules.

*The model of the derived categories.* Everything is stated at `HasDerivedCategory.standard`
(named explicitly, by `letI` in each binder and conclusion that needs it, since instance search
would otherwise choose the locally small global instances of
`StacksFrontier.Homology.DerivedCategory.LocallySmall`), the model of
`AlgebraicGeometry.DerivedFibreBetti.derivedFiberBetti`, of the open subscheme of
[stacks 0BDK] and of the relative dualizing complexes of
`StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizingComplex.lean`; there
`OXMod.{u, u} X.toRingedSpace` and `X.Modules` agree by `rfl`, so no bridge is needed.

## References

* [Stacks Project, Tag 0BDK](https://stacks.math.columbia.edu/tag/0BDK)
* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
* [Stacks Project, Tag 0BYP](https://stacks.math.columbia.edu/tag/0BYP)
* [Stacks Project, Tag 068V](https://stacks.math.columbia.edu/tag/068V)
* [Stacks Project, Tag 08EB](https://stacks.math.columbia.edu/tag/08EB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)
open AlgebraicGeometry.Scheme.Modules
open StrictlyPerfect (OXMod)

universe d' u

namespace AlgebraicGeometry.PseudoCoherentFibreInvertible

/-- The standard model of `D(C)`. -/
local notation "𝔻ˢ[" C "]" => @DerivedCategory C _ _ (HasDerivedCategory.standard C)

/-! ### Ring-theoretic input -/

/-- **A vanishing derived-fibre Betti number of a pseudo-coherent object is a vanishing
cohomology module of the derived fibre.** Let `R` be a commutative ring, `K` a pseudo-coherent
object of `D(R)` and `q` a prime of `R`. If `dim_{κ(q)} Hʲ(K ⊗ᴸ_R κ(q)) = 0`, then
`Hʲ(K ⊗ᴸ_R κ(q)) = 0`, in the representative form `StacksDraft.Perfect.FibreCohomologyVanishes`.

The cohomology is computed on a bounded-above complex of finite free modules representing `K`,
so it is a subquotient of a finite-dimensional vector space, and a finite-dimensional space of
dimension zero vanishes. -/
theorem fibreCohomologyVanishes_of_fibreBetti_eq_zero {R : Type u} [CommRing R]
    (K : 𝔻ˢ[(ModuleCat.{u} R)])
    (hK : letI := HasDerivedCategory.standard (ModuleCat.{u} R)
      StacksDraft.PseudoCoherence.IsPseudoCoherent K) (q : PrimeSpectrum R) (j : ℤ)
    (h : letI := HasDerivedCategory.standard (ModuleCat.{u} R)
      StacksDraft.Perfect.fibreBetti.{u, u} K j q = 0) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    StacksDraft.Perfect.FibreCohomologyVanishes.{u, u} q.asIdeal K j := by
  let (T : Scheme.{u}) := HasDerivedCategory.standard (OXMod.{u, u} T.toRingedSpace)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toSheafedSpace))
  let (A : Type u) [Ring A] := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  obtain ⟨F, hF, ⟨eF⟩⟩ := hK
  obtain ⟨bd, hbd⟩ := hF.upperBound
  let := hbd
  have hFfin : ∀ i : ℤ, Module.Finite R (F.X i) := fun i => (hF.finiteFree i).1
  have hFfree : ∀ i : ℤ, Module.Free R (F.X i) := fun i => (hF.finiteFree i).2
  let := hFfree
  have hFproj : ∀ i : ℤ, Projective (F.X i) := fun i =>
    ModuleCat.projective_of_free (Module.Free.chooseBasis R (F.X i))
  let := hFproj
  refine ⟨F, hF, ⟨eF⟩, ?_⟩
  set ψ : R →+* q.asIdeal.ResidueField := algebraMap R q.asIdeal.ResidueField with hψ
  set Pκ := ((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj F with hPκ
  have hbetti : StacksDraft.Perfect.fibreBetti.{u, u} K j q =
      Module.finrank q.asIdeal.ResidueField (Pκ.homology j) := by
    show Module.finrank q.asIdeal.ResidueField
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} q.asIdeal.ResidueField) j).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          ψ).functor.obj K)) = _
    rw [StacksDraft.Perfect.finrank_homologyFunctor_eq_of_iso
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        ψ).functor.mapIso eF.symm) j]
    exact StacksDraft.Perfect.finrank_homologyFunctor_totalDerived_Q_obj.{u, u} ψ F bd j
  have : Module.Finite q.asIdeal.ResidueField (Pκ.X j) :=
    StacksDraft.Perfect.finite_extendScalars ψ (F.X j) (hFfin j)
  have hmono : Function.Injective (ModuleCat.Hom.hom (Pκ.iCycles j)) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have : Module.Finite q.asIdeal.ResidueField (Pκ.cycles j) :=
    FiniteDimensional.of_injective (ModuleCat.Hom.hom (Pκ.iCycles j)) hmono
  have hepi : Function.Surjective (ModuleCat.Hom.hom (Pκ.homologyπ j)) :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have : Module.Finite q.asIdeal.ResidueField (Pκ.homology j) :=
    Module.Finite.of_surjective _ hepi
  have hzero : Module.finrank q.asIdeal.ResidueField (Pκ.homology j) = 0 := hbetti ▸ h
  show IsZero (Pκ.homology j)
  have : Subsingleton (Pκ.homology j) := Module.finrank_zero_iff.mp hzero
  exact ModuleCat.isZero_of_subsingleton _

/-- A faithful functor preserving zero morphisms reflects zero objects. -/
theorem isZero_of_isZero_obj_of_faithful {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) [F.Faithful] [F.PreservesZeroMorphisms] {Y : C}
    (h : IsZero (F.obj Y)) : IsZero Y := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  apply F.map_injective
  rw [F.map_id, F.map_zero, h]

/-! ### Perfectness on affine charts -/

/-- **[Stacks 068V] on an affine scheme.** A pseudo-coherent object `E` of `D(𝒪_{Spec R})` whose
derived-fibre Betti numbers vanish outside `[a, b]` at every point is perfect.

`E` is `M̃` for a pseudo-coherent `M ∈ D(R)`, the Betti numbers of `E` are those of `M`, so the
derived fibres of `M` have cohomology only in `[a, b]` at every prime and `M` is perfect by
[stacks 068V]; perfectness returns to `E` by [stacks 08EB]. -/
theorem isPerfect_of_forall_derivedFiberBetti_eq_zero_affine (R : CommRingCat.{u})
    (E : 𝔻ˢ[(Spec R).Modules])
    (hE : letI := HasDerivedCategory.standard ((Spec R).Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} (Spec R).toRingedSpace)
      RingedSpace.IsPseudoCoherent.{u, u + 1} (X := (Spec R).toRingedSpace) E) (a b : ℤ)
    (h : letI := HasDerivedCategory.standard ((Spec R).Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} (Spec R).toRingedSpace)
      ∀ (y : Spec R) (j : ℤ), (j < a ∨ b < j) →
      DerivedFibreBetti.derivedFiberBetti (Spec R) E hE j y = 0) :
    letI := HasDerivedCategory.standard ((Spec R).Modules)
    letI := HasDerivedCategory.standard (OXMod.{u, u} (Spec R).toRingedSpace)
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec R).toRingedSpace) E := by
  let (T : Scheme.{u}) := HasDerivedCategory.standard (OXMod.{u, u} T.toRingedSpace)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toSheafedSpace))
  let (A : Type u) [Ring A] := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard ((Spec R).Modules)
  let := HasDerivedCategory.standard (OXMod.{u, u} (Spec R).toRingedSpace)
  obtain ⟨M, hM, ⟨e⟩⟩ := RingedSpace.exists_isPseudoCoherent_iso_mapDerivedCategory_tilde R E hE
  have hprime : ∀ q : PrimeSpectrum R, ∀ j : ℤ, j < a ∨ b < j →
      StacksDraft.Perfect.FibreCohomologyVanishes.{u, u} q.asIdeal M j := by
    intro q j hj
    exact fibreCohomologyVanishes_of_fibreBetti_eq_zero M hM q j
      ((derivedFiberBetti_eq_fibreBetti_of_iso R M E hE e j q).symm.trans (h q j hj))
  have hMperf : StacksDraft.Perfect.IsPerfect M :=
    ((StacksDraft.Perfect.isPerfect_and_torAmplitude_iff_fibreCohomologyVanishes.{u, u}
      M hM a b).1.2 hprime).1
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1} e
    ((isPerfect_tilde_iff M).2 hMperf)

/-- **[Stacks 0BYP] on an affine scheme.** Let `E` be a pseudo-coherent object of
`D(𝒪_{Spec R})` which is bounded below, and `p` a point at which the derived-fibre Betti numbers
of `E` vanish in all degrees below `a`. Then the derived pullback of `E` to some principal open
`D(g) ∋ p` is perfect.

`E` is `M̃` for a pseudo-coherent `M ∈ D(R)`, which is bounded below because derived
sheafification commutes with cohomology and reflects zero modules; [stacks 0BYP] makes
`M ⊗ᴸ_R R_g` perfect for some `g ∉ p`, and [stacks 08DW] part (2) and [stacks 08EB] carry this to
the derived pullback of `E` along `Spec R_g ⟶ Spec R`. -/
theorem exists_away_isPerfect_derivedPullback_of_isGE (R : CommRingCat.{u})
    (E : 𝔻ˢ[(Spec R).Modules])
    (hE : letI := HasDerivedCategory.standard ((Spec R).Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} (Spec R).toRingedSpace)
      RingedSpace.IsPseudoCoherent.{u, u + 1} (X := (Spec R).toRingedSpace) E) (c : ℤ)
    (hc : letI := HasDerivedCategory.standard ((Spec R).Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} (Spec R).toRingedSpace)
      E.IsGE c) (a : ℤ) (p : Spec R)
    (h : letI := HasDerivedCategory.standard ((Spec R).Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} (Spec R).toRingedSpace)
      ∀ j : ℤ, j < a → DerivedFibreBetti.derivedFiberBetti (Spec R) E hE j p = 0) :
    letI := HasDerivedCategory.standard ((Spec R).Modules)
    letI := HasDerivedCategory.standard (OXMod.{u, u} (Spec R).toRingedSpace)
    ∃ g : (R : Type u), g ∉ p.asIdeal ∧
      letI := HasDerivedCategory.standard (Spec (CommRingCat.of (Localization.Away g))).Modules
      letI := HasDerivedCategory.standard
        (OXMod.{u, u} (Spec (CommRingCat.of (Localization.Away g))).toRingedSpace)
      letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing
        (Spec (CommRingCat.of (Localization.Away g))).toSheafedSpace))
      letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing
        (Spec (CommRingCat.of (R : Type u))).toSheafedSpace))
      Stacks.Cohomology.PerfectComplexes.IsPerfect
        (X := (Spec (CommRingCat.of (Localization.Away g))).toRingedSpace)
        ((derivedPullback (Spec.map (CommRingCat.ofHom
          (algebraMap (R : Type u) (Localization.Away g)))).toLRSHom.toShHom).obj E) := by
  let (T : Scheme.{u}) := HasDerivedCategory.standard (OXMod.{u, u} T.toRingedSpace)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toSheafedSpace))
  let (A : Type u) [Ring A] := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard ((Spec R).Modules)
  let := HasDerivedCategory.standard (OXMod.{u, u} (Spec R).toRingedSpace)
  have : p.asIdeal.IsPrime := p.isPrime
  obtain ⟨M, hM, ⟨e⟩⟩ := RingedSpace.exists_isPseudoCoherent_iso_mapDerivedCategory_tilde R E hE
  have hMge : M.IsGE c := by
    rw [DerivedCategory.isGE_iff]
    intro j hj
    have hz : IsZero ((DerivedCategory.homologyFunctor (Spec R).Modules j).obj
        ((tilde.functor R).mapDerivedCategory.obj M)) :=
      IsZero.of_iso (DerivedCategory.isZero_of_isGE E c j hj)
        ((DerivedCategory.homologyFunctor (Spec R).Modules j).mapIso e)
    exact isZero_of_isZero_obj_of_faithful (tilde.functor R)
      (IsZero.of_iso hz (((tilde.functor R).mapDerivedCategoryHomologyFunctorIso j).app M).symm)
  have hvan : ∀ i : ℤ, i < a →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} p.asIdeal.ResidueField) i).obj
        ((totalDerivedExtensionScalars.{u, u, u}
          (algebraMap (R : Type u) p.asIdeal.ResidueField)).functor.obj M)) := by
    intro i hi
    refine (StacksDraft.Perfect.fibreCohomologyVanishes_iff_isZero_homology.{u, u}
      p.asIdeal M hM i).1 (fibreCohomologyVanishes_of_fibreBetti_eq_zero M hM p i ?_)
    exact (derivedFiberBetti_eq_fibreBetti_of_iso R M E hE e i p).symm.trans (h i hi)
  obtain ⟨g, hg, hcont⟩ :=
    StacksDraft.Perfect.exists_away_bounded_free_complex_representing_of_fibre_vanishing_below.{u,
      u} p.asIdeal M hM ⟨c, hMge⟩ a hvan
  refine ⟨g, hg, ?_⟩
  have hperf : StacksDraft.Perfect.IsPerfect ((totalDerivedExtensionScalars.{u, u, u}
      (algebraMap (R : Type u) (Localization.Away g))).functor.obj M) := hcont.1
  have e' : (derivedPullback (Spec.map (CommRingCat.ofHom
        (algebraMap (R : Type u) (Localization.Away g)))).toLRSHom.toShHom).obj E ≅
      (tilde.functor (CommRingCat.of (Localization.Away g))).mapDerivedCategory.obj
        ((totalDerivedExtensionScalars.{u, u, u}
          (algebraMap (R : Type u) (Localization.Away g))).functor.obj M) :=
    (derivedPullback (Spec.map (CommRingCat.ofHom
        (algebraMap (R : Type u) (Localization.Away g)))).toLRSHom.toShHom).mapIso e.symm ≪≫
      (StandardModel.affinePullbackComparison R (CommRingCat.of (Localization.Away g))
        (CommRingCat.ofHom (algebraMap (R : Type u) (Localization.Away g)))).app M
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1} e'.symm
    ((isPerfect_tilde_iff _).2 hperf)

/-! ### Moving membership in the open subscheme of [stacks 0BDK] along open immersions -/

/-- **Membership in the open subscheme of [stacks 0BDK] descends along an open immersion.** If
`h : W ⟶ X` is an open immersion and `w` lies in the open subscheme of `W` on which the derived
pullback of `E` is a finite locally free module of rank `r` in degree `i`, then `h w` lies in the
corresponding open subscheme of `X`. -/
theorem mem_singleDegreeRankOpen_of_mem_derivedPullback {X W : Scheme.{u}}
    (E : 𝔻ˢ[X.Modules]) (h : W ⟶ X) [IsOpenImmersion h] (i : ℤ) (r : ℕ) {w : W}
    (hw : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      letI := HasDerivedCategory.standard (W.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} W.toRingedSpace)
      letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing X.toSheafedSpace))
      letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing W.toSheafedSpace))
      w ∈ singleDegreeRankOpen ((derivedPullback h.toLRSHom.toShHom).obj E) i r) :
    letI := HasDerivedCategory.standard (X.Modules)
    letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
    letI := HasDerivedCategory.standard (W.Modules)
    letI := HasDerivedCategory.standard (OXMod.{u, u} W.toRingedSpace)
    letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing X.toSheafedSpace))
    letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing W.toSheafedSpace))
    h.base w ∈ singleDegreeRankOpen E i r := by
  let (T : Scheme.{u}) := HasDerivedCategory.standard (OXMod.{u, u} T.toRingedSpace)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toSheafedSpace))
  let (A : Type u) [Ring A] := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard (X.Modules)
  let := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
  let := HasDerivedCategory.standard (W.Modules)
  let := HasDerivedCategory.standard (OXMod.{u, u} W.toRingedSpace)
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing W.toSheafedSpace))
  let EW := (derivedPullback h.toLRSHom.toShHom).obj E
  let U' : W.Opens := singleDegreeRankOpen EW i r
  obtain ⟨M, hM, ⟨e⟩⟩ := (nonempty_iso_singleFunctor_restrict_iff_le EW i r U').2 le_rfl
  exact mem_singleDegreeRankOpen_of_isOpenImmersion E i r (U'.ι ≫ h)
    ⟨M, hM, ⟨derivedRestrictCompIsoOfDerivedPullback E i U'.ι h M
      (((derivedRestrictIsoDerivedPullback U'.ι).app EW).symm ≪≫ e)⟩⟩ ⟨⟨w, hw⟩, rfl⟩

/-- **[Stacks 0BDK] through an open immersion on which `E` becomes perfect.** Let `E` be a
pseudo-coherent object of `D(𝒪_X)`, `h : W ⟶ X` an open immersion along which the derived
pullback of `E` is perfect, and `w ∈ W` a point at whose image the derived-fibre Betti numbers of
`E` vanish outside degree `i` and equal `r` in degree `i`. Then `h w` lies in the open subscheme
`singleDegreeRankOpen E i r`. -/
theorem mem_singleDegreeRankOpen_of_isPerfect_derivedPullback {X W : Scheme.{u}}
    (E : 𝔻ˢ[X.Modules])
    (hE : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      letI := HasDerivedCategory.standard (W.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} W.toRingedSpace)
      letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing X.toSheafedSpace))
      letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing W.toSheafedSpace))
      RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace) E)
    (h : W ⟶ X) [IsOpenImmersion h]
    (hW : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      letI := HasDerivedCategory.standard (W.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} W.toRingedSpace)
      letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing X.toSheafedSpace))
      letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing W.toSheafedSpace))
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace)
      ((derivedPullback h.toLRSHom.toShHom).obj E))
    (i : ℤ) (r : ℕ) {w : W}
    (hvanish : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      letI := HasDerivedCategory.standard (W.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} W.toRingedSpace)
      letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing X.toSheafedSpace))
      letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing W.toSheafedSpace))
      ∀ j : ℤ, j ≠ i → DerivedFibreBetti.derivedFiberBetti X E hE j (h.base w) = 0)
    (hrank : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      letI := HasDerivedCategory.standard (W.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} W.toRingedSpace)
      letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing X.toSheafedSpace))
      letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing W.toSheafedSpace))
      DerivedFibreBetti.derivedFiberBetti X E hE i (h.base w) = r) :
    letI := HasDerivedCategory.standard (X.Modules)
    letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
    letI := HasDerivedCategory.standard (W.Modules)
    letI := HasDerivedCategory.standard (OXMod.{u, u} W.toRingedSpace)
    letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing X.toSheafedSpace))
    letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing W.toSheafedSpace))
    h.base w ∈ singleDegreeRankOpen E i r := by
  let (T : Scheme.{u}) := HasDerivedCategory.standard (OXMod.{u, u} T.toRingedSpace)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toSheafedSpace))
  let (A : Type u) [Ring A] := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard (X.Modules)
  let := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
  let := HasDerivedCategory.standard (W.Modules)
  let := HasDerivedCategory.standard (OXMod.{u, u} W.toRingedSpace)
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing W.toSheafedSpace))
  have hbc : ∀ j : ℤ, DerivedFibreBetti.derivedFiberBetti W
      ((derivedPullback h.toLRSHom.toShHom).obj E)
      (DerivedFibreBetti.isPseudoCoherent_derivedPullback h E hE) j w =
      DerivedFibreBetti.derivedFiberBetti X E hE j (h.base w) := fun j =>
    congrFun (DerivedFibreBetti.derivedFiberBetti_derivedPullback h E hE j) w
  exact mem_singleDegreeRankOpen_of_mem_derivedPullback E h i r
    (mem_singleDegreeRankOpen_of_derivedFiberBetti _ hW
      (DerivedFibreBetti.isPseudoCoherent_derivedPullback h E hE) i r
      (fun j hj => (hbc j).trans (hvanish j hj)) ((hbc i).trans hrank))

/-! ### The two pointwise criteria for membership -/

/-- Bounded below on an open `V` passes to the derived pullback along any open immersion with
image in `V`. -/
theorem isGE_derivedPullback_of_isGE_restrict {X W : Scheme.{u}} (E : 𝔻ˢ[X.Modules])
    (V : X.Opens) (c : ℤ) (hc : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      letI := HasDerivedCategory.standard (V.toScheme.Modules)
      letI := HasDerivedCategory.standard (W.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} W.toRingedSpace)
      letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing X.toSheafedSpace))
      letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing W.toSheafedSpace))
      ((restrictFunctor V.ι).mapDerivedCategory.obj E).IsGE c)
    (h : W ⟶ X) [IsOpenImmersion h] (hle : Set.range h.base ⊆ (V : Set X)) :
    letI := HasDerivedCategory.standard (X.Modules)
    letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
    letI := HasDerivedCategory.standard (V.toScheme.Modules)
    letI := HasDerivedCategory.standard (W.Modules)
    letI := HasDerivedCategory.standard (OXMod.{u, u} W.toRingedSpace)
    letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing X.toSheafedSpace))
    letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing W.toSheafedSpace))
    ((derivedPullback h.toLRSHom.toShHom).obj E).IsGE c := by
  let (T : Scheme.{u}) := HasDerivedCategory.standard (OXMod.{u, u} T.toRingedSpace)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toSheafedSpace))
  let (A : Type u) [Ring A] := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard (X.Modules)
  let := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
  let := HasDerivedCategory.standard (V.toScheme.Modules)
  let := HasDerivedCategory.standard (W.Modules)
  let := HasDerivedCategory.standard (OXMod.{u, u} W.toRingedSpace)
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing W.toSheafedSpace))
  have hle' : Set.range h.base ⊆ Set.range V.ι.base := by rwa [Scheme.Opens.range_ι]
  let a : W ⟶ V.toScheme := IsOpenImmersion.lift V.ι h hle'
  have ha : a ≫ V.ι = h := IsOpenImmersion.lift_fac V.ι h hle'
  rw [DerivedCategory.isGE_iff]
  intro j hj
  have hV : IsZero ((restrictFunctor V.ι).obj
      ((DerivedCategory.homologyFunctor X.Modules j).obj E)) :=
    IsZero.of_iso (DerivedCategory.isZero_of_isGE _ c j hj)
      ((homologyFunctor_mapDerivedCategory_restrictFunctor_iso V.ι j).app E).symm
  have hW : IsZero ((restrictFunctor h).obj
      ((DerivedCategory.homologyFunctor X.Modules j).obj E)) :=
    IsZero.of_iso (Functor.map_isZero (restrictFunctor a) hV)
      ((restrictFunctorCongr ha.symm).app _ ≪≫ (restrictFunctorComp a V.ι).app _)
  exact IsZero.of_iso hW
    ((DerivedCategory.homologyFunctor W.Modules j).mapIso
        ((derivedRestrictIsoDerivedPullback h).app E).symm ≪≫
      (homologyFunctor_mapDerivedCategory_restrictFunctor_iso h j).app E)

/-- **[Stacks 0BDK] for a pseudo-coherent object which is bounded below near the point.** Let `E`
be a pseudo-coherent object of `D(𝒪_X)` whose restriction to an open `V ∋ x` lies in `D^{≥ c}`.
If the derived-fibre Betti numbers of `E` at `x` vanish outside degree `i` and equal `r` in degree
`i`, then `x` lies in `singleDegreeRankOpen E i r`. -/
theorem mem_singleDegreeRankOpen_of_isGE {X : Scheme.{u}} (E : 𝔻ˢ[X.Modules])
    (hE : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace) E)
    (V : X.Opens) (c : ℤ) (hc : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      letI := HasDerivedCategory.standard (V.toScheme.Modules)
      ((restrictFunctor V.ι).mapDerivedCategory.obj E).IsGE c)
    (i : ℤ) (r : ℕ) {x : X} (hxV : x ∈ V)
    (hvanish : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      letI := HasDerivedCategory.standard (V.toScheme.Modules)
      ∀ j : ℤ, j ≠ i → DerivedFibreBetti.derivedFiberBetti X E hE j x = 0)
    (hrank : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      letI := HasDerivedCategory.standard (V.toScheme.Modules)
      DerivedFibreBetti.derivedFiberBetti X E hE i x = r) :
    letI := HasDerivedCategory.standard (X.Modules)
    letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
    letI := HasDerivedCategory.standard (V.toScheme.Modules)
    x ∈ singleDegreeRankOpen E i r := by
  let (T : Scheme.{u}) := HasDerivedCategory.standard (OXMod.{u, u} T.toRingedSpace)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toSheafedSpace))
  let (A : Type u) [Ring A] := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard (X.Modules)
  let := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
  let := HasDerivedCategory.standard (V.toScheme.Modules)
  obtain ⟨V', hV'aff, hxV', hV'V⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hxV
  let U : X.affineOpens := ⟨V', hV'aff⟩
  obtain ⟨y, hy⟩ : x ∈ Set.range (U.2.fromSpec).base := by rwa [U.2.range_fromSpec]
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have hge := isGE_derivedPullback_of_isGE_restrict E V c hc U.2.fromSpec
    (by rwa [U.2.range_fromSpec])
  let EV := (derivedPullback (U.2.fromSpec).toLRSHom.toShHom).obj E
  have hPCV := DerivedFibreBetti.isPseudoCoherent_derivedPullback U.2.fromSpec E hE
  have hbc : ∀ j : ℤ, DerivedFibreBetti.derivedFiberBetti (Spec Γ(X, U.1)) EV hPCV j y =
      DerivedFibreBetti.derivedFiberBetti X E hE j x := fun j =>
    (congrFun (DerivedFibreBetti.derivedFiberBetti_derivedPullback U.2.fromSpec E hE j) y).trans
      (congrArg (DerivedFibreBetti.derivedFiberBetti X E hE j) hy)
  obtain ⟨g, hg, hperf⟩ := exists_away_isPerfect_derivedPullback_of_isGE Γ(X, U.1) EV hPCV c hge
    i y (fun j hj => (hbc j).trans (hvanish j (by omega)))
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (Γ(X, U.1) : Type u) (Localization.Away g)))) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway g
  obtain ⟨z, hz⟩ : y ∈ Set.range (Spec.map (CommRingCat.ofHom
      (algebraMap (Γ(X, U.1) : Type u) (Localization.Away g)))).base := by
    have hb : y ∈ PrimeSpectrum.basicOpen g := hg
    rwa [← Scheme.Hom.opensRange_localizationAway (R := Γ(X, U.1)) g] at hb
  have hyU : y ∈ singleDegreeRankOpen EV i r := by
    have := mem_singleDegreeRankOpen_of_isPerfect_derivedPullback EV hPCV
      (Spec.map (CommRingCat.ofHom
        (algebraMap (Γ(X, U.1) : Type u) (Localization.Away g)))) hperf i r (w := z)
      (fun j hj => by rw [hz]; exact (hbc j).trans (hvanish j hj))
      (by rw [hz]; exact (hbc i).trans hrank)
    rwa [hz] at this
  have := mem_singleDegreeRankOpen_of_mem_derivedPullback E U.2.fromSpec i r hyU
  rwa [hy] at this

/-- **[Stacks 0BDK] with the hypothesis at every point.** Let `E` be a pseudo-coherent object of
`D(𝒪_X)` whose derived-fibre Betti numbers are, at every point, concentrated in degree `i` with
value `r`. Then the open subscheme `singleDegreeRankOpen E i r` is all of `X`.

No boundedness is needed: on every affine chart the hypothesis at every point makes `E` perfect by
[stacks 068V]. -/
theorem singleDegreeRankOpen_eq_top_of_forall_derivedFiberBetti {X : Scheme.{u}}
    (E : 𝔻ˢ[X.Modules])
    (hE : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace) E) (i : ℤ) (r : ℕ)
    (h : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      ∀ (x : X) (j : ℤ), DerivedFibreBetti.derivedFiberBetti X E hE j x =
      if j = i then r else 0) :
    letI := HasDerivedCategory.standard (X.Modules)
    letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
    singleDegreeRankOpen E i r = ⊤ := by
  let (T : Scheme.{u}) := HasDerivedCategory.standard (OXMod.{u, u} T.toRingedSpace)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toSheafedSpace))
  let (A : Type u) [Ring A] := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard (X.Modules)
  let := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
  refine top_le_iff.1 fun x _ => ?_
  obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
  obtain ⟨y, hy⟩ : x ∈ Set.range (U.2.fromSpec).base := by rwa [U.2.range_fromSpec]
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have hPCV := DerivedFibreBetti.isPseudoCoherent_derivedPullback U.2.fromSpec E hE
  have hperf : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (Spec Γ(X, U.1)).toRingedSpace)
      ((derivedPullback (U.2.fromSpec).toLRSHom.toShHom).obj E) := by
    refine isPerfect_of_forall_derivedFiberBetti_eq_zero_affine Γ(X, U.1) _ hPCV i i
      fun y' j hj => ?_
    rw [congrFun (DerivedFibreBetti.derivedFiberBetti_derivedPullback U.2.fromSpec E hE j) y',
      Function.comp_apply, h, if_neg (by omega)]
  have := mem_singleDegreeRankOpen_of_isPerfect_derivedPullback E hE U.2.fromSpec hperf i r
    (w := y) (fun j hj => by rw [h, if_neg hj]) (by rw [h, if_pos rfl])
  rwa [hy] at this

/-! ### From the open subscheme to a trivialization -/

/-- Restriction of a module placed in degree `i` along a factorisation of open immersions. If
`h ≫ g = k` and `E` restricted along `g` is `M` placed in degree `i`, then `E` restricted along
`k` is the restriction of `M` along `h` placed in degree `i`. -/
def restrictCompSingleIso {X Y Z : Scheme.{u}} (E : 𝔻ˢ[X.Modules]) (i : ℤ)
    (g : Y ⟶ X) [IsOpenImmersion g] (h : Z ⟶ Y) [IsOpenImmersion h] (k : Z ⟶ X)
    [IsOpenImmersion k] (hk : h ≫ g = k) (M : Y.Modules)
    (e : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (Y.Modules)
      letI := HasDerivedCategory.standard (Z.Modules)
      (restrictFunctor g).mapDerivedCategory.obj E ≅
      (DerivedCategory.singleFunctor Y.Modules i).obj M) :
    letI := HasDerivedCategory.standard (X.Modules)
    letI := HasDerivedCategory.standard (Y.Modules)
    letI := HasDerivedCategory.standard (Z.Modules)
    (restrictFunctor k).mapDerivedCategory.obj E ≅
      (DerivedCategory.singleFunctor Z.Modules i).obj ((restrictFunctor h).obj M) :=
  letI (T : Scheme.{u}) := HasDerivedCategory.standard (OXMod.{u, u} T.toRingedSpace)
  letI (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  letI (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules (structureSheafRing T.toRingedSpace))
  letI (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules (structureSheafRing T.toSheafedSpace))
  letI (A : Type u) [Ring A] := HasDerivedCategory.standard (ModuleCat.{u} A)
  letI := HasDerivedCategory.standard (X.Modules)
  letI := HasDerivedCategory.standard (Y.Modules)
  letI := HasDerivedCategory.standard (Z.Modules)
  ((Functor.mapDerivedCategoryCompIsoOfCompIso (restrictFunctorComp h g).symm ≪≫
      Functor.mapDerivedCategoryCongr (restrictFunctorCongr hk)).app E).symm ≪≫
    (restrictFunctor h).mapDerivedCategory.mapIso e ≪≫
      ((restrictFunctor h).mapDerivedCategorySingleFunctor i).app M

/-- **On a neighbourhood of a point of the rank-one open subscheme, `E` is the structure sheaf
placed in degree `i`.** If `x ∈ singleDegreeRankOpen E i 1`, there is an open `U ∋ x` with
`E|_U ≅ 𝒪_U[-i]`: on the open subscheme `E` is an invertible module placed in degree `i`, and an
invertible module is trivial near each point. -/
theorem exists_restrict_iso_singleFunctor_unit_of_mem {X : Scheme.{u}}
    (E : 𝔻ˢ[X.Modules]) (i : ℤ) {x : X} (hx : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      x ∈ singleDegreeRankOpen E i 1) :
    letI := HasDerivedCategory.standard (X.Modules)
    letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
    ∃ U : X.Opens, x ∈ U ∧
      letI := HasDerivedCategory.standard U.toScheme.Modules
      Nonempty ((restrictFunctor U.ι).mapDerivedCategory.obj E ≅
        (DerivedCategory.singleFunctor U.toScheme.Modules i).obj
          (SheafOfModules.unit U.toScheme.ringCatSheaf)) := by
  let (T : Scheme.{u}) := HasDerivedCategory.standard (OXMod.{u, u} T.toRingedSpace)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toSheafedSpace))
  let (A : Type u) [Ring A] := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard (X.Modules)
  let := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
  obtain ⟨N, hN, ⟨e₀⟩⟩ :=
    (nonempty_iso_singleFunctor_restrict_iff_le E i 1 (singleDegreeRankOpen E i 1)).2 le_rfl
  obtain ⟨V, hV, ⟨ε⟩⟩ := (isFiniteLocallyFreeOfRank_iff N 1).2 hN ⟨x, hx⟩
  let U₀ := singleDegreeRankOpen E i 1
  refine ⟨U₀.ι ''ᵁ V, ⟨⟨x, hx⟩, hV, rfl⟩, ?_⟩
  have hrange : Set.range (U₀.ι ''ᵁ V).ι.base = Set.range (V.ι ≫ U₀.ι).base := by
    simp [Set.range_comp]
    rfl
  let φ : (U₀.ι ''ᵁ V).toScheme ≅ V.toScheme :=
    IsOpenImmersion.isoOfRangeEq (U₀.ι ''ᵁ V).ι (V.ι ≫ U₀.ι) hrange
  have hφ : (φ.hom ≫ V.ι) ≫ U₀.ι = (U₀.ι ''ᵁ V).ι := by
    rw [Category.assoc]
    exact IsOpenImmersion.isoOfRangeEq_hom_fac (U₀.ι ''ᵁ V).ι (V.ι ≫ U₀.ι) hrange
  refine ⟨restrictCompSingleIso E i U₀.ι (φ.hom ≫ V.ι) (U₀.ι ''ᵁ V).ι hφ N e₀ ≪≫
    (DerivedCategory.singleFunctor _ i).mapIso ?_⟩
  exact (restrictFunctorComp φ.hom V.ι).app N ≪≫ (restrictFunctor φ.hom).mapIso ε ≪≫
    (restrictFreeIso φ.hom _).symm ≪≫ Stacks.SheafOfModules.Invertible.freeUniqueIso _

/-! ### The pointwise statements -/

/-- **A pseudo-coherent object, bounded below near `x`, whose derived fibre at `x` is a line in
degree `-1`, is `𝒪[1]` near `x`.** Let `X` be a scheme, `E` a pseudo-coherent object of `D(𝒪_X)`
whose restriction to an open `V ∋ x` lies in `D^{≥ c}`, and suppose the derived fibre `Li_x^* E`
has cohomology only in degree `-1`, of dimension `1` over `κ(x)`. Then there is an open `U ∋ x`
with `Lι_U^* E ≅ 𝒪_U[1]`.

The bounded-below hypothesis cannot be dropped: see the module docstring. -/
theorem exists_derivedPullback_iso_singleFunctor_unit_of_isGE {X : Scheme.{u}}
    (E : 𝔻ˢ[X.Modules])
    (hE : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace) E)
    (V : X.Opens) (c : ℤ) (hc : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      letI := HasDerivedCategory.standard (V.toScheme.Modules)
      ((restrictFunctor V.ι).mapDerivedCategory.obj E).IsGE c)
    {x : X} (hxV : x ∈ V)
    (hx : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      letI := HasDerivedCategory.standard (V.toScheme.Modules)
      ∀ j : ℤ, DerivedFibreBetti.derivedFiberBetti X E hE j x = if j = -1 then 1 else 0) :
    letI := HasDerivedCategory.standard (X.Modules)
    letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
    letI := HasDerivedCategory.standard (V.toScheme.Modules)
    ∃ U : X.Opens, x ∈ U ∧
      letI := HasDerivedCategory.standard U.toScheme.Modules
      letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing X.toSheafedSpace))
      letI := HasDerivedCategory.standard
        (SheafOfModules (structureSheafRing U.toScheme.toSheafedSpace))
      Nonempty ((derivedPullback U.ι.toLRSHom.toShHom).obj E ≅
        (DerivedCategory.singleFunctor U.toScheme.Modules (-1)).obj
          (SheafOfModules.unit U.toScheme.ringCatSheaf)) := by
  let (T : Scheme.{u}) := HasDerivedCategory.standard (OXMod.{u, u} T.toRingedSpace)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toSheafedSpace))
  let (A : Type u) [Ring A] := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard (X.Modules)
  let := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
  let := HasDerivedCategory.standard (V.toScheme.Modules)
  have hmem := mem_singleDegreeRankOpen_of_isGE E hE V c hc (-1) 1 hxV
    (fun j hj => by rw [hx, if_neg hj]) (by rw [hx, if_pos rfl])
  obtain ⟨U, hxU, ⟨e⟩⟩ := exists_restrict_iso_singleFunctor_unit_of_mem E (-1) hmem
  exact ⟨U, hxU, ⟨((derivedRestrictIsoDerivedPullback U.ι).app E).symm ≪≫ e⟩⟩

/-- The special case of `exists_derivedPullback_iso_singleFunctor_unit_of_isGE` for `E` bounded
below on all of `X`. -/
theorem exists_derivedPullback_iso_singleFunctor_unit_of_isGE_global {X : Scheme.{u}}
    (E : 𝔻ˢ[X.Modules])
    (hE : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace) E)
    (c : ℤ) (hc : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      E.IsGE c) (x : X)
    (hx : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      ∀ j : ℤ, DerivedFibreBetti.derivedFiberBetti X E hE j x = if j = -1 then 1 else 0) :
    letI := HasDerivedCategory.standard (X.Modules)
    letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
    ∃ U : X.Opens, x ∈ U ∧
      letI := HasDerivedCategory.standard U.toScheme.Modules
      letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing X.toSheafedSpace))
      letI := HasDerivedCategory.standard
        (SheafOfModules (structureSheafRing U.toScheme.toSheafedSpace))
      Nonempty ((derivedPullback U.ι.toLRSHom.toShHom).obj E ≅
        (DerivedCategory.singleFunctor U.toScheme.Modules (-1)).obj
          (SheafOfModules.unit U.toScheme.ringCatSheaf)) := by
  let (T : Scheme.{u}) := HasDerivedCategory.standard (OXMod.{u, u} T.toRingedSpace)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toSheafedSpace))
  let (A : Type u) [Ring A] := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard (X.Modules)
  let := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
  refine exists_derivedPullback_iso_singleFunctor_unit_of_isGE E hE ⊤ c ?_ trivial hx
  rw [DerivedCategory.isGE_iff]
  intro j hj
  exact IsZero.of_iso (Functor.map_isZero (restrictFunctor (⊤ : X.Opens).ι)
      (DerivedCategory.isZero_of_isGE E c j hj))
    ((homologyFunctor_mapDerivedCategory_restrictFunctor_iso (⊤ : X.Opens).ι j).app E)

/-- **A pseudo-coherent object whose derived fibres are all lines in degree `-1` is locally
`𝒪[1]`.** If at every point of `X` the derived fibre of the pseudo-coherent object `E` has
cohomology only in degree `-1`, of dimension `1`, then every point has an open neighbourhood `U`
with `Lι_U^* E ≅ 𝒪_U[1]`. No boundedness hypothesis is needed. -/
theorem exists_derivedPullback_iso_singleFunctor_unit_of_forall {X : Scheme.{u}}
    (E : 𝔻ˢ[X.Modules])
    (hE : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace) E)
    (h : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      ∀ (x : X) (j : ℤ), DerivedFibreBetti.derivedFiberBetti X E hE j x =
      if j = -1 then 1 else 0) (x : X) :
    letI := HasDerivedCategory.standard (X.Modules)
    letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
    ∃ U : X.Opens, x ∈ U ∧
      letI := HasDerivedCategory.standard U.toScheme.Modules
      letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing X.toSheafedSpace))
      letI := HasDerivedCategory.standard
        (SheafOfModules (structureSheafRing U.toScheme.toSheafedSpace))
      Nonempty ((derivedPullback U.ι.toLRSHom.toShHom).obj E ≅
        (DerivedCategory.singleFunctor U.toScheme.Modules (-1)).obj
          (SheafOfModules.unit U.toScheme.ringCatSheaf)) := by
  let (T : Scheme.{u}) := HasDerivedCategory.standard (OXMod.{u, u} T.toRingedSpace)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toSheafedSpace))
  let (A : Type u) [Ring A] := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard (X.Modules)
  let := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
  have hmem : x ∈ singleDegreeRankOpen E (-1) 1 := by
    rw [singleDegreeRankOpen_eq_top_of_forall_derivedFiberBetti E hE (-1) 1 h]
    trivial
  obtain ⟨U, hxU, ⟨e⟩⟩ := exists_restrict_iso_singleFunctor_unit_of_mem E (-1) hmem
  exact ⟨U, hxU, ⟨((derivedRestrictIsoDerivedPullback U.ι).app E).symm ≪≫ e⟩⟩

/-! ### The global corollaries -/

/-- The whole scheme carries `E` in degree `i` with rank `r` when the hypothesis holds at every
point. -/
theorem isSingleDegreeRank_top_of_forall_derivedFiberBetti {X : Scheme.{u}}
    (E : 𝔻ˢ[X.Modules])
    (hE : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace) E) (i : ℤ) (r : ℕ)
    (h : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      ∀ (x : X) (j : ℤ), DerivedFibreBetti.derivedFiberBetti X E hE j x =
      if j = i then r else 0) :
    letI := HasDerivedCategory.standard (X.Modules)
    letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
    IsSingleDegreeRank E i r ⊤ :=
  let (T : Scheme.{u}) := HasDerivedCategory.standard (OXMod.{u, u} T.toRingedSpace)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  letI (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules (structureSheafRing T.toRingedSpace))
  letI (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules (structureSheafRing T.toSheafedSpace))
  let (A : Type u) [Ring A] := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard (X.Modules)
  let := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
  (le_singleDegreeRankOpen_iff E i r ⊤).2
    (singleDegreeRankOpen_eq_top_of_forall_derivedFiberBetti E hE i r h).ge

/-- **Corollary (a), vanishing.** If at every point the derived fibre of the pseudo-coherent
object `E` has cohomology only in degree `-1`, of dimension `1`, then `Hʲ(E) = 0` for `j ≠ -1`. -/
theorem isZero_homology_of_forall_derivedFiberBetti {X : Scheme.{u}}
    (E : 𝔻ˢ[X.Modules])
    (hE : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace) E)
    (h : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      ∀ (x : X) (j : ℤ), DerivedFibreBetti.derivedFiberBetti X E hE j x =
      if j = -1 then 1 else 0) (j : ℤ) (hj : j ≠ -1) :
    letI := HasDerivedCategory.standard (X.Modules)
    letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
    IsZero ((DerivedCategory.homologyFunctor X.Modules j).obj E) := by
  let (T : Scheme.{u}) := HasDerivedCategory.standard (OXMod.{u, u} T.toRingedSpace)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toSheafedSpace))
  let (A : Type u) [Ring A] := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard (X.Modules)
  let := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
  have : IsIso (⊤ : X.Opens).ι := inferInstanceAs (IsIso X.topIso.hom)
  exact isZero_of_isZero_restrict_isIso (⊤ : X.Opens).ι
    ((isSingleDegreeRank_top_of_forall_derivedFiberBetti E hE (-1) 1 h).1 j hj)

/-- **Corollary (a), rank one.** If at every point the derived fibre of the pseudo-coherent object
`E` has cohomology only in degree `-1`, of dimension `1`, then `H⁻¹(E)` is finite locally free of
rank one. -/
theorem isFiniteLocallyFreeOfRank_homology_of_forall_derivedFiberBetti {X : Scheme.{u}}
    (E : 𝔻ˢ[X.Modules])
    (hE : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace) E)
    (h : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      ∀ (x : X) (j : ℤ), DerivedFibreBetti.derivedFiberBetti X E hE j x =
      if j = -1 then 1 else 0) :
    letI := HasDerivedCategory.standard (X.Modules)
    letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((DerivedCategory.homologyFunctor X.Modules (-1)).obj E) 1 := by
  let (T : Scheme.{u}) := HasDerivedCategory.standard (OXMod.{u, u} T.toRingedSpace)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toSheafedSpace))
  let (A : Type u) [Ring A] := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard (X.Modules)
  let := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
  have : IsIso (⊤ : X.Opens).ι := inferInstanceAs (IsIso X.topIso.hom)
  exact (isFiniteLocallyFreeOfRank_iff _ 1).1
    (isFiniteLocallyFreeOfRank_of_restrict_isIso (⊤ : X.Opens).ι
      ((isFiniteLocallyFreeOfRank_iff _ 1).2
        (isSingleDegreeRank_top_of_forall_derivedFiberBetti E hE (-1) 1 h).2))

/-- **Corollary (a), invertibility.** If at every point the derived fibre of the pseudo-coherent
object `E` has cohomology only in degree `-1`, of dimension `1`, then `H⁻¹(E)` is an invertible
`𝒪_X`-module. -/
theorem isInvertible_homology_of_forall_derivedFiberBetti {X : Scheme.{u}}
    (E : 𝔻ˢ[X.Modules])
    (hE : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace) E)
    (h : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      ∀ (x : X) (j : ℤ), DerivedFibreBetti.derivedFiberBetti X E hE j x =
      if j = -1 then 1 else 0) :
    letI := HasDerivedCategory.standard (X.Modules)
    letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((DerivedCategory.homologyFunctor X.Modules (-1)).obj E) :=
  let (T : Scheme.{u}) := HasDerivedCategory.standard (OXMod.{u, u} T.toRingedSpace)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  letI (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules (structureSheafRing T.toRingedSpace))
  letI (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules (structureSheafRing T.toSheafedSpace))
  let (A : Type u) [Ring A] := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard (X.Modules)
  let := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
  Stacks.ModuleDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one X _
    (isFiniteLocallyFreeOfRank_homology_of_forall_derivedFiberBetti E hE h)

/-- **Corollary (b).** If at every point the derived fibre of the pseudo-coherent object `E` has
cohomology only in degree `-1`, of dimension `1`, then `E ≅ H⁻¹(E)[1]`. -/
theorem nonempty_iso_singleFunctor_homology_of_forall_derivedFiberBetti {X : Scheme.{u}}
    (E : 𝔻ˢ[X.Modules])
    (hE : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace) E)
    (h : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      ∀ (x : X) (j : ℤ), DerivedFibreBetti.derivedFiberBetti X E hE j x =
      if j = -1 then 1 else 0) :
    letI := HasDerivedCategory.standard (X.Modules)
    letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
    Nonempty (E ≅ (DerivedCategory.singleFunctor X.Modules (-1)).obj
      ((DerivedCategory.homologyFunctor X.Modules (-1)).obj E)) :=
  let (T : Scheme.{u}) := HasDerivedCategory.standard (OXMod.{u, u} T.toRingedSpace)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  letI (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules (structureSheafRing T.toRingedSpace))
  letI (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules (structureSheafRing T.toSheafedSpace))
  let (A : Type u) [Ring A] := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard (X.Modules)
  let := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
  DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero E (-1)
    (isZero_homology_of_forall_derivedFiberBetti E hE h)

/-! ### The first component of a relative dualizing complex -/

/-- **Corollaries (a) and (b) for a relative dualizing complex.** Let `f : X ⟶ S` be flat and
locally of finite presentation and `(K, ξ)` a relative dualizing complex for `f`. If at every
point of `X` the derived fibre of `K` has cohomology only in degree `-1`, of dimension `1`, then
the cohomology sheaves of `K` vanish outside degree `-1`, `H⁻¹(K)` is finite locally free of rank
one and invertible, and `K ≅ H⁻¹(K)[1]`. The pseudo-coherence used is the one contained in the
relative perfectness of `K`. -/
theorem isRelativeDualizingComplex_shape_of_forall_derivedFiberBetti {X S : Scheme.{u}}
    (f : X ⟶ S)
    [HasDerivedCategory.{d'} (OXMod.{u, u} (RingedSpace.inverseImage S.toRingedSpace f.base))]
    [∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      HasDerivedCategory.{d'}
        (OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
          U.isOpenEmbedding))]
    [Flat f] [LocallyOfFinitePresentation f]
    (Dten : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{d', u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (D : f.DiagonalOpen) (K : 𝔻ˢ[(OXMod.{u, u} X.toRingedSpace)])
    (ξ : letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      letI := HasDerivedCategory.standard (X.Modules)
      D.diagonalObject ⟶ D.derivedPullbackProj K)
    (hK : letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      letI := HasDerivedCategory.standard (X.Modules)
      f.IsRelativeDualizingComplex Dten D K ξ)
    (h : letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      letI := HasDerivedCategory.standard (X.Modules)
      ∀ (x : X) (j : ℤ),
      DerivedFibreBetti.derivedFiberBetti X K hK.isPerfectRelativeTo.1 j x =
        if j = -1 then 1 else 0) :
    letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
    letI := HasDerivedCategory.standard (X.Modules)
    (∀ j : ℤ, j ≠ -1 → IsZero ((DerivedCategory.homologyFunctor X.Modules j).obj K)) ∧
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((DerivedCategory.homologyFunctor X.Modules (-1)).obj K) 1 ∧
      AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        ((DerivedCategory.homologyFunctor X.Modules (-1)).obj K) ∧
      Nonempty (K ≅ (DerivedCategory.singleFunctor X.Modules (-1)).obj
        ((DerivedCategory.homologyFunctor X.Modules (-1)).obj K)) :=
  let (T : Scheme.{u}) := HasDerivedCategory.standard (OXMod.{u, u} T.toRingedSpace)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  letI (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules (structureSheafRing T.toRingedSpace))
  letI (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules (structureSheafRing T.toSheafedSpace))
  let (A : Type u) [Ring A] := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
  let := HasDerivedCategory.standard (X.Modules)
  ⟨isZero_homology_of_forall_derivedFiberBetti K hK.isPerfectRelativeTo.1 h,
    isFiniteLocallyFreeOfRank_homology_of_forall_derivedFiberBetti K hK.isPerfectRelativeTo.1 h,
    isInvertible_homology_of_forall_derivedFiberBetti K hK.isPerfectRelativeTo.1 h,
    nonempty_iso_singleFunctor_homology_of_forall_derivedFiberBetti K hK.isPerfectRelativeTo.1 h⟩

end AlgebraicGeometry.PseudoCoherentFibreInvertible

end
