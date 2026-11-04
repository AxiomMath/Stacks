module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.BabyCaseTensor
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LargerClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedCap
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpen
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreEulerCharacteristicSingle

/-!
# The classes of Stacks 0F9H as localized classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `X = X₁ ∪ X₂` be a closed cover, and let `E` be a perfect object of
`D(𝒪_X)` whose restriction to `X₁` is zero, resp. a finite locally free module of rank `< p`
placed in degree `0`. Stacks 0F9H provides the class `P'_p(E|_{X₂})`, resp. `c'_p(E|_{X₂})`, in
`A^p(X₂ ⟶ X)`. If `(X, X₂, E)` satisfies the finiteness condition (3) of Situation 0GUJ, Stacks
0FB8 says that it is the localized class `P_p(X₂ ⟶ X, E)`, resp. `c_p(X₂ ⟶ X, E)`, of
Definition 0FB5.

The proof is the source's. By More on Algebra, Lemma 0BCD, `E` is zero, resp. finite locally free
of rank `< p` in degree `0`, on an open `U ⊇ X₁`. Let `Z` be the reduced closed subscheme on
`X ∖ U`; then `Z ⊆ X₂` and `Z ∩ X₁ = ∅`. By Stacks 0FB7 the localized class for `X₂` is the
pushforward along `Z ⟶ X₂` of the one for `Z`, which kills the classes from `X₁` by Stacks 0FB6;
and by Stacks 0FB4 it caps the classes from `X₂` as `P_p(E|_{X₂})`, resp. `c_p(E|_{X₂})`, does.
These are the two formulas characterizing the class of Stacks 0F9H.

The open `U` is found pointwise. At a point `x ∈ X₁` the derived fibre of `E` is computed on
`X₁`: it vanishes, resp. is a vector space of dimension `< p` in degree `0`. By derived Nakayama,
resp. by the minimal representative of Stacks 0BCC, the derived stalk of `E` at `x` vanishes,
resp. is a finite free module in degree `0`. So `x` lies in the open of Stacks 0GT1 on which the
cohomology sheaves of `E` are finite locally free, with `H^n(E)` of rank `0` at `x` for `n ≠ 0`,
and with `H^0(E)` of rank at `x` the derived-fibre Euler characteristic of `E` at `x`, which is
`< p`. The ranks being locally constant and, near every point, zero in all but finitely many
degrees, the locus of that open where `H^n(E)` has rank `0` for `n ≠ 0` and `H^0(E)` has rank
`< p` is open, and on it `E` is `H^0(E)` placed in degree `0`.

## Main definitions

* `Stacks.Chow.LocalizedSituation.withReducedComplement` — the situation of Stacks 0GUJ for
  the reduced closed subscheme on the complement of an open on which condition (2) holds.

## Main results

* `Stacks.Chow.LocalizedSituation.closedCoverPowerSum_eq_localizedPowerSum`,
  `Stacks.Chow.LocalizedSituation.closedCoverChernClass_eq_localizedChern` — **Stacks
  0FB8**.
* `LocalizedSituation.closedCoverPowerSum_eq_localizedPowerSum_withLargerClosed`,
  `LocalizedSituation.closedCoverChernClass_eq_localizedChern_withLargerClosed` (in
  the namespace `Stacks.Chow`) — the same for a situation along a closed `Z ⊆ X₂` disjoint from
  `X₁`, with `X₂` the larger closed subscheme of Stacks 0FB7.
* `Stacks.Chow.exists_opens_isZero_derivedPullback_of_isZero`,
  `Stacks.Chow.exists_opens_iso_singleFunctor_of_iso_singleFunctor` — the open neighbourhood of
  `X₁` given by Stacks 0BCD.
* `Stacks.Chow.exists_opens_iso_singleFunctor_isFiniteLocallyFreeOfRankLT` — a perfect object is
  a finite locally free module of rank `< p` in degree `0` on an open containing every point of
  the finite free locus of Stacks 0GT1 with the corresponding fibre ranks.
* `StacksDraft.Perfect.isZero_homology_and_free_of_totalDerivedExtensionScalars` — a
  pseudo-coherent complex over a local ring whose base change to a field is concentrated in
  degree `0` is a finite free module in degree `0`.

## Implementation notes

The statement takes `(X, X₂, E)` as a situation `S` of Stacks 0GUJ with `S.Z = X₂`: condition
(3) is the field `S.finiteness`, and the source's "provided `E` satisfies assumption (3)" is this
input. Condition (2) for `X₂`, which the source leaves implicit, is derived from the hypothesis on
`E|_{X₁}`, and so is the hypothesis of Stacks 0F9H on `E|_{X₂}` along `X₁ ∩ X₂`; both appear in
the statement as the proofs that derive them. The degree of `c_p` is the degree `S.p` of the
situation.

Stacks 0BCD is the ring-level statement at a prime of a ring; what the proof consumes is its
consequence at a point of a scheme, which is reached here through the local-ring form Stacks
0BCC at the derived stalk and the open of Stacks 0GT1.

## References

* [Stacks Project, Tag 0FB8](https://stacks.math.columbia.edu/tag/0FB8)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0FB5](https://stacks.math.columbia.edu/tag/0FB5)
* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
* [Stacks Project, Tag 0FB4](https://stacks.math.columbia.edu/tag/0FB4)
* [Stacks Project, Tag 0FB6](https://stacks.math.columbia.edu/tag/0FB6)
* [Stacks Project, Tag 0FB7](https://stacks.math.columbia.edu/tag/0FB7)
* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
* [Stacks Project, Tag 0BCC](https://stacks.math.columbia.edu/tag/0BCC)
* [Stacks Project, Tag 0GT1](https://stacks.math.columbia.edu/tag/0GT1)
* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-! ### Perfect complexes over a local ring whose derived fibre is concentrated in degree `0` -/

namespace StacksDraft.Perfect

open CochainComplex.DerivedExtensionScalars

attribute [local instance 2000] HasDerivedCategory.standard

/-- **Flat derived extension of scalars commutes with cohomology**: for a flat `ψ : A →+* B`,
`Hⁿ(M ⊗ᴸ_A B) ≅ Hⁿ(M) ⊗_A B` for every object `M` of `D(A)` (no perfectness, unlike
`StacksDraft.Perfect.nonempty_homology_totalDerivedExtensionScalars_iso_of_flat`), computed on a
K-flat representative of `M`. -/
theorem nonempty_homology_totalDerivedExtensionScalars_iso_of_flat_of_kFlatRepresentative
    {A B : Type u} [CommRing A] [CommRing B] (ψ : A →+* B) (hψ : ψ.Flat)
    (M : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) n).obj
        ((totalDerivedExtensionScalars.{u, u, u} ψ).functor.obj M) ≅
      (ModuleCat.extendScalars.{u, u, u} ψ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj M)) := by
  obtain ⟨P, hP, -, ⟨e⟩⟩ := exists_kFlat_representative.{u, u} M
  let D := totalDerivedExtensionScalars.{u, u, u} ψ
  let F := ModuleCat.extendScalars.{u, u, u} ψ
  have : IsIso (D.comparison.app P) := D.comparison_isIso_of_kFlat P hP
  have : F.PreservesHomology := extendScalars_preservesHomology_of_flat.{u, u} ψ hψ
  exact ⟨(DerivedCategory.homologyFunctor _ n).mapIso (D.functor.mapIso e ≪≫
      asIso (D.comparison.app P)) ≪≫ (DerivedCategory.homologyFunctorFactors _ n).app _ ≪≫
    (P.sc n).mapHomologyIso F ≪≫ F.mapIso (((DerivedCategory.homologyFunctor _ n).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ n).app P).symm)⟩

/-- **Derived extension of scalars from a field to a nonzero ring reflects vanishing of a
cohomology module**, the extension being faithfully flat. -/
theorem isZero_homology_of_isZero_homology_totalDerivedExtensionScalars_of_field {k L : Type u}
    [Field k] [CommRing L] [Nontrivial L] (ψ : k →+* L) (M : DerivedCategory (ModuleCat.{u} k))
    (n : ℤ) (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} L) n).obj
      ((totalDerivedExtensionScalars.{u, u, u} ψ).functor.obj M))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).obj M) := by
  have hflat : ψ.Flat := by
    let := ψ.toAlgebra
    show Module.Flat k L
    infer_instance
  obtain ⟨e⟩ :=
    nonempty_homology_totalDerivedExtensionScalars_iso_of_flat_of_kFlatRepresentative ψ hflat M n
  let := Module.compHom L ψ
  have hs : Subsingleton (TensorProduct k L
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).obj M)) :=
    ModuleCat.isZero_iff_subsingleton.mp (h.of_iso e.symm)
  have : Module.Free k L := Module.Free.of_divisionRing k L
  exact ModuleCat.isZero_iff_subsingleton.mpr
    ((Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right k L).mp hs)

/-- **A pseudo-coherent complex over a local ring whose derived base change along a local
homomorphism is concentrated in degree `0` is a finite free module in degree `0`**, provided the
residue map of the target is flat (for instance when the target is a field). By the minimal
representative of Stacks 0BCC, whose term in degree `i` is free of rank
`dim_κ Hⁱ(K ⊗ᴸ_R κ)`, it suffices that the derived fibre `K ⊗ᴸ_R κ` is concentrated in degree
`0`; and `K ⊗ᴸ_R κ(S) = (K ⊗ᴸ_R κ) ⊗_κ κ(S)` is concentrated in degree `0` because
`K ⊗ᴸ_R S` is and `S ⟶ κ(S)` is flat. -/
theorem isZero_homology_and_free_of_totalDerivedExtensionScalars {R S : Type u} [CommRing R]
    [IsLocalRing R] [CommRing S] [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ]
    (hS : (IsLocalRing.residue S).Flat) (K : DerivedCategory (ModuleCat.{u} R))
    (hK : PseudoCoherence.IsPseudoCoherent K)
    (h : ∀ n : ℤ, n ≠ 0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).obj
      ((totalDerivedExtensionScalars.{u, u, u} φ).functor.obj K))) :
    (∀ n : ℤ, n ≠ 0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj K)) ∧
      Module.Free R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj K) ∧
        Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj K) := by
  set res := IsLocalRing.residue R
  set ψ := IsLocalRing.ResidueField.map φ
  have hcomp : ψ.comp res = (IsLocalRing.residue S).comp φ := by
    ext x
    exact IsLocalRing.ResidueField.map_residue φ x
  have hfib : ∀ n : ℤ, n ≠ 0 → IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (IsLocalRing.ResidueField R)) n).obj
        ((totalDerivedExtensionScalars.{u, u, u} res).functor.obj K)) := by
    intro n hn
    obtain ⟨e⟩ := nonempty_homology_totalDerivedExtensionScalars_iso_of_flat_of_kFlatRepresentative
      (IsLocalRing.residue S) hS ((totalDerivedExtensionScalars.{u, u, u} φ).functor.obj K) n
    have h₁ : IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (IsLocalRing.ResidueField S)) n).obj
        ((totalDerivedExtensionScalars.{u, u, u}
          ((IsLocalRing.residue S).comp φ)).functor.obj K)) :=
      ((Functor.map_isZero _ (h n hn)).of_iso e).of_iso
        ((DerivedCategory.homologyFunctor _ n).mapIso
          ((totalDerivedExtensionScalarsComp.{u, u} φ (IsLocalRing.residue S)).app K).symm)
    rw [← hcomp] at h₁
    exact isZero_homology_of_isZero_homology_totalDerivedExtensionScalars_of_field ψ _ n
      (h₁.of_iso ((DerivedCategory.homologyFunctor _ n).mapIso
        ((totalDerivedExtensionScalarsComp.{u, u} res ψ).app K)))
  obtain ⟨-, -, -, P, -, ⟨hPX, ⟨e⟩⟩, -⟩ :=
    StacksDraft.Perfect.exists_unique_boundedAbove_free_complex_representing.{u, u} K hK
  have hzero : ∀ i : ℤ, i ≠ 0 → IsZero (P.X i) := by
    intro i hi
    refine IsZero.of_iso ?_ (hPX i).some
    have : Subsingleton ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (IsLocalRing.ResidueField R)) i).obj
          ((totalDerivedExtensionScalars.{u, u, u} res).functor.obj K)) :=
      ModuleCat.isZero_iff_subsingleton.1 (hfib i hi)
    rw [Module.finrank_zero_of_subsingleton]
    exact ModuleCat.isZero_of_subsingleton _
  have hH : ∀ n : ℤ, (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj K ≅
      P.homology n := fun n =>
    (DerivedCategory.homologyFunctor _ n).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors _ n).app P
  refine ⟨fun n hn => ((P.sc n).isZero_homology_of_isZero_X₂ (hzero n hn)).of_iso (hH n), ?_⟩
  have h₀ : P.homology 0 ≅ P.X 0 :=
    (P.isoHomologyπ (-1) 0 (by simp) ((hzero (-1) (by omega)).eq_of_src _ _)).symm ≪≫
      P.iCyclesIso 0 1 (by simp) ((hzero 1 (by omega)).eq_of_tgt _ _)
  let ε : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj K ≃ₗ[R] (Fin _ → R) :=
    (hH 0 ≪≫ h₀ ≪≫ (hPX 0).some).toLinearEquiv.trans ULift.moduleEquiv
  exact ⟨Module.Free.of_equiv ε.symm, Module.Finite.equiv ε.symm⟩

end StacksDraft.Perfect

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The locus where a perfect object is a finite locally free module in degree `0` -/

section RankLocus

/-- **The locus where infinitely many locally constant functions vanish is open**, as soon as
near every point all but finitely many of them vanish identically. -/
theorem isOpen_setOf_forall_eq_zero {T : Type*} [TopologicalSpace T] (r : ℤ → T → ℕ)
    (hr : ∀ n, IsLocallyConstant (r n))
    (hfin : ∀ τ, ∃ V : Set T, IsOpen V ∧ τ ∈ V ∧ ∃ s : Finset ℤ, ∀ n ∉ s, ∀ v ∈ V, r n v = 0)
    (N : Set ℤ) : IsOpen {τ | ∀ n ∈ N, r n τ = 0} := by
  refine isOpen_iff_forall_mem_open.2 fun τ hτ => ?_
  obtain ⟨V, hV, hτV, s, hs⟩ := hfin τ
  refine ⟨V ∩ ⋂ n ∈ s, r n ⁻¹' {r n τ}, fun v hv n hn => ?_,
    hV.inter (isOpen_biInter_finset fun n _ => hr n _), hτV, Set.mem_iInter₂.2 fun n _ => rfl⟩
  by_cases hns : n ∈ s
  · exact (Set.mem_iInter₂.1 hv.2 n hns).trans (hτ n hn)
  · exact hs n hns v hv.1

variable {X : Scheme.{u}} (E : DerivedCategory X.Modules)
  (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)

include hE in
/-- **A perfect object is a finite locally free module of rank `< p` in degree `0` on an open
containing every point at which its cohomology stalks are finite free, of fibre rank `0` in
nonzero degrees and `< p` in degree `0`.** On the open `W` of Stacks 0GT1 where the cohomology
stalks of `E` are finite free, the cohomology sheaves of `E` are finite locally free, so their
ranks are locally constant, and near every point only finitely many of them are nonzero; the
locus of `W` where `H^n(E)` has rank `0` for `n ≠ 0` and `H^0(E)` has rank `< p` is therefore
open, and on it `E` is `H^0(E)` placed in degree `0`. -/
theorem exists_opens_iso_singleFunctor_isFiniteLocallyFreeOfRankLT (p : ℕ) :
    ∃ U : X.Opens, (∀ x ∈ RingedSpace.cohomologyFiniteFreeLocus E,
        (∀ n : ℤ, n ≠ 0 → Scheme.Modules.fiberRank
          ((DerivedCategory.homologyFunctor X.Modules n).obj E) x = 0) →
        Scheme.Modules.fiberRank ((DerivedCategory.homologyFunctor X.Modules 0).obj E) x < p →
          x ∈ U) ∧
      ∃ M : U.toScheme.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          U.ι.toLRSHom.toShHom).obj E ≅
            (DerivedCategory.singleFunctor U.toScheme.Modules 0).obj M) := by
  classical
  let S₀ : ComplexAndDivisorSituation.{u, u + 1} :=
    { X := X
      D := ⊤
      isEffectiveCartierDivisor := Stacks.Divisors.isEffectiveCartierDivisor_top
      M := E
      isPerfect := hE }
  let W : X.Opens := S₀.locallyFreeLocus
  let K := (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    W.ι.toLRSHom.toShHom).obj E
  have hK : RingedSpace.IsPerfect (X := W.toScheme.toRingedSpace) K :=
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ E hE
  have hH : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((DerivedCategory.homologyFunctor W.toScheme.Modules n).obj K) := fun n => by
    have h₀ := (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2
      (S₀.isFiniteLocallyFree_locallyFreeLocusCohomologySheaf n)
    exact (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).1
      (Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso (h := h₀)
        ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app _ ≪≫
          (homologyDerivedPullbackOpenImmersionIso W.ι E n).symm))
  have hrk : ∀ (n : ℤ) (w : W.toScheme),
      @Scheme.Modules.finiteLocallyFreeRank _ _ (hH n) w =
        Scheme.Modules.fiberRank ((DerivedCategory.homologyFunctor X.Modules n).obj E)
          (W.ι w) := fun n w => by
    rw [← Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict W.ι]
    refine (@fiberRank_eq_moduleRank _ _ (hH n) w).symm.trans ?_
    exact Scheme.Modules.fiberRank_eq_of_iso
      ((homologyDerivedPullbackOpenImmersionIso W.ι E n) ≪≫
        ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app _).symm) w
  let r : ℤ → W.toScheme → ℕ := fun n => @Scheme.Modules.finiteLocallyFreeRank _ _ (hH n)
  have hopen : IsOpen {w : W.toScheme | (∀ n ∈ {n : ℤ | n ≠ 0}, r n w = 0) ∧ r 0 w < p} :=
    (isOpen_setOf_forall_eq_zero r (fun n => (@Scheme.Modules.finiteLocallyFreeRank _ _
        (hH n)).isLocallyConstant)
      (fun τ => by
        obtain ⟨V, hτ, s, hs⟩ :=
          exists_finiteLocallyFreeRank_homology_eq_zero_of_isPerfect K hK hH τ
        exact ⟨V, V.isOpen, hτ, s, hs⟩) _).inter
      ((@Scheme.Modules.finiteLocallyFreeRank _ _ (hH 0)).isLocallyConstant (Set.Iio p))
  let U' : W.toScheme.Opens := ⟨_, hopen⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_isFiniteLocallyFreeOfRankLT_derivedPullback U'.ι K hH
    (fun n y hn => y.2.1 n hn) (fun y => y.2.2)
  refine ⟨W.ι ''ᵁ U', fun x hx h0 hp => ⟨⟨x, hx⟩, ⟨fun n hn => ?_, ?_⟩, rfl⟩, ?_⟩
  · exact (hrk n ⟨x, hx⟩).trans (h0 n hn)
  · exact (hrk 0 ⟨x, hx⟩).trans_lt hp
  · exact exists_isFiniteLocallyFreeOfRankLT_derivedPullback_of_factors
      (Scheme.Hom.isoImage_inv_ι W.ι U')
      ⟨M, hM, ⟨(derivedPullbackCompIsoOfScheme U'.ι W.ι E).symm ≪≫ e⟩⟩

/-- **A perfect object whose derived stalk at `x` vanishes vanishes near `x`**, in the form that
`x` lies in the finite free locus of Stacks 0GT1 with all cohomology sheaves of fibre rank `0`
there: the cohomology stalks of `E` at `x` are the cohomology of its derived stalk, the stalk
functor being exact. -/
theorem mem_cohomologyFiniteFreeLocus_of_isZero_derivedStalkFunctor (x : X)
    (h : IsZero ((derivedStalkFunctor x).obj E)) :
    x ∈ RingedSpace.cohomologyFiniteFreeLocus E ∧ ∀ n : ℤ,
      Scheme.Modules.fiberRank ((DerivedCategory.homologyFunctor X.Modules n).obj E) x = 0 := by
  have hs : ∀ n : ℤ, Subsingleton
      (ToType (((DerivedCategory.homologyFunctor X.Modules n).obj E).presheaf.stalk x)) := by
    intro n
    have hz : IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj
        ((DerivedCategory.homologyFunctor X.Modules n).obj E)) :=
      (Functor.map_isZero (DerivedCategory.homologyFunctor _ n) h).of_iso
        (((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryHomologyIso
          n).app E).symm
    exact ModuleCat.subsingleton_of_isZero hz
  refine ⟨fun n => ?_, fun n => Scheme.Modules.fiberRank_eq_zero_of_subsingleton_stalk _ _ (hs n)⟩
  have h' := hs n
  refine ⟨@Module.Free.of_subsingleton _ _ _ _ _ h', ⟨⟨∅, top_unique fun m _ => ?_⟩⟩⟩
  rw [@Subsingleton.elim _ h' m 0]
  exact Submodule.zero_mem _

/-- **A point at which the derived stalk of `E` is a finite free module in degree `0` lies in the
finite free locus of Stacks 0GT1**, with all cohomology sheaves in nonzero degrees of fibre rank
`0` there: the cohomology stalks of `E` are the cohomology of its derived stalk, the stalk functor
being exact. -/
theorem mem_cohomologyFiniteFreeLocus_of_derivedStalkFunctor (x : X)
    (h₁ : ∀ n : ℤ, n ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) n).obj
      ((derivedStalkFunctor x).obj E)))
    (h₂ : Module.Free (X.presheaf.stalk x)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj
        ((derivedStalkFunctor x).obj E)))
    (h₃ : Module.Finite (X.presheaf.stalk x)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj
        ((derivedStalkFunctor x).obj E))) :
    x ∈ RingedSpace.cohomologyFiniteFreeLocus E ∧ ∀ n : ℤ, n ≠ 0 →
      Scheme.Modules.fiberRank ((DerivedCategory.homologyFunctor X.Modules n).obj E) x = 0 := by
  let eH : ∀ n : ℤ, (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj
      ((DerivedCategory.homologyFunctor X.Modules n).obj E) ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) n).obj
          ((derivedStalkFunctor x).obj E) :=
    fun n => (((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryHomologyIso
      n).app E).symm
  have hs : ∀ n : ℤ, n ≠ 0 → Subsingleton
      (ToType (((DerivedCategory.homologyFunctor X.Modules n).obj E).presheaf.stalk x)) :=
    fun n hn => ModuleCat.subsingleton_of_isZero ((h₁ n hn).of_iso (eH n))
  refine ⟨fun n => ?_, fun n hn => Scheme.Modules.fiberRank_eq_zero_of_subsingleton_stalk _ _
    (hs n hn)⟩
  rcases eq_or_ne n 0 with rfl | hn
  · exact ⟨Module.Free.of_equiv (eH 0).toLinearEquiv.symm,
      Module.Finite.equiv (eH 0).toLinearEquiv.symm⟩
  · have h' := hs n hn
    refine ⟨@Module.Free.of_subsingleton _ _ _ _ _ h', ⟨⟨∅, top_unique fun m _ => ?_⟩⟩⟩
    rw [@Subsingleton.elim _ h' m 0]
    exact Submodule.zero_mem _

include hE in
/-- **A perfect object whose derived pullback to a point is concentrated in degree `0` has, at
the image point, a derived stalk which is a finite free module in degree `0`.** Let `f : T ⟶ X`
and `t : T` be such that the local ring of `T` at `t` is a field and the cohomology of `Lf^*E`
vanishes in nonzero degrees. The derived stalk of `Lf^*E` at `t` is the derived base change of
the derived stalk of `E` at `f t` along the local homomorphism `𝒪_{X, f t} ⟶ 𝒪_{T, t}`; by the
minimal representative of Stacks 0BCC the latter is a finite free module in degree `0`. -/
theorem derivedStalkFunctor_of_isZero_homology_derivedPullback {T : Scheme.{u}} (f : T ⟶ X)
    (t : T) (hfield : IsField (T.presheaf.stalk t))
    (hL : ∀ n : ℤ, n ≠ 0 → IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom).obj E))) :
    (∀ n : ℤ, n ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk (f t))) n).obj
      ((derivedStalkFunctor (f t)).obj E))) ∧
      Module.Free (X.presheaf.stalk (f t))
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk (f t))) 0).obj
          ((derivedStalkFunctor (f t)).obj E)) ∧
      Module.Finite (X.presheaf.stalk (f t))
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk (f t))) 0).obj
          ((derivedStalkFunctor (f t)).obj E)) := by
  have : (Stacks.ModuleSkyscraper.modulesStalkFunctor T t).Additive :=
    modulesStalkFunctor_additive t
  have : PreservesFiniteLimits (Stacks.ModuleSkyscraper.modulesStalkFunctor T t) :=
    modulesStalkFunctor_preservesFiniteLimits t
  have : IsLocalHom (f.stalkMap t).hom := f.prop t
  have hres : (IsLocalRing.residue (T.presheaf.stalk t)).Flat := by
    refine RingHom.Flat.of_bijective ⟨?_, IsLocalRing.residue_surjective⟩
    rw [RingHom.injective_iff_ker_eq_bot, IsLocalRing.ker_residue]
    exact (IsLocalRing.isField_iff_maximalIdeal_eq).1 hfield
  refine StacksDraft.Perfect.isZero_homology_and_free_of_totalDerivedExtensionScalars
    (f.stalkMap t).hom hres _ (isPseudoCoherent_derivedStalkFunctor_obj E hE (f t))
    fun n hn => ?_
  exact (Functor.map_isZero (Stacks.ModuleSkyscraper.modulesStalkFunctor T t)
    (hL n hn)).of_iso ((DerivedCategory.homologyFunctor _ n).mapIso
      ((derivedPullbackStalkIso f t).app E).symm ≪≫
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor T t).mapDerivedCategoryHomologyIso
          n).app _)

include hE in
/-- **At a point of a closed subscheme on which `E` is a finite locally free module in degree `0`,
the cohomology stalks of `E` are finite free and vanish in nonzero degrees.** The derived fibre
of `E` at `x = i₁ y`, computed through `Spec κ(y) ⟶ X₁ ⟶ X`, is a vector space in degree `0`. -/
theorem mem_cohomologyFiniteFreeLocus_of_iso_singleFunctor {X₁ : Scheme.{u}} (i₁ : X₁ ⟶ X)
    (M : X₁.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M]
    (e : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback i₁.toLRSHom.toShHom).obj E ≅
      (DerivedCategory.singleFunctor _ 0).obj M) (y : X₁) :
    i₁ y ∈ RingedSpace.cohomologyFiniteFreeLocus E ∧ ∀ n : ℤ, n ≠ 0 →
      Scheme.Modules.fiberRank ((DerivedCategory.homologyFunctor X.Modules n).obj E) (i₁ y) =
        0 := by
  have hpt : (X₁.fromSpecResidueField y ≫ i₁) (IsLocalRing.closedPoint (X₁.residueField y)) =
      i₁ y :=
    congrArg i₁.base (X₁.fromSpecResidueField_apply y _)
  have hfield : IsField ((Spec (X₁.residueField y)).presheaf.stalk
      (IsLocalRing.closedPoint (X₁.residueField y))) :=
    MulEquiv.isField (Field.toIsField _)
      (stalkClosedPointIso (X₁.residueField y)).commRingCatIsoToRingEquiv.toMulEquiv
  have eL := (derivedPullbackCompIsoOfScheme (X₁.fromSpecResidueField y) i₁ E).symm ≪≫
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X₁.fromSpecResidueField y).toLRSHom.toShHom).mapIso e ≪≫
    derivedPullbackSingleIsoOfIsFiniteLocallyFree _ M
  obtain ⟨h₁, h₂, h₃⟩ := derivedStalkFunctor_of_isZero_homology_derivedPullback E hE _ _ hfield
    fun n hn => (Scheme.Modules.isZero_homologyFunctor_singleFunctor_obj _ hn).of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso eL)
  rw [← hpt]
  exact mem_cohomologyFiniteFreeLocus_of_derivedStalkFunctor E _ h₁ h₂ h₃

include hE in
/-- **Stacks 0BCD, the case of a vanishing restriction.** If a perfect object `E` of `D(𝒪_X)`
restricts to zero on a closed subscheme `X₁ ⊆ X`, then it restricts to zero on an open
neighbourhood `U` of `X₁`. At a point `x ∈ X₁` the derived fibre of `E` factors through `X₁`,
so it vanishes; by derived Nakayama the derived stalk of `E` at `x` vanishes, and
`Stacks.Chow.exists_opens_iso_singleFunctor_isFiniteLocallyFreeOfRankLT` for `p = 1` gives the
open. -/
theorem exists_opens_isZero_derivedPullback_of_isZero {X₁ : Scheme.{u}} (i₁ : X₁ ⟶ X)
    [IsClosedImmersion i₁]
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      i₁.toLRSHom.toShHom).obj E)) :
    ∃ U : X.Opens, Set.range i₁ ⊆ U ∧
      IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        U.ι.toLRSHom.toShHom).obj E) := by
  obtain ⟨U, hU, M, hM, ⟨e⟩⟩ := exists_opens_iso_singleFunctor_isFiniteLocallyFreeOfRankLT E hE 1
  refine ⟨U, fun x hx => ?_, (Functor.map_isZero (DerivedCategory.singleFunctor _ 0)
    (isZero_of_isFiniteLocallyFreeOfRankLT_one hM)).of_iso e⟩
  have hfib : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X.fromSpecResidueField x).toLRSHom.toShHom).obj E) :=
    isZero_derivedPullback_of_range_subset i₁ _
      (by rw [Scheme.range_fromSpecResidueField]; exact Set.singleton_subset_iff.2 hx) hzero
  obtain ⟨hx₁, hx₂⟩ := mem_cohomologyFiniteFreeLocus_of_isZero_derivedStalkFunctor E x
    (isZero_derivedStalkFunctor_obj_of_isZero_derivedPullback E hE x hfib)
  exact hU x hx₁ (fun n _ => hx₂ n) ((hx₂ 0).trans_lt Nat.one_pos)

/-- The derived-fibre Euler characteristic of `E` at `i₁ y` is the rank `r` of `M` near `y`, when
the derived pullback of `E` along `i₁ : X₁ ⟶ X` is `M` placed in degree `0`. -/
private theorem chiDerivedFibre_eq_of_iso_singleFunctor
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) {X₁ : Scheme.{u}} (i₁ : X₁ ⟶ X)
    (M : X₁.Modules)
    (e : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback i₁.toLRSHom.toShHom).obj E ≅
      (DerivedCategory.singleFunctor _ 0).obj M) (V : X₁.Opens) (r : ℕ)
    (hr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := StrictlyPerfect.structureSheafOfRings (X₁.toRingedSpace.restrict V.isOpenEmbedding))
      ((RingedSpace.PseudoCoherence.restrictModules X₁.toRingedSpace V).obj M) r)
    (y : X₁) (hyV : y ∈ V) :
    DerivedFibreBetti.chiDerivedFibre X E (DerivedFibreBetti.isPseudoCoherent_of_isPerfect E hE)
      (i₁ y) = r := by
  have hpc := DerivedFibreBetti.isPseudoCoherent_derivedPullback i₁ E
    (DerivedFibreBetti.isPseudoCoherent_of_isPerfect E hE)
  have hpc' : RingedSpace.IsPseudoCoherent (X := X₁.toRingedSpace)
      ((DerivedCategory.singleFunctor _ 0).obj M) := by
    obtain ⟨K, hK, ⟨v⟩⟩ := hpc
    exact ⟨K, hK, ⟨v ≪≫ e⟩⟩
  exact (congrFun (DerivedFibreBetti.chiDerivedFibre_derivedPullback i₁ E
    (DerivedFibreBetti.isPseudoCoherent_of_isPerfect E hE)) y).symm.trans
    ((congrFun (DerivedFibreBetti.chiDerivedFibre_congr _ hpc hpc' e) y).trans
      (DerivedFibreBetti.chiDerivedFibre_singleFunctor_eq_of_restrict X₁ M hpc' V r hr y hyV))

include hE in
/-- **At a point of the finite free locus where the cohomology sheaves of `E` in nonzero degrees
have fibre rank `0`, the derived-fibre Euler characteristic of `E` is the fibre rank of
`H^0(E)`**: near such a point `E` is `H^0(E)` placed in degree `0`
(`Stacks.Chow.exists_opens_iso_singleFunctor_isFiniteLocallyFreeOfRankLT`), and the Euler
characteristic of a finite locally free module in degree `0` is its rank. -/
theorem chiDerivedFibre_eq_fiberRank (x : X) (hx : x ∈ RingedSpace.cohomologyFiniteFreeLocus E)
    (h0 : ∀ n : ℤ, n ≠ 0 → Scheme.Modules.fiberRank
      ((DerivedCategory.homologyFunctor X.Modules n).obj E) x = 0) :
    DerivedFibreBetti.chiDerivedFibre X E (DerivedFibreBetti.isPseudoCoherent_of_isPerfect E hE)
        x =
      Scheme.Modules.fiberRank ((DerivedCategory.homologyFunctor X.Modules 0).obj E) x := by
  obtain ⟨U, hU, M, hM, ⟨e⟩⟩ := exists_opens_iso_singleFunctor_isFiniteLocallyFreeOfRankLT E hE
    (Scheme.Modules.fiberRank ((DerivedCategory.homologyFunctor X.Modules 0).obj E) x + 1)
  have hxU : x ∈ U := hU x hx h0 (Nat.lt_succ_self _)
  let x' : U.toScheme := ⟨x, hxU⟩
  obtain ⟨V, hxV, r, -, hr⟩ := hM.2 x'
  have hχ : DerivedFibreBetti.chiDerivedFibre X E
      (DerivedFibreBetti.isPseudoCoherent_of_isPerfect E hE) x = r :=
    chiDerivedFibre_eq_of_iso_singleFunctor E hE U.ι M e V r hr x' hxV
  have eM : M ≅ (Scheme.Modules.restrictFunctor U.ι).obj
      ((DerivedCategory.homologyFunctor X.Modules 0).obj E) :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm ≪≫
      (DerivedCategory.homologyFunctor _ 0).mapIso e.symm ≪≫
      homologyDerivedPullbackOpenImmersionIso U.ι E 0 ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app _).symm
  have h2 : Scheme.Modules.fiberRank M x' =
      Scheme.Modules.fiberRank ((DerivedCategory.homologyFunctor X.Modules 0).obj E) x :=
    (Scheme.Modules.fiberRank_eq_of_iso eM x').trans
      (Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict U.ι _ x')
  have h3 : Scheme.Modules.fiberRank M x' = r := by
    let V' : U.toScheme.Opens := V
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.restrictFunctor V'.ι).obj M) r :=
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
        ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict U.toScheme
          V').app M) hr
    exact (Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict V'.ι M ⟨x', hxV⟩).symm.trans
      (Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank _ r _)
  rw [hχ, ← h2, h3]

include hE in
/-- **Stacks 0BCD, the case of a finite locally free restriction.** If a perfect object `E` of
`D(𝒪_X)` restricts on a closed subscheme `X₁ ⊆ X` to a finite locally free module of rank `< p`
placed in degree `0`, then so it does on an open neighbourhood `U` of `X₁`. At a point `x ∈ X₁`
the derived fibre of `E` is a vector space of dimension `< p` in degree `0`; by the minimal
representative of Stacks 0BCC the derived stalk of `E` at `x` is then a finite free module in
degree `0`, so `x` lies in the finite free locus of Stacks 0GT1 with `H^n(E)` of rank `0` for
`n ≠ 0`, and the rank of `H^0(E)` at `x` is the Euler characteristic of the derived fibre, which
is `< p`. -/
theorem exists_opens_iso_singleFunctor_of_iso_singleFunctor {X₁ : Scheme.{u}} (i₁ : X₁ ⟶ X)
    {p : ℕ} (hrank : ∃ M : X₁.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        i₁.toLRSHom.toShHom).obj E ≅ (DerivedCategory.singleFunctor _ 0).obj M)) :
    ∃ U : X.Opens, Set.range i₁ ⊆ U ∧
      ∃ M : U.toScheme.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          U.ι.toLRSHom.toShHom).obj E ≅
            (DerivedCategory.singleFunctor U.toScheme.Modules 0).obj M) := by
  obtain ⟨M₁, hM₁, ⟨e₁⟩⟩ := hrank
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M₁ := hM₁.1
  obtain ⟨U, hU, hrest⟩ := exists_opens_iso_singleFunctor_isFiniteLocallyFreeOfRankLT E hE p
  refine ⟨U, ?_, hrest⟩
  rintro _ ⟨y, rfl⟩
  obtain ⟨hx, h0⟩ := mem_cohomologyFiniteFreeLocus_of_iso_singleFunctor E hE i₁ M₁ e₁ y
  refine hU _ hx h0 ?_
  obtain ⟨V, hyV, r, hrp, hr⟩ := hM₁.2 y
  have h4 := chiDerivedFibre_eq_of_iso_singleFunctor E hE i₁ M₁ e₁ V r hr y hyV
  have h5 := chiDerivedFibre_eq_fiberRank E hE _ hx h0
  omega

end RankLocus

end Stacks.Chow

namespace Stacks.Chow.LocalizedSituation

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The characterization through a smaller closed subscheme -/

section Characterization

variable {S : LocalizedSituation.{u}}
  {X₁ X₂ : Scheme.{u}} {i₁ : X₁ ⟶ S.X} [IsClosedImmersion i₁] {i₂ : X₂ ⟶ S.X}
  [IsClosedImmersion i₂] {j : S.Z ⟶ X₂} [IsClosedImmersion j] {hj : j ≫ i₂ = S.i}
  (hE₂ : HasDefinedChernClasses
    ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback i₂.toLRSHom.toShHom).obj
      (S.E : DerivedCategory S.X.Modules)))

include hE₂ in
/-- **`P_p(X₂ ⟶ X, E)` satisfies the characterization of Stacks 0F9H**, when `E` is zero away
from a closed subscheme `Z ⊆ X₂` disjoint from `X₁`. -/
theorem isClosedCoverExtension_localizedPowerSum_withLargerClosed
    (h : S.IsZeroOnComplement) (hdisj : Disjoint (Set.range i₁) (Set.range S.i)) (p : ℕ) :
    IsClosedCoverExtension S.base (gysinSystemOfInvertible S.base) S.a i₁ i₂ (i₂ ≫ S.a) rfl
      (perfectPowerSumComponent S.base (i₂ ≫ S.a) hE₂ p)
      ((S.withLargerClosed i₂ j hj).localizedPowerSum h.withLargerClosed p) := by
  refine isClosedCoverExtension_of_capVanishesOver i₁ ?_ ?_
  · intro T g hg k α
    have : @LocallyOfFiniteType T (S.withLargerClosed i₂ j hj).X g := hg
    exact (S.withLargerClosed i₂ j hj).localizedPowerSum_cap_chowPush h.withLargerClosed p g k α
  · rw [localizedPowerSum_withLargerClosed]
    exact ((localizedPowerSum_capVanishesOver h p i₁ hdisj).congrHom hj.symm
      (by rw [hj])).bivariantProperPushforward j i₂ (by rw [← Category.assoc, hj]) rfl

include hE₂ in
/-- **`c_p(X₂ ⟶ X, E)` satisfies the characterization of Stacks 0F9H**, when `E` is finite
locally free of rank `< p` in degree `0` away from a closed subscheme `Z ⊆ X₂` disjoint from
`X₁`. -/
theorem isClosedCoverExtension_localizedChern_withLargerClosed
    (h : S.IsFiniteLocallyFreeOfRankLTOnComplement)
    (hdisj : Disjoint (Set.range i₁) (Set.range S.i)) :
    IsClosedCoverExtension S.base (gysinSystemOfInvertible S.base) S.a i₁ i₂ (i₂ ≫ S.a) rfl
      (perfectChernClass S.base (i₂ ≫ S.a) hE₂ S.p)
      ((S.withLargerClosed i₂ j hj).localizedChern h.withLargerClosed) := by
  refine isClosedCoverExtension_of_capVanishesOver i₁ ?_ ?_
  · intro T g hg k α
    have : @LocallyOfFiniteType T (S.withLargerClosed i₂ j hj).X g := hg
    exact (S.withLargerClosed i₂ j hj).localizedChern_cap_chowPush h.withLargerClosed g k α
  · rw [localizedChern_withLargerClosed]
    exact ((localizedChern_capVanishesOver h i₁ hdisj).congrHom hj.symm
      (by rw [hj])).bivariantProperPushforward j i₂ (by rw [← Category.assoc, hj]) rfl

variable (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)

/-- **`P'_p(E₂) = P_p(X₂ ⟶ X, E)`**, when `E` is zero away from a closed subscheme `Z ⊆ X₂`
disjoint from `X₁`: by uniqueness in Stacks 0F9H. -/
theorem closedCoverPowerSum_eq_localizedPowerSum_withLargerClosed
    (h : S.IsZeroOnComplement) (hdisj : Disjoint (Set.range i₁) (Set.range S.i)) (p : ℕ)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁ i₂).toLRSHom.toShHom).obj
        ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback i₂.toLRSHom.toShHom).obj
          (S.E : DerivedCategory S.X.Modules)))) :
    closedCoverPowerSum S.base S.a i₁ i₂ (i₂ ≫ S.a) rfl hE₂ p hcover hzero =
      (S.withLargerClosed i₂ j hj).localizedPowerSum h.withLargerClosed p :=
  (eq_closedCoverPowerSum_of_isClosedCoverExtension S.base S.a i₁ i₂ (i₂ ≫ S.a) rfl hE₂ p
    hcover hzero
    (isClosedCoverExtension_localizedPowerSum_withLargerClosed hE₂ h hdisj p)).symm

/-- **`c'_p(E₂) = c_p(X₂ ⟶ X, E)`**, when `E` is finite locally free of rank `< p` in degree `0`
away from a closed subscheme `Z ⊆ X₂` disjoint from `X₁`: by uniqueness in Stacks 0F9H. -/
theorem closedCoverChernClass_eq_localizedChern_withLargerClosed
    (h : S.IsFiniteLocallyFreeOfRankLTOnComplement)
    (hdisj : Disjoint (Set.range i₁) (Set.range S.i))
    (hrank : ∃ M : (pullback i₁ i₂).Modules, IsFiniteLocallyFreeOfRankLT M S.p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.snd i₁ i₂).toLRSHom.toShHom).obj
          ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback i₂.toLRSHom.toShHom).obj
            (S.E : DerivedCategory S.X.Modules)) ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    closedCoverChernClass S.base S.a i₁ i₂ (i₂ ≫ S.a) rfl hE₂ S.p hcover hrank =
      (S.withLargerClosed i₂ j hj).localizedChern h.withLargerClosed :=
  (eq_closedCoverChernClass_of_isClosedCoverExtension S.base S.a i₁ i₂ (i₂ ≫ S.a) rfl hE₂ S.p
    hcover hrank
    (isClosedCoverExtension_localizedChern_withLargerClosed hE₂ h hdisj)).symm

end Characterization

/-! ### The situation for the reduced complement of an open -/

section ReducedComplement

variable (S : LocalizedSituation.{u}) (U : S.X.Opens)

/-- The reduced closed subscheme of `X` on the complement of an open `U`, as an ideal sheaf: the
vanishing ideal of `X ∖ U`. -/
abbrev reducedComplementIdeal : S.X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    (⟨(U : Set S.X)ᶜ, U.isOpen.isClosed_compl⟩ : TopologicalSpace.Closeds S.X)

/-- The reduced closed subscheme on `X ∖ U` has underlying set `X ∖ U`. -/
theorem range_reducedComplementIdeal_subschemeι :
    Set.range (S.reducedComplementIdeal U).subschemeι = (U : Set S.X)ᶜ :=
  Scheme.IdealSheafData.range_subschemeι_vanishingIdeal _

/-- A set contained in `U` is disjoint from the reduced closed subscheme on `X ∖ U`. -/
private theorem disjoint_range_reducedComplementIdeal_subschemeι {X₁ : Scheme.{u}} (i₁ : X₁ ⟶ S.X)
    (hU : Set.range i₁ ⊆ U) :
    Disjoint (Set.range i₁) (Set.range (S.reducedComplementIdeal U).subschemeι) := by
  rw [range_reducedComplementIdeal_subschemeι]
  exact Set.disjoint_compl_right_iff_subset.2 hU

/-- The complement of the reduced closed subscheme on `X ∖ U` is `U`. -/
theorem compl_range_reducedComplementIdeal_subschemeι :
    (⟨(Set.range (S.reducedComplementIdeal U).subschemeι.base)ᶜ,
      (S.reducedComplementIdeal U).subschemeι.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
        S.X.Opens) = U := by
  ext x
  show x ∈ (Set.range (S.reducedComplementIdeal U).subschemeι)ᶜ ↔ _
  rw [range_reducedComplementIdeal_subschemeι, compl_compl]

/-- **The situation of Stacks 0GUJ for the reduced complement of an open.** For an open `U ⊆ X`
on which `E` is zero, resp. a finite locally free module of rank `< p` placed in degree `0`, the
situation for `X`, the reduced closed subscheme `Z` on `X ∖ U`, and `E`; the base, the degree and
the finiteness condition (3) are those of `S`. -/
def withReducedComplement
    (hU : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (S.X.toRingedSpace.ofRestrict U.isOpenEmbedding)).obj S.E) ∨
      ∃ M : StrictlyPerfect.OXMod.{u, u, u} (S.X.toRingedSpace.restrict U.isOpenEmbedding),
        IsFiniteLocallyFreeOfRankLT M S.p ∧
          Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            (S.X.toRingedSpace.ofRestrict U.isOpenEmbedding)).obj S.E ≅
              (DerivedCategory.singleFunctor _ 0).obj M)) :
    LocalizedSituation.{u} where
  base := S.base
  X := S.X
  a := S.a
  Z := (S.reducedComplementIdeal U).subscheme
  i := (S.reducedComplementIdeal U).subschemeι
  E := S.E
  p := S.p
  perfect := S.perfect
  restriction := (S.compl_range_reducedComplementIdeal_subschemeι U).symm ▸ hU
  finiteness := S.finiteness

/-- **The reduced closed subscheme on `X ∖ U` lies in `Z` when `X ∖ U ⊆ Z`**: a closed immersion
`(X ∖ U)_red ⟶ Z` over `X`, the source being reduced (Stacks 0356). -/
theorem exists_isClosedImmersion_reducedComplementIdeal (hU : (U : Set S.X)ᶜ ⊆ Set.range S.i) :
    ∃ j : (S.reducedComplementIdeal U).subscheme ⟶ S.Z, IsClosedImmersion j ∧
      j ≫ S.i = (S.reducedComplementIdeal U).subschemeι := by
  obtain ⟨g, hg⟩ := (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support
    S.i.ker (S.reducedComplementIdeal U).subschemeι).2 (by
      rw [Scheme.Hom.support_ker, range_reducedComplementIdeal_subschemeι]
      exact hU.trans subset_closure)
  have hj : (g ≫ inv S.i.toImage) ≫ S.i = (S.reducedComplementIdeal U).subschemeι := by
    rw [Category.assoc, inv_toImage_comp, hg]
  have : IsClosedImmersion ((g ≫ inv S.i.toImage) ≫ S.i) := by
    rw [hj]
    infer_instance
  exact ⟨_, IsClosedImmersion.of_comp _ S.i, hj⟩

end ReducedComplement

/-! ### Stacks 0FB8 -/

section ClosedCover

variable (S : LocalizedSituation.{u}) {X₁ : Scheme.{u}} (i₁ : X₁ ⟶ S.X)
  [IsClosedImmersion i₁] (hcover : Set.range i₁ ∪ Set.range S.i = Set.univ)

omit [IsClosedImmersion i₁] in
include hcover in
/-- Every point of `X ∖ Z` lies on `X₁`, for a closed cover `X = X₁ ∪ Z`. -/
theorem compl_range_subset_range (x : S.X) (hx : x ∉ Set.range S.i) : x ∈ Set.range i₁ := by
  have h : x ∈ Set.range i₁ ∪ Set.range S.i := hcover ▸ Set.mem_univ x
  exact h.resolve_right hx

omit [IsClosedImmersion i₁] in
include hcover in
/-- For an open `U` containing `X₁`, of a closed cover `X = X₁ ∪ Z`, `X ∖ U ⊆ Z`. -/
theorem compl_subset_range_of_range_subset {U : S.X.Opens} (hU : Set.range i₁ ⊆ U) :
    (U : Set S.X)ᶜ ⊆ Set.range S.i := fun x hx => by
  by_contra h
  exact hx (hU (compl_range_subset_range S i₁ hcover x h))

omit [IsClosedImmersion i₁] in
include hcover in
/-- For an open `U` containing `X₁`, of a closed cover `X = X₁ ∪ Z`, `X ∖ Z ⊆ U`. -/
theorem compl_range_le_of_range_subset {U : S.X.Opens} (hU : Set.range i₁ ⊆ U) :
    (⟨(Set.range S.i.base)ᶜ, S.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
      S.X.Opens) ≤ U :=
  fun x hx => hU (compl_range_subset_range S i₁ hcover x hx)

include hcover in
/-- **Condition (2) of Situation 0GUJ for `Z = X₂`, from the vanishing on `X₁`.** If `E|_{X₁}` is
zero for a closed cover `X = X₁ ∪ Z`, then `E|_{X ∖ Z}` is zero: `X ∖ Z` lies in an open
neighbourhood of `X₁` on which `E` vanishes
(`Stacks.Chow.exists_opens_isZero_derivedPullback_of_isZero`). -/
theorem isZeroOnComplement_of_isZero_derivedPullback
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      i₁.toLRSHom.toShHom).obj (S.E : DerivedCategory S.X.Modules))) :
    S.IsZeroOnComplement := by
  obtain ⟨U, hU₁, hU⟩ := exists_opens_isZero_derivedPullback_of_isZero S.E S.perfect i₁ hzero
  exact isZero_derivedPullback_of_factors (i := Scheme.Opens.ι _) (k := Scheme.Opens.ι _)
    (S.X.homOfLE_ι (compl_range_le_of_range_subset S i₁ hcover hU₁)) hU

omit [IsClosedImmersion i₁] in
include hcover in
/-- **Condition (2) of Situation 0GUJ for `Z = X₂`, from the restriction to `X₁`.** If `E|_{X₁}`
is a finite locally free module of rank `< p` in degree `0` for a closed cover `X = X₁ ∪ Z`, then
so is `E|_{X ∖ Z}`: `X ∖ Z` lies in an open neighbourhood of `X₁` on which `E` is such a module
(`Stacks.Chow.exists_opens_iso_singleFunctor_of_iso_singleFunctor`). -/
theorem isFiniteLocallyFreeOfRankLTOnComplement_of_iso_singleFunctor
    (hrank : ∃ M : X₁.Modules, IsFiniteLocallyFreeOfRankLT M S.p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        i₁.toLRSHom.toShHom).obj (S.E : DerivedCategory S.X.Modules) ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    S.IsFiniteLocallyFreeOfRankLTOnComplement := by
  obtain ⟨U, hU₁, hU⟩ := exists_opens_iso_singleFunctor_of_iso_singleFunctor S.E S.perfect i₁
    hrank
  exact exists_isFiniteLocallyFreeOfRankLT_derivedPullback_of_factors (i := Scheme.Opens.ι _)
    (k := Scheme.Opens.ι _) (S.X.homOfLE_ι (compl_range_le_of_range_subset S i₁ hcover hU₁)) hU

/-- **Stacks 0FB8, for `P_p`.** Let `X = X₁ ∪ X₂` be a closed cover, let `E` be a perfect object
of `D(𝒪_X)` whose restriction to `X₁` is zero, and let `(X, X₂, E)` satisfy the finiteness
condition (3) of Situation 0GUJ, i.e. form a situation `S` with `S.Z = X₂`. Then the class
`P'_p(E|_{X₂}) ∈ A^p(X₂ ⟶ X)` of Stacks 0F9H agrees with the localized class
`P_p(X₂ ⟶ X, E)` of Definition 0FB5. Condition (2) of Situation 0GUJ for `X₂` is
`Stacks.Chow.LocalizedSituation.isZeroOnComplement_of_isZero_derivedPullback`, and the
vanishing of `E|_{X₂}` on `X₁ ∩ X₂` is that of `E|_{X₁}`.

By Stacks 0BCD `E` vanishes on an open `U ⊇ X₁`; let `Z` be the reduced closed subscheme on
`X ∖ U`, so that `Z ⊆ X₂` and `Z ∩ X₁ = ∅`. By Stacks 0FB7 `P_p(X₂ ⟶ X, E)` is pushed forward from
`P_p(Z ⟶ X, E)`, which kills the classes from `X₁` by Stacks 0FB6; and it caps the classes from
`X₂` as `P_p(E|_{X₂})` does by Stacks 0FB4. Uniqueness in Stacks 0F9H concludes. -/
@[stacks 0FB8 "for P_p: P'_p(E₂) = P_p(X₂ → X, E) when E|_{X₁} is zero"]
theorem closedCoverPowerSum_eq_localizedPowerSum
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      i₁.toLRSHom.toShHom).obj (S.E : DerivedCategory S.X.Modules))) (p : ℕ) :
    closedCoverPowerSum S.base S.a i₁ S.i (S.i ≫ S.a) rfl
        (S.hasDefinedChernClasses_E.derivedPullback S.i) p hcover
        (isZero_derivedPullback_of_isZero_of_comp_eq pullback.condition hzero) =
      S.localizedPowerSum (S.isZeroOnComplement_of_isZero_derivedPullback i₁ hcover hzero) p := by
  obtain ⟨U, hU₁, hU⟩ := exists_opens_isZero_derivedPullback_of_isZero S.E S.perfect i₁ hzero
  obtain ⟨j, hj, hjS⟩ := S.exists_isClosedImmersion_reducedComplementIdeal U
    (compl_subset_range_of_range_subset S i₁ hcover hU₁)
  let T := S.withReducedComplement U (Or.inl hU)
  have hT : T.IsZeroOnComplement :=
    isZero_derivedPullback_of_factors (i := Scheme.Opens.ι _) (k := Scheme.Opens.ι _)
      (S.X.homOfLE_ι (S.compl_range_reducedComplementIdeal_subschemeι U).le) hU
  have : @IsClosedImmersion X₁ T.X i₁ := ‹_›
  have : @IsClosedImmersion S.Z T.X S.i := S.isClosedImmersion
  have : @IsClosedImmersion T.Z S.Z j := hj
  have hdisj : Disjoint (Set.range i₁) (Set.range T.i) :=
    disjoint_range_reducedComplementIdeal_subschemeι S U i₁ hU₁
  exact closedCoverPowerSum_eq_localizedPowerSum_withLargerClosed (S := T) (i₂ := S.i)
    (hj := hjS) _ hcover hT hdisj p _

/-- **Stacks 0FB8, for `c_p`.** Let `X = X₁ ∪ X₂` be a closed cover, let `E` be a perfect object
of `D(𝒪_X)` whose restriction to `X₁` is a finite locally free module of rank `< p` placed in
degree `0`, and let `(X, X₂, E)` satisfy the finiteness condition (3) of Situation 0GUJ, i.e.
form a situation `S` with `S.Z = X₂` and `S.p = p`. Then the class `c'_p(E|_{X₂}) ∈ A^p(X₂ ⟶ X)`
of Stacks 0F9H agrees with the localized Chern class `c_p(X₂ ⟶ X, E)` of Definition 0FB5.
Condition (2) of Situation 0GUJ for `X₂` is
`Stacks.Chow.LocalizedSituation.isFiniteLocallyFreeOfRankLTOnComplement_of_iso_singleFunctor`,
and the hypothesis of Stacks 0F9H on `E|_{X₂}` along `X₁ ∩ X₂` is the restriction of that on
`E|_{X₁}`.

By Stacks 0BCD `E` is a finite locally free module of rank `< p` in degree `0` on an open
`U ⊇ X₁`; let `Z` be the reduced closed subscheme on `X ∖ U`, so that `Z ⊆ X₂` and `Z ∩ X₁ = ∅`.
By Stacks 0FB7 `c_p(X₂ ⟶ X, E)` is pushed forward from `c_p(Z ⟶ X, E)`, which kills the classes
from `X₁` by Stacks 0FB6; and it caps the classes from `X₂` as `c_p(E|_{X₂})` does by
Stacks 0FB4. Uniqueness in Stacks 0F9H concludes. -/
@[stacks 0FB8 "for c_p: c'_p(E₂) = c_p(X₂ → X, E) when E|_{X₁} is finite locally free of rank \
< p in degree 0"]
theorem closedCoverChernClass_eq_localizedChern
    (hrank : ∃ M : X₁.Modules, IsFiniteLocallyFreeOfRankLT M S.p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        i₁.toLRSHom.toShHom).obj (S.E : DerivedCategory S.X.Modules) ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    closedCoverChernClass S.base S.a i₁ S.i (S.i ≫ S.a) rfl
        (S.hasDefinedChernClasses_E.derivedPullback S.i) S.p hcover
        (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_pullbackSnd i₁ S.i hrank) =
      S.localizedChern
        (S.isFiniteLocallyFreeOfRankLTOnComplement_of_iso_singleFunctor i₁ hcover hrank) := by
  obtain ⟨U, hU₁, hU⟩ := exists_opens_iso_singleFunctor_of_iso_singleFunctor S.E S.perfect i₁
    hrank
  obtain ⟨j, hj, hjS⟩ := S.exists_isClosedImmersion_reducedComplementIdeal U
    (compl_subset_range_of_range_subset S i₁ hcover hU₁)
  let T := S.withReducedComplement U (Or.inr hU)
  have hT : T.IsFiniteLocallyFreeOfRankLTOnComplement :=
    exists_isFiniteLocallyFreeOfRankLT_derivedPullback_of_factors (i := Scheme.Opens.ι _)
      (k := Scheme.Opens.ι _)
      (S.X.homOfLE_ι (S.compl_range_reducedComplementIdeal_subschemeι U).le) hU
  have : @IsClosedImmersion X₁ T.X i₁ := ‹_›
  have : @IsClosedImmersion S.Z T.X S.i := S.isClosedImmersion
  have : @IsClosedImmersion T.Z S.Z j := hj
  have hdisj : Disjoint (Set.range i₁) (Set.range T.i) :=
    disjoint_range_reducedComplementIdeal_subschemeι S U i₁ hU₁
  exact closedCoverChernClass_eq_localizedChern_withLargerClosed (S := T) (i₂ := S.i)
    (hj := hjS) _ hcover hT hdisj _

end ClosedCover

end Stacks.Chow.LocalizedSituation

end
