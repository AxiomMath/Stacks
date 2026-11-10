module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.KrullDimension.Module
public import StacksFrontier.RingTheory.LocalCohomology.DimensionVanishing
public import StacksFrontier.RingTheory.LocalCohomology.LongExactSequence.AllModules
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimensionBounds
public import StacksFrontier.RingTheory.LocalCohomology.RestrictScalars
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.Localization

/-!
# Bounding the cohomological dimension by the dimension of the support

Stacks 0DXC has two assertions: the local cohomology of a finite module vanishes above the
dimension of its support, and the cohomological dimension of a finitely generated ideal is
bounded by the Krull dimension of the ring. This file carries out every step of the source's
proof whose ingredients are available in this library, so that both assertions are reduced to
the *local* case of the second one — the single statement

`A local, I finitely generated, dim A ≤ d ⟹ cd(A, I) ≤ d`,

which the source proves from the vanishing of sheaf cohomology above the dimension of a
spectral space (Stacks 0A3G) together with the implication (3) ⇒ (1) of Stacks 0DX7, neither of
which is available here.

Two reductions are performed. Globalization is Stacks 0DXB: the cohomological dimension is the
supremum of the cohomological dimensions of the localizations, and a localization of `A` at a
prime is local of dimension at most `dim A`. Passage from the regular module to an arbitrary
finite module is the source's last paragraph: if `𝔞` annihilates `M` and `B = A/𝔞`, then
`Spec B = Supp M`, local cohomology over `A` of a `B`-module agrees with local cohomology over
`B` (Stacks 0BJB), and a vanishing bound for `B` is a vanishing bound for every `B`-module by
the implication (1) ⇒ (2) of Stacks 0DX7, which *is* available here.

## Main definitions

* `Stacks.LocalCohomology.homologyMapDerivedIso` — an exact functor commutes with the cohomology
  of an object of the unbounded derived category.

## Main results

* `Stacks.LocalCohomology.localCohomologyModule_restrictScalars_iso` — the degree-`i` local
  cohomology over `A` of a `B`-module is the degree-`i` local cohomology over `B`, restricted to
  `A`; this is Stacks 0BJB read on cohomology modules.
* `Stacks.LocalCohomology.cohomologicalDimension_le_of_forall_localization_le` — a bound holding
  at every localization holds globally. This is a corollary of Stacks 0DXB and depends on
  nothing unproved.
* `Stacks.LocalCohomology.ringKrullDim_localizationAtPrime_le` — a localization at a prime has
  Krull dimension at most that of the ring.
* `Stacks.LocalCohomology.cohomologicalDimension_le_ringKrullDim_of_isLocalRing` — the second
  assertion of Stacks 0DXC, reduced to its own local case.
* `Stacks.LocalCohomology.cohomologicalDimension_le_ringKrullDim_of_exists_zeroLocus_generators` —
  the same assertion reduced instead to the local form of Kronecker's bound on arithmetic rank.
* `Stacks.LocalCohomology.localCohomologyModule_isZero_of_supportDim_lt_of_quotient_bound` — the
  first assertion of Stacks 0DXC, reduced to a bound on the cohomological dimension of
  `A / ann(M)`.

## Implementation notes

The reductions take the missing input as an explicit hypothesis rather than as an axiom. For the
first assertion that hypothesis is a single inequality about the one ring `A / ann(M)`, so it is
visibly satisfiable. For the second it is a statement about all local rings, and
`cohomologicalDimension_le_of_exists_zeroLocus_generators_card_le` discharges its body in every
case where the zero locus is cut out by at most `e` elements — in particular for `I = ⊥` and
`e = 0` — so that shape is attainable too. No `@[stacks 0DXC]` attribute is placed here: these
are reductions, and the tag itself is
`StacksFrontier/RingTheory/LocalCohomology/CohomologicalDimension/KrullDimension.lean`.

## References

* [Stacks Project, Tag 0DXC](https://stacks.math.columbia.edu/tag/0DXC)
* [Stacks Project, Tag 0DXB](https://stacks.math.columbia.edu/tag/0DXB)
* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7)
* [Stacks Project, Tag 0BJB](https://stacks.math.columbia.edu/tag/0BJB)
-/

@[expose] public noncomputable section

universe v u

namespace Stacks.LocalCohomology

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

/-- An additive functor preserving finite limits and finite colimits commutes with the
cohomology of an object of the unbounded derived category. -/
noncomputable def homologyMapDerivedIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (K : DerivedCategory C) (i : ℤ) :
    (DerivedCategory.homologyFunctor D i).obj (F.mapDerivedCategory.obj K) ≅
      F.obj ((DerivedCategory.homologyFunctor C i).obj K) := by
  let P := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  exact (DerivedCategory.homologyFunctor D i).mapIso
      (F.mapDerivedCategory.mapIso e.symm ≪≫ F.mapDerivedCategoryFactors.app P) ≪≫
    (DerivedCategory.homologyFunctorFactors D i).app _ ≪≫
    (ShortComplex.mapHomologyIso (P.sc i) F) ≪≫
    F.mapIso ((DerivedCategory.homologyFunctorFactors C i).app P).symm ≪≫
    F.mapIso ((DerivedCategory.homologyFunctor C i).mapIso e)

/-- **Stacks Project, Tag 0BJB on cohomology modules.** For a ring map `f : A →+* B` and a
finitely generated ideal `I ⊆ A`, the degree-`i` local cohomology over `A` with support in
`V(I)` of a `B`-module restricted to `A` is the degree-`i` local cohomology over `B` with
support in `V(IB)`, restricted to `A`. -/
noncomputable def localCohomologyModule_restrictScalars_iso
    {A : Type u} {B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{max u v} B) (i : ℤ) :
    localCohomologyModule A I hI ((ModuleCat.restrictScalars f).obj M) i ≅
      (ModuleCat.restrictScalars f).obj
        (localCohomologyModule B (I.map f) (hI.map f) M i) := by
  let PA := Dualizing.derivedPowerTorsionProperty A I hI
  let PB := Dualizing.derivedPowerTorsionProperty B (I.map f) (hI.map f)
  let LC_A := Dualizing.localCohomologyFunctor A I hI
  let LC_B := Dualizing.localCohomologyFunctor B (I.map f) (hI.map f)
  let K := (DerivedCategory.singleFunctor (ModuleCat.{max u v} B) 0).obj M
  let F := ModuleCat.restrictScalars.{max u v} f
  let e₀ : F.mapDerivedCategory.obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj (F.obj M) :=
    (F.mapDerivedCategorySingleFunctor 0).app M
  let e₁ : LC_A.obj (F.mapDerivedCategory.obj K) ≅
      (powerTorsionRestrictScalars.{u, u, v} f I hI).obj (LC_B.obj K) :=
    (localCohomologyRestrictScalarsIso.{u, u, v} f I hI).app K
  let e₂ := (powerTorsionRestrictScalarsCompInclusionIso.{u, u, v} f I hI).app (LC_B.obj K)
  let e := PA.ι.mapIso (LC_A.mapIso e₀.symm) ≪≫ PA.ι.mapIso e₁ ≪≫ e₂
  let h := (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso e
  let h' := h ≪≫ homologyMapDerivedIso F (PB.ι.obj (LC_B.obj K)) i
  simpa [PA, PB, LC_A, LC_B, K, F, localCohomologyModule] using h'

/-- **A corollary of Stacks Project, Tag 0DXB.** A bound on the cohomological dimension that
holds after localizing at every prime ideal holds for the ring itself. -/
theorem cohomologicalDimension_le_of_forall_localization_le
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (d : ℤ) (hd : (-1 : ℤ) ≤ d)
    (h : ∀ p : PrimeSpectrum A,
      cohomologicalDimension (Localization.AtPrime p.asIdeal)
        (I.map (algebraMap A (Localization.AtPrime p.asIdeal)))
        (hI.map (algebraMap A (Localization.AtPrime p.asIdeal))) ≤ d) :
    cohomologicalDimension A I hI ≤ d := by
  rw [cohomologicalDimension_eq_sSup_localizations A I hI]
  refine csSup_le ⟨-1, Set.mem_insert _ _⟩ ?_
  rintro x (rfl | ⟨p, rfl⟩)
  exacts [hd, h p]

/-- The Krull dimension of a localization at a prime ideal is at most the Krull dimension of the
ring: it is the height of that prime. -/
theorem ringKrullDim_localizationAtPrime_le (A : Type u) [CommRing A] (p : PrimeSpectrum A) :
    ringKrullDim (Localization.AtPrime p.asIdeal) ≤ ringKrullDim A := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (Localization.AtPrime p.asIdeal)]
  exact Ideal.height_le_ringKrullDim_of_isPrime

/-- **The second assertion of Stacks Project, Tag 0DXC, reduced to its local case.** Granting
the bound `cd(B, J) ≤ dim B` for every *local* ring `B`, the cohomological dimension of a
finitely generated ideal of any ring is bounded by the Krull dimension of that ring.

This is the globalization step of the source's proof: by Tag 0DXB the cohomological dimension is
the supremum of the cohomological dimensions of the localizations `A_𝔭`, each of which is local
of dimension `ht 𝔭 ≤ dim A`. -/
theorem cohomologicalDimension_le_ringKrullDim_of_isLocalRing
    (hlocal : ∀ (B : Type u) [CommRing B] [IsLocalRing B] (J : Ideal B) (hJ : J.FG) (e : ℕ),
      ringKrullDim B ≤ (e : WithBot ℕ∞) → cohomologicalDimension B J hJ ≤ (e : ℤ))
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (d : ℕ)
    (hd : ringKrullDim A ≤ (d : WithBot ℕ∞)) :
    cohomologicalDimension A I hI ≤ (d : ℤ) := by
  refine cohomologicalDimension_le_of_forall_localization_le A I hI (d : ℤ) (by omega) fun p => ?_
  let B := Localization.AtPrime p.asIdeal
  let _ : IsLocalRing B := IsLocalization.AtPrime.isLocalRing B p.asIdeal
  exact hlocal B (I.map (algebraMap A B)) (hI.map (algebraMap A B)) d
    ((ringKrullDim_localizationAtPrime_le A p).trans hd)

/-- The bound of `cohomologicalDimension_le_ringKrullDim_of_isLocalRing`'s hypothesis holds
whenever the zero locus of `I` is cut out by at most `e` elements. This is the generator bound of
Stacks 0DX9 (2) restated in the shape that hypothesis asks for; in particular it shows that
shape is attainable, since for `I = ⊥` and `e = 0` the empty family qualifies. -/
theorem cohomologicalDimension_le_of_exists_zeroLocus_generators_card_le
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (e : ℕ)
    (h : ∃ (n : ℕ) (f : Fin n → A), n ≤ e ∧
      PrimeSpectrum.zeroLocus ((Ideal.span (Set.range f) : Ideal A) : Set A) =
        PrimeSpectrum.zeroLocus (I : Set A)) :
    cohomologicalDimension A I hI ≤ (e : ℤ) := by
  obtain ⟨n, f, hn, hf⟩ := h
  exact (cohomologicalDimension_le_card_zeroLocus_generators A I hI f hf).trans
    (by exact_mod_cast hn)

/-- **The second assertion of Stacks Project, Tag 0DXC, reduced to a bound on arithmetic rank.**
Granting that in every local ring `B` of Krull dimension at most `e` the zero locus of every
finitely generated ideal is cut out by at most `e` elements, the cohomological dimension of a
finitely generated ideal of any ring is bounded by the Krull dimension of that ring.

This is the second of the two routes to the local case. The hypothesis is the local form of
Kronecker's bound on the arithmetic rank of an ideal, which is a statement of commutative algebra
with no sheaf cohomology in it, and which is absent from both Mathlib and this library. Note that
it is *strictly stronger* than Kronecker's theorem as usually stated: that gives `dim B + 1`
elements, which through `cohomologicalDimension_le_card_zeroLocus_generators` would bound the
cohomological dimension by `dim B + 1` and not by `dim B`. -/
theorem cohomologicalDimension_le_ringKrullDim_of_exists_zeroLocus_generators
    (hara : ∀ (B : Type u) [CommRing B] [IsLocalRing B] (J : Ideal B), J.FG → ∀ e : ℕ,
      ringKrullDim B ≤ (e : WithBot ℕ∞) → ∃ (n : ℕ) (g : Fin n → B), n ≤ e ∧
        PrimeSpectrum.zeroLocus ((Ideal.span (Set.range g) : Ideal B) : Set B) =
          PrimeSpectrum.zeroLocus (J : Set B))
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (d : ℕ)
    (hd : ringKrullDim A ≤ (d : WithBot ℕ∞)) :
    cohomologicalDimension A I hI ≤ (d : ℤ) :=
  cohomologicalDimension_le_ringKrullDim_of_isLocalRing
    (fun B _ _ J hJ e he =>
      cohomologicalDimension_le_of_exists_zeroLocus_generators_card_le B J hJ e
        (hara B J hJ e he))
    A I hI d hd

/-- **The first assertion of Stacks Project, Tag 0DXC, reduced to a bound on `A / ann(M)`.** Let
`M` be a finite `A`-module whose support has dimension strictly below `i`. If the cohomological
dimension of `I (A/ann M)` is at most `i - 1`, then `H^i_{V(I)}(M) = 0`.

This is the last paragraph of the source's proof. Put `𝔞 = ann(M)` and `B = A/𝔞`, so that
`Spec B = Supp M` and `dim B = dim Supp M < i`. The module `M` is a `B`-module, local cohomology
over `A` of a `B`-module agrees with local cohomology over `B` (Tag 0BJB, in the form
`localCohomologyModule_restrictScalars_iso`), and the hypothesis makes `i - 1` a vanishing bound
for `B` itself, hence for *every* `B`-module by the implication (1) ⇒ (2) of Tag 0DX7. The
degenerate case of a subsingleton module is separate, because the dimension of an empty support
is `⊥`. -/
theorem localCohomologyModule_isZero_of_supportDim_lt_of_quotient_bound
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{max u v} A) [Module.Finite A M] (i : ℤ)
    (hi : Module.supportDim A M < (i.toNat : WithBot ℕ∞))
    (hbound : cohomologicalDimension (A ⧸ Module.annihilator A M)
        (I.map (Ideal.Quotient.mk (Module.annihilator A M)))
        (hI.map (Ideal.Quotient.mk (Module.annihilator A M))) ≤ (i.toNat : ℤ) - 1) :
    IsZero (localCohomologyModule A I hI M i) := by
  by_cases hzero : Subsingleton M
  · exact isZero_homology_localCohomology_of_subsingleton.{u, v} A I hI M i
  have hi0 : 0 < i := by
    by_contra hi0
    refine hzero ((Module.supportDim_eq_bot_iff_subsingleton A M).mp ?_)
    apply (WithBot.lt_zero_iff_eq_bot _).mp
    simpa [Int.toNat_of_nonpos (by omega : i ≤ 0)] using hi
  let J := Module.annihilator A M
  let B := A ⧸ J
  let f : A →+* B := Ideal.Quotient.mk J
  have hTor := Module.isTorsionBySet_annihilator A M
  let _ : Module B M := hTor.module
  let _ : IsScalarTower A B M := hTor.isScalarTower
  let MB : ModuleCat.{max u v} B := ModuleCat.of B M
  have hMB := isZero_homology_localCohomology_of_isZero_homology_self.{v, u}
    (I.map f) (hI.map f) ((i.toNat : ℤ) - 1)
    (fun j hj => (isLocalCohomologyBound_cohomologicalDimension B (I.map f) (hI.map f)).2 j
      (hbound.trans_lt hj)) MB i (by omega)
  have hRestr : IsZero ((ModuleCat.restrictScalars f).obj
      (localCohomologyModule B (I.map f) (hI.map f) MB i)) := by
    rw [ModuleCat.isZero_iff_subsingleton] at hMB ⊢; assumption
  let eLin : ((ModuleCat.restrictScalars f).obj MB) ≃ₗ[A] M :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun a m => hTor.mk_smul a m }
  let eM : (ModuleCat.restrictScalars f).obj MB ≅ ModuleCat.of A M :=
    { hom := ModuleCat.ofHom eLin.toLinearMap
      inv := ModuleCat.ofHom eLin.symm.toLinearMap
      hom_inv_id := by ext m; rfl
      inv_hom_id := by ext m; rfl }
  exact (hRestr.of_iso (localCohomologyModule_restrictScalars_iso.{v} f I hI MB i)).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso
      ((Dualizing.derivedPowerTorsionProperty A I hI).ι.mapIso
        ((Dualizing.localCohomologyFunctor A I hI).mapIso
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).mapIso eM))))

end Stacks.LocalCohomology

end
