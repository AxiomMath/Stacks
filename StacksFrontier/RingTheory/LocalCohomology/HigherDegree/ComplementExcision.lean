module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.PuncturedComplement
public import StacksFrontier.AlgebraicGeometry.MayerVietorisHgroup.Excision
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.ComplementSheafCohomology
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Excision in all degrees for a torsion module on the complement of a zero locus

Let `A` be a commutative ring, `X = Spec A`, let `I`, `J`, `K` be ideals of `A` with

`V(J) ∩ V(I) = V(K)`

and let `N` be an `I`-power-torsion `A`-module.  Then the restriction map

`H^p(X ∖ V(K), Ñ) ⟶ H^p(X ∖ V(J), Ñ)`

is an isomorphism for **every** `p`.  For a local ring `A` with maximal ideal `𝔪` and
`V(J) ∩ V(I) = {𝔪}` this is excision between the punctured spectrum and `X ∖ V(J)`.

The cohomology is the `AddCommGrpCat`-valued cohomology `Hgroup` of Stacks 01E3 over an open of
`X`, and the restriction map is `HrestrictNT`.

## Main results

* `Stacks.LocalCohomology.subsingleton_localizedModule_of_isIPowerTorsion` — an
  `I`-power-torsion module localizes to zero at every prime outside `V(I)`.
* `Stacks.LocalCohomology.isZero_restrict_tilde_of_le_complementZeroLocus` — `Ñ` restricts to the
  zero sheaf of modules on every open contained in `X ∖ V(I)`.
* `Stacks.LocalCohomology.isZero_hgroup_tilde_of_le_complementZeroLocus` — the cohomology of `Ñ`
  over such an open vanishes in every degree.
* `Stacks.LocalCohomology.isIso_hrestrict_complementZeroLocus_of_isIPowerTorsion` —
  **excision in all degrees**, for ideals `I`, `J`, `K` with `V(J) ∩ V(I) = V(K)`.
* `Stacks.LocalCohomology.isIso_hrestrict_maximalIdeal_of_isIPowerTorsion` — the same with
  `K = 𝔪` the maximal ideal of a local ring, the hypothesis read as `V(J) ∩ V(I) = {𝔪}`.
* `Stacks.LocalCohomology.isIso_hrestrict_puncturedSpectrum_of_isIPowerTorsion` — the same
  written with the punctured spectrum `Spec A ∖ {𝔪}` as the source open.

## References

* [Stacks Project, Tag 0DXQ](https://stacks.math.columbia.edu/tag/0DXQ)
* [Stacks Project, Tag 0DWS](https://stacks.math.columbia.edu/tag/0DWS)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-! ### A torsion module localizes to zero off its support -/

/-- **An `I`-power-torsion module localizes to zero at every prime not containing `I`.** -/
public theorem subsingleton_localizedModule_of_isIPowerTorsion (I : Ideal A)
    (N : ModuleCat.{u} A) (hN : IsIPowerTorsion A N I) (p : PrimeSpectrum A)
    (hp : p ∉ PrimeSpectrum.zeroLocus (I : Set A)) :
    Subsingleton (LocalizedModule p.asIdeal.primeCompl N) := by
  obtain ⟨f, hfI, hfp⟩ := Set.not_subset.mp ((PrimeSpectrum.mem_zeroLocus _ _).not.mp hp)
  rw [LocalizedModule.subsingleton_iff]
  intro m
  obtain ⟨k, -, hkill⟩ := hN m
  exact ⟨f ^ k, p.asIdeal.primeCompl.pow_mem hfp k, hkill _ (Ideal.pow_mem_pow hfI k)⟩

/-- The stalk of `M̃` at a prime where `M` localizes to zero is trivial. -/
private theorem subsingleton_tilde_stalk {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (x : PrimeSpectrum.Top R) (h : Subsingleton (LocalizedModule x.asIdeal.primeCompl M)) :
    Subsingleton ((tilde M).presheaf.stalk x) := by
  have _ := h
  exact (IsLocalizedModule.iso x.asIdeal.primeCompl (tilde.toStalk M x).hom).symm.injective
    |>.subsingleton

/-! ### The sheaf and its cohomology vanish on the complement of the zero locus -/

/-- **`Ñ` restricts to the zero sheaf on every open inside `X ∖ V(I)`, for `N` an
`I`-power-torsion module.** -/
public theorem isZero_restrict_tilde_of_le_complementZeroLocus (I : Ideal A)
    (N : ModuleCat.{u} A) (hN : IsIPowerTorsion A N I)
    (W : (Spec (CommRingCat.of A)).Opens) (hW : W ≤ complementZeroLocus A I) :
    IsZero ((Scheme.Modules.restrictFunctor W.ι).obj (tilde (R := CommRingCat.of A) N)) := by
  set G := (Scheme.Modules.restrictFunctor W.ι).obj (tilde (R := CommRingCat.of A) N)
  have hstalk (x : W) : IsZero (G.presheaf.stalk x) :=
    IsZero.of_iso
      (AddCommGrpCat.isZero_iff_subsingleton.mpr
        (subsingleton_tilde_stalk (R := CommRingCat.of A) N x.1
          (subsingleton_localizedModule_of_isIPowerTorsion I N hN x.1 (hW x.2))))
      (Scheme.Modules.restrictStalkNatIso W.ι x |>.app (tilde (R := CommRingCat.of A) N))
  let Gsheaf : TopCat.Sheaf Ab (TopCat.of W) := ⟨G.presheaf, G.isSheaf⟩
  have hGsheaf : IsZero Gsheaf := by
    rw [TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero]
    exact hstalk
  have hGpresheaf : IsZero G.presheaf :=
    Functor.map_isZero (TopCat.Sheaf.forget Ab (TopCat.of W)) hGsheaf
  refine (IsZero.iff_id_eq_zero G).mpr (Functor.map_injective (Scheme.Modules.toPresheaf W) ?_)
  rw [Functor.map_zero]
  exact (IsZero.iff_id_eq_zero G.presheaf).mp hGpresheaf

/-- **The cohomology of `Ñ` over an open inside `X ∖ V(I)` vanishes in every degree**, for `N` an
`I`-power-torsion module. -/
public theorem isZero_hgroup_tilde_of_le_complementZeroLocus (I : Ideal A)
    (N : ModuleCat.{u} A) (hN : IsIPowerTorsion A N I)
    (W : (Spec (CommRingCat.of A)).Opens) (hW : W ≤ complementZeroLocus A I) (n : ℕ) :
    IsZero (Hgroup (Spec (CommRingCat.of A)).ringCatSheaf W n
      (tilde (R := CommRingCat.of A) N)) := by
  exact IsZero.of_iso (Functor.isZero_rightDerived_obj (secF (W : Scheme).ringCatSheaf ⊤) n
      (isZero_restrict_tilde_of_le_complementZeroLocus I N hN W hW))
    (hgroupRestrictIso (Spec (CommRingCat.of A)) W n (tilde (R := CommRingCat.of A) N))

/-! ### The two opens of the cover -/

/-- **`V(J) ∩ V(I) = V(K)` says exactly that `X ∖ V(J)` and `X ∖ V(I)` cover `X ∖ V(K)`.** -/
public theorem complementZeroLocus_sup_eq_of_zeroLocus_inter (I J K : Ideal A)
    (hK : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)
      = PrimeSpectrum.zeroLocus (K : Set A)) :
    complementZeroLocus A J ⊔ complementZeroLocus A I = complementZeroLocus A K := by
  refine TopologicalSpace.Opens.ext ?_
  change (PrimeSpectrum.zeroLocus (J : Set A))ᶜ ∪ (PrimeSpectrum.zeroLocus (I : Set A))ᶜ
      = (PrimeSpectrum.zeroLocus (K : Set A))ᶜ
  rw [← Set.compl_inter, hK]

/-- A smaller zero locus has a larger open complement. -/
public theorem complementZeroLocus_le_of_zeroLocus_subset (I K : Ideal A)
    (h : PrimeSpectrum.zeroLocus (K : Set A) ⊆ PrimeSpectrum.zeroLocus (I : Set A)) :
    complementZeroLocus A I ≤ complementZeroLocus A K :=
  Set.compl_subset_compl.2 h

/-! ### Excision in all degrees -/

/-- **Excision in all degrees.**  Let `I`, `J`, `K` be ideals of a commutative ring `A` with
`V(J) ∩ V(I) = V(K)`, and let `N` be an `I`-power-torsion `A`-module.  Then the restriction map

`H^p(Spec A ∖ V(K), Ñ) ⟶ H^p(Spec A ∖ V(J), Ñ)`

is an isomorphism for every `p`. -/
public theorem isIso_hrestrict_complementZeroLocus_of_isIPowerTorsion
    (I J K : Ideal A) (N : ModuleCat.{u} A) (hN : IsIPowerTorsion A N I)
    (hK : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)
      = PrimeSpectrum.zeroLocus (K : Set A))
    (hJK : complementZeroLocus A J ≤ complementZeroLocus A K) (p : ℕ) :
    IsIso (Hrestrict (Spec (CommRingCat.of A)).ringCatSheaf hJK p
      (tilde (R := CommRingCat.of A) N)) := by
  have hIK : complementZeroLocus A I ≤ complementZeroLocus A K :=
    complementZeroLocus_le_of_zeroLocus_subset I K (hK ▸ Set.inter_subset_right)
  exact Stacks.Cohomology.AmbientMayerVietoris.isIso_Hrestrict_of_isZero
    (Spec (CommRingCat.of A)).ringCatSheaf _ _ _ hJK hIK
    (complementZeroLocus_sup_eq_of_zeroLocus_inter I J K hK) _
    (fun n ↦ isZero_hgroup_tilde_of_le_complementZeroLocus I N hN _ le_rfl n)
    (fun n ↦ isZero_hgroup_tilde_of_le_complementZeroLocus I N hN _ inf_le_right n) p

/-- **Excision in all degrees, with `Ñ` spelled as the universe-independent associated sheaf
`Stacks.LocalCohomology.associatedSheaf`.**  For ideals `I`, `J`, `K` of `A` with
`V(J) ∩ V(I) = V(K)` and `N` an `I`-power-torsion `A`-module, the restriction map
`H^p(Spec A ∖ V(K), Ñ) ⟶ H^p(Spec A ∖ V(J), Ñ)` is an isomorphism for every `p`. -/
public theorem isIso_hrestrict_complementZeroLocus_associatedSheaf_of_isIPowerTorsion
    (I J K : Ideal A) (N : ModuleCat.{u} A) (hN : IsIPowerTorsion A N I)
    (hK : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)
      = PrimeSpectrum.zeroLocus (K : Set A))
    (hJK : complementZeroLocus A J ≤ complementZeroLocus A K) (p : ℕ) :
    IsIso (Hrestrict (Spec (CommRingCat.of A)).ringCatSheaf hJK p (associatedSheaf A N)) := by
  rw [associatedSheaf_eq_tilde]
  exact isIso_hrestrict_complementZeroLocus_of_isIPowerTorsion I J K N hN hK hJK p

/-- **Excision in all degrees at the closed point of a local ring.**  For `A` local with maximal
ideal `𝔪`, ideals `I`, `J` with `V(J) ∩ V(I) = {𝔪}`, and `N` an `I`-power-torsion `A`-module, the
restriction map

`H^p(Spec A ∖ V(𝔪), Ñ) ⟶ H^p(Spec A ∖ V(J), Ñ)`

is an isomorphism for every `p`. -/
public theorem isIso_hrestrict_maximalIdeal_of_isIPowerTorsion [IsLocalRing A]
    (I J : Ideal A) (N : ModuleCat.{u} A) (hN : IsIPowerTorsion A N I)
    (hK : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)
      = {closedPoint A})
    (hJK : complementZeroLocus A J ≤ complementZeroLocus A (maximalIdeal A)) (p : ℕ) :
    IsIso (Hrestrict (Spec (CommRingCat.of A)).ringCatSheaf hJK p
      (tilde (R := CommRingCat.of A) N)) :=
  isIso_hrestrict_complementZeroLocus_of_isIPowerTorsion I J (maximalIdeal A) N hN
    (hK.trans (zeroLocus_maximalIdeal_eq_singleton A).symm) hJK p

/-- **Excision in all degrees between the punctured spectrum and `X ∖ V(J)`.**  For `A` local,
ideals `I`, `J` with `V(J) ∩ V(I) = {𝔪}`, and `N` an `I`-power-torsion `A`-module, the restriction
map from the cohomology of `Ñ` over the punctured spectrum to its cohomology over `Spec A ∖ V(J)`
is an isomorphism in every degree. -/
public theorem isIso_hrestrict_puncturedSpectrum_of_isIPowerTorsion [IsLocalRing A]
    (I J : Ideal A) (N : ModuleCat.{u} A) (hN : IsIPowerTorsion A N I)
    (hK : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)
      = {closedPoint A})
    (hJK : complementZeroLocus A J ≤ Stacks.puncturedSpectrum A) (p : ℕ) :
    IsIso (Hrestrict (Spec (CommRingCat.of A)).ringCatSheaf hJK p
      (tilde (R := CommRingCat.of A) N)) := by
  revert hJK
  rw [puncturedSpectrum_eq_complementZeroLocus A]
  exact fun hJK ↦ isIso_hrestrict_maximalIdeal_of_isIPowerTorsion I J N hN hK hJK p

end Stacks.LocalCohomology

end
