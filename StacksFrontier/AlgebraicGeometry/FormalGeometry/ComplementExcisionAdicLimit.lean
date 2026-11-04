module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementAdicQuotientLimit
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.ComplementExcision
public import StacksFrontier.RingTheory.LocalCohomology.MittagLefflerAdicQuotientShrink
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.RightDerivedCompIsoNatTrans

/-!
# The limit of the adic quotients may be taken on the punctured spectrum

Let `A` be a commutative ring, let `I`, `J`, `K` be ideals with `V(J) ∩ V(I) = V(K)`, let `M` be
an `A`-module and put `V = Spec A ∖ V(J)`, `W = Spec A ∖ V(K)`.  Each term of the tower
`n ↦ M/IⁿM` is `I`-power torsion, so by excision the restriction map

`H^p(W, (M/IⁿM)~) ⟶ H^p(V, (M/IⁿM)~)`

is an isomorphism in every degree.  Those isomorphisms are the components of a natural
transformation of functors of the module, so they assemble into an isomorphism of the two inverse
limits over the tower, and the canonical map of [Stacks, Tag 0DXQ] may be read with its target
taken on `W` instead of on `V`.

For a local ring `A` with `K = 𝔪` this turns the limit over `V` into the limit over the punctured
spectrum `U = Spec A ∖ {𝔪}`, which is the open the source takes the limit on.

## Main definitions

* `Stacks.Algebraization.complementCohomologyRestrict` — restriction of the cohomology on the
  complement of a smaller zero locus to that of a larger one, as a natural transformation of
  functors on sheaves of modules.
* `Stacks.Algebraization.complementCohomologyBaseRestrict` — the same, read over `A` as a natural
  transformation of functors of the `A`-module.
* `Stacks.Algebraization.adicQuotientComplementRestrictNatIso` — the restriction, whiskered with
  the adic quotient tower, as a **natural isomorphism**.
* `Stacks.Algebraization.adicQuotientComplementLimitIso` — hence an isomorphism of the two
  inverse limits.
* `Stacks.Algebraization.complementAdicQuotientToExcisedLimit` — the canonical map
  `H^p(V, M̃) ⟶ lim_n H^p(W, (M/IⁿM)~)`.

## Main results

* `Stacks.Algebraization.isIso_complementCohomologyBaseRestrict_app_of_isIPowerTorsion` — the
  restriction is invertible at an `I`-power-torsion module.
* `Stacks.Algebraization.isIso_complementAdicQuotientToExcisedLimit` — the canonical map into the
  limit taken on `W` is invertible exactly when the one into the limit taken on `V` is.

## Implementation notes

Two models of the cohomology of an open meet here.  The excision theorem
`Stacks.LocalCohomology.isIso_hrestrict_complementZeroLocus_of_isIPowerTorsion` is stated for the
`AddCommGrpCat`-valued cohomology `Hgroup` of [Stacks, Tag 01E3] and its restriction map
`HrestrictNT`, while the comparison of [Stacks, Tag 0DWR] and the limit comparison of
[Stacks, Tag 0DXQ] live in the `A`-module-valued model
`Stacks.LocalCohomologySequence.complementCohomologyBaseFunctor`.  The two are related by
`forget₂_rightDerived_sectionsOnComplement_restriction_eq_HrestrictNT`, which says that forgetting
the module structure takes the restriction of the derived module-valued sections to `HrestrictNT`;
since `forget₂ (ModuleCat R) AddCommGrpCat` reflects isomorphisms, invertibility transfers back.

Only the components of the restriction at the terms of the tower are invertible, not those at a
general module, so the natural isomorphism is formed after whiskering with the tower:
`CategoryTheory.NatIso.isIso_of_isIso_app` upgrades the whiskered transformation to an isomorphism
from the invertibility of its components, and `CategoryTheory.Limits.HasLimit.isoOfNatIso` turns
that into the isomorphism of limits.

## References

* [Stacks Project, Tag 0DXQ](https://stacks.math.columbia.edu/tag/0DXQ)
* [Stacks Project, Tag 0DWS](https://stacks.math.columbia.edu/tag/0DWS)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.ProEtale
open Stacks.Cohomology.SectionsWithSupport
open Stacks.Cohomology.ModuleComparison
open Stacks.LocalCohomologyTilde
open RingedSpaceModuleAdjunction

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology Stacks.LocalCohomologySequence

variable (A : Type u) [CommRing A]

/-! ### The restriction between two open complements, as a natural transformation -/

/-- **Restriction from the complement of a smaller zero locus to that of a larger one**, on the
cohomology of sheaves of modules on `Spec A` valued in modules over the global functions.  For
`V(K) ⊆ V(J)` the open `Spec A ∖ V(J)` is contained in `Spec A ∖ V(K)`, so restriction runs from
the cohomology of the latter to that of the former. -/
def complementCohomologyRestrict (K J : Ideal A)
    (hKJ : PrimeSpectrum.zeroLocus (K : Set A) ⊆ PrimeSpectrum.zeroLocus (J : Set A)) (p : ℕ) :
    complementCohomology (A := CommRingCat.of A) K p ⟶
      complementCohomology (A := CommRingCat.of A) J p :=
  NatTrans.rightDerived
    (sectionsOnComplementRestrict (Spec (CommRingCat.of A)).toRingedSpace
      (isClosed_zeroLocusSubset (A := CommRingCat.of A) K)
      (isClosed_zeroLocusSubset (A := CommRingCat.of A) J) hKJ) p

/-- **The restriction between two open complements, read over `A` as a natural transformation of
functors of the module.**  Its component at `N` is the restriction map
`H^p(Spec A ∖ V(K), Ñ) ⟶ H^p(Spec A ∖ V(J), Ñ)`. -/
def complementCohomologyBaseRestrict (K J : Ideal A)
    (hKJ : PrimeSpectrum.zeroLocus (K : Set A) ⊆ PrimeSpectrum.zeroLocus (J : Set A)) (p : ℕ) :
    complementCohomologyBaseFunctor (A := CommRingCat.of A) K p ⟶
      complementCohomologyBaseFunctor (A := CommRingCat.of A) J p :=
  Functor.whiskerRight
    (Functor.whiskerLeft (tildeSheafFunctor (CommRingCat.of A))
      (complementCohomologyRestrict A K J hKJ p))
    (globalToBase (CommRingCat.of A))

/-- The component of `complementCohomologyBaseRestrict` at `N` is the image under `globalToBase`
of the component of `complementCohomologyRestrict` at `Ñ`. -/
theorem complementCohomologyBaseRestrict_app (K J : Ideal A)
    (hKJ : PrimeSpectrum.zeroLocus (K : Set A) ⊆ PrimeSpectrum.zeroLocus (J : Set A)) (p : ℕ)
    (N : ModuleCat.{u} A) :
    (complementCohomologyBaseRestrict A K J hKJ p).app N =
      (globalToBase (CommRingCat.of A)).map
        ((complementCohomologyRestrict A K J hKJ p).app (tildeSheaf N)) :=
  rfl

/-! ### Invertibility at a torsion module -/

/-- A commuting square with three invertible sides has its fourth side invertible. -/
private theorem isIso_of_comp_eq {C : Type*} [Category* C] {W X Y Z : C}
    {f : W ⟶ X} {g : X ⟶ Z} {u : W ⟶ Y} {v : Y ⟶ Z}
    (hg : IsIso g) (hu : IsIso u) (hv : IsIso v) (h : f ≫ g = u ≫ v) : IsIso f := by
  have := hg
  have := hu
  have := hv
  have : IsIso (f ≫ g) := by rw [h]; infer_instance
  exact IsIso.of_isIso_comp_right f g

/-- **The restriction is invertible at an `I`-power-torsion module, in every degree**, provided
`V(J) ∩ V(I) = V(K)`.

This is excision for `I`-power-torsion modules, carried from the abelian-group-valued model of
cohomology to the module-valued one. -/
theorem isIso_complementCohomologyRestrict_app_of_isIPowerTorsion (I J K : Ideal A)
    (N : ModuleCat.{u} A) (hN : IsIPowerTorsion A N I)
    (hK : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)
      = PrimeSpectrum.zeroLocus (K : Set A))
    (hKJ : PrimeSpectrum.zeroLocus (K : Set A) ⊆ PrimeSpectrum.zeroLocus (J : Set A)) (p : ℕ) :
    IsIso ((complementCohomologyRestrict A K J hKJ p).app (tildeSheaf N)) := by
  set X := (Spec (CommRingCat.of A)).toRingedSpace with hX
  have hle : complementZeroLocus A J ≤ complementZeroLocus A K :=
    Set.compl_subset_compl.2 hKJ
  have hexc : IsIso ((HrestrictNT (structureSheafRing X)
      (openComplement_le_openComplement X
        (isClosed_zeroLocusSubset (A := CommRingCat.of A) K)
        (isClosed_zeroLocusSubset (A := CommRingCat.of A) J) hKJ) p).app (tildeSheaf N)) :=
    isIso_hrestrict_complementZeroLocus_of_isIPowerTorsion I J K N hN hK hle p
  have hforget : ∀ L : Ideal A, IsIso ((sectionsOnOpenForgetIso X
      (openComplement (zeroLocusSubset (A := CommRingCat.of A) L)
        (isClosed_zeroLocusSubset (A := CommRingCat.of A) L)) p).hom.app (tildeSheaf N)) :=
    fun L => ((sectionsOnOpenForgetIso X
      (openComplement (zeroLocusSubset (A := CommRingCat.of A) L)
        (isClosed_zeroLocusSubset (A := CommRingCat.of A) L)) p).app (tildeSheaf N)).isIso_hom
  have hbridge := congrArg (fun α => NatTrans.app α (tildeSheaf N))
    (forget₂_rightDerived_sectionsOnComplement_restriction_eq_HrestrictNT X
      (isClosed_zeroLocusSubset (A := CommRingCat.of A) K)
      (isClosed_zeroLocusSubset (A := CommRingCat.of A) J) hKJ p)
  have : IsIso ((forget₂ (GlobalModules X) AddCommGrpCat.{u}).map
      ((complementCohomologyRestrict A K J hKJ p).app (tildeSheaf N))) :=
    isIso_of_comp_eq (hforget J) (hforget K) hexc hbridge
  exact isIso_of_reflects_iso _ (forget₂ (GlobalModules X) AddCommGrpCat.{u})

/-- **The restriction, read over `A`, is invertible at an `I`-power-torsion module.** -/
theorem isIso_complementCohomologyBaseRestrict_app_of_isIPowerTorsion (I J K : Ideal A)
    (N : ModuleCat.{u} A) (hN : IsIPowerTorsion A N I)
    (hK : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)
      = PrimeSpectrum.zeroLocus (K : Set A))
    (hKJ : PrimeSpectrum.zeroLocus (K : Set A) ⊆ PrimeSpectrum.zeroLocus (J : Set A)) (p : ℕ) :
    IsIso ((complementCohomologyBaseRestrict A K J hKJ p).app N) := by
  have := isIso_complementCohomologyRestrict_app_of_isIPowerTorsion A I J K N hN hK hKJ p
  rw [complementCohomologyBaseRestrict_app]
  exact Functor.map_isIso (globalToBase (CommRingCat.of A)) _

/-! ### The isomorphism of the two limits -/

/-- **The restriction, whiskered with the adic quotient tower, is a natural isomorphism.**  Each
term `M/IⁿM` of the tower is `I`-power torsion, so each component is invertible. -/
def adicQuotientComplementRestrictNatIso (I J K : Ideal A) (M : ModuleCat.{u} A)
    (hK : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)
      = PrimeSpectrum.zeroLocus (K : Set A))
    (hKJ : PrimeSpectrum.zeroLocus (K : Set A) ⊆ PrimeSpectrum.zeroLocus (J : Set A)) (p : ℕ) :
    adicQuotientModuleSystem A I M ⋙
        complementCohomologyBaseFunctor (A := CommRingCat.of A) K p ≅
      adicQuotientModuleSystem A I M ⋙
        complementCohomologyBaseFunctor (A := CommRingCat.of A) J p :=
  haveI hcomp : ∀ n : ℕᵒᵖ, IsIso ((Functor.whiskerLeft (adicQuotientModuleSystem A I M)
      (complementCohomologyBaseRestrict A K J hKJ p)).app n) := by
    intro n
    obtain ⟨n⟩ := n
    exact isIso_complementCohomologyBaseRestrict_app_of_isIPowerTorsion A I J K
      ((adicQuotientModuleSystem A I M).obj (op n))
      (isIPowerTorsion_adicQuotientModuleSystem_obj A I M n) hK hKJ p
  haveI : IsIso (Functor.whiskerLeft (adicQuotientModuleSystem A I M)
      (complementCohomologyBaseRestrict A K J hKJ p)) := NatIso.isIso_of_isIso_app _
  asIso (Functor.whiskerLeft (adicQuotientModuleSystem A I M)
    (complementCohomologyBaseRestrict A K J hKJ p))

/-- **The inverse limit of the cohomology of the adic quotients does not change when the open is
enlarged from `Spec A ∖ V(J)` to `Spec A ∖ V(K)`**, provided `V(J) ∩ V(I) = V(K)`. -/
def adicQuotientComplementLimitIso (I J K : Ideal A) (M : ModuleCat.{u} A)
    (hK : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)
      = PrimeSpectrum.zeroLocus (K : Set A))
    (hKJ : PrimeSpectrum.zeroLocus (K : Set A) ⊆ PrimeSpectrum.zeroLocus (J : Set A)) (p : ℕ) :
    limit (adicQuotientModuleSystem A I M ⋙
        complementCohomologyBaseFunctor (A := CommRingCat.of A) K p) ≅
      limit (adicQuotientModuleSystem A I M ⋙
        complementCohomologyBaseFunctor (A := CommRingCat.of A) J p) :=
  HasLimit.isoOfNatIso (adicQuotientComplementRestrictNatIso A I J K M hK hKJ p)

/-! ### The canonical map with the limit taken on the larger open -/

/-- **The canonical map `H^p(Spec A ∖ V(J), M̃) ⟶ lim_n H^p(Spec A ∖ V(K), (M/IⁿM)~)`** of
[Stacks, Tag 0DXQ], with the limit on the right taken on the larger open `Spec A ∖ V(K)`.  It is
the canonical map into the limit taken on `Spec A ∖ V(J)`, followed by the inverse of the
excision isomorphism of the two limits. -/
def complementAdicQuotientToExcisedLimit (I J K : Ideal A) (M : ModuleCat.{u} A)
    (hK : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)
      = PrimeSpectrum.zeroLocus (K : Set A))
    (hKJ : PrimeSpectrum.zeroLocus (K : Set A) ⊆ PrimeSpectrum.zeroLocus (J : Set A)) (p : ℕ) :
    (complementCohomologyBaseFunctor (A := CommRingCat.of A) J p).obj M ⟶
      limit (adicQuotientModuleSystem A I M ⋙
        complementCohomologyBaseFunctor (A := CommRingCat.of A) K p) :=
  complementAdicQuotientToLimit A I J M p ≫
    (adicQuotientComplementLimitIso A I J K M hK hKJ p).inv

/-- **The canonical map into the limit taken on the larger open is invertible exactly when the
one into the limit taken on `Spec A ∖ V(J)` is.** -/
theorem isIso_complementAdicQuotientToExcisedLimit (I J K : Ideal A) (M : ModuleCat.{u} A)
    (hK : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)
      = PrimeSpectrum.zeroLocus (K : Set A))
    (hKJ : PrimeSpectrum.zeroLocus (K : Set A) ⊆ PrimeSpectrum.zeroLocus (J : Set A)) (p : ℕ)
    (h : IsIso (complementAdicQuotientToLimit A I J M p)) :
    IsIso (complementAdicQuotientToExcisedLimit A I J K M hK hKJ p) := by
  have := h
  exact IsIso.comp_isIso

end Stacks.Algebraization

end
