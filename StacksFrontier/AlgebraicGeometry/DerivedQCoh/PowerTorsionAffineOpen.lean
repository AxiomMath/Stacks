module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.PowerTorsionQcqs
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Comparison
public import StacksFrontier.AlgebraicGeometry.Perfect.RestrictionOfPerfectObjects
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineDerivedPresentation
public import StacksFrontier.AlgebraicGeometry.Smooth.TildeTransport
public import StacksFrontier.Homology.Perfect.ModelIndependence
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms out of a perfect object into an object supported on `V(f)` are `f`-power torsion

Let `X` be a quasi-compact quasi-separated scheme, let `f ∈ Γ(X, 𝒪_X)` and let `E`, `E'` be
objects of `D_QCoh(𝒪_X)` with `E` perfect and `E'` cohomologically supported on the zero locus
`T = V(f)`. Then every morphism `α : E ⟶ E'` is annihilated by a power of `f`. This file proves the
affine case on an affine scheme and on an affine open, and deduces the statement on `X`.

## Main results

* `Stacks.DerivedQCoh.homPowerTorsion_of_isAffine`: the statement on an affine scheme.
* `Stacks.DerivedQCoh.homPowerTorsionOn_of_isAffineOpen`: the statement on an affine open of an
  arbitrary scheme.
* `Stacks.DerivedQCoh.exists_pow_smul_eq_zero_of_isPerfect_of_cohomologySupportedOn`: the
  statement on a quasi-compact quasi-separated scheme.
* `Stacks.DerivedQCoh.cohomologySupportedOn_derivedRestrict_of_notMem`: restriction along an
  arbitrary open immersion of schemes pulls a cohomological support back.
* `Stacks.DerivedQCoh.isPerfect_derivedRestrict_opens_of_model`: restriction to an open subscheme
  preserves perfectness, at an arbitrary chosen derived category.

## Implementation notes

The affine case is transported from `Spec R` along `AlgebraicGeometry.Scheme.isoSpec` of an
affine scheme `W`, so that the ring of scalars is `Γ(W, ⊤)` and no
`AlgebraicGeometry.Scheme.Opens.topIso` appears.

The two spellings `X.Modules` and `SheafOfModules` of the category of `𝒪_X`-modules are
definitionally equal, but instance search does not cross them. The perfectness statements are
written at `IsPerfect.{u, u, u + 1}` with every universe explicit: otherwise the hom universe of
the derived category is left a metavariable and elaboration runs out of heartbeats. For the same
reason shifts are written `(shiftFunctor (DerivedCategory Y.Modules) n).obj K` rather than `K⟦n⟧`.

The `CommRing` instance on `GlobalSectionRing` is scoped: without `open scoped IsMulCommutative`
the statements below elaborate with `sorryAx` inside them rather than failing.

## References

* [Stacks Project, Lemma 36.13.9 (Tag 08EJ)](https://stacks.math.columbia.edu/tag/08EJ)
* [Stacks Project, Lemma 36.3.5 (Tag 06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Lemma 20.46.14 (Tag 09UA)](https://stacks.math.columbia.edu/tag/09UA)
* [Stacks Project, Section 36.6 (Tag 08DA)](https://stacks.math.columbia.edu/tag/08DA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.SiteModules
open Stacks.ExtensionByZero
open Stacks.Duality.OpenImmersion (derivedRestrict)
open scoped IsMulCommutative

universe u

namespace Stacks.DerivedQCoh

open Stacks.Koszul.PowerLift

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] preservesFiniteLimits_restrictFunctor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-! ### Instances the statements below depend on -/

section Instances

example (X : Scheme.{u}) : CommRing ↥(GlobalSectionRing X.ringCatSheaf) := inferInstance

example (X : Scheme.{u}) : Linear ↥(GlobalSectionRing X.ringCatSheaf) X.Modules := inferInstance

example (X : Scheme.{u}) :
    Linear ↥(GlobalSectionRing X.ringCatSheaf) (DerivedCategory X.Modules) := inferInstance

end Instances

/-! ### Restriction and the cohomological support, at a general open immersion -/

/-- If every cohomology sheaf of `E` has vanishing stalks outside `T`, then every cohomology
sheaf of the restriction of `E` along `g` has vanishing stalks outside any set `S` whose
complement `g` maps into the complement of `T`. -/
public theorem cohomologySupportedOn_derivedRestrict_of_notMem {A B : Scheme.{u}} (g : A ⟶ B)
    [IsOpenImmersion g] (T : Set B) (S : Set A) (hS : ∀ x : A, x ∉ S → g.base x ∉ T)
    (E : DerivedCategory B.Modules)
    (hE : AlgebraicGeometry.CohomologySupportedOn B.ringCatSheaf T E) :
    AlgebraicGeometry.CohomologySupportedOn A.ringCatSheaf S ((derivedRestrict g).obj E) :=
  fun n x hx ↦ (hE n (g.base x) (hS x hx)).of_iso <|
    ((Scheme.Modules.toPresheaf A ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
      (((Scheme.Modules.restrictFunctor g).mapDerivedCategoryHomologyIso n).app E)) ≪≫
    (Scheme.Modules.restrictStalkNatIso g x).app
      ((DerivedCategory.homologyFunctor B.Modules n).obj E)

/-- A point outside the zero locus of the pullback of a section lies over a point outside the
zero locus of the section. -/
public theorem notMem_zeroLocus_of_notMem_zeroLocus_appTop {A B : Scheme.{u}} (g : A ⟶ B)
    (f : Γ(B, ⊤)) (x : A) (hx : x ∉ A.zeroLocus {g.appTop f}) : g.base x ∉ B.zeroLocus {f} := by
  rw [Scheme.zeroLocus_singleton, Set.mem_compl_iff, not_not] at hx ⊢
  exact (Scheme.preimage_basicOpen_top g f).ge hx

/-- The zero locus of the global section of `𝒪_{Spec R}` named by `g ∈ R` is the zero locus of
`g` in the prime spectrum. -/
public theorem zeroLocus_singleton_ΓSpecIso_inv {R : CommRingCat.{u}} (g : R) :
    (Spec R).zeroLocus {(Scheme.ΓSpecIso R).inv g} = PrimeSpectrum.zeroLocus {g} := by
  rw [Scheme.zeroLocus_singleton, basicOpen_eq_of_affine]
  exact (congrArg compl (PrimeSpectrum.basicOpen_eq_zeroLocus_compl g)).trans (compl_compl _)

/-! ### Perfectness, in the `X.Modules` spelling -/

/-- A shift of a perfect object is perfect, in the `X.Modules` spelling. -/
public theorem isPerfect_shift_modules {Y : Scheme.{u}} (K : DerivedCategory Y.Modules) (n : ℤ)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := Y.toRingedSpace) K) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := Y.toRingedSpace)
      ((shiftFunctor (DerivedCategory Y.Modules) n).obj K) :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift.{u, u + 1} hK n

/-- Restriction along an isomorphism of schemes preserves perfectness, in the `X.Modules`
spelling. -/
public theorem isPerfect_derivedRestrict_of_isIso {A B : Scheme.{u}} (g : A ⟶ B) [IsIso g]
    (K : DerivedCategory B.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := B.toRingedSpace) K) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := A.toRingedSpace)
      ((derivedRestrict g).obj K) :=
  Scheme.Modules.isPerfect_restrictFunctor_mapDerivedCategory_of_isIso.{u} g K hK

/-- Restriction to an open subscheme preserves perfectness, in the `X.Modules` spelling. -/
public theorem isPerfect_derivedRestrict_opens {X : Scheme.{u}} (V : X.Opens)
    (K : DerivedCategory X.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) K) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1}
      (X := V.toScheme.toRingedSpace) ((derivedRestrict V.ι).obj K) :=
  Scheme.Modules.isPerfect_restrictFunctor_mapDerivedCategory.{u} X V K hK

/-! ### The tag on an affine scheme -/

/-- Let `W` be an affine scheme, let
`f ∈ Γ(W, 𝒪_W)` and let `E`, `F` be objects of `D(𝒪_W)` with `E` perfect, the cohomology of `F`
quasi-coherent and `F` cohomologically supported on the zero locus of `f`. Then every morphism
`E⟦n⟧ ⟶ F` is annihilated by a power of `f`. -/
public theorem homPowerTorsion_of_isAffine {W : Scheme.{u}} [IsAffine W] (f : Γ(W, ⊤))
    (E F : DerivedCategory W.Modules)
    (hFqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor W.Modules i).obj F).IsQuasicoherent)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) E)
    (hF : AlgebraicGeometry.CohomologySupportedOn W.ringCatSheaf (W.zeroLocus {f}) F)
    (n : ℤ) :
    HomPowerTorsion (globalScalar W.ringCatSheaf f) (E⟦n⟧) F := by
  refine homPowerTorsion_of_derivedRestrict W.isoSpec f E F n ?_
  have hEs := isPerfect_shift_modules ((derivedRestrict W.isoSpec.inv).obj E) n
    (isPerfect_derivedRestrict_of_isIso W.isoSpec.inv E hE)
  have hFs : AlgebraicGeometry.CohomologySupportedOn (Spec Γ(W, ⊤)).ringCatSheaf
      (PrimeSpectrum.zeroLocus {f}) ((derivedRestrict W.isoSpec.inv).obj F) :=
    cohomologySupportedOn_derivedRestrict_of_notMem W.isoSpec.inv (W.zeroLocus {f})
      (PrimeSpectrum.zeroLocus {f})
      (fun x hx hmem => hx (by rwa [← W.isoSpec_inv_preimage_zeroLocus ({f} : Set Γ(W, ⊤))]))
      F hF
  rw [show globalScalar (Spec Γ(W, ⊤)).ringCatSheaf (W.isoSpec.inv.appTop f) =
      globalScalar (Spec Γ(W, ⊤)).ringCatSheaf ((Scheme.ΓSpecIso Γ(W, ⊤)).inv f) from
    congrArg (fun φ : Γ(W, ⊤) ⟶ Γ(Spec Γ(W, ⊤), ⊤) =>
      globalScalar (Spec Γ(W, ⊤)).ringCatSheaf (φ f)) (_root_.Stacks.Modules.isoSpec_inv_appTop)]
  intro α
  exact Stacks.AffineTilde.exists_pow_smul_eq_zero_of_isPerfect_of_cohomologySupportedOn f
    (fun i =>
      AlgebraicGeometry.PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ _ hEs i)
    (fun i => AlgebraicGeometry.isQuasicoherent_homology_restrictFunctor_mapDerivedCategory
      W.isoSpec.inv hFqc i)
    hEs hFs α

/-! ### The affine open case, and the tag on a quasi-compact quasi-separated scheme -/

/-- On an affine open `V` of a scheme `X`, every morphism from each shift of `E|_V` into `F|_V` is
annihilated by a power of `f|_V`. -/
public theorem homPowerTorsionOn_of_isAffineOpen {X : Scheme.{u}} (f : Γ(X, ⊤))
    (E F : DerivedCategory X.Modules)
    (hFqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj F).IsQuasicoherent)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (hF : AlgebraicGeometry.CohomologySupportedOn X.ringCatSheaf (X.zeroLocus {f}) F)
    (V : X.Opens) (hV : IsAffineOpen V) : HomPowerTorsionOn f E F V := by
  have : IsAffine V.toScheme := hV
  intro n
  exact homPowerTorsion_of_isAffine (V.ι.appTop f) ((derivedRestrict V.ι).obj E)
    ((derivedRestrict V.ι).obj F)
    (fun i => AlgebraicGeometry.isQuasicoherent_homology_restrictFunctor_mapDerivedCategory
      V.ι hFqc i)
    (isPerfect_derivedRestrict_opens V E hE)
    (cohomologySupportedOn_derivedRestrict_of_notMem V.ι (X.zeroLocus {f})
      (V.toScheme.zeroLocus {V.ι.appTop f})
      (notMem_zeroLocus_of_notMem_zeroLocus_appTop V.ι f) F hF) n

/-- On a quasi-compact quasi-separated scheme, every morphism from each shift of `E` into `F` is
annihilated by a power of `f`. -/
public theorem homPowerTorsion_of_compactSpace {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (f : Γ(X, ⊤))
    (E F : DerivedCategory X.Modules)
    (hFqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj F).IsQuasicoherent)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (hF : AlgebraicGeometry.CohomologySupportedOn X.ringCatSheaf (X.zeroLocus {f}) F)
    (n : ℤ) : HomPowerTorsion (globalScalar X.ringCatSheaf f) (E⟦n⟧) F :=
  homPowerTorsion_of_compact_of_affine f E F
    (fun V hV => homPowerTorsionOn_of_isAffineOpen f E F hFqc hE hF V hV) n

/-- Let `X` be a quasi-compact quasi-separated scheme and let
`f ∈ Γ(X, 𝒪_X)`. Let `E` and `E'` be objects of `D_QCoh(𝒪_X)` with `E` perfect and `E'`
cohomologically supported on `T = V(f)`. Then for every `α : E ⟶ E'` there is an `n ≥ 0` with
`f ^ n · α = 0`. -/
@[stacks 08EJ "on a quasi-compact quasi-separated scheme, the statement in full"]
public theorem exists_pow_smul_eq_zero_of_isPerfect_of_cohomologySupportedOn {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (f : Γ(X, ⊤))
    (E F : DerivedCategory X.Modules)
    (hFqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj F).IsQuasicoherent)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (hF : AlgebraicGeometry.CohomologySupportedOn X.ringCatSheaf (X.zeroLocus {f}) F)
    (α : E ⟶ F) :
    ∃ n : ℕ, globalScalar X.ringCatSheaf f ^ n • α = 0 :=
  HomPowerTorsion.of_iso ((shiftFunctorZero (DerivedCategory X.Modules) ℤ).app E)
    (homPowerTorsion_of_compactSpace f E F hFqc hE hF 0) α

/-! ### Non-vacuity

The statement at `X = Spec ℤ`, with the nonzero scalar named by `2 ∈ ℤ`, `E` the derived
sheafification of the Koszul complex on `(2)` and `F` that of `ℤ/2` in degree zero. -/

section Witness

private abbrev ringZZ : CommRingCat.{0} := CommRingCat.of ℤ

private abbrev specZZ : Scheme.{0} := Spec ringZZ

/-- The global section of `𝒪_{Spec ℤ}` named by `2 ∈ ℤ`. -/
private abbrev sectionTwo : Γ(specZZ, ⊤) := (Scheme.ΓSpecIso ringZZ).inv (2 : ℤ)

example (α : (tilde.functor ringZZ).mapDerivedCategory.obj StacksDraft.Perfect.koszulTwo ⟶
      (tilde.functor ringZZ).mapDerivedCategory.obj StacksDraft.Perfect.zmodTwoSingle) :
    ∃ k : ℕ, globalScalar specZZ.ringCatSheaf sectionTwo ^ k • α = 0 :=
  exists_pow_smul_eq_zero_of_isPerfect_of_cohomologySupportedOn sectionTwo _ _
    (fun i => AlgebraicGeometry.isQuasicoherent_homology_mapDerivedCategory_obj _ _ i)
    ((isPerfect_tilde_iff _).2 (StacksDraft.Perfect.isPerfect_extend_koszul _))
    (by
      rw [zeroLocus_singleton_ΓSpecIso_inv]
      exact Stacks.AffineTilde.cohomologySupportedOn_mapDerivedCategory_tilde _ _
        StacksDraft.Perfect.support_homology_subset_zeroLocus_zmodTwoSingle)
    α

/-- The scalar of the witness is not the zero section. -/
example : sectionTwo ≠ 0 := fun h => by
  have h2 : (2 : ℤ) = 0 := by
    have := congrArg (Scheme.ΓSpecIso ringZZ).hom h
    rwa [← CommRingCat.comp_apply, (Scheme.ΓSpecIso ringZZ).inv_hom_id, CommRingCat.id_apply,
      map_zero] at this
  exact two_ne_zero h2

/-- The zero locus of `2` is not the whole of `Spec ℤ`. -/
example : PrimeSpectrum.zeroLocus {(2 : ℤ)} ≠ (Set.univ : Set (PrimeSpectrum ringZZ)) := by
  intro h
  have hp : (Ideal.span {(3 : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by norm_num)).2 (Int.prime_iff_natAbs_prime.mpr (by norm_num))
  have hmem : (⟨Ideal.span {(3 : ℤ)}, hp⟩ : PrimeSpectrum ringZZ) ∈
      PrimeSpectrum.zeroLocus {(2 : ℤ)} := h ▸ Set.mem_univ _
  rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe,
    Ideal.mem_span_singleton] at hmem
  norm_num at hmem

end Witness

/-- The class of the restriction of a complex representing a perfect object is perfect, at the
standard model. -/
private theorem isPerfect_q_restrictComplex {X : Scheme.{u}} (V : X.Opens)
    (E : CochainComplex X.Modules ℤ)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X.toRingedSpace)
      (DerivedCategory.Q.obj E)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1}
      (X := V.toScheme.toRingedSpace) (DerivedCategory.Q.obj
        (((Scheme.Modules.restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)) :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
    ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategoryFactors.app E)
    (isPerfect_derivedRestrict_opens V (DerivedCategory.Q.obj E) hE)

end Stacks.DerivedQCoh

/-! ### Perfectness of restrictions at an arbitrary chosen derived category -/

namespace Stacks.DerivedQCoh

universe w

/-- Restriction to an open subscheme preserves perfectness, for arbitrary chosen derived
categories of `X` and of `V`. -/
@[sga "6 I 4.18" "special case"]
public theorem isPerfect_derivedRestrict_opens_of_model {X : Scheme.{u}} (V : X.Opens)
    [hX : HasDerivedCategory.{w} X.Modules] [hV : HasDerivedCategory.{w} V.toScheme.Modules]
    (K : DerivedCategory X.Modules)
    (hK : @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace hX K) :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect V.toScheme.toRingedSpace hV
      ((derivedRestrict V.ι).obj K) := by
  obtain ⟨E, ⟨eE⟩⟩ : ∃ E : CochainComplex X.Modules ℤ,
      Nonempty ((@DerivedCategory.Q X.Modules _ _ hX).obj E ≅ K) :=
    ⟨DerivedCategory.Q.objPreimage K, ⟨DerivedCategory.Q.objObjPreimageIso K⟩⟩
  have eR : (@DerivedCategory.Q V.toScheme.Modules _ _ hV).obj
        (((Scheme.Modules.restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj E) ≅
      (derivedRestrict V.ι).obj K :=
    ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategoryFactors.app E).symm ≪≫
      (derivedRestrict V.ι).mapIso eE
  exact (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_of_model _ hV (Iso.refl _) eR).1
    (isPerfect_q_restrictComplex V E
      ((Stacks.Cohomology.PerfectComplexes.isPerfect_iff_of_model hX _ eE (Iso.refl _)).1 hK))

end Stacks.DerivedQCoh

end
