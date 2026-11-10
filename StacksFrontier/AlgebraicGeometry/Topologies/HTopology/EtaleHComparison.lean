module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.FiniteFreeDominationAffine
public import StacksFrontier.AlgebraicGeometry.Topologies.H.BigSite

/-!
# Étale coverings are h coverings

An étale covering of a scheme is a family of étale morphisms whose images cover the target.
Étale morphisms are locally of finite presentation, so such a family is an h covering as soon
as it is a ph covering.  This file proves that it is a ph covering: over an affine open `U` of
the target the family is refined by a standard ph covering.

## Main results

* `AlgebraicGeometry.exists_standardPHCovering_hom_of_etale`: a finite, jointly surjective
  family of étale morphisms of affine schemes over an affine base is refined by a standard ph
  covering.
* `AlgebraicGeometry.isPHCovering_of_etale`: the étale case of Stacks 0DBT, an étale covering
  is a ph covering.
* `AlgebraicGeometry.isHCovering_of_etale` and
  `AlgebraicGeometry.isHCovering_of_presieve₀_mem_etalePrecoverage`: an étale covering is
  an h covering, the étale clause of Stacks 0ETV.
* `AlgebraicGeometry.isHCoveringInCutoff_of_isEtaleCovering`: the same statement for families
  in a size-bounded category of schemes.

## Implementation notes

Local finite presentation of an étale morphism is found by instance search, and
`AlgebraicGeometry.IsZariskiLocalAtSource` for `AlgebraicGeometry.Etale` is supplied
explicitly: the instance of `AlgebraicGeometry.HasRingHomProperty` for it leaves the ring
homomorphism property as a metavariable, so instance search does not find it.

## References

* [Stacks Project, Tag 02LH](https://stacks.math.columbia.edu/tag/02LH)
* [Stacks Project, Tag 0DBD](https://stacks.math.columbia.edu/tag/0DBD)
* [Stacks Project, Tag 0DBG](https://stacks.math.columbia.edu/tag/0DBG)
* [Stacks Project, Tag 0DBT](https://stacks.math.columbia.edu/tag/0DBT)
* [Stacks Project, Tag 0ETS](https://stacks.math.columbia.edu/tag/0ETS)
* [Stacks Project, Tag 0ETV](https://stacks.math.columbia.edu/tag/0ETV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- A finite family of étale morphisms from affine schemes to an affine scheme whose images
cover the target is refined by a standard ph covering. -/
public theorem exists_standardPHCovering_hom_of_etale {S : Scheme.{u}} [IsAffine S]
    {J : Type u} [Finite J] (Y : J → Scheme.{u}) [∀ a, IsAffine (Y a)] (q : ∀ a, Y a ⟶ S)
    [∀ a, Etale (q a)] (hsurj : (⋃ a, Set.range (q a).base) = Set.univ) :
    ∃ 𝒲 : PreZeroHypercover.{u} S, StandardPHCovering 𝒲.f ∧
      Nonempty (𝒲.Hom ⟨J, Y, q⟩) := by
  classical
  have _ : IsZariskiLocalAtSource @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  have _ : Etale (Sigma.desc q) := IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  have _ : Surjective (Sigma.desc q) := Surjective.sigmaDesc_of_union_range_eq_univ hsurj
  obtain ⟨V, p, hflf, hpsurj, 𝒯, -, g', hlift⟩ :=
    Stacks.Topologies.Etale.exists_isFiniteLocallyFree_surjective_finite_openCover_lift
      (U := ∐ Y) (S := S) (Sigma.desc q)
  rw [Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation] at hflf
  obtain ⟨hpfin, -, -⟩ := hflf
  have _ : IsFinite p := hpfin
  have _ : IsAffine V := isAffine_of_isAffineHom p
  have _ : Surjective p := hpsurj
  let 𝒱 : V.OpenCover := 𝒯.bind fun k ↦ (sigmaOpenCover Y).pullback₁ (g' k)
  let Arf := 𝒱.affineRefinement.openCover
  let W := Arf.finiteSubcover
  let toV : W ⟶ 𝒱 :=
    (⟨fun a ↦ Arf.idx a.val, fun _ ↦ 𝟙 _, fun _ ↦ rfl⟩ : W ⟶ Arf).comp 𝒱.fromAffineRefinement
  refine ⟨⟨W.I₀, W.X, fun a ↦ W.f a ≫ p⟩, ?_, ?_⟩
  · exact StandardPHCovering.of_presentation _
      (hX := fun a ↦ by
        change IsAffine (Spec (𝒱.affineRefinement.X (Arf.idx a.val)))
        infer_instance)
      p W.f inferInstance hpsurj (fun _ ↦ inferInstance) W.iUnion_range fun _ ↦ rfl
  · refine ⟨(⟨toV.s₀, toV.h₀, fun a ↦ ?_⟩ :
      (⟨W.I₀, W.X, fun a ↦ W.f a ≫ p⟩ : PreZeroHypercover.{u} S).Hom
        ⟨𝒱.I₀, 𝒱.X, fun kj ↦ 𝒱.f kj ≫ p⟩).comp
      (⟨fun kj ↦ kj.2, fun kj ↦ (sigmaOpenCover Y).pullbackHom (g' kj.1) kj.2, fun kj ↦ ?_⟩ :
        (⟨𝒱.I₀, 𝒱.X, fun kj ↦ 𝒱.f kj ≫ p⟩ : PreZeroHypercover.{u} S).Hom ⟨J, Y, q⟩)⟩
    · change toV.h₀ a ≫ 𝒱.f (toV.s₀ a) ≫ p = W.f a ≫ p
      rw [← Category.assoc, toV.w₀]
    · change (sigmaOpenCover Y).pullbackHom (g' kj.1) kj.2 ≫ q kj.2 =
        (((sigmaOpenCover Y).pullback₁ (g' kj.1)).f kj.2 ≫ 𝒯.f kj.1) ≫ p
      have hd : (sigmaOpenCover Y).f kj.2 ≫ Sigma.desc q = q kj.2 := Sigma.ι_comp_desc q kj.2
      rw [← hd, reassoc_of% Scheme.Cover.pullbackHom_map (sigmaOpenCover Y) (g' kj.1) kj.2, ← hlift,
        Category.assoc]

/-- A family of étale morphisms of schemes whose images cover the target is a ph covering. -/
@[stacks 0DBT "étale coverings"]
public theorem isPHCovering_of_etale {T : Scheme.{u}} {I : Type v} (X : I → Scheme.{u})
    (f : ∀ i, X i ⟶ T) (hsurj : ∀ x : T, ∃ i, x ∈ Set.range (f i).base)
    (hetale : ∀ i, Etale (f i)) :
    IsPHCovering X f := by
  classical
  rw [isPHCovering_iff]
  refine ⟨fun i ↦ have := hetale i; inferInstance, fun U hU ↦ ?_⟩
  have : IsAffine U.toScheme := hU
  have hEt : ∀ i, Etale (pullback.snd (f i) U.ι) := fun i ↦ have := hetale i; inferInstance
  have hsurjU : ∀ x : U.toScheme, ∃ i, x ∈ Set.range (pullback.snd (f i) U.ι).base := by
    intro x
    obtain ⟨i, y, hy⟩ := hsurj (U.ι x)
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := f i) (g := U.ι) y x hy
    exact ⟨i, z, hz⟩
  have hchoice : ∀ u : U.toScheme, ∃ (i : I) (A : (pullback (f i) U.ι).Opens),
      IsAffineOpen A ∧ u ∈ Set.range (A.ι ≫ pullback.snd (f i) U.ι).base := by
    intro u
    obtain ⟨i, x, hx⟩ := hsurjU u
    obtain ⟨A, hA, hxA, -⟩ := exists_isAffineOpen_mem_and_subset
      (X := pullback (f i) U.ι) (x := x) (U := ⊤) (Opens.mem_top x)
    exact ⟨i, A, hA, ⟨⟨x, hxA⟩, (Scheme.Hom.comp_apply _ _ _).trans hx⟩⟩
  choose idx A hA hcov using hchoice
  have hqEt : ∀ u : U.toScheme, Etale ((A u).ι ≫ pullback.snd (f (idx u)) U.ι) :=
    fun u ↦ have := hEt (idx u); inferInstance
  obtain ⟨s, hs⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set U.toScheme)).elim_finite_subcover
      (fun u ↦ Set.range ((A u).ι ≫ pullback.snd (f (idx u)) U.ι).base)
      (fun u ↦ have := hqEt u
        ((A u).ι ≫ pullback.snd (f (idx u)) U.ι).isOpenMap.isOpen_range)
      fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hcov x⟩
  have hunion : (⋃ a : {u : U.toScheme // u ∈ s},
      Set.range ((A a.1).ι ≫ pullback.snd (f (idx a.1)) U.ι).base) = Set.univ := by
    refine Set.eq_univ_of_univ_subset (hs.trans (le_of_eq ?_))
    exact (Set.iUnion_subtype (fun u : U.toScheme ↦ u ∈ s)
      fun a ↦ Set.range ((A a).ι ≫ pullback.snd (f (idx a)) U.ι).base).symm
  have _ : ∀ a : {u : U.toScheme // u ∈ s}, IsAffine (A a.1).toScheme := fun a ↦ hA a.1
  have _ : ∀ a : {u : U.toScheme // u ∈ s},
      Etale ((A a.1).ι ≫ pullback.snd (f (idx a.1)) U.ι) := fun a ↦ hqEt a.1
  obtain ⟨𝒲, hstd, ⟨ρ⟩⟩ := exists_standardPHCovering_hom_of_etale (S := U.toScheme)
    (fun a : {u : U.toScheme // u ∈ s} ↦ (A a.1).toScheme)
    (fun a ↦ (A a.1).ι ≫ pullback.snd (f (idx a.1)) U.ι) hunion
  exact ⟨𝒲, hstd, ⟨ρ.comp ⟨fun a ↦ idx a.1, fun a ↦ (A a.1).ι, fun _ ↦ rfl⟩⟩⟩

/-- A family of étale morphisms of schemes whose images cover the target is an h covering. -/
public theorem isHCovering_of_etale {T : Scheme.{u}} {I : Type v} (X : I → Scheme.{u})
    (f : ∀ i, X i ⟶ T) (hsurj : ∀ x : T, ∃ i, x ∈ Set.range (f i).base)
    (hetale : ∀ i, Etale (f i)) :
    IsHCovering X f :=
  ⟨fun i ↦ have := hetale i; inferInstance, isPHCovering_of_etale X f hsurj hetale⟩

/-- A family of morphisms of schemes whose presieve is an étale covering is an h covering. -/
public theorem isHCovering_of_presieve₀_mem_etalePrecoverage {T : Scheme.{u}}
    (E : PreZeroHypercover.{v} T) (hE : E.presieve₀ ∈ Scheme.etalePrecoverage T) :
    IsHCovering E.X E.f :=
  have h := (Scheme.presieve₀_mem_precoverage_iff (P := @Etale) E).mp hE
  isHCovering_of_etale E.X E.f h.1 h.2

/-- An étale covering family in a size-bounded category of schemes is an h covering family
there. -/
public theorem isHCoveringInCutoff_of_isEtaleCovering {κ : Cardinal.{u}}
    (𝒰 : Covering.{u + 1, u, u + 1} (SchemeBelow κ)) (h𝒰 : IsEtaleCovering 𝒰) :
    IsHCoveringInCutoff 𝒰 :=
  isHCovering_of_presieve₀_mem_etalePrecoverage (𝒰.2.map (schemeBelowInclusion κ)) h𝒰

end AlgebraicGeometry

end
