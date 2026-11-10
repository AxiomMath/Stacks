module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.GenericTrivialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.OpenRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibleHomology

/-!
# A finite family of constructible sheaves is locally constant on a common nonempty open

Let `X` be a nonempty reduced scheme of a big étale site and `Gᵢ`, `i ∈ s` with `s` finite,
constructible sheaves of `Λ`-modules on its small étale site, `Λ` a Noetherian ring in any
universe. Then there is a nonempty open subscheme of `X` over which every `Gᵢ` is locally
constant of finite type. This is the choice of a good open in the reduction of the Weil II weight
bound to curves ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), applied to the finitely
many nonzero `Rˢ g_! F'₀`.

The one-sheaf statement near a generic point is
`exists_isOpenImmersion_isFiniteTypeLocallyConstant_of_isConstructibleModuleSheaf`, stated for a
coefficient ring in `Type (u + 1)`. Its proof uses nothing about that universe, and it is repeated
here for a ring in any universe `r`, with sheaves valued in `ModuleCat.{max (u + 1) r} Λ`. The
ℓ-adic coefficient rings `ℤ_ℓ` and `ℤ/ℓⁿ` live in `Type`. The finite family is then handled by
shrinking the open once for each sheaf: an open of a reduced scheme is reduced, a nonempty one has
a generic point, and local constancy of finite type and constructibility both restrict to opens.

## Main results

* `exists_isOpenImmersion_isFiniteTypeLocallyConstant_of_isConstructibleModuleSheaf'`:
  the statement near a generic point, for a ring in any universe.
* `exists_isOpenImmersion_forall_isFiniteTypeLocallyConstant`: the common nonempty open of a
  finite family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u r

namespace AlgebraicGeometry

attribute [local instance] SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ]

/-- **A constructible sheaf is locally constant of finite type on an open neighbourhood of each
generic point**, for a coefficient ring in any universe. Let `X` be a reduced scheme of a big
étale site, `G` a constructible sheaf of `Λ`-modules on its small étale site and `η` a generic
point of an irreducible component of `X`. Then there is an open immersion `o : O ⟶ X` whose image
contains `η` and along which the inverse image of `G` is locally constant of finite type. -/
public theorem exists_isOpenImmersion_isFiniteTypeLocallyConstant_of_isConstructibleModuleSheaf'
    (X : B.Scheme) [IsReduced X.obj]
    (G : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ))
    (hG : IsConstructibleModuleSheaf B X Λ G) {η : X.obj} (hη : η ∈ genericPoints X.obj) :
    ∃ (O : B.Scheme) (o : O ⟶ X), IsOpenImmersion (B.inclusion.map o) ∧
      η ∈ Set.range (B.inclusion.map o).base ∧
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B O.obj O.property)
        (((smallEtaleBaseChange B o).sheafPullback (ModuleCat.{max (u + 1) r} Λ)
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B O.obj O.property)).obj G) := by
  obtain ⟨U, hU, hηU⟩ : ∃ U : X.obj.Opens, IsAffineOpen U ∧ η ∈ U := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
      X.obj.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η) isOpen_univ
    exact ⟨U, hU, hηU⟩
  obtain ⟨s, hs⟩ := hG ⟨U, hU⟩
  have hηcov : η ∈ ⋃ i, Set.range (B.inclusion.map (s.inclusion i)).base := s.covers ▸ hηU
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hηcov
  set f := B.inclusion.map (s.inclusion i)
  have : IsImmersion f := s.isImmersion i
  have : IsAffine U.toScheme := hU
  have : SpectralSpace U.toScheme :=
    Scheme.spectralSpace_of_compactSpace_quasiSeparatedSpace U.toScheme
  let ηU : U.toScheme := ⟨η, hηU⟩
  have hηU' : ηU ∈ genericPoints U.toScheme :=
    TopologicalSpace.mem_genericPoints_of_forall_specializes_eq fun y hy =>
      U.ι.isOpenEmbedding.injective
        (TopologicalSpace.forall_specializes_eq_of_mem_genericPoints hη _
          (hy.map U.ι.base.hom.continuous))
  set T := U.ι.base ⁻¹' Set.range f.base
  have hηT : ηU ∈ T := hi
  have hnot : ηU ∉ closure Tᶜ :=
    Topology.notMem_closure_of_mem_genericPoints_of_isConstructible hηU'
      (s.constructible i).compl fun h => h hηT
  let OU : U.toScheme.Opens := ⟨(closure Tᶜ)ᶜ, isClosed_closure.isOpen_compl⟩
  let O : X.obj.Opens := U.ι ''ᵁ OU
  have hO : (O : Set X.obj) ⊆ Set.range f.base := by
    rintro x ⟨y, hy, rfl⟩
    by_contra hyT
    exact hy (subset_closure hyT)
  have hηO : η ∈ O := ⟨ηU, hnot, rfl⟩
  have hc : B.Contains (f ⁻¹ᵁ O).toScheme :=
    Scheme.size_lt_of_isOpenImmersion (f ⁻¹ᵁ O).ι (s.piece i).property
  let ι' : B.obj (f ⁻¹ᵁ O).toScheme hc ⟶ s.piece i := ObjectProperty.homMk (f ⁻¹ᵁ O).ι
  have hmap : B.inclusion.map (ι' ≫ s.inclusion i) = (f ⁻¹ᵁ O).ι ≫ f := rfl
  refine ⟨B.obj (f ⁻¹ᵁ O).toScheme hc, ι' ≫ s.inclusion i, ?_, ?_, ?_⟩
  · rw [hmap]
    have : IsReduced (B.inclusion.obj X) := ‹IsReduced X.obj›
    exact isOpenImmersion_comp_of_isImmersion_of_subset_range f O hO
  · obtain ⟨p, hp⟩ := hO hηO
    refine ⟨⟨p, show f.base p ∈ O from hp ▸ hηO⟩, ?_⟩
    rw [hmap]
    exact hp
  · exact Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ _
      ((smallEtaleSheafPullbackCompIso B _ _ X ι' (s.inclusion i)
        (ModuleCat.{max (u + 1) r} Λ)).app G)
      (isFiniteTypeLocallyConstant_smallEtaleSheafPullback B Λ ι' _ (hs i))

/-- **A finite family of constructible sheaves is locally constant of finite type on a common
nonempty open.** Let `X` be a nonempty reduced scheme of a big étale site and `Gᵢ`, `i ∈ s`,
finitely many constructible sheaves of `Λ`-modules on its small étale site. Then there is an open
immersion `o : V ⟶ X` with `V` nonempty along which the inverse image of every `Gᵢ` is locally
constant of finite type. -/
public theorem exists_isOpenImmersion_forall_isFiniteTypeLocallyConstant {ι : Type*}
    (s : Finset ι) (X : B.Scheme) [IsReduced X.obj] [Nonempty X.obj]
    (G : ι → Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ))
    (hG : ∀ i ∈ s, IsConstructibleModuleSheaf B X Λ (G i)) :
    ∃ (V : B.Scheme) (o : V ⟶ X), IsOpenImmersion (B.inclusion.map o) ∧ Nonempty V.obj ∧
      ∀ i ∈ s, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
        (SmallEtale.topology B V.obj V.property)
        (((smallEtaleBaseChange B o).sheafPullback (ModuleCat.{max (u + 1) r} Λ)
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B V.obj V.property)).obj (G i)) := by
  classical
  induction s using Finset.induction_on generalizing X with
  | empty =>
    exact ⟨X, 𝟙 X, by
      show IsOpenImmersion (B.inclusion.map (𝟙 X))
      rw [CategoryTheory.Functor.map_id]
      infer_instance, inferInstance, by simp⟩
  | insert a s ha ih =>
    obtain ⟨V, o, ho, hV, hlc⟩ := ih X G (fun i hi => hG i (Finset.mem_insert_of_mem hi))
    have : IsOpenImmersion (B.inclusion.map o) := ho
    have : IsReduced (B.inclusion.obj X) := ‹IsReduced X.obj›
    have : IsReduced V.obj := isReduced_of_isOpenImmersion (B.inclusion.map o)
    obtain ⟨η, hη⟩ : (genericPoints V.obj).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have hc := genericPoints.closure (α := V.obj)
      rw [h, closure_empty] at hc
      obtain ⟨x⟩ := hV
      exact (Set.mem_empty_iff_false x).1 (hc ▸ Set.mem_univ x)
    obtain ⟨O, o', ho', hηO, hlc'⟩ :=
      exists_isOpenImmersion_isFiniteTypeLocallyConstant_of_isConstructibleModuleSheaf' B Λ V _
        (isConstructibleModuleSheaf_pullback_of_isOpenImmersion B Λ o ho (G a)
          (hG a (Finset.mem_insert_self a s))) hη
    have : IsOpenImmersion (B.inclusion.map o') := ho'
    refine ⟨O, o' ≫ o, ?_, ⟨hηO.choose⟩, fun i hi => ?_⟩
    · rw [Functor.map_comp]
      infer_instance
    · refine Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ _
        ((smallEtaleSheafPullbackCompIso B _ _ X o' o
          (ModuleCat.{max (u + 1) r} Λ)).app (G i)) ?_
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hlc'
      · exact isFiniteTypeLocallyConstant_smallEtaleSheafPullback B Λ o' _ (hlc i hi)

end AlgebraicGeometry
