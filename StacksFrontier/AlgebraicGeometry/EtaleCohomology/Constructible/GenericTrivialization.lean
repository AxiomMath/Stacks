module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ZeroStalkAtGenericPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.SmallEtaleStability
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.IrreducibleOpenSubobject
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.Sheaves

/-!
# A constructible sheaf is locally constant near a generic point

Let `X` be a reduced locally Noetherian scheme of a big étale site and `G` a constructible sheaf of
`Λ`-modules on its small étale site. Around every generic point `η` of an irreducible component of
`X` there is an open subscheme of `X` on which `G` is locally constant of finite type, and so `G`
becomes constant, with finitely generated value, on affine schemes étale over that open which
cover it.

This is the step of the dévissage of Stacks 03SC from a constructible sheaf to a sheaf which is
finite locally constant on a dense open.

The argument: pick an affine open `U ∋ η` and a constructible stratification of `U` on which `G` is
locally constant; the stratum through `η` has constructible image `T` in the spectral space `U`,
and since `η` is a generic point the closure of `U \ T` misses it (Stacks 005K,
`Topology.notMem_closure_of_mem_genericPoints_of_isConstructible`), so `T` contains an open
neighbourhood `O` of `η`. Over `O` the stratum is a surjective immersion, hence a surjective closed
immersion, hence an isomorphism because `X` is reduced; so the inclusion of `O` factors through the
stratum by an open immersion, and inverse image preserves local constancy of finite type.

## Main results

* `isOpenImmersion_comp_of_isImmersion_of_subset_range`: an immersion into a reduced scheme
  restricts to an open immersion over any open contained in its image.
* `exists_isOpenImmersion_isFiniteTypeLocallyConstant_of_isConstructibleModuleSheaf`: the open
  neighbourhood of `η` on which `G` is locally constant of finite type.
* `exists_etale_affine_constant_of_isFiniteTypeLocallyConstant`: a sheaf locally constant of finite
  type is constant with finitely generated value on affine schemes étale over the base, one through
  every point.

## References

* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 005K](https://stacks.math.columbia.edu/tag/005K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **An immersion into a reduced scheme is an open immersion over an open inside its image.** For
`f : P ⟶ X` an immersion, `X` reduced and `O` an open of `X` contained in the image of `f`, the
composite `f⁻¹ O ⟶ P ⟶ X` is an open immersion: over `O` the morphism `f` is a surjective
immersion, hence a surjective closed immersion, hence an isomorphism. -/
public theorem isOpenImmersion_comp_of_isImmersion_of_subset_range {P X : Scheme.{u}}
    (f : P ⟶ X) [IsImmersion f] [IsReduced X] (O : X.Opens)
    (hO : (O : Set X) ⊆ Set.range f.base) :
    IsOpenImmersion ((f ⁻¹ᵁ O).ι ≫ f) := by
  have hsurj : Surjective (f ∣_ O) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨p, hp⟩ := hO y.2
    refine ⟨⟨p, show f.base p ∈ O from hp ▸ y.2⟩, ?_⟩
    apply O.ι.isOpenEmbedding.injective
    show (f ∣_ O ≫ O.ι).base _ = O.ι.base y
    rw [morphismRestrict_ι]
    exact hp
  have : IsClosedImmersion (f ∣_ O) :=
    IsClosedImmersion.of_isPreimmersion _ <| by
      rw [Set.range_eq_univ.mpr hsurj.surj]
      exact isClosed_univ
  have : IsIso (f ∣_ O) := isIso_of_isClosedImmersion_of_surjective _
  rw [← morphismRestrict_ι]
  infer_instance

/-- `Stacks.ConstantSheaf.hasSheafify_over_moduleCat` with its universes pinned to the small
étale site and the coefficient universe `u + 1`; instance search leaves the constraint
`max (u + 1) u ?x =?= u + 1` stuck. -/
private theorem hasSheafify_over_moduleCat_succ_aux (B : BigEtaleSite.{u}) (Y : B.Scheme)
    (Λ : Type (u + 1)) [CommRing Λ] (U : SmallEtale B Y.obj Y.property) :
    HasSheafify ((SmallEtale.topology B Y.obj Y.property).over U) (ModuleCat.{u + 1} Λ) :=
  Stacks.ConstantSheaf.hasSheafify_over_moduleCat.{u + 1, u, u + 1, u + 1} _ Λ U

attribute [local instance high] hasSheafify_over_moduleCat_succ_aux
attribute [-instance] Stacks.ConstantSheaf.hasSheafify_over_moduleCat

variable (B : BigEtaleSite.{u}) (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

/-- **A constructible sheaf is locally constant of finite type on an open neighbourhood of each
generic point.** Let `X` be a reduced scheme of a big étale site, `G` a constructible sheaf of
`Λ`-modules on its small étale site and `η` a generic point of an irreducible component of `X`.
Then there is an open immersion `o : O ⟶ X` of the big étale site whose image contains `η` and
along which the inverse image of `G` is locally constant of finite type. -/
public theorem exists_isOpenImmersion_isFiniteTypeLocallyConstant_of_isConstructibleModuleSheaf
    (X : B.Scheme) [IsReduced X.obj]
    (G : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (hG : IsConstructibleModuleSheaf B X Λ G) {η : X.obj} (hη : η ∈ genericPoints X.obj) :
    ∃ (O : B.Scheme) (o : O ⟶ X), IsOpenImmersion (B.inclusion.map o) ∧
      η ∈ Set.range (B.inclusion.map o).base ∧
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B O.obj O.property)
        (((smallEtaleBaseChange B o).sheafPullback (ModuleCat.{u + 1} Λ)
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B O.obj O.property)).obj G) := by
  obtain ⟨U, hU, hηU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := η) trivial
  obtain ⟨s, hs⟩ := hG ⟨U, hU⟩
  have hηcov : η ∈ ⋃ i, Set.range (B.inclusion.map (s.inclusion i)).base := s.covers ▸ hηU
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hηcov
  set f := B.inclusion.map (s.inclusion i)
  have : IsImmersion f := s.isImmersion i
  have : IsAffine U.toScheme := hU
  have hspec : SpectralSpace U.toScheme :=
    Scheme.spectralSpace_of_compactSpace_quasiSeparatedSpace U.toScheme
  let ηU : U.toScheme := ⟨η, hηU⟩
  have hηU' : ηU ∈ genericPoints U.toScheme :=
    TopologicalSpace.mem_genericPoints_of_forall_specializes_eq fun y hy =>
      U.ι.isOpenEmbedding.injective
        (TopologicalSpace.forall_specializes_eq_of_mem_genericPoints hη _
          (hy.map U.ι.base.hom.continuous))
  set T := U.ι.base ⁻¹' Set.range f.base
  have hTc : Topology.IsConstructible T := s.constructible i
  have hηT : ηU ∈ T := hi
  have hnot : ηU ∉ closure Tᶜ :=
    Topology.notMem_closure_of_mem_genericPoints_of_isConstructible hηU' hTc.compl
      (fun h => h hηT)
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
  · refine Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr.{_, _, u + 1, u + 1} _ _
      ((smallEtaleSheafPullbackCompIso B _ _ X ι' (s.inclusion i) (ModuleCat.{u + 1} Λ)).app G) ?_
    exact isFiniteTypeLocallyConstant_smallEtaleSheafPullback B Λ ι' _ (hs i)

/-- **A sheaf locally constant of finite type is constant on affine étale neighbourhoods.** Let
`H` be a sheaf of `Λ`-modules on the small étale site of a scheme `O` of a big étale site which is
locally constant of finite type, and `x` a point of `O`. There is an object `V` of the small étale
site, with affine underlying scheme and `x` in the image of its structure morphism, on whose own
small étale site the inverse image of `H` is the constant sheaf on a finitely generated module. -/
public theorem exists_etale_affine_constant_of_isFiniteTypeLocallyConstant (O : B.Scheme)
    (H : Sheaf (SmallEtale.topology B O.obj O.property) (ModuleCat.{u + 1} Λ))
    (hH : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
      (SmallEtale.topology B O.obj O.property) H) (x : O.obj) :
    ∃ (V : SmallEtale B O.obj O.property) (E : ModuleCat.{u + 1} Λ),
      IsAffine ((SmallEtale.toScheme B O.obj O.property).obj V) ∧
      x ∈ Set.range (B.inclusion.map V.obj.hom).base ∧ ModuleCat.isFG Λ E ∧
      Nonempty ((constantSheaf (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
          (ModuleCat.{u + 1} Λ)).obj E ≅
        ((smallEtaleBaseChange B V.obj.hom).sheafPullback (ModuleCat.{u + 1} Λ)
          (SmallEtale.topology B O.obj O.property)
          (SmallEtale.topology B V.obj.left.1 V.obj.left.property)).obj H) := by
  obtain ⟨I, V, f, hcov, hc⟩ := hH (SmallEtale.final B O.obj O.property)
  obtain ⟨W₁, g₁, hg₁, w, hw⟩ :=
    SmallEtale.exists_mem_arrows_mem_range B O.obj O.property hcov
      (show (SmallEtale.toScheme B O.obj O.property).obj
        (SmallEtale.final B O.obj O.property) from x)
  obtain ⟨a, h, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg₁
  obtain ⟨E, hE, ⟨c⟩⟩ := hc a
  obtain ⟨W', hW'a, hwW', -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := w) trivial
  have hW'c : B.Contains W'.toScheme :=
    Scheme.size_lt_of_isOpenImmersion W'.ι W₁.obj.left.property
  let V₀ := SmallEtale.openObj W₁ W' hW'c
  have c₀ := Stacks.ConstantSheaf.constantIsoOverPullbackOfMap _ (ModuleCat.{u + 1} Λ)
    (SmallEtale.openObjHom W₁ W' hW'c) H E
    (Stacks.ConstantSheaf.constantIsoOverPullbackOfMap _ (ModuleCat.{u + 1} Λ) h H E c)
  refine ⟨V₀, E, hW'a, ?_, hE,
    (nonempty_constantSheafIso_over_iff B O.obj O.property V₀ (ModuleCat.{u + 1} Λ) H E).mp
      ⟨c₀⟩⟩
  refine ⟨⟨w, hwW'⟩, ?_⟩
  rw [← hw]
  show (B.inclusion.map W₁.obj.hom).base w = (B.inclusion.map g₁.hom.left).base w
  rw [show B.inclusion.map W₁.obj.hom =
      B.inclusion.map (g₁.hom.left ≫ (SmallEtale.final B O.obj O.property).obj.hom) by
    rw [Over.w g₁.hom]]
  rfl

end AlgebraicGeometry

end
