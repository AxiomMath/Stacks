module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreDimensionDrop
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFibreSum
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ResidueFieldAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionOneSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.ProperMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFamilySchematicNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointNeighborhoodLift
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase

/-!
# A schematic neighbourhood of the generic fibre in the dimension-drop case

In Situation 0EDT let `W` and `W'` be good integral algebraic spaces over the base and let
`q : W ⟶ W'` be a proper morphism over the base with `dim_δ(W) = dim_δ(W') + 1`. This is the
situation of the branch `dim_δ(p(W)) = k` of the proof of **Stacks 0EQC**. The source reduces
it to schemes in three moves: shrink `W'` to an open which is a scheme, observe that the generic
fibre `W_η` is a scheme by Stacks 0ADD, and descend that along the limit `Spec R(W') = lim U` by
Stacks 07SR.

This file does the same reduction without forming the generic fibre or its limit presentation.

## Main results

* `AlgebraicGeometry.Space.exists_isRepresentable_preimage_of_deltaValue_drop`: there is an open
  subspace `U ⊆ W'` containing the generic point of `W'` which is a scheme and whose inverse image
  `q⁻¹(U) ⊆ W` is a scheme.

## The argument

Shrink `W'` to an affine open subspace `U₀` around its generic point `η` and put
`P = q⁻¹(U₀)`. Then `P ⟶ U₀` is proper, so `P` is separated (Stacks 0ADD's hypothesis is not
available on `W` itself: a good space need not be separated), and it is locally Noetherian.
Every point of `P` over `η` has local ring of dimension at most one, by
`AlgebraicGeometry.Space.localRingDimension_le_one_of_pointsMap_eq_genericPoint`, so by
Stacks 0ADD it lies in the schematic locus `L` of `P` (Stacks 03JH). The complement `F` of `L`
in `|P|` is closed, so its image in `|U₀|` is closed because `P ⟶ U₀` is universally closed, and
it misses `η`. The open `U = U₀ ∖ q(F)` contains `η`, and `q⁻¹(U) ⊆ L` is an open subspace of a
scheme, hence a scheme.

This replaces the limit argument of Stacks 07SR by the closedness of a proper morphism, which is
the elementary reason Stacks 07SR applies in the source.

## References

* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 07SR](https://stacks.math.columbia.edu/tag/07SR)
* [Stacks Project, Tag 0EQC](https://stacks.math.columbia.edu/tag/0EQC)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})

/-- An open subspace of an algebraic space containing a point and represented by an affine
scheme exists around every point of a good algebraic space which lies on a dense open subspace
which is a scheme; in particular around the generic point of a good integral algebraic space. -/
theorem exists_isOpenSubspace_isAffineSpace_genericPoint
    {W' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sW' : W' ⟶ D.space)
    (hW' : D.IsGood sW') (hW'int : IsIntegralSpace D.site D.base D.base_mem W') :
    ∃ U₀ : Subfunctor W', IsOpenSubspace D.site D.base D.base_mem U₀ ∧
      IsAffineSpace D.site D.base D.base_mem U₀.toFunctor ∧
      genericPoint D.site D.base D.base_mem hW'.1 hW'int ∈
        Set.range (pointsMap D.site D.base D.base_mem U₀.toFunctor U₀.ι) := by
  obtain ⟨G, hG, hGrep, hGdense⟩ :=
    D.exists_denseRange_isRepresentable_isOpenSubspace_of_isGood sW' hW'
  have hGopen : IsOpen (Set.range (pointsMap D.site D.base D.base_mem G.toFunctor G.ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion D.site D.base D.base_mem G.ι hG.2
  have hηG : genericPoint D.site D.base D.base_mem hW'.1 hW'int ∈
      Set.range (pointsMap D.site D.base D.base_mem G.toFunctor G.ι) := by
    refine ((isGenericPoint_genericPoint D.site D.base D.base_mem hW'.1 hW'int).mem_open_set_iff
      hGopen).2 ?_
    obtain ⟨y⟩ := hGdense.nonempty_iff.2 ⟨genericPoint D.site D.base D.base_mem hW'.1 hW'int⟩
    exact ⟨_, Set.mem_univ _, y, rfl⟩
  have _ := hGrep
  set T := G.toFunctor.reprX with hT
  set e : yoneda.obj T ≅ G.toFunctor := G.toFunctor.reprW with he
  set α : yoneda.obj T ⟶ W' := e.hom ≫ G.ι with hα
  have hαopen : IsOpenImmersion D.site D.base D.base_mem α :=
    MorphismProperty.RespectsIso.precomp _ e.hom G.ι hG.2
  obtain ⟨g, hg⟩ := hηG
  set t : (BigFppfOver.toScheme D.site D.base D.base_mem).obj T :=
    pointsToScheme D.site D.base D.base_mem T (pointsMap D.site D.base D.base_mem _ e.inv g)
    with ht
  obtain ⟨-, ⟨Vaff, hVaff, rfl⟩, htV, -⟩ :=
    ((BigFppfOver.toScheme D.site D.base D.base_mem).obj T).isBasis_affineOpens
      |>.exists_subset_of_mem_open
      (show t ∈ (⊤ : ((BigFppfOver.toScheme D.site D.base D.base_mem).obj T).Opens) from trivial)
      (⊤ : ((BigFppfOver.toScheme D.site D.base D.base_mem).obj T).Opens).2
  obtain ⟨U₀, hU₀, hU₀aff, hU₀range⟩ :=
    exists_isOpenSubspace_isAffineSpace_of_isAffineOpen D.site D.base D.base_mem α hαopen Vaff
      hVaff
  refine ⟨U₀, hU₀, hU₀aff, ?_⟩
  rw [hU₀range]
  refine ⟨pointsMap D.site D.base D.base_mem _ e.inv g, htV, ?_⟩
  have hee : pointsMap D.site D.base D.base_mem _ e.hom
      (pointsMap D.site D.base D.base_mem _ e.inv g) = g := by
    rw [← pointsMap_comp_apply, Iso.inv_hom_id, pointsMap_id, id_eq]
  rw [hα, pointsMap_comp_apply, hee, hg]

variable {W W' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sW : W ⟶ D.space) (hW : D.IsGood sW) (hWint : IsIntegralSpace D.site D.base D.base_mem W)
    (sW' : W' ⟶ D.space) (hW' : D.IsGood sW')
    (hW'int : IsIntegralSpace D.site D.base D.base_mem W')
    (q : W ⟶ W') (hq : q ≫ sW' = sW)

include hWint hq in
/-- **A schematic neighbourhood of the generic fibre in the dimension-drop branch of
Stacks 0EQC.** Let `q : W ⟶ W'` be a proper morphism over the base of good integral algebraic
spaces with `dim_δ(W) = dim_δ(W') + 1`. There is an open subspace `U ⊆ W'` containing the
generic point of `W'` which is a scheme and whose inverse image `q⁻¹(U)` is a scheme.

See the module docstring for the argument: Stacks 0ADD on the inverse image of an affine open,
and the closedness of the proper morphism in place of the limit argument of Stacks 07SR. -/
theorem exists_isRepresentable_preimage_of_deltaValue_drop
    (hqp : IsProper D.site D.base D.base_mem q) (k : ℤ)
    (hWd : D.deltaValue sW (genericPoint D.site D.base D.base_mem hW.1 hWint) = k + 1)
    (hW'd : D.deltaValue sW' (genericPoint D.site D.base D.base_mem hW'.1 hW'int) = k) :
    ∃ U : Subfunctor W', IsOpenSubspace D.site D.base D.base_mem U ∧
      U.toFunctor.IsRepresentable ∧
      genericPoint D.site D.base D.base_mem hW'.1 hW'int ∈
        Set.range (pointsMap D.site D.base D.base_mem U.toFunctor U.ι) ∧
      (U.preimage q).toFunctor.IsRepresentable := by
  classical
  -- an affine open `U₀` around the generic point of `W'`, and its inverse image `P`
  obtain ⟨U₀, hU₀, hU₀aff, hηU₀⟩ :=
    exists_isOpenSubspace_isAffineSpace_genericPoint D sW' hW' hW'int
  obtain ⟨T, hTaff, ⟨eT⟩⟩ := hU₀aff
  set P := U₀.preimage q with hPdef
  have hP : IsOpenSubspace D.site D.base D.base_mem P :=
    isOpenSubspace_preimage D.site D.base D.base_mem q U₀ hW'.1 hW.1 hU₀
  set q₀ : P.toFunctor ⟶ U₀.toFunctor := U₀.fromPreimage q with hq₀def
  have hsq : IsPullback q₀ P.ι U₀.ι q := Subfunctor.isPullback_preimage q U₀
  have hq₀ : IsProper D.site D.base D.base_mem q₀ :=
    isProper_of_isPullback' hP.1 hW.1 hU₀.1 hW'.1 hsq.flip hqp
  -- `P` is separated and locally Noetherian
  have hsep : IsAbsolutelySeparated D.site D.base D.base_mem D.site.contains_terminal
      P.toFunctor :=
    isAbsolutelySeparated_of_isSeparated_of_isAffineRepresentation D.site D.base D.base_mem
      D.site.contains_terminal T hTaff eT q₀ hq₀.1
  have hPet : IsEtale D.site D.base D.base_mem P.ι :=
    isEtale_of_isOpenImmersion D.site D.base D.base_mem hP.2
  have hnoeth : HasEtaleLocalProperty D.site D.base D.base_mem P.toFunctor
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base D.base_mem hP.1 hW.1 P.ι
      (isLocallyOfFiniteType_of_isEtale D.site D.base D.base_mem hW.1 hPet)
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sW hW)
  -- the schematic locus `L` of `P` contains every point over the generic point of `W'`
  obtain ⟨hL, hLrep⟩ :=
    isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace D.site D.base
      D.base_mem hP.1
  set L := schematicLocus D.site D.base D.base_mem P.toFunctor with hLdef
  have hfib : ∀ p : points D.site D.base D.base_mem P.toFunctor,
      pointsMap D.site D.base D.base_mem W q (pointsMap D.site D.base D.base_mem _ P.ι p) =
        genericPoint D.site D.base D.base_mem hW'.1 hW'int →
      p ∈ Set.range (pointsMap D.site D.base D.base_mem L.toFunctor L.ι) := by
    intro p hp
    have hdimW := localRingDimension_le_one_of_pointsMap_eq_genericPoint D sW hW hWint sW' hW'
      hW'int q hq k hWd hW'd _ hp
    have hdim : localRingDimension D.site D.base D.base_mem p ≤ 1 := by
      rwa [← localRingDimension_pointsMap_of_etale D.site D.base D.base_mem hP.1 hW.1 P.ι hPet p]
    obtain ⟨G, hG, hGrep, hpG⟩ :=
      exists_isOpenSubspace_isRepresentable_of_localRingDimension_le_one D.site D.base
        D.base_mem hP.1 hsep hnoeth p hdim
    have hGL : G ≤ L := le_schematicLocus D.site D.base D.base_mem _ G hG hGrep
    obtain ⟨g, rfl⟩ := hpG
    exact ⟨pointsMap D.site D.base D.base_mem _ (Subfunctor.homOfLe hGL) g, by
      rw [← pointsMap_comp_apply, Subfunctor.homOfLe_ι]⟩
  -- the image in `|U₀|` of the complement of `L` is closed and misses the generic point
  set F : Set (points D.site D.base D.base_mem P.toFunctor) :=
    (Set.range (pointsMap D.site D.base D.base_mem L.toFunctor L.ι))ᶜ with hFdef
  have hFclosed : IsClosed F :=
    (isOpen_range_pointsMap_of_isOpenImmersion D.site D.base D.base_mem L.ι hL.2).isClosed_compl
  have hq₀closed : IsClosedMap (pointsMap D.site D.base D.base_mem P.toFunctor q₀) :=
    isClosedMap_pointsMap_of_pullback_fst_id D.site D.base D.base_mem q₀
      (hq₀.2.2 U₀.toFunctor hU₀.1 (𝟙 _))
  set C := pointsMap D.site D.base D.base_mem P.toFunctor q₀ '' F with hCdef
  have hCclosed : IsClosed C := hq₀closed F hFclosed
  have hU₀ι : ∀ p : points D.site D.base D.base_mem P.toFunctor,
      pointsMap D.site D.base D.base_mem _ U₀.ι (pointsMap D.site D.base D.base_mem _ q₀ p) =
        pointsMap D.site D.base D.base_mem W q (pointsMap D.site D.base D.base_mem _ P.ι p) := by
    intro p
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hsq.w]
  -- the open `U = U₀ ∖ C`, read in `|W'|`
  have _ : Mono U₀.ι := mono_of_isOpenImmersion D.site D.base D.base_mem _ hU₀.2
  set O : Set (points D.site D.base D.base_mem W') :=
    pointsMap D.site D.base D.base_mem _ U₀.ι '' Cᶜ with hOdef
  have hO : IsOpen O :=
    isOpenMap_pointsMap_of_isOpenImmersion D.site D.base D.base_mem U₀.ι hU₀.2 _
      hCclosed.isOpen_compl
  set U := openSubspaceOfPoints D.site D.base D.base_mem W' O with hUdef
  have hU : IsOpenSubspace D.site D.base D.base_mem U :=
    isOpenSubspace_openSubspaceOfPoints D.site D.base D.base_mem hW'.1 O hO
  have hUrange : Set.range (pointsMap D.site D.base D.base_mem U.toFunctor U.ι) = O :=
    range_pointsMap_ι_openSubspaceOfPoints D.site D.base D.base_mem O
  have hUU₀ : U ≤ U₀ := by
    refine le_of_range_pointsMap_ι_subset D.site D.base D.base_mem hU₀ ?_
    rw [hUrange]
    rintro _ ⟨o, -, rfl⟩
    exact ⟨o, rfl⟩
  have hU₀rep : U₀.toFunctor.IsRepresentable := by
    have : (yoneda.obj T).IsRepresentable := inferInstance
    exact isRepresentable_of_natIso _ eT.symm
  have hUrep : U.toFunctor.IsRepresentable :=
    isRepresentable_of_le_of_isRepresentable D.site D.base D.base_mem hU hUU₀ hU₀rep
  -- the generic point lies in `U`
  have hηU : genericPoint D.site D.base D.base_mem hW'.1 hW'int ∈
      Set.range (pointsMap D.site D.base D.base_mem U.toFunctor U.ι) := by
    rw [hUrange]
    obtain ⟨o, ho⟩ := hηU₀
    refine ⟨o, ?_, ho⟩
    rintro ⟨p, hpF, hpo⟩
    refine hpF (hfib p ?_)
    rw [← hU₀ι, hpo, ho]
  -- the inverse image of `U` lies in the image of `L`, so it is a scheme
  obtain ⟨K, hK, hKrep, hKrange⟩ :=
    exists_isOpenSubspace_isRepresentable_of_isOpenSubspace D.site D.base D.base_mem hW.1 hP hL
      hLrep
  have hV : IsOpenSubspace D.site D.base D.base_mem (U.preimage q) :=
    isOpenSubspace_preimage D.site D.base D.base_mem q U hW'.1 hW.1 hU
  have hVK : U.preimage q ≤ K := by
    refine le_of_range_pointsMap_ι_subset D.site D.base D.base_mem hK ?_
    rw [hKrange, range_pointsMap_subfunctor_preimage, hUrange]
    intro x hx
    obtain ⟨o, ho, hox⟩ := hx
    have hxP : x ∈ Set.range (pointsMap D.site D.base D.base_mem P.toFunctor P.ι) := by
      rw [hPdef, range_pointsMap_subfunctor_preimage]
      exact ⟨o, hox⟩
    obtain ⟨p, rfl⟩ := hxP
    have hpo : pointsMap D.site D.base D.base_mem _ q₀ p = o :=
      pointsMap_injective_of_mono D.site D.base D.base_mem U₀.ι (by rw [hU₀ι, hox])
    have hpL : p ∈ Set.range (pointsMap D.site D.base D.base_mem L.toFunctor L.ι) := by
      by_contra hpF
      exact ho ⟨p, hpF, hpo⟩
    obtain ⟨l, rfl⟩ := hpL
    exact ⟨l, by rw [pointsMap_comp_apply]⟩
  exact ⟨U, hU, hUrep, hηU, isRepresentable_of_le_of_isRepresentable D.site D.base D.base_mem hV
    hVK hKrep⟩

end AlgebraicGeometry.Space

end
