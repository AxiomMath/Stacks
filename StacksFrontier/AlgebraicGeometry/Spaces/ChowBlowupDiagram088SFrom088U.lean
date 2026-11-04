module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowBlowupDiagramReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemmaTag
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria

/-!
# Stacks 088S for a separated base, from Stacks 088U

Stacks 088S is the diagram of `AlgebraicGeometry.Space.HasChowBlowupDiagram` for a separated
morphism of finite type `f : X ⟶ Y` of algebraic spaces with `Y` Noetherian.  This file proves it
when `Y` is moreover separated, from Stacks 088U, Chow's lemma for algebraic spaces
(`AlgebraicGeometry.Space.C1573.exists_isAdmissibleBlowup_isImmersion_projectiveSpace`), which
assumes `Y` separated.  Stacks 088S for any Noetherian `Y`, from Stacks 088Q through Stacks 088R,
is `AlgebraicGeometry.Space.exists_denseOpen_hasChowBlowupDiagram`.

## Main results

* `AlgebraicGeometry.Space.exists_denseOpen_hasChowBlowupDiagram_of_isAbsolutelySeparated`:
  Stacks 088S for `Y` separated and Noetherian.

## References

* [Stacks Project, Tag 088S](https://stacks.math.columbia.edu/tag/088S)
* [Stacks Project, Tag 088U](https://stacks.math.columbia.edu/tag/088U)
* [Stacks Project, Tag 088G](https://stacks.math.columbia.edu/tag/088G)
* [Stacks Project, Tag 085T](https://stacks.math.columbia.edu/tag/085T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 088S for a separated base, from Stacks 088U.**  Let `f : X ⟶ Y` be a separated
morphism of finite type of algebraic spaces over `S` with `Y` separated and Noetherian.  Then
there are a dense open subspace `U ⊆ X`, an integer `n` and an immersion `i : U ⟶ ℙⁿ_Y` over
`Y` for which the diagram of Stacks 088S exists
(`AlgebraicGeometry.Space.HasChowBlowupDiagram`). -/
theorem exists_denseOpen_hasChowBlowupDiagram_of_isAbsolutelySeparated
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f)
    (hYsep : IsAbsolutelySeparated B S hS hZ Y)
    (hYnoeth : IsNoetherian B S hS hZ Y) :
    ∃ (U : Subfunctor X) (hU : IsOpenSubspace B S hS U),
      (letI : TopologicalSpace (points B S hS X) := pointTopology B S hS X;
        DenseRange (pointsMap B S hS U.toFunctor U.ι)) ∧
      ∃ (n : ℕ) (i : U.toFunctor ⟶ projectiveSpaceOver B S hS Y n),
        IsImmersion B S hS i ∧ i ≫ prod.fst = U.ι ≫ f ∧
          HasChowBlowupDiagram B S hS hX f U hU n i := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
  obtain ⟨U, hdense, n, X', π, iP, hadm, himm, hcomp⟩ :=
    C1573.exists_isAdmissibleBlowup_isImmersion_projectiveSpace hZ
      (X := ⟨X, hX⟩) (Y := ⟨Y, hY⟩) (ObjectProperty.homMk f) hsep hft hYsep hYnoeth
  have hP : IsAlgebraicSpace B S hS (projectiveSpaceOver B S hS Y n) :=
    isAlgebraicSpace_projectiveSpaceOver B S hS hY n
  have hPY : IsProper B S hS (prod.fst : projectiveSpaceOver B S hS Y n ⟶ Y) :=
    isProper_projectiveSpaceOver_fst B S hS hY n
  have hPqs : IsAbsolutelyQuasiSeparated B S hS hZ (projectiveSpaceOver B S hS Y n) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hP hYnoeth.2.1
      (isQuasiSeparated_of_isSeparated B S hS hPY.1)
  set m : X'.1 ⟶ projectiveSpaceOver B S hS Y n :=
    iP ≫ (prodIsoPullback Y (projectiveSpaceFunctor B S hS n)).inv with hmdef
  have hmfst : m ≫ prod.fst = π.hom ≫ f := by
    rw [hmdef, Category.assoc, prodIsoPullback_inv_fst]
    exact hcomp.symm
  have hmimm : IsImmersion B S hS m :=
    isImmersion_comp B S hS _ _ himm
      (isImmersion_of_isOpenImmersion B S hS (isOpenImmersion_of_isIso B S hS _))
  have hXqc : IsQuasiCompactSpace B S hS X :=
    isQuasiCompactSpace_of_iso B S hS (asIso (pullback.snd (𝟙 Y) f))
      (hft.2 Y hY hYnoeth.1 (𝟙 Y))
  have hπproper : IsProper B S hS π.hom := IsAdmissibleBlowup.isProper B S hS hadm
  have hX'qc : IsQuasiCompactSpace B S hS X'.1 :=
    isQuasiCompactSpace_of_iso B S hS (asIso (pullback.snd (𝟙 X) π.hom))
      (hπproper.2.1.2 X hX hXqc (𝟙 X))
  have hmqc : IsQuasiCompact B S hS m :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hP hPqs hX'qc m
  obtain ⟨hjopen, -, -, -, -⟩ :=
    isOpenImmersion_and_dense_toSchemeTheoreticImage_of_qc_or_reduced B S hS X'.2 hP m hmimm
      (Or.inl hmqc)
  set Zs := schemeTheoreticImageSubfunctor B S hS m
  have hZcl : IsClosedSubspace B S hS Zs :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS m hP
  set jm := toSchemeTheoreticImage B S hS m
  have hjmk : jm ≫ Zs.ι = m := toSchemeTheoreticImage_ι B S hS m
  obtain ⟨Zc, hZcfp, hZcdisj, hZcbl⟩ := hadm
  set OZ := openComplementOfClosedSubspace B S hS ⟨X, hX⟩ Zc
  have hUOZ : U.1 ≤ OZ.1 := by
    refine le_of_range_pointsMap_ι_subset B S hS OZ.2 ?_
    change subspacePointSet B S hS X U.1 ⊆ subspacePointSet B S hS X OZ.1
    rw [subspacePointSet_openComplement B S hS ⟨X, hX⟩ Zc]
    exact Set.disjoint_left.1 hZcdisj
  have hiso : IsIso (OZ.1.fromPreimage π.hom) := isIso_fromPreimage_openComplement hZcbl
  have hrangeU : Subfunctor.range U.1.ι ≤ OZ.1 := by
    rw [Subfunctor.range_ι]; exact hUOZ
  set s₀ : U.1.toFunctor ⟶ OZ.1.toFunctor := Subfunctor.lift U.1.ι hrangeU
  have hs₀ι : s₀ ≫ OZ.1.ι = U.1.ι := Subfunctor.lift_ι _ _
  have hs₀open : IsOpenImmersion B S hS s₀ := by
    refine isOpenImmersion_of_comp_mono B S hS s₀ OZ.1.ι ?_
    rw [hs₀ι]; exact U.2.2
  have hpreopen : IsOpenSubspace B S hS (OZ.1.preimage π.hom) :=
    isOpenSubspace_preimage B S hS π.hom OZ.1 hX X'.2 OZ.2
  set sU : U.1.toFunctor ⟶ X'.1 :=
    s₀ ≫ inv (OZ.1.fromPreimage π.hom) ≫ (OZ.1.preimage π.hom).ι with hsUdef
  have hsUπ : sU ≫ π.hom = U.1.ι := by
    rw [hsUdef, Category.assoc, Category.assoc, ← Subfunctor.fromPreimage_ι OZ.1 π.hom,
      IsIso.inv_hom_id_assoc, hs₀ι]
  have hsUopen : IsOpenImmersion B S hS sU :=
    isOpenImmersion_comp B S hS _ _ hs₀open
      (isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS _) hpreopen.2)
  set uZ : U.1.toFunctor ⟶ Zs.toFunctor := sU ≫ jm with huZdef
  have huZopen : IsOpenImmersion B S hS uZ :=
    isOpenImmersion_comp B S hS _ _ hsUopen hjopen
  have : Mono uZ := mono_of_isOpenImmersion B S hS _ huZopen
  have hUZ : IsOpenSubspace B S hS (Subfunctor.range uZ) :=
    isOpenSubspace_range_of_open B S hS uZ U.2.1 huZopen
  have hiimm : IsImmersion B S hS (uZ ≫ Zs.ι) :=
    isImmersion_comp B S hS _ _ (isImmersion_of_isOpenImmersion B S hS huZopen)
      (isImmersion_of_isClosedImmersion B S hS hZcl.2)
  have hifac : (uZ ≫ Zs.ι) ≫ prod.fst = U.1.ι ≫ f := by
    rw [huZdef, Category.assoc, Category.assoc, ← Category.assoc jm Zs.ι prod.fst, hjmk, hmfst,
      ← Category.assoc, hsUπ]
  have hZY : IsProper B S hS (Zs.ι ≫ prod.fst) :=
    isProper_comp B S hS hZcl.1 hP hY _ _
      (isProper_of_isClosedImmersion B S hS hZcl.1 hP _ hZcl.2) hPY
  have hZYrep : yoneda.relativelyRepresentable (Zs.ι ≫ prod.fst) :=
    MorphismProperty.comp_mem _ _ _ hZcl.2.rep
      (relativelyRepresentable_projectiveSpaceOver_fst B S hS Y n)
  refine ⟨U.1, U.2, hdense, n, uZ ≫ Zs.ι, hiimm, hifac, X', ⟨Zs.toFunctor, hZcl.1⟩,
    ⟨Zs.toFunctor, hZcl.1⟩, π, ObjectProperty.homMk jm, 𝟙 _, Zs.ι, sU, uZ, uZ, hUZ,
    hsUopen, huZopen, huZopen, ⟨Zc, hZcfp, hZcdisj, hZcbl⟩, hjopen, ?_, ?_,
    isAdmissibleBlowup_id_emptyClosedSubspace ⟨Zs.toFunctor, hZcl.1⟩ ⟨Subfunctor.range uZ, hUZ⟩,
    hZcl.2, hsUπ, rfl, ?_, rfl, ?_⟩
  · simpa only [ObjectProperty.FullSubcategory.id_hom, Category.id_comp] using hZY
  · simpa only [ObjectProperty.FullSubcategory.id_hom, Category.id_comp] using hZYrep
  · simp only [ObjectProperty.FullSubcategory.id_hom, Category.comp_id]
  · simp only [ObjectProperty.homMk_hom, ObjectProperty.FullSubcategory.id_hom, Category.id_comp]
    rw [← Category.assoc, hjmk, hmfst]

end AlgebraicGeometry.Space

end
