module

public import StacksCore.Topology.Noetherian.Retrocompact
public import StacksFrontier.AlgebraicGeometry.HProjectiveProper.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageOverOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.SectionGraphClosure
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.StandardAffineChart
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ClosedImmersionStructureSheaf
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# Chow's lemma over a Noetherian affine base

Let `A` be a Noetherian ring and let `f : X ⟶ Spec A` be separated, locally of finite type and
quasi-compact. Around any point `x` of `X` there is an affine open `U`, a projective space
`ℙᵐ_A`, an open `V ⊆ ℙᵐ_A` and a closed subscheme `Z ⊆ X ×_A ℙᵐ_A` of finite presentation whose
two projections `b : Z ⟶ X` and `c : Z ⟶ ℙᵐ_A` satisfy: `b` is an isomorphism over `U` and hits
`x`, `c` is a closed immersion over `V`, and `b ⁻¹ᵁ U = c ⁻¹ᵁ V`. Moreover the direct image of
`𝒪_Z` along `Z ⟶ X ×_A ℙᵐ_A`, placed in degree zero, is a pseudo-coherent object of
`D(𝒪_{X ×_A ℙᵐ_A})` whose cohomology is supported on the image of `Z`.

## Main results

* `AlgebraicGeometry.isImmersion_of_isClosedImmersion_morphismRestrict`: a morphism whose image
  lies in an open subscheme of its target and which is a closed immersion over that open is an
  immersion.
* `AlgebraicGeometry.range_toImage_eq_preimage_of_isClosedImmersion_morphismRestrict`: for such
  a morphism, if it is quasi-compact, the part of its scheme-theoretic image lying over that
  open is exactly its image.
* `AlgebraicGeometry.isClosedImmersion_morphismRestrict_pullbackLift_of_isClosedImmersion_opens`:
  the graph of `j : U ⟶ P` over `S` is a closed immersion into the part of `X ×_S P` lying over
  an open `W ⊆ P` into which `j` is a closed immersion, provided `f : X ⟶ S` is separated.
* `AlgebraicGeometry.preimage_imageι_comp_fst_eq_preimage_imageι_comp_snd`: clause (4) of
  [Stacks, Tag 0CSJ] — the part of the graph closure lying over `U` and the part lying over `W`
  coincide, both being the graph itself.
* `AlgebraicGeometry.isClosedImmersion_morphismRestrict_imageι_comp_snd`: clause (3) of
  [Stacks, Tag 0CSJ] — over `W` the second projection from the graph closure is the closed
  immersion `j`.
* `AlgebraicGeometry.exists_chowDatum_of_isNoetherian`: clauses (1)–(4) of [Stacks, Tag 0CSJ]
  for a Noetherian affine base.
* `AlgebraicGeometry.exists_chowDatum_isPseudoCoherent_of_isNoetherian`: all six clauses of
  [Stacks, Tag 0CSJ] for a Noetherian affine base, the complex of clauses (5) and (6) being
  `(b, c)_* 𝒪_Z` in degree zero.

## References

* [Stacks Project, Tag 0CSJ](https://stacks.math.columbia.edu/tag/0CSJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-- The inclusion of the open subscheme `⊤` is an isomorphism. -/
private theorem isIso_ι_of_eq_top {Y : Scheme.{u}} (U : Y.Opens) (hU : U = ⊤) : IsIso U.ι := by
  subst hU
  exact inferInstanceAs (IsIso (Scheme.topIso Y).hom)

/-- If `k ⁻¹ᵁ O = ⊤`, then `k` factors through `k ∣_ O` and `O.ι`. -/
private theorem inv_ι_comp_morphismRestrict_comp_ι {Y T : Scheme.{u}} (k : Y ⟶ T) (O : T.Opens)
    [IsIso (k ⁻¹ᵁ O).ι] : (inv (k ⁻¹ᵁ O).ι ≫ (k ∣_ O)) ≫ O.ι = k := by
  rw [Category.assoc, morphismRestrict_ι, IsIso.inv_hom_id_assoc]

/-- A morphism whose image lies in an open subscheme `O` of its target and which is a closed
immersion over `O` is an immersion. -/
theorem isImmersion_of_isClosedImmersion_morphismRestrict {Y T : Scheme.{u}} (k : Y ⟶ T)
    (O : T.Opens) (hO : k ⁻¹ᵁ O = ⊤) [IsClosedImmersion (k ∣_ O)] : IsImmersion k := by
  have := isIso_ι_of_eq_top _ hO
  have hw := inv_ι_comp_morphismRestrict_comp_ι k O
  rw [← hw]
  infer_instance

/-- **The part of a scheme-theoretic image lying over an open in which the morphism is closed.**
If `k : Y ⟶ T` is quasi-compact, its image lies in an open subscheme `O` of `T`, and `k` is a
closed immersion over `O`, then the part of the scheme-theoretic image of `k` lying over `O` is
exactly the image of `k`. -/
theorem range_toImage_eq_preimage_of_isClosedImmersion_morphismRestrict {Y T : Scheme.{u}}
    (k : Y ⟶ T) [QuasiCompact k] (O : T.Opens) (hO : k ⁻¹ᵁ O = ⊤)
    [IsClosedImmersion (k ∣_ O)] :
    Set.range k.toImage = k.imageι ⁻¹' (O : Set T) := by
  have := isIso_ι_of_eq_top _ hO
  have hw := inv_ι_comp_morphismRestrict_comp_ι k O
  have hqc : QuasiCompact ((inv (k ⁻¹ᵁ O).ι ≫ (k ∣_ O)) ≫ O.ι) := by
    rw [hw]; infer_instance
  rw [← hw]
  exact range_toImage_comp_opens_ι O _

/-- The graph `(U.ι, j)` of a morphism `j` which factors through an open `W` of `P` has
preimage of `X ×_S W` equal to the whole of `U`. -/
private theorem preimage_pullback_lift_snd_eq_top {X S P : Scheme.{u}} (f : X ⟶ S) (g : P ⟶ S)
    (U : X.Opens) (W : P.Opens) (j : U.toScheme ⟶ P) (j' : U.toScheme ⟶ W.toScheme)
    (hj : j' ≫ W.ι = j) (h : U.ι ≫ f = j ≫ g) :
    pullback.lift U.ι j h ⁻¹ᵁ (pullback.snd f g ⁻¹ᵁ W) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, pullback.lift_snd, ← hj, Scheme.Hom.comp_preimage,
      W.ι_preimage_self]
    simp

/-- The graph `(U.ι, j) : U ⟶ X ×_S P` of a morphism `j : U ⟶ P` over `S` is a closed immersion
into the part of `X ×_S P` lying over an open `W` of `P` through which `j` factors by a closed
immersion, provided `f : X ⟶ S` is separated. Equivalently, the graph is closed in `X ×_S W`. -/
theorem isClosedImmersion_morphismRestrict_pullbackLift_of_isClosedImmersion_opens
    {X S P : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (g : P ⟶ S) (U : X.Opens) (W : P.Opens)
    (j : U.toScheme ⟶ P) (j' : U.toScheme ⟶ W.toScheme) [IsClosedImmersion j']
    (hj : j' ≫ W.ι = j) (h : U.ι ≫ f = j ≫ g) :
    IsClosedImmersion (pullback.lift U.ι j h ∣_ pullback.snd f g ⁻¹ᵁ W) := by
  have hdom := preimage_pullback_lift_snd_eq_top f g U W j j' hj h
  have := isIso_ι_of_eq_top _ hdom
  have e : (pullback.lift U.ι j h ∣_ pullback.snd f g ⁻¹ᵁ W) ≫ (pullback.snd f g ∣_ W) =
      (pullback.lift U.ι j h ⁻¹ᵁ (pullback.snd f g ⁻¹ᵁ W)).ι ≫ j' := by
    rw [← cancel_mono W.ι]
    simp only [Category.assoc]
    rw [hj, morphismRestrict_ι, morphismRestrict_ι_assoc, pullback.lift_snd]
  have : IsClosedImmersion ((pullback.lift U.ι j h ∣_ pullback.snd f g ⁻¹ᵁ W) ≫
      (pullback.snd f g ∣_ W)) := by
    rw [e]; infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.snd f g ∣_ W)

/-- **Clause (4) of [Stacks, Tag 0CSJ].** Let `f : X ⟶ S` and `g : P ⟶ S` be separated, let `U`
be an open subscheme of `X`, and let `j : U ⟶ P` be a morphism over `S` factoring as a closed
immersion into an open `W` of `P`. The part of the scheme-theoretic closure of the graph of `j`
lying over `U` and the part lying over `W` coincide: both are the graph itself. -/
theorem preimage_imageι_comp_fst_eq_preimage_imageι_comp_snd {X S P : Scheme.{u}}
    (f : X ⟶ S) [IsSeparated f] (g : P ⟶ S) [IsSeparated g] (U : X.Opens) (W : P.Opens)
    (j : U.toScheme ⟶ P) (j' : U.toScheme ⟶ W.toScheme) [IsClosedImmersion j']
    (hj : j' ≫ W.ι = j) (h : U.ι ≫ f = j ≫ g)
    [QuasiCompact (pullback.lift U.ι j h)] :
    ((pullback.lift U.ι j h).imageι ≫ pullback.fst f g) ⁻¹ᵁ U =
      ((pullback.lift U.ι j h).imageι ≫ pullback.snd f g) ⁻¹ᵁ W := by
  have h1 : pullback.lift U.ι j h ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, pullback.lift_fst]
    exact U.ι_preimage_self
  have h2 := preimage_pullback_lift_snd_eq_top f g U W j j' hj h
  have : IsClosedImmersion (pullback.lift U.ι j h ∣_ pullback.fst f g ⁻¹ᵁ U) :=
    isClosedImmersion_morphismRestrict_pullbackLift_of_isSeparated f g U j h
  have : IsClosedImmersion (pullback.lift U.ι j h ∣_ pullback.snd f g ⁻¹ᵁ W) :=
    isClosedImmersion_morphismRestrict_pullbackLift_of_isClosedImmersion_opens f g U W j j' hj h
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
  exact TopologicalSpace.Opens.ext
    ((range_toImage_eq_preimage_of_isClosedImmersion_morphismRestrict _ _ h1).symm.trans
      (range_toImage_eq_preimage_of_isClosedImmersion_morphismRestrict _ _ h2))

/-- **Clause (3) of [Stacks, Tag 0CSJ].** In the situation above, the second projection from the
scheme-theoretic closure of the graph of `j` is, over `W`, the closed immersion `j` itself; in
particular it is a closed immersion over `W`. -/
theorem isClosedImmersion_morphismRestrict_imageι_comp_snd {X S P : Scheme.{u}}
    (f : X ⟶ S) [IsSeparated f] (g : P ⟶ S) (U : X.Opens) (W : P.Opens)
    (j : U.toScheme ⟶ P) (j' : U.toScheme ⟶ W.toScheme) [IsClosedImmersion j']
    (hj : j' ≫ W.ι = j) (h : U.ι ≫ f = j ≫ g)
    [QuasiCompact (pullback.lift U.ι j h)] :
    IsClosedImmersion (((pullback.lift U.ι j h).imageι ≫ pullback.snd f g) ∣_ W) := by
  have h2 := preimage_pullback_lift_snd_eq_top f g U W j j' hj h
  have : IsClosedImmersion (pullback.lift U.ι j h ∣_ pullback.snd f g ⁻¹ᵁ W) :=
    isClosedImmersion_morphismRestrict_pullbackLift_of_isClosedImmersion_opens f g U W j j' hj h
  have : IsImmersion (pullback.lift U.ι j h) :=
    isImmersion_of_isClosedImmersion_morphismRestrict _ _ h2
  have : IsOpenImmersion (pullback.lift U.ι j h).toImage :=
    isOpenImmersion_toImage _ (Or.inl inferInstance)
  have hrange : Set.range (pullback.lift U.ι j h).toImage =
      Set.range (((pullback.lift U.ι j h).imageι ≫ pullback.snd f g) ⁻¹ᵁ W).ι := by
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_preimage]
    exact range_toImage_eq_preimage_of_isClosedImmersion_morphismRestrict _ _ h2
  obtain ⟨ε, hε⟩ : ∃ ε : U.toScheme ≅
      (((pullback.lift U.ι j h).imageι ≫ pullback.snd f g) ⁻¹ᵁ W).toScheme,
      ε.hom ≫ (((pullback.lift U.ι j h).imageι ≫ pullback.snd f g) ⁻¹ᵁ W).ι =
        (pullback.lift U.ι j h).toImage :=
    ⟨IsOpenImmersion.isoOfRangeEq _ _ hrange, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩
  have key : ε.hom ≫ (((pullback.lift U.ι j h).imageι ≫ pullback.snd f g) ∣_ W) = j' := by
    rw [← cancel_mono W.ι, hj]
    simp only [Category.assoc]
    rw [morphismRestrict_ι, ← Category.assoc, hε, ← Category.assoc,
      Scheme.Hom.toImage_imageι, pullback.lift_snd]
  have e2 : (((pullback.lift U.ι j h).imageι ≫ pullback.snd f g) ∣_ W) = ε.inv ≫ j' := by
    rw [← key, Iso.inv_hom_id_assoc]
  rw [e2]
  infer_instance

/-- **Clauses (1)–(4) of [Stacks, Tag 0CSJ] over a Noetherian base.** Let `A` be a Noetherian
ring and let `f : X ⟶ Spec A` be separated, locally of finite type and quasi-compact. For every
point `x` of `X` there are an open `U ∋ x`, an `m`, an open `V` of `ℙᵐ_A`, a closed subscheme
`iZ : Z ⟶ X ×_A ℙᵐ_A` and a point `z` of `Z` such that, writing `b` and `c` for the two
projections of `Z`: `iZ` is of finite presentation, `b` is an isomorphism over `U` and `b z = x`,
`c` is a closed immersion over `V`, and `b ⁻¹ᵁ U = c ⁻¹ᵁ V`. -/
theorem exists_chowDatum_of_isNoetherian {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (x : X) :
    ∃ (U : X.Opens) (m : ℕ) (V : (projectiveSpaceOver m (Spec (.of A))).Opens) (Z : Scheme.{u})
      (iZ : Z ⟶ pullback f (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))) (z : Z),
      x ∈ U ∧ IsClosedImmersion iZ ∧ FinitePresentation iZ ∧
        IsIso ((iZ ≫ pullback.fst f
          (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))) ∣_ U) ∧
        (iZ ≫ pullback.fst f
          (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))).base z = x ∧
        IsClosedImmersion ((iZ ≫ pullback.snd f
          (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))) ∣_ V) ∧
        (iZ ≫ pullback.fst f
            (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))) ⁻¹ᵁ U =
          (iZ ≫ pullback.snd f
            (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))) ⁻¹ᵁ V := by
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  obtain ⟨U, hUaff, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by simp)
  have : IsAffine U.toScheme := hUaff
  have : IsNoetherian U.toScheme := isNoetherian_of_locallyOfFiniteType U.ι
  obtain ⟨m, c₀, hc₀, hc₀S⟩ := exists_isClosedImmersion_affineSpace (U.ι ≫ f)
  have := hc₀
  have hcomm : U.ι ≫ f = (c₀ ≫ projectiveSpaceOver.affineChart m 0
      (Equiv.ulift.{u}.trans (finSuccAboveEquiv (0 : Fin (m + 1)))) (Spec (.of A))) ≫
      (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A)) := by
    rw [Category.assoc, projectiveSpaceOver.affineChart_over]
    exact hc₀S.symm
  have hj : (c₀ ≫ (projectiveSpaceOver.standardChartIso m 0
        (Equiv.ulift.{u}.trans (finSuccAboveEquiv (0 : Fin (m + 1)))) (Spec (.of A))).hom) ≫
      (projectiveSpaceOver.standardChart m (Spec (.of A)) 0).ι =
      c₀ ≫ projectiveSpaceOver.affineChart m 0
        (Equiv.ulift.{u}.trans (finSuccAboveEquiv (0 : Fin (m + 1)))) (Spec (.of A)) := by
    rw [Category.assoc, projectiveSpaceOver.standardChartIso_hom_ι]
  have hUretro : IsRetrocompact (U : Set X) := noetherianSpace_isRetrocompact _ _
  have : IsLocallyNoetherian
      (pullback f (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst f (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A)))
  have hiso2 : IsIso (((pullback.lift U.ι (c₀ ≫ projectiveSpaceOver.affineChart m 0
      (Equiv.ulift.{u}.trans (finSuccAboveEquiv (0 : Fin (m + 1)))) (Spec (.of A)))
      hcomm).imageι ≫ pullback.fst f
      (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))) ∣_ U) :=
    isIso_morphismRestrict_imageι_comp_fst_of_isSeparated f _ U hUretro _ hcomm
  obtain ⟨z, hz⟩ := @exists_base_eq_of_isIso_morphismRestrict X _ _ U hiso2 x hxU
  exact ⟨U, m, projectiveSpaceOver.standardChart m (Spec (.of A)) 0, _, _, z, hxU,
    inferInstance, finitePresentation_of_finiteType _, hiso2, hz,
    isClosedImmersion_morphismRestrict_imageι_comp_snd f _ U _ _ _ hj hcomm,
    preimage_imageι_comp_fst_eq_preimage_imageι_comp_snd f _ U _ _ _ hj hcomm⟩

/-- **Chow's lemma in the derived category, over a Noetherian base.** Let `A` be a Noetherian
ring and let `f : X ⟶ Spec A` be separated, locally of finite type and quasi-compact. For every
point `x` of `X` there are an open `U ∋ x`, an `m`, an open `V` of `ℙᵐ_A`, a closed subscheme
`iZ : Z ⟶ X ×_A ℙᵐ_A`, a point `z` of `Z` and an object `E` of `D(𝒪_{X ×_A ℙᵐ_A})` such that,
writing `b` and `c` for the two projections of `Z`:

* `iZ` is a closed immersion of finite presentation;
* `b` is an isomorphism over `U`, and `b z = x`;
* `c` is a closed immersion over `V`;
* `b ⁻¹ᵁ U = c ⁻¹ᵁ V`;
* `E` is isomorphic to the direct image `(b, c)_* 𝒪_Z` placed in degree zero;
* `E` is pseudo-coherent and its cohomology is supported on the image of `Z`.

This is the Noetherian case of [Stacks, Tag 0CSJ]. -/
theorem exists_chowDatum_isPseudoCoherent_of_isNoetherian {A : Type u} [CommRing A]
    [IsNoetherianRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (x : X) :
    ∃ (U : X.Opens) (m : ℕ) (V : (projectiveSpaceOver m (Spec (.of A))).Opens) (Z : Scheme.{u})
      (iZ : Z ⟶ pullback f (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))) (z : Z)
      (E : DerivedCategory
        (pullback f (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))).Modules),
      x ∈ U ∧ IsClosedImmersion iZ ∧ FinitePresentation iZ ∧
        IsIso ((iZ ≫ pullback.fst f
          (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))) ∣_ U) ∧
        (iZ ≫ pullback.fst f
          (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))).base z = x ∧
        IsClosedImmersion ((iZ ≫ pullback.snd f
          (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))) ∣_ V) ∧
        (iZ ≫ pullback.fst f
            (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))) ⁻¹ᵁ U =
          (iZ ≫ pullback.snd f
            (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))) ⁻¹ᵁ V ∧
        Nonempty (E ≅ (DerivedCategory.singleFunctor
            (pullback f (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))).Modules 0).obj
          ((Scheme.Modules.pushforward iZ).obj (SheafOfModules.unit Z.ringCatSheaf))) ∧
        RingedSpace.IsPseudoCoherent (X := (pullback f
          (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))).toRingedSpace) E ∧
        CohomologySupportedOn (pullback f
            (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))).ringCatSheaf
          (Set.range iZ.base) E := by
  obtain ⟨U, m, V, Z, iZ, z, hxU, hiZ, hfp, hisoU, hz, hVcl, hpre⟩ :=
    exists_chowDatum_of_isNoetherian f x
  have := hiZ
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have : IsLocallyNoetherian
      (pullback f (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst f (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A)))
  exact ⟨U, m, V, Z, iZ, z, (DerivedCategory.singleFunctor
      (pullback f (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))).Modules 0).obj
      ((Scheme.Modules.pushforward iZ).obj (SheafOfModules.unit Z.ringCatSheaf)),
    hxU, hiZ, hfp, hisoU, hz, hVcl, hpre, ⟨Iso.refl _⟩,
    isPseudoCoherent_singleFunctor_pushforward_unit_of_isClosedImmersion iZ,
    cohomologySupportedOn_singleFunctor_pushforward_unit iZ⟩

end AlgebraicGeometry

end
