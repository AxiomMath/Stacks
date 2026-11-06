module

public import StacksFrontier.Algebra.Homology.RelativePullbackMap
public import
  StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianDerivedBaseChangeCriteria
public import
  StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianDerivedBaseChangeIdentity
public import StacksFrontier.Homology.DerivedIndexing.Composite
public import StacksFrontier.Homology.DerivedIndexing.Extend

/-!
# The degreewise base change map, from the derived one

Let `G ⊣ G_*` and `G' ⊣ G'_*` be adjunctions between abelian categories with `G` and `G'`
exact, let `F` and `F'` be additive and let `e : G'_* ⋙ F ≅ F' ⋙ G_*`. The mate
`τ : F ⋙ G ⟶ G' ⋙ F'` descends to bounded below derived categories as
`Stacks.Cohomology.BaseChange.derived`.

In each degree `n` the map `Stacks.Cohomology.RelativePullback.map` attached to the unit
`E ⟶ G'_* G' E` has an adjoint `G (Rⁿ F E) ⟶ Rⁿ F' (G' E)`, computed on injective resolutions.
This file shows that it is invertible as soon as the descended comparison is invertible at `E`
placed in degree zero.

## Main results

* `Stacks.Cohomology.RelativePullback.adjointHom_complexMap`: the adjoint of the morphism of
  complexes `F I ⟶ G_*(F' J)` is the mate applied to `I` followed by `F'` of the adjoint of the
  comparison.
* `Stacks.Cohomology.RelativePullback.isIso_homologyMap_of_isIso_derived_app`: if the descended
  comparison is invertible at `E` placed in degree zero, then the mate applied to an injective
  resolution of `E`, followed by `F'` of a quasi-isomorphism to an injective resolution of
  `G' E`, is invertible on cohomology.
* `Stacks.Cohomology.RelativePullback.isIso_homEquiv_symm_map_unit`: consequently the degreewise
  map `G (Rⁿ F E) ⟶ Rⁿ F' (G' E)` is invertible in every degree.

## References

* [Stacks Project, Tag 02N7](https://stacks.math.columbia.edu/tag/02N7)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits HomologicalComplex

namespace Stacks.Cohomology.RelativePullback

open RightDerivedCoEdge HomologyAdjunction Stacks.Cohomology.BaseChange

attribute [local instance] HasDerivedCategory.standard

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C) {Gp : D ⥤ B} {G'p : C ⥤ A}
  (adj : G ⊣ Gp) (adj' : G' ⊣ G'p)
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive] [Gp.Additive] [G'p.Additive]
  [HasInjectiveResolutions A] [HasInjectiveResolutions C] [PreservesFiniteLimits Gp]
  (e : G'p ⋙ F ≅ F' ⋙ Gp)

/-- The adjoint of the morphism of complexes `F I ⟶ G_*(F' J)` attached to a comparison
`c : I ⟶ G'_* J` is the mate applied to `I`, followed by `F'` of the adjoint of `c`. -/
lemma adjointHom_complexMap {I : CochainComplex A ℕ}
    {J : CochainComplex C ℕ} (χ : I ⟶ (G'p.mapHomologicalComplex _).obj J) :
    adjointHom adj (complexMap F F' G'p Gp e χ) =
      (NatTrans.mapHomologicalComplex (mate adj adj' F F' e) _).app I ≫
        (F'.mapHomologicalComplex _).map (adjointHom adj' χ) := by
  ext k
  simp only [adjointHom_f, comp_f, complexMap_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, mate_app, Adjunction.homEquiv_counit, assoc,
    G.map_comp, F'.map_comp]
  symm
  have h₁ := adj.counit.naturality (F'.map (G'.map (χ.f k)) ≫ F'.map (adj'.counit.app (J.X k)))
  simp only [Functor.comp_map, Functor.id_map, Functor.id_obj] at h₁
  rw [← h₁]
  have h₂ := e.hom.naturality (G'.map (χ.f k) ≫ adj'.counit.app (J.X k))
  simp only [Functor.comp_map, Functor.id_obj] at h₂
  rw [← G.map_comp_assoc, ← G.map_comp_assoc, ← F'.map_comp, assoc, ← h₂,
    ← assoc, ← F.map_comp]
  have h₃ : adj'.unit.app (I.X k) ≫ G'p.map (G'.map (χ.f k) ≫ adj'.counit.app (J.X k)) =
      χ.f k := by
    have := (adj'.homEquiv (I.X k) (J.X k)).apply_symm_apply (χ.f k)
    rwa [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit] at this
  rw [h₃, G.map_comp_assoc]
  rfl

section Resolution

variable [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] [G'p.PreservesInjectiveObjects]

/-- The adjoint `G' I ⟶ J` of the comparison of chosen injective resolutions extending the unit
`E ⟶ G'_* G' E`. -/
abbrev resolutionMap (E : A) :
    (G'.mapHomologicalComplex _).obj (injectiveResolution E).cocomplex ⟶
      (injectiveResolution (G'.obj E)).cocomplex :=
  adjointHom adj' (comparison G'p (adj'.unit.app E))

omit [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] in
/-- In degree `0`, `G'` of the augmentation `E ⟶ I⁰` followed by `resolutionMap` is the
augmentation `G' E ⟶ J⁰` of the chosen injective resolution of `G' E`. -/
lemma aug_comp_resolutionMap_f_zero (E : A) :
    G'.map (aug (injectiveResolution E)) ≫ (resolutionMap G' adj' E).f 0 =
      aug (injectiveResolution (G'.obj E)) := by
  rw [adjointHom_f, ← Adjunction.homEquiv_naturality_left_symm,
    aug_comp_comparison_f_zero, Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_counit, adj'.left_triangle_components, id_comp]

/-- The adjoint comparison `resolutionMap` is a quasi-isomorphism. -/
instance quasiIso_resolutionMap (E : A) : QuasiIso (resolutionMap G' adj' E) := by
  have : G'.PreservesHomology := Functor.preservesHomologyOfExact G'
  have h : ((HomologicalComplex.singleMapHomologicalComplex G' (ComplexShape.up ℕ) 0).inv.app E ≫
      (G'.mapHomologicalComplex _).map (injectiveResolution E).ι ≫ resolutionMap G' adj' E :
        (HomologicalComplex.single C (ComplexShape.up ℕ) 0).obj (G'.obj E) ⟶ _) =
      (injectiveResolution (G'.obj E)).ι := by
    refine HomologicalComplex.from_single_hom_ext ?_
    rw [comp_f, comp_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
    simpa [aug] using aug_comp_resolutionMap_f_zero G' adj' E
  have : QuasiIso ((G'.mapHomologicalComplex _).map (injectiveResolution E).ι ≫
      resolutionMap G' adj' E) :=
    (quasiIso_iff_comp_left
      ((HomologicalComplex.singleMapHomologicalComplex G' (ComplexShape.up ℕ) 0).inv.app E) _).1
      (by rw [h]; infer_instance)
  exact quasiIso_of_comp_left ((G'.mapHomologicalComplex _).map (injectiveResolution E).ι) _

end Resolution

section Derived

variable [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]

omit [HasInjectiveResolutions A] [HasInjectiveResolutions C] in
/-- A morphism of bounded below complexes which becomes invertible in the bounded below derived
category induces isomorphisms on all cohomology objects. -/
lemma isIso_homologyMap_of_isIso_Qh_map {K L : CochainComplex D ℤ}
    (hK : HomotopyCategory.plus D ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj K))
    (hL : HomotopyCategory.plus D ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj L))
    (ψ : K ⟶ L)
    (h : IsIso (DerivedCategory.Plus.Qh.map (ObjectProperty.homMk
      ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map ψ) :
        (⟨_, hK⟩ : HomotopyCategory.Plus D) ⟶ ⟨_, hL⟩))) (n : ℤ) :
    IsIso (homologyMap ψ n) := by
  let g : (⟨_, hK⟩ : HomotopyCategory.Plus D) ⟶ ⟨_, hL⟩ :=
    ObjectProperty.homMk ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map ψ)
  exact (NatIso.isIso_map_iff (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) n)
    ψ).1 ((NatIso.isIso_map_iff (Stacks.DerivedIndexing.plusHomologyIso (D := D) n) g).1
      (inferInstanceAs (IsIso ((DerivedCategory.Plus.homologyFunctor D n).map
        (DerivedCategory.Plus.Qh.map g)))))

omit [HasInjectiveResolutions A] [HasInjectiveResolutions C] [EnoughInjectives A]
  [EnoughInjectives B] [EnoughInjectives C] in
/-- `Stacks.DerivedIndexing.mapExtendXIso` for a composite of two additive functors. -/
private lemma mapExtendXIso_comp_hom {ι : Type*} {c : ComplexShape ι} (F₁ : A ⥤ C) (F₂ : C ⥤ D)
    [F₁.Additive] [F₂.Additive] (K : HomologicalComplex A c) (o : Option ι) :
    (Stacks.DerivedIndexing.mapExtendXIso (F₁ ⋙ F₂) K o).hom =
      (Stacks.DerivedIndexing.mapExtendXIso F₂ ((F₁.mapHomologicalComplex c).obj K) o).hom ≫
        F₂.map (Stacks.DerivedIndexing.mapExtendXIso F₁ K o).hom := by
  cases o with
  | none => exact (isZero_zero _).eq_of_src _ _
  | some a =>
    show 𝟙 _ = 𝟙 _ ≫ F₂.map (𝟙 _)
    rw [F₂.map_id, id_comp]

omit [HasInjectiveResolutions A] [HasInjectiveResolutions C] [EnoughInjectives A]
  [EnoughInjectives B] [EnoughInjectives C] in
/-- `Stacks.DerivedIndexing.mapExtendIso` for a composite of two additive functors. -/
lemma mapExtendIso_comp_hom {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (F₁ : A ⥤ C) (F₂ : C ⥤ D) [F₁.Additive] [F₂.Additive]
    (K : HomologicalComplex A c) :
    (Stacks.DerivedIndexing.mapExtendIso (F₁ ⋙ F₂) e K).hom =
      (Stacks.DerivedIndexing.mapExtendIso F₂ e ((F₁.mapHomologicalComplex c).obj K)).hom ≫
        (F₂.mapHomologicalComplex c').map (Stacks.DerivedIndexing.mapExtendIso F₁ e K).hom := by
  ext i'
  exact mapExtendXIso_comp_hom F₁ F₂ K (e.r i')

omit [HasInjectiveResolutions A] [HasInjectiveResolutions C] in
/-- Let `τ : F ⋙ G ⟶ G' ⋙ F'` with `G'` exact, let `I` be the chosen injective resolution of
`E`, and let `r : G' I ⟶ J` be a quasi-isomorphism to the chosen injective resolution of `G' E`. If
the descent `Stacks.Cohomology.BaseChange.derived` of `τ` is invertible at `E` placed in degree
zero, then `τ` applied to `I` followed by `F' r` induces isomorphisms on all cohomology objects. -/
theorem isIso_homologyMap_of_isIso_derived_app (τ : F ⋙ G ⟶ G' ⋙ F')
    (eG : G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus)
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] (E : A)
    (r : (G'.mapHomologicalComplex _).obj (injectiveResolution E).cocomplex ⟶
      (injectiveResolution (G'.obj E)).cocomplex) [QuasiIso r]
    (h : IsIso ((derived F F' G G' τ eG).app ((DerivedCategory.Plus.singleFunctor A 0).obj E)))
    (n : ℕ) :
    IsIso (homologyMap ((NatTrans.mapHomologicalComplex τ _).app (injectiveResolution E).cocomplex ≫
      (F'.mapHomologicalComplex _).map r) n) := by
  let emb := ComplexShape.embeddingUpNat
  let I := (injectiveResolution E).cocomplex
  let J := (injectiveResolution (G'.obj E)).cocomplex
  let p := (Stacks.DerivedIndexing.mapExtendIso G' emb I).inv ≫ extendMap r emb
  let φ := (NatTrans.mapHomologicalComplex τ _).app I ≫ (F'.mapHomologicalComplex _).map r
  have h₁ : IsIso ((derived F F' G G' τ eG).app
      (DerivedCategory.Plus.Qh.obj (Stacks.DerivedIndexing.resPlus.obj E))) :=
    (NatTrans.isIso_app_iff_of_iso _ (Stacks.DerivedIndexing.singleIsoResPlusQh.app E)).1 h
  have : IsIso G'.rightDerivedFunctorPlusUnith := exactUnit_isIso G'
  rw [isIso_derived_app_Qh_iff F F' G G' τ eG _ inferInstance inferInstance] at h₁
  let q : G'.mapHomotopyCategoryPlus.obj (Stacks.DerivedIndexing.resPlus.obj E) ⟶
      Stacks.DerivedIndexing.resPlus.obj (G'.obj E) :=
    ObjectProperty.homMk ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map p)
  have hq : IsIso (DerivedCategory.Plus.Qh.map q) := by
    refine Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C) _ ?_
    have := (quasiIso_extendMap_iff r emb).2 inferInstance
    have : QuasiIso p := quasiIso_comp _ _
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2
      ((HomologicalComplex.mem_quasiIso_iff p).2 this)
  have nat : F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj
        (Stacks.DerivedIndexing.resPlus.obj E)) ≫
        F'.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map q) =
      DerivedCategory.Plus.Qh.map (F'.mapHomotopyCategoryPlus.map q) ≫
        F'.rightDerivedFunctorPlusUnith.app (Stacks.DerivedIndexing.resPlus.obj (G'.obj E)) :=
    (F'.rightDerivedFunctorPlusUnith.naturality q).symm
  have h₂ : IsIso (DerivedCategory.Plus.Qh.map
      ((mapPlus τ).app (Stacks.DerivedIndexing.resPlus.obj E) ≫
      F'.mapHomotopyCategoryPlus.map q)) := by
    have e₃ : DerivedCategory.Plus.Qh.map ((mapPlus τ).app (Stacks.DerivedIndexing.resPlus.obj E) ≫
        F'.mapHomotopyCategoryPlus.map q) ≫
          F'.rightDerivedFunctorPlusUnith.app (Stacks.DerivedIndexing.resPlus.obj (G'.obj E)) =
        (DerivedCategory.Plus.Qh.map ((mapPlus τ).app (Stacks.DerivedIndexing.resPlus.obj E)) ≫
          F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj
            (Stacks.DerivedIndexing.resPlus.obj E))) ≫
          F'.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map q) := by
      refine (congrArg (· ≫ F'.rightDerivedFunctorPlusUnith.app
        (Stacks.DerivedIndexing.resPlus.obj (G'.obj E)))
          (DerivedCategory.Plus.Qh.map_comp _ _)).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (DerivedCategory.Plus.Qh.map ((mapPlus τ).app
        (Stacks.DerivedIndexing.resPlus.obj E)) ≫ ·) nat.symm).trans ?_
      exact (Category.assoc _ _ _).symm
    have h₃ : IsIso (DerivedCategory.Plus.Qh.map ((mapPlus τ).app
        (Stacks.DerivedIndexing.resPlus.obj E) ≫ F'.mapHomotopyCategoryPlus.map q) ≫
          F'.rightDerivedFunctorPlusUnith.app (Stacks.DerivedIndexing.resPlus.obj (G'.obj E))) := by
      rw [e₃]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (F'.rightDerivedFunctorPlusUnith.app (Stacks.DerivedIndexing.resPlus.obj (G'.obj E)))
  let ψ := (NatTrans.mapHomologicalComplex τ _).app (I.extend emb) ≫
    (F'.mapHomologicalComplex _).map p
  have h₄ : IsIso (homologyMap ψ (n : ℤ)) :=
    isIso_homologyMap_of_isIso_Qh_map _ _ ψ h₂ n
  have hψ : ψ = (Stacks.DerivedIndexing.mapExtendIso (F ⋙ G) emb I).inv ≫
      extendMap φ emb ≫
      (Stacks.DerivedIndexing.mapExtendIso F' emb J).hom := by
    have h₅ : (Stacks.DerivedIndexing.mapExtendIso (F ⋙ G) emb I).hom ≫
        (NatTrans.mapHomologicalComplex τ _).app (I.extend emb) =
        extendMap ((NatTrans.mapHomologicalComplex τ _).app I) emb ≫
          (Stacks.DerivedIndexing.mapExtendIso (G' ⋙ F') emb I).hom :=
      (Stacks.DerivedIndexing.mapExtendIso_hom_natTrans τ emb I).symm
    have h₆ :
        (Stacks.DerivedIndexing.mapExtendIso F' emb ((G'.mapHomologicalComplex _).obj I)).hom ≫
        (F'.mapHomologicalComplex _).map (extendMap r emb) =
        extendMap ((F'.mapHomologicalComplex _).map r) emb ≫
          (Stacks.DerivedIndexing.mapExtendIso F' emb J).hom :=
      ((Stacks.DerivedIndexing.mapExtendNatIso F' emb).hom.naturality r).symm
    have h₇ : (Stacks.DerivedIndexing.mapExtendIso (G' ⋙ F') emb I).hom ≫
        (F'.mapHomologicalComplex _).map (Stacks.DerivedIndexing.mapExtendIso G' emb I).inv =
        (Stacks.DerivedIndexing.mapExtendIso F' emb ((G'.mapHomologicalComplex _).obj I)).hom := by
      rw [mapExtendIso_comp_hom emb G' F' I, assoc, ← CategoryTheory.Functor.map_comp,
        Iso.hom_inv_id, CategoryTheory.Functor.map_id, comp_id]
    rw [Iso.eq_inv_comp, extendMap_comp, assoc, ← h₆, ← reassoc_of% h₇, ← reassoc_of% h₅]
    simp only [ψ, p, CategoryTheory.Functor.map_comp]
  rw [hψ, homologyMap_comp, homologyMap_comp, isIso_comp_left_iff, isIso_comp_right_iff] at h₄
  exact (quasiIsoAt_iff_isIso_homologyMap _ _).1 ((quasiIsoAt_extendMap_iff φ emb
      (j := n) (j' := (n : ℤ)) rfl).1 ((quasiIsoAt_iff_isIso_homologyMap _ _).2 h₄))

end Derived

section DerivedUnit

variable [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]

/-- For `G ⊣ G_*` and `G' ⊣ G'_*` with `G` and `G'` exact and `e : G'_* ⋙ F ≅ F' ⋙ G_*`, the
adjoint `G (Rⁿ F E) ⟶ Rⁿ F' (G' E)` of `Stacks.Cohomology.RelativePullback.map` at the unit
`E ⟶ G'_* G' E` is invertible as soon as the descent of the mate to bounded below derived
categories is invertible at `E` placed in degree zero. -/
theorem isIso_homEquiv_symm_map_unit [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] [G'p.PreservesInjectiveObjects]
    (eG : G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus) (E : A)
    (h : IsIso ((derived F F' G G' (mate adj adj' F F' e) eG).app
      ((DerivedCategory.Plus.singleFunctor A 0).obj E))) (n : ℕ) :
    IsIso ((adj.homEquiv _ _).symm (map F F' G'p Gp e (adj'.unit.app E) n)) := by
  rw [map, homEquiv_symm_mapOf F F' G'p Gp adj e, adjointHom_complexMap F F' G G' adj adj' e]
  have := isIso_homologyMap_of_isIso_derived_app F F' G G' (mate adj adj' F F' e) eG E
    (resolutionMap G' adj' E) h n
  infer_instance

end DerivedUnit

end Stacks.Cohomology.RelativePullback

end
