module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionThickening

/-!
# `h_𝔛` as a colimit of schemes along thickenings

Let `𝔛` be a formal scheme in the sense of McQuillan. **Stacks 0AIV** concludes that the functor of
points `h_𝔛` is a colimit, as in Stacks 0AIU, of a directed system of schemes along thickenings
exactly when `𝔛` has a fundamental system of weak ideals of definition. This file defines the
colimit condition and proves the direction from a fundamental system to a colimit: the system of
schemes is `ℐ ↦ (𝔛, 𝒪_𝔛/ℐ)` and the comparison map from the colimit to `h_𝔛` is Zariski locally
bijective.

## Main definitions

* `McQuillanFormalScheme.IsColimitOfThickenings`: `h_𝔛` is a colimit of schemes along
  thickenings.

## Main results

* `LocallyTopologicallyRingedSpace.IdealSheaf.isColimitOfThickenings_of_isFundamentalSystem`:
  a fundamental system of weak ideals of definition presents `h_𝔛` as a colimit.

## Implementation notes

The colimit is taken in the category of presheaves of sets on all schemes, and the condition is
that the comparison map `colim h_{X_λ} → h_𝔛` is locally bijective for the Zariski topology, that
is, an isomorphism after sheafification; this is the convention of
`StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsColimit` for the colimit formula of
Stacks 0AIE. No sheafification is formed, which would not exist at this size.

## References

* [Stacks Project, Tag 0AIV](https://stacks.math.columbia.edu/tag/0AIV)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- **The functor of points of a McQuillan formal scheme is a colimit of schemes along
thickenings, Zariski form**: there are a nonempty directed preorder `Λ`, a system `λ ↦ X_λ` of
schemes whose transition morphisms are thickenings, and morphisms `h_{X_λ} → h_𝔛` compatible with
the transitions, such that the comparison map `colim h_{X_λ} → h_𝔛` is bijective Zariski locally,
i.e. an isomorphism after Zariski sheafification. This is an auxiliary form: the colimit of Stacks
0AIU, taken in fppf sheaves, is `McQuillanFormalScheme.IsFppfColimitOfThickenings`, and the two
are equivalent by `McQuillanFormalScheme.isFppfColimitOfThickenings_iff`
(`StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionColimitFppf`). -/
def McQuillanFormalScheme.IsColimitOfThickenings (𝔛 : McQuillanFormalScheme.{u}) : Prop :=
  ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
    (D : Λ ⥤ Scheme.{u}) (_ : ∀ ⦃i j : Λ⦄ (g : i ⟶ j), Stacks.Thickenings.IsThickening (D.map g))
    (ι : D ⋙ yoneda ⟶ (Functor.const Λ).obj (mcQuillanFormalSchemePoints 𝔛)),
    Presheaf.IsLocallyInjective Scheme.zariskiTopology
        (colimit.desc (D ⋙ yoneda) (Cocone.mk _ ι)) ∧
      Presheaf.IsLocallySurjective Scheme.zariskiTopology
        (colimit.desc (D ⋙ yoneda) (Cocone.mk _ ι))

namespace LocallyTopologicallyRingedSpace.IdealSheaf

section System

variable {𝔛 : McQuillanFormalScheme.{u}} (h𝔛 : IsMcQuillanFormalScheme 𝔛.obj)
  (𝒮 : Set (IdealSheaf 𝔛.obj))
  (hI : ∀ I ∈ 𝒮, I.IsWeakIdealOfDefinitionOn (IsWeakAffineFormalOpen 𝔛.obj))
  (hC : ∀ I ∈ 𝒮, I.IsCutOutOn (IsWeakAffineFormalOpen 𝔛.obj))

/-- The members of a family of ideal sheaves, ordered by reverse inclusion: a smaller ideal sheaf
cuts out a larger scheme. -/
def SystemIndex : Type u := {I : IdealSheaf 𝔛.obj // I ∈ 𝒮}

/-- Members of the system are ordered by reverse inclusion of their sections over every open. -/
instance : Preorder (SystemIndex 𝒮) where
  le I J := ∀ V, J.1.ideal V ≤ I.1.ideal V
  le_refl _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ V := (h₂ V).trans (h₁ V)

variable {𝒮}

/-- The scheme `(𝔛, 𝒪_𝔛/ℐ)` of a member of the system. -/
noncomputable abbrev systemScheme (I : SystemIndex 𝒮) : Scheme.{u} :=
  I.1.quotientScheme (hI I.1 I.2) (hC I.1 I.2)

/-- The obvious morphism `(𝔛, 𝒪_𝔛/ℐ) → 𝔛` of a member of the system. -/
noncomputable abbrev systemPoint (I : SystemIndex 𝒮) :
    schemeToLTRSObj (systemScheme hI hC I) ⟶ 𝔛.obj :=
  I.1.quotientPoint (hI I.1 I.2) (hC I.1 I.2) h𝔛

/-- For `𝒥 ⊆ ℐ`, the ideal sheaf `𝒥` kills the morphism `(𝔛, 𝒪_𝔛/ℐ) → 𝔛`. -/
theorem kills_systemPoint_of_le {I J : SystemIndex 𝒮} (h : I ≤ J) :
    J.1.Kills (systemPoint h𝔛 hI hC I) :=
  fun V => (h V).trans (I.1.kills_quotientPoint (hI I.1 I.2) (hC I.1 I.2) h𝔛 V)

/-- The transition morphism `(𝔛, 𝒪_𝔛/ℐ) → (𝔛, 𝒪_𝔛/𝒥)` for `𝒥 ⊆ ℐ`. -/
noncomputable def systemTransition {I J : SystemIndex 𝒮} (h : I ≤ J) :
    systemScheme hI hC I ⟶ systemScheme hI hC J :=
  (J.1.existsUnique_quotientPoint_factor (hI J.1 J.2) (hC J.1 J.2) h𝔛 _
    (kills_systemPoint_of_le h𝔛 hI hC h)).choose

/-- The transition morphism `(𝔛, 𝒪_𝔛/ℐ) → (𝔛, 𝒪_𝔛/𝒥)` composed with `(𝔛, 𝒪_𝔛/𝒥) → 𝔛` is
`(𝔛, 𝒪_𝔛/ℐ) → 𝔛`. -/
theorem systemTransition_comp {I J : SystemIndex 𝒮} (h : I ≤ J) :
    schemeToLTRS.map (systemTransition h𝔛 hI hC h) ≫ systemPoint h𝔛 hI hC J =
      systemPoint h𝔛 hI hC I :=
  (J.1.existsUnique_quotientPoint_factor (hI J.1 J.2) (hC J.1 J.2) h𝔛 _
    (kills_systemPoint_of_le h𝔛 hI hC h)).choose_spec.1

/-- Morphisms into a member of the system are determined by their composites with its point. -/
theorem systemScheme_hom_ext {T : Scheme.{u}} {J : SystemIndex 𝒮} {a b : T ⟶ systemScheme hI hC J}
    (h : schemeToLTRS.map a ≫ systemPoint h𝔛 hI hC J =
      schemeToLTRS.map b ≫ systemPoint h𝔛 hI hC J) : a = b := by
  obtain ⟨c, -, huniq⟩ := J.1.existsUnique_quotientPoint_factor (hI J.1 J.2) (hC J.1 J.2) h𝔛 _
    ((J.1.kills_quotientPoint (hI J.1 J.2) (hC J.1 J.2) h𝔛).comp _)
  exact (huniq a h).trans (huniq b rfl).symm

/-- Composing with a transition morphism does not change the composite with the point. -/
private theorem map_comp_systemTransition_comp_systemPoint {T : Scheme.{u}} {I J : SystemIndex 𝒮}
    (h : I ≤ J) (a : T ⟶ systemScheme hI hC I) :
    schemeToLTRS.map (a ≫ systemTransition h𝔛 hI hC h) ≫ systemPoint h𝔛 hI hC J =
      schemeToLTRS.map a ≫ systemPoint h𝔛 hI hC I := by
  rw [schemeToLTRS_map_comp_assoc, systemTransition_comp]

/-- The directed system `ℐ ↦ (𝔛, 𝒪_𝔛/ℐ)`. -/
noncomputable def systemDiagram : SystemIndex 𝒮 ⥤ Scheme.{u} where
  obj I := systemScheme hI hC I
  map g := systemTransition h𝔛 hI hC (leOfHom g)
  map_id I := systemScheme_hom_ext h𝔛 hI hC ((systemTransition_comp h𝔛 hI hC _).trans
    ((congrArg (· ≫ systemPoint h𝔛 hI hC I) (schemeToLTRS.map_id _)).trans
      (Category.id_comp _)).symm)
  map_comp _ _ := systemScheme_hom_ext h𝔛 hI hC ((systemTransition_comp h𝔛 hI hC _).trans (by
    rw [schemeToLTRS_map_comp_assoc, systemTransition_comp, systemTransition_comp]))

/-- **The transition morphisms of the system are thickenings**: `(𝔛, 𝒪_𝔛/ℐ) → (𝔛, 𝒪_𝔛/𝒥)` is, up to
isomorphism, the base change of `h_{(𝔛, 𝒪_𝔛/ℐ)} → h_𝔛` along the point `(𝔛, 𝒪_𝔛/𝒥) → 𝔛`, which is
a thickening by `isThickening_pullbackProj`. -/
theorem isThickening_systemTransition {I J : SystemIndex 𝒮} (h : I ≤ J) :
    Stacks.Thickenings.IsThickening (systemTransition h𝔛 hI hC h) := by
  set φ := systemPoint h𝔛 hI hC J
  have hτ : I.1.Kills (schemeToLTRS.map (systemTransition h𝔛 hI hC h) ≫ φ) := by
    rw [systemTransition_comp]
    exact I.1.kills_quotientPoint (hI I.1 I.2) (hC I.1 I.2) h𝔛
  obtain ⟨m, hm, -⟩ := existsUnique_pullbackProj_factor I.1 (hI I.1 I.2) (hC I.1 I.2) h𝔛 _ hτ
  obtain ⟨n, hn, -⟩ := I.1.existsUnique_quotientPoint_factor (hI I.1 I.2) (hC I.1 I.2) h𝔛
    (schemeToLTRS.map (pullbackProj I.1 (hI I.1 I.2) (hC I.1 I.2) h𝔛 (φ := φ)) ≫ φ)
    (kills_pullbackProj I.1 (hI I.1 I.2) (hC I.1 I.2) h𝔛)
  have hnτ : n ≫ systemTransition h𝔛 hI hC h =
      pullbackProj I.1 (hI I.1 I.2) (hC I.1 I.2) h𝔛 (φ := φ) :=
    systemScheme_hom_ext h𝔛 hI hC
      ((map_comp_systemTransition_comp_systemPoint h𝔛 hI hC h n).trans hn)
  have := mono_pullbackProj I.1 (hI I.1 I.2) (hC I.1 I.2) h𝔛 (φ := φ)
  have : IsIso m := ⟨n, systemScheme_hom_ext h𝔛 hI hC (by
      rw [schemeToLTRS_map_comp_assoc, hn]
      erw [← schemeToLTRS_map_comp_assoc, hm]
      rw [systemTransition_comp, schemeToLTRS.map_id]
      exact (Category.id_comp _).symm),
    (cancel_mono (pullbackProj I.1 (hI I.1 I.2) (hC I.1 I.2) h𝔛 (φ := φ))).mp (by
      rw [Category.assoc, hm, hnτ, Category.id_comp])⟩
  rw [← hm]
  exact Stacks.Thickenings.isThickening_comp (Stacks.Thickenings.isThickening_of_isIso m)
    (isThickening_pullbackProj I.1 (hI I.1 I.2) (hC I.1 I.2) h𝔛)

/-- The morphisms `h_{(𝔛, 𝒪_𝔛/ℐ)} → h_𝔛` are compatible with the transitions. -/
theorem yoneda_map_systemTransition_comp {I J : SystemIndex 𝒮} (h : I ≤ J) :
    yoneda.map (systemTransition h𝔛 hI hC h) ≫
        J.1.quotientMorphism (hI J.1 J.2) (hC J.1 J.2) h𝔛 =
      I.1.quotientMorphism (hI I.1 I.2) (hC I.1 I.2) h𝔛 := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  exact InducedCategory.hom_ext ((J.1.quotientMorphism_app_hom (hI J.1 J.2) (hC J.1 J.2) h𝔛
    _).trans (systemTransition_comp h𝔛 hI hC h))

/-- The morphisms `h_{(𝔛, 𝒪_𝔛/ℐ)} → h_𝔛`, as a cocone over the system. -/
noncomputable def systemCocone :
    systemDiagram h𝔛 hI hC ⋙ yoneda ⟶
      (Functor.const (SystemIndex 𝒮)).obj (mcQuillanFormalSchemePoints 𝔛) where
  app I := I.1.quotientMorphism (hI I.1 I.2) (hC I.1 I.2) h𝔛
  naturality _ _ g := by
    simp only [Functor.comp_map, Functor.const_obj_map]
    exact yoneda_map_systemTransition_comp h𝔛 hI hC (leOfHom g)

variable (𝒮) in
/-- The comparison map `colim h_{(𝔛, 𝒪_𝔛/ℐ)} → h_𝔛`. -/
noncomputable abbrev systemComparison :=
  colimit.desc (systemDiagram h𝔛 hI hC ⋙ yoneda) (Cocone.mk _ (systemCocone h𝔛 hI hC))

/-- Every element of the colimit over a scheme comes from one of the stages. -/
theorem exists_systemColimit_eq {T : Scheme.{u}}
    (x : (colimit (systemDiagram h𝔛 hI hC ⋙ yoneda)).obj (op T)) :
    ∃ (I : SystemIndex 𝒮) (a : T ⟶ systemScheme hI hC I),
      (colimit.ι (systemDiagram h𝔛 hI hC ⋙ yoneda) I).app (op T) a = x :=
  Types.jointly_surjective_of_isColimit (isColimitOfPreserves
    ((evaluation _ (Type u)).obj (op T)) (colimit.isColimit (systemDiagram h𝔛 hI hC ⋙ yoneda))) x

/-- The comparison map sends the image of `a : T ⟶ (𝔛, 𝒪_𝔛/ℐ)` in the colimit to the composite
of `a` with `(𝔛, 𝒪_𝔛/ℐ) → 𝔛`. -/
theorem systemComparison_app_ι {T : Scheme.{u}} (I : SystemIndex 𝒮)
    (a : T ⟶ systemScheme hI hC I) :
    (systemComparison h𝔛 𝒮 hI hC).app (op T)
        ((colimit.ι (systemDiagram h𝔛 hI hC ⋙ yoneda) I).app (op T) a) =
      (I.1.quotientMorphism (hI I.1 I.2) (hC I.1 I.2) h𝔛).app (op T) a :=
  congrArg (fun η => η.app (op T) a) (colimit.ι_desc (Cocone.mk _ (systemCocone h𝔛 hI hC)) I)

/-- For a directed family, the comparison map from the colimit is injective over every scheme. -/
theorem injective_systemComparison_app
    (hdir : ∀ I ∈ 𝒮, ∀ J ∈ 𝒮, ∃ K ∈ 𝒮, ∀ W : Opens 𝔛.obj,
      K.ideal W ≤ I.ideal W ∧ K.ideal W ≤ J.ideal W) (T : Scheme.{u}) :
    Function.Injective ((systemComparison h𝔛 𝒮 hI hC).app (op T)) := by
  intro x y hxy
  obtain ⟨I, a, rfl⟩ := exists_systemColimit_eq h𝔛 hI hC x
  obtain ⟨J, b, rfl⟩ := exists_systemColimit_eq h𝔛 hI hC y
  rw [systemComparison_app_ι, systemComparison_app_ι] at hxy
  have hab : schemeToLTRS.map a ≫ systemPoint h𝔛 hI hC I =
      schemeToLTRS.map b ≫ systemPoint h𝔛 hI hC J := by
    have := congrArg (fun z => z.hom) hxy
    simp only at this
    rwa [quotientMorphism_app_hom, quotientMorphism_app_hom] at this
  obtain ⟨K, hK, hKle⟩ := hdir I.1 I.2 J.1 J.2
  have hIK : I ≤ ⟨K, hK⟩ := fun W => (hKle W).1
  have hJK : J ≤ ⟨K, hK⟩ := fun W => (hKle W).2
  have hx := congrArg (fun η => η.app (op T) a)
    (colimit.w (systemDiagram h𝔛 hI hC ⋙ yoneda) (homOfLE hIK))
  have hy := congrArg (fun η => η.app (op T) b)
    (colimit.w (systemDiagram h𝔛 hI hC ⋙ yoneda) (homOfLE hJK))
  refine hx.symm.trans (Eq.trans ?_ hy)
  refine congrArg ((colimit.ι (systemDiagram h𝔛 hI hC ⋙ yoneda) ⟨K, hK⟩).app (op T))
    (show a ≫ systemTransition h𝔛 hI hC hIK = b ≫ systemTransition h𝔛 hI hC hJK from ?_)
  exact systemScheme_hom_ext h𝔛 hI hC
    ((map_comp_systemTransition_comp_systemPoint h𝔛 hI hC hIK a).trans
      (hab.trans (map_comp_systemTransition_comp_systemPoint h𝔛 hI hC hJK b).symm))

/-- **For a fundamental system, the comparison map is Zariski locally surjective.** A point of `𝔛`
over an affine open `V` of a scheme, landing in a weak affine formal open `U ≅ Spfw A`, kills the
image of a weak ideal of definition `L` of `A`, `V` being quasi-compact; that image is a
neighbourhood of zero in `𝒪_𝔛(U)`, so it contains `ℐ(U)` for a member `ℐ` of the fundamental
system, and the point then kills `ℐ`, which is cut out by `ℐ(U)`, and factors through
`(𝔛, 𝒪_𝔛/ℐ)`. -/
theorem isLocallySurjective_systemComparison
    (hfund : IsFundamentalSystemOfWeakIdealsOfDefinitionOn 𝒮 (IsWeakAffineFormalOpen 𝔛.obj)) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology (systemComparison h𝔛 𝒮 hI hC) := by
  refine ⟨fun {T} s => ?_⟩
  set f := s.hom
  choose U hxU hU using (isMcQuillanFormalScheme_iff_forall_isWeakAffineFormalOpen _).mp h𝔛
  choose V hVa hqV hVU using fun q : T => exists_isAffineOpen_mem_and_subset (x := q)
    (U := (Opens.map f.toHom.base).obj (U (f.toHom.base q))) (hxU _)
  rw [Scheme.mem_grothendieckTopology_iff]
  refine ⟨Scheme.Cover.mkOfCovers T (fun q => (V q).toScheme) (fun q => (V q).ι)
    (fun q => ⟨q, ⟨q, hqV q⟩, rfl⟩), ?_⟩
  rintro _ _ ⟨q⟩
  set W := U (f.toHom.base q)
  set hW := hU (f.toHom.base q)
  set g : schemeToLTRSObj (V q).toScheme ⟶ 𝔛.obj := schemeToLTRS.map (V q).ι ≫ f
  have hg : Set.range g.toHom.base ⊆ (W : Set 𝔛.obj) := by
    rintro _ ⟨y, rfl⟩
    exact hVU q y.2
  have : CompactSpace (V q).toScheme := isCompact_iff_compactSpace.mp (hVa q).isCompact
  obtain ⟨L, hL⟩ := exists_weakIdeal_kill_weakChartSections _ hW.chart.admissible hW.chart.iso g hg
  set e := weakChartSectionsHomeomorph _ hW.chart.admissible hW.chart.iso
  have hnhds : e.symm ⁻¹' (L.1 : Set hW.chart.ring.α) ∈ nhds (0 : (𝔛.obj.presheaf.obj (op W)).α) :=
    (L.2.1.preimage e.symm.continuous).mem_nhds (by
      rw [Set.mem_preimage]
      rw [show e.symm 0 = 0 from (weakChartSectionsRingEquiv _ hW.chart.admissible
        hW.chart.iso).symm.map_zero]
      exact L.1.zero_mem)
  obtain ⟨I, hI𝒮, hIL⟩ := ((hfund.2 W hW).mem_iff).mp hnhds
  have hgI : I.Kills g := by
    refine I.kills_of_isCutOutOn (hC I hI𝒮) g hW hg fun t ht => ?_
    have := hL _ (hIL ht)
    rwa [show (weakChartSections _ hW.chart.admissible hW.chart.iso).1 (e.symm t) = t from
      e.apply_symm_apply t] at this
  obtain ⟨k, hk, -⟩ := I.existsUnique_quotientPoint_factor (hI I hI𝒮) (hC I hI𝒮) h𝔛 g hgI
  exact ⟨(colimit.ι (systemDiagram h𝔛 hI hC ⋙ yoneda) ⟨I, hI𝒮⟩).app _ k,
    (systemComparison_app_ι h𝔛 hI hC ⟨I, hI𝒮⟩ k).trans
      (InducedCategory.hom_ext ((I.quotientMorphism_app_hom _ _ h𝔛 k).trans hk))⟩

include h𝔛 hI hC in
/-- **Stacks 0AIV, a fundamental system presents `h_𝔛` as a colimit.** Let `𝒮` be a nonempty
fundamental system of weak ideals of definition of a McQuillan formal scheme `𝔛`, directed by
inclusion, each member cut out by its sections over the weak affine formal opens. Then `h_𝔛` is the
colimit of the system of schemes `ℐ ↦ (𝔛, 𝒪_𝔛/ℐ)` along thickenings. -/
theorem isColimitOfThickenings_of_isFundamentalSystem (hne : 𝒮.Nonempty)
    (hdir : ∀ I ∈ 𝒮, ∀ J ∈ 𝒮, ∃ K ∈ 𝒮, ∀ W : Opens 𝔛.obj,
      K.ideal W ≤ I.ideal W ∧ K.ideal W ≤ J.ideal W)
    (hfund : IsFundamentalSystemOfWeakIdealsOfDefinitionOn 𝒮 (IsWeakAffineFormalOpen 𝔛.obj)) :
    𝔛.IsColimitOfThickenings := by
  have : Nonempty (SystemIndex 𝒮) := ⟨⟨hne.some, hne.some_mem⟩⟩
  have : IsDirected (SystemIndex 𝒮) (· ≤ ·) := ⟨fun I J => by
    obtain ⟨K, hK, hKle⟩ := hdir I.1 I.2 J.1 J.2
    exact ⟨⟨K, hK⟩, fun W => (hKle W).1, fun W => (hKle W).2⟩⟩
  exact ⟨SystemIndex 𝒮, inferInstance, inferInstance, inferInstance, systemDiagram h𝔛 hI hC,
    fun _ _ g => isThickening_systemTransition h𝔛 hI hC (leOfHom g), systemCocone h𝔛 hI hC,
    Presheaf.isLocallyInjective_of_injective _ _ fun T =>
      injective_systemComparison_app h𝔛 hI hC hdir T.unop,
    isLocallySurjective_systemComparison h𝔛 hI hC hfund⟩

end System

end LocallyTopologicallyRingedSpace.IdealSheaf

end AlgebraicGeometry

end
