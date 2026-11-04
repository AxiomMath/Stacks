module

public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.DifferentialSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiQuasicoherentSheaf

/-!
# Relative differentials form a Zariski sheaf on the schemes over a base

The presheaf sending a scheme `T` over `S` to the global sections of its sheaf of relative
differentials `Ω_{T/S}` is a sheaf for the Zariski topology on `CategoryTheory.Over S`.

## Main definitions

* `AlgebraicGeometry.differentialsRestrictIso` identifies, for an arrow `g : A ⟶ Y` of
  `CategoryTheory.Over S` whose underlying morphism is an open immersion, the restriction of
  `Ω_{Y/S}` to the open image of `g` with `Ω_{A/S}`.
* `AlgebraicGeometry.differentialsOverMap` is the induced map on global sections, with its target
  written as a group of sections of `Ω_{Y/S}` over an open of `Y.left`.

## Main results

* `AlgebraicGeometry.differentialSectionsMap_comp_differentialsOverMap` and
  `AlgebraicGeometry.differentialSectionsMap_comp_differentialsOverMap_comp`: under those
  identifications the maps of the presheaf of relative differentials are restriction maps of
  `Ω_{Y/S}`.
* `AlgebraicGeometry.isSheafFor_differentialSections` is the sheaf condition for a presieve of
  jointly surjective open immersions over `S`.
* `AlgebraicGeometry.relativeDifferentialsPresheaf_isSheaf_zariski` is the Zariski sheaf
  condition for the presheaf of relative differentials.

## References

* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03O2](https://stacks.math.columbia.edu/tag/03O2)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Scheme.Modules
open Stacks.Sites

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} (Y : Over S)

/-- **The restriction of `Ω_{Y/S}` along an open immersion over `S` is the sheaf of relative
differentials of the source.**  This is the canonical morphism of Stacks 01UV, preceded by the
identification of restriction with pullback. -/
noncomputable def differentialsRestrictIso {A : Over S} (g : A ⟶ Y) [IsOpenImmersion g.left] :
    (restrictFunctor g.left).obj (Scheme.Hom.relativeDifferentials Y.hom) ≅
      Scheme.Hom.relativeDifferentials A.hom :=
  (restrictFunctorIsoPullback g.left).app (Scheme.Hom.relativeDifferentials Y.hom) ≪≫
    asIso (Scheme.Hom.relativeDifferentialsMap g.left Y.hom A.hom (𝟙 S) (by simp [Over.w g]))

/-- `AlgebraicGeometry.differentialsRestrictIso` on global sections, with its target written as a
group of sections of `Ω_{Y/S}` over an open of `Y.left`. -/
noncomputable def differentialsOverMap {A : Over S} (g : A ⟶ Y) [IsOpenImmersion g.left] :
    Γ(Scheme.Hom.relativeDifferentials A.hom, (⊤ : A.left.Opens)) ⟶
      Γ(Scheme.Hom.relativeDifferentials Y.hom, g.left ''ᵁ (⊤ : A.left.Opens)) :=
  Scheme.Modules.Hom.app (differentialsRestrictIso Y g).inv (⊤ : A.left.Opens)

/-- `AlgebraicGeometry.differentialsOverMap` is an isomorphism. -/
instance isIso_differentialsOverMap {A : Over S} (g : A ⟶ Y) [IsOpenImmersion g.left] :
    IsIso (differentialsOverMap Y g) :=
  inferInstanceAs
    (IsIso (Scheme.Modules.Hom.app (differentialsRestrictIso Y g).inv (⊤ : A.left.Opens)))

/-- The structure morphism of the target of an arrow over `S` is compatible with its underlying
morphism. -/
private lemma left_comp_hom_eq {A B : Over S} (g : A ⟶ B) : g.left ≫ B.hom = A.hom ≫ 𝟙 S := by
  simp [Over.w g]

/-- The inverse of `AlgebraicGeometry.differentialsRestrictIso` as the inverse of the canonical
morphism of Stacks 01UV followed by the comparison of restriction with pullback. -/
private lemma differentialsRestrictIso_inv_eq {A : Over S} (g : A ⟶ Y) [IsOpenImmersion g.left]
    (h : g.left ≫ Y.hom = A.hom ≫ 𝟙 S) :
    (differentialsRestrictIso Y g).inv =
      inv (Scheme.Hom.relativeDifferentialsMap g.left Y.hom A.hom (𝟙 S) h) ≫
        (restrictFunctorIsoPullback g.left).inv.app (Scheme.Hom.relativeDifferentials Y.hom) :=
  rfl

/-- The inverse of `AlgebraicGeometry.differentialsRestrictIso` cancels the canonical morphism of
Stacks 01UV, leaving the comparison of restriction with pullback. -/
private lemma relativeDifferentialsMap_comp_differentialsRestrictIso_inv
    {A : Over S} (g : A ⟶ Y) [IsOpenImmersion g.left]
    (h : g.left ≫ Y.hom = A.hom ≫ 𝟙 S) :
    Scheme.Hom.relativeDifferentialsMap g.left Y.hom A.hom (𝟙 S) h ≫
        (differentialsRestrictIso Y g).inv =
      (restrictFunctorIsoPullback g.left).inv.app
        (Scheme.Hom.relativeDifferentials Y.hom) := by
  simp [differentialsRestrictIso]

/-- The map of the presheaf of relative differentials along a morphism of schemes over `S` is an
instance of `Stacks.Sites.topUnitMap`. -/
private lemma differentialSectionsMap_eq_topUnitMap {A B : Over S} (g : A ⟶ B)
    (h : g.left ≫ B.hom = A.hom ≫ 𝟙 S) :
    differentialSectionsMap g =
      topUnitMap g.left (Scheme.Hom.relativeDifferentialsMap g.left B.hom A.hom (𝟙 S) h) := by
  rw [topUnitMap, differentialSectionsMap, differentialsSectionMorphism]
  exact congrArg _ ((Scheme.Hom.relativeDifferentials A.hom).presheaf.map_id _)

/-- **The map of the presheaf of relative differentials along an arrow whose underlying morphism
is an open immersion is the restriction map to the open image.** -/
theorem differentialSectionsMap_comp_differentialsRestrictIso {A : Over S} (g : A ⟶ Y)
    [IsOpenImmersion g.left] :
    differentialSectionsMap g ≫
        Scheme.Modules.Hom.app (differentialsRestrictIso Y g).inv (⊤ : A.left.Opens) =
      (Scheme.Hom.relativeDifferentials Y.hom).presheaf.map
        (homOfLE (le_top (a := g.left ''ᵁ (⊤ : A.left.Opens)))).op := by
  rw [differentialSectionsMap_eq_topUnitMap g (left_comp_hom_eq g), topUnitMap_comp,
    relativeDifferentialsMap_comp_differentialsRestrictIso_inv]
  exact topUnitMap_restrictFunctorIsoPullback_inv g.left
    (Scheme.Hom.relativeDifferentials Y.hom)

/-- `AlgebraicGeometry.differentialSectionsMap_comp_differentialsRestrictIso` with the target of
the comparison written as a group of sections of `Ω_{Y/S}`. -/
theorem differentialSectionsMap_comp_differentialsOverMap {A : Over S} (g : A ⟶ Y)
    [IsOpenImmersion g.left] :
    differentialSectionsMap g ≫ differentialsOverMap Y g =
      (Scheme.Hom.relativeDifferentials Y.hom).presheaf.map
        (homOfLE (le_top (a := g.left ''ᵁ (⊤ : A.left.Opens)))).op :=
  differentialSectionsMap_comp_differentialsRestrictIso Y g

/-- The canonical morphisms of Stacks 01UV of two composable arrows of `CategoryTheory.Over S`
compose to the canonical morphism of the composite. -/
private lemma relativeDifferentialsMap_comp_over {A B : Over S} (g : A ⟶ Y) (k : B ⟶ A)
    (hg : g.left ≫ Y.hom = A.hom ≫ 𝟙 S) (hk : k.left ≫ A.hom = B.hom ≫ 𝟙 S)
    (hkg : (k.left ≫ g.left) ≫ Y.hom = B.hom ≫ 𝟙 S) :
    (pullbackComp k.left g.left).inv.app (Scheme.Hom.relativeDifferentials Y.hom) ≫
        (pullback k.left).map
          (Scheme.Hom.relativeDifferentialsMap g.left Y.hom A.hom (𝟙 S) hg) ≫
        Scheme.Hom.relativeDifferentialsMap k.left A.hom B.hom (𝟙 S) hk =
      Scheme.Hom.relativeDifferentialsMap (k.left ≫ g.left) Y.hom B.hom (𝟙 S) hkg :=
  (Scheme.Hom.IsRelativeDifferentialsMap.comp
    (Scheme.Hom.isRelativeDifferentialsMap_relativeDifferentialsMap g.left Y.hom A.hom (𝟙 S) hg)
    (Scheme.Hom.isRelativeDifferentialsMap_relativeDifferentialsMap k.left A.hom B.hom
      (𝟙 S) hk)).eq_relativeDifferentialsMap (𝟙 S) hkg

/-- The canonical morphism of a composite, cancelled against the canonical morphism of its
second factor. -/
private lemma relativeDifferentialsMap_cancel {A B : Over S} (g : A ⟶ Y) (k : B ⟶ A)
    [IsOpenImmersion g.left] [IsOpenImmersion (k.left ≫ g.left)]
    (hg : g.left ≫ Y.hom = A.hom ≫ 𝟙 S) (hk : k.left ≫ A.hom = B.hom ≫ 𝟙 S)
    (hkg : (k.left ≫ g.left) ≫ Y.hom = B.hom ≫ 𝟙 S) :
    Scheme.Hom.relativeDifferentialsMap k.left A.hom B.hom (𝟙 S) hk ≫
        inv (Scheme.Hom.relativeDifferentialsMap (k.left ≫ g.left) Y.hom B.hom (𝟙 S) hkg) =
      (pullback k.left).map
          (inv (Scheme.Hom.relativeDifferentialsMap g.left Y.hom A.hom (𝟙 S) hg)) ≫
        (pullbackComp k.left g.left).hom.app (Scheme.Hom.relativeDifferentials Y.hom) := by
  rw [IsIso.comp_inv_eq, ← relativeDifferentialsMap_comp_over Y g k hg hk hkg, Category.assoc,
    Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, IsIso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The map of the presheaf of relative differentials along a factor of an arrow with open
immersion underlying morphism is the restriction map between the two open images.** -/
theorem differentialSectionsMap_comp_differentialsRestrictIso_comp {A B : Over S} (g : A ⟶ Y)
    (k : B ⟶ A) [IsOpenImmersion g.left] [hki : IsOpenImmersion (k ≫ g).left]
    (hle : (k ≫ g).left ''ᵁ (⊤ : B.left.Opens) ≤ g.left ''ᵁ (⊤ : A.left.Opens)) :
    differentialSectionsMap k ≫
        Scheme.Modules.Hom.app (differentialsRestrictIso Y (k ≫ g)).inv (⊤ : B.left.Opens) =
      Scheme.Modules.Hom.app (differentialsRestrictIso Y g).inv (⊤ : A.left.Opens) ≫
        (Scheme.Hom.relativeDifferentials Y.hom).presheaf.map (homOfLE hle).op := by
  have hcomp : IsOpenImmersion (k.left ≫ g.left) := hki
  have hkoi : IsOpenImmersion k.left := IsOpenImmersion.of_comp k.left g.left
  have hg := left_comp_hom_eq g
  have hk := left_comp_hom_eq k
  have hkg : (k.left ≫ g.left) ≫ Y.hom = B.hom ≫ 𝟙 S := left_comp_hom_eq (k ≫ g)
  have harg : Scheme.Hom.relativeDifferentialsMap k.left A.hom B.hom (𝟙 S) hk ≫
      (differentialsRestrictIso Y (k ≫ g)).inv =
      (pullback k.left).map
          (inv (Scheme.Hom.relativeDifferentialsMap g.left Y.hom A.hom (𝟙 S) hg)) ≫
        ((pullbackComp k.left g.left).hom.app (Scheme.Hom.relativeDifferentials Y.hom) ≫
          (restrictFunctorIsoPullback (k.left ≫ g.left)).inv.app
            (Scheme.Hom.relativeDifferentials Y.hom)) := by
    rw [differentialsRestrictIso_inv_eq Y (k ≫ g) hkg, ← Category.assoc]
    exact (congrArg (· ≫ _) (relativeDifferentialsMap_cancel Y g k hg hk hkg)).trans
      (Category.assoc _ _ _)
  rw [differentialSectionsMap_eq_topUnitMap k hk, topUnitMap_comp, harg,
    ← comp_topUnitMap, ← topUnitMap_comp,
    topUnitMap_pullbackComp k.left g.left (Scheme.Hom.relativeDifferentials Y.hom) hle,
    differentialsRestrictIso_inv_eq Y g hg, Scheme.Modules.Hom.comp_app]
  exact (Category.assoc _ _ _).symm

/-- The `AlgebraicGeometry.differentialsOverMap` form of
`AlgebraicGeometry.differentialSectionsMap_comp_differentialsRestrictIso_comp`. -/
theorem differentialSectionsMap_comp_differentialsOverMap_comp {A B : Over S} (g : A ⟶ Y)
    (k : B ⟶ A) [IsOpenImmersion g.left] [IsOpenImmersion (k ≫ g).left]
    (hle : (k ≫ g).left ''ᵁ (⊤ : B.left.Opens) ≤ g.left ''ᵁ (⊤ : A.left.Opens)) :
    differentialSectionsMap k ≫ differentialsOverMap Y (k ≫ g) =
      differentialsOverMap Y g ≫ (Scheme.Hom.relativeDifferentials Y.hom).presheaf.map
        (homOfLE hle).op :=
  differentialSectionsMap_comp_differentialsRestrictIso_comp Y g k hle

/-- Restricting a transferred section of the presheaf of relative differentials to a smaller open
can be computed through any factorisation of the arrow it comes from. -/
private lemma map_differentialsOverMap {A B : Over S} (g : A ⟶ Y) (k : B ⟶ A) (m : B ⟶ Y)
    (hm : k ≫ g = m) [IsOpenImmersion g.left] [IsOpenImmersion m.left] (V : Y.left.Opens)
    (hVm : V ≤ m.left ''ᵁ (⊤ : B.left.Opens)) (hVg : V ≤ g.left ''ᵁ (⊤ : A.left.Opens))
    (t : ToType Γ(Scheme.Hom.relativeDifferentials A.hom, (⊤ : A.left.Opens))) :
    (Scheme.Hom.relativeDifferentials Y.hom).presheaf.map (homOfLE hVg).op
        (differentialsOverMap Y g t) =
      (Scheme.Hom.relativeDifferentials Y.hom).presheaf.map (homOfLE hVm).op
        (differentialsOverMap Y m (differentialSectionsMap k t)) := by
  subst hm
  have hk : IsOpenImmersion (k.left ≫ g.left) := ‹IsOpenImmersion (k ≫ g).left›
  have hmle : (k ≫ g).left ''ᵁ (⊤ : B.left.Opens) ≤ g.left ''ᵁ (⊤ : A.left.Opens) :=
    image_top_comp_le k.left g.left
  have h : differentialsOverMap Y (k ≫ g) (differentialSectionsMap k t) =
      (Scheme.Hom.relativeDifferentials Y.hom).presheaf.map (homOfLE hmle).op
        (differentialsOverMap Y g t) :=
    ConcreteCategory.congr_hom
      (differentialSectionsMap_comp_differentialsOverMap_comp Y g k hmle) t
  rw [h]
  exact (presheaf_map_apply_comp (Scheme.Hom.relativeDifferentials Y.hom) (homOfLE hmle)
    (homOfLE hVm) (homOfLE hVg) _).symm

/-- **Two sections transferred along arrows of a presieve of open immersions agree on the
intersection of the two open images**, as soon as they agree after restriction along every pair
of morphisms with a common composite. -/
private lemma differentialSections_compatible {A B : Over S} (g₁ : A ⟶ Y) (g₂ : B ⟶ Y)
    [IsOpenImmersion g₁.left] [IsOpenImmersion g₂.left]
    (t₁ : ToType Γ(Scheme.Hom.relativeDifferentials A.hom, (⊤ : A.left.Opens)))
    (t₂ : ToType Γ(Scheme.Hom.relativeDifferentials B.hom, (⊤ : B.left.Opens)))
    (ht : ∀ (C : Over S) (k₁ : C ⟶ A) (k₂ : C ⟶ B), k₁ ≫ g₁ = k₂ ≫ g₂ →
      differentialSectionsMap k₁ t₁ = differentialSectionsMap k₂ t₂) :
    (Scheme.Hom.relativeDifferentials Y.hom).presheaf.map
        (Opens.infLELeft (g₁.left ''ᵁ (⊤ : A.left.Opens))
          (g₂.left ''ᵁ (⊤ : B.left.Opens))).op (differentialsOverMap Y g₁ t₁) =
      (Scheme.Hom.relativeDifferentials Y.hom).presheaf.map
        (Opens.infLERight (g₁.left ''ᵁ (⊤ : A.left.Opens))
          (g₂.left ''ᵁ (⊤ : B.left.Opens))).op (differentialsOverMap Y g₂ t₂) := by
  obtain ⟨C, m, hmi, hVm, k₁, k₂, hm₁, hm₂⟩ :=
    exists_common_refinement Y g₁ g₂
      ((g₁.left ''ᵁ (⊤ : A.left.Opens)) ⊓ (g₂.left ''ᵁ (⊤ : B.left.Opens)))
      inf_le_left inf_le_right
  have := hmi
  rw [presheaf_map_eq _ (Opens.infLELeft _ _) (homOfLE inf_le_left),
    presheaf_map_eq _ (Opens.infLERight _ _) (homOfLE inf_le_right),
    map_differentialsOverMap Y g₁ k₁ m hm₁ _ hVm inf_le_left t₁,
    map_differentialsOverMap Y g₂ k₂ m hm₂ _ hVm inf_le_right t₂,
    ht C k₁ k₂ (hm₁.trans hm₂.symm)]

/-- **The Zariski sheaf condition for the presheaf of relative differentials**, for a presieve of
`CategoryTheory.Over S` whose arrows are open immersions of the underlying schemes and are
jointly surjective. -/
theorem isSheafFor_differentialSections (R : Presieve Y)
    (hoi : ∀ {A : Over S} (g : A ⟶ Y), R g → IsOpenImmersion g.left)
    (hcov : ∀ y : Y.left, ∃ (A : Over S) (g : A ⟶ Y) (_ : R g), y ∈ Set.range g.left.base) :
    Presieve.IsSheafFor
      ((relativeDifferentialsPresheaf S).functor ⋙ CategoryTheory.forget AddCommGrpCat) R := by
  intro x hx
  have hoi' : ∀ i : Σ A : Over S, { g : A ⟶ Y // R g }, IsOpenImmersion i.2.1.left :=
    fun i => hoi i.2.1 i.2.2
  have key : ∀ {A : Over S} (g : A ⟶ Y) (_ : IsOpenImmersion g.left)
      (t : ToType Γ(Scheme.Hom.relativeDifferentials Y.hom, (⊤ : Y.left.Opens))),
      differentialsOverMap Y g (differentialSectionsMap g t) =
        (Scheme.Hom.relativeDifferentials Y.hom).presheaf.map
          (homOfLE (le_top (a := g.left ''ᵁ (⊤ : A.left.Opens)))).op t :=
    fun g _ t =>
      ConcreteCategory.congr_hom (differentialSectionsMap_comp_differentialsOverMap Y g) t
  have hcompat : ∀ i j : Σ A : Over S, { g : A ⟶ Y // R g },
      (Scheme.Hom.relativeDifferentials Y.hom).presheaf.map
          (Opens.infLELeft (i.2.1.left ''ᵁ (⊤ : i.1.left.Opens))
            (j.2.1.left ''ᵁ (⊤ : j.1.left.Opens))).op
          (differentialsOverMap Y i.2.1 (x i.2.1 i.2.2)) =
        (Scheme.Hom.relativeDifferentials Y.hom).presheaf.map
          (Opens.infLERight (i.2.1.left ''ᵁ (⊤ : i.1.left.Opens))
            (j.2.1.left ''ᵁ (⊤ : j.1.left.Opens))).op
          (differentialsOverMap Y j.2.1 (x j.2.1 j.2.2)) := by
    intro i j
    have := hoi' i
    have := hoi' j
    exact differentialSections_compatible Y i.2.1 j.2.1 _ _
      fun C k₁ k₂ hk => hx k₁ k₂ i.2.2 j.2.2 hk
  obtain ⟨s, hs, hsuniq⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨(Scheme.Hom.relativeDifferentials Y.hom).presheaf,
      (Scheme.Hom.relativeDifferentials Y.hom).isSheaf⟩ :
      TopCat.Sheaf AddCommGrpCat.{u} Y.left)
    (fun i : Σ A : Over S, { g : A ⟶ Y // R g } => i.2.1.left ''ᵁ (⊤ : i.1.left.Opens))
    (⊤ : Y.left.Opens) (fun _ => homOfLE le_top)
    (by
      intro y _
      obtain ⟨A, g, hg, hy⟩ := hcov y
      refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨A, ⟨g, hg⟩⟩, ?_⟩
      rwa [Scheme.Hom.image_top_eq_opensRange])
    (fun i => differentialsOverMap Y i.2.1 (x i.2.1 i.2.2))
    hcompat
  refine ⟨s, ?_, ?_⟩
  · intro A g hg
    have := hoi g hg
    exact (ConcreteCategory.bijective_of_isIso (differentialsOverMap Y g)).1
      ((key g this s).trans (hs ⟨A, ⟨g, hg⟩⟩))
  · intro t ht
    refine hsuniq _ fun i => ?_
    have hi : IsOpenImmersion i.2.1.left := hoi' i
    refine (key i.2.1 hi t).symm.trans ?_
    exact congrArg (fun z => ConcreteCategory.hom (differentialsOverMap Y i.2.1) z)
      (ht i.2.1 i.2.2)

/-- **The Zariski sheaf condition for the presheaf of relative differentials**, for the presieves
that generate the Zariski topology on `CategoryTheory.Over S`. -/
theorem isSheafFor_zariski_presieve_differentials (R : Presieve Y)
    (hR : R.map (Over.forget S) ∈ Scheme.precoverage @IsOpenImmersion Y.left) :
    Presieve.IsSheafFor
      ((relativeDifferentialsPresheaf S).functor ⋙ CategoryTheory.forget AddCommGrpCat) R := by
  obtain ⟨hsurj, hoi⟩ := hR
  rw [Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hsurj
  refine isSheafFor_differentialSections Y R (fun g hg => hoi (Presieve.map.of hg)) ?_
  intro y
  obtain ⟨W, f, @⟨A, g, hg⟩, hy⟩ := hsurj y
  exact ⟨A, g, hg, hy⟩

/-- The presheaf on schemes over `S` sending a scheme to the global sections of its sheaf of
relative differentials is a sheaf for the Zariski topology. -/
@[stacks 03O2 "zariski_sheaf"]
theorem relativeDifferentialsPresheaf_isSheaf_zariski (S : Scheme.{u}) :
    Presheaf.IsSheaf (Scheme.zariskiTopology.{u}.over S)
      (relativeDifferentialsPresheaf S).functor :=
  isSheaf_addCommGrpCat_over_toGrothendieck_of_isSheafFor
    (Scheme.precoverage @IsOpenImmersion) S _
    fun {Y} R hR => isSheafFor_zariski_presieve_differentials Y R hR

end AlgebraicGeometry

end
