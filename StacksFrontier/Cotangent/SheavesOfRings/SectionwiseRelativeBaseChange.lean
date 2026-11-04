module

public import StacksFrontier.Cotangent.OverDifferentialsSquare
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseTower

/-!
# The sectionwise base change `R_• ⊗_{S_•} B` of Remark 08SE

Let `A ⟶ B ⟶ D` be homomorphisms of sheaves of commutative rings on a site. Over every object
`U`, Remark 08SE attaches to the ring maps `A(U) → B(U) → D(U)` the augmented simplicial
`B(U)`-algebra `R̄_•(U) = R_•(U) ⊗_{S_•(U)} B(U)`, where `R_•(U)` and `S_•(U)` are the standard
resolutions of `D(U)` and `B(U)` over `B(U)` (`CommAlgCat.relativeBaseChange`), together with the
complex `Ω[R̄_•(U)⁄B(U)] ⊗ D(U)`.

This file makes `U ↦ R̄_•(U)` functorial in `U`, by the universal property of the pushouts that
define it, and assembles the complexes `Ω[R̄_•(U)⁄B(U)] ⊗ D(U)` into a complex of presheaves of
`D`-modules.

## Main definitions

* `CategoryTheory.Sheaf.relativeBaseChangeRestriction`: the restriction maps
  `R̄_n(U) ⟶ R̄_n(V)`.
* `CategoryTheory.Sheaf.sectionwiseRelativeBaseChangeComplex`: the complex of presheaves of
  `D`-modules `U ↦ Ω[R̄_•(U)⁄B(U)] ⊗ D(U)`.
* `CategoryTheory.Sheaf.sectionwiseRelativeBaseChangeLeg`: the map of complexes of presheaves
  `U ↦ (L_{D(U)/B(U)} ⟶ Ω[R̄_•(U)⁄B(U)] ⊗ D(U))` induced by the pushout legs.

## References

* [Stacks Project, Tag 08SE](https://stacks.math.columbia.edu/tag/08SE)
* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B D : Sheaf J CommRingCat.{max u v w}} (g : A ⟶ B) (h : B ⟶ D)

/-- The restriction square of `B` along `U ⟶ V`, read as a square between `B(U)` and `B(V)`
viewed as algebras over themselves. -/
noncomputable def baseSelfRestrictionSquare {U V : Cᵒᵖ} (k : U ⟶ V) :
    CommAlgCat.AlgebraSquare.{max u v w, max u v w, max u v w} (B.obj.obj U) (B.obj.obj V)
      (CommAlgCat.of (B.obj.obj U) (B.obj.obj U)) (CommAlgCat.of (B.obj.obj V) (B.obj.obj V)) where
  base := (B.obj.map k).hom
  map := (B.obj.map k).hom
  map_algebraMap _ := rfl

/-- The square `(id, B(U) → D(U))` restricts along `U ⟶ V` in two ways, and the two composite
squares agree. -/
theorem idSquare_overBase_comp {U V : Cᵒᵖ} (k : U ⟶ V) :
    (CommAlgCat.idSquare (CommAlgCat.overBase (sectionsTowerHom J g h U))).comp
        (sectionsRestrictionSquare J h k) =
      (baseSelfRestrictionSquare J k).comp
        (CommAlgCat.idSquare (CommAlgCat.overBase (sectionsTowerHom J g h V))) := by
  unfold CommAlgCat.idSquare sectionsRestrictionSquare baseSelfRestrictionSquare
    CommAlgCat.AlgebraSquare.comp
  congr 1
  exact (congrArg CommRingCat.Hom.hom (h.hom.naturality k)).symm

/-- The maps of standard resolutions of the two composite squares of `idSquare_overBase_comp`
agree, elementwise. -/
theorem standardResolutionSquareMap_overBase_comp {U V : Cᵒᵖ} (k : U ⟶ V)
    (n : SimplexCategoryᵒᵖ)
    (s : (CommAlgCat.standardResolution.{max u v w, max u v w} (B.obj.obj U)
      (CommAlgCat.of (B.obj.obj U) (B.obj.obj U))).left.obj n) :
    CommAlgCat.standardResolutionSquareMap.{max u v w, max u v w, max u v w}
        (sectionsRestrictionSquare J h k) n
        (CommAlgCat.standardResolutionSquareMap.{max u v w, max u v w, max u v w}
          (CommAlgCat.idSquare (CommAlgCat.overBase (sectionsTowerHom J g h U))) n s) =
      CommAlgCat.standardResolutionSquareMap.{max u v w, max u v w, max u v w}
        (CommAlgCat.idSquare (CommAlgCat.overBase (sectionsTowerHom J g h V))) n
        (CommAlgCat.standardResolutionSquareMap.{max u v w, max u v w, max u v w}
          (baseSelfRestrictionSquare J k) n s) :=
  (RingHom.congr_fun (CommAlgCat.standardResolutionSquareMap_comp.{max u v w, max u v w}
      (CommAlgCat.idSquare (CommAlgCat.overBase (sectionsTowerHom J g h U)))
      (sectionsRestrictionSquare J h k) n) s).symm.trans
    ((congrArg (fun sq => CommAlgCat.standardResolutionSquareMap.{max u v w, max u v w,
        max u v w} sq n s) (idSquare_overBase_comp J g h k)).trans
      (RingHom.congr_fun (CommAlgCat.standardResolutionSquareMap_comp.{max u v w, max u v w}
        (baseSelfRestrictionSquare J k)
        (CommAlgCat.idSquare (CommAlgCat.overBase (sectionsTowerHom J g h V))) n) s))

/-- Elementwise form of the compatibility of the restriction of `R̄_•` with the pushout square:
both ways around carry a section `s` of `S_n(U)` to the image of `s` in `R̄_n(V)`. -/
theorem relativeBaseChangeRestriction_w_apply {U V : Cᵒᵖ} (k : U ⟶ V) (n : SimplexCategoryᵒᵖ)
    (s : (CommAlgCat.standardResolution.{max u v w, max u v w} (B.obj.obj U)
      (CommAlgCat.of (B.obj.obj U) (B.obj.obj U))).left.obj n) :
    CommAlgCat.canonicalBaseChangeMap.{max u v w, max u v w} (B.obj.obj V)
        (CommAlgCat.overBase (sectionsTowerHom J g h V)) n
      (CommAlgCat.standardResolutionSquareMap.{max u v w, max u v w, max u v w}
        (sectionsRestrictionSquare J h k) n
        ((((CommAlgCat.standardResolutionFunctor.{max u v w, max u v w} (B.obj.obj U)).map
          (CommAlgCat.overBase (sectionsTowerHom J g h U))).left.app n).hom.toRingHom s)) =
    algebraMap (B.obj.obj V) ((CommAlgCat.relativeBaseChange (sectionsTowerHom J g h V)).left.obj n)
      ((B.obj.map k).hom (CommAlgCat.standardResolutionAugmentationHom.{max u v w, max u v w}
        (B.obj.obj U) (CommAlgCat.of (B.obj.obj U) (B.obj.obj U)) n s)) := by
  have h₁ := (congrArg (CommAlgCat.standardResolutionSquareMap.{max u v w, max u v w, max u v w}
      (sectionsRestrictionSquare J h k) n)
      (RingHom.congr_fun (CommAlgCat.standardResolutionSquareMap_idSquare
        (CommAlgCat.overBase (sectionsTowerHom J g h U)) n) s).symm).trans
    ((standardResolutionSquareMap_overBase_comp J g h k n s).trans
      (RingHom.congr_fun (CommAlgCat.standardResolutionSquareMap_idSquare
        (CommAlgCat.overBase (sectionsTowerHom J g h V)) n) _))
  have h₂ := ConcreteCategory.congr_hom
    (CommAlgCat.relativeBaseChange_isPushout (sectionsTowerHom J g h V) n).w
    (CommAlgCat.standardResolutionSquareMap.{max u v w, max u v w, max u v w}
      (baseSelfRestrictionSquare J k) n s)
  have h₃ := CommAlgCat.standardResolutionSquareMap_augmentation_app.{max u v w, max u v w,
    max u v w} (baseSelfRestrictionSquare J k) n s
  exact (congrArg (CommAlgCat.canonicalBaseChangeMap.{max u v w, max u v w} (B.obj.obj V)
    (CommAlgCat.overBase (sectionsTowerHom J g h V)) n) h₁).trans
      (h₂.trans (congrArg (algebraMap (B.obj.obj V)
        ((CommAlgCat.relativeBaseChange (sectionsTowerHom J g h V)).left.obj n)) h₃))

/-- **The restriction maps of `U ↦ R̄_n(U)`**, by the universal property of the pushout
`R̄_n(U) = R_n(U) ⊗_{S_n(U)} B(U)`: the map of standard resolutions of `D` over `B` followed by
the pushout leg into `R̄_n(V)`, and the restriction of `B` followed by the structure map. -/
noncomputable def relativeBaseChangeRestriction {U V : Cᵒᵖ} (k : U ⟶ V)
    (n : SimplexCategoryᵒᵖ) :
    CommRingCat.of ((CommAlgCat.relativeBaseChange (sectionsTowerHom J g h U)).left.obj n) ⟶
      CommRingCat.of ((CommAlgCat.relativeBaseChange (sectionsTowerHom J g h V)).left.obj n) :=
  (CommAlgCat.relativeBaseChange_isPushout (sectionsTowerHom J g h U) n).desc
    (CommRingCat.ofHom (CommAlgCat.standardResolutionSquareMap.{max u v w, max u v w, max u v w}
        (sectionsRestrictionSquare J h k) n) ≫
      CommRingCat.ofHom (CommAlgCat.canonicalBaseChangeMap.{max u v w, max u v w} (B.obj.obj V)
        (CommAlgCat.overBase (sectionsTowerHom J g h V)) n))
    (CommRingCat.ofHom (B.obj.map k).hom ≫ CommRingCat.ofHom (algebraMap (B.obj.obj V)
      ((CommAlgCat.relativeBaseChange (sectionsTowerHom J g h V)).left.obj n)))
    (CommRingCat.hom_ext (RingHom.ext fun s => relativeBaseChangeRestriction_w_apply J g h k n s))

/-- The restriction of `R̄_•` on the pushout leg out of `R_•`. -/
theorem relativeBaseChangeRestriction_canonicalBaseChangeMap {U V : Cᵒᵖ} (k : U ⟶ V)
    (n : SimplexCategoryᵒᵖ)
    (r : (CommAlgCat.standardResolution.{max u v w, max u v w} (B.obj.obj U)
      (sectionsAlgebra J h U)).left.obj n) :
    (relativeBaseChangeRestriction J g h k n).hom
        (CommAlgCat.canonicalBaseChangeMap.{max u v w, max u v w} (B.obj.obj U)
          (CommAlgCat.overBase (sectionsTowerHom J g h U)) n r) =
      CommAlgCat.canonicalBaseChangeMap.{max u v w, max u v w} (B.obj.obj V)
        (CommAlgCat.overBase (sectionsTowerHom J g h V)) n
        (CommAlgCat.standardResolutionSquareMap.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare J h k) n r) :=
  ConcreteCategory.congr_hom
    ((CommAlgCat.relativeBaseChange_isPushout (sectionsTowerHom J g h U) n).inl_desc _ _ _) r

/-- The restriction of `R̄_•` on the structure map out of `B`. -/
theorem relativeBaseChangeRestriction_algebraMap {U V : Cᵒᵖ} (k : U ⟶ V)
    (n : SimplexCategoryᵒᵖ) (b : B.obj.obj U) :
    (relativeBaseChangeRestriction J g h k n).hom
        (algebraMap (B.obj.obj U)
          ((CommAlgCat.relativeBaseChange (sectionsTowerHom J g h U)).left.obj n) b) =
      algebraMap (B.obj.obj V)
        ((CommAlgCat.relativeBaseChange (sectionsTowerHom J g h V)).left.obj n)
        ((B.obj.map k).hom b) :=
  ConcreteCategory.congr_hom
    ((CommAlgCat.relativeBaseChange_isPushout (sectionsTowerHom J g h U) n).inr_desc _ _ _) b

/-- The augmentation of `R̄_•(U)` to `D(U)`, in simplicial degree `n`, as a ring homomorphism. -/
noncomputable abbrev relativeBaseChangeAugmentation (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ) :
    CommRingCat.of ((CommAlgCat.relativeBaseChange (sectionsTowerHom J g h U)).left.obj n) ⟶
      CommRingCat.of (D.obj.obj U) :=
  CommRingCat.ofHom
    ((CommAlgCat.relativeBaseChange (sectionsTowerHom J g h U)).hom.app n).hom.toRingHom

/-- The restriction maps of `R̄_•` are compatible with the augmentations to `D`. -/
theorem relativeBaseChangeRestriction_augmentation {U V : Cᵒᵖ} (k : U ⟶ V)
    (n : SimplexCategoryᵒᵖ) :
    relativeBaseChangeRestriction J g h k n ≫ relativeBaseChangeAugmentation J g h V n =
      relativeBaseChangeAugmentation J g h U n ≫ D.obj.map k := by
  refine (CommAlgCat.relativeBaseChange_isPushout (sectionsTowerHom J g h U) n).hom_ext ?_ ?_
  · refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    have h₁ := relativeBaseChangeRestriction_canonicalBaseChangeMap J g h k n r
    have h₂ := CommAlgCat.canonicalBaseChangeMap_augmentation_apply
      (CommAlgCat.overBase (sectionsTowerHom J g h V)) n
      (CommAlgCat.standardResolutionSquareMap.{max u v w, max u v w, max u v w}
        (sectionsRestrictionSquare J h k) n r)
    have h₃ := CommAlgCat.standardResolutionSquareMap_augmentation_app.{max u v w, max u v w,
      max u v w} (sectionsRestrictionSquare J h k) n r
    have h₄ := CommAlgCat.canonicalBaseChangeMap_augmentation_apply
      (CommAlgCat.overBase (sectionsTowerHom J g h U)) n r
    show ((CommAlgCat.relativeBaseChange (sectionsTowerHom J g h V)).hom.app n).hom.toRingHom
        ((relativeBaseChangeRestriction J g h k n).hom
          (CommAlgCat.canonicalBaseChangeMap _ _ n r)) =
      (D.obj.map k).hom (((CommAlgCat.relativeBaseChange (sectionsTowerHom J g h U)).hom.app
        n).hom.toRingHom (CommAlgCat.canonicalBaseChangeMap _ _ n r))
    rw [h₁]
    exact h₂.trans (h₃.trans (congrArg (D.obj.map k).hom h₄.symm))
  · refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
    have h₁ := relativeBaseChangeRestriction_algebraMap J g h k n b
    show ((CommAlgCat.relativeBaseChange (sectionsTowerHom J g h V)).hom.app n).hom.toRingHom
        ((relativeBaseChangeRestriction J g h k n).hom (algebraMap _ _ b)) =
      (D.obj.map k).hom (((CommAlgCat.relativeBaseChange (sectionsTowerHom J g h U)).hom.app
        n).hom.toRingHom (algebraMap _ _ b))
    rw [h₁]
    refine (((CommAlgCat.relativeBaseChange (sectionsTowerHom J g h V)).hom.app n).hom.commutes
      _).trans ?_
    refine Eq.trans ?_ (congrArg (D.obj.map k).hom
      (((CommAlgCat.relativeBaseChange (sectionsTowerHom J g h U)).hom.app n).hom.commutes
        b).symm)
    exact congrArg (fun φ : B.obj.obj U ⟶ D.obj.obj V => φ.hom b) (h.hom.naturality k)

/-- The restriction maps of `R̄_•` commute with the simplicial operators. -/
theorem relativeBaseChangeRestriction_naturality {U V : Cᵒᵖ} (k : U ⟶ V)
    {i j : SimplexCategoryᵒᵖ} (m : i ⟶ j) :
    CommRingCat.ofHom ((CommAlgCat.relativeBaseChange (sectionsTowerHom J g h U)).left.map
        m).hom.toRingHom ≫ relativeBaseChangeRestriction J g h k j =
      relativeBaseChangeRestriction J g h k i ≫
        CommRingCat.ofHom ((CommAlgCat.relativeBaseChange (sectionsTowerHom J g h V)).left.map
          m).hom.toRingHom := by
  refine (CommAlgCat.relativeBaseChange_isPushout (sectionsTowerHom J g h U) i).hom_ext ?_ ?_
  · refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    show (relativeBaseChangeRestriction J g h k j).hom
        ((CommAlgCat.relativeBaseChange (sectionsTowerHom J g h U)).left.map m
          (CommAlgCat.canonicalBaseChangeMap _ _ i r)) =
      (CommAlgCat.relativeBaseChange (sectionsTowerHom J g h V)).left.map m
        ((relativeBaseChangeRestriction J g h k i).hom (CommAlgCat.canonicalBaseChangeMap _ _ i r))
    exact (congrArg (relativeBaseChangeRestriction J g h k j).hom
        (CommAlgCat.canonicalBaseChangeMap_naturality_apply
          (CommAlgCat.overBase (sectionsTowerHom J g h U)) m r)).trans
      ((relativeBaseChangeRestriction_canonicalBaseChangeMap J g h k j _).trans
        ((congrArg (CommAlgCat.canonicalBaseChangeMap.{max u v w, max u v w} (B.obj.obj V)
            (CommAlgCat.overBase (sectionsTowerHom J g h V)) j)
          (CommAlgCat.standardResolutionSquareMap_naturality.{max u v w, max u v w, max u v w}
            (sectionsRestrictionSquare J h k) m r)).trans
          ((CommAlgCat.canonicalBaseChangeMap_naturality_apply
            (CommAlgCat.overBase (sectionsTowerHom J g h V)) m _).symm.trans
            (congrArg ((CommAlgCat.relativeBaseChange (sectionsTowerHom J g h V)).left.map m)
              (relativeBaseChangeRestriction_canonicalBaseChangeMap J g h k i r).symm))))
  · refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
    show (relativeBaseChangeRestriction J g h k j).hom
        ((CommAlgCat.relativeBaseChange (sectionsTowerHom J g h U)).left.map m
          (algebraMap _ _ b)) =
      (CommAlgCat.relativeBaseChange (sectionsTowerHom J g h V)).left.map m
        ((relativeBaseChangeRestriction J g h k i).hom (algebraMap _ _ b))
    rw [((CommAlgCat.relativeBaseChange (sectionsTowerHom J g h U)).left.map m).hom.commutes,
      relativeBaseChangeRestriction_algebraMap, relativeBaseChangeRestriction_algebraMap,
      ((CommAlgCat.relativeBaseChange (sectionsTowerHom J g h V)).left.map m).hom.commutes]

/-- The restriction of `R̄_•` along an identity is the identity. -/
theorem relativeBaseChangeRestriction_id (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ) :
    relativeBaseChangeRestriction J g h (𝟙 U) n = 𝟙 _ := by
  refine (CommAlgCat.relativeBaseChange_isPushout (sectionsTowerHom J g h U) n).hom_ext ?_ ?_
  · refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    refine (relativeBaseChangeRestriction_canonicalBaseChangeMap J g h (𝟙 U) n r).trans ?_
    refine congrArg (CommAlgCat.canonicalBaseChangeMap _ _ n) ?_
    rw [sectionsRestrictionSquare_id, CommAlgCat.standardResolutionSquareMap_id]
    rfl
  · refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
    refine (relativeBaseChangeRestriction_algebraMap J g h (𝟙 U) n b).trans ?_
    rw [B.obj.map_id]
    rfl

/-- The restriction of `R̄_•` along a composite is the composite of the restrictions. -/
theorem relativeBaseChangeRestriction_comp {U V W : Cᵒᵖ} (k : U ⟶ V) (k' : V ⟶ W)
    (n : SimplexCategoryᵒᵖ) :
    relativeBaseChangeRestriction J g h (k ≫ k') n =
      relativeBaseChangeRestriction J g h k n ≫ relativeBaseChangeRestriction J g h k' n := by
  refine (CommAlgCat.relativeBaseChange_isPushout (sectionsTowerHom J g h U) n).hom_ext ?_ ?_
  · refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    refine (relativeBaseChangeRestriction_canonicalBaseChangeMap J g h (k ≫ k') n r).trans ?_
    refine Eq.trans ?_ ((congrArg (relativeBaseChangeRestriction J g h k' n).hom
      (relativeBaseChangeRestriction_canonicalBaseChangeMap J g h k n r)).trans
        (relativeBaseChangeRestriction_canonicalBaseChangeMap J g h k' n _)).symm
    refine congrArg (CommAlgCat.canonicalBaseChangeMap.{max u v w, max u v w} (B.obj.obj W)
      (CommAlgCat.overBase (sectionsTowerHom J g h W)) n) ?_
    exact (congrArg (fun sq => CommAlgCat.standardResolutionSquareMap.{max u v w, max u v w,
        max u v w} sq n r) (sectionsRestrictionSquare_comp J h k k')).trans
      (RingHom.congr_fun (CommAlgCat.standardResolutionSquareMap_comp.{max u v w, max u v w}
        _ _ n) r)
  · refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
    refine (relativeBaseChangeRestriction_algebraMap J g h (k ≫ k') n b).trans ?_
    show _ = (relativeBaseChangeRestriction J g h k' n).hom
      ((relativeBaseChangeRestriction J g h k n).hom (algebraMap _ _ b))
    rw [relativeBaseChangeRestriction_algebraMap, relativeBaseChangeRestriction_algebraMap,
      B.obj.map_comp]
    rfl

/-- The augmentation `R̄_•(U) ⟶ D(U)`, with target written as the algebra of sections of `h`. -/
noncomputable def relativeBaseChangeAug (U : Cᵒᵖ) :
    (CommAlgCat.relativeBaseChange (sectionsTowerHom J g h U)).left ⟶
      (SimplicialObject.const (CommAlgCat.{max u v w} (B.obj.obj U))).obj (sectionsAlgebra J h U) :=
  (CommAlgCat.relativeBaseChange (sectionsTowerHom J g h U)).hom

/-- The complex `Ω[R̄_•(U)⁄B(U)] ⊗ D(U)` of Remark 08SE. -/
noncomputable abbrev relativeBaseChangeCotangentComplex (U : Cᵒᵖ) :
    CochainComplex (ModuleCat.{max u v w} (sectionsAlgebra J h U)) ℤ :=
  CommAlgCat.augmentedCotangentCochainComplex (relativeBaseChangeAug J g h U)

/-- The map of complexes `Ω[R̄_•(U)⁄B(U)] ⊗ D(U) ⟶ Ω[R̄_•(V)⁄B(V)] ⊗ D(V)` induced by the
restriction along `U ⟶ V`. -/
noncomputable def relativeBaseChangeCotangentRestriction {U V : Cᵒᵖ} (k : U ⟶ V) :
    relativeBaseChangeCotangentComplex J g h U ⟶
      ((ModuleCat.restrictScalars (sectionsRestrictionSquare J h k).map).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (relativeBaseChangeCotangentComplex J g h V) :=
  CommAlgCat.augmentedCotangentSquareMap (sectionsRestrictionSquare J h k)
    (relativeBaseChangeAug J g h U) (relativeBaseChangeAug J g h V)
    (fun n => (relativeBaseChangeRestriction J g h k n).hom)
    (fun n b => relativeBaseChangeRestriction_algebraMap J g h k n b)
    (fun n x => ConcreteCategory.congr_hom (relativeBaseChangeRestriction_augmentation J g h k n) x)
    (fun m x => ConcreteCategory.congr_hom (relativeBaseChangeRestriction_naturality J g h k m) x)

/-- The complex `Ω[P_•⁄R] ⊗ D` of an augmented simplicial algebra vanishes in positive
degrees. -/
theorem augmentedCotangentCochainComplex_isZero_pos {R : Type (max u v w)} [CommRing R]
    {E : CommAlgCat.{max u v w} R} {P : SimplicialObject (CommAlgCat.{max u v w} R)}
    (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{max u v w} R)).obj E) (j : ℤ) (hj : 0 < j) :
    IsZero ((CommAlgCat.augmentedCotangentCochainComplex ε).X j) := by
  apply HomologicalComplex.isZero_extend_X
  intro n
  simp only [ComplexShape.embeddingUpIntLE_f]
  lia

/-- The restriction of `Ω[R̄_•⁄B] ⊗ D` sends `1 ⊗ d x` to `1 ⊗ d` of the restriction of `x`. -/
theorem relativeBaseChangeCotangentRestriction_f_mk {U V : Cᵒᵖ} (k : U ⟶ V) (n : ℕ)
    (p : ((CommAlgCat.relativeBaseChange (sectionsTowerHom J g h U)).left.obj (op ⦋n⦌) :
      Type (max u v w))) :
    (relativeBaseChangeCotangentRestriction J g h k).f (-(n : ℤ))
        (CommAlgCat.augmentedCotangentMk (relativeBaseChangeAug J g h U) n p) =
      CommAlgCat.augmentedCotangentMk (relativeBaseChangeAug J g h V) n
        ((relativeBaseChangeRestriction J g h k (op ⦋n⦌)).hom p) :=
  CommAlgCat.augmentedCotangentSquareMap_f_mk (sectionsRestrictionSquare J h k)
    (relativeBaseChangeAug J g h U) (relativeBaseChangeAug J g h V)
    (fun n => (relativeBaseChangeRestriction J g h k n).hom)
    (fun n b => relativeBaseChangeRestriction_algebraMap J g h k n b)
    (fun n x => ConcreteCategory.congr_hom (relativeBaseChangeRestriction_augmentation J g h k n) x)
    (fun m x => ConcreteCategory.congr_hom
      (relativeBaseChangeRestriction_naturality J g h k m) x) n p

/-- The presheaf of `D`-modules `U ↦ (Ω[R̄_•(U)⁄B(U)] ⊗ D(U))^j`. -/
noncomputable def sectionwiseRelativeBaseChangeTerm (j : ℤ) :
    PresheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj where
  obj U := (relativeBaseChangeCotangentComplex J g h U).X j
  map k := (relativeBaseChangeCotangentRestriction J g h k).f j
  map_id U := by
    by_cases hj : 0 < j
    · exact (augmentedCotangentCochainComplex_isZero_pos.{u, v, w}
        (relativeBaseChangeAug J g h U) j hj).eq_of_src _ _
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by lia⟩
      refine CommAlgCat.augmentedCotangent_hom_ext (relativeBaseChangeAug J g h U) n _ _
        fun p => ?_
      change (relativeBaseChangeCotangentRestriction J g h (𝟙 U)).f (-(n : ℤ))
          (CommAlgCat.augmentedCotangentMk (relativeBaseChangeAug J g h U) n p) =
        CommAlgCat.augmentedCotangentMk (relativeBaseChangeAug J g h U) n p
      exact (relativeBaseChangeCotangentRestriction_f_mk J g h (𝟙 U) n p).trans
        (congrArg (CommAlgCat.augmentedCotangentMk (relativeBaseChangeAug J g h U) n)
          (ConcreteCategory.congr_hom (relativeBaseChangeRestriction_id J g h U (op ⦋n⦌)) p))
  map_comp {U V W} k k' := by
    by_cases hj : 0 < j
    · exact (augmentedCotangentCochainComplex_isZero_pos.{u, v, w}
        (relativeBaseChangeAug J g h U) j hj).eq_of_src _ _
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by lia⟩
      refine CommAlgCat.augmentedCotangent_hom_ext (relativeBaseChangeAug J g h U) n _ _
        fun p => ?_
      change (relativeBaseChangeCotangentRestriction J g h (k ≫ k')).f (-(n : ℤ))
          (CommAlgCat.augmentedCotangentMk (relativeBaseChangeAug J g h U) n p) =
        (relativeBaseChangeCotangentRestriction J g h k').f (-(n : ℤ))
          ((relativeBaseChangeCotangentRestriction J g h k).f (-(n : ℤ))
            (CommAlgCat.augmentedCotangentMk (relativeBaseChangeAug J g h U) n p))
      refine (relativeBaseChangeCotangentRestriction_f_mk J g h (k ≫ k') n p).trans ?_
      refine Eq.trans ?_ ((congrArg ((relativeBaseChangeCotangentRestriction J g h k').f
        (-(n : ℤ))) (relativeBaseChangeCotangentRestriction_f_mk J g h k n p)).trans
          (relativeBaseChangeCotangentRestriction_f_mk J g h k' n _)).symm
      exact congrArg (CommAlgCat.augmentedCotangentMk (relativeBaseChangeAug J g h W) n)
        (ConcreteCategory.congr_hom (relativeBaseChangeRestriction_comp J g h k k' (op ⦋n⦌)) p)

/-- **The complex of presheaves of `D`-modules `U ↦ Ω[R̄_•(U)⁄B(U)] ⊗ D(U)`** of Remark 08SE. -/
noncomputable def sectionwiseRelativeBaseChangeComplex :
    CochainComplex (PresheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj) ℤ where
  X j := sectionwiseRelativeBaseChangeTerm J g h j
  d i j :=
    { app U := (relativeBaseChangeCotangentComplex J g h U).d i j
      naturality k := (relativeBaseChangeCotangentRestriction J g h k).comm i j }
  shape i j hij := by
    refine PresheafOfModules.Hom.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
    exact ConcreteCategory.congr_hom
      ((relativeBaseChangeCotangentComplex J g h U).shape i j hij) x
  d_comp_d' i j k _ _ := by
    refine PresheafOfModules.Hom.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
    exact ConcreteCategory.congr_hom
      ((relativeBaseChangeCotangentComplex J g h U).d_comp_d i j k) x

/-- The value of `U ↦ Ω[R̄_•(U)⁄B(U)] ⊗ D(U)` over `U`. -/
theorem sectionwiseRelativeBaseChangeComplex_evaluation (U : Cᵒᵖ) :
    ((PresheafOfModules.evaluation _ U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (sectionwiseRelativeBaseChangeComplex J g h) =
      relativeBaseChangeCotangentComplex J g h U :=
  rfl

/-- The identification of `Ω[R_•(U)⁄B(U)] ⊗ D(U)` with `L_{D(U)/B(U)}` sends `1 ⊗ d r` to the
pure differential `1 ⊗ d r` of the cotangent complex. -/
theorem sectionsStandardCotangentComplexIso_hom_f_mk (U : Cᵒᵖ) (n : ℕ)
    (r : (CommAlgCat.standardResolution.{max u v w, max u v w} (B.obj.obj U)
      (sectionsAlgebra J h U)).left.obj (op ⦋n⦌)) :
    (CommAlgCat.standardCotangentComplexIso (sectionsTowerHom J g h U)).hom.f (-(n : ℤ))
        (CommAlgCat.augmentedCotangentMk (CommAlgCat.standardResolution.{max u v w, max u v w}
          (B.obj.obj U) (sectionsAlgebra J h U)).hom n r) =
      sectionsCotangentDifferential' J h U n r :=
  CommAlgCat.standardCotangentComplexIso_hom_f_mk (sectionsTowerHom J g h U) n r

/-- The first arrow `L_{D(U)/B(U)} ⟶ Ω[R̄_•(U)⁄B(U)] ⊗ D(U)` of the comparison of Remark 08SE
sends `1 ⊗ d r` to `1 ⊗ d` of the image of `r` under the pushout leg `R_•(U) ⟶ R̄_•(U)`. -/
theorem relativeBaseChangeCotangentLeg_f_mk (U : Cᵒᵖ) (n : ℕ)
    (r : (CommAlgCat.standardResolution.{max u v w, max u v w} (B.obj.obj U)
      (sectionsAlgebra J h U)).left.obj (op ⦋n⦌)) :
    (CommAlgCat.relativeBaseChangeCotangentLeg (sectionsTowerHom J g h U)).f (-(n : ℤ))
        ((CommAlgCat.standardCotangentComplexIso (sectionsTowerHom J g h U)).hom.f (-(n : ℤ))
          (CommAlgCat.augmentedCotangentMk (CommAlgCat.standardResolution.{max u v w, max u v w}
            (B.obj.obj U) (sectionsAlgebra J h U)).hom n r)) =
      CommAlgCat.augmentedCotangentMk (relativeBaseChangeAug J g h U) n
        ((CommAlgCat.relativeBaseChangeLeg (sectionsTowerHom J g h U)).app (op ⦋n⦌) r) := by
  have e := congrArg (fun φ => φ.f (-(n : ℤ)) (CommAlgCat.augmentedCotangentMk
      (CommAlgCat.standardResolution.{max u v w, max u v w} (B.obj.obj U)
        (sectionsAlgebra J h U)).hom n r))
    (Iso.hom_inv_id_assoc (CommAlgCat.standardCotangentComplexIso (sectionsTowerHom J g h U))
      (CommAlgCat.resolutionCotangentComplexMap _ _
        (CommAlgCat.relativeBaseChangeLeg (sectionsTowerHom J g h U))
        (CommAlgCat.relativeBaseChangeLeg_comp_hom (sectionsTowerHom J g h U))))
  exact e.trans (CommAlgCat.resolutionCotangentComplexMap_f_mk _ _
    (CommAlgCat.relativeBaseChangeLeg (sectionsTowerHom J g h U))
    (CommAlgCat.relativeBaseChangeLeg_comp_hom (sectionsTowerHom J g h U)) n r)

/-- The first arrow of the comparison of Remark 08SE on a pure differential of `L_{D(U)/B(U)}`. -/
theorem relativeBaseChangeCotangentLeg_sectionsCotangentDifferential (U : Cᵒᵖ) (n : ℕ)
    (r : (CommAlgCat.standardResolution.{max u v w, max u v w} (B.obj.obj U)
      (sectionsAlgebra J h U)).left.obj (op ⦋n⦌)) :
    (CommAlgCat.relativeBaseChangeCotangentLeg (sectionsTowerHom J g h U)).f (-(n : ℤ))
        (sectionsCotangentDifferential' J h U n r) =
      CommAlgCat.augmentedCotangentMk (relativeBaseChangeAug J g h U) n
        (CommAlgCat.canonicalBaseChangeMap.{max u v w, max u v w} (B.obj.obj U)
          (CommAlgCat.overBase (sectionsTowerHom J g h U)) (op ⦋n⦌) r) := by
  rw [← sectionsStandardCotangentComplexIso_hom_f_mk J g h U n r]
  exact relativeBaseChangeCotangentLeg_f_mk J g h U n r

/-- The first arrow `L_{D(U)/B(U)} ⟶ Ω[R̄_•(U)⁄B(U)] ⊗ D(U)` of the comparison of Remark 08SE,
with source written as the cotangent complex of the ring map on sections. -/
noncomputable def sectionsRelativeBaseChangeCotangentLeg (U : Cᵒᵖ) :
    CommAlgCat.cotangentComplex.{max u v w, max u v w} (B.obj.obj U) (sectionsAlgebra J h U) ⟶
      relativeBaseChangeCotangentComplex J g h U :=
  CommAlgCat.relativeBaseChangeCotangentLeg (sectionsTowerHom J g h U)

/-- `CategoryTheory.Sheaf.sectionsRelativeBaseChangeCotangentLeg` on a pure differential. -/
theorem sectionsRelativeBaseChangeCotangentLeg_f_mk (U : Cᵒᵖ) (n : ℕ)
    (r : (CommAlgCat.standardResolution.{max u v w, max u v w} (B.obj.obj U)
      (sectionsAlgebra J h U)).left.obj (op ⦋n⦌)) :
    (sectionsRelativeBaseChangeCotangentLeg J g h U).f (-(n : ℤ))
        (sectionsCotangentDifferential' J h U n r) =
      CommAlgCat.augmentedCotangentMk (relativeBaseChangeAug J g h U) n
        (CommAlgCat.canonicalBaseChangeMap.{max u v w, max u v w} (B.obj.obj U)
          (CommAlgCat.overBase (sectionsTowerHom J g h U)) (op ⦋n⦌) r) :=
  relativeBaseChangeCotangentLeg_sectionsCotangentDifferential J g h U n r

/-- The first arrows of the comparison of Remark 08SE commute with the restriction maps along
`U ⟶ V`. -/
theorem sectionsRelativeBaseChangeCotangentLeg_naturality {U V : Cᵒᵖ} (k : U ⟶ V) (n : ℕ) :
    (CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
        (sectionsRestrictionSquare J h k)).f (-(n : ℤ)) ≫
      (ModuleCat.restrictScalars (sectionsRestrictionSquare J h k).map).map
        ((sectionsRelativeBaseChangeCotangentLeg J g h V).f (-(n : ℤ))) =
    (sectionsRelativeBaseChangeCotangentLeg J g h U).f (-(n : ℤ)) ≫
      (relativeBaseChangeCotangentRestriction J g h k).f (-(n : ℤ)) := by
  refine sectionsCotangentComplex_hom_ext J h U n _ _ fun p => ?_
  have e1 := congrArg (fun x => (sectionsRelativeBaseChangeCotangentLeg J g h V).f (-(n : ℤ)) x)
    (squareCotangentComplexMap_sectionsCotangentDifferential' J h k n p)
  have e2 := sectionsRelativeBaseChangeCotangentLeg_f_mk J g h V n
    ((CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
      (sectionsRestrictionSquare J h k)).resolution (op ⦋n⦌) p)
  have e3 := relativeBaseChangeRestriction_canonicalBaseChangeMap J g h k (op ⦋n⦌) p
  have e4 := relativeBaseChangeCotangentRestriction_f_mk J g h k n
    (CommAlgCat.canonicalBaseChangeMap.{max u v w, max u v w} (B.obj.obj U)
      (CommAlgCat.overBase (sectionsTowerHom J g h U)) (op ⦋n⦌) p)
  have e5 := sectionsRelativeBaseChangeCotangentLeg_f_mk J g h U n p
  exact (e1.trans e2).trans ((congrArg
    (CommAlgCat.augmentedCotangentMk (relativeBaseChangeAug J g h V) n) e3.symm).trans
      (e4.symm.trans (congrArg (fun x => (relativeBaseChangeCotangentRestriction J g h k).f
        (-(n : ℤ)) x) e5.symm)))

/-- **The first arrow of the comparison of Remark 08SE, sectionwise**: the maps
`L_{D(U)/B(U)} ⟶ Ω[R̄_•(U)⁄B(U)] ⊗ D(U)` induced by the pushout legs `R_•(U) ⟶ R̄_•(U)`, as a map
of complexes of presheaves of `D`-modules. -/
noncomputable def sectionwiseRelativeBaseChangeLeg :
    sectionwiseCotangentModuleComplex J h ⟶ sectionwiseRelativeBaseChangeComplex J g h where
  f j :=
    { app U := (sectionsRelativeBaseChangeCotangentLeg J g h U).f j
      naturality {U V} k := by
        by_cases hj : 0 < j
        · exact (CommAlgCat.cotangentComplex_isZero_pos.{max u v w, max u v w} (B.obj.obj U)
            (sectionsAlgebra J h U) j hj).eq_of_src _ _
        · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by lia⟩
          exact sectionsRelativeBaseChangeCotangentLeg_naturality J g h k n }
  comm' i j _ := by
    refine PresheafOfModules.Hom.ext (funext fun U => ?_)
    exact (sectionsRelativeBaseChangeCotangentLeg J g h U).comm i j

end CategoryTheory.Sheaf

end
