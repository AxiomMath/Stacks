module

public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTerm
public import StacksFrontier.Deformation.PredeformationTangent.DifferentialLinear
public import StacksFrontier.Deformation.Schlessinger.AssociatedFunctor
public import StacksFrontier.Deformation.Schlessinger.Basic

/-!
# Linearity of the tangent space and differential at a point

Let `𝓕` be a category cofibered in groupoids over `𝒞_Λ` and let `x` be an object of its fibre
over the residue field. If `𝓕` satisfies Schlessinger's condition (S2), then the tangent space
`T_x 𝓕` of `𝓕` at `x` is a `k`-vector space, and for a morphism `φ : 𝓕 ⟶ 𝓖` of categories
cofibered in groupoids with `𝓖` also satisfying (S2) the differential `d_x φ` is `k`-linear.

## Main definitions

* `Deformation.tangentSpaceAtPointAddCommGroup` and `Deformation.tangentSpaceAtPointModule`: the
  natural `k`-vector space structure on the tangent space at a point.

## Main results

* `Deformation.schlessingerConditionS2_isomorphismClasses_objectsOverFunctor`: (S2) for the
  associated functor of isomorphism classes of the slice predeformation category at a point.
* `Deformation.mapIsomorphismClasses_isLinearMap_artinianDualNumbers`: linearity of the map of
  associated functors at the universe-lifted dual numbers.
* `Deformation.differentialAtPoint_isLinearMap`: the differential at a point is `k`-linear.

## Implementation notes

The vector space structure is the one of Tag 06IH, carried by
`Deformation.associatedTangentSpaceModule`, applied to the slice predeformation category
`Deformation.objectsOverFunctor` of Tag 06GU. Its two hypotheses are supplied by Tag 06SQ
(`Deformation.schlessingerConditionS2_objectsOverFunctor`, which passes (S2) to the slice) and
Tag 06I0 (`Deformation.schlessingerConditionS2_of_isIsomorphismClasses`, which passes it to the
associated functor); the special-fibre disjunct of the latter is discharged by Tag 06GU.

The linearity statement of Tag 06IJ is available in the library only for the Artinian algebras
whose carrier universe is that of the residue field, while the tangent space at a point uses
the universe-lifted dual numbers `Deformation.artinianDualNumbers`. So the naturality argument
of Tag 06IJ is re-run here against the lifted linear lift
`Deformation.associatedTangentSpaceModuleStructure`, using
`Deformation.isLinearMap_of_natural_at`, which is the naturality-implies-linearity step at an
arbitrary module in an arbitrary universe.

## References

* [Stacks Project, Tag 06IK](https://stacks.math.columbia.edu/tag/06IK)
-/

@[expose] public section

namespace Deformation

/-! ### Condition (S2) for the slice predeformation category at a point -/

section
open CategoryTheory

universe u v w u₁ v₁ u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type u₁} [Category.{v₁} F] {G : Type u₂} [Category.{v₂} G]

/-- **Stacks Project, Tag 06SQ.** Schlessinger's condition (S2) passes from a category
cofibered in groupoids to the associated functor of isomorphism classes of its slice
predeformation category at a point over the residue field. -/
@[stacks 06SQ "condition (S2) for the associated functor of a slice"]
theorem schlessingerConditionS2_isomorphismClasses_objectsOverFunctor
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (hS2 : SchlessingerConditionS2 p)
    (x : p.Fiber (residueFieldObject.{u, v, w} Λ k)) :
    SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses
        (BasedCategory.ofFunctor (objectsOverFunctor p x.1))
        (isPredeformationCategory_objectsOverFunctor p hp x).cofibered)) :=
  schlessingerConditionS2_of_isIsomorphismClasses
    (BasedCategory.ofFunctor (objectsOverFunctor p x.1))
    (isPredeformationCategory_objectsOverFunctor p hp x).cofibered
    (schlessingerConditionS2_objectsOverFunctor p x.1 hS2)
    (.inl (isPredeformationCategory_objectsOverFunctor p hp x))

/-! ### The vector space structure on the tangent space at a point -/

/-- **Stacks Project, Tag 06IK.** The additive group underlying the natural `k`-vector space
structure on the tangent space of a category cofibered in groupoids at a point over the
residue field, available when the category satisfies Schlessinger's condition (S2). -/
@[stacks 06IK "vector_space_structure"]
noncomputable instance tangentSpaceAtPointAddCommGroup
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    [hS2 : Fact (SchlessingerConditionS2 p)]
    (x : p.Fiber (residueFieldObject.{u, v, w} Λ k)) :
    AddCommGroup (tangentSpaceAtPoint.{u, v, w} p hp x) :=
  @associatedTangentSpaceAddCommGroup.{u, v, w} Λ k _ _ _
    (BasedCategory.ofFunctor (objectsOverFunctor p x.1))
    ⟨isPredeformationCategory_objectsOverFunctor p hp x⟩
    ⟨schlessingerConditionS2_isomorphismClasses_objectsOverFunctor p hp hS2.out x⟩

/-- **Stacks Project, Tag 06IK.** The natural action of the residue field on the tangent space
of a category cofibered in groupoids at a point over the residue field, available when the
category satisfies Schlessinger's condition (S2). -/
@[stacks 06IK "vector_space_structure"]
noncomputable instance tangentSpaceAtPointModule
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    [hS2 : Fact (SchlessingerConditionS2 p)]
    (x : p.Fiber (residueFieldObject.{u, v, w} Λ k)) :
    Module k (tangentSpaceAtPoint.{u, v, w} p hp x) :=
  @associatedTangentSpaceModule.{u, v, w} Λ k _ _ _
    (BasedCategory.ofFunctor (objectsOverFunctor p x.1))
    ⟨isPredeformationCategory_objectsOverFunctor p hp x⟩
    ⟨schlessingerConditionS2_isomorphismClasses_objectsOverFunctor p hp hS2.out x⟩

end

/-! ### Linearity of the differential at a point -/

section
open CategoryTheory

universe u v w u₁ v₁ u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **Stacks Project, Tag 06IJ.** The map induced on associated functors of isomorphism classes
by a morphism of predeformation categories is `k`-linear at the universe-lifted dual numbers,
when both associated functors satisfy (S2).

This is `Deformation.differential_isLinearMap` for the universe-lifted presentation of the
dual numbers used by the tangent space at a point. -/
@[stacks 06IJ "lifted dual numbers"]
theorem mapIsomorphismClasses_isLinearMap_artinianDualNumbers
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (h𝓕 : IsPredeformationCategory.{u, v, w} 𝓕.p)
    (h𝓖 : IsPredeformationCategory.{u, v, w} 𝓖.p)
    (hS2𝓕 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered)))
    (hS2𝓖 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered)))
    (φ : BasedFunctor 𝓕 𝓖) :
    letI : Fact (IsPredeformationCategory.{u, v, w} 𝓕.p) := ⟨h𝓕⟩
    letI : Fact (IsPredeformationCategory.{u, v, w} 𝓖.p) := ⟨h𝓖⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) := ⟨hS2𝓕⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) := ⟨hS2𝓖⟩
    IsLinearMap k (mapIsomorphismClasses h𝓕.cofibered h𝓖.cofibered φ
      (artinianDualNumbers.{u, w, v} Λ k)) := by
  let : Fact (IsPredeformationCategory.{u, v, w} 𝓕.p) := ⟨h𝓕⟩
  let : Fact (IsPredeformationCategory.{u, v, w} 𝓖.p) := ⟨h𝓖⟩
  let : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) := ⟨hS2𝓕⟩
  let : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) := ⟨hS2𝓖⟩
  let S := squareZeroExtensionArtinian.{u, w, max v w} Λ k
  let UF := S ⋙ isomorphismClasses 𝓕 h𝓕.cofibered
  let UG := S ⋙ isomorphismClasses 𝓖 h𝓖.cofibered
  let LF := associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕 hS2𝓕
  let LG := associatedTangentSpaceModuleStructure.{u, v, w} 𝓖 h𝓖 hS2𝓖
  let eF (M : FGModuleCat.{max v w} k) : (LF.functor.obj M : Type u₁) = UF.obj M :=
    congrArg (fun H : FGModuleCat.{max v w} k ⥤ Type u₁ => H.obj M) LF.forget_comp
  let eG (M : FGModuleCat.{max v w} k) : (LG.functor.obj M : Type u₂) = UG.obj M :=
    congrArg (fun H : FGModuleCat.{max v w} k ⥤ Type u₂ => H.obj M) LG.forget_comp
  let tset : ∀ M : FGModuleCat.{max v w} k, UF.obj M → UG.obj M := fun M z =>
    mapIsomorphismClasses h𝓕.cofibered h𝓖.cofibered φ (S.obj M) z
  have htset : ∀ {M N : FGModuleCat.{max v w} k} (f : M ⟶ N) (z : UF.obj M),
      tset N (UF.map f z) = UG.map f (tset M z) := fun f z =>
    mapIsomorphismClasses_naturality h𝓕.cofibered h𝓖.cofibered φ (S.map f) z
  let tmod : ∀ M : FGModuleCat.{max v w} k, LF.functor.obj M → LG.functor.obj M := fun M y =>
    cast (eG M).symm (tset M (cast (eF M) y))
  have htmod : ∀ {M N : FGModuleCat.{max v w} k} (f : M ⟶ N) (y : LF.functor.obj M),
      tmod N ((LF.functor.map f) y) = (LG.functor.map f) (tmod M y) := by
    intro M N f y
    dsimp only [tmod]
    rw [moduleFunctor_map_cast k LF.functor UF LF.forget_comp f y, htset f]
    simpa [eF, eG] using (congrArg (cast (eG N).symm) (moduleFunctor_map_cast k LG.functor UG
      LG.forget_comp f (cast (eG M).symm (tset M (cast (eF M) y))))).symm
  let A : FGModuleCat.{max v w} k := FGModuleCat.of k (ULift.{v} k)
  have hlin := isLinearMap_of_natural_at k LF.functor LG.functor tmod htmod A
  have hFcarrier := associatedTangentSpaceModuleStructure_carrier.{u, v, w} 𝓕 h𝓕 hS2𝓕
  have hGcarrier := associatedTangentSpaceModuleStructure_carrier.{u, v, w} 𝓖 h𝓖 hS2𝓖
  let DF : AddModuleData k (LF.functor.obj A) := ⟨inferInstance, inferInstance⟩
  let DG : AddModuleData k (LG.functor.obj A) := ⟨inferInstance, inferInstance⟩
  have hdiff (y : tangentSpaceArtinian.{u, w, v} Λ k (isomorphismClasses 𝓕 h𝓕.cofibered)) :
      mapIsomorphismClasses h𝓕.cofibered h𝓖.cofibered φ
          (artinianDualNumbers.{u, w, v} Λ k) y =
        cast hGcarrier (tmod A (cast hFcarrier.symm y)) := by
    change _ = cast hGcarrier
      (cast hGcarrier.symm (tset A (cast hFcarrier (cast hFcarrier.symm y))))
    rw [cast_symm_cancel hFcarrier y, cast_symm_cancel hGcarrier (tset A y)]
  have hFadd (y z : tangentSpaceArtinian.{u, w, v} Λ k
        (isomorphismClasses 𝓕 h𝓕.cofibered)) :
      cast hFcarrier.symm (y + z) = cast hFcarrier.symm y + cast hFcarrier.symm z := by
    exact cast_symm_add_rec hFcarrier DF y z
  have hFsmul (r : k) (y : tangentSpaceArtinian.{u, w, v} Λ k
        (isomorphismClasses 𝓕 h𝓕.cofibered)) :
      cast hFcarrier.symm (r • y) = r • cast hFcarrier.symm y := by
    exact cast_symm_smul_rec hFcarrier DF r y
  have hGadd (y z : LG.functor.obj A) :
      cast hGcarrier (y + z) = cast hGcarrier y + cast hGcarrier z := by
    exact cast_add_rec hGcarrier DG y z
  have hGsmul (r : k) (y : LG.functor.obj A) :
      cast hGcarrier (r • y) = r • cast hGcarrier y := by
    exact cast_smul_rec hGcarrier DG r y
  constructor
  · intro y z
    rw [hdiff, hdiff, hdiff, hFadd, hlin.map_add, hGadd]
  · intro r y
    rw [hdiff, hdiff, hFsmul, hlin.map_smul, hGsmul]

end

section
open CategoryTheory

universe u v w u₁ v₁ u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type u₁} [Category.{v₁} F] {G : Type u₂} [Category.{v₂} G]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
variable {q : G ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}

/-- **Stacks Project, Tag 06IK.** If both categories cofibered in groupoids satisfy
Schlessinger's condition (S2), then the differential of a morphism between them at a point over
the residue field is `k`-linear for the natural vector space structures on the tangent spaces
at that point and its image. -/
@[stacks 06IK "differential_at_point_linear"]
theorem differentialAtPoint_isLinearMap
    (hp : IsCofiberedInGroupoids p)
    (hq : IsCofiberedInGroupoids q)
    (hS2p : SchlessingerConditionS2 p)
    (hS2q : SchlessingerConditionS2 q)
    (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    (x : p.Fiber (residueFieldObject.{u, v, w} Λ k)) :
    letI : Fact (SchlessingerConditionS2 p) := ⟨hS2p⟩
    letI : Fact (SchlessingerConditionS2 q) := ⟨hS2q⟩
    IsLinearMap k (differentialAtPoint.{u, v, w} hp hq φ x) := by
  let : Fact (SchlessingerConditionS2 p) := ⟨hS2p⟩
  let : Fact (SchlessingerConditionS2 q) := ⟨hS2q⟩
  exact mapIsomorphismClasses_isLinearMap_artinianDualNumbers.{u, v, w}
    (BasedCategory.ofFunctor (objectsOverFunctor p x.1))
    (BasedCategory.ofFunctor (objectsOverFunctor q (imagePoint φ x).1))
    (isPredeformationCategory_objectsOverFunctor p hp x)
    (isPredeformationCategory_objectsOverFunctor q hq (imagePoint φ x))
    (schlessingerConditionS2_isomorphismClasses_objectsOverFunctor p hp hS2p x)
    (schlessingerConditionS2_isomorphismClasses_objectsOverFunctor q hq hS2q
      (imagePoint φ x))
    (sliceBasedFunctorAtPoint φ x)

end

end Deformation
