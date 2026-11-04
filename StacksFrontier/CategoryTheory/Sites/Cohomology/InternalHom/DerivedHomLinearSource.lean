module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomAdditive
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomTriangulated

/-!
# Derived internal Hom is linear over the structure sheaf in its contravariant variable

Let `(𝒞, 𝒪)` be a ringed site and `M ∈ D(𝒪)`. Then `R𝑆heafHom_𝒪(-, M) : D(𝒪)ᵒᵖ ⥤ D(𝒪)` carries
multiplication by a compatible family of local sections of `𝒪` to multiplication by that same
family. The statement in the covariant variable is
`AlgebraicGeometry.RingedSite.derivedSheafHom_map_globalSectionToEnd`.

## Main results

* `AlgebraicGeometry.RingedSite.homMap_globalSectionToEnd_left`: at the level of internal Hom
  complexes, the map induced by multiplication by a global section in the *source* is
  multiplication by that section.
* `AlgebraicGeometry.RingedSite.derivedSheafHom_map_globalSectionToEnd_source`: the same for the
  derived internal Hom.

## References

* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 0997](https://stacks.math.columbia.edu/tag/0997)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex
open scoped IsMulCommutative

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

attribute [local instance] linearCatCenterRingSheaf

/-- **Multiplication by a global section passes through the internal Hom complex, in the
source.** The map of internal Hom complexes induced by multiplication by a compatible family of
local sections of `𝒪` in the source is multiplication by that same family. -/
lemma homMap_globalSectionToEnd_left
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj ⋙ forget RingCat).sections) :
    homMap X
        (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
          𝟙 A) (𝟙 B) =
      Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
        𝟙 (sheafHomComplex X A B).obj := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  rintro ⟨U⟩
  ext s : 2
  apply ((sheafHomComplex X A B).sectionsEquiv U n).injective
  rw [homMap_f, sectionsEquiv_homMapHom]
  refine Cochain.ext _ _ fun p q hpq => ?_
  refine sliceHom_ext X fun W g x => ?_
  have hcomp : ∀ {P Q R : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)}
      (φ : P ⟶ Q) (ψ : Q ⟶ R) (V : (Over U)ᵒᵖ) (y : P.val.obj V),
      ((φ ≫ ψ).val.app V) y = (ψ.val.app V) ((φ.val.app V) y) := fun _ _ _ _ => rfl
  have hR0 : (ModuleCat.Hom.hom
      (((Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
          𝟙 (sheafHomComplex X A B).obj).f n).val.app (op U))) s =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) from a.val (op U)) • s :=
    rfl
  have hleft : (ModuleCat.Hom.hom
      ((SheafOfModules.Hom.over
        ((Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
          𝟙 A).f p) U).val.app (op (Over.mk g)))) x =
      (show ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj.obj (op (Over.mk g)) from
        a.val (op W)) • x := rfl
  have hsec :
      (show ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj.obj (op (Over.mk g)) from
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map g.op
          (show (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) from a.val (op U))) =
      (show ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj.obj (op (Over.mk g)) from
        a.val (op W)) :=
    a.property g.op
  rw [cochainConj_v, hcomp, hcomp, hleft, map_smul,
    hR0, (sheafHomComplex X A B).sectionsEquiv_smul U
      (show (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) from a.val (op U))
      n p q hpq s g x, hsec]
  rfl

/-- A contravariant functor carries multiplication by a scalar to multiplication by that scalar
at an object as soon as it does so at an isomorphic object. -/
theorem map_op_smul_id_of_iso {R : Type*} [Semiring R] {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D] (F : Cᵒᵖ ⥤ D) (r : R) {M N : C}
    (e : M ≅ N) (h : F.map (r • 𝟙 M).op = r • 𝟙 (F.obj (op M))) :
    F.map (r • 𝟙 N).op = r • 𝟙 (F.obj (op N)) := by
  have he : (r • 𝟙 N : N ⟶ N) = e.inv ≫ (r • 𝟙 M) ≫ e.hom := by
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Iso.inv_hom_id]
  rw [he, op_comp, op_comp, F.map_comp, F.map_comp, h, Linear.comp_smul, Linear.smul_comp,
    Category.comp_id, ← F.map_comp, ← op_comp, e.inv_hom_id, op_id, F.map_id]

/-- A natural endomorphism which is multiplication by a scalar at one object is multiplication by
that scalar at every isomorphic object. -/
theorem app_eq_smul_id_of_iso {R : Type*} [Semiring R] {C D : Type*} [Category C] [Category D]
    [Preadditive D] [Linear R D] {F : C ⥤ D} (τ : F ⟶ F) (r : R) {M N : C} (e : M ≅ N)
    (h : τ.app M = r • 𝟙 (F.obj M)) : τ.app N = r • 𝟙 (F.obj N) := by
  refine (cancel_epi (F.map e.hom)).mp ?_
  rw [τ.naturality, h, Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **Derived internal Hom into a fixed object carries multiplication by a global section to
multiplication by that section.** This is the `𝒪`-linearity of `R𝑆heafHom_𝒪(-, M)` in its
contravariant variable, at the central endomorphisms given by compatible families of local
sections of `𝒪`. -/
theorem derivedSheafHom_map_globalSectionToEnd_source
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj ⋙ forget RingCat).sections)
    (A M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedSheafHomBifunctor X).map
        (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
          𝟙 A).op).app M =
      Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
        𝟙 (((derivedSheafHomBifunctor X).obj (op A)).obj M) := by
  have hmodel :
      ∀ (A₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))),
      ((derivedSheafHomBifunctor X).map
          (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
            𝟙 (DerivedCategory.Q.obj A₀)).op).app N =
        Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
          𝟙 (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A₀))).obj N) := by
    intro A₀ N
    have : (kInjectiveModel X N).IsKInjective := isKInjective_kInjectiveModel X N
    refine app_eq_smul_id_of_iso _ _ (kInjectiveModelIso X N) ?_
    have hQ : ∀ C : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
        DerivedCategory.Q.map
          (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
            𝟙 C) =
        Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a •
          𝟙 (DerivedCategory.Q.obj C) := fun C => by
      rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
    refine eq_smul_id_of_mono (c := (derivedSheafHomComparison X A₀ (kInjectiveModel X N)).hom) ?_
    rw [← hQ A₀, derivedSheafHomComparison_naturality_id,
      ← Stacks.Cohomology.InternalHom.homMap_eq_sheafHomComplexMap]
    simp only [homMap_globalSectionToEnd_left, hQ]
  exact map_op_smul_id_of_iso ((derivedSheafHomBifunctor X).flip.obj M) _
    (DerivedCategory.Q.objObjPreimageIso A) (hmodel (DerivedCategory.Q.objPreimage A) M)

end Derived

end AlgebraicGeometry.RingedSite

end
