module

public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentInverseImageBaseChange
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentOfSurjection

/-!
# Naturality of the inverse image of the naive cotangent complex in the base ring, degree `-1`

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi and `a = φ ≫ a'` a factorisation of a homomorphism
`a : A ⟶ B` of sheaves of commutative rings on `D` through `a' : A' ⟶ B`. This file proves that
the change of base ring `NL_{B/A} ⟶ NL_{B/A'}` of Stacks 08TX and the identification
`f⁻¹ NL_{B/A} ≅ NL_{f⁻¹B/f⁻¹A}` of Stacks 08TZ commute in degree `-1`, and assembles the two
degrees into the naturality of the identification of complexes.

## Main results

* `Stacks.Sites.FreeAlgebra.inverseImageFreeAlgebraInv_comp_map_canonicalFreeAlgebraMapOfSquare`:
  the identification `f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]` is natural in the coefficients.
* `Sheaves.RingedToposModules.inverseImage_conormalClassHom_comp_inverseImageConormalIso_hom`:
  the comparison `f⁻¹(ℐ/ℐ²) ≅ ℐ'/ℐ'²` sends the inverse image of the class of a local section of
  `ℐ` to the class of its image in `ℐ' ≅ f⁻¹ℐ`.
* `Stacks.Sheaves.RingedToposModules.inverseImage_idealSheafSetsMap_comp_inverseImageIdealIso`:
  the identification `f⁻¹ℐ ≅ ℐ'` is natural in the presentation.
* `Stacks.SheafOfModules.inverseImageNaiveCotangentNegOneIso_naturality`: **Stacks 08TZ is
  natural in the base ring, in degree `-1`.**
* `Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso_naturality`: **Stacks 08TZ is
  natural in the base ring**, as an identity of chain maps.
* `Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso_conormalToNaiveCotangentComplex`:
  the identification of Stacks 08TZ is compatible with the chain map `η : (I/I²)[1] ⟶ NL_{B/A}`
  of a locally surjective `A ⟶ B`, through `f⁻¹(I/I²) ≅ I'/I'²`
  (`Stacks.SheafOfModules.inverseImageConormalSheafIso`).

## Implementation notes

Morphisms out of the conormal sheaf of a presentation are determined by their restrictions to the
kernel ideal, and the inverse image of the identification `f⁻¹ℐ ≅ ℐ'` is an isomorphism, so the
degree `-1` statement is checked after precomposition with `f⁻¹ℐ ≅ ℐ'`, on local sections of the
underlying sheaves of sets. Values of morphisms into a restriction of scalars are compared typed in
the sections of the unrestricted sheaf of modules (the `@Eq` statements below), which keeps the
kernel away from the two spellings of the same carrier.

## References

* [Stacks Project, Tag 08TZ](https://stacks.math.columbia.edu/tag/08TZ)
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.Sites.FreeAlgebra

section CoefficientNaturality

universe w w' v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J CommRingCat.{w}] [HasWeakSheafify K CommRingCat.{w'}]

/-- The morphism `A[B] ⟶ A'[B]` attached to a morphism of coefficients `φ : A ⟶ A'` fixes the
variables, on sheaves of sets. -/
theorem variableSheaf_comp_map_canonicalFreeAlgebraMapOfSquare_id
    {A A' : Sheaf J CommRingCat.{w}} (B : Sheaf J CommRingCat.{w}) (φ : A ⟶ A') :
    variableSheaf J A B ≫ (sheafCompose J (forget CommRingCat.{w})).map
        (Stacks.SheafOfModules.canonicalFreeAlgebraMapOfSquare J A A' B B φ (𝟙 B)) =
      variableSheaf J A' B := by
  refine Sheaf.hom_ext ((Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_freeAlgebraMapOfSquare
    J A A' _ _ φ _).trans ?_)
  simp only [Stacks.SheafOfModules.underlyingPresheafMap, CategoryTheory.Functor.map_id,
    Functor.whiskerRight_id']
  exact Category.id_comp _

variable {J K} (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  {A A' : Sheaf K CommRingCat.{w'}} (B : Sheaf K CommRingCat.{w'}) (φ : A ⟶ A')

/-- **The identification `f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]` is natural in the coefficients.** -/
theorem inverseImageFreeAlgebraInv_comp_map_canonicalFreeAlgebraMapOfSquare :
    inverseImageFreeAlgebraInv f A B ≫ f.inverseImageRing.map
        (Stacks.SheafOfModules.canonicalFreeAlgebraMapOfSquare K A A' B B φ (𝟙 B)) =
      Stacks.SheafOfModules.canonicalFreeAlgebraMapOfSquare J (f.inverseImageRing.obj A)
          (f.inverseImageRing.obj A') (f.inverseImageRing.obj B) (f.inverseImageRing.obj B)
          (f.inverseImageRing.map φ) (𝟙 _) ≫
        inverseImageFreeAlgebraInv f A' B := by
  refine freeAlgebraSheaf_hom_ext J _ _ _ ?_ ?_
  · rw [← Category.assoc, coefficientMap_comp_inverseImageFreeAlgebraInv, ← Functor.map_comp,
      Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare,
      Functor.map_comp, ← Category.assoc,
      Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare,
      Category.assoc, coefficientMap_comp_inverseImageFreeAlgebraInv]
  · have key : variableSheaf J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B) ≫
          (sheafCompose J (forget CommRingCat.{w})).map (inverseImageFreeAlgebraInv f A B ≫
            f.inverseImageRing.map
              (Stacks.SheafOfModules.canonicalFreeAlgebraMapOfSquare K A A' B B φ (𝟙 B))) =
        variableSheaf J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B) ≫
          (sheafCompose J (forget CommRingCat.{w})).map
            (Stacks.SheafOfModules.canonicalFreeAlgebraMapOfSquare J (f.inverseImageRing.obj A)
              (f.inverseImageRing.obj A') (f.inverseImageRing.obj B) (f.inverseImageRing.obj B)
              (f.inverseImageRing.map φ) (𝟙 _) ≫
            inverseImageFreeAlgebraInv f A' B) := by
      rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc,
        variableSheaf_comp_inverseImageFreeAlgebraInv,
        variableSheaf_comp_map_canonicalFreeAlgebraMapOfSquare_id,
        variableSheaf_comp_inverseImageFreeAlgebraInv, MorphismOfTopoi.inverseImageRing_map_forget]
      exact (f.inverseImage.map_comp _ _).symm.trans (congrArg f.inverseImage.map
        (variableSheaf_comp_map_canonicalFreeAlgebraMapOfSquare_id K B φ))
    exact congrArg Sheaf.homEquiv key

/-- **The identification `f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]` is natural in the coefficients**, in the
direction `f⁻¹(A[B]) ⟶ (f⁻¹A)[f⁻¹B]`. -/
theorem map_canonicalFreeAlgebraMapOfSquare_comp_inverseImageFreeAlgebraHom :
    f.inverseImageRing.map
        (Stacks.SheafOfModules.canonicalFreeAlgebraMapOfSquare K A A' B B φ (𝟙 B)) ≫
      inverseImageFreeAlgebraHom f A' B =
    inverseImageFreeAlgebraHom f A B ≫
      Stacks.SheafOfModules.canonicalFreeAlgebraMapOfSquare J (f.inverseImageRing.obj A)
          (f.inverseImageRing.obj A') (f.inverseImageRing.obj B) (f.inverseImageRing.obj B)
          (f.inverseImageRing.map φ) (𝟙 _) := by
  rw [← Category.id_comp (f.inverseImageRing.map
      (Stacks.SheafOfModules.canonicalFreeAlgebraMapOfSquare K A A' B B φ (𝟙 B))),
    ← inverseImageFreeAlgebraHom_comp_inv f A B]
  simp only [Category.assoc]
  rw [← Category.assoc (inverseImageFreeAlgebraInv f A B),
    inverseImageFreeAlgebraInv_comp_map_canonicalFreeAlgebraMapOfSquare, Category.assoc,
    inverseImageFreeAlgebraInv_comp_hom, Category.comp_id]

end CoefficientNaturality

end Stacks.Sites.FreeAlgebra

namespace Stacks.Sites.Conormal

section KernelSetsMap

universe t v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v t})]
  {A₁ A₂ B₁ B₂ : Sheaf J CommRingCat.{max u v t}}
  (α₁ : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) A₁ ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) B₁)
  (α₂ : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) A₂ ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) B₂)
  (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) A₁ ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) A₂)
  (β : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) B₁ ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) B₂)
  (hsq : ψ ≫ α₂ = α₁ ≫ β)

omit [J.HasSheafCompose (forget AddCommGrpCat.{max u v t})] in
include hsq in
/-- A section of the kernel of `α₁` is carried by `ψ` into the kernel of `α₂`. -/
lemma app_mem_idealSheaf (V : Cᵒᵖ) (x : ↥((idealSheaf.{t, v, u} J α₁).val.obj V)) :
    ψ.hom.app V x.1 ∈ LinearMap.ker
      ((presentationModuleHom.{t, v, u} J α₂).val.app V).hom := by
  change α₂.hom.app V (ψ.hom.app V x.1) = 0
  exact (congrArg (fun g => g.hom.app V x.1) hsq).trans
    ((congrArg (β.hom.app V) (x.2 : α₁.hom.app V x.1 = 0)).trans (map_zero _))

/-- **The map of kernel ideals induced by a commutative square**, on underlying sheaves of sets:
a local section `x` of `Ker α₁` goes to `ψ x`. -/
noncomputable def idealSheafSetsMap :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} A₁)).obj
        (idealSheaf.{t, v, u} J α₁) ⟶
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} A₂)).obj
        (idealSheaf.{t, v, u} J α₂) :=
  ObjectProperty.homMk
    { app := fun V => TypeCat.ofHom (fun x : ↥((idealSheaf.{t, v, u} J α₁).val.obj V) =>
          (⟨ψ.hom.app V x.1, app_mem_idealSheaf.{t, v, u} J α₁ α₂ ψ β hsq V x⟩ :
            ↥((idealSheaf.{t, v, u} J α₂).val.obj V)))
      naturality := fun V W g => by
        ext x
        have h := ConcreteCategory.congr_hom (ψ.hom.naturality g)
          (x : ↥((idealSheaf.{t, v, u} J α₁).val.obj V)).1
        exact Subtype.ext h }

/-- The map of kernel ideals acts on a local section by `ψ`. -/
lemma idealSheafSetsMap_app (V : Cᵒᵖ) (x : ↥((idealSheaf.{t, v, u} J α₁).val.obj V)) :
    ((idealSheafSetsMap.{t, v, u} J α₁ α₂ ψ β hsq).hom.app V x).1 = ψ.hom.app V x.1 :=
  rfl

/-- The map of kernel ideals followed by the kernel inclusion is the kernel inclusion followed
by `ψ`, on underlying sheaves of sets. -/
lemma idealSheafSetsMap_comp_kerIota :
    idealSheafSetsMap.{t, v, u} J α₁ α₂ ψ β hsq ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} A₂)).map
          (SheafOfModules.kerIota (presentationModuleHom.{t, v, u} J α₂)) =
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} A₁)).map
          (SheafOfModules.kerIota (presentationModuleHom.{t, v, u} J α₁)) ≫
        (sheafCompose J (forget RingCat.{max u v t})).map ψ :=
  rfl

end KernelSetsMap

end Stacks.Sites.Conormal

namespace Stacks.Sites.Conormal

section TypedValuesComp

universe t v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v t})]

/-- A morphism into a restriction of scalars followed by a morphism of the unrestricted sheaves
of modules, read on underlying sheaves of sets, acts on local sections as the composite does. -/
lemma sectionsFunctor_map_moduleSheafFunctor_map_comp_eqToHom_comp
    {R R' : Sheaf J RingCat.{max u v t}} (α : R ⟶ R') {M : SheafOfModules.{max u v t} R}
    {N N' : SheafOfModules.{max u v t} R'} (z : M ⟶ (SheafOfModules.restrictScalars α).obj N)
    (h : N ⟶ N') (V : Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor J V).obj ((Sheaf.moduleSheafFunctor R).obj M)) :
    @Eq ↥(N'.val.obj V)
      ((Sheaf.sectionsFunctor J V).map ((Sheaf.moduleSheafFunctor R).map z ≫
        eqToHom (Stacks.Sheaves.RingedToposModules.moduleSheaf_restrictScalars α N) ≫
          (Sheaf.moduleSheafFunctor R').map h) x)
      (h.val.app V (z.val.app V x)) :=
  rfl

/-- A morphism of sheaves of sets followed by a morphism into a restriction of scalars, read on
underlying sheaves of sets, acts on local sections as the composite does. -/
lemma sectionsFunctor_map_comp_moduleSheafFunctor_map_comp_eqToHom
    {R R' : Sheaf J RingCat.{max u v t}} (α : R ⟶ R') {M : SheafOfModules.{max u v t} R}
    {N : SheafOfModules.{max u v t} R'} {X : Sheaf J (Type (max u v t))}
    (s : X ⟶ (Sheaf.moduleSheafFunctor R).obj M)
    (z : M ⟶ (SheafOfModules.restrictScalars α).obj N) (V : Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor J V).obj X) :
    @Eq ↥(N.val.obj V)
      ((Sheaf.sectionsFunctor J V).map (s ≫ (Sheaf.moduleSheafFunctor R).map z ≫
        eqToHom (Stacks.Sheaves.RingedToposModules.moduleSheaf_restrictScalars α N)) x)
      (z.val.app V ((Sheaf.sectionsFunctor J V).map s x)) :=
  rfl

/-- Two composites of morphisms of underlying sheaves of sets, the first through a restriction
of scalars and a morphism of unrestricted sheaves of modules, the second through a morphism of
sheaves of sets and a restriction of scalars, agree once they agree on local sections. -/
lemma moduleSheafFunctor_map_comp_eqToHom_comp_eq_of_app
    {R R' R₂ : Sheaf J RingCat.{max u v t}} (α : R ⟶ R') (α₂ : R₂ ⟶ R')
    {M : SheafOfModules.{max u v t} R} {N N' : SheafOfModules.{max u v t} R'}
    {M₂ : SheafOfModules.{max u v t} R₂}
    (z : M ⟶ (SheafOfModules.restrictScalars α).obj N) (h : N ⟶ N')
    (s : (Sheaf.moduleSheafFunctor R).obj M ⟶ (Sheaf.moduleSheafFunctor R₂).obj M₂)
    (z₂ : M₂ ⟶ (SheafOfModules.restrictScalars α₂).obj N')
    (H : ∀ (V : Cᵒᵖ) (x : (Sheaf.sectionsFunctor J V).obj ((Sheaf.moduleSheafFunctor R).obj M)),
      @Eq ↥(N'.val.obj V) (h.val.app V (z.val.app V x))
        (z₂.val.app V ((Sheaf.sectionsFunctor J V).map s x))) :
    (Sheaf.moduleSheafFunctor R).map z ≫
        eqToHom (Stacks.Sheaves.RingedToposModules.moduleSheaf_restrictScalars α N) ≫
          (Sheaf.moduleSheafFunctor R').map h =
      s ≫ (Sheaf.moduleSheafFunctor R₂).map z₂ ≫
        eqToHom (Stacks.Sheaves.RingedToposModules.moduleSheaf_restrictScalars α₂ N') :=
  Sheaf.hom_ext_sections H

end TypedValuesComp

end Stacks.Sites.Conormal

namespace Stacks.Sheaves.RingedToposModules

section ConormalSquareClass

universe w' v' u'

open Stacks.Sites.Conormal

attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget AddCommGrpCat.{max u' v' w'})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u' v' w'} RingCat.{max u' v' w'})]
  {S₁ S₂ T : Sheaf K CommRingCat.{max u' v' w'}} (p₁ : S₁ ⟶ T) (p₂ : S₂ ⟶ T) (Ψ : S₁ ⟶ S₂)
  (hsq : Ψ ≫ p₂ = p₁ ≫ 𝟙 T)

omit [K.HasSheafCompose (forget AddCommGrpCat.{max u' v' w'})] in
include hsq in
/-- The square `Ψ ≫ p₂ = p₁` of ring maps underlying a commutative triangle of sheaves of
commutative rings. -/
lemma presentationRingHom_square :
    presentationRingHom.{w', v', u'} K Ψ ≫ presentationRingHom.{w', v', u'} K p₂ =
      presentationRingHom.{w', v', u'} K p₁ ≫ 𝟙 _ := by
  rw [Category.comp_id]
  exact ((Stacks.forgetCommRingSheaf.{v', u', max u' v' w'} K).map_comp Ψ p₂).symm.trans
    (congrArg (Stacks.forgetCommRingSheaf.{v', u', max u' v' w'} K).map
      (hsq.trans (Category.comp_id p₁)))

variable [Presheaf.IsLocallySurjective K p₁.hom] [Presheaf.IsLocallySurjective K p₂.hom]

/-- The map `ℐ₁/ℐ₁² ⟶ ℐ₂/ℐ₂²` of conormal sheaves attached to a triangle `Ψ ≫ p₂ = p₁`, as a
morphism of sheaves of modules over the common target. -/
noncomputable abbrev conormalModuleMapOfTriangle :
    conormalSheaf.{v', u', max u' v' w', w'} K S₁ T p₁ ⟶
      conormalModule.{w', v', u'} K p₂ :=
  conormalSheafMapOfSquare.{v', u', max u' v' w', w'} K S₁ S₂ T T p₁ p₂ Ψ (𝟙 T) hsq

/-- **The map of conormal sheaves attached to a triangle, on classes**: it sends the class of
a local section `x` of the kernel ideal of `p₁` to the class of `Ψ x`. -/
lemma conormalSheafMapOfSquare_conormalClassHom_app (V : Dᵒᵖ)
    (x : (Sheaf.sectionsFunctor K V).obj ((Sheaf.moduleSheafFunctor
      (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} S₁)).obj
        (idealSheaf.{w', v', u'} K (presentationRingHom.{w', v', u'} K p₁)))) :
    @Eq ↥((conormalModule.{w', v', u'} K p₂).val.obj V)
      ((conormalModuleMapOfTriangle.{w', v', u'} p₁ p₂ Ψ hsq).val.app V
        ((conormalClassHom.{w', v', u'} p₁).val.app V x))
      ((conormalClassHom.{w', v', u'} p₂).val.app V
        ((Sheaf.sectionsFunctor K V).map (idealSheafSetsMap.{w', v', u'} K
          (presentationRingHom.{w', v', u'} K p₁)
          (presentationRingHom.{w', v', u'} K p₂) (presentationRingHom.{w', v', u'} K Ψ) (𝟙 _)
          (presentationRingHom_square.{w', v', u'} p₁ p₂ Ψ hsq)) x)) := by
  have hy₁ := coe_mem_kernelIdeal.{w', v', u'} K p₁ (presentationRingHom.{w', v', u'} K p₁) rfl V x
  have h₁ := conormalModuleHomEquivOf_app_conormalClass.{w', v', u'} K p₁
    (presentationRingHom.{w', v', u'} K p₁) rfl S₁ (𝟙 S₁) _ (𝟙 _) V x ⟨x.1, hy₁⟩ rfl
  have h₂ := conormalSheafMapOfSquare_conormalClass.{v', u', max u' v' w', w'} K S₁ S₂
    S₁ S₂ T T (𝟙 S₁) (𝟙 S₂) p₁ p₂ Ψ (𝟙 T) hsq V ⟨x.1, hy₁⟩
  let y := (idealSheafSetsMap.{w', v', u'} K (presentationRingHom.{w', v', u'} K p₁)
    (presentationRingHom.{w', v', u'} K p₂) (presentationRingHom.{w', v', u'} K Ψ) (𝟙 _)
    (presentationRingHom_square.{w', v', u'} p₁ p₂ Ψ hsq)).hom.app V x
  have hy₂ := coe_mem_kernelIdeal.{w', v', u'} K p₂ (presentationRingHom.{w', v', u'} K p₂) rfl V y
  have h₃ := conormalModuleHomEquivOf_app_conormalClass.{w', v', u'} K p₂
    (presentationRingHom.{w', v', u'} K p₂) rfl S₂ (𝟙 S₂) _ (𝟙 _) V y ⟨y.1, hy₂⟩ rfl
  exact ((congrArg _ h₁).trans h₂).trans h₃.symm

/-- **The map of conormal sheaves attached to a triangle, on classes**, as morphisms of
underlying sheaves of sets. -/
lemma moduleSheafFunctor_map_conormalClassHom_comp_conormalSheafMapOfSquare :
    (Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} S₁)).map
        (conormalClassHom.{w', v', u'} p₁) ≫
      eqToHom (moduleSheaf_restrictScalars (presentationRingHom.{w', v', u'} K p₁)
        (conormalModule.{w', v', u'} K p₁)) ≫
      (Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} T)).map
        (conormalModuleMapOfTriangle.{w', v', u'} p₁ p₂ Ψ hsq) =
    idealSheafSetsMap.{w', v', u'} K (presentationRingHom.{w', v', u'} K p₁)
        (presentationRingHom.{w', v', u'} K p₂) (presentationRingHom.{w', v', u'} K Ψ) (𝟙 _)
        (presentationRingHom_square.{w', v', u'} p₁ p₂ Ψ hsq) ≫
      (Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} S₂)).map
        (conormalClassHom.{w', v', u'} p₂) ≫
      eqToHom (moduleSheaf_restrictScalars (presentationRingHom.{w', v', u'} K p₂)
        (conormalModule.{w', v', u'} K p₂)) :=
  moduleSheafFunctor_map_comp_eqToHom_comp_eq_of_app.{w', v', u'} K
    (presentationRingHom.{w', v', u'} K p₁) (presentationRingHom.{w', v', u'} K p₂)
    (conormalClassHom.{w', v', u'} p₁) (conormalModuleMapOfTriangle.{w', v', u'} p₁ p₂ Ψ hsq)
    (idealSheafSetsMap.{w', v', u'} K (presentationRingHom.{w', v', u'} K p₁)
      (presentationRingHom.{w', v', u'} K p₂) (presentationRingHom.{w', v', u'} K Ψ) (𝟙 _)
      (presentationRingHom_square.{w', v', u'} p₁ p₂ Ψ hsq))
    (conormalClassHom.{w', v', u'} p₂)
    (conormalSheafMapOfSquare_conormalClassHom_app p₁ p₂ Ψ hsq)

end ConormalSquareClass

end Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.RingedToposModules

section InverseImageIdealNaturality

universe w w' v u v' u'

open Stacks.Sites.Conormal

attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{max u' v' w'})]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u' v' w'} RingCat.{max u' v' w'})]
  (f : MorphismOfTopoi (Sheaf J (Type (max u v w))) (Sheaf K (Type (max u' v' w'))))
  {S₁ S₂ T : Sheaf K CommRingCat.{max u' v' w'}} (p₁ : S₁ ⟶ T) (p₂ : S₂ ⟶ T) (Ψ : S₁ ⟶ S₂)
  (hsq : Ψ ≫ p₂ = p₁ ≫ 𝟙 T)

omit [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{max u' v' w'})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u' v' w'} RingCat.{max u' v' w'})] in
include hsq in
/-- The inverse image of a commutative triangle of ring maps, at the spellings of the
presentations of the inverse image. -/
lemma inverseImagePresentationRingHom_square :
    presentationRingHom.{w, v, u} J (f.inverseImageRing.map Ψ) ≫
        inverseImagePresentationRingHom.{w, w', v, u, v', u'} f p₂ =
      inverseImagePresentationRingHom.{w, w', v, u, v', u'} f p₁ ≫ 𝟙 _ := by
  have hJ : f.inverseImageRing.map Ψ ≫ f.inverseImageRing.map p₂ =
      f.inverseImageRing.map p₁ ≫ 𝟙 _ := by
    rw [← Functor.map_comp, hsq, Category.comp_id, Category.comp_id]
  change _ ≫ Stacks.Sheaves.ToposPushforward.inverseImageRingMap f
      (presentationRingHom.{w', v', u'} K p₂) =
    Stacks.Sheaves.ToposPushforward.inverseImageRingMap f
      (presentationRingHom.{w', v', u'} K p₁) ≫ _
  rw [inverseImageRingMap_presentationRingHom.{w, w', v, u, v', u'} f p₁,
    inverseImageRingMap_presentationRingHom.{w, w', v, u, v', u'} f p₂]
  exact presentationRingHom_square.{w, v, u} _ _ _ hJ

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u' v' w'} RingCat.{max u' v' w'})] in
/-- The identification `f⁻¹ℐ ≅ ℐ'` followed by the kernel inclusion of the inverse image is the
inverse image of the kernel inclusion, on underlying sheaves of sets. -/
lemma moduleSheafFunctor_map_inverseImageIdealIso_hom_comp_kerIota :
    (Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj S₁))).map
        (inverseImageIdealIso.{w, w', v, u, v', u'} f p₁).hom ≫
      (Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj S₁))).map
        (SheafOfModules.kerIota (presentationModuleHom.{w, v, u} J
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f p₁))) =
    f.inverseImage.map ((Sheaf.moduleSheafFunctor
        (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} S₁)).map
      (SheafOfModules.kerIota (presentationModuleHom.{w', v', u'} K
        (presentationRingHom.{w', v', u'} K p₁)))) := by
  have h : (Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj S₁))).map
        (inverseImageIdealIso.{w, w', v, u, v', u'} f p₁).hom ≫
      (Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj S₁))).map
        (SheafOfModules.kerIota (presentationModuleHom.{w, v, u} J
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f p₁))) =
      (Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj S₁))).map
        ((inverseImageCommModules.{w, w', v, u, v', u'} f S₁).map
          (SheafOfModules.kerIota (presentationModuleHom.{w', v', u'} K
            (presentationRingHom.{w', v', u'} K p₁)))) ≫
      (Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj S₁))).map
        (inverseImageUnitIso.{w, w', v, u, v', u'} f S₁).hom := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (inverseImageIdealHom_comp.{w, w', v, u, v', u'} f p₁)
  exact h.trans ((congrArg (_ ≫ ·) ((Sheaf.moduleSheafFunctor
      (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj S₁))).map_id
        _)).trans ((Category.comp_id _).trans
          (moduleSheafFunctor_map_inverseImageCommModules_map f S₁ _)))

/-- **The identification `f⁻¹ℐ ≅ ℐ'` is natural in the presentation**, on underlying sheaves of
sets: for a triangle `Ψ ≫ p₂ = p₁`, the inverse image of the map of kernel ideals induced by `Ψ`
is the map of kernel ideals induced by `f⁻¹Ψ`. -/
lemma inverseImage_idealSheafSetsMap_comp_inverseImageIdealIso :
    f.inverseImage.map (idealSheafSetsMap.{w', v', u'} K (presentationRingHom.{w', v', u'} K p₁)
        (presentationRingHom.{w', v', u'} K p₂) (presentationRingHom.{w', v', u'} K Ψ) (𝟙 _)
        (presentationRingHom_square.{w', v', u'} p₁ p₂ Ψ hsq)) ≫
      (Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj S₂))).map
        (inverseImageIdealIso.{w, w', v, u, v', u'} f p₂).hom =
    (Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj S₁))).map
        (inverseImageIdealIso.{w, w', v, u, v', u'} f p₁).hom ≫
      idealSheafSetsMap.{w, v, u} J (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f p₁)
        (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f p₂)
        (presentationRingHom.{w, v, u} J (f.inverseImageRing.map Ψ)) (𝟙 _)
        (inverseImagePresentationRingHom_square.{w, w', v, u, v', u'} f p₁ p₂ Ψ hsq) := by
  have hι₂ := moduleSheafFunctor_map_inverseImageIdealIso_hom_comp_kerIota.{w, w', v, u, v', u'}
    f p₂
  have hι₁ := moduleSheafFunctor_map_inverseImageIdealIso_hom_comp_kerIota.{w, w', v, u, v', u'}
    f p₁
  have hK := idealSheafSetsMap_comp_kerIota.{w', v', u'} K (presentationRingHom.{w', v', u'} K p₁)
    (presentationRingHom.{w', v', u'} K p₂) (presentationRingHom.{w', v', u'} K Ψ) (𝟙 _)
    (presentationRingHom_square.{w', v', u'} p₁ p₂ Ψ hsq)
  have hJ := idealSheafSetsMap_comp_kerIota.{w, v, u} J
    (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f p₁)
    (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f p₂)
    (presentationRingHom.{w, v, u} J (f.inverseImageRing.map Ψ)) (𝟙 _)
    (inverseImagePresentationRingHom_square.{w, w', v, u, v', u'} f p₁ p₂ Ψ hsq)
  have key : (f.inverseImage.map (idealSheafSetsMap.{w', v', u'} K
        (presentationRingHom.{w', v', u'} K p₁)
        (presentationRingHom.{w', v', u'} K p₂) (presentationRingHom.{w', v', u'} K Ψ) (𝟙 _)
        (presentationRingHom_square.{w', v', u'} p₁ p₂ Ψ hsq)) ≫
      (Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj S₂))).map
        (inverseImageIdealIso.{w, w', v, u, v', u'} f p₂).hom) ≫
      (Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj S₂))).map
        (SheafOfModules.kerIota (presentationModuleHom.{w, v, u} J
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f p₂))) =
    ((Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj S₁))).map
        (inverseImageIdealIso.{w, w', v, u, v', u'} f p₁).hom ≫
      idealSheafSetsMap.{w, v, u} J (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f p₁)
        (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f p₂)
        (presentationRingHom.{w, v, u} J (f.inverseImageRing.map Ψ)) (𝟙 _)
        (inverseImagePresentationRingHom_square.{w, w', v, u, v', u'} f p₁ p₂ Ψ hsq)) ≫
      (Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj S₂))).map
        (SheafOfModules.kerIota (presentationModuleHom.{w, v, u} J
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f p₂))) := by
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) hι₂).trans ?_
    refine (f.inverseImage.map_comp _ _).symm.trans ?_
    refine (congrArg f.inverseImage.map hK).trans ?_
    refine (f.inverseImage.map_comp _ _).trans ?_
    refine (congrArg (_ ≫ ·) (MorphismOfTopoi.inverseImageRing_map_forget f Ψ).symm).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (congrArg (_ ≫ ·) hJ).symm
    refine Eq.trans ?_ (Category.assoc _ _ _)
    exact (congrArg (· ≫ _) hι₁).symm
  exact Sheaf.hom_ext_sections fun U s =>
    Subtype.ext (congrArg (fun m => (Sheaf.sectionsFunctor J U).map m s) key)

end InverseImageIdealNaturality

end Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.RingedToposModules

section ConormalClassUntransposed

universe w w' v u v' u'

open Stacks.Sites.Conormal

attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{max u' v' w'})]
  (f : MorphismOfTopoi (Sheaf J (Type (max u v w))) (Sheaf K (Type (max u' v' w'))))
  {A B : Sheaf K CommRingCat.{max u' v' w'}} (φ : A ⟶ B) [Presheaf.IsLocallySurjective K φ.hom]

/-- **The comparison of Stacks 08TZ on conormal sheaves, characterised on classes**, on
underlying sheaves of sets: the inverse image of the class map of `φ`, followed by the
comparison, is the identification `f⁻¹ℐ ≅ ℐ'` followed by the class map of `f⁻¹φ`. -/
lemma inverseImage_conormalClassHom_comp_inverseImageConormalIso_hom :
    f.inverseImage.map
        ((Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map
            (conormalClassHom φ) ≫
          eqToHom (moduleSheaf_restrictScalars (presentationRingHom.{w', v', u'} K φ)
            (conormalModule.{w', v', u'} K φ))) ≫
      (Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj B))).map
        (inverseImageConormalIso.{w, w', v, u, v', u'} f φ).hom =
    (Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A))).map
        ((inverseImageIdealIso.{w, w', v, u, v', u'} f φ).hom ≫
          inverseImageConormalClassHom f φ) ≫
      eqToHom (moduleSheaf_restrictScalars
        (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)
        (conormalModule.{w, v, u} J (f.inverseImageRing.map φ))) := by
  apply (f.adj.homEquiv _ _).injective
  refine Eq.trans ?_ (f.adj.homEquiv_naturality_right _ _).symm
  refine Eq.trans ?_
    (homEquiv_inverseImageIdealIso_hom_comp_inverseImageConormalClassHom.{w, w', v, u, v', u'}
      f φ).symm
  refine Eq.trans ?_ (Category.assoc _ _ _)
  exact f.adj.homEquiv_naturality_left _ _

/-- **The inverse of the comparison of Stacks 08TZ on conormal sheaves, on classes**, on
underlying sheaves of sets: the class map of `f⁻¹φ` followed by the inverse of the comparison is
the identification `ℐ' ≅ f⁻¹ℐ` followed by the inverse image of the class map of `φ`. -/
lemma inverseImageIdealIso_inv_comp_inverseImage_conormalClassHom :
    (Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A))).map
        (inverseImageIdealIso.{w, w', v, u, v', u'} f φ).inv ≫
      f.inverseImage.map
        ((Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map
            (conormalClassHom φ) ≫
          eqToHom (moduleSheaf_restrictScalars (presentationRingHom.{w', v', u'} K φ)
            (conormalModule.{w', v', u'} K φ))) =
    (Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A))).map
        (inverseImageConormalClassHom f φ) ≫
      eqToHom (moduleSheaf_restrictScalars
        (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)
        (conormalModule.{w, v, u} J (f.inverseImageRing.map φ))) ≫
      (Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj B))).map
        (inverseImageConormalIso.{w, w', v, u, v', u'} f φ).inv := by
  have L := congrArg (fun t => (Sheaf.moduleSheafFunctor
      (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A))).map
        (inverseImageIdealIso.{w, w', v, u, v', u'} f φ).inv ≫ t ≫ (Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj B))).map
        (inverseImageConormalIso.{w, w', v, u, v', u'} f φ).inv)
    (inverseImage_conormalClassHom_comp_inverseImageConormalIso_hom.{w, w', v, u, v', u'} f φ)
  have h1 : (Sheaf.moduleSheafFunctor
        (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj B))).map
        (inverseImageConormalIso.{w, w', v, u, v', u'} f φ).hom ≫
      (Sheaf.moduleSheafFunctor
        (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj B))).map
        (inverseImageConormalIso.{w, w', v, u, v', u'} f φ).inv = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  have h2 : (Sheaf.moduleSheafFunctor
        (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A))).map
        (inverseImageIdealIso.{w, w', v, u, v', u'} f φ).inv ≫
      (Sheaf.moduleSheafFunctor
        (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A))).map
        ((inverseImageIdealIso.{w, w', v, u, v', u'} f φ).hom ≫ inverseImageConormalClassHom f φ) =
      (Sheaf.moduleSheafFunctor
        (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A))).map
        (inverseImageConormalClassHom f φ) := by
    rw [← Functor.map_comp, Iso.inv_hom_id_assoc]
  refine Eq.trans ?_ (L.trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h2)))
  refine congrArg (_ ≫ ·) ?_
  exact ((Category.comp_id _).symm.trans (congrArg (_ ≫ ·) h1.symm)).trans
    (Category.assoc _ _ _).symm

omit [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{max u' v' w'})] in
/-- The morphism out of the kernel ideal of `f⁻¹φ` attached to a morphism out of the conormal
sheaf of `f⁻¹φ` is the class map followed by that morphism. -/
lemma conormalModuleHomEquivOf_eq_inverseImageConormalClassHom_comp
    (G : SheafOfModules.{max u v w}
      (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj B)))
    (z : conormalModule.{w, v, u} J (f.inverseImageRing.map φ) ⟶ G) :
    conormalModuleHomEquivOf.{w, v, u} J (f.inverseImageRing.map φ)
        (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)
        (inverseImageRingMap_presentationRingHom.{w, w', v, u, v', u'} f φ) G z =
      inverseImageConormalClassHom f φ ≫
        (SheafOfModules.restrictScalars
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).map z := by
  simpa only [Category.id_comp] using conormalModuleHomEquivOf_comp.{w, v, u} J
    (f.inverseImageRing.map φ) (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)
    (inverseImageRingMap_presentationRingHom.{w, w', v, u, v', u'} f φ) _ G (𝟙 _) z

/-- **The comparison of Stacks 08TZ on conormal sheaves, read on the kernel ideal.** For a
morphism `z` out of the conormal sheaf of `f⁻¹φ`, the identification `f⁻¹ℐ ≅ ℐ'` followed by
the restriction of `z` to the kernel ideal is, on underlying sheaves of sets, the inverse image
of the class map of `φ` followed by the comparison and by `z`. -/
lemma inverseImageIdealIso_hom_comp_conormalModuleHomEquivOf
    (G : SheafOfModules.{max u v w}
      (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj B)))
    (z : conormalModule.{w, v, u} J (f.inverseImageRing.map φ) ⟶ G) :
    (Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A))).map
        (inverseImageIdealIso.{w, w', v, u, v', u'} f φ).hom ≫
      (Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A))).map
        (conormalModuleHomEquivOf.{w, v, u} J (f.inverseImageRing.map φ)
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)
          (inverseImageRingMap_presentationRingHom.{w, w', v, u, v', u'} f φ) G z) ≫
      eqToHom (moduleSheaf_restrictScalars
        (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ) G) =
    f.inverseImage.map
        ((Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map
            (conormalClassHom φ) ≫
          eqToHom (moduleSheaf_restrictScalars (presentationRingHom.{w', v', u'} K φ)
            (conormalModule.{w', v', u'} K φ))) ≫
      (Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj B))).map
        ((inverseImageConormalIso.{w, w', v, u, v', u'} f φ).hom ≫ z) := by
  refine Eq.trans ?_ (congrArg (_ ≫ ·) ((Sheaf.moduleSheafFunctor
    (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj B))).map_comp
      _ _)).symm
  rw [conormalModuleHomEquivOf_eq_inverseImageConormalClassHom_comp, Functor.map_comp,
    moduleSheafFunctor_map_restrictScalars_map_eq_eqToHom]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg (· ≫ (Sheaf.moduleSheafFunctor
      (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj B))).map z)
    (inverseImage_conormalClassHom_comp_inverseImageConormalIso_hom.{w, w', v, u, v', u'}
      f φ)).symm
  rw [Functor.map_comp]
  exact ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).symm

end ConormalClassUntransposed

end Stacks.Sheaves.RingedToposModules

namespace Stacks.Sites.Conormal

section TypedValues

universe t v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v t})]

/-- A morphism into a restriction of scalars, read on underlying sheaves of sets through the
identification of underlying sheaves of sets, acts on local sections as the morphism does; the
value is typed in the sections of the unrestricted sheaf of modules. -/
lemma sectionsFunctor_map_moduleSheafFunctor_map_comp_eqToHom
    {R R' : Sheaf J RingCat.{max u v t}} (α : R ⟶ R') {M : SheafOfModules.{max u v t} R}
    {N : SheafOfModules.{max u v t} R'} (z : M ⟶ (SheafOfModules.restrictScalars α).obj N)
    (V : Cᵒᵖ) (x : (Sheaf.sectionsFunctor J V).obj ((Sheaf.moduleSheafFunctor R).obj M)) :
    @Eq ↥(N.val.obj V)
      ((Sheaf.sectionsFunctor J V).map ((Sheaf.moduleSheafFunctor R).map z ≫
        eqToHom (Stacks.Sheaves.RingedToposModules.moduleSheaf_restrictScalars α N)) x)
      (z.val.app V x) :=
  rfl

variable {A B : Sheaf J CommRingCat.{max u v t}} (φ : A ⟶ B) [Presheaf.IsLocallySurjective J φ.hom]
  (α : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) A ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) B)
  (hα : α = presentationRingHom.{t, v, u} J φ)

omit [J.HasSheafCompose (forget AddCommGrpCat.{max u v t})] in
/-- `Stacks.Sites.Conormal.conormalModuleHomEquivOf_app_conormalClass`, with both sides typed in
the sections of the unrestricted sheaf of modules. -/
lemma conormalModuleHomEquivOf_val_app_eq_conormalClass
    (R : Sheaf J CommRingCat.{max u v t}) (c : R ⟶ A)
    (G : SheafOfModules.{max u v t} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} B))
    (x : conormalModule.{t, v, u} J φ ⟶ G) (U : Cᵒᵖ)
    (g : ↥((idealSheaf.{t, v, u} J α).val.obj U)) (y : ↥(kernelIdeal φ.hom U))
    (hgy : g.1 = y.1) :
    @Eq ↥(G.val.obj U) ((conormalModuleHomEquivOf.{t, v, u} J φ α hα G x).val.app U g)
      (x.val.app U (conormalClass.{v, u, max u v t, t} J R A B c φ U y)) :=
  conormalModuleHomEquivOf_app_conormalClass.{t, v, u} J φ α hα R c G x U g y hgy

/-- The restriction to the kernel ideal of a morphism out of the conormal sheaf sends a local
section `y` to the value of the morphism at the class of `y`, read on underlying sheaves of
sets. -/
private lemma sections_map_conormalModuleHomEquivOf_eqToHom
    (R : Sheaf J CommRingCat.{max u v t}) (c : R ⟶ A)
    (G : SheafOfModules.{max u v t} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} B))
    (x : conormalModule.{t, v, u} J φ ⟶ G) (U : Cᵒᵖ) (y : ↥((idealSheaf.{t, v, u} J α).val.obj U)) :
    @Eq ↥(G.val.obj U)
      ((Sheaf.sectionsFunctor J U).map ((Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} A)).map
          (conormalModuleHomEquivOf.{t, v, u} J φ α hα G x) ≫
        eqToHom (Stacks.Sheaves.RingedToposModules.moduleSheaf_restrictScalars α G)) y)
      (x.val.app U (conormalClass.{v, u, max u v t, t} J R A B c φ U
        ⟨y.1, coe_mem_kernelIdeal.{t, v, u} J φ α hα U y⟩)) :=
  (sectionsFunctor_map_moduleSheafFunctor_map_comp_eqToHom.{t, v, u} J α
    (conormalModuleHomEquivOf.{t, v, u} J φ α hα G x) U y).trans
    (conormalModuleHomEquivOf_val_app_eq_conormalClass.{t, v, u} J φ α hα R c G x U y _ rfl)

end TypedValues

end Stacks.Sites.Conormal

namespace Stacks.SheafOfModules

section InverseImageConormalBaseChangeSections

universe u v w u' v' w'

open CategoryTheory.Limits AlgebraicGeometry.SheafOfModules
open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.ToposPushforward
open CategoryTheory.Sheaf (inverseImageTargetModules)

attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J CommRingCat.{max u v w}] [HasWeakSheafify K CommRingCat.{max u' v' w'}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u' v' w'} RingCat.{max u' v' w'})]
  (f : MorphismOfTopoi (Sheaf J (Type (max u v w))) (Sheaf K (Type (max u' v' w'))))
  {A B : Sheaf K CommRingCat.{max u' v' w'}} (a : A ⟶ B)
  {A' : Sheaf K CommRingCat.{max u' v' w'}} (a' : A' ⟶ B) (φ : A ⟶ A') (hf : a = φ ≫ a')

omit [K.HasSheafCompose (forget₂ CommRingCat.{max u' v' w'} RingCat.{max u' v' w'})] in
include hf in
/-- The morphism `A[B] ⟶ A'[B]` attached to a factorisation `a = φ ≫ a'` is compatible with
the two canonical presentations. -/
lemma canonicalFreeAlgebraMapOfBase_comp :
    canonicalFreeAlgebraMapOfSquare K A A' B B φ (𝟙 B) ≫ canonicalPresentation K A' B a' =
      canonicalPresentation K A B a ≫ 𝟙 B :=
  freeAlgebraMapOfSquare_comp_canonicalPresentation K A A' B B a a' φ (𝟙 B)
    (comp_id_eq_comp_of_fac K A B a A' a' φ hf)

/-- The comparison `f⁻¹ℐ ≅ ℐ'` of the canonical presentation of `f⁻¹B` over `f⁻¹A'` followed by
`inverseImagePresentationConormalIso` sends a local section `z` of the kernel ideal to the class
of its image in `(f⁻¹A')[f⁻¹B]`, read on underlying sheaves of sets. -/
private lemma sections_map_inverseImagePresentationConormalIso_hom
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasWeakSheafify J CommRingCat.{max u v w}] [HasWeakSheafify K CommRingCat.{max u' v' w'}]
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
    (f : MorphismOfTopoi (Sheaf J (Type (max u v w))) (Sheaf K (Type (max u' v' w'))))
    {A' B : Sheaf K CommRingCat.{max u' v' w'}} (a' : A' ⟶ B) (U : Cᵒᵖ)
    (z : ↥((idealSheaf.{max u v w, v, u} J
      (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
        (canonicalPresentation K A' B a'))).val.obj U)) :
    @Eq ↥((canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A')
        (f.inverseImageRing.obj B) (f.inverseImageRing.map a')).X₁.val.obj U)
      ((Sheaf.sectionsFunctor J U).map ((Sheaf.moduleSheafFunctor (Tensor.ringSheaf.{u, v,
          max u v w} (f.inverseImageRing.obj (freeAlgebraSheaf K A' (underlyingPresheaf K B))))).map
        (conormalModuleHomEquivOf.{max u v w, v, u} J
          (f.inverseImageRing.map (canonicalPresentation K A' B a'))
          (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
            (canonicalPresentation K A' B a'))
          (inverseImageRingMap_presentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
            (canonicalPresentation K A' B a'))
          (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A')
            (f.inverseImageRing.obj B) (f.inverseImageRing.map a')).X₁
          (inverseImagePresentationConormalIso.{u, v, w, u', v', w'} J K f a').hom) ≫
        eqToHom (moduleSheaf_restrictScalars
          (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
            (canonicalPresentation K A' B a'))
          (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A')
            (f.inverseImageRing.obj B) (f.inverseImageRing.map a')).X₁)) z)
      (conormalClass.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A')
        (freeAlgebraSheaf J (f.inverseImageRing.obj A')
          (underlyingPresheaf J (f.inverseImageRing.obj B))) (f.inverseImageRing.obj B)
        (freeAlgebraSheafCoefficientMap J (f.inverseImageRing.obj A')
          (underlyingPresheaf J (f.inverseImageRing.obj B)))
        (canonicalPresentation J (f.inverseImageRing.obj A') (f.inverseImageRing.obj B)
          (f.inverseImageRing.map a')) U
        ⟨(inverseImageFreeAlgebraIso f A' B).hom.hom.app U z.1,
          kernelIdeal_le_comap _ _ _ (hom_of_comp_eq
            (inverseImageFreeAlgebraHom_comp_canonicalPresentation f A' B a')) U
            (coe_mem_kernelIdeal.{max u v w, v, u} J
              (f.inverseImageRing.map (canonicalPresentation K A' B a'))
              (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
                (canonicalPresentation K A' B a'))
              (inverseImageRingMap_presentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
                (canonicalPresentation K A' B a')) U z)⟩) :=
  (sections_map_conormalModuleHomEquivOf_eqToHom.{max u v w, v, u} J
    (f.inverseImageRing.map (canonicalPresentation K A' B a'))
    (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
      (canonicalPresentation K A' B a'))
    (inverseImageRingMap_presentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
      (canonicalPresentation K A' B a'))
    (f.inverseImageRing.obj A')
    (f.inverseImageRing.map (freeAlgebraSheafCoefficientMap K A' (underlyingPresheaf K B)))
    (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A')
      (f.inverseImageRing.obj B) (f.inverseImageRing.map a')).X₁
    (inverseImagePresentationConormalIso.{u, v, w, u', v', w'} J K f a').hom U z).trans
    (conormalSheafMapOfFac_conormalClass (J := J) (R := f.inverseImageRing.obj A')
      (B := f.inverseImageRing.obj B)
      (A₁ := f.inverseImageRing.obj (freeAlgebraSheaf K A' (underlyingPresheaf K B)))
      (A₂ := freeAlgebraSheaf J (f.inverseImageRing.obj A')
        (underlyingPresheaf J (f.inverseImageRing.obj B)))
      (a₁ := f.inverseImageRing.map (freeAlgebraSheafCoefficientMap K A' (underlyingPresheaf K B)))
      (a₂ := freeAlgebraSheafCoefficientMap J (f.inverseImageRing.obj A')
        (underlyingPresheaf J (f.inverseImageRing.obj B)))
      (φ₁ := f.inverseImageRing.map (canonicalPresentation K A' B a'))
      (φ₂ := canonicalPresentation J (f.inverseImageRing.obj A') (f.inverseImageRing.obj B)
        (f.inverseImageRing.map a'))
      (ψ := (inverseImageFreeAlgebraIso f A' B).hom)
      (hψ := inverseImageFreeAlgebraHom_comp_canonicalPresentation f A' B a')
      (X := U) (x := ⟨z.1, _⟩))

/-- A map out of the conormal sheaf of `f⁻¹p₁` equals the comparison of Stacks 08TZ composed with
the inverse image of a triangle map and a map `z` out of the conormal sheaf of `f⁻¹p₂`, once the
two agree on the kernel ideal, on underlying sheaves of sets. -/
private lemma inverseImageConormalIso_inv_comp_map_comp_eq
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
    [K.HasSheafCompose (forget₂ CommRingCat.{max u' v' w'} RingCat.{max u' v' w'})]
    (f : MorphismOfTopoi (Sheaf J (Type (max u v w))) (Sheaf K (Type (max u' v' w'))))
    {S₁ S₂ T : Sheaf K CommRingCat.{max u' v' w'}} (p₁ : S₁ ⟶ T) (p₂ : S₂ ⟶ T) (Ψ : S₁ ⟶ S₂)
    (hsq : Ψ ≫ p₂ = p₁ ≫ 𝟙 T) [Presheaf.IsLocallySurjective K p₁.hom]
    [Presheaf.IsLocallySurjective K p₂.hom]
    {G : SheafOfModules.{max u v w} (Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj T))}
    (z : conormalModule.{max u v w, v, u} J (f.inverseImageRing.map p₂) ⟶ G)
    (X : conormalModule.{max u v w, v, u} J (f.inverseImageRing.map p₁) ⟶ G)
    (H : (Sheaf.moduleSheafFunctor
          (Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj S₁))).map
        (conormalModuleHomEquivOf.{max u v w, v, u} J (f.inverseImageRing.map p₁)
          (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f p₁)
          (inverseImageRingMap_presentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f p₁)
          G X) ≫
      eqToHom (moduleSheaf_restrictScalars
        (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f p₁) G) =
    idealSheafSetsMap.{max u v w, v, u} J
        (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f p₁)
        (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f p₂)
        (presentationRingHom.{max u v w, v, u} J (f.inverseImageRing.map Ψ)) (𝟙 _)
        (inverseImagePresentationRingHom_square.{max u v w, max u' v' w', v, u, v', u'}
          f p₁ p₂ Ψ hsq) ≫
      (Sheaf.moduleSheafFunctor
          (Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj S₂))).map
        (conormalModuleHomEquivOf.{max u v w, v, u} J (f.inverseImageRing.map p₂)
          (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f p₂)
          (inverseImageRingMap_presentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f p₂)
          G z) ≫
      eqToHom (moduleSheaf_restrictScalars
        (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f p₂) G)) :
    (inverseImageConormalIso.{max u v w, max u' v' w', v, u, v', u'} f p₁).inv ≫
      (inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := T)).map
        (conormalModuleMapOfTriangle.{max u' v' w', v', u'} p₁ p₂ Ψ hsq) ≫
      (inverseImageConormalIso.{max u v w, max u' v' w', v, u, v', u'} f p₂).hom ≫ z = X := by
  apply (conormalModuleHomEquivOf.{max u v w, v, u} J (f.inverseImageRing.map p₁)
    (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f p₁)
    (inverseImageRingMap_presentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f p₁)
    G).injective
  apply hom_ext_moduleSheafFunctor
  apply (cancel_epi ((Sheaf.moduleSheafFunctor (Tensor.ringSheaf.{u, v, max u v w}
    (f.inverseImageRing.obj S₁))).map
      (inverseImageIdealIso.{max u v w, max u' v' w', v, u, v', u'} f p₁).hom)).1
  apply (cancel_mono (eqToHom (moduleSheaf_restrictScalars
    (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f p₁) G))).1
  have e1 := inverseImageIdealIso_hom_comp_conormalModuleHomEquivOf.{max u v w, max u' v' w',
    v, u, v', u'} f p₁ G
    ((inverseImageConormalIso.{max u v w, max u' v' w', v, u, v', u'} f p₁).inv ≫
      (inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := T)).map
        (conormalModuleMapOfTriangle.{max u' v' w', v', u'} p₁ p₂ Ψ hsq) ≫
      (inverseImageConormalIso.{max u v w, max u' v' w', v, u, v', u'} f p₂).hom ≫ z)
  have e2 := (congrArg (Sheaf.moduleSheafFunctor (Tensor.ringSheaf.{u, v, max u v w}
      (f.inverseImageRing.obj T))).map (Iso.hom_inv_id_assoc
        (inverseImageConormalIso.{max u v w, max u' v' w', v, u, v', u'} f p₁)
        ((inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := T)).map
          (conormalModuleMapOfTriangle.{max u' v' w', v', u'} p₁ p₂ Ψ hsq) ≫
          (inverseImageConormalIso.{max u v w, max u' v' w', v, u, v', u'} f p₂).hom ≫ z))).trans
    (((Sheaf.moduleSheafFunctor (Tensor.ringSheaf.{u, v, max u v w}
      (f.inverseImageRing.obj T))).map_comp _ _).trans
      (congrArg (· ≫ _) (moduleSheafFunctor_map_inverseImageCommModules_map f T _)))
  have e3 := moduleSheafFunctor_map_conormalClassHom_comp_conormalSheafMapOfSquare.{max u' v' w',
    v', u'} p₁ p₂ Ψ hsq
  have e4 := inverseImageIdealIso_hom_comp_conormalModuleHomEquivOf.{max u v w, max u' v' w',
    v, u, v', u'} f p₂ G z
  have e5 := inverseImage_idealSheafSetsMap_comp_inverseImageIdealIso.{max u v w, max u' v' w',
    v, u, v', u'} f p₁ p₂ Ψ hsq
  refine (Category.assoc _ _ _).trans ?_
  refine e1.trans ?_
  refine (congrArg (_ ≫ ·) e2).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (f.inverseImage.map_comp _ _).symm).trans ?_
  refine (congrArg (fun t => f.inverseImage.map t ≫ _) ((Category.assoc _ _ _).trans e3)).trans ?_
  refine (congrArg (· ≫ _) (f.inverseImage.map_comp _ _)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) e4.symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) e5).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) H.symm).trans ?_
  exact (Category.assoc _ _ _).symm

omit [K.HasSheafCompose (forget₂ CommRingCat.{max u' v' w'} RingCat.{max u' v' w'})] in
include hf in
/-- **The degree `-1` change of base ring of the inverse image, on classes.** For a local
section `y` of the kernel ideal of `f⁻¹(A[B] ⟶ B)`, the class of `y`, carried to the conormal
sheaf of the canonical presentation of `f⁻¹B` over `f⁻¹A` and then along the change of base
ring, is the class of the image of `y` under `f⁻¹(A[B] ⟶ A'[B])`, carried to the conormal sheaf
of the canonical presentation of `f⁻¹B` over `f⁻¹A'`; as morphisms of sheaves of sets. -/
lemma naiveCotangentConormalMapOfBase_inverseImagePresentationConormalIso :
    (Sheaf.moduleSheafFunctor (Tensor.ringSheaf.{u, v, max u v w}
          (f.inverseImageRing.obj (freeAlgebraSheaf K A (underlyingPresheaf K B))))).map
        (conormalModuleHomEquivOf.{max u v w, v, u} J
          (f.inverseImageRing.map (canonicalPresentation K A B a))
          (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
            (canonicalPresentation K A B a))
          (inverseImageRingMap_presentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
            (canonicalPresentation K A B a))
          (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A')
            (f.inverseImageRing.obj B) (f.inverseImageRing.map a')).X₁
          ((inverseImagePresentationConormalIso.{u, v, w, u', v', w'} J K f a).hom ≫
            naiveCotangentConormalMapOfBase.{v, u, max u v w, max u v w} J
              (f.inverseImageRing.obj A) (f.inverseImageRing.obj B) (f.inverseImageRing.map a)
              (f.inverseImageRing.obj A') (f.inverseImageRing.map a') (f.inverseImageRing.map φ)
              (inverseImageRing_map_fac J K f a a' φ hf))) ≫
      eqToHom (moduleSheaf_restrictScalars
        (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
          (canonicalPresentation K A B a))
        (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A')
          (f.inverseImageRing.obj B) (f.inverseImageRing.map a')).X₁) =
    idealSheafSetsMap.{max u v w, v, u} J
        (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
          (canonicalPresentation K A B a))
        (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
          (canonicalPresentation K A' B a'))
        (presentationRingHom.{max u v w, v, u} J
          (f.inverseImageRing.map (canonicalFreeAlgebraMapOfSquare K A A' B B φ (𝟙 B))))
        (𝟙 _)
        (inverseImagePresentationRingHom_square.{max u v w, max u' v' w', v, u, v', u'} f
          (canonicalPresentation K A B a) (canonicalPresentation K A' B a')
          (canonicalFreeAlgebraMapOfSquare K A A' B B φ (𝟙 B))
          (canonicalFreeAlgebraMapOfBase_comp K a a' φ hf)) ≫
      (Sheaf.moduleSheafFunctor (Tensor.ringSheaf.{u, v, max u v w}
          (f.inverseImageRing.obj (freeAlgebraSheaf K A' (underlyingPresheaf K B))))).map
        (conormalModuleHomEquivOf.{max u v w, v, u} J
          (f.inverseImageRing.map (canonicalPresentation K A' B a'))
          (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
            (canonicalPresentation K A' B a'))
          (inverseImageRingMap_presentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
            (canonicalPresentation K A' B a'))
          (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A')
            (f.inverseImageRing.obj B) (f.inverseImageRing.map a')).X₁
          (inverseImagePresentationConormalIso.{u, v, w, u', v', w'} J K f a').hom) ≫
      eqToHom (moduleSheaf_restrictScalars
        (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
          (canonicalPresentation K A' B a'))
        (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A')
          (f.inverseImageRing.obj B) (f.inverseImageRing.map a')).X₁) := by
  refine Sheaf.hom_ext_sections fun U y => ?_
  have hy := coe_mem_kernelIdeal.{max u v w, v, u} J
    (f.inverseImageRing.map (canonicalPresentation K A B a))
    (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
      (canonicalPresentation K A B a))
    (inverseImageRingMap_presentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
      (canonicalPresentation K A B a)) U y
  have l2 := conormalSheafMapOfFac_conormalClass (J := J) (R := f.inverseImageRing.obj A)
    (B := f.inverseImageRing.obj B)
    (A₁ := f.inverseImageRing.obj (freeAlgebraSheaf K A (underlyingPresheaf K B)))
    (A₂ := freeAlgebraSheaf J (f.inverseImageRing.obj A)
      (underlyingPresheaf J (f.inverseImageRing.obj B)))
    (a₁ := f.inverseImageRing.map (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)))
    (a₂ := freeAlgebraSheafCoefficientMap J (f.inverseImageRing.obj A)
      (underlyingPresheaf J (f.inverseImageRing.obj B)))
    (φ₁ := f.inverseImageRing.map (canonicalPresentation K A B a))
    (φ₂ := canonicalPresentation J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
      (f.inverseImageRing.map a))
    (ψ := (inverseImageFreeAlgebraIso f A B).hom)
    (hψ := inverseImageFreeAlgebraHom_comp_canonicalPresentation f A B a)
    (X := U) (x := ⟨y.1, hy⟩)
  have l3 := conormalSheafMapOfSquare_conormalClass.{v, u, max u v w, max u v w} J
    (f.inverseImageRing.obj A) (f.inverseImageRing.obj A')
    (freeAlgebraSheaf J (f.inverseImageRing.obj A)
      (underlyingPresheaf J (f.inverseImageRing.obj B)))
    (freeAlgebraSheaf J (f.inverseImageRing.obj A')
      (underlyingPresheaf J (f.inverseImageRing.obj B)))
    (f.inverseImageRing.obj B) (f.inverseImageRing.obj B)
    (freeAlgebraSheafCoefficientMap J (f.inverseImageRing.obj A)
      (underlyingPresheaf J (f.inverseImageRing.obj B)))
    (freeAlgebraSheafCoefficientMap J (f.inverseImageRing.obj A')
      (underlyingPresheaf J (f.inverseImageRing.obj B)))
    (canonicalPresentation J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
      (f.inverseImageRing.map a))
    (canonicalPresentation J (f.inverseImageRing.obj A') (f.inverseImageRing.obj B)
      (f.inverseImageRing.map a'))
    (canonicalFreeAlgebraMapOfSquare J (f.inverseImageRing.obj A) (f.inverseImageRing.obj A')
      (f.inverseImageRing.obj B) (f.inverseImageRing.obj B) (f.inverseImageRing.map φ) (𝟙 _))
    (𝟙 _) (canonicalFreeAlgebraMapOfBase_comp J (f.inverseImageRing.map a)
      (f.inverseImageRing.map a') (f.inverseImageRing.map φ)
      (inverseImageRing_map_fac J K f a a' φ hf)) U
    ⟨(inverseImageFreeAlgebraIso f A B).hom.hom.app U y.1,
      kernelIdeal_le_comap _ _ _ (hom_of_comp_eq
        (inverseImageFreeAlgebraHom_comp_canonicalPresentation f A B a)) U hy⟩
  have e := congrArg (fun g => g.hom.app U y.1)
    (map_canonicalFreeAlgebraMapOfSquare_comp_inverseImageFreeAlgebraHom f B φ)
  refine (sections_map_conormalModuleHomEquivOf_eqToHom.{max u v w, v, u} J
    (f.inverseImageRing.map (canonicalPresentation K A B a))
    (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
      (canonicalPresentation K A B a))
    (inverseImageRingMap_presentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
      (canonicalPresentation K A B a))
    (f.inverseImageRing.obj A)
    (f.inverseImageRing.map (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)))
    (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A')
      (f.inverseImageRing.obj B) (f.inverseImageRing.map a')).X₁
    ((inverseImagePresentationConormalIso.{u, v, w, u', v', w'} J K f a).hom ≫
      naiveCotangentConormalMapOfBase.{v, u, max u v w, max u v w} J
        (f.inverseImageRing.obj A) (f.inverseImageRing.obj B) (f.inverseImageRing.map a)
        (f.inverseImageRing.obj A') (f.inverseImageRing.map a') (f.inverseImageRing.map φ)
        (inverseImageRing_map_fac J K f a a' φ hf)) U y).trans
    ((congrArg _ l2).trans (l3.trans ?_))
  refine Eq.trans ?_ (sections_map_inverseImagePresentationConormalIso_hom.{u, v, w, u', v', w'}
    J K f a' U _).symm
  exact congrArg _ (Subtype.ext e.symm)

include hf in
/-- The degree `-1` comparison of Stacks 08TZ, transported back along the comparison for `a`,
turns the inverse image of the change of base ring into the change of base ring of the inverse
image, as morphisms out of the conormal sheaf of `f⁻¹(A[B] ⟶ B)`. -/
lemma inverseImageConormalIso_inv_comp_naiveCotangentConormalMapOfBase :
    (inverseImageConormalIso.{max u v w, max u' v' w', v, u, v', u'} f
        (canonicalPresentation K A B a)).inv ≫
      (inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := B)).map
        (conormalModuleMapOfTriangle.{max u' v' w', v', u'} (canonicalPresentation K A B a)
          (canonicalPresentation K A' B a') (canonicalFreeAlgebraMapOfSquare K A A' B B φ (𝟙 B))
          (canonicalFreeAlgebraMapOfBase_comp K a a' φ hf)) ≫
      (inverseImageConormalIso.{max u v w, max u' v' w', v, u, v', u'} f
        (canonicalPresentation K A' B a')).hom ≫
      (inverseImagePresentationConormalIso.{u, v, w, u', v', w'} J K f a').hom =
    (inverseImagePresentationConormalIso.{u, v, w, u', v', w'} J K f a).hom ≫
      naiveCotangentConormalMapOfBase.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
        (f.inverseImageRing.obj B) (f.inverseImageRing.map a) (f.inverseImageRing.obj A')
        (f.inverseImageRing.map a') (f.inverseImageRing.map φ)
        (inverseImageRing_map_fac J K f a a' φ hf) := by
  refine inverseImageConormalIso_inv_comp_map_comp_eq J K f (canonicalPresentation K A B a)
    (canonicalPresentation K A' B a') (canonicalFreeAlgebraMapOfSquare K A A' B B φ (𝟙 B))
    (canonicalFreeAlgebraMapOfBase_comp K a a' φ hf) _ _ ?_
  have e6 := naiveCotangentConormalMapOfBase_inverseImagePresentationConormalIso J K f a a' φ hf
  exact e6

omit [K.HasSheafCompose (forget₂ CommRingCat.{max u' v' w'} RingCat.{max u' v' w'})] in
/-- The degree `-1` comparison `inverseImageNaiveCotangentNegOneIso` is the composite of
`inverseImageConormalIso` for the canonical presentation with
`inverseImagePresentationConormalIso`. -/
lemma inverseImageNaiveCotangentNegOneIso_hom_eq :
    (inverseImageNaiveCotangentNegOneIso.{u, v, w, u', v', w'} J K f a).hom =
      (inverseImageConormalIso.{max u v w, max u' v' w', v, u, v', u'} f
        (canonicalPresentation K A B a)).hom ≫
        (inverseImagePresentationConormalIso.{u, v, w, u', v', w'} J K f a).hom :=
  rfl

include hf in
/-- The degree `-1` change of base ring `naiveCotangentConormalMapOfBase` is the map of conormal
sheaves `conormalModuleMapOfTriangle` induced by the map of canonical presentations. -/
lemma naiveCotangentConormalMapOfBase_eq_conormalModuleMapOfTriangle :
    naiveCotangentConormalMapOfBase.{v', u', max u' v' w', max u' v' w'} K A B a A' a' φ hf =
      conormalModuleMapOfTriangle.{max u' v' w', v', u'} (canonicalPresentation K A B a)
          (canonicalPresentation K A' B a') (canonicalFreeAlgebraMapOfSquare K A A' B B φ (𝟙 B))
          (canonicalFreeAlgebraMapOfBase_comp K a a' φ hf) :=
  rfl

include hf in
/-- The degree `-1` comparison `inverseImageNaiveCotangentNegOneIso` is natural in the base ring:
it commutes with the change of base ring `naiveCotangentConormalMapOfBase` along `φ : A ⟶ A'`. -/
theorem inverseImageNaiveCotangentNegOneIso_naturality :
    (inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := B)).map
        (naiveCotangentConormalMapOfBase.{v', u', max u' v' w', max u' v' w'} K A B a A' a' φ hf) ≫
      (inverseImageNaiveCotangentNegOneIso.{u, v, w, u', v', w'} J K f a').hom =
    (inverseImageNaiveCotangentNegOneIso.{u, v, w, u', v', w'} J K f a).hom ≫
      naiveCotangentConormalMapOfBase.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
        (f.inverseImageRing.obj B) (f.inverseImageRing.map a) (f.inverseImageRing.obj A')
        (f.inverseImageRing.map a') (f.inverseImageRing.map φ)
        (inverseImageRing_map_fac J K f a a' φ hf) := by
  have key := inverseImageConormalIso_inv_comp_naiveCotangentConormalMapOfBase J K f a a' φ hf
  rw [inverseImageNaiveCotangentNegOneIso_hom_eq, inverseImageNaiveCotangentNegOneIso_hom_eq,
    naiveCotangentConormalMapOfBase_eq_conormalModuleMapOfTriangle K a a' φ hf]
  refine (Iso.hom_inv_id_assoc (inverseImageConormalIso.{max u v w, max u' v' w', v, u, v', u'} f
    (canonicalPresentation K A B a)) _).symm.trans ?_
  exact (congrArg (_ ≫ ·) key).trans (Category.assoc _ _ _).symm

/-- The degree `-1` component of the comparison of Stacks 08TZ of complexes is the degree `-1`
comparison, read through the identifications of the degree `-1` terms. -/
lemma inverseImageNaiveCotangentComplexIso_hom_f_negOne :
    (inverseImageNaiveCotangentComplexIso.{u, v, w, u', v', w'} J K f a).hom.f (-1) =
      (inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := B)).map
          (eqToHom (naiveCotangentComplex_X_negOne.{v', u', max u' v' w', max u' v' w'} K A B a)) ≫
        (inverseImageNaiveCotangentNegOneIso.{u, v, w, u', v', w'} J K f a).hom ≫
        eqToHom (naiveCotangentComplex_X_negOne.{v, u, max u v w, max u v w} J
          (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
          (f.inverseImageRing.map a)).symm := by
  simp [inverseImageNaiveCotangentComplexIso, HomologicalComplex.isoFromMapDouble,
    naiveCotangentComplexXNegOneIso, HomologicalComplex.doubleXIso₀]
  rfl

/-- The degree `0` component of the comparison of Stacks 08TZ of complexes is the degree `0`
comparison, read through the identifications of the degree `0` terms. -/
lemma inverseImageNaiveCotangentComplexIso_hom_f_zero :
    (inverseImageNaiveCotangentComplexIso.{u, v, w, u', v', w'} J K f a).hom.f 0 =
      (inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := B)).map
          (eqToHom (naiveCotangentComplex_X_zero.{v', u', max u' v' w', max u' v' w'} K A B a)) ≫
        (inverseImageNaiveCotangentZeroTargetIso.{u, v, w, u', v', w'} J K f a).hom ≫
        eqToHom (naiveCotangentComplex_X_zero.{v, u, max u v w, max u v w} J
          (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
          (f.inverseImageRing.map a)).symm := by
  simp [inverseImageNaiveCotangentComplexIso, HomologicalComplex.isoFromMapDouble,
    naiveCotangentComplexXZeroIso, HomologicalComplex.doubleXIso₁]
  rfl

include hf in
/-- **Stacks 08TZ is natural in the base ring.** For a factorisation `a = φ ≫ a'` of
`a : A ⟶ B` through `a' : A' ⟶ B`, the inverse image of the change of base ring
`NL_{B/A} ⟶ NL_{B/A'}` of Stacks 08TX, read through the identifications
`f⁻¹ NL_{B/A} ≅ NL_{f⁻¹B/f⁻¹A}` and `f⁻¹ NL_{B/A'} ≅ NL_{f⁻¹B/f⁻¹A'}` of Stacks 08TZ, is the
change of base ring for the factorisation `f⁻¹a = f⁻¹φ ≫ f⁻¹a'`. -/
theorem inverseImageNaiveCotangentComplexIso_naturality
    [J.WEqualsLocallyBijective CommRingCat.{max u v w}] :
    ((inverseImageTargetModules.{u, v, w, u', v', w'} J K f
          (B := B)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (naiveCotangentComplexMapOfBase.{v', u', max u' v' w', max u' v' w'} K A B a A' a' φ hf) ≫
      (inverseImageNaiveCotangentComplexIso.{u, v, w, u', v', w'} J K f a').hom =
    (inverseImageNaiveCotangentComplexIso.{u, v, w, u', v', w'} J K f a).hom ≫
      naiveCotangentComplexMapOfBase.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
        (f.inverseImageRing.obj B) (f.inverseImageRing.map a) (f.inverseImageRing.obj A')
        (f.inverseImageRing.map a') (f.inverseImageRing.map φ)
        (inverseImageRing_map_fac J K f a a' φ hf) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  obtain rfl | h₀ := eq_or_ne n (-1)
  · rw [inverseImageNaiveCotangentComplexIso_hom_f_negOne,
      inverseImageNaiveCotangentComplexIso_hom_f_negOne, naiveCotangentComplexMapOfBase_f_negOne,
      naiveCotangentComplexMapOfBase_f_negOne]
    simp only [Functor.map_comp, Category.assoc, eqToHom_map, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    rw [← Category.assoc ((inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := B)).map _),
      inverseImageNaiveCotangentNegOneIso_naturality, Category.assoc]
  obtain rfl | h₁ := eq_or_ne n 0
  · rw [inverseImageNaiveCotangentComplexIso_hom_f_zero,
      inverseImageNaiveCotangentComplexIso_hom_f_zero, naiveCotangentComplexMapOfBase_f_zero,
      naiveCotangentComplexMapOfBase_f_zero]
    simp only [Functor.map_comp, Category.assoc, eqToHom_map, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    rw [← Category.assoc ((inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := B)).map _),
      inverseImageNaiveCotangentZeroTargetIso_naturality, Category.assoc]
  exact (naiveCotangentComplex_isZero_X.{v, u, max u v w, max u v w} J
    (f.inverseImageRing.obj A') (f.inverseImageRing.obj B) (f.inverseImageRing.map a') n h₀
    h₁).eq_of_tgt _ _

end InverseImageConormalBaseChangeSections

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules

section InverseImageEta

universe u

open CategoryTheory.Limits AlgebraicGeometry.SheafOfModules
open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.ToposPushforward
open CategoryTheory.Sheaf (inverseImageTargetModules)

attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J CommRingCat.{u}] [HasWeakSheafify K CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (f : MorphismOfTopoi (Sheaf J (Type u)) (Sheaf K (Type u)))
  {A B : Sheaf K CommRingCat.{u}} (a : A ⟶ B) [Presheaf.IsLocallySurjective K a.hom]

omit [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The constants on the inverse image, on classes.** For a local section `y` of the kernel
ideal of `f⁻¹a`, the class of the constant `y` in the conormal sheaf of the canonical
presentation of `f⁻¹B` is the image under `f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]` of the class of the image
of `y` under `f⁻¹` of the constants; as morphisms of sheaves of sets. -/
lemma conormalToNaiveCotangentConormal_inverseImagePresentationConormalIso :
    (Sheaf.moduleSheafFunctor (Tensor.ringSheaf.{u, u, u} (f.inverseImageRing.obj A))).map
        (conormalModuleHomEquivOf.{u, u, u} J (f.inverseImageRing.map a)
          (inverseImagePresentationRingHom.{u, u, u, u, u, u} f a)
          (inverseImageRingMap_presentationRingHom.{u, u, u, u, u, u} f a)
          (canonicalConormalSequence.{u, u, u, u} J (f.inverseImageRing.obj A)
            (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₁
          (conormalToNaiveCotangentConormal J (f.inverseImageRing.obj A)
            (f.inverseImageRing.obj B) (f.inverseImageRing.map a))) ≫
      eqToHom (moduleSheaf_restrictScalars (inverseImagePresentationRingHom.{u, u, u, u, u, u} f a)
        (canonicalConormalSequence.{u, u, u, u} J (f.inverseImageRing.obj A)
          (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₁) =
    (idealSheafSetsMap.{u, u, u} J
        (inverseImagePresentationRingHom.{u, u, u, u, u, u} f a)
        (inverseImagePresentationRingHom.{u, u, u, u, u, u} f (canonicalPresentation K A B a))
        (presentationRingHom.{u, u, u} J
          (f.inverseImageRing.map (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B))))
        (𝟙 _)
        (inverseImagePresentationRingHom_square.{u, u, u, u, u, u} f a
          (canonicalPresentation K A B a)
          (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B))
          (coefficientMap_comp_canonicalPresentation K A B a))) ≫
      (Sheaf.moduleSheafFunctor (Tensor.ringSheaf.{u, u, u}
          (f.inverseImageRing.obj (freeAlgebraSheaf K A (underlyingPresheaf K B))))).map
        (conormalModuleHomEquivOf.{u, u, u} J
          (f.inverseImageRing.map (canonicalPresentation K A B a))
          (inverseImagePresentationRingHom.{u, u, u, u, u, u} f (canonicalPresentation K A B a))
          (inverseImageRingMap_presentationRingHom.{u, u, u, u, u, u} f
            (canonicalPresentation K A B a))
          (canonicalConormalSequence.{u, u, u, u} J (f.inverseImageRing.obj A)
            (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₁
          (inverseImagePresentationConormalIso.{u, u, u, u, u, u} J K f a).hom) ≫
      eqToHom (moduleSheaf_restrictScalars
        (inverseImagePresentationRingHom.{u, u, u, u, u, u} f (canonicalPresentation K A B a))
        (canonicalConormalSequence.{u, u, u, u} J (f.inverseImageRing.obj A)
          (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₁) := by
  refine Sheaf.hom_ext_sections fun U y => ?_
  have hy := coe_mem_kernelIdeal.{u, u, u} J (f.inverseImageRing.map a)
    (inverseImagePresentationRingHom.{u, u, u, u, u, u} f a)
    (inverseImageRingMap_presentationRingHom.{u, u, u, u, u, u} f a) U y
  have l2 := conormalToNaiveCotangentConormal_conormalClass J (f.inverseImageRing.obj A)
    (f.inverseImageRing.obj B) (f.inverseImageRing.map a) (𝟙 _) U ⟨y.1, hy⟩
  have e := congrArg (fun g => g.hom.app U y.1)
    (map_coefficientMap_comp_inverseImageFreeAlgebraHom f A B)
  refine (sections_map_conormalModuleHomEquivOf_eqToHom.{u, u, u} J (f.inverseImageRing.map a)
    (inverseImagePresentationRingHom.{u, u, u, u, u, u} f a)
    (inverseImageRingMap_presentationRingHom.{u, u, u, u, u, u} f a)
    (f.inverseImageRing.obj A) (𝟙 _)
    (canonicalConormalSequence.{u, u, u, u} J (f.inverseImageRing.obj A)
      (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₁
    (conormalToNaiveCotangentConormal J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
      (f.inverseImageRing.map a)) U y).trans (l2.trans ?_)
  refine Eq.trans ?_ (sections_map_inverseImagePresentationConormalIso_hom.{u, u, u, u, u, u}
    J K f a U _).symm
  exact congrArg _ (Subtype.ext e.symm)

/-- The degree `-1` comparison of Stacks 08TZ for the canonical presentation, transported back
along the comparison for `a`, turns the inverse image of the map of conormal sheaves induced by
the constants into the map of conormal sheaves induced by the constants of `f⁻¹a`. -/
lemma inverseImageConormalIso_inv_comp_conormalToNaiveCotangentConormal :
    (inverseImageConormalIso.{u, u, u, u, u, u} f a).inv ≫
      (inverseImageTargetModules.{u, u, u, u, u, u} J K f (B := B)).map
        (conormalModuleMapOfTriangle.{u, u, u} a (canonicalPresentation K A B a)
          (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B))
          (coefficientMap_comp_canonicalPresentation K A B a)) ≫
      (inverseImageConormalIso.{u, u, u, u, u, u} f (canonicalPresentation K A B a)).hom ≫
      (inverseImagePresentationConormalIso.{u, u, u, u, u, u} J K f a).hom =
    (conormalToNaiveCotangentConormal J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
      (f.inverseImageRing.map a)) := by
  refine inverseImageConormalIso_inv_comp_map_comp_eq.{u, u, u, u, u, u} J K f a
    (canonicalPresentation K A B a)
    (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B))
    (coefficientMap_comp_canonicalPresentation K A B a) _ _ ?_
  have e6 := conormalToNaiveCotangentConormal_inverseImagePresentationConormalIso J K f a
  exact e6

/-- **The inverse image of the conormal sheaf is the conormal sheaf of the inverse image**:
`f⁻¹(I/I²) ≅ I'/I'²` for a locally surjective `a : A ⟶ B` with kernel `I` and `I' = Ker(f⁻¹a)`.
This is `Stacks.Sheaves.RingedToposModules.inverseImageConormalIso`, stated between the conormal
sheaves; on classes it is described by
`Stacks.Sheaves.RingedToposModules.inverseImage_conormalClassHom_comp_inverseImageConormalIso_hom`.
-/
noncomputable def inverseImageConormalSheafIso :
    (inverseImageTargetModules.{u, u, u, u, u, u} J K f (B := B)).obj
        (conormalSheaf.{u, u, u, u} K A B a) ≅
      conormalSheaf.{u, u, u, u} J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
        (f.inverseImageRing.map a) :=
  inverseImageConormalIso.{u, u, u, u, u, u} f a

/-- The map `conormalToNaiveCotangentConormal` is the map of conormal sheaves
`conormalModuleMapOfTriangle` induced by the coefficient map into the canonical presentation. -/
lemma conormalToNaiveCotangentConormal_eq_conormalModuleMapOfTriangle :
    conormalToNaiveCotangentConormal K A B a =
      conormalModuleMapOfTriangle.{u, u, u} a (canonicalPresentation K A B a)
        (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B))
        (coefficientMap_comp_canonicalPresentation K A B a) :=
  rfl

/-- The degree `-1` comparison of Stacks 08TZ for the canonical presentation carries the inverse
image of the map of conormal sheaves induced by the constants to the map of conormal sheaves
induced by the constants of `f⁻¹a`, through the identification of the conormal sheaves. -/
lemma inverseImage_conormalToNaiveCotangentConormal_comp_inverseImageNaiveCotangentNegOneIso :
    (inverseImageTargetModules.{u, u, u, u, u, u} J K f (B := B)).map
        (conormalToNaiveCotangentConormal K A B a) ≫
      (inverseImageNaiveCotangentNegOneIso.{u, u, u, u, u, u} J K f a).hom =
    (inverseImageConormalIso.{u, u, u, u, u, u} f a).hom ≫
      (conormalToNaiveCotangentConormal J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
        (f.inverseImageRing.map a)) := by
  rw [inverseImageNaiveCotangentNegOneIso_hom_eq,
    conormalToNaiveCotangentConormal_eq_conormalModuleMapOfTriangle]
  exact (Iso.inv_comp_eq _).1
    (inverseImageConormalIso_inv_comp_conormalToNaiveCotangentConormal J K f a)

/-- **The identification of Stacks 08TZ is compatible with `η`.** For a locally surjective
`a : A ⟶ B` with kernel `I`, the inverse image of the chain map `η : (I/I²)[1] ⟶ NL_{B/A}`,
read through the identification `f⁻¹ NL_{B/A} ≅ NL_{f⁻¹B/f⁻¹A}` of Stacks 08TZ, is the chain map
`η` of `f⁻¹a` precomposed with the identification `f⁻¹(I/I²) ≅ I'/I'²` of the conormal sheaves. -/
theorem inverseImageNaiveCotangentComplexIso_conormalToNaiveCotangentComplex :
    ((inverseImageTargetModules.{u, u, u, u, u, u} J K f (B := B)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (conormalToNaiveCotangentComplex K A B a) ≫
      (inverseImageNaiveCotangentComplexIso.{u, u, u, u, u, u} J K f a).hom =
    (HomologicalComplex.singleMapHomologicalComplex
        (inverseImageTargetModules.{u, u, u, u, u, u} J K f (B := B))
        (ComplexShape.up ℤ) (-1)).hom.app
          (conormalSheaf.{u, u, u, u} K A B a) ≫
      (CochainComplex.singleFunctor
        (_root_.SheafOfModules.{u} (Tensor.ringSheaf (f.inverseImageRing.obj B))) (-1)).map
          (inverseImageConormalSheafIso J K f a).hom ≫
      conormalToNaiveCotangentComplex J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
        (f.inverseImageRing.map a) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  obtain rfl | hn := eq_or_ne n (-1)
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, conormalToNaiveCotangentComplex_f_negOne,
      inverseImageNaiveCotangentComplexIso_hom_f_negOne,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      conormalToNaiveCotangentComplex_f_negOne]
    have hs : ((CochainComplex.singleFunctor
        (_root_.SheafOfModules.{u} (Tensor.ringSheaf (f.inverseImageRing.obj B))) (-1)).map
          (inverseImageConormalSheafIso J K f a).hom).f (-1) =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1)
            ((inverseImageTargetModules.{u, u, u, u, u, u} J K f (B := B)).obj
              (conormalSheaf.{u, u, u, u} K A B a))).hom ≫
          (inverseImageConormalSheafIso J K f a).hom ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1)
            (conormalSheaf.{u, u, u, u} J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
              (f.inverseImageRing.map a))).inv :=
      HomologicalComplex.single_map_f_self (ComplexShape.up ℤ) (-1) _
    rw [hs]
    simp only [Functor.map_comp, Category.assoc, eqToHom_map, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Iso.inv_hom_id_assoc]
    refine congrArg (_ ≫ ·) ?_
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ _) <|
      inverseImage_conormalToNaiveCotangentConormal_comp_inverseImageNaiveCotangentNegOneIso J K f a
  · exact IsZero.eq_of_src (Functor.map_isZero
      (inverseImageTargetModules.{u, u, u, u, u, u} J K f (B := B))
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (-1)
        (conormalSheaf.{u, u, u, u} K A B a) n hn)) _ _

end InverseImageEta

end Stacks.SheafOfModules
