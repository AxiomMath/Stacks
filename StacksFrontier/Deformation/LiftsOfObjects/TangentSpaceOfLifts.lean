module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Lift
public import StacksFrontier.Deformation.LiftsOfObjects.Basic
public import StacksFrontier.Deformation.PredeformationTangent.TangentVectorSpace
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Schlessinger.AssociatedFunctor
public import StacksFrontier.Deformation.Schlessinger.Basic
public import StacksFrontier.Deformation.TangentSpace.Functor

/-!
# Lifts to a square-zero extension and the tangent space of a localization

For an object `x₀` over the residue field, lifts of `x₀` along an augmentation `k[V] → k` are
the same thing as objects of the category localized at `x₀`, lying in the fibre over `k[V]`, up
to isomorphism. Under Schlessinger's condition (S2) these lifts carry a canonical `k`-vector
space structure, and it is the tangent space of the localized category tensored with `V`.

## Main definitions

* `Deformation.liftToLocalizedFiber` and `Deformation.localizedFiberToLift`: the comparison
  functors between lifts and the localized fibre.
* `Deformation.LiftTangentSpaceData`: the vector-space structure on isomorphism classes of lifts
  together with its tensor-product identification and the requirement that the identification
  agree with the canonical one.

## Main results

* `Deformation.liftClassesEquivObjectsOver`: lifts are the isomorphism classes of the localized
  fibre, compatibly with representatives.
* `Deformation.liftClassesTangentSpace`: under (S2), the isomorphism classes of lifts to `k[V]`
  form a vector space identified with the tangent space of the localized category tensored with
  `V`.
* `Deformation.liftClassesTangentSpace_naturality`: the identification is natural in the
  finite-dimensional vector space.

## References

* [Stacks Project, Tag 06JG](https://stacks.math.columbia.edu/tag/06JG)
-/

@[expose] public section

namespace Deformation

/-! ### Lifts as isomorphism classes in the localized fibre -/

section
open CategoryTheory

universe u w u₁ v₁

private theorem type_eqToHom_apply_cast {α β : Type v₁} (h : α = β) (x : α) :
    (eqToHom h : α ⟶ β) x = cast h x := by
  cases h
  rfl

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type u₁} [Category.{v₁} F]
variable (p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k)

/-- A lift of `x₀` along a morphism to the residue-field object, as an object of the localized
category in the source fibre. -/
public noncomputable def liftToLocalizedFiber
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (e : A ⟶ residueFieldObject Λ k)
    (x₀ : p.Fiber (residueFieldObject Λ k)) :
    Lift p e x₀ ⥤ (objectsOverFunctor p x₀.1).Fiber A where
  obj a :=
    ⟨Over.mk a.hom, by
      dsimp only [objectsOverFunctor]
      exact CategoryTheory.IsHomLift.domain_eq p e a.hom⟩
  map {a b} f := by
    let q := objectsOverFunctor p x₀.1
    let ha : q.obj (Over.mk a.hom) = A := CategoryTheory.IsHomLift.domain_eq p e a.hom
    let hb : q.obj (Over.mk b.hom) = A := CategoryTheory.IsHomLift.domain_eq p e b.hom
    refine ⟨Over.homMk f.hom f.fac, ?_⟩
    apply CategoryTheory.IsHomLift.of_fac' q (𝟙 A) (Over.homMk f.hom f.fac) ha hb
    change p.map f.hom = _
    simpa [q, objectsOverFunctor] using CategoryTheory.IsHomLift.fac' p (𝟙 A) f.hom
  map_id _ := CategoryTheory.Functor.Fiber.hom_ext rfl
  map_comp _ _ := CategoryTheory.Functor.Fiber.hom_ext rfl

/-- An object of the localized category in the source fibre, as a lift of `x₀`. -/
public noncomputable def localizedFiberToLift
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (e : A ⟶ residueFieldObject Λ k)
    (x₀ : p.Fiber (residueFieldObject Λ k)) :
    (objectsOverFunctor p x₀.1).Fiber A ⥤ Lift p e x₀ where
  obj y := by
    let a := y.1
    let hA : p.obj a.left = A := by
      dsimp only [objectsOverFunctor] at y
      exact y.2
    have hres :
        eqToHom hA.symm ≫ p.map a.hom ≫ eqToHom x₀.2 = e :=
      homToResidueFieldObject_unique _ _
    refine ⟨a.left, a.hom, CategoryTheory.IsHomLift.of_fac' p e a.hom hA x₀.2 ?_⟩
    simpa using congrArg (fun z => eqToHom hA ≫ z ≫ eqToHom x₀.2.symm) hres
  map {y z} f := by
    refine ⟨f.1.left, ?_, f.1.w⟩
    let q := objectsOverFunctor p x₀.1
    let _ : q.IsHomLift (𝟙 A) f.1 := f.2
    have hdom := CategoryTheory.IsHomLift.domain_eq q (𝟙 A) f.1
    have hcod := CategoryTheory.IsHomLift.codomain_eq q (𝟙 A) f.1
    apply CategoryTheory.IsHomLift.of_fac' p (𝟙 A) f.1.left hdom hcod
    simpa [q, objectsOverFunctor] using CategoryTheory.IsHomLift.fac' q (𝟙 A) f.1
  map_id _ := Lift.Hom.ext rfl
  map_comp _ _ := Lift.Hom.ext rfl

/-- The two comparison functors give a bijection on isomorphism classes. -/
public noncomputable def liftLocalizedClassesEquiv
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (e : A ⟶ residueFieldObject Λ k)
    (x₀ : p.Fiber (residueFieldObject Λ k)) :
    LiftClasses p e x₀ ≃
      ThinSkeleton ((objectsOverFunctor p x₀.1).Fiber A) where
  toFun := (ThinSkeleton.map (liftToLocalizedFiber p e x₀)).obj
  invFun := (ThinSkeleton.map (localizedFiberToLift p e x₀)).obj
  left_inv z := Quotient.inductionOn z fun a ↦ Quotient.sound ⟨eqToIso (by cases a; rfl)⟩
  right_inv z := Quotient.inductionOn z fun y ↦
    Quotient.sound ⟨eqToIso (by obtain ⟨val, _⟩ := y; cases val; rfl)⟩

/-- A lift of `x₀` along a square-zero augmentation is an object of the localized category over
`x₀` in the source fibre, up to isomorphism. -/
@[stacks 06JG "lifts as localized isomorphism classes"]
public noncomputable def liftClassesEquivObjectsOver
    (hp : IsCofiberedInGroupoids p)
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (e : A ⟶ residueFieldObject Λ k)
    (x₀ : p.Fiber (residueFieldObject Λ k)) :
    let q := objectsOverFunctor p x₀.1
    let hq := (isPredeformationCategory_objectsOverFunctor p hp x₀).cofibered
    { comparison : LiftClasses p e x₀ ≃
        (isomorphismClasses (BasedCategory.ofFunctor q) hq).obj A //
      ∀ a : Lift p e x₀, comparison (ThinSkeleton.mk a) =
        classOf (BasedCategory.ofFunctor q) hq
          (⟨Over.mk a.hom,
            IsHomLift.domain_eq p e a.hom⟩ : q.Fiber A) } := by
  let q := objectsOverFunctor p x₀.1
  let hq := (isPredeformationCategory_objectsOverFunctor p hp x₀).cofibered
  let 𝓕 := BasedCategory.ofFunctor q
  let H := isomorphismClasses 𝓕 hq
  let classEquiv := liftLocalizedClassesEquiv p e x₀
  let targetEquiv : H.obj A ≃ ThinSkeleton (q.Fiber A) :=
    Equiv.cast (isomorphismClasses_obj 𝓕 hq A)
  refine ⟨classEquiv.trans targetEquiv.symm, ?_⟩
  intro a
  apply targetEquiv.injective
  calc
    targetEquiv ((classEquiv.trans targetEquiv.symm) (ThinSkeleton.mk a)) =
        ThinSkeleton.mk ((liftToLocalizedFiber p e x₀).obj a) :=
      targetEquiv.apply_symm_apply _
    _ = targetEquiv (classOf 𝓕 hq
        (⟨Over.mk a.hom,
          CategoryTheory.IsHomLift.domain_eq p e a.hom⟩ : q.Fiber A)) :=
      (classOf_eq 𝓕 hq _).symm

/-- The natural vector-space structure on lifts, together with its linear identification with the
tangent space tensored with `V`. -/
public structure LiftTangentSpaceData
    (hp : IsCofiberedInGroupoids p)
    (hS2 : SchlessingerConditionS2 p)
    (x₀ : p.Fiber (residueFieldObject Λ k))
    (V : FGModuleCat.{w} k)
    (e : (squareZeroExtensionArtinian Λ k).obj V ⟶ residueFieldObject Λ k) where
  /-- The associated functor of the localized predeformation category satisfies (S2). -/
  associatedS2 :
    let q := objectsOverFunctor p x₀.1
    SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses
        (BasedCategory.ofFunctor q)
        (isPredeformationCategory_objectsOverFunctor p hp x₀).cofibered))
  /-- Addition on isomorphism classes of lifts. -/
  addCommGroup : AddCommGroup (LiftClasses p e x₀)
  /-- Scalar multiplication on isomorphism classes of lifts. -/
  module : letI := addCommGroup
    Module k (LiftClasses p e x₀)
  /-- The canonical tensor-product description of the lifts. -/
  equiv :
    let q := objectsOverFunctor p x₀.1
    let hpq := isPredeformationCategory_objectsOverFunctor p hp x₀
    letI : Fact (IsPredeformationCategory (BasedCategory.ofFunctor q).p) := ⟨hpq⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses
        (BasedCategory.ofFunctor q) hpq.cofibered))) := ⟨associatedS2⟩
    letI : AddCommGroup
      (artinianTangentSpace Λ k
        (isomorphismClasses (BasedCategory.ofFunctor q) hpq.cofibered)) :=
      associatedTangentSpaceAddCommGroupUnlifted (BasedCategory.ofFunctor q)
    letI : Module k
      (artinianTangentSpace Λ k
        (isomorphismClasses (BasedCategory.ofFunctor q) hpq.cofibered)) :=
      associatedTangentSpaceModuleUnlifted (BasedCategory.ofFunctor q)
    letI := addCommGroup
    letI := module
    TensorProduct k
      (artinianTangentSpace Λ k
        (isomorphismClasses (BasedCategory.ofFunctor q) hpq.cofibered))
      V ≃ₗ[k] LiftClasses p e x₀
  /-- The equivalence agrees pointwise with the canonical tensor map for the associated functor,
  after comparing lifts with localized isomorphism classes. -/
  canonical :
    let q := objectsOverFunctor p x₀.1
    let hpq := isPredeformationCategory_objectsOverFunctor p hp x₀
    let 𝓕 := BasedCategory.ofFunctor q
    let H := isomorphismClasses 𝓕 hpq.cofibered
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hpq⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π H)) :=
      ⟨associatedS2⟩
    letI : AddCommGroup (artinianTangentSpace Λ k H) :=
      associatedTangentSpaceAddCommGroupUnlifted 𝓕
    letI : Module k (artinianTangentSpace Λ k H) :=
      associatedTangentSpaceModuleUnlifted 𝓕
    letI := addCommGroup
    letI := module
    ∀ z : TensorProduct k (artinianTangentSpace Λ k H) V,
      (liftClassesEquivObjectsOver p hp e x₀).1 (equiv z) =
        cast (congrArg (fun G : FGModuleCat.{w} k ⥤ Type (max u₁ v₁) ↦ G.obj V)
          (associatedTangentSpaceModuleStructureUnlifted 𝓕 hpq associatedS2).forget_comp)
          (associatedTangentSpaceFunctor_iso_tensorLeftUnlifted 𝓕 hpq associatedS2 V z)

/-- Under (S2), the lifts to `k[V]` are the tangent space of the category localized at `x₀`,
tensored with `V`, as vector spaces. -/
@[stacks 06JG "tangent-space tensor identification"]
public noncomputable def liftClassesTangentSpace
    (hp : IsCofiberedInGroupoids p)
    (hS2 : SchlessingerConditionS2 p)
    (x₀ : p.Fiber (residueFieldObject Λ k))
    (V : FGModuleCat.{w} k)
    (e : (squareZeroExtensionArtinian Λ k).obj V ⟶ residueFieldObject Λ k) :
    LiftTangentSpaceData p hp hS2 x₀ V e := by
  let q := objectsOverFunctor p x₀.1
  let hpq := isPredeformationCategory_objectsOverFunctor p hp x₀
  let 𝓕 := BasedCategory.ofFunctor q
  let H := isomorphismClasses 𝓕 hpq.cofibered
  let hS2q := schlessingerConditionS2_objectsOverFunctor p x₀.1 hS2
  let associatedS2 :=
    schlessingerConditionS2_of_isIsomorphismClasses 𝓕 hpq.cofibered hS2q (.inl hpq)
  let moduleStructure := associatedTangentSpaceModuleStructureUnlifted 𝓕 hpq associatedS2
  let L := moduleStructure.functor
  let A := (squareZeroExtensionArtinian Λ k).obj V
  let comparison := liftClassesEquivObjectsOver p hp e x₀
  let hcarrier :
      ((L.obj V : ModuleCat.{max u₁ v₁} k) : Type (max u₁ v₁)) = H.obj A :=
    congrArg (fun G : FGModuleCat.{w} k ⥤ Type (max u₁ v₁) ↦ G.obj V)
      moduleStructure.forget_comp
  let hcarrierEquiv := Equiv.cast hcarrier
  letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hpq⟩
  letI : Fact (SchlessingerConditionS2 (Functor.Elements.π H)) := ⟨associatedS2⟩
  letI : AddCommGroup (artinianTangentSpace Λ k H) :=
    associatedTangentSpaceAddCommGroupUnlifted 𝓕
  letI : Module k (artinianTangentSpace Λ k H) :=
    associatedTangentSpaceModuleUnlifted 𝓕
  letI : AddCommGroup (H.obj A) := Equiv.addCommGroup hcarrierEquiv.symm
  letI : Module k (H.obj A) := (Equiv.addEquiv hcarrierEquiv.symm).module k
  letI : AddCommGroup (LiftClasses p e x₀) := Equiv.addCommGroup comparison.1
  letI : Module k (LiftClasses p e x₀) := (Equiv.addEquiv comparison.1).module k
  let hcarrierLinear :
      ((L.obj V : ModuleCat.{max u₁ v₁} k) : Type (max u₁ v₁)) ≃ₗ[k] H.obj A :=
    ((Equiv.addEquiv hcarrierEquiv.symm).linearEquiv k).symm
  let tangentEquiv :=
    associatedTangentSpaceFunctor_iso_tensorLeftUnlifted 𝓕 hpq associatedS2 V
  let equiv : TensorProduct k (artinianTangentSpace Λ k H) V ≃ₗ[k]
      LiftClasses p e x₀ :=
    tangentEquiv.trans
      (hcarrierLinear.trans ((Equiv.addEquiv comparison.1).linearEquiv k).symm)
  refine
    { associatedS2 := associatedS2
      addCommGroup := inferInstance
      module := inferInstance
      equiv := equiv
      canonical := ?_ }
  change ∀ z : TensorProduct k (artinianTangentSpace Λ k H) V,
    comparison.1 (equiv z) =
      cast (congrArg (fun G : FGModuleCat.{w} k ⥤ Type (max u₁ v₁) ↦ G.obj V)
        moduleStructure.forget_comp)
        (associatedTangentSpaceFunctor_iso_tensorLeftUnlifted
          𝓕 hpq associatedS2 V z)
  intro z
  change comparison.1 (equiv z) = cast hcarrier (tangentEquiv z)
  simp [equiv, hcarrierLinear, comparison, hcarrierEquiv, tangentEquiv]

/-- The tensor identification of lifts commutes with every linear map of finite-dimensional vector
spaces, using the induced map on localized lifts. -/
@[stacks 06JG "naturality in the vector space"]
public theorem liftClassesTangentSpace_naturality
    (hp : IsCofiberedInGroupoids p)
    (hS2 : SchlessingerConditionS2 p)
    (x₀ : p.Fiber (residueFieldObject Λ k))
    (V W : FGModuleCat.{w} k)
    (eV : (squareZeroExtensionArtinian Λ k).obj V ⟶ residueFieldObject Λ k)
    (eW : (squareZeroExtensionArtinian Λ k).obj W ⟶ residueFieldObject Λ k)
    (f : V ⟶ W) :
    let q := objectsOverFunctor p x₀.1
    let hpq := isPredeformationCategory_objectsOverFunctor p hp x₀
    let H := isomorphismClasses (BasedCategory.ofFunctor q) hpq.cofibered
    let DV := liftClassesTangentSpace p hp hS2 x₀ V eV
    let DW := liftClassesTangentSpace p hp hS2 x₀ W eW
    letI : Fact (IsPredeformationCategory (BasedCategory.ofFunctor q).p) := ⟨hpq⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π H)) := ⟨DV.associatedS2⟩
    letI : AddCommGroup (artinianTangentSpace Λ k H) :=
      associatedTangentSpaceAddCommGroupUnlifted (BasedCategory.ofFunctor q)
    letI : Module k (artinianTangentSpace Λ k H) :=
      associatedTangentSpaceModuleUnlifted (BasedCategory.ofFunctor q)
    ∀ z : TensorProduct k (artinianTangentSpace Λ k H) V,
      (liftClassesEquivObjectsOver p hp eW x₀).1
          (DW.equiv (TensorProduct.map
            (LinearMap.id : artinianTangentSpace Λ k H →ₗ[k]
              artinianTangentSpace Λ k H) f.hom.hom z)) =
        H.map ((squareZeroExtensionArtinian Λ k).map f)
          ((liftClassesEquivObjectsOver p hp eV x₀).1 (DV.equiv z)) := by
  let q := objectsOverFunctor p x₀.1
  let hpq := isPredeformationCategory_objectsOverFunctor p hp x₀
  let 𝓕 := BasedCategory.ofFunctor q
  let H := isomorphismClasses 𝓕 hpq.cofibered
  let DV := liftClassesTangentSpace p hp hS2 x₀ V eV
  let DW := liftClassesTangentSpace p hp hS2 x₀ W eW
  let associatedS2 := DV.associatedS2
  let moduleStructure := associatedTangentSpaceModuleStructureUnlifted 𝓕 hpq associatedS2
  let L := moduleStructure.functor
  have hfun := moduleStructure.forget_comp
  let g := (squareZeroExtensionArtinian Λ k).map f
  let Fset := tangentSpaceSetFunctor Λ k
    (artinianLocalOver Λ k)
    (squareZeroExtension_mem_artinianLocalOver Λ k)
    (artinianLocalOverToArtinian Λ k ⋙ H)
  let hobj (X : FGModuleCat.{w} k) :
      ((L.obj X : ModuleCat.{max u₁ v₁} k) : Type (max u₁ v₁)) = Fset.obj X :=
    congrArg (fun G : FGModuleCat.{w} k ⥤ Type (max u₁ v₁) ↦ G.obj X) hfun
  let tangentMap := associatedTangentSpaceFunctor_iso_tensorLeftUnlifted 𝓕 hpq associatedS2
  let forgetIso : (L ⋙ CategoryTheory.forget (ModuleCat.{max u₁ v₁} k)) ≅ Fset :=
    eqToIso hfun
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨hpq⟩
  let : Fact (SchlessingerConditionS2 (Functor.Elements.π H)) := ⟨associatedS2⟩
  let : AddCommGroup (artinianTangentSpace Λ k H) :=
    associatedTangentSpaceAddCommGroupUnlifted 𝓕
  let : Module k (artinianTangentSpace Λ k H) :=
    associatedTangentSpaceModuleUnlifted 𝓕
  have happ (X : FGModuleCat.{w} k) : forgetIso.hom.app X = eqToHom (hobj X) :=
    CategoryTheory.eqToHom_app hfun X
  have hcomm (y : (L.obj V : ModuleCat.{max u₁ v₁} k)) :
      Fset.map f (cast (hobj V) y) = cast (hobj W) ((L.map f).hom y) := by
    have hh := forgetIso.hom.naturality f
    rw [happ, happ] at hh
    have hhx := ConcreteCategory.congr_hom hh y
    rw [types_comp_apply, types_comp_apply, type_eqToHom_apply_cast,
      type_eqToHom_apply_cast] at hhx
    exact hhx.symm
  change ∀ z : TensorProduct k (artinianTangentSpace Λ k H) V, _
  intro z
  rw [DW.canonical, DV.canonical]
  have hnat := associatedTangentSpaceFunctor_iso_tensorLeft_naturalityUnlifted
    𝓕 hpq associatedS2 V W f z
  have hcomp :
      cast (hobj W) (tangentMap W
        (TensorProduct.map
          (LinearMap.id : artinianTangentSpace Λ k H →ₗ[k]
            artinianTangentSpace Λ k H) f.hom.hom z)) =
        Fset.map f (cast (hobj V) (tangentMap V z)) :=
    (congrArg (cast (hobj W)) hnat.symm).trans (hcomm (tangentMap V z)).symm
  convert hcomp using 1
  rfl

end

end Deformation
