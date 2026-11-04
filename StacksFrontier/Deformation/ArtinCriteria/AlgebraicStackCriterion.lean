module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.SpecField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphismSupplement
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.Stalk
public import StacksFrontier.Deformation.Artin.Approximation
public import StacksFrontier.Deformation.Artin.Basic
public import StacksFrontier.Deformation.Artin.ChangeOfField
public import StacksFrontier.Deformation.Artin.FormalObject.Predeformation
public import StacksFrontier.Deformation.Artin.FormalObject.Versal
public import StacksFrontier.Deformation.Artin.LimitPreserving
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximationSupplement
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.PredeformationTangent.TangentVectorSpace
public import StacksFrontier.Deformation.RimSchlessinger.Basic
public import StacksFrontier.Deformation.Schlessinger.VersalExistence
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses
public import StacksFrontier.Deformation.TangentSpace.LiftedComparison
import all StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation.LengthCriterion
import all StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation.ResidueFieldTransport

/-!
# Artin's criterion for algebraicity

## Main results

* `Deformation.Artin.exists_versal_finiteTypePoint` is the first step of the proof of
  **Stacks 07XY**: a finite-type field-valued object of a fibred category satisfying Artin's
  axioms extends to an object over a quasi-compact finite-type base which is versal at a finite
  type point carrying the prescribed residue field.  The remaining steps, and the whole tag, are
  `Deformation.Artin.exists_smooth_finiteType_neighborhood` in
  `StacksFrontier.Deformation.ArtinCriteria.SmoothNeighborhood`.

## References

* [Stacks Project, Tag 07Y4](https://stacks.math.columbia.edu/tag/07Y4)
* [Stacks Project, Tag 07XY](https://stacks.math.columbia.edu/tag/07XY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
attribute [local implicit_reducible] CategoryTheory.Over.post
attribute [local implicit_reducible] CategoryTheory.Functor.Elements
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber.fiberInclusion
attribute [local implicit_reducible] Deformation.Artin.baseOver
attribute [local implicit_reducible] Deformation.Artin.truncationOver

namespace Deformation.Artin

universe u v w

/-! ### The local ring at a finite type point of the base -/

/-- The canonical map from the local ring at the image point of a field-valued point
factors that point through the spectrum of the local ring. -/
private theorem stalk_map_factors_through
    (S : Scheme.{u}) (k : Type u) [Field k]
    (i₀ : Spec (.of k) ⟶ S) (s : S)
    (hs : i₀ (IsLocalRing.closedPoint k) = s) :
    letI : Algebra (S.presheaf.stalk s) k :=
      (eqToHom (congrArg S.presheaf.stalk hs).symm ≫
        Scheme.stalkClosedPointTo i₀).hom.toAlgebra
    Spec.map (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk s) k)) ≫ S.fromSpecStalk s = i₀ := by
  cases hs
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk i₀

/-- A quasi-compact field-valued point locally of finite type has finite residue
field extension. -/
private theorem finite_residue_extension_of_finite_point
    (S : Scheme.{u}) (k : Type u) [Field k]
    (i₀ : Spec (.of k) ⟶ S) (_s : S)
    (hfinite : LocallyOfFiniteType i₀) (hqc : QuasiCompact i₀) :
    let q := Scheme.SpecToEquivOfField k S i₀
    letI : Algebra (S.residueField q.1) k := q.2.hom.toAlgebra
    Module.Finite (S.residueField q.1) k := by
  dsimp only
  obtain ⟨U, hU, x, hx, hclosed, hfiniteκ⟩ :=
    ((AlgebraicGeometry.finiteType_specField_tfae i₀).out 1 4).mp
      (show LocallyOfFiniteType i₀ ∧ QuasiCompact i₀ from ⟨hfinite, hqc⟩)
  exact hfiniteκ

/-- The field of a quasi-compact field-valued point locally of finite type is a finite
module over the local ring at its image. -/
private theorem finite_stalk_to_field
    (S : Scheme.{u}) (k : Type u) [Field k]
    (i₀ : Spec (.of k) ⟶ S)
    (hfinite : LocallyOfFiniteType i₀) (hqc : QuasiCompact i₀) :
    let q := Scheme.SpecToEquivOfField k S i₀
    letI : Algebra (S.presheaf.stalk q.1) k :=
      (q.2.hom.comp (S.residue q.1).hom).toAlgebra
    Module.Finite (S.presheaf.stalk q.1) k := by
  dsimp only
  let q := Scheme.SpecToEquivOfField k S i₀
  let κ := S.residueField q.1
  let : Algebra (S.presheaf.stalk q.1) κ := (S.residue q.1).hom.toAlgebra
  let : Algebra κ k := q.2.hom.toAlgebra
  let : Algebra (S.presheaf.stalk q.1) k :=
    (q.2.hom.comp (S.residue q.1).hom).toAlgebra
  let : IsScalarTower (S.presheaf.stalk q.1) κ k :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite (S.presheaf.stalk q.1) κ :=
    .of_surjective (Algebra.linearMap _ κ) (S.residue_surjective q.1)
  have : Module.Finite κ k :=
    finite_residue_extension_of_finite_point S k i₀ q.1 hfinite hqc
  exact Module.Finite.trans κ k

/-! ### Base maps of arrows between field-valued points -/

/-- Comparing two presentations of the base of an object identifies the arrow out of a
field-valued point with the spectrum of the corresponding map of fields. -/
private theorem base_relation
    {Λ k k' : Type u} [CommRing Λ] [Field k] [Field k'] [Algebra Λ k]
    [Algebra Λ k']
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    {X : Type v} [Category.{w} X] (q : X ⥤ Over S)
    (x₀ x₁ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₁ : q.obj x₁ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k')) ≫ iΛ))
    {A₀ : Type u} [CommRing A₀] [Algebra Λ A₀]
    (b : q.obj x₁ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ A₀)) ≫ iΛ))
    (ra : A₀ →+* k) (ra' : A₀ →+* k') (e : k' →+* k)
    (ρ : x₀ ⟶ x₁)
    (hρ : eqToHom (congrArg Over.left hx₀).symm ≫ (q.map ρ).left ≫
      eqToHom (congrArg Over.left b) = Spec.map (CommRingCat.ofHom ra))
    (hC : eqToHom (congrArg Over.left hx₁).symm ≫
      eqToHom (congrArg Over.left b) = Spec.map (CommRingCat.ofHom ra'))
    (hcomp : ra = e.comp ra') :
    eqToHom (congrArg Over.left hx₀).symm ≫ (q.map ρ).left ≫
      eqToHom (congrArg Over.left hx₁) = Spec.map (CommRingCat.ofHom e) := by
  have : IsIso (Spec.map (CommRingCat.ofHom ra')) := by
    rw [← hC]
    infer_instance
  have hv : eqToHom (congrArg Over.left b) =
      eqToHom (congrArg Over.left hx₁) ≫ Spec.map (CommRingCat.ofHom ra') := by
    rw [← hC]
    simp
  have hRHS : Spec.map (CommRingCat.ofHom e) ≫ Spec.map (CommRingCat.ofHom ra') =
      Spec.map (CommRingCat.ofHom ra) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  have hLHS : (eqToHom (congrArg Over.left hx₀).symm ≫ (q.map ρ).left ≫
        eqToHom (congrArg Over.left hx₁)) ≫ Spec.map (CommRingCat.ofHom ra') =
      Spec.map (CommRingCat.ofHom ra) := by
    rw [← hρ, hv]
    simp
  exact (cancel_mono (Spec.map (CommRingCat.ofHom ra'))).mp
    (hLHS.trans hRHS.symm)

/-- The underlying map of schemes of an arrow of the site is the image of its map of
site objects. -/
private theorem post_map_left
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : Type v} [Category.{w} X] (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    {x y : X} (ρ : x ⟶ y) :
    ((p ⋙ Over.post B.inclusion).map ρ).left =
      B.inclusion.map ((p.map ρ).left) := rfl

/-- A strongly Cartesian arrow whose underlying map of schemes is an isomorphism is an
isomorphism. -/
private theorem isIso_of_isStronglyCartesian_of_left_isIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type v} [Category.{w} X] (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    {x y : X} (ρ : x ⟶ y)
    [p.IsStronglyCartesian (p.map ρ) ρ]
    (h : IsIso (((p ⋙ Over.post B.inclusion).map ρ).left)) :
    IsIso ρ := by
  have h0 : IsIso (B.inclusion.map ((p.map ρ).left)) := h
  have h1 : IsIso ((p.map ρ).left) :=
    isIso_of_fully_faithful B.inclusion ((p.map ρ).left)
  have h2 : IsIso ((Over.forget (B.obj hS)).map (p.map ρ)) := h1
  have h3 : IsIso (p.map ρ) :=
    isIso_of_reflects_iso (p.map ρ) (Over.forget (B.obj hS))
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso p (p.map ρ) ρ

/-- The arrow from a field-valued point to a deformation over an Artinian algebra whose
residue field is identified with another field is the spectrum of that identification. -/
private theorem base_relation'
    {Λ k k' : Type u} [CommRing Λ] [Field k] [Field k'] [Algebra Λ k]
    [Algebra Λ k']
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    {X : Type v} [Category.{w} X] (q : X ⥤ Over S)
    (x₀ x₁ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₁ : q.obj x₁ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k')) ≫ iΛ))
    (e : k' ≃ₐ[Λ] k)
    (AC : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k')
    (AD : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hADC : AD = (artinianChangeResidueField e).obj AC)
    (bD : q.obj x₁ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ AD)) ≫ iΛ))
    (bC : q.obj x₁ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ AC)) ≫ iΛ))
    (ρ : x₀ ⟶ x₁)
    (hρ : eqToHom (congrArg Over.left hx₀).symm ≫ (q.map ρ).left ≫
      eqToHom (congrArg Over.left bD) =
        Spec.map (CommRingCat.ofHom (residueMap AD)))
    (hC : eqToHom (congrArg Over.left hx₁).symm ≫
      eqToHom (congrArg Over.left bC) =
        Spec.map (CommRingCat.ofHom (residueMap AC))) :
    eqToHom (congrArg Over.left hx₀).symm ≫ (q.map ρ).left ≫
      eqToHom (congrArg Over.left hx₁) =
      Spec.map (CommRingCat.ofHom (e.toRingHom : k' →+* k)) := by
  subst hADC
  exact base_relation iΛ q x₀ x₁ hx₀ hx₁ bC
    (residueMap ((artinianChangeResidueField e).obj AC))
    (residueMap AC) e.toRingHom ρ hρ hC
    (artinianChangeResidueField_residueMap e AC)

/-- A deformation whose arrow out of the field-valued point is the identity presents that
point itself over the Artinian algebra. -/
private theorem closedPoint_base_relation
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    {X : Type v} [Category.{w} X] (q : X ⥤ Over S)
    (x₁ y : X)
    (hx₁ : q.obj x₁ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (bA : q.obj y = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ))
    (arr : x₁ ⟶ y)
    (harrb : eqToHom (congrArg Over.left hx₁).symm ≫ (q.map arr).left ≫
      eqToHom (congrArg Over.left bA) =
        Spec.map (CommRingCat.ofHom (residueMap A)))
    (hpt : y = x₁) (harr : HEq arr (𝟙 x₁)) :
    ∃ b : q.obj x₁ = Over.mk
        (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ),
      eqToHom (congrArg Over.left hx₁).symm ≫
        eqToHom (congrArg Over.left b) =
        Spec.map (CommRingCat.ofHom (residueMap A)) := by
  subst hpt
  obtain rfl : arr = 𝟙 y := eq_of_heq harr
  exact ⟨bA, by simpa using harrb⟩

/-! ### Limit preservation on objects -/

section LimitPreserving

universe uI vCat uCat

/-- A type promoted to a category with a single morphism in a prescribed universe between
any two objects. -/
private structure CodiscreteV (A : Type uCat) where
  /-- The underlying element. -/
  as : A

/-- The codiscrete category structure with homs in a prescribed universe. -/
@[instance_reducible]
private def codiscreteVCategory (A : Type uCat) : Category.{vCat, uCat} (CodiscreteV A) where
  Hom _ _ := PUnit.{vCat + 1}
  id _ := PUnit.unit
  comp _ _ := PUnit.unit
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

attribute [local instance] codiscreteVCategory

/-- The codiscrete category on a type, as an object of `Cat`. -/
private def codiscreteV (A : Type uCat) : Cat.{vCat, uCat} := Cat.of (CodiscreteV A)

/-- A function induces a functor between codiscrete categories. -/
private def codiscreteVMap {A B : Type uCat} (f : A → B) : CodiscreteV A ⥤ CodiscreteV B where
  obj x := ⟨f x.as⟩
  map _ := ⟨⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The codiscrete-category functor with homs in a prescribed universe. -/
private def codiscreteVFunctor : Type uCat ⥤ Cat.{vCat, uCat} where
  obj := codiscreteV
  map f := (codiscreteVMap f).toCatHom
  map_id _ := Cat.Hom.ext <| CategoryTheory.Functor.ext
    (fun x => by cases x; rfl) (fun _ _ _ => by change PUnit.unit = PUnit.unit; rfl)
  map_comp _ _ := Cat.Hom.ext <| CategoryTheory.Functor.ext
    (fun x => by cases x; rfl) (fun _ _ _ => by change PUnit.unit = PUnit.unit; rfl)

/-- The objects functor is left adjoint to the codiscrete-category functor. -/
private def codiscreteVAdj : Cat.objects ⊣ codiscreteVFunctor := Adjunction.mkOfHomEquiv {
  homEquiv C A := {
    toFun := fun f => Functor.toCatHom {
      obj := fun x => ⟨f.hom x⟩
      map := fun _ => ⟨⟩
      map_id _ := rfl
      map_comp _ _ := rfl }
    invFun := fun F => ↾fun x => (F.toFunctor.obj x).as
    left_inv := by intro f; ext x; rfl
    right_inv F := Cat.Hom.ext <| CategoryTheory.Functor.ext
      (fun x => by
        change CodiscreteV.mk ((F.toFunctor.obj x).as) = F.toFunctor.obj x
        cases F.toFunctor.obj x
        rfl)
      (fun _ _ _ => by change PUnit.unit = PUnit.unit; rfl) }
  homEquiv_naturality_left_symm _ _ := rfl
  homEquiv_naturality_right _ _ := rfl }

/-- Every object of a filtered colimit of categories comes from a stage. -/
private theorem colimit_obj_represented {I : Type uI} [Category.{w} I] [IsFiltered I]
    (F : I ⥤ Cat.{vCat, uCat}) [HasColimit F] (x : Cat.objects.obj (colimit F)) :
    ∃ (i : I) (a : F.obj i), (colimit.ι F i).toFunctor.obj a = x := by
  let : PreservesColimitsOfShape I Cat.objects :=
    codiscreteVAdj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  let G := F ⋙ Cat.objects
  let hc : IsColimit (Cat.objects.mapCocone (colimit.cocone F)) :=
    isColimitOfPreserves Cat.objects (colimit.isColimit F)
  let e := hc.coconePointUniqueUpToIso (colimit.isColimit G)
  obtain ⟨i, a, ha⟩ := Concrete.colimit_exists_rep G (e.hom.hom x)
  refine ⟨i, a, ?_⟩
  have hi : Cat.objects.map (colimit.ι F i) ≫ e.hom = colimit.ι G i := by
    show Cat.objects.map (colimit.ι F i) ≫ hc.desc (colimit.cocone G) = _
    exact hc.fac (colimit.cocone G) i
  exact (isIso_iff_bijective e.hom).1 inferInstance |>.1 <|
    (congrArg (fun f : TypeCat.Hom _ _ => f.hom a) hi).trans ha

/-- A fibred category whose objects over an affine inverse limit descend to a finite stage
is limit preserving on objects for its structure morphism. -/
private theorem isLimitPreservingOnObjects_of_object_descends
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (hdesc : letI : X.val.p.IsFibered := X.property.isFibered
      ∀ (I : Type uI) [Category.{vCat} I] [IsCofiltered I]
        (D : I ⥤ AlgebraicGeometry.BigAffineFppf B S hS) (c : Cone D),
        IsLimit ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).mapCone c) →
        ∀ (i : I) (x : X.val.p.Fiber
          ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj c.pt)),
        ∃ (i' : I) (_ : i' ⟶ i)
          (x' : X.val.p.Fiber
            ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj (D.obj i'))),
          Nonempty (Functor.pullbackFiber X.val.p x'
            ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i')) ≅ x)) :
    AlgebraicGeometry.BigFppfOver.IsLimitPreservingOnObjects.{u, uI, vCat, u, u + 1} B S hS X
      (Approximation.baseFiberedCategory B S hS)
      (Approximation.structureMorphism B S hS X) := by
  let C := AlgebraicGeometry.BigFppfOver B S hS
  let inc := AlgebraicGeometry.BigAffineFppf.inclusion B S hS
  let p := X.val.p
  let : p.IsFibered := X.property.isFibered
  intro I instCat instCof D c hc i y x gamma hgamma
  obtain ⟨i', j, x', ⟨eβ⟩⟩ := hdesc I D c hc i x
  let xU := Functor.pullbackFiber p x' (inc.map (c.π.app i'))
  let δ : xU.1 ⟶ x'.1 := Functor.IsPreFibered.pullbackMap x'.2
    (inc.map (c.π.app i'))
  let β : xU.1 ⟶ x.1 := Functor.Fiber.fiberInclusion.map eβ.hom
  let γ' : p.obj x'.1 ⟶ y.1 :=
    eqToHom x'.2 ≫ inc.map (D.map j) ≫ eqToHom y.2.symm
  have hdelta : p.IsStronglyCartesian (inc.map (c.π.app i')) δ := by
    let : p.IsCartesian (inc.map (c.π.app i')) δ :=
      Functor.IsPreFibered.pullbackMap.IsCartesian x'.2 (inc.map (c.π.app i'))
    infer_instance
  have hbeta : p.IsHomLift (𝟙 (inc.obj c.pt)) β := eβ.hom.2
  have hbetaIso : IsIso β := Functor.map_isIso _ eβ.hom
  have hgamma' : (𝟭 C).IsStronglyCartesian (inc.map (D.map j)) γ' := by
    let : (𝟭 C).IsHomLift (inc.map (D.map j)) γ' :=
      IsHomLift.of_fac' (𝟭 C) (inc.map (D.map j)) γ' x'.2 y.2 rfl
    exact Functor.isFiberedInGroupoids_id.isStronglyCartesian_homLift
      (inc.map (D.map j)) γ'
  refine ⟨i', j, x', xU, δ, β, γ', hdelta, hbeta, hbetaIso, hgamma', ?_⟩
  show p.map δ ≫ γ' = p.map β ≫ gamma
  have hδfac : p.map δ =
      eqToHom xU.2 ≫ inc.map (c.π.app i') ≫ eqToHom x'.2.symm := by
    simpa using IsHomLift.fac' p (inc.map (c.π.app i')) δ
  have hβfac : p.map β =
      eqToHom xU.2 ≫ 𝟙 (inc.obj c.pt) ≫ eqToHom x.2.symm := by
    simpa using IsHomLift.fac' p (𝟙 (inc.obj c.pt)) β
  have hγ : gamma =
      eqToHom x.2 ≫ inc.map (c.π.app i) ≫ eqToHom y.2.symm := by
    let : (𝟭 C).IsHomLift (inc.map (c.π.app i)) gamma := hgamma.toIsHomLift
    exact IsHomLift.fac' (𝟭 C) (inc.map (c.π.app i)) gamma
  have hδcomp : p.map δ ≫ eqToHom x'.2 =
      eqToHom xU.2 ≫ inc.map (c.π.app i') := by
    rw [hδfac]
    simp [Category.assoc]
  have hβcomp : p.map β ≫ eqToHom x.2 = eqToHom xU.2 := by
    rw [hβfac]
    simp
  have hcone : inc.map (c.π.app i') ≫ inc.map (D.map j) =
      inc.map (c.π.app i) := by
    rw [← Functor.map_comp, c.w j]
  have hconeWhisker :
      (eqToHom xU.2 ≫ inc.map (c.π.app i')) ≫
          (inc.map (D.map j) ≫ eqToHom y.2.symm) =
        eqToHom xU.2 ≫ inc.map (c.π.app i) ≫ eqToHom y.2.symm := by
    simpa [Category.assoc] using
      congrArg (fun f => eqToHom xU.2 ≫ f ≫ eqToHom y.2.symm) hcone
  have hsplit : p.map δ ≫ γ' =
      (p.map δ ≫ eqToHom x'.2) ≫ (inc.map (D.map j) ≫ eqToHom y.2.symm) :=
    (Category.assoc _ _ _).symm
  rw [hγ, hsplit, hδcomp, hconeWhisker, ← hβcomp]
  exact Category.assoc _ _ _

/-- A limit preserving fibred category is limit preserving on objects for its structure
morphism. -/
private theorem isLimitPreservingOnObjects_of_isLimitPreserving
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (hLP : Deformation.Artin.IsLimitPreserving.{u, uI, vCat, u + 1, u} B S hS X) :
    AlgebraicGeometry.BigFppfOver.IsLimitPreservingOnObjects.{u, uI, vCat, u, u + 1} B S hS X
      (Approximation.baseFiberedCategory B S hS)
      (Approximation.structureMorphism B S hS X) := by
  let inc := AlgebraicGeometry.BigAffineFppf.inclusion B S hS
  let p := X.val.p
  let : p.IsFibered := X.property.isFibered
  apply isLimitPreservingOnObjects_of_object_descends B S hS X
  intro I instCat instCof D c hc i x
  let D' := D ⋙ inc
  let c' := inc.mapCone c
  let F := Deformation.Artin.fiberDiagram p D'
  let cmp := Deformation.Artin.colimitComparison p D' c'
  have : cmp.IsEquivalence := hLP I D c hc
  obtain ⟨z, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage cmp x
  obtain ⟨j₀, a₀, ha₀⟩ := colimit_obj_represented F z
  let hcommon := IsFilteredOrEmpty.cocone_objs (Opposite.op i) j₀
  let k := hcommon.choose
  let fᵢ : Opposite.op i ⟶ k := hcommon.choose_spec.choose
  let f₀ : j₀ ⟶ k := hcommon.choose_spec.choose_spec.choose
  let i' := k.unop
  let j : i' ⟶ i := fᵢ.unop
  let a' := (F.map f₀).toFunctor.obj a₀
  have haStage : (colimit.ι F k).toFunctor.obj a' =
      (colimit.ι F j₀).toFunctor.obj a₀ := by
    have h := congrArg (fun g : Cat.Hom (F.obj j₀) (colimit F) => g.toFunctor.obj a₀)
      (colimit.w F f₀)
    simpa only [Cat.Hom.comp_toFunctor, Functor.comp_obj, a'] using h
  have ha' : (colimit.ι F k).toFunctor.obj a' = z := haStage.trans ha₀
  let stageIso := Deformation.Artin.colimitComparisonStageIso p D' c' i'
  let aSplit : p.SplitFiber (D'.obj i') :=
    AsSmall.down.{u, u + 1, max uI vCat}.obj a'
  let x' : p.Fiber (inc.obj (D.obj i')) := aSplit.toFiber
  let xU : p.Fiber (inc.obj c.pt) :=
    ((Functor.chosenPullbacks p).pullbackFunctor (inc.map (c.π.app i'))).obj x'
  let eStage : cmp.obj ((colimit.ι F k).toFunctor.obj a') ≅ x :=
    eqToIso (congrArg cmp.obj ha') ≪≫ e
  let ePull : cmp.obj ((colimit.ι F k).toFunctor.obj a') ≅ xU :=
    stageIso.app a'
  let eβ : xU ≅ x := ePull.symm ≪≫ eStage
  exact ⟨i', j, x', ⟨eβ⟩⟩

end LimitPreserving

/-! ### The formal object attached to a formal object of a predeformation category -/

section FormalObjectOfPredeformation

/-- A complete local algebra over `Λ` whose residue field presents a quasi-compact
field-valued point locally of finite type is a formal base. -/
private def formalBaseOfCompleteLocal
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    (R : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    FormalBase S := by
  let iR := Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ iΛ
  let J := maximalIdeal R ^ (0 + 1)
  let e₀ : (R ⧸ J) ≃ₐ[Λ] k :=
    (Ideal.quotientEquivAlgOfEq Λ (pow_one (maximalIdeal R))).trans R.residueEquiv
  let g := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ iR
  let e := e₀.toRingEquiv.toCommRingCatIso
  have he : Spec.map e.hom ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ := by
    dsimp [g, iR]
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    exact CommRingCat.hom_ext e₀.toAlgHom.comp_algebraMap
  have hg : g = Spec.map e.inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) := by
    rw [← he, ← Category.assoc, ← Spec.map_comp]
    simp
  have hfg : LocallyOfFiniteType g := by
    rw [hg]
    infer_instance
  have hqg : QuasiCompact g := by
    rw [hg]
    infer_instance
  exact {
    R := R
    noetherian := inferInstance
    complete := inferInstance
    toS := iR
    residueLocallyFiniteType := hfg
    residueQuasiCompact := hqg }

attribute [local implicit_reducible] formalBaseOfCompleteLocal

/-- Each level of a formal object of a predeformation category lies over the corresponding
infinitesimal thickening of its complete local base. -/
private theorem predeformation_level_base
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    {X : Type v} [Category.{w} X] (q : X ⥤ Over S)
    (x₀ : X) (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (D : PredeformationConstruction iΛ q x₀ hx₀) :
    letI := D.category
    ∀ (ξ : Deformation.FormalObject D.projection) (n : ℕ),
    q.obj (D.objects (ξ.level n)).point =
      Over.mk (AlgebraicGeometry.adicThickeningι ξ.base
          (IsLocalRing.maximalIdeal ξ.base) n ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base)) ≫ iΛ) := by
  let := D.category
  intro ξ n
  have he : (D.objects (ξ.level n)).algebra = Deformation.AdicTruncation.obj ξ.base n :=
    (D.object_projection _).symm.trans (ξ.level_eq n)
  have hb := (D.objects (ξ.level n)).base
  rw [he] at hb
  refine hb.trans ?_
  congr 1
  rw [AlgebraicGeometry.adicThickeningι, ← Category.assoc, ← Spec.map_comp]
  rfl

/-- Objects of the site are determined by their image as objects over the base scheme. -/
private theorem over_post_injective
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Function.Injective (Over.post B.inclusion (X := B.obj hS)).obj := by
  intro U V h
  rcases U with ⟨⟨U, hU⟩, ⟨⟨⟩⟩, ⟨f⟩⟩
  rcases V with ⟨⟨V, hV⟩, ⟨⟨⟩⟩, ⟨g⟩⟩
  change Over.mk f = Over.mk g at h
  cases h
  rfl

/-- The reversed arrow of a morphism of deformations lies over the spectrum of the arrow of
`𝒞_Λ` that the morphism projects to. -/
private theorem predeformation_morphism_base
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    {X : Type v} [Category.{w} X] (q : X ⥤ Over S)
    (x₀ : X) (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (D : PredeformationConstruction iΛ q x₀ hx₀) :
    letI := D.category
    ∀ {a b : D.carrier} (f : a ⟶ b)
      {A B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
      (g : A ⟶ B) (_hf : D.projection.IsHomLift g f)
      (ha : (q.obj (D.objects a).point).left = Spec (.of A))
      (hb : (q.obj (D.objects b).point).left = Spec (.of B)),
      eqToHom hb.symm ≫ (q.map (D.morphisms a b f).arrow).left ≫ eqToHom ha =
        Spec.map (CommRingCat.ofHom g.hom.toRingHom) := by
  let := D.category
  intro a b f A B g hf ha hb
  let := hf
  have hA : (D.objects a).algebra = A :=
    (D.object_projection a).symm.trans (IsHomLift.domain_eq D.projection g f)
  have hB : (D.objects b).algebra = B :=
    (D.object_projection b).symm.trans (IsHomLift.codomain_eq D.projection g f)
  subst A B
  have hg : g = (D.morphisms a b f).ringHom :=
    (IsHomLift.fac D.projection g f).trans (D.morphism_projection f)
  subst g
  exact (D.morphisms a b f).arrow_base

/-- A formal object of the predeformation category of a field-valued point gives a formal
object of the ambient fibred category. -/
private def formalObjectOfPredeformation
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    {X : Type v} [Category.{w} X] (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (x₀ : X) (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (D : PredeformationConstruction iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    letI := D.category
    Deformation.FormalObject D.projection → FormalObject B S hS p := by
  letI := D.category
  intro ξ
  let A := formalBaseOfCompleteLocal iΛ ξ.base hfinite hqc
  have hb (n : ℕ) : (p ⋙ Over.post B.inclusion).obj (D.objects (ξ.level n)).point =
      Over.mk (A.truncationToS n) :=
    predeformation_level_base iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀ D ξ n
  have hc (n : ℕ) : B.Contains (A.truncation n) := by
    have hn := congrArg Over.left (hb n)
    change (p.obj (D.objects (ξ.level n)).point).left.obj = A.truncation n at hn
    rw [← hn]
    exact (p.obj (D.objects (ξ.level n)).point).left.property
  have he (n : ℕ) : p.obj (D.objects (ξ.level n)).point =
      truncationOver B S hS A hc n :=
    over_post_injective B S hS (hb n)
  exact {
    base := A
    contains := hc
    level := fun n => (D.objects (ξ.level n)).point
    level_eq := he
    transition := fun n => (D.morphisms _ _ (ξ.transition n)).arrow
    transition_lift := by
      intro n
      apply IsHomLift.of_fac p _ _ (he n) (he (n + 1))
      apply (Over.post B.inclusion).map_injective
      apply Over.OverMorphism.ext
      simp only [Functor.map_comp]
      have ha (m : ℕ) :
          ((p ⋙ Over.post B.inclusion).obj (D.objects (ξ.level m)).point).left =
            Spec (.of (Deformation.AdicTruncation.obj ξ.base m)) :=
        congrArg Over.left (hb m)
      have ht := predeformation_morphism_base iΛ (p ⋙ Over.post B.inclusion)
        x₀ hx₀ D (ξ.transition n)
        ((Deformation.AdicTruncation.transitionNat n).app ξ.base)
        (ξ.transition_lift n) (ha (n + 1)) (ha n)
      have hring :
          ((Deformation.AdicTruncation.transitionNat n).app ξ.base).hom.toRingHom =
            Ideal.Quotient.factorPow (maximalIdeal ξ.base) (Nat.le_succ (n + 1)) := by
        ext z
        rfl
      rw [hring] at ht
      simp only [eqToHom_map, Over.comp_left, Over.eqToHom_left]
      convert ht.symm using 1 <;> rfl }

attribute [local implicit_reducible] formalObjectOfPredeformation

/-- The arrow out of the closed fibre of the formal object built from a formal object of a
predeformation category is the arrow recorded by that predeformation object. -/
private theorem formalObjectOfPredeformation_closedPointArrow
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    {X : Type v} [Category.{w} X]
    (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (x₀ : X) (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (D : PredeformationConstruction iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    letI := D.category
    ∀ (η : Deformation.FormalObject D.projection) (n : ℕ),
      (D.objects (η.level 0)).arrow ≫
        FormalObject.closedPointArrow
          (formalObjectOfPredeformation B S hS iΛ p x₀ hx₀ D hfinite hqc η) n =
        (D.objects (η.level n)).arrow := by
  let := D.category
  intro η n
  induction n with
  | zero =>
      show (D.objects (η.level 0)).arrow ≫
        𝟙 (D.objects (η.level 0)).point = _
      simp
  | succ n ih =>
      rw [FormalObject.closedPointArrow, ← Category.assoc, ih]
      show (D.objects (η.level n)).arrow ≫
        (D.morphisms _ _ (η.transition n)).arrow = _
      exact (D.morphisms _ _ (η.transition n)).triangle

section

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  (iΛ : Spec (.of Λ) ⟶ S)
  {X : Type v} [Category.{w} X] (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (x₀ : X) (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (D : PredeformationConstruction iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
  (hfinite : LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hqc : QuasiCompact
    (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

/-- The levels of the formal object built from a predeformation formal object. -/
private theorem formalObjectOfPredeformation_level :
    letI := D.category
    ∀ (η : Deformation.FormalObject D.projection) (n : ℕ),
      (formalObjectOfPredeformation B S hS iΛ p x₀ hx₀ D hfinite hqc η).level n =
        (D.objects (η.level n)).point := by
  let := D.category
  intro η n
  rfl

/-- The transitions of the formal object built from a predeformation formal object. -/
private theorem formalObjectOfPredeformation_transition :
    letI := D.category
    ∀ (η : Deformation.FormalObject D.projection) (n : ℕ),
      (formalObjectOfPredeformation B S hS iΛ p x₀ hx₀ D hfinite hqc η).transition n =
        (D.morphisms (η.level (n + 1)) (η.level n) (η.transition n)).arrow := by
  let := D.category
  intro η n
  rfl

/-- The complete local base of the formal object built from a predeformation formal object
recovers the original complete local base after the canonical change of residue field. -/
private theorem completeChangeResidueField_completeLocalBase :
    letI := D.category
    ∀ (η : Deformation.FormalObject D.projection),
      letI : Algebra Λ (formalObjectOfPredeformation B S hS iΛ p x₀ hx₀ D hfinite
        hqc η).base.R := η.base.algebra
      (completeChangeResidueField η.base.residueEquiv).obj
          (FormalObject.completeLocalBase
            (formalObjectOfPredeformation B S hS iΛ p x₀ hx₀ D hfinite hqc η) Λ) =
        η.base := by
  let := D.category
  intro η
  rfl

end

end FormalObjectOfPredeformation

/-! ### Reading off the base of the finite-type approximation -/

section Approximation

/-- The underlying map of schemes of a composite of arrows of the site. -/
private theorem bigFppf_leftHom_comp {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {X Y Z : AlgebraicGeometry.BigFppfOver B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).left.hom = f.left.hom ≫ g.left.hom := rfl

/-- The underlying map of schemes of a coherence isomorphism of the site. -/
private theorem bigFppf_eqToHom_leftHom {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {X Y : AlgebraicGeometry.BigFppfOver B S hS} (h : X = Y) :
    (eqToHom h).left.hom =
      eqToHom (congrArg (fun Z : AlgebraicGeometry.BigFppfOver B S hS ↦
        (Z.left.1 : Scheme.{u})) h) := by
  subst h
  simp

/-- The residue field transported along any presentation of the maximal ideal composes with
the canonical closed immersion to the residue map. -/
private theorem eqToHom_spec_quotient_comp {R : Type u} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I = maximalIdeal R)
    (h : Spec (.of (ResidueField R)) = Spec (.of (R ⧸ I))) :
    eqToHom h ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) := by
  subst hI
  exact (Category.id_comp _).trans rfl

/-- A morphism from the spectrum of a field which factors through the local ring at a point
via a map that is the residue map followed by an isomorphism is the canonical residue-field
point of that point. -/
private theorem fromSpecStalk_factor_eq_fromSpecResidueField
    {X : Scheme.{u}} {k : Type u} [Field k] (u : X) (g : Spec (.of k) ⟶ X)
    (ε : X.residueField u ≃+* k) (ψ : X.presheaf.stalk u →+* k)
    (hψ : ψ = ε.toRingHom.comp (IsLocalRing.residue (X.presheaf.stalk u)))
    (hg : g = Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk u) :
    g = Spec.map (CommRingCat.ofHom ε.toRingHom) ≫
      X.fromSpecResidueField u := by
  rw [hg, Scheme.fromSpecResidueField, ← Spec.map_comp_assoc, hψ]
  rfl

/-- The level-zero base of a composite of a morphism of formal objects with a realization of
the target over its complete local base. -/
private theorem approximation_level_zero_base
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type v} [Category.{w} F] {p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS}
    {ξ Y : FormalObject B S hS p} (f : ξ ⟶ Y)
    {A : Spec (.of ξ.base.R) ⟶ Spec (.of Y.base.R)}
    (hA : FormalObject.Hom.IsBaseMap f A)
    (y : CompleteLocalObjectsFull B S hS p)
    (hYbase : Y.base = chosenBase B S hS p y)
    (rApp : Y.level 0 ⟶ y.1)
    (hι : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        (eqToHom (Y.level_eq 0).symm ≫ p.map rApp ≫
          eqToHom (chosenBase_eq B S hS p y)) =
      AlgebraicGeometry.adicThickeningι Y.base.R (maximalIdeal Y.base.R) 0 ≫
        eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) hYbase)) :
    (eqToHom (ξ.level_eq 0).symm ≫ p.map (f.app 0 ≫ rApp) ≫
        eqToHom (chosenBase_eq B S hS p y)).left.hom =
      AlgebraicGeometry.adicThickeningι ξ.base.R (maximalIdeal ξ.base.R) 0 ≫ A ≫
        eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) hYbase) := by
  have hsplit : (eqToHom (ξ.level_eq 0).symm ≫ p.map (f.app 0 ≫ rApp) ≫
        eqToHom (chosenBase_eq B S hS p y)) =
      (eqToHom (ξ.level_eq 0).symm ≫ p.map (f.app 0) ≫
        eqToHom (Y.level_eq 0)) ≫
      (eqToHom (Y.level_eq 0).symm ≫ p.map rApp ≫
        eqToHom (chosenBase_eq B S hS p y)) := by
    rw [p.map_comp]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [hsplit]
  have hcomp : ((eqToHom (ξ.level_eq 0).symm ≫ p.map (f.app 0) ≫
        eqToHom (Y.level_eq 0)) ≫
      (eqToHom (Y.level_eq 0).symm ≫ p.map rApp ≫
        eqToHom (chosenBase_eq B S hS p y))).left.hom =
      (eqToHom (ξ.level_eq 0).symm ≫ p.map (f.app 0) ≫
        eqToHom (Y.level_eq 0)).left.hom ≫
      (eqToHom (Y.level_eq 0).symm ≫ p.map rApp ≫
        eqToHom (chosenBase_eq B S hS p y)).left.hom := rfl
  rw [hcomp]
  have hι' : (eqToHom (Y.level_eq 0).symm ≫ p.map rApp ≫
        eqToHom (chosenBase_eq B S hS p y)).left.hom =
      AlgebraicGeometry.adicThickeningι Y.base.R (maximalIdeal Y.base.R) 0 ≫
        eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) hYbase) := hι
  rw [hι', ← Category.assoc, hA.2 0, Category.assoc]

end Approximation

/-! ### The versal finite-type point -/

/-- The first step of the proof of Stacks 07XY: a finite-type field-valued object `x₀` of a
fibred category satisfying Artin's axioms over a locally Noetherian base extends to an object
`x` over a quasi-compact base locally of finite type over `S`, versal at a finite type point
`u₀` of that base whose residue field is identified with `k`, with an arrow `x₀ ⟶ x` realizing
that identification.

The tag itself is registered on `Deformation.Artin.exists_smooth_finiteType_neighborhood`,
which states it whole. -/
public theorem exists_versal_finiteTypePoint
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (k : Type u) [Field k]
    (i₀ : Spec (.of k) ⟶ S) (x₀ : 𝒳.val.obj)
    (hx₀ : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ = Over.mk i₀)
    (hfinite₀ : LocallyOfFiniteType i₀) (hqc₀ : QuasiCompact i₀)
    (s : S) (hs : i₀ (IsLocalRing.closedPoint k) = s)
    (hlimit : IsLimitPreserving.{u, u, u, max (u + 1) v w, max u v} B S hS 𝒳)
    (hRS : SatisfiesRS B S hS 𝒳.val.p 𝒳.property)
    (htangent :
      ∀ (Λ : Type u) [CommRing Λ] [Algebra Λ k]
        (_hΛstalk : Λ = S.presheaf.stalk s)
        (iΛ : Spec (.of Λ) ⟶ S)
        (_hiΛ : HEq iΛ (S.fromSpecStalk s))
        (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ = i₀),
        let hx : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ =
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) :=
          hx₀.trans (congrArg Over.mk hbase.symm)
        let D := predeformationCategory iΛ
          (𝒳.val.p ⋙ Over.post B.inclusion) x₀ hx
        letI : Category D.carrier := D.category
        ∀ hD : Deformation.IsDeformationCategory D.projection,
          let 𝓕 := BasedCategory.ofFunctor D.projection
          let hS2 := schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD
          letI : Fact (Deformation.IsPredeformationCategory 𝓕.p) :=
            ⟨hD.predeformation⟩
          letI : Fact (Deformation.SchlessingerConditionS2
            (CategoryOfElements.π
              (Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered))) :=
            ⟨hS2⟩
          let F := Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered
          let T := Deformation.artinianTangentSpace Λ k F
          letI : AddCommGroup T := Deformation.associatedTangentSpaceAddCommGroupUnlifted 𝓕
          letI : Module k T := Deformation.associatedTangentSpaceModuleUnlifted 𝓕
          FiniteDimensional k T)
    (heffective : ∀ ξ : FormalObject B S hS 𝒳.val.p,
      FormalObject.IsEffective B S hS 𝒳.val.p 𝒳.property ξ)
    (hG : IsGRing (S.presheaf.stalk s)) :
    ∃ (x : 𝒳.val.obj)
      (u₀ : ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).left)
      (e : ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).left.residueField u₀ ≃+* k)
      (r : x₀ ⟶ x),
      LocallyOfFiniteType ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).hom ∧
      QuasiCompact ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).hom ∧
      AlgebraicGeometry.IsFiniteTypePoint u₀ ∧
      (eqToHom hx₀.symm ≫ (𝒳.val.p ⋙ Over.post B.inclusion).map r).left =
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).left.fromSpecResidueField u₀ ∧
      IsVersalAt ((𝒳.val.p ⋙ Over.post B.inclusion).obj x)
        (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x rfl := by
  let hAlg : Algebra (S.presheaf.stalk s) k :=
    (eqToHom (congrArg S.presheaf.stalk hs).symm ≫
      Scheme.stalkClosedPointTo i₀).hom.toAlgebra
  let iΛ : Spec (CommRingCat.of (S.presheaf.stalk s : Type u)) ⟶ S :=
    S.fromSpecStalk s
  have hbase : Spec.map (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk s) k)) ≫ iΛ = i₀ :=
    stalk_map_factors_through S k i₀ s hs
  let hx : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap (S.presheaf.stalk s) k)) ≫ iΛ) :=
    hx₀.trans (congrArg Over.mk hbase.symm)
  have hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom
        (algebraMap (S.presheaf.stalk s) k)) ≫ iΛ) :=
    hbase.symm ▸ hfinite₀
  have hqc : QuasiCompact
      (Spec.map (CommRingCat.ofHom
        (algebraMap (S.presheaf.stalk s) k)) ≫ iΛ) :=
    hbase.symm ▸ hqc₀
  let D := @predeformationCategory _ k _ _ hAlg S iΛ _ _
    (𝒳.val.p ⋙ Over.post B.inclusion) x₀ hx
  let : Category D.carrier := D.category
  have hD : Deformation.IsDeformationCategory D.projection :=
    @isDeformationCategory_predeformationCategory B S hS _ _ 𝒳.val.p 𝒳.property hRS
      _ k _ _ hAlg iΛ x₀ hx hfinite hqc
  let 𝓕 : BasedCategory
      (@Deformation.ArtinianLocalAlgCat _ k _ _ hAlg) :=
    BasedCategory.ofFunctor D.projection
  let hS1 := Deformation.schlessingerConditionS1_of_satisfiesRS hD.satisfiesRS
  let hS2 := schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD
  let : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
  let : Fact (Deformation.SchlessingerConditionS2
    (CategoryOfElements.π
      (Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨hS2⟩
  let F := Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered
  let T := @Deformation.artinianTangentSpace _ k _ _ hAlg F
  let : AddCommGroup T := Deformation.associatedTangentSpaceAddCommGroupUnlifted 𝓕
  let : Module k T := Deformation.associatedTangentSpaceModuleUnlifted 𝓕
  have hfiniteT : FiniteDimensional k T :=
    @htangent _ _ hAlg rfl iΛ HEq.rfl hbase hD
  have hpoint : (Scheme.SpecToEquivOfField k S i₀).1 = s := hs
  have : Module.Finite (S.presheaf.stalk s) k := by
    cases hpoint
    exact finite_stalk_to_field S k i₀ hfinite₀ hqc₀
  have hS2p : Deformation.SchlessingerConditionS2 𝓕.p :=
    Deformation.schlessingerConditionS2_of_satisfiesRS hD.satisfiesRS
  obtain ⟨η, hversalη⟩ :=
    @Deformation.exists_versalFormalObject _ k _ _ _ hAlg _ 𝓕
      hD.predeformation hS1 hS2p
      (@Deformation.finiteDimensional_tangentSpaceArtinian_of_artinianTangentSpace
        _ k _ _ hAlg 𝓕 hD.predeformation hS2 hfiniteT)
  let ξ : FormalObject B S hS 𝒳.val.p :=
    formalObjectOfPredeformation B S hS iΛ 𝒳.val.p x₀ hx D
      hfinite hqc η
  let gη : η.base →+* k :=
    η.base.residueEquiv.toRingHom.comp (IsLocalRing.residue η.base)
  have hgη : gη.comp (algebraMap (S.presheaf.stalk s) η.base) =
      algebraMap (S.presheaf.stalk s) k := by
    ext r
    exact η.base.residueEquiv.commutes r
  have hΛkLocal : IsLocalHom (algebraMap (S.presheaf.stalk s) k) := by
    cases hs
    show IsLocalHom (Scheme.stalkClosedPointTo i₀).hom
    infer_instance
  have : IsLocalHom (algebraMap (S.presheaf.stalk s) η.base) := by
    have : IsLocalHom (gη.comp (algebraMap (S.presheaf.stalk s) η.base)) :=
      hgη.symm ▸ hΛkLocal
    exact isLocalHom_of_comp (algebraMap (S.presheaf.stalk s) η.base) gη
  have hξclosed : ξ.base.toS (IsLocalRing.closedPoint ξ.base.R) = s := by
    have h1 := Scheme.Hom.comp_apply
      (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) η.base))) iΛ
      (IsLocalRing.closedPoint η.base)
    have h2 : (Spec.map (CommRingCat.ofHom
          (algebraMap (S.presheaf.stalk s) η.base)))
          (IsLocalRing.closedPoint η.base) =
        IsLocalRing.closedPoint (S.presheaf.stalk s) := Spec_closedPoint
    refine Eq.trans ?_ Scheme.fromSpecStalk_closedPoint
    exact h1.trans (congrArg (fun y => iΛ y) h2)
  let : Algebra (S.presheaf.stalk s) ξ.base.R := η.base.algebra
  have hξbase : Spec.map (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk s) ξ.base.R)) ≫
      iΛ = ξ.base.toS := rfl
  let rη : x₀ ⟶ ξ.level 0 := (D.objects (η.level 0)).arrow
  have hrηbase :
      eqToHom (congrArg Over.left hx).symm ≫
        ((𝒳.val.p ⋙ Over.post B.inclusion).map rη).left ≫
        eqToHom (congrArg Over.left (D.objects (η.level 0)).base) =
      Spec.map (CommRingCat.ofHom (residueMap (D.objects (η.level 0)).algebra)) :=
    (D.objects (η.level 0)).arrow_base
  have hlimitObjects :
      AlgebraicGeometry.Stack.IsLimitPreservingOverTerminal.{u, u, u} B S hS 𝒳 :=
    AlgebraicGeometry.Stack.isLimitPreservingOverTerminal_of_isLimitPreserving
      B S hS 𝒳 hlimit
  let : CommRing ξ.base.R := ξ.base.commRing
  let : IsLocalRing ξ.base.R := ξ.base.localRing
  let : Field (IsLocalRing.ResidueField ξ.base.R) :=
    IsLocalRing.ResidueField.field ξ.base.R
  let : Algebra (S.presheaf.stalk s) (IsLocalRing.ResidueField ξ.base.R) :=
    IsLocalRing.ResidueField.algebra ξ.base.R
  let hxξ := ξ.basePoint (S.presheaf.stalk s) iΛ hξbase
  let C := predeformationCategory
    (Λ := (S.presheaf.stalk s : Type u))
    (k := (IsLocalRing.ResidueField ξ.base.R : Type u))
    iΛ (𝒳.val.p ⋙ Over.post B.inclusion) (ξ.level 0) hxξ
  let : Category C.carrier := C.category
  let ηξ := ξ.predeformationFormalObject (S.presheaf.stalk s)
    iΛ hξbase
  let e : IsLocalRing.ResidueField ξ.base.R ≃ₐ[S.presheaf.stalk s] k :=
    η.base.residueEquiv
  have hηpoint : ∀ n, (C.objects (ηξ.level n)).point = ξ.level n := fun _ => rfl
  have hηarrow : ∀ n, HEq (C.objects (ηξ.level n)).arrow
      (FormalObject.closedPointArrow ξ n) := fun _ => HEq.rfl
  have hηtrans : ∀ n, HEq
      (C.morphisms (ηξ.level (n + 1)) (ηξ.level n) (ηξ.transition n)).arrow
      (ξ.transition n) := fun _ => HEq.rfl
  have hAD : (D.objects (η.level 0)).algebra =
      Deformation.AdicTruncation.obj η.base 0 :=
    (D.object_projection _).symm.trans (η.level_eq 0)
  have hAC : (C.objects (ηξ.level 0)).algebra =
      Deformation.AdicTruncation.obj ηξ.base 0 :=
    (C.object_projection _).symm.trans (ηξ.level_eq 0)
  have hCLB : (completeChangeResidueField e).obj ηξ.base = η.base :=
    completeChangeResidueField_completeLocalBase B S hS iΛ
      𝒳.val.p x₀ hx D hfinite hqc η
  have hADC : (D.objects (η.level 0)).algebra =
      (artinianChangeResidueField e).obj ((C.objects (ηξ.level 0)).algebra) := by
    rw [hAD, hAC, artinianChangeResidueField_adicTruncation_obj, hCLB]
  obtain ⟨bC, hCrel⟩ :=
    closedPoint_base_relation iΛ
      (𝒳.val.p ⋙ Over.post B.inclusion) (ξ.level 0)
      (C.objects (ηξ.level 0)).point hxξ (C.objects (ηξ.level 0)).algebra
      (C.objects (ηξ.level 0)).base (C.objects (ηξ.level 0)).arrow
      (C.objects (ηξ.level 0)).arrow_base (hηpoint 0) (hηarrow 0)
  have hrho : eqToHom (congrArg Over.left hx).symm ≫
      ((𝒳.val.p ⋙ Over.post B.inclusion).map rη).left ≫
      eqToHom (congrArg Over.left hxξ) =
      Spec.map (CommRingCat.ofHom
        (e.toRingHom : IsLocalRing.ResidueField ξ.base.R →+* k)) :=
    base_relation' iΛ (𝒳.val.p ⋙ Over.post B.inclusion)
      x₀ (ξ.level 0) hx hxξ e (C.objects (ηξ.level 0)).algebra
      (D.objects (η.level 0)).algebra hADC (D.objects (η.level 0)).base bC rη
      hrηbase hCrel
  have : IsIso (CommRingCat.ofHom
      (e.toRingHom : IsLocalRing.ResidueField ξ.base.R →+* k)) :=
    inferInstanceAs (IsIso (RingEquiv.toCommRingCatIso e.toRingEquiv).hom)
  have hisoLeft : IsIso (((𝒳.val.p ⋙ Over.post B.inclusion).map rη).left) := by
    have h2 := eq_of_eqToHom_conj (congrArg Over.left hx)
      (congrArg Over.left hxξ) hrho
    rw [h2]
    infer_instance
  have : 𝒳.val.p.IsStronglyCartesian (𝒳.val.p.map rη) rη :=
    𝒳.property.isStronglyCartesian rη
  have : IsIso rη :=
    isIso_of_isStronglyCartesian_of_left_isIso B S hS 𝒳.val.p rη hisoLeft
  have hpointD : ∀ n, (C.objects (ηξ.level n)).point =
      (D.objects (η.level n)).point := fun n => (hηpoint n).trans
    (formalObjectOfPredeformation_level B S hS iΛ 𝒳.val.p x₀ hx D
      hfinite hqc η n)
  have harrowD : ∀ n, HEq (rη ≫ (C.objects (ηξ.level n)).arrow)
      ((D.objects (η.level n)).arrow) := fun n =>
    (heq_comp_of_heq (hηpoint n) (hηarrow n) rη).trans
      (heq_of_eq (formalObjectOfPredeformation_closedPointArrow B S hS
        iΛ 𝒳.val.p x₀ hx D hfinite hqc η n))
  have htransD : ∀ n, HEq
      (C.morphisms (ηξ.level (n + 1)) (ηξ.level n) (ηξ.transition n)).arrow
      ((D.morphisms (η.level (n + 1)) (η.level n) (η.transition n)).arrow) :=
    fun n => (hηtrans n).trans (heq_of_eq
      (formalObjectOfPredeformation_transition B S hS iΛ
        𝒳.val.p x₀ hx D hfinite hqc η n))
  have hA8 : (changeFormalObjects e iΛ
      (𝒳.val.p ⋙ Over.post B.inclusion) x₀ (ξ.level 0) hx hxξ rη hrho D C).obj ηξ
      = η :=
    changeFormalObjects_obj_eq e iΛ
      (𝒳.val.p ⋙ Over.post B.inclusion) x₀ (ξ.level 0) hx hxξ rη hrho D C ηξ η
      hCLB hpointD harrowD htransD
  have hversalC : FormalObject.IsVersal B S hS 𝒳.val.p 𝒳.property ξ
      (S.presheaf.stalk s) iΛ hξbase :=
    isVersal_of_changeFormalObjects e iΛ
      (𝒳.val.p ⋙ Over.post B.inclusion) x₀ (ξ.level 0) hx hxξ rη hrho D C _
      hD.predeformation.cofibered ηξ η hA8 hversalη
  obtain ⟨U, u₀, V, _hV, xA, hxU, hfinU, hqcU, hftp, _hres, hversalAt,
    xR, eiso, rA, eR, _hcartA, hbaseeq⟩ :=
    exists_finiteType_versal_approximation_univ B S hS 𝒳 ξ (heffective ξ) s hξclosed hG
      hlimitObjects iΛ rfl hξbase hversalC
  subst hxU
  obtain ⟨rApp, hbaseG, _hcartApp, _htransApp, _hnatApp, hιApp⟩ :=
    (approximationFunctorData B S hS 𝒳.val.p 𝒳.property).2
  have : IsLocallyNoetherian (B.inclusion.obj (B.obj hS)) :=
    inferInstanceAs (IsLocallyNoetherian S)
  have : IsLocallyNoetherian
      ((𝒳.val.p ⋙ Over.post B.inclusion).obj xA.1).left :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((𝒳.val.p ⋙ Over.post B.inclusion).obj xA.1).hom
  have hbmIso : IsIso (FormalObject.Hom.baseMap eiso.hom) :=
    ⟨FormalObject.Hom.baseMap eiso.inv,
      by rw [← formalBaseMap_comp, eiso.hom_inv_id, formalBaseMap_id],
      by rw [← formalBaseMap_comp, eiso.inv_hom_id, formalBaseMap_id]⟩
  have : IsIso (FormalObject.Hom.baseMap eiso.hom ≫
      eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R))
        (hbaseG xR))) := inferInstance
  have hbe : (eqToHom (chosenBase_eq B S hS 𝒳.val.p xR.obj).symm ≫
        𝒳.val.p.map rA).left.hom =
      Spec.map (CommRingCat.ofHom eR.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap
          (((𝒳.val.p ⋙ Over.post B.inclusion).obj xA.1).left.presheaf.stalk u₀)
          (AlgebraicGeometry.Scheme.completedLocalRing
            ((𝒳.val.p ⋙ Over.post B.inclusion).obj xA.1).left u₀))) ≫
        ((𝒳.val.p ⋙ Over.post B.inclusion).obj xA.1).left.fromSpecStalk u₀ :=
    (Category.comp_id _).symm.trans hbaseeq
  obtain ⟨α, hα⟩ := exists_ringEquiv_of_specIso
    (asIso (FormalObject.Hom.baseMap eiso.hom ≫
      eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hbaseG xR))))
  rw [asIso_hom] at hα
  obtain ⟨ε, hε⟩ :
      ∃ ε : ((𝒳.val.p ⋙ Over.post B.inclusion).obj xA.1).left.residueField u₀
          ≃+* k,
        (ε.toRingHom.comp (IsLocalRing.residue
            (((𝒳.val.p ⋙ Over.post B.inclusion).obj xA.1).left.presheaf.stalk
              u₀))) =
          e.toRingHom.comp
            ((IsLocalRing.residue ξ.base.R).comp
              (α.toRingHom.comp
                (eR.toRingHom.comp
                  (algebraMap
                    (((𝒳.val.p ⋙ Over.post B.inclusion).obj xA.1).left.presheaf.stalk
                      u₀)
                    (AlgebraicGeometry.Scheme.completedLocalRing
                      ((𝒳.val.p ⋙ Over.post B.inclusion).obj xA.1).left u₀))))) := by
    refine ⟨(RingEquiv.ofBijective _
        (AlgebraicGeometry.Scheme.completedLocalRing_residueFieldMap_bijective
          ((𝒳.val.p ⋙ Over.post B.inclusion).obj xA.1).left u₀)).trans
        ((IsLocalRing.ResidueField.mapEquiv eR).trans
          ((IsLocalRing.ResidueField.mapEquiv α).trans e.toRingEquiv)), ?_⟩
    ext a
    rfl
  refine ⟨xA.1, u₀, ε, rη ≫ eiso.hom.app 0 ≫ rApp xR 0 ≫ rA,
    hfinU, hqcU, hftp, ?_, hversalAt⟩
  have hconv : Spec (CommRingCat.of (IsLocalRing.ResidueField ξ.base.R)) =
      AlgebraicGeometry.adicThickening ξ.base.R (maximalIdeal ξ.base.R) 0 :=
    congrArg (fun I : Ideal ξ.base.R ↦ Spec (CommRingCat.of (ξ.base.R ⧸ I)))
      (pow_one (maximalIdeal ξ.base.R)).symm
  have hstep3 : eqToHom hconv ≫
      AlgebraicGeometry.adicThickeningι ξ.base.R (maximalIdeal ξ.base.R) 0 =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ξ.base.R)) :=
    eqToHom_spec_quotient_comp _ (pow_one (maximalIdeal ξ.base.R)) hconv
  have hstep4 : eqToHom hconv ≫
      (eqToHom (ξ.level_eq 0).symm).left.hom =
      eqToHom (congrArg Over.left hxξ).symm := by
    rw [bigFppf_eqToHom_leftHom, eqToHom_trans]
  have hstep1 : (eqToHom hx₀.symm).left ≫
      ((𝒳.val.p ⋙ Over.post B.inclusion).map rη).left =
      Spec.map (CommRingCat.ofHom (e.toRingHom)) ≫ eqToHom hconv ≫
        (eqToHom (ξ.level_eq 0).symm).left.hom := by
    rw [hstep4]
    have h0 : (eqToHom hx₀.symm :
        Over.mk i₀ ⟶ (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀).left =
        eqToHom (congrArg Over.left hx).symm := by
      rw [Over.eqToHom_left]
    rw [h0, ← hrho]
    simp
  have hinner : (eqToHom (ξ.level_eq 0).symm ≫
        𝒳.val.p.map (eiso.hom.app 0 ≫ rApp xR 0) ≫
        eqToHom (chosenBase_eq B S hS 𝒳.val.p xR.obj)) ≫
      (eqToHom (chosenBase_eq B S hS 𝒳.val.p xR.obj).symm ≫
        𝒳.val.p.map rA) =
      eqToHom (ξ.level_eq 0).symm ≫ 𝒳.val.p.map (eiso.hom.app 0) ≫
        𝒳.val.p.map (rApp xR 0) ≫ 𝒳.val.p.map rA := by
    rw [𝒳.val.p.map_comp]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
  have hstep2 : (eqToHom (ξ.level_eq 0).symm).left.hom ≫
      ((𝒳.val.p ⋙ Over.post B.inclusion).map (eiso.hom.app 0)).left ≫
      ((𝒳.val.p ⋙ Over.post B.inclusion).map (rApp xR 0)).left ≫
      ((𝒳.val.p ⋙ Over.post B.inclusion).map rA).left =
      AlgebraicGeometry.adicThickeningι ξ.base.R (maximalIdeal ξ.base.R) 0 ≫
        Spec.map (CommRingCat.ofHom α.toRingHom) ≫
        Spec.map (CommRingCat.ofHom eR.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap
          (((𝒳.val.p ⋙ Over.post B.inclusion).obj xA.1).left.presheaf.stalk u₀)
          (AlgebraicGeometry.Scheme.completedLocalRing
            ((𝒳.val.p ⋙ Over.post B.inclusion).obj xA.1).left u₀))) ≫
        ((𝒳.val.p ⋙ Over.post B.inclusion).obj xA.1).left.fromSpecStalk u₀ := by
    have hL : (eqToHom (ξ.level_eq 0).symm).left.hom ≫
        ((𝒳.val.p ⋙ Over.post B.inclusion).map (eiso.hom.app 0)).left ≫
        ((𝒳.val.p ⋙ Over.post B.inclusion).map (rApp xR 0)).left ≫
        ((𝒳.val.p ⋙ Over.post B.inclusion).map rA).left =
        (eqToHom (ξ.level_eq 0).symm ≫
          𝒳.val.p.map (eiso.hom.app 0) ≫
          𝒳.val.p.map (rApp xR 0) ≫ 𝒳.val.p.map rA).left.hom := rfl
    rw [hL, ← hinner, bigFppf_leftHom_comp,
      approximation_level_zero_base eiso.hom
        (FormalObject.Hom.baseMap_spec eiso.hom) xR.obj
        (hbaseG xR) (rApp xR 0) (hιApp xR 0),
      hbe, hα, Category.assoc]
  refine fromSpecStalk_factor_eq_fromSpecResidueField u₀ _ ε _ hε.symm ?_
  have hexp : (eqToHom hx₀.symm ≫ (𝒳.val.p ⋙ Over.post B.inclusion).map
        (rη ≫ eiso.hom.app 0 ≫ rApp xR 0 ≫ rA)).left =
      ((eqToHom hx₀.symm).left ≫
        ((𝒳.val.p ⋙ Over.post B.inclusion).map rη).left) ≫
      (((𝒳.val.p ⋙ Over.post B.inclusion).map (eiso.hom.app 0)).left ≫
        ((𝒳.val.p ⋙ Over.post B.inclusion).map (rApp xR 0)).left ≫
        ((𝒳.val.p ⋙ Over.post B.inclusion).map rA).left) := by
    simp only [Functor.map_comp, Over.comp_left, Category.assoc]
  rw [hexp, hstep1, Category.assoc, Category.assoc, hstep2,
    ← Category.assoc (eqToHom hconv), hstep3]
  simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]

end Deformation.Artin

end
