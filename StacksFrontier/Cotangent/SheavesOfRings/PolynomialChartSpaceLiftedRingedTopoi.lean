module

public import StacksFrontier.AlgebraicGeometry.SheafifyCommRing.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites
public import StacksFrontier.Cotangent.SheavesOfRings.PolynomialChartSpaceRingedTopoi
public import StacksFrontier.Cotangent.Spaces.CotangentComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The ringed topoi of polynomial charts, in the coefficient universe

Let `X` be an algebraic space over a ring `Λ` and `C_{X/Λ}` its category of polynomial charts
`(U ⟶ A)`, with the topology inherited from `X_étale`. This file builds the diagram of ringed
topoi of [Stacks Project, Tag 08VK]
```
(Sh(C_{X/Λ}), π⁻¹𝒪_X) --i--> (Sh(C_{X/Λ}), 𝒪)
        |
        π
        v
(Sh(X_étale), 𝒪_X)
```
with coefficients in the universe `u + 1` of the chart category, the universe in which the
cotangent complex of Tag 08VD is formed.

## Main definitions

* `AlgebraicGeometry.Space.PolynomialChart.liftedAffineSheaf`: the sheaf of rings `𝒪`, the
  sheafification of `(U ⟶ A) ↦ Γ(A, 𝒪_A)`.
* `AlgebraicGeometry.Space.PolynomialChart.liftedProjection`: the morphism of topoi `π`.
* `AlgebraicGeometry.Space.PolynomialChart.liftedVerticalHom` and `liftedHorizontalHom`: the
  morphisms of ringed topoi `π` and `i`.
* `AlgebraicGeometry.Space.PolynomialChart.liftedBaseSheafMap`: the structure map `Λ ⟶ 𝒪`.

## Implementation notes

A polynomial chart carries a `Type u` set of variables, so the chart category has objects and
arrows in `Type (u + 1)`, and sheafification of commutative rings on it is available in that
universe, where it is found by instance search. Accordingly `𝒪_X`, whose sections live in
universe `u`, is presented by the canonical `ULift` of its section rings,
`AlgebraicGeometry.Space.smallEtaleStructureSheafULift`, and the presheaves of rings of
`StacksFrontier.Cotangent.SheavesOfRings.PolynomialChartSpaceRingedTopoi` are composed with the
universe lift `liftRing`. The right Kan extension along `u.op` is produced, as there, from an
initial object of each fibre of the forgetful functor.

## References

* [Stacks Project, Tag 08VK](https://stacks.math.columbia.edu/tag/08VK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.AffineEmptyChart
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space.PolynomialChart

noncomputable section

variable (Λ : Type u) [CommRing Λ] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (CommRingCat.of Λ)))
  (X : (BigFppfOver B (Spec (CommRingCat.of Λ)) hS)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (CommRingCat.of Λ)) hS X)

/-! ### Presentation in the coefficient universe -/

/-- Commutative rings of the universe of `X`, presented in the coefficient universe. -/
abbrev liftRing : CommRingCat.{u} ⥤ CommRingCat.{u + 1} :=
  SheafOfModules.commRingCatULift.{u, u + 1}

/-! ### The two presheaves of rings in the coefficient universe -/

/-- The presheaf `(U ⟶ A) ↦ Γ(A, 𝒪_A)`, in the coefficient universe. -/
abbrev liftedAffinePresheaf : (PolynomialChart Λ B hS X hX)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  affinePresheaf Λ B hS X hX ⋙ liftRing

/-- The presheaf `(U ⟶ A) ↦ 𝒪_X(U)`, in the coefficient universe. -/
abbrev liftedEtalePresheaf : (PolynomialChart Λ B hS X hX)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  etalePresheaf Λ B hS X hX ⋙ liftRing

/-- The map `𝒪 ⟶ π⁻¹𝒪_X` of presheaves in the coefficient universe. -/
def liftedEvaluation : liftedAffinePresheaf Λ B hS X hX ⟶ liftedEtalePresheaf Λ B hS X hX :=
  Functor.whiskerRight (evaluation Λ B hS X hX) liftRing

/-! ### Sheafification in the coefficient universe -/

/-- Presheaves of commutative rings on the chart site admit sheafification with sections in the
universe `u + 1` of the chart category. -/
instance hasSheafify_topology : HasSheafify (topology Λ B hS X hX) CommRingCat.{u + 1} :=
  Stacks.SheafifyCommRing.hasSheafifyCommRingCat.{0, u, u + 1} (topology Λ B hS X hX)

/-- Presheaves of commutative rings on the chart site admit sheafification, in the weak form that
`presheafToSheaf` asks for. -/
instance hasWeakSheafify_topology : HasWeakSheafify (topology Λ B hS X hX) CommRingCat.{u + 1} :=
  HasSheafify.isRightAdjoint

/-- The sheaf of rings `𝒪`: the sheafification of the affine-functions presheaf. -/
abbrev liftedAffineSheaf :
    Sheaf (topology Λ B hS X hX) CommRingCat.{u + 1} :=
  (presheafToSheaf (topology Λ B hS X hX) CommRingCat.{u + 1}).obj
    (liftedAffinePresheaf Λ B hS X hX)

/-- The restriction of the structure sheaf of the small étale site of `X` along the forgetful
functor, as a sheaf of rings on the category of polynomial charts. Its underlying presheaf is
`liftedEtalePresheaf`. -/
abbrev liftedEtaleSheaf : Sheaf (topology Λ B hS X hX) CommRingCat.{u + 1} :=
  ((openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).sheafPushforwardContinuous
    CommRingCat.{u + 1} (topology Λ B hS X hX)
      (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)).obj
    (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩)

/-- The presheaf `(U ⟶ A) ↦ 𝒪_X(U)` is a sheaf for the inherited topology: the forgetful functor
to the small étale site is continuous, and `𝒪_X` is a sheaf there. -/
theorem liftedEtalePresheaf_isSheaf :
    Presheaf.IsSheaf (topology Λ B hS X hX) (liftedEtalePresheaf Λ B hS X hX) :=
  (liftedEtaleSheaf Λ B hS X hX).property

/-- The sheafification of `liftedEtalePresheaf`. -/
abbrev liftedEtalePullbackSheaf :
    Sheaf (topology Λ B hS X hX) CommRingCat.{u + 1} :=
  (presheafToSheaf (topology Λ B hS X hX) CommRingCat.{u + 1}).obj (liftedEtalePresheaf Λ B hS X hX)

/-- The constant sheaf of rings `Λ` on the category of polynomial charts. -/
abbrev liftedConstantBaseSheaf :
    Sheaf (topology Λ B hS X hX) CommRingCat.{u + 1} :=
  (presheafToSheaf (topology Λ B hS X hX) CommRingCat.{u + 1}).obj
    ((Functor.const (PolynomialChart Λ B hS X hX)ᵒᵖ).obj
      (liftRing.obj (CommRingCat.of Λ)))

/-- `liftedConstantBaseSheaf` is the value of the constant-sheaf functor at `Λ`. -/
theorem constantSheaf_obj_eq_liftedConstantBaseSheaf :
    (constantSheaf (topology Λ B hS X hX) CommRingCat.{u + 1}).obj
        (liftRing.obj (CommRingCat.of Λ)) =
      liftedConstantBaseSheaf Λ B hS X hX := rfl

/-! ### The right Kan extension in the coefficient universe -/

/-- Restriction along `u.op` has a pointwise right Kan extension, with sections in the universe
of the sections of `𝒪_X` rather than in the universe of the site: each fibre of `u.op` has an
initial object, so the limit computing the extension is over a category with an initial object
and exists for size-independent reasons. -/
instance hasPointwiseRightKanExtension_openFunctor_op_lifted
    (G : (PolynomialChart Λ B hS X hX)ᵒᵖ ⥤ Type (u + 1)) :
    Functor.HasPointwiseRightKanExtension
      (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).op G := by
  intro Y
  change HasLimit (StructuredArrow.proj Y
    (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).op ⋙ G)
  have huniq : ∀ Z, Unique (fibreInitial Λ B hS X hX Y.unop ⟶ Z) := fun Z =>
    { default := fibreInitialHom Λ B hS X hX Y.unop Z
      uniq := fibreInitialHom_unique Λ B hS X hX Y.unop Z }
  have : HasInitial (StructuredArrow Y
      (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).op) :=
    hasInitial_of_unique (fibreInitial Λ B hS X hX Y.unop)
  infer_instance

/-! ### The morphisms of topoi -/

/-- The morphism of topoi `π : Sh(C_{X/Λ}) ⟶ Sh(X_étale)` induced by the forgetful functor: its
inverse image is restriction along `u.op` and its direct image is the right adjoint of that
restriction. -/
def liftedProjection : MorphismOfTopoi
    (Sheaf (topology Λ B hS X hX) (Type (u + 1)))
    (Sheaf (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X) (Type (u + 1))) where
  pushforward := (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X)
    (hX := hX)).sheafPushforwardCocontinuous (Type (u + 1)) (topology Λ B hS X hX)
      (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)
  inverseImage := (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X)
    (hX := hX)).sheafPushforwardContinuous (Type (u + 1)) (topology Λ B hS X hX)
      (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)
  adj := (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X)
    (hX := hX)).sheafAdjunctionCocontinuous (Type (u + 1)) (topology Λ B hS X hX)
      (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)
  preservesFiniteLimits := by
    have hcomp : PreservesFiniteLimits
        ((openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X)
          (hX := hX)).sheafPushforwardContinuous (Type (u + 1)) (topology Λ B hS X hX)
            (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X) ⋙
          sheafToPresheaf (topology Λ B hS X hX) (Type (u + 1))) :=
      preservesFiniteLimits_of_natIso
        ((openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X)
          (hX := hX)).sheafPushforwardContinuousCompSheafToPresheafIso (Type (u + 1))
            (topology Λ B hS X hX)
            (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)).symm
    exact preservesFiniteLimits_of_reflects_of_preserves _
      (sheafToPresheaf (topology Λ B hS X hX) (Type (u + 1)))

/-- The inverse image of `π` is restriction of sheaves along the forgetful functor. -/
theorem liftedProjection_inverseImage :
    (liftedProjection Λ B hS X hX).inverseImage =
      (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X)
        (hX := hX)).sheafPushforwardContinuous (Type (u + 1)) (topology Λ B hS X hX)
          (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X) := rfl

/-- The identity morphism of the topos of sheaves on the category of polynomial charts, the
underlying geometric morphism of `i`. -/
def liftedIdentityTopos : MorphismOfTopoi
    (Sheaf (topology Λ B hS X hX) (Type (u + 1)))
    (Sheaf (topology Λ B hS X hX) (Type (u + 1))) where
  pushforward := 𝟭 _
  inverseImage := 𝟭 _
  adj := Adjunction.id
  preservesFiniteLimits := by infer_instance

/-! ### The comparison isomorphisms -/

/-- `π⁻¹𝒪_X` is the restriction of `𝒪_X` along the forgetful functor: transporting the ring
operations along restriction of sheaves of sets is restriction of sheaves of rings. -/
def liftedRestrictionIso :
    (inverseImageCommRingFunctor (liftedProjection Λ B hS X hX)).obj
        (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩) ≅
      liftedEtaleSheaf Λ B hS X hX :=
  restrictionCommRingIso (topology Λ B hS X hX)
    (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)
    (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX))
    (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩)

/-- `π⁻¹𝒪_X` is the sheafification of `(U ⟶ A) ↦ 𝒪_X(U)`. -/
def liftedPullbackIso :
    (inverseImageCommRingFunctor (liftedProjection Λ B hS X hX)).obj
        (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩) ≅
      liftedEtalePullbackSheaf Λ B hS X hX :=
  liftedRestrictionIso Λ B hS X hX ≪≫ sheafificationIso (liftedEtaleSheaf Λ B hS X hX)

/-- On sections over a chart, the comparison `π⁻¹𝒪_X ≅ (liftedEtalePresheaf)^#` is the
sheafification unit of `liftedEtalePresheaf`: the first factor is the identity on sections. -/
theorem forget_map_liftedPullbackIso_hom_app
    (P : PolynomialChart Λ B hS X hX) :
    (forget CommRingCat).map ((liftedPullbackIso Λ B hS X hX).hom.hom.app (Opposite.op P)) =
      (forget CommRingCat).map
        ((toSheafify (topology Λ B hS X hX) (liftedEtalePresheaf Λ B hS X hX)).app
          (Opposite.op P)) := rfl

/-- `i⁻¹𝒪 = 𝒪`: transporting the ring operations along the identity functor of sheaves of sets
does nothing. This is the identity case of the comparison with restriction. -/
def liftedIdentityRingIso :
    (inverseImageCommRingFunctor (liftedIdentityTopos Λ B hS X hX)).obj
      (liftedAffineSheaf Λ B hS X hX) ≅ liftedAffineSheaf Λ B hS X hX :=
  restrictionCommRingIso (topology Λ B hS X hX) (topology Λ B hS X hX)
    (𝟭 (PolynomialChart Λ B hS X hX)) (liftedAffineSheaf Λ B hS X hX)

/-- On sections over a chart, the comparison `i⁻¹𝒪 ≅ 𝒪` is the identity. -/
theorem forget_map_liftedIdentityRingIso_hom_app
    (P : PolynomialChart Λ B hS X hX) :
    HEq ((forget CommRingCat).map ((liftedIdentityRingIso Λ B hS X hX).hom.hom.app (Opposite.op P)))
      ((forget CommRingCat).map
        (𝟙 (((inverseImageCommRingFunctor (liftedIdentityTopos Λ B hS X hX)).obj
          (liftedAffineSheaf Λ B hS X hX)).obj.obj (Opposite.op P)))) := HEq.rfl

/-! ### The constant sheaf `Λ` and its structure map -/

/-- The map from the constant presheaf `Λ` to the affine functions, in the coefficient
universe. -/
def liftedBasePresheafMap :
    (Functor.const (PolynomialChart Λ B hS X hX)ᵒᵖ).obj
        (liftRing.obj (CommRingCat.of Λ)) ⟶ liftedAffinePresheaf Λ B hS X hX where
  app P := liftRing.map ((basePresheafMap Λ B hS X hX).app P)
  naturality := by
    intro P Q f
    have h := (basePresheafMap Λ B hS X hX).naturality f
    simp only [Functor.const_obj_map] at h
    simp only [Functor.const_obj_map, Functor.comp_map]
    rw [← Functor.map_comp]
    exact congrArg liftRing.map h

/-- The structure map `Λ ⟶ 𝒪` from the constant sheaf. -/
def liftedBaseSheafMap :
    liftedConstantBaseSheaf Λ B hS X hX ⟶ liftedAffineSheaf Λ B hS X hX :=
  (presheafToSheaf (topology Λ B hS X hX) CommRingCat.{u + 1}).map
    (liftedBasePresheafMap Λ B hS X hX)

/-- Naturality of the sheafification unit, on sections over a chart. -/
private theorem toSheafify_app_comp_sheafifyMap_app
    {P Q : (PolynomialChart Λ B hS X hX)ᵒᵖ ⥤ CommRingCat.{u + 1}} (η : P ⟶ Q)
    (U : (PolynomialChart Λ B hS X hX)ᵒᵖ) :
    (toSheafify (topology Λ B hS X hX) P).app U ≫
        ((presheafToSheaf (topology Λ B hS X hX) CommRingCat.{u + 1}).map η).hom.app U =
      η.app U ≫ (toSheafify (topology Λ B hS X hX) Q).app U :=
  (NatTrans.congr_app (toSheafify_naturality (topology Λ B hS X hX) η) U).symm

/-- On sections over a chart `U ⟶ A`, the structure map `Λ ⟶ 𝒪` after the sheafification unit
of the constant presheaf is pullback along the structural arrow `A ⟶ Spec Λ` followed by the
sheafification unit. -/
theorem liftedBaseSheafMap_canonical (P : PolynomialChart Λ B hS X hX) :
    (toSheafify (topology Λ B hS X hX)
          ((Functor.const (PolynomialChart Λ B hS X hX)ᵒᵖ).obj
            (liftRing.obj (CommRingCat.of Λ)))).app (Opposite.op P) ≫
        (liftedBaseSheafMap Λ B hS X hX).hom.app (Opposite.op P) =
      liftRing.map ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫
          Scheme.Γ.map P.toBase.op) ≫
        (toSheafify (topology Λ B hS X hX) (liftedAffinePresheaf Λ B hS X hX)).app
          (Opposite.op P) :=
  toSheafify_app_comp_sheafifyMap_app Λ B hS X hX _ _

/-- The composite `Λ ⟶ 𝒪 ⟶ π⁻¹𝒪_X` is pullback along the structure morphism of the étale chart
underlying the polynomial chart. -/
theorem liftedBaseSheafMap_horizontal (P : PolynomialChart Λ B hS X hX) :
    (toSheafify (topology Λ B hS X hX)
          ((Functor.const (PolynomialChart Λ B hS X hX)ᵒᵖ).obj
            (liftRing.obj (CommRingCat.of Λ)))).app (Opposite.op P) ≫
        (liftedBaseSheafMap Λ B hS X hX).hom.app (Opposite.op P) ≫
        ((presheafToSheaf (topology Λ B hS X hX) CommRingCat.{u + 1}).map
          (liftedEvaluation Λ B hS X hX)).hom.app (Opposite.op P) =
      liftRing.map ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫
          Scheme.Γ.map (openPartToBase Λ B hS X P.openPart).op) ≫
        (toSheafify (topology Λ B hS X hX) (liftedEtalePresheaf Λ B hS X hX)).app
          (Opposite.op P) := by
  rw [← Category.assoc, liftedBaseSheafMap_canonical]
  refine (Category.assoc _ _ _).trans ?_
  erw [toSheafify_app_comp_sheafifyMap_app]
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ _) ((liftRing.map_comp _ _).symm.trans
    (congrArg liftRing.map (basePresheafMap_evaluation Λ B hS X hX P)))

/-! ### The diagram -/

/-- The inverse-image form of `i♯`: evaluation, read from `𝒪` to `π⁻¹𝒪_X` through the two
comparison isomorphisms. -/
def liftedHorizontalMapInverse :
    (inverseImageCommRingFunctor (liftedIdentityTopos Λ B hS X hX)).obj
      (liftedAffineSheaf Λ B hS X hX) ⟶
      (inverseImageCommRingFunctor (liftedProjection Λ B hS X hX)).obj
        (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩) :=
  (liftedIdentityRingIso Λ B hS X hX).hom ≫
    (presheafToSheaf (topology Λ B hS X hX) CommRingCat.{u + 1}).map
        (liftedEvaluation Λ B hS X hX) ≫
      (liftedPullbackIso Λ B hS X hX).inv

/-- Read through the two comparison isomorphisms, the inverse-image form of `i♯` is the
sheafification of the evaluation map. -/
theorem liftedHorizontalMapInverse_cancel :
    (liftedIdentityRingIso Λ B hS X hX).inv ≫ liftedHorizontalMapInverse Λ B hS X hX ≫
        (liftedPullbackIso Λ B hS X hX).hom =
      (presheafToSheaf (topology Λ B hS X hX) CommRingCat.{u + 1}).map
        (liftedEvaluation Λ B hS X hX) := by
  simp only [liftedHorizontalMapInverse, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The morphism of ringed topoi `i`, whose structure map in inverse-image form is evaluation. -/
def liftedHorizontalHom :
    RingedToposHom
      ⟨PolynomialChart Λ B hS X hX, topology Λ B hS X hX,
        (inverseImageCommRingFunctor (liftedProjection Λ B hS X hX)).obj
          (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩)⟩
      ⟨PolynomialChart Λ B hS X hX, topology Λ B hS X hX, liftedAffineSheaf Λ B hS X hX⟩ where
  toToposHom := liftedIdentityTopos Λ B hS X hX
  fSharp := (commRingImageAdjunction (liftedIdentityTopos Λ B hS X hX)).homEquiv _ _
    (liftedHorizontalMapInverse Λ B hS X hX)

/-- The structure map of `i` in inverse-image form is `liftedHorizontalMapInverse`. -/
theorem liftedHorizontalHom_fSharpInverseImage :
    (liftedHorizontalHom Λ B hS X hX).fSharpInverseImage = liftedHorizontalMapInverse Λ B hS X hX :=
  Equiv.symm_apply_apply
    ((commRingImageAdjunction (liftedIdentityTopos Λ B hS X hX)).homEquiv _ _)
    (liftedHorizontalMapInverse Λ B hS X hX)

/-- The morphism of ringed topoi `π : (Sh(C_{X/Λ}), π⁻¹𝒪_X) ⟶ (Sh(X_étale), 𝒪_X)`, whose
structure map is the unit of the adjunction `π⁻¹ ⊣ π_*` on sheaves of rings. -/
def liftedVerticalHom :
    RingedToposHom
      ⟨PolynomialChart Λ B hS X hX, topology Λ B hS X hX,
        (inverseImageCommRingFunctor (liftedProjection Λ B hS X hX)).obj
          (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩)⟩
      ⟨SmallEtale B (Spec (CommRingCat.of Λ)) hS X,
        SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X,
        smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩⟩ where
  toToposHom := liftedProjection Λ B hS X hX
  fSharp := (commRingImageAdjunction (liftedProjection Λ B hS X hX)).unit.app
    (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩)

end

end AlgebraicGeometry.Space.PolynomialChart

end
