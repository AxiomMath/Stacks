module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import StacksFrontier.Cotangent.SheavesOfRings.AffineEmptyChart
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CommRingPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAFibredCategory
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoiRing
public import StacksFrontier.Cotangent.SheavesOfRings.PolynomialChartSpaceFibred
import StacksCore.Tactic.StacksAttribute

/-!
# The ringed topoi of the polynomial charts of an algebraic space

Let `X` be an algebraic space over a ring `Λ` and let `C_{X/Λ}` be its category of polynomial
charts, fibred over the small étale site `X_étale`. Giving `C_{X/Λ}` the inherited topology makes
the forgetful functor `u : C_{X/Λ} ⥤ X_étale` continuous and cocontinuous, hence induces a
morphism of topoi `π : Sh(C_{X/Λ}) ⟶ Sh(X_étale)`. The site carries two sheaves of rings — the
affine functions `𝒪 : (U ⟶ A) ↦ Γ(A, 𝒪_A)` and the inverse image `π⁻¹𝒪_X` — together with the
constant sheaf `Λ`, and this file produces the resulting diagram of ringed topoi
```
(Sh(C_{X/Λ}), π⁻¹𝒪_X) --i--> (Sh(C_{X/Λ}), 𝒪)
        |
        π
        v
(Sh(X_étale), 𝒪_X)
```
in which `i` is the identity on underlying topoi and `i♯ : 𝒪 ⟶ π⁻¹𝒪_X` is the sheafification of
the evaluation map `Γ(A, 𝒪_A) ⟶ 𝒪_X(U)`.

## Main definitions

* `AlgebraicGeometry.Space.PolynomialChart.affinePresheaf`: the presheaf `(U ⟶ A) ↦ Γ(A, 𝒪_A)`.
* `AlgebraicGeometry.Space.PolynomialChart.etalePresheaf`: the restriction of the structure sheaf
  of `X_étale` along the forgetful functor, `(U ⟶ A) ↦ 𝒪_X(U)`.
* `AlgebraicGeometry.Space.PolynomialChart.evaluation`: the map from affine functions to étale
  functions given by pullback along `U ⟶ A`.
* `AlgebraicGeometry.Space.PolynomialChart.topology`: the topology inherited from `X_étale`.
* `AlgebraicGeometry.Space.PolynomialChart.projection`: the morphism of topoi induced by the
  forgetful functor.
* `AlgebraicGeometry.Space.PolynomialChart.PiSpacesDiagram`: the diagram of ringed topoi together
  with canonical characterizations of all of its arrows and comparison isomorphisms.

## Main results

* `AlgebraicGeometry.Space.PolynomialChart.fibreInitial`, the trivial chart `U ⟶ Spec Λ[∅]`, is
  an initial object of the fibre of the forgetful functor over an object `U` of `X_étale`, so the
  right Kan extension along `u.op` exists with values in `Type u`, the universe of the sections of
  `𝒪_X`, although `C_{X/Λ}` lives in `Type (u + 1)`.
* `AlgebraicGeometry.Space.PolynomialChart.etalePresheaf_isSheaf`: `(U ⟶ A) ↦ 𝒪_X(U)` is already a
  sheaf, and `π⁻¹𝒪_X` is its sheafification, the comparison being the sheafification unit on
  sections.
* `AlgebraicGeometry.Space.PolynomialChart.piSpacesDiagram`: the diagram above.

## References

* [Stacks Project, Tag 08VK](https://stacks.math.columbia.edu/tag/08VK)
* [Stacks Project, Tag 08P8](https://stacks.math.columbia.edu/tag/08P8)
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

/-! ### The two presheaves of rings on the category of polynomial charts -/

/-- The affine space of a polynomial chart, functorially in the chart. -/
def affineFunctor : PolynomialChart Λ B hS X hX ⥤ Scheme.{u} where
  obj P := P.affineSpace
  map f := f.affine
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The presheaf `(U ⟶ A) ↦ Γ(A, 𝒪_A)` of global functions on the affine space of a chart,
denoted `𝒪`. -/
def affinePresheaf : (PolynomialChart Λ B hS X hX)ᵒᵖ ⥤ CommRingCat.{u} :=
  (affineFunctor Λ B hS X hX).op ⋙ Scheme.Γ

/-- The presheaf `(U ⟶ A) ↦ 𝒪_X(U)`, the structure sheaf of the small étale site of `X`
restricted along the forgetful functor. -/
def etalePresheaf : (PolynomialChart Λ B hS X hX)ᵒᵖ ⥤ CommRingCat.{u} :=
  (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).op ⋙
    structurePresheaf B (Spec (CommRingCat.of Λ)) hS X

/-- Pullback of functions along the arrow `U ⟶ A` of a polynomial chart, natural in the chart.
Its sheafification is the map `i♯ : 𝒪 ⟶ π⁻¹𝒪_X`. -/
def evaluation : affinePresheaf Λ B hS X hX ⟶ etalePresheaf Λ B hS X hX where
  app P := Scheme.Γ.map P.unop.toAffine.op
  naturality := by
    intro P Q f
    change Scheme.Γ.map f.unop.affine.op ≫ Scheme.Γ.map Q.unop.toAffine.op =
      Scheme.Γ.map P.unop.toAffine.op ≫
        Scheme.Γ.map ((smallEtaleToScheme Λ B hS X).map f.unop.openMap).op
    rw [← Scheme.Γ.map_comp, ← Scheme.Γ.map_comp]
    exact congrArg Scheme.Γ.map (congrArg Quiver.Hom.op f.unop.map_comm)

/-! ### The inherited topology -/

/-- The topology on the category of polynomial charts inherited from the small étale site
of `X`: a family covers when each member is strongly cartesian over its image and the family of
images covers. -/
abbrev topology : GrothendieckTopology (PolynomialChart Λ B hS X hX) :=
  (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).inheritedTopology
    (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)

/-- The forgetful functor from polynomial charts to the small étale site is continuous for the
inherited topology. -/
instance isContinuous_openFunctor :
    (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).IsContinuous
      (topology Λ B hS X hX) (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X) :=
  Stacks.Sites.FibredCategory.isContinuous_inheritedTopology_of_isFibered _ _

/-- The forgetful functor from polynomial charts to the small étale site is cocontinuous for the
inherited topology. -/
instance isCocontinuous_openFunctor :
    (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).IsCocontinuous
      (topology Λ B hS X hX) (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X) :=
  Stacks.Sites.FibredCategory.isCocontinuous_inheritedTopology_of_isFibered _ _

/-- The sheaf of rings `𝒪`: the sheafification of the affine-functions presheaf. -/
abbrev affineSheaf [HasWeakSheafify (topology Λ B hS X hX) CommRingCat.{u}] :
    Sheaf (topology Λ B hS X hX) CommRingCat.{u} :=
  (presheafToSheaf (topology Λ B hS X hX) CommRingCat.{u}).obj (affinePresheaf Λ B hS X hX)

/-- The restriction of the structure sheaf of the small étale site of `X` along the forgetful
functor, as a sheaf of rings on the category of polynomial charts. Its underlying presheaf is
`etalePresheaf`. -/
abbrev etaleSheaf : Sheaf (topology Λ B hS X hX) CommRingCat.{u} :=
  ((openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).sheafPushforwardContinuous
    CommRingCat.{u} (topology Λ B hS X hX)
      (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)).obj
    (structureSheaf B (Spec (CommRingCat.of Λ)) hS X hX)

/-- The presheaf `(U ⟶ A) ↦ 𝒪_X(U)` is a sheaf for the inherited topology: the forgetful functor
to the small étale site is continuous, and `𝒪_X` is a sheaf there. -/
theorem etalePresheaf_isSheaf :
    Presheaf.IsSheaf (topology Λ B hS X hX) (etalePresheaf Λ B hS X hX) :=
  (etaleSheaf Λ B hS X hX).property

/-- The sheafification of `etalePresheaf`. -/
abbrev etalePullbackSheaf [HasWeakSheafify (topology Λ B hS X hX) CommRingCat.{u}] :
    Sheaf (topology Λ B hS X hX) CommRingCat.{u} :=
  (presheafToSheaf (topology Λ B hS X hX) CommRingCat.{u}).obj (etalePresheaf Λ B hS X hX)

/-- The constant sheaf of rings `Λ` on the category of polynomial charts. -/
abbrev constantBaseSheaf [HasWeakSheafify (topology Λ B hS X hX) CommRingCat.{u}] :
    Sheaf (topology Λ B hS X hX) CommRingCat.{u} :=
  (presheafToSheaf (topology Λ B hS X hX) CommRingCat.{u}).obj
    ((Functor.const (PolynomialChart Λ B hS X hX)ᵒᵖ).obj (CommRingCat.of Λ))

/-- `constantBaseSheaf` is the value of the constant-sheaf functor at `Λ`. -/
theorem constantSheaf_obj_eq [HasWeakSheafify (topology Λ B hS X hX) CommRingCat.{u}] :
    (constantSheaf (topology Λ B hS X hX) CommRingCat.{u}).obj (CommRingCat.of Λ) =
      constantBaseSheaf Λ B hS X hX := rfl

/-! ### Initial objects in the fibres of the forgetful functor -/

/-- The structure morphism `U ⟶ Spec Λ` of an object `U` of the small étale site. -/
def openPartToBase (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) :
    (smallEtaleToScheme Λ B hS X).obj U ⟶ Spec (CommRingCat.of Λ) :=
  B.inclusion.map
    ((SmallEtale.toOver B (Spec (CommRingCat.of Λ)) hS X).obj U).hom

/-- The structure morphisms to `Spec Λ` commute with the maps of the small étale site. -/
theorem map_comp_openPartToBase {U V : SmallEtale B (Spec (CommRingCat.of Λ)) hS X}
    (f : U ⟶ V) :
    (smallEtaleToScheme Λ B hS X).map f ≫ openPartToBase Λ B hS X V =
      openPartToBase Λ B hS X U := by
  change B.inclusion.map
      (((SmallEtale.toOver B (Spec (CommRingCat.of Λ)) hS X).map f).left ≫
        ((SmallEtale.toOver B (Spec (CommRingCat.of Λ)) hS X).obj V).hom) =
    B.inclusion.map (((SmallEtale.toOver B (Spec (CommRingCat.of Λ)) hS X).obj U).hom)
  exact congrArg B.inclusion.map
    (Over.w ((SmallEtale.toOver B (Spec (CommRingCat.of Λ)) hS X).map f))

/-- The trivial chart on `U`: the chart `U ⟶ Spec Λ[∅]` with no variables. -/
def trivialChart (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) :
    PolynomialChart Λ B hS X hX where
  openPart := U
  variableIndex := PEmpty
  affineSpace := Spec (CommRingCat.of (MvPolynomial PEmpty Λ))
  affineEquiv := Iso.refl _
  toAffine := openPartToBase Λ B hS X U ≫ specEmptyEval Λ
  comm := by
    change openPartToBase Λ B hS X U ≫ specEmptyEval Λ ≫ specEmptyConstants Λ =
      openPartToBase Λ B hS X U
    rw [specEmptyEval_comp_specEmptyConstants]
    exact Category.comp_id _

/-- The structural arrow of the affine space of the trivial chart is
`specEmptyConstants Λ : Spec Λ[∅] ⟶ Spec Λ`. -/
theorem trivialChart_toBase (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) :
    (trivialChart Λ B hS X hX U).toBase = specEmptyConstants Λ :=
  Category.id_comp _

/-- The square making the unique arrow out of the trivial chart on `U` a chart morphism, after
composing with the monomorphism `Spec Λ[∅] ⟶ Spec Λ`. -/
theorem trivialChartSquare (P : PolynomialChart Λ B hS X hX)
    (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) (f : P.openPart ⟶ U) :
    (P.toAffine ≫ P.affineEquiv.hom ≫ specEmptyToVariables (Λ := Λ) (σ := P.variableIndex)) ≫
        specEmptyConstants Λ =
      ((smallEtaleToScheme Λ B hS X).map f ≫
        openPartToBase Λ B hS X U ≫ specEmptyEval Λ) ≫ specEmptyConstants Λ := by
  simp only [Category.assoc]
  rw [specEmptyToVariables_comp_specEmptyConstants, specEmptyEval_comp_specEmptyConstants,
    Category.comp_id]
  exact P.comm.trans (map_comp_openPartToBase Λ B hS X f).symm

/-- The unique morphism from a chart `P` to the trivial chart on `U`, over a given arrow
`P.openPart ⟶ U` of the small étale site. -/
def toTrivialChart (P : PolynomialChart Λ B hS X hX)
    (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) (f : P.openPart ⟶ U) :
    P ⟶ trivialChart Λ B hS X hX U where
  openMap := f
  affine := P.affineEquiv.hom ≫ specEmptyToVariables (Λ := Λ) (σ := P.variableIndex)
  map_comm := (cancel_mono (specEmptyConstants Λ)).1 (trivialChartSquare Λ B hS X hX P U f)
  base_comm :=
    (Category.assoc _ _ _).trans
      (congrArg (fun g => P.affineEquiv.hom ≫ g)
        (specEmptyToVariables_comp_specEmptyConstants Λ P.variableIndex))

/-- The trivial chart on `U`, as an object of the fibre of `u.op` over `U`. -/
def fibreInitial (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) :
    StructuredArrow (Opposite.op U)
      (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).op :=
  StructuredArrow.mk (S := Opposite.op U)
    (T := (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).op)
    (Y := Opposite.op (trivialChart Λ B hS X hX U)) (𝟙 (Opposite.op U))

/-- The structural arrow of the affine space of `fibreInitial` is `specEmptyConstants Λ`. -/
theorem fibreInitial_right_toBase (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) :
    (Opposite.unop (fibreInitial Λ B hS X hX U).right).toBase = specEmptyConstants Λ :=
  trivialChart_toBase Λ B hS X hX U

/-- The arrow from the trivial chart to an arbitrary object of the fibre over `U`. -/
def fibreInitialHom (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (Z : StructuredArrow (Opposite.op U)
      (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).op) :
    fibreInitial Λ B hS X hX U ⟶ Z := by
  refine StructuredArrow.homMk
    (Quiver.Hom.op (toTrivialChart Λ B hS X hX Z.right.unop U Z.hom.unop)) ?_
  change (𝟙 _) ≫
    (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).op.map
      (Quiver.Hom.op (toTrivialChart Λ B hS X hX Z.right.unop U Z.hom.unop)) = Z.hom
  rw [Category.id_comp]
  exact Quiver.Hom.op_unop Z.hom

/-- Every arrow out of `fibreInitial` lies over the structure arrow of its target in the small
étale site. -/
theorem fibreInitialHom_openMap (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (Z : StructuredArrow (Opposite.op U)
      (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).op)
    (g : fibreInitial Λ B hS X hX U ⟶ Z) :
    (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).map
      (Quiver.Hom.unop g.right) = Z.hom.unop := by
  have hgw := StructuredArrow.w g
  change (𝟙 _) ≫
    (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).op.map g.right =
      Z.hom at hgw
  rw [Category.id_comp] at hgw
  exact congrArg Quiver.Hom.unop hgw

/-- Every arrow out of `fibreInitial` is `fibreInitialHom`, so `fibreInitial` is initial in the
fibre over `U`. -/
theorem fibreInitialHom_unique (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (Z : StructuredArrow (Opposite.op U)
      (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).op)
    (f : fibreInitial Λ B hS X hX U ⟶ Z) : f = fibreInitialHom Λ B hS X hX U Z := by
  apply StructuredArrow.hom_ext
  apply Quiver.Hom.unop_inj
  refine Hom.ext ?_ ?_
  · exact (fibreInitialHom_openMap Λ B hS X hX U Z f).trans
      (fibreInitialHom_openMap Λ B hS X hX U Z (fibreInitialHom Λ B hS X hX U Z)).symm
  · have h1 := (Quiver.Hom.unop f.right).base_comm
    have h2 := (Quiver.Hom.unop (fibreInitialHom Λ B hS X hX U Z).right).base_comm
    rw [fibreInitial_right_toBase] at h1 h2
    exact (cancel_mono (specEmptyConstants Λ)).1 (h1.trans h2.symm)

/-- Restriction along `u.op` has a pointwise right Kan extension, with sections in the universe
of the sections of `𝒪_X` rather than in the universe of the site: each fibre of `u.op` has an
initial object, so the limit computing the extension is over a category with an initial object
and exists for size-independent reasons. -/
instance hasPointwiseRightKanExtension_openFunctor_op
    (G : (PolynomialChart Λ B hS X hX)ᵒᵖ ⥤ Type u) :
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
def projection : MorphismOfTopoi
    (Sheaf (topology Λ B hS X hX) (Type u))
    (Sheaf (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X) (Type u)) where
  pushforward := (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X)
    (hX := hX)).sheafPushforwardCocontinuous (Type u) (topology Λ B hS X hX)
      (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)
  inverseImage := (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X)
    (hX := hX)).sheafPushforwardContinuous (Type u) (topology Λ B hS X hX)
      (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)
  adj := (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X)
    (hX := hX)).sheafAdjunctionCocontinuous (Type u) (topology Λ B hS X hX)
      (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)
  preservesFiniteLimits := by
    have hcomp : PreservesFiniteLimits
        ((openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X)
          (hX := hX)).sheafPushforwardContinuous (Type u) (topology Λ B hS X hX)
            (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X) ⋙
          sheafToPresheaf (topology Λ B hS X hX) (Type u)) :=
      preservesFiniteLimits_of_natIso
        ((openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X)
          (hX := hX)).sheafPushforwardContinuousCompSheafToPresheafIso (Type u)
            (topology Λ B hS X hX)
            (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)).symm
    exact preservesFiniteLimits_of_reflects_of_preserves _
      (sheafToPresheaf (topology Λ B hS X hX) (Type u))

/-- The inverse image of `projection` is restriction of sheaves along the forgetful functor. -/
theorem projection_inverseImage :
    (projection Λ B hS X hX).inverseImage =
      (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X)
        (hX := hX)).sheafPushforwardContinuous (Type u) (topology Λ B hS X hX)
          (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X) := rfl

/-- The identity morphism of the topos of sheaves on the category of polynomial charts, the
underlying geometric morphism of `i`. -/
def identityTopos : MorphismOfTopoi
    (Sheaf (topology Λ B hS X hX) (Type u))
    (Sheaf (topology Λ B hS X hX) (Type u)) where
  pushforward := 𝟭 _
  inverseImage := 𝟭 _
  adj := Adjunction.id
  preservesFiniteLimits := by infer_instance

/-! ### The comparison isomorphisms -/

/-- `π⁻¹𝒪_X` is the restriction of `𝒪_X` along the forgetful functor: transporting the ring
operations along restriction of sheaves of sets is restriction of sheaves of rings. -/
def restrictionIso :
    (inverseImageCommRingFunctor (projection Λ B hS X hX)).obj
        (structureSheaf B (Spec (CommRingCat.of Λ)) hS X hX) ≅ etaleSheaf Λ B hS X hX :=
  restrictionCommRingIso (topology Λ B hS X hX)
    (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)
    (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX))
    (structureSheaf B (Spec (CommRingCat.of Λ)) hS X hX)

/-- `π⁻¹𝒪_X` is the sheafification of `(U ⟶ A) ↦ 𝒪_X(U)`. -/
def pullbackIso [HasWeakSheafify (topology Λ B hS X hX) CommRingCat.{u}] :
    (inverseImageCommRingFunctor (projection Λ B hS X hX)).obj
        (structureSheaf B (Spec (CommRingCat.of Λ)) hS X hX) ≅
      etalePullbackSheaf Λ B hS X hX :=
  restrictionIso Λ B hS X hX ≪≫ sheafificationIso (etaleSheaf Λ B hS X hX)

/-- On sections over a chart, the comparison `π⁻¹𝒪_X ≅ (etalePresheaf)^#` is the sheafification
unit of `etalePresheaf`: the first factor is the identity on sections. -/
theorem forget_map_pullbackIso_hom_app
    [HasWeakSheafify (topology Λ B hS X hX) CommRingCat.{u}]
    (P : PolynomialChart Λ B hS X hX) :
    (forget CommRingCat).map ((pullbackIso Λ B hS X hX).hom.hom.app (Opposite.op P)) =
      (forget CommRingCat).map
        ((toSheafify (topology Λ B hS X hX) (etalePresheaf Λ B hS X hX)).app
          (Opposite.op P)) := rfl

/-- `i⁻¹𝒪 = 𝒪`: transporting the ring operations along the identity functor of sheaves of sets
does nothing. -/
def identityRingIso [HasWeakSheafify (topology Λ B hS X hX) CommRingCat.{u}] :
    (inverseImageCommRingFunctor (identityTopos Λ B hS X hX)).obj
      (affineSheaf Λ B hS X hX) ≅ affineSheaf Λ B hS X hX :=
  restrictionCommRingIso (topology Λ B hS X hX) (topology Λ B hS X hX)
    (𝟭 (PolynomialChart Λ B hS X hX)) (affineSheaf Λ B hS X hX)

/-- On sections over a chart, the comparison `identityRingIso` is the identity, as a
heterogeneous equality. -/
theorem forget_map_identityRingIso_hom_app
    [HasWeakSheafify (topology Λ B hS X hX) CommRingCat.{u}]
    (P : PolynomialChart Λ B hS X hX) :
    HEq ((forget CommRingCat).map ((identityRingIso Λ B hS X hX).hom.hom.app (Opposite.op P)))
      ((forget CommRingCat).map
        (𝟙 (((inverseImageCommRingFunctor (identityTopos Λ B hS X hX)).obj
          (affineSheaf Λ B hS X hX)).obj.obj (Opposite.op P)))) := HEq.rfl

/-! ### The constant sheaf `Λ` and its structure map -/

/-- The map from the constant presheaf `Λ` to the affine functions, given on a chart by pullback
along the structural arrow `A ⟶ Spec Λ` of its affine space. -/
def basePresheafMap :
    (Functor.const (PolynomialChart Λ B hS X hX)ᵒᵖ).obj (CommRingCat.of Λ) ⟶
      affinePresheaf Λ B hS X hX where
  app P := (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ Scheme.Γ.map P.unop.toBase.op
  naturality := by
    intro P Q f
    have hbase : f.unop.affine ≫ P.unop.toBase = Q.unop.toBase := f.unop.base_comm
    have hΓ : Scheme.Γ.map P.unop.toBase.op ≫ Scheme.Γ.map f.unop.affine.op =
        Scheme.Γ.map Q.unop.toBase.op := by
      rw [← Scheme.Γ.map_comp]
      exact congrArg Scheme.Γ.map (congrArg Quiver.Hom.op hbase)
    change (𝟙 (CommRingCat.of Λ)) ≫
        ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ Scheme.Γ.map Q.unop.toBase.op) =
      ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ Scheme.Γ.map P.unop.toBase.op) ≫
        Scheme.Γ.map f.unop.affine.op
    rw [Category.id_comp]
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    exact congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ t) hΓ.symm

/-- The structure map `Λ ⟶ 𝒪` from the constant sheaf. -/
def baseSheafMap [HasWeakSheafify (topology Λ B hS X hX) CommRingCat.{u}] :
    constantBaseSheaf Λ B hS X hX ⟶ affineSheaf Λ B hS X hX :=
  (presheafToSheaf (topology Λ B hS X hX) CommRingCat.{u}).map (basePresheafMap Λ B hS X hX)

/-- On sections over a chart, `baseSheafMap` is pullback along the structural arrow
`A ⟶ Spec Λ` of its affine space, composed with the sheafification unit. -/
theorem baseSheafMap_canonical [HasWeakSheafify (topology Λ B hS X hX) CommRingCat.{u}]
    (P : PolynomialChart Λ B hS X hX) :
    (toSheafify (topology Λ B hS X hX)
          ((Functor.const (PolynomialChart Λ B hS X hX)ᵒᵖ).obj (CommRingCat.of Λ))).app
        (Opposite.op P) ≫ (baseSheafMap Λ B hS X hX).hom.app (Opposite.op P) =
      ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ Scheme.Γ.map P.toBase.op) ≫
        (toSheafify (topology Λ B hS X hX) (affinePresheaf Λ B hS X hX)).app
          (Opposite.op P) := by
  have h := congrArg (fun t => t.app (Opposite.op P))
    (toSheafify_naturality (topology Λ B hS X hX) (basePresheafMap Λ B hS X hX)).symm
  simp only [NatTrans.comp_app] at h
  exact h

/-- The composite of `basePresheafMap` and `evaluation` on a chart over `U` is pullback along
the structure morphism `U ⟶ Spec Λ`. -/
theorem basePresheafMap_evaluation (P : PolynomialChart Λ B hS X hX) :
    (basePresheafMap Λ B hS X hX).app (Opposite.op P) ≫
        (evaluation Λ B hS X hX).app (Opposite.op P) =
      (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫
        Scheme.Γ.map (openPartToBase Λ B hS X P.openPart).op := by
  have hcomm : P.toAffine ≫ P.toBase = openPartToBase Λ B hS X P.openPart := P.comm
  have hΓ : Scheme.Γ.map P.toBase.op ≫ Scheme.Γ.map P.toAffine.op =
      Scheme.Γ.map (openPartToBase Λ B hS X P.openPart).op := by
    rw [← Scheme.Γ.map_comp]
    exact congrArg Scheme.Γ.map (congrArg Quiver.Hom.op hcomm)
  change ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ Scheme.Γ.map P.toBase.op) ≫
      Scheme.Γ.map P.toAffine.op =
    (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫
      Scheme.Γ.map (openPartToBase Λ B hS X P.openPart).op
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ t) hΓ

/-- On sections over a chart over `U`, the composite of `baseSheafMap` with the sheafified
evaluation is pullback along `U ⟶ Spec Λ`, composed with the sheafification unit. -/
theorem baseSheafMap_horizontal [HasWeakSheafify (topology Λ B hS X hX) CommRingCat.{u}]
    (P : PolynomialChart Λ B hS X hX) :
    (toSheafify (topology Λ B hS X hX)
          ((Functor.const (PolynomialChart Λ B hS X hX)ᵒᵖ).obj (CommRingCat.of Λ))).app
        (Opposite.op P) ≫ (baseSheafMap Λ B hS X hX).hom.app (Opposite.op P) ≫
        ((presheafToSheaf (topology Λ B hS X hX) CommRingCat.{u}).map
          (evaluation Λ B hS X hX)).hom.app (Opposite.op P) =
      (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫
        Scheme.Γ.map (openPartToBase Λ B hS X P.openPart).op ≫
          (toSheafify (topology Λ B hS X hX) (etalePresheaf Λ B hS X hX)).app
            (Opposite.op P) := by
  have hnat := congrArg (fun t => t.app (Opposite.op P))
    (toSheafify_naturality (topology Λ B hS X hX)
      (basePresheafMap Λ B hS X hX ≫ evaluation Λ B hS X hX)).symm
  simp only [NatTrans.comp_app, sheafifyMap_comp, Category.assoc] at hnat
  refine hnat.trans ?_
  refine ((Category.assoc _ _ _).symm.trans (congrArg
    (fun t => t ≫ (toSheafify (topology Λ B hS X hX) (etalePresheaf Λ B hS X hX)).app
      (Opposite.op P)) (basePresheafMap_evaluation Λ B hS X hX P))).trans
    (Category.assoc _ _ _)

/-! ### The diagram -/

/-- The diagram of ringed topoi of the polynomial charts: the morphism of ringed topoi
`i : (Sh(C_{X/Λ}), π⁻¹𝒪_X) ⟶ (Sh(C_{X/Λ}), 𝒪)` and the morphism of ringed topoi
`π : (Sh(C_{X/Λ}), π⁻¹𝒪_X) ⟶ (Sh(X_étale), 𝒪_X)`, both out of `(Sh(C_{X/Λ}), π⁻¹𝒪_X)`. The
diagram has only these two arrows: there is no morphism of ringed topoi from `(Sh(C_{X/Λ}), 𝒪)`
to `(Sh(X_étale), 𝒪_X)` in it, and no commutativity is asserted. The structure also records the
canonical characterizations of all of its data: `i` is the identity on underlying topoi with
`i♯ : 𝒪 ⟶ π⁻¹𝒪_X` the sheafification of evaluation, `π` is induced by the forgetful functor with
`π♯` the unit of `π⁻¹ ⊣ π_*`, the two comparison isomorphisms, and the structure map `Λ ⟶ 𝒪`.

Here `𝒪` is the sheafification of the presheaf `(U ⟶ A) ↦ Γ(A, 𝒪_A)`; that presheaf is not
itself a sheaf when `Λ ≠ 0`, since the empty family covers a chart with `U = ∅`. -/
structure PiSpacesDiagram [HasWeakSheafify (topology Λ B hS X hX) CommRingCat.{u}] where
  /-- The structure map from the constant sheaf `Λ` to the affine functions. -/
  baseStructureMap : constantBaseSheaf Λ B hS X hX ⟶ affineSheaf Λ B hS X hX
  /-- On a chart, the structure map from `Λ` is pullback along the structural arrow of its
  affine space. -/
  baseStructureMap_canonical : ∀ P : PolynomialChart Λ B hS X hX,
    (toSheafify (topology Λ B hS X hX)
          ((Functor.const (PolynomialChart Λ B hS X hX)ᵒᵖ).obj (CommRingCat.of Λ))).app
        (Opposite.op P) ≫ baseStructureMap.hom.app (Opposite.op P) =
      ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ Scheme.Γ.map P.toBase.op) ≫
        (toSheafify (topology Λ B hS X hX) (affinePresheaf Λ B hS X hX)).app (Opposite.op P)
  /-- The geometric morphism `π`. -/
  projectionTopos : MorphismOfTopoi
    (Sheaf (topology Λ B hS X hX) (Type u))
    (Sheaf (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X) (Type u))
  /-- `π⁻¹` is restriction along the forgetful functor. -/
  projectionTopos_inverseImage :
    projectionTopos.inverseImage =
      (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X)
        (hX := hX)).sheafPushforwardContinuous (Type u) (topology Λ B hS X hX)
          (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)
  /-- The morphism of ringed topoi `π`. -/
  vertical : RingedToposHom
    ⟨PolynomialChart Λ B hS X hX, topology Λ B hS X hX,
      (inverseImageCommRingFunctor projectionTopos).obj
        (structureSheaf B (Spec (CommRingCat.of Λ)) hS X hX)⟩
    ⟨SmallEtale B (Spec (CommRingCat.of Λ)) hS X,
      SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X,
      structureSheaf B (Spec (CommRingCat.of Λ)) hS X hX⟩
  /-- Its underlying geometric morphism is `π`. -/
  vertical_topos : vertical.toToposHom = projectionTopos
  /-- Its structure map is the unit of the adjunction `π⁻¹ ⊣ π_*` on sheaves of rings. -/
  vertical_fSharp : HEq vertical.fSharp
    ((commRingImageAdjunction projectionTopos).unit.app
      (structureSheaf B (Spec (CommRingCat.of Λ)) hS X hX))
  /-- `π⁻¹𝒪_X` is the sheafification of `(U ⟶ A) ↦ 𝒪_X(U)`. -/
  pullbackIso : (inverseImageCommRingFunctor projectionTopos).obj
      (structureSheaf B (Spec (CommRingCat.of Λ)) hS X hX) ≅ etalePullbackSheaf Λ B hS X hX
  /-- The presheaf `(U ⟶ A) ↦ 𝒪_X(U)` is already a sheaf. -/
  etaleIsSheaf : Presheaf.IsSheaf (topology Λ B hS X hX) (etalePresheaf Λ B hS X hX)
  /-- On sections the comparison is the sheafification unit. -/
  pullbackIso_canonical : ∀ P : PolynomialChart Λ B hS X hX,
    HEq ((forget CommRingCat).map (pullbackIso.hom.hom.app (Opposite.op P)))
      ((forget CommRingCat).map
        ((toSheafify (topology Λ B hS X hX) (etalePresheaf Λ B hS X hX)).app (Opposite.op P)))
  /-- The morphism of ringed topoi `i`. -/
  horizontal : RingedToposHom
    ⟨PolynomialChart Λ B hS X hX, topology Λ B hS X hX,
      (inverseImageCommRingFunctor projectionTopos).obj
        (structureSheaf B (Spec (CommRingCat.of Λ)) hS X hX)⟩
    ⟨PolynomialChart Λ B hS X hX, topology Λ B hS X hX, affineSheaf Λ B hS X hX⟩
  /-- The inverse image of `i` is the identity functor. -/
  horizontal_inverseImage : horizontal.toToposHom.inverseImage = 𝟭 _
  /-- The direct image of `i` is the identity functor. -/
  horizontal_pushforward : horizontal.toToposHom.pushforward = 𝟭 _
  /-- The identification `i⁻¹𝒪 ≅ 𝒪`. -/
  horizontalIdentityIso :
    (inverseImageCommRingFunctor horizontal.toToposHom).obj (affineSheaf Λ B hS X hX) ≅
      affineSheaf Λ B hS X hX
  /-- The identification `i⁻¹𝒪 ≅ 𝒪` is the identity on sections. -/
  horizontalIdentityIso_canonical : ∀ P : PolynomialChart Λ B hS X hX,
    HEq ((forget CommRingCat).map (horizontalIdentityIso.hom.hom.app (Opposite.op P)))
      ((forget CommRingCat).map
        (𝟙 (((inverseImageCommRingFunctor horizontal.toToposHom).obj
          (affineSheaf Λ B hS X hX)).obj.obj (Opposite.op P))))
  /-- `i♯`, in inverse-image form, is the sheafification of the evaluation map. -/
  horizontal_fSharp :
    horizontalIdentityIso.inv ≫ horizontal.fSharpInverseImage ≫ pullbackIso.hom =
      (presheafToSheaf (topology Λ B hS X hX) CommRingCat.{u}).map (evaluation Λ B hS X hX)
  /-- The composite `Λ ⟶ 𝒪 ⟶ π⁻¹𝒪_X` is pullback along the structure morphism of `U`. -/
  baseStructureMap_horizontal : ∀ P : PolynomialChart Λ B hS X hX,
    (toSheafify (topology Λ B hS X hX)
          ((Functor.const (PolynomialChart Λ B hS X hX)ᵒᵖ).obj (CommRingCat.of Λ))).app
        (Opposite.op P) ≫ baseStructureMap.hom.app (Opposite.op P) ≫
        ((presheafToSheaf (topology Λ B hS X hX) CommRingCat.{u}).map
          (evaluation Λ B hS X hX)).hom.app (Opposite.op P) =
      (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫
        Scheme.Γ.map (openPartToBase Λ B hS X P.openPart).op ≫
          (toSheafify (topology Λ B hS X hX) (etalePresheaf Λ B hS X hX)).app (Opposite.op P)

/-- The inverse-image form of `i♯`: evaluation, read from `𝒪` to `π⁻¹𝒪_X` through the two
comparison isomorphisms. -/
def horizontalMapInverse [HasWeakSheafify (topology Λ B hS X hX) CommRingCat.{u}] :
    (inverseImageCommRingFunctor (identityTopos Λ B hS X hX)).obj (affineSheaf Λ B hS X hX) ⟶
      (inverseImageCommRingFunctor (projection Λ B hS X hX)).obj
        (structureSheaf B (Spec (CommRingCat.of Λ)) hS X hX) :=
  (identityRingIso Λ B hS X hX).hom ≫
    (presheafToSheaf (topology Λ B hS X hX) CommRingCat.{u}).map (evaluation Λ B hS X hX) ≫
      (pullbackIso Λ B hS X hX).inv

/-- Composed with the two comparison isomorphisms, `horizontalMapInverse` is the sheafification
of `evaluation`. -/
theorem horizontalMapInverse_cancel
    [HasWeakSheafify (topology Λ B hS X hX) CommRingCat.{u}] :
    (identityRingIso Λ B hS X hX).inv ≫ horizontalMapInverse Λ B hS X hX ≫
        (pullbackIso Λ B hS X hX).hom =
      (presheafToSheaf (topology Λ B hS X hX) CommRingCat.{u}).map
        (evaluation Λ B hS X hX) := by
  simp only [horizontalMapInverse, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc]

/-- The morphism of ringed topoi `i`, whose structure map in inverse-image form is evaluation. -/
def horizontalHom [HasWeakSheafify (topology Λ B hS X hX) CommRingCat.{u}] :
    RingedToposHom
      ⟨PolynomialChart Λ B hS X hX, topology Λ B hS X hX,
        (inverseImageCommRingFunctor (projection Λ B hS X hX)).obj
          (structureSheaf B (Spec (CommRingCat.of Λ)) hS X hX)⟩
      ⟨PolynomialChart Λ B hS X hX, topology Λ B hS X hX, affineSheaf Λ B hS X hX⟩ where
  toToposHom := identityTopos Λ B hS X hX
  fSharp := (commRingImageAdjunction (identityTopos Λ B hS X hX)).homEquiv _ _
    (horizontalMapInverse Λ B hS X hX)

/-- The structure map of `horizontalHom` in inverse-image form is `horizontalMapInverse`. -/
theorem horizontalHom_fSharpInverseImage
    [HasWeakSheafify (topology Λ B hS X hX) CommRingCat.{u}] :
    (horizontalHom Λ B hS X hX).fSharpInverseImage = horizontalMapInverse Λ B hS X hX :=
  Equiv.symm_apply_apply
    ((commRingImageAdjunction (identityTopos Λ B hS X hX)).homEquiv _ _)
    (horizontalMapInverse Λ B hS X hX)

/-- The diagram of ringed topoi of the polynomial charts of an algebraic space over a ring: the
morphisms of ringed topoi `i : (Sh(C_{X/Λ}), π⁻¹𝒪_X) ⟶ (Sh(C_{X/Λ}), 𝒪)` and
`π : (Sh(C_{X/Λ}), π⁻¹𝒪_X) ⟶ (Sh(X_étale), 𝒪_X)`, with all of their data pinned to the
canonical ones. -/
@[stacks 08VK "the morphisms of ringed topoi i and π out of (Sh(C_{X/Λ}), π⁻¹𝒪_X); 𝒪 is taken \
as the sheafification of (U ⟶ A) ↦ Γ(A, 𝒪_A), which is not a sheaf at charts with U = ∅"]
def piSpacesDiagram [HasWeakSheafify (topology Λ B hS X hX) CommRingCat.{u}] :
    PiSpacesDiagram Λ B hS X hX where
  baseStructureMap := baseSheafMap Λ B hS X hX
  baseStructureMap_canonical := baseSheafMap_canonical Λ B hS X hX
  projectionTopos := projection Λ B hS X hX
  projectionTopos_inverseImage := projection_inverseImage Λ B hS X hX
  vertical :=
    { toToposHom := projection Λ B hS X hX
      fSharp := (commRingImageAdjunction (projection Λ B hS X hX)).unit.app
        (structureSheaf B (Spec (CommRingCat.of Λ)) hS X hX) }
  vertical_topos := rfl
  vertical_fSharp := HEq.rfl
  pullbackIso := pullbackIso Λ B hS X hX
  etaleIsSheaf := etalePresheaf_isSheaf Λ B hS X hX
  pullbackIso_canonical := fun P =>
    heq_of_eq (forget_map_pullbackIso_hom_app Λ B hS X hX P)
  horizontal := horizontalHom Λ B hS X hX
  horizontal_inverseImage := rfl
  horizontal_pushforward := rfl
  horizontalIdentityIso := identityRingIso Λ B hS X hX
  horizontalIdentityIso_canonical := forget_map_identityRingIso_hom_app Λ B hS X hX
  horizontal_fSharp := by
    rw [horizontalHom_fSharpInverseImage]
    exact horizontalMapInverse_cancel Λ B hS X hX
  baseStructureMap_horizontal := baseSheafMap_horizontal Λ B hS X hX

end

end AlgebraicGeometry.Space.PolynomialChart

end
