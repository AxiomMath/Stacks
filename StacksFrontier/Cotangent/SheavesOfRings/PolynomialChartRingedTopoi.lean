module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import StacksFrontier.Cotangent.SheavesOfRings.AffineEmptyChart
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.AlgebraicGeometry.SheafifyCommRing.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAFibredCategory
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
public import StacksFrontier.Cotangent.PolynomialChart
public import StacksFrontier.Cotangent.SheavesOfRings.PolynomialChartFibred

/-!
# The ringed topoi of the polynomial charts of a scheme

Let `X` be a scheme over a ring `Λ` and let `C_{X/Λ}` be its category of polynomial charts,
fibred over the Zariski site of `X`. Giving `C_{X/Λ}` the inherited topology makes the forgetful
functor `u : C_{X/Λ} ⥤ X_Zar` continuous and cocontinuous, hence induces a morphism of topoi
`π : Sh(C_{X/Λ}) ⟶ Sh(X_Zar)`. The site carries two sheaves of rings — the affine functions
`𝒪 : (U ⟶ A) ↦ Γ(A, 𝒪_A)` and the inverse image `π⁻¹𝒪_X` — together with the constant sheaf
`Λ`, and this file produces the resulting diagram of ringed topoi
```
(Sh(C_{X/Λ}), π⁻¹𝒪_X) --i--> (Sh(C_{X/Λ}), 𝒪)
        |
        π
        v
    (Sh(X_Zar), 𝒪_X)
```
in which `i` is the identity on underlying topoi and `i♯ : 𝒪 ⟶ π⁻¹𝒪_X` is the sheafification of
the evaluation map `Γ(A, 𝒪_A) ⟶ 𝒪_X(U)`.

## Main definitions

* `AlgebraicGeometry.PolynomialChart.topology`: the topology inherited from the Zariski site.
* `AlgebraicGeometry.PolynomialChart.affinePresheaf`: the presheaf `(U ⟶ A) ↦ Γ(A, 𝒪_A)`.
* `AlgebraicGeometry.PolynomialChart.zariskiPresheaf`: the restriction of `𝒪_X` along the
  forgetful functor, `(U ⟶ A) ↦ 𝒪_X(U)`.
* `AlgebraicGeometry.PolynomialChart.evaluation`: the map from affine functions to functions on
  the open subscheme, given by pullback along `U ⟶ A`.
* `AlgebraicGeometry.PolynomialChart.projection`: the morphism of topoi induced by the forgetful
  functor.
* `AlgebraicGeometry.PolynomialChart.PiSchemesDiagram`: the diagram of ringed topoi together
  with canonical characterizations of all of its arrows and comparison isomorphisms.

## Main results

* `AlgebraicGeometry.PolynomialChart.hasWeakSheafify_topology`: presheaves of commutative rings
  on the chart site admit sheafification in the coefficient universe.
* `AlgebraicGeometry.PolynomialChart.hasInitial_fibre`: the chart with no variables is initial
  in each fibre of the forgetful functor, which is what makes the right Kan extension along
  `u.op` exist with sections in the coefficient universe even though `C_{X/Λ}` is large.
* `AlgebraicGeometry.PolynomialChart.piSchemesDiagram`: **Stacks 08VA**, the diagram above.

## Implementation notes

The coefficient universe is `max w (u + 1)` for an independent universe variable `w`. The
`u + 1` is forced rather than chosen: a polynomial chart carries a `Type u` set of variables, so
the chart category has objects in `Type (u + 1)`, and sheafification of commutative rings on a
site with objects in `Type (u + 1)` is available only in a coefficient universe containing
`u + 1`. It is then supplied by `Stacks.SheafifyCommRing.hasSheafifyCommRingCat` and is not a
hypothesis. Accordingly `𝒪_X`, whose sections live in universe `u`, is presented in the
coefficient universe by the canonical `ULift` of its section rings.

The morphism of topoi is built from an initial object of each fibre of `u.op` rather than from
the general construction for a fibred category, which forms it with sections large enough to
contain the site. Over `U` the chart `U ⟶ Spec Λ[∅]` with no variables is initial: a chart map
into it is forced by the monomorphism `Spec Λ[∅] ⟶ Spec Λ`, and the inclusion of open
subschemes is a proposition. Continuity and cocontinuity of `u` are taken from the fibred
category development, where they hold for an arbitrary fibred category with no hypothesis on
the base site.

The comparison `π⁻¹𝒪_X ≅ (𝒪_X restricted along u)` is
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`: transporting the ring operations of a
sheaf along restriction of sheaves of sets *is* restriction of sheaves of rings, and the
comparison is the identity on sections. In particular `zariskiPresheaf` is already a sheaf. The
two characterizations of the comparisons are stated with `HEq` only because the field they
constrain is quantified over an arbitrary morphism of topoi, so its source is not syntactically
the restriction functor.

## References

* [Stacks Project, Tag 08VA](https://stacks.math.columbia.edu/tag/08VA)
* [Stacks Project, Tag 08V8](https://stacks.math.columbia.edu/tag/08V8)
* [Stacks Project, Tag 08V9](https://stacks.math.columbia.edu/tag/08V9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.AffineEmptyChart
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u w

namespace AlgebraicGeometry.PolynomialChart

noncomputable section

variable (Λ : Type u) [CommRing Λ] (X : Scheme.{u})
    (structureMap : X ⟶ Spec (CommRingCat.of Λ))

/-! ### The inherited topology -/

/-- The topology on the category of polynomial charts inherited from the Zariski site of `X`:
a family covers when each member is strongly cartesian over its image and the images cover. -/
abbrev topology : GrothendieckTopology (PolynomialChart Λ X structureMap) :=
  (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).inheritedTopology
    (Opens.grothendieckTopology X.carrier)

/-- Presheaves of commutative rings on the chart site admit sheafification in the coefficient
universe: the chart category has objects in `Type (u + 1)` and arrows in `Type u`. -/
theorem hasWeakSheafify_topology :
    HasWeakSheafify (topology Λ X structureMap) CommRingCat.{max w (u + 1)} := inferInstance

/-! ### Presentation in the coefficient universe -/

/-- Commutative rings of the scheme's universe, presented in the coefficient universe. -/
abbrev liftRing : CommRingCat.{u} ⥤ CommRingCat.{max w (u + 1)} :=
  SheafOfModules.commRingCatULift.{u, max w (u + 1)}

/-- The structure sheaf `𝒪_X` of the Zariski site, presented in the coefficient universe of the
chart topos by the canonical lift of its section rings. -/
def liftedStructureSheaf :
    Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{max w (u + 1)} where
  obj := X.sheaf.obj ⋙ liftRing.{u, w}
  property := by
    have : HasLimitsOfSize.{u, u} CommRingCat.{max w (u + 1)} :=
      hasLimitsOfSizeShrink.{u, u, max w (u + 1), max w (u + 1)} _
    refine (Presheaf.isSheaf_iff_isSheaf_comp _ _
      (forget CommRingCat.{max w (u + 1)})).mpr ?_
    change Presheaf.IsSheaf _
      ((X.sheaf.obj ⋙ forget CommRingCat.{u}) ⋙ uliftFunctor.{max w (u + 1), u})
    exact Presheaf.isSheaf_comp_of_isSheaf _ _ _
      ((sheafCompose _ (forget CommRingCat.{u})).obj X.sheaf).property

/-! ### Continuity and the geometric morphism `π` -/

/-- The forgetful functor `u : C_{X/Λ} ⥤ X_Zar` is continuous for the inherited topology. -/
instance isContinuous_openFunctor :
    (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).IsContinuous
      (topology Λ X structureMap) (Opens.grothendieckTopology X.carrier) :=
  Stacks.Sites.FibredCategory.isContinuous_inheritedTopology_of_isFibered _ _

/-- The forgetful functor `u : C_{X/Λ} ⥤ X_Zar` is cocontinuous for the inherited topology. -/
instance isCocontinuous_openFunctor :
    (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).IsCocontinuous
      (topology Λ X structureMap) (Opens.grothendieckTopology X.carrier) :=
  Stacks.Sites.FibredCategory.isCocontinuous_inheritedTopology_of_isFibered _ _

/-! ### Initial objects in the fibres of the forgetful functor -/

/-- The chart `U ⟶ Spec Λ[∅]` with no variables on an open subscheme `U`: its chart map is the
inclusion of `U` followed by the structure morphism of `X` and the map `Spec Λ ⟶ Spec Λ[∅]`. -/
def trivialChart (U : X.Opens) : PolynomialChart Λ X structureMap where
  openPart := U
  variableIndex := PEmpty.{u + 1}
  affineSpace := Spec (CommRingCat.of (MvPolynomial PEmpty.{u + 1} Λ))
  affineEquiv := Iso.refl _
  toAffine := U.ι ≫ structureMap ≫ specEmptyEval Λ
  comm := by
    change (U.ι ≫ structureMap ≫ specEmptyEval Λ) ≫ 𝟙 _ ≫ specEmptyConstants Λ =
      U.ι ≫ structureMap
    rw [Category.id_comp, Category.assoc, Category.assoc,
      specEmptyEval_comp_specEmptyConstants, Category.comp_id]

/-- The structural arrow of the trivial chart is the structural arrow `Spec Λ[∅] ⟶ Spec Λ` of the
affine space with no variables. -/
theorem trivialChart_toBase (U : X.Opens) :
    (trivialChart Λ X structureMap U).toBase = specEmptyConstants Λ :=
  Category.id_comp _

/-- The morphism from a chart to the trivial chart on an open subscheme containing it. -/
def toTrivialChart (P : PolynomialChart Λ X structureMap) (U : X.Opens)
    (h : P.openPart ≤ U) : P ⟶ trivialChart Λ X structureMap U where
  open_le := h
  affine := P.affineEquiv.hom ≫ specEmptyToVariables (Λ := Λ) (σ := P.variableIndex)
  map_comm := by
    refine (cancel_mono (specEmptyConstants Λ)).1 ?_
    have hL : (P.toAffine ≫ P.affineEquiv.hom ≫
          specEmptyToVariables (Λ := Λ) (σ := P.variableIndex)) ≫ specEmptyConstants Λ =
        P.openPart.ι ≫ structureMap := by
      simp only [Category.assoc]
      rw [specEmptyToVariables_comp_specEmptyConstants]
      exact P.comm
    have hR : (X.homOfLE h ≫ (trivialChart Λ X structureMap U).toAffine) ≫
        specEmptyConstants Λ = P.openPart.ι ≫ structureMap := by
      change (X.homOfLE h ≫ U.ι ≫ structureMap ≫ specEmptyEval Λ) ≫
        specEmptyConstants Λ = _
      simp only [Category.assoc]
      rw [specEmptyEval_comp_specEmptyConstants, Category.comp_id, ← Category.assoc,
        Scheme.homOfLE_ι]
    exact hL.trans hR.symm
  base_comm := by
    change (P.affineEquiv.hom ≫ specEmptyToVariables (Λ := Λ) (σ := P.variableIndex)) ≫
      (trivialChart Λ X structureMap U).toBase = P.toBase
    rw [trivialChart_toBase, Category.assoc,
      specEmptyToVariables_comp_specEmptyConstants]
    rfl

/-- A chart admits at most one morphism to a trivial chart: the arrow between affine spaces is
forced by the monomorphism `Spec Λ[∅] ⟶ Spec Λ`, and the inclusion of opens is a proposition. -/
theorem toTrivialChart_unique (P : PolynomialChart Λ X structureMap) (U : X.Opens)
    (f g : P ⟶ trivialChart Λ X structureMap U) : f = g := by
  refine Hom.ext ?_
  refine (cancel_mono (specEmptyConstants Λ)).1 ?_
  have key (h : P ⟶ trivialChart Λ X structureMap U) :
      h.affine ≫ specEmptyConstants Λ = P.toBase := by
    simpa only [trivialChart_toBase] using h.base_comm
  exact (key f).trans (key g).symm

/-- The trivial chart on `U`, as an object of the fibre of `u.op` over `U`. -/
def fibreInitial (U : X.Opens) :
    StructuredArrow (Opposite.op U)
      (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).op :=
  StructuredArrow.mk (S := Opposite.op U)
    (T := (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).op)
    (Y := Opposite.op (trivialChart Λ X structureMap U)) (𝟙 (Opposite.op U))

/-- The arrow from the trivial chart to an arbitrary object of the fibre over `U`. -/
def fibreInitialHom (U : X.Opens)
    (Z : StructuredArrow (Opposite.op U)
      (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).op) :
    fibreInitial Λ X structureMap U ⟶ Z :=
  StructuredArrow.homMk
    (Quiver.Hom.op (toTrivialChart Λ X structureMap Z.right.unop U Z.hom.unop.le))
    (Subsingleton.elim _ _)

/-- Over an open subscheme `U`, the chart with no variables is an initial object of the fibre
of the forgetful functor. -/
instance hasInitial_fibre (U : X.Opens) :
    HasInitial (StructuredArrow (Opposite.op U)
      (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).op) := by
  have huniq : ∀ Z, Unique (fibreInitial Λ X structureMap U ⟶ Z) := fun Z =>
    { default := fibreInitialHom Λ X structureMap U Z
      uniq := fun f => StructuredArrow.hom_ext _ _
        (Quiver.Hom.unop_inj (toTrivialChart_unique Λ X structureMap _ _ _ _)) }
  exact hasInitial_of_unique (fibreInitial Λ X structureMap U)

/-- Restriction along `u.op` has a pointwise right Kan extension, with sections in the
coefficient universe rather than the universe of the chart site: each fibre of `u.op` has an
initial object, so the limit computing the extension exists for size-independent reasons. -/
instance hasPointwiseRightKanExtension_openFunctor_op
    (F : (PolynomialChart Λ X structureMap)ᵒᵖ ⥤ Type (max w (u + 1))) :
    Functor.HasPointwiseRightKanExtension
      (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).op F := by
  intro Y
  change HasLimit (StructuredArrow.proj Y
    (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).op ⋙ F)
  have : HasInitial (StructuredArrow Y
      (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).op) :=
    hasInitial_fibre Λ X structureMap Y.unop
  infer_instance

/-- The morphism of topoi `π : Sh(C_{X/Λ}) ⟶ Sh(X_Zar)` induced by the forgetful functor: its
inverse image is restriction along `u.op` and its direct image is the right adjoint of that
restriction. -/
def projection : MorphismOfTopoi
    (Sheaf (topology Λ X structureMap) (Type (max w (u + 1))))
    (Sheaf (Opens.grothendieckTopology X.carrier) (Type (max w (u + 1)))) where
  pushforward := (openFunctor (Λ := Λ) (X := X)
    (structureMap := structureMap)).sheafPushforwardCocontinuous (Type (max w (u + 1)))
      (topology Λ X structureMap) (Opens.grothendieckTopology X.carrier)
  inverseImage := (openFunctor (Λ := Λ) (X := X)
    (structureMap := structureMap)).sheafPushforwardContinuous (Type (max w (u + 1)))
      (topology Λ X structureMap) (Opens.grothendieckTopology X.carrier)
  adj := (openFunctor (Λ := Λ) (X := X)
    (structureMap := structureMap)).sheafAdjunctionCocontinuous (Type (max w (u + 1)))
      (topology Λ X structureMap) (Opens.grothendieckTopology X.carrier)
  preservesFiniteLimits := by
    have hcomp : PreservesFiniteLimits
        ((openFunctor (Λ := Λ) (X := X)
          (structureMap := structureMap)).sheafPushforwardContinuous (Type (max w (u + 1)))
            (topology Λ X structureMap) (Opens.grothendieckTopology X.carrier) ⋙
          sheafToPresheaf (topology Λ X structureMap) (Type (max w (u + 1)))) :=
      preservesFiniteLimits_of_natIso
        ((openFunctor (Λ := Λ) (X := X)
          (structureMap := structureMap)).sheafPushforwardContinuousCompSheafToPresheafIso
            (Type (max w (u + 1))) (topology Λ X structureMap)
            (Opens.grothendieckTopology X.carrier)).symm
    exact preservesFiniteLimits_of_reflects_of_preserves _
      (sheafToPresheaf (topology Λ X structureMap) (Type (max w (u + 1))))

/-- The inverse image of `π` is restriction of sheaves along the forgetful functor. -/
theorem projection_inverseImage :
    (projection.{u, w} Λ X structureMap).inverseImage =
      (openFunctor (Λ := Λ) (X := X)
        (structureMap := structureMap)).sheafPushforwardContinuous (Type (max w (u + 1)))
          (topology Λ X structureMap) (Opens.grothendieckTopology X.carrier) := rfl

/-- `π⁻¹𝒪_X`: the inverse image along `π` of the structure sheaf of `X`. -/
def chartStructureSheaf : Sheaf (topology Λ X structureMap) CommRingCat.{max w (u + 1)} :=
  (inverseImageCommRingFunctor (projection.{u, w} Λ X structureMap)).obj
    (liftedStructureSheaf.{u, w} X)

/-! ### The two presheaves of rings on the category of polynomial charts -/

/-- The affine space of a polynomial chart, functorially in the chart. -/
def affineFunctor : PolynomialChart Λ X structureMap ⥤ Scheme.{u} where
  obj P := P.affineSpace
  map f := f.affine
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The presheaf `(U ⟶ A) ↦ Γ(A, 𝒪_A)` of global functions on the affine space of a chart,
denoted `𝒪` in the source. -/
def affineSectionsPresheaf : (PolynomialChart Λ X structureMap)ᵒᵖ ⥤ CommRingCat.{u} :=
  (affineFunctor Λ X structureMap).op ⋙ Scheme.Γ

/-- The presheaf `(U ⟶ A) ↦ 𝒪_X(U)`, the structure sheaf of the Zariski site of `X` restricted
along the forgetful functor. -/
def zariskiSectionsPresheaf : (PolynomialChart Λ X structureMap)ᵒᵖ ⥤ CommRingCat.{u} :=
  (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).op ⋙ X.presheaf

/-- The presheaf of global functions on the open subscheme underlying each chart. -/
abbrev openSectionsPresheaf : (PolynomialChart Λ X structureMap)ᵒᵖ ⥤ CommRingCat.{u} :=
  (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).op ⋙
    (X.restrictFunctor.op ⋙ (Over.forget X).op ⋙ Scheme.Γ)

/-- Pullback of functions along the arrow `U ⟶ A` of a polynomial chart, landing in the global
functions of the open subscheme. -/
def evaluationToOpenSections :
    affineSectionsPresheaf Λ X structureMap ⟶ openSectionsPresheaf Λ X structureMap where
  app P := Scheme.Γ.map P.unop.toAffine.op
  naturality := by
    intro P Q f
    change Scheme.Γ.map f.unop.affine.op ≫ Scheme.Γ.map Q.unop.toAffine.op =
      Scheme.Γ.map P.unop.toAffine.op ≫
        Scheme.Γ.map (X.homOfLE f.unop.open_le).op
    rw [← Scheme.Γ.map_comp, ← Scheme.Γ.map_comp]
    exact congrArg Scheme.Γ.map (congrArg Quiver.Hom.op f.unop.map_comm)

/-- Pullback of functions along `U ⟶ A`, as a map to the restricted structure sheaf. This is
the map denoted `i♯` in the source, before lifting and sheafification. -/
def evaluationSections :
    affineSectionsPresheaf Λ X structureMap ⟶ zariskiSectionsPresheaf Λ X structureMap :=
  evaluationToOpenSections Λ X structureMap ≫
    Functor.whiskerLeft
      (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).op
      X.restrictFunctorΓ.hom

/-- The presheaf `(U ⟶ A) ↦ Γ(A, 𝒪_A)`, in the coefficient universe. -/
abbrev affinePresheaf :
    (PolynomialChart Λ X structureMap)ᵒᵖ ⥤ CommRingCat.{max w (u + 1)} :=
  affineSectionsPresheaf Λ X structureMap ⋙ liftRing.{u, w}

/-- The presheaf `(U ⟶ A) ↦ 𝒪_X(U)`, in the coefficient universe. -/
abbrev zariskiPresheaf :
    (PolynomialChart Λ X structureMap)ᵒᵖ ⥤ CommRingCat.{max w (u + 1)} :=
  zariskiSectionsPresheaf Λ X structureMap ⋙ liftRing.{u, w}

/-- The map `𝒪 ⟶ π⁻¹𝒪_X` of presheaves in the coefficient universe. -/
def evaluation :
    affinePresheaf.{u, w} Λ X structureMap ⟶ zariskiPresheaf.{u, w} Λ X structureMap :=
  Functor.whiskerRight (evaluationSections Λ X structureMap) liftRing.{u, w}

/-! ### The sheaves of rings -/

/-- The sheaf of rings `𝒪`: the sheafification of the affine-functions presheaf. -/
abbrev affineSheaf : Sheaf (topology Λ X structureMap) CommRingCat.{max w (u + 1)} :=
  (presheafToSheaf (topology Λ X structureMap) CommRingCat.{max w (u + 1)}).obj
    (affinePresheaf.{u, w} Λ X structureMap)

/-- The restriction of `𝒪_X` along the forgetful functor, as a sheaf of rings on the category
of polynomial charts. Its underlying presheaf is `zariskiPresheaf`. -/
abbrev zariskiSheaf : Sheaf (topology Λ X structureMap) CommRingCat.{max w (u + 1)} :=
  ((openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).sheafPushforwardContinuous
    CommRingCat.{max w (u + 1)} (topology Λ X structureMap)
      (Opens.grothendieckTopology X.carrier)).obj (liftedStructureSheaf.{u, w} X)

/-- The presheaf `(U ⟶ A) ↦ 𝒪_X(U)` is a sheaf for the inherited topology: the forgetful
functor is continuous and `𝒪_X` is a sheaf on the Zariski site. -/
theorem zariskiPresheaf_isSheaf :
    Presheaf.IsSheaf (topology Λ X structureMap) (zariskiPresheaf.{u, w} Λ X structureMap) :=
  (zariskiSheaf.{u, w} Λ X structureMap).property

/-- The sheafification of `zariskiPresheaf`. -/
abbrev zariskiPullbackSheaf : Sheaf (topology Λ X structureMap) CommRingCat.{max w (u + 1)} :=
  (presheafToSheaf (topology Λ X structureMap) CommRingCat.{max w (u + 1)}).obj
    (zariskiPresheaf.{u, w} Λ X structureMap)

/-- The constant sheaf of rings `Λ` on the category of polynomial charts. -/
abbrev constantBaseSheaf : Sheaf (topology Λ X structureMap) CommRingCat.{max w (u + 1)} :=
  (presheafToSheaf (topology Λ X structureMap) CommRingCat.{max w (u + 1)}).obj
    ((Functor.const (PolynomialChart Λ X structureMap)ᵒᵖ).obj
      (liftRing.{u, w}.obj (CommRingCat.of Λ)))

/-- `constantBaseSheaf` is the value of the constant-sheaf functor at `Λ`. -/
theorem constantSheaf_obj_eq :
    (constantSheaf (topology Λ X structureMap) CommRingCat.{max w (u + 1)}).obj
        (liftRing.{u, w}.obj (CommRingCat.of Λ)) =
      constantBaseSheaf.{u, w} Λ X structureMap := rfl

/-! ### The comparison isomorphisms -/

/-- `π⁻¹𝒪_X` is the restriction of `𝒪_X` along the forgetful functor: transporting the ring
operations along restriction of sheaves of sets is restriction of sheaves of rings. -/
def restrictionIso :
    chartStructureSheaf.{u, w} Λ X structureMap ≅ zariskiSheaf.{u, w} Λ X structureMap :=
  restrictionCommRingIso (topology Λ X structureMap)
    (Opens.grothendieckTopology X.carrier)
    (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap))
    (liftedStructureSheaf.{u, w} X)

/-- `π⁻¹𝒪_X` is the sheafification of `(U ⟶ A) ↦ 𝒪_X(U)`. -/
def pullbackIso :
    chartStructureSheaf.{u, w} Λ X structureMap ≅ zariskiPullbackSheaf.{u, w} Λ X structureMap :=
  restrictionIso.{u, w} Λ X structureMap ≪≫
    sheafificationIso (zariskiSheaf.{u, w} Λ X structureMap)

/-- On sections over a chart, the comparison `π⁻¹𝒪_X ≅ (zariskiPresheaf)^#` is the
sheafification unit: the first factor is the identity on sections. -/
theorem forget_map_pullbackIso_hom_app (P : PolynomialChart Λ X structureMap) :
    (forget CommRingCat).map
        ((pullbackIso.{u, w} Λ X structureMap).hom.hom.app (Opposite.op P)) =
      (forget CommRingCat).map
        ((toSheafify (topology Λ X structureMap)
          (zariskiPresheaf.{u, w} Λ X structureMap)).app (Opposite.op P)) := rfl

/-- The identity morphism of the topos of sheaves on the category of polynomial charts, the
underlying geometric morphism of `i`. -/
def identityTopos : MorphismOfTopoi
    (Sheaf (topology Λ X structureMap) (Type (max w (u + 1))))
    (Sheaf (topology Λ X structureMap) (Type (max w (u + 1)))) where
  pushforward := 𝟭 _
  inverseImage := 𝟭 _
  adj := Adjunction.id
  preservesFiniteLimits := by infer_instance

/-- `i⁻¹𝒪 = 𝒪`: transporting the ring operations along the identity functor of sheaves of sets
does nothing. -/
def identityRingIso :
    (inverseImageCommRingFunctor (identityTopos.{u, w} Λ X structureMap)).obj
      (affineSheaf.{u, w} Λ X structureMap) ≅ affineSheaf.{u, w} Λ X structureMap :=
  restrictionCommRingIso (topology Λ X structureMap) (topology Λ X structureMap)
    (𝟭 (PolynomialChart Λ X structureMap)) (affineSheaf.{u, w} Λ X structureMap)

/-- On sections over a chart, the comparison `i⁻¹𝒪 ≅ 𝒪` is the identity. -/
theorem forget_map_identityRingIso_hom_app (P : PolynomialChart Λ X structureMap) :
    HEq ((forget CommRingCat).map
        ((identityRingIso.{u, w} Λ X structureMap).hom.hom.app (Opposite.op P)))
      ((forget CommRingCat).map
        (𝟙 (((inverseImageCommRingFunctor (identityTopos.{u, w} Λ X structureMap)).obj
          (affineSheaf.{u, w} Λ X structureMap)).obj.obj (Opposite.op P)))) := HEq.rfl

/-! ### The constant sheaf `Λ` and its structure map -/

/-- The map from the constant presheaf `Λ` to the affine functions, given on a chart by pullback
along the structural arrow `A ⟶ Spec Λ` of its affine space. -/
def baseSectionsMap :
    (Functor.const (PolynomialChart Λ X structureMap)ᵒᵖ).obj (CommRingCat.of Λ) ⟶
      affineSectionsPresheaf Λ X structureMap where
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

/-- The map from the constant presheaf `Λ` to the affine functions, in the coefficient
universe. -/
def basePresheafMap :
    (Functor.const (PolynomialChart Λ X structureMap)ᵒᵖ).obj
        (liftRing.{u, w}.obj (CommRingCat.of Λ)) ⟶ affinePresheaf.{u, w} Λ X structureMap where
  app P := liftRing.{u, w}.map ((baseSectionsMap Λ X structureMap).app P)
  naturality := by
    intro P Q f
    have h := (baseSectionsMap Λ X structureMap).naturality f
    simp only [Functor.const_obj_map] at h
    simp only [Functor.const_obj_map, Functor.comp_map]
    rw [← Functor.map_comp]
    exact congrArg liftRing.{u, w}.map h

/-- The structure map `Λ ⟶ 𝒪` from the constant sheaf. -/
def baseSheafMap :
    constantBaseSheaf.{u, w} Λ X structureMap ⟶ affineSheaf.{u, w} Λ X structureMap :=
  (presheafToSheaf (topology Λ X structureMap) CommRingCat.{max w (u + 1)}).map
    (basePresheafMap.{u, w} Λ X structureMap)

/-- On sections, sheafifying a map of presheaves commutes with the sheafification units. -/
private theorem toSheafify_app_comp_sheafifyMap {P Q : (PolynomialChart Λ X structureMap)ᵒᵖ ⥤
      CommRingCat.{max w (u + 1)}} (η : P ⟶ Q) (T : PolynomialChart Λ X structureMap) :
    (toSheafify (topology Λ X structureMap) P).app (Opposite.op T) ≫
        ((presheafToSheaf (topology Λ X structureMap)
          CommRingCat.{max w (u + 1)}).map η).hom.app (Opposite.op T) =
      η.app (Opposite.op T) ≫ (toSheafify (topology Λ X structureMap) Q).app (Opposite.op T) := by
  have h := congrArg (fun t => t.app (Opposite.op T))
    (toSheafify_naturality (topology Λ X structureMap) η).symm
  simpa only [NatTrans.comp_app] using h

/-- On sections over a chart `U ⟶ A`, the structure map `Λ ⟶ 𝒪` after the sheafification unit
of the constant presheaf is pullback along the structural arrow `A ⟶ Spec Λ` followed by the
sheafification unit. -/
theorem baseSheafMap_canonical (P : PolynomialChart Λ X structureMap) :
    (toSheafify (topology Λ X structureMap)
          ((Functor.const (PolynomialChart Λ X structureMap)ᵒᵖ).obj
            (liftRing.{u, w}.obj (CommRingCat.of Λ)))).app (Opposite.op P) ≫
        (baseSheafMap.{u, w} Λ X structureMap).hom.app (Opposite.op P) =
      liftRing.{u, w}.map ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫
          Scheme.Γ.map P.toBase.op) ≫
        (toSheafify (topology Λ X structureMap)
          (affinePresheaf.{u, w} Λ X structureMap)).app (Opposite.op P) := by
  exact toSheafify_app_comp_sheafifyMap.{u, w} Λ X structureMap
    (basePresheafMap.{u, w} Λ X structureMap) P

/-- On sections over a chart `U ⟶ A`, the map `Λ ⟶ Γ(A, 𝒪_A)` followed by evaluation is
pullback along the structure morphism `U ⟶ Spec Λ`. -/
theorem baseSectionsMap_evaluation (P : PolynomialChart Λ X structureMap) :
    (baseSectionsMap Λ X structureMap).app (Opposite.op P) ≫
        (evaluationSections Λ X structureMap).app (Opposite.op P) =
      (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫
        Scheme.Γ.map (P.openPart.ι ≫ structureMap).op ≫
          (X.restrictFunctorΓ.hom.app (Opposite.op P.openPart)) := by
  have hcomm : P.toAffine ≫ P.toBase = P.openPart.ι ≫ structureMap := P.comm
  have hΓ : Scheme.Γ.map P.toBase.op ≫ Scheme.Γ.map P.toAffine.op =
      Scheme.Γ.map (P.openPart.ι ≫ structureMap).op := by
    rw [← Scheme.Γ.map_comp]
    exact congrArg Scheme.Γ.map (congrArg Quiver.Hom.op hcomm)
  have hbs : (baseSectionsMap Λ X structureMap).app (Opposite.op P) =
      (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ Scheme.Γ.map P.toBase.op := rfl
  have hev : (evaluationSections Λ X structureMap).app (Opposite.op P) =
      Scheme.Γ.map P.toAffine.op ≫
        Scheme.restrictFunctorΓ.hom.app (Opposite.op P.openPart) := rfl
  rw [hbs, hev]
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hΓ)))

/-- The composite `Λ ⟶ 𝒪 ⟶ π⁻¹𝒪_X` is pullback along the structure morphism of the chart's
open subscheme. -/
theorem baseSheafMap_horizontal (P : PolynomialChart Λ X structureMap) :
    (toSheafify (topology Λ X structureMap)
          ((Functor.const (PolynomialChart Λ X structureMap)ᵒᵖ).obj
            (liftRing.{u, w}.obj (CommRingCat.of Λ)))).app (Opposite.op P) ≫
        (baseSheafMap.{u, w} Λ X structureMap).hom.app (Opposite.op P) ≫
        ((presheafToSheaf (topology Λ X structureMap) CommRingCat.{max w (u + 1)}).map
          (evaluation.{u, w} Λ X structureMap)).hom.app (Opposite.op P) =
      liftRing.{u, w}.map ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫
          Scheme.Γ.map (P.openPart.ι ≫ structureMap).op ≫
            (X.restrictFunctorΓ.hom.app (Opposite.op P.openPart))) ≫
        (toSheafify (topology Λ X structureMap)
          (zariskiPresheaf.{u, w} Λ X structureMap)).app (Opposite.op P) := by
  have hsec : liftRing.{u, w}.map ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫
        Scheme.Γ.map P.toBase.op) ≫ (evaluation.{u, w} Λ X structureMap).app (Opposite.op P) =
      liftRing.{u, w}.map ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫
        Scheme.Γ.map (P.openPart.ι ≫ structureMap).op ≫
          (X.restrictFunctorΓ.hom.app (Opposite.op P.openPart))) := by
    exact (Functor.map_comp _ _ _).symm.trans
      (congrArg liftRing.{u, w}.map (baseSectionsMap_evaluation Λ X structureMap P))
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) (baseSheafMap_canonical Λ X structureMap P)).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (toSheafify_app_comp_sheafifyMap Λ X structureMap _ P)).trans <|
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hsec)

/-! ### The horizontal morphism of ringed topoi -/

/-- The inverse-image form of `i♯`: evaluation, read from `𝒪` to `π⁻¹𝒪_X` through the two
comparison isomorphisms. -/
def horizontalMapInverse :
    (inverseImageCommRingFunctor (identityTopos.{u, w} Λ X structureMap)).obj
        (affineSheaf.{u, w} Λ X structureMap) ⟶
      chartStructureSheaf.{u, w} Λ X structureMap :=
  (identityRingIso.{u, w} Λ X structureMap).hom ≫
    (presheafToSheaf (topology Λ X structureMap) CommRingCat.{max w (u + 1)}).map
      (evaluation.{u, w} Λ X structureMap) ≫ (pullbackIso.{u, w} Λ X structureMap).inv

/-- Read through the two comparison isomorphisms, the inverse-image form of `i♯` is the
sheafification of the evaluation map. -/
theorem horizontalMapInverse_cancel :
    (identityRingIso.{u, w} Λ X structureMap).inv ≫
        horizontalMapInverse.{u, w} Λ X structureMap ≫
        (pullbackIso.{u, w} Λ X structureMap).hom =
      (presheafToSheaf (topology Λ X structureMap) CommRingCat.{max w (u + 1)}).map
        (evaluation.{u, w} Λ X structureMap) := by
  simp only [horizontalMapInverse, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The morphism of ringed topoi `i`, whose structure map in inverse-image form is
evaluation. -/
def horizontalHom :
    RingedToposHom
      ⟨PolynomialChart Λ X structureMap, topology Λ X structureMap,
        chartStructureSheaf.{u, w} Λ X structureMap⟩
      ⟨PolynomialChart Λ X structureMap, topology Λ X structureMap,
        affineSheaf.{u, w} Λ X structureMap⟩ where
  toToposHom := identityTopos.{u, w} Λ X structureMap
  fSharp := (commRingImageAdjunction (identityTopos.{u, w} Λ X structureMap)).homEquiv _ _
    (horizontalMapInverse.{u, w} Λ X structureMap)

/-- The structure map of `i` in inverse-image form is `horizontalMapInverse`. -/
theorem horizontalHom_fSharpInverseImage :
    (horizontalHom.{u, w} Λ X structureMap).fSharpInverseImage =
      horizontalMapInverse.{u, w} Λ X structureMap :=
  Equiv.symm_apply_apply
    ((commRingImageAdjunction (identityTopos.{u, w} Λ X structureMap)).homEquiv _ _)
    (horizontalMapInverse.{u, w} Λ X structureMap)

/-! ### The diagram -/

/-- **Stacks 08VA.** The diagram of ringed topoi
`(Sh(C_{X/Λ}), π⁻¹𝒪_X) ⟶ (Sh(C_{X/Λ}), 𝒪)` over `(Sh(X_Zar), 𝒪_X)`, together with the
canonical characterizations of all of its data: the geometric morphisms, the two comparison
isomorphisms and both structure maps. -/
structure PiSchemesDiagram where
  /-- The structure map from the constant sheaf `Λ` to the affine functions. -/
  baseStructureMap :
    constantBaseSheaf.{u, w} Λ X structureMap ⟶ affineSheaf.{u, w} Λ X structureMap
  /-- On a chart, the structure map from `Λ` is pullback along the structural arrow of its
  affine space. -/
  baseStructureMap_canonical : ∀ P : PolynomialChart Λ X structureMap,
    (toSheafify (topology Λ X structureMap)
          ((Functor.const (PolynomialChart Λ X structureMap)ᵒᵖ).obj
            (liftRing.{u, w}.obj (CommRingCat.of Λ)))).app (Opposite.op P) ≫
        baseStructureMap.hom.app (Opposite.op P) =
      liftRing.{u, w}.map ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫
          Scheme.Γ.map P.toBase.op) ≫
        (toSheafify (topology Λ X structureMap)
          (affinePresheaf.{u, w} Λ X structureMap)).app (Opposite.op P)
  /-- The morphism of ringed topoi `π`. -/
  vertical : RingedToposHom
    ⟨PolynomialChart Λ X structureMap, topology Λ X structureMap,
      chartStructureSheaf.{u, w} Λ X structureMap⟩
    ⟨X.Opens, Opens.grothendieckTopology X.carrier, liftedStructureSheaf.{u, w} X⟩
  /-- Its underlying geometric morphism is `π`. -/
  vertical_topos : vertical.toToposHom = projection.{u, w} Λ X structureMap
  /-- Its structure map is the unit of the adjunction `π⁻¹ ⊣ π_*` on sheaves of rings. -/
  vertical_fSharp : HEq vertical.fSharp
    ((commRingImageAdjunction (projection.{u, w} Λ X structureMap)).unit.app
      (liftedStructureSheaf.{u, w} X))
  /-- `π⁻¹𝒪_X` is the sheafification of `(U ⟶ A) ↦ 𝒪_X(U)`. -/
  pullbackIso : chartStructureSheaf.{u, w} Λ X structureMap ≅
    zariskiPullbackSheaf.{u, w} Λ X structureMap
  /-- That presheaf is already a sheaf. -/
  zariskiIsSheaf :
    Presheaf.IsSheaf (topology Λ X structureMap) (zariskiPresheaf.{u, w} Λ X structureMap)
  /-- On sections the comparison is the sheafification unit. -/
  pullbackIso_canonical : ∀ P : PolynomialChart Λ X structureMap,
    HEq ((forget CommRingCat).map (pullbackIso.hom.hom.app (Opposite.op P)))
      ((forget CommRingCat).map
        ((toSheafify (topology Λ X structureMap)
          (zariskiPresheaf.{u, w} Λ X structureMap)).app (Opposite.op P)))
  /-- The morphism of ringed topoi `i`. -/
  horizontal : RingedToposHom
    ⟨PolynomialChart Λ X structureMap, topology Λ X structureMap,
      chartStructureSheaf.{u, w} Λ X structureMap⟩
    ⟨PolynomialChart Λ X structureMap, topology Λ X structureMap,
      affineSheaf.{u, w} Λ X structureMap⟩
  /-- `i` is the identity on underlying topoi. -/
  horizontal_inverseImage : horizontal.toToposHom.inverseImage = 𝟭 _
  /-- `i` is the identity on underlying topoi. -/
  horizontal_pushforward : horizontal.toToposHom.pushforward = 𝟭 _
  /-- Hence `i⁻¹𝒪 = 𝒪`. -/
  horizontalIdentityIso :
    (inverseImageCommRingFunctor horizontal.toToposHom).obj
      (affineSheaf.{u, w} Λ X structureMap) ≅ affineSheaf.{u, w} Λ X structureMap
  /-- And that identification is the identity on sections. -/
  horizontalIdentityIso_canonical : ∀ P : PolynomialChart Λ X structureMap,
    HEq ((forget CommRingCat).map (horizontalIdentityIso.hom.hom.app (Opposite.op P)))
      ((forget CommRingCat).map
        (𝟙 (((inverseImageCommRingFunctor horizontal.toToposHom).obj
          (affineSheaf.{u, w} Λ X structureMap)).obj.obj (Opposite.op P))))
  /-- `i♯`, in inverse-image form, is the sheafification of the evaluation map. -/
  horizontal_fSharp :
    horizontalIdentityIso.inv ≫ horizontal.fSharpInverseImage ≫ pullbackIso.hom =
      (presheafToSheaf (topology Λ X structureMap) CommRingCat.{max w (u + 1)}).map
        (evaluation.{u, w} Λ X structureMap)
  /-- The composite `Λ ⟶ 𝒪 ⟶ π⁻¹𝒪_X` is pullback along the structure morphism of `U`. -/
  baseStructureMap_horizontal : ∀ P : PolynomialChart Λ X structureMap,
    (toSheafify (topology Λ X structureMap)
          ((Functor.const (PolynomialChart Λ X structureMap)ᵒᵖ).obj
            (liftRing.{u, w}.obj (CommRingCat.of Λ)))).app (Opposite.op P) ≫
        baseStructureMap.hom.app (Opposite.op P) ≫
        ((presheafToSheaf (topology Λ X structureMap) CommRingCat.{max w (u + 1)}).map
          (evaluation.{u, w} Λ X structureMap)).hom.app (Opposite.op P) =
      liftRing.{u, w}.map ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫
          Scheme.Γ.map (P.openPart.ι ≫ structureMap).op ≫
            Scheme.restrictFunctorΓ.hom.app (Opposite.op P.openPart)) ≫
        (toSheafify (topology Λ X structureMap)
          (zariskiPresheaf.{u, w} Λ X structureMap)).app (Opposite.op P)

/-- **Stacks 08VA.** The diagram of ringed topoi of the polynomial charts of a scheme over a
ring, with all of its arrows pinned to the canonical ones. -/
@[stacks 08VA]
def piSchemesDiagram : PiSchemesDiagram.{u, w} Λ X structureMap where
  baseStructureMap := baseSheafMap.{u, w} Λ X structureMap
  baseStructureMap_canonical := baseSheafMap_canonical.{u, w} Λ X structureMap
  vertical :=
    { toToposHom := projection.{u, w} Λ X structureMap
      fSharp := (commRingImageAdjunction (projection.{u, w} Λ X structureMap)).unit.app
        (liftedStructureSheaf.{u, w} X) }
  vertical_topos := rfl
  vertical_fSharp := HEq.rfl
  pullbackIso := pullbackIso.{u, w} Λ X structureMap
  zariskiIsSheaf := zariskiPresheaf_isSheaf.{u, w} Λ X structureMap
  pullbackIso_canonical := fun P =>
    heq_of_eq (forget_map_pullbackIso_hom_app.{u, w} Λ X structureMap P)
  horizontal := horizontalHom.{u, w} Λ X structureMap
  horizontal_inverseImage := rfl
  horizontal_pushforward := rfl
  horizontalIdentityIso := identityRingIso.{u, w} Λ X structureMap
  horizontalIdentityIso_canonical := forget_map_identityRingIso_hom_app.{u, w} Λ X structureMap
  horizontal_fSharp := by
    rw [horizontalHom_fSharpInverseImage]
    exact horizontalMapInverse_cancel.{u, w} Λ X structureMap
  baseStructureMap_horizontal := baseSheafMap_horizontal.{u, w} Λ X structureMap

end

end AlgebraicGeometry.PolynomialChart

end
