module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.InverseImageComparison
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesCompare
public import StacksFrontier.Cotangent.SheavesOfRings.BaseChangedCotangentDerived
public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangleGeneral
public import StacksFrontier.Cotangent.SheavesOfRings.PullbackCotangentComplex
public import StacksFrontier.Cotangent.SheavesOfRings.RingedToposTransitivityTriangle
public import StacksFrontier.Cotangent.SheavesOfRings.SquareFunctoriality
import StacksCore.Tactic.StacksAttribute

/-!
# The transitivity triangle of the cotangent complex for morphisms of ringed topoi (Tag 08V1)

Let `f : (Sh(C₁), 𝒪₁) ⟶ (Sh(C₂), 𝒪₂)` and `g : (Sh(C₂), 𝒪₂) ⟶ (Sh(C₃), 𝒪₃)` be morphisms of
ringed topoi. This file proves Tag 08V1: there is a canonical distinguished triangle

`Lf^* L_g ⟶ L_{g ∘ f} ⟶ L_f ⟶ (Lf^* L_g)[1]`

in `D(𝒪₁)`. The proof is the source's: set `h = g ∘ f`, identify `h⁻¹𝒪₃` with `f⁻¹g⁻¹𝒪₃`, and
run the fundamental triangle of Tag 08SZ for the tower `f⁻¹g⁻¹𝒪₃ ⟶ f⁻¹𝒪₂ ⟶ 𝒪₁` on the site of
the source. Its three vertices are `L_{f⁻¹𝒪₂/f⁻¹g⁻¹𝒪₃} ⊗_{f⁻¹𝒪₂} 𝒪₁`, `L_{𝒪₁/f⁻¹g⁻¹𝒪₃}` and
`L_{𝒪₁/f⁻¹𝒪₂} = L_f`. The second is `L_{g ∘ f}` across `h⁻¹𝒪₃ = f⁻¹g⁻¹𝒪₃`, and the first is
`Lf^* L_g`: by Tag 08SV the inverse image of `L_g` is `L_{f⁻¹𝒪₂/f⁻¹g⁻¹𝒪₃}`, and `L_g` is a
bounded above complex of flat modules, so its derived pullback is computed degreewise
(Tag 06YY).

## Main definitions

The tower, `AlgebraicGeometry.RingedToposHom.towerBaseMap`, and its middle vertex
`AlgebraicGeometry.RingedToposHom.compositeCotangentComplex` are those of
`StacksFrontier/Cotangent/SheavesOfRings/RingedToposTransitivityTriangle.lean`.

* `SheafOfModules.restrictScalarsIdIso`: restriction of scalars along the identity is the
  identity.
* `AlgebraicGeometry.RingedToposHom.derivedPullback` is the derived pullback `Lf^*` of
  Tag 06YY.
* `AlgebraicGeometry.RingedToposHom.derivedPullbackCotangentComplexIso`: `Lf^* L_g` is the first
  vertex of the fundamental triangle of the tower.
* `AlgebraicGeometry.RingedToposHom.compCotangentComplexIso`: `L_{g ∘ f}` is its middle vertex.
* `AlgebraicGeometry.RingedToposHom.transitivityUnit` and
  `AlgebraicGeometry.RingedToposHom.transitivityCounit`: the two canonical arrows
  `Lf^* L_g ⟶ L_{g ∘ f} ⟶ L_f`.

## Main results

* `AlgebraicGeometry.RingedToposHom.exists_distTriang_tower`: the fundamental triangle of the
  tower (Tag 08SZ).
* `AlgebraicGeometry.RingedToposHom.comp_fSharpInverseImage_eq_tower`: the source's
  `h⁻¹𝒪₃ = f⁻¹g⁻¹𝒪₃`.
* `AlgebraicGeometry.RingedToposHom.exists_distTriang_transitivity`: **Tag 08V1**.

## Implementation notes

The derived categories are the standard models `HasDerivedCategory.standard`, the models the
derived pullback of Tag 06YY is stated for.

The fundamental triangle and the identification of its first vertex hold with the three sites in
independent universes. For the identification of the middle vertex with `L_{g ∘ f}` the three
structure sheaves have to live in one universe of sections, and
`CategoryTheory.Sheaf.cotangentComplex` asks that universe to contain the universes of the
site; so in Tag 08V1 itself the sites of the source and the middle topos share their universes.

## References

* [Stacks Project, Tag 08V1](https://stacks.math.columbia.edu/tag/08V1), the triangle.
* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ), the fundamental
  triangle of a tower of sheaves of rings.
* [Stacks Project, Tag 08SV](https://stacks.math.columbia.edu/tag/08SV), the inverse image of
  the cotangent complex.
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY), the derived pullback.
* [Stacks Project, Tag 08SU](https://stacks.math.columbia.edu/tag/08SU), the cotangent complex
  of a morphism of ringed topoi.
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ), extension of scalars
  for sheaves of modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Sheaves.RingedToposModules (extendScalars extendRestrictScalarsAdjunction)

universe v u w v' u' w' v'' u'' w'' t

namespace SheafOfModules

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **Restriction of scalars along the identity is the identity**: a sheaf of `R`-modules read
over `R` along `𝟙 R` is isomorphic to itself, by the identity on sections. -/
noncomputable def restrictScalarsIdIso (α : R ⟶ R) (hα : α = 𝟙 R) (M : SheafOfModules.{v} R) :
    (SheafOfModules.restrictScalars α).obj M ≅ M := by
  subst hα
  exact (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun X => ModuleCat.restrictScalarsId'App _ rfl (M.val.obj X))
      (fun _ _ _ => by ext; rfl))

/-- `restrictScalarsIdIso` on complexes. -/
noncomputable def restrictScalarsIdComplexIso (α : R ⟶ R) (hα : α = 𝟙 R)
    (K : CochainComplex (SheafOfModules.{v} R) ℤ) :
    ((SheafOfModules.restrictScalars α).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun i => restrictScalarsIdIso α hα (K.X i))
    (fun i j _ => by subst hα; ext; rfl)

end SheafOfModules

namespace AlgebraicGeometry.RingedToposHom

/-! ## The middle vertex is `L_{g ∘ f}` -/

section CompositeVertex

open Stacks.Sheaves.ToposPushforward (inverseImageCommRingComp)

variable {X Y : RingedTopos.{v, u, max u v w}} {Z : RingedTopos.{v'', u'', max u v w}}
  [X.J.HasSheafCompose (forget RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget RingCat.{max u v w})]
  [Z.J.HasSheafCompose (forget RingCat.{max u v w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [X.J.HasSheafCompose (forget CommRingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget CommRingCat.{max u v w})]
  [Z.J.HasSheafCompose (forget CommRingCat.{max u v w})]
  (F : RingedToposHom Y Z) (G : RingedToposHom X Y)

/-- **The source's `h⁻¹𝒪₃ = f⁻¹g⁻¹𝒪₃`.** The structure map of the composite `g ∘ f` is the
identification of `(g ∘ f)⁻¹𝒪₃` with `f⁻¹g⁻¹𝒪₃`, followed by the structure map
`f⁻¹g⁻¹𝒪₃ ⟶ 𝒪₁` of the tower. -/
theorem comp_fSharpInverseImage_eq_tower :
    (F.comp G).fSharpInverseImage ≫ 𝟙 X.O =
      (inverseImageCommRingComp F.toToposHom G.toToposHom).inv.app Z.O ≫
        (towerBaseMap F G ≫ G.fSharpInverseImage) :=
  (Category.comp_id _).trans (X.forgetRing.map_injective
    ((comp_fSharpInverseImage_forget F G).trans (forget_map_compFSharpInverseImage F G).symm))

/-- **The middle vertex of Tag 08V1.** The cotangent complex `L_{g ∘ f}` of the composite is the
cotangent complex `L_{𝒪₁/f⁻¹g⁻¹𝒪₃}` of the tower, across the identification
`(g ∘ f)⁻¹𝒪₃ = f⁻¹g⁻¹𝒪₃`. -/
def compCotangentComplexIso :
    (F.comp G).cotangentComplex ≅ compositeCotangentComplex F G :=
  @Sheaf.squareCotangentComplexIso.{u, v, w} X.C X.category X.J _ _ _ _ _ _ _ _
    (comp_fSharpInverseImage_eq_tower F G)
    (inferInstance : IsIso ((inverseImageCommRingComp F.toToposHom G.toToposHom).app Z.O).inv)
    inferInstance ≪≫
    SheafOfModules.restrictScalarsIdComplexIso _ (CategoryTheory.Functor.map_id _ _) _

end CompositeVertex

/-! ## The triangle -/

section Triangle

variable {X : RingedTopos.{v, u, max u v w}} {Y : RingedTopos.{v', u', max u' v' w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget RingCat.{max u' v' w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{max u' v' w'} RingCat.{max u' v' w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasSheafify Y.J AddCommGrpCat.{max u' v' w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max u' v' w'}]
  (F : RingedToposHom Y Z) (G : RingedToposHom X Y)

attribute [local instance 10000] HasDerivedCategory.standard


/-- Replacing the first vertex of a distinguished triangle by an isomorphic object, with the
first and third morphisms conjugated accordingly, gives a distinguished triangle. -/
private lemma distinguished_of_iso_obj₁ {E : Type*} [Category E] [Preadditive E]
    [HasZeroObject E] [HasShift E ℤ] [∀ n : ℤ, (CategoryTheory.shiftFunctor E n).Additive]
    [Pretriangulated E] (T : Triangle E) (hT : T ∈ distTriang E) {P : E} (e : P ≅ T.obj₁) :
    Triangle.mk (e.hom ≫ T.mor₁) T.mor₂ (T.mor₃ ≫ e.inv⟦(1 : ℤ)⟧') ∈ distTriang E :=
  isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp [← Functor.map_comp]))

/-- Replacing the second vertex of a distinguished triangle by an isomorphic object, with the
first two morphisms conjugated accordingly, gives a distinguished triangle. -/
private lemma distinguished_of_iso_obj₂ {E : Type*} [Category E] [Preadditive E]
    [HasZeroObject E] [HasShift E ℤ] [∀ n : ℤ, (CategoryTheory.shiftFunctor E n).Additive]
    [Pretriangulated E] (T : Triangle E) (hT : T ∈ distTriang E) {P : E} (e : T.obj₂ ≅ P) :
    Triangle.mk (T.mor₁ ≫ e.hom) (e.inv ≫ T.mor₂) T.mor₃ ∈ distTriang E :=
  isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _)
    (by simp) (by simp) (by simp))

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify Y.J AddCommGrpCat.{max u' v' w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max u' v' w'}] in
/-- **The fundamental triangle of the tower `f⁻¹g⁻¹𝒪₃ ⟶ f⁻¹𝒪₂ ⟶ 𝒪₁`** (Tag 08SZ): its first two
arrows are the canonical maps `L_{f⁻¹𝒪₂/f⁻¹g⁻¹𝒪₃} ⊗_{f⁻¹𝒪₂} 𝒪₁ ⟶ L_{𝒪₁/f⁻¹g⁻¹𝒪₃} ⟶ L_f`. -/
theorem exists_distTriang_tower :
    ∃ δ : G.cotangentComplexDerived ⟶ (DerivedCategory.Q.obj
        (Sheaf.baseChangedCotangentComplex.{u, v, w} X.J (towerBaseMap F G)
          G.fSharpInverseImage))⟦(1 : ℤ)⟧,
      Triangle.mk (DerivedCategory.Q.map (Sheaf.towerCotangentBaseChange.{u, v, w} X.J
          (towerBaseMap F G) G.fSharpInverseImage))
        (DerivedCategory.Q.map (Sheaf.towerCotangentChangeOfBase.{u, v, w} X.J
          (towerBaseMap F G) G.fSharpInverseImage)) δ ∈
        distTriang (DerivedCategory (Sheaf.targetModules.{u, v, w} X.J X.O)) :=
  Sheaf.exists_distTriang_towerCotangent X.J (towerBaseMap F G) G.fSharpInverseImage

section DerivedPullback

variable [Y.J.HasSheafCompose (forget AddCommGrpCat.{max u' v' w'})]
  [HasSheafify X.J (Type (max u v w))] [HasSheafify Y.J (Type (max u' v' w'))]

/-- The derived pullback along `f` exists (Tag 06YY). -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy :
    (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackOnHomotopy G).HasLeftDerivedFunctor
      (Stacks.Cohomology.DerivedPullbackOfToposHom.quasiIsoTarget (Y := Y)) :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy G

/-- The derived pullback `Lf^* : D(𝒪₂) ⥤ D(𝒪₁)` of Tag 06YY. -/
abbrev derivedPullback :
    DerivedCategory (Sheaf.targetModules.{u', v', w'} Y.J Y.O) ⥤
      DerivedCategory (Sheaf.targetModules.{u, v, w} X.J X.O) :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback G

/-- The degreewise pullback `f^*L_g` is the first vertex `L_{f⁻¹𝒪₂/f⁻¹g⁻¹𝒪₃} ⊗_{f⁻¹𝒪₂} 𝒪₁` of the
fundamental triangle of the tower. -/
def degreewisePullbackCotangentComplexIso :
    ((G.toModulesHom.pullbackModules).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        F.cotangentComplex ≅
      Sheaf.baseChangedCotangentComplex.{u, v, w} X.J (towerBaseMap F G) G.fSharpInverseImage :=
  (NatIso.mapHomologicalComplex (eqToIso (congrArg (·.pullbackModules)
      (toModulesHom_eq_toRingedToposModulesHom G))) (ComplexShape.up ℤ)).app _ ≪≫
    Sheaf.pullbackModulesCotangentComplexIso.{u, v, w, u', v', w'} G F.fSharpInverseImage

/-- The degreewise pullback `f^* L_g` is the first vertex
`L_{f⁻¹𝒪₂/f⁻¹g⁻¹𝒪₃} ⊗_{f⁻¹𝒪₂} 𝒪₁` of the fundamental triangle of the tower: `L_g` is a bounded
above complex of flat modules, so `Lf^*` is computed on it degreewise (Tag 06YY), and the
degreewise pullback of `L_g` is that first vertex by Tag 08SV. -/
def derivedPullbackCotangentComplexIso :
    (derivedPullback G).obj F.cotangentComplexDerived ≅
      DerivedCategory.Q.obj
        (Sheaf.baseChangedCotangentComplex.{u, v, w} X.J (towerBaseMap F G) G.fSharpInverseImage) :=
  haveI : IsIso ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison G).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj F.cotangentComplex)) :=
    Stacks.Cohomology.DerivedPullbackOfToposHom.isIso_derivedPullbackComparison_app G
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat (Y := Y))
    (fun N ↦ by
      obtain ⟨K, hK, t, ht⟩ :=
        Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat (Y := Y) N
      exact ⟨K, hK, t, ht⟩)
    (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackInvertsQuasiIso_isKFlat G)
    _ (Sheaf.isKFlat_cotangentComplex' Y.J F.fSharpInverseImage)
  (derivedPullback G).mapIso ((DerivedCategory.quotientCompQhIso _).app _).symm ≪≫
    asIso ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison G).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj F.cotangentComplex)) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    DerivedCategory.Q.mapIso (degreewisePullbackCotangentComplexIso F G)

/-- **Stacks 08V1, with the middle vertex over `f⁻¹g⁻¹𝒪₃`.** The triangle
`Lf^* L_g ⟶ L_{𝒪₁/f⁻¹g⁻¹𝒪₃} ⟶ L_f ⟶ Lf^* L_g[1]` on the two canonical arrows of Tag 08SZ is
distinguished in `D(𝒪₁)`: it is the fundamental triangle of the tower `f⁻¹g⁻¹𝒪₃ ⟶ f⁻¹𝒪₂ ⟶ 𝒪₁`
read through `derivedPullbackCotangentComplexIso`. -/
theorem exists_distTriang_derivedPullback_tower :
    ∃ δ : G.cotangentComplexDerived ⟶ ((derivedPullback G).obj F.cotangentComplexDerived)⟦(1 : ℤ)⟧,
      Triangle.mk ((derivedPullbackCotangentComplexIso F G).hom ≫
          DerivedCategory.Q.map (Sheaf.towerCotangentBaseChange.{u, v, w} X.J
            (towerBaseMap F G) G.fSharpInverseImage))
        (DerivedCategory.Q.map (Sheaf.towerCotangentChangeOfBase.{u, v, w} X.J
          (towerBaseMap F G) G.fSharpInverseImage)) δ ∈
        distTriang (DerivedCategory (Sheaf.targetModules.{u, v, w} X.J X.O)) := by
  obtain ⟨δ, hT⟩ := exists_distTriang_tower F G
  exact ⟨_, distinguished_of_iso_obj₁ _ hT (derivedPullbackCotangentComplexIso F G)⟩

end DerivedPullback

end Triangle

/-! ## Tag 08V1 -/

section Transitivity

variable {X Y : RingedTopos.{v, u, max u v w}} {Z : RingedTopos.{v'', u'', max u v w}}
  [X.J.HasSheafCompose (forget RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget RingCat.{max u v w})]
  [Z.J.HasSheafCompose (forget RingCat.{max u v w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [X.J.HasSheafCompose (forget CommRingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget CommRingCat.{max u v w})]
  [Z.J.HasSheafCompose (forget CommRingCat.{max u v w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasSheafify Y.J AddCommGrpCat.{max u v w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasSheafify X.J (Type (max u v w))] [HasSheafify Y.J (Type (max u v w))]
  (F : RingedToposHom Y Z) (G : RingedToposHom X Y)

attribute [local instance 10000] HasDerivedCategory.standard

/-- The first arrow `Lf^* L_g ⟶ L_{g ∘ f}` of the transitivity triangle: the first arrow of the
fundamental triangle of the tower `f⁻¹g⁻¹𝒪₃ ⟶ f⁻¹𝒪₂ ⟶ 𝒪₁` (Tag 08SZ), read through
`Lf^* L_g ≅ L_{f⁻¹𝒪₂/f⁻¹g⁻¹𝒪₃} ⊗_{f⁻¹𝒪₂} 𝒪₁` and `L_{𝒪₁/f⁻¹g⁻¹𝒪₃} ≅ L_{g ∘ f}`. -/
noncomputable def transitivityUnit :
    (derivedPullback G).obj F.cotangentComplexDerived ⟶ (F.comp G).cotangentComplexDerived :=
  ((derivedPullbackCotangentComplexIso F G).hom ≫
    DerivedCategory.Q.map (Sheaf.towerCotangentBaseChange.{u, v, w} X.J (towerBaseMap F G)
      G.fSharpInverseImage)) ≫
    DerivedCategory.Q.map (compCotangentComplexIso F G).inv

/-- The second arrow `L_{g ∘ f} ⟶ L_f` of the transitivity triangle: the change-of-base-ring arrow
of the fundamental triangle of the tower (Tag 08SZ), read through `L_{g ∘ f} ≅ L_{𝒪₁/f⁻¹g⁻¹𝒪₃}`. -/
noncomputable def transitivityCounit :
    (F.comp G).cotangentComplexDerived ⟶ G.cotangentComplexDerived :=
  DerivedCategory.Q.map (compCotangentComplexIso F G).hom ≫
    DerivedCategory.Q.map (Sheaf.towerCotangentChangeOfBase.{u, v, w} X.J (towerBaseMap F G)
      G.fSharpInverseImage)

/-- **Stacks 08V1.** Let `f : (Sh(C₁), 𝒪₁) ⟶ (Sh(C₂), 𝒪₂)` and `g : (Sh(C₂), 𝒪₂) ⟶ (Sh(C₃), 𝒪₃)`
be morphisms of ringed topoi. The canonical triangle

`Lf^* L_g ⟶ L_{g ∘ f} ⟶ L_f ⟶ Lf^* L_g[1]`

is distinguished in `D(𝒪₁)`. Its first two arrows are `transitivityUnit` and
`transitivityCounit`, those of the fundamental triangle of the tower
`(g ∘ f)⁻¹𝒪₃ = f⁻¹g⁻¹𝒪₃ ⟶ f⁻¹𝒪₂ ⟶ 𝒪₁` of Tag 08SZ; its first vertex is the derived pullback of
`L_g`, which `L_g` being a bounded above complex of flat modules computes degreewise as
`L_{f⁻¹𝒪₂/f⁻¹g⁻¹𝒪₃} ⊗_{f⁻¹𝒪₂} 𝒪₁` (Tags 06YY and 08SV). -/
@[stacks 08V1]
theorem exists_distTriang_transitivity :
    ∃ δ : G.cotangentComplexDerived ⟶ ((derivedPullback G).obj F.cotangentComplexDerived)⟦(1 : ℤ)⟧,
      Triangle.mk (transitivityUnit F G) (transitivityCounit F G) δ ∈
        distTriang (DerivedCategory (Sheaf.targetModules.{u, v, w} X.J X.O)) := by
  obtain ⟨δ, hT⟩ := exists_distTriang_derivedPullback_tower F G
  refine ⟨δ, ?_⟩
  have h := distinguished_of_iso_obj₂ _ hT
    (DerivedCategory.Q.mapIso (compCotangentComplexIso F G)).symm
  exact h

end Transitivity

end AlgebraicGeometry.RingedToposHom

end
