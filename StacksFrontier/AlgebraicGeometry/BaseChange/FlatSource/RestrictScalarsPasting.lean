module

public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatSource.UnderivedComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangePasting
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ExactPushforwardCounit

/-!
# Base change through an exact pushforward

For two vertically pasted commutative squares of ringed spaces whose upper vertical arrows
have exact pushforward, the derived base change map of the lower square at the pushforward of a
complex, followed by the underived base change map of the upper square, is invertible when the
derived base change map of the outer rectangle is. The file also packages the derived base
change map at complexes as a natural transformation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedBaseChange

universe u

namespace Stacks.AlgebraicGeometry.FlatSourceBaseChange

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable {X' X Y' Y S' S : RingedSpace.{u, u}} (k : X' ⟶ X) (ι' : X' ⟶ Y') (ι : X ⟶ Y)
  (l : Y' ⟶ Y) (π' : Y' ⟶ S') (π : Y ⟶ S) (m : S' ⟶ S) (sqA : k ≫ ι = ι' ≫ l)
  (sqB : l ≫ π = π' ≫ m)

/-- The comparison of the derived pullback along the middle row with the underived one, followed
by the underived base change map of the upper square and the image of a map, before the unit of
the exact pushforward `ι'`: it is the derived base change map of the upper square after the unit
of `ι`, followed by the comparison along `k` and the map. -/
theorem derivedPullbackComparison_comp_underived_comp_unit
    (U : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (U' : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X')) (ComplexShape.up ℤ))
    (χ : ((modulePullback k).mapHomotopyCategory (ComplexShape.up ℤ)).obj U ⟶ U') :
    (derivedPullbackComparison l).app (((modulePushforward ι).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj U) ≫
      DerivedCategory.Qh.map ((underivedBaseChangeSquare k ι' ι l sqA).app U ≫
        ((modulePushforward ι').mapHomotopyCategory (ComplexShape.up ℤ)).map χ) ≫
      (derivedPushforwardUnit ι').app U' =
    (derivedPullback l).map ((derivedPushforwardUnit ι).app U) ≫
      derivedBaseChangeMap k ι' ι l sqA (DerivedCategory.Qh.obj U) ≫
      (derivedPushforward ι').map
        ((derivedPullbackComparison k).app U ≫ DerivedCategory.Qh.map χ) := by
  have hnat := (derivedPushforwardUnit ι').naturality χ
  have hQh := derivedBaseChangeMap_Qh_comparison k ι' ι l sqA U
  rw [Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_map, pushforwardToDerivedCategory] at hnat
  rw [hnat, Functor.map_comp]
  simpa only [Category.assoc] using
    (hQh =≫ (derivedPushforward ι').map (DerivedCategory.Qh.map χ)).symm

/-- The diagram chase behind `isIso_derivedBaseChangeMap_comp_of_exact_pushforward`, with every
derived functor and map abstracted. -/
theorem isIso_comp_map_of_pasting {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (G : 𝒞 ⥤ 𝒟)
    {P P₁ P₂ T T' : 𝒟} {A A' B Q Q' : 𝒞} (b₁ : P ⟶ G.obj A) (Z : A ⟶ Q) (u' : Q ⟶ Q')
    (llu : A ⟶ A') (bca : A' ⟶ B) (ry : B ⟶ Q') (e₁ : Z ≫ u' = llu ≫ bca ≫ ry)
    (m₁ : P ⟶ P₁) (b₂ : P₁ ⟶ G.obj A') (nB : m₁ ≫ b₂ = b₁ ≫ G.map llu) (m₂ : P₁ ⟶ P₂)
    (m₂' : P₂ ⟶ P₁) (hm : m₂ ≫ m₂' = 𝟙 _) (c₁ : G.obj B ⟶ T) (bcr : P₂ ⟶ T)
    (hcomp : m₂' ≫ b₂ ≫ G.map bca ≫ c₁ = bcr) (c₂ : G.obj Q' ⟶ T') (r'' : T ⟶ T')
    (hnatC : G.map ry ≫ c₂ = c₁ ≫ r'') [IsIso m₁] [IsIso m₂] [IsIso (G.map u' ≫ c₂)]
    (h : IsIso (bcr ≫ r'')) : IsIso (b₁ ≫ G.map Z) := by
  have key : (b₁ ≫ G.map Z) ≫ G.map u' ≫ c₂ = m₁ ≫ m₂ ≫ bcr ≫ r'' := by
    rw [← hcomp, Category.assoc, ← G.map_comp_assoc, e₁, G.map_comp, G.map_comp]
    simp only [Category.assoc]
    rw [← reassoc_of% nB, hnatC, reassoc_of% hm]
  have : IsIso ((b₁ ≫ G.map Z) ≫ G.map u' ≫ c₂) := by
    rw [key]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (G.map u' ≫ c₂)

/-- **The base change comparison on complexes**: at a complex `E` on `Y`, the derived base change
map of the square `(l, π', π, m)` at `E`, followed by the comparison of the derived pullback of
`E` along `l` with its termwise pullback. It is natural in the complex. -/
def derivedBaseChangeComplexTrans :
    HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⋙ derivedPushforward π ⋙
        derivedPullback m ⟶
      (modulePullback l).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⋙
          derivedPushforward π') where
  app E := derivedBaseChangeMap l π' π m sqB
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj E)) ≫
    (derivedPushforward π').map ((derivedPullbackComparison l).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj E))
  naturality E₁ E₂ u := by
    have h₁ := derivedBaseChangeMap_naturality l π' π m sqB
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map u))
    have h₂ := (derivedPullbackComparison l).naturality
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map u)
    dsimp only [Functor.comp_map, Functor.comp_obj] at h₂ ⊢
    rw [reassoc_of% h₁]
    exact (congrArg (derivedBaseChangeMap l π' π m sqB _ ≫ ·)
      ((((derivedPushforward π').map_comp _ _).symm.trans
        (congrArg (derivedPushforward π').map h₂)).trans
          ((derivedPushforward π').map_comp _ _))).trans (Category.assoc _ _ _).symm

/-- The components of the base change comparison on complexes. -/
theorem derivedBaseChangeComplexTrans_app
    (E : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) :
    (derivedBaseChangeComplexTrans l π' π m sqB).app E =
      derivedBaseChangeMap l π' π m sqB
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj E)) ≫
      (derivedPushforward π').map ((derivedPullbackComparison l).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj E)) :=
  rfl

variable [PreservesFiniteColimits (modulePushforward ι)]
  [PreservesFiniteColimits (modulePushforward ι')]

/-- **Base change through exact pushforwards.** Consider two vertically pasted commutative squares
of ringed spaces

```
X' --k--> X
|ι'       |ι
Y' --l--> Y
|π'       |π
S' --m--> S
```

with `ι_*` and `ι'_*` exact. For a complex `U` on `X` and a map `χ : k^*U ⟶ U'`, if the derived
base change map of the outer rectangle at `U` followed by the comparison along `k` and `χ` is
invertible, then so is the derived base change map of the lower square at `ι_*U` followed by
the comparison along `l`, the underived base change map of the upper square and `ι'_*χ`. -/
theorem isIso_derivedBaseChangeMap_comp_of_exact_pushforward
    (U : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (U' : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X')) (ComplexShape.up ℤ))
    (χ : ((modulePullback k).mapHomotopyCategory (ComplexShape.up ℤ)).obj U ⟶ U')
    (h : IsIso (derivedBaseChangeMap k (ι' ≫ π') (ι ≫ π) m (comp_square k ι' ι l π' π m sqA sqB)
        (DerivedCategory.Qh.obj U) ≫ (derivedPushforward (ι' ≫ π')).map
          ((derivedPullbackComparison k).app U ≫ DerivedCategory.Qh.map χ))) :
    IsIso (derivedBaseChangeMap l π' π m sqB
        (DerivedCategory.Qh.obj (((modulePushforward ι).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj U)) ≫
      (derivedPushforward π').map ((derivedPullbackComparison l).app
          (((modulePushforward ι).mapHomotopyCategory (ComplexShape.up ℤ)).obj U) ≫
        DerivedCategory.Qh.map ((underivedBaseChangeSquare k ι' ι l sqA).app U ≫
          ((modulePushforward ι').mapHomotopyCategory (ComplexShape.up ℤ)).map χ))) := by
  have hcomp := derivedBaseChangeMap_comp k ι' ι l π' π m sqA sqB (DerivedCategory.Qh.obj U)
  have hm : (derivedPullback m).map ((derivedPushforwardCompIso ι π).hom.app
        (DerivedCategory.Qh.obj U)) ≫ (derivedPullback m).map
        ((derivedPushforwardCompIso ι π).inv.app (DerivedCategory.Qh.obj U)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    exact (derivedPullback m).map_id _
  exact isIso_comp_map_of_pasting (derivedPushforward π') _ _ _ _ _ _
    (((Category.assoc _ _ _).trans
      (derivedPullbackComparison_comp_underived_comp_unit k ι' ι l sqA U U' χ))) _ _
    (derivedBaseChangeMap_naturality l π' π m sqB ((derivedPushforwardUnit ι).app U)) _ _ hm
    _ _ hcomp _ _ ((derivedPushforwardCompIso ι' π').hom.naturality
      ((derivedPullbackComparison k).app U ≫ DerivedCategory.Qh.map χ)) h

/-- The derived base change map is unchanged when the vertical arrows of the square are replaced
by equal ones, also when it is followed by the image of a map under the derived pushforward. -/
theorem isIso_derivedBaseChangeMap_comp_map_congr {f₁ f₂ : X ⟶ S} {f₁' f₂' : X' ⟶ S'}
    (e : f₁ = f₂) (e' : f₁' = f₂') (sq₁ : k ≫ f₁ = f₁' ≫ m) (sq₂ : k ≫ f₂ = f₂' ≫ m)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    {B : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    (x : (derivedPullback k).obj K ⟶ B)
    (h : IsIso (derivedBaseChangeMap k f₂' f₂ m sq₂ K ≫ (derivedPushforward f₂').map x)) :
    IsIso (derivedBaseChangeMap k f₁' f₁ m sq₁ K ≫ (derivedPushforward f₁').map x) := by
  subst e e'
  exact h

/-- `isIso_derivedBaseChangeMap_comp_of_exact_pushforward` for complexes and a map of complexes:
the underived base change map of the upper square is applied termwise. -/
theorem isIso_derivedBaseChangeMap_comp_of_exact_pushforward_complex
    (W : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (W' : CochainComplex (SheafOfModules.{u} (structureSheafRing X')) ℤ)
    (χ : ((modulePullback k).mapHomologicalComplex (ComplexShape.up ℤ)).obj W ⟶ W')
    (h : IsIso (derivedBaseChangeMap k (ι' ≫ π') (ι ≫ π) m (comp_square k ι' ι l π' π m sqA sqB)
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj W)) ≫
      (derivedPushforward (ι' ≫ π')).map ((derivedPullbackComparison k).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj W) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map χ)))) :
    IsIso (derivedBaseChangeMap l π' π m sqB
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((modulePushforward ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj W))) ≫
      (derivedPushforward π').map ((derivedPullbackComparison l).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (((modulePushforward ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj W)) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (moduleBaseChangeSquare k ι' ι l sqA)
            (ComplexShape.up ℤ)).app W ≫
            ((modulePushforward ι').mapHomologicalComplex (ComplexShape.up ℤ)).map χ)))) := by
  have hq : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (moduleBaseChangeSquare k ι' ι l sqA)
          (ComplexShape.up ℤ)).app W ≫
          ((modulePushforward ι').mapHomologicalComplex (ComplexShape.up ℤ)).map χ) =
      (underivedBaseChangeSquare k ι' ι l sqA).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj W) ≫
        ((modulePushforward ι').mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map χ) := by
    rw [underivedBaseChangeSquare_app_quotient]
    exact (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_comp _ _
  have key := isIso_derivedBaseChangeMap_comp_of_exact_pushforward k ι' ι l π' π m sqA sqB
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj W)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj W')
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map χ) h
  rwa [← hq] at key

end

end Stacks.AlgebraicGeometry.FlatSourceBaseChange
