module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceLevelTower
public import StacksFrontier.AlgebraicGeometry.Perfect.TensorFinitelyPresentedPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparisonBraiding
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.BraidingIsoSymmetry
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackMonoidalFunctor
public import StacksFrontier.AlgebraicGeometry.Perfect.GlobalSectionsTensorFlatProperSupport
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback

/-!
# Base change for the level tower of Grothendieck's existence theorem

In Situation [Stacks, Tag 0CTC], the square

```
Xₙ   --tₙ-->  Xₙ₊₁
|fₙ           |fₙ₊₁
Spec Aₙ  -->  Spec Aₙ₊₁
```

is cartesian
(`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.isPullback_transitionScheme`).
For a perfect `E` on `X`, this file shows that the derived base change map of this square at
`ℱₙ₊₁ ⊗^𝐋 Eₙ₊₁`, followed by `Rfₙ,*` of the comparison
`Ltₙ^*(ℱₙ₊₁ ⊗^𝐋 Eₙ₊₁) ⟶ ℱₙ ⊗^𝐋 Eₙ` of the level tower, is an isomorphism. This is the base-change
half of [Stacks, Tag 0A1H] for the proper flat family `ℱₙ₊₁` over `Spec Aₙ₊₁`, read in the order
`ℱ ⊗ E` of [Stacks, Tag 0CTE] rather than the order `E ⊗ ℱ` of the library's statement of
[Stacks, Tag 0A1H]; the two are exchanged by the commutativity constraint of the derived tensor
product, with which derived pullback is compatible
(`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_braiding`).

## Implementation notes

As for [Stacks, Tag 0A1H] itself, everything here is at
`CategoryTheory.HasDerivedCategory.standard`,
scoped to each declaration, as for the level tower.

## References

* [Stacks Project, Tag 0CTE](https://stacks.math.columbia.edu/tag/0CTE)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex
  derivedPullbackTensorIso)
open Stacks.Cohomology.DerivedBaseChangeComparison (baseChangeTensorComparison)
open Stacks.SheafOfModules.DerivedMonoidal (canonicalBraidingHom)
open scoped CategoryTheory.Prod

universe u

namespace AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

variable (S : ExistenceSituation.{u})

/-- The structure morphism `fₙ : Xₙ ⟶ Spec Aₙ` is of finite presentation, being a base change of
the structure morphism of `X`. -/
theorem finitePresentation_levelStructure (n : ℕ) : FinitePresentation (S.levelStructure n) :=
  have := S.finitePresentation.locallyOfFinitePresentation
  have := S.finitePresentation.quasiCompact
  have := S.finitePresentation.quasiSeparated
  ⟨inferInstance, inferInstance, inferInstance⟩

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The commutativity constraint `M ⊗^𝐋 N ≅ N ⊗^𝐋 M` of the derived tensor product on a ringed
space, as an isomorphism: its inverse is the constraint in the other order. -/
def tensorBraidingIso (Z : RingedSpace.{u, u})
    (M N : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))) :
    ((derivedTensorProductFunctor Z.sheaf).obj M).obj N ≅
      ((derivedTensorProductFunctor Z.sheaf).obj N).obj M where
  hom := canonicalBraidingHom Z.sheaf M N
  inv := canonicalBraidingHom Z.sheaf N M
  hom_inv_id := Stacks.Cohomology.SupportedComplexes.canonicalBraidingHom_symmetry Z M N
  inv_hom_id := Stacks.Cohomology.SupportedComplexes.canonicalBraidingHom_symmetry Z N M

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `ℱₙ₊₁ ⊗^𝐋 Eₙ₊₁ ≅ Eₙ₊₁ ⊗^𝐋 ℱₙ₊₁[0]`, with `ℱₙ₊₁[0]` read as the class of the single complex: the
reordering under which the level objects match the statement of [Stacks, Tag 0A1H]. -/
def levelTensorSheafSwapIso (n : ℕ) (E : DerivedCategory S.X.left.Modules) :
    S.levelTensorSheaf (n + 1) E ≅
      ((derivedTensorProductFunctor (schemeAt S.system S.X (n + 1)).toRingedSpace.sheaf).obj
        ((S.levelPullback (n + 1)).obj E)).obj
          (DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor (schemeAt S.system S.X (n + 1)).Modules 0).obj
              (S.F (n + 1)))) :=
  tensorBraidingIso _ (S.levelSheafStandard (n + 1)) ((S.levelPullback (n + 1)).obj E) ≪≫
    ((derivedTensorProductFunctor (schemeAt S.system S.X (n + 1)).toRingedSpace.sheaf).obj
      ((S.levelPullback (n + 1)).obj E)).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ (schemeAt S.system S.X (n + 1)).Modules 0).app
          (S.F (n + 1)))

end AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

namespace AlgebraicGeometry.GrothendieckExistence

section Generic

-- As in `Stacks.Cohomology.DerivedPullbackTensor`: the ring sheaf of the canonical derived tensor
-- product and the structure sheaf of the derived pullback are the same only once these unfold.
attribute [local implicit_reducible]
  StacksDraft.KFlat.modulePullback CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf
  TopCat.Sheaf TopCat.Presheaf.IsSheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X' X : RingedSpace.{u, u}} (h : X' ⟶ X)

local notation "DX" =>
  DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)
local notation "DX'" =>
  DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X')

/-- Post-composing both sides of `f ≫ g = f' ≫ g'` with `k`, with the composites reassociated. -/
private theorem comp_assoc_eq_of_comp_eq {C : Type*} [Category C] {P Q Q' R S : C}
    {f : P ⟶ Q} {g : Q ⟶ R} {f' : P ⟶ Q'} {g' : Q' ⟶ R} (H : f ≫ g = f' ≫ g') (k : R ⟶ S) :
    f ≫ g ≫ k = f' ≫ g' ≫ k :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ k) H).trans (Category.assoc _ _ _))

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The commutativity constraint of the derived tensor product is natural in the right factor. -/
theorem canonicalBraidingHom_naturality_right (M : DX') {C D : DX'} (b : C ⟶ D) :
    ((derivedTensorProductFunctor X'.sheaf).obj M).map b ≫ canonicalBraidingHom X'.sheaf M D =
      canonicalBraidingHom X'.sheaf M C ≫
        ((derivedTensorProductFunctor X'.sheaf).map b).app M := by
  simpa only [Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_left,
    Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_right] using
    Stacks.Cohomology.DerivedPullbackTensor.canonicalBraidingHom_naturality X' (𝟙 M) b

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The pullback–tensor comparison with the two factors exchanged.** For `h : X' ⟶ X`, objects
`E, A, B` of `D(𝒪_X)`, a map `a : B ⟶ A` and maps `ψ : Lh^*A ⟶ K'`, `φ : Lh^*B ⟶ K'` with
`Lh^*a ≫ ψ = φ`: reading `Lh^*(A ⊗ E)` through `E ⊗ B ⟶ E ⊗ A ≅ A ⊗ E`, the comparison
`Lh^*(A ⊗ E) ⟶ Lh^*A ⊗ Lh^*E ⟶ K' ⊗ Lh^*E` is the base-change comparison
`Lh^*(E ⊗ B) ⟶ Lh^*E ⊗ K'` followed by the commutativity constraint. -/
theorem derivedPullback_map_braiding_comp_derivedPullbackTensorIso
    (E A B : DX) (a : B ⟶ A) (K' : DX')
    (ψ : (derivedPullback h).obj A ⟶ K') (φ : (derivedPullback h).obj B ⟶ K')
    (hφ : (derivedPullback h).map a ≫ ψ = φ) :
    (derivedPullback h).map (((derivedTensorProductFunctor X.sheaf).obj E).map a ≫
        canonicalBraidingHom X.sheaf E A) ≫
      (derivedPullbackTensorIso h).hom.app (A, E) ≫
        ((derivedTensorProductFunctor X'.sheaf).map ψ).app ((derivedPullback h).obj E) =
      baseChangeTensorComparison h E B K' φ ≫
        canonicalBraidingHom X'.sheaf ((derivedPullback h).obj E) K' := by
  let T := derivedTensorProductFunctor X.sheaf
  let T' := derivedTensorProductFunctor X'.sheaf
  let LE := (derivedPullback h).obj E
  have e1 : (derivedPullback h).map ((T.obj E).map a) ≫
      (derivedPullbackTensorIso h).hom.app (E, A) =
      (derivedPullbackTensorIso h).hom.app (E, B) ≫ (T'.obj LE).map ((derivedPullback h).map a) :=
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_hom_app_naturality_right
      h E a).symm
  have e2 : (T'.map ((derivedPullback h).map a)).app LE ≫ (T'.map ψ).app LE =
      (T'.map φ).app LE := by
    rw [← hφ]
    exact (congrArg (fun m => m.app LE) (T'.map_comp ((derivedPullback h).map a) ψ)).symm
  let x1 := (derivedPullback h).map ((T.obj E).map a)
  let x2 := (derivedPullback h).map (canonicalBraidingHom X.sheaf E A)
  let p1 := (derivedPullbackTensorIso h).hom.app (A, E)
  let p2 := (derivedPullbackTensorIso h).hom.app (E, A)
  let p3 := (derivedPullbackTensorIso h).hom.app (E, B)
  let c1 := canonicalBraidingHom X'.sheaf LE ((derivedPullback h).obj A)
  let c2 := canonicalBraidingHom X'.sheaf LE ((derivedPullback h).obj B)
  let c3 := canonicalBraidingHom X'.sheaf LE K'
  let y := (T'.obj LE).map ((derivedPullback h).map a)
  let z := (T'.map ((derivedPullback h).map a)).app LE
  let x := (T'.map ψ).app LE
  let w := (T'.map φ).app LE
  let v := (T'.obj LE).map φ
  have s1 : (derivedPullback h).map ((T.obj E).map a ≫ canonicalBraidingHom X.sheaf E A) ≫
      p1 ≫ x = x1 ≫ x2 ≫ p1 ≫ x := by
    exact (congrArg (· ≫ p1 ≫ x) ((derivedPullback h).map_comp ((T.obj E).map a)
      (canonicalBraidingHom X.sheaf E A))).trans (Category.assoc _ _ _)
  have s2 : x2 ≫ p1 ≫ x = p2 ≫ c1 ≫ x :=
    comp_assoc_eq_of_comp_eq
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_braiding h E A) x
  have s3 : x1 ≫ p2 ≫ c1 ≫ x = p3 ≫ y ≫ c1 ≫ x := comp_assoc_eq_of_comp_eq e1 (c1 ≫ x)
  have s4 : y ≫ c1 ≫ x = c2 ≫ z ≫ x :=
    comp_assoc_eq_of_comp_eq
      (canonicalBraidingHom_naturality_right LE ((derivedPullback h).map a)) x
  have s5 : c2 ≫ w = v ≫ c3 := (canonicalBraidingHom_naturality_right LE φ).symm
  exact s1.trans ((congrArg (x1 ≫ ·) s2).trans (s3.trans ((congrArg (p3 ≫ ·) s4).trans
    ((congrArg (fun m => p3 ≫ c2 ≫ m) e2).trans ((congrArg (p3 ≫ ·) s5).trans
      (Category.assoc _ _ _).symm)))))

end Generic

end AlgebraicGeometry.GrothendieckExistence


namespace AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

variable (S : ExistenceSituation.{u})

attribute [local implicit_reducible]
  StacksDraft.KFlat.modulePullback CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf
  TopCat.Sheaf TopCat.Presheaf.IsSheaf Stacks.SheafOfModules.Tensor.ringSheaf

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `Ltₙ^*Eₙ₊₁ ⊗^𝐋 tₙ^*ℱₙ₊₁ ≅ ℱₙ ⊗^𝐋 Eₙ`: the target of the base change comparison of
[Stacks, Tag 0A1H] at level `n`, read as the level object `ℱₙ ⊗^𝐋 Eₙ`. -/
def levelTensorSheafPullbackComparisonIso (n : ℕ) (E : DerivedCategory S.X.left.Modules) :
    ((derivedTensorProductFunctor (schemeAt S.system S.X n).toRingedSpace.sheaf).obj
        ((derivedPullback (S.transitionScheme n).toLRSHom.toShHom).obj
          ((S.levelPullback (n + 1)).obj E))).obj
        (DerivedCategory.Q.obj ((pullbackComplex (S.transitionScheme n).toLRSHom.toShHom).obj
          ((CochainComplex.singleFunctor (schemeAt S.system S.X (n + 1)).Modules 0).obj
            (S.F (n + 1))))) ≅
      S.levelTensorSheaf n E :=
  ((derivedTensorProductFunctor (schemeAt S.system S.X n).toRingedSpace.sheaf).obj
      ((derivedPullback (S.transitionScheme n).toLRSHom.toShHom).obj
        ((S.levelPullback (n + 1)).obj E))).mapIso (S.levelSheafPullbackComplexIso n) ≪≫
    tensorBraidingIso _
        ((derivedPullback (S.transitionScheme n).toLRSHom.toShHom).obj
          ((S.levelPullback (n + 1)).obj E)) (S.levelSheafStandard n) ≪≫
      ((derivedTensorProductFunctor (schemeAt S.system S.X n).toRingedSpace.sheaf).obj
        (S.levelSheafStandard n)).mapIso (S.levelPullbackTransitionIso n E)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The comparison `Ltₙ^*(ℱₙ₊₁ ⊗^𝐋 Eₙ₊₁) ⟶ ℱₙ ⊗^𝐋 Eₙ` of the level tower, read through the swap
of the two factors, is the base change comparison of [Stacks, Tag 0A1H] followed by
`levelTensorSheafPullbackComparisonIso`. -/
theorem levelTensorSheafSwapIso_inv_comp_levelTensorSheafPullbackMap (n : ℕ)
    (E : DerivedCategory S.X.left.Modules) :
    (derivedPullback (S.transitionScheme n).toLRSHom.toShHom).map
          (S.levelTensorSheafSwapIso n E).inv ≫ S.levelTensorSheafPullbackMap n E =
      baseChangeTensorComparison (S.transitionScheme n).toLRSHom.toShHom
          ((S.levelPullback (n + 1)).obj E)
          (DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor (schemeAt S.system S.X (n + 1)).Modules 0).obj
              (S.F (n + 1))))
          (DerivedCategory.Q.obj ((pullbackComplex (S.transitionScheme n).toLRSHom.toShHom).obj
            ((CochainComplex.singleFunctor (schemeAt S.system S.X (n + 1)).Modules 0).obj
              (S.F (n + 1)))))
          ((derivedPullbackNatTrans (S.transitionScheme n).toLRSHom.toShHom).app
            ((CochainComplex.singleFunctor (schemeAt S.system S.X (n + 1)).Modules 0).obj
              (S.F (n + 1)))) ≫
        (S.levelTensorSheafPullbackComparisonIso n E).hom := by
  let t := (S.transitionScheme n).toLRSHom.toShHom
  let E' := (S.levelPullback (n + 1)).obj E
  let G :=
    (CochainComplex.singleFunctor (schemeAt S.system S.X (n + 1)).Modules 0).obj (S.F (n + 1))
  let sIQ := (DerivedCategory.singleFunctorIsoCompQ (schemeAt S.system S.X (n + 1)).Modules 0).app
    (S.F (n + 1))
  let u := S.levelTensorSheafSwapIso n E
  let φ₀ := (derivedPullbackNatTrans t).app G
  let ψE := S.levelPullbackTransitionIso n E
  let T₀ := derivedTensorProductFunctor (schemeAt S.system S.X n).toRingedSpace.sheaf
  let LE' := (derivedPullback t).obj E'
  let sFn := S.levelSheafStandard n
  let ι := S.levelSheafPullbackComplexIso n
  let W := S.levelTensorSheafPullbackComparisonIso n E
  let bTC₀ := baseChangeTensorComparison t E' (DerivedCategory.Q.obj G)
    (DerivedCategory.Q.obj ((pullbackComplex t).obj G)) φ₀
  let bTC₁ := baseChangeTensorComparison t E' (DerivedCategory.Q.obj G) sFn (φ₀ ≫ ι.hom)
  let PTI := (derivedPullbackTensorIso t).hom.app (S.levelSheafStandard (n + 1), E')
  let Tρ := (T₀.map (S.levelSheafTransition n)).app LE'
  let TψE := (T₀.obj sFn).map ψE.hom
  let cB := canonicalBraidingHom (schemeAt S.system S.X n).toRingedSpace.sheaf LE' sFn
  have hgen := derivedPullback_map_braiding_comp_derivedPullbackTensorIso
    t E' (S.levelSheafStandard (n + 1)) (DerivedCategory.Q.obj G) sIQ.inv (S.levelSheafStandard n)
    (S.levelSheafTransition n) (φ₀ ≫ (S.levelSheafPullbackComplexIso n).hom)
    (((derivedPullback t).mapIso sIQ).inv_hom_id_assoc _)
  have hb : bTC₁ = bTC₀ ≫ (T₀.obj LE').map ι.hom :=
    (congrArg ((derivedPullbackTensorIso t).hom.app (E', DerivedCategory.Q.obj G) ≫ ·)
      ((T₀.obj LE').map_comp φ₀ ι.hom)).trans (Category.assoc _ _ _).symm
  rw [show S.levelTensorSheafPullbackMap n E = PTI ≫ Tρ ≫ TψE from rfl]
  have a1 : (derivedPullback t).map u.inv ≫ PTI ≫ Tρ ≫ TψE =
      ((derivedPullback t).map u.inv ≫ PTI ≫ Tρ) ≫ TψE :=
    (congrArg ((derivedPullback t).map u.inv ≫ ·) (Category.assoc PTI Tρ TψE).symm).trans
      (Category.assoc _ _ _).symm
  have a2 : ((derivedPullback t).map u.inv ≫ PTI ≫ Tρ) ≫ TψE =
      ((bTC₀ ≫ (T₀.obj LE').map ι.hom) ≫ cB) ≫ TψE :=
    congrArg (· ≫ TψE) (hgen.trans (congrArg (· ≫ cB) hb))
  have a3 : ((bTC₀ ≫ (T₀.obj LE').map ι.hom) ≫ cB) ≫ TψE = bTC₀ ≫ W.hom :=
    (Category.assoc _ _ _).trans (Category.assoc _ _ _)
  exact a1.trans (a2.trans a3)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The derived base change map of the cartesian square at `ℱₙ₊₁ ⊗^𝐋 Eₙ₊₁` followed by `Rfₙ,*` of
the comparison of the level tower is, up to the swap of the two factors, the base change map of
[Stacks, Tag 0A1H] followed by `Rfₙ,*` of `levelTensorSheafPullbackComparisonIso`. -/
theorem derivedBaseChangeMap_comp_levelTensorSheafPullbackMap_eq (n : ℕ)
    (E : DerivedCategory S.X.left.Modules) :
    (derivedPullback (baseTransition S.system n).toLRSHom.toShHom).map
          ((derivedPushforward (S.levelStructure (n + 1)).toLRSHom.toShHom).map
            (S.levelTensorSheafSwapIso n E).inv) ≫
        (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap
            (S.transitionScheme n).toLRSHom.toShHom (S.levelStructure n).toLRSHom.toShHom
            (S.levelStructure (n + 1)).toLRSHom.toShHom
            (baseTransition S.system n).toLRSHom.toShHom
            (comp_toShHom_of_comm (S.isPullback_transitionScheme n).w)
            (S.levelTensorSheaf (n + 1) E) ≫
          (derivedPushforward (S.levelStructure n).toLRSHom.toShHom).map
            (S.levelTensorSheafPullbackMap n E)) =
      tensorFlatBaseChangeMap (S.levelStructure (n + 1)) (baseTransition S.system n)
          (S.levelStructure n) (S.transitionScheme n)
          (comp_toShHom_of_comm (S.isPullback_transitionScheme n).w)
          ((S.levelPullback (n + 1)).obj E)
          ((CochainComplex.singleFunctor (schemeAt S.system S.X (n + 1)).Modules 0).obj
            (S.F (n + 1))) ≫
        (derivedPushforward (S.levelStructure n).toLRSHom.toShHom).map
          (S.levelTensorSheafPullbackComparisonIso n E).hom := by
  let t := (S.transitionScheme n).toLRSHom.toShHom
  let f' := (S.levelStructure n).toLRSHom.toShHom
  let f := (S.levelStructure (n + 1)).toLRSHom.toShHom
  let g := (baseTransition S.system n).toLRSHom.toShHom
  let sq := comp_toShHom_of_comm (S.isPullback_transitionScheme n).w
  have key2 := Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_naturality t f' f g sq
    (S.levelTensorSheafSwapIso n E).inv
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) key2).trans ?_)
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (((derivedPushforward f').map_comp _ _).symm.trans
    ((congrArg (derivedPushforward f').map
        (S.levelTensorSheafSwapIso_inv_comp_levelTensorSheafPullbackMap n E)).trans
      ((derivedPushforward f').map_comp _ _)))).trans ?_
  exact (Category.assoc _ _ _).symm

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The base change of the level tower is invertible** ([Stacks, Tag 0A1H] for the proper flat
family `ℱₙ₊₁` over `Spec Aₙ₊₁`). For a perfect `E` on `X`, the derived base change map of the
cartesian square `tₙ ≫ fₙ₊₁ = fₙ ≫ Spec (Aₙ₊₁ ⟶ Aₙ)` at `ℱₙ₊₁ ⊗^𝐋 Eₙ₊₁`, followed by `Rfₙ,*` of
the comparison `Ltₙ^*(ℱₙ₊₁ ⊗^𝐋 Eₙ₊₁) ⟶ ℱₙ ⊗^𝐋 Eₙ` of the level tower, is an isomorphism. -/
theorem isIso_derivedBaseChangeMap_comp_levelTensorSheafPullbackMap (n : ℕ)
    (E : DerivedCategory S.X.left.Modules)
    (hE : RingedSpace.IsPerfect (X := S.X.left.toRingedSpace) E) :
    IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap
        (S.transitionScheme n).toLRSHom.toShHom (S.levelStructure n).toLRSHom.toShHom
        (S.levelStructure (n + 1)).toLRSHom.toShHom (baseTransition S.system n).toLRSHom.toShHom
        (comp_toShHom_of_comm (S.isPullback_transitionScheme n).w) (S.levelTensorSheaf (n + 1) E) ≫
      (derivedPushforward (S.levelStructure n).toLRSHom.toShHom).map
        (S.levelTensorSheafPullbackMap n E)) := by
  let t := (S.transitionScheme n).toLRSHom.toShHom
  let f' := (S.levelStructure n).toLRSHom.toShHom
  let f := (S.levelStructure (n + 1)).toLRSHom.toShHom
  let g := (baseTransition S.system n).toLRSHom.toShHom
  let sq := comp_toShHom_of_comm (S.isPullback_transitionScheme n).w
  let E' := (S.levelPullback (n + 1)).obj E
  let G :=
    (CochainComplex.singleFunctor (schemeAt S.system S.X (n + 1)).Modules 0).obj (S.F (n + 1))
  let u := S.levelTensorSheafSwapIso n E
  let W := S.levelTensorSheafPullbackComparisonIso n E
  have hE' : RingedSpace.IsPerfect (X := (schemeAt S.system S.X (n + 1)).toRingedSpace) E' :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ E hE
  have := S.finitelyPresented (n + 1)
  have hfp := S.finitePresentation_levelStructure (n + 1)
  have : LocallyOfFinitePresentation (S.levelStructure (n + 1)) := hfp.locallyOfFinitePresentation
  have hG : FlatProperSupportFinitelyPresented (S.levelStructure (n + 1)) G :=
    flatProperSupportFinitelyPresented_single_of_properSupport _ (S.F (n + 1)) (S.flat (n + 1))
      (S.properSupport (n + 1))
  have h0 := (isPerfect_derivedPushforward_tensor_and_isIso_tensorFlatBaseChangeMap
    (S.levelStructure (n + 1)) hfp E' hE' G hG).2 (baseTransition S.system n) (S.levelStructure n)
    (S.transitionScheme n) (S.isPullback_transitionScheme n)
  have main : (derivedPullback g).map ((derivedPushforward f).map u.inv) ≫
      (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap t f' f g sq
        (S.levelTensorSheaf (n + 1) E) ≫
        (derivedPushforward f').map (S.levelTensorSheafPullbackMap n E)) =
      tensorFlatBaseChangeMap (S.levelStructure (n + 1)) (baseTransition S.system n)
        (S.levelStructure n) (S.transitionScheme n) sq E' G ≫
        (derivedPushforward f').map W.hom :=
    S.derivedBaseChangeMap_comp_levelTensorSheafPullbackMap_eq n E
  have : IsIso ((derivedPullback g).map ((derivedPushforward f).map u.inv) ≫
      (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap t f' f g sq
        (S.levelTensorSheaf (n + 1) E) ≫
        (derivedPushforward f').map (S.levelTensorSheafPullbackMap n E))) := by
    rw [main]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h0 ((derivedPushforward f').mapIso W).isIso_hom
  have : IsIso ((derivedPushforward f).map u.inv) :=
    Iso.isIso_inv ((derivedPushforward f).mapIso u)
  have : IsIso ((derivedPullback g).map ((derivedPushforward f).map u.inv)) :=
    (derivedPullback g).map_isIso _
  exact IsIso.of_isIso_comp_left ((derivedPullback g).map ((derivedPushforward f).map u.inv)) _

end AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

end
