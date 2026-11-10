module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekLocalCompleteIntersection.FundamentalClass

/-!
# The map `∧^r Ω_{X/Y} ⟶ ω_{X/Y}` of [Stacks, Tag 0E9Z] at constant ranks

Let `S` be a Noetherian scheme and `f : X ⟶ Y` a morphism of `FTS S` which factors as a
Koszul-regular closed immersion `i : X ⟶ U` with conormal sheaf of rank `c`, an open `U ⊆ P` and a
proper morphism `g : P ⟶ Y` smooth of relative dimension `d`. Put `r = d - c`. For every
compactification computing `f^!`, the cohomology sheaf `H^k(f^!𝒪_Y)` has nonzero stalk at `x`
exactly for `k = -r`, and there is a map `∧^r Ω_{X/Y} ⟶ H^{-r}(f^!𝒪_Y)` which is an isomorphism
on the stalk at `x` exactly when `f` is smooth at `x`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe u

attribute [local implicit_reducible] structureSheafRing AlgebraicGeometry.SheafedSpace.sheaf

namespace Stacks.Duality.ClosedOpenProperFactorization

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  {P : Scheme.{u}} (U : P.Opens) (i : X.left ⟶ U.toScheme) (g : P ⟶ Y.left)
  [IsClosedImmersion i] [IsProper g] (hf : i ≫ U.ι ≫ g = f.left)
  (j : CompactificationOf (Over.mk f.left)) (d c : ℕ) [SmoothOfRelativeDimension d g]
  (hi : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsKoszulRegularImmersion i)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    (R := X.left.ringCatSheaf) (Stacks.Conormal.conormalSheaf i) c]

/-- The cohomology sheaf `H^k(f^!𝒪_Y)`. -/
abbrev upperShriekHomology (k : ℤ) : X.left.Modules :=
  (DerivedCategory.homologyFunctor X.left.Modules k).obj
    ((upperShriek f j).obj (DerivedPushforward.derivedStructureSheaf Y.left)).obj

/-- The conormal modules `conormalModules U i` are finite locally free of rank `c`. -/
private theorem isFiniteLocallyFreeOfRank_conormalModules :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := toRingCat (Opens.grothendieckTopology
        ↥X.left.toLocallyRingedSpace.toRingedSpace.carrier)
        X.left.toLocallyRingedSpace.toRingedSpace.sheaf) (conormalModules U i) c := by
  -- (`omit` cannot be used on private declarations here, so the unused instance is touched)
  have := ‹AlgebraicGeometry.IsNoetherian S›
  assumption

/-- An isomorphism of sheaves of modules on a scheme identifies their stalks. -/
def stalkAddEquivOfIso {Z : Scheme.{u}} {M N : Z.Modules} (e : M ≅ N) (x : Z) :
    ↑(M.presheaf.stalk x) ≃+ ↑(N.presheaf.stalk x) :=
  ((Stacks.ConormalSequenceRight.stalkAb Z x).mapIso e).addCommGroupIsoToAddEquiv

include hf hi in
/-- **The cohomology sheaves of `f^!𝒪_Y` at constant ranks**: the stalk of `H^k(f^!𝒪_Y)` at `x`
is nonzero exactly for `k = -(d - c)`. -/
theorem nontrivial_stalk_upperShriekHomology_iff (x : X.left) (k : ℤ) :
    Nontrivial ↑((upperShriekHomology f j k).presheaf.stalk x) ↔ k = -((d : ℤ) - c) := by
  let T := Scheme.Modules.tensorObjRingedSpace X.left
    (Scheme.Modules.exteriorPower (Stacks.Divisors.normalSheaf i) c)
    (pulledBackDeterminant U i g d)
  let eT := upperShriekStructureSheafIso f U i g hf j d c hi
  let e := stalkAddEquivOfIso ((DerivedCategory.homologyFunctor X.left.Modules k).mapIso eT) x
  rw [e.toEquiv.nontrivial_congr]
  by_cases hk : k = (c : ℤ) + -(d : ℤ)
  · subst hk
    refine iff_of_true ?_ (by omega)
    let e' := stalkAddEquivOfIso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.left.Modules
        ((c : ℤ) + -(d : ℤ))).app T) x
    have := isFiniteLocallyFreeOfRank_pullback_relativeDifferentials U i g d
    have := isFiniteLocallyFreeOfRank_conormalModules U i c
    have : Nontrivial ↑(TopCat.Presheaf.stalk
        X.left.toLocallyRingedSpace.toRingedSpace.sheaf.obj x) :=
      (X.left.toLocallyRingedSpace.isLocalRing x).toNontrivial
    have h := nontrivial_stalk_target (X := X.left.toLocallyRingedSpace.toRingedSpace.carrier)
      (_root_.SheafOfModules.ringedSpaceAlgebras X.left.toLocallyRingedSpace.toRingedSpace
        (conormalModules U i))
      (_root_.SheafOfModules.ringedSpaceAlgebras X.left.toLocallyRingedSpace.toRingedSpace
        ((Scheme.Modules.pullback (i ≫ U.ι)).obj (Scheme.Hom.relativeDifferentials g)))
      (_root_.SheafOfModules.ringedSpaceAlgebras X.left.toLocallyRingedSpace.toRingedSpace
        (dualMod (conormalModules U i))) c d x
    have hT : Nontrivial ↑(T.presheaf.stalk x) :=
      @Equiv.nontrivial _ _
        (stalkAddEquivOfIso (tensorExteriorPowerPullbackIso U i g d c) x).symm.toEquiv h
    exact @Equiv.nontrivial _ _ e'.toEquiv hT
  · refine iff_of_false ?_ (by omega)
    have hz : IsZero ((DerivedCategory.homologyFunctor X.left.Modules k).obj
        ((DerivedCategory.singleFunctor X.left.Modules ((c : ℤ) + -(d : ℤ))).obj T)) := by
      rcases lt_or_gt_of_ne hk with h | h
      · exact DerivedCategory.isZero_of_isGE _ ((c : ℤ) + -(d : ℤ)) k h
      · exact DerivedCategory.isZero_of_isLE _ ((c : ℤ) + -(d : ℤ)) k h
    have hs : Subsingleton ↑((Stacks.ConormalSequenceRight.stalkAb X.left x).obj
        ((DerivedCategory.homologyFunctor X.left.Modules k).obj
          ((DerivedCategory.singleFunctor X.left.Modules ((c : ℤ) + -(d : ℤ))).obj T))) :=
      AddCommGrpCat.subsingleton_of_isZero
        (@Functor.map_isZero _ _ _ _ _ _ (Stacks.ConormalSequenceRight.stalkAb X.left x)
          (AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor_preservesZeroMorphisms _ x)
          _ hz)
    exact @not_nontrivial _ hs

omit [AlgebraicGeometry.IsNoetherian S] [IsClosedImmersion i] [IsProper g] in
include hf in
/-- The composite `(i ≫ U.ι) ≫ g` is the morphism `f.left`. -/
theorem comp_eq_left : (i ≫ U.ι) ≫ g = f.left := by rw [Category.assoc]; exact hf

/-- `H^{-(d-c)}(f^!𝒪_Y) ≅ ∧^c 𝒩 ⊗ (i ≫ U.ι)^* ∧^d Ω_{P/Y}`. -/
def upperShriekHomologyIso :
    upperShriekHomology f j (-((d : ℤ) - c)) ≅
      Scheme.Modules.tensorObjRingedSpace X.left
        (Scheme.Modules.exteriorPower (Stacks.Divisors.normalSheaf i) c)
        (pulledBackDeterminant U i g d) :=
  (DerivedCategory.homologyFunctor X.left.Modules (-((d : ℤ) - c))).mapIso
      (upperShriekStructureSheafIso f U i g hf j d c hi) ≪≫
    eqToIso (congrArg (fun k => (DerivedCategory.homologyFunctor X.left.Modules k).obj
      ((DerivedCategory.singleFunctor X.left.Modules ((c : ℤ) + -(d : ℤ))).obj
        (Scheme.Modules.tensorObjRingedSpace X.left
          (Scheme.Modules.exteriorPower (Stacks.Divisors.normalSheaf i) c)
          (pulledBackDeterminant U i g d)))) (by omega)) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso X.left.Modules
      ((c : ℤ) + -(d : ℤ))).app _

/-- **The map `∧^r Ω_{X/Y} ⟶ H^{-r}(f^!𝒪_Y)`, `r = d - c`, of [Stacks, Tag 0E9Z]**: the map of
[Stacks, Tag 0E9Y] for the conormal sequence of `X ⊆ P` followed by the computation of
`f^!𝒪_Y`. -/
def fundamentalClass :
    Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f.left) ((d : ℤ) - c) ⟶
      upperShriekHomology f j (-((d : ℤ) - c)) :=
  haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := toRingCat (Opens.grothendieckTopology
        ↥X.left.toLocallyRingedSpace.toRingedSpace.carrier)
        X.left.toLocallyRingedSpace.toRingedSpace.sheaf) (conormalModules U i) c := ‹_›
  eqToHom (congrArg (fun h => Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials h)
      ((d : ℤ) - c)) (comp_eq_left f U i g hf).symm) ≫
    fundamentalClassMap U i g d c ≫ (upperShriekHomologyIso f U i g hf j d c hi).inv

omit [AlgebraicGeometry.IsNoetherian S] in
/-- A morphism `φ : M ⟶ N` of sheaves of modules on a scheme induces an isomorphism of stalks
at `x` if and only if it induces an isomorphism of the underlying abelian groups of the stalks. -/
theorem isIso_stalkMap_iff_isIso_stalkAb {Z : Scheme.{u}} (x : Z) {M N : Z.Modules}
    (φ : M ⟶ N) :
    IsIso (AlgebraicGeometry.SheafOfModules.stalkMap
        (toRingCat (Opens.grothendieckTopology ↥Z.toLocallyRingedSpace.toRingedSpace.carrier)
          Z.toLocallyRingedSpace.toRingedSpace.sheaf) x φ) ↔
      IsIso ((Stacks.ConormalSequenceRight.stalkAb Z x).map φ) :=
  (ConcreteCategory.isIso_iff_bijective _).trans
    (ConcreteCategory.isIso_iff_bijective ((Stacks.ConormalSequenceRight.stalkAb Z x).map φ)).symm

/-- **The isomorphism locus of the map of [Stacks, Tag 0E9Z] at constant ranks**: its stalk at
`x` is an isomorphism exactly when `f` is smooth at `x`. -/
theorem isIso_stalkMap_fundamentalClass_iff (x : X.left) :
    IsIso (AlgebraicGeometry.SheafOfModules.stalkMap
        (toRingCat (Opens.grothendieckTopology
          ↥X.left.toLocallyRingedSpace.toRingedSpace.carrier)
          X.left.toLocallyRingedSpace.toRingedSpace.sheaf) x
        (fundamentalClass f U i g hf j d c hi)) ↔
      InfinitesimalLifting.SmoothAt f.left x := by
  let F := Stacks.ConormalSequenceRight.stalkAb X.left x
  have := isFiniteLocallyFreeOfRank_conormalModules U i c
  have hsm : InfinitesimalLifting.SmoothAt ((i ≫ U.ι) ≫ g) x ↔
      InfinitesimalLifting.SmoothAt f.left x := by
    rw [comp_eq_left f U i g hf]
  refine (isIso_stalkMap_iff_isIso_stalkAb x _).trans (Iff.trans ?_
    ((isIso_stalkMap_iff_isIso_stalkAb x (fundamentalClassMap U i g d c)).symm.trans
      ((isIso_stalkMap_fundamentalClassMap_iff_smoothAt U i g d c x).trans hsm)))
  change IsIso (F.map (fundamentalClass f U i g hf j d c hi)) ↔
    IsIso (F.map (fundamentalClassMap U i g d c))
  unfold fundamentalClass
  rw [F.map_comp, F.map_comp, isIso_comp_left_iff, isIso_comp_right_iff]

end Stacks.Duality.ClosedOpenProperFactorization
