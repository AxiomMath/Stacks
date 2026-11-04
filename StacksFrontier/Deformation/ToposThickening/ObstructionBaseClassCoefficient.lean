module

public import StacksFrontier.Deformation.ToposThickening.CanonicalCotangentObstruction

/-!
# The class `γ` of a square-zero extension problem under a change of target module

Let `S` be a square-zero extension problem of ringed topoi (Tag 08UF): a morphism `f`, a first
order thickening of the base, a target module `G` and a map `c : f⁻¹J ⟶ G`. Given a map of
`O`-modules `k : G ⟶ G'`, the problem `S.mapTarget k` has the same base data, target `G'`, and
prescribed map `c ≫ k`.

The class `γ : L_{f⁻¹O_B/f⁻¹O_{B'}} ⊗ O ⟶ G[1]` of `c` (`obstructionBaseClass`) is natural in
this change: `γ(S.mapTarget k) = γ(S) ≫ k[1]`. Consequently the class of a solution of
`S.mapTarget k`, restricted along the first map of the fundamental triangle, is `γ(S)` pushed into
`G'`.

## Main definitions

* `Deformation.ToposThickening.RingedToposExtensionProblem.mapTarget`: the problem with target
  changed along `k`.

## Main results

* `DerivedCategory.negOneHomologyMap_comp_single_map`: the map on `H^{-1}` is natural in the
  target.
* `DerivedCategory.negOneHomologySingleIso_hom_naturality`: so is the automorphism
  `negOneHomologySingleIso`, for a natural identification `G[-1] ≅ G[0][1]`.
* `CotangentObstruction.baseExtEquiv_comp_single_map`: `baseExtEquiv` is natural in the target.
* `RingedToposExtensionProblem.obstructionBaseClass_mapTarget`: `γ(S.mapTarget k) = γ(S) ≫ k[1]`.
* `RingedToposExtensionProblem.towerCotangentBaseChange_comp_solutionCotangentClass_mapTarget`:
  the class of a solution of `S.mapTarget k`, restricted along the first map of the fundamental
  triangle, is `γ(S) ≫ k[1]`.

## References

* [Stacks Project, Tag 08V5](https://stacks.math.columbia.edu/tag/08V5)
* [Stacks Project, Tag 07YY](https://stacks.math.columbia.edu/tag/07YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t u v' u' w'

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- **The map on `H^{-1}` is natural in the target.** -/
public theorem negOneHomologyMap_comp_single_map (M : CochainComplex C ℤ) {G G' : C} (k : G ⟶ G')
    (e : Q.obj M ⟶ ((singleFunctor C 0).obj G)⟦(1 : ℤ)⟧) :
    negOneHomologyMap M G' (e ≫ ((singleFunctor C 0).map k)⟦(1 : ℤ)⟧') =
      negOneHomologyMap M G e ≫ k := by
  have h2 : ((homologyFunctor C 0).shift (0 : ℤ)).map ((singleFunctor C 0).map k) ≫
      ((singleFunctorCompHomologyFunctorIso C 0).app G').hom =
        ((singleFunctorCompHomologyFunctorIso C 0).app G).hom ≫ k :=
    (singleFunctorCompHomologyFunctorIso C 0).hom.naturality k
  simp only [negOneHomologyMap, Functor.shiftMap_comp]
  exact (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h2))).trans
    ((congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm)

/-- **The automorphism `negOneHomologySingleIso` is natural in `G`**, for identifications
`G[-1] ≅ G[0][1]` that are natural in `G`. -/
public theorem negOneHomologySingleIso_hom_naturality {G G' : C} (k : G ⟶ G')
    (e₀ : Q.obj ((HomologicalComplex.single C (ComplexShape.up ℤ) (-1)).obj G) ⟶
      ((singleFunctor C 0).obj G)⟦(1 : ℤ)⟧) [IsIso e₀]
    (e₀' : Q.obj ((HomologicalComplex.single C (ComplexShape.up ℤ) (-1)).obj G') ⟶
      ((singleFunctor C 0).obj G')⟦(1 : ℤ)⟧) [IsIso e₀']
    (hnat : Q.map ((HomologicalComplex.single C (ComplexShape.up ℤ) (-1)).map k) ≫ e₀' =
      e₀ ≫ ((singleFunctor C 0).map k)⟦(1 : ℤ)⟧') :
    (negOneHomologySingleIso G e₀).hom ≫ k = k ≫ (negOneHomologySingleIso G' e₀').hom := by
  simp only [negOneHomologySingleIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  rw [← negOneHomologyMap_comp_single_map, ← hnat, negOneHomologyMap_Q_map_comp,
    ← HomologicalComplex.singleObjHomologySelfIso_inv_naturality_assoc]

end DerivedCategory

namespace Deformation.ToposThickening

namespace CotangentObstruction

open CategoryTheory.Sheaf

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective CommRingCat.{u}]
  {A' A O : Sheaf J CommRingCat.{u}} (g : A' ⟶ A) (h : A ⟶ O)
  [Presheaf.IsLocallySurjective J g.hom]
  [HasDerivedCategory.{t} (targetModules.{u, u, u} J O)]

/-- **`baseExtEquiv` is natural in the target.** -/
public theorem baseExtEquiv_comp_single_map {G G' : targetModules.{u, u, u} J O} (k : G ⟶ G')
    (x : DerivedCategory.Q.obj (baseChangedComplex.{u, u, u} J g h) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj G)⟦(1 : ℤ)⟧) :
    baseExtEquiv.{u, u, u} J g h G' (x ≫ ((DerivedCategory.singleFunctor _ 0).map k)⟦(1 : ℤ)⟧') =
      baseExtEquiv.{u, u, u} J g h G x ≫ (squareRestrict.{u, u, u} J h).map k := by
  show (cotangentComplexHomologyNegOneIsoConormal.{u, u, u} J g).inv ≫
      (towerExtendRestrictAdjunction.{u, u, u} J h).homEquiv _ _
        ((extendScalarsCotangentHomologyNegOneIso.{u, u, u} J g h).inv ≫
          DerivedCategory.negOneHomologyMap _ G'
            (x ≫ ((DerivedCategory.singleFunctor _ 0).map k)⟦(1 : ℤ)⟧') ≫ 𝟙 _) ≫ 𝟙 _ =
    ((cotangentComplexHomologyNegOneIsoConormal.{u, u, u} J g).inv ≫
      (towerExtendRestrictAdjunction.{u, u, u} J h).homEquiv _ _
        ((extendScalarsCotangentHomologyNegOneIso.{u, u, u} J g h).inv ≫
          DerivedCategory.negOneHomologyMap _ G x ≫ 𝟙 _) ≫ 𝟙 _) ≫
      (squareRestrict.{u, u, u} J h).map k
  simp only [DerivedCategory.negOneHomologyMap_comp_single_map, Category.comp_id,
    Category.assoc, ← Adjunction.homEquiv_naturality_right]
  congr 2

/-- The inverse of `baseExtEquiv` is natural in the target. -/
public theorem baseExtEquiv_symm_comp {G G' : targetModules.{u, u, u} J O} (k : G ⟶ G')
    (y : Stacks.Sites.Conormal.conormalSheaf.{u, u, max u u u, u} J A' A g ⟶
      (squareRestrict.{u, u, u} J h).obj G) :
    (baseExtEquiv.{u, u, u} J g h G').symm (y ≫ (squareRestrict.{u, u, u} J h).map k) =
      (baseExtEquiv.{u, u, u} J g h G).symm y ≫
        ((DerivedCategory.singleFunctor _ 0).map k)⟦(1 : ℤ)⟧' := by
  rw [Equiv.symm_apply_eq, baseExtEquiv_comp_single_map, Equiv.apply_symm_apply]

/-- `towerBaseClass` is natural in the target. -/
public theorem towerBaseClass_comp {G G' : targetModules.{u, u, u} J O} (k : G ⟶ G')
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (y : Stacks.Sites.Conormal.conormalSheaf.{u, u, max u u u, u} J A' A g ⟶
      (squareRestrict.{u, u, u} J h).obj G) :
    towerBaseClass G' g h (y ≫ (squareRestrict.{u, u, u} J h).map k) =
      towerBaseClass G g h y ≫ ((DerivedCategory.singleFunctor _ 0).map k)⟦(1 : ℤ)⟧' := by
  rw [towerBaseClass, towerBaseClass, baseExtEquiv_symm_comp, Category.assoc]

end CotangentObstruction

namespace RingedToposExtensionProblem

open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sites.Conormal

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (S : RingedToposExtensionProblem X B)

/-- **The problem with its target changed along `k : G ⟶ G'`**: the same base data, target `G'`,
and prescribed map `c ≫ k`. -/
public def mapTarget {G' : SheafOfModules.{u}
      ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj X.O)} (k : S.G ⟶ G') :
    RingedToposExtensionProblem X B :=
  { S with
    G := G'
    c := S.c ≫ (SheafOfModules.restrictScalars
      ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).map S.f.fSharpInverseImage)).map k }

variable {G' : SheafOfModules.{u}
  ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj X.O)} (k : S.G ⟶ G')

/-- On the kernel of `f⁻¹O_{B'} ⟶ f⁻¹O_B`, the prescribed map of `S.mapTarget k` is that of `S`
followed by `k`. -/
public theorem baseIdealRestriction_mapTarget_app (U : X.Cᵒᵖ)
    (x : kernelIdeal S.baseReductionInverseImage.hom U) :
    (S.mapTarget k).baseIdealRestriction.app U x = k.val.app U (S.baseIdealRestriction.app U x) :=
  rfl

variable [HasWeakSheafify X.J CommRingCat.{u}] [X.J.WEqualsLocallyBijective CommRingCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{t} (Sheaf.targetModules.{u, u, u} X.J X.O)]

omit [HasWeakSheafify X.J CommRingCat.{u}] [X.J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- The automorphism of the single-shift identification commutes with `k`. -/
public theorem singleShiftAutomorphism_mapTarget :
    (singleShiftAutomorphism S).hom ≫ k = k ≫ (singleShiftAutomorphism (S.mapTarget k)).hom := by
  let k' : targetG.{u, u, u} S ⟶ targetG.{u, u, u} (S.mapTarget k) := k
  have hnat := ((DerivedCategory.singleFunctors (Sheaf.targetModules.{u, u, u} X.J X.O)).shiftIso
    (1 : ℤ) (-1) 0 (by decide)).inv.naturality k'
  exact DerivedCategory.negOneHomologySingleIso_hom_naturality k' _ _ hnat

omit [HasWeakSheafify X.J CommRingCat.{u}] [X.J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- **The conormal map of `c` is natural in the target**:
`baseConormalMap (S.mapTarget k) = baseConormalMap S ≫ k`. -/
public theorem baseConormalMap_mapTarget :
    (S.mapTarget k).baseConormalMap =
      S.baseConormalMap ≫ (Sheaf.squareRestrict.{u, u, u} X.J S.f.fSharpInverseImage).map k := by
  refine conormal_hom_ext S.baseReductionInverseImage _ fun U x => ?_
  have h₁ := conormalDesc_toAssociatedModule S.baseReductionInverseImage _
    (S.mapTarget k).baseIdealRestriction U x
  have h₂ := conormalDesc_toAssociatedModule S.baseReductionInverseImage _
    S.baseIdealRestriction U x
  have h₃ := congrArg (fun m => m.val.app U (S.baseIdealRestriction.app U x))
    (singleShiftAutomorphism_mapTarget S k)
  refine (congrArg (((Sheaf.squareRestrict.{u, u, u} X.J S.f.fSharpInverseImage).map
      (singleShiftAutomorphism (S.mapTarget k)).hom).val.app U) h₁).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => ((Sheaf.squareRestrict.{u, u, u} X.J
    S.f.fSharpInverseImage).map k).val.app U (((Sheaf.squareRestrict.{u, u, u} X.J
      S.f.fSharpInverseImage).map (singleShiftAutomorphism S).hom).val.app U t)) h₂).symm
  exact h₃.symm

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The class `γ` is natural in the target**: `γ(S.mapTarget k) = γ(S) ≫ k[1]`. -/
public theorem obstructionBaseClass_mapTarget :
    (S.mapTarget k).obstructionBaseClass =
      S.obstructionBaseClass ≫ ((DerivedCategory.singleFunctor _ 0).map k)⟦(1 : ℤ)⟧' := by
  rw [obstructionBaseClass, obstructionBaseClass, baseConormalMap_mapTarget]
  exact CotangentObstruction.towerBaseClass_comp _ _ k _

/-- The class of a solution of `S.mapTarget k`, restricted along the first map of the fundamental
triangle of `f⁻¹O_{B'} ⟶ f⁻¹O_B ⟶ O`, is the class `γ` of `S` pushed into `G'`. -/
public theorem towerCotangentBaseChange_comp_solutionCotangentClass_mapTarget
    [X.J.HasSheafCompose (forget CommRingCat.{u})]
    [(forget CommRingCat.{u}).ReflectsIsomorphisms]
    (P : (S.mapTarget k).CompatibleFirstOrderThickening) :
    DerivedCategory.Q.map (Sheaf.towerCotangentBaseChange.{u, u, u} X.J
        S.baseReductionInverseImage S.f.fSharpInverseImage) ≫
          (S.mapTarget k).solutionCotangentClass P =
      S.obstructionBaseClass ≫ ((DerivedCategory.singleFunctor _ 0).map k)⟦(1 : ℤ)⟧' :=
  ((S.mapTarget k).towerCotangentBaseChange_comp_solutionCotangentClass P).trans
    (S.obstructionBaseClass_mapTarget k)

end RingedToposExtensionProblem

end Deformation.ToposThickening

end
