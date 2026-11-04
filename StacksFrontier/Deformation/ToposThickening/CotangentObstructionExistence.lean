module

public import StacksFrontier.AlgebraicGeometry.Duality.KoszulHighDegreeOrthogonality
public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangleGeneral
public import StacksFrontier.Deformation.SquareZero.ExtBaseChange
public import StacksFrontier.Deformation.ToposThickening.CotangentObstructionFibre
public import StacksFrontier.Deformation.ToposThickening.CotangentObstructionRestriction
public import StacksFrontier.Deformation.ToposThickening.SolutionPairObstruction

/-!
# The obstruction class in `Ext²` of the cotangent complex

Let `g : A' ⟶ A` be a locally surjective homomorphism of sheaves of commutative rings with kernel
`I`, let `h : A ⟶ O` be a further homomorphism and `G` a sheaf of `O`-modules. An `A`-linear map
`c : I/I² ⟶ G` is a map `L_{A/A'} ⊗_A O ⟶ G[1]` in the derived category, and the connecting
morphism `δ : L_{O/A} ⟶ (L_{A/A'} ⊗_A O)[1]` of the fundamental triangle of `A' ⟶ A ⟶ O`
(Tag 08SZ) carries it to a class in `Hom(L_{O/A}, G[2])`. This file shows that the class vanishes
exactly when `c` is the restriction of a class of `Ext¹_O(NL_{O/A'}, G)`, and deduces part (1) of
Tag 08V5.

## Main definitions

* `Deformation.ToposThickening.CotangentObstruction.towerBaseClass`: the map
  `L_{A/A'} ⊗_A O ⟶ G[1]` attached to `c`.
* `Deformation.ToposThickening.RingedToposExtensionProblem.obstructionClass`: the obstruction
  class in `Ext²_O(L_f, G)` of a square-zero extension problem of ringed topoi.

## Main results

* `Deformation.ToposThickening.CotangentObstruction.exists_Q_map_canonicalNaiveComparison_comp_eq`:
  every map `L_{O/A'} ⟶ G[1]` factors through the canonical map `L ⟶ NL` of Tag 08US.
* `Deformation.ToposThickening.CotangentObstruction.comp_shift_towerBaseClass_eq_zero_iff`: the
  class `δ ≫ c[1]` vanishes exactly when `c` comes from `Ext¹_O(NL_{O/A'}, G)`.
* `Deformation.ToposThickening.RingedToposExtensionProblem.nonempty_iff_obstructionClass_eq_zero`:
  **Stacks 08V5 (1)**, a solution exists if and only if the obstruction class vanishes.

## References

* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
* [Stacks Project, Tag 08US](https://stacks.math.columbia.edu/tag/08US)
* [Stacks Project, Tag 08V5](https://stacks.math.columbia.edu/tag/08V5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal Stacks.SheafOfModules

universe t u v' u' w'

namespace Deformation.ToposThickening.CotangentObstruction

open CategoryTheory.Sheaf

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective CommRingCat.{u}]
  {A' A O : Sheaf J CommRingCat.{u}}
  [HasDerivedCategory.{t} (targetModules.{u, u, u} J O)] (G : targetModules.{u, u, u} J O)

omit [J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- **Maps `L_{O/A'} ⟶ G[1]` factor through `NL_{O/A'}`.** The canonical map `L ⟶ NL` of Tag 08US
is an isomorphism on cohomology in degrees `≥ -1`, so it is an isomorphism after `τ_{≥ -1}`, and
maps into `G[1]` only see that truncation. -/
theorem exists_Q_map_canonicalNaiveComparison_comp_eq (f : A' ⟶ O)
    (d : DerivedCategory.Q.obj (cotangentComplex.{u, u, u} J f) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj G)⟦(1 : ℤ)⟧) :
    ∃ ζ : DerivedCategory.Q.obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, max u u u, u} J A' O f) ⟶
          ((DerivedCategory.singleFunctor _ 0).obj G)⟦(1 : ℤ)⟧,
      DerivedCategory.Q.map (canonicalNaiveComparison.{u, u, u} J f) ≫ ζ = d := by
  let t := DerivedCategory.TStructure.t (C := targetModules.{u, u, u} J O)
  have : t.IsGE (((DerivedCategory.singleFunctor _ 0).obj G)⟦(1 : ℤ)⟧) (-1) :=
    t.isGE_shift _ 0 1 (-1) (by decide)
  have : IsIso ((t.truncGE (-1)).map
      (DerivedCategory.Q.map (canonicalNaiveComparison.{u, u, u} J f))) := by
    rw [Stacks.DerivedTruncation.isIso_truncGE_map_iff_forall_isIso_homologyMap]
    intro i hi
    refine (NatIso.isIso_map_iff
      (DerivedCategory.homologyFunctorFactors (targetModules.{u, u, u} J O) i) _).2 ?_
    exact canonicalNaiveComparison_isIso_homologyMap J f i hi
  obtain ⟨d', hd'⟩ := (Stacks.Deformation.truncGEHomAddEquiv t (-1) _ _).surjective d
  refine ⟨(t.truncGEπ (-1)).app _ ≫ inv ((t.truncGE (-1)).map
    (DerivedCategory.Q.map (canonicalNaiveComparison.{u, u, u} J f))) ≫ d', ?_⟩
  rw [← Category.assoc, ← t.truncGEπ_naturality, Category.assoc, IsIso.hom_inv_id_assoc]
  exact hd'

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (g : A' ⟶ A) (h : A ⟶ O) [Presheaf.IsLocallySurjective J g.hom]

/-- **The map `L_{A/A'} ⊗_A O ⟶ G[1]` attached to an `A`-linear map `c : I/I² ⟶ G`**, on the first
vertex of the fundamental triangle of `A' ⟶ A ⟶ O`: the inverse of `baseExtEquiv`. -/
noncomputable def towerBaseClass
    (c : conormalSheaf.{u, u, max u u u, u} J A' A g ⟶ (squareRestrict.{u, u, u} J h).obj G) :
    DerivedCategory.Q.obj (baseChangedCotangentComplex.{u, u, u} J g h) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj G)⟦(1 : ℤ)⟧ :=
  DerivedCategory.Q.map (towerExtendScalarsCotangentComplexIso.{u, u, u} J g h).inv ≫
    (baseExtEquiv.{u, u, u} J g h G).symm c

/-- **The class `δ ≫ c[1]` vanishes exactly when `c` comes from `Ext¹_O(NL_{O/A'}, G)`.** For the
connecting morphism `δ` of the fundamental triangle of `A' ⟶ A ⟶ O`, the composite of `δ` with the
shift of the map attached to `c` vanishes if and only if `c` is the map attached to the
composite of the first morphism of the triangle, the canonical map `L ⟶ NL` and a map
`NL_{O/A'} ⟶ G[1]`. This is the exactness of `Hom(-, G[1])` along the triangle. -/
theorem comp_shift_towerBaseClass_eq_zero_iff
    (δ : cotangentComplexDerived.{u, u, u, t} J h ⟶
      (DerivedCategory.Q.obj (baseChangedCotangentComplex.{u, u, u} J g h))⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (DerivedCategory.Q.map (towerCotangentBaseChange.{u, u, u} J g h))
        (DerivedCategory.Q.map (towerCotangentChangeOfBase.{u, u, u} J g h)) δ ∈
      distTriang (DerivedCategory (targetModules.{u, u, u} J O)))
    (c : conormalSheaf.{u, u, max u u u, u} J A' A g ⟶ (squareRestrict.{u, u, u} J h).obj G) :
    δ ≫ (towerBaseClass G g h c)⟦(1 : ℤ)⟧' = 0 ↔
      ∃ d : DerivedCategory.Q.obj (cotangentComplex.{u, u, u} J (g ≫ h)) ⟶
          ((DerivedCategory.singleFunctor _ 0).obj G)⟦(1 : ℤ)⟧,
        baseExtEquiv.{u, u, u} J g h G
          (DerivedCategory.Q.map (towerExtendScalarsCotangentComplexIso.{u, u, u} J g h).hom ≫
            DerivedCategory.Q.map (towerCotangentBaseChange.{u, u, u} J g h) ≫ d) = c := by
  have hc : (baseExtEquiv.{u, u, u} J g h G).symm c =
      DerivedCategory.Q.map (towerExtendScalarsCotangentComplexIso.{u, u, u} J g h).hom ≫
        towerBaseClass G g h c := by
    rw [towerBaseClass, ← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  constructor
  · intro h0
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₃ _ (rot_of_distTriang _ hT)
      ((towerBaseClass G g h c)⟦(1 : ℤ)⟧') h0
    refine ⟨(shiftFunctor _ (1 : ℤ)).preimage (-k), ?_⟩
    have hd : DerivedCategory.Q.map (towerCotangentBaseChange.{u, u, u} J g h) ≫
        (shiftFunctor _ (1 : ℤ)).preimage (-k) = towerBaseClass G g h c := by
      refine (shiftFunctor _ (1 : ℤ)).map_injective ?_
      refine (CategoryTheory.Functor.map_comp _ _ _).trans ((congrArg (_ ≫ ·)
        (CategoryTheory.Functor.map_preimage _ (-k))).trans ?_)
      rw [hk]
      exact (Preadditive.comp_neg _ _).trans (Preadditive.neg_comp _ _).symm
    rw [hd, ← hc, Equiv.apply_symm_apply]
  · rintro ⟨d, hd⟩
    have hb : towerBaseClass G g h c =
        DerivedCategory.Q.map (towerCotangentBaseChange.{u, u, u} J g h) ≫ d := by
      rw [← hd, towerBaseClass, Equiv.symm_apply_apply, ← Category.assoc,
        ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
        Category.id_comp]
    rw [hb, CategoryTheory.Functor.map_comp, ← Category.assoc]
    have h3 := comp_distTriang_mor_zero₃₁ _ hT
    simp only [Triangle.mk_mor₃, Triangle.mk_mor₁] at h3
    rw [h3, zero_comp]

end Deformation.ToposThickening.CotangentObstruction

namespace Deformation.ToposThickening.RingedToposExtensionProblem

open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (S : RingedToposExtensionProblem X B)

/-- The inverse image `f⁻¹O_{B'} ⟶ f⁻¹O_B` of the base reduction is locally surjective. -/
instance isLocallySurjective_baseReductionInverseImage :
    Presheaf.IsLocallySurjective X.J S.baseReductionInverseImage.hom :=
  Stacks.Sheaves.ToposPushforward.isLocallySurjective_inverseImageCommRingFunctor_map
    S.f.toToposHom S.baseReduction S.baseLocallySurjective

/-- The chosen preimage in `f⁻¹J` of a section of the kernel of `f⁻¹O_{B'} ⟶ f⁻¹O_B`. -/
noncomputable abbrev kernelPreimage {U : X.Cᵒᵖ}
    (x : kernelIdeal S.baseReductionInverseImage.hom U) :
    S.I.val.obj U :=
  idealPreimage S x.1 x.2

/-- The chosen preimage maps to the given section of the kernel. -/
theorem idealInclusion_kernelPreimage {U : X.Cᵒᵖ}
    (x : kernelIdeal S.baseReductionInverseImage.hom U) :
    (show S.thickenedBaseInverseImage.obj.obj U from
      S.idealInclusion.val.app U (S.kernelPreimage x)) = x.1 :=
  idealInclusion_idealPreimage S x.1 x.2

/-- The chosen preimage is the only section of `f⁻¹J` mapping to the given section. -/
theorem kernelPreimage_eq {U : X.Cᵒᵖ} (x : kernelIdeal S.baseReductionInverseImage.hom U)
    (a : S.I.val.obj U)
    (ha : (show S.thickenedBaseInverseImage.obj.obj U from S.idealInclusion.val.app U a) = x.1) :
    S.kernelPreimage x = a :=
  (S.idealUniversal U x.1 x.2).unique (S.idealInclusion_kernelPreimage x) ha

/-- **The prescribed map `c : f⁻¹J ⟶ G`, read on the kernel of `f⁻¹O_{B'} ⟶ f⁻¹O_B`**: a
section of the kernel is the image of a unique section of `f⁻¹J`, which `c` sends to `G`. -/
noncomputable def baseIdealRestriction :
    IdealRestriction S.baseReductionInverseImage
      ((Sheaf.squareRestrict.{u, u, u} X.J S.f.fSharpInverseImage).obj S.G) where
  app U :=
    { toFun := fun x => S.c.val.app U (S.kernelPreimage x)
      map_zero' := by
        rw [S.kernelPreimage_eq 0 0 (map_zero _)]
        exact map_zero _
      map_add' := fun x y => by
        rw [S.kernelPreimage_eq (x + y) (S.kernelPreimage x + S.kernelPreimage y)
          ((map_add _ _ _).trans (congrArg₂ (· + ·) (S.idealInclusion_kernelPreimage x)
            (S.idealInclusion_kernelPreimage y)))]
        exact map_add _ _ _ }
  app_smul U r x := by
    change S.c.val.app U (S.kernelPreimage (r • x)) = _
    have hs : (show S.thickenedBaseInverseImage.obj.obj U from S.idealInclusion.val.app U
        (show ((SheafOfModules.restrictScalars ((sheafCompose X.J
          (forget₂ CommRingCat.{u} RingCat.{u})).map S.baseReductionInverseImage)).obj
            S.I).val.obj U from r • (show ((SheafOfModules.restrictScalars ((sheafCompose X.J
            (forget₂ CommRingCat.{u} RingCat.{u})).map S.baseReductionInverseImage)).obj
              S.I).val.obj U from S.kernelPreimage x))) = (r • x).1 :=
      (map_smul (S.idealInclusion.val.app U).hom r _).trans
        (congrArg (r • ·) (S.idealInclusion_kernelPreimage x))
    rw [S.kernelPreimage_eq (r • x) _ hs]
    exact map_smul (S.c.val.app U).hom _ _
  app_map {U V} f x := by
    change S.c.val.app V (S.kernelPreimage _) = _
    have hs : (show S.thickenedBaseInverseImage.obj.obj V from S.idealInclusion.val.app V
        (S.I.val.map f (S.kernelPreimage x))) =
        (⟨(S.thickenedBaseInverseImage.obj.map f).hom x.1, map_kernel _ f x.2⟩ :
          kernelIdeal S.baseReductionInverseImage.hom V).1 :=
      (PresheafOfModules.naturality_apply S.idealInclusion.val f (S.kernelPreimage x)).trans
        (congrArg _ (S.idealInclusion_kernelPreimage x))
    rw [S.kernelPreimage_eq _ _ hs]
    exact PresheafOfModules.naturality_apply S.c.val f _

variable [HasWeakSheafify X.J CommRingCat.{u}] [X.J.WEqualsLocallyBijective CommRingCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{t} (Sheaf.targetModules.{u, u, u} X.J X.O)]

/-- The automorphism of `G` relating maps on `H^{-1}` to maps into `G[1]`
(`DerivedCategory.negOneHomologySingleIso`), for the identification `G[-1] ≅ G[0][1]` of the
single functors. -/
noncomputable abbrev singleShiftAutomorphism : targetG S ≅ targetG S :=
  DerivedCategory.negOneHomologySingleIso (targetG S)
    (((DerivedCategory.singleFunctors _).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app (targetG S))

/-- **The prescribed map `c : f⁻¹J ⟶ G` as a map out of the conormal sheaf** `I/I²` of
`f⁻¹O_{B'} ⟶ f⁻¹O_B`, linear over `f⁻¹O_B`, followed by the automorphism of `G` fixed by the
identification of maps into `G[1]` with maps on `H^{-1}`. -/
noncomputable def baseConormalMap :
    conormalSheaf.{u, u, max u u u, u} X.J S.thickenedBaseInverseImage
        ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) S.baseReductionInverseImage ⟶
      (Sheaf.squareRestrict.{u, u, u} X.J S.f.fSharpInverseImage).obj (targetG S) :=
  conormalDesc S.baseReductionInverseImage _ S.baseIdealRestriction ≫
    (Sheaf.squareRestrict.{u, u, u} X.J S.f.fSharpInverseImage).map
      (singleShiftAutomorphism S).hom

omit [HasWeakSheafify X.J CommRingCat.{u}] [X.J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- The map out of the conormal sheaf attached to `c` sends the class of a section `x` of the
kernel to the automorphism of `G` applied to `c` of the section of `f⁻¹J` mapping to `x`. -/
theorem baseConormalMap_conormalClass (U : X.Cᵒᵖ)
    (x : kernelIdeal S.baseReductionInverseImage.hom U) :
    (S.baseConormalMap).val.app U
        (conormalClass.{u, u, max u u u, u} X.J S.thickenedBaseInverseImage
          S.thickenedBaseInverseImage _ (𝟙 _) S.baseReductionInverseImage U x) =
      (singleShiftAutomorphism S).hom.val.app U (S.c.val.app U (S.kernelPreimage x)) :=
  congrArg ((singleShiftAutomorphism S).hom.val.app U)
    (conormalDesc_conormalClass S.baseReductionInverseImage _ S.thickenedBaseInverseImage (𝟙 _)
      S.baseIdealRestriction U x)

/-- The connecting morphism `L_{O/f⁻¹O_B} ⟶ (L_{f⁻¹O_B/f⁻¹O_{B'}} ⊗ O)[1]` of the fundamental
triangle of `f⁻¹O_{B'} ⟶ f⁻¹O_B ⟶ O` (Tags 08SZ and 08V1). -/
noncomputable def towerConnecting :
    Sheaf.cotangentComplexDerived.{u, u, u, t} X.J S.f.fSharpInverseImage ⟶
      (DerivedCategory.Q.obj (Sheaf.baseChangedCotangentComplex.{u, u, u} X.J
        S.baseReductionInverseImage S.f.fSharpInverseImage))⟦(1 : ℤ)⟧ :=
  (Sheaf.exists_distTriang_towerCotangent X.J S.baseReductionInverseImage
    S.f.fSharpInverseImage).choose

/-- The map `L_{f⁻¹O_B/f⁻¹O_{B'}} ⊗ O ⟶ G[1]` in the derived category attached to the prescribed
map `c : f⁻¹J ⟶ G`. -/
noncomputable abbrev obstructionBaseClass :
    DerivedCategory.Q.obj (Sheaf.baseChangedCotangentComplex.{u, u, u} X.J
        S.baseReductionInverseImage S.f.fSharpInverseImage) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj (targetG.{u, u, u} S))⟦(1 : ℤ)⟧ :=
  CotangentObstruction.towerBaseClass (targetG.{u, u, u} S) S.baseReductionInverseImage
    S.f.fSharpInverseImage S.baseConormalMap

/-- **The obstruction class of Tag 08V5 (1)**: the image in `Ext²_O(L_f, G)`, under the
connecting morphism of the fundamental triangle of `f⁻¹O_{B'} ⟶ f⁻¹O_B ⟶ O`, of the class in
`Ext¹_O(L_{f⁻¹O_B/f⁻¹O_{B'}} ⊗ O, G)` of the prescribed map `c : f⁻¹J ⟶ G`. -/
noncomputable def obstructionClass : S.f.cotangentExt (targetG.{u, u, u} S) 2 :=
  S.towerConnecting ≫ (S.obstructionBaseClass)⟦(1 : ℤ)⟧' ≫
    (shiftFunctorAdd' _ (1 : ℤ) 1 2 (by norm_num)).inv.app _

/-- The class of `ξ` in `Ext¹_O(NL_{O/f⁻¹O_{B'}}, G)`, restricted to the conormal sheaf, sends the
class of a section `ι a` of the kernel to the automorphism of `G` applied to `ξ`'s restriction
to the base ideal at `a`. -/
private theorem baseExtEquiv_conormalClass_eq_idealRestrictionOfExt
    (ξ : S.squareZeroProblem.f.naiveCotangentExt S.squareZeroProblem.G 1) (U : X.Cᵒᵖ)
    (x : kernelIdeal S.baseReductionInverseImage.hom U) (a : S.I.val.obj U)
    (ha : (show S.thickenedBaseInverseImage.obj.obj U from S.idealInclusion.val.app U a) = x.1) :
    ((CotangentObstruction.baseExtEquiv.{u, u, u} X.J S.baseReductionInverseImage
        S.f.fSharpInverseImage (targetG.{u, u, u} S))
      (DerivedCategory.Q.map (Sheaf.towerExtendScalarsCotangentComplexIso.{u, u, u} X.J
          S.baseReductionInverseImage S.f.fSharpInverseImage).hom ≫
        DerivedCategory.Q.map (Sheaf.towerCotangentBaseChange.{u, u, u} X.J
          S.baseReductionInverseImage S.f.fSharpInverseImage) ≫
        DerivedCategory.Q.map (eqToHom (congrArg (Sheaf.cotangentComplex.{u, u, u} X.J)
          S.toThickenedBase_fSharpInverseImage.symm)) ≫
        DerivedCategory.Q.map (Sheaf.canonicalNaiveComparison.{u, u, u} X.J
          S.toThickenedBase.fSharpInverseImage) ≫ ξ)).val.app U
      (conormalClass.{u, u, max u u u, u} X.J S.thickenedBaseInverseImage
        S.thickenedBaseInverseImage _ (𝟙 _) S.baseReductionInverseImage U x) =
    (singleShiftAutomorphism S).hom.val.app U
      (CompatibleFirstOrderThickening.idealRestrictionOfExt (S := S) ξ U a) := by
  obtain ⟨x, hx⟩ := x
  obtain rfl : S.idealInclusion.val.app U a = x := ha
  refine (CotangentObstruction.baseExtEquiv_canonicalClass_conormalClass
      S.baseReductionInverseImage S.f.fSharpInverseImage (targetG.{u, u, u} S)
      (CompatibleFirstOrderThickening.twistGenerators (S := S.squareZeroProblem) ξ)
      (CompatibleFirstOrderThickening.twistGeneratorsMap (S := S.squareZeroProblem) ξ)
      S.toThickenedBase.fSharpInverseImage S.toThickenedBase_fSharpInverseImage
      (hE := CompatibleFirstOrderThickening.isLocallySurjective_twistPresentation
        (S := S.squareZeroProblem) ξ)
      (CompatibleFirstOrderThickening.twistFunctional (S := S.squareZeroProblem) ξ) ξ
      (CompatibleFirstOrderThickening.comparison_comp_eq_twistFunctional
        (S := S.squareZeroProblem) ξ) U _).trans ?_
  refine congrArg ((singleShiftAutomorphism S).hom.val.app U) ?_
  unfold CompatibleFirstOrderThickening.idealRestrictionOfExt
  rfl

/-- **Stacks 08V5 (1)**: a solution of the square-zero extension problem exists if and only if
the obstruction class in `Ext²_O(L_f, G)` vanishes. -/
@[stacks 08V5 "(1): the element `obstructionClass` of `Ext²_O(L_f, G)`, the image of the class of \
`c` under the connecting morphism of the fundamental triangle of `f⁻¹O_{B'} → f⁻¹O_B → O`, \
vanishes exactly when a solution exists"]
theorem nonempty_iff_obstructionClass_eq_zero :
    Nonempty S.CompatibleFirstOrderThickening ↔ S.obstructionClass = 0 := by
  have hT := (Sheaf.exists_distTriang_towerCotangent X.J S.baseReductionInverseImage
    S.f.fSharpInverseImage).choose_spec
  have e0 : S.obstructionClass = 0 ↔ S.towerConnecting ≫ (S.obstructionBaseClass)⟦(1 : ℤ)⟧' = 0 :=
    ⟨fun h0 => (cancel_mono ((shiftFunctorAdd' _ (1 : ℤ) 1 2 (by norm_num)).inv.app _)).1
      ((Category.assoc _ _ _).trans (h0.trans zero_comp.symm)),
      fun h0 => (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h0).trans zero_comp)⟩
  refine CompatibleFirstOrderThickening.nonempty_iff_exists_idealRestrictionOfExt.trans
    (Iff.trans ?_ (e0.trans (CotangentObstruction.comp_shift_towerBaseClass_eq_zero_iff
      (targetG.{u, u, u} S) S.baseReductionInverseImage S.f.fSharpInverseImage S.towerConnecting
        hT S.baseConormalMap)).symm)
  have hφ := S.toThickenedBase_fSharpInverseImage
  have hχ := fun U => _root_.SheafOfModules.injective_app_of_mono
    (singleShiftAutomorphism S).hom U
  constructor
  · rintro ⟨ξ, hξ⟩
    refine ⟨DerivedCategory.Q.map (eqToHom (congrArg (Sheaf.cotangentComplex.{u, u, u} X.J)
      hφ.symm)) ≫ DerivedCategory.Q.map (Sheaf.canonicalNaiveComparison.{u, u, u} X.J
        S.toThickenedBase.fSharpInverseImage) ≫ ξ, ?_⟩
    refine conormal_hom_ext S.baseReductionInverseImage _ fun U x => ?_
    refine (S.baseExtEquiv_conormalClass_eq_idealRestrictionOfExt ξ U x _
      (S.idealInclusion_kernelPreimage x)).trans ?_
    exact (congrArg ((singleShiftAutomorphism S).hom.val.app U) (hξ U _)).trans
      (S.baseConormalMap_conormalClass U x).symm
  · rintro ⟨d, hd⟩
    obtain ⟨ξ, hξ⟩ := CotangentObstruction.exists_Q_map_canonicalNaiveComparison_comp_eq
      (targetG.{u, u, u} S) S.toThickenedBase.fSharpInverseImage
      (DerivedCategory.Q.map (eqToHom (congrArg (Sheaf.cotangentComplex.{u, u, u} X.J) hφ)) ≫ d)
    refine ⟨ξ, fun U a => ?_⟩
    let x : kernelIdeal S.baseReductionInverseImage.hom U :=
      ⟨S.idealInclusion.val.app U a, S.idealZero U a⟩
    have hpre : S.kernelPreimage x = a := S.kernelPreimage_eq x a rfl
    have hd' : DerivedCategory.Q.map (eqToHom (congrArg (Sheaf.cotangentComplex.{u, u, u} X.J)
        hφ.symm)) ≫ DerivedCategory.Q.map (Sheaf.canonicalNaiveComparison.{u, u, u} X.J
          S.toThickenedBase.fSharpInverseImage) ≫ ξ = d := by
      refine (congrArg (DerivedCategory.Q.map (eqToHom (congrArg
        (Sheaf.cotangentComplex.{u, u, u} X.J) hφ.symm)) ≫ ·) hξ).trans ?_
      have aux : ∀ {K L : CochainComplex (Sheaf.targetModules.{u, u, u} X.J X.O) ℤ}
          (p : L = K) (q : K = L) {W : DerivedCategory (Sheaf.targetModules.{u, u, u} X.J X.O)}
          (e : DerivedCategory.Q.obj K ⟶ W),
          DerivedCategory.Q.map (eqToHom q) ≫ DerivedCategory.Q.map (eqToHom p) ≫ e = e := by
        intro _ _ p _ _ e
        subst p
        rw [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
      exact aux _ _ d
    have key := S.baseExtEquiv_conormalClass_eq_idealRestrictionOfExt ξ U x a rfl
    rw [hd', hd, S.baseConormalMap_conormalClass, hpre] at key
    exact (hχ U key).symm

end Deformation.ToposThickening.RingedToposExtensionProblem

end
