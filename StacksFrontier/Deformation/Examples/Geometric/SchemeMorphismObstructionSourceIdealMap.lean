module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionKey
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionPulledIdeal

/-!
# The canonical map on the ideal of the source thickening of Stacks 0E3V

Let `f : X ⟶ Y` be a morphism of schemes over a field `k` and let `Y'` be a deformation of `Y`
over the square-zero base `k[M] = k ⊕ M`, with special fibre `j : Y ⟶ Y'`. On `|X|` the inverse
image `f⁻¹𝒪_{Y'}` is an extension of `f⁻¹𝒪_Y`, and its ideal maps canonically to the coefficient
sheaf `𝒪_X ⊗_k M`: the ideal of `Y` in `Y'` is `𝒪_Y ⊗_k M` by flatness
(`Deformation.Examples.SchemeDeformationCategory.toSolution`,
`Deformation.Examples.pulledIdealCoefficientIso`), and `f^*` carries it to `𝒪_X ⊗_k M`.

## Main definitions

* `Deformation.Examples.schemeMorphismSourceIdeal`: the canonical restriction datum
  `Ker(f⁻¹𝒪_{Y'} ⟶ f⁻¹𝒪_Y) ⟶ 𝒪_X ⊗_k M`.
* `Deformation.Examples.sourceIdealGenerator`: the global section `ũ(m)` of `f⁻¹𝒪_{Y'}` given by
  the function `(0, m)` of `Spec k[M]`.

## Main results

* `Deformation.Examples.sourceIdealGenerator_mem`: `ũ(m)` lies in the ideal.
* `Deformation.Examples.schemeMorphismSourceIdeal_app_generator`: the canonical map sends `ũ(m)` to
  `1 ⊗ m`.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.Sites.Conormal Stacks.Sites.Conormal.IdealRestriction Stacks.Topology
open AlgebraicGeometry.RingedSpaceThickening RingedSpaceModuleAdjunction

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  {M : FGModuleCat.{u} k}
  (yε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
    ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))

variable (M) in
/-- The map from the pulled-back ideal of `k[M]` on `Y` to `f_*(𝒪_X ⊗_k M)`: the identification
`pulledIdealCoefficientIso` with `𝒪_Y ⊗_k M`, followed by the transfer along `f`. -/
def sourceIdealTheta :
    SchemeDeformationCategory.pulledIdeal ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
      (Over.mk pY) ⟶ (modulePushforward f.toLRSHom.toShHom).obj
        (schemeMorphismCoefficientSheaf f pY M) :=
  (pulledIdealCoefficientIso (Λ := Λ) M (Over.mk pY)).hom ≫ coefficientTransfer f pY M

/-- **The canonical map on the ideal of the source thickening**
`Ker(f⁻¹𝒪_{Y'} ⟶ f⁻¹𝒪_Y) ⟶ 𝒪_X ⊗_k M`, linear over `f⁻¹𝒪_{Y'}`: a local section of the ideal
induced by a section `incl q` of the ideal of `Y` in `Y'` goes to the image of `q` under
`𝒪_Y ⊗_k M ⟶ f_*(𝒪_X ⊗_k M)`. -/
def schemeMorphismSourceIdeal :
    IdealRestriction.{u, u, u, u} (Scheme.liftSourceReduction yε.1.specialMap f)
      (schemeMorphismPushCoefficients f pY M) :=
  sourceIdealRestrictionOf f pY yε (sourceIdealTheta f pY M)

/-- **The generators `ũ(m)` of the ideal of the source thickening**: the global section of
`f⁻¹𝒪_{Y'}` induced by the image in `Γ(Y', 𝒪_{Y'})` of the function `(0, m)` of `Spec k[M]`. -/
def sourceIdealGenerator (m : M) : (Scheme.liftSource yε.1.specialMap f).obj.obj (op ⊤) :=
  ambientSection (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base yε.1.scheme.sheaf
    (U := ⊤) (fun _ _ => trivial)
    (((yε.1.rebase yε.2).toBase.appTop).hom (squareZeroSpecFunction (Λ := Λ) M m))

/-- The section `ũ(m)` is the image of the global function `(0, m)` of `Y'` under the unit of the
pullback–pushforward adjunction along `f ≫ j`. -/
theorem sourceIdealGenerator_eq_unit (m : M) :
    sourceIdealGenerator f pY yε m =
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
          (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base).unit.app
            yε.1.scheme.toRingedSpace.sheaf).hom.app (op ⊤)).hom
        ((yε.1.rebase yε.2).toBase.appTop (squareZeroSpecFunction (Λ := Λ) M m)) :=
  ConcreteCategory.congr_hom (ambientSection_eq_unit _ _ ⊤) _

/-! ### The canonical map on the generators -/

/-- Under `Γ(Spec k[M], 𝒪) ≅ k[M]`, the function `squareZeroSpecFunction M m` is `(0, m)`. -/
theorem squareZeroSpecFunction_hom (m : M) :
    (Scheme.ΓSpecIso (CommRingCat.of ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))).hom.hom
        (squareZeroSpecFunction (Λ := Λ) M m) = TrivSqZeroExt.inr (R := k) (M := M) m :=
  congrArg (fun φ => φ.hom (squareZeroInr (Λ := Λ) M m))
    (Scheme.ΓSpecIso
      (CommRingCat.of ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))).inv_hom_id

/-- The function `(0, m)` of `Spec k[M]` restricts to zero along `residueSpecMap`, the closed
immersion `Spec k ⟶ Spec k[M]`. -/
theorem residueSpecMap_squareZeroSpecFunction (m : M) :
    (((residueSpecMap
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom.hom.c.app
      (op ⊤)).hom (squareZeroSpecFunction (Λ := Λ) M m)) = 0 := by
  have h := residueSpecMap_app_top_eq (Λ := Λ) M (squareZeroSpecFunction (Λ := Λ) M m)
  rw [squareZeroSpecFunction_hom] at h
  exact h.trans ((congrArg _ (TrivSqZeroExt.fst_inr k m)).trans (map_zero _))

/-- The section of the ideal of `Y` in `Y'` attached to the function `(0, m)` of `Spec k[M]`: its
image under the transposed ideal map of the solution attached to `Y'`. -/
def sourceIdealBaseSection (m : M) : (sourceIdealModule pY yε).val.obj (op ⊤) :=
  ((sourceSolution pY yε).idealMapTranspose.val.app (op ⊤)).hom
    (baseIdealSection
      (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom
      (op ⊤) (squareZeroSpecFunction (Λ := Λ) M m) (residueSpecMap_squareZeroSpecFunction m))

/-- The image of `sourceIdealBaseSection m` in `Γ(Y', 𝒪_{Y'})` is the pullback of the function
`(0, m)` along `Y' ⟶ Spec k[M]`. -/
theorem incl_sourceIdealBaseSection (m : M) :
    (sourceSolution pY yε).incl (sourceIdealBaseSection pY yε m) =
      ((sourceSolution pY yε).f'.hom.c.app (op ⊤)).hom (squareZeroSpecFunction (Λ := Λ) M m) :=
  ((sourceSolution pY yε).incl_idealMapTranspose (op ⊤) _).trans
    (congrArg _ (idealSheafι_baseIdealSection _ _ _ _))

/-- The pullback of the function `(0, m)` along the structure morphism of the rebased deformation
agrees with its pullback along the morphism `f'` of the solution attached to `Y'`. -/
theorem rebase_toBase_appTop (m : M) :
    (yε.1.rebase yε.2).toBase.appTop (squareZeroSpecFunction (Λ := Λ) M m) =
      ((sourceSolution pY yε).f'.hom.c.app (op ⊤)).hom (squareZeroSpecFunction (Λ := Λ) M m) := by
  rfl

/-- The pullback of the function `(0, m)` to `Y'` is the image of `sourceIdealBaseSection m`. -/
private theorem rebase_toBase_appTop_eq_incl (m : M) :
    (yε.1.rebase yε.2).toBase.appTop (squareZeroSpecFunction (Λ := Λ) M m) =
      (sourceSolution pY yε).incl (sourceIdealBaseSection pY yε m) :=
  (rebase_toBase_appTop pY yε m).trans (incl_sourceIdealBaseSection pY yε m).symm

/-- The pullback to `Y'` of the function `(0, m)` of `Spec k[M]` restricts to zero on the special
fibre `Y`. -/
theorem specialMap_c_rebase_toBase_appTop (m : M) :
    (yε.1.specialMap.toLRSHom.toShHom.hom.c.app (op ⊤)).hom
      ((yε.1.rebase yε.2).toBase.appTop (squareZeroSpecFunction (Λ := Λ) M m)) = 0 :=
  (congrArg _ (rebase_toBase_appTop_eq_incl pY yε m)).trans
    ((sourceSolution pY yε).reduction_incl _)

/-- **The generators `ũ(m)` lie in the ideal of the source thickening.** -/
theorem sourceIdealGenerator_mem (m : M) :
    sourceIdealGenerator f pY yε m ∈
      kernelIdeal (Scheme.liftSourceReduction yε.1.specialMap f).hom (op ⊤) := by
  show ((Scheme.liftSourceReduction yε.1.specialMap f).hom.app (op ⊤)).hom
    (sourceIdealGenerator f pY yε m) = 0
  refine (Scheme.liftSourceReduction_ambientSection yε.1.specialMap f
    (W := ⊤) (V := ⊤) _ _).trans ?_
  rw [specialMap_c_rebase_toBase_appTop pY yε m]
  exact map_zero (ambientSection f.toLRSHom.toShHom.hom.base Y.sheaf
    (U := (Opens.map yε.1.specialMap.toLRSHom.toShHom.hom.base).obj ⊤) (V := ⊤)
    (fun _ _ => trivial)).hom

/-- The section `ũ(m)` is induced by the image of `sourceIdealBaseSection m` in
`Γ(Y', 𝒪_{Y'})`. -/
theorem sourceIdealGenerator_eq (m : M) :
    sourceIdealGenerator f pY yε m =
      ambientSection (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base yε.1.scheme.sheaf
        (U := ⊤) (V := ⊤) (fun _ _ => trivial)
        ((sourceSolution pY yε).incl (sourceIdealBaseSection pY yε m)) :=
  congrArg (ambientSection (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base yε.1.scheme.sheaf
      (U := ⊤) (V := ⊤) (fun _ _ => trivial)).hom
    (rebase_toBase_appTop_eq_incl pY yε m)

/-- The base section of the ideal of `Y` in `Y'` attached to `(0, m)` is the prescribed section,
read through the comparison of the two direct images to `Spec k[M]`. -/
theorem sourceIdealBaseSection_eq (m : M) :
    sourceIdealBaseSection pY yε m =
      (((sourceSolution pY yε).toMorphismOfThickenings.pushforwardComparison
        (SchemeDeformationCategory.pulledIdeal ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
          (Over.mk pY))).val.app (op ⊤)).hom
        (prescribedIdealSection (f := (Over.mk pY).hom.toLRSHom.toShHom) (𝟙 _) (op ⊤)
          (squareZeroSpecFunction (Λ := Λ) M m) (residueSpecMap_squareZeroSpecFunction m)) :=
  congrArg (fun φ => (φ.val.app (op ⊤)).hom
    (baseIdealSection
      (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom
      (op ⊤) (squareZeroSpecFunction (Λ := Λ) M m) (residueSpecMap_squareZeroSpecFunction m)))
    (sourceSolution pY yε).idealMapTranspose_eq

/-- **The canonical map sends `ũ(m)` to `1 ⊗ m`.** -/
theorem schemeMorphismSourceIdeal_app_generator (m : M) :
    (schemeMorphismSourceIdeal f pY yε).app (op ⊤)
        ⟨sourceIdealGenerator f pY yε m, sourceIdealGenerator_mem f pY yε m⟩ =
      coefficientSheafSection (f ≫ pY) M m := by
  refine sourceIdealRestrictionOf_app_eq ⟨⊤, fun _ _ => trivial, sourceIdealBaseSection pY yε m,
    sourceIdealGenerator_eq f pY yε m, ?_⟩
  have e₁ := (sourceIdealBaseSection_eq pY yε m).trans
    ((sourceSolution pY yε).toMorphismOfThickenings.pushforwardComparison_val_app _ (op ⊤) _)
  have e₂ := pulledIdealCoefficientIso_hom_prescribedIdealSection (Λ := Λ) M (Over.mk pY)
    (squareZeroSpecFunction (Λ := Λ) M m) (residueSpecMap_squareZeroSpecFunction m) m
    (squareZeroSpecFunction_hom m)
  have e₃ := coefficientTransfer_section (f := f) (pY := pY) m
  have e₄ := PresheafOfModules.naturality_apply (sourceIdealTheta f pY M).val
    (eqToHom (congrArg (fun g : Y.toRingedSpace ⟶
        (baseSpec ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toRingedSpace =>
      op ((Opens.map g.hom.base).obj ⊤)) (sourceSolution pY yε).comm.symm))
    (prescribedIdealSection (f := (Over.mk pY).hom.toLRSHom.toShHom) (𝟙 _) (op ⊤)
      (squareZeroSpecFunction (Λ := Λ) M m) (residueSpecMap_squareZeroSpecFunction m))
  have e₅ : ((sourceIdealTheta f pY M).val.app _).hom
      (prescribedIdealSection (f := (Over.mk pY).hom.toLRSHom.toShHom) (𝟙 _) (op ⊤)
        (squareZeroSpecFunction (Λ := Λ) M m) (residueSpecMap_squareZeroSpecFunction m)) =
      coefficientSheafSection (f ≫ pY) M m :=
    (congrArg ((coefficientTransfer f pY M).val.app _).hom e₂).trans e₃
  have e₆ := ((congrArg ((sourceIdealTheta f pY M).val.app
    (op ((Opens.map yε.1.specialMap.toLRSHom.toShHom.hom.base).obj ⊤))).hom e₁).trans e₄).trans
    (congrArg _ e₅)
  exact ((congrArg ((schemeMorphismCoefficientSheaf f pY M).val.map _).hom e₆).trans
    ((map_map_eq_map (schemeMorphismCoefficientSheaf f pY M) _ _ (𝟙 _) _).trans
      (map_self_eq _ _ _))).symm

end Deformation.Examples

end
