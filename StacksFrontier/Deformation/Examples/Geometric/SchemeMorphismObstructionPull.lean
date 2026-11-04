module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionPulledIdeal
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionKeyCriterion
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionPush
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionPushClass
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionSourceTransition
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionFibreInverseImage
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionHomIdealMap
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionThickenedSheafMap
public import StacksFrontier.Deformation.RingedSpaceThickening.SchemeDeformationExtClassNaturality
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionLiftTargetIso
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpacePulledNaiveTransfer

/-!
# The pulled-back class `Pull(X')` of the obstruction of Stacks 0E3V

Let `f : X ⟶ Y` be a morphism of schemes over a field `k` and `X'` a deformation of `X` over the
square-zero base `k[M] = k ⊕ M`. On `|X|`, the structure sheaf `𝒪_{X'}` is a square-zero
extension of `𝒪_X` by `𝒪_X ⊗_k M`, an algebra over `k` through `k ⟶ k[M]`. Pulling it back along
`f^♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` gives the extension `𝒪_{X'} ×_{𝒪_X} f⁻¹𝒪_Y` of `f⁻¹𝒪_Y` (the second
construction of Stacks 0GQ2), whose class, transferred to `Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X ⊗_k M)`,
is the class `Pull(X')` whose difference with `Push(Y')` is the obstruction of
[Stacks Project, Tag 0E3V] (last paragraph of its proof).

## Main definitions

* `Deformation.Examples.schemeMorphismPullBaseMap`: the `k`-algebra structure of `𝒪_{X'}`.
* `Deformation.Examples.schemeMorphismPullExtension`: `𝒪_{X'}` as an extension of `𝒪_X` by
  `𝒪_X ⊗_k M`.
* `Deformation.Examples.schemeMorphismPullData`: the data of Stacks 0GQ2 it defines.
* `Deformation.Examples.schemeMorphismObstructionPull`: the class `Pull(X')`.

## Main results

* `Deformation.Examples.schemeMorphismPullExtension_ideal_adjointBase`: the function `(0, m)` of
  `Spec k[M]` is carried to the section `1 ⊗ m` of the ideal.
* `Deformation.Examples.schemeMorphismObstructionPull_naturality`: the class is natural along
  arrows of deformations over `k[g] : k[M] ⟶ k[N]`.
* `Deformation.Examples.schemeMorphismObstructionPull_isIsomorphic`: it is invariant under
  isomorphism of deformations.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 0GQ2](https://stacks.math.columbia.edu/tag/0GQ2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction AlgebraicGeometry.RingedSpaceThickening
open AlgebraicGeometry.RingedSpace (inverseImage inverseImageProjection inverseImageSourceInclusion)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

/-- **The structure map of `i ≫ p` factors through `(X, i⁻¹𝒪_{X'})`**: it is the structure map of
`(X, i⁻¹𝒪_{X'}) ⟶ X' ⟶ T` followed by the structure map of `i`. -/
theorem ringedSpaceStructureMap_inverseImageProjection_comp_comp {X X' T : RingedSpace.{u, u}}
    (i : X ⟶ X') (p : X' ⟶ T) :
    Stacks.SheafOfModules.ringedSpaceStructureMap (inverseImageProjection X' i.hom.base ≫ p) ≫
        Stacks.SheafOfModules.ringedSpaceStructureMap i =
      Stacks.SheafOfModules.ringedSpaceStructureMap (i ≫ p) := by
  have hχ : RingedSpace.homOver (Z := inverseImage X' i.hom.base) (i.hom.base ≫ p.hom.base)
      (Stacks.SheafOfModules.ringedSpaceStructureMap (inverseImageProjection X' i.hom.base ≫ p)) =
      inverseImageProjection X' i.hom.base ≫ p :=
    RingedSpace.homOver_base_ringedSpaceStructureMap (inverseImageProjection X' i.hom.base ≫ p)
  have e : i ≫ p = RingedSpace.homOver (Z := X) (i.hom.base ≫ p.hom.base)
      (Stacks.SheafOfModules.ringedSpaceStructureMap (inverseImageProjection X' i.hom.base ≫ p) ≫
        Stacks.SheafOfModules.ringedSpaceStructureMap i) :=
    calc i ≫ p = inverseImageSourceInclusion i ≫ (inverseImageProjection X' i.hom.base ≫ p) := by
          rw [← Category.assoc, RingedSpace.inverseImageSourceInclusion_comp_projection]
      _ = inverseImageSourceInclusion i ≫ RingedSpace.homOver (Z := inverseImage X' i.hom.base)
            (i.hom.base ≫ p.hom.base) (Stacks.SheafOfModules.ringedSpaceStructureMap
              (inverseImageProjection X' i.hom.base ≫ p)) := by rw [hχ]
      _ = _ := RingedSpace.inverseImageSourceInclusion_comp_homOver i _ _
  refine Eq.trans ?_ (Deformation.Examples.eqToHom_comp_ringedSpaceStructureMap e rfl)
  rw [RingedSpace.ringedSpaceStructureMap_homOver (Z := X) (W := T)]
  exact (Category.id_comp _).symm

namespace DeformationSolution

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {ht : IsFirstOrderThickening t}
  {f : X ⟶ S} {G : SheafOfModules.{u} (structureSheafRing X)}
  {c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}
  (Q : DeformationSolution t ht f G c) {T : RingedSpace.{u, u}} (p : Q.X' ⟶ T)

/-- **The algebra structure given by `p : X' ⟶ T`, followed by the reduction, is the structure map
of `i ≫ p`.** -/
theorem comorphismOnOpens_adjoint_comp_reduction :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        (Q.i.hom.base ≫ p.hom.base)).homEquiv _ _).symm (Q.comorphismOnOpensSheafMap p) ≫
        Q.thickenedSheafReduction =
      Stacks.SheafOfModules.ringedSpaceStructureMap (Q.i ≫ p) := by
  rw [← Q.ringedSpaceStructureMap_inverseImageProjection_comp_inv p]
  have h : Q.thickenedSheafIsoInverseImage.inv ≫ Q.thickenedSheafReduction =
      Stacks.SheafOfModules.ringedSpaceStructureMap Q.i := by
    rw [← Q.thickenedSheafIsoInverseImage_hom_comp]
    exact Iso.inv_hom_id_assoc _ _
  exact (Category.assoc _ _ _).trans ((congrArg (Stacks.SheafOfModules.ringedSpaceStructureMap
    (inverseImageProjection Q.X' Q.i.hom.base ≫ p) ≫ ·) h).trans
    (ringedSpaceStructureMap_inverseImageProjection_comp_comp Q.i p))

/-- `comorphismOnOpens_adjoint_comp_reduction`, after a transport of the source. -/
theorem eqToHom_comorphismOnOpens_adjoint_comp_reduction
    {W : TopCat.Sheaf CommRingCat.{u} X.carrier}
    (e : W = (TopCat.Sheaf.pullback CommRingCat.{u} (Q.i.hom.base ≫ p.hom.base)).obj T.sheaf) :
    (eqToHom e ≫ ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        (Q.i.hom.base ≫ p.hom.base)).homEquiv _ _).symm (Q.comorphismOnOpensSheafMap p)) ≫
        Q.thickenedSheafReduction =
      eqToHom e ≫ Stacks.SheafOfModules.ringedSpaceStructureMap (Q.i ≫ p) := by
  subst e
  exact (Q.comorphismOnOpens_adjoint_comp_reduction p).trans (Category.id_comp _).symm

end DeformationSolution

end AlgebraicGeometry.RingedSpaceThickening

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))

/-- The structure map `f⁻¹𝒪_{Spec k} ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X` of the base of `X_A = (X, f⁻¹𝒪_Y)`,
followed by `f^♯`, is the structure map of `X ⟶ Spec k`. -/
theorem schemeMorphismInverseImageBase_structure :
    AlgebraicGeometry.RingedSpaceThickening.structureRingMap (schemeMorphismInverseImageBase f pY) ≫
        Stacks.SheafOfModules.ringedSpaceStructureMap f.toLRSHom.toShHom =
      Stacks.SheafOfModules.ringedSpaceStructureMap
        (f.toLRSHom.toShHom ≫ pY.toLRSHom.toShHom) := by
  have h' : (Stacks.SheafOfModules.inverseImageCompIso
        (inverseImageProjection Y.toRingedSpace f.toLRSHom.toShHom.hom.base)
          pY.toLRSHom.toShHom).hom ≫
      Stacks.SheafOfModules.inverseImageFirstRingMap
        (inverseImageProjection Y.toRingedSpace f.toLRSHom.toShHom.hom.base)
          pY.toLRSHom.toShHom =
      Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap
        (schemeMorphismInverseImageBase f pY) := by
    have h := Stacks.SheafOfModules.inverseImageCompIso_hom_comp
      (inverseImageProjection Y.toRingedSpace f.toLRSHom.toShHom.hom.base)
        pY.toLRSHom.toShHom
    rw [AlgebraicGeometry.RingedSpace.ringedSpaceStructureMap_inverseImageProjection] at h
    exact ((Category.comp_id _).symm.trans (Category.assoc _ _ _)).trans h
  exact (congrArg (· ≫ Stacks.SheafOfModules.ringedSpaceStructureMap f.toLRSHom.toShHom)
    h'.symm).trans ((Category.assoc _ _ _).trans
      (Stacks.SheafOfModules.inverseImageCompIso_hom_comp f.toLRSHom.toShHom
        pY.toLRSHom.toShHom))

variable (hf : f ≫ pY = pX) (M : FGModuleCat.{u} k)
  (xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
    ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))

/-- The solution of the deformation problem of Stacks 08U7 attached to a deformation of `X` over
`k[M]`. -/
abbrev schemeMorphismPullSolution :=
  fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two (Λ := Λ) M) xε

include hf in
/-- The deformation `X' ⟶ Spec k[M] ⟶ Spec k`, restricted to `X`, is `f ≫ p_Y`. -/
theorem schemeMorphismPull_comp_eq :
    (schemeMorphismPullSolution pX M xε).i ≫
        (schemeMorphismPushStructure pX xε).toLRSHom.toShHom =
      f.toLRSHom.toShHom ≫ pY.toLRSHom.toShHom := by
  have h := congrArg (fun t : X ⟶ baseSpec (residueFieldBase Λ k) => t.toLRSHom.toShHom)
    ((specialMap_comp_schemeMorphismPushStructure pX xε).trans hf.symm)
  exact h

/-- The two maps `|X| ⟶ |Spec k|` underlying the base of `X_A` and `X ⟶ X' ⟶ Spec k` agree. -/
theorem schemeMorphismPull_base_eq :
    (schemeMorphismInverseImageBase f pY).hom.base =
      (schemeMorphismPullSolution pX M xε).i.hom.base ≫
        (schemeMorphismPushStructure pX xε).toLRSHom.toShHom.hom.base := by
  have : Subsingleton ((baseSpec (residueFieldBase Λ k)) : Type u) := subsingleton_baseSpec _
  ext x
  exact Subsingleton.elim (α := (baseSpec (residueFieldBase Λ k) : Type u)) _ _

/-- **The `k`-algebra structure of `𝒪_{X'}`**, over the base of `X_A = (X, f⁻¹𝒪_Y)`: the
adjoint of the comorphism of `X' ⟶ Spec k[M] ⟶ Spec k`, read on the opens of `X`. -/
def schemeMorphismPullBaseMap :
    AlgebraicGeometry.RingedSpaceThickening.inverseImageBaseRing
        (schemeMorphismInverseImageBase f pY) ⟶
      (schemeMorphismPullSolution pX M xε).thickenedSheaf :=
  eqToHom (congrArg (fun t : X.carrier ⟶ (baseSpec (residueFieldBase Λ k)).carrier =>
      (TopCat.Sheaf.pullback CommRingCat.{u} t).obj
        (baseSpec (residueFieldBase Λ k)).toRingedSpace.sheaf)
      (schemeMorphismPull_base_eq f pX pY M xε)) ≫
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      ((schemeMorphismPullSolution pX M xε).i.hom.base ≫
        (schemeMorphismPushStructure pX xε).toLRSHom.toShHom.hom.base)).homEquiv _ _).symm
      ((schemeMorphismPullSolution pX M xε).comorphismOnOpensSheafMap
        (schemeMorphismPushStructure pX xε).toLRSHom.toShHom)

include hf in
/-- The `k`-algebra structure of `𝒪_{X'}` is compatible with the reduction to `𝒪_X` and `f^♯`. -/
theorem schemeMorphismPullBaseMap_comp_reduction :
    schemeMorphismPullBaseMap f pX pY M xε ≫
        (schemeMorphismPullSolution pX M xε).thickenedSheafReduction =
      AlgebraicGeometry.RingedSpaceThickening.structureRingMap
          (schemeMorphismInverseImageBase f pY) ≫
        Stacks.SheafOfModules.ringedSpaceStructureMap f.toLRSHom.toShHom := by
  refine ((schemeMorphismPullSolution pX M xε).eqToHom_comorphismOnOpens_adjoint_comp_reduction
    (schemeMorphismPushStructure pX xε).toLRSHom.toShHom _).trans ?_
  exact (eqToHom_comp_ringedSpaceStructureMap (a := f.toLRSHom.toShHom ≫ pY.toLRSHom.toShHom)
    (b := (schemeMorphismPullSolution pX M xε).i ≫
      (schemeMorphismPushStructure pX xε).toLRSHom.toShHom)
    (schemeMorphismPull_comp_eq f pX pY hf M xε).symm _).trans
    (schemeMorphismInverseImageBase_structure f pY).symm

/-! ### The extension `𝒪_{X'}` of `𝒪_X` by `𝒪_X ⊗_k M` -/

include hf in
/-- The coefficient sheaf of the obstruction is the pullback of `M^~` along `p_X = f ≫ p_Y`. -/
theorem schemeMorphismCoefficientSheaf_eq :
    (modulePullback pX.toLRSHom.toShHom).obj (tildeSheaf M) =
      schemeMorphismCoefficientSheaf f pY M := by
  subst hf
  rfl

include hf in
/-- **The pulled-back ideal of `k[M]` on `X` is the coefficient sheaf `𝒪_X ⊗_k M`** of the
obstruction, through `f ≫ p_Y = p_X`. -/
def schemeMorphismPulledIdealIso :
    SchemeDeformationCategory.pulledIdeal ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
        (Over.mk pX) ≅ schemeMorphismCoefficientSheaf f pY M :=
  pulledIdealCoefficientIso (Λ := Λ) M (Over.mk pX) ≪≫
    eqToIso (schemeMorphismCoefficientSheaf_eq f pX pY hf M)

/-- **`𝒪_{X'}` as a square-zero extension of `𝒪_X` by `𝒪_X ⊗_k M`**: the extension attached to
the deformation, with its ideal identified with the coefficient sheaf. -/
def schemeMorphismPullExtension :
    AlgebraSquareZeroExtension ((Over.mk pX).hom.toLRSHom.toShHom ≫
        (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom)
      (schemeMorphismCoefficientSheaf f pY M) :=
  thickenedExtensionOfIdeal xε
    ((schemeMorphismPullSolution pX M xε).toAlgebraExtension.ideal.mapCoeff
      (schemeMorphismPulledIdealIso f pX pY hf M).hom)

/-- The ideal of `𝒪_{X'}` is identified with `𝒪_X ⊗_k M` bijectively. -/
theorem schemeMorphismPullExtension_idealBijective :
    (schemeMorphismPullExtension f pX pY hf M xε).IdealBijective := fun U =>
  ((SheafOfModules.evaluation _ U).mapIso
    (schemeMorphismPulledIdealIso f pX pY hf M)).toLinearEquiv.bijective.comp
    ((schemeMorphismPullSolution pX M xε).toAlgebraExtension_idealBijective U)

/-- **The function `(0, m)` of `Spec k[M]` is carried to the section `1 ⊗ m`**: the algebra
structure of `𝒪_{X'}` sends `(0, m)` into the ideal, where it is the global section `1 ⊗ m` of
`𝒪_X ⊗_k M`. -/
theorem schemeMorphismPullExtension_ideal_adjointBase (m : M) :
    (schemeMorphismPullExtension f pX pY hf M xε).ideal.app _
        ⟨((schemeMorphismPullExtension f pX pY hf M xε).adjointBase.hom.app (op ⊤)).hom
          (squareZeroSpecFunction (Λ := Λ) M m),
          (schemeMorphismPullExtension f pX pY hf M xε).adjointBase_mem_kernelIdeal (op ⊤) _
            (residueSpecMap_squareZeroSpecFunction (Λ := Λ) m)⟩ =
      coefficientSheafSection (f ≫ pY) M m := by
  have h1 := (schemeMorphismPullSolution pX M xε).toAlgebraExtension_ideal_adjointBase (op ⊤)
    (squareZeroSpecFunction (Λ := Λ) M m) (residueSpecMap_squareZeroSpecFunction (Λ := Λ) m)
  have h2 := pulledIdealCoefficientIso_hom_prescribedIdealSection (Λ := Λ) M (Over.mk pX) _
    (residueSpecMap_squareZeroSpecFunction (Λ := Λ) m) m (squareZeroSpecFunction_hom (Λ := Λ) m)
  refine (congrArg (fun z => ((schemeMorphismPulledIdealIso f pX pY hf M).hom.val.app _).hom z)
    h1).trans ?_
  refine (congrArg (fun z => ((eqToHom (schemeMorphismCoefficientSheaf_eq f pX pY hf M)).val.app
    _).hom z) h2).trans ?_
  subst hf
  rfl

/-- **`schemeMorphismPullExtension_ideal_adjointBase` in inclusion form**: the section `1 ⊗ m` of
the ideal of `𝒪_{X'}` is the function `(0, m)` of `Spec k[M]`. -/
theorem schemeMorphismPullExtension_idealIncl (m : M) :
    (schemeMorphismPullExtension f pX pY hf M xε).idealIncl
        (schemeMorphismPullExtension_idealBijective f pX pY hf M xε) (op ⊤)
        (coefficientSheafSection (f ≫ pY) M m) =
      ((schemeMorphismPullExtension f pX pY hf M xε).adjointBase.hom.app (op ⊤)).hom
        (squareZeroSpecFunction (Λ := Λ) M m) :=
  (congrArg ((schemeMorphismPullExtension f pX pY hf M xε).idealIncl
      (schemeMorphismPullExtension_idealBijective f pX pY hf M xε) (op ⊤))
    (schemeMorphismPullExtension_ideal_adjointBase f pX pY hf M xε m).symm).trans
    ((schemeMorphismPullExtension f pX pY hf M xε).idealIncl_ideal
      (schemeMorphismPullExtension_idealBijective f pX pY hf M xε) (op ⊤) _)

attribute [local instance] HasDerivedCategory.standard

/-- **The data of Stacks 0GQ2 attached to a deformation of `X`**: `𝒪_{X'}`, an extension of `𝒪_X`
by `𝒪_X ⊗_k M` and a `k`-algebra, pulled back along `f^♯ : f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
def schemeMorphismPullData :
    FibreExtensionData (schemeMorphismInverseImageBase f pY) (schemeMorphismPushCoefficients f pY M)
      (Stacks.SheafOfModules.ringedSpaceStructureMap f.toLRSHom.toShHom) :=
  (schemeMorphismPullExtension f pX pY hf M xε).fibreExtensionData f.toLRSHom.toShHom
    (schemeMorphismPullExtension_idealBijective f pX pY hf M xε)
    (schemeMorphismInverseImageBase f pY) (schemeMorphismPullBaseMap f pX pY M xε)
    (schemeMorphismPullBaseMap_comp_reduction f pX pY hf M xε)

/-- **The class `Pull(X')` of Stacks 0E3V**: the class of the pulled-back extension
`𝒪_{X'} ×_{𝒪_X} f⁻¹𝒪_Y` of `f⁻¹𝒪_Y`, transferred to `Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X ⊗_k M)`. -/
def schemeMorphismObstructionPull : (schemeMorphismObstructionExtFunctor f pY).obj M :=
  haveI := (schemeMorphismPullData f pX pY hf M xε).toExtension.reduction_surjective
  pulledNaiveCotangentTransfer f.toLRSHom.toShHom pY.toLRSHom.toShHom
    (schemeMorphismCoefficientSheaf f pY M)
    (schemeMorphismPullData f pX pY hf M xε).toExtension.toPresented.extClass

/-- The class `schemeMorphismObstructionPull` is the transfer, along
`pulledNaiveCotangentTransfer`, of the extension class of the pulled-back extension
`schemeMorphismPullData`. -/
theorem schemeMorphismObstructionPull_def :
    haveI := (schemeMorphismPullData f pX pY hf M xε).toExtension.reduction_surjective
    schemeMorphismObstructionPull f pX pY hf M xε =
      pulledNaiveCotangentTransfer f.toLRSHom.toShHom pY.toLRSHom.toShHom
        (schemeMorphismCoefficientSheaf f pY M)
        (schemeMorphismPullData f pX pY hf M xε).toExtension.toPresented.extClass :=
  rfl

/-! ### Naturality of the pull class in the coefficient module -/

section Naturality

variable {M N : FGModuleCat.{u} k} (g : M ⟶ N)
  (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
    ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
  (y : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
    ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj N)) (a : x.1 ⟶ y.1)
  (ha : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).IsHomLift
    ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g) a)

include ha in
/-- An arrow of deformations over `k[g] : k[M] ⟶ k[N]` lies over `Spec k[N] ⟶ Spec k[M]`. -/
theorem fiber_arrow_toBase :
    a.map ≫ x.1.toBase ≫ eqToHom (congrArg baseSpec x.2) =
      (y.1.toBase ≫ eqToHom (congrArg baseSpec y.2)) ≫
        baseSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g) := by
  have h := IsHomLift.fac' (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
    ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g) a
  change a.base = _ at h
  rw [← Category.assoc, a.cartesian.w, h, baseSpecMap_comp, baseSpecMap_comp, baseSpecMap_eqToHom,
    baseSpecMap_eqToHom]
  simp

include ha in
/-- An arrow of deformations over `k[g]` is a morphism over `Spec k`. -/
theorem fiber_arrow_pushStructure :
    a.map ≫ schemeMorphismPushStructure pX x = schemeMorphismPushStructure pX y :=
  SchemeDeformationCategory.map_comp_rebase_toBase_comp_squareZeroStructureSpecMap x.2 y.2 a
    (IsHomLift.fac' (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g) a)

/-- The deformed spaces of an arrow form a morphism under `X`. -/
theorem fiber_arrow_i :
    (schemeMorphismPullSolution pX N y).i ≫ a.map.toLRSHom.toShHom =
      (schemeMorphismPullSolution pX M x).i :=
  congrArg (fun t : X ⟶ x.1.scheme => t.toLRSHom.toShHom) a.special_compat

/-- **The map `𝒪_{X'_x} ⟶ 𝒪_{X'_y}` on the opens of `X` given by an arrow of deformations.** -/
abbrev schemeMorphismPullTransition :
    (schemeMorphismPullSolution pX M x).thickenedSheaf ⟶
      (schemeMorphismPullSolution pX N y).thickenedSheaf :=
  (schemeMorphismPullSolution pX M x).thickenedSheafMap (schemeMorphismPullSolution pX N y)
    a.map.toLRSHom.toShHom (fiber_arrow_i pX x y a)

include ha in
/-- **The `k`-algebra structures are compatible with an arrow of deformations.** -/
theorem schemeMorphismPullBaseMap_comp_transition :
    schemeMorphismPullBaseMap f pX pY M x ≫ schemeMorphismPullTransition pX x y a =
      schemeMorphismPullBaseMap f pX pY N y := by
  have hq : a.map.toLRSHom.toShHom ≫ (schemeMorphismPushStructure pX x).toLRSHom.toShHom =
      (schemeMorphismPushStructure pX y).toLRSHom.toShHom :=
    congrArg (fun t : y.1.scheme ⟶ baseSpec (residueFieldBase Λ k) => t.toLRSHom.toShHom)
      (fiber_arrow_pushStructure pX g x y a ha)
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (eqToHom _ ≫ ·)
    ((schemeMorphismPullSolution pX M x).comorphismOnOpens_adjoint_comp_thickenedSheafMap
    (schemeMorphismPullSolution pX N y) a.map.toLRSHom.toShHom (fiber_arrow_i pX x y a)
    (schemeMorphismPushStructure pX x).toLRSHom.toShHom)).trans ?_
  refine (eqToHom_trans_assoc _ _ _).trans ?_
  exact DeformationSolution.eqToHom_comp_comorphismOnOpens_adjoint_congr
    (schemeMorphismPullSolution pX N y) hq _ _

/-- The opposite scalar action on a module over a field, through `MulOpposite.unop`. -/
private abbrev oppositeModule (V : FGModuleCat.{u} k) : Module kᵐᵒᵖ V :=
  Module.compHom V {
    toFun := MulOpposite.unop
    map_one' := rfl
    map_mul' := by simp [mul_comm]
    map_zero' := rfl
    map_add' := by intros; rfl }

/-- The map of spectra of `k[g] : k[M] ⟶ k[N]` carries the function `(0, m)` to `(0, g m)`. -/
theorem baseSpecMap_appTop_squareZeroSpecFunction (m : M) :
    (baseSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g)).appTop
        (squareZeroSpecFunction (Λ := Λ) M m) = squareZeroSpecFunction (Λ := Λ) N (g.hom m) := by
  have h := congrArg (fun φ => φ.hom (squareZeroInr (Λ := Λ) M m))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g).hom.toRingHom))
  refine h.symm.trans ?_
  change (Scheme.ΓSpecIso
      (CommRingCat.of ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj N))).inv.hom
    (((squareZeroExtensionArtinian.{u, u, u} Λ k).map g).hom (squareZeroInr (Λ := Λ) M m)) = _
  let : Module kᵐᵒᵖ M := oppositeModule M
  let : Module kᵐᵒᵖ N := oppositeModule N
  let : IsCentralScalar k M := ⟨fun _ _ => rfl⟩
  let : IsCentralScalar k N := ⟨fun _ _ => rfl⟩
  exact congrArg (Scheme.ΓSpecIso (CommRingCat.of
    ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj N))).inv.hom
    (TrivSqZeroExt.map_inr g.hom.hom m)

include ha in
/-- An arrow of deformations is compatible with the maps to `Spec k[M]` and `Spec k[N]`. -/
theorem fiber_arrow_f' :
    a.map.toLRSHom.toShHom ≫ (schemeMorphismPullSolution pX M x).f' =
      (schemeMorphismPullSolution pX N y).f' ≫
        (baseSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g)).toLRSHom.toShHom :=
  congrArg (fun t : y.1.scheme ⟶ baseSpec ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M) =>
    t.toLRSHom.toShHom) (fiber_arrow_toBase pX g x y a ha)

include ha in
/-- **The algebra structures over `k[M]` and `k[N]` are compatible with an arrow over `k[g]`**: the
function `(0, m)` of `Spec k[M]` goes to the function `(0, g m)` of `Spec k[N]`. -/
theorem schemeMorphismPullTransition_adjointBase (m : M) :
    ((schemeMorphismPullTransition pX x y a).hom.app (op ⊤)).hom
        (((schemeMorphismPullSolution pX M x).toAlgebraExtension.adjointBase.hom.app (op ⊤)).hom
          (squareZeroSpecFunction (Λ := Λ) M m)) =
      ((schemeMorphismPullSolution pX N y).toAlgebraExtension.adjointBase.hom.app (op ⊤)).hom
        (squareZeroSpecFunction (Λ := Λ) N (g.hom m)) := by
  have hx : (schemeMorphismPullSolution pX M x).toAlgebraExtension.adjointBase =
      (schemeMorphismPullSolution pX M x).deformedBaseSheafMap :=
    (schemeMorphismPullSolution pX M x).adjoint_thickenedSheafBase
  have hy : (schemeMorphismPullSolution pX N y).toAlgebraExtension.adjointBase =
      (schemeMorphismPullSolution pX N y).deformedBaseSheafMap :=
    (schemeMorphismPullSolution pX N y).adjoint_thickenedSheafBase
  have hc0 : (a.map.toLRSHom.toShHom ≫ (schemeMorphismPullSolution pX M x).f').hom =
      ((schemeMorphismPullSolution pX N y).f' ≫
        (baseSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g)).toLRSHom.toShHom).hom :=
    congrArg InducedCategory.Hom.hom (fiber_arrow_f' pX g x y a ha)
  have hc := congrArg (fun t => t.hom (squareZeroSpecFunction (Λ := Λ) M m))
    (PresheafedSpace.congr_app hc0 (op ⊤))
  have hσ := baseSpecMap_appTop_squareZeroSpecFunction (Λ := Λ) g m
  refine (congrArg (fun z => ((schemeMorphismPullTransition pX x y a).hom.app (op ⊤)).hom z)
    (congrArg (fun t => (t.hom.app (op ⊤)).hom (squareZeroSpecFunction (Λ := Λ) M m)) hx)).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => (t.hom.app (op ⊤)).hom
    (squareZeroSpecFunction (Λ := Λ) N (g.hom m))) hy).symm
  change ((schemeMorphismPullTransition pX x y a).hom.app (op ⊤)).hom
      (((schemeMorphismPullSolution pX M x).deformedBasePresheafMap.app (op ⊤)).hom _) =
    ((schemeMorphismPullSolution pX N y).deformedBasePresheafMap.app (op ⊤)).hom _
  rw [DeformationSolution.deformedBasePresheafMap_app,
    DeformationSolution.deformedBasePresheafMap_app]
  refine ((schemeMorphismPullSolution pX M x).thickenedSheafMap_app_c_app
    (schemeMorphismPullSolution pX N y) a.map.toLRSHom.toShHom (fiber_arrow_i pX x y a)
    (schemeMorphismPullSolution pX M x).f' ⊤ _
    ((schemeMorphismPullSolution pX M x).opens_map_f' ⊤) rfl _).trans ?_
  refine (congrArg (fun z => ((schemeMorphismPullSolution pX N y).X'.presheaf.map _).hom z)
    hc).trans ?_
  change ((schemeMorphismPullSolution pX N y).X'.presheaf.map _).hom
    (((schemeMorphismPullSolution pX N y).X'.presheaf.map _).hom
      (((schemeMorphismPullSolution pX N y).f'.hom.c.app _).hom
        ((baseSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g)).appTop
          (squareZeroSpecFunction (Λ := Λ) M m)))) = _
  rw [hσ]
  exact DeformationSolution.presheaf_map_map_apply _ _ _ _ _

include hf in
/-- The map of thickened structure sheaves of an arrow is compatible with the reductions of the
extensions. -/
theorem schemeMorphismPullTransition_comp_reduction :
    schemeMorphismPullTransition pX x y a ≫ (schemeMorphismPullExtension f pX pY hf N y).reduction =
      (schemeMorphismPullExtension f pX pY hf M x).reduction :=
  (schemeMorphismPullSolution pX M x).thickenedSheafMap_comp_reduction
    (schemeMorphismPullSolution pX N y) a.map.toLRSHom.toShHom (fiber_arrow_i pX x y a)

/-- The map of coefficient sheaves induced on the ideals by an arrow of deformations. -/
abbrev schemeMorphismPullIdealMap :
    schemeMorphismCoefficientSheaf f pY M ⟶ schemeMorphismCoefficientSheaf f pY N :=
  (schemeMorphismPullExtension f pX pY hf M x).idealMapOfHom
    (schemeMorphismPullExtension f pX pY hf N y)
    (schemeMorphismPullExtension_idealBijective f pX pY hf M x)
    (schemeMorphismPullTransition pX x y a)
    (schemeMorphismPullTransition_comp_reduction f pX pY hf x y a)

include ha in
/-- **On the ideals, an arrow of deformations over `k[g]` induces `𝒪_X ⊗_k g`**: both sides send
`1 ⊗ m` to `1 ⊗ g m`. -/
theorem schemeMorphismPullIdealMap_eq :
    schemeMorphismPullIdealMap f pX pY hf x y a =
      (schemeMorphismCoefficientSheafFunctor f pY).map g := by
  refine coefficientSheaf_hom_ext (f ≫ pY) M (fun m => ?_)
  refine Eq.trans ?_ (coefficientSheafSection_map (f ≫ pY) g m).symm
  change (schemeMorphismPullExtension f pX pY hf N y).ideal.app (op ⊤) ⟨_, _⟩ = _
  refine Eq.trans (congrArg ((schemeMorphismPullExtension f pX pY hf N y).ideal.app (op ⊤))
    (Subtype.ext ?_)) (schemeMorphismPullExtension_ideal_adjointBase f pX pY hf N y (g.hom m))
  change ((schemeMorphismPullTransition pX x y a).hom.app (op ⊤)).hom
    ((schemeMorphismPullExtension f pX pY hf M x).idealIncl
      (schemeMorphismPullExtension_idealBijective f pX pY hf M x) (op ⊤)
      (coefficientSheafSection (f ≫ pY) M m)) = _
  rw [schemeMorphismPullExtension_idealIncl]
  exact schemeMorphismPullTransition_adjointBase pX g x y a ha m

include ha in
/-- **Naturality of the pull class in the coefficient module**: for an arrow of deformations of `X`
over `k[g] : k[M] ⟶ k[N]`, `Pull(X'_y)` is `Pull(X'_x)` pushed forward along `𝒪_X ⊗_k g`. -/
theorem schemeMorphismObstructionPull_naturality :
    schemeMorphismObstructionPull f pX pY hf N y =
      (schemeMorphismObstructionExtFunctor f pY).map g
        (schemeMorphismObstructionPull f pX pY hf M x) := by
  have := (schemeMorphismPullData f pX pY hf M x).toExtension.reduction_surjective
  have := (schemeMorphismPullData f pX pY hf N y).toExtension.reduction_surjective
  have hcl := (schemeMorphismPullData f pX pY hf M x).extClass_toExtension_comp
    (schemeMorphismPullData f pX pY hf N y)
    ((modulePushforward (inverseImageSourceInclusion f.toLRSHom.toShHom)).map
      ((schemeMorphismCoefficientSheafFunctor f pY).map g))
    (schemeMorphismPullTransition pX x y a)
    (schemeMorphismPullTransition_comp_reduction f pX pY hf x y a)
    (schemeMorphismPullBaseMap_comp_transition f pX pY g x y a ha)
    (fun U n => ((schemeMorphismPullExtension f pX pY hf M x).hom_idealIncl_idealMapOfHom
      (schemeMorphismPullExtension f pX pY hf N y)
      (schemeMorphismPullExtension_idealBijective f pX pY hf M x)
      (schemeMorphismPullExtension_idealBijective f pX pY hf N y)
      (schemeMorphismPullTransition pX x y a)
      (schemeMorphismPullTransition_comp_reduction f pX pY hf x y a) U n).trans
      (congrArg (fun φ => (schemeMorphismPullExtension f pX pY hf N y).idealIncl
        (schemeMorphismPullExtension_idealBijective f pX pY hf N y) U ((φ.val.app U).hom n))
        (schemeMorphismPullIdealMap_eq f pX pY hf g x y a ha)))
  refine (congrArg (pulledNaiveCotangentTransfer f.toLRSHom.toShHom pY.toLRSHom.toShHom
    (schemeMorphismCoefficientSheaf f pY N)) hcl.symm).trans ?_
  exact pulledNaiveCotangentTransfer_naturality f.toLRSHom.toShHom pY.toLRSHom.toShHom
    ((schemeMorphismCoefficientSheafFunctor f pY).map g) _

end Naturality

/-- **The pull class is invariant under isomorphism of deformations.** -/
theorem schemeMorphismObstructionPull_isIsomorphic (hf : f ≫ pY = pX) (M : FGModuleCat.{u} k)
    (x x' : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)) (h : IsIsomorphic x x') :
    schemeMorphismObstructionPull f pX pY hf M x = schemeMorphismObstructionPull f pX pY hf M x' :=
  eq_of_isIsomorphic_of_natural (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
    (schemeMorphismObstructionExtFunctor f pY)
    (fun M x => schemeMorphismObstructionPull f pX pY hf M x)
    (fun g x y a ha => schemeMorphismObstructionPull_naturality f pX pY hf g x y a ha) M x x' h

end Deformation.Examples
