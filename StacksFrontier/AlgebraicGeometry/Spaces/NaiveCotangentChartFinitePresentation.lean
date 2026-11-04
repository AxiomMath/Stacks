module

public import StacksFrontier.Algebra.Homology.DoubleQuasiIso
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentChartDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentChartSectionTensorMono

/-!
# The naive cotangent complex of a morphism of algebraic spaces on an affine chart

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, and let `d` be a diagram of
étale scheme charts over `f` with affine charts `V = Spec A` of `X` and `W = Spec R` of `Y`.
Write `Γ` for the ring of global functions of the small étale site of `X` localized at `V`,
which evaluation at the final object identifies with `A`, and `M ↦ M ⊗_Γ 𝒪` for the functor of
`Stacks.Cohomology.SiteModules.sectionTensorSheafFunctor` on the localized site.

This file builds the canonical chain map

`(NL_{A/R}) ⊗_A 𝒪 ⟶ NL_{X/Y}|_V`

from the complex of sheaves attached to the canonical naive cotangent complex of `A` over `R` to
the restriction to the localized site of the naive cotangent complex of `f` (Stacks 0D0V).  In
degree `-1` it is the comparison `NL_{𝒪_X(V)/(f⁻¹𝒪_Y)(V)} ⟶ NL_{X/Y}(V)` of sections
(`Stacks.SheafOfModules.sectionsConormalComparison`) precomposed with the map of naive cotangent
complexes of the square `R → (f⁻¹𝒪_Y)(V)`, `A = 𝒪_X(V)`, extended `𝒪`-linearly through the
universal property of `M ⊗_Γ 𝒪`; in degree `0` likewise with
`Stacks.SheafOfModules.sectionsTensorComparison`.

## Main definitions

* `AlgebraicGeometry.Space.chartModuleLift`: an `A`-module, read as a `Γ`-module with its elements
  lifted to the universe of the sections of `NL_{X/Y}`.
* `AlgebraicGeometry.Space.chartSectionsTheta` and
  `AlgebraicGeometry.Space.chartSectionsTensorHom`: an `A`-linear map into the sections over `V` of
  a sheaf of `𝒪_X`-modules, as a `Γ`-linear map into the global sections of its restriction to `V`,
  and as a morphism out of `M ⊗_Γ 𝒪`.
* `AlgebraicGeometry.Space.chartNaiveCotangentSlice`: `NL_{X/Y}|_V`.
* `AlgebraicGeometry.Space.chartCanonicalNaiveCotangentMap`: the chain map
  `(NL_{A/R}) ⊗_A 𝒪 ⟶ NL_{X/Y}|_V`.

## References

* [Stacks Project, Tag 0D0Z](https://stacks.math.columbia.edu/tag/0D0Z)
* [Stacks Project, Tag 0D0V](https://stacks.math.columbia.edu/tag/0D0V)
* [Stacks Project, Tag 0D0I](https://stacks.math.columbia.edu/tag/0D0I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite
  TensorProduct Stacks.Cohomology.SiteModules Algebra

universe u

attribute [local instance 1]
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Sheaf.hasWeakSheafifyCommRingCat
  Sheaf.hasSheafifyAddCommGrpCat
  Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

namespace Stacks.NaiveCotangent

variable {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
  [Algebra R S] [Algebra R' S'] (fR : R →+* R') (fS : S →+* S')
  (h : ∀ r : R, fS (algebraMap R S r) = algebraMap R' S' (fR r))

/-- The map on conormal modules of a square is semilinear over its top edge. -/
theorem cotangentMapOfSquare_smul (s : S) (x : (Generators.self R S).toExtension.Cotangent) :
    cotangentMapOfSquare fR fS h (s • x) = fS s • cotangentMapOfSquare fR fS h x := by
  let := fR.toAlgebra
  let := fS.toAlgebra
  let := (fS.comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun r => h r
  have : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (Extension.Cotangent.map
    (selfHomOfSquare (R := R) (S := S) (R' := R') (S' := S')).toExtensionHom).map_smul s x

/-- The map on cotangent spaces of a square is semilinear over its top edge. -/
theorem cotangentSpaceMapOfSquare_smul (s : S)
    (x : (Generators.self R S).toExtension.CotangentSpace) :
    cotangentSpaceMapOfSquare fR fS h (s • x) = fS s • cotangentSpaceMapOfSquare fR fS h x := by
  let := fR.toAlgebra
  let := fS.toAlgebra
  let := (fS.comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun r => h r
  have : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (Extension.CotangentSpace.map
    (selfHomOfSquare (R := R) (S := S) (R' := R') (S' := S')).toExtensionHom).map_smul s x

include h in
/-- The map on cotangent spaces of a square, on the differential of a variable. -/
theorem cotangentSpaceMapOfSquare_tmul_D_X (s : S) (t : S) :
    cotangentSpaceMapOfSquare fR fS h
        (s ⊗ₜ[(Generators.self R S).toExtension.Ring] KaehlerDifferential.D R
          (Generators.self R S).toExtension.Ring
          (MvPolynomial.X t)) =
      fS s ⊗ₜ[(Generators.self R' S').toExtension.Ring] KaehlerDifferential.D R'
          (Generators.self R' S').toExtension.Ring
          (MvPolynomial.X (fS t)) := by
  let := fR.toAlgebra
  let := fS.toAlgebra
  let := (fS.comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun r => h r
  have : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine (Extension.CotangentSpace.map_tmul
    (selfHomOfSquare (R := R) (S := S) (R' := R') (S' := S')).toExtensionHom s _).trans ?_
  congr 1
  refine congrArg (KaehlerDifferential.D R' (Generators.self R' S').toExtension.Ring) ?_
  exact (selfHomOfSquare_toAlgHom fR fS h (MvPolynomial.X t)).trans
    (selfRingHomOfSquare_X fR fS t)

end Stacks.NaiveCotangent

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom)

/-! ### Modules over the chart ring, read over the global functions of the slice -/

/-- The ring `A = 𝒪_X(V)` of the chart of `X`. -/
abbrev chartSourceRing : Type u := ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))

/-- **An `A`-module read as a `Γ`-module**, through evaluation `Γ → A` at the final object of the
slice, with its elements lifted to the universe of the sections of `NL_{X/Y}`. -/
def chartModuleLift :
    ModuleCat.{u} (chartSourceRing B S hS f d) ⥤ ModuleCat.{u + 1} (chartGlobalRing B S hS f d) :=
  ModuleCat.restrictScalars (chartEvalTop B S hS f d) ⋙ ModuleCat.uliftFunctor.{u + 1, u} _

/-- The functor `chartModuleLift` is additive. -/
instance : (chartModuleLift B S hS f d).Additive := by
  dsimp only [chartModuleLift]
  infer_instance

/-- The functor `N ↦ N ⊗_A 𝒪` on the slice at `V`: an `A`-module, read over `Γ`, tensored with
the structure sheaf. -/
abbrev chartTensorFunctor :
    ModuleCat.{u} (chartSourceRing B S hS f d) ⥤
      _root_.SheafOfModules.{u + 1} (chartSliceRingSheaf B S hS f d) :=
  chartModuleLift B S hS f d ⋙
    sectionTensorSheafFunctor.{u + 1, u, u, u} (chartSliceRing B S hS f d)

/-- The functor `N ↦ N ⊗_A 𝒪` is additive. -/
instance : (chartTensorFunctor B S hS f d).Additive :=
  have := (sectionTensorSheafAdjunction.{u + 1, u, u, u}
    (chartSliceRing B S hS f d)).left_adjoint_additive
  inferInstance

/-! ### Sections over `V` as global sections of the slice -/

/-- The restriction of a sheaf of `𝒪_X`-modules to the slice at `V`, read over the structure
sheaf of the slice in the spelling of the global-sections API. -/
abbrev chartSliceModule (G : _root_.SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)) :
    _root_.SheafOfModules.{u + 1} (chartSliceRingSheaf B S hS f d) :=
  G.over d.U

section Theta

variable (G : _root_.SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))
  {N : ModuleCat.{u} (chartSourceRing B S hS f d)} (s : N →+ G.val.obj (op d.U))
  (hs : ∀ (a : chartSourceRing B S hS f d) (n : N),
    s (a • n) = (show (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X).O).obj.obj (op d.U) from a) • s n)

include hs in
/-- **An `A`-linear map into the sections over `V` of a sheaf of `𝒪_X`-modules, as a `Γ`-linear
map into the global sections of its restriction to the slice at `V`.** -/
def chartSectionsTheta :
    (chartModuleLift B S hS f d).obj N ⟶
      (globalSectionsFunctor (chartSliceRingSheaf B S hS f d)).obj
        (chartSliceModule B S hS f d G) :=
  ModuleCat.ofHom (X := (chartModuleLift B S hS f d).obj N)
      (Y := (globalSectionsFunctor (chartSliceRingSheaf B S hS f d)).obj
        (chartSliceModule B S hS f d G))
    { toFun := fun m => (chartSliceModule B S hS f d G).val.sectionsOfIsTerminal
        (chartTopIsTerminal B S hS f d) (s (ULift.down m))
      map_add' := fun m₁ m₂ => by
        refine PresheafOfModules.sections_ext _ _ fun U => ?_
        change (chartSliceModule B S hS f d G).val.map
              ((chartTopIsTerminal B S hS f d).from U.unop).op
            (s (ULift.down m₁ + ULift.down m₂)) =
          (chartSliceModule B S hS f d G).val.map ((chartTopIsTerminal B S hS f d).from U.unop).op
              (s (ULift.down m₁)) +
            (chartSliceModule B S hS f d G).val.map ((chartTopIsTerminal B S hS f d).from U.unop).op
              (s (ULift.down m₂))
        exact (congrArg ((chartSliceModule B S hS f d G).val.map
          ((chartTopIsTerminal B S hS f d).from U.unop).op)
          (map_add s _ _)).trans (map_add _ _ _)
      map_smul' := fun γ m => by
        refine PresheafOfModules.sections_ext _ _ fun U => ?_
        have e := hs (chartEvalTop B S hS f d γ) (ULift.down m)
        change (chartSliceModule B S hS f d G).val.map
              ((chartTopIsTerminal B S hS f d).from U.unop).op
            (s (chartEvalTop B S hS f d γ • ULift.down m)) =
          γ.1 U • ((chartSliceModule B S hS f d G).val.map
              ((chartTopIsTerminal B S hS f d).from U.unop).op
            (s (ULift.down m)) : (chartSliceModule B S hS f d G).val.obj U)
        refine (congrArg ((chartSliceModule B S hS f d G).val.map
          ((chartTopIsTerminal B S hS f d).from U.unop).op) e).trans ?_
        exact ((chartSliceModule B S hS f d G).val.map_smul _ _ _).trans
          (congrArg (· • _) (globalSectionEvalHom_naturality _ γ)) }

include hs in
/-- The section of `chartSectionsTheta` at `m`, evaluated on an object `U` of the slice, is the
restriction of `s m` along `U ⟶ V`. -/
theorem chartSectionsTheta_apply_val (m : (chartModuleLift B S hS f d).obj N) (U : Over d.U) :
    ((chartSectionsTheta B S hS f d G s hs).hom m).val (op U) =
      G.val.map U.hom.op (s (ULift.down m)) :=
  rfl

/-- **The morphism `N ⊗_A 𝒪 ⟶ G|_V`** attached to an `A`-linear map `N → G(V)`, through the
universal property of `M ⊗_Γ 𝒪`. -/
def chartSectionsTensorHom : (chartTensorFunctor B S hS f d).obj N ⟶ G.over d.U :=
  ((sectionTensorSheafAdjunction.{u + 1, u, u, u} (chartSliceRing B S hS f d)).homEquiv _
    (chartSliceModule B S hS f d G)).symm (chartSectionsTheta B S hS f d G s hs)

/-- The adjunction transports `chartSectionsTensorHom` back to `chartSectionsTheta`. -/
theorem chartSectionsTensorHom_homEquiv :
    (sectionTensorSheafAdjunction.{u + 1, u, u, u} (chartSliceRing B S hS f d)).homEquiv _
      (chartSliceModule B S hS f d G) (chartSectionsTensorHom B S hS f d G s hs) =
        chartSectionsTheta B S hS f d G s hs :=
  Equiv.apply_symm_apply _ _

end Theta

/-! ### The chain map `(NL_{A/R}) ⊗_A 𝒪 ⟶ NL_{X/Y}|_V` -/

section ChainMap

open Stacks.NaiveCotangentFinitePresentation HomologicalComplex

attribute [local instance] chartDiagramAlgebraInst

/-- The ring `R = 𝒪_Y(W)` of the chart of `Y`. -/
abbrev chartTargetRing : Type u := ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V))

/-- The final object of the slice at `V`. -/
abbrev chartTop : Over d.U := Over.mk (𝟙 d.U)

/-- The canonical presentation of `A` over `R`. -/
abbrev chartCanonicalGenerators :=
  NaiveCotangent.canonicalGenerators (chartTargetRing B S hS f d) (chartSourceRing B S hS f d)

/-- **`NL_{X/Y}|_V`**, the restriction of the naive cotangent complex of `f` (Stacks 0D0V) to the
small étale site of `X` localized at `V`. -/
abbrev chartNaiveCotangentSlice :
    CochainComplex (_root_.SheafOfModules.{u + 1} (chartSliceRingSheaf B S hS f d)) ℤ :=
  ((_root_.SheafOfModules.overFunctor.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)
        d.U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (naiveCotangentComplex B S hS f)

/-- The conormal sequence of the canonical presentation of `f♯`, whose left-hand map is the
differential of `NL_{X/Y}`. -/
abbrev chartCS := naiveCotangentConormalSequence B S hS f

/-- The degree `-1` comparison on sections over `V`: the map of conormal modules of the square
`R → (f⁻¹𝒪_Y)(V)`, `A → 𝒪_X(V)`, followed by the comparison of sections of
`Stacks.SheafOfModules.sectionsConormalComparison`. -/
def chartConormalSection :
    nlMod₁ (chartCanonicalGenerators B S hS f d) →+
      (chartCS B S hS f).X₁.val.obj (op d.U) :=
  letI := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op d.U)
  letI := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f)
    (op (chartTop B S hS f d).left)
  (Stacks.SheafOfModules.sectionsConormalComparison.{u, u + 1, u, u} _
    (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
    (structureSharpInverseImage B S hS f) (op d.U)).toAddMonoidHom.comp
    (Stacks.NaiveCotangent.cotangentMapOfSquare (chartDiagramRestrictBase B S hS f d
      (chartTop B S hS f d)) (chartDiagramRestrictO B S hS f d (chartTop B S hS f d))
      (chartSquare_comm B S hS f d (chartTop B S hS f d)))

/-- The degree `0` comparison on sections over `V`: the map of cotangent spaces of the square,
followed by the comparison of sections of `Stacks.SheafOfModules.sectionsTensorComparison`. -/
def chartTensorSection :
    nlMod₀ (chartCanonicalGenerators B S hS f d) →+
      (chartCS B S hS f).X₂.val.obj (op d.U) :=
  letI := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op d.U)
  letI := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f)
    (op (chartTop B S hS f d).left)
  (Stacks.SheafOfModules.sectionsTensorComparison.{u, u + 1, u, u} _
    (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
    (structureSharpInverseImage B S hS f) (op d.U)).toAddMonoidHom.comp
    (Stacks.NaiveCotangent.cotangentSpaceMapOfSquare (chartDiagramRestrictBase B S hS f d
      (chartTop B S hS f d)) (chartDiagramRestrictO B S hS f d (chartTop B S hS f d))
      (chartSquare_comm B S hS f d (chartTop B S hS f d)))

/-- Restriction along the identity of `V`, on the regular functions. -/
theorem chartDiagramRestrictO_top (a : chartSourceRing B S hS f d) :
    chartDiagramRestrictO B S hS f d (chartTop B S hS f d) a = a :=
  ConcreteCategory.congr_hom ((smallEtaleRingedTopos B S hS X).O.obj.map_id (op d.U)) a

/-- A linear map composed with an additive map which is semilinear is semilinear. -/
private theorem comp_apply_smul_of_eq {A T P Q N : Type*} [SMul A P] [Semiring T]
    [AddCommMonoid Q] {_ : Module T Q} [AddCommMonoid N] {_ : Module T N} [AddZeroClass P]
    (c : Q →ₗ[T] N) (g : P →+ Q) {a : A} {x : P} {t : T} (e : g (a • x) = t • g x) :
    (c.toAddMonoidHom.comp g) (a • x) = t • (c.toAddMonoidHom.comp g) x := by
  simp [e]

/-- The degree `-1` comparison `chartConormalSection` is `A`-linear. -/
theorem chartConormalSection_smul (a : chartSourceRing B S hS f d)
    (x : nlMod₁ (chartCanonicalGenerators B S hS f d)) :
    chartConormalSection B S hS f d (a • x) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).obj.obj
        (op d.U) from a) • chartConormalSection B S hS f d x := by
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op d.U)
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f)
    (op (chartTop B S hS f d).left)
  unfold chartConormalSection
  exact comp_apply_smul_of_eq _ _ ((Stacks.NaiveCotangent.cotangentMapOfSquare_smul
    (chartDiagramRestrictBase B S hS f d (chartTop B S hS f d))
    (chartDiagramRestrictO B S hS f d (chartTop B S hS f d))
    (chartSquare_comm B S hS f d (chartTop B S hS f d)) a x).trans
      (congrArg (· • _) (chartDiagramRestrictO_top B S hS f d a)))

/-- The degree `0` comparison `chartTensorSection` is `A`-linear. -/
theorem chartTensorSection_smul (a : chartSourceRing B S hS f d)
    (x : nlMod₀ (chartCanonicalGenerators B S hS f d)) :
    chartTensorSection B S hS f d (a • x) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).obj.obj
        (op d.U) from a) • chartTensorSection B S hS f d x := by
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op d.U)
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f)
    (op (chartTop B S hS f d).left)
  unfold chartTensorSection
  exact comp_apply_smul_of_eq _ _ ((Stacks.NaiveCotangent.cotangentSpaceMapOfSquare_smul
    (chartDiagramRestrictBase B S hS f d (chartTop B S hS f d))
    (chartDiagramRestrictO B S hS f d (chartTop B S hS f d))
    (chartSquare_comm B S hS f d (chartTop B S hS f d)) a x).trans
      (congrArg (· • _) (chartDiagramRestrictO_top B S hS f d a)))

/-- **The two comparisons commute with the differentials**: the differential of `NL_{X/Y}` over
`V` after the degree `-1` comparison is the degree `0` comparison after the differential of
`NL_{A/R}`. -/
theorem chartSection_comm (x : nlMod₁ (chartCanonicalGenerators B S hS f d)) :
    (chartCS B S hS f).f.val.app (op d.U) (chartConormalSection B S hS f d x) =
      chartTensorSection B S hS f d ((nlModD (chartCanonicalGenerators B S hS f d)).hom x) := by
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op d.U)
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f)
    (op (chartTop B S hS f d).left)
  refine (LinearMap.congr_fun (Stacks.SheafOfModules.sectionsComparison_comm.{u, u + 1, u, u} _
    (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
    (structureSharpInverseImage B S hS f) (op d.U)) _).trans ?_
  exact congrArg (Stacks.SheafOfModules.sectionsTensorComparison.{u, u + 1, u, u} _
    (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
    (structureSharpInverseImage B S hS f) (op d.U))
    (Stacks.NaiveCotangent.cotangentMapOfSquare_cotangentComplex _ _ _ x)

/-- The degree `-1` component `(I/I²) ⊗_A 𝒪 ⟶ 𝒞|_V` into the restricted conormal sheaf. -/
def chartConormalTensorHom :
    (chartTensorFunctor B S hS f d).obj (nlMod₁ (chartCanonicalGenerators B S hS f d)) ⟶
      chartSliceModule B S hS f d (chartCS B S hS f).X₁ :=
  chartSectionsTensorHom B S hS f d _ (chartConormalSection B S hS f d)
    (chartConormalSection_smul B S hS f d)

/-- The degree `0` component `(Ω ⊗ A) ⊗_A 𝒪 ⟶ (𝒪 ⊗ Ω)|_V`. -/
def chartTensorTensorHom :
    (chartTensorFunctor B S hS f d).obj (nlMod₀ (chartCanonicalGenerators B S hS f d)) ⟶
      chartSliceModule B S hS f d (chartCS B S hS f).X₂ :=
  chartSectionsTensorHom B S hS f d _ (chartTensorSection B S hS f d)
    (chartTensorSection_smul B S hS f d)

/-- **The two components commute with the differentials.** -/
theorem chartTensorHom_comm :
    (chartTensorFunctor B S hS f d).map (nlModD (chartCanonicalGenerators B S hS f d)) ≫
        chartTensorTensorHom B S hS f d =
      chartConormalTensorHom B S hS f d ≫
        (_root_.SheafOfModules.overFunctor.{u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) d.U).map
              (chartCS B S hS f).f := by
  apply ((sectionTensorSheafAdjunction.{u + 1, u, u, u} (chartSliceRing B S hS f d)).homEquiv _
    _).injective
  refine ((sectionTensorSheafAdjunction.{u + 1, u, u, u}
    (chartSliceRing B S hS f d)).homEquiv_naturality_left _ _).trans ?_
  refine Eq.trans ?_ ((sectionTensorSheafAdjunction.{u + 1, u, u, u}
    (chartSliceRing B S hS f d)).homEquiv_naturality_right _ _).symm
  refine (congrArg (fun t => (chartModuleLift B S hS f d).map
    (nlModD (chartCanonicalGenerators B S hS f d)) ≫ t)
    (chartSectionsTensorHom_homEquiv B S hS f d _ (chartTensorSection B S hS f d)
      (chartTensorSection_smul B S hS f d))).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => t ≫ (globalSectionsFunctor
    (chartSliceRingSheaf B S hS f d)).map ((_root_.SheafOfModules.overFunctor.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) d.U).map
      (chartCS B S hS f).f))
    (chartSectionsTensorHom_homEquiv B S hS f d _ (chartConormalSection B S hS f d)
      (chartConormalSection_smul B S hS f d))).symm
  refine ModuleCat.hom_ext (LinearMap.ext fun m => PresheafOfModules.sections_ext _ _ fun U => ?_)
  show (chartCS B S hS f).X₂.val.map U.unop.hom.op
      (chartTensorSection B S hS f d ((nlModD (chartCanonicalGenerators B S hS f d)).hom
        (ULift.down m))) =
    (chartCS B S hS f).f.val.app (op U.unop.left)
      ((chartCS B S hS f).X₁.val.map U.unop.hom.op (chartConormalSection B S hS f d
        (ULift.down m)))
  refine (congrArg ((chartCS B S hS f).X₂.val.map U.unop.hom.op)
    (chartSection_comm B S hS f d (ULift.down m)).symm).trans ?_
  exact (PresheafOfModules.naturality_apply (chartCS B S hS f).f.val U.unop.hom.op _).symm

end ChainMap

end AlgebraicGeometry.Space

end
