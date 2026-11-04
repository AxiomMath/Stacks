module

public import StacksFrontier.Algebra.Category.ModuleCat.LinearFromNaturality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.CategoryTheory.Limits.FormalCoproductLinear
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.CohomologyComparisonDegreewise
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SectionsComplexModule
public import StacksFrontier.Homology.DerivedLinear
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# The cohomology of a hypercovering with quasi-coherent coefficients, `Γ(X, ⊤)`-linearly

Let `X` be a scheme, let `K` be a hypercovering of the Zariski site of `X` all of whose members
are affine opens, and let `F` be a quasi-coherent `𝒪_X`-module. The complex of sections
`s(F(K))` is a complex of modules over the ring `Γ(X, ⊤)` of global sections of the structure
sheaf, and this file identifies its cohomology in every degree with the cohomology of `F`,

`H ⁱ(s(F(K))) ≅ R ⁱΓ(X, F)`,

as `Γ(X, ⊤)`-modules, naturally in `F` over the full subcategory of quasi-coherent modules.

The underlying isomorphism of abelian groups is the comparison of [Stacks, Tag 01GY], which
degenerates because a quasi-coherent module is acyclic on an affine open ([Stacks, Tag 01XB]).
The content here is the linear structure: both sides are `Γ(X, ⊤)`-linear functors, and a
natural transformation between the abelian-group-valued functors underlying two `Γ(X, ⊤)`-linear
functors automatically has `Γ(X, ⊤)`-linear components.

## Main definitions

* `Stacks.Cohomology.HypercoveringModules.globalSectionsLinear`: the `Γ(X, ⊤)`-linear structure
  on the category of `𝒪_X`-modules, a scalar acting on local sections through its restriction.
* `Stacks.Cohomology.HypercoveringModules.cechModuleCohomologyForget`: the comparison
  `H ⁱ(s(-(K))) ⟶ R ⁱΓ(X, -)` of the underlying abelian-group-valued functors.
* `Stacks.Cohomology.HypercoveringModules.cechModuleCohomology`: **the comparison
  `H ⁱ(s(-(K))) ⟶ R ⁱΓ(X, -)` of `Γ(X, ⊤)`-module-valued functors.**
* `Stacks.Cohomology.HypercoveringModules.sectionsModuleComplexHomologyIso` and
  `Stacks.Cohomology.HypercoveringModules.sectionsModuleComplexHomologyIsoGlobalSections`: **its
  value at a quasi-coherent module — the isomorphism of `Γ(X, ⊤)`-modules asserted above**, with
  the ring of scalars written in the two spellings of the global sections of the structure sheaf.
* `Stacks.Cohomology.HypercoveringModules.quasicoherentCechModuleCohomologyIso`: the same
  isomorphism as an isomorphism of functors on the full subcategory of quasi-coherent modules.

## Main results

* `Stacks.Cohomology.HypercoveringModules.evaluationTop_rightDerived_linear`: the right derived
  functors of module-valued global sections are `Γ(X, ⊤)`-linear.
* `Stacks.Cohomology.HypercoveringModules.sectionsModuleComplexHomology_linear`: the degree-`i`
  cohomology of the module-valued complex of sections of `K` is a `Γ(X, ⊤)`-linear functor of the
  coefficient module.
* `Stacks.Cohomology.HypercoveringModules.isZero_rightDerived_sections_of_isAffineOpen`:
  the abelian-group-valued higher cohomology of a quasi-coherent module vanishes on an affine
  open.
* `Stacks.Cohomology.HypercoveringModules.isIso_cechModuleCohomology_app`: **the comparison is an
  isomorphism at every quasi-coherent module.**

## Implementation notes

The ring of scalars is `X.ringCatSheaf.obj.obj (op ⊤)`, the sections of the structure sheaf on
the whole scheme read as an object of `RingCat`; this is the ring the module-valued complex of
sections is already a complex over. It is commutative, and `commRing_ringCatSheaf` records that,
which is what makes `ModuleCat` over it a linear category.

Linearity of the complex of sections is assembled from linearity of its two factors. The first
is `SectionsOver.sectionsModulePresheafFunctor`, where a scalar acts on the sections over an
open `U` by the restriction of its image; the scalar acting on the module sheaf acts by the
restriction along the structure map `U ⟶ ⊤`, and the two restrictions agree because `⊤` is
terminal. The second is `Mathlib`'s `FormalCoproduct.cochainComplexFunctor`, whose linearity is
`StacksFrontier.CategoryTheory.Limits.FormalCoproductLinear`. Linearity of homology is
`Stacks.DerivedLinear.homologyFunctor_linear`, and linearity of the right derived functors of
global sections is `Stacks.DerivedLinear.rightDerived_linear`.

The abelian-group-valued comparison is assembled from four identifications and one map: the
exactness of forgetting the module structure moves it past homology;
`SectionsOver.sectionsModuleComplexForgetIso` identifies the resulting complex with the complex
of sections of the underlying abelian sheaf;
`Stacks.CategoryTheory.Hypercovering.cechToSheafCohomologyOfEq` is the comparison of
[Stacks, Tag 01GY] in degree `i`; and [Stacks, Tag 03FD] and [Stacks, Tag 01F1] part (1) —
`underlyingSectionsIso` and `rightDerivedEvaluationForgetIso` — move the target back to the
module-valued derived functor.

Acyclicity on the members enters twice over: [Stacks, Tag 01XB] gives it for the
`SheafOfModules`-derived functor, and [Stacks, Tag 03FD] transports it to the
`Sheaf AddCommGrpCat`-derived functor the degeneration asks for.

## References

* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite Simplicial TopologicalSpace
open AlgebraicGeometry
open Stacks.CategoryTheory.Hypercovering

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme

/-- **The rings of sections of the structure sheaf of a scheme, read as a `RingCat`-valued
sheaf, are commutative.**  This is what makes the categories of modules over them linear. -/
instance commRing_ringCatSheaf (X : Scheme.{u}) (U : (X.Opens)ᵒᵖ) :
    CommRing ↥(X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing ↥(X.presheaf.obj U))

end AlgebraicGeometry.Scheme

namespace Stacks.Cohomology.HypercoveringModules

variable (X : Scheme.{u})

/-! ### The linear structures -/

/-- **The category of `𝒪_X`-modules is linear over the ring `Γ(X, ⊤)` of global sections of the
structure sheaf**, a scalar acting on the sections over an open `U` by the restriction of that
scalar to `U`.  This is `Stacks.SheafOfModules.linearOfTerminalSection` at the terminal open
`⊤`, with the identity ring map. -/
@[instance_reducible]
def globalSectionsLinear :
    Linear ↥(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))) (SheafOfModules.{u} X.ringCatSheaf) :=
  Stacks.SheafOfModules.linearOfTerminalSection X.ringCatSheaf
    (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))) ⊤ isTerminalTop (RingHom.id _)

attribute [local instance] globalSectionsLinear

/-- **Module-valued global sections form a `Γ(X, ⊤)`-linear functor.**  A scalar acts on the
global sections of a module sheaf by the scalar itself, the restriction to `⊤` being trivial. -/
instance evaluationTop_linear :
    Functor.Linear ↥(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))
      (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))) := by
  rw [Functor.linear_iff]
  intro F a
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  exact Stacks.SheafOfModules.smul_val_app_terminal X.ringCatSheaf
    (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))) ⊤ isTerminalTop (RingHom.id _) a (𝟙 F) x

/-- **The right derived functors of module-valued global sections are `Γ(X, ⊤)`-linear.**  This is
`Stacks.DerivedLinear.rightDerived_linear` at `evaluationTop_linear`. -/
instance evaluationTop_rightDerived_linear (i : ℕ) :
    Functor.Linear ↥(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))
      ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived i) :=
  Stacks.DerivedLinear.rightDerived_linear
    (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))) i

/-- **The sections of a module sheaf on the opens over `⊤`, as a presheaf of `Γ(X, ⊤)`-modules,
form a `Γ(X, ⊤)`-linear functor.**  A scalar acts on both sides by the restriction of its image
along the structure map of the open, the two restrictions agreeing because `⊤` is terminal. -/
instance sectionsModulePresheafFunctor_linear :
    Functor.Linear ↥(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))
      (SectionsOver.sectionsModulePresheafFunctor.{u} X.ringCatSheaf ⊤) := by
  rw [Functor.linear_iff]
  intro F a
  exact NatTrans.ext (funext fun _ ↦ ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl))

variable (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : X.Opens))))

/-- **The module-valued complex of sections of `K` is a `Γ(X, ⊤)`-linear functor of the
coefficient module sheaf.**  It is the composite of `sectionsModulePresheafFunctor` with
`Mathlib`'s `FormalCoproduct.cochainComplexFunctor`, and both are linear. -/
instance sectionsModuleComplexFunctor_linear :
    Functor.Linear ↥(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))
      (SectionsOver.sectionsModuleComplexFunctor.{u} X.ringCatSheaf ⊤ K) :=
  inferInstanceAs (Functor.Linear ↥(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))
    (SectionsOver.sectionsModulePresheafFunctor.{u} X.ringCatSheaf ⊤ ⋙
      FormalCoproduct.cochainComplexFunctor K))

/-- **The degree-`i` cohomology of the module-valued complex of sections of `K` is a
`Γ(X, ⊤)`-linear functor of the coefficient module sheaf.** -/
instance sectionsModuleComplexHomology_linear (i : ℕ) :
    Functor.Linear ↥(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))
      (SectionsOver.sectionsModuleComplexFunctor.{u} X.ringCatSheaf ⊤ K ⋙
        HomologicalComplex.homologyFunctor
          (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) (up ℕ) i) :=
  letI := Stacks.DerivedLinear.homologyFunctor_linear
    (R := ↥(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))))
    (D := ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) i
  inferInstance

/-! ### The comparison of the underlying abelian-group-valued functors -/

open Stacks.Cohomology.ModuleComparison in
/-- **Forgetting the module structure commutes with the degree-`i` cohomology of the module-valued
complex of sections of `K`**, naturally in the coefficient module sheaf: forgetting the module
structure is exact. -/
def moduleComplexHomologyForgetIso (i : ℕ) :
    (SectionsOver.sectionsModuleComplexFunctor.{u} X.ringCatSheaf ⊤ K ⋙
          HomologicalComplex.homologyFunctor
            (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) (up ℕ) i) ⋙
        forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) AddCommGrpCat.{u} ≅
      SectionsOver.sectionsModuleComplexFunctor.{u} X.ringCatSheaf ⊤ K ⋙
        ((forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))))
            AddCommGrpCat.{u}).mapHomologicalComplex (up ℕ) ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (up ℕ) i) :=
  Functor.isoWhiskerLeft _ (homologyMapFunctorIso
    (forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))))
      AddCommGrpCat.{u}) i).symm

/-- **The degree-`i` cohomology of the module-valued complex of sections of `K`, with the module
structure forgotten, is the degree-`i` cohomology of the complex of sections of `K` with
coefficients in the underlying abelian sheaf**, naturally in the coefficient module sheaf.  This
is `SectionsOver.sectionsModuleComplexForgetIso` read in cohomology. -/
def moduleComplexHomologyIsoSectionsComplexHomology (i : ℕ) :
    SectionsOver.sectionsModuleComplexFunctor.{u} X.ringCatSheaf ⊤ K ⋙
        ((forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))))
            AddCommGrpCat.{u}).mapHomologicalComplex (up ℕ) ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (up ℕ) i) ≅
      SheafOfModules.toSheaf X.ringCatSheaf ⋙
        (SectionsOver.sectionsComplexFunctor.{u} (Opens.grothendieckTopology ↥X) K ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (up ℕ) i) :=
  Functor.isoWhiskerRight (SectionsOver.sectionsModuleComplexForgetIso.{u} X.ringCatSheaf ⊤ K)
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (up ℕ) i)

open Stacks.Cohomology.ModuleComparison in
/-- **The abelian-group-valued cohomology of a module sheaf on the whole scheme is the
module-valued cohomology with the module structure forgotten**, naturally in the module sheaf.
This is [Stacks, Tag 03FD] followed by [Stacks, Tag 01F1] part (1). -/
def derivedGlobalSectionsForgetIso (i : ℕ) :
    SheafOfModules.toSheaf X.ringCatSheaf ⋙
        (sheafToPresheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u} ⋙
          (evaluation (X.Opens)ᵒᵖ AddCommGrpCat.{u}).obj (op (⊤ : X.Opens))).rightDerived i ≅
      (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived i ⋙
        forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) AddCommGrpCat.{u} :=
  (underlyingSectionsIso X.ringCatSheaf ⊤ i).symm ≪≫
    (rightDerivedEvaluationForgetIso X.ringCatSheaf ⊤ i).symm

/-- **The comparison `H ⁱ(s(-(K))) ⟶ R ⁱΓ(X, -)` of the abelian-group-valued functors underlying
the two module-valued ones.**  It is the comparison of [Stacks, Tag 01GY] in degree `i`,
conjugated by the two identifications above. -/
def cechModuleCohomologyForget (hK : IsHypercovering (Opens.pretopology ↥X) K) (i : ℕ) :
    (SectionsOver.sectionsModuleComplexFunctor.{u} X.ringCatSheaf ⊤ K ⋙
          HomologicalComplex.homologyFunctor
            (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) (up ℕ) i) ⋙
        forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) AddCommGrpCat.{u} ⟶
      (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived i ⋙
        forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) AddCommGrpCat.{u} :=
  (moduleComplexHomologyForgetIso X K i).hom ≫
    (moduleComplexHomologyIsoSectionsComplexHomology X K i).hom ≫
    Functor.whiskerLeft (SheafOfModules.toSheaf X.ringCatSheaf)
      (cechToSheafCohomologyOfEq.{u} (Opens.pretopology ↥X)
        (Opens.pretopology_toGrothendieck ↥X) ⊤ K hK i) ≫
    (derivedGlobalSectionsForgetIso X i).hom

/-! ### Degeneration at a quasi-coherent module -/

open Stacks.Cohomology.ModuleComparison in
/-- **The higher abelian-group-valued cohomology of a quasi-coherent module vanishes on an affine
open.**  This is Serre vanishing, [Stacks, Tag 01XB], transported from the `SheafOfModules`-derived
to the `Sheaf AddCommGrpCat`-derived spelling by [Stacks, Tag 03FD]. -/
theorem isZero_rightDerived_sections_of_isAffineOpen (F : SheafOfModules.{u} X.ringCatSheaf)
    [F.IsQuasicoherent] (V : X.Opens) (hV : IsAffineOpen V) (q : ℕ) (hq : 0 < q) :
    IsZero (((sheafToPresheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u} ⋙
      (evaluation (X.Opens)ᵒᵖ AddCommGrpCat.{u}).obj (op V)).rightDerived q).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)) :=
  (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F V hV q hq).of_iso
    ((underlyingSectionsIso X.ringCatSheaf V q).app F).symm

/-- **The comparison of the underlying abelian-group-valued functors is an isomorphism at a
quasi-coherent module**, when every member of the hypercovering is an affine open. -/
theorem isIso_cechModuleCohomologyForget_app
    (hK : IsHypercovering (Opens.pretopology ↥X) K)
    (haff : ∀ (n : ℕ) (j : (K.obj (op ⦋n⦌)).I), IsAffineOpen ((K.obj (op ⦋n⦌)).obj j).left)
    (i : ℕ) (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] :
    IsIso ((cechModuleCohomologyForget X K hK i).app F) := by
  have h := isIso_cechToSheafCohomologyOfEq_app.{u} (Opens.pretopology ↥X)
    (Opens.pretopology_toGrothendieck ↥X) ⊤ K hK i
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)
    (fun n j q hq ↦ isZero_rightDerived_sections_of_isAffineOpen X F _ (haff n j) q hq)
  dsimp only [cechModuleCohomologyForget, NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

/-! ### The linear comparison -/

/-- **The comparison `H ⁱ(s(-(K))) ⟶ R ⁱΓ(X, -)` of `Γ(X, ⊤)`-module-valued functors.**  Its
components are the components of `cechModuleCohomologyForget`, which are `Γ(X, ⊤)`-linear because
both functors are. -/
def cechModuleCohomology (hK : IsHypercovering (Opens.pretopology ↥X) K) (i : ℕ) :
    SectionsOver.sectionsModuleComplexFunctor.{u} X.ringCatSheaf ⊤ K ⋙
        HomologicalComplex.homologyFunctor
          (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) (up ℕ) i ⟶
      (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived i :=
  Stacks.LinearFromNaturality.lift _ _ (cechModuleCohomologyForget X K hK i)

/-- Forgetting the module structure of `cechModuleCohomology` returns
`cechModuleCohomologyForget`. -/
theorem forget₂_map_cechModuleCohomology_app
    (hK : IsHypercovering (Opens.pretopology ↥X) K) (i : ℕ)
    (F : SheafOfModules.{u} X.ringCatSheaf) :
    (forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) AddCommGrpCat.{u}).map
        ((cechModuleCohomology X K hK i).app F) =
      (cechModuleCohomologyForget X K hK i).app F :=
  rfl

/-- **The linear comparison is an isomorphism at a quasi-coherent module**, when every member of
the hypercovering is an affine open: forgetting the module structure reflects isomorphisms. -/
theorem isIso_cechModuleCohomology_app (hK : IsHypercovering (Opens.pretopology ↥X) K)
    (haff : ∀ (n : ℕ) (j : (K.obj (op ⦋n⦌)).I), IsAffineOpen ((K.obj (op ⦋n⦌)).obj j).left)
    (i : ℕ) (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] :
    IsIso ((cechModuleCohomology X K hK i).app F) := by
  have h := isIso_cechModuleCohomologyForget_app X K hK haff i F
  have : IsIso ((forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))))
      AddCommGrpCat.{u}).map ((cechModuleCohomology X K hK i).app F)) := by
    rw [forget₂_map_cechModuleCohomology_app]
    exact h
  exact isIso_of_reflects_iso _
    (forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) AddCommGrpCat.{u})

/-- **The component of the linear comparison at a quasi-coherent module, as an isomorphism**, with
its source written as the value of the degree-`i` cohomology functor. -/
def cechModuleCohomologyIsoApp (hK : IsHypercovering (Opens.pretopology ↥X) K)
    (haff : ∀ (n : ℕ) (j : (K.obj (op ⦋n⦌)).I), IsAffineOpen ((K.obj (op ⦋n⦌)).obj j).left)
    (i : ℕ) (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] :
    (SectionsOver.sectionsModuleComplexFunctor.{u} X.ringCatSheaf ⊤ K ⋙
          HomologicalComplex.homologyFunctor
            (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) (up ℕ) i).obj F ≅
      ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived i).obj F :=
  haveI := isIso_cechModuleCohomology_app X K hK haff i F
  asIso ((cechModuleCohomology X K hK i).app F)

/-- **The cohomology of the module-valued complex of sections of a hypercovering with affine
members, with quasi-coherent coefficients, is the cohomology of the coefficient module, as
`Γ(X, ⊤)`-modules.**  In degree `i`,

`H ⁱ(s(F(K))) ≅ R ⁱΓ(X, F)`. -/
def sectionsModuleComplexHomologyIso (hK : IsHypercovering (Opens.pretopology ↥X) K)
    (haff : ∀ (n : ℕ) (j : (K.obj (op ⦋n⦌)).I), IsAffineOpen ((K.obj (op ⦋n⦌)).obj j).left)
    (i : ℕ) (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] :
    (SectionsOver.sectionsModuleComplex.{u} X.ringCatSheaf ⊤ K F).homology i ≅
      ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived i).obj F :=
  cechModuleCohomologyIsoApp X K hK haff i F

/-- **The isomorphism of `sectionsModuleComplexHomologyIso`, with the ring of scalars written
`Γ(X, ⊤)`.**  The `RingCat` object `X.ringCatSheaf.obj.obj (op ⊤)` that the module-valued complex
of sections is a complex over and the `CommRingCat` object `Γ(X, ⊤)` have the same underlying
ring, so this is the same isomorphism. -/
def sectionsModuleComplexHomologyIsoGlobalSections
    (hK : IsHypercovering (Opens.pretopology ↥X) K)
    (haff : ∀ (n : ℕ) (j : (K.obj (op ⦋n⦌)).I), IsAffineOpen ((K.obj (op ⦋n⦌)).obj j).left)
    (i : ℕ) (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) (up ℕ) i).obj
        (SectionsOver.sectionsModuleComplex.{u} X.ringCatSheaf ⊤ K F) ≅
      ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived i).obj F :=
  sectionsModuleComplexHomologyIso X K hK haff i F

/-- **The isomorphism of `sectionsModuleComplexHomologyIso` is natural in the coefficient module
over the full subcategory of quasi-coherent modules.** -/
def quasicoherentCechModuleCohomologyIso (hK : IsHypercovering (Opens.pretopology ↥X) K)
    (haff : ∀ (n : ℕ) (j : (K.obj (op ⦋n⦌)).I), IsAffineOpen ((K.obj (op ⦋n⦌)).obj j).left)
    (i : ℕ) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
        (SectionsOver.sectionsModuleComplexFunctor.{u} X.ringCatSheaf ⊤ K ⋙
          HomologicalComplex.homologyFunctor
            (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) (up ℕ) i) ≅
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
        (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived i :=
  haveI : ∀ F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory,
      IsIso ((Functor.whiskerLeft (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι
        (cechModuleCohomology X K hK i)).app F) :=
    fun F ↦ isIso_cechModuleCohomology_app X K hK haff i F.obj
  haveI : IsIso (Functor.whiskerLeft (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι
      (cechModuleCohomology X K hK i)) := NatIso.isIso_of_isIso_app _
  asIso (Functor.whiskerLeft (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι
    (cechModuleCohomology X K hK i))

end Stacks.Cohomology.HypercoveringModules

end
