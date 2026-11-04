module

public import StacksFrontier.AlgebraicGeometry.CechPushforwardComplex.Basic
public import StacksFrontier.AlgebraicGeometry.GenericPointSheaf.ProductSections
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.HypercoveringAbsoluteFactor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EvaluationConservative
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.OpensInf
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SectionsComplexFunctorial

/-!
# The sections of the relative hypercovering complex over an open of the base

Let `f : X ⟶ S` be a morphism of schemes, let `K` be a simplicial object of formal coproducts of
opens of `X` and let `M` be an `𝒪_X`-module.  The complex

`𝓚⁼(K, f, M) = ( ∏_{i ∈ I₀} (U_i)_{,*} M|_{U_i} ⟶ ∏_{i ∈ I₁} (U_i)_{,*} M|_{U_i} ⟶ ⋯ )`

of `𝒪_S`-modules of `StacksFrontier.AlgebraicGeometry.RelativeCechComplex.HypercoveringAllModules`
has, over an open `V` of `S`, the sections

`∏_{i ∈ Iₙ} M(U_i ⊓ f ⁻¹ V)`,

which is the degree-`n` term of the complex of sections of the hypercovering `K ⊓ f ⁻¹ V` of
[Stacks, Tag 0DAZ] with coefficients in the underlying abelian sheaf of `M`. **This file identifies
the two as cochain complexes.**

It is the crux of the relative form of [Stacks, Tag 01GV]: the sections-level resolution statements
for a hypercovering hold for an arbitrary open of `X` as the base object, with no affineness of the
members and no quasi-coherence of the coefficients, and this identification is what lets them be
read as statements about the complex of `𝒪_S`-modules `𝓚⁼(K, f, M)`.

## Main definitions

* `sectionsAG`:  the sections of an `𝒪_X`-module over an open set, as an abelian group.
* `abPresheafAG`:  the underlying abelian presheaf of an `𝒪_X`-module.
* `cechDiagramSectionsIso`:  the sections over an open `W` of the Čech diagram of
  [Stacks, Tag 02FU] are the sections of `M` on the intersections with `W`.
* `pushforwardPresheafAllSectionsIso`:  **the sections over `V` of the coefficient presheaf of
  [Stacks, Tag 01XN] are the sections of `M` on the intersections with `f ⁻¹ V`.**
* `hypercoveringSectionsComplexIso`:  **the sections over `V` of the complex `𝓚⁼(K, f, M)` are the
  complex of sections of the hypercovering `K ⊓ f ⁻¹ V` with coefficients in `M`.**

## Main results

* `pushforward_comp_sectionsAG`: the sections over `V` of a direct image along `f` are the sections
  over `f ⁻¹ V`.
* `pushforwardPresheafAll_comp_sectionsAG`:  the two factorisations composed.
* `abPresheafAG_map_eq` and `thinRestrictionIso`:  the lattice of opens is a thin category, so a
  restriction map between two equal open sets is an isomorphism and every square built from
  restriction maps commutes.

## Implementation notes

`sectionsAG` is built on `Stacks.AlgebraicGeometry.GenericPointSheaf.sectionsFunctor` rather than
directly on `CategoryTheory.SheafOfModules.evaluation`:  `AlgebraicGeometry.Scheme.Modules` is a
`def`, so `Mathlib`'s instance for the preservation of products by evaluation is not found at the
scheme level, and that file supplies it.  Additivity needs the same treatment and is supplied here,
again as an explicit term.

The equality `(pushforwardPresheafAll f).obj M ⋙ sectionsAG S V = (absCechPresheafAll X).obj M ⋙
sectionsAG X (f ⁻¹ V)` holds by definition, but the single `rfl` for it exhausts the kernel's
budget; it is assembled instead from `pushforwardPresheafAll_obj_eq`, associativity of functor
composition and `pushforward_comp_sectionsAG`, each of which checks immediately.

The universe enlargement of [Stacks, Tag 02FU] survives inside the Čech diagram, so the sections of
the diagram over `W` at the open `U` are a `ULift` of `M(W ⊓ U)`.  It is removed by
`Stacks.CechSiteChange.moduleUniverseLiftOpensIso`, whose component at `M` is a morphism of module
sheaves and hence natural in the open set — which is exactly the naturality the comparison needs.
The remaining discrepancy is the order of the intersection, `W ⊓ U` against `U ⊓ W`; the lattice of
opens is thin, so the comparison is a restriction map and the square it sits in commutes by
`Subsingleton.elim`.

## References

* [Stacks Project, Tag 01GV](https://stacks.math.columbia.edu/tag/01GV)
* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 01XN](https://stacks.math.columbia.edu/tag/01XN)
* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
* [Stacks Project, Tag 0DAZ](https://stacks.math.columbia.edu/tag/0DAZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.GenericPointSheaf
open Stacks.CategoryTheory.Hypercovering
open Stacks.CechSiteChange

universe u

namespace Stacks.AlgebraicGeometry.UniversalPushforward

variable {X S : Scheme.{u}}

/-! ### Sections as abelian groups -/

/-- **The underlying abelian presheaf of an `𝒪_X`-module**, functorially. -/
noncomputable abbrev abPresheafAG (X : Scheme.{u}) :
    X.Modules ⥤ ((X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  SheafOfModules.toSheaf X.ringCatSheaf ⋙
    sheafToPresheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}

/-- **The sections of an `𝒪_X`-module over an open set, as an abelian group**, functorially. -/
noncomputable abbrev sectionsAG (X : Scheme.{u}) (V : X.Opens) : X.Modules ⥤ AddCommGrpCat.{u} :=
  sectionsFunctor X V ⋙
    forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op V))) AddCommGrpCat.{u}

/-- Module-valued sections over an open set are an additive functor of the module sheaf.  This is
`Stacks.SheafOfModulesEvaluation.evaluation_additive`, which typeclass search does not find at the
scheme level because `AlgebraicGeometry.Scheme.Modules` is a `def`. -/
instance sectionsFunctor_additive (V : X.Opens) : (sectionsFunctor X V).Additive :=
  Stacks.SheafOfModulesEvaluation.evaluation_additive.{u, u, u, u} X.ringCatSheaf (op V)

/-- **The sections over `V` of a direct image along `f` are the sections over `f ⁻¹ V`.** -/
theorem pushforward_comp_sectionsAG (f : X ⟶ S) (V : S.Opens) :
    pushforward f ⋙ sectionsAG S V = sectionsAG X (f ⁻¹ᵁ V) :=
  rfl

/-- **The sections over an open `V` of `S` of the coefficient presheaf of [Stacks, Tag 01XN] are
the sections over `f ⁻¹ V` of the absolute coefficient presheaf.** -/
theorem pushforwardPresheafAll_comp_sectionsAG (f : X ⟶ S) (M : X.Modules) (V : S.Opens) :
    (pushforwardPresheafAll f).obj M ⋙ sectionsAG S V =
      (absCechPresheafAll X).obj M ⋙ sectionsAG X (f ⁻¹ᵁ V) :=
  (congrArg (fun P ↦ P ⋙ sectionsAG S V) (pushforwardPresheafAll_obj_eq f M)).trans
    (congrArg (fun H ↦ (absCechPresheafAll X).obj M ⋙ H) (pushforward_comp_sectionsAG f V))

/-! ### Restriction maps in the thin lattice of opens -/

/-- Two restriction maps of an abelian presheaf on the opens of a scheme between the same pair of
open sets agree:  the lattice of opens is a thin category. -/
theorem abPresheafAG_map_eq (P : (X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u}) {A B : (X.Opens)ᵒᵖ}
    (r r' : A ⟶ B) : P.map r = P.map r' :=
  congrArg P.map (Subsingleton.elim r r')

/-- **The restriction map of an abelian presheaf between two equal open sets is an isomorphism**,
with the reverse restriction map as its inverse. -/
noncomputable def thinRestrictionIso (P : (X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u}) {A B : X.Opens}
    (hBA : B ≤ A) (hAB : A ≤ B) : P.obj (op A) ≅ P.obj (op B) where
  hom := P.map (homOfLE hBA).op
  inv := P.map (homOfLE hAB).op
  hom_inv_id :=
    ((P.map_comp _ _).symm.trans (abPresheafAG_map_eq P _ (𝟙 (op A)))).trans (P.map_id _)
  inv_hom_id :=
    ((P.map_comp _ _).symm.trans (abPresheafAG_map_eq P _ (𝟙 (op B)))).trans (P.map_id _)

/-! ### The sections of the Čech diagram -/

/-- The sections over `W` of the Čech diagram at `U` are the sections over `W ⊓ U` of the universe
enlargement of `M`. -/
theorem sectionsAG_cechDiagramOpens_obj (M : X.Modules) (U W : X.Opens) :
    (sectionsAG X W).obj (((cechDiagramOpens X).obj M).obj (op U)) =
      ((abPresheafAG X).obj ((moduleUniverseLiftOpens X).obj M)).obj (op (W ⊓ U)) :=
  rfl

/-- The restriction maps in the open set of the sections over `W` of the Čech diagram are the
restriction maps of the universe enlargement of `M` along `W ⊓ U' ≤ W ⊓ U`. -/
theorem sectionsAG_cechDiagramOpens_map (M : X.Modules) (W : X.Opens)
    {U U' : (X.Opens)ᵒᵖ} (g : U ⟶ U') :
    (sectionsAG X W).map (((cechDiagramOpens X).obj M).map g) =
      ((abPresheafAG X).obj ((moduleUniverseLiftOpens X).obj M)).map
        (homOfLE (inf_le_inf_left W (leOfHom g.unop))).op :=
  rfl

/-- The sections over `W` of the Čech diagram at `U`, compared with the sections of `M` on `U ⊓ W`:
the universe enlargement is removed and the intersection reordered. -/
noncomputable def cechDiagramSectionsIsoApp (X : Scheme.{u}) (M : X.Modules) (W : X.Opens)
    (U : (X.Opens)ᵒᵖ) :
    ((abPresheafAG X).obj ((moduleUniverseLiftOpens X).obj M)).obj (op (W ⊓ U.unop)) ≅
      ((abPresheafAG X).obj M).obj (op (U.unop ⊓ W)) :=
  (((abPresheafAG X).mapIso ((moduleUniverseLiftOpensIso X).app M)).app
      (op (W ⊓ U.unop))).trans
    (thinRestrictionIso ((abPresheafAG X).obj M) (le_of_eq (inf_comm U.unop W))
      (le_of_eq (inf_comm W U.unop)))

/-- The comparison of `cechDiagramSectionsIsoApp`, written out:  the universe enlargement removed,
then a restriction map. -/
theorem cechDiagramSectionsIsoApp_hom (X : Scheme.{u}) (M : X.Modules) (W : X.Opens)
    (U : (X.Opens)ᵒᵖ) :
    (cechDiagramSectionsIsoApp X M W U).hom =
      ((abPresheafAG X).map ((moduleUniverseLiftOpensIso X).hom.app M)).app
          (op (W ⊓ U.unop)) ≫
        ((abPresheafAG X).obj M).map (homOfLE (le_of_eq (inf_comm U.unop W))).op :=
  rfl

/-- **Removing the universe enlargement of [Stacks, Tag 02FU] is natural in the open set**:  the
comparison is a morphism of module sheaves, so it commutes with the restriction maps.  The two
spellings `M` and `(𝟭 X.Modules).obj M` of its target are definitionally equal, and the statement
here pins the first of them. -/
theorem moduleUniverseLiftOpensIso_app_naturality (X : Scheme.{u}) (M : X.Modules)
    {A B : (X.Opens)ᵒᵖ} (r : A ⟶ B) :
    ((abPresheafAG X).obj ((moduleUniverseLiftOpens X).obj M)).map r ≫
        ((abPresheafAG X).map ((moduleUniverseLiftOpensIso X).hom.app M)).app B =
      ((abPresheafAG X).map ((moduleUniverseLiftOpensIso X).hom.app M)).app A ≫
        ((abPresheafAG X).obj M).map r :=
  ((abPresheafAG X).map ((moduleUniverseLiftOpensIso X).hom.app M)).naturality r

/-- `moduleUniverseLiftOpensIso_app_naturality` with a further morphism appended. -/
theorem moduleUniverseLiftOpensIso_app_naturality_assoc (X : Scheme.{u}) (M : X.Modules)
    {A B : (X.Opens)ᵒᵖ} (r : A ⟶ B) {Z : AddCommGrpCat.{u}}
    (h : ((abPresheafAG X).obj M).obj B ⟶ Z) :
    ((abPresheafAG X).obj ((moduleUniverseLiftOpens X).obj M)).map r ≫
        (((abPresheafAG X).map ((moduleUniverseLiftOpensIso X).hom.app M)).app B ≫ h) =
      ((abPresheafAG X).map ((moduleUniverseLiftOpensIso X).hom.app M)).app A ≫
        (((abPresheafAG X).obj M).map r ≫ h) := by
  rw [← Category.assoc, ← Category.assoc, moduleUniverseLiftOpensIso_app_naturality]

/-- The naturality in the open set of the comparison of `cechDiagramSectionsIsoApp`. -/
theorem cechDiagramSectionsIsoApp_naturality (X : Scheme.{u}) (M : X.Modules) (W : X.Opens)
    {U U' : (X.Opens)ᵒᵖ} (g : U ⟶ U') :
    ((abPresheafAG X).obj ((moduleUniverseLiftOpens X).obj M)).map
          (homOfLE (inf_le_inf_left W (leOfHom g.unop))).op ≫
        (cechDiagramSectionsIsoApp X M W U').hom =
      (cechDiagramSectionsIsoApp X M W U).hom ≫
        ((abPresheafAG X).obj M).map ((opensInf W).op.map g) := by
  simp only [cechDiagramSectionsIsoApp_hom]
  rw [moduleUniverseLiftOpensIso_app_naturality_assoc,
    ← ((abPresheafAG X).obj M).map_comp, Category.assoc]
  refine congrArg (fun z ↦ ((abPresheafAG X).map
      ((moduleUniverseLiftOpensIso X).hom.app M)).app (op (W ⊓ U.unop)) ≫ z) ?_
  exact (abPresheafAG_map_eq ((abPresheafAG X).obj M) _
      ((homOfLE (le_of_eq (inf_comm U.unop W))).op ≫ (opensInf W).op.map g)).trans
    (((abPresheafAG X).obj M).map_comp _ _)

/-- **The sections over an open `W` of the Čech diagram of [Stacks, Tag 02FU] are the sections of
`M` on the intersections with `W`.** -/
noncomputable def cechDiagramSectionsIso (X : Scheme.{u}) (M : X.Modules) (W : X.Opens) :
    (cechDiagramOpens X).obj M ⋙ sectionsAG X W ≅
      (opensInf W).op ⋙ (abPresheafAG X).obj M :=
  NatIso.ofComponents (cechDiagramSectionsIsoApp X M W) (fun {U U'} g ↦ by
    change (sectionsAG X W).map (((cechDiagramOpens X).obj M).map g) ≫
        (cechDiagramSectionsIsoApp X M W U').hom =
      (cechDiagramSectionsIsoApp X M W U).hom ≫
        ((abPresheafAG X).obj M).map ((opensInf W).op.map g)
    rw [sectionsAG_cechDiagramOpens_map M W g]
    exact cechDiagramSectionsIsoApp_naturality X M W g)

/-! ### The sections of the relative coefficient presheaf -/

/-- **The sections over an open `V` of `S` of the coefficient presheaf of [Stacks, Tag 01XN] are
the sections of `M` on the intersections with `f ⁻¹ V`.** -/
noncomputable def pushforwardPresheafAllSectionsIso (f : X ⟶ S) (M : X.Modules) (V : S.Opens) :
    (pushforwardPresheafAll f).obj M ⋙ sectionsAG S V ≅
      (Over.forget (⊤ : Opens X)).op ⋙ (opensInf (f ⁻¹ᵁ V)).op ⋙ (abPresheafAG X).obj M :=
  (eqToIso (pushforwardPresheafAll_comp_sectionsAG f M V)).trans
    ((Functor.isoWhiskerRight (absCechPresheafAllObjIso X M)
        (sectionsAG X (f ⁻¹ᵁ V))).trans
      (Functor.isoWhiskerLeft (Over.forget (⊤ : Opens X)).op
        (cechDiagramSectionsIso X M (f ⁻¹ᵁ V))))

/-! ### The sections of the complex -/

/-- **The sections over an open `V` of `S` of the complex `𝓚⁼(K, f, M)` of [Stacks, Tag 01XN] are
the complex of sections of the hypercovering `K ⊓ f ⁻¹ V` of [Stacks, Tag 0DAZ] with coefficients
in the underlying abelian sheaf of `M`.**

The passage from the simplicial object `K` of opens of `X` to its degreewise intersection with
`f ⁻¹ V` is
`Stacks.AlgebraicGeometry.HypercoveringBaseChange.cochainComplexFunctor_mapFormalCoproduct_obj` at
the functor `(· ⊓ f ⁻¹ V)`: reindexing the simplicial object and restricting the coefficients give
the same complex, on the nose. -/
noncomputable def hypercoveringSectionsComplexIso (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X)))) (M : X.Modules)
    (V : S.Opens) :
    ((sectionsAG S V).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((FormalCoproduct.cochainComplexFunctor.{u} K).obj ((pushforwardPresheafAll f).obj M)) ≅
      SectionsOver.sectionsComplex (Opens.grothendieckTopology ↥X)
        (K ⋙ mapFormalCoproduct.{u} (Over.post (opensInf (f ⁻¹ᵁ V)) (X := (⊤ : Opens X))))
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) :=
  ((Stacks.CechPushforward.cochainComplexFunctorCompMapHomologicalComplexIso.{u}
        (sectionsAG S V) K).app ((pushforwardPresheafAll f).obj M)).trans
    ((FormalCoproduct.cochainComplexFunctor.{u} K).mapIso
      (pushforwardPresheafAllSectionsIso f M V))

end Stacks.AlgebraicGeometry.UniversalPushforward

end
