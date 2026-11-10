module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Topology.Sheaves.Module
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact
import StacksCore.Tactic.StacksAttribute

/-!
# The internal Hom complex of complexes of modules on a ringed space

Let `(X, O_X)` be a ringed space and let `K` and `I` be cochain complexes of `O_X`-modules.
The *internal Hom complex* `SheafHom^•(K, I)` is the complex of `O_X`-modules whose sections
over an open `U` are the ordinary Hom complex `Hom^•(K|_U, I|_U)` of the restricted complexes.
Those section complexes, together with their compatibility with further restriction and with
the action of `O_X(U)`, determine the complex up to canonical isomorphism, and they are what
every statement about it uses. This file fixes that data as the structure
`Stacks.SheafOfModules.SheafHomComplex`, describes the maps induced by morphisms in the two
variables, and bundles a choice of the complexes with its induced maps and their identity and
composition laws.

No complex is constructed here: a `SheafHomComplex` is a *realization*, and this file fixes only
the vocabulary. A realization exists for every pair of complexes —
`Stacks.SheafOfModules.sheafHomComplex` ([Stacks, Tag 0A8K], in the file
`StacksFrontier/Topology/Sheaves/Cohomology/HomComplexAndStrictPerfection/`
`InternalHomComplexQuasiIso.lean`) — so a statement about the internal Hom complex can be made
here for an arbitrary realization and then instantiated at that construction, holding with no
realization hypothesis. That is what
`Stacks.SheafOfModules.sheafHomComplexHomologyEquiv` ([Stacks, Tag 0A8L]) does; the corresponding
statement for [Stacks, Tag 0A8R] is still carried only for an arbitrary realization.

## Main definitions

* `Stacks.SheafOfModules.StructureSheafModules`: the category of `O_X`-modules, i.e. of
  sheaves of modules over the structure sheaf of rings `structureSheaf Rc` of a sheaf `Rc` of
  commutative rings on a space.
* `Stacks.SheafOfModules.restrictComplex`: restriction of a complex of `O_X`-modules to the
  slice site over an open `U`, degreewise.
* `Stacks.SheafOfModules.sectionAbelianFunctor` and
  `Stacks.SheafOfModules.sectionComplex`: sections over `U` of an `O_X`-module as an abelian
  group, and the resulting complex of abelian groups of a complex of `O_X`-modules.
* `Stacks.SheafOfModules.SheafHomComplex`: a realization of the internal Hom complex,
  characterized by its complexes of sections on every open.
* `Stacks.SheafOfModules.SheafHomComplex.IsInducedMap`: the property of a morphism of
  realizations of being the map induced by morphisms in the two variables, namely sending a
  local cochain `z` to `g ≫ z ≫ f` on every open.
* `Stacks.SheafOfModules.SheafHomComplexConstruction`: a realization for every pair of
  complexes, bundled with its induced maps and their identity and composition laws.

## Implementation notes

Restriction to an open is `SheafOfModules.overFunctor`, i.e. restriction to the slice site
`Opens X / U`, not restriction to the open subspace `U`; the two are identified by
`Opens.sheafOfModulesEquivOver`. The slice site is the form in which a section of the internal
Hom over `U` is literally a morphism of sheaves of modules, so it is the form in which
`sectionsIso` can be stated without inserting a comparison functor.

The two naturality fields of `SheafHomComplex` are stated on elements rather than as commuting
squares of complexes. A section of the internal Hom over `U` is a cochain of morphisms on the
slice site, so comparing its restriction to `V` with the restriction of the cochain means
comparing the components at an object `W ≤ V` of `Opens X / V` with the components at the same
`W`, viewed in `Opens X / U`; writing that as a square would require naming the comparison of
the two slice sites, which is exactly what evaluating at `W` avoids.

## References

* [Stacks Project, Tag 0A8S](https://stacks.math.columbia.edu/tag/0A8S)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

/-- The category of modules over the underlying ring sheaf of a commutative
ringed space. -/
abbrev StructureSheafModules := SheafOfModules.{u} (structureSheaf Rc)

/-- Restriction of sheaves of modules to the slice site over `U` preserves zero morphisms. -/
noncomputable local instance (U : Opens X) :
    (SheafOfModules.overFunctor (structureSheaf Rc) U).PreservesZeroMorphisms where
  map_zero {A B} := by
    ext V x
    rfl

/-- Taking sections over `U`, as an abelian group, preserves zero morphisms. -/
noncomputable local instance (U : Opens X) :
    ((SheafOfModules.evaluation (structureSheaf Rc) (op U)) ⋙
      forget₂ (ModuleCat.{u} ((structureSheaf Rc).obj.obj (op U)))
        AddCommGrpCat.{u}).PreservesZeroMorphisms where
  map_zero {A B} := by
    ext x
    rfl

/-- Restriction of a complex of modules on `X` to the slice site over an open
subset `U`. -/
noncomputable abbrev restrictComplex
    (K : CochainComplex (StructureSheafModules Rc) ℤ) (U : Opens X) :
    CochainComplex (SheafOfModules.{u} ((structureSheaf Rc).over U)) ℤ :=
  ((SheafOfModules.overFunctor (structureSheaf Rc) U).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

/-- The functor sending a sheaf of modules to its abelian group of sections over `U`. -/
noncomputable abbrev sectionAbelianFunctor (U : Opens X) :
    SheafOfModules.{u} (structureSheaf Rc) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.evaluation (structureSheaf Rc) (op U) ⋙
    forget₂ (ModuleCat.{u} ((structureSheaf Rc).obj.obj (op U))) AddCommGrpCat.{u}

/-- The complex of abelian groups of sections over `U` of a complex of sheaves of modules. -/
noncomputable abbrev sectionComplex
    (K : CochainComplex (StructureSheafModules Rc) ℤ) (U : Opens X) :
    CochainComplex AddCommGrpCat.{u} ℤ :=
  (((SheafOfModules.evaluation (structureSheaf Rc) (op U)) ⋙
      forget₂ (ModuleCat.{u} ((structureSheaf Rc).obj.obj (op U)))
        AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- A realization of the internal sheaf-Hom complex
`SheafHom•(K, I)`.  Its sections over `U` are the ordinary Hom complex from
`K|_U` to `I|_U`; the last two fields express compatibility with restriction
and with the action of the structure sheaf. -/
structure SheafHomComplex (K I : CochainComplex (StructureSheafModules Rc) ℤ) where
  /-- The underlying complex of sheaves of modules. -/
  obj : CochainComplex (StructureSheafModules Rc) ℤ
  /-- The canonical identification of sections with the Hom complex of the
  restrictions. -/
  sectionsIso : ∀ U : Opens X,
    sectionComplex Rc obj U ≅ (restrictComplex Rc K U).HomComplex (restrictComplex Rc I U)
  /-- The section identifications commute with restriction to smaller opens. -/
  restrict_natural : ∀ {U V : Opens X} (hVU : V ≤ U) (n p q : ℤ)
      (hpq : p + n = q) (s : (obj.X n).val.obj (op U))
      {W : Opens X} (hWV : W ≤ V) (x : (K.X p).val.obj (op W)),
    (((AddCommGrpCat.Hom.hom ((sectionsIso U).hom.f n) s).v p q hpq).val.app
        (op (Over.mk (homOfLE (le_trans hWV hVU)))) x) =
      (((AddCommGrpCat.Hom.hom ((sectionsIso V).hom.f n)
        ((obj.X n).val.map (homOfLE hVU).op s)).v p q hpq).val.app
          (op (Over.mk (homOfLE hWV))) x)
  /-- The section identifications respect scalar multiplication by local
  sections of the structure sheaf. -/
  smul_natural : ∀ (U : Opens X) (r : (structureSheaf Rc).obj.obj (op U))
      (n p q : ℤ) (hpq : p + n = q) (s : (obj.X n).val.obj (op U))
      {W : Opens X} (hWU : W ≤ U) (x : (K.X p).val.obj (op W)),
    (((AddCommGrpCat.Hom.hom ((sectionsIso U).hom.f n) (r • s)).v p q hpq).val.app
        (op (Over.mk (homOfLE hWU))) x) =
      ((structureSheaf Rc).obj.map (homOfLE hWU).op r) •
        (show (I.X q).val.obj (op W) from
          (((AddCommGrpCat.Hom.hom ((sectionsIso U).hom.f n) s).v p q hpq).val.app
            (op (Over.mk (homOfLE hWU))) x))

namespace SheafHomComplex

/-- A morphism between internal sheaf-Hom complexes is the map induced by
`g : K' ⟶ K` and `f : I' ⟶ I` when, on every open subset, it sends a
cochain `z` to the cochain with components `g ≫ z ≫ f`. -/
def IsInducedMap {K K' I I' : CochainComplex (StructureSheafModules Rc) ℤ}
    (g : K' ⟶ K) (f : I' ⟶ I)
    (H : SheafHomComplex Rc K I') (H' : SheafHomComplex Rc K' I)
    (h : H.obj ⟶ H'.obj) : Prop :=
  ∀ (U : Opens X) (n p q : ℤ) (hpq : p + n = q)
    (s : (H.obj.X n).val.obj (op U)),
    (AddCommGrpCat.Hom.hom ((H'.sectionsIso U).hom.f n)
      ((h.f n).val.app (op U) s)).v p q hpq =
      (g.f p).over U ≫
        (AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n) s).v p q hpq ≫
          (f.f q).over U

end SheafHomComplex

/-- A coherent construction of the internal sheaf-Hom complex.  Besides the
sectionwise realization, this bundles its contravariant functoriality in the
first variable, covariant functoriality in the second variable, and the
identity and composition laws for the induced maps. -/
structure SheafHomComplexConstruction where
  /-- The internal Hom complex attached to a pair of complexes. -/
  complex : (K I : CochainComplex (StructureSheafModules Rc) ℤ) → SheafHomComplex Rc K I
  /-- Simultaneous precomposition and postcomposition on internal Hom complexes. -/
  map : {K K' I I' : CochainComplex (StructureSheafModules Rc) ℤ} →
    (K' ⟶ K) → (I' ⟶ I) → ((complex K I').obj ⟶ (complex K' I).obj)
  /-- On sections, `map g f` sends a cochain `z` to `g ≫ z ≫ f`. -/
  map_isInduced : ∀ {K K' I I' : CochainComplex (StructureSheafModules Rc) ℤ}
    (g : K' ⟶ K) (f : I' ⟶ I),
    SheafHomComplex.IsInducedMap Rc g f (complex K I') (complex K' I) (map g f)
  /-- The map induced by two identity morphisms is the identity. -/
  map_id : ∀ (K I : CochainComplex (StructureSheafModules Rc) ℤ),
    map (𝟙 K) (𝟙 I) = 𝟙 (complex K I).obj
  /-- Induced maps respect simultaneous composition in the two variables. -/
  map_comp : ∀ {K₀ K₁ K₂ I₀ I₁ I₂ : CochainComplex (StructureSheafModules Rc) ℤ}
    (g₁ : K₁ ⟶ K₀) (g₂ : K₂ ⟶ K₁) (f₁ : I₀ ⟶ I₁) (f₂ : I₁ ⟶ I₂),
    map g₁ f₁ ≫ map g₂ f₂ = map (g₂ ≫ g₁) (f₁ ≫ f₂)

end Stacks.SheafOfModules
