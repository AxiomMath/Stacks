module

public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sheaves.Module

/-!
# Restriction of free sheaves of modules, and pointwise finite local freeness

Restricting a free sheaf of modules to an open subscheme gives a free sheaf of modules on the
same index set, because restriction is a left adjoint and a free sheaf is a coproduct of copies
of the structure sheaf. The same argument applies to the equivalence between modules over the
slice sheaf of rings and modules on the open subscheme.

This is what turns the class `Stacks.FiniteLocallyFree.IsFiniteLocallyFree`, whose local data
lives over the slice sheaves of rings, into the pointwise statement
`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree`, which says that every point has an open
neighbourhood on which the restricted module is free of finite rank.

## Main definitions

* `SheafOfModules.freeIsoOfUnitIso`: a coproduct-preserving functor between categories of sheaves
  of modules which carries the structure sheaf to the structure sheaf carries free sheaves to
  free sheaves.
* `AlgebraicGeometry.Scheme.Modules.restrictFunctorObjFree`: restriction along an open immersion
  preserves free sheaves of modules.
* `AlgebraicGeometry.Scheme.Modules.restrictFreeOfLE`: a module which restricts to a free module
  on an open restricts to a free module on every smaller open.
* `AlgebraicGeometry.Scheme.Modules.overEquivFunctorObjFree`: the equivalence
  `AlgebraicGeometry.Scheme.Modules.overEquiv` preserves free sheaves of modules.
* `Stacks.Sheaves.RingedPoint.restrictScalarsObjFreeIso`: restriction of scalars along an
  isomorphism of sheaves of rings preserves free sheaves of modules.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFree`: a finite locally
  free sheaf of modules on a scheme is, around every point, isomorphic to a free sheaf on a
  finite index set.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def`, not an abbreviation, and carries its own
`Category` instance; that instance is only definitionally the one on `SheafOfModules` after
delta-unfolding, so instance *synthesis* cannot see through it. Consequently the preservation
hypothesis of `SheafOfModules.freeIsoOfUnitIso` is an explicit argument rather than an instance
argument: at the use sites it is supplied by `inferInstanceAs` stated in the `Scheme.Modules`
vocabulary, which is checked against the `SheafOfModules` vocabulary by unification rather than
by instance search.

Mathlib's `TopologicalSpace.Opens.coversTop_iff` already identifies covering families for
`TopologicalSpace.Opens.grothendieckTopology` with open covers, and
`TopologicalSpace.IsOpenCover` is by definition `iSup U = ⊤`; so no separate bridge between
`CategoryTheory.GrothendieckTopology.CoversTop` and suprema of opens is needed.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace SheafOfModules

/-- **A coproduct-preserving functor which fixes the structure sheaf fixes free sheaves.**
`SheafOfModules.free I` is the coproduct of `I` copies of `SheafOfModules.unit`, so an
isomorphism `G.obj (unit R₁) ≅ unit R₂` together with preservation of `I`-indexed coproducts
gives `G.obj (free I) ≅ free I`. -/
def freeIsoOfUnitIso {C₁ : Type*} [Category* C₁] {J₁ : GrothendieckTopology C₁}
    {C₂ : Type*} [Category* C₂] {J₂ : GrothendieckTopology C₂}
    {R₁ : Sheaf J₁ RingCat.{u}} {R₂ : Sheaf J₂ RingCat.{u}}
    [HasWeakSheafify J₁ AddCommGrpCat.{u}] [J₁.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J₂ AddCommGrpCat.{u}] [J₂.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (G : SheafOfModules.{u} R₁ ⥤ SheafOfModules.{u} R₂)
    (e : G.obj (unit R₁) ≅ unit R₂) (I : Type u)
    (hG : PreservesColimitsOfShape (Discrete I) G) :
    G.obj (free I) ≅ free (R := R₂) I :=
  letI := hG
  letI : HasCoproducts.{u} (PresheafOfModules.{u} R₁.obj) := fun _ =>
    PresheafOfModules.hasColimitsOfShape _ _
  letI : HasCoproducts.{u} (PresheafOfModules.{u} R₂.obj) := fun _ =>
    PresheafOfModules.hasColimitsOfShape _ _
  letI : HasCoproducts.{u} (SheafOfModules.{u} R₁) := fun _ =>
    SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _
  letI : HasCoproducts.{u} (SheafOfModules.{u} R₂) := fun _ =>
    SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _
  letI : PreservesColimit (Discrete.functor (fun _ : I => unit R₁)) G :=
    PreservesColimitsOfShape.preservesColimit
  (PreservesCoproduct.iso G (fun _ : I => unit R₁)).trans (Sigma.mapIso (fun _ => e))

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- **Restriction along an open immersion preserves free sheaves of modules.** Restriction is a
left adjoint, hence preserves coproducts, and it carries the structure sheaf to the structure
sheaf by `AlgebraicGeometry.Scheme.Modules.restrictUnitIso`. -/
def restrictFunctorObjFree {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (I : Type u) :
    (Scheme.Modules.restrictFunctor f).obj (SheafOfModules.free I) ≅
      SheafOfModules.free (R := X.ringCatSheaf) I :=
  SheafOfModules.freeIsoOfUnitIso (Scheme.Modules.restrictFunctor f)
    (Scheme.Modules.restrictUnitIso f) I
    (inferInstanceAs (PreservesColimitsOfShape (Discrete I) (Scheme.Modules.restrictFunctor f)))

/-- **A module which is free on an open stays free on a smaller open.** The inclusion of the
smaller open factors through the larger one, so restriction to the smaller open is restriction
along that factorisation, and restriction preserves free sheaves by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorObjFree`. -/
def restrictFreeOfLE {X : Scheme.{u}} {U V : X.Opens} (hle : U ≤ V) (F : X.Modules)
    (I : Type u) (e : F.restrict V.ι ≅ SheafOfModules.free I) :
    F.restrict U.ι ≅ SheafOfModules.free (R := (U : Scheme.{u}).ringCatSheaf) I :=
  (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hle).symm).app F ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE hle) V.ι).app F ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE hle)).mapIso e ≪≫
    Scheme.Modules.restrictFunctorObjFree (X.homOfLE hle) I

/-- **Modules over the slice sheaf of rings are modules on the open subscheme, compatibly with
free sheaves.** The equivalence `AlgebraicGeometry.Scheme.Modules.overEquiv` preserves
coproducts and carries the structure sheaf to the structure sheaf by
`TopologicalSpace.Opens.sheafOfModulesEquivOverUnit`, which is the identity. -/
def overEquivFunctorObjFree {X : Scheme.{u}} (U : X.Opens) (I : Type u) :
    (Scheme.Modules.overEquiv U).functor.obj (SheafOfModules.free I) ≅
      SheafOfModules.free (R := (U : Scheme.{u}).ringCatSheaf) I :=
  SheafOfModules.freeIsoOfUnitIso (Scheme.Modules.overEquiv U).functor
    (Opens.sheafOfModulesEquivOverUnit U X.ringCatSheaf) I
    (inferInstanceAs
      (PreservesColimitsOfShape (Discrete I) (Scheme.Modules.overEquiv U).functor))

/-- **Finite local freeness is pointwise local freeness of finite rank.** The local generators
data of `Stacks.FiniteLocallyFree.IsFiniteLocallyFree` covers the terminal open, so every point
lies in one of its members `V`; over `V` the generating sections exhibit the module over the
slice sheaf of rings as free on a finite index set, and
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv` together with
`AlgebraicGeometry.Scheme.Modules.overEquivFunctorObjFree` transports that to the restriction of
the module to the open subscheme `V`. -/
theorem isFiniteLocallyFree_of_isFiniteLocallyFree {X : Scheme.{u}} (F : X.Modules)
    [h : Stacks.FiniteLocallyFree.IsFiniteLocallyFree (R := X.ringCatSheaf) F] :
    Scheme.Modules.IsFiniteLocallyFree F := by
  obtain ⟨q, hfree, hfin⟩ := h.exists_isFiniteLocallyFreeData
  intro x
  have hcov : iSup q.X = ⊤ := (Opens.coversTop_iff _ q.X).mp q.coversTop
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcov ▸ Opens.mem_top x)
  refine ⟨q.X i, hi, (q.generators i).I, (hfin.isFiniteType i).finite, ⟨?_⟩⟩
  have : IsIso (q.generators i).π := hfree.isIso i
  exact ((Scheme.Modules.overFunctorEquiv (q.X i)).app F).symm ≪≫
    (Scheme.Modules.overEquiv (q.X i)).functor.mapIso (asIso (q.generators i).π).symm ≪≫
    overEquivFunctorObjFree (q.X i) _

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.Sheaves.RingedPoint

/-- **Restriction of scalars along an isomorphism of sheaves of rings carries free sheaves of
modules to free sheaves of modules.** `SheafOfModules.free I` is the coproduct of `I` copies of
the structure sheaf, restriction of scalars along an isomorphism is an equivalence and therefore
preserves coproducts, and it fixes the structure sheaf by
`Stacks.Sheaves.RingedPoint.restrictScalarsObjUnitIso`.

This is the `restrictScalars` analogue of
`AlgebraicGeometry.Scheme.Modules.overEquivFunctorObjFree`, and the two compose to the transport
of freeness across a change of *both* the site and the sheaf of rings — which is the shape in
which an open subscheme of a scheme carrying a sheaf of rings other than its structure sheaf
presents itself. -/
def restrictScalarsObjFreeIso {T : Type u} [Category* T] {J : GrothendieckTopology T}
    {R S : Sheaf J RingCat.{u}} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] (e : R ≅ S) (I : Type u) :
    (restrictScalarsEquivalenceOfIso e).functor.obj (SheafOfModules.free I) ≅
      SheafOfModules.free (R := S) I :=
  SheafOfModules.freeIsoOfUnitIso (restrictScalarsEquivalenceOfIso e).functor
    (restrictScalarsObjUnitIso e) I
    (inferInstanceAs
      (Limits.PreservesColimitsOfShape (Discrete I) (restrictScalarsEquivalenceOfIso e).functor))

end Stacks.Sheaves.RingedPoint

end
