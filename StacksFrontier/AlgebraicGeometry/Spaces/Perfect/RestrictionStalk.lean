module

public import Mathlib.CategoryTheory.Limits.Final.Type
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPoints

/-!
# Stalks of the restriction of a module to an étale chart

Let `j : U ⟶ X` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  The small étale site of `U` is the localization of the small étale site of `X`
at `U`, compatibly with the structure sheaves, so the pullback `j^*F` of an `𝒪_X`-module `F`
deserves the name `F|_U`.  Stacks' Equation 08GT is the resulting identification of stalks

`(F|_U)_ū = F_x̄`

for a geometric point `ū` of `U` with image `x̄ = j ∘ ū` in `X`.

## Main definitions

* `AlgebraicGeometry.Space.moduleUnderlyingPresheaf` is the underlying presheaf of sets of an
  `𝒪`-module on the small étale site, the presheaf whose geometric stalks are taken below.
* `AlgebraicGeometry.Space.moduleGerm` is the germ at a geometric point of a section of an
  `𝒪`-module over a small étale neighbourhood.

## Main results

* `AlgebraicGeometry.Space.etaleModulePullbackStalkIso`: the stalk at `ū` of the étale
  restriction of an `𝒪_X`-module is its stalk at `x̄`, naturally in the module.
* `AlgebraicGeometry.Space.etaleModulePullbackStalkIso_hom_app_moduleGerm`: that comparison
  carries the germ at `ū` of a section over an étale chart of `U` to the germ at `x̄` of the
  same section, read over the composite chart of `X`.
* `AlgebraicGeometry.Space.modulePullbackStalkIso`: **Stacks' Equation 08GT** —
  `(F|_U)_ū = F_x̄` for the pullback of modules itself, naturally in `F`.
* `AlgebraicGeometry.Space.modulePullbackStalkIso_hom_app_moduleGerm` pins that comparison on
  germs: it is the identification of Stacks 03LV of the pullback with étale restriction, taken
  on sections over a chart and then passed to germs.
* `AlgebraicGeometry.Space.modulePullbackStalkIso_germ_add` and
  `AlgebraicGeometry.Space.modulePullbackStalkIso_germ_smul`: the comparison is one of
  modules and not merely of sets — on germs it respects addition and the action of the
  structure sheaf.

## Implementation notes

Stalks are taken on the underlying presheaves of sets, so that no smallness assumption on the
category of small étale neighbourhoods is needed: `AlgebraicGeometry.Space.stalkSetFunctor` is
the colimit as a quotient type, which exists at every universe.  The category-valued stalk
`AlgebraicGeometry.Space.stalkFunctor` is not available here.  Its colimit exists only when the
target has colimits indexed by the neighbourhoods, whose objects are one universe above the
schemes; that is why `AlgebraicGeometry.Space.etaleLocalRing` takes the stalk of
`AlgebraicGeometry.Space.liftedStructurePresheaf` in `CommRingCat.{u + 1}` rather than of the
structure presheaf in `CommRingCat.{u}`.  An `AddCommGrpCat.{m}`-valued form of the statement
would therefore carry a hypothesis that is unsatisfiable at `m = u`, which is the module
universe of `AlgebraicGeometry.Space.modulePullback`.

The module structure is instead pinned by the three germ equations.  The comparison is the germ
of a single map on sections — the component of the isomorphism of Stacks 03LV, which is an
isomorphism of sheaves of `𝒪`-modules — and the additivity and scalar equations say that this
map is additive and `𝒪`-linear.  So the covering set states an identification of modules: a
bijection of the underlying sets not respecting the operations would falsify them.

The proof is cofinality and nothing else.  Along étale restriction the sections of a module over
a chart of `U` are, on the nose, its sections over the composite chart of `X`
(`AlgebraicGeometry.Space.etaleModulePullback_obj_val_obj`), so the two diagrams of sections
differ only by reindexing along postcomposition of neighbourhoods, and that functor is initial
by `AlgebraicGeometry.Space.SmallEtaleNeighborhood.initial_postcomp`.  Hence
`CategoryTheory.Functor.bijective_colimitTypePrecomp` applies and the comparison is the germ
map itself; no comparison of colimits is assembled by hand, and the germ equation holds by
`rfl`.

Transporting the statement from étale restriction to the pullback of modules is clause (2) of
Stacks 03LV, `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`.  That comparison is
an isomorphism of sheaves of modules, so its component on sections is a module homomorphism,
which is what makes the additivity and scalar equations below immediate.

The module universe `m` stays free for étale restriction, so
`AlgebraicGeometry.Space.etaleModulePullbackStalkIso` is the universe-polymorphic form of the
statement.  For the pullback it is forced to the universe of the schemes:
`AlgebraicGeometry.Space.modulePullback` is a functor
`Modules.{u, u} ⥤ Modules.{u, u}`, and hence so is the comparison of Stacks 03LV.

## References

* [Stacks Project, Tag 08GT](https://stacks.math.columbia.edu/tag/08GT)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The underlying presheaf of sets of an `𝒪_F`-module on the small étale site of an algebraic
space `F`: forget the sheaf condition, the module structures and the group structures. -/
def moduleUnderlyingPresheaf (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    Modules.{u, m} B S hS F hF ⥤ (SmallEtale B S hS F)ᵒᵖ ⥤ Type m :=
  SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _ ⋙
    (Functor.whiskeringRight _ AddCommGrpCat.{m} (Type m)).obj (forget AddCommGrpCat.{m})

/-- The sections of the underlying presheaf of sets of a module are its sections. -/
theorem moduleUnderlyingPresheaf_obj_obj {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (M : Modules.{u, m} B S hS F hF)
    (W : (SmallEtale B S hS F)ᵒᵖ) :
    ((moduleUnderlyingPresheaf.{u, m} B S hS F hF).obj M).obj W = M.val.obj W :=
  rfl

/-- The germ at a geometric point `x` of a section of an `𝒪_F`-module over a small étale
neighbourhood of `x`, as an element of the stalk of Stacks 04JY. -/
def moduleGerm (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {x : GeometricPoint B S hS F} (M : Modules.{u, m} B S hS F hF)
    (W : SmallEtaleNeighborhood x) (a : M.val.obj (Opposite.op W.chart)) :
    (stalkSetFunctor x).obj ((moduleUnderlyingPresheaf.{u, m} B S hS F hF).obj M) :=
  (SmallEtaleNeighborhood.sections (x := x)
    ((moduleUnderlyingPresheaf.{u, m} B S hS F hF).obj M)).ιColimitType (Opposite.op W) a

variable {U X : AlgebraicSpaces B S hS}

/-- **Stacks 08GT** in its restriction reading.  The stalk at a geometric point `ū` of `U` of
the étale restriction of an `𝒪_X`-module along an étale `j : U ⟶ X` is the stalk of that module
at the image point `x̄ = j ∘ ū`, naturally in the module.

Restriction reindexes sections along postcomposition of charts with `j`, and postcomposition is
initial on small étale neighbourhoods, so the comparison is the germ map. -/
@[stacks 08GT "the stalks of an étale restriction"]
def etaleModulePullbackStalkIso (j : U ⟶ X) (hj : IsEtale B S hS j.hom)
    (y : GeometricPoint B S hS U.1) :
    etaleModulePullback.{u, m} B S hS j hj ⋙
        moduleUnderlyingPresheaf.{u, m} B S hS U.1 U.2 ⋙ stalkSetFunctor y ≅
      moduleUnderlyingPresheaf.{u, m} B S hS X.1 X.2 ⋙
        stalkSetFunctor (geometricPointMap j.hom y) :=
  have := SmallEtaleNeighborhood.initial_postcomp B S hS j hj y
  NatIso.ofComponents
    (fun M => Equiv.toIso (Equiv.ofBijective
      ((SmallEtaleNeighborhood.postcomp B S hS j hj y).op.colimitTypePrecomp
        (SmallEtaleNeighborhood.sections (x := geometricPointMap j.hom y)
          ((moduleUnderlyingPresheaf.{u, m} B S hS X.1 X.2).obj M)))
      (Functor.bijective_colimitTypePrecomp _ _)))
    (by
      intro M N f
      ext z
      induction z using Quot.inductionOn with
      | _ p => rfl)

/-- The comparison of Stacks 08GT for étale restriction is the germ map: it carries the germ at
`ū` of a section over a chart of `U` to the germ at `x̄` of the same section, read over the
composite chart of `X`. -/
@[stacks 08GT "the étale restriction comparison on germs"]
theorem etaleModulePullbackStalkIso_hom_app_moduleGerm (j : U ⟶ X)
    (hj : IsEtale B S hS j.hom) (y : GeometricPoint B S hS U.1)
    (M : Modules.{u, m} B S hS X.1 X.2) (W : SmallEtaleNeighborhood y)
    (a : ((etaleModulePullback.{u, m} B S hS j hj).obj M).val.obj (Opposite.op W.chart)) :
    (etaleModulePullbackStalkIso.{u, m} B S hS j hj y).hom.app M
        (moduleGerm.{u, m} B S hS U.1 U.2
          ((etaleModulePullback.{u, m} B S hS j hj).obj M) W a) =
      moduleGerm.{u, m} B S hS X.1 X.2 M
        ((SmallEtaleNeighborhood.postcomp B S hS j hj y).obj W) a :=
  rfl

/-- **Stacks' Equation 08GT.**  Let `j : U ⟶ X` be an étale morphism of algebraic spaces over
`S`, let `F` be an `𝒪_X`-module and let `ū` be a geometric point of `U` with image `x̄` in `X`.
Then the stalk of the restriction `F|_U = j^*F` at `ū` is the stalk of `F` at `x̄`, naturally
in `F`:

`(F|_U)_ū = F_x̄`.

The pullback of modules is étale restriction by clause (2) of Stacks 03LV, and the stalks of an
étale restriction are `AlgebraicGeometry.Space.etaleModulePullbackStalkIso`. -/
@[stacks 08GT]
def modulePullbackStalkIso (j : U ⟶ X) (hj : IsEtale B S hS j.hom)
    (y : GeometricPoint B S hS U.1) :
    modulePullback B S hS j ⋙
        moduleUnderlyingPresheaf.{u, u} B S hS U.1 U.2 ⋙ stalkSetFunctor y ≅
      moduleUnderlyingPresheaf.{u, u} B S hS X.1 X.2 ⋙
        stalkSetFunctor (geometricPointMap j.hom y) :=
  Functor.isoWhiskerRight (modulePullbackIsoEtaleModulePullback B S hS j hj)
      (moduleUnderlyingPresheaf.{u, u} B S hS U.1 U.2 ⋙ stalkSetFunctor y) ≪≫
    etaleModulePullbackStalkIso.{u, u} B S hS j hj y

/-- **Stacks 08GT, canonicity.**  The comparison `(F|_U)_ū = F_x̄` sends the germ at `ū` of a
section of `j^*F` over a chart of `U` to the germ at `x̄` of its image under the identification
of Stacks 03LV of the pullback with étale restriction.  So it is the canonical identification
and not merely some natural isomorphism of the two stalk functors. -/
@[stacks 08GT "the comparison on germs"]
theorem modulePullbackStalkIso_hom_app_moduleGerm (j : U ⟶ X) (hj : IsEtale B S hS j.hom)
    (y : GeometricPoint B S hS U.1) (M : Modules.{u, u} B S hS X.1 X.2)
    (W : SmallEtaleNeighborhood y)
    (a : ((modulePullback B S hS j).obj M).val.obj (Opposite.op W.chart)) :
    (modulePullbackStalkIso B S hS j hj y).hom.app M
        (moduleGerm.{u, u} B S hS U.1 U.2 ((modulePullback B S hS j).obj M) W a) =
      moduleGerm.{u, u} B S hS X.1 X.2 M
        ((SmallEtaleNeighborhood.postcomp B S hS j hj y).obj W)
        (((modulePullbackIsoEtaleModulePullback B S hS j hj).hom.app M).val.app
          (Opposite.op W.chart) a) :=
  rfl

/-- **Stacks 08GT** is an identification of modules and not merely of sets: on germs the
comparison respects addition, the sum being taken in the sections of `j^*F` over a chart of `U`
on one side and in the sections of `F` over the composite chart of `X` on the other. -/
@[stacks 08GT "additivity on germs"]
theorem modulePullbackStalkIso_germ_add (j : U ⟶ X) (hj : IsEtale B S hS j.hom)
    (y : GeometricPoint B S hS U.1) (M : Modules.{u, u} B S hS X.1 X.2)
    (W : SmallEtaleNeighborhood y)
    (a b : ((modulePullback B S hS j).obj M).val.obj (Opposite.op W.chart)) :
    (modulePullbackStalkIso B S hS j hj y).hom.app M
        (moduleGerm.{u, u} B S hS U.1 U.2 ((modulePullback B S hS j).obj M) W (a + b)) =
      moduleGerm.{u, u} B S hS X.1 X.2 M
        ((SmallEtaleNeighborhood.postcomp B S hS j hj y).obj W)
        (((modulePullbackIsoEtaleModulePullback B S hS j hj).hom.app M).val.app
            (Opposite.op W.chart) a +
          ((modulePullbackIsoEtaleModulePullback B S hS j hj).hom.app M).val.app
            (Opposite.op W.chart) b) :=
  by rw [modulePullbackStalkIso_hom_app_moduleGerm, map_add]

/-- **Stacks 08GT** is an identification of modules and not merely of abelian groups: on germs
the comparison respects the action of the structure sheaf.  The scalar is a section of `𝒪_U`
over a chart of `U`, which is a section of `𝒪_X` over the composite chart of `X` — étale
postcomposition leaves the underlying scheme of a chart, hence its regular functions,
unchanged. -/
@[stacks 08GT "action on germs"]
theorem modulePullbackStalkIso_germ_smul (j : U ⟶ X) (hj : IsEtale B S hS j.hom)
    (y : GeometricPoint B S hS U.1) (M : Modules.{u, u} B S hS X.1 X.2)
    (W : SmallEtaleNeighborhood y)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS U.1 U.2).O)).obj.obj
      (Opposite.op W.chart))
    (a : ((modulePullback B S hS j).obj M).val.obj (Opposite.op W.chart)) :
    (modulePullbackStalkIso B S hS j hj y).hom.app M
        (moduleGerm.{u, u} B S hS U.1 U.2 ((modulePullback B S hS j).obj M) W (r • a)) =
      moduleGerm.{u, u} B S hS X.1 X.2 M
        ((SmallEtaleNeighborhood.postcomp B S hS j hj y).obj W)
        (r • ((modulePullbackIsoEtaleModulePullback B S hS j hj).hom.app M).val.app
          (Opposite.op W.chart) a) :=
  by rw [modulePullbackStalkIso_hom_app_moduleGerm, map_smul]

end AlgebraicGeometry.Space

end
