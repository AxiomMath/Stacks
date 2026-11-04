module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafComparison

/-!
# Stacks 01BH: construction (2) and the comparison of the three constructions

Let `(X, 𝒪_X)` be a ringed space, let `α : R → Γ(X, 𝒪_X)` be a ring map and let `M` be an
`R`-module. Stacks Tag 01BH names three constructions of the associated sheaf of
`𝒪_X`-modules `ℱ_M`:

1. `ℱ₁ = π^* M`, the pullback along the morphism of ringed spaces `π : (X, 𝒪_X) ⟶ ({*}, R)`
   whose map on structure sheaves is `α`;
2. `ℱ₂ = coker(⊕_{j ∈ J} 𝒪_X ⟶ ⊕_{i ∈ I} 𝒪_X)`, for a presentation
   `⊕_{j ∈ J} R ⟶ ⊕_{i ∈ I} R ⟶ M ⟶ 0` of `M`, the map of free `𝒪_X`-modules being given by
   the matrix whose entries are the `α`-images of the matrix coefficients `r_{ij}`;
3. `ℱ₃`, the sheafification of `U ↦ 𝒪_X(U) ⊗_R M`.

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafComparison` builds the coefficient
point `({*}, R)`, the morphism `π`, construction (1)
(`Stacks.AssociatedSheaf.coefficientPointPullback`), construction (3)
(`Stacks.AssociatedSheaf.associatedSheaf`) and the comparison of (1) with (3)
(`Stacks.AssociatedSheaf.coefficientPointPullbackIsoAssociatedSheaf`). This file adds
construction (2) and compares it with the other two, which completes the three-way comparison
for a sheaf of modules on the coefficient point.

The argument is the one Stacks gives: `π^*` is a left adjoint, hence preserves cokernels and
coproducts, and `π^* 𝒪_{pt} = 𝒪_X`, so `π^*` carries a presentation of a sheaf of modules on
the point to a presentation of its pullback, with the generator and relation index types
unchanged. Mathlib packages a global presentation as `SheafOfModules.Presentation` and its
transport along a colimit-preserving functor identifying the structure sheaves as
`SheafOfModules.Presentation.map`; `π^* 𝒪_{pt} ≅ 𝒪_X` is
`SheafOfModules.pullbackObjUnitToUnit`, an isomorphism because the functor `Opens({*}) ⥤
Opens(X)` given by `π^{-1}` is final.

## Main definitions

* `Stacks.CoefficientPointPresentation.relationMap`: the relation matrix of a
  `SheafOfModules.Presentation`, as a morphism of free sheaves of modules
  `free (relations) ⟶ free (generators)`. This is the map whose cokernel is construction (2).
* `Stacks.CoefficientPointPresentation.presentationMatrix`, `presentationGenerators` and
  `presentationSheaf`: **construction (2)** — the matrix of free `𝒪_X`-modules
  `⊕_J 𝒪_X ⟶ ⊕_I 𝒪_X`, the generating map `⊕_I 𝒪_X ⟶ π^* N`, and construction (2) itself as
  the cokernel of the matrix.
* `Stacks.CoefficientPointPresentation.pullbackPresentation`: construction (2) packaged as a
  `SheafOfModules.Presentation` of `π^* N`.
* `Stacks.CoefficientPointPresentation.pullbackFreeIso`: `π^*` of a free sheaf is free, that is
  `π^*(⊕_I 𝒪_{pt}) ≅ ⊕_I 𝒪_X`.
* `Stacks.CoefficientPointPresentation.freeComparison`: the identification
  `⊕_I 𝒪_X ≅ π^*(⊕_I 𝒪_{pt})` through which construction (2) reads a matrix over `R` as a matrix
  over `𝒪_X`, determined summand by summand by `ιFree_comp_freeComparison_hom`.
* `Stacks.CoefficientPointPresentation.mapCokernelIso`: the abstract form of `(2) ≅ (1)`, for an
  arbitrary colimit-preserving functor identifying the structure sheaves.

## Main results

* `Stacks.CoefficientPointPresentation.presentationCokernelIso`: a sheaf of modules with a
  presentation is the cokernel of the presentation's relation matrix. This is what makes
  `presentationSheaf` deserve the name "construction (2)".
* `Stacks.CoefficientPointPresentation.presentationSheafIsoPullback`: **(2) ≅ (1)**,
  construction (2) is construction (1).
* `Stacks.CoefficientPointPresentation.presentationSheafIsoAssociatedSheaf`: **(2) ≅ (3)**,
  construction (2) is construction (3). With the previous item and
  `Stacks.AssociatedSheaf.coefficientPointPullbackIsoAssociatedSheaf` this is the three-way
  comparison.
* `Stacks.CoefficientPointPresentation.presentationMatrix_eq`: the relation matrix of
  construction (2) is the relation matrix on the point, pulled back along `π` and read through
  `freeComparison`. Since the scalar map of `π` is `α`, this is the clause of Stacks 01BH
  construction (2) that the entries of the matrix of free `𝒪_X`-modules are the `α`-images of
  the entries over `R`; see that declaration's docstring for what is and is not proved.
* `Stacks.CoefficientPointPresentation.presentationGenerators_eq` and
  `ιFree_comp_cokernel_π_presentationSheafIsoPullback_hom`: the generating map of
  construction (2) is the `π^*`-image of the generating map of the presentation on the point,
  and the comparison `(2) ≅ (1)` sends the `i`-th generator to the image of the `i`-th
  generating section of `N`. So the comparison remembers the quotient map onto `M`, not just the
  relation matrix.
* `Stacks.CoefficientPointPresentation.pullbackPresentation_generators_I` and
  `pullbackPresentation_relations_I`: the generator and relation index types are unchanged by
  `π^*`, so construction (2) uses the same presentation `⊕_J R ⟶ ⊕_I R ⟶ M ⟶ 0` as the source.

## Implementation notes

Everything is at `SheafOfModules.{u}` over `RingedSpace.{u, u}`: `SheafOfModules.Presentation`
indexes its generators and relations by types in the ring universe, so the free sheaves of
construction (2) live in that universe, and
`Stacks.AssociatedSheaf.coefficientPointPullbackIsoAssociatedSheaf` is available there. The
larger module universes that `AssociatedSheafComparison` supports are not used here.

Four instances are supplied by hand rather than found by synthesis, and each is local to this
file:

* `(RingedSpaceModuleAdjunction.opensMap f).Final`, from
  `CategoryTheory.final_of_representablyFlat`: the opens of the target whose preimage contains a
  fixed open of the source are closed under intersection. The same instance is declared, also
  locally, in `StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic`.
* `(SheafOfModules.pushforward.{u} (RingedSpaceModuleAdjunction.structureSheafHom f))`
  `.IsRightAdjoint`.
  `RingedSpaceModuleAdjunction.modulePushforward_isRightAdjoint` states this for
  `RingedSpaceModuleAdjunction.modulePushforward f`, which is a semireducible `def`, so synthesis
  does not see through it; the universe must also be pinned, since
  `SheafOfModules.pushforward` is polymorphic in the module universe and synthesis would
  otherwise be asked for a metavariable.
* `PreservesColimitsOfSize.{u, u} (pointPullback X α)` is found only because `pointPullback` is
  an `abbrev`: through the semireducible `Stacks.AssociatedSheaf.coefficientPointPullback` the
  `Functor.IsLeftAdjoint` instance is invisible. The two functors are equal by `rfl`
  (`pointPullback_eq`), which is how the comparison with construction (3) is stated.
* `PreservesColimitsOfSize.{0, 0} F` in the generic section, from
  `CategoryTheory.Limits.preservesColimitsOfSize_shrink`: the cokernel shape lives in `Type 0`,
  while the hypothesis available is colimit preservation at size `u`. Mathlib's own
  `SheafOfModules.Presentation.map` does the same, and for the same reason does not make it
  global.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.AssociatedSheaf

universe u v w

namespace Stacks.CoefficientPointPresentation

/-! ### A sheaf of modules is the cokernel of the relation matrix of a presentation

This section is about an arbitrary `SheafOfModules.Presentation` and does not mention the
coefficient point. Mathlib's `SheafOfModules.Presentation` records generators and relations as
*sections*; the matrix of free sheaves that Stacks 01BH construction (2) takes the cokernel of
is `relationMap`, and `presentationCokernelIso` is the statement that its cokernel is the
sheaf presented. -/

section Generic

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C} {Rs : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} Rs}

/-- The relation matrix of a presentation of a sheaf of modules: the morphism of free sheaves
`⊕_{relations} Rs ⟶ ⊕_{generators} Rs` whose cokernel is the presented sheaf. It is the map
`free relations.I ⟶ ker (generators.π) ⟶ free generators.I` given by the relations, which are
by definition sections generating the kernel of the map from the free sheaf on the generators.

This is an `abbrev` on purpose: `SheafOfModules.Presentation.isColimit` is stated for the
unfolded composite, and a semireducible `def` here would make `cokernel` of it a different,
non-unifying type. -/
abbrev relationMap (P : M.Presentation) :
    SheafOfModules.free (R := Rs) P.relations.I ⟶ SheafOfModules.free P.generators.I :=
  (SheafOfModules.freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π

/-- A sheaf of modules with a presentation is the cokernel of the presentation's relation
matrix. This is the sense in which the cokernel of a presentation matrix — Stacks 01BH
construction (2) — computes the sheaf it presents. -/
def presentationCokernelIso (P : M.Presentation) : cokernel (relationMap P) ≅ M :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) P.isColimit

/-- The comparison `presentationCokernelIso` carries the class of a section of the free sheaf on
the generators to its image under the generating map of the presentation. -/
@[reassoc (attr := simp)]
theorem cokernel_π_presentationCokernelIso_hom (P : M.Presentation) :
    cokernel.π (relationMap P) ≫ (presentationCokernelIso P).hom = P.generators.π :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) P.isColimit
    WalkingParallelPair.one

section Map

variable {C' : Type v} [Category.{w} C'] {J' : GrothendieckTopology C'}
  {Ss : Sheaf J' RingCat.{u}}
  [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (P : M.Presentation) (F : SheafOfModules.{u} Rs ⥤ SheafOfModules.{u} Ss)
  [PreservesColimitsOfSize.{u, u} F] (η : SheafOfModules.unit Ss ≅ F.obj (SheafOfModules.unit Rs))

/-- `F` preserves colimits indexed by categories whose objects and morphisms lie in `Type`, such
as the shape of a cokernel. -/
local instance : PreservesColimitsOfSize.{0, 0} F := preservesColimitsOfSize_shrink _

/-- The relation matrix of a transported presentation is the relation matrix of the original,
mapped by `F` and read through the identification `F (⊕_I Rs) ≅ ⊕_I Ss` of
`SheafOfModules.mapFreeIso`. -/
theorem mapRelations_eq : P.mapRelations F η =
    (SheafOfModules.mapFreeIso F P.relations.I η).hom ≫ F.map (relationMap P) ≫
      (SheafOfModules.mapFreeIso F P.generators.I η).inv := by
  rw [SheafOfModules.Presentation.mapRelations, F.map_comp]
  simp

/-- The transported generating map is the original generating map, mapped by `F` and read
through `SheafOfModules.mapFreeIso`. True by definition; stated because
`SheafOfModules.GeneratingSections.mapFreeHom` has no equation lemma to rewrite with. -/
theorem mapGenerators_eq : P.mapGenerators F η =
    (SheafOfModules.mapFreeIso F P.generators.I η).hom ≫ F.map P.generators.π := rfl

/-- The transported relation matrix followed by `SheafOfModules.mapFreeIso` on the generators is
`SheafOfModules.mapFreeIso` on the relations followed by the `F`-image of the relation matrix. -/
@[reassoc]
theorem mapRelations_comp_mapFreeIso_hom :
    P.mapRelations F η ≫ (SheafOfModules.mapFreeIso F P.generators.I η).hom =
      (SheafOfModules.mapFreeIso F P.relations.I η).hom ≫ F.map (relationMap P) := by
  rw [mapRelations_eq]
  simp

/-- **`F` carries construction (2) to construction (2).** If `F` preserves colimits and carries
the structure sheaf to the structure sheaf, then the cokernel of the transported relation matrix
is `F` of the sheaf presented.

This is the Stacks 01BH argument that construction (2) agrees with construction (1), in the
abstract: `F` is right exact, so it takes the cokernel of the relation matrix to the cokernel of
the `F`-image of that matrix, and it takes free sheaves to free sheaves, so the `F`-image of the
matrix is the transported matrix up to the identifications `SheafOfModules.mapFreeIso`. -/
def mapCokernelIso : cokernel (P.mapRelations F η) ≅ F.obj M :=
  cokernel.mapIso (P.mapRelations F η) (F.map (relationMap P))
      (SheafOfModules.mapFreeIso F P.relations.I η)
      (SheafOfModules.mapFreeIso F P.generators.I η)
      (mapRelations_comp_mapFreeIso_hom P F η) ≪≫
    (PreservesCokernel.iso F (relationMap P)).symm ≪≫ F.mapIso (presentationCokernelIso P)

/-- The comparison of `mapCokernelIso` carries the class of a section of the free sheaf on the
generators to its image under the transported generating map. -/
@[reassoc (attr := simp)]
theorem cokernel_π_mapCokernelIso_hom :
    cokernel.π (P.mapRelations F η) ≫ (mapCokernelIso P F η).hom = P.mapGenerators F η := by
  rw [mapCokernelIso, Iso.trans_hom, Iso.trans_hom, cokernel.mapIso_hom, cokernel.π_desc_assoc,
    mapGenerators_eq]
  simp [← Functor.map_comp]

/-- The transported generating map sends the `i`-th generator to the image of the `i`-th
generator of the source. -/
theorem ιFree_comp_mapGenerators (i : P.generators.I) :
    SheafOfModules.ιFree i ≫ P.mapGenerators F η =
      η.hom ≫ F.map (SheafOfModules.ιFree i ≫ P.generators.π) := by
  rw [mapGenerators_eq, SheafOfModules.ιFree_mapFreeIso_hom_assoc, F.map_comp]

end Map

end Generic

/-! ### The coefficient point

`π : X ⟶ ({*}, R)` is `Stacks.AssociatedSheaf.toCoefficientPoint' X α`. -/

section Point

attribute [local instance] modulePushforward_isRightAdjoint

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The functor `Opens Y ⥤ Opens X` given by preimage along a morphism of ringed spaces is
final, being representably flat. This is what makes `SheafOfModules.pullbackObjUnitToUnit` an
isomorphism, hence `π^* 𝒪_Y ≅ 𝒪_X`. -/
local instance finalOpensMap : (opensMap f).Final :=
  CategoryTheory.final_of_representablyFlat _

section

variable (X) {R : Type u} [CommRing R] (α : R →+* X.presheaf.obj (op ⊤))

/-- **Stacks 01BH, construction (1)**, in the shape this file uses: pullback of sheaves of
modules along `π : X ⟶ ({*}, R)`. Reducible, so that the instances carried by
`SheafOfModules.pullback` — above all that it preserves colimits, being a left adjoint — remain
visible to synthesis. -/
abbrev pointPullback :
    SheafOfModules.{u} (structureSheafRing (coefficientPoint (CommRingCat.of R))) ⥤
      SheafOfModules.{u} (structureSheafRing X) :=
  SheafOfModules.pullback.{u} (structureSheafHom (toCoefficientPoint' X α))

/-- `pointPullback` is `Stacks.AssociatedSheaf.coefficientPointPullback` at module universe
`u`. -/
theorem pointPullback_eq : pointPullback X α = coefficientPointPullback.{u, u} X α := rfl

/-- `π^* 𝒪_{pt} ≅ 𝒪_X`: the pullback of the structure sheaf of the coefficient point is the
structure sheaf of `X`. Stated in the direction `SheafOfModules.Presentation.map` consumes. -/
abbrev pullbackUnitIso : SheafOfModules.unit (structureSheafRing X) ≅
    (pointPullback X α).obj (SheafOfModules.unit _) :=
  (asIso (SheafOfModules.pullbackObjUnitToUnit
    (structureSheafHom (toCoefficientPoint' X α)))).symm

/-- `π^*(⊕_I 𝒪_{pt}) ≅ ⊕_I 𝒪_X`: the pullback along `π` of a free sheaf of modules is free on
the same index type. This is the "`π^*` commutes with direct sums and `π^* R = 𝒪_X`" step of the
Stacks proof that construction (2) agrees with construction (1). -/
def pullbackFreeIso (I : Type u) :
    (pointPullback X α).obj (SheafOfModules.free I) ≅ SheafOfModules.free I :=
  SheafOfModules.pullbackObjFreeIso _ I

/-- `⊕_I 𝒪_X ≅ π^*(⊕_I 𝒪_{pt})`, the identification got by applying `π^* 𝒪_{pt} ≅ 𝒪_X` on each
summand. This is the identification through which construction (2) reads the matrix over `R` as a
matrix over `𝒪_X`, and it is characterized summand by summand by
`ιFree_comp_freeComparison_hom`.

`pullbackFreeIso` is Mathlib's other construction of an identification of the same two objects.
No comparison of the two is proved here: Mathlib's `ιFree`-extensionality for `free I` is stated
at `(SheafOfModules.freeCofan I).pt`, whose reduction to `SheafOfModules.free I` is blocked
because `CategoryTheory.Limits.getColimitCocone` is not exposed, and the Mathlib lemmas that
work around this enable the backward `defeqAttrib.useBackward` compatibility flag, which is not
used here. -/
abbrev freeComparison (I : Type u) :
    SheafOfModules.free (R := structureSheafRing X) I ≅
      (pointPullback X α).obj (SheafOfModules.free I) :=
  SheafOfModules.mapFreeIso (pointPullback X α) I (pullbackUnitIso X α)

/-- `freeComparison` on the `i`-th summand is `π^* 𝒪_{pt} ≅ 𝒪_X` followed by `π^*` of the `i`-th
inclusion. This determines it. -/
theorem ιFree_comp_freeComparison_hom (I : Type u) (i : I) :
    SheafOfModules.ιFree i ≫ (freeComparison X α I).hom =
      (pullbackUnitIso X α).hom ≫ (pointPullback X α).map (SheafOfModules.ιFree i) :=
  SheafOfModules.ιFree_mapFreeIso_hom _ _ _ _

/-! #### Construction (2) -/

variable {N : SheafOfModules.{u} (structureSheafRing (coefficientPoint (CommRingCat.of R)))}

/-- **Stacks 01BH, construction (2).** Given a presentation `⊕_J 𝒪_{pt} ⟶ ⊕_I 𝒪_{pt} ⟶ N ⟶ 0`
of a sheaf of modules on the coefficient point `({*}, R)`, the presentation
`⊕_J 𝒪_X ⟶ ⊕_I 𝒪_X ⟶ π^* N ⟶ 0` of `𝒪_X`-modules obtained by applying `π^*`.

This is construction (2) with its comparison to construction (1) built in: `π^*` preserves
cokernels because it is a left adjoint, and carries `𝒪_{pt}` to `𝒪_X`, so the cokernel of the
matrix of free `𝒪_X`-modules is `π^* N`. See `presentationSheafIsoPullback` for that statement
on its own, `presentationMatrix_eq` for the matrix being the `α`-image of the matrix over `R`,
and `pullbackPresentation_generators_I`/`pullbackPresentation_relations_I` for the index types
being unchanged. -/
def pullbackPresentation (P : N.Presentation) : ((pointPullback X α).obj N).Presentation :=
  P.map (pointPullback X α) (pullbackUnitIso X α)

/-- The generators of `pullbackPresentation` are indexed by the same type as those of `P`. -/
@[simp]
theorem pullbackPresentation_generators_I (P : N.Presentation) :
    (pullbackPresentation X α P).generators.I = P.generators.I := rfl

/-- The relations of `pullbackPresentation` are indexed by the same type as those of `P`. -/
@[simp]
theorem pullbackPresentation_relations_I (P : N.Presentation) :
    (pullbackPresentation X α P).relations.I = P.relations.I := rfl

/-- **Stacks 01BH, construction (2), the matrix.** The map of free `𝒪_X`-modules
`⊕_J 𝒪_X ⟶ ⊕_I 𝒪_X` whose cokernel is construction (2). This is the relation matrix that
`pullbackPresentation` presents `π^* N` by. -/
abbrev presentationMatrix (P : N.Presentation) :
    SheafOfModules.free (R := structureSheafRing X) P.relations.I ⟶
      SheafOfModules.free P.generators.I :=
  P.mapRelations (pointPullback X α) (pullbackUnitIso X α)

/-- The generating map of construction (2): `⊕_I 𝒪_X ⟶ π^* N`. -/
abbrev presentationGenerators (P : N.Presentation) :
    SheafOfModules.free (R := structureSheafRing X) P.generators.I ⟶ (pointPullback X α).obj N :=
  P.mapGenerators (pointPullback X α) (pullbackUnitIso X α)

/-- **The matrix of construction (2) is the matrix over `R` pushed through `α`.** Precisely: the
matrix of free `𝒪_X`-modules is the matrix of free `𝒪_{pt}`-modules pulled back along `π` and
read through `freeComparison`. The scalar map of `π` on global sections is `α`
(`Stacks.AssociatedSheaf.structureSheafHom_app_top_apply`), so pulling back along `π` is what
applies `α` to a matrix coefficient.

This is the structural form of the clause of Stacks 01BH construction (2) that the entries of
the matrix are the `α`-images of the `r_{ij}`. The entrywise formula itself — the identity
`(freeHomEquiv _ (presentationMatrix X α P) j) = α`-image of `freeHomEquiv _ (relationMap P) j`
read in coordinates on each open — is not proved here. -/
theorem presentationMatrix_eq (P : N.Presentation) :
    presentationMatrix X α P = (freeComparison X α P.relations.I).hom ≫
      (pointPullback X α).map (relationMap P) ≫ (freeComparison X α P.generators.I).inv :=
  mapRelations_eq P (pointPullback X α) (pullbackUnitIso X α)

/-- **Stacks 01BH, construction (2)**, as a sheaf: the cokernel of the matrix of free
`𝒪_X`-modules attached to a presentation of `N` on the coefficient point. -/
abbrev presentationSheaf (P : N.Presentation) : SheafOfModules.{u} (structureSheafRing X) :=
  cokernel (presentationMatrix X α P)

/-- **Stacks 01BH, (2) ≅ (1).** Construction (2), the cokernel of the presentation matrix over
`𝒪_X`, is construction (1), the pullback along `π : X ⟶ ({*}, R)`. -/
def presentationSheafIsoPullback (P : N.Presentation) :
    presentationSheaf X α P ≅ (pointPullback X α).obj N :=
  mapCokernelIso P (pointPullback X α) (pullbackUnitIso X α)

/-- The comparison `(2) ≅ (1)` carries the class of a section of `⊕_I 𝒪_X` to its image under
the generating map of construction (2), so it remembers the quotient map onto `π^* N` and not
only the relation matrix. -/
@[reassoc (attr := simp)]
theorem cokernel_π_presentationSheafIsoPullback_hom (P : N.Presentation) :
    cokernel.π (presentationMatrix X α P) ≫ (presentationSheafIsoPullback X α P).hom =
      presentationGenerators X α P :=
  cokernel_π_mapCokernelIso_hom P (pointPullback X α) (pullbackUnitIso X α)

/-- **The generating map of construction (2) is the `π^*`-image of the generating map over
`R`.** The map `⊕_I 𝒪_X ⟶ π^* N` of construction (2) is `π^*` of the map
`⊕_I 𝒪_{pt} ⟶ N` of the presentation on the point, read through `freeComparison`. -/
theorem presentationGenerators_eq (P : N.Presentation) :
    presentationGenerators X α P =
      (freeComparison X α P.generators.I).hom ≫ (pointPullback X α).map P.generators.π :=
  mapGenerators_eq P (pointPullback X α) (pullbackUnitIso X α)

/-- **The comparison `(2) ≅ (1)` sends the `i`-th generator to the image of the `i`-th
generator of `N`.** On the `i`-th summand of `⊕_I 𝒪_X`, the class in construction (2) goes to
the image under `π^*` of the `i`-th generating section of `N`. -/
theorem ιFree_comp_cokernel_π_presentationSheafIsoPullback_hom (P : N.Presentation)
    (i : P.generators.I) :
    SheafOfModules.ιFree i ≫ cokernel.π (presentationMatrix X α P) ≫
        (presentationSheafIsoPullback X α P).hom =
      (pullbackUnitIso X α).hom ≫
        (pointPullback X α).map (SheafOfModules.ιFree i ≫ P.generators.π) := by
  rw [cokernel_π_presentationSheafIsoPullback_hom]
  exact ιFree_comp_mapGenerators P (pointPullback X α) (pullbackUnitIso X α) i

/-- The generating map of the `SheafOfModules.Presentation`-valued construction (2) is the
generating map `presentationGenerators`. -/
theorem pullbackPresentation_generators_π (P : N.Presentation) :
    (pullbackPresentation X α P).generators.π = presentationGenerators X α P :=
  SheafOfModules.Presentation.map_π_eq P (pointPullback X α) (pullbackUnitIso X α)

/-- **Stacks 01BH, (2) ≅ (3).** Construction (2), the cokernel of the presentation matrix over
`𝒪_X`, is construction (3), the sheafification of `U ↦ 𝒪_X(U) ⊗_R M` for `M` the sections of `N`
on the point. Together with `presentationSheafIsoPullback` and
`Stacks.AssociatedSheaf.coefficientPointPullbackIsoAssociatedSheaf` this is the comparison of
the three constructions of Stacks 01BH. -/
def presentationSheafIsoAssociatedSheaf (P : N.Presentation) :
    presentationSheaf X α P ≅ (associatedSheafFunctor.{u, u} X α).obj
      ((pointSections.{u, u} (R := R)).obj ((SheafOfModules.forget _).obj N)) :=
  presentationSheafIsoPullback X α P ≪≫
    (coefficientPointPullbackIsoAssociatedSheaf.{u, u} X α).app N

end

end Point

end Stacks.CoefficientPointPresentation

end
