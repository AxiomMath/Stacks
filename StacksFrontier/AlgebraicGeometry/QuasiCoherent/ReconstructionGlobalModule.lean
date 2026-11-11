module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionGlobalSchemeIso
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionGluedModule

/-!
# The single invertible module of [Stacks, Tag 0GPJ]

Let `X` and `Y` be quasi-compact and quasi-separated schemes and let
`e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be an equivalence.  The reconstruction of [Stacks, Tag 0GPJ]
produces opens `V i` covering `Y`, isomorphisms of schemes `f i : V i ≅ U i` and invertible
sheaves `L i` of `𝒪_{V i}`-modules, one per member of an affine open cover `U i` of `X`.  The
scheme half of the conclusion — the single isomorphism `Y ≅ X` — is
`AlgebraicGeometry.exists_schemeIso_of_quasicoherentEquivalence`.  This file supplies the
**single invertible `𝒪_Y`-module**.

## The module is `e(𝒪_X)`

The per-chart sheaves `L i` come out of independent existential choices, one per index, so
nothing about the choices relates two indices.  What relates them is that all of them compute
one and the same global object: the image under `e` of the structure sheaf of `X`.  Indeed the
two isomorphisms `α i` and `β i` of a chart of [Stacks, Tag 0GPJ] read at `𝒪_X` give

`e(𝒪_X)|_{V i} ≅ F_i(𝒪_X|_{U i}) ≅ (f i)^*(𝒪_{U i}) ⊗ L i ≅ 𝒪_{V i} ⊗ L i ≅ L i`,

which is `AlgebraicGeometry.restrictMapUnitIsoOfChartIso`.  The three identifications it uses
are `AlgebraicGeometry.Scheme.Modules.restrictUnitIso` (restriction of the structure sheaf is
the structure sheaf), `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` (inverse image of
the structure sheaf is the structure sheaf) and the right unitor
`AlgebraicGeometry.tensorLeftFunctorObjUnitSchemeIso`.

Two consequences.  First, `e(𝒪_X)` is invertible, invertibility of a module on a scheme being
local on the base.  Second, the transition data that
`AlgebraicGeometry.exists_invertibleModule_of_isOpenCover_of_overlapCompatible` of
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionGluedModule.lean` asks for is
available for the reconstruction's own charts: it is
`AlgebraicGeometry.transOfRestrictIso` of the single module `e(𝒪_X)` together with the above
family of isomorphisms, and its two compatibilities are
`AlgebraicGeometry.transOfRestrictIso_resLE` and `AlgebraicGeometry.transOfRestrictIso_trans`.
The module documentation of that file records the construction of this data as the work that
remained;
`AlgebraicGeometry.exists_isOpenCover_invertibleModule_restrictIso_of_isAffineOpenCover` below
is the gluing run with it supplied.

## Main definitions

* `AlgebraicGeometry.quasicoherentUnit` — the structure sheaf of `X` as an object of
  `QCoh(𝒪_X)`.
* `AlgebraicGeometry.tensorLeftFunctorObjUnitSchemeIso` — the right unitor `L ⊗ 𝒪_Y ≅ L` on a
  scheme, obtained from the symmetry of the sheafified tensor product and the existing left
  unitor.
* `AlgebraicGeometry.restrictMapUnitIsoOfChartIso` — one reconstruction chart read at the
  structure sheaf: `e(𝒪_X)|_V ≅ L`.

## Main results

* `AlgebraicGeometry.isInvertible_map_quasicoherentUnit_of_quasicoherentEquivalence` — **the
  image of the structure sheaf under an equivalence of categories of quasi-coherent modules on
  quasi-compact quasi-separated schemes is an invertible module.**
* `AlgebraicGeometry.exists_isOpenCover_invertibleModule_restrictIso_of_isAffineOpenCover` — the
  global form of [Stacks, Tag 0GPJ] with that module added, obtained by running
  `AlgebraicGeometry.exists_invertibleModule_of_isOpenCover_of_overlapCompatible` on the
  reconstruction's own charts with the transition data supplied.

Neither is an existential in the module: `∃ L, IsInvertible L` is satisfied by the structure
sheaf and would assert nothing.  The first names the module, and the second ties it to the
per-chart sheaves of the reconstruction.

## The rest of [Stacks, Tag 0GPJ]

The tag asserts a single isomorphism of schemes `g : Y ≅ X`, a single invertible `𝒪_Y`-module
`L`, **and** an isomorphism of functors `e(F) ≅ g^*F ⊗ L`.  The first is
`AlgebraicGeometry.exists_schemeIso_of_quasicoherentEquivalence`, the second is here, and the
isomorphism of functors, with the whole statement, is
`AlgebraicGeometry.exists_natIso_pullbackTensorFunctor_of_quasicoherentEquivalence` of
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionGlobalComparison.lean`, which imports
this file.  Nothing below assumes it.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

/- One object is named through two chains of definitions — the structure sheaf of a scheme as
`AlgebraicGeometry.Scheme.ringCatSheaf` and as
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` of its structure presheaf — and
instance search, which works at `reducible` transparency, sees through neither.  The same list
is declared in `StacksFrontier/AlgebraicGeometry/QuasiCoherent/AffineReconstruction.lean`. -/
attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory
  CategoryTheory.sheafCompose TopCat.Sheaf

/-! ### The structure sheaf as a quasi-coherent module -/

/-- **The structure sheaf of `X`, as an object of `QCoh(𝒪_X)`.**  Quasi-coherence is
`AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit`. -/
def quasicoherentUnit (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  ⟨SheafOfModules.unit X.ringCatSheaf, inferInstance⟩

/-- **The right unitor of the tensor product of sheaves of modules on a scheme**, `L ⊗ 𝒪_Y ≅ L`,
with the structure sheaf in the *argument* slot of the tensor functor.  The unitor
`Stacks.SheafOfModules.Invertible.tensorLeftFunctorUnitIso` puts it in the left factor, and
`Stacks.SheafOfModules.Invertible.tensorLeftFunctorSwap` moves it across. -/
def tensorLeftFunctorObjUnitSchemeIso {Y : Scheme.{u}} (L : Y.Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf
            (forget₂ CommRingCat RingCat) Y.ringCatSheaf.2⟩).obj L).obj
        (SheafOfModules.unit Y.ringCatSheaf) ≅ L :=
  Stacks.SheafOfModules.Invertible.tensorLeftFunctorSwap Y.presheaf Y.ringCatSheaf.2
      (SheafOfModules.unit Y.ringCatSheaf) L ≪≫
    (Stacks.SheafOfModules.Invertible.tensorLeftFunctorUnitIso Y.presheaf
      Y.ringCatSheaf.2).app L

/-! ### One reconstruction chart, read at the structure sheaf -/

/-- **A reconstruction chart computes the restriction of `E(𝒪_X)` to be `L`.**  Let
`E : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` be a functor and let `V ⊆ Y`, `U ⊆ X` be opens carrying the data of
one chart of [Stacks, Tag 0GPJ]: a functor `F : QCoh(𝒪_U) ⥤ QCoh(𝒪_V)`, an isomorphism of
schemes `f : V ≅ U`, a sheaf `L` of `𝒪_V`-modules, an isomorphism `α` identifying `E` followed
by restriction to `V` with restriction to `U` followed by `F`, and an isomorphism `β`
identifying `F` with `f^*(-) ⊗ L`.  Then the restriction of `E(𝒪_X)` to `V` is `L`.

Read `α` and then `β` at the structure sheaf and simplify the three resulting occurrences of it:
its restriction to `U` is the structure sheaf of `U`
(`AlgebraicGeometry.Scheme.Modules.restrictUnitIso`), whose inverse image along `f` is the
structure sheaf of `V` (`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`), which the
right unitor then absorbs.

This is what makes the per-chart sheaves of the reconstruction comparable: they are all
restrictions of one global module, and nothing about the existential choices that produced them
is needed. -/
def restrictMapUnitIsoOfChartIso {X Y : Scheme.{u}}
    (E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
    {V : Y.Opens} {U : X.Opens}
    {F : (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).FullSubcategory}
    (f : V.toScheme ≅ U.toScheme) (L : SheafOfModules.{u} V.toScheme.ringCatSheaf)
    (α : E ⋙ quasicoherentRestriction V.ι ≅ quasicoherentRestriction U.ι ⋙ F)
    (β : F ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf) ≅
      pullbackTensorFunctor f.hom L) :
    Scheme.Modules.restrict (E.obj (quasicoherentUnit X)).obj V.ι ≅ L :=
  (ObjectProperty.ι (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf)).mapIso
      (α.app (quasicoherentUnit X)) ≪≫
    β.app ((quasicoherentRestriction U.ι).obj (quasicoherentUnit X)) ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨V.toScheme.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ V.toScheme.presheaf
          (forget₂ CommRingCat RingCat) V.toScheme.ringCatSheaf.2⟩).obj L).mapIso
      ((Scheme.Modules.pullback f.hom).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
        AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f.hom) ≪≫
    tensorLeftFunctorObjUnitSchemeIso L

/-! ### The single invertible module -/

section Reconstruction

variable {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
  [QuasiSeparatedSpace Y]
  (e : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)

include e

/-- **The image of the structure sheaf under an equivalence of categories of quasi-coherent
modules is invertible.**  Let `X` and `Y` be quasi-compact and quasi-separated schemes and let
`e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be an equivalence.  Then `e(𝒪_X)` is an invertible `𝒪_Y`-module.

Invertibility of a module on a scheme is local on the base
(`Stacks.Modules.isInvertible_of_isInvertible_restrict_isOpenCover`), the opens `V i` of the
reconstruction cover `Y`, and over each of them `e(𝒪_X)` is the invertible sheaf `L i` of that
chart by `AlgebraicGeometry.restrictMapUnitIsoOfChartIso`. -/
theorem isInvertible_map_quasicoherentUnit_of_quasicoherentEquivalence :
    Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (e.functor.obj (quasicoherentUnit X)).obj := by
  obtain ⟨V, hVcover, hVrest⟩ :=
    exists_isOpenCover_schemeIso_invertibleSheaf_of_isAffineOpenCover e
      (fun i : X.affineOpens => (i : X.Opens)) (fun i => i.2) (iSup_affineOpens_eq_top X)
  choose hVaff hVc F f L hFequiv hLinv hα hβ using hVrest
  refine Stacks.Modules.isInvertible_of_isInvertible_restrict_isOpenCover _ V hVcover fun i => ?_
  have := hLinv i
  exact Stacks.SheafOfModules.isInvertible_of_iso (V i).toScheme.presheaf
    (V i).toScheme.ringCatSheaf.2
    (restrictMapUnitIsoOfChartIso e.functor (f i) (L i) (hα i).some (hβ i).some).symm

/-- **The global form of [Stacks, Tag 0GPJ] with the per-chart invertible sheaves glued into one
invertible module.**  Let `X` and `Y` be quasi-compact and quasi-separated schemes, let
`e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be an equivalence and let `U i` be an affine open cover of `X`.
Then there are opens `V i` covering `Y`, each affine, and for each `i` an equivalence
`F i : QCoh(𝒪_{U i}) ≌ QCoh(𝒪_{V i})` compatible with `e` and the two restrictions, an
isomorphism of schemes `f i : V i ≅ U i` and an invertible sheaf `L i` of `𝒪_{V i}`-modules with
`F i` inverse image along `f i` followed by `- ⊗ L i` — **and a single invertible `𝒪_Y`-module
`M` whose restriction to each `V i` is `L i`**.

This is
`AlgebraicGeometry.exists_isOpenCover_schemeIso_invertibleSheaf_of_isAffineOpenCover` with the
families pulled out of the per-index existential, together with
`AlgebraicGeometry.exists_invertibleModule_of_isOpenCover_of_overlapCompatible` run on those
charts.  The three transition hypotheses of the gluing are
`AlgebraicGeometry.transOfRestrictIso`, `AlgebraicGeometry.transOfRestrictIso_resLE` and
`AlgebraicGeometry.transOfRestrictIso_trans` for the module `e(𝒪_X)`, which restricts to each
`L i` by `AlgebraicGeometry.restrictMapUnitIsoOfChartIso`. -/
theorem exists_isOpenCover_invertibleModule_restrictIso_of_isAffineOpenCover {κ : Type u}
    (U : κ → X.Opens) (hUaff : ∀ i, IsAffineOpen (U i)) (hUcover : IsOpenCover U) :
    ∃ (V : κ → Y.Opens)
      (F : ∀ i, (SheafOfModules.isQuasicoherent (U i).toScheme.ringCatSheaf).FullSubcategory ⥤
        (SheafOfModules.isQuasicoherent (V i).toScheme.ringCatSheaf).FullSubcategory)
      (f : ∀ i, (V i).toScheme ≅ (U i).toScheme)
      (L : ∀ i, SheafOfModules.{u} (V i).toScheme.ringCatSheaf) (M : Y.Modules),
      IsOpenCover V ∧ (∀ i, IsAffineOpen (V i)) ∧ (∀ i, (F i).IsEquivalence) ∧
        (∀ i, Stacks.SheafOfModules.IsInvertible (V i).toScheme.presheaf
          (V i).toScheme.ringCatSheaf.2 (L i)) ∧
        (∀ i, Nonempty (e.functor ⋙ quasicoherentRestriction (V i).ι ≅
          quasicoherentRestriction (U i).ι ⋙ F i)) ∧
        (∀ i, Nonempty (F i ⋙ ObjectProperty.ι
            (SheafOfModules.isQuasicoherent (V i).toScheme.ringCatSheaf) ≅
          pullbackTensorFunctor (f i).hom (L i))) ∧
        Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M ∧
        ∀ i, Nonempty (Scheme.Modules.restrict M (V i).ι ≅ L i) := by
  obtain ⟨V, hVcover, hVrest⟩ :=
    exists_isOpenCover_schemeIso_invertibleSheaf_of_isAffineOpenCover e U hUaff hUcover
  choose hVaff hVc F f L hFequiv hLinv hα hβ using hVrest
  have hres : ∀ i, Scheme.Modules.restrict (e.functor.obj (quasicoherentUnit X)).obj (V i).ι ≅
      L i := fun i =>
    restrictMapUnitIsoOfChartIso e.functor (f i) (L i) (hα i).some (hβ i).some
  obtain ⟨M, hMrest, hMinv⟩ :=
    exists_invertibleModule_of_isOpenCover_of_overlapCompatible V hVcover L hLinv
      (transOfRestrictIso _ hres) (transOfRestrictIso_resLE _ hres)
      (transOfRestrictIso_trans _ hres)
  exact ⟨V, F, f, L, M, hVcover, hVaff, hFequiv, hLinv, hα, hβ, hMinv, hMrest⟩

end Reconstruction

end AlgebraicGeometry

end
