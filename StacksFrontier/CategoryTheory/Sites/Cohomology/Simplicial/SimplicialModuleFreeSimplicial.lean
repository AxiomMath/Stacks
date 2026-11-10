module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ExtensionByZeroLowerShriekModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.DerivedProjectionMooreComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModuleLowerShriekColim
import StacksCore.Tactic.StacksAttribute

/-!
# The fibrewise reading of `j_{W!}O_W` is a free simplicial module

Let `(C, J)` be a small site, let `O` be a sheaf of rings on it and let `π : Δ × C ⥤ C` be the
projection of Stacks 09D0. For an object `W = (m, U)` of `Δ × C`, the extension by zero
`j_{W!}(π^{-1}O)_W` — the generator of `Mod(π^{-1}O)` that the resolution of Stacks 06XX is built
from — is, read fibrewise, the free simplicial object `∐_{Mor_Δ(-, m)} j_{U!}O_U`.

This is the module-coefficient form of
`Stacks.SimplicialModules.fibrewiseExtensionByZeroUnitAbIso`, and the route is the same: `(i_m)_!`
read fibrewise is the left adjoint of evaluation in degree `m`, whose values are the free
simplicial objects. Both inputs on the simplicial side are already stated at arbitrary abelian
coefficients — `Stacks.SimplicialModules.evaluationLeftAdjointObjIsoFreeSimplicial` and
`Stacks.ChaoticSite.SimplexValued.freeSimplicial` — so only the module-coefficient halves are
new here.

## Main results

* `Stacks.SimplicialModules.fibreAdjunctionMod`: the adjunction `(i_m)_! ⊣ (i_m)^{-1}` on sheaves
  of modules.
* `Stacks.SimplicialModules.fibreExtensionModCompFibrewiseIso`: `(i_m)_!` read fibrewise is the
  left adjoint of evaluation in degree `m`.
* `Stacks.SimplicialModules.fibrewiseModExtensionByZeroUnitIso`: **the fibrewise reading of
  `j_{W!}(π^{-1}O)_W` is a free simplicial module.**

## References

* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

namespace Stacks.SimplicialModules

open Stacks.Cohomology.DerivedLowerShriek

universe w

variable (C : Type w) [SmallCategory C] (J : GrothendieckTopology C)
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  (O : Sheaf J RingCat.{w})
  [HasWeakSheafify (projectionTopology C J) AddCommGrpCat.{w}]
  [(projectionTopology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(SheafOfModules.pushforward.{w} (F := projection C)
    (idRingMap (projectionTopology C J) J (projection C) O)).IsRightAdjoint]

/-- **Coproducts of sheaves of modules indexed by a `Type`.** This is
`Stacks.SheafOfModules.FlatCoproduct.hasColimitsOfShape_discrete` with its index universe shrunk
to `Type`; instance search does not get there on its own. The free simplicial objects of
`Stacks.ChaoticSite.SimplexValued.freeSimplicial` need exactly these, their index sets being
hom-sets of `Δ`. This is the module-coefficient form of
`Stacks.SimplicialModules.hasColimitsOfShape_discrete_type_sheafAb`. -/
instance hasColimitsOfShape_discrete_type_sheafOfModules {E : Type w} [SmallCategory E]
    {L : GrothendieckTopology E} (R : Sheaf L RingCat.{w})
    [HasWeakSheafify L AddCommGrpCat.{w}] [L.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (ι : Type) :
    HasColimitsOfShape (Discrete ι) (SheafOfModules.{w} R) :=
  haveI := Stacks.SheafOfModules.FlatCoproduct.hasColimitsOfShape_discrete R (ULift.{w} ι)
  hasColimitsOfShape_of_equivalence
    (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w} ι) ≌ Discrete ι)

/-- **Coproducts of sheaves of modules indexed by a type of `Type 0`.** This is what the free
simplicial objects over `Δ` ask for, the hom-sets of `Δ` being in `Type 0`. -/
instance hasCoproducts_zero_sheafOfModules {E : Type w} [SmallCategory E]
    {L : GrothendieckTopology E} (R : Sheaf L RingCat.{w})
    [HasWeakSheafify L AddCommGrpCat.{w}] [L.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    HasCoproducts.{0} (SheafOfModules.{w} R) :=
  fun ι => hasColimitsOfShape_discrete_type_sheafOfModules R ι

/-- `(i_m)_!`, the lower-shriek functor of the fibre inclusion on sheaves of modules: the left
adjoint of evaluation in degree `m`. Its structure map of sheaves of rings is the identity, by
`Stacks.SimplicialModules.fibreRingMap`. -/
abbrev fibreExtensionMod (m : SimplexCategory) :
    SheafOfModules.{w} O ⥤ SheafOfModules.{w} (projectionRing C J O) :=
  Stacks.SheafOfModules.lowerShriek.{w} J (projectionTopology C J) (fibreInclusion C m)
    (projectionRing C J O)

/-- **The adjunction `(i_m)_! ⊣ (i_m)^{-1}` on sheaves of modules.** The right adjoint is
restriction along the fibre inclusion, which is `Stacks.SimplicialModules.fibreRestrictionMod`:
both are `SheafOfModules.pushforward` for the identity morphism of sheaves of rings. -/
def fibreAdjunctionMod (m : SimplexCategory) :
    fibreExtensionMod C J O m ⊣ fibreRestrictionMod C J O m :=
  Stacks.SheafOfModules.lowerShriekAdjunction.{w} J (projectionTopology C J)
    (fibreInclusion C m) (projectionRing C J O)

/-- **Uncurrying a simplicial sheaf of modules and restricting to the fibre over `m` gives back
its degree `m`.** This is `Stacks.SimplicialModules.uncurryModFibrewiseIso` evaluated in degree
`m`, available in this shape because restriction along `i_m` is evaluation of the fibrewise
reading on the nose (`Stacks.SimplicialModules.fibrewiseMod_comp_evaluation`). -/
def uncurryModCompFibreRestrictionIso (m : SimplexCategory) :
    uncurryMod C J O ⋙ fibreRestrictionMod C J O m ≅
      (evaluation SimplexCategoryᵒᵖ (SheafOfModules.{w} O)).obj (op m) :=
  Functor.isoWhiskerRight (uncurryModFibrewiseIso C J O)
      ((evaluation SimplexCategoryᵒᵖ (SheafOfModules.{w} O)).obj (op m)) ≪≫
    Functor.leftUnitor _

/-- **`(i_m)_!` read fibrewise is left adjoint to evaluation in degree `m`.** Compose the
adjunction `(i_m)_! ⊣ (i_m)^{-1}` with the equivalence `fibrewiseMod ⊣ uncurryMod` and identify
the resulting right adjoint with evaluation by
`Stacks.SimplicialModules.uncurryModCompFibreRestrictionIso`. -/
def fibreExtensionModCompFibrewiseAdjunction (m : SimplexCategory) :
    fibreExtensionMod C J O m ⋙ fibrewiseMod C J O ⊣
      (evaluation SimplexCategoryᵒᵖ (SheafOfModules.{w} O)).obj (op m) :=
  Adjunction.ofNatIsoRight
    ((fibreAdjunctionMod C J O m).comp (simplicialModuleEquivalence C J O).toAdjunction)
    (uncurryModCompFibreRestrictionIso C J O m)

/-- **`(i_m)_!` read fibrewise is the left adjoint of evaluation in degree `m`.** Both are left
adjoints of the same functor — the first by
`Stacks.SimplicialModules.fibreExtensionModCompFibrewiseAdjunction`, the second by Mathlib's
`CategoryTheory.evaluationAdjunctionRight` — and left adjoints of one functor agree. -/
def fibreExtensionModCompFibrewiseIso (m : SimplexCategory) :
    fibreExtensionMod C J O m ⋙ fibrewiseMod C J O ≅
      evaluationLeftAdjoint (SheafOfModules.{w} O) (op m) :=
  Adjunction.leftAdjointUniq (fibreExtensionModCompFibrewiseAdjunction C J O m)
    (evaluationAdjunctionRight (SheafOfModules.{w} O) (op m))

variable [∀ V : SimplexCategory × C, (SheafOfModules.pushforward.{w} (F := Over.forget V)
    (𝟙 ((projectionRing C J O).over V) :
      (projectionRing C J O).over V ⟶ (projectionRing C J O).over V)).IsRightAdjoint]
  [∀ U : C, (SheafOfModules.pushforward.{w} (F := Over.forget U)
    (𝟙 (O.over U) : O.over U ⟶ O.over U)).IsRightAdjoint]

/-- **The extension by zero of the structure sheaf at a representable of the simplicial site,
read fibrewise, is a free simplicial module.** For `W = (m, U)`, `j_{W!}(π^{-1}O)_W` is
`(i_m)_!(j_{U!}O_U)`
(`Stacks.Cohomology.DerivedLowerShriek.lowerShriekExtensionByZeroUnitIso`, which is Stacks 07AC
for the fibre inclusion), reading `(i_m)_!` fibrewise gives the left adjoint of evaluation at
`op m` (`Stacks.SimplicialModules.fibreExtensionModCompFibrewiseIso`), and that left adjoint has
the free simplicial objects as its values
(`Stacks.SimplicialModules.evaluationLeftAdjointObjIsoFreeSimplicial`). -/
def fibrewiseModExtensionByZeroUnitIso (W : SimplexCategory × C) :
    (fibrewiseMod C J O).obj (extensionByZeroUnit (projectionRing C J O) W) ≅
      Stacks.ChaoticSite.SimplexValued.freeSimplicial W.1 (extensionByZeroUnit O W.2) :=
  (fibrewiseMod C J O).mapIso
      (lowerShriekExtensionByZeroUnitIso.{w} J (projectionTopology C J)
        (fibreInclusion C W.1) (projectionRing C J O) W.2).symm ≪≫
    (fibreExtensionModCompFibrewiseIso C J O W.1).app (extensionByZeroUnit O W.2) ≪≫
    evaluationLeftAdjointObjIsoFreeSimplicial W.1 (extensionByZeroUnit O W.2)

/-! ### The Moore augmentation of a term of the resolution -/

variable [HasColimitsOfShape SimplexCategoryᵒᵖ (SheafOfModules.{w} O)]

omit [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  [(SheafOfModules.pushforward.{w} (F := projection C)
    (idRingMap (projectionTopology C J) J (projection C) O)).IsRightAdjoint]
  [HasColimitsOfShape SimplexCategoryᵒᵖ (SheafOfModules.{w} O)] in
/-- **The Moore complex of the fibrewise reading of a direct sum of extensions by zero of the
structure sheaf has no homology in positive degrees.** Such a sheaf of modules is a direct sum of
the `j_{W!}(π^{-1}O)_W`, `fibrewiseMod` is an equivalence and so carries that direct sum to a
direct sum of the fibrewise readings, each of which is a free simplicial module
(`Stacks.SimplicialModules.fibrewiseModExtensionByZeroUnitIso`); the vanishing holds for a free
simplicial object by contractibility of the standard simplex
(`Stacks.ChaoticSite.SimplexValued.isZero_homology_alternatingFaceMapComplex_freeSimplicial_succ`)
and passes to direct sums because coproducts of sheaves of modules are exact. -/
theorem isZero_homology_alternatingFaceMapComplex_fibrewiseMod_succ
    (P : SheafOfModules.{w} (projectionRing C J O))
    (hP : IsSumOfExtensionByZeroUnits (projectionRing C J O) P) (k : ℕ) :
    IsZero (((alternatingFaceMapComplex (SheafOfModules.{w} O)).obj
      ((fibrewiseMod C J O).obj P)).homology (k + 1)) := by
  obtain ⟨ι, W, ⟨e⟩⟩ := hP
  have hiso :
      (fibrewiseMod C J O).obj P ≅
        ∐ fun i : ι => Stacks.ChaoticSite.SimplexValued.freeSimplicial (W i).1
          (extensionByZeroUnit O (W i).2) :=
    (fibrewiseMod C J O).mapIso e.symm ≪≫
      PreservesCoproduct.iso (fibrewiseMod C J O)
        (fun i : ι => extensionByZeroUnit (projectionRing C J O) (W i)) ≪≫
      Sigma.whiskerEquiv (Equiv.refl ι)
        (fun i => (fibrewiseModExtensionByZeroUnitIso C J O (W i)).symm)
  refine ChaoticSite.SimplexValued.isZero_homology_alternatingFaceMapComplex_of_iso
    hiso (k + 1) ?_
  exact ChaoticSite.SimplexValued.isZero_homology_alternatingFaceMapComplex_succ_of_coproduct _
    (fun i n =>
      ChaoticSite.SimplexValued.isZero_homology_alternatingFaceMapComplex_freeSimplicial_succ
        _ _ n) k

omit [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  [(SheafOfModules.pushforward.{w} (F := projection C)
    (idRingMap (projectionTopology C J) J (projection C) O)).IsRightAdjoint] in
/-- **The Moore augmentation of the fibrewise reading of a direct sum of extensions by zero of
the structure sheaf is a quasi-isomorphism.** This is the hypothesis `haug` of
`Stacks.ChaoticSite.GeneralValued.mooreCochainQIsoColimOfResolution` at the terms of the
resolution that Stacks 06XX produces: over `Δ` with the tautological cosimplicial object `𝟭 Δ`
the cokernel presentation of the colimit injection needs no hypothesis at all
(`Stacks.ChaoticSite.SimplexValued.colimitIotaZeroIsColimit`), so the only input is the
positive-degree vanishing
`Stacks.SimplicialModules.isZero_homology_alternatingFaceMapComplex_fibrewiseMod_succ`. -/
theorem quasiIso_mooreCochainAugmentation_fibrewiseMod
    (P : SheafOfModules.{w} (projectionRing C J O))
    (hP : IsSumOfExtensionByZeroUnits (projectionRing C J O) P) :
    QuasiIso ((Stacks.ChaoticSite.GeneralValued.mooreCochainAugmentation
      (𝟭 SimplexCategory)).app ((fibrewiseMod C J O).obj P)) :=
  Stacks.ChaoticSite.SimplexValued.quasiIso_mooreCochainAugmentation_of_isZero _
    fun k => isZero_homology_alternatingFaceMapComplex_fibrewiseMod_succ C J O P hP k

end Stacks.SimplicialModules

end
