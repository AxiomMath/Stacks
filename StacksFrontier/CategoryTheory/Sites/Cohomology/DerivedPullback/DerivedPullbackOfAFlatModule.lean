module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CoefficientChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOnKFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
import StacksCore.Tactic.StacksAttribute

/-!
# The derived pullback of a flat module placed in one degree

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi presented by a morphism of
the underlying sites and let `ℳ` be a *flat* sheaf of `𝒪_D`-modules. This file identifies the
derived pullback of `ℳ` placed in a single degree with the degreewise pullback placed in that
degree:

`Lf^*(ℳ[q]) ≅ (f^*ℳ)[q]`.

This is the step the Stacks Project writes as `Li^* = i^*`: for a flat module there is nothing
to derive. The source uses it in [Stacks, Tag 08PU], where `Li^*Ω_{𝒪/A} = i^*Ω_{𝒪/A}` is
justified by the freeness of the differentials of each object of the site, and it is the only
general mechanism by which a derived pullback of a module can be computed by an ordinary one.

The statement is then specialised to a change of coefficient rings on a fixed site, which is the
shape derived extension of scalars takes in this development
(`Stacks.Cohomology.derivedCoefficientChange`): the underlying morphism of sites is the identity,
so the hypothesis that `f` is presented by a morphism of sites is discharged outright and the
specialisation carries no hypothesis beyond the flatness of `ℳ`.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.derivedPullbackSingleIso`: **`Lf^*(ℳ[q]) ≅ (f^*ℳ)[q]`** for a
  flat `ℳ`, at an arbitrary morphism of ringed topoi presented by a morphism of sites.
* `Stacks.Cohomology.derivedCoefficientChangeSingleIso`: the same at a change of coefficient
  rings `α : 𝒪 ⟶ 𝒪'` on a fixed site, where the degreewise functor is extension of scalars
  along `α`.

## Main results

* `Stacks.Sheaves.DerivedPullback.isFlat_single_X`: every term of `ℳ[q]` is flat when `ℳ` is.

## Implementation notes

**What is new here.** The two inputs are
`Stacks.Sheaves.DerivedPullback.flatPullbackIso` ([Stacks, Tag 06YY]: a K-flat complex with flat
terms computes the derived pullback) and
`Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat` (a flat module in one degree is a
K-flat complex). What this file adds is `isFlat_single_X` — the terms of `ℳ[q]` are `ℳ` in degree
`q` and zero elsewhere, both flat — and the assembly, in which
`HomologicalComplex.singleMapHomologicalComplex` moves the degreewise pullback past the
placement in a degree.

This generalises `Stacks.Sheaves.DerivedPullback.derivedPullbackSingleUnitIso`, which is the
case `ℳ = 𝒪_D` of the same argument: there the flatness input is
`Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit` and the degree is `0`.

**Why the coefficient-change form is unconditional.** `Stacks.Cohomology.derivedCoefficientChange`
is the derived pullback along `AlgebraicGeometry.RingedToposSiteHom.coefficientChange`, whose
underlying functor of sites is `𝟭 C`; `CategoryTheory.Functor.isMorphismOfSites_id` discharges
`hmos`. The degreewise functor there is extension of scalars: the pullback of the ringed topos
of a coefficient change is `Stacks.Sheaves.ModuleAdjunction.extendScalars` of the induced map of
sheaves of rings, by `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos_coefficientChange`,
which holds by `rfl`.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY), the derived pullback and
  its computation on K-flat complexes with flat terms.
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU), whose proof uses
  `Li^* = i^*` for a flat module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.DerivedPullback.KFlatPullback

namespace Stacks.Sheaves.DerivedPullback

universe u

/-! ## A flat module placed in one degree is a complex with flat terms -/

section Flatness

variable (Y : RingedTopos.{u, u, u})
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Every term of `ℳ[q]` is flat when `ℳ` is.** In degree `q` the term is `ℳ` itself, and in
every other degree it is a zero object, which is flat by
`Stacks.SheafOfModules.DerivedTensorProduct.isFlat_of_isZero`. -/
theorem isFlat_single_X
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) M) (q i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      (((HomologicalComplex.single
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ) q).obj M).X i) := by
  by_cases h : i = q
  · subst h
    exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso Y.O
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i M).symm hM
  · exact Stacks.SheafOfModules.DerivedTensorProduct.isFlat_of_isZero
      (Y := ⟨Y.C, Y.J, Y.O⟩) _
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) q M i h)

end Flatness

/-! ## `Lf^*(ℳ[q]) ≅ (f^*ℳ)[q]` -/

section Derived

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]

/-- **The derived pullback of a flat module placed in one degree is its degreewise pullback
placed in that degree**: `Lf^*(ℳ[q]) ≅ (f^*ℳ)[q]`.

A flat module in one degree is a K-flat complex
(`Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat`) with flat terms
(`isFlat_single_X`), so `Stacks.Sheaves.DerivedPullback.flatPullbackIso` computes the derived
pullback by the degreewise pullback; and the degreewise pullback of a complex concentrated in
one degree is the pullback of its one module placed in that degree, by
`HomologicalComplex.singleMapHomologicalComplex`.

This is the step [Stacks, Tag 08PU] writes as `Li^* = i^*`. -/
def derivedPullbackSingleIso (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) M) (q : ℤ) :
    (derivedPullback f).obj
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) q).obj M) ≅
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).obj
        (f.pullbackTopos.obj M) :=
  flatPullbackIso f hmos
      ((HomologicalComplex.single
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ) q).obj M)
      (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat Y.O M hM q)
      (isFlat_single_X Y M hM q) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex f.pullbackTopos
          (ComplexShape.up ℤ) q).app M)

end Derived

end Stacks.Sheaves.DerivedPullback

/-! ## The case of a change of coefficient rings -/

namespace Stacks.Cohomology

universe u

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {O O' : Sheaf J CommRingCat.{u}}

/-- **Derived extension of scalars of a flat module placed in one degree is ordinary extension
of scalars**: for `α : 𝒪 ⟶ 𝒪'` a map of sheaves of commutative rings on a fixed site and `ℳ` a
flat sheaf of `𝒪`-modules,

`(ℳ ⊗^𝐋_𝒪 𝒪')[q] = (ℳ ⊗_𝒪 𝒪')[q]`.

The underlying morphism of sites of a coefficient change is the identity functor, which is a
morphism of sites, so this instance of
`Stacks.Sheaves.DerivedPullback.derivedPullbackSingleIso` carries no hypothesis beyond the
flatness of `ℳ`. The degreewise functor on the right is
`Stacks.Sheaves.ModuleAdjunction.extendScalars` along the induced map of sheaves of rings, by
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos_coefficientChange`. -/
def derivedCoefficientChangeSingleIso (α : O ⟶ O')
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos J O).O))
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := O) M) (q : ℤ) :
    (derivedCoefficientChange α).obj
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
              (ringedTopos J O).O)) q).obj M) ≅
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
            (ringedTopos J O').O)) q).obj
        ((AlgebraicGeometry.RingedToposSiteHom.coefficientChange.{u, u, u} J α).pullbackTopos.obj
          M) :=
  Stacks.Sheaves.DerivedPullback.derivedPullbackSingleIso
    (AlgebraicGeometry.RingedToposSiteHom.coefficientChange.{u, u, u} J α)
    (Functor.isMorphismOfSites_id J) M hM q

end Stacks.Cohomology

end
