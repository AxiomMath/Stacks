module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorQuasicoherentOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DegreeZeroComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The derived tensor product of complexes with quasi-coherent cohomology on an algebraic space

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let
`D_QCoh(𝒪_X) ⊆ D(𝒪_X)` be the full subcategory of Stacks 071X cut out by quasi-coherence of
every cohomology sheaf.  Stacks 08F5 asserts that this subcategory is closed under the derived
tensor product.  This file proves the closure for the two arguments that the development can
compute: a pair of quasi-coherent `𝒪_X`-modules placed in degree zero, one of which is K-flat
there.

For such a pair the derived tensor product *is* an ordinary tensor product placed in degree
zero — `Stacks.SheafOfModules.DerivedTensorProduct.tensorSingleIso` — so its cohomology sheaves
are `M ⊗_{𝒪_X} N` in degree zero and zero elsewhere, and quasi-coherence of the first is
Stacks 03L6 for a ringed site.  No resolution of a complex is involved, which is what makes the
case reachable; see "What is not proved" below.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.isQuasicoherentOnSite_sheafTensor`: Stacks 03L6
  in the spelling of the derived tensor product, the tensor product of two quasi-coherent
  sheaves of modules on a ringed site being quasi-coherent.
* `Stacks.SheafOfModules.DerivedTensorProduct.isQuasicoherentOnSite_homology_tensor_single`:
  on any ringed site, every cohomology sheaf of `M[0] ⊗^L_𝒪 N[0]` is quasi-coherent as soon as
  `M` and `N` are and `M[0]` is K-flat.
* `Stacks.SheafOfModules.DerivedTensorProduct.isQuasicoherentOnSite_homology_tensor_single'`:
  the same with the K-flatness hypothesis on the right factor.
* `AlgebraicGeometry.Space.derivedQuasicoherent_derivedTensor_single`: **Stacks 08F5** for that
  pair of arguments on an algebraic space, stated as membership in `D_QCoh(𝒪_X)`.
* `AlgebraicGeometry.Space.derivedQuasicoherent_derivedTensor_single'`: the same with the
  K-flatness hypothesis on the right factor.

## Implementation notes

*The derived tensor product is a parameter, not a construction.*  `⊗^L_{𝒪_X}` enters as a term
`T : Stacks.SheafOfModules.DerivedTensorProduct` of the structure that packages a derived tensor
bifunctor with its K-flat comparisons, exactly as in
`Stacks.EtaleCohomology.ConstructibleFiniteTorDerivedCategory` of Stacks 03TQ, which takes the
same datum on the slices of a ringed site.  That structure is stated at
`AlgebraicGeometry.RingedSite.{u + 1, u, u}` and so is available over
`AlgebraicGeometry.Space.smallEtaleRingedSite`; what is *not* available there is an inhabitant,
and that is recorded under "What is not proved".

*The two spellings of the category of `𝒪_X`-modules.*  `AlgebraicGeometry.Space.Modules` is
stated over `AlgebraicGeometry.RingedSite.ringSheaf` of the small étale ringed site, and the
derived tensor product over `Stacks.SheafOfModules.Tensor.ringSheaf` of its structure sheaf.
The two are definitionally equal — both compose the structure sheaf with
`CategoryTheory.forget₂ CommRingCat RingCat` and the sheaf condition is a proposition — so
`AlgebraicGeometry.RingedSite.Modules (smallEtaleRingedSite B S hS F hF)` and
`AlgebraicGeometry.Space.Modules.{u, u} B S hS F hF` are the same category by `rfl`, and no
transport appears below.  The same equality is what lets Stacks 03L6 in the spelling
`Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isQuasicoherentOnSite`, whose tensor
product is `Stacks.SheafOfModules.Tensor.sheafTensor`, discharge quasi-coherence of
`Stacks.SheafOfModules.Tensor.sheafTensor`.

*Why the module universe is the universe of the schemes.*  Stacks 03L6 is used at a module
universe independent of the site's, so it applies on the small étale site at the module
universe `u` of the structure rings; the sheafification instances available there, from
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify`, are at that same universe.  The
equi-universe form `Stacks.SheafOfModules.isQuasicoherentOnSite_tensorSheaf` would demand
modules at `max (u + 1) u = u + 1` and does not apply.

*The cohomology of a single complex.*  `((DerivedCategory.singleFunctor _ 0).obj M).IsLE 0` and
`.IsGE 0` are Mathlib instances, so `DerivedCategory.isZero_of_isLE` and `isZero_of_isGE` give
the vanishing away from degree zero, and
`DerivedCategory.singleFunctorCompHomologyFunctorIso` the value at degree zero.  A zero sheaf of
modules is quasi-coherent by `SheafOfModules.IsQuasicoherentOnSite.of_isZero`, with no weak
Serre hypothesis.

## What is not proved

Stacks 08F5 for arbitrary `K` and `L` of `D_QCoh(𝒪_X)` is **not** proved here, and no
declaration below states it.  Four inputs are missing, each verified absent:

1. *No inhabitant of the derived tensor product.*  Both constructions —
   `Stacks.SheafOfModules.nonempty_derivedTensorProduct_of_exact` and
   `Stacks.DerivedTensor.RingedSite.exists_derivedTensorProduct` — are stated for a site with
   `CategoryTheory.SmallCategory`, that is for `AlgebraicGeometry.RingedSite.{u, u, u}`, whereas
   `AlgebraicGeometry.Space.smallEtaleRingedSite` is an
   `AlgebraicGeometry.RingedSite.{u + 1, u, u}`.  This is why `T` is a parameter.
2. *No K-flat resolutions.*  `Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution`
   (Stacks 06YS) carries the same `CategoryTheory.SmallCategory` hypothesis, so neither `K` nor
   `L` can be replaced by a complex on which `T.comparison` computes.  That is the reason the
   arguments here are single complexes, for which the comparison applies with no resolution:
   `Stacks.SheafOfModules.isKFlat_single_unit` does not help either, being stated for a
   structure sheaf at the universe `max u v = u + 1` of the site's objects rather than at `u`.
3. *Quasi-coherence is not known to be a weak Serre class.*  Any dévissage from single complexes
   to general ones reads cohomology sheaves of complexes with quasi-coherent terms, hence needs
   closure under kernels and cokernels.  For the small étale site of an algebraic space those
   are the hypotheses `(isQuasicoherentOnSite _).IsClosedUnderKernels` and
   `.IsClosedUnderCokernels` of Stacks 03M1 which
   `AlgebraicGeometry.Space.quasicoherentSheaves_isWeakSerreClass` carries and which this
   development never discharges; the only unconditional weak Serre class for
   `SheafOfModules.isQuasicoherentOnSite` is on a chaotic site with flat restrictions
   (`Stacks.SheafOfModules.isQuasicoherentOnSite_isWeakSerreClass`).
4. *No étale-pullback comparison for the derived tensor product.*  The route of the source —
   pull back along a surjective étale `φ : U → X` and invoke the case of a scheme — needs
   Stacks 079U for algebraic spaces, of which the development has only the ringed-space form
   `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`, and would land in
   `D(𝒪_U)` for the small étale site of `U`, not in the Zariski-based `D(𝒪_U)` of
   `Stacks.Duality.isQuasicoherent_homology_derivedTensor` (Stacks 08DX for a scheme).

## References

* [Stacks Project, Tag 08F5](https://stacks.math.columbia.edu/tag/08F5)
* [Stacks Project, Tag 071X](https://stacks.math.columbia.edu/tag/071X)
* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace Stacks.SheafOfModules.DerivedTensorProduct

open AlgebraicGeometry

section Underived

variable {X : AlgebraicGeometry.RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks 03L6 in the spelling of the derived tensor product.**  The tensor product
`Stacks.SheafOfModules.Tensor.sheafTensor` of two quasi-coherent sheaves of modules on a ringed
site is quasi-coherent.

This is `Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isQuasicoherentOnSite`, whose
tensor product is `Stacks.SheafOfModules.Tensor.sheafTensor` and whose sheaf of rings is
`CategoryTheory.Sheaf.toRingCat`, read at the two spellings the derived tensor product uses,
namely `Stacks.SheafOfModules.Tensor.sheafTensor` over
`Stacks.SheafOfModules.Tensor.ringSheaf`.  The two tensor products and the two sheaves of rings
are definitionally equal, so the content is the cited theorem and nothing more.

The `CategoryTheory.GrothendieckTopology.HasSheafCompose` argument is supplied as
`AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat` rather than left to instance
search.  That is load-bearing and not cosmetic: the instance Mathlib finds is size-restricted
and leaves the universe of the module sections an unsolved metavariable, so the application dies
on a stuck `UnivLE` constraint, whereas this one keeps that universe free — which is exactly
what the ringed site of an algebraic space needs, its objects living one universe above its
sections.  Both quasi-coherence hypotheses are passed explicitly for the same reason: typeclass
matching does not cross the two spellings of the sheaf of rings, `Tensor.ringSheaf` not
unfolding to `Sheaf.toRingCat` at reducible transparency. -/
@[ega "I 9.1.1" "more general", ega "IV 8.2.7" "case A = O_S"]
theorem isQuasicoherentOnSite_sheafTensor
    (M N : AlgebraicGeometry.RingedSite.Modules.{u, v, w} X)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).obj
      N).IsQuasicoherentOnSite :=
  @Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isQuasicoherentOnSite
    _ _ X.J (AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat X) _ _
    X.O M N hM hN

end Underived

section Single

variable {X : AlgebraicGeometry.RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X)]

/-- Every cohomology sheaf of a module placed in degree zero is quasi-coherent as soon as the
module is: in degree zero it *is* the module, and in every other degree it is a zero object,
which is quasi-coherent with no weak Serre hypothesis. -/
theorem isQuasicoherentOnSite_homology_single
    (M : AlgebraicGeometry.RingedSite.Modules.{u, v, w} X)
    (hM : M.IsQuasicoherentOnSite) (n : ℤ) :
    ((DerivedCategory.homologyFunctor (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) n).obj
      ((DerivedCategory.singleFunctor
        (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) 0).obj M)).IsQuasicoherentOnSite := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact _root_.SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) 0).app M).symm hM
  · refine _root_.SheafOfModules.IsQuasicoherentOnSite.of_isZero ?_
    rcases lt_or_gt_of_ne hn with h | h
    · exact DerivedCategory.isZero_of_isGE _ 0 n h
    · exact DerivedCategory.isZero_of_isLE _ 0 n h

/-- A complex isomorphic to `(M ⊗_O N)[0]` has quasi-coherent cohomology sheaves when `M` and `N`
are quasi-coherent. -/
private theorem homology_isQuasicoherentOnSite_of_iso_single
    (M N : AlgebraicGeometry.RingedSite.Modules.{u, v, w} X)
    (hMq : M.IsQuasicoherentOnSite) (hNq : N.IsQuasicoherentOnSite)
    {K : DerivedCategory (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X)}
    (e : K ≅ (DerivedCategory.singleFunctor
      (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) 0).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).obj N))
    (n : ℤ) :
    ((DerivedCategory.homologyFunctor (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) n).obj
      K).IsQuasicoherentOnSite :=
  _root_.SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((DerivedCategory.homologyFunctor (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) n).mapIso
      e).symm
    (isQuasicoherentOnSite_homology_single
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).obj N)
      (isQuasicoherentOnSite_sheafTensor M N hMq hNq) n)

end Single

section Tensor

variable {X : AlgebraicGeometry.RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O)
      (ComplexShape.up ℤ)]

/-- **The derived tensor product of two modules in degree zero is their tensor product in degree
zero, up to the right K-flat comparison.**  This is the mirror of
`Stacks.SheafOfModules.DerivedTensorProduct.tensorSingleIso`, which assumes K-flatness of the
left factor; here it is the right factor that is K-flat, so `comparisonRight` rather than
`comparisonLeft` identifies the derived tensor product with the total tensor complex.  The two
comparisons have the same target, so the second leg of the composite is the same. -/
def tensorSingleIso' (T : DerivedTensorProduct.{u, v, w, d} X)
    (M N : AlgebraicGeometry.RingedSite.Modules.{u, v, w} X)
    (hN : IsKFlat X.O
      ((CochainComplex.singleFunctor (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) 0).obj N)) :
    (T.tensor.obj
          ((DerivedCategory.singleFunctor
            (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) 0).obj M)).obj
        ((DerivedCategory.singleFunctor
          (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) 0).obj N) ≅
      (DerivedCategory.singleFunctor (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) 0).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).obj N) :=
  T.comparisonRight _ _ hN ≪≫
    DerivedCategory.Q.mapIso
      (HomologicalComplex.mapBifunctorSingleIso
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O) M N)

/-- **Stacks 08F5 for two modules placed in degree zero, the left one K-flat, on a ringed
site.**  If `M` and `N` are quasi-coherent sheaves of `O`-modules and `M[0]` is K-flat, then
every cohomology sheaf of `M[0] ⊗^L_O N[0]` is quasi-coherent.

The K-flat comparison of `T` identifies `M[0] ⊗^L_O N[0]` with `(M ⊗_O N)[0]`, whose cohomology
sheaves are `M ⊗_O N` in degree zero and zero objects elsewhere; quasi-coherence of `M ⊗_O N` is
Stacks 03L6, in the spelling
`Stacks.SheafOfModules.DerivedTensorProduct.isQuasicoherentOnSite_sheafTensor`. -/
theorem isQuasicoherentOnSite_homology_tensor_single (T : DerivedTensorProduct.{u, v, w, d} X)
    (M N : AlgebraicGeometry.RingedSite.Modules.{u, v, w} X)
    (hM : IsKFlat X.O
      ((CochainComplex.singleFunctor (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) 0).obj M))
    (hMq : M.IsQuasicoherentOnSite) (hNq : N.IsQuasicoherentOnSite) (n : ℤ) :
    ((DerivedCategory.homologyFunctor (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) n).obj
        ((T.tensor.obj
            ((DerivedCategory.singleFunctor
              (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) 0).obj M)).obj
          ((DerivedCategory.singleFunctor
            (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) 0).obj N))).IsQuasicoherentOnSite :=
  homology_isQuasicoherentOnSite_of_iso_single M N hMq hNq (T.tensorSingleIso M N hM) n

/-- **Stacks 08F5 for two modules placed in degree zero, the right one K-flat, on a ringed
site.**  The mirror of
`Stacks.SheafOfModules.DerivedTensorProduct.isQuasicoherentOnSite_homology_tensor_single`, read
through `Stacks.SheafOfModules.DerivedTensorProduct.tensorSingleIso'`. -/
theorem isQuasicoherentOnSite_homology_tensor_single' (T : DerivedTensorProduct.{u, v, w, d} X)
    (M N : AlgebraicGeometry.RingedSite.Modules.{u, v, w} X)
    (hN : IsKFlat X.O
      ((CochainComplex.singleFunctor (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) 0).obj N))
    (hMq : M.IsQuasicoherentOnSite) (hNq : N.IsQuasicoherentOnSite) (n : ℤ) :
    ((DerivedCategory.homologyFunctor (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) n).obj
        ((T.tensor.obj
            ((DerivedCategory.singleFunctor
              (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) 0).obj M)).obj
          ((DerivedCategory.singleFunctor
            (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) 0).obj N))).IsQuasicoherentOnSite :=
  homology_isQuasicoherentOnSite_of_iso_single M N hMq hNq (T.tensorSingleIso' M N hN) n

end Tensor

end Stacks.SheafOfModules.DerivedTensorProduct

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules (DerivedTensorProduct)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
  [HasDerivedCategory.{d} (Modules.{u, u} B S hS F hF)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS F hF).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS F hF).O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, u} B S hS F hF) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} (smallEtaleRingedSite B S hS F hF).O)
      (ComplexShape.up ℤ)]

/-- **Stacks 08F5 for two quasi-coherent modules placed in degree zero, the left one K-flat.**
Let `X` be an algebraic space, let `T` be a derived tensor product on `𝒪_X`, and let `M` and `N`
be quasi-coherent `𝒪_X`-modules with `M[0]` K-flat.  Then `M[0] ⊗^L_{𝒪_X} N[0]` lies in
`D_QCoh(𝒪_X)`.

Membership in `D_QCoh(𝒪_X)` is the object property `DerivedCategoryB.derivedCategoryB` for
quasi-coherence that `AlgebraicGeometry.Space.QuasicoherentDerivedCategory` of Stacks 071X is
the full subcategory on, so no new predicate appears.  The content is
`Stacks.SheafOfModules.DerivedTensorProduct.isQuasicoherentOnSite_homology_tensor_single` on the
small étale ringed site of `X`; the general case of Stacks 08F5 is not proved, and the module
docstring records the four missing inputs. -/
@[stacks 08F5 "the case of two quasi-coherent modules placed in degree zero, the left one K-flat"]
theorem derivedQuasicoherent_derivedTensor_single
    (T : DerivedTensorProduct.{u + 1, u, u, d} (smallEtaleRingedSite B S hS F hF))
    (M N : Modules.{u, u} B S hS F hF)
    (hM : Stacks.SheafOfModules.IsKFlat (smallEtaleRingedSite B S hS F hF).O
      ((CochainComplex.singleFunctor (Modules.{u, u} B S hS F hF) 0).obj M))
    (hMq : M.IsQuasicoherentOnSite) (hNq : N.IsQuasicoherentOnSite) :
    DerivedCategoryB.derivedCategoryB
      (_root_.SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))
      ((T.tensor.obj
          ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS F hF) 0).obj M)).obj
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS F hF) 0).obj N)) :=
  fun n => T.isQuasicoherentOnSite_homology_tensor_single M N hM hMq hNq n

/-- **Stacks 08F5 for two quasi-coherent modules placed in degree zero, the right one K-flat.**
The mirror of `AlgebraicGeometry.Space.derivedQuasicoherent_derivedTensor_single`, read through
`Stacks.SheafOfModules.DerivedTensorProduct.isQuasicoherentOnSite_homology_tensor_single'`. -/
@[stacks 08F5 "the case of two quasi-coherent modules placed in degree zero, the right one K-flat"]
theorem derivedQuasicoherent_derivedTensor_single'
    (T : DerivedTensorProduct.{u + 1, u, u, d} (smallEtaleRingedSite B S hS F hF))
    (M N : Modules.{u, u} B S hS F hF)
    (hN : Stacks.SheafOfModules.IsKFlat (smallEtaleRingedSite B S hS F hF).O
      ((CochainComplex.singleFunctor (Modules.{u, u} B S hS F hF) 0).obj N))
    (hMq : M.IsQuasicoherentOnSite) (hNq : N.IsQuasicoherentOnSite) :
    DerivedCategoryB.derivedCategoryB
      (_root_.SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))
      ((T.tensor.obj
          ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS F hF) 0).obj M)).obj
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS F hF) 0).obj N)) :=
  fun n => T.isQuasicoherentOnSite_homology_tensor_single' M N hN hMq hNq n

end AlgebraicGeometry.Space

end
