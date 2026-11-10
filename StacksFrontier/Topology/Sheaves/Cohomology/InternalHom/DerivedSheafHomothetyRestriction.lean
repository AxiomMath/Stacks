module

public import StacksFrontier.CategoryTheory.Monoidal.InternalHomHomothetyTransfer
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLocality.InvertibilityOnACovering
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedSheafHomTransposeIsIso
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomCounitTransport

/-!
# The homothety of an object of `D(𝒪_X)`, restricted to an open

Let `(X, 𝒪_X)` be a ringed space, `K` an object of `D(𝒪_X)` and

`h_K : 𝒪_X[0] ⟶ R𝓗om_{𝒪_X}(K, K)`

the homothety of `K`, `Stacks.SheafOfModules.derivedSheafHomothety`. Invertibility of `h_K` is
what the evaluation hypothesis of [Stacks, Tag 0ATP] reduces to at a pair of objects differing
by an invertible object, and it is a statement one wants to check on an open cover: a morphism
of `D(𝒪_X)` is invertible as soon as its restrictions to the slice sites of a covering family
are (`Stacks.Cohomology.isIso_of_isIso_mapDerivedCategory_overFunctor`).

This file supplies the glueing step of the reduction and the two identifications of spellings
it needs. The restriction step — that the restriction of `h_K` to the slice site over an open
`U` is invertible as soon as `R𝓗om_{𝒪_X|_U}(K|_U, K|_U)` is isomorphic to `𝒪_X|_U[0]` as an
*object* — is `Stacks.SheafOfModules.isIso_map_derivedSheafHomothety_of_iso_derivedSheafHom`,
where the comparisons of tensor products and of units are read off the monoidal structure of
derived restriction and so are not parameters.

## Main results

* `Stacks.SheafOfModules.structureSheaf_eq_tensorRingSheaf` — the ringed space's sheaf of rings
  is the ringed site's.
* `Stacks.SheafOfModules.derivedSheafHomCounit_eq_ringedSite` — the evaluation morphism of a
  ringed space is the evaluation morphism of the ringed site of its opens.
* `Stacks.SheafOfModules.isIso_derivedSheafHomothety_of_coversTop` — **the homothety of `K` is
  an isomorphism** as soon as its restrictions to the members of a family of opens covering `X`
  are.

## Implementation notes

The monoidal structure of `D(𝒪_X)` is `Stacks.SheafOfModules.derivedMonoidalStructure` and that
of `D(𝒪_X|_U)` is `AlgebraicGeometry.RingedSite.derivedTensorMonoidal` at the slice site. Both
are re-seated onto the derived tensor product of [Stacks, Tag 06YU], so in both the whiskering
`a ▷ L` *is* `((derivedTensorProductFunctor _).map a).app L` and the unit *is* the structure
sheaf in degree zero, each by `rfl`; that is what lets the bijection of [Stacks, Tag 08J8] on
the slice site and the equation defining the homothety over `X` be fed to one formal statement.

## References

* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace
open Opposite AlgebraicGeometry
open Stacks.Cohomology.SliceDerivedSheafHom

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor.{u, u, u, u, u} Rc)
      (ComplexShape.up ℤ)]

/-! ### The two spellings of the sheaf of rings -/

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor.{u, u, u, u, u} Rc)
      (ComplexShape.up ℤ)] in
/-- **The ringed space's sheaf of rings is the ringed site's.** `structureSheaf Rc` forgets
commutativity from `Rc` by composing its underlying presheaf with `forget₂ CommRingCat RingCat`,
and `Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O` does the same to the structure
sheaf of the ringed site of the opens of `X`, which is `Rc`. Hence `Mod(𝒪_X)` has the two
spellings `StructureSheafModules Rc` and
`SheafOfModules (Tensor.ringSheaf (ringedSite Rc).O)`, and every statement below that mixes the
ringed-space and the ringed-site vocabulary passes through this identification. -/
theorem structureSheaf_eq_tensorRingSheaf :
    structureSheaf Rc = Tensor.ringSheaf (ringedSite Rc).O := rfl

/-! ### The two spellings of the evaluation morphism -/

/-- The evaluation morphism of a ringed space, written at the ringed site of its opens: the
bijection of [Stacks, Tag 08DI] at the identity, in the spelling
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`. This is `rfl`, and naming it is what lets
the ringed-space and the ringed-site spellings of the evaluation morphism be exchanged without
asking the elaborator to unify two applications of that bijection; see the implementation notes
of `StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/SliceDerivedSheafHomTranspose.lean`.
-/
theorem derivedSheafHomCounit_eq_derivedCurryHomEquiv_id
    (K M : DerivedCategory (StructureSheafModules Rc)) :
    derivedSheafHomCounit Rc K M =
      RingedSite.derivedCurryHomEquiv (ringedSite Rc)
        (((derivedSheafHom Rc).obj (op K)).obj M) K M
        (𝟙 (((derivedSheafHom Rc).obj (op K)).obj M)) := rfl

/-- **The evaluation morphism of a ringed space is the evaluation morphism of its ringed
site.** Both are the bijection of [Stacks, Tag 08DI] at the identity; the equation is proved
from `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_apply` and functoriality of the derived
tensor product rather than by conversion, which does not finish at these objects. -/
theorem derivedSheafHomCounit_eq_ringedSite
    (K M : DerivedCategory (StructureSheafModules Rc)) :
    derivedSheafHomCounit Rc K M = RingedSite.derivedSheafHomCounit (ringedSite Rc) K M := by
  refine (derivedSheafHomCounit_eq_derivedCurryHomEquiv_id Rc K M).trans ?_
  -- The bijection's defining equation is instantiated at explicit arguments and composed in
  -- term position. Left to `rw` it is matched against the target, and the match asks whether
  -- `Rc` has the slice site's structure-sheaf type -- a question only `TopCat.Sheaf`'s
  -- definition answers, which the rewrite's type-correctness check does not unfold.
  refine (RingedSite.derivedCurryHomEquiv_apply (ringedSite Rc)
    (((derivedSheafHom Rc).obj (op K)).obj M) K M
    (𝟙 (((derivedSheafHom Rc).obj (op K)).obj M))).trans ?_
  have h : (derivedTensorProductFunctor (ringedSite Rc)).map
      (𝟙 (((derivedSheafHom Rc).obj (op K)).obj M)) =
      𝟙 ((derivedTensorProductFunctor (ringedSite Rc)).obj
        (((derivedSheafHom Rc).obj (op K)).obj M)) :=
    (derivedTensorProductFunctor (ringedSite Rc)).map_id _
  have hK : ((derivedTensorProductFunctor (ringedSite Rc)).map
        (𝟙 (((derivedSheafHom Rc).obj (op K)).obj M))).app K =
      𝟙 (((derivedTensorProductFunctor (ringedSite Rc)).obj
        (((derivedSheafHom Rc).obj (op K)).obj M)).obj K) :=
    (congrArg (fun t => NatTrans.app t K) h).trans (NatTrans.id_app _ _)
  exact (congrArg (fun m => m ≫ RingedSite.derivedSheafHomCounit (ringedSite Rc) K M) hK).trans
    (Category.id_comp _)

/-! ### Glueing over a covering family of opens -/

section Glueing

variable {ι : Type*} {Y : ι → Opens X}

/-- **The homothety is an isomorphism as soon as its restrictions to a covering family of opens
are.** A morphism of `D(𝒪_X)` is invertible exactly when its restrictions to the slice sites of
a family of opens covering `X` are
(`Stacks.Cohomology.isIso_of_isIso_mapDerivedCategory_overFunctor`, which reads invertibility
off the homology sheaves), and the homothety is such a morphism.

Composed with `Stacks.SheafOfModules.isIso_map_derivedSheafHomothety_of_iso_derivedSheafHom`
over each member, this reduces invertibility of the homothety of `K` to an isomorphism
`R𝓗om_{𝒪_X|_{Y i}}(K|_{Y i}, K|_{Y i}) ≅ 𝒪_X|_{Y i}[0]` of objects over each member of the
cover. -/
theorem isIso_derivedSheafHomothety_of_coversTop
    (hY : (Opens.grothendieckTopology X).CoversTop Y)
    [∀ i, HasSheafify ((Opens.grothendieckTopology X).over (Y i)) AddCommGrpCat.{u}]
    [∀ i, ((Opens.grothendieckTopology X).over (Y i)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (K : DerivedCategory (StructureSheafModules Rc))
    (h : ∀ i, IsIso ((restrictD (ringedSite Rc) (Y i)).map (derivedSheafHomothety Rc K))) :
    IsIso (derivedSheafHomothety Rc K) :=
  Stacks.Cohomology.isIso_of_isIso_mapDerivedCategory_overFunctor hY
    (derivedSheafHomothety Rc K) h

end Glueing

end Stacks.SheafOfModules

end
