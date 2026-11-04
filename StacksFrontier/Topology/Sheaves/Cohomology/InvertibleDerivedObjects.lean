module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSummandNoSliceSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSummandSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TrivialRingSheafModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorOrthogonal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentIso
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObjectDual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategory
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedMonoidalStructure
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorFlatVanishing
public import StacksFrontier.Homology.DerivedCategory.ZeroDifferentialCoproduct
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.CanonicalTruncation
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.ModuleInDegreeZero
public import StacksCore.Tactic.StacksAttribute

/-!
# Invertible objects of the derived category of a ringed space

Let `(X, 𝒪_X)` be a ringed space. An object of `D(𝒪_X)` is invertible for the derived tensor
product exactly when the structure sheaf admits a locally finite direct product decomposition
`𝒪_X = ∏_{n ∈ ℤ} 𝒪_n` on whose factors the cohomology sheaves become invertible modules
`ℋ^n`, with the object itself the sum `⨁ ℋ^n[-n]`; such an object is perfect.

## Main definitions

* `Stacks.Cohomology.InvertibleDerived.ProductDecomposition`: a locally finite direct product
  decomposition `𝒪_X = ∏_{n ∈ ℤ} 𝒪_n` of the structure sheaf, the convention under which
  only finitely many factors are nonzero near any point.
* `Stacks.Cohomology.InvertibleDerived.ProductDecomposition.proj` and
  `Stacks.Cohomology.InvertibleDerived.ProductDecomposition.toOXMod`: the projection
  `𝒪_X ⟶ 𝒪_n` of ring sheaves and the restriction of scalars along it, which views an
  `𝒪_n`-module as an `𝒪_X`-module.
* `Stacks.Cohomology.InvertibleDerived.HasInvertibleModuleDecomposition`: clause (2) of
  Stacks 0FPG, that such a decomposition exists together with invertible `𝒪_n`-modules `ℋ^n`
  and an identification `M = ⨁ ℋ^n[-n]` in `D(𝒪_X)`.
* `Stacks.Cohomology.InvertibleDerived.IsInvertibleObject`: clause (1) of Stacks 0FPG, that `M`
  is invertible for the derived tensor product of Stacks 0FPB, in the sense of Stacks 0FFN.
* `Stacks.Cohomology.InvertibleDerived.HasLocalInvertibleDegree`: clause (3) of Stacks 0FPG,
  that `M` is locally an invertible module placed in a single degree.

## Main results

* `Stacks.Cohomology.InvertibleDerived.isPerfect_of_hasInvertibleModuleDecomposition`: the
  perfectness conclusion of Stacks 0FPG, from clause (2).
* `Stacks.Cohomology.InvertibleDerived.exists_exactPairing_of_isInvertibleObject`: the first step
  of the source's proof of `(1) ⟹ (2)`, that an invertible object of `D(𝒪_X)` has a left dual
  there. A step of the proof, not a clause, so it carries no tag.
* `Stacks.Cohomology.InvertibleDerived.ProductDecomposition.isZero_tensor_toOXMod_unit`: the
  orthogonality `𝒪_n ⊗_{𝒪_X} 𝒪_m = 0` of two distinct factors of a product decomposition, which
  the source's proof of `(2) ⟹ (1)` uses. Also a step of a proof, so also untagged.
* `Stacks.Cohomology.InvertibleDerived.ProductDecomposition.isFlat_toOXMod_unit`: each factor is
  flat over `𝒪_X`, the other input that proof uses. Untagged for the same reason.
* `Stacks.Cohomology.InvertibleDerived.ProductDecomposition.isZero_derivedTensor_toOXMod_unit`:
  the **derived** orthogonality `𝒪_n ⊗^L 𝒪_m = 0` in `D(𝒪_X)`, which is the shape the source's
  proof of `(2) ⟹ (1)` consumes. It is the previous two read through
  `Stacks.Cohomology.MonoidalDerived.isZero_derivedTensor_of_isZero_tensor_of_isFlat`. Also a
  step of a proof, so also untagged.

## Implementation notes

The three clauses are stated here and each carries `@[stacks 0FPG]`. The assertions of the tag
are proved in the files importing this one: `(2) ⟹ (1)` is
`isInvertibleObject_of_hasInvertibleModuleDecomposition_unconditional`
(`InvertibleDerivedFlatRestrictScalars.lean`), and under local stalks `(2) ⟺ (3)` is
`hasInvertibleModuleDecomposition_iff_hasLocalInvertibleDegree`
(`InvertibleDerivedClauseThreeToTwo.lean`).

The hypothesis of the perfectness assertion is inhabited over every ringed space —
`exists_hasInvertibleModuleDecomposition` below.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.SheafOfModules.DerivedMonoidal StrictlyPerfect
open AlgebraicGeometry.RingedSpace.PseudoCoherence

universe u d

namespace Stacks.Cohomology.InvertibleDerived

variable (X : RingedSpace.{u, u})

/-- A **locally finite direct product decomposition** `𝒪_X = ∏_{n ∈ ℤ} 𝒪_n` of the structure
sheaf of a ringed space: a family of sheaves of commutative rings indexed by the integers, an
isomorphism of `𝒪_X` with their product, and the local finiteness condition that every point
has a neighbourhood on which all but finitely many of the factors are the zero ring. -/
public structure ProductDecomposition where
  /-- The factors `𝒪_n` of the decomposition. -/
  factor : ℤ → Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}
  /-- The identification of the structure sheaf with the product of the factors. -/
  iso : X.sheaf ≅ ∏ᶜ factor
  /-- Local finiteness: near every point all but finitely many factors vanish. -/
  locallyFinite : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
    {n : ℤ | ¬ Subsingleton ((factor n).obj.obj (op U))}.Finite

namespace ProductDecomposition

variable {X}

/-- The projection `𝒪_X ⟶ 𝒪_n` onto the `n`-th factor, as a morphism of the sheaves of
(not necessarily commutative) rings over which modules are taken. -/
public def proj (D : ProductDecomposition X) (n : ℤ) :
    Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n) :=
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map (D.iso.hom ≫ Pi.π D.factor n)

/-- An `𝒪_n`-module viewed as an `𝒪_X`-module, by restriction of scalars along the projection
onto the `n`-th factor. -/
public abbrev toOXMod (D : ProductDecomposition X) (n : ℤ) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)) ⥤ Mod X.sheaf :=
  SheafOfModules.restrictScalars (D.proj n)

/-- The projection `𝒪_X ⟶ 𝒪_n` of the sheaves of rings of the slice sites over an open set
`W`, obtained from `ProductDecomposition.proj` by restricting to the slice site. -/
public def projOver (D : ProductDecomposition X) (n : ℤ) (W : Opens X.carrier) :
    (StrictlyPerfect.structureSheafOfRings X).over W ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)).over W :=
  ((Opens.grothendieckTopology X.carrier).overPullback RingCat.{u} W).map
    (show StrictlyPerfect.structureSheafOfRings X ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n) from D.proj n)

/-- An `𝒪_n`-module on the slice site over an open set `W`, viewed as a module on the restricted
ringed space `X|_W`: restriction of scalars along `ProductDecomposition.projOver`, followed by
the identification of modules on the slice site with modules on `X|_W`. -/
public def toRestrictedOXMod (D : ProductDecomposition X) (n : ℤ) (W : Opens X.carrier) :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)).over W) ⥤
      StrictlyPerfect.OXMod.{u, u} (X.restrict W.isOpenEmbedding) :=
  SheafOfModules.restrictScalars (D.projOver n W) ⋙
    AlgebraicGeometry.RingedSpace.overToRestricted X W

/-- Viewing an `𝒪_n`-module on the slice site over `W` as a module on `X|_W` is additive: both
restriction of scalars and the identification with modules on the restricted space are. -/
public instance toRestrictedOXMod_additive (D : ProductDecomposition X) (n : ℤ)
    (W : Opens X.carrier) : (D.toRestrictedOXMod n W).Additive :=
  have := AlgebraicGeometry.RingedSpace.overToRestricted_additive X W
  inferInstanceAs ((SheafOfModules.restrictScalars (D.projOver n W) ⋙
    AlgebraicGeometry.RingedSpace.overToRestricted X W).Additive)

/-- Each factor `𝒪_n` of a direct product decomposition of the structure sheaf is, viewed as an
`𝒪_X`-module, a direct summand of `𝒪_X`: the projection onto the factor is split by the
inclusion of the factor into the product. -/
public theorem nonempty_retract_toOXMod_unit (D : ProductDecomposition X) (n : ℤ) :
    Nonempty (Retract ((D.toOXMod n).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))))
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) :=
  Stacks.SheafOfModules.RingSheafProductFactor.nonempty_retract_of_iso D.iso n

/-- **The orthogonality of the factors**: `𝒪_n ⊗_{𝒪_X} 𝒪_m = 0` for `n ≠ m`.

This is used by the implication `(2) ⟹ (1)`, at the level of sheaves of modules. It is
`Stacks.SheafOfModules.RingSheafProductFactor`'s site-level statement read at the product
presentation that `ProductDecomposition.iso` supplies, and needs no flatness: over each open the
section of `𝒪_X` with `n`-th component `1` and all others zero acts as the identity on `𝒪_n` and
as zero on `𝒪_m`, which kills every pure tensor.

A step of the proof of an implication of Stacks 0FPG, not a clause of it, so it carries no
`@[stacks]` attribute. -/
public theorem isZero_tensor_toOXMod_unit
    (D : ProductDecomposition X) {n m : ℤ} (hmn : m ≠ n) :
    letI := SheafOfModules.monoidalCategorySheafTensor X.sheaf
    IsZero (MonoidalCategory.tensorObj
      ((D.toOXMod n).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))))
      ((D.toOXMod m).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor m))))) :=
  -- pinned by name: the general instance applies here, but resolving it by search from this
  -- file's context exhausts the typeclass budget.
  let : HasBinaryBiproducts
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :=
    inferInstanceAs (HasBinaryBiproducts (StrictlyPerfect.OXMod.{u, u} X))
  Stacks.SheafOfModules.RingSheafProductFactor.isZero_tensorObj_factorModule
    (Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation.ofIso D.iso) hmn

/-- **Each factor of a product decomposition is flat over the structure sheaf.** It is a retract
of `𝒪_X` as an `𝒪_X`-module, `𝒪_X` is flat over itself, and a retract of a flat sheaf of modules
is flat.

This is the input the source uses to pass from the orthogonality
`𝒪_n ⊗_{𝒪_X} 𝒪_m = 0` of `isZero_tensor_toOXMod_unit` to its derived form, from
`Stacks.SheafOfModules.FlatRetract.isFlat_of_retract` and
`Stacks.RingedSpace.isFlat_unit_of_ringedSpace`.

A step of a proof, not a clause, so it carries no `@[stacks]` attribute. -/
public theorem isFlat_toOXMod_unit (D : ProductDecomposition X) (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      ((D.toOXMod n).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))) := by
  obtain ⟨ret⟩ := D.nonempty_retract_toOXMod_unit n
  exact Stacks.SheafOfModules.FlatRetract.isFlat_of_retract X.sheaf ret.i ret.r ret.retract
    (Stacks.RingedSpace.isFlat_unit_of_ringedSpace X)

end ProductDecomposition

/-- A family of retracts gives a retract of the biproducts: the two biproduct maps compose to
the biproduct map of the composites, which is the identity. -/
public def retractBiproduct {C : Type*} [Category* C] [Preadditive C] {ι : Type*}
    {f g : ι → C} [HasBiproduct f] [HasBiproduct g]
    (ρ : ∀ j, Retract (f j) (g j)) : Retract (⨁ f) (⨁ g) where
  i := biproduct.map fun j => (ρ j).i
  r := biproduct.map fun j => (ρ j).r
  retract := biproduct.hom_ext _ _ fun j => by simp [(ρ j).retract]

section Summand

variable {X}

/-- **The transport step.** If an `𝒪_n`-module `ℒ` is, on the slice site over an open set `W`, a
split submodule of a finite product of copies of `𝒪_n`, and if `𝒪_n` is a direct summand of
`𝒪_X` as an `𝒪_X`-module, then `ℒ` viewed as an `𝒪_X`-module restricts to a direct summand of a
finite free module on `X|_W`. -/
public theorem isDirectSummandOfFiniteFree_restrictModules_toOXMod
    (D : ProductDecomposition X) (n : ℤ)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (ret : Retract ((D.toOXMod n).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))))
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    (W : Opens X.carrier) (k : ℕ)
    (s : L.over W ⟶ ∏ᶜ fun _ : Fin k => SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)).over W))
    (hs : IsSplitMono s) :
    IsDirectSummandOfFiniteFree ((restrictModules X W).obj ((D.toOXMod n).obj L)) := by
  have := hs
  have ρ₀ : Retract (L.over W) (⨁ fun _ : Fin k => SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)).over W)) :=
    (⟨s, retraction s, IsSplitMono.id s⟩ : Retract (L.over W) (∏ᶜ _)).trans
      (Retract.ofIso (biproduct.isoProduct _).symm)
  have ρᵤ : Retract ((D.toRestrictedOXMod n W).obj (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)).over W)))
      (StrictlyPerfect.structureModule (X.restrict W.isOpenEmbedding)) :=
    (ret.map (SheafOfModules.overFunctor (StrictlyPerfect.structureSheafOfRings X) W)).map
      (AlgebraicGeometry.RingedSpace.overToRestricted X W)
  have ρ : Retract ((D.toRestrictedOXMod n W).obj (L.over W))
      (StrictlyPerfect.finiteFree (X.restrict W.isOpenEmbedding) k) :=
    (ρ₀.map (D.toRestrictedOXMod n W)).trans
      ((Retract.ofIso ((D.toRestrictedOXMod n W).mapBiproduct _)).trans
        (retractBiproduct fun _ : Fin k => ρᵤ))
  exact StrictlyPerfect.isDirectSummandOfFiniteFree_of_retract ρ
    ((StrictlyPerfect.isDirectSummandOfFiniteFree_iff_retract _).mpr ⟨k, ⟨Retract.refl _⟩⟩)

/-- **Stacks 0B8N on a factor of a product decomposition.** For a direct product decomposition
`𝒪_X = ∏_m 𝒪_m` of the structure sheaf of a ringed space and an invertible `𝒪_n`-module `ℒ`,
every point of every open set `U` has a neighbourhood `W ≤ U` on which `ℒ`, viewed as an
`𝒪_X`-module, is a direct summand of a finite free `𝒪_X|_W`-module. -/
public theorem exists_isDirectSummandOfFiniteFree_toOXMod
    (D : ProductDecomposition X) (n : ℤ)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (hL : Stacks.SheafOfModules.Tensor.IsInvertibleModule (D.factor n) L)
    (x : X.carrier) (U : Opens X.carrier) (hxU : x ∈ U) :
    ∃ W : Opens X.carrier, x ∈ W ∧ W ≤ U ∧
      IsDirectSummandOfFiniteFree ((restrictModules X W).obj ((D.toOXMod n).obj L)) := by
  obtain ⟨ret⟩ := D.nonempty_retract_toOXMod_unit n
  obtain ⟨I, V, f, hcov, hsplit⟩ :=
    @Stacks.SheafOfModules.exists_cover_isDirectSummand_finiteFree
      _ _ _ _ _ _ (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)).property L hL U
  obtain ⟨W₀, -, ⟨Z, a, b, hb, -⟩, hxW₀⟩ := (Opens.mem_grothendieckTopology _).mp hcov x hxU
  cases hb with
  | mk i =>
    obtain ⟨k, s, hs⟩ := hsplit i
    exact ⟨V i, a.le hxW₀, leOfHom (f i),
      isDirectSummandOfFiniteFree_restrictModules_toOXMod D n L ret (V i) k s hs⟩

end Summand

variable [inst : HasDerivedCategory.{d} (Mod X.sheaf)]

namespace ProductDecomposition

variable {X}

/-- **The derived orthogonality of the factors**: `𝒪_n ⊗^L 𝒪_m = 0` in `D(𝒪_X)` for `n ≠ m`.

This is the shape the source's proof of `(2) ⟹ (1)` consumes. Both factors are
flat over `𝒪_X` (`isFlat_toOXMod_unit`) so each, placed in degree zero, is a K-flat complex and
the comparison of the derived monoidal structure applies to the pair; the complex it compares
with is the total tensor product of the two singles, which vanishes because the ordinary tensor
product does (`isZero_tensor_toOXMod_unit`).

A step of the proof of an implication of Stacks 0FPG, not a clause of it, so it carries no
`@[stacks]` attribute. -/
public theorem isZero_derivedTensor_toOXMod_unit (D : ProductDecomposition X) {n m : ℤ}
    (hmn : m ≠ n) :
    letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
    IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj
        ((D.toOXMod n).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))))
      ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj
        ((D.toOXMod m).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor m)))))) :=
  Stacks.Cohomology.MonoidalDerived.isZero_derivedTensor_of_isZero_tensor_of_isFlat X _ _
    (D.isFlat_toOXMod_unit n) (D.isFlat_toOXMod_unit m) (D.isZero_tensor_toOXMod_unit hmn)

end ProductDecomposition

/-- **Clause (2) of Stacks 0FPG.** There is a locally finite direct product decomposition
`𝒪_X = ∏_{n ∈ ℤ} 𝒪_n` of the structure sheaf and for each `n` an invertible `𝒪_n`-module
`ℋ^n` such that `M = ⨁_{n ∈ ℤ} ℋ^n[-n]` in `D(𝒪_X)`, the `n`-th summand being `ℋ^n` viewed
as an `𝒪_X`-module and placed in degree `n`. -/
@[stacks 0FPG "clause (2) as a condition on M: that there is a locally finite direct product \
decomposition 𝒪_X = ∏_{n ∈ ℤ} 𝒪_n and for each n an invertible 𝒪_n-module ℋ^n, in the sense of \
Stacks 01CS, with M = ⨁ ℋ^n[-n] in D(𝒪_X). This is the clause, not an implication between \
clauses; the decomposition itself is `ProductDecomposition`"]
public def HasInvertibleModuleDecomposition (M : DerivedModules X.sheaf) : Prop :=
  letI : HasCoproducts.{u} (DerivedModules X.sheaf) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
  ∃ (D : ProductDecomposition X)
      (H : ∀ n : ℤ, SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))),
    (∀ n : ℤ, Stacks.SheafOfModules.Tensor.IsInvertibleModule (D.factor n) (H n)) ∧
      Nonempty (M ≅ ∐ fun n : ℤ =>
        (DerivedCategory.singleFunctor (Mod X.sheaf) n).obj ((D.toOXMod n).obj (H n)))

/-! ### Perfectness from a locally finite decomposition -/

variable {X}

omit inst in
/-- A point lying in every member of a finite family of opens lies in their intersection. -/
public theorem mem_finsetInf {ι : Type*} {s : Finset ι} {f : ι → Opens X.carrier}
    {x : X.carrier} (h : ∀ i ∈ s, x ∈ f i) : x ∈ s.inf f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.inf_insert]
      exact ⟨h a (Finset.mem_insert_self a s),
        ih fun i hi => h i (Finset.mem_insert_of_mem hi)⟩

omit inst in
/-- A complex of `𝒪_X`-modules is perfect as soon as each term is, around every point,
a direct summand of a finite free module, and the terms indexed outside the finite set of
factors of a locally finite product decomposition which survive near a point restrict to zero
there: intersecting the finitely many neighbourhoods produces an open on which the restricted
complex is bounded with every term a direct summand of a finite free module. -/
public theorem isPerfectComplex_of_local_data (D : ProductDecomposition X)
    (E : CochainComplex (Mod X.sheaf) ℤ)
    (hsummand : ∀ (n : ℤ) (x : X.carrier) (U : Opens X.carrier), x ∈ U →
      ∃ W : Opens X.carrier, x ∈ W ∧ W ≤ U ∧
        IsDirectSummandOfFiniteFree ((restrictModules X W).obj (E.X n)))
    (hzero : ∀ (n : ℤ) (U : Opens X.carrier),
      Subsingleton ((D.factor n).obj.obj (op U)) → ∀ W ≤ U,
        IsZero ((restrictModules X W).obj (E.X n))) :
    Stacks.Cohomology.PerfectComplexes.IsPerfectComplex E := by
  classical
  have key : ∀ x : X.carrier, ∃ W : Opens X.carrier, x ∈ W ∧
      IsStrictlyPerfect
        (((restrictModules X W).mapHomologicalComplex (ComplexShape.up ℤ)).obj E) := by
    intro x
    obtain ⟨U, hxU, hfin⟩ := D.locallyFinite x
    choose Wn hxWn hWnU hWns using fun n : ℤ => hsummand n x U hxU
    refine ⟨hfin.toFinset.inf Wn ⊓ U, ⟨mem_finsetInf (fun n _ => hxWn n), hxU⟩, ?_⟩
    have hle : hfin.toFinset.inf Wn ⊓ U ≤ U := inf_le_right
    refine ⟨hfin.subset fun i hi => ?_, fun i => ?_⟩
    · by_contra hmem
      exact hi (hzero i U (by simpa using hmem) _ hle)
    · by_cases hi : i ∈ hfin.toFinset
      · have hle' : hfin.toFinset.inf Wn ⊓ U ≤ Wn i :=
          le_trans inf_le_left (Finset.inf_le hi)
        exact isDirectSummandOfFiniteFree_of_iso
          ((AlgebraicGeometry.RingedSpace.restrictModulesOfLECompIso X hle').app (E.X i)).symm
          (AlgebraicGeometry.RingedSpace.isDirectSummandOfFiniteFree_restrictModulesOfLE
            hle' (hWns i))
      · exact isDirectSummandOfFiniteFree_of_isZero
          (hzero i U (by simpa using (Set.Finite.mem_toFinset hfin).not.mp hi) _ hle)
  choose W hxW hsp using key
  exact ⟨X.carrier, W, le_antisymm le_top fun x _ => Opens.mem_iSup.mpr ⟨x, hxW x⟩,
    fun x => ⟨_, hsp x, 𝟙 _, inferInstance⟩⟩

omit inst in
/-- A factor of the decomposition which is the zero ring on an open contributes nothing there:
a module over it restricts to the zero module on every smaller open. -/
public theorem isZero_restrict_toOXMod (D : ProductDecomposition X) (n : ℤ)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    {U : Opens X.carrier} (hU : Subsingleton ((D.factor n).obj.obj (op U)))
    {W : Opens X.carrier} (hWU : W ≤ U) :
    IsZero ((restrictModules X W).obj ((D.toOXMod n).obj L)) := by
  have h1 : Subsingleton
      ((Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)).obj.obj (op U)) := hU
  exact Stacks.SheafOfModules.isZero_restrictModules_restrictScalars W (D.proj n) L
    (Stacks.SheafOfModules.subsingleton_of_subsingleton_of_le (homOfLE hWU) h1)

/-- The object `⨁ ℋ^n[-n]` of clause (2) is represented by the complex with `ℋ^n` in degree
`n` and zero differentials, so an object with a decomposition as in clause (2) is perfect as
soon as that complex is a perfect complex. -/
public theorem isPerfect_of_isPerfectComplex_zeroDifferential (M : DerivedModules X.sheaf)
    (hM : HasInvertibleModuleDecomposition X M)
    (hyp : ∀ (D : ProductDecomposition X)
      (H : ∀ n : ℤ, SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))),
      (∀ n : ℤ, Stacks.SheafOfModules.Tensor.IsInvertibleModule (D.factor n) (H n)) →
      Stacks.Cohomology.PerfectComplexes.IsPerfectComplex (X := X)
        (CochainComplex.zeroDifferentialComplex fun n => (D.toOXMod n).obj (H n))) :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, d} X inst M := by
  let _i0 : HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u, u} X) := inst
  obtain ⟨D, H, hinv, ⟨e⟩⟩ := hM
  let _i1 : HasCoproducts.{u} (DerivedModules X.sheaf) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
  let _i2 : PreservesColimitsOfShape (Discrete (ULift.{u} ℤ))
      (DerivedCategory.Q (C := Mod X.sheaf)) :=
    Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts _ _
  let _i3 : PreservesColimitsOfShape (Discrete ℤ) (DerivedCategory.Q (C := Mod X.sheaf)) :=
    preservesColimitsOfShape_discrete_shrink.{u} _ _
  refine ⟨CochainComplex.zeroDifferentialComplex fun n => (D.toOXMod n).obj (H n),
    hyp D H hinv, ⟨?_⟩⟩
  show (DerivedCategory.Q (C := Mod X.sheaf)).obj
      (CochainComplex.zeroDifferentialComplex fun n => (D.toOXMod n).obj (H n)) ≅ M
  exact (CochainComplex.derivedCoproductIso
    (fun n : ℤ => (D.toOXMod n).obj (H n))).symm ≪≫ e.symm

/-- **Stacks 0FPG, the perfectness conclusion.** Let `(X, 𝒪_X)` be a ringed space and let `M`
be an object of `D(𝒪_X)`. If there is a locally finite direct product decomposition
`𝒪_X = ∏_{n ∈ ℤ} 𝒪_n` and for each `n` an invertible `𝒪_n`-module `ℋ^n` with
`M = ⨁ ℋ^n[-n]` in `D(𝒪_X)`, then `M` is a perfect object of `D(𝒪_X)`.

Near a point only finitely many factors survive, each `ℋ^n` is locally a direct summand of a
finite free `𝒪_n`-module and `𝒪_n` is a direct summand of `𝒪_X`, so the complex with `ℋ^n` in
degree `n` and zero differentials — which represents `⨁ ℋ^n[-n]` — is locally strictly
perfect. -/
@[stacks 0FPG "clause (2) implies that M is a perfect object of D(𝒪_X)"]
public theorem isPerfect_of_hasInvertibleModuleDecomposition (M : DerivedModules X.sheaf)
    (hM : HasInvertibleModuleDecomposition X M) :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, d} X inst M :=
  isPerfect_of_isPerfectComplex_zeroDifferential M hM fun D H hinv =>
    isPerfectComplex_of_local_data D _
      (fun n x U hxU =>
        exists_isDirectSummandOfFiniteFree_toOXMod D n (H n) (hinv n) x U hxU)
      (fun n _U hU _W hWU => isZero_restrict_toOXMod D n (H n) hU hWU)

/-! ### Clause (1): invertibility for the derived tensor product

The monoidal structure is the derived tensor product of Stacks 0FPB and invertibility is the
notion of Stacks 0FFN. It is a `def` carrying `@[instance_reducible]` rather than an instance,
so it is introduced with `letI`.
-/

/-- **Clause (1) of Stacks 0FPG.** `M` is an invertible object of `D(𝒪_X)`: there is an object
`N` of `D(𝒪_X)` with `M ⊗^L N ≅ 𝒪_X` and `N ⊗^L M ≅ 𝒪_X`, the tensor product being the derived
tensor product and `𝒪_X` the structure sheaf in degree zero. -/
@[stacks 0FPG "clause (1) as a condition on M: that M is invertible in D(𝒪_X) in the sense of \
Stacks 0FFN, for the derived tensor product of Stacks 0FPB. This is the clause, not an \
implication between clauses"]
public def IsInvertibleObject (M : DerivedModules X.sheaf) : Prop :=
  letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
  MonoidalCategory.IsInvertible M

/-- **Clause (1) of Stacks 0FPG supplies the hypothesis of Stacks 0FPD.** An object of `D(𝒪_X)`
which is invertible for the derived tensor product admits a left dual there, in the sense of
Stacks 0FFP: its tensor inverse is one, with a coevaluation and an evaluation satisfying the two
triangle identities.

This is the first step of the source's proof of `(1) ⟹ (2)` — "then `N` is a left dual for `M`
in the monoidal category `D(𝒪_X)` and we conclude that `M` is perfect by Lemma 0FPD" — and a
step of a proof rather than a clause of the tag, so it carries no `@[stacks]` attribute. It is
`CategoryTheory.MonoidalCategory.IsInvertible.exists_exactPairing` read at the derived tensor
product. -/
public theorem exists_exactPairing_of_isInvertibleObject (M : DerivedModules X.sheaf)
    (hM : IsInvertibleObject M) :
    letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
    ∃ N : DerivedModules X.sheaf, Nonempty (CategoryTheory.ExactPairing M N) :=
  let := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
  MonoidalCategory.IsInvertible.exists_exactPairing hM

/-! ### Clause (3): one invertible module in one degree, locally

Clause (3) of the source is stated under the hypothesis that every stalk `𝒪_{X, x}` is a local
ring, but the statement itself does not mention that hypothesis, and it is recorded here
without it; it is a condition on `M` alone, free of any `ProductDecomposition`.

The shape follows `Stacks.Cohomology.PerfectComplexes.IsPerfectComplex`: a cover of `X`, and
over each member a quasi-isomorphism from the local model to the restricted complex. Stating
it this way, rather than with an isomorphism in `D(𝒪_X|_{U_i})`, avoids needing a derived
category for each restricted space.
-/

/-- Invertibility of an `𝒪_Y`-module in the sense of Stacks 01CS, for a ringed space `Y`:
tensoring by it is an equivalence of the category of `𝒪_Y`-modules. This is
`Stacks.SheafOfModules.IsInvertible` read at the structure sheaf of `Y`, in the spelling of
`StrictlyPerfect.OXMod`. -/
public abbrev IsInvertibleModule (Y : RingedSpace.{u, u}) (L : StrictlyPerfect.OXMod.{u, u} Y) :
    Prop :=
  Stacks.SheafOfModules.IsInvertible Y.presheaf
    (StrictlyPerfect.structureSheafOfRings Y).property L

omit inst in
/-- **Clause (3) of Stacks 0FPG, at the level of complexes.** There is an open covering
`X = ⋃ U_i` and for each `i` an integer `n_i` and an invertible `𝒪_{U_i}`-module `L_i` such that
`L_i` placed in degree `n_i` is quasi-isomorphic to the restriction of the complex to `U_i`. -/
public def IsLocallyInvertibleModuleComplex (E : CochainComplex (Mod X.sheaf) ℤ) : Prop :=
  ∃ (I : Type u) (U : I → Opens X.carrier), iSup U = ⊤ ∧
    ∀ i : I, ∃ (n : ℤ) (L : StrictlyPerfect.OXMod.{u, u} (X.restrict (U i).isOpenEmbedding)),
      IsInvertibleModule _ L ∧
      ∃ f : (CochainComplex.singleFunctor _ n).obj L ⟶
          ((restrictModules X (U i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj E,
        QuasiIso f

/-- **Clause (3) of Stacks 0FPG.** `M` is represented by a complex which, on each member of
some open covering of `X`, is quasi-isomorphic to an invertible module placed in a single
degree — the degree being allowed to vary with the member of the covering. -/
@[stacks 0FPG "clause (3) as a condition on M: that there is an open covering X = ⋃ U_i and for \
each i an integer n_i with M|_{U_i} represented by an invertible 𝒪_{U_i}-module placed in degree \
n_i. The source's condition that every stalk 𝒪_{X,x} is a local ring belongs to the equivalence \
of (3) with the other clauses, which is hasInvertibleModuleDecomposition_iff_hasLocalInvertibleDegree"]
public def HasLocalInvertibleDegree (M : DerivedModules X.sheaf) : Prop :=
  ∃ E : CochainComplex (Mod X.sheaf) ℤ,
    IsLocallyInvertibleModuleComplex E ∧ Nonempty (DerivedCategory.Q.obj E ≅ M)

/-! ### The one-factor decomposition, and the non-vacuity of clause (2)

`HasInvertibleModuleDecomposition` is an existential over a `ProductDecomposition`, and
`isPerfect_of_hasInvertibleModuleDecomposition` consumes it as a hypothesis. So the content of
that theorem depends on the datum having an inhabitant, and the declarations below exhibit one
over every ringed space, assuming nothing: the decomposition with `𝒪_0 = 𝒪_X` and every other
factor the zero ring, carrying the unit module in each degree. For it `⨁ ℋ^n[-n]` is `𝒪_X` placed
in degree zero, so the conclusion reads as the perfectness of the structure sheaf; the witness is
not degenerate.

These are not clauses of the tag and carry no tag.
-/

section OneFactor

universe v w

variable {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
  (R : Sheaf K CommRingCat.{w})

/-- **The zero sheaf of rings** on a site: the constant sheaf at the zero ring, which is the
terminal object of sheaves of commutative rings. -/
public def zeroRingSheaf (K : GrothendieckTopology D) : Sheaf K CommRingCat.{w} :=
  Sheaf.terminal _ CommRingCat.punitIsTerminal

/-- The zero sheaf of rings is terminal among sheaves of commutative rings. -/
public def isTerminalZeroRingSheaf : IsTerminal (zeroRingSheaf.{u, v, w} K) :=
  Sheaf.isTerminalTerminal _ CommRingCat.punitIsTerminal

/-- **The one-factor family** attached to a sheaf of commutative rings `R`: `R` in degree zero
and the zero ring in every other degree. -/
public def oneFactorFamily : ℤ → Sheaf K CommRingCat.{w} :=
  fun n => if n = 0 then R else zeroRingSheaf K

/-- In degree zero the one-factor family is `R` itself. -/
public theorem oneFactorFamily_zero : oneFactorFamily R 0 = R := if_pos rfl

/-- Away from degree zero the one-factor family is the zero sheaf of rings. -/
public theorem oneFactorFamily_of_ne {n : ℤ} (h : n ≠ 0) :
    oneFactorFamily R n = zeroRingSheaf K := if_neg h

/-- Away from degree zero the one-factor family has no sections beyond zero. This is the local
finiteness of the decomposition, read on the rings of sections. -/
public theorem subsingleton_oneFactorFamily_of_ne {n : ℤ} (h : n ≠ 0) (U : Dᵒᵖ) :
    Subsingleton ((oneFactorFamily R n).obj.obj U) := by
  rw [oneFactorFamily_of_ne R h]
  simp only [zeroRingSheaf, Sheaf.terminal_obj, Functor.const_obj_obj]
  infer_instance

/-- The projection of `R` onto the `n`-th member of the one-factor family: the identity in
degree zero and the unique map to the zero ring elsewhere. -/
public def oneFactorProj (n : ℤ) : R ⟶ oneFactorFamily R n :=
  if h : n = 0 then eqToHom (by rw [h, oneFactorFamily_zero])
  else (isTerminalZeroRingSheaf (K := K)).from R ≫ eqToHom (oneFactorFamily_of_ne R h).symm

/-- In degree zero the projection onto the one-factor family is the identity of `R`, up to the
identification `oneFactorFamily_zero`. -/
public theorem oneFactorProj_zero :
    oneFactorProj R 0 = eqToHom (oneFactorFamily_zero R).symm := by
  simp [oneFactorProj]

/-- `R` *is* the product of the one-factor family: the fan of the projections is a limit fan.
In degree zero the projection is the identity, and every other factor is terminal, so a cone
over the family is determined by its degree-zero leg. -/
public def isLimitOneFactorFan : IsLimit (Fan.mk R (oneFactorProj R)) := by
  refine Fan.IsLimit.mk _ (fun s => s.proj 0 ≫ eqToHom (oneFactorFamily_zero R)) ?_ ?_
  · intro s n
    by_cases h : n = 0
    · subst h
      simp [Fan.proj, oneFactorProj_zero]
    · rw [← cancel_mono (eqToHom (oneFactorFamily_of_ne R h))]
      exact (isTerminalZeroRingSheaf (K := K)).hom_ext _ _
  · intro s m hm
    have h0 : m ≫ oneFactorProj R 0 = s.proj 0 := hm 0
    rw [oneFactorProj_zero] at h0
    rw [← h0]
    simp

/-- The identification `R ≅ ∏ᶜ` of the one-factor family. -/
public def oneFactorIso [HasProduct (oneFactorFamily R)] : R ≅ ∏ᶜ oneFactorFamily R :=
  (isLimitOneFactorFan R).conePointUniqueUpToIso (productIsProduct _)

end OneFactor

variable (X)

/-- **The one-factor product decomposition** of the structure sheaf of a ringed space:
`𝒪_0 = 𝒪_X` and `𝒪_n = 0` for `n ≠ 0`. It is locally finite on the whole of `X`, only the
degree-zero factor having any sections. -/
public def oneFactorDecomposition : ProductDecomposition X where
  factor := oneFactorFamily X.sheaf
  iso := oneFactorIso X.sheaf
  locallyFinite x := ⟨⊤, by simp, by
    refine (Set.finite_singleton (0 : ℤ)).subset fun n hn => ?_
    simp only [Set.mem_singleton_iff]
    by_contra hne
    exact hn (subsingleton_oneFactorFamily_of_ne X.sheaf hne _)⟩

/-- **Clause (2) of Stacks 0FPG has an inhabitant over every ringed space**, so
`isPerfect_of_hasInvertibleModuleDecomposition` is not vacuous. Take the one-factor
decomposition and the unit module in each degree: the unit of a sheaf of rings is invertible,
and `⨁ ℋ^n[-n]` is then `𝒪_X` in degree zero. -/
public theorem exists_hasInvertibleModuleDecomposition :
    ∃ M : DerivedModules X.sheaf, HasInvertibleModuleDecomposition X M := by
  let : HasCoproducts.{u} (DerivedModules X.sheaf) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
  exact ⟨∐ fun n : ℤ => (DerivedCategory.singleFunctor (Mod X.sheaf) n).obj
      (((oneFactorDecomposition X).toOXMod n).obj (SheafOfModules.unit _)),
    oneFactorDecomposition X, fun n => SheafOfModules.unit _,
    fun n => Stacks.SheafOfModules.isInvertible_unit _ _, ⟨Iso.refl _⟩⟩

end Stacks.Cohomology.InvertibleDerived

end
