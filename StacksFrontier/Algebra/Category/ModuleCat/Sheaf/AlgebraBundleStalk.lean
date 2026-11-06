module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraInhabitant

/-!
# The tensor, exterior and symmetric algebras of an arbitrary sheaf of modules

Let `O` be a sheaf of commutative rings on a site `(C, J)`.
`SheafOfModules.TensorExteriorSymmetricAlgebras J F` (in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras`) is the
twenty-three-field package Stacks Section 17.21 attaches to a sheaf of `O`-modules `F`, and
`SheafOfModules.tensorExteriorSymmetricAlgebras` (in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraInhabitant`) constructs an inhabitant
of it — but only for a sheaf of the shape `(moduleSheafification J a).obj P`, the sheafification
of a presheaf of modules. A sheaf of modules `G` given in advance is merely *isomorphic* to such
a sheafification, by the counit of the sheafification adjunction, and a package whose fields
mention the pieces of three graded algebras, two generators, a family of tensor powers and a
coproduct does not move along that isomorphism by itself.

This file moves it. `TensorExteriorSymmetricAlgebras.ofIso` transports the whole package along
an isomorphism `F ≅ G` of the underlying sheaves of modules, and
`SheafOfModules.nonempty_tensorExteriorSymmetricAlgebras'` concludes that **every** sheaf of
modules on every such site has a tensor algebra with its exterior and symmetric quotients.
`SheafOfModules.algebras` is the resulting chosen package, which is what a statement about *the*
symmetric or exterior power of a given sheaf of modules — a stalk of `Symⁿ F`, the
quasi-coherence of `Sym(F)`, an exact presentation of `⋀ⁿ F` — needs in order to be stated at
all with a type whose only axioms are the three standard ones.

## Main definitions

* `SheafOfModules.tensorPowerMapIso`: an isomorphism of sheaves of modules induces one of their
  `n`-fold tensor powers, in every degree.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.ofIso`: **the transport of the package along
  an isomorphism of the underlying sheaf of modules.** The three graded algebras, their two
  quotient maps and the vanishing in negative degrees are carried over unchanged; the two
  generators are precomposed with the inverse isomorphism, and the homogeneous identifications
  and the direct-sum comparison are composed with `tensorPowerMapIso`.
* `SheafOfModules.valPresheaf` and `SheafOfModules.sheafifyValIso`: the presheaf of modules
  underlying a sheaf of modules, over the presheaf of rings `Osharp.obj`, and the counit of the
  sheafification adjunction at it, as an isomorphism.
* `SheafOfModules.sheafifiedAlgebras`: the three algebras of a given sheaf of modules, each
  realized as the degreewise sheafification of its sectionwise counterpart;
  `SheafOfModules.algebras` is that package named as *the* choice, and
  `SheafOfModules.ringedSpaceAlgebras` is it on a ringed space.
* `SheafOfModules.symmetricPowerSheafifyIso`, `exteriorPowerSheafifyIso` and
  `tensorPieceSheafifyIso`: **the degree-`n` symmetric, exterior and tensor pieces of an
  arbitrary package over `G` are the sheafifications of the presheaves of sectionwise powers**
  `U ↦ Symⁿ_{O(U)}(G(U))`, `U ↦ ⋀ⁿ_{O(U)}(G(U))` and `U ↦ Tⁿ_{O(U)}(G(U))`. These are the
  object-level content of Stacks 01CG and its exterior analogue, and they are what a computation
  of a stalk, of a local presentation, or of quasi-coherence has to start from.

## Main results

* `SheafOfModules.GradedAlgebra.isUniversal_iso_comp`: **a universal degree-one generator stays
  universal after precomposition with an isomorphism**, for an arbitrary property of generators
  transported along that isomorphism in both directions. This is the one nontrivial field of the
  transport that is not bookkeeping: it is what carries the universal properties of the tensor,
  exterior and symmetric algebras from `F` to `G`, and it is instantiated three times, with
  `fun _ _ => True`, with `SheafOfModules.GradedAlgebra.SquareZero` and with
  `SheafOfModules.GradedAlgebra.PairwiseCommutes`.
* `SheafOfModules.tensorPowerMapIso_unit_tmul`: the induced isomorphism of tensor powers, read
  on the image of a pure tensor under the sheafification unit. This is what the
  `tensorPieceIso_mul_left` field of the transported package needs.
* `SheafOfModules.nonempty_tensorExteriorSymmetricAlgebras'`: **every sheaf of modules has a
  tensor algebra with its exterior and symmetric quotients**, and
  `SheafOfModules.nonempty_ringedSpaceAlgebras`: the same on a ringed space, which is the form
  Section 17.21 states and the form its lemmas are consumed in.

## Implementation notes

**Why the three algebras themselves are not moved.** A package over `F` and the transported
package over `G` have *the same* three graded algebras and the same two quotient maps: nothing
in the data of a sheaf of graded algebras refers to `F`. Only the two generators, the four
identifications of homogeneous pieces and the direct-sum comparison mention it, and all of them
are morphisms out of or into the tensor powers of `F`. So the transport is: precompose the
generators with `e.inv`, and compose the identifications with `tensorPowerMapIso`. The one field
that needs an argument rather than a rewrite is `tensorPieceIso_mul_left`, whose two sides are
compared on arbitrary local sections of `G` and on the image of a pure tensor.

**The universal properties are transported through one lemma, not three.**
`SheafOfModules.GradedAlgebra.IsUniversal` takes its side condition as
`P : ∀ B, (M ⟶ B.piece 1) → Prop`, so the condition for `F` and the condition for `G` are
different predicates even when they are "the same" condition.
`GradedAlgebra.isUniversal_iso_comp` therefore takes both predicates together with the two
implications relating them along `e`, which for `SquareZero` and `PairwiseCommutes` are
`GradedAlgebra.squareZero_comp` and `GradedAlgebra.pairwiseCommutes_comp` applied to `e.hom` and
to `e.inv`. Quantifying over the predicate is also what makes the lemma usable for the tensor
algebra, whose side condition is `fun _ _ => True`.

**The degree in `tensorPowerMapIso` is a variable, and the recursion is the one of
`SheafOfModules.tensorPower`.** The transport of a tensor power is defined by the same
three-case recursion as the tensor power itself — `Iso.refl` in degree zero, `e` in degree one,
and the bifunctor applied to `Iso.prod` above that — so that `tensorPowerMapIso J e n` is
definitionally what the degree-`n` field of the package expects, with no reindexing and no
`eqToIso`. In particular the degree-zero case is `Iso.refl` on `SheafOfModules.unit`, which both
`tensorPower J F 0` and `tensorPower J G 0` unfold to, so the degree-zero fields of the package
and the degree-zero piece of the exterior algebra need no transport at all. Every statement
below keeps the degree a variable and is instantiated only at the point of use, as recorded in
the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraInhabitant`.

**`a = 𝟙` is a choice, and the only one available.** `nonempty_tensorExteriorSymmetricAlgebras'`
instantiates the inhabitant at the presheaf of rings `Osharp.obj` with the locally bijective map
`a := 𝟙 Osharp.obj`, and at the presheaf of modules underlying `G`. Any locally bijective `a`
whose sheafification carries `G` would do; the identity is the one that exists for every
`Osharp` with no further hypothesis, and the instances
`Presheaf.IsLocallyInjective J (toRingCatMap J (𝟙 Osharp.obj))` and its surjective companion are
found by instance search.

**Universes.** The site universes `u`, `v` are independent of the ring universe `w`, and the
module universe is `w` as well. That is forced, not chosen, for exactly the two reasons recorded
in the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras`: the tensor
product of sheaves of modules used for the tensor powers exists only over a presheaf of
commutative rings in the module universe, and the degree-zero identifications land in the
structure sheaf, whose sections are the ring's. Nothing here is narrowed relative to the files
it builds on.

**The `@[stacks 01CF]` tag, and what carries it.** Tag 01CF is the section itself; 0FQW is the
definition of a sheaf of graded algebras (carried by `SheafOfModules.GradedAlgebra`), and the
lemmas of the section (01CG, 01CH, 01CJ, 01CK, 01CL) are statements *about* the algebras, none of
which is proved here. What is here is the construction of the object those lemmas are about, and
since the section has no finer tag for it, `SheafOfModules.ringedSpaceAlgebras` carries 01CF with
a clause comment saying so. It is the only carrier of 01CF anywhere in the two trees, and it is
the ringed-space case because that is the setting Section 17.21 works in; the construction itself
is `SheafOfModules.sheafifiedAlgebras`, over an arbitrary site, which is the section's own route —
each of the three algebras is the degreewise sheafification of its sectionwise counterpart.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

open scoped TensorProduct

universe v u w

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

/-! ### Transporting a universal degree-one generator along an isomorphism -/

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {M N : SheafOfModules.{w} R}

/-- **A universal degree-one generator stays universal after precomposition with an
isomorphism.** The side condition is arbitrary, and is related to the side condition on the
other side of `e` by the two implications `hPQ` and `hQP`; for the tensor algebra it is
`fun _ _ => True` and both are trivial, and for the exterior and symmetric algebras it is
`SquareZero` and `PairwiseCommutes`, for which both are `squareZero_comp` and
`pairwiseCommutes_comp`. -/
theorem isUniversal_iso_comp (e : M ≅ N)
    {P : ∀ B : GradedAlgebra.{w, w} R, (M ⟶ B.piece 1) → Prop}
    {Q : ∀ B : GradedAlgebra.{w, w} R, (N ⟶ B.piece 1) → Prop}
    (hPQ : ∀ (B : GradedAlgebra.{w, w} R) (κ : N ⟶ B.piece 1), Q B κ → P B (e.hom ≫ κ))
    (hQP : ∀ (B : GradedAlgebra.{w, w} R) (κ : M ⟶ B.piece 1), P B κ → Q B (e.inv ≫ κ))
    {A : GradedAlgebra.{w, w} R} {ι : M ⟶ A.piece 1} (hA : IsUniversal P A ι) :
    IsUniversal Q A (e.inv ≫ ι) := by
  refine ⟨hQP A ι hA.1, fun B κ hκ => ?_⟩
  obtain ⟨g, hg, hu⟩ := hA.2 B (e.hom ≫ κ) (hPQ B κ hκ)
  refine ⟨g, ?_, fun h hh => hu h ?_⟩
  · change (e.inv ≫ ι) ≫ g.app 1 = κ
    rw [Category.assoc, hg, e.inv_hom_id_assoc]
  · change (e.inv ≫ ι) ≫ h.app 1 = κ at hh
    change ι ≫ h.app 1 = e.hom ≫ κ
    rw [← hh, Category.assoc, e.hom_inv_id_assoc]

end SheafOfModules.GradedAlgebra

/-! ### Transporting the tensor powers along an isomorphism -/

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

section TensorPowers

variable {F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}

/-- An isomorphism of sheaves of modules induces an isomorphism of their `n`-fold tensor
powers, by the same recursion that defines the tensor powers. -/
noncomputable def tensorPowerMapIso (e : F ≅ G) :
    ∀ n : ℕ, tensorPower J F n ≅ tensorPower J G n
  | 0 => Iso.refl _
  | 1 => e
  | n + 2 => (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).mapIso e).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj _).mapIso (tensorPowerMapIso e (n +
          1)))

@[simp] theorem tensorPowerMapIso_zero (e : F ≅ G) :
    tensorPowerMapIso J e 0 = Iso.refl (tensorPower J F 0) := rfl

@[simp] theorem tensorPowerMapIso_one (e : F ≅ G) : tensorPowerMapIso J e 1 = e := rfl

theorem tensorPowerMapIso_add_two (e : F ≅ G) (n : ℕ) :
    tensorPowerMapIso J e (n + 2) = (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).mapIso
        e).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj _).mapIso (tensorPowerMapIso J e (n +
          1))) := rfl

/-- **The induced isomorphism of tensor powers, on the image of a pure tensor under the
sheafification unit.** This is the computation the `tensorPieceIso_mul_left` field of the
transported package needs; the degree is a variable throughout. -/
theorem tensorPowerMapIso_unit_tmul (e : F ≅ G) (n : ℕ) (U : Cᵒᵖ) (s : F.val.obj U)
    (x : (tensorPower J F (n + 1)).val.obj U) :
    (tensorPowerMapIso J e (n + 2)).hom.val.app U
        (((PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf
            Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj F.val (tensorPower J F (n + 1)).val)).app U
          (s ⊗ₜ[Osharp.obj.obj U] x)) =
      ((PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf
          Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj G.val (tensorPower J G (n + 1)).val)).app U
        (e.hom.val.app U s ⊗ₜ[Osharp.obj.obj U]
          (tensorPowerMapIso J e (n + 1)).hom.val.app U x) :=
  PresheafOfModules.tensorSheafBifunctor_map_unit_tmul J
    (Iso.prod e (tensorPowerMapIso J e (n + 1))).hom U s x

end TensorPowers

/-- Countable coproducts of sheaves of modules, stated directly: instance search for
`HasColimit (Discrete.functor _)` in `SheafOfModules` times out under Lean v4.35.0. -/
local instance : HasColimitsOfShape (Discrete ℕ) (SheafOfModules.{w} (toRingCat J Osharp)) :=
  haveI := PresheafOfModules.hasColimitsOfShape (toRingCat J Osharp).obj (Discrete ℕ)
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
    (toRingCat J Osharp) (Discrete ℕ)

/-! ### Transporting the package along an isomorphism -/

namespace TensorExteriorSymmetricAlgebras

variable {F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}

/-- **The tensor, exterior and symmetric algebras of a sheaf of modules, transported along an
isomorphism of that sheaf.** The three graded algebras, the two quotient maps and the vanishing
in negative degrees are unchanged; the generators are precomposed with `e.inv` and the
homogeneous identifications are composed with `tensorPowerMapIso`. -/
noncomputable def ofIso (e : F ≅ G) (A : TensorExteriorSymmetricAlgebras J F) :
    TensorExteriorSymmetricAlgebras J G where
  tensor := A.tensor
  tensorGenerator := e.inv ≫ A.tensorGenerator
  tensor_isTensorAlgebra :=
    GradedAlgebra.isUniversal_iso_comp e (fun _ _ _ => trivial) (fun _ _ _ => trivial)
      A.tensor_isTensorAlgebra
  tensorPieceIso n := A.tensorPieceIso n ≪≫ tensorPowerMapIso J e n
  tensorPieceIso_one := by
    have h : A.tensorGenerator ≫ (A.tensorPieceIso 1 ≪≫ tensorPowerMapIso J e 1).hom =
        (tensorPowerMapIso J e 1).hom := by
      rw [Iso.trans_hom, ← Category.assoc, A.tensorPieceIso_one']
      exact Category.id_comp _
    rw [Category.assoc, h]
    exact e.inv_hom_id
  tensorPieceIso_zero U := A.tensorPieceIso_zero U
  tensorPieceIso_mul_left n U s x := by
    refine Eq.trans (congrArg (fun z => (tensorPowerMapIso J e (n + 2)).hom.val.app U z)
      (A.tensorPieceIso_mul_left n U (e.inv.val.app U s)
        ((tensorPowerMapIso J e (n + 1)).inv.val.app U x))) ?_
    refine Eq.trans (tensorPowerMapIso_unit_tmul J e n U (e.inv.val.app U s)
      ((tensorPowerMapIso J e (n + 1)).inv.val.app U x)) ?_
    refine congrArg (fun z => PresheafOfModules.Hom.app
      (PresheafOfModules.tensorSheafUnit G (tensorPower J G (n + 1))) U z) ?_
    have h1 : e.hom.val.app U (e.inv.val.app U s) = s :=
      hom_congr_app_apply e.inv_hom_id U s
    have h2 : (tensorPowerMapIso J e (n + 1)).hom.val.app U
        ((tensorPowerMapIso J e (n + 1)).inv.val.app U x) = x :=
      hom_congr_app_apply (tensorPowerMapIso J e (n + 1)).inv_hom_id U x
    rw [h1, h2]
  tensorDirectSumIso :=
    (Sigma.mapIso fun n : ℕ => (tensorPowerMapIso J e n).symm) ≪≫ A.tensorDirectSumIso
  tensorDirectSumIso_ι n := by
    rw [Iso.trans_hom, ← Category.assoc,
      Sigma.ι_mapIso_hom (fun m : ℕ => (tensorPowerMapIso J e m).symm) n, Category.assoc,
      A.tensorDirectSumIso_ι n, Iso.symm_hom, Iso.trans_inv, Category.assoc]
  tensorPiece_eq_zero_of_neg := A.tensorPiece_eq_zero_of_neg
  exterior := A.exterior
  exteriorGenerator := e.inv ≫ A.exteriorGenerator
  exterior_isExteriorAlgebra :=
    GradedAlgebra.isUniversal_iso_comp e
      (fun _ _ hκ => GradedAlgebra.squareZero_comp e.hom hκ)
      (fun _ _ hκ => GradedAlgebra.squareZero_comp e.inv hκ)
      A.exterior_isExteriorAlgebra
  exteriorPieceIso_zero := A.exteriorPieceIso_zero
  exteriorPieceIso_zero_one := A.exteriorPieceIso_zero_one
  exteriorPiece_eq_zero_of_neg := A.exteriorPiece_eq_zero_of_neg
  symmetric := A.symmetric
  symmetricGenerator := e.inv ≫ A.symmetricGenerator
  symmetric_isSymmetricAlgebra :=
    GradedAlgebra.isUniversal_iso_comp e
      (fun _ _ hκ => GradedAlgebra.pairwiseCommutes_comp e.hom hκ)
      (fun _ _ hκ => GradedAlgebra.pairwiseCommutes_comp e.inv hκ)
      A.symmetric_isSymmetricAlgebra
  symmetricPiece_eq_zero_of_neg := A.symmetricPiece_eq_zero_of_neg
  tensorToExterior := A.tensorToExterior
  tensorToExterior_extends := by rw [Category.assoc, A.tensorToExterior_extends]
  tensorToSymmetric := A.tensorToSymmetric
  tensorToSymmetric_extends := by rw [Category.assoc, A.tensorToSymmetric_extends]

end TensorExteriorSymmetricAlgebras

/-! ### Every sheaf of modules has the three algebras -/

section Existence

variable (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))

/-- The presheaf of modules underlying a sheaf of modules, regarded over the presheaf of rings
`Osharp.obj` rather than over the sheaf of rings. This is the presheaf whose sheafification the
counit of the sheafification adjunction identifies with the sheaf itself. -/
noncomputable abbrev valPresheaf :
    PresheafOfModules.{w} (Osharp.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}) :=
  (PresheafOfModules.restrictScalars (toRingCatMap J (𝟙 Osharp.obj))).obj G.val

/-- The sheafification of the presheaf of modules underlying a sheaf of modules is that sheaf of
modules: the counit of the sheafification adjunction is an isomorphism. -/
noncomputable def sheafifyValIso :
    (PresheafOfModules.moduleSheafification J (𝟙 Osharp.obj)).obj (valPresheaf J G) ≅ G :=
  (asIso ((PresheafOfModules.sheafificationAdjunction
    (toRingCatMap J (𝟙 Osharp.obj))).counit)).app G

/-- **The tensor, exterior and symmetric algebras of a sheaf of modules**, each realized as the
degreewise sheafification of its sectionwise counterpart: the inhabitant of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraInhabitant`, transported along the
counit isomorphism `sheafifyValIso`. -/
noncomputable def sheafifiedAlgebras : TensorExteriorSymmetricAlgebras J G :=
  TensorExteriorSymmetricAlgebras.ofIso J (sheafifyValIso J G)
    (tensorExteriorSymmetricAlgebras J (𝟙 Osharp.obj) (valPresheaf J G))

/-- **Every sheaf of modules has a tensor algebra with its exterior and symmetric quotients.**
The inhabitant of `TensorExteriorSymmetricAlgebras` built in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraInhabitant` is for the sheafification
of a presheaf of modules; this transports it along the counit isomorphism to the given sheaf. -/
theorem nonempty_tensorExteriorSymmetricAlgebras' :
    Nonempty (TensorExteriorSymmetricAlgebras J G) :=
  ⟨sheafifiedAlgebras J G⟩

/-- The tensor, exterior and symmetric algebras of a sheaf of modules, as a chosen package.
This is the term a statement about *the* tensor, exterior or symmetric power of a given sheaf of
modules is made with; `TensorExteriorSymmetricAlgebras.tensorAlgebraIso`,
`exteriorAlgebraIso` and `symmetricAlgebraIso` identify it with any other choice. -/
noncomputable def algebras : TensorExteriorSymmetricAlgebras J G :=
  sheafifiedAlgebras J G

end Existence

/-! ### The homogeneous pieces are the sheafified sectionwise powers -/

section Pieces

variable {G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
  (A : TensorExteriorSymmetricAlgebras J G) (n : ℕ)

/-- **The degree-`n` symmetric power of a sheaf of modules is the sheafification of the presheaf
of sectionwise symmetric powers** `U ↦ Symⁿ_{O(U)}(G(U))`. The right-hand side is
`sheafifiedAlgebras`' own degree-`n` symmetric piece on the nose — the sheafified sectionwise
symmetric algebra is graded by `PresheafOfModules.symPow`, and `extendFamily` at a nonnegative
degree is that family — and the comparison is `symmetricAlgebraIso`, so the statement holds for
an arbitrary package `A` and not only for the constructed one. -/
noncomputable def symmetricPowerSheafifyIso :
    A.symmetricPower n ≅ (PresheafOfModules.moduleSheafification J (𝟙 Osharp.obj)).obj
      (PresheafOfModules.symPow n (valPresheaf J G)) :=
  TensorExteriorSymmetricAlgebras.symmetricAlgebraIso A (sheafifiedAlgebras J G) (n : ℤ)

/-- **The degree-`n` exterior power of a sheaf of modules is the sheafification of the presheaf
of sectionwise exterior powers** `U ↦ ⋀ⁿ_{O(U)}(G(U))`, for an arbitrary package `A`. -/
noncomputable def exteriorPowerSheafifyIso :
    A.exteriorPower n ≅ (PresheafOfModules.moduleSheafification J (𝟙 Osharp.obj)).obj
      (PresheafOfModules.extPow n (valPresheaf J G)) :=
  TensorExteriorSymmetricAlgebras.exteriorAlgebraIso A (sheafifiedAlgebras J G) (n : ℤ)

/-- **The degree-`n` piece of the tensor algebra of a sheaf of modules is the sheafification of
the presheaf of sectionwise tensor powers** `U ↦ T^n_{O(U)}(G(U))`, for an arbitrary package `A`.
This is a second description of that piece: `A.tensorPieceIso` identifies it with the `n`-fold
sheafified tensor product `SheafOfModules.tensorPower`. -/
noncomputable def tensorPieceSheafifyIso :
    A.tensor.piece (n : ℤ) ≅ (PresheafOfModules.moduleSheafification J (𝟙 Osharp.obj)).obj
      (PresheafOfModules.tensorPow n (valPresheaf J G)) :=
  TensorExteriorSymmetricAlgebras.tensorAlgebraIso A (sheafifiedAlgebras J G) (n : ℤ)

end Pieces

end SheafOfModules

/-! ### The ringed-space case -/

namespace SheafOfModules

open AlgebraicGeometry TopologicalSpace RingedSpaceModuleAdjunction

variable (X : RingedSpace.{w, w})

/-- **Every sheaf of modules on a ringed space has a tensor algebra with its exterior and
symmetric quotients.** This is `nonempty_tensorExteriorSymmetricAlgebras'` at the site of open
subsets of `X`, where `structureSheafRing X` is `Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf`
on the nose (`SheafOfModules.ringSheaf_eq`). -/
theorem nonempty_ringedSpaceAlgebras (F : SheafOfModules.{w} (structureSheafRing X)) :
    Nonempty (TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) F) :=
  nonempty_tensorExteriorSymmetricAlgebras' _ F

/-- **The tensor, exterior and symmetric algebras of a sheaf of modules on a ringed space**, as
the package Section 17.21 attaches to `F`: the three graded algebras, their three universal
properties, the identification of the homogeneous pieces of `T(F)` with the tensor powers of `F`,
the degree-zero identifications, the vanishing in negative degrees, the direct-sum presentation
and the two quotient maps `T(F) ⟶ ⋀(F)` and `T(F) ⟶ Sym(F)`. It is `SheafOfModules.algebras`,
i.e. `sheafifiedAlgebras`, at the site of open subsets of `X`, so each of the three algebras is
the degreewise sheafification of its sectionwise counterpart, which is the section's own
construction. -/
@[stacks 01CF "the construction of the three algebras themselves, for a sheaf of modules on a \
ringed space, which is the object the lemmas 01CG, 01CH, 01CJ, 01CK and 01CL of the section are \
statements about; the section has no finer tag for it"]
noncomputable def ringedSpaceAlgebras (F : SheafOfModules.{w} (structureSheafRing X)) :
    TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) F :=
  algebras _ F

end SheafOfModules

end

