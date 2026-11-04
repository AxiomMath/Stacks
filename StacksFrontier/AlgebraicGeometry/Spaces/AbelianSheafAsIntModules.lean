module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.CompactGenerationOfAbelianSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.MapOutOfAConstantComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.AbelianSheafMonoidalPreadditive

/-!
# Abelian sheaves are the modules over the constant sheaf of rings `ℤ`

On a site `(C, J)` the category of abelian sheaves is equivalent to the category of sheaves of
modules over the constant sheaf of rings `ℤ`, in the spelling
`Stacks.SheafOfModules.DerivedMonoidal.Mod` that the derived tensor product of a ringed site is
built on. Specialised to the open-cover topology of a topological space, this presents
`Stacks.Cohomology.Leray.AbelianSheaf X` as a category of sheaves of modules.

The mathematics is entirely imported. `Stacks.Cohomology.isEquivalence_toSheaf_intSheaf` already
says that sheaves of modules over the constant sheaf of rings `ℤ` are the abelian sheaves, and
the only thing between that statement and the one wanted here is that a ringed site's structure
sheaf takes values in `CommRingCat`: the derived tensor product is indexed by a sheaf of
*commutative* rings `O`, and the sheaf of rings its modules are taken over is
`Stacks.SheafOfModules.Tensor.ringSheaf O`. For `O` the constant sheaf of commutative rings `ℤ`
that sheaf of rings is the constant sheaf of rings `ℤ` by `CategoryTheory.constantCommuteCompose`,
and a change of the sheaf of rings along an isomorphism is an equivalence by
`Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso`.

## Main definitions

* `Stacks.Cohomology.constIntCommSheaf`: the constant sheaf of commutative rings with value
  `ULift ℤ`.
* `Stacks.Cohomology.ringSheafConstIntIso`: its underlying sheaf of rings is the constant sheaf
  of rings `ℤ`.

## Main results

* `Stacks.Cohomology.intModulesEquivAbelianSheaves`: **abelian sheaves on a site are the modules
  over the constant sheaf of rings `ℤ`.**
* `Stacks.Cohomology.Leray.abelianSheafIntModulesEquivalence`: the same for the abelian sheaves
  of a topological space.

## Implementation notes

**What this is for, and what it does not supply.** The derived category of modules on a ringed
site is monoidal, `Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal`, and the single
hypothesis of the general construction
`CochainComplex.KFlatMonoidal.derivedMonoidal` — the existence of K-flat resolutions — is
discharged there unconditionally by Tag 06YS. That hypothesis transports along an equivalence of
categories carrying one tensor product to the other,
`CochainComplex.KFlatBifunctor.exists_kFlat_resolution_of_equivalence`. The equivalence below,
and its additivity in both directions, are unconditional.

**What that transport still wants, enumerated against its binders.** It is worth being exact,
because the equivalence is *not* the only thing missing. Reading
`CochainComplex.KFlatBifunctor.exists_kFlat_resolution_of_equivalence` at
`A := Stacks.SheafOfModules.DerivedMonoidal.Mod (constIntCommSheaf J)`,
`A' := Sheaf J AddCommGrpCat`, `F := Stacks.SheafOfModules.Tensor.sheafTensor` and
`F' := MonoidalCategory.curriedTensor`, all of its inputs are available except the tensor
comparison.

Available:

* `hres` on the `A` side, unconditionally and with no ringed-site wrapper interposed:
  `Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution` asks only for
  `HasSheafify J AddCommGrpCat` and `J.WEqualsLocallyBijective AddCommGrpCat`, both of which are
  already in scope here, and its conclusion is `KFlat (curriedTensor (Mod R))`, which is
  `KFlat (Stacks.SheafOfModules.Tensor.sheafTensor R)` by
  `Stacks.SheafOfModules.DerivedMonoidal.curriedTensor_mod_eq_sheafTensor`.
* the additivity of `F` in each variable, and the all-pairs total tensor complex
  `Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor` — but only when `F` is spelled
  `Stacks.SheafOfModules.Tensor.sheafTensor R`, since the instance is named at that spelling and
  not at `curriedTensor (Mod R)`, the two being `rfl`-equal but not syntactically equal.
* the additivity of the equivalence's two functors, which is what this file adds below.
* the additivity of `F'` in each variable, from
  `Stacks.Cohomology.Leray.abelianSheafMonoidalPreadditive`.
* the all-pairs total tensor complex on the `A'` side,
  `Stacks.Cohomology.hasMapBifunctor_curriedTensor_abelianSheaves`, together with the braided
  monoidal structure on the cochain complexes of abelian sheaves,
  `Stacks.Cohomology.braidedCategoryCochainComplexAbelianSheaves`, both in
  `StacksFrontier/AlgebraicGeometry/Spaces/AbelianSheafDerivedTensor.lean`. They hold because
  tensoring with an abelian sheaf is a left adjoint —
  `Stacks.Cohomology.monoidalClosed_abelianSheaves`, Day's reflection theorem applied
  to the sheafification adjunction — so it commutes with the antidiagonal coproducts.
* `HasDerivedCategory (Sheaf J AddCommGrpCat)`, which needs nothing new: it is
  `HasDerivedCategory.standard`, Mathlib's construction for an arbitrary abelian category, which
  this library already seats for `Stacks.Cohomology.Leray.AbelianSheaf` in
  `StacksFrontier/Topology/Sheaves/Cohomology/Leray/AbelianSheafSpectralSequence.lean`. It is
  carried as an instance binder rather than renamed, `HasDerivedCategory` being data.

Also available:

* the tensor comparison, `Stacks.Cohomology.abelianSheafTensorComparison` of
  `StacksFrontier/AlgebraicGeometry/Spaces/AbelianSheafTensorComparison.lean`, with its two
  naturality squares; the transport is run there and
  `Stacks.Cohomology.exists_kFlat_resolution_abelianSheaves` is its conclusion. The paragraphs
  below record which legs of that construction are definitional and which are not, and the
  construction follows them. It is a natural isomorphism identifying the tensor product of
  `Stacks.SheafOfModules.Tensor.sheafTensor` with the tensor product of abelian sheaves across
  the equivalence — concretely, that `SheafOfModules.toSheaf` carries `ℱ ⊗_{ℤ̲} 𝒢` to `ℱ ⊗ 𝒢`.
  Only the bifunctor comparison `ε` and its two naturality squares are wanted, not monoidality.
  Both tensor products are sheafifications of an objectwise tensor, over `ℤ̲(U)` on the one side
  and over `ℤ` on the other, and the objectwise comparison is Mathlib's
  `TensorProduct.mapOfCompatibleSMul`, which is objectwise surjective
  (`TensorProduct.mapOfCompatibleSMul_surjective`) and whose kernel is spanned by the elements
  `(a • m) ⊗ₜ n - m ⊗ₜ (a • n)`
  (`TensorProduct.AlgebraTensorModule.ker_mapOfCompatibleSMul`). Each such generator dies on the
  sieve where `a` becomes an integer, which is covering because the sheafification unit is
  locally surjective, so the comparison is locally bijective and an isomorphism after
  sheafification.

**Which legs of that transport are already definitional.** Two of the three legs below are
free, and naming them is what keeps the construction from being carried out in the wrong
spelling.

* On the `Mod` side nothing is owed at all. The underlying abelian sheaf of a sheafified
  presheaf of modules *is* the sheafification of the underlying abelian presheaf:
  `PresheafOfModules.sheafificationCompToSheaf` is `Iso.refl`, and it applies at
  `Stacks.SheafOfModules.Tensor.ringSheaf (constIntCommSheaf J)` as it stands. Since
  `Stacks.SheafOfModules.Tensor.sheafTensor` is by definition
  `Stacks.SheafOfModules.Tensor.presheafTensor` followed by that sheafification, the left-hand
  side of `ε` is already `presheafToSheaf` of an objectwise tensor of presheaves of modules.
* On the abelian-sheaf side the carrier is definitional too, and at an *arbitrary* universe:
  for `F G : Cᵒᵖ ⥤ AddCommGrpCat.{v}` and `V : Cᵒᵖ`, both `(F ⊗ G).obj V = F.obj V ⊗ G.obj V`
  and the identification of the carrier of `A ⊗ B` with
  `TensorProduct AddCommGrpCat.ULiftInt (uliftIntEquivalence.inverse.obj A)
  (uliftIntEquivalence.inverse.obj B)` hold by `rfl`. So the transport from
  `CategoryTheory.Sheaf.monoidalCategory` down to a concrete `TensorProduct` over
  `AddCommGrpCat.ULiftInt` costs nothing; what the two `rfl`s do *not* give is any
  identification of `uliftIntEquivalence.inverse.obj (F.obj V)` with `F.obj V`, which is not
  `rfl` and has to be carried by the counit of the equivalence.
* Passing between the sheaf-level tensor and the sheafification of the presheaf-level tensor is
  free as well: `presheafToSheaf J AddCommGrpCat` is strong monoidal, so
  `Functor.Monoidal.μIso` is available, and `(sheafificationAdjunction J AddCommGrpCat).counit`
  is an isomorphism, so a sheaf is the sheafification of its own underlying presheaf.
  Finally `J.W_of_isLocallyBijective` together with `Localization.inverts` turns a locally
  bijective presheaf map into an isomorphism after sheafification.

**The objectwise bridge that already exists cannot be used here, and the obstruction is
universes.** `AddCommGrpCat.presheafTensorIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/SpacesEtaleTensor.lean` identifies the objectwise tensor
product over `ℤ` of two presheaves of abelian groups with the tensor product of the transported
monoidal structure, which is exactly the comparison wanted — but it is stated only for
`Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}`, as are `AddCommGrpCat.presheafTensor` and
`AddCommGrpCat.presheafTensorMap`. A generic `AddCommGrpCat.{v}` is not of successor form, so
reading it at the universe this file is written over fails to elaborate. The same pinning
affects `AddCommGrpCat.uliftInt_smul_eq_zsmul`, which is generic in its universe but whose
statement mentions the `SMul` instance `AddCommGrpCat.uliftIntSMul` declared `local` in that
file, so outside it the statement is about a different instance than the one instance search
supplies. Either the `ℤ`-objectwise route is generalised in universe, or — and this is the
shorter road — the comparison is built directly against
`TensorProduct AddCommGrpCat.ULiftInt`, which the two `rfl`s above hand over for free and
which is also the base ring `TensorProduct.mapOfCompatibleSMul` is wanted at, so that the
detour through a tensor product over `ℤ` is never taken.

**What the comparison is built from, in this order, in
`StacksFrontier/AlgebraicGeometry/Spaces/AbelianSheafTensorComparison.lean`.** A
presheaf-level natural transformation from the
pointwise tensor of the two underlying abelian presheaves to the underlying abelian presheaf of
`Stacks.SheafOfModules.Tensor.presheafTensor`, objectwise
`TensorProduct.mapOfCompatibleSMul`; its naturality in `V`, which is where the counit of
`AddCommGrpCat.uliftIntEquivalence` enters; its local surjectivity, which is objectwise
surjectivity; its local injectivity by the span argument above, which needs the sections of
`constIntCommSheaf J` to be locally integers and a finite intersection of covering sieves; and
then the assembly of `ε` and of the two naturality squares. None of that is a coherence
condition — `ε` is a family of isomorphisms with two naturality squares and nothing else — so
no monoidal structure on either side has to be compared, and in particular the statement is
not blocked on anything of the kind.

That is the whole of it: with the instances of
`StacksFrontier/AlgebraicGeometry/Spaces/AbelianSheafDerivedTensor.lean` in scope, every *instance*
binder of `CochainComplex.KFlatBifunctor.exists_kFlat_resolution_of_equivalence` at the four
arguments above is discharged by instance search, and `ε` with its two naturality squares is the
only input left. `Stacks.Cohomology.derivedMonoidalAbelianSheaves` is the packaging that consumes
the resulting `hres`.

The module documentation of `StacksFrontier/Homology/KFlat/MonoidalResolutionTransport.lean`
records the state of the passage as a whole.

The universes are pinned to a single `u`, the site being small with its morphisms and its
sections in the same universe, because that is the generality
`Stacks.SheafOfModules.DerivedMonoidal.Mod` is available at; the restriction is inherited from
there and is not introduced here. For a topological space `X : TopCat.{u}` it is no restriction
at all: `Stacks.Cohomology.Leray.AbelianSheaf X` is already at that universe.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Cohomology

section Site

variable {C : Type u} [SmallCategory.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{u}] [HasSheafify J RingCat.{u}]
  [J.WEqualsLocallyBijective RingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The constant sheaf of commutative rings with value `ULift ℤ`, the structure sheaf of the
ringed site whose modules are the abelian sheaves. -/
abbrev constIntCommSheaf : Sheaf J CommRingCat.{u} :=
  (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of (ULift.{u} ℤ))

/-- **The sheaf of rings underlying the constant sheaf of commutative rings `ℤ` is the constant
sheaf of rings `ℤ`.** Forgetting commutativity preserves sheafification, so it commutes with the
constant sheaf functor. -/
def ringSheafConstIntIso :
    Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (constIntCommSheaf J) ≅ intSheaf.{u} J :=
  (constantCommuteCompose J (forget₂ CommRingCat.{u} RingCat.{u})).app
    (CommRingCat.of (ULift.{u} ℤ))

/-- **Abelian sheaves on a site are the modules over the constant sheaf of rings `ℤ`**, in the
spelling of the modules of a ringed site. An additive map of abelian sheaves is automatically
`ℤ`-linear and an abelian sheaf carries a unique action of the constant sheaf `ℤ`, which is
`Stacks.Cohomology.isEquivalence_toSheaf_intSheaf`; what is added here is only the passage from
the constant sheaf of rings to the constant sheaf of *commutative* rings that the structure sheaf
of a ringed site is, which is a change of the sheaf of rings along
`Stacks.Cohomology.ringSheafConstIntIso`. -/
def intModulesEquivAbelianSheaves :
    Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J) ≌
      Sheaf J AddCommGrpCat.{u} :=
  letI := isEquivalence_toSheaf_intSheaf.{u} J
  (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      (ringSheafConstIntIso J)).trans
    (SheafOfModules.toSheaf (intSheaf.{u} J)).asEquivalence

/-- **The equivalence presenting abelian sheaves as modules over the constant sheaf of rings `ℤ`
is additive.** On morphisms it changes nothing: a morphism of modules over the constant sheaf is
in particular a morphism of the underlying abelian sheaves, and neither restricting the scalars
along `Stacks.Cohomology.ringSheafConstIntIso` nor forgetting them afterwards touches the
underlying map, so addition of morphisms is preserved by definition.

This and `Stacks.Cohomology.inverseAdditive_intModulesEquivAbelianSheaves` are two of the binders
required by `CochainComplex.KFlatBifunctor.exists_kFlat_resolution_of_equivalence`; see the
implementation notes above. -/
instance functorAdditive_intModulesEquivAbelianSheaves :
    (intModulesEquivAbelianSheaves J).functor.Additive where
  map_add := by intros; rfl

/-- **The quasi-inverse of that equivalence is additive too**, a quasi-inverse of an additive
equivalence between preadditive categories being additive. -/
instance inverseAdditive_intModulesEquivAbelianSheaves :
    (intModulesEquivAbelianSheaves J).inverse.Additive :=
  inferInstance

end Site

namespace Leray

/-- **The abelian sheaves of a topological space are the modules over the constant sheaf of
rings `ℤ` on its site of opens.** This is
`Stacks.Cohomology.intModulesEquivAbelianSheaves` at the open-cover topology, whose
sheafification hypotheses for presheaves of rings are
`Stacks.Cohomology.hasSheafify_ringCat` and
`Stacks.Cohomology.wEqualsLocallyBijective_ringCat`. -/
def abelianSheafIntModulesEquivalence (X : TopCat.{u}) :
    Stacks.SheafOfModules.DerivedMonoidal.Mod.{u}
        (constIntCommSheaf (Opens.grothendieckTopology X)) ≌ AbelianSheaf X :=
  letI := hasSheafify_ringCat.{u, u, u} (Opens.grothendieckTopology X)
  letI := wEqualsLocallyBijective_ringCat.{u, u, u} (Opens.grothendieckTopology X)
  intModulesEquivAbelianSheaves (Opens.grothendieckTopology X)

/-- The equivalence of `Stacks.Cohomology.Leray.abelianSheafIntModulesEquivalence` is additive.
This is `Stacks.Cohomology.functorAdditive_intModulesEquivAbelianSheaves`, restated at the
open-cover topology: the generic-site instance is named at
`Stacks.Cohomology.intModulesEquivAbelianSheaves J`, and the two `letI`s in the body above put
the specialisation out of reach of instance search. -/
instance functorAdditive_abelianSheafIntModulesEquivalence (X : TopCat.{u}) :
    (abelianSheafIntModulesEquivalence X).functor.Additive where
  map_add := by intros; rfl

/-- The quasi-inverse of `Stacks.Cohomology.Leray.abelianSheafIntModulesEquivalence` is
additive. -/
instance inverseAdditive_abelianSheafIntModulesEquivalence (X : TopCat.{u}) :
    (abelianSheafIntModulesEquivalence X).inverse.Additive :=
  inferInstance

end Leray

end Stacks.Cohomology

end
