module

public import StacksFrontier.CategoryTheory.Sites.Modules.FlatExtensionByZeroFreeModuleUniverse
public import StacksFrontier.CategoryTheory.Sites.Modules.Gate18b.FlatRestrictionFreeModuleUniverse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero preserves flatness, at a free module universe

Let `(C, O)` be a ringed site whose objects lie in `Type u`, whose morphisms lie in `v` and
whose structure sheaf and modules have sections in `max v a`, let `U` be an object of `C` and
let `G` be a flat sheaf of `O|_U`-modules. Then `j_{U!}G` is a flat sheaf of `O`-modules.

Flatness of `j_{U!}G` is exactness of `F ↦ F ⊗_O j_{U!}G`, a functor of the module on the big
site. Stacks 0E8I identifies its value with `j_{U!}(G ⊗_{O|_U} F|_U)`, which is the composite
of three exact functors — restriction to the slice (Stacks 04IX), tensoring with the flat `G`
(Stacks 05ND), and extension by zero (Stacks 03DJ) — but only *pointwise*, and exactness of a
functor cannot be read off a pointwise identification.
`Stacks.Sites.ExtensionByZero.FreeModuleUniverse.restrictionTensorIso_naturality_right` makes
the identification natural in `F`, so the two functors are isomorphic and the exactness
transports.

## Main results

* `Stacks.SheafOfModules.FlatExtensionByZero.FreeModuleUniverse.tensorLeftExtendByZeroIso`:
  Stacks 0E8I read as an isomorphism of functors **in the module on the big site**,
  `(-) ⊗_O j_{U!}G ≅ j_{U!}(G ⊗_{O|_U} (-)|_U)`.
* `Stacks.SheafOfModules.FlatExtensionByZero.FreeModuleUniverse.isFlat_extendByZero`:
  **extension by zero preserves flatness.**

The three factors and their exactness are `sliceRestriction`, `sliceTensorLeft`,
`sliceExtension` and the three `_exact` statements about them.

## The transposed isomorphism, and what it costs

`restrictionTensorIso` is an isomorphism of functors of the module on the *slice*, one for each
module `F` on the big site. What flatness of `j_{U!}G` needs is the transpose: a single
isomorphism of functors of `F`, at a fixed `G`. Forming it means supplying a naturality square,
and that square is the naturality of `restrictionTensorIso` in `F`, which is
`restrictionTensorIso_naturality_right`. Which ways of forming it fit in the elaboration
budget is recorded below, and the answer is not the one the shape of the terms suggests.

* **The square itself is affordable, stated at variables with the composite's `.map` written
  out.** `tensorLeftExtendByZeroIso_naturality` *is* `restrictionTensorIso_naturality_right`,
  with no step in between; the one identification in it is that
  `(sliceTensorLeft X U G).map ((sliceRestriction X U).map α)` and
  `Stacks.Sites.ExtensionByZero.FreeModuleUniverse.sliceTensorRightMap X U α G` are the same
  morphism, which they are by definition.
* **The three factors of the composite are named by `def`, not by `abbrev`.** The only thing
  the naturality field asks of the elaborator beyond that square is that `(E ⋙ T ⋙ J).map α`
  is `J.map (T.map (E.map α))` — two unfoldings of `CategoryTheory.Functor.comp`. With `E`,
  `T` and `J` reducible that check does not fit in the budget; semireducible, it does, and
  nothing stronger is needed. `sliceExtension` exists for exactly this reason, as a
  semireducible name for the reducible
  `Stacks.Sites.ExtensionByZero.FreeModuleUniverse.extendByZero`. A `local irreducible` on the
  three is not an option and is not used: `tensorLeftExtendByZeroIsoApp` needs them unfolded,
  and an `abbrev` cannot carry the attribute in any case.
* **The transformation is formed first and inverted afterwards**, by
  `CategoryTheory.NatIso.isIso_of_isIso_app`, rather than assembled by
  `CategoryTheory.NatIso.ofComponents`, whose naturality argument is over budget. Giving the
  inverse explicitly instead does not help: its naturality square is affordable, but the two
  `Iso` identities are then equalities of natural transformations, and
  `CategoryTheory.NatTrans.ext` on them is over budget in turn. What is affordable is
  `tensorLeftExtendByZeroHom_app`, which identifies a component of the transformation with a
  component of the isomorphism, and that is the whole of what `asIso` needs.
* **`IsIso` of a component is read off that equation and not found by instance search.** Both
  the search and an explicit `⟨inv, _, _⟩` witness are over budget at the size of these
  morphisms; the `rw` of `tensorLeftExtendByZeroHom_app` is not.
* **The last four statements are four declarations.** The heartbeat budget is counted per
  declaration, and each of the applications assembling the exactness measures inside it while
  any two of them together do not. There is no reasoning in the split — only size.

All three factors name their source and target at the ring sheaf
`(ringSheaf X.O).over U` rather than at the other spelling
`ringSheaf (X.O.over U)` that instance search produces when the slice is
approached through `X.O.over U`; the two are definitionally equal but not reducibly so, and
pinning them is what lets the three functors be composed at all.

Raising the heartbeat budget is not an option in this development, and none of the above does.

## Universes

The objects of `C` lie in `Type u`, its morphisms in `v`, and the structure sheaf *and* the
modules in `max v a` with `UnivLE.{v, a}`. The `UnivLE` hypothesis is load-bearing and not
bookkeeping: dropped, the universe `a` occurs only inside `max v a`, Lean's level unifier is
left solving `max v ?a` against the module universe of each of the three factors, and the
naturality field below stops elaborating. The structure sheaf is tied to the modules here,
where `Stacks.SheafOfModules.FlatRestriction.FreeModuleUniverse.isFlat_over` leaves it free,
by one input: exactness of restriction to the slice,
`Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits` and
`overFunctor_preservesFiniteColimits` of Stacks 04IX, is stated with the ring sections and the
module sections in one universe. (`SheafOfModules.overFunctor_preservesFiniteLimits` of
`StacksFrontier/CategoryTheory/Sites/Modules/OverFunctorExact.lean` has the two independent but
asks the site for binary products, which a ringed site does not come with.)

That is no restriction for the site this is wanted for: the constant-coefficient ringed site of
Stacks 03TR is an `AlgebraicGeometry.RingedSite.{u + 1, u, max (u + 1) r}` whose modules lie in
`max (u + 1) r` as well, which is the case `u := u + 1`, `v := u`, `a := max (u + 1) r` of this
shape.

## References

* [Stacks Project, Tag 0E8I](https://stacks.math.columbia.edu/tag/0E8I)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 03EV](https://stacks.math.columbia.edu/tag/03EV)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 05ND](https://stacks.math.columbia.edu/tag/05ND)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules.FlatExtensionByZero.FreeModuleUniverse

universe a v u

open AlgebraicGeometry (RingedSite)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Sites.ExtensionByZero.FreeModuleUniverse
  (extendByZero tensorLeftIsoSheafTensorRight restrictionTensorIso
    restrictionTensorIso_naturality_right)

section Flat

variable (X : RingedSite.{u, v, max v a}) (U : X.C) [UnivLE.{v, a}]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max v a} RingCat.{max v a})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{max v a} RingCat.{max v a})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max v a}]
  [HasWeakSheafify X.J AddCommGrpCat.{max v a}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{max v a}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{max v a}]

/-! ### The three factors -/

/-- Restriction of sheaves of modules to the site localized at `U`, with the ring sheaf of the
slice pinned to the spelling `(ringSheaf X.O).over U` and the module universe
pinned to `max v a`: the first factor of the composite `tensorLeftExtendByZeroIso` compares
with. This is a `def` and not an `abbrev` on purpose — see the module docstring. -/
noncomputable def sliceRestriction :
    SheafOfModules.{max v a} (ringSheaf X.O) ⥤
      SheafOfModules.{max v a} ((ringSheaf X.O).over U) :=
  SheafOfModules.overFunctor (ringSheaf X.O) U

/-- Tensoring on the left with a sheaf of modules on the site localized at `U`, with its source
and target spelled at the ring sheaf `(ringSheaf X.O).over U` and at the module
universe `max v a`: the middle factor of the composite. It is the functor the flatness of `G`
is transported to, by
`Stacks.Sites.ExtensionByZero.FreeModuleUniverse.tensorLeftIsoSheafTensorRight`. -/
noncomputable def sliceTensorLeft
    (G : SheafOfModules.{max v a} ((ringSheaf X.O).over U)) :
    SheafOfModules.{max v a} ((ringSheaf X.O).over U) ⥤
      SheafOfModules.{max v a} ((ringSheaf X.O).over U) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor (X.O.over U)).obj G

/-- Extension by zero from the site localized at `U`, at the module universe `max v a`: the
last factor of the composite. This is
`Stacks.Sites.ExtensionByZero.FreeModuleUniverse.extendByZero`, which is an `abbrev` and so
reducible, under a semireducible name — which is what keeps the unifier out of it when the
composite's action on a morphism is unfolded. -/
@[sga "4 XVII 5.1.1" "partial"]
noncomputable def sliceExtension :
    SheafOfModules.{max v a} ((ringSheaf X.O).over U) ⥤
      SheafOfModules.{max v a} (ringSheaf X.O) :=
  extendByZero.{max v a} X U

/-! ### Each of the three is exact -/

omit [UnivLE.{v, a}] [X.J.HasSheafCompose (forget₂ CommRingCat.{max v a} RingCat.{max v a})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{max v a} RingCat.{max v a})] in
/-- **Restriction to the slice over `U` is exact** (Stacks 04IX), at the module universe
`max v a`. The strong sheafification both halves need is derived from `HasWeakSheafify` and
`GrothendieckTopology.WEqualsLocallyBijective`, which are hypotheses already. -/
theorem sliceRestriction_exact : exactFunctor _ _ (sliceRestriction X U) := by
  have : HasSheafify X.J AddCommGrpCat.{max v a} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  have : HasSheafify (X.J.over U) AddCommGrpCat.{max v a} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  rw [exactFunctor_iff]
  exact ⟨Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U,
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U⟩

omit [UnivLE.{v, a}] [X.J.HasSheafCompose (forget₂ CommRingCat.{max v a} RingCat.{max v a})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{max v a} RingCat.{max v a})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max v a}]
  [HasWeakSheafify X.J AddCommGrpCat.{max v a}] in
/-- **Tensoring on the left with a flat sheaf of modules on the slice is exact.** Flatness is
exactness of tensoring on the *right*, and the two agree by
`Stacks.Sites.ExtensionByZero.FreeModuleUniverse.tensorLeftIsoSheafTensorRight`. -/
theorem sliceTensorLeft_exact
    (G : SheafOfModules.{max v a} ((ringSheaf X.O).over U))
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat (O := X.O.over U) G) :
    exactFunctor _ _ (sliceTensorLeft X U G) :=
  ObjectProperty.IsClosedUnderIsomorphisms.of_iso
    (tensorLeftIsoSheafTensorRight (X.J.over U) (X.O.over U) G).symm hG

omit [UnivLE.{v, a}] [X.J.HasSheafCompose (forget₂ CommRingCat.{max v a} RingCat.{max v a})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{max v a} RingCat.{max v a})] in
/-- **Extension by zero is exact** (Stacks 03DJ), at the module universe `max v a`: this is
`Stacks.Sites.ExtensionByZero.FreeModuleUniverse.extensionByZero_exact`, read at the
semireducible name. -/
theorem sliceExtension_exact : exactFunctor _ _ (sliceExtension X U) := by
  have : HasSheafify X.J AddCommGrpCat.{max v a} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  have : HasSheafify (X.J.over U) AddCommGrpCat.{max v a} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  exact Stacks.Sites.ExtensionByZero.FreeModuleUniverse.extensionByZero_exact.{a, max v a, v, u}
    X.J (ringSheaf X.O) U

/-! ### Stacks 0E8I transposed -/

/-- **Stacks 0E8I at a fixed module on the slice**, at an object: the value of `(-) ⊗_O j_{U!}G`
at `F` is `j_{U!}(G ⊗_{O|_U} F|_U)`.

Both sides are read off `restrictionTensorIso` at the component `G`: tensoring on the left with
`j_{U!}G` and tensoring on the right with `F` have the same value, and so do tensoring on the
left with `G` and tensoring on the right with `F|_U` on the slice. -/
noncomputable def tensorLeftExtendByZeroIsoApp
    (G : SheafOfModules.{max v a} ((ringSheaf X.O).over U))
    (F : SheafOfModules.{max v a} (ringSheaf X.O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max v a, max v a, max v a} X.O).obj
        ((extendByZero.{max v a} X U).obj G)).obj F ≅
      (sliceExtension X U).obj
        ((sliceTensorLeft X U G).obj ((sliceRestriction X U).obj F)) :=
  (restrictionTensorIso.{max v a} X U F).app G

/-- **Stacks 0E8I at a fixed module on the slice is natural in the module on the big site.**

This is `restrictionTensorIso_naturality_right`, with the action of the three-fold composite
`sliceRestriction ⋙ sliceTensorLeft ⋙ sliceExtension` on `α` written out as three nested
`Functor.map`s rather than folded: it is the naturality field of `tensorLeftExtendByZeroHom`
below, and stating it here, at variables and unfolded, is what keeps that field from having to
undo the folding. -/
lemma tensorLeftExtendByZeroIso_naturality
    (G : SheafOfModules.{max v a} ((ringSheaf X.O).over U))
    {F F' : SheafOfModules.{max v a} (ringSheaf X.O)} (α : F ⟶ F') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max v a, max v a, max v a} X.O).obj
        ((extendByZero.{max v a} X U).obj G)).map α ≫
        (tensorLeftExtendByZeroIsoApp X U G F').hom =
      (tensorLeftExtendByZeroIsoApp X U G F).hom ≫
        (sliceExtension X U).map
          ((sliceTensorLeft X U G).map ((sliceRestriction X U).map α)) :=
  restrictionTensorIso_naturality_right X U α G

/-- **Stacks 0E8I read in the module on the big site**, as a natural transformation
`(-) ⊗_O j_{U!}G ⟶ j_{U!}(G ⊗_{O|_U} (-)|_U)`: the components are `restrictionTensorIso` at
`G`, and the naturality is `restrictionTensorIso_naturality_right`. -/
noncomputable def tensorLeftExtendByZeroHom
    (G : SheafOfModules.{max v a} ((ringSheaf X.O).over U)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max v a, max v a, max v a} X.O).obj
        ((extendByZero.{max v a} X U).obj G) ⟶
      sliceRestriction X U ⋙ sliceTensorLeft X U G ⋙ sliceExtension X U where
  app F := (tensorLeftExtendByZeroIsoApp X U G F).hom
  naturality _ _ α := tensorLeftExtendByZeroIso_naturality X U G α

/-- The components of `tensorLeftExtendByZeroHom` are the components of
`tensorLeftExtendByZeroIsoApp`, by definition.

Naming this is what makes `isIso_tensorLeftExtendByZeroHom_app` affordable. Asking for
`CategoryTheory.IsIso` of the left-hand side directly is not: both instance search and an
explicit `⟨inv, _, _⟩` witness exhaust the elaboration budget at the size of this morphism.
Reading the two sides of this equation off each other costs one unfolding of a semireducible
definition and a projection. -/
lemma tensorLeftExtendByZeroHom_app
    (G : SheafOfModules.{max v a} ((ringSheaf X.O).over U))
    (F : SheafOfModules.{max v a} (ringSheaf X.O)) :
    (tensorLeftExtendByZeroHom X U G).app F = (tensorLeftExtendByZeroIsoApp X U G F).hom :=
  rfl

/-- Every component of `tensorLeftExtendByZeroHom` is an isomorphism, it being the forward
map of `tensorLeftExtendByZeroIsoApp`. -/
instance isIso_tensorLeftExtendByZeroHom_app
    (G : SheafOfModules.{max v a} ((ringSheaf X.O).over U))
    (F : SheafOfModules.{max v a} (ringSheaf X.O)) :
    IsIso ((tensorLeftExtendByZeroHom X U G).app F) := by
  rw [tensorLeftExtendByZeroHom_app]
  infer_instance

/-- **Stacks 0E8I read in the module on the big site**: for a fixed sheaf `G` of
`O|_U`-modules,

`(-) ⊗_O j_{U!}G ≅ j_{U!}(G ⊗_{O|_U} (-)|_U)`

as an isomorphism of endofunctors of sheaves of `O`-modules. With `restrictionTensorIso`,
which is the naturality in the module on the slice, this is the bifunctoriality of the
comparison, transposed; no new square is proved here. -/
noncomputable def tensorLeftExtendByZeroIso
    (G : SheafOfModules.{max v a} ((ringSheaf X.O).over U)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max v a, max v a, max v a} X.O).obj
        ((extendByZero.{max v a} X U).obj G) ≅
      sliceRestriction X U ⋙ sliceTensorLeft X U G ⋙ sliceExtension X U :=
  haveI : IsIso (tensorLeftExtendByZeroHom X U G) :=
    NatIso.isIso_of_isIso_app (tensorLeftExtendByZeroHom X U G)
  asIso (tensorLeftExtendByZeroHom X U G)

/-! ### Extension by zero preserves flatness -/

omit [UnivLE.{v, a}] [X.J.HasSheafCompose (forget₂ CommRingCat.{max v a} RingCat.{max v a})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{max v a} RingCat.{max v a})] in
/-- **The composite of the three exact functors is exact.** Each factor is exact — by
Stacks 04IX, by the flatness of `G`, and by Stacks 03DJ — and exactness is preserved by
composition.

This and the three statements after it are four applications in a row, and they are four
declarations rather than one proof. The heartbeat budget is counted per declaration, and each
of the four steps measures inside it while any two of them together do not; the elaboration
cost here is in the size of the functors, not in the reasoning. -/
theorem sliceTensorExtension_exact
    (G : SheafOfModules.{max v a} ((ringSheaf X.O).over U))
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat (O := X.O.over U) G) :
    exactFunctor _ _ (sliceRestriction X U ⋙ sliceTensorLeft X U G ⋙ sliceExtension X U) := by
  obtain ⟨h₁l, h₁c⟩ := (exactFunctor_iff _).mp (sliceRestriction_exact X U)
  obtain ⟨h₂l, h₂c⟩ := (exactFunctor_iff _).mp (sliceTensorLeft_exact X U G hG)
  obtain ⟨h₃l, h₃c⟩ := (exactFunctor_iff _).mp (sliceExtension_exact X U)
  have : PreservesFiniteLimits (sliceTensorLeft X U G ⋙ sliceExtension X U) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (sliceTensorLeft X U G ⋙ sliceExtension X U) :=
    comp_preservesFiniteColimits _ _
  rw [exactFunctor_iff]
  exact ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _⟩

/-- **Tensoring on the left with `j_{U!}G` is exact**, for `G` flat: it is isomorphic to the
composite of the three exact functors by `tensorLeftExtendByZeroIso`, which is Stacks 0E8I read
in the module on the big site. -/
theorem tensorLeft_extendByZero_exact
    (G : SheafOfModules.{max v a} ((ringSheaf X.O).over U))
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat (O := X.O.over U) G) :
    exactFunctor _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max v a, max v a, max v a} X.O).obj
        ((extendByZero.{max v a} X U).obj G)) :=
  ObjectProperty.IsClosedUnderIsomorphisms.of_iso (tensorLeftExtendByZeroIso X U G).symm
    (sliceTensorExtension_exact X U G hG)

/-- **Tensoring on the right with `j_{U!}G` is exact**, for `G` flat: it is
`tensorLeft_extendByZero_exact` read through the braiding
`Stacks.Sites.ExtensionByZero.FreeModuleUniverse.tensorLeftIsoSheafTensorRight`. -/
theorem sheafTensorRight_extendByZero_exact
    (G : SheafOfModules.{max v a} ((ringSheaf X.O).over U))
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat (O := X.O.over U) G) :
    exactFunctor _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max v a, max v a, max v a} X.O).flip.obj
        ((extendByZero.{max v a} X U).obj G)) :=
  ObjectProperty.IsClosedUnderIsomorphisms.of_iso
    (tensorLeftIsoSheafTensorRight X.J X.O ((extendByZero.{max v a} X U).obj G))
    (tensorLeft_extendByZero_exact X U G hG)

/-- **Extension by zero preserves flatness**, at a free module universe: if `G` is a flat sheaf
of `O|_U`-modules then `j_{U!}G` is a flat sheaf of `O`-modules.

Flatness is exactness of tensoring on the right with `j_{U!}G`, which is
`sheafTensorRight_extendByZero_exact`; this reads that as the predicate.

Stacks 03EV part (2) — `j_{U!}O_U` is a flat `O`-module — is the case `G = O|_U` of this. -/
@[sga "4 V 1.3.1" "special case"]
theorem isFlat_extendByZero
    (G : SheafOfModules.{max v a} ((ringSheaf X.O).over U))
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat (O := X.O.over U) G) :
    AlgebraicGeometry.SheafOfModules.IsFlat ((extendByZero.{max v a} X U).obj G) :=
  sheafTensorRight_extendByZero_exact X U G hG

end Flat

section Instantiations

universe r

/-- The shape of the constant-coefficient ringed site of Stacks 03TR — an
`AlgebraicGeometry.RingedSite.{u + 1, u, max (u + 1) r}`, whose structure sheaf and module
sections both lie in `max (u + 1) r` while its morphisms lie in `u` — which is the site
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ConstructibleComplexes/` works over. The
universes have to be named at the call site: Lean's level unifier does not solve
`max v ?a =?= max (u + 1) r`, even though `v := u`, `a := max (u + 1) r` is a solution. The
order is module parameter, morphism universe, object universe. -/
example (X : RingedSite.{u + 1, u, max (u + 1) r}) (U : X.C)
    [X.J.HasSheafCompose (forget₂ CommRingCat.{max (u + 1) r} RingCat.{max (u + 1) r})]
    [(X.J.over U).HasSheafCompose
      (forget₂ CommRingCat.{max (u + 1) r} RingCat.{max (u + 1) r})]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) r}]
    [HasWeakSheafify X.J AddCommGrpCat.{max (u + 1) r}]
    [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) r}]
    [HasWeakSheafify (X.J.over U) AddCommGrpCat.{max (u + 1) r}]
    (G : SheafOfModules.{max (u + 1) r} ((ringSheaf X.O).over U))
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat (O := X.O.over U) G) :
    AlgebraicGeometry.SheafOfModules.IsFlat ((extendByZero.{max (u + 1) r} X U).obj G) :=
  isFlat_extendByZero.{max (u + 1) r, u, u + 1} X U G hG

end Instantiations

end Stacks.SheafOfModules.FlatExtensionByZero.FreeModuleUniverse

end
