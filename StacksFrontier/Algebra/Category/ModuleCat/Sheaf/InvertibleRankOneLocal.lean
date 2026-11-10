module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Invertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom
public import StacksCore.Tactic.StacksAttribute

/-!
# A finite locally free sheaf of modules of rank one is invertible

Let `𝒪` be a presheaf of commutative rings on a site `(C, J)` whose underlying presheaf of
rings is a sheaf, and let `L` be a sheaf of `𝒪`-modules. This file proves the unconditional
direction of [Stacks, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M): if `L` is finite
locally free of rank one, then `L` is invertible.

Both halves of that implication are already in this library and this file is the bridge
between them. On one side,
`Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank L 1` says that `L` admits local
generators forming locally free data whose indexing types are equivalent to `Fin 1`, and
`Stacks.SheafOfModules.Invertible.isLocallyTrivial_of_isFiniteLocallyFreeOfRank_one` turns
that into a covering family `X : I → C` of the final object together with trivializations
`L.over (X i) ≅ SheafOfModules.unit (𝒪.over (X i))`. On the other side,
`Stacks.SheafOfModules.isInvertible_of_dualBasisOne` proves invertibility from a
`Stacks.SheafOfModules.DualBasisOne` on each member of a covering family, that is, from a
generating section of `L` over `X i` together with its dual coordinate. The content here is
the conversion of a trivialization into such a dual basis.

## Main definitions

* `Stacks.SheafOfModules.DualBasisOne.ofTrivialization`: the rank-one dual basis attached to a
  trivialization `ε : L.over U ≅ SheafOfModules.unit (𝒪.over U)`. Its basis section is the
  image of `1` under `ε.inv`, and its dual coordinate is `ε.hom` read as a section of the dual
  sheaf `L^∨` over `U`.

## Main results

* `Stacks.SheafOfModules.exists_coversTop_dualBasisOne_of_isFiniteLocallyFreeOfRank_one`: a
  finite locally free sheaf of modules of rank one carries rank-one dual bases on a family of
  objects covering the final object.
* `Stacks.SheafOfModules.isInvertible_of_isFiniteLocallyFreeOfRank_one`: **Tag 0B8M**, the
  unconditional direction. A finite locally free sheaf of modules of rank one is invertible.
  `Stacks.SheafOfModules.isInvertible_of_isFiniteLocallyFreeOfRank_one'` is the same statement
  with the hypothesis as an explicit argument, which is what a consumer spelling the structure
  sheaf differently must use; see the implementation notes.
* `Stacks.SheafOfModules.module_invertible_grpStalk` and
  `Stacks.SheafOfModules.nonempty_grpStalk_linearEquiv`: the first two steps of the converse
  direction on a ringed space. The stalks of an invertible sheaf of modules are invertible
  modules over the stalks of the structure sheaf, hence free of rank one as soon as those stalks
  are local rings. See the implementation notes for what the converse still needs.

## Implementation notes

**The identification that makes this work.** A section of the dual sheaf `L^∨` over `U` is, by
`internalHom` of [Stacks, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM), a morphism
`(restrFun 𝒪 U).obj L.val ⟶ (restrFun 𝒪 U).obj (SheafOfModules.unit _).val` of presheaves of
modules on the slice site `C/U`, where `restrFun 𝒪 U` is
`PresheafOfModules.pushforward (𝟙 (ORestr 𝒪 U))`. A trivialization, on the other hand, is a
morphism of sheaves of modules over `(Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
  h𝒪).over U`, whose underlying
presheaf morphism is produced by `SheafOfModules.overFunctor`, that is, by
`SheafOfModules.pushforward (𝟙 _)` along the same functor `(Over.forget U).op`. The two are
therefore the *same* construction, and `over_obj_eq_ORestr`, `over_val_eq_restrFun` and
`unit_over_val_eq_restrFun` record that they agree on the nose. Those three `rfl` lemmas are
what lets `ε.hom.val` be used directly as a section of the dual sheaf, with no transport.

**Why the basis section is extracted through `SheafOfModules.unitHomEquiv`.** The basis section
is `ε.inv` applied to `1`, and the `span` field of `DualBasisOne` needs its restriction to every
object `V` of `C/U`. Reading `ε.inv` as a global section of `L.over U` through
`SheafOfModules.unitHomEquiv` packages exactly that compatibility: the `span` proof is then
`PresheafOfModules.sections_property` applied to the morphism
`Over.homMk V.unop.hom : V.unop ⟶ Over.mk (𝟙 U)` of `C/U`. Going instead through naturality of
`ε.inv` would require rewriting with `PresheafOfModules.unit_map_one` across the
`SheafOfModules.unit _ |>.val` versus `PresheafOfModules.unit _` spellings, which `rw` cannot
see through.

**Why the sections of the unit module need an explicit ring instance.** The sections of
`SheafOfModules.unit ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over U)`
  over an object `V` of `C/U` are
`ModuleCat.of (𝒪.obj (op V.unop.left)) (𝒪.obj (op V.unop.left))`, so their carrier *is* a ring,
but `SheafOfModules.unit` is a plain definition and instance search does not unfold it. The
numeral `1` therefore does not elaborate at that type without help;
`commRingUnitOverObj` supplies the instance, and it is `local` because it is needed only for
the proofs in this file.

**Universes (inherited, not narrowed here).** The module universe is `max u v` for a site
`C : Type u` with `Category.{v} C`, and the ring universe is the same. This is the restriction
already recorded in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafHom.lean`, of which only
one cause applies: `Stacks03EM.internalHom` is universe-polymorphic in the module universe, so
the pin comes solely from `Stacks.SheafOfModules.TensorSheafification` identifying the ring
universe with the module universe. Nothing is narrowed further here. The covering family
produced by `IsLocallyTrivial` is indexed by a `Type u`, which is what
`isInvertible_of_dualBasisOne` accepts, so no index universe is specialized either.

**The two settings in this file.** Everything up to and including Tag 0B8M's unconditional
direction works over an arbitrary site. The two stalk results at the end are stated on a ringed
space `X : RingedSpace.{u, u}`, because "the stalks of the structure sheaf are local rings" is a
statement about points, and because the stalk pairing they consume
(`Stacks.SheafOfModules.stalkPairing` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FinitePresentationStalk.lean`) is built there.
They use the `Stacks.SheafOfModules.TensorStalkRingedSpace` vocabulary `structureSheafRing`,
  `ringStalk`, `grpStalk` of
Tag 01CB, which is the vocabulary in which that pairing is stated.

**What the converse still needs.** Tag 0B8M's converse is, in Stacks' own proof, the
composite of four steps: the stalks of `L` are invertible; they are therefore free of rank one
over a local ring; `L` is of finite presentation; and Tag 0B8J then trivialises `L` on a
neighbourhood of each point. The first two steps are `module_invertible_grpStalk` and
`nonempty_grpStalk_linearEquiv` here, and the fourth is
`Stacks.SheafOfModules.exists_iso_free_over_of_stalk_iso_free` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/StalkFreeCover.lean`. The third is missing: no
declaration in this library derives `SheafOfModules.IsFinitePresentation L` from invertibility.
What is available is
`Stacks.SheafOfModules.exists_cover_isDirectSummand_finiteFree` (Tag 0B8N) of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleSummandSheafify.lean`, which exhibits
`L` locally as a split subobject of a finite product of copies of the structure sheaf; turning
that retraction into a `SheafOfModules.QuasicoherentData` with finite generators and finite
relations is the step nobody has taken. A second, smaller gap sits between the two stalk
results here and Tag 0B8J: that tag's hypothesis is phrased with the stalk of the structure
sheaf computed in `RingCat`, whereas `ringStalk` computes it in `CommRingCat`, and the
comparison of those two filtered colimits is not yet a declaration either. So no converse
statement is proved here and nothing carries a second `@[stacks 0B8M]` attribute.

**What is not proved at all.** The parenthetical remark of Tag 0B8M, that the converse fails for
a general ringed space, is not addressed. Its witness is a one-point space whose ring of
sections has nontrivial Picard group, and the pinned Mathlib proves no ring's Picard group to be
nontrivial: it has `CommRing.Pic`, `ClassGroup.equivPic` and the triviality results, but no
computed example.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
* [Stacks Project, Tag 0AFW](https://stacks.math.columbia.edu/tag/0AFW)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}}
  {h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪)}
  {L : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}

/-! ### The identification of the two restriction constructions -/

/-- The sheaf of rings `𝒪` restricted to the slice site `C/U` by Mathlib's `Sheaf.over` is the
presheaf of rings `ORestr 𝒪 U` of Tag 03EM: both are `(Over.forget U).op ⋙ Oforget 𝒪`. -/
lemma over_obj_eq_ORestr (U : C) :
    ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over U).obj = ORestr 𝒪 U :=
      rfl

/-- A sheaf of modules restricted to the slice site `C/U` by Mathlib's `SheafOfModules.over` has
as underlying presheaf of modules the restriction `restrFun 𝒪 U` of Tag 03EM: both are
`PresheafOfModules.pushforward` of the identity along `(Over.forget U).op`. -/
lemma over_val_eq_restrFun (U : C) : (L.over U).val = (restrFun 𝒪 U).obj L.val := rfl

/-- The structure sheaf of the slice site `C/U`, viewed as a module over itself, is the
restriction of the structure sheaf of `C` viewed as a module over itself. -/
lemma unit_over_val_eq_restrFun (U : C) :
    (SheafOfModules.unit ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over
      U)).val =
      (restrFun 𝒪 U).obj (SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)).val := rfl

/-- The sections over an object `V` of `C/U` of the structure sheaf of `C/U`, viewed as a module
over itself, form a commutative ring: they are the sections of `𝒪` over `V.left`. Instance
search does not see this on its own, because `SheafOfModules.unit` is not reducible; the
instance is needed so that the numeral `1` elaborates at that type. -/
noncomputable local instance commRingUnitOverObj (U : C) (V : (Over U)ᵒᵖ) :
    CommRing ((SheafOfModules.unit
      ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over U)).val.obj V) :=
  inferInstanceAs (CommRing (𝒪.obj (op V.unop.left)))

/-! ### From a trivialization to a rank-one dual basis -/

section Trivialization

variable {U : C}
  (ε : L.over U ≅ SheafOfModules.unit ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
    h𝒪).over U))

/-- The component of a trivialization at an object of the slice site is injective on the nose:
`ε.inv` undoes `ε.hom`. -/
lemma trivialization_inv_hom_apply (V : (Over U)ᵒᵖ) (x : (L.over U).val.obj V) :
    (ε.inv.val.app V).hom ((ε.hom.val.app V).hom x) = x := by
  have h : ((ε.hom ≫ ε.inv).val.app V).hom x = x := by rw [ε.hom_inv_id]; rfl
  exact h

/-- The component of a trivialization at an object of the slice site is surjective on the nose:
`ε.hom` undoes `ε.inv`. -/
lemma trivialization_hom_inv_apply (V : (Over U)ᵒᵖ)
    (y : (SheafOfModules.unit ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over
      U)).val.obj V) :
    (ε.hom.val.app V).hom ((ε.inv.val.app V).hom y) = y := by
  have h : ((ε.inv ≫ ε.hom).val.app V).hom y = y := by rw [ε.inv_hom_id]; rfl
  exact h

/-- Scaling the image of `1` under `ε.inv` is the image of the scalar: the trivialization is
linear, and the unit module is the structure sheaf acting on itself, so `c • 1 = c`. This is the
computation behind the `span` field of `DualBasisOne.ofTrivialization`. -/
lemma smul_trivialization_inv_one (V : (Over U)ᵒᵖ)
    (c : ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over U).obj.obj V) :
    c • (ε.inv.val.app V).hom (1 : (SheafOfModules.unit
        ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over U)).val.obj V) =
      (ε.inv.val.app V).hom c := by
  rw [← (ε.inv.val.app V).hom.map_smul]
  congr 1
  exact mul_one c

/-- **A trivialization of `L` over `U` is a rank-one dual basis over `U`.**

The basis section is the image of `1 ∈ 𝒪(U)` under `ε.inv`, and the dual coordinate is `ε.hom`,
which is literally a section of the dual sheaf `L^∨` over `U` by `over_val_eq_restrFun` and
`unit_over_val_eq_restrFun`. The `span` field says that a section `g` of `L` over an object `V`
of `C/U` is `ε.hom(g)` times the restriction of the basis section, which holds because `ε.inv`
is linear and inverts `ε.hom`; the `eval_self` field says that `ε.hom` sends the basis section
to `1`, which is the other half of `ε` being an isomorphism rather than a mere retraction. -/
noncomputable def DualBasisOne.ofTrivialization : DualBasisOne 𝒪 h𝒪 L U where
  e := ((L.over U).unitHomEquiv ε.inv).val (op (Over.mk (𝟙 U)))
  lam := ε.hom.val
  span V g := by
    rw [show resSection V (((L.over U).unitHomEquiv ε.inv).val (op (Over.mk (𝟙 U)))) =
        (ε.inv.val.app V).hom 1 from
      PresheafOfModules.sections_property ((L.over U).unitHomEquiv ε.inv)
        (Over.homMk V.unop.hom (Category.comp_id _) : V.unop ⟶ Over.mk (𝟙 U)).op]
    exact (smul_trivialization_inv_one ε V _).trans (trivialization_inv_hom_apply ε V g)
  eval_self := trivialization_hom_inv_apply ε (op (Over.mk (𝟙 U))) 1

end Trivialization

/-! ### Tag 0B8M, the unconditional direction -/

section Sheafification

variable [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{max u v}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- **A finite locally free sheaf of modules of rank one carries rank-one dual bases on a
covering family.** The local generators of rank one trivialize `L` over a covering family of the
final object (`Invertible.isLocallyTrivial_of_isFiniteLocallyFreeOfRank_one`), and each
trivialization is a rank-one dual basis by `DualBasisOne.ofTrivialization`.

`DualBasisOne` is data, not a proposition, so the family of dual bases is asserted through
`Nonempty`; the data itself is produced by `DualBasisOne.ofTrivialization` from a chosen
trivialization. -/
theorem exists_coversTop_dualBasisOne_of_isFiniteLocallyFreeOfRank_one
    (L : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    [Invertible.IsFiniteLocallyFreeOfRank L 1] :
    ∃ (I : Type u) (X : I → C) (_ : J.CoversTop X),
      Nonempty (∀ i, DualBasisOne 𝒪 h𝒪 L (X i)) := by
  obtain ⟨I, X, hX, ε⟩ :=
    (Invertible.isLocallyTrivial_of_isFiniteLocallyFreeOfRank_one
      L).exists_trivializing_cover
  exact ⟨I, X, hX, ⟨fun i => DualBasisOne.ofTrivialization (ε i).some⟩⟩

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]

namespace Invertible

/-- **Stacks Project, Tag 0B8M.** A finite locally free sheaf of modules of rank one is
invertible.

This is the statement for `Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank`, and it
lives in that predicate's namespace;
`Stacks.SheafOfModules.isInvertible_of_isFiniteLocallyFreeOfRank_one` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyTrivialInvertible.Basic` is the statement
for `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank`, the other rank predicate of
[Stacks, Tag 01CS].

The local generators of rank one give a covering family of the final object on which `L` becomes
isomorphic to the structure sheaf; each such trivialization is a rank-one dual basis, and
`isInvertible_of_dualBasisOne` turns a family of those on a covering family into invertibility
by way of the evaluation pairing `L^∨ ⊗ L ⟶ 𝒪` and Tag 0B8K. -/
@[stacks 0B8M "locally free of rank one implies invertible", instance]
theorem isInvertible_of_isFiniteLocallyFreeOfRank_one
    (L : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    [Invertible.IsFiniteLocallyFreeOfRank L 1] : IsInvertible 𝒪 h𝒪 L := by
  obtain ⟨_, _, hX, ⟨b⟩⟩ :=
    exists_coversTop_dualBasisOne_of_isFiniteLocallyFreeOfRank_one L
  exact isInvertible_of_dualBasisOne 𝒪 h𝒪 hX b

/-- `isInvertible_of_isFiniteLocallyFreeOfRank_one` with the finite-local-freeness hypothesis as
an explicit argument rather than an instance.

This is the form a consumer that writes the structure sheaf differently has to use.
`Invertible.IsFiniteLocallyFreeOfRank` is indexed by the sheaf of rings, and
`Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪` is a plain definition, so a
  hypothesis stated with a
definitionally equal but syntactically different spelling of that sheaf of rings — for instance
the `structureSheaf Rc` of Stacks Tag 01CO on a ringed space — is not
found by instance search, which does not unfold either spelling. Passing it explicitly works,
because the elaborator checks definitional equality there. -/
theorem isInvertible_of_isFiniteLocallyFreeOfRank_one'
    (L : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    (h : Invertible.IsFiniteLocallyFreeOfRank L 1) : IsInvertible 𝒪 h𝒪 L :=
  have := h
  isInvertible_of_isFiniteLocallyFreeOfRank_one L

end Invertible

end Sheafification

/-! ### Towards the converse: the stalks of an invertible sheaf of modules -/

section RingedSpaceStalks

open AlgebraicGeometry Stacks.SheafOfModules.TensorStalkRingedSpace

variable (X : RingedSpace.{u, u}) (L : SheafOfModules.{u} (structureSheafRing X))
  [IsInvertible X.presheaf (structureSheafRing X).property L]

/-- **The stalks of an invertible sheaf of modules are invertible modules.**

By Tag 0B8K there is a sheaf of modules `N` with `L ⊗ N ≅ 𝒪`, and `stalkPairing` turns that
isomorphism into a linear equivalence `L_x ⊗_{𝒪_x} N_x ≃ 𝒪_x` of stalks; a module admitting such
a partner is invertible. No hypothesis on the stalks of the structure sheaf is needed. -/
theorem module_invertible_grpStalk (x : X.carrier) :
    Module.Invertible (ringStalk X x) (grpStalk X L.val x) := by
  obtain ⟨N, ⟨ψ⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit
    (O := X.presheaf) (hO := (structureSheafRing X).property) L).mp ‹_›
  exact Module.Invertible.left (stalkPairing ψ x)

/-- **The stalks of an invertible sheaf of modules are free of rank one when the stalks of the
structure sheaf are local rings.**

This is the pointwise input to the converse direction of Tag 0B8M: the Picard group of a local
ring is trivial, so the invertible module `L_x` of `module_invertible_grpStalk` is isomorphic to
`𝒪_x`. It is Tag 0AFW, supplied by
`Invertible.nonempty_linearEquiv_of_module_invertible`. -/
theorem nonempty_grpStalk_linearEquiv [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
    (x : X.carrier) :
    Nonempty (grpStalk X L.val x ≃ₗ[ringStalk X x] ringStalk X x) :=
  have := module_invertible_grpStalk X L x
  Invertible.nonempty_linearEquiv_of_module_invertible _ _

end RingedSpaceStalks

end Stacks.SheafOfModules

end
