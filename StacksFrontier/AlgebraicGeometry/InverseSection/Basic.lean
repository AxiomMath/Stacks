module

public import StacksFrontier.AlgebraicGeometry.InverseSection.Pairing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 01CY: a nonvanishing section has an inverse in the inverse tensor power

Let `(X, 𝒪_X)` be a ringed space all of whose stalks are local rings, let `L` be an invertible
`𝒪_X`-module and let `s` be a global section of `L`. On the nonvanishing open

`X_s = {x ∈ X ∣ germ_x s ∉ 𝔪_x L_x}`

the section `s` is a basis of `L`, so it has an inverse: this file proves the third and last
clause of Stacks Tag 01CY, that there is a section `t` of `L ^⊗ (-1)` over `X_s` whose canonical
tensor-power pairing with `s` is `1`.

Everything is at the **ringed-space** spelling of the tagged statement, the one at
which the openness and trivialization clauses are proved in
`StacksFrontier/AlgebraicGeometry/NonvanishingTrivialize/Basic.lean`.

## Main results

* `Stacks.InverseSection.exists_tensorInv_section_pairing_eq_one`: **Stacks Tag 01CY, the
  inverse-section clause**, in the shape of the tagged statement: there is a section `t` of
  `L ^⊗ (-1)` over the nonvanishing open such that the image of `s ⊗ t` under the sheafification
  unit, the addition isomorphism in degrees `1` and `-1`, the reindexing along `1 + (-1) = 0` and
  the identification of the zeroth power with the structure sheaf is `1`.
* `Stacks.InverseSection.exists_pairingHom_eq_one`: the same statement written with
  `Stacks.InverseSection.pairingHom`, pairing against `s`, which is how it is proved.
* `Stacks.InverseSection.eq_of_pairingHom_eq` and
  `Stacks.InverseSection.injective_pairingHom`: over every open inside the nonvanishing locus,
  pairing against `s` is injective on sections. This is the half of the argument that makes the
  local inverses glue.
* `Stacks.InverseSection.exists_nhd_pairingHom_eq_one`: every point of an open inside the
  nonvanishing locus has a neighbourhood over which an inverse of `s` exists.
* `Stacks.InverseSection.exists_pairingHom_eq_one_of_le`: the same as
  `exists_pairingHom_eq_one` over an arbitrary open inside the nonvanishing locus.
* `Stacks.InverseSection.tensorPowPairingIso_hom_val_app`: the canonical pairing, on sections, is
  the three isomorphisms of its definition applied in turn. This is what converts the proof's
  formulation into that of the tagged statement.

## The route

The pairing is the degree `(1, -1)` case of the addition isomorphism of Stacks Tag 01CU, which is
built by a recursion over `ℤ` inside a `LocalizedMonoidal` structure and has no sectionwise
description. The proof therefore never computes with it; it uses only that it is an
**isomorphism**, and puts all the content into the one step that *is* elementary:

> over an open `W` inside `X_s`, the map `t ↦ s|_W ⊗ t` from the sections of `L ^⊗ (-1)` to the
> sections of the **presheaf** tensor product is bijective

(`Stacks.InverseSection.bijective_tensorLeftSection_app`), because over such a `W`
multiplication by `s` is bijective by `Stacks.NonvanishingTrivialize.bijective_smul`, and
tensoring a module isomorphism with the identity is an isomorphism.

Pairing against `s` is then the composite of that map, the sheafification unit of the presheaf
tensor product, and the canonical pairing. The sheafification unit is not bijective on sections,
only **locally** bijective, and this is where the sheaf conditions enter:

* *Injectivity over `W ≤ X_s`.* If two sections pair to the same thing then, the canonical
  pairing being an isomorphism, they have the same image under the sheafification unit; by local
  injectivity of that unit they agree locally after `t ↦ s ⊗ t`, hence locally, hence globally
  on `W` because `L ^⊗ (-1)` is a sheaf.
* *Local existence.* Transport `1` back along the canonical pairing to a section `ξ` of the
  sheafified tensor product over `X_s`. By local surjectivity of the sheafification unit, `ξ` is
  locally the image of a section of the presheaf tensor product, which by the elementary step is
  `s ⊗ t` for a unique `t`; that `t` pairs to `1` on that neighbourhood.
* *Gluing.* The local inverses agree on overlaps by injectivity, glue by the sheaf condition for
  `L ^⊗ (-1)`, and the glued section pairs to `1` because the structure sheaf is separated.

Local injectivity and local surjectivity of the sheafification unit are not proved here: the
underlying map of presheaves of abelian groups of
  `Stacks.SheafOfModules.TensorSheafification.toSheafify` **is**
`CategoryTheory.toSheafify`, definitionally, so Mathlib's instances for the latter apply. That
identification is `PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app`, and the
two instances are the ones provided by `GrothendieckTopology.WEqualsLocallyBijective`, which is
a hypothesis of every statement about tensor powers in this development.

## Implementation notes

**Transparency and elaboration depth.** `AlgebraicGeometry.SheafOfModules.tensorPow` is a
semireducible `def` sitting in the type of every morphism here, and `rw` elaborates congruence
motives at implicit transparency, so rewriting under it fails -- and when it does, the error
names whichever lemma was being rewritten rather than the real cause. Independently, unifying
two spellings of the sections of these objects costs about three times the elaborator's default
recursion budget, so a lemma that mentions a *specific* composite morphism and asks the unifier
to reconcile two spellings of its sections does not elaborate. Three devices keep everything
inside the budget, and all of them are load-bearing:

* every compatibility with restriction and every congruence is proved **once, generically** --
  `Stacks.InverseSection.res_val_app`, `hom_app_eq_of_res_eq`, `app_congr`, `hom_app_congr`,
  `Stacks.InverseSection.app_presheaf_map`, `Stacks.InverseSection.comp_app_apply` -- and then
  applied to the specific morphism as a whole;
* the unit section of the structure sheaf is given a name, `Stacks.InverseSection.unitOne`, so
  that the identification of the sections of `SheafOfModules.unit` with `X.presheaf.obj (op W)`
  is made once rather than at every use of the value `1`;
* where a chain of equalities has to meet the goal, it is fed in with `rw` at explicit arguments
  or with `refine Eq.trans _ ?_`, so that the unifier is given a syntactic pattern instead of a
  two-sided problem.

The same budget is why the two arguments of the presheaf tensor product in the statement of
`exists_tensorInv_section_pairing_eq_one` are written `Stacks.InverseSection.powPre L 1` and
`powPre L (-1)` rather than `(tensorPow 𝒪 h𝒪 L 1).val` and `(tensorPow 𝒪 h𝒪 L (-1)).val`, which
is how the tagged statement writes them. The two are definitionally equal -- `powPre` is a
`@[reducible]` abbreviation for exactly that, differing only in the spelling of the scalar
presheaf -- and the tagged statement's spelling does not elaborate there.

No compiler option is set anywhere in this directory.

**Restriction spellings.** Restriction of a section is spelled
`Stacks.NonvanishingTrivialize.res`, i.e. through the underlying presheaf of abelian groups,
because `PresheafOfModules.map` lands in a restriction-of-scalars wrapper whose carrier is the
same type but whose terms are not interchangeable with the sections in practice. For sections of
the structure sheaf read through `SheafOfModules.unit` the bridge to `X.presheaf` is
`Stacks.InverseSection.unit_res_eq`.

## What is not done

The section `t` is not shown to be unique, although the proof produces it from a bijection and
`injective_pairingHom` says exactly that it is; the uniqueness statement is simply not recorded.
Nothing is said in Mathlib's `AlgebraicGeometry.Scheme.Modules` spelling, and nothing is deduced
about the restriction of `L` to `X_s` being isomorphic to the structure sheaf as a bare statement
of triviality. The pairing in the opposite order, `t ⊗ s`, is not treated, for the reason given
in `StacksFrontier/AlgebraicGeometry/InverseSection/Reindex.lean`.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite TensorProduct
open AlgebraicGeometry Stacks.SheafOfModules.TensorSheafification
open AlgebraicGeometry.SheafOfModules (IsInvertible)

namespace Stacks.InverseSection

section Generic

open scoped Stacks.NonvanishingTrivialize

variable {X : RingedSpace.{u}}

/-- **A morphism of sheaves of modules commutes with restriction of sections.** Stated for an
arbitrary morphism on purpose: substituting a specific composite of the isomorphisms of this
development makes the unifier diverge, while the generic statement applies to each of them. -/
theorem res_val_app {M N : SheafOfModules.{u} (structureSheaf X.sheaf)} (f : M ⟶ N)
    {W W' : Opens X} (h : W' ⟶ W) (m : M.val.obj (op W)) :
    f.val.app (op W') (Stacks.NonvanishingTrivialize.res h m) =
      Stacks.NonvanishingTrivialize.res h (f.val.app (op W) m) :=
  app_presheaf_map f.val h.op m

/-- **Restriction of a section through a morphism of sheaves of modules.** If `f` sends `m` to
`c`, and `m` and `c` restrict to `n` and `c'`, then `f` sends `n` to `c'`. Generic on purpose:
with the canonical pairing substituted for `f`, the restriction compatibility and the two
restrictions cannot be reconciled with each other inside the elaborator's recursion budget,
while each of them can be reconciled with this statement. -/
theorem hom_app_eq_of_res_eq {M N : SheafOfModules.{u} (structureSheaf X.sheaf)} (f : M ⟶ N)
    {W W' : Opens X} (h : W' ⟶ W) {m : M.val.obj (op W)} {n : M.val.obj (op W')}
    {c : N.val.obj (op W)} {c' : N.val.obj (op W')} (hm : f.val.app (op W) m = c)
    (hn : Stacks.NonvanishingTrivialize.res h m = n)
    (hc : Stacks.NonvanishingTrivialize.res h c = c') :
    f.val.app (op W') n = c' :=
  hn ▸ (res_val_app f h m).trans ((congrArg (Stacks.NonvanishingTrivialize.res h) hm).trans hc)

/-- Congruence for a component of a morphism of presheaves of modules. -/
theorem app_congr {P Q : PresheafOfModules.{u} (structureRingPresheaf X.sheaf.obj)} (f : P ⟶ Q)
    (W : Opens X) {a b : P.obj (op W)} (h : a = b) : f.app (op W) a = f.app (op W) b :=
  congrArg _ h

/-- Congruence for a component of a morphism of sheaves of modules. Generic on purpose: with the
specific morphisms of this development the elaborator has to identify two spellings of the
sections, and doing it under a `congrArg` whose function mentions them is far deeper than doing
it here. -/
theorem hom_app_congr {M N : SheafOfModules.{u} (structureSheaf X.sheaf)} (f : M ⟶ N)
    (W : Opens X) {a b : M.val.obj (op W)} (h : a = b) :
    f.val.app (op W) a = f.val.app (op W) b := congrArg _ h

/-- Two sections of a sheaf of modules whose images under a morphism to the structure sheaf are
both `1` have equal images. Generic on purpose, so that the identification of the sections of
`SheafOfModules.unit` with the sections of `X.presheaf` is made with the sheaf a variable. -/
theorem hom_app_eq_of_eq_one {M : SheafOfModules.{u} (structureSheaf X.sheaf)}
    (f : M ⟶ SheafOfModules.unit (structureSheaf X.sheaf)) {W : Opens X}
    {a b : M.val.obj (op W)} (ha : f.val.app (op W) a = (1 : X.presheaf.obj (op W)))
    (hb : f.val.app (op W) b = (1 : X.presheaf.obj (op W))) :
    f.val.app (op W) a = f.val.app (op W) b := ha.trans hb.symm

/-- An isomorphism of sheaves of modules undoes its inverse on sections. -/
theorem hom_app_inv_app {M N : SheafOfModules.{u} (structureSheaf X.sheaf)} (i : M ≅ N)
    (W : Opens X) (n : N.val.obj (op W)) :
    i.hom.val.app (op W) (i.inv.val.app (op W) n) = n :=
  ((SheafOfModules.evaluation (structureSheaf X.sheaf) (op W)).mapIso i).inv_hom_id_apply n

/-- An isomorphism of sheaves of modules undoes its inverse on sections, after restriction. -/
theorem hom_app_res_inv_app {M N : SheafOfModules.{u} (structureSheaf X.sheaf)} (i : M ≅ N)
    {W W' : Opens X} (h : W' ⟶ W) (n : N.val.obj (op W)) :
    i.hom.val.app (op W') (Stacks.NonvanishingTrivialize.res h (i.inv.val.app (op W) n)) =
      Stacks.NonvanishingTrivialize.res h n :=
  hom_app_eq_of_res_eq i.hom h (hom_app_inv_app i W n) rfl rfl

/-- Restriction of a section inside the restriction-of-scalars-along-an-identity wrapper that
`Stacks.SheafOfModules.TensorSheafification.toSheafify` produces as its codomain is restriction of
  a section of the sheaf
itself. Generic on purpose: this identification is what lets the local surjectivity of the
sheafification unit be read in the spelling the rest of the proof uses. -/
theorem restrictScalarsId_presheaf_map {M : SheafOfModules.{u} (structureSheaf X.sheaf)}
    {W W' : Opens X} (h : W' ⟶ W)
    (m : ((SheafOfModules.forget (structureSheaf X.sheaf) ⋙
        PresheafOfModules.restrictScalars
          (𝟙 (structureSheaf X.sheaf).obj)).obj M).presheaf.obj (op W)) :
    ((SheafOfModules.forget (structureSheaf X.sheaf) ⋙
        PresheafOfModules.restrictScalars
          (𝟙 (structureSheaf X.sheaf).obj)).obj M).presheaf.map h.op m =
      Stacks.NonvanishingTrivialize.res h m := rfl

/-- Restriction of a section of the structure sheaf, read through `SheafOfModules.unit`, is
restriction in `X.presheaf`. -/
theorem unit_res_eq {W W' : Opens X} (h : W' ⟶ W)
    (a : (SheafOfModules.unit (structureSheaf X.sheaf)).val.obj (op W)) :
    Stacks.NonvanishingTrivialize.res
        (L := SheafOfModules.unit (structureSheaf X.sheaf)) h a =
      X.presheaf.map h.op a :=
  (PresheafOfModules.presheaf_map_apply_coe _ h.op a).trans (unit_val_map h a)

/-- The unit section of the structure sheaf restricts to the unit section. -/
theorem unit_res_one {W W' : Opens X} (h : W' ⟶ W) :
    Stacks.NonvanishingTrivialize.res
        (L := SheafOfModules.unit (structureSheaf X.sheaf)) h
        (1 : X.presheaf.obj (op W)) = (1 : X.presheaf.obj (op W')) :=
  (PresheafOfModules.presheaf_map_apply_coe _ h.op _).trans (unit_val_map_one h)

/-- **The unit section of the structure sheaf, read as a section of `SheafOfModules.unit`.**
Identifying the sections of `SheafOfModules.unit (structureSheaf X.sheaf)` with
`X.presheaf.obj (op W)` is expensive for the elaborator -- about three times the default
recursion budget when it has to be done inside a unification -- so it is done here, once, and
every statement about the value of a pairing is phrased with `unitOne`. -/
noncomputable def unitOne (W : Opens X) :
    (SheafOfModules.unit (structureSheaf X.sheaf)).val.obj (op W) :=
  (1 : X.presheaf.obj (op W))

/-- `unitOne` is `1`. -/
theorem unitOne_eq_one (W : Opens X) :
    (unitOne W : X.presheaf.obj (op W)) = (1 : X.presheaf.obj (op W)) := rfl

/-- The unit section restricts to the unit section. -/
theorem unitOne_res {W W' : Opens X} (h : W' ⟶ W) :
    Stacks.NonvanishingTrivialize.res
      (L := SheafOfModules.unit (structureSheaf X.sheaf)) h (unitOne W) = unitOne W' :=
  unit_res_one h

/-- A compatible family of sections of a sheaf of modules on a ringed space glues. This is
`TopCat.Sheaf.existsUnique_gluing'` at the spelling of this development; it is the module
analogue of `Stacks.NonvanishingTrivialize.exists_res_eq_ring`, which the sibling file provides
for the structure sheaf only. -/
theorem exists_res_eq {M : SheafOfModules.{u} (structureSheaf X.sheaf)} {ι : Type u}
    (C : ι → Opens X) (W : Opens X) (iCW : ∀ i, C i ⟶ W) (hcover : W ≤ iSup C)
    (m : ∀ i, M.val.presheaf.obj (op (C i)))
    (hcompat : ∀ i j, M.val.presheaf.map (homOfLE (inf_le_left : C i ⊓ C j ≤ C i)).op (m i) =
      M.val.presheaf.map (homOfLE (inf_le_right : C i ⊓ C j ≤ C j)).op (m j)) :
    ∃ A : M.val.obj (op W), ∀ i, Stacks.NonvanishingTrivialize.res (iCW i) A = m i := by
  obtain ⟨A, hA, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨M.val.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab.{u} _) C W iCW hcover m hcompat
  exact ⟨A, hA⟩

end Generic

section Locality

variable {X : RingedSpace.{u}}

/-- **The sheafification unit of presheaves of modules is locally surjective.** Its underlying
map of presheaves of abelian groups is `CategoryTheory.toSheafify` on the nose, by
`PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app`, so this is Mathlib's
instance for the latter. -/
instance isLocallySurjective_toSheafify
    (P : PresheafOfModules.{u} (structureRingPresheaf X.sheaf.obj)) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map
        (toSheafify X.sheaf.obj (structureSheaf X.sheaf).property P)) := by
  change Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf)
  infer_instance

/-- **The sheafification unit of presheaves of modules is locally injective**, by the same
identification as `isLocallySurjective_toSheafify`. -/
instance isLocallyInjective_toSheafify
    (P : PresheafOfModules.{u} (structureRingPresheaf X.sheaf.obj)) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map
        (toSheafify X.sheaf.obj (structureSheaf X.sheaf).property P)) := by
  change Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf)
  infer_instance

/-- Local surjectivity, read as a statement about open neighbourhoods: a section of the target
over `W` is, near every point of `W`, the image of a section of the source. This is
`Presheaf.imageSieve_mem` together with the description of the covering sieves of the Grothendieck
topology of a topological space. -/
theorem exists_nhd_app_eq {P Q : PresheafOfModules.{u} (structureRingPresheaf X.sheaf.obj)}
    (f : P ⟶ Q) [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map f)]
    {W : Opens X} (y : Q.presheaf.obj (op W)) {x : X} (hx : x ∈ W) :
    ∃ (V : Opens X) (i : V ⟶ W), x ∈ V ∧ ∃ z : P.presheaf.obj (op V),
      f.app (op V) z = Q.presheaf.map i.op y := by
  obtain ⟨V, i, ⟨z, hz⟩, hxV⟩ :=
    Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map f) y x hx
  exact ⟨V, i, hxV, z, hz⟩

/-- Local injectivity, read as a statement about open neighbourhoods: two sections with the same
image agree, near every point, after restriction. -/
theorem exists_nhd_map_eq {P Q : PresheafOfModules.{u} (structureRingPresheaf X.sheaf.obj)}
    (f : P ⟶ Q) [Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map f)]
    {W : Opens X} (z z' : P.presheaf.obj (op W)) (h : f.app (op W) z = f.app (op W) z')
    {x : X} (hx : x ∈ W) :
    ∃ (V : Opens X) (i : V ⟶ W), x ∈ V ∧ P.presheaf.map i.op z = P.presheaf.map i.op z' := by
  obtain ⟨V, i, hi, hxV⟩ :=
    Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map f) z z' h x hx
  exact ⟨V, i, hxV, hi⟩

end Locality

section Main

open scoped Stacks.InverseSection Stacks.NonvanishingTrivialize
open AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u}} (L : SheafOfModules.{u} (structureSheaf X.sheaf))
  [IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property L]

/-- The `(-1)`-st tensor power of `L`, abbreviated. Unlike
`Stacks.InverseSection.powPre` this is spelled at the type `tensorPow` itself has, so that
mentioning its sections in a statement costs the elaborator nothing; `powPre` carries a change of
spelling of the scalar presheaf, which is cheap once but not cheap inside a unification. -/
@[reducible] noncomputable def invPow : SheafOfModules.{u} (structureSheaf X.sheaf) :=
  tensorPow X.sheaf.obj (structureSheaf X.sheaf).property L (-1)

/-- **The canonical pairing, on sections, is its three factors applied in turn**: the addition
isomorphism in degrees `1` and `-1`, the reindexing along `1 + (-1) = 0`, and the identification
of the zeroth tensor power with the structure sheaf. This is the bridge between the formulation
`Stacks.InverseSection.pairingHom` that the proof uses and the formulation of the tagged
statement. -/
theorem tensorPowPairingIso_hom_val_app (h : (1 : ℤ) + -1 = 0) (W : Opens X)
    (z : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj)
          (forget₂ CommRingCat RingCat) ((structureSheaf X.sheaf).property)⟩).obj
        ((tensorPow X.sheaf.obj (structureSheaf X.sheaf).property L 1))).obj
        ((tensorPow X.sheaf.obj (structureSheaf X.sheaf).property L (-1))))).val.obj (op W)) :
    (tensorPowPairingIso X.sheaf.obj (structureSheaf X.sheaf).property L).hom.val.app (op W) z =
      (tensorPowZeroIso X.sheaf.obj (structureSheaf X.sheaf).property L).hom.val.app (op W)
        ((tensorPowReindexIso X.sheaf.obj (structureSheaf X.sheaf).property L h).hom.val.app
          (op W)
          ((tensorPowAddIsoSheaf X.sheaf.obj (structureSheaf X.sheaf).property L
            1 (-1)).hom.val.app (op W) z)) := by
  have e : (tensorPowPairingIso X.sheaf.obj (structureSheaf X.sheaf).property L).hom.val =
      (tensorPowAddIsoSheaf X.sheaf.obj (structureSheaf X.sheaf).property L 1 (-1)).hom.val ≫
        ((tensorPowReindexIso X.sheaf.obj (structureSheaf X.sheaf).property L h).hom.val ≫
          (tensorPowZeroIso X.sheaf.obj (structureSheaf X.sheaf).property L).hom.val) := rfl
  rw [e]
  refine (comp_app_apply
    (tensorPowAddIsoSheaf X.sheaf.obj (structureSheaf X.sheaf).property L 1 (-1)).hom.val
    ((tensorPowReindexIso X.sheaf.obj (structureSheaf X.sheaf).property L h).hom.val ≫
      (tensorPowZeroIso X.sheaf.obj (structureSheaf X.sheaf).property L).hom.val)
    (op W) z).trans ?_
  exact comp_app_apply
    (tensorPowReindexIso X.sheaf.obj (structureSheaf X.sheaf).property L h).hom.val
    (tensorPowZeroIso X.sheaf.obj (structureSheaf X.sheaf).property L).hom.val (op W) _

/-- **Local surjectivity of the sheafification unit of the presheaf tensor product**, with the
restriction on the right-hand side spelled through the sheafified tensor product, which is the
spelling the rest of the proof uses. -/
theorem exists_nhd_toSheafify_tensor_eq {W : Opens X}
    (xi : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj)
          (forget₂ CommRingCat RingCat) ((structureSheaf X.sheaf).property)⟩).obj
        ((tensorPow X.sheaf.obj (structureSheaf X.sheaf).property L 1))).obj
        ((tensorPow X.sheaf.obj (structureSheaf X.sheaf).property L (-1))))).val.obj (op W))
    {x : X} (hx : x ∈ W) :
    ∃ (V : Opens X) (i : V ⟶ W), x ∈ V ∧
      ∃ z : ((PresheafOfModules.tensorObj (O := X.sheaf.obj) ((powPre L 1))
          ((powPre L (-1))))).presheaf.obj (op V),
        Stacks.NonvanishingTrivialize.res
            (L := (((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj)
                  (forget₂ CommRingCat RingCat) ((structureSheaf X.sheaf).property)⟩).obj
                ((tensorPow X.sheaf.obj (structureSheaf X.sheaf).property L 1))).obj
                ((tensorPow X.sheaf.obj (structureSheaf X.sheaf).property L (-1))))) i xi =
          (toSheafify X.sheaf.obj (structureSheaf X.sheaf).property
            ((PresheafOfModules.tensorObj (O := X.sheaf.obj) ((powPre L 1))
              ((powPre L (-1)))))).app (op V) z := by
  obtain ⟨V, i, hxV, z, hz⟩ := exists_nhd_app_eq
    (toSheafify X.sheaf.obj (structureSheaf X.sheaf).property
      ((PresheafOfModules.tensorObj (O := X.sheaf.obj) ((powPre L 1)) ((powPre L (-1)))))) xi hx
  exact ⟨V, i, hxV, z, (hz.trans (restrictScalarsId_presheaf_map
    (M := (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj)
          (forget₂ CommRingCat RingCat) ((structureSheaf X.sheaf).property)⟩).obj
        ((tensorPow X.sheaf.obj (structureSheaf X.sheaf).property L 1))).obj
        ((tensorPow X.sheaf.obj (structureSheaf X.sheaf).property L (-1))))) i xi)).symm⟩

/-- A section pairing to `1` restricts to a section pairing to `1`. -/
theorem pairingHom_res_eq_one (s : L.sections) {W W' : Opens X} (h : W' ⟶ W)
    {t : (invPow L).val.obj (op W)}
    (ht : (pairingHom L s).val.app (op W) t = unitOne W) :
    (pairingHom L s).val.app (op W') (Stacks.NonvanishingTrivialize.res h t) = unitOne W' :=
  hom_app_eq_of_res_eq (pairingHom L s) h ht rfl (unitOne_res h)

variable [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

/-- **Over every open inside the nonvanishing locus of `s`, pairing against `s` is injective on
sections.** The canonical pairing is an isomorphism, so two sections pairing to the same value
have the same image under the sheafification unit; local injectivity of that unit then makes
their images under `t ↦ s ⊗ t` agree locally, the elementary bijectivity makes the sections
themselves agree locally, and `L ^⊗ (-1)` being a sheaf makes them agree. -/
theorem eq_of_pairingHom_eq (s : L.sections) {W : Opens X}
    (hW : W ≤ Stacks.NonvanishingTrivialize.nonvanishingOpen X L s)
    {t t' : (invPow L).val.obj (op W)}
    (hEq : (pairingHom L s).val.app (op W) t = (pairingHom L s).val.app (op W) t') :
    t = t' := by
  have h1 : (tensorLeftSectionSheaf L s).val.app (op W) t =
      (tensorLeftSectionSheaf L s).val.app (op W) t' :=
    (bijective_hom_app
      (tensorPowPairingIso X.sheaf.obj (structureSheaf X.sheaf).property L) W).injective
      ((pairingHom_val_app' L s W t).symm.trans
        (hEq.trans (pairingHom_val_app' L s W t')))
  have h2 : (toSheafify X.sheaf.obj (structureSheaf X.sheaf).property
        ((PresheafOfModules.tensorObj (O := X.sheaf.obj) ((powPre L 1))
          ((powPre L (-1)))))).app (op W)
          ((tensorLeftSection L s).app (op W) t) =
      (toSheafify X.sheaf.obj (structureSheaf X.sheaf).property
        ((PresheafOfModules.tensorObj (O := X.sheaf.obj) ((powPre L 1))
          ((powPre L (-1)))))).app (op W)
          ((tensorLeftSection L s).app (op W) t') :=
    (tensorLeftSectionSheaf_val_app' L s W t).symm.trans
      (h1.trans (tensorLeftSectionSheaf_val_app' L s W t'))
  choose V iV hxV hV using fun x : W =>
    exists_nhd_map_eq (toSheafify X.sheaf.obj (structureSheaf X.sheaf).property
      ((PresheafOfModules.tensorObj (O := X.sheaf.obj) ((powPre L 1)) ((powPre L (-1))))))
      ((tensorLeftSection L s).app (op W) t) ((tensorLeftSection L s).app (op W) t') h2 x.2
  refine Stacks.NonvanishingTrivialize.eq_of_res_eq V W iV
    (fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩) t t' fun y => ?_
  exact (bijective_tensorLeftSection_app L s ((leOfHom (iV y)).trans hW)).injective
    ((app_presheaf_map (tensorLeftSection L s) (iV y).op t).trans
      ((hV y).trans (app_presheaf_map (tensorLeftSection L s) (iV y).op t').symm))

/-- **Over every open inside the nonvanishing locus of `s`, pairing against `s` is injective on
sections**, as a `Function.Injective` statement. -/
theorem injective_pairingHom (s : L.sections) {W : Opens X}
    (hW : W ≤ Stacks.NonvanishingTrivialize.nonvanishingOpen X L s) :
    Function.Injective fun t : (invPow L).val.obj (op W) =>
      (pairingHom L s).val.app (op W) t :=
  fun _ _ h => eq_of_pairingHom_eq L s hW h

/-- The inductive step of `exists_nhd_pairingHom_eq_one`, with the section of the sheafified
tensor product that `1` pulls back to taken as a variable. Keeping it a variable matters: with
the pullback written out, identifying the two spellings of the sections of the sheafified tensor
product is deep enough to exhaust the elaborator's recursion budget. -/
theorem exists_nhd_pairingHom_eq_one_aux (s : L.sections) {W : Opens X}
    (hW : W ≤ Stacks.NonvanishingTrivialize.nonvanishingOpen X L s)
    (xi : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj)
          (forget₂ CommRingCat RingCat) ((structureSheaf X.sheaf).property)⟩).obj
        ((tensorPow X.sheaf.obj (structureSheaf X.sheaf).property L 1))).obj
        ((tensorPow X.sheaf.obj (structureSheaf X.sheaf).property L (-1))))).val.obj (op W))
    (hxi : (tensorPowPairingIso X.sheaf.obj (structureSheaf X.sheaf).property L).hom.val.app
      (op W) xi = unitOne W)
    {x : X} (hx : x ∈ W) :
    ∃ V : Opens X, V ≤ W ∧ x ∈ V ∧
      ∃ t : (invPow L).val.obj (op V), (pairingHom L s).val.app (op V) t = unitOne V := by
  obtain ⟨V, i, hxV, y, hy⟩ := exists_nhd_toSheafify_tensor_eq L xi hx
  obtain ⟨t, ht⟩ := (bijective_tensorLeftSection_app L s ((leOfHom i).trans hW)).2 y
  have ht' : (tensorLeftSection L s).app (op V) t = y := ht
  refine ⟨V, leOfHom i, hxV, t, ?_⟩
  refine (pairingHom_val_app' L s V t).trans ?_
  refine (hom_app_congr (tensorPowPairingIso X.sheaf.obj
    (structureSheaf X.sheaf).property L).hom V
      (tensorLeftSectionSheaf_val_app' L s V t)).trans ?_
  refine (hom_app_congr (tensorPowPairingIso X.sheaf.obj
    (structureSheaf X.sheaf).property L).hom V
      (app_congr (toSheafify X.sheaf.obj (structureSheaf X.sheaf).property
        ((PresheafOfModules.tensorObj (O := X.sheaf.obj) ((powPre L 1))
          ((powPre L (-1)))))) V ht')).trans ?_
  exact hom_app_eq_of_res_eq (tensorPowPairingIso X.sheaf.obj
    (structureSheaf X.sheaf).property L).hom i hxi hy (unitOne_res i)

/-- **Every point of an open inside the nonvanishing locus has a neighbourhood on which `s` has
an inverse.** Transport `1` back along the canonical pairing; by local surjectivity of the
sheafification unit it is locally the image of a section of the presheaf tensor product, which
by `bijective_tensorLeftSection_app` is `s ⊗ t`. -/
theorem exists_nhd_pairingHom_eq_one (s : L.sections) {W : Opens X}
    (hW : W ≤ Stacks.NonvanishingTrivialize.nonvanishingOpen X L s) {x : X} (hx : x ∈ W) :
    ∃ V : Opens X, V ≤ W ∧ x ∈ V ∧
      ∃ t : (invPow L).val.obj (op V), (pairingHom L s).val.app (op V) t = unitOne V :=
  exists_nhd_pairingHom_eq_one_aux L s hW _
    (hom_app_inv_app (tensorPowPairingIso X.sheaf.obj (structureSheaf X.sheaf).property L) W
      (unitOne W)) hx

/-- **Stacks Tag 01CY, the inverse-section clause, over an arbitrary open inside the nonvanishing
locus**: there is a section of `L ^⊗ (-1)` there that pairs with `s` to `1`. The local inverses
of `exists_nhd_pairingHom_eq_one` agree on overlaps by `eq_of_pairingHom_eq`, glue by the sheaf
condition for `L ^⊗ (-1)`, and the glued section pairs to `1` because the structure sheaf is
separated. -/
theorem exists_pairingHom_eq_one_of_le (s : L.sections) {W : Opens X}
    (hW : W ≤ Stacks.NonvanishingTrivialize.nonvanishingOpen X L s) :
    ∃ t : (invPow L).val.obj (op W),
      (pairingHom L s).val.app (op W) t = unitOne W := by
  choose V hVle hxV t ht using fun x : W => exists_nhd_pairingHom_eq_one L s hW x.2
  have hcover : W ≤ iSup V := fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩
  have hcompat : ∀ x y, Stacks.NonvanishingTrivialize.res
        (homOfLE (inf_le_left : V x ⊓ V y ≤ V x)) (t x) =
      Stacks.NonvanishingTrivialize.res
        (homOfLE (inf_le_right : V x ⊓ V y ≤ V y)) (t y) := by
    intro x y
    refine eq_of_pairingHom_eq L s (W := V x ⊓ V y)
      (((inf_le_left : V x ⊓ V y ≤ V x).trans (hVle x)).trans hW) ?_
    rw [pairingHom_res_eq_one L s (homOfLE (inf_le_left : V x ⊓ V y ≤ V x)) (ht x),
      pairingHom_res_eq_one L s (homOfLE (inf_le_right : V x ⊓ V y ≤ V y)) (ht y)]
  obtain ⟨A, hA⟩ := exists_res_eq
    (M := invPow L) V W
    (fun x => homOfLE (hVle x)) hcover t hcompat
  refine ⟨A, ?_⟩
  refine Stacks.NonvanishingTrivialize.eq_of_res_eq
    (L := SheafOfModules.unit (structureSheaf X.sheaf)) V W
    (fun x => homOfLE (hVle x)) hcover _ (unitOne W) fun y => ?_
  rw [unitOne_res]
  refine Eq.trans (res_val_app (pairingHom L s) (homOfLE (hVle y)) A).symm ?_
  rw [hA y]
  exact ht y

/-- **Stacks Tag 01CY, the inverse-section clause**, in the formulation the proof uses: there is
a section of `L ^⊗ (-1)` over the nonvanishing open of `s` that pairs with `s` to `1`. -/
theorem exists_pairingHom_eq_one (s : L.sections) :
    ∃ t : (invPow L).val.obj
        (op (Stacks.NonvanishingTrivialize.nonvanishingOpen X L s)),
      (pairingHom L s).val.app
          (op (Stacks.NonvanishingTrivialize.nonvanishingOpen X L s)) t =
        unitOne (Stacks.NonvanishingTrivialize.nonvanishingOpen X L s) :=
  exists_pairingHom_eq_one_of_le L s le_rfl

/-- **Stacks Tag 01CY, the inverse-section clause**, in the shape of the tagged statement: on the
nonvanishing open of a global section `s` of an invertible module, there is a section `t` of the
`(-1)`-st tensor power whose canonical tensor-power pairing with `s` evaluates to `1`.

The pairing is the one the tagged statement names: form the elementary tensor of `s`, read in the first
tensor power, with `t`; push it into the sheafified tensor product; apply the addition
isomorphism of Stacks Tag 01CU in degrees `1` and `-1`; reindex along `1 + (-1) = 0`. The tagged
statement then compares the result with `1` directly, its zeroth tensor power being the unit of
`SheafOfModules` on the nose; here the zeroth tensor power is the *sheafified* unit, so
`AlgebraicGeometry.SheafOfModules.tensorPowZeroIso` is inserted, and only then is the comparison
with `1 : 𝒪_X(X_s)` a statement. -/
@[stacks 01CY "inverse section", ega "0 5.5.2" "(b) => (c)"]
theorem exists_tensorInv_section_pairing_eq_one (s : L.sections) :
    ∃ t : (tensorPow X.sheaf.obj (structureSheaf X.sheaf).property L (-1)).val.obj
        (op (Stacks.NonvanishingTrivialize.nonvanishingOpen X L s)),
      (tensorPowZeroIso X.sheaf.obj (structureSheaf X.sheaf).property L).hom.val.app
        (op (Stacks.NonvanishingTrivialize.nonvanishingOpen X L s))
        ((tensorPowReindexIso X.sheaf.obj (structureSheaf X.sheaf).property L
            (show (1 : ℤ) + -1 = 0 by omega)).hom.val.app
          (op (Stacks.NonvanishingTrivialize.nonvanishingOpen X L s))
          ((tensorPowAddIsoSheaf X.sheaf.obj (structureSheaf X.sheaf).property L
              1 (-1)).hom.val.app
            (op (Stacks.NonvanishingTrivialize.nonvanishingOpen X L s))
            ((toSheafify X.sheaf.obj (structureSheaf X.sheaf).property
                ((PresheafOfModules.tensorObj (O := X.sheaf.obj) ((powPre L 1))
                  ((powPre L (-1)))))).app
              (op (Stacks.NonvanishingTrivialize.nonvanishingOpen X L s))
              ((tensorPowOneIso X.sheaf.obj (structureSheaf X.sheaf).property L).inv.val.app
                  (op (Stacks.NonvanishingTrivialize.nonvanishingOpen X L s))
                  (s.eval (op (Stacks.NonvanishingTrivialize.nonvanishingOpen X L s)))
                ⊗ₜ[X.presheaf.obj
                    (op (Stacks.NonvanishingTrivialize.nonvanishingOpen X L s))] t)))) =
      (1 : X.presheaf.obj
        (op (Stacks.NonvanishingTrivialize.nonvanishingOpen X L s))) := by
  obtain ⟨t, ht⟩ := exists_pairingHom_eq_one L s
  refine ⟨t, ?_⟩
  have e1 := congrArg (fun w : (tensorPow X.sheaf.obj (structureSheaf X.sheaf).property L 1).val.obj
      (op (Stacks.NonvanishingTrivialize.nonvanishingOpen X L s)) =>
    (tensorPowZeroIso X.sheaf.obj (structureSheaf X.sheaf).property L).hom.val.app
      (op (Stacks.NonvanishingTrivialize.nonvanishingOpen X L s))
      ((tensorPowReindexIso X.sheaf.obj (structureSheaf X.sheaf).property L
          (show (1 : ℤ) + -1 = 0 by omega)).hom.val.app
        (op (Stacks.NonvanishingTrivialize.nonvanishingOpen X L s))
        ((tensorPowAddIsoSheaf X.sheaf.obj (structureSheaf X.sheaf).property L
            1 (-1)).hom.val.app
          (op (Stacks.NonvanishingTrivialize.nonvanishingOpen X L s))
          ((toSheafify X.sheaf.obj (structureSheaf X.sheaf).property
              ((PresheafOfModules.tensorObj (O := X.sheaf.obj) ((powPre L 1))
                ((powPre L (-1)))))).app
            (op (Stacks.NonvanishingTrivialize.nonvanishingOpen X L s))
            (w ⊗ₜ[X.presheaf.obj
              (op (Stacks.NonvanishingTrivialize.nonvanishingOpen X L s))] t)))))
    (sectionHom_one L s (Stacks.NonvanishingTrivialize.nonvanishingOpen X L s))
  exact e1.symm.trans ((tensorPowPairingIso_hom_val_app L
    (show (1 : ℤ) + -1 = 0 by omega) _ _).symm.trans
      ((pairingHom_val_app L s _ t).symm.trans
        (ht.trans (unitOne_eq_one
          (Stacks.NonvanishingTrivialize.nonvanishingOpen X L s)))))

end Main

end Stacks.InverseSection

end
