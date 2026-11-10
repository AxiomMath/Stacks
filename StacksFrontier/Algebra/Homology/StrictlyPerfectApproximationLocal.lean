module

public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestrictionOfLE
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Local strictly perfect approximations concentrated in degrees at most `r`

Let `(X, O_X)` be a ringed space and let `K` be an `m`-pseudo-coherent object of `D(O_X)` whose
cohomology sheaves vanish in degrees `> r`, with `m ≤ r`. This file proves that `K` is
represented by a complex `C` such that every point of `X` has an open neighbourhood on which
`C` receives a map from a strictly perfect complex *with no terms above degree `r`* which is an
isomorphism on cohomology in degrees `> m` and an epimorphism in degree `m`.

This is the local shrinking step that the Stacks proof of Tag 08DN performs inline — "the map
`E^{n-1} ⟶ E^n` is surjective as `H^n(E) = 0`; by Lemma 08C6 we can locally find a section of
this surjection and write `E^{n-1} = E' ⊕ E^n`" — stated once and for all, and run as a
downward induction over the finitely many degrees between `r` and the top nonzero degree.

`StacksFrontier/Algebra/Homology/StrictlyPerfectApproximation.lean` carries the purely homological
half (truncate at `r`, given that the degree-`r` cycles are a direct summand of a finite free
module) and records the local half as deliberately absent: the shrinking "needs the restriction
functors for module sheaves on open subspaces and is deliberately kept out". Those functors are
`StacksFrontier/Algebra/Homology/StrictlyPerfectRestrictionOfLE.lean`; this file is the shrinking.

## Main definitions

* `Stacks.SheafOfModules.restrictSheafOfModulesOfLEUnitIso`: restriction of sheaves of modules
  along `V ≤ U` takes the unit object to the unit object.
* `Stacks.SheafOfModules.functorCompIsoOfLETrans`,
  `Stacks.SheafOfModules.restrictSheafOfModulesOfLETrans`: restricting along `V ≤ U` and then
  along `W ≤ V` is restricting along `W ≤ U`.
* `StrictlyPerfect.mapFiniteFreeIso`: an exact functor of `O_X`-module categories which
  preserves the structure sheaf takes `O_X^{⊕n}` to `O_Y^{⊕n}`.
* `StrictlyPerfect.mapCyclesIso`, `StrictlyPerfect.restrictCyclesOfLEIso`: an exact functor
  commutes with the cycles of a complex.
* `StrictlyPerfect.IsPseudoCoherentComplexFrom`, `StrictlyPerfect.IsPseudoCoherentFrom`:
  Stacks 08CB parts (1) and (3), `m`-pseudo-coherence of a complex and of a derived object on a
  ringed space.

## Main results

* `Stacks.SheafOfModules.isIso_unitToPushforwardObjUnit`: the pushforward of sheaves of modules
  along an *invertible* comparison of sheaves of rings preserves the unit object.
* `Stacks.SheafOfModules.exists_lift_of_retract_pushforward`: the purely categorical half of
  Stacks 08C6 — a morphism out of a retract of a finite biproduct of copies of the unit lifts
  through such a pushforward as soon as the finitely many sections it is assembled from do.
* `Stacks.SheafOfModules.exists_le_restrict_lift_of_retract` and
  `StrictlyPerfect.exists_le_local_lift_of_isDirectSummandOfFiniteFree`: **Stacks 08C6 along an
  inclusion of opens** — the conclusion lives on an open of the ambient space, so a second
  shrinking step composes with the first instead of descending into a subspace of a subspace.
* `StrictlyPerfect.isDirectSummandOfFiniteFree_map`, `StrictlyPerfect.isStrictlyPerfect_map`,
  and their specializations `..._restrictModulesOfLE`, `..._restrictComplexOfLE`,
  `..._restrictComplex`: restriction preserves "direct summand of a finite free module" and
  strict perfection.
* `StrictlyPerfect.epi_homologyMap_map`: an exact functor preserves the property of being an
  epimorphism on a cohomology sheaf (the `IsIso` half is
  `StrictlyPerfect.isIso_homologyMap_restrictComplexOfLE`, already available).
* `StrictlyPerfect.exists_le_isDirectSummandOfFiniteFree_cycles`: **the shrinking induction** —
  the degree-`r` cycles of a strictly perfect complex with no cohomology above `r` become a
  direct summand of a finite free module after shrinking the open.
* `StrictlyPerfect.exists_local_isStrictlyPerfect_approximation_boundedAbove`: the statement
  described above.

## Implementation notes

**Universes are the ring universe `u`, the carrier universe `v`, and the derived-category
universe `d`, with `u` and `v` independent.** The module universe is kept equal to the ring
universe throughout. `StrictlyPerfect.IsDirectSummandOfFiniteFree` is now stated at an
arbitrary module universe (it lifts its argument along `StrictlyPerfect.moduleULift` and asks
for a retract of the lifted `StrictlyPerfect.finiteFree` in the common universe), but nothing
in this file profits from that: `StrictlyPerfect.isDirectSummandOfFiniteFree_iff_retract` —
the only way to recover retract *data* from the predicate, and what several proofs below need
— holds exactly when the module universe is the ring universe. So every `OXMod` below is
spelled `OXMod.{u, u, v}` in full. Note two spelling pitfalls: `RingedSpace.{u, v}` is ring
universe *first* and carrier universe second, the reverse of how the abbreviation reads; and
`OXMod.{u, w, v}` takes the ring universe first, then the module universe and the
carrier universe.

**The sheafification instances are hypotheses, not instance-search results.** `SheafOfModules`
over the structure sheaf of rings is abelian once
`HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u}` and
`WEqualsLocallyBijective` hold, and Mathlib supplies those only after the ring, carrier and
module universes have collapsed. Assuming them keeps `u` and `v` independent. This is why the
section `StrictlyPerfect.Truncation` restates four lemmas of
`StacksFrontier/Algebra/Homology/StrictlyPerfectApproximation.lean`: there the homology instances
were discharged by search, so `isStrictlyPerfect_truncLE` and
`exists_isStrictlyPerfect_boundedAbove_of_approximation` have **empty** `levelParams` and
`isZero_truncLE_X`, `epi_toCycles_of_isZero_homology`, `retractCyclesOfSection` and
`isLE_of_isIso_homologyMap` a single one, none of them applicable at `RingedSpace.{u, v}`. The
proofs are the ones in that file; only the statements change, and they strictly generalize it.

**Why Stacks 08C6 had to be reproved along an inclusion of opens.** The library's
`StrictlyPerfect.exists_local_lift_of_isDirectSummandOfFiniteFree` produces an open `W` of the
*subspace* `U` and a lift over `restrictModules (X|_U) W`, which lands in modules on
`(X|_U)|_W`. A downward induction applies it once per degree, and `(X|_U)|_W` is not `X|_V` for
any open `V` of `X` — only homeomorphic to it. The version proved here produces an open `V ≤ U`
of `X` itself and a lift over `restrictModulesOfLE`, so the steps compose through
`restrictSheafOfModulesOfLETrans` and no transport through a homeomorphism of subspaces occurs.
The invertibility of the ring-sheaf comparison `restrictSheafOfRingsHomOfLE` is what makes this
possible: it is needed exactly once, to turn a section into a morphism out of
`(restrictModulesOfLE h).obj O_{X|U}`, via Mathlib's `SheafOfModules.unitToPushforwardObjUnit`
and `SheafOfModules.pushforwardSections_unitHomEquiv`.

**Two spellings of one complex, and where they must not meet.** `restrictComplexOfLE h P` and
`((restrictModulesOfLE h).mapHomologicalComplex (ComplexShape.up ℤ)).obj P` are definitionally
equal and not syntactically equal, and likewise `(restrictComplexOfLE h P).X i` and
`(restrictModulesOfLE h).obj (P.X i)`. A composite that mixes them *elaborates*, because defeq
is checked, and is then not type-correct at `implicit` transparency, after which `rw` refuses
with a message naming a pattern. Mixing at the outermost type of an equation is harmless;
mixing at an intermediate object of a composition is not. Hence `restrictCyclesOfLEIso` and
`toCycles_comp_restrictCyclesOfLEIso_hom`, which repackage the generic `mapCyclesIso` in the
`restrictComplexOfLE` spelling, and hence the two places below where a morphism is re-ascribed
through `obtain ⟨_, _⟩ : ∃ _, _` or `Nonempty` before being composed. No `erw` and no
`set_option` is used.

## References

* [Stacks Project, Tag 08C6](https://stacks.math.columbia.edu/tag/08C6)
* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 08DN](https://stacks.math.columbia.edu/tag/08DN)
* [Stacks Project, Cohomology, Section 46](https://stacks.math.columbia.edu/tag/08C3)
* [Stacks Project, Cohomology, Section 47](https://stacks.math.columbia.edu/tag/08CA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology Opposite

universe u v d w r t v₁ v₂ u₁ u₂

namespace Stacks.SheafOfModules

/-! ### The unit object under a pushforward along an invertible map of sheaves of rings -/

section Unit

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {Fun : C ⥤ D}
  {S : Sheaf J RingCat.{r}} {Rg : Sheaf K RingCat.{r}} [Functor.IsContinuous Fun J K]

/-- If `φ` is an isomorphism of sheaves of rings, then the canonical morphism
`unit S ⟶ (pushforward φ).obj (unit Rg)` is an isomorphism: on underlying presheaves of
abelian groups it is `φ` itself. -/
theorem isIso_unitToPushforwardObjUnit
    (φ : S ⟶ (Fun.sheafPushforwardContinuous RingCat.{r} J K).obj Rg) [IsIso φ] :
    IsIso (_root_.SheafOfModules.unitToPushforwardObjUnit φ) := by
  rw [← isIso_iff_of_reflects_iso _ (_root_.SheafOfModules.forget.{r} S ⋙
    PresheafOfModules.toPresheaf S.obj), NatTrans.isIso_iff_isIso_app]
  intro X
  have h0 : IsIso ((sheafToPresheaf J RingCat.{r}).map φ) := inferInstance
  have h1 : IsIso (φ.hom.app X) := NatIso.isIso_app_of_isIso φ.hom X
  rw [← isIso_iff_of_reflects_iso _ (forget AddCommGrpCat.{r}), isIso_iff_bijective]
  have h2 : (forget AddCommGrpCat.{r}).map (((_root_.SheafOfModules.forget.{r} S ⋙
      PresheafOfModules.toPresheaf S.obj).map
      (_root_.SheafOfModules.unitToPushforwardObjUnit φ)).app X) =
      (forget RingCat.{r}).map (φ.hom.app X) := by
    ext x
    exact _root_.SheafOfModules.unitToPushforwardObjUnit_val_app_apply φ x
  rw [h2]
  exact ConcreteCategory.bijective_of_isIso (φ.hom.app X)

/-- The pushforward of sheaves of modules along `φ` is an additive functor. -/
instance additive_pushforward
    (φ : S ⟶ (Fun.sheafPushforwardContinuous RingCat.{r} J K).obj Rg) :
    (_root_.SheafOfModules.pushforward.{w} φ).Additive where
  map_add := by intros; ext; rfl

/-- A morphism out of the unit object lifts through `pushforward φ` as soon as the
corresponding section does. -/
theorem exists_lift_unit_of_pushforwardSections
    (φ : S ⟶ (Fun.sheafPushforwardContinuous RingCat.{r} J K).obj Rg) [IsIso φ]
    {F G : _root_.SheafOfModules.{r} Rg} (p : G ⟶ F)
    (σ : _root_.SheafOfModules.unit Rg ⟶ F)
    (s : ((_root_.SheafOfModules.pushforward.{r} φ).obj G).sections)
    (hs : _root_.SheafOfModules.sectionsMap
          ((_root_.SheafOfModules.pushforward.{r} φ).map p) s =
        _root_.SheafOfModules.pushforwardSections φ (F.unitHomEquiv σ)) :
    ∃ τ : (_root_.SheafOfModules.pushforward.{r} φ).obj (_root_.SheafOfModules.unit Rg) ⟶
        (_root_.SheafOfModules.pushforward.{r} φ).obj G,
      τ ≫ (_root_.SheafOfModules.pushforward.{r} φ).map p =
        (_root_.SheafOfModules.pushforward.{r} φ).map σ := by
  have := isIso_unitToPushforwardObjUnit φ
  refine ⟨inv (_root_.SheafOfModules.unitToPushforwardObjUnit φ) ≫
    ((_root_.SheafOfModules.pushforward.{r} φ).obj G).unitHomEquiv.symm s, ?_⟩
  rw [Category.assoc, _root_.SheafOfModules.unitHomEquiv_symm_comp, hs,
    _root_.SheafOfModules.pushforwardSections_unitHomEquiv, Equiv.symm_apply_apply,
    IsIso.inv_hom_id_assoc]

/-- A morphism out of a retract of a finite biproduct of copies of the unit object lifts
through `pushforward φ` as soon as the finitely many sections it is assembled from do.

The reassembly is `biproduct.total`, exactly as in
`Stacks.SheafOfModules.exists_restrict_lift_of_retract`; the hypothesis `hlift` is the part
that a shrinking argument has to supply. -/
theorem exists_lift_of_retract_pushforward
    (φ : S ⟶ (Fun.sheafPushforwardContinuous RingCat.{r} J K).obj Rg) [IsIso φ]
    [HasFiniteBiproducts (_root_.SheafOfModules.{r} Rg)]
    {E F G : _root_.SheafOfModules.{r} Rg} (p : G ⟶ F) {n : ℕ}
    (ρ : Retract E (⨁ fun _ : Fin n => _root_.SheafOfModules.unit Rg)) (α : E ⟶ F)
    (hlift : ∀ k : Fin n, ∃ s : ((_root_.SheafOfModules.pushforward.{r} φ).obj G).sections,
      _root_.SheafOfModules.sectionsMap
          ((_root_.SheafOfModules.pushforward.{r} φ).map p) s =
        _root_.SheafOfModules.pushforwardSections φ (F.unitHomEquiv
          (biproduct.ι (fun _ : Fin n => _root_.SheafOfModules.unit Rg) k ≫ ρ.r ≫ α))) :
    ∃ β : (_root_.SheafOfModules.pushforward.{r} φ).obj E ⟶
        (_root_.SheafOfModules.pushforward.{r} φ).obj G,
      β ≫ (_root_.SheafOfModules.pushforward.{r} φ).map p =
        (_root_.SheafOfModules.pushforward.{r} φ).map α := by
  choose s hs using hlift
  have hex : ∀ k : Fin n, ∃ τ : (_root_.SheafOfModules.pushforward.{r} φ).obj
      (_root_.SheafOfModules.unit Rg) ⟶ (_root_.SheafOfModules.pushforward.{r} φ).obj G,
      τ ≫ (_root_.SheafOfModules.pushforward.{r} φ).map p =
        (_root_.SheafOfModules.pushforward.{r} φ).map
          (biproduct.ι (fun _ : Fin n => _root_.SheafOfModules.unit Rg) k ≫ ρ.r ≫ α) :=
    fun k => exists_lift_unit_of_pushforwardSections φ p _ (s k) (hs k)
  choose τ hτ using hex
  refine ⟨(_root_.SheafOfModules.pushforward.{r} φ).map ρ.i ≫ ∑ k : Fin n,
    (_root_.SheafOfModules.pushforward.{r} φ).map
      (biproduct.π (fun _ : Fin n => _root_.SheafOfModules.unit Rg) k) ≫ τ k, ?_⟩
  have htot : ∀ g : (⨁ fun _ : Fin n => _root_.SheafOfModules.unit Rg) ⟶ F,
      ∑ a : Fin n, biproduct.π (fun _ : Fin n => _root_.SheafOfModules.unit Rg) a ≫
        biproduct.ι (fun _ : Fin n => _root_.SheafOfModules.unit Rg) a ≫ g = g := by
    intro g
    simp only [← Category.assoc]
    rw [← Preadditive.sum_comp, biproduct.total, Category.id_comp]
  rw [Category.assoc, Preadditive.sum_comp]
  simp only [Category.assoc, hτ, ← Functor.map_comp]
  rw [← Functor.map_sum, htot, ← Functor.map_comp, ← Category.assoc, ρ.retract,
    Category.id_comp]

end Unit

/-! ### Restriction along `V ≤ U` preserves the unit object -/

section OfLEUnit

variable {Z : TopCat.{t}} {V U : Opens Z} (R : Sheaf (Opens.grothendieckTopology Z) RingCat.{r})

/-- The comparison morphism of sheaves of rings along `V ≤ U` is an isomorphism: each of its
components is `R` applied to an isomorphism of opens. -/
instance isIso_restrictSheafOfRingsHomOfLE (h : V ≤ U) :
    IsIso (restrictSheafOfRingsHomOfLE.{r, t} R h) := by
  rw [← isIso_iff_of_reflects_iso _
    (sheafToPresheaf (Opens.grothendieckTopology ((Opens.toTopCat Z).obj V)) RingCat.{r}),
    NatTrans.isIso_iff_isIso_app]
  intro O
  have h1 : IsIso ((functorCompIsoOfLE h).hom.app O.unop) :=
    NatIso.isIso_app_of_isIso (functorCompIsoOfLE h).hom O.unop
  change IsIso (R.obj.map ((functorCompIsoOfLE h).hom.app O.unop).op)
  infer_instance

/-- Restriction of sheaves of modules along `V ≤ U` takes the unit object to the unit object.

Unlike for restriction along an open embedding, this is *not* the identity: the comparison
restricts scalars along the (invertible) comparison morphism `restrictSheafOfRingsHomOfLE` of
sheaves of rings. -/
def restrictSheafOfModulesOfLEUnitIso (h : V ≤ U) :
    (restrictSheafOfModulesOfLE.{r, r, t} R h).obj
        (_root_.SheafOfModules.unit (restrictSheafOfRings U.isOpenEmbedding R)) ≅
      _root_.SheafOfModules.unit (restrictSheafOfRings V.isOpenEmbedding R) := by
  letI i1 := (isOpenEmbedding_inclusionOfLE h).functor_isContinuous
  letI i2 := isIso_unitToPushforwardObjUnit (restrictSheafOfRingsHomOfLE.{r, t} R h)
  exact (asIso (_root_.SheafOfModules.unitToPushforwardObjUnit
    (restrictSheafOfRingsHomOfLE.{r, t} R h))).symm

end OfLEUnit

/-! ### Stacks 08C6 along an inclusion of opens -/

section OfLELift

variable {Z : TopCat.{t}} (R : Sheaf (Opens.grothendieckTopology Z) RingCat.{r})

/-- The image in `Z` of an open of the subspace `U` is an open of `Z` contained in `U`. -/
lemma isOpenEmbedding_functor_obj_le (U : Opens Z)
    (W : Opens ((Opens.toTopCat Z).obj U)) :
    U.isOpenEmbedding.functor.obj W ≤ U := by
  rintro z ⟨y, -, rfl⟩
  exact y.2

/-- Inside the subspace `U`, the image of the whole of `V := ι_U '' W` is contained in `W`:
the inclusion `ι_U` is injective, so a point of `V`, viewed in `U`, *is* the point of `W` it
came from. -/
lemma inclusionOfLE_functor_obj_top_le (U : Opens Z)
    (W : Opens ((Opens.toTopCat Z).obj U)) :
    (isOpenEmbedding_inclusionOfLE (isOpenEmbedding_functor_obj_le U W)).functor.obj ⊤ ≤ W := by
  rintro y ⟨q, -, rfl⟩
  obtain ⟨b, hb, hbq⟩ := q.2
  have hy : b = inclusionOfLE (isOpenEmbedding_functor_obj_le U W) q := Subtype.ext hbq
  rw [← hy]
  exact hb

/-- **Stacks 08C6 along an inclusion of opens.** Given `α : E ⟶ F` and an epimorphism
`p : G ⟶ F` of sheaves of modules on an open `U` of `Z`, with `E` a retract of a finite
biproduct of copies of the unit object, a factorisation of `α` through `p` exists after
restricting to a small enough open `V ≤ U`.

This is the form Stacks 08C6 is used in when an open has to be shrunk *twice*: the
conclusion lives on an open of `Z`, so a second application of the lemma composes with the
first through `restrictSheafOfModulesOfLEIso` rather than descending into a subspace of a
subspace. -/
theorem exists_le_restrict_lift_of_retract {U : Opens Z}
    [HasSheafify (Opens.grothendieckTopology ((Opens.toTopCat Z).obj U)) AddCommGrpCat.{r}]
    [(Opens.grothendieckTopology ((Opens.toTopCat Z).obj U)).WEqualsLocallyBijective
      AddCommGrpCat.{r}]
    [HasFiniteBiproducts (_root_.SheafOfModules.{r} (restrictSheafOfRings U.isOpenEmbedding R))]
    {E F G : _root_.SheafOfModules.{r} (restrictSheafOfRings U.isOpenEmbedding R)}
    (p : G ⟶ F) {n : ℕ}
    (ρ : Retract E (⨁ fun _ : Fin n =>
      _root_.SheafOfModules.unit (restrictSheafOfRings U.isOpenEmbedding R)))
    (α : E ⟶ F) (hp : Epi p) (x : Z) (hx : x ∈ U) :
    ∃ V : Opens Z, ∃ h : V ≤ U, x ∈ V ∧
      ∃ β : (restrictSheafOfModulesOfLE.{r, r, t} R h).obj E ⟶
          (restrictSheafOfModulesOfLE.{r, r, t} R h).obj G,
        β ≫ (restrictSheafOfModulesOfLE.{r, r, t} R h).map p =
          (restrictSheafOfModulesOfLE.{r, r, t} R h).map α := by
  have := hp
  obtain ⟨W, hxW, hlift⟩ := exists_mem_forall_exists_preimage_of_epi p
    (fun k : Fin n => F.unitHomEquiv
      (biproduct.ι (fun _ : Fin n =>
        _root_.SheafOfModules.unit (restrictSheafOfRings U.isOpenEmbedding R)) k ≫ ρ.r ≫ α))
    (⟨x, hx⟩ : (Opens.toTopCat Z).obj U)
  choose t ht using hlift
  refine ⟨U.isOpenEmbedding.functor.obj W, isOpenEmbedding_functor_obj_le U W,
    ⟨⟨x, hx⟩, hxW, rfl⟩, ?_⟩
  set h : U.isOpenEmbedding.functor.obj W ≤ U := isOpenEmbedding_functor_obj_le U W with hh
  have i1 := (isOpenEmbedding_inclusionOfLE h).functor_isContinuous
  set φ := restrictSheafOfRingsHomOfLE.{r, t} R h with hφ
  have hle : (isOpenEmbedding_inclusionOfLE h).functor.obj ⊤ ≤ W :=
    inclusionOfLE_functor_obj_top_le U W
  refine exists_lift_of_retract_pushforward φ p ρ α fun k => ?_
  refine ⟨Stacks.PresheafOfModules.sectionOfTop
    ((_root_.SheafOfModules.pushforward.{r} φ).obj G).val
    (G.val.map (homOfLE hle).op (t k)), ?_⟩
  refine Stacks.PresheafOfModules.sections_ext_top ?_
  change p.val.app (op ((isOpenEmbedding_inclusionOfLE h).functor.obj ⊤))
      ((Stacks.PresheafOfModules.sectionOfTop
        ((_root_.SheafOfModules.pushforward.{r} φ).obj G).val
        (G.val.map (homOfLE hle).op (t k))).val (op ⊤)) =
    (F.unitHomEquiv (biproduct.ι (fun _ : Fin n =>
      _root_.SheafOfModules.unit (restrictSheafOfRings U.isOpenEmbedding R)) k ≫
      ρ.r ≫ α)).val (op ((isOpenEmbedding_inclusionOfLE h).functor.obj ⊤))
  rw [Stacks.PresheafOfModules.sectionOfTop_val_top
    ((_root_.SheafOfModules.pushforward.{r} φ).obj G).val
    (G.val.map (homOfLE hle).op (t k))]
  refine (_root_.PresheafOfModules.naturality_apply p.val (homOfLE hle).op (t k)).trans ?_
  rw [ht k]
  exact (F.unitHomEquiv _).property _

end OfLELift

/-! ### Transitivity of restriction along an inclusion of opens -/

section OfLETrans

variable {Z : TopCat.{t}} {W V U : Opens Z} (R : Sheaf (Opens.grothendieckTopology Z) RingCat.{r})

/-- Taking the image in `V` of an open of `W` and then the image in `U` is taking the image in
`U` directly. -/
def functorCompIsoOfLETrans (h₁ : W ≤ V) (h₂ : V ≤ U) :
    (isOpenEmbedding_inclusionOfLE h₁).functor ⋙ (isOpenEmbedding_inclusionOfLE h₂).functor ≅
      (isOpenEmbedding_inclusionOfLE (h₁.trans h₂)).functor :=
  NatIso.ofComponents (fun O => eqToIso (by
    refine TopologicalSpace.Opens.ext ?_
    change (inclusionOfLE h₂ : _ → _) '' ((inclusionOfLE h₁ : _ → _) '' (O : Set _)) = _
    rw [Set.image_image]
    rfl)) (fun _ => Subsingleton.elim _ _)

/-- Restricting along `V ≤ U` and then along `W ≤ V` is restricting along `W ≤ U`.

This is the companion of `restrictSheafOfModulesOfLEIso` that lets a *second* shrinking step
be flattened, and it is proved the same way: `pushforwardComp` is `Iso.refl`, so the composite
is definitionally the pushforward along the composite functor of sites, and
`pushforwardCongr₂` compares that with the functor of sites of `W ≤ U` through
`functorCompIsoOfLETrans`. -/
def restrictSheafOfModulesOfLETrans (h₁ : W ≤ V) (h₂ : V ≤ U) :
    restrictSheafOfModulesOfLE.{w, r, t} R h₂ ⋙ restrictSheafOfModulesOfLE.{w, r, t} R h₁ ≅
      restrictSheafOfModulesOfLE.{w, r, t} R (h₁.trans h₂) := by
  letI i1 := (isOpenEmbedding_inclusionOfLE h₁).functor_isContinuous
  letI i2 := (isOpenEmbedding_inclusionOfLE h₂).functor_isContinuous
  letI i3 := (isOpenEmbedding_inclusionOfLE (h₁.trans h₂)).functor_isContinuous
  letI i4 : Functor.IsContinuous
      ((isOpenEmbedding_inclusionOfLE h₁).functor ⋙ (isOpenEmbedding_inclusionOfLE h₂).functor)
      (Opens.grothendieckTopology ((Opens.toTopCat Z).obj W))
      (Opens.grothendieckTopology ((Opens.toTopCat Z).obj U)) :=
    Functor.isContinuous_comp _ _ (Opens.grothendieckTopology ((Opens.toTopCat Z).obj W))
      (Opens.grothendieckTopology ((Opens.toTopCat Z).obj V))
      (Opens.grothendieckTopology ((Opens.toTopCat Z).obj U))
  refine (_root_.SheafOfModules.pushforwardComp
    (restrictSheafOfRingsHomOfLE R h₁) (restrictSheafOfRingsHomOfLE R h₂)).trans ?_
  refine _root_.SheafOfModules.pushforwardCongr₂ _
      (ψ := restrictSheafOfRingsHomOfLE R (h₁.trans h₂))
      (functorCompIsoOfLETrans h₁ h₂).symm ?_
  refine Sheaf.hom_ext (NatTrans.ext (funext fun O => ?_))
  change R.obj.map _ ≫ R.obj.map _ ≫ R.obj.map _ = R.obj.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

end OfLETrans

end Stacks.SheafOfModules

namespace StrictlyPerfect

open Stacks.SheafOfModules

/-! ### What an exact functor of `O_X`-module categories preserves -/

section Preservation

variable {X Y : RingedSpace.{u, v}} (F : OXMod.{u, u, v} X ⥤ OXMod.{u, u, v} Y) [F.Additive]

section PreservesLimits

variable [PreservesFiniteLimits F]

/-- An exact functor of `O_X`-module categories which takes the structure sheaf to the
structure sheaf takes `O_X^{⊕n}` to `O_Y^{⊕n}`. -/
def mapFiniteFreeIso (e : F.obj (structureModule X) ≅ structureModule Y) (n : ℕ) :
    F.obj (finiteFree X n) ≅ finiteFree Y n :=
  letI : PreservesBiproduct (fun _ : Fin n => structureModule X) F :=
    preservesBiproduct_of_preservesProduct F
  (F.mapBiproduct (fun _ : Fin n => structureModule X)).trans
    (biproduct.mapIso (fun _ : Fin n => e))

end PreservesLimits

/-- A merely *additive* functor of `O_X`-module categories which takes the structure sheaf to
the structure sheaf preserves the property of being a direct summand of a finite free module.

No preservation of biproducts — hence no exactness — is needed: for an additive `F` the object
`F(O_X^{⊕n})` is always a *retract* of `⨁ⁿ F(O_X)`, because the two biproduct comparison
morphisms compose to the identity (`CategoryTheory.Functor.retractMapBiproduct`), and a retract
of a retract is a retract. When `F` is moreover exact the comparison is an isomorphism, which is
`mapFiniteFreeIso`.

The module universe is the ring universe on both sides, so
`isDirectSummandOfFiniteFree_iff_retract` converts the predicate to retract data and back and
the universe-lifting functor of the definition never meets `F`. -/
theorem isDirectSummandOfFiniteFree_map (e : F.obj (structureModule X) ≅ structureModule Y)
    {E : OXMod.{u, u, v} X} (hE : IsDirectSummandOfFiniteFree E) :
    IsDirectSummandOfFiniteFree (F.obj E) := by
  obtain ⟨n, ⟨ρ⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract E).mp hE
  exact (isDirectSummandOfFiniteFree_iff_retract _).mpr
    ⟨n, ⟨(ρ.map F).trans ((F.retractMapBiproduct fun _ : Fin n => structureModule X).trans
      (Retract.ofIso (biproduct.mapIso fun _ : Fin n => e)))⟩⟩

/-- Hence it preserves strict perfection of a complex: it takes a zero term to a zero term, so
the complex stays bounded. -/
theorem isStrictlyPerfect_map (e : F.obj (structureModule X) ≅ structureModule Y)
    {P : CochainComplex (OXMod.{u, u, v} X) ℤ} (hP : IsStrictlyPerfect P) :
    IsStrictlyPerfect ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) where
  bounded := hP.bounded.subset (fun i hi => by
    simp only [Set.mem_ofPred_eq] at hi ⊢
    exact fun hz => hi (F.map_isZero hz))
  directSummand i := isDirectSummandOfFiniteFree_map F e (hP.directSummand i)

end Preservation

/-! ### The cycles comparison, and preservation of epimorphisms on homology -/

section Exact

variable {X Y : RingedSpace.{u, v}} (F : OXMod.{u, u, v} X ⥤ OXMod.{u, u, v} Y) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [CategoryWithHomology (OXMod.{u, u, v} X)] [CategoryWithHomology (OXMod.{u, u, v} Y)]

/-- An exact functor commutes with the cycles of a complex. -/
def mapCyclesIso (P : CochainComplex (OXMod.{u, u, v} X) ℤ) (k : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).cycles k ≅ F.obj (P.cycles k) :=
  ShortComplex.mapCyclesIso (P.sc k) F

/-- The cycles comparison `mapCyclesIso` is compatible with the inclusions of cycles. -/
@[reassoc]
lemma mapCyclesIso_hom_iCycles (P : CochainComplex (OXMod.{u, u, v} X) ℤ) (k : ℤ) :
    (mapCyclesIso F P k).hom ≫ F.map (P.iCycles k) =
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).iCycles k :=
  ShortComplex.mapCyclesIso_hom_iCycles (P.sc k) F

/-- The cycles comparison is compatible with `toCycles`. -/
lemma toCycles_comp_mapCyclesIso_hom (P : CochainComplex (OXMod.{u, u, v} X) ℤ) (i j : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).toCycles i j ≫
        (mapCyclesIso F P j).hom = F.map (P.toCycles i j) := by
  have hmono : Mono (F.map (P.iCycles j)) := inferInstance
  rw [← cancel_mono (F.map (P.iCycles j)), Category.assoc, mapCyclesIso_hom_iCycles,
    HomologicalComplex.toCycles_i, ← F.map_comp, HomologicalComplex.toCycles_i]
  rfl

/-- An exact functor preserves the property of being an epimorphism on a cohomology sheaf. -/
theorem epi_homologyMap_map {P Q : CochainComplex (OXMod.{u, u, v} X) ℤ} (α : P ⟶ Q) (m : ℤ)
    (hα : Epi (HomologicalComplex.homologyMap α m)) :
    Epi (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map α) m) := by
  set φ := (HomologicalComplex.shortComplexFunctor (OXMod.{u, u, v} X)
    (ComplexShape.up ℤ) m).map α with hφ
  have hα' : Epi (ShortComplex.homologyMap φ) := hα
  have h2 : Epi (ShortComplex.homologyMap (F.mapShortComplex.map φ) ≫
      ((Q.sc m).mapHomologyIso F).hom) := by
    rw [ShortComplex.mapHomologyIso_hom_naturality φ F]
    exact epi_comp _ _
  have := h2
  have h4 : Epi ((ShortComplex.homologyMap (F.mapShortComplex.map φ) ≫
      ((Q.sc m).mapHomologyIso F).hom) ≫ ((Q.sc m).mapHomologyIso F).inv) := epi_comp _ _
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h4
  exact h4

end Exact

/-! ### Restriction functors preserve strict perfection -/

section Restrict

variable {X : RingedSpace.{u, v}} {V U : Opens X.carrier}

/-- Restriction along `V ≤ U` takes the structure sheaf of `X|_U` to the structure sheaf of
`X|_V`. -/
def restrictModulesOfLEStructureModuleIso (h : V ≤ U) :
    (restrictModulesOfLE.{u, u, v} h).obj (structureModule (X.restrict U.isOpenEmbedding)) ≅
      structureModule (X.restrict V.isOpenEmbedding) :=
  restrictSheafOfModulesOfLEUnitIso (structureSheafOfRings X) h

/-- Restriction to `U` takes the structure sheaf of `X` to the structure sheaf of `X|_U`; this
one holds on the nose (`restrictModules_obj_structureModule`). -/
def restrictModulesStructureModuleIso (U : Opens X.carrier) :
    (restrictModules.{u, u, v} X U).obj (structureModule X) ≅
      structureModule (X.restrict U.isOpenEmbedding) :=
  eqToIso (restrictModules_obj_structureModule U)

/-- Restricting along `V ≤ U` and then along `W ≤ V` is restricting along `W ≤ U`. -/
def restrictComplexOfLETrans {W : Opens X.carrier} (h₁ : W ≤ V) (h₂ : V ≤ U)
    (E : CochainComplex (OXMod.{u, u, v} (X.restrict U.isOpenEmbedding)) ℤ) :
    restrictComplexOfLE.{u, u, v} h₁ (restrictComplexOfLE.{u, u, v} h₂ E) ≅
      restrictComplexOfLE.{u, u, v} (h₁.trans h₂) E :=
  (NatIso.mapHomologicalComplex
    (restrictSheafOfModulesOfLETrans.{u, u, v} (structureSheafOfRings X) h₁ h₂)
    (ComplexShape.up ℤ)).app E

/-- Restriction along `V ≤ U` preserves the property of being a direct summand of a finite
free module. -/
theorem isDirectSummandOfFiniteFree_restrictModulesOfLE (h : V ≤ U)
    {E : OXMod.{u, u, v} (X.restrict U.isOpenEmbedding)}
    (hE : IsDirectSummandOfFiniteFree E) :
    IsDirectSummandOfFiniteFree ((restrictModulesOfLE.{u, u, v} h).obj E) :=
  let := preservesFiniteLimits_restrictModulesOfLE.{u} (X := X) h
  isDirectSummandOfFiniteFree_map _ (restrictModulesOfLEStructureModuleIso h) hE

/-- Restriction along `V ≤ U` preserves strict perfection. -/
theorem isStrictlyPerfect_restrictComplexOfLE (h : V ≤ U)
    {P : CochainComplex (OXMod.{u, u, v} (X.restrict U.isOpenEmbedding)) ℤ}
    (hP : IsStrictlyPerfect P) : IsStrictlyPerfect (restrictComplexOfLE.{u, u, v} h P) :=
  let := preservesFiniteLimits_restrictModulesOfLE.{u} (X := X) h
  isStrictlyPerfect_map _ (restrictModulesOfLEStructureModuleIso h) hP

/-- Restriction to an open preserves strict perfection. -/
theorem isStrictlyPerfect_restrictComplex (U : Opens X.carrier)
    {P : CochainComplex (OXMod.{u, u, v} X) ℤ} (hP : IsStrictlyPerfect P) :
    IsStrictlyPerfect (restrictComplex.{u, u, v} P U) :=
  let := preservesFiniteLimits_restrictModules.{u} (X := X) U
  isStrictlyPerfect_map _ (restrictModulesStructureModuleIso U) hP

end Restrict

/-! ### Truncating an approximation, at independent ring and carrier universes

The four statements below are the universe-polymorphic forms of
`StrictlyPerfect.isZero_truncLE_X`, `StrictlyPerfect.isLE_of_isIso_homologyMap`,
`StrictlyPerfect.isStrictlyPerfect_truncLE` and
`StrictlyPerfect.exists_isStrictlyPerfect_boundedAbove_of_approximation` of
`StacksFrontier/Algebra/Homology/StrictlyPerfectApproximation.lean`. The latter two have *empty*
`levelParams` there, and the former two a single one, because the homology instances were
discharged by instance search rather than assumed: that search supplies
`HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{a}` only once the ring, carrier and
module universes have collapsed. Taking `CategoryWithHomology` as a hypothesis instead keeps
the ring universe `u` and the carrier universe `v` independent, which is what a statement
about an open subspace of a ringed space needs. The proofs are those of the cited file. -/

namespace Truncation

variable {X : RingedSpace.{u, v}} [CategoryWithHomology (OXMod.{u, u, v} X)]
  {P G : CochainComplex (OXMod.{u, u, v} X) ℤ}

/-- The canonical truncation in degrees `≤ r` has no terms above degree `r`. -/
theorem isZero_truncLE_X (P : CochainComplex (OXMod.{u, u, v} X) ℤ) (r : ℤ) {i : ℤ}
    (hi : r < i) : IsZero ((P.truncLE r).X i) :=
  (P.truncLE r).isZero_of_isStrictlyLE r i hi

/-- The map `P^k ⟶ Z^{k+1}(P)` is an epimorphism when the cohomology in degree `k + 1`
vanishes: that cohomology is by definition its cokernel. -/
theorem epi_toCycles_of_isZero_homology (P : CochainComplex (OXMod.{u, u, v} X) ℤ) (k : ℤ)
    (h : IsZero (P.homology (k + 1))) : Epi (P.toCycles k (k + 1)) :=
  Preadditive.epi_of_isZero_cokernel' _ (P.homologyIsCokernel k (k + 1) (by simp)) h

/-- A section of `P^k ⟶ Z^{k+1}(P)` exhibits the degree-`k` cycles as a retract of `P^k`. -/
def retractCyclesOfSection (k : ℤ) (s : P.cycles (k + 1) ⟶ P.X k)
    (hs : s ≫ P.toCycles k (k + 1) = 𝟙 (P.cycles (k + 1))) :
    Retract (P.cycles k) (P.X k) := by
  have hiz : P.iCycles k ≫ P.toCycles k (k + 1) = 0 := by
    rw [← cancel_mono (P.iCycles (k + 1)), Category.assoc, P.toCycles_i, zero_comp,
      P.iCycles_d k (k + 1)]
  have hp : (𝟙 (P.X k) - P.toCycles k (k + 1) ≫ s) ≫ P.d k (k + 1) = 0 := by
    have hsd : s ≫ P.d k (k + 1) = P.iCycles (k + 1) := by
      rw [← P.toCycles_i k (k + 1), ← Category.assoc, hs, Category.id_comp]
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hsd, P.toCycles_i, sub_self]
  refine ⟨P.iCycles k, P.liftCycles (𝟙 (P.X k) - P.toCycles k (k + 1) ≫ s) (k + 1) (by simp) hp,
    ?_⟩
  rw [← cancel_mono (P.iCycles k), Category.assoc, P.liftCycles_i, Preadditive.comp_sub,
    Category.comp_id, ← Category.assoc, hiz, zero_comp, sub_zero, Category.id_comp]

/-- If `α` is an isomorphism on the cohomology in degree `i`, the source has no cohomology there
as soon as the target has none. -/
private theorem isZero_homology_of_isIso_homologyMap {C : Type*} [Category C] [Preadditive C]
    {c : ComplexShape ℤ} {A B : HomologicalComplex C c} (α : A ⟶ B) (i : ℤ)
    [A.HasHomology i] [B.HasHomology i] [IsIso (HomologicalComplex.homologyMap α i)]
    (h : IsZero (B.homology i)) : IsZero (A.homology i) :=
  h.of_iso (asIso (HomologicalComplex.homologyMap α i))

/-- An approximation in degrees `≥ m` of a complex without cohomology above `r ≥ m` has
itself no cohomology above `r`. -/
theorem isLE_of_isIso_homologyMap (m r : ℤ) (hmr : m ≤ r) (α : P ⟶ G)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hG : ∀ i : ℤ, r < i → IsZero (G.homology i)) : P.IsLE r := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have := hiso i (lt_of_le_of_lt hmr hi)
  exact isZero_homology_of_isIso_homologyMap α i (hG i hi)

/-- The canonical truncation in degrees `≤ r` of a strictly perfect complex is strictly
perfect, provided its degree-`r` cycles are a direct summand of a finite free module. -/
theorem isStrictlyPerfect_truncLE (hP : IsStrictlyPerfect P) (r : ℤ)
    (hcyc : IsDirectSummandOfFiniteFree (P.cycles r)) :
    IsStrictlyPerfect (P.truncLE r) where
  bounded := by
    refine Set.Finite.subset (hP.bounded.union (Set.finite_singleton r)) ?_
    intro i hi
    simp only [Set.mem_ofPred_eq] at hi
    rcases lt_trichotomy i r with h | h | h
    · exact Or.inl fun hz => hi (hz.of_iso (P.truncLEXIso r i h))
    · exact Or.inr (by simp [h])
    · exact absurd (isZero_truncLE_X P r h) hi
  directSummand i := by
    rcases lt_trichotomy i r with h | h | h
    · exact isDirectSummandOfFiniteFree_of_iso (P.truncLEXIso r i h) (hP.directSummand i)
    · subst h
      exact isDirectSummandOfFiniteFree_of_iso (P.truncLEXIsoCycles i) hcyc
    · exact isDirectSummandOfFiniteFree_of_isZero (isZero_truncLE_X P r h)

/-- Truncating an approximation: if `α : P ⟶ G` is an approximation in degrees `≥ m` of a
complex `G` with no cohomology above `r ≥ m`, if `P` is strictly perfect and if the degree-`r`
cycles of `P` are a direct summand of a finite free module, then `G` admits an approximation
in degrees `≥ m` by a strictly perfect complex with no terms above degree `r`. -/
theorem exists_isStrictlyPerfect_boundedAbove_of_approximation
    (hP : IsStrictlyPerfect P) (m r : ℤ) (hmr : m ≤ r)
    (hG : ∀ i : ℤ, r < i → IsZero (G.homology i)) (α : P ⟶ G)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hepi : Epi (HomologicalComplex.homologyMap α m))
    (hcyc : IsDirectSummandOfFiniteFree (P.cycles r)) :
    ∃ Q : CochainComplex (OXMod.{u, u, v} X) ℤ, IsStrictlyPerfect Q ∧
      (∀ i : ℤ, r < i → IsZero (Q.X i)) ∧
      ∃ β : Q ⟶ G, (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap β j)) ∧
        Epi (HomologicalComplex.homologyMap β m) := by
  have : P.IsLE r := isLE_of_isIso_homologyMap m r hmr α hiso hG
  have hι : ∀ j : ℤ, IsIso (HomologicalComplex.homologyMap (P.ιTruncLE r) j) := fun j =>
    (quasiIsoAt_iff_isIso_homologyMap _ j).1 (QuasiIso.quasiIsoAt (f := P.ιTruncLE r) j)
  refine ⟨P.truncLE r, isStrictlyPerfect_truncLE hP r hcyc,
    fun i hi => isZero_truncLE_X P r hi, P.ιTruncLE r ≫ α, fun j hj => ?_, ?_⟩
  · rw [HomologicalComplex.homologyMap_comp]
    exact IsIso.comp_isIso' (hι j) (hiso j hj)
  · rw [HomologicalComplex.homologyMap_comp]
    have := hι m
    exact epi_comp _ _

end Truncation

/-! ### The shrinking induction -/

section Shrink

variable {X : RingedSpace.{u, v}}
  [∀ U : Opens X.carrier,
    HasSheafify (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
      AddCommGrpCat.{u}]
  [∀ U : Opens X.carrier,
    (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier).WEqualsLocallyBijective
      AddCommGrpCat.{u}]

/-- Sheafification of abelian presheaves exists on the open subspace `X.restrict U`. -/
local instance hasSheafifyRestrict (U : Opens X.carrier) :
    HasSheafify (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
      AddCommGrpCat.{u} :=
  (inferInstance : ∀ U : Opens X.carrier,
    HasSheafify (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
      AddCommGrpCat.{u}) U

/-- On the open subspace `X.restrict U`, the morphisms of abelian presheaves inverted by
sheafification are exactly the locally bijective ones. -/
local instance wEqualsLocallyBijectiveRestrict (U : Opens X.carrier) :
    (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  (inferInstance : ∀ U : Opens X.carrier,
    (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier).WEqualsLocallyBijective
      AddCommGrpCat.{u}) U

/-- Sheafification of abelian presheaves exists on the open `U`, regarded as a topological
space. -/
local instance hasSheafifyOpen (U : Opens X.carrier) :
    HasSheafify (Opens.grothendieckTopology ((Opens.toTopCat X.carrier).obj U))
      AddCommGrpCat.{u} :=
  hasSheafifyRestrict U

/-- On the open `U`, regarded as a topological space, the morphisms of abelian presheaves
inverted by sheafification are exactly the locally bijective ones. -/
local instance wEqualsLocallyBijectiveOpen (U : Opens X.carrier) :
    (Opens.grothendieckTopology ((Opens.toTopCat X.carrier).obj U)).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  wEqualsLocallyBijectiveRestrict U

/-- Modules over the restriction of the structure sheaf to `U` have finite biproducts. -/
local instance hasFiniteBiproductsRestrictSheafOfRings (U : Opens X.carrier) :
    HasFiniteBiproducts (_root_.SheafOfModules.{u}
      (restrictSheafOfRings U.isOpenEmbedding (structureSheafOfRings X))) :=
  inferInstanceAs (HasFiniteBiproducts (OXMod.{u, u, v} (X.restrict U.isOpenEmbedding)))

/-- Restriction of modules along `V ≤ U` preserves finite limits. -/
local instance preservesFiniteLimitsOfLE {V U : Opens X.carrier} (h : V ≤ U) :
    PreservesFiniteLimits (restrictModulesOfLE.{u, u, v} h (X := X)) :=
  preservesFiniteLimits_restrictModulesOfLE.{u} h

/-- Restriction of modules along `V ≤ U` preserves finite colimits. -/
local instance preservesFiniteColimitsOfLE {V U : Opens X.carrier} (h : V ≤ U) :
    PreservesFiniteColimits (restrictModulesOfLE.{u, u, v} h (X := X)) :=
  preservesFiniteColimits_restrictModulesOfLE.{u} h

/-- The cycles of the restriction `restrictComplexOfLE h P` of a complex along `V ≤ U` are
isomorphic to the restriction of the cycles of `P`. -/
def restrictCyclesOfLEIso {V U : Opens X.carrier} (h : V ≤ U)
    (P : CochainComplex (OXMod.{u, u, v} (X.restrict U.isOpenEmbedding)) ℤ) (k : ℤ) :
    (restrictComplexOfLE.{u, u, v} h P).cycles k ≅
      (restrictModulesOfLE.{u, u, v} h).obj (P.cycles k) :=
  mapCyclesIso (restrictModulesOfLE.{u, u, v} h) P k

/-- The cycles comparison `restrictCyclesOfLEIso` is compatible with `toCycles`. -/
lemma toCycles_comp_restrictCyclesOfLEIso_hom {V U : Opens X.carrier} (h : V ≤ U)
    (P : CochainComplex (OXMod.{u, u, v} (X.restrict U.isOpenEmbedding)) ℤ) (i j : ℤ) :
    (restrictComplexOfLE.{u, u, v} h P).toCycles i j ≫ (restrictCyclesOfLEIso h P j).hom =
      (restrictModulesOfLE.{u, u, v} h).map (P.toCycles i j) :=
  toCycles_comp_mapCyclesIso_hom (restrictModulesOfLE.{u, u, v} h) P i j

/-- **Stacks 08C6 along an inclusion of opens**, for `O_X`-modules on an open subspace of a
ringed space: a morphism out of a direct summand of a finite free module factors through an
epimorphism after shrinking `U` to a smaller open `V` of `X` (not of `U`). -/
theorem exists_le_local_lift_of_isDirectSummandOfFiniteFree {U : Opens X.carrier}
    {E F G : OXMod.{u, u, v} (X.restrict U.isOpenEmbedding)}
    (hE : IsDirectSummandOfFiniteFree E) (α : E ⟶ F) (p : G ⟶ F) (hp : Epi p)
    (x : X.carrier) (hx : x ∈ U) :
    ∃ V : Opens X.carrier, ∃ h : V ≤ U, x ∈ V ∧
      ∃ β : (restrictModulesOfLE.{u, u, v} h).obj E ⟶ (restrictModulesOfLE.{u, u, v} h).obj G,
        β ≫ (restrictModulesOfLE.{u, u, v} h).map p =
          (restrictModulesOfLE.{u, u, v} h).map α := by
  obtain ⟨n, ⟨ρ⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract E).mp hE
  exact exists_le_restrict_lift_of_retract (structureSheafOfRings X) p ρ α hp x hx

/-- **The shrinking induction.** Let `P` be a strictly perfect complex on an open `U` of a
ringed space `X` whose cohomology vanishes above `r`. Then every point of `U` has a
neighbourhood `V ≤ U` on which the degree-`r` cycles of `P` are a direct summand of a finite
free module.

The induction runs downwards from the top nonzero degree of `P`, where the cycles vanish, to
`r`. At each step the already-known retraction of `Z^{k+1}` onto a finite free module turns,
by Stacks 08C6 along an inclusion of opens, into a *section* of `P^k ⟶ Z^{k+1}(P)` over a
smaller open — which is exactly what exhibits `Z^k(P)` as a retract of `P^k`. The opens
produced are opens of `X` below the previous one, so the finitely many shrinking steps compose
through `restrictSheafOfModulesOfLETrans` instead of descending into a subspace of a
subspace. -/
theorem exists_le_isDirectSummandOfFiniteFree_cycles {U : Opens X.carrier}
    {P : CochainComplex (OXMod.{u, u, v} (X.restrict U.isOpenEmbedding)) ℤ}
    (hP : IsStrictlyPerfect P) (r : ℤ)
    (hzero : ∀ i : ℤ, r < i → IsZero (P.homology i)) (x : X.carrier) (hx : x ∈ U) :
    ∃ V : Opens X.carrier, ∃ h : V ≤ U, x ∈ V ∧
      IsDirectSummandOfFiniteFree ((restrictComplexOfLE.{u, u, v} h P).cycles r) := by
  obtain ⟨N, hN⟩ : ∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P.X i) := by
    obtain ⟨N, hN⟩ := hP.bounded.bddAbove
    refine ⟨N, fun i hi => ?_⟩
    by_contra hcon
    exact absurd (hN hcon) (not_le.2 hi)
  have hzeroCyc : ∀ (W : Opens X.carrier) (hWU : W ≤ U) (k : ℤ), N < k →
      IsDirectSummandOfFiniteFree ((restrictComplexOfLE.{u, u, v} hWU P).cycles k) := by
    intro W hWU k hk
    refine isDirectSummandOfFiniteFree_of_isZero
      (IsZero.of_mono ((restrictComplexOfLE.{u, u, v} hWU P).iCycles k) ?_)
    exact (restrictModulesOfLE.{u, u, v} hWU).map_isZero (hN k hk)
  have main : ∀ j : ℕ, ∀ (W : Opens X.carrier) (hWU : W ≤ U) (k : ℤ), r ≤ k →
      N + 1 - k ≤ (j : ℤ) → x ∈ W →
      ∃ V : Opens X.carrier, ∃ h : V ≤ W, x ∈ V ∧
        IsDirectSummandOfFiniteFree
          ((restrictComplexOfLE.{u, u, v} (h.trans hWU) P).cycles k) := by
    intro j
    induction j with
    | zero =>
      intro W hWU k _ hk hxW
      exact ⟨W, le_rfl, hxW, hzeroCyc W (le_rfl.trans hWU) k (by omega)⟩
    | succ j ih =>
      intro W hWU k hrk hk hxW
      rcases lt_or_ge N k with hNk | hNk
      · exact ⟨W, le_rfl, hxW, hzeroCyc W (le_rfl.trans hWU) k hNk⟩
      obtain ⟨V₁, h₁, hxV₁, hcyc⟩ := ih W hWU (k + 1) (by omega) (by omega) hxW
      have hQsp : IsStrictlyPerfect (restrictComplexOfLE.{u, u, v} (h₁.trans hWU) P) :=
        isStrictlyPerfect_restrictComplexOfLE (h₁.trans hWU) hP
      have hQz : IsZero ((restrictComplexOfLE.{u, u, v} (h₁.trans hWU) P).homology (k + 1)) :=
        isZero_homology_restrictComplexOfLE.{u, u, v} (h₁.trans hWU) P (k + 1)
          (hzero (k + 1) (by omega))
      have hepi : Epi ((restrictComplexOfLE.{u, u, v} (h₁.trans hWU) P).toCycles k (k + 1)) :=
        Truncation.epi_toCycles_of_isZero_homology _ k hQz
      obtain ⟨V₂, h₂₁, hxV₂, β, hβ⟩ :=
        exists_le_local_lift_of_isDirectSummandOfFiniteFree hcyc
          (𝟙 ((restrictComplexOfLE.{u, u, v} (h₁.trans hWU) P).cycles (k + 1)))
          ((restrictComplexOfLE.{u, u, v} (h₁.trans hWU) P).toCycles k (k + 1)) hepi x hxV₁
      -- Re-ascribe the lift so that its codomain is spelled as a term of the restricted
      -- complex; the two spellings are definitionally equal but a rewrite cannot cross them.
      obtain ⟨β', hβ'⟩ : ∃ β' : (restrictModulesOfLE.{u, u, v} h₂₁).obj
            ((restrictComplexOfLE.{u, u, v} (h₁.trans hWU) P).cycles (k + 1)) ⟶
          (restrictComplexOfLE.{u, u, v} h₂₁
            (restrictComplexOfLE.{u, u, v} (h₁.trans hWU) P)).X k,
          β' ≫ (restrictModulesOfLE.{u, u, v} h₂₁).map
            ((restrictComplexOfLE.{u, u, v} (h₁.trans hWU) P).toCycles k (k + 1)) = 𝟙 _ :=
        ⟨β, hβ.trans ((restrictModulesOfLE.{u, u, v} h₂₁).map_id _)⟩
      have hsec : ((restrictCyclesOfLEIso h₂₁
            (restrictComplexOfLE.{u, u, v} (h₁.trans hWU) P) (k + 1)).hom ≫ β') ≫
          (restrictComplexOfLE.{u, u, v} h₂₁
            (restrictComplexOfLE.{u, u, v} (h₁.trans hWU) P)).toCycles k (k + 1) = 𝟙 _ := by
        rw [← cancel_mono (restrictCyclesOfLEIso h₂₁
          (restrictComplexOfLE.{u, u, v} (h₁.trans hWU) P) (k + 1)).hom, Category.id_comp,
          Category.assoc, Category.assoc, toCycles_comp_restrictCyclesOfLEIso_hom, hβ',
          Category.comp_id]
      have hret := Truncation.retractCyclesOfSection k _ hsec
      have hXk : IsDirectSummandOfFiniteFree ((restrictComplexOfLE.{u, u, v} h₂₁
          (restrictComplexOfLE.{u, u, v} (h₁.trans hWU) P)).X k) :=
        (isStrictlyPerfect_restrictComplexOfLE h₂₁ hQsp).directSummand k
      refine ⟨V₂, h₂₁.trans h₁, hxV₂, ?_⟩
      refine isDirectSummandOfFiniteFree_of_iso
        (HomologicalComplex.cyclesMapIso
          (restrictComplexOfLETrans h₂₁ (h₁.trans hWU) P) k).symm ?_
      exact isDirectSummandOfFiniteFree_of_retract hret hXk
  obtain ⟨V, h, hxV, hV⟩ := main (N + 1 - r).toNat U le_rfl r le_rfl (Int.self_le_toNat _) hx
  exact ⟨V, h.trans le_rfl, hxV, hV⟩

end Shrink

/-! ### Pseudo-coherence on a ringed space, and the bounded-above local approximation -/

section PseudoCoherent

variable {X : RingedSpace.{u, v}}
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Opens X.carrier,
    HasSheafify (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
      AddCommGrpCat.{u}]
  [∀ U : Opens X.carrier,
    (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier).WEqualsLocallyBijective
      AddCommGrpCat.{u}]

/-- Sheafification of abelian presheaves exists on the open subspace `X.restrict U`. -/
local instance hasSheafifyRestrict' (U : Opens X.carrier) :
    HasSheafify (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
      AddCommGrpCat.{u} :=
  (inferInstance : ∀ U : Opens X.carrier,
    HasSheafify (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
      AddCommGrpCat.{u}) U

/-- On the open subspace `X.restrict U`, the morphisms of abelian presheaves inverted by
sheafification are exactly the locally bijective ones. -/
local instance wEqualsLocallyBijectiveRestrict' (U : Opens X.carrier) :
    (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  (inferInstance : ∀ U : Opens X.carrier,
    (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier).WEqualsLocallyBijective
      AddCommGrpCat.{u}) U

/-- Restriction of modules along `V ≤ U` preserves finite limits. -/
local instance preservesFiniteLimitsOfLE' {V U : Opens X.carrier} (h : V ≤ U) :
    PreservesFiniteLimits (restrictModulesOfLE.{u, u, v} h (X := X)) :=
  preservesFiniteLimits_restrictModulesOfLE.{u} h

/-- Restriction of modules along `V ≤ U` preserves finite colimits. -/
local instance preservesFiniteColimitsOfLE' {V U : Opens X.carrier} (h : V ≤ U) :
    PreservesFiniteColimits (restrictModulesOfLE.{u, u, v} h (X := X)) :=
  preservesFiniteColimits_restrictModulesOfLE.{u} h

/-- **Stacks 08CB, part (1).** A complex of `O_X`-modules is `m`-pseudo-coherent if every point
has an open neighbourhood on which the complex receives a map from a strictly perfect complex
which is an isomorphism on cohomology in degrees `> m` and an epimorphism in degree `m`. -/
abbrev IsPseudoCoherentComplexFrom (E : CochainComplex (OXMod.{u, u, v} X) ℤ) (m : ℤ) : Prop :=
  ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
    ∃ P : CochainComplex (OXMod.{u, u, v} (X.restrict U.isOpenEmbedding)) ℤ,
      IsStrictlyPerfect P ∧
      ∃ α : P ⟶ restrictComplex.{u, u, v} E U,
        (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
        Epi (HomologicalComplex.homologyMap α m)

/-- **Stacks 08CB, part (3).** An object of the derived category is `m`-pseudo-coherent if it
is represented by an `m`-pseudo-coherent complex. -/
abbrev IsPseudoCoherentFrom [HasDerivedCategory.{d} (OXMod.{u, u, v} X)]
    (E : DerivedCategory (OXMod.{u, u, v} X)) (m : ℤ) : Prop :=
  ∃ K : CochainComplex (OXMod.{u, u, v} X) ℤ,
    IsPseudoCoherentComplexFrom K m ∧ Nonempty (DerivedCategory.Q.obj K ≅ E)

/-- **A pseudo-coherent derived object whose cohomology vanishes above `r` has local strictly
perfect approximations concentrated in degrees at most `r`.**

This is the local shrinking step that the proof of Stacks 08DN performs inline ("we can locally
find a section of this surjection and write `E^{n-1} = E' ⊕ E^n`"), stated once and for all.
Combining `exists_le_isDirectSummandOfFiniteFree_cycles` — which shrinks the open until the
degree-`r` cycles of the given approximation are a direct summand of a finite free module — with
the truncation `Truncation.exists_isStrictlyPerfect_boundedAbove_of_approximation`. The
approximation is transported to the smaller open by the exactness of restriction: the
isomorphisms on cohomology by `isIso_homologyMap_restrictComplexOfLE` and the epimorphism in
degree `m` by `epi_homologyMap_map`. -/
theorem exists_local_isStrictlyPerfect_approximation_boundedAbove
    [HasDerivedCategory.{d} (OXMod.{u, u, v} X)]
    (K : DerivedCategory (OXMod.{u, u, v} X)) (m r : ℤ) (hmr : m ≤ r)
    (hK : IsPseudoCoherentFrom K m)
    (hzero : ∀ i : ℤ, r < i →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u, v} X) i).obj K)) :
    ∃ C : CochainComplex (OXMod.{u, u, v} X) ℤ,
      Nonempty (DerivedCategory.Q.obj C ≅ K) ∧
      ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
        ∃ P : CochainComplex (OXMod.{u, u, v} (X.restrict U.isOpenEmbedding)) ℤ,
          IsStrictlyPerfect P ∧ (∀ i : ℤ, r < i → IsZero (P.X i)) ∧
          ∃ α : P ⟶ restrictComplex.{u, u, v} C U,
            (∀ i : ℤ, m < i → IsIso (HomologicalComplex.homologyMap α i)) ∧
            Epi (HomologicalComplex.homologyMap α m) := by
  obtain ⟨C, hC, ⟨eC⟩⟩ := hK
  refine ⟨C, ⟨eC⟩, fun x => ?_⟩
  have hCzero : ∀ i : ℤ, r < i → IsZero (C.homology i) := fun i hi =>
    (hzero i hi).of_iso
      (((DerivedCategory.homologyFunctorFactors (OXMod.{u, u, v} X) i).app C).symm.trans
        ((DerivedCategory.homologyFunctor (OXMod.{u, u, v} X) i).mapIso eC))
  obtain ⟨U, hxU, P, hP, α, hiso, hepi⟩ := hC x
  have hPz : ∀ i : ℤ, r < i → IsZero (P.homology i) := by
    intro i hi
    have := hiso i (lt_of_le_of_lt hmr hi)
    exact Truncation.isZero_homology_of_isIso_homologyMap α i
      (isZero_homology_restrictComplex.{u, u, v} C i (hCzero i hi))
  obtain ⟨V, hVU, hxV, hcyc⟩ := exists_le_isDirectSummandOfFiniteFree_cycles hP r hPz x hxU
  refine ⟨V, hxV, ?_⟩
  -- Re-ascribe the comparison isomorphism in the `mapHomologicalComplex` spelling, so that
  -- composing it with the restricted approximation is type-correct at `implicit`
  -- transparency and `homologyMap_comp` applies.
  obtain ⟨e⟩ : Nonempty (((restrictModulesOfLE.{u, u, v} hVU).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (restrictComplex.{u, u, v} C U) ≅
      restrictComplex.{u, u, v} C V) := ⟨restrictComplexOfLEIso.{u, u, v} hVU C⟩
  set αV := ((restrictModulesOfLE.{u, u, v} hVU).mapHomologicalComplex
    (ComplexShape.up ℤ)).map α ≫ e.hom with hαV
  have he : ∀ j : ℤ, IsIso (HomologicalComplex.homologyMap e.hom j) := fun j =>
    (HomologicalComplex.homologyMapIso e j).isIso_hom
  have hisoV : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap αV j) := by
    intro j hj
    have := isIso_homologyMap_restrictComplexOfLE.{u, u, v} hVU α j (hiso j hj)
    rw [hαV, HomologicalComplex.homologyMap_comp]
    infer_instance
  have hepiV : Epi (HomologicalComplex.homologyMap αV m) := by
    have := epi_homologyMap_map (restrictModulesOfLE.{u, u, v} hVU) α m hepi
    rw [hαV, HomologicalComplex.homologyMap_comp]
    infer_instance
  obtain ⟨Q, hQsp, hQzero, β, hβiso, hβepi⟩ :=
    Truncation.exists_isStrictlyPerfect_boundedAbove_of_approximation
      (isStrictlyPerfect_restrictComplexOfLE hVU hP) m r hmr
      (fun i hi => isZero_homology_restrictComplex.{u, u, v} C i (hCzero i hi))
      αV hisoV hepiV hcyc
  exact ⟨Q, hQsp, hQzero, β, hβiso, hβepi⟩

end PseudoCoherent

end StrictlyPerfect

end
