module

public import StacksFrontier.AlgebraicGeometry.Crystalline.LevelSectionsModule

/-!
# The functor of [Stacks, Tag 07JG] into `Crystalline.FirstOrderCrystal`

Before this module no declaration in the tree had type `_ ⥤ Crystalline.FirstOrderCrystal`, and
the only inhabitant of `Crystalline.FirstOrderCrystal` anywhere was
`Crystalline.trivialFirstOrderCrystal`, the zero module over the zero divided power ring.  The
functor was carried, as the field
`Crystalline.GlobalCrystallineSituation.SmallSite.PreReduction07JG.functor`, and five further
fields of that bundle mention `functor.obj F`, so all six were blocked on the same absence.

This module constructs the functor.  Its source is the crystals in quasi-coherent
`𝒪_{X/S}`-modules on `Cris(X/S)`, its value at `ℱ` has for its module the limit
`M = lim_e Γ(T_e, ℱ)` of [Stacks, Lemma 60.17.3, Tag 07JG] over the ring
`D = lim_e Γ(T_e, 𝒪_{T_e})` of that tag, and its value at a morphism is the level-by-level map of
`...SmallSite.levelSectionsLimitMap`.

## Main definitions

Everything is in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `LevelScalars07JG` — a system of levels together with the identification of `D` with the limit
  of their section rings.  These are the fields `levelSystem` and `ringEquiv` of
  `...SmallSite.PreReduction07JG`, separated out because the `D`-module structure on the limit of
  the level sections is defined from them.
* `LevelScalars07JG.sections` — **the module `M = lim_e Γ(T_e, ℱ)` as a `D`-module**, the limit of
  `...SmallSite.levelSectionsLimit` with scalars restricted along `ringEquiv`, and
  `LevelScalars07JG.sectionsMap` the `D`-linear map a morphism of crystals induces on it.
* `LevelScalars07JG.sectionsEquiv` — that module is the limit on the nose, as an `AddEquiv`.
* `LevelComparison07JG` — the datum from which the functor is built: the first-order comparison
  datum of a crystal read on `M`, natural in the crystal, together with the three items of
  [Stacks, Tag 07JG] that `Crystalline.FirstOrderCrystal` carries.
* `LevelComparison07JG.functor` — **the functor** `QuasiCoherentCrystal S ⥤ FirstOrderCrystal`.
* `LevelReduction07JG` and `LevelReduction07JG.toPreReduction07JG` — that datum together with the
  three clauses about the first-order thickenings of the levels, and the
  `...SmallSite.PreReduction07JG` it yields.

## Main results

* `LevelComparison07JG.functor_obj_carrier` and `LevelComparison07JG.functor_map_toLinearMap` —
  the functor is the level-by-level assignment, not an abstract one.
* `LevelReduction07JG.toPreReduction07JG` — **four of the twelve fields of
  `...SmallSite.PreReduction07JG` are discharged by construction**: `functor` is
  `LevelComparison07JG.functor`, `sections` is the identity identification
  `LevelScalars07JG.sectionsEquiv`, and `sections_smul` and `sections_naturality` are
  `LevelScalars07JG.sectionsEquiv_smul` and `...SmallSite.levelSectionsLimitMap_val`.

## What is and is not proved

**[Stacks, Tag 07JG] and [Stacks, Tag 07JH] are `...SmallSite.crystalPairFunctor` and
`...SmallSite.crystalPairFunctor_isEquivalence`; no tag attribute is placed in this
module.**  In particular `Functor.IsEquivalence (LevelComparison07JG.functor L)` is **not**
proved: by `...SmallSite.faithful_functor07JG_iff` it contains the faithfulness half of the
conclusion of [Stacks, Tag 07JH], so it is not a formality about this construction but the tag
itself, and nothing below bears on it.

What this module does is move the functor from a hypothesis to a construction, and it is exact
about what the construction still runs on.  `LevelComparison07JG` carries five things, each a
named missing input and none of them a stand-in for the tag:

1. `comparison`, the first-order comparison datum of the crystal read on `M`.  This is the
   geometric datum `...SmallSite.firstOrderComparison` of
   `StacksFrontier/AlgebraicGeometry/Crystalline/CrystalFirstOrderComparison.lean` — which *is*
   constructed there, from the crystal condition, as an isomorphism
   `ε : p₀^* ℱ_T ≅ p₁^* ℱ_T` of sheaves of modules — transcribed into the algebraic record
   `Crystalline.FirstOrderComparison` over the limit ring.  That transcription needs the sections
   of `SheafOfModules.pullback` to be a base change, which is
   `...GlobalCrystallineSituation.FirstOrderIdealBaseChange`: constructed only for
   `ℱ = 𝒪_{X/S}`, by `...firstOrderIdealBaseChangeUnit`, and false as spelled on a non-affine
   object.  It is the same obstruction as the fields `baseChange` and `baseChange_tmul` of
   `...SmallSite.PreReduction07JG`.
2. `comparison_naturality`.  Its sheaf-level counterpart is proved, as
   `...SmallSite.firstOrderComparison_naturality`, and it is item 1 again that stops it being
   read on `M`.
3. `isPAdicallyComplete`, item (07JB).
4. `isIntegrable`, item (07JD), and `hasCoordinateOperators`, the non-vacuity of the last two
   conditions.
5. `isTopologicallyQuasiNilpotent`, item (07JE).

Items 3–5 are the three fields of `Crystalline.FirstOrderCrystal` the library derives from no
crystal, which is recorded in the "What is and is not proved" sections of
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalsToPairs.lean` and
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalPairsFirstOrder.lean`.  They are stated here
exactly as `Crystalline.FirstOrderCrystal` states them, quantified over the crystal, and not
weakened.

What is **not** carried, and is the gain, is the module `M` itself with its `D`-action, the
functoriality, and the limit identification: the fields `functor`, `sections`, `sections_smul` and
`sections_naturality` of `...SmallSite.PreReduction07JG` are consequences of the construction and
not inputs to it.  `LevelReduction07JG.toPreReduction07JG` is that statement.

`LevelReduction07JG` is **not** a `...SmallSite.Reduction07JG`: it says nothing about the system
of levels, so like `...SmallSite.PreReduction07JG` it is inhabited by the degenerate datum over
the empty open of `X` and **no tag may be stated against it**.  Composing
`toPreReduction07JG` with `...SmallSite.Reduction07JG.ofWholeSpaceSystem` is what narrows it to
the source's own system.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J8](https://stacks.math.columbia.edu/tag/07J8)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

universe u uI

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} {A : Type u} [CommRing A]
  {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u} [AddCommGroup Omega]
  [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {p : ℕ} {ι : Type uI} {dx : ι → Omega}

/-! ### The scalars: a system of levels whose section rings have `D` for their limit -/

/-- **A system of levels of `Cris(X/S)` together with the identification of `D` with the limit of
their section rings.**  These are the fields `levelSystem` and `ringEquiv` of
`Crystalline.GlobalCrystallineSituation.SmallSite.PreReduction07JG`, and they are separated out
because the `D`-module structure on the limit of the level sections is defined from them and the
remaining clauses of that bundle are stated over that module.

`ringEquiv` is available for the system of [Stacks, Tag 07JN] at the completed envelope of
[Stacks, Tag 07J8], as `...SmallSite.envelopeLevelRingLimitEquiv`, so this part of the datum is
not an obstruction. -/
structure LevelScalars07JG (S : GlobalCrystallineSituation.{u}) (D : DividedPowerRing.{u}) where
  /-- The system of levels `T_0 ⟶ T_1 ⟶ ⋯` of `Cris(X/S)`. -/
  levelSystem : ℕ ⥤ CrystallineThickening S
  /-- `D` is the inverse limit of the section rings of the levels. -/
  ringEquiv : (D : Type u) ≃+* ↥(levelRingLimit S levelSystem)

namespace LevelScalars07JG

variable (L : LevelScalars07JG S D)

/-- **The module `M = lim_e Γ(T_e, ℱ)` of [Stacks, Tag 07JG], as a `D`-module.**  It is the limit
`Crystalline.GlobalCrystallineSituation.SmallSite.levelSectionsLimit`, whose module structure over
the limit of the section rings is `...SmallSite.instModuleLevelSectionsLimit`, with the scalars
restricted along `ringEquiv`.

It is a type synonym and not the limit itself only because the `D`-action depends on `ringEquiv`,
which is a field and not an instance; `LevelScalars07JG.sectionsEquiv` is the identification. -/
def sections (F : QuasiCoherentCrystal S) : Type u :=
  ↥(levelSectionsLimit S L.levelSystem F)

/-- The additive group structure of `L.sections F`, that of the limit of the level sections. -/
instance (F : QuasiCoherentCrystal S) : AddCommGroup (L.sections F) :=
  inferInstanceAs (AddCommGroup ↥(levelSectionsLimit S L.levelSystem F))

/-- The module structure of `L.sections F` over the limit of the section rings of the levels,
that of the limit of the level sections. -/
instance (F : QuasiCoherentCrystal S) :
    Module ↥(levelRingLimit S L.levelSystem) (L.sections F) :=
  inferInstanceAs
    (Module ↥(levelRingLimit S L.levelSystem) ↥(levelSectionsLimit S L.levelSystem F))

/-- The `D`-module structure of `L.sections F`: the action of the limit of the section rings,
with the scalars restricted along `ringEquiv`. -/
instance (F : QuasiCoherentCrystal S) : Module (D : Type u) (L.sections F) :=
  Module.compHom (L.sections F) L.ringEquiv.toRingHom

/-- **The module of the datum is the limit of the level sections on the nose.**  This is the field
`Crystalline.GlobalCrystallineSituation.SmallSite.PreReduction07JG.sections`: an additive
isomorphism and not a linear one, the two sides being modules over `D` and over the limit of the
section rings, which `ringEquiv` identifies. -/
def sectionsEquiv (F : QuasiCoherentCrystal S) :
    L.sections F ≃+ ↥(levelSectionsLimit S L.levelSystem F) :=
  AddEquiv.refl _

/-- `LevelScalars07JG.sectionsEquiv` is the identity on underlying elements. -/
@[simp] theorem sectionsEquiv_apply (F : QuasiCoherentCrystal S) (m : L.sections F) :
    L.sectionsEquiv F m = m :=
  rfl

/-- **The identification of the module with the limit is semilinear for `ringEquiv`**, level by
level.  This is the field
`Crystalline.GlobalCrystallineSituation.SmallSite.PreReduction07JG.sections_smul`, and it holds
because the `D`-action is the action of the limit ring through `ringEquiv` by definition. -/
theorem sectionsEquiv_smul (F : QuasiCoherentCrystal S) (a : (D : Type u)) (m : L.sections F)
    (e : ℕ) :
    (L.sectionsEquiv F (a • m)).val e = (L.ringEquiv a).val e • (L.sectionsEquiv F m).val e :=
  rfl

/-- **A morphism of crystals induces a `D`-linear map of the modules**, the level-by-level map of
`Crystalline.GlobalCrystallineSituation.SmallSite.levelSectionsLimitMap`.  It is `D`-linear and not
merely additive because the `D`-action on both sides is the action of the limit ring through one
and the same `ringEquiv`. -/
def sectionsMap {F G : QuasiCoherentCrystal S} (psi : F ⟶ G) :
    L.sections F →ₗ[(D : Type u)] L.sections G where
  toFun := levelSectionsLimitMap psi
  map_add' := map_add (levelSectionsLimitMap psi)
  map_smul' a m := map_smul (levelSectionsLimitMap psi) (L.ringEquiv a) m

/-- At each level, `LevelScalars07JG.sectionsMap psi` is the map of sections induced by `psi`. -/
@[simp] theorem sectionsMap_val {F G : QuasiCoherentCrystal S} (psi : F ⟶ G) (m : L.sections F)
    (e : ℕ) :
    (L.sectionsEquiv G (L.sectionsMap psi m)).val e =
      (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val
        (op (L.levelSystem.obj e))).hom ((L.sectionsEquiv F m).val e) :=
  rfl

/-- `LevelScalars07JG.sectionsMap` sends the identity of a crystal to the identity map. -/
theorem sectionsMap_id (F : QuasiCoherentCrystal S) :
    L.sectionsMap (𝟙 F) = LinearMap.id :=
  LinearMap.ext fun _ ↦ Subtype.ext (funext fun _ ↦ rfl)

/-- `LevelScalars07JG.sectionsMap` sends a composite of morphisms of crystals to the composite of
the maps. -/
theorem sectionsMap_comp {F G H : QuasiCoherentCrystal S} (psi : F ⟶ G) (chi : G ⟶ H) :
    L.sectionsMap (psi ≫ chi) = (L.sectionsMap chi).comp (L.sectionsMap psi) :=
  LinearMap.ext fun _ ↦ Subtype.ext (funext fun _ ↦ rfl)

end LevelScalars07JG

/-! ### The comparison datum on the limit, and the functor it builds -/

/-- **The datum the functor of [Stacks, Tag 07JG] is built from**, over a system of levels whose
section rings have `D` for their limit: the first-order comparison datum of a crystal read on the
module `M = lim_e Γ(T_e, ℱ)`, natural in the crystal, together with the three items of the tag
that `Crystalline.FirstOrderCrystal` carries and the non-vacuity of the last two.

Every field is a named missing input and none is a stand-in for the tag.  `comparison` and
`comparison_naturality` are the geometric datum `...SmallSite.firstOrderComparison` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalFirstOrderComparison.lean` — which is
constructed there from the crystal condition, as an isomorphism `ε : p₀^* ℱ_T ≅ p₁^* ℱ_T`, with
its naturality `...SmallSite.firstOrderComparison_naturality` — read in the algebraic record over
the limit ring, which needs the sections of `SheafOfModules.pullback` to be a base change.  The
remaining three are items (07JB), (07JD) and (07JE), which the library derives from no crystal.

What the datum does **not** supply, and what distinguishes it from the fields of
`...SmallSite.PreReduction07JG` it replaces, is the module, its `D`-action, the identification of
it with the limit, and the functoriality: those are
`...SmallSite.LevelScalars07JG.sections`, `...LevelScalars07JG.sectionsEquiv` and
`...LevelScalars07JG.sectionsMap`, all constructed. -/
structure LevelComparison07JG (S : GlobalCrystallineSituation.{u}) (A : Type u) [CommRing A]
    (D : DividedPowerRing.{u}) (g : A →+* D) (Omega : Type u) [AddCommGroup Omega]
    [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
    (d : DividedPowerDerivation A D g Omega) (p : ℕ) {ι : Type uI} (dx : ι → Omega)
    (L : LevelScalars07JG S D) where
  /-- The first-order comparison datum of the crystal, read on `M = lim_e Γ(T_e, ℱ)`. -/
  comparison : ∀ F : QuasiCoherentCrystal S, FirstOrderComparison A D g Omega d (L.sections F)
  /-- It is natural in the crystal, which is the functoriality clause of the tag. -/
  comparison_naturality : ∀ {F G : QuasiCoherentCrystal S} (psi : F ⟶ G) (m : L.sections F),
    comparison G (L.sectionsMap psi m) =
      LinearMap.lTensor (firstOrderExtension D Omega) (L.sectionsMap psi) (comparison F m)
  /-- **Item (07JB), carried.**  The module is `p`-adically complete. -/
  isPAdicallyComplete : ∀ F : QuasiCoherentCrystal S, IsPAdicallyComplete p D (L.sections F)
  /-- **Carried.**  The connection admits coordinate operators for the chosen differentials. -/
  hasCoordinateOperators : ∀ F : QuasiCoherentCrystal S,
    ∃ theta : ι → (L.sections F → L.sections F),
      IsCoordinateExpansion p D Omega dx ((comparison F).completedConnection p) theta
  /-- **Item (07JD), carried.**  The connection is integrable. -/
  isIntegrable : ∀ F : QuasiCoherentCrystal S,
    IsIntegrable p D Omega dx ((comparison F).completedConnection p)
  /-- **Item (07JE), carried.**  The connection is topologically quasi-nilpotent. -/
  isTopologicallyQuasiNilpotent : ∀ F : QuasiCoherentCrystal S,
    IsTopologicallyQuasiNilpotent p D Omega dx ((comparison F).completedConnection p)

namespace LevelComparison07JG

variable {L : LevelScalars07JG S D} (C : LevelComparison07JG S A D g Omega d p dx L)

/-- **The first-order crystal datum of a crystal in quasi-coherent `𝒪_{X/S}`-modules**: its module
is `M = lim_e Γ(T_e, ℱ)` over `D`, and its comparison map and three carried items are those of the
datum.

This is an object of `Crystalline.FirstOrderCrystal` over an arbitrary divided power ring, which
`Crystalline.trivialFirstOrderCrystal` — the zero module over the zero divided power ring, and
otherwise the only inhabitant in the library — is not.  It is **not** a claim that the category is
inhabited over a nonzero ring: that needs a `LevelComparison07JG` over one, and this module
constructs none. -/
def obj (F : QuasiCoherentCrystal S) :
    FirstOrderCrystal.{u, u, u, uI, u} A D g Omega d p dx where
  carrier := L.sections F
  comparison := C.comparison F
  isPAdicallyComplete := C.isPAdicallyComplete F
  hasCoordinateOperators := C.hasCoordinateOperators F
  isIntegrable := C.isIntegrable F
  isTopologicallyQuasiNilpotent := C.isTopologicallyQuasiNilpotent F

/-- **The reduction functor of [Stacks, Tag 07JG]**, from the crystals in quasi-coherent
`𝒪_{X/S}`-modules on `Cris(X/S)` to the first-order crystal data over `D`.  This is the field
`Crystalline.GlobalCrystallineSituation.SmallSite.PreReduction07JG.functor`, constructed rather
than carried.

Composed with `Crystalline.firstOrderCrystalsToPairs` it is the functor
`...SmallSite.functor07JG` that [Stacks, Tag 07JH] is about.  **That it is an equivalence is not
proved and does not follow from anything here**: by `...SmallSite.faithful_functor07JG_iff` its
faithfulness is the faithfulness half of the tag's own conclusion. -/
def functor : QuasiCoherentCrystal S ⥤ FirstOrderCrystal.{u, u, u, uI, u} A D g Omega d p dx where
  obj F := C.obj F
  map psi :=
    { toLinearMap := L.sectionsMap psi
      comparison_naturality := C.comparison_naturality psi }
  map_id F := FirstOrderCrystalHom.ext (L.sectionsMap_id F)
  map_comp psi chi := FirstOrderCrystalHom.ext (L.sectionsMap_comp psi chi)

/-- The value of `LevelComparison07JG.functor` at a crystal is `LevelComparison07JG.obj`. -/
@[simp] theorem functor_obj (C : LevelComparison07JG S A D g Omega d p dx L)
    (F : QuasiCoherentCrystal S) : C.functor.obj F = C.obj F :=
  rfl

/-- The module of the value of `LevelComparison07JG.functor` at `F` is `M = lim_e Γ(T_e, ℱ)`. -/
@[simp] theorem functor_obj_carrier (F : QuasiCoherentCrystal S) :
    (C.functor.obj F).carrier = L.sections F :=
  rfl

/-- The linear map of the value of `LevelComparison07JG.functor` at a morphism is
`LevelScalars07JG.sectionsMap`. -/
@[simp] theorem functor_map_toLinearMap (C : LevelComparison07JG S A D g Omega d p dx L)
    {F G : QuasiCoherentCrystal S} (psi : F ⟶ G) :
    (C.functor.map psi).toLinearMap = L.sectionsMap psi :=
  rfl

end LevelComparison07JG

/-! ### The clauses about the first-order thickenings of the levels -/

/-- **The reduction datum of [Stacks, Tag 07JG] with the module, its action and the limit
identification removed**, those three being constructed: the comparison datum of
`Crystalline.GlobalCrystallineSituation.SmallSite.LevelComparison07JG` together with the three
clauses of `...SmallSite.PreReduction07JG` that speak about the first-order universal thickenings
of [Stacks, Tag 07J2] of the levels.

Those three clauses are transcribed unchanged, with `(functor.obj F).carrier` replaced by the
module it is: `thickeningRingHom` and `thickeningRingHom_p₀` because the section rings of the
first-order thickenings of the levels are not computed anywhere in the tree, and `baseChange`,
`baseChange_tmul` and `comparison_eq` because the sections of a crystal over such a thickening are
not known to be a base change — the datum
`...GlobalCrystallineSituation.FirstOrderIdealBaseChange`, constructed only for
`ℱ = 𝒪_{X/S}`.

**No tag may be stated against this bundle.**  Like `...SmallSite.PreReduction07JG` it says
nothing about the system of levels, so it is inhabited by the degenerate datum over the empty open
of `X` at which every clause holds between elements of a subsingleton; see
`...SmallSite.preReduction07JGBot`.  Narrowing it to the source's own system is
`...SmallSite.Reduction07JG.ofWholeSpaceSystem` applied to `toPreReduction07JG`. -/
structure LevelReduction07JG (S : GlobalCrystallineSituation.{u}) (A : Type u) [CommRing A]
    (D : DividedPowerRing.{u}) (g : A →+* D) (Omega : Type u) [AddCommGroup Omega]
    [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
    (d : DividedPowerDerivation A D g Omega) (p : ℕ) {ι : Type uI} (dx : ι → Omega)
    (L : LevelScalars07JG S D)
    extends LevelComparison07JG S A D g Omega d p dx L where
  /-- The ring `D ⊕ Ω` maps to the sections of `𝒪_{X/S}` over the first-order thickening of the
  level `e`. -/
  thickeningRingHom : ∀ e : ℕ, firstOrderExtension D Omega →+*
    (structureSheaf S).val.obj (op (firstOrderThickeningCrysObject S (L.levelSystem.obj e)))
  /-- On the `D` summand it is the reduction of `D` to the level followed by restriction along the
  projection of [Stacks, Tag 07J2]. -/
  thickeningRingHom_p₀ : ∀ (e : ℕ) (a : (D : Type u)),
    thickeningRingHom e (firstOrderP₀ D Omega a) =
      ((structureSheaf S).val.map
        (firstOrderThickeningCrysP₀ S (L.levelSystem.obj e)).op).hom ((L.ringEquiv a).val e)
  /-- The base change `(D ⊕ Ω) ⊗_D M` maps to the sections over the first-order thickening of the
  level `e`. -/
  baseChange : ∀ (F : QuasiCoherentCrystal S) (e : ℕ),
    (firstOrderExtension D Omega ⊗[D] L.sections F) →+
      F.obj.val.obj (op (firstOrderThickeningCrysObject S (L.levelSystem.obj e)))
  /-- It sends `b ⊗ m` to `b · p₀^* m`, which determines it outright. -/
  baseChange_tmul : ∀ (F : QuasiCoherentCrystal S) (e : ℕ)
    (b : firstOrderExtension D Omega) (m : L.sections F),
    baseChange F e (b ⊗ₜ[D] m) = thickeningRingHom e b •
      F.obj.val.map (firstOrderThickeningCrysP₀ S (L.levelSystem.obj e)).op
        ((L.sectionsEquiv F m).val e)
  /-- **The recipe of [Stacks, Tag 07JG].**  Read at each level inside the base change, the
  comparison map is the restriction along the second projection. -/
  comparison_eq : ∀ (F : QuasiCoherentCrystal S) (e : ℕ) (m : L.sections F),
    baseChange F e (comparison F m) =
      F.obj.val.map (firstOrderThickeningCrysP₁ S (L.levelSystem.obj e)).op
        ((L.sectionsEquiv F m).val e)

/-- **Four of the twelve fields of
`Crystalline.GlobalCrystallineSituation.SmallSite.PreReduction07JG` are not inputs.**  Given the
comparison datum and the three clauses about the first-order thickenings of the levels, the
reduction datum of [Stacks, Tag 07JG] without its level condition follows: `functor` is
`...SmallSite.LevelComparison07JG.functor`, `sections` is the identity identification
`...SmallSite.LevelScalars07JG.sectionsEquiv`, `sections_smul` is
`...LevelScalars07JG.sectionsEquiv_smul`, and `sections_naturality` holds by construction of
`...LevelScalars07JG.sectionsMap`.

The module `M = lim_e Γ(T_e, ℱ)`, its `D`-action and the functoriality of the assignment are
therefore no longer carried anywhere.  What remains carried is the comparison datum with its
naturality, the three items (07JB), (07JD), (07JE) with the non-vacuity of the last two, and the
three clauses about the thickenings — and **not** [Stacks, Tag 07JH], which is
`Functor.IsEquivalence` of the composite and is proved nowhere. -/
def LevelReduction07JG.toPreReduction07JG {L : LevelScalars07JG S D}
    (R : LevelReduction07JG S A D g Omega d p dx L) :
    PreReduction07JG S A D g Omega d p dx where
  levelSystem := L.levelSystem
  functor := R.toLevelComparison07JG.functor
  ringEquiv := L.ringEquiv
  thickeningRingHom := R.thickeningRingHom
  thickeningRingHom_p₀ := R.thickeningRingHom_p₀
  sections := L.sectionsEquiv
  sections_smul F a m e := L.sectionsEquiv_smul F a m e
  sections_naturality _ _ _ := rfl
  baseChange := R.baseChange
  baseChange_tmul := R.baseChange_tmul
  comparison_eq := R.comparison_eq

/-- The system of levels of `LevelReduction07JG.toPreReduction07JG` is that of `L`. -/
@[simp] theorem LevelReduction07JG.toPreReduction07JG_levelSystem {L : LevelScalars07JG S D}
    (R : LevelReduction07JG S A D g Omega d p dx L) :
    R.toPreReduction07JG.levelSystem = L.levelSystem :=
  rfl

/-- The functor of `LevelReduction07JG.toPreReduction07JG` is `LevelComparison07JG.functor`. -/
@[simp] theorem LevelReduction07JG.toPreReduction07JG_functor {L : LevelScalars07JG S D}
    (R : LevelReduction07JG S A D g Omega d p dx L) :
    R.toPreReduction07JG.functor = R.toLevelComparison07JG.functor :=
  rfl

end Crystalline.GlobalCrystallineSituation.SmallSite
