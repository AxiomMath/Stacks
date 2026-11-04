module

public import StacksFrontier.AlgebraicGeometry.CotangentAppIsoGenerator.Engine
public import StacksFrontier.AlgebraicGeometry.ConormalAffineShape.Shape
public import StacksFrontier.AlgebraicGeometry.ConormalOpenFactorizations.Basic

/-!
# The locality comparison of [Stacks, Tag 01R3] over the top open, at both shapes

`StacksDraft.AlgebraicGeometry.F3.CotangentAppIsoGenerator.Engine` proves the generator formula
for the part (2) engine of [Stacks, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3) —
`Stacks.Conormal.CotangentAppIsoGenerator.restrictAffineModelIso_val_app_top` and
`affineSectionsIsoCotangent_apply` — under one hypothesis, `hc`, which characterizes the locality
comparison fed into the engine on the section being carried. That file leaves `hc` open at
both of the shapes at which the comparison is used.

This file discharges it at both, and nothing is assumed beyond the data each shape already
carries: no affineness, no Noetherian, no finiteness, no quasi-compactness, and the
closed-immersion factorization is arbitrary.

## Main results

* `Stacks.Tag08S2Locality.conormalSheafRestrictIso_unit_app_top`: **the locality comparison's
  generator formula over the top open.**
  `Stacks.Conormal.Locality.conormalSheafRestrictIso_unit_app` states it over
  `(i' ⁻¹ᵁ O).ι ⁻¹ᵁ (i' ⁻¹ᵁ O)`, which is `⊤` but not definitionally; this is the same statement
  read over `⊤`.
* `Stacks.Tag08S2Locality.restrictPushforward_top`: the engine's first factor over the top open —
  `Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`, preceded by the restriction
  map along `V.ι ''ᵁ ⊤ = V`, is a single restriction map of the source module.
* `Stacks.Tag08S2Locality.hc_conormalSheafRestrictIso`: **`hc` at the shape
  `Stacks.Conormal.CotangentAppIso.pushforwardConormalSectionsIsoCotangent` uses**, namely at
  `Stacks.Conormal.Locality.conormalSheafRestrictIso`. The section carried is the quotient
  generator `Stacks.Conormal.conormalQuotientMap` of a section `y₀` of the ideal sheaf of `i'`,
  and the unit generator it goes to is attached to the matching section of the ideal sheaf of
  `i' ∣_ O`, which `Stacks.Conormal.Locality.restrictIdealSheafIso'_app_ι` identifies.
* `Stacks.Tag08S2Locality.hc_conormalSheafRestrictIsoOfLe`: **`hc` at the shape
  `Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent` uses** — the one
  `StacksDraft.AlgebraicGeometry.F3.DiagonalQuotientPresentation.Basic` instantiates at the
  diagonal — namely at `Stacks.Conormal.AffineShape.conormalSheafRestrictIsoOfLe`. The section of
  the ideal sheaf of `i ∣_ V` that the generator goes to is pinned by its image in the structure
  sheaf, which is the hypothesis `hy`.

## The second factor has an elementwise description

The Engine's "What is not done" section says of the second factor of
`conormalSheafRestrictIsoOfLe` that

> `Stacks.Conormal.AffineCotangent.Transport.idealSheafPullbackIsoOfIsoTarget` … has no
> elementwise description yet.

**That is false.** `idealSheafPullbackIsoOfIsoTarget g β h hh` is by definition
`Stacks.Conormal.pullbackIdealSheafIsoOfCompEq g β.hom h hh`, and
`Stacks.Conormal.OpenFactorizations.generator_eq_of_compEq` describes *that* isomorphism's inverse
on a unit generator already — it carries the unit generator of `g^* I(g)` named by a section `x`
to the unit generator of `h^* I(h)` named by the section `y` with
`Stacks.Conormal.OpenFactorizations.idealRestrictHomOfCompEq y = x`, modulo two restriction maps
which over the top open are the identity. Together with
`Stacks.Conormal.OpenFactorizations.idealRestrictHomOfCompEq_comp_ι` and the injectivity of the
inclusion of an ideal sheaf (`Stacks.Conormal.Locality.idealSheaf_section_injective`), that pins
`y` down by its image in the structure sheaf. So the factor needed no new mathematics; it needed
reading `ConormalOpenFactorizations`.

## Route

Everything is a transport of opens along two equalities that hold but not definitionally:
`Scheme.Opens.ι_preimage_self` (`O.ι ⁻¹ᵁ O = ⊤`) at two different schemes. Five reading lemmas do
the work:

* `val_app_eqToHom` — naturality of a morphism of sheaves of modules along an equality of opens;
* `map_map` and `map_self` — two restriction maps compose, and a restriction map along a hom from
  an open to itself is the identity on sections;
* `restrict_val_map` and `pushforward_val_map` — the restriction maps of a restriction and of a
  direct image are restriction maps of the underlying module, both by `rfl`;
* `unit_app_top_of_eq` — the one place the three transports meet: the unit of `g^* ⊣ g_*` read over
  an open equal to `⊤`, with the correcting restriction maps on the other side, is the unit over
  `⊤`.

`rw` is used only inside those helpers, where the goal is written in this file's own spelling. At
the call sites it is unusable, for the reason the Engine's docstring records: the hypotheses
imported from `Conormal.LocalityGenerator` and `ConormalOpenFactorizations` display their maps as
`CategoryTheory.ConcreteCategory.hom` while this file writes `ModuleCat.Hom.hom`, and `rw` is
syntactic. The two are definitionally equal, so `Eq.trans`, `congrArg` and `exact` cross the
boundary without comment; `rw` reports "did not find an occurrence" on a pattern that is present.
Every step at a call site is therefore a `refine Eq.trans (congrArg …) ?_` with the function
written out in full — `congrArg _` makes no progress here, as the Engine's docstring also records.

## What is not done

* **No clause of [Stacks, Tag 01R3] or [Stacks, Tag 08S2] is discharged and no `stacks` attribute
  is attached.** What is proved is the *hypothesis* of a generator formula, not the formula: to
  reach the part (2) assertion the result of
  `Stacks.Conormal.CotangentAppIsoGenerator.affineSectionsIsoCotangent_apply` must still be fed
  the affine-model data `x`, `hxy` and `hax`, which name the ambient ideal element.
* **No reduction of the quantifier over closed-immersion factorizations.**
* **Nothing about the square of the ideal or epimorphy of the quotient map.**

## Universe situation

A single universe `u`, as in the tagged statements.

## Vocabulary

The conormal quotient map of Tag 01R3 is `Stacks.Conormal.conormalQuotientMap`
(`StacksDraft.AlgebraicGeometry.F3.Conormal.IdealSheafComparison`).

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Tag08S2Locality

/-! ### Reading restriction maps and transports of opens -/

/-- **Naturality of a morphism of sheaves of modules along an equality of opens.** Discharged by
`subst`, after which the transport is a restriction map along the identity. -/
theorem val_app_eqToHom {Y : Scheme.{u}} {M N : Y.Modules} (p : M ⟶ N) {W W' : Y.Opens}
    (h : W = W') (t : M.val.obj (.op W')) :
    (p.val.app (.op W)).hom ((M.val.map (eqToHom h).op).hom t) =
      (N.val.map (eqToHom h).op).hom ((p.val.app (.op W')).hom t) := by
  subst h
  simp

/-- Two restriction maps compose to the restriction map along the composite. -/
theorem map_map {Y : Scheme.{u}} (M : Y.Modules) {a b c : Y.Opens} (h₁ : a ⟶ b) (h₂ : b ⟶ c)
    (z : M.val.obj (.op c)) :
    (M.val.map h₁.op).hom ((M.val.map h₂.op).hom z) = (M.val.map (h₁ ≫ h₂).op).hom z := by
  rw [← PresheafOfModules.map_comp_apply]
  rfl

/-- **A restriction map along any hom from an open to itself is the identity on sections.** The
hom is an argument rather than `𝟙`: the opens produced by the transports below are definitionally
but not syntactically equal to one another, and homs in a poset category agree by proof
irrelevance, so passing the hom lets unification identify the two opens first. This is
`Stacks.Conormal.AffineShape.map_eqToHom_self` in the `val.map` spelling. -/
theorem map_self {Y : Scheme.{u}} (M : Y.Modules) {a : Y.Opens} (g : a ⟶ a)
    (z : M.val.obj (.op a)) : (M.val.map g.op).hom z = z :=
  Stacks.Conormal.AffineShape.map_eqToHom_self M rfl z

/-- A composite of morphisms of sheaves of modules, read on sections. -/
theorem comp_val_app {Y : Scheme.{u}} {M N P : Y.Modules} (φ : M ⟶ N) (ψ : N ⟶ P)
    (W : Y.Opens) (t : M.val.obj (.op W)) :
    ((φ ≫ ψ).val.app (.op W)).hom t = (ψ.val.app (.op W)).hom ((φ.val.app (.op W)).hom t) :=
  rfl

/-- The restriction maps of a direct image are the restriction maps of the source module. -/
theorem pushforward_val_map {A B : Scheme.{u}} (g : A ⟶ B) (M : A.Modules)
    {a b : B.Opens} (hab : a ⟶ b) (hpre : g ⁻¹ᵁ a ≤ g ⁻¹ᵁ b)
    (z : M.val.obj (.op (g ⁻¹ᵁ b))) :
    (((Scheme.Modules.pushforward g).obj M).val.map hab.op).hom z =
      (M.val.map (homOfLE hpre).op).hom z :=
  rfl

/-- The restriction maps of a restriction to an open are the restriction maps of the module,
between the images of the two opens. -/
theorem restrict_val_map {Y : Scheme.{u}} (O : Y.Opens) (M : Y.Modules)
    {a b : O.toScheme.Opens} (g : a ⟶ b) (hab : O.ι ''ᵁ a ≤ O.ι ''ᵁ b)
    (z : M.val.obj (.op (O.ι ''ᵁ b))) :
    (((Scheme.Modules.restrictFunctor O.ι).obj M).val.map g.op).hom z =
      (M.val.map (homOfLE hab).op).hom z :=
  rfl

/-- A restriction map of a restriction to an open, after a restriction map of the module, is a
single restriction map of the module. -/
private theorem restrict_map_map {Y : Scheme.{u}} (O : Y.Opens) (M : Y.Modules)
    {a b : O.toScheme.Opens} (g : a ⟶ b) {c : Y.Opens} (h : O.ι ''ᵁ b ⟶ c) (k : O.ι ''ᵁ a ⟶ c)
    (z : M.val.obj (.op c)) :
    (((Scheme.Modules.restrictFunctor O.ι).obj M).val.map g.op).hom ((M.val.map h.op).hom z) =
      (M.val.map k.op).hom z :=
  (restrict_val_map O M g (O.ι.image_mono (leOfHom g)) _).trans (map_map _ _ _ _)

/-- `val_app_eqToHom` at the unit of `g^* ⊣ g _*`, with the correcting restriction map on the
right written as a restriction map of `g^* M` rather than of `g _* g^* M`. The two are the same
map by `pushforward_val_map`, and naming the lemma puts that single definitional step in one
place. -/
theorem unit_val_app_eqToHom {A B : Scheme.{u}} (g : A ⟶ B) (M : B.Modules)
    {W W' : B.Opens} (h : W = W') (hp : g ⁻¹ᵁ W ≤ g ⁻¹ᵁ W') (t : M.val.obj (.op W')) :
    (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app (.op W)).hom
        ((M.val.map (eqToHom h).op).hom t) =
      (((Scheme.Modules.pullback g).obj M).val.map (homOfLE hp).op).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app
          (.op W')).hom t) :=
  val_app_eqToHom _ h t

/-- **The unit of `g^* ⊣ g _*` over an open equal to `⊤`, corrected by two restriction maps, is
the unit over `⊤`.** This is the shape in which the generator formula for the locality comparison
meets the engine: the comparison is stated over an open which is `⊤` but not definitionally, and
the two correcting homs composed with the unit's own restriction map form a hom from `⊤` to
itself, which `map_self` deletes. -/
theorem unit_app_top_of_eq {A B : Scheme.{u}} (g : A ⟶ B) (M : B.Modules)
    {W : B.Opens} (hW : W = ⊤) {W₀ : A.Opens} (e1 : (⊤ : A.Opens) ⟶ W₀) (e2 : W₀ ⟶ g ⁻¹ᵁ W)
    (t : M.val.obj (.op ⊤)) :
    (((Scheme.Modules.pullback g).obj M).val.map e1.op).hom
        ((((Scheme.Modules.pullback g).obj M).val.map e2.op).hom
          ((((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app (.op W)).hom
            ((M.val.map (eqToHom hW).op).hom t))) =
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app (.op ⊤)).hom t := by
  rw [unit_val_app_eqToHom g M hW (le_of_eq (congrArg _ hW))]
  refine Eq.trans (map_map _ _ _ _) ?_
  refine Eq.trans (map_map _ _ _ _) ?_
  exact map_self _ _ _

/-! ### The locality comparison over the top open -/

section Locality

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
  (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i)
  (O : U.toScheme.Opens)

/-- **The generator formula for `Stacks.Conormal.Locality.conormalSheafRestrictIso` over the top
open.** For an immersion `i : Z ⟶ X`, any closed-immersion factorization `i' : Z ⟶ U` of it and
any open `O` of `U`, the locality comparison carries the restriction to `(i' ⁻¹ᵁ O).ι ''ᵁ ⊤` of
the quotient generator attached to a section `y` of the ideal sheaf of `i'` over `O` to the unit
generator attached to the matching section of the ideal sheaf of `i' ∣_ O`.

`Stacks.Conormal.Locality.conormalSheafRestrictIso_unit_app` is this statement over the open
`(i' ⁻¹ᵁ O).ι ⁻¹ᵁ (i' ⁻¹ᵁ O)`, which is `⊤` by `AlgebraicGeometry.Scheme.Opens.ι_preimage_self`
but not definitionally — and `⊤` is where the part (2) engine reads its sections, so this
transport is what connects the two. Three applications of `val_app_eqToHom`, at the comparison
itself, at `Stacks.Conormal.Restriction.restrictIdealSheafIso'` and at the unit, with
`unit_app_top_of_eq` collapsing the correcting restriction maps. -/
theorem conormalSheafRestrictIso_unit_app_top
    (y : (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.obj (.op O)) :
    ((Stacks.Conormal.Locality.conormalSheafRestrictIso i U i' hfac O).hom.val.app
          (.op ⊤)).hom
        (((Stacks.Conormal.conormalSheaf i).val.map
            (homOfLE (Scheme.Opens.ι_image_top (i' ⁻¹ᵁ O)).le).op).hom
          (((Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (.op O)).hom y)) =
      (((Scheme.Modules.pullbackPushforwardAdjunction (i' ∣_ O)).unit.app
          (Stacks.ClosedImmersion.idealSheaf (i' ∣_ O).toLRSHom.toShHom)).val.app (.op ⊤)).hom
        (((Stacks.Conormal.Restriction.restrictIdealSheafIso' i' O).hom.val.app (.op ⊤)).hom
          (((Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.map
            (homOfLE (Scheme.Opens.ι_image_top O).le).op).hom y)) := by
  have h0 : ((i' ⁻¹ᵁ O).ι ⁻¹ᵁ (i' ⁻¹ᵁ O)) = (⊤ : (i' ⁻¹ᵁ O).toScheme.Opens) :=
    Scheme.Opens.ι_preimage_self _
  have h1 : (O.ι ⁻¹ᵁ O) = (⊤ : O.toScheme.Opens) := Scheme.Opens.ι_preimage_self _
  have key := Stacks.Conormal.Locality.conormalSheafRestrictIso_unit_app i U i' hfac O y
  have nat := val_app_eqToHom
    (Stacks.Conormal.Locality.conormalSheafRestrictIso i U i' hfac O).hom h0.symm
      (((Stacks.Conormal.conormalSheaf i).val.map
          (homOfLE ((i' ⁻¹ᵁ O).ι.image_preimage_le (i' ⁻¹ᵁ O))).op).hom
        (((Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (.op O)).hom y))
  have harg : (((Scheme.Modules.restrictFunctor (i' ⁻¹ᵁ O).ι).obj
        (Stacks.Conormal.conormalSheaf i)).val.map (eqToHom h0.symm).op).hom
      (((Stacks.Conormal.conormalSheaf i).val.map
          (homOfLE ((i' ⁻¹ᵁ O).ι.image_preimage_le (i' ⁻¹ᵁ O))).op).hom
        (((Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (.op O)).hom y)) =
      ((Stacks.Conormal.conormalSheaf i).val.map
          (homOfLE (Scheme.Opens.ι_image_top (i' ⁻¹ᵁ O)).le).op).hom
        (((Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (.op O)).hom y) := by
    exact restrict_map_map (i' ⁻¹ᵁ O) (Stacks.Conormal.conormalSheaf i) (eqToHom h0.symm) _ _ _
  rw [harg] at nat
  rw [key] at nat
  refine nat.trans ?_
  have hy : (((Scheme.Modules.restrictFunctor O.ι).obj
        (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom)).val.map (eqToHom h1).op).hom
        (((Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.map
          (homOfLE (Scheme.Opens.ι_image_top O).le).op).hom y) =
      ((Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.map
        (homOfLE (O.ι.image_preimage_le O)).op).hom y := by
    exact restrict_map_map O (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom)
      (eqToHom h1) _ _ _
  have hρ := val_app_eqToHom (Stacks.Conormal.Restriction.restrictIdealSheafIso' i' O).hom h1
    (((Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.map
      (homOfLE (Scheme.Opens.ι_image_top O).le).op).hom y)
  rw [hy] at hρ
  rw [hρ]
  exact unit_app_top_of_eq (i' ∣_ O) _ h1 (eqToHom h0.symm)
    (eqToHom (Stacks.Conormal.Locality.preimage_ι_preimage_eq i' O)) _

end Locality

/-! ### The engine's first factor over the top open -/

/-- **`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso` over the top open.**
Preceded by the restriction map along `V.ι ''ᵁ ⊤ = V` — which is how the part (2) engine reads a
section of `j _* M` over `V` as a global section of its restriction to `V` — the comparison is the
single restriction map of `M` from `j ⁻¹ᵁ V` down to `(j ⁻¹ᵁ V).ι ''ᵁ ⊤`.

`Stacks.Conormal.Restriction.restrictPushforwardIso_hom_app` supplies the comparison on sections
(it is a restriction map along `image_morphismRestrict_preimage`); the two restriction maps then
compose. -/
theorem restrictPushforward_top {A B : Scheme.{u}} (j : A ⟶ B) (V : B.Opens) (M : A.Modules)
    (s : M.val.obj (.op (j ⁻¹ᵁ V))) :
    ((((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso j V).app
            M).hom.val.app (.op ⊤)).hom
        ((((Scheme.Modules.pushforward j).obj M).val.map
          (eqToHom V.ι_image_top).op).hom s)) =
      (M.val.map (homOfLE (Scheme.Opens.ι_image_top (j ⁻¹ᵁ V)).le).op).hom s := by
  refine Eq.trans (Stacks.Conormal.Restriction.restrictPushforwardIso_hom_app j V M ⊤ _) ?_
  refine Eq.trans (congrArg (fun z => (M.val.map
      (eqToHom (image_morphismRestrict_preimage j V ⊤)).op).hom z)
    (pushforward_val_map j M (eqToHom V.ι_image_top)
      (j.preimage_mono (le_of_eq V.ι_image_top)) s)) ?_
  exact map_map _ _ _ _

/-! ### The hypothesis `hc` at the two shapes of [Stacks, Tag 01R3] -/

section Shapes

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
  (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i)

/-- **The hypothesis `hc` of the part (2) engine, at the shape
`Stacks.Conormal.CotangentAppIso.pushforwardConormalSectionsIsoCotangent` feeds it.** There the
locality comparison is `Stacks.Conormal.Locality.conormalSheafRestrictIso` at an open `O` of the
factorization's target, and the section of `i' _* C(i)` over `O` whose generator formula is wanted
is the quotient generator of a section `y₀` of the ideal sheaf of `i'`.

This is `restrictPushforward_top` followed by `conormalSheafRestrictIso_unit_app_top`, and nothing
else: the engine's first factor and the locality comparison are the only two maps involved.

Feeding this to `Stacks.Conormal.CotangentAppIsoGenerator.affineSectionsIsoCotangent_apply`
discharges the `hc` argument with `y` the section of the ideal sheaf of `i' ∣_ O` named by `y₀`,
which `Stacks.Conormal.Locality.restrictIdealSheafIso'_app_ι` identifies through its image in the
structure sheaf. -/
theorem hc_conormalSheafRestrictIso (O : U.toScheme.Opens)
    (y₀ : (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.obj (.op O)) :
    ((Stacks.Conormal.Locality.conormalSheafRestrictIso i U i' hfac O).hom.val.app
          (.op ⊤)).hom
        ((((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso
            i' O).app (Stacks.Conormal.conormalSheaf i)).hom.val.app (.op ⊤)).hom
          ((((Scheme.Modules.pushforward i').obj
              (Stacks.Conormal.conormalSheaf i)).val.map
            (eqToHom O.ι_image_top).op).hom
            (((Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (.op O)).hom y₀))) =
      (((Scheme.Modules.pullbackPushforwardAdjunction (i' ∣_ O)).unit.app
          (Stacks.ClosedImmersion.idealSheaf (i' ∣_ O).toLRSHom.toShHom)).val.app (.op ⊤)).hom
        (((Stacks.Conormal.Restriction.restrictIdealSheafIso' i' O).hom.val.app (.op ⊤)).hom
          (((Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.map
            (homOfLE (Scheme.Opens.ι_image_top O).le).op).hom y₀)) :=
  (congrArg (fun z => ((Stacks.Conormal.Locality.conormalSheafRestrictIso
        i U i' hfac O).hom.val.app (.op ⊤)).hom z)
      (restrictPushforward_top i' O (Stacks.Conormal.conormalSheaf i)
        (((Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (.op O)).hom y₀))).trans
    (conormalSheafRestrictIso_unit_app_top i U i' hfac O y₀)

/-- **The hypothesis `hc` of the part (2) engine, at the shape
`Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent` feeds it** — the shape
`StacksDraft.AlgebraicGeometry.F3.DiagonalQuotientPresentation.Basic` instantiates at the
diagonal. There the locality comparison is
`Stacks.Conormal.AffineShape.conormalSheafRestrictIsoOfLe` at an open `V ≤ U` of the *ambient*
scheme, which is `conormalSheafRestrictIso` at `U.ι ⁻¹ᵁ V` followed by the inverse of
`Stacks.Conormal.AffineCotangent.Transport.idealSheafPullbackIsoOfIsoTarget`.

The section of the ideal sheaf of `i ∣_ V` that the quotient generator of `y₀` is carried to is
determined by its image in the structure sheaf, and `hy` is exactly that determination — the shape
`Stacks.Conormal.OpenFactorizations.idealRestrictHomOfCompEq_comp_ι` produces, so no further
bookkeeping is needed to use it. The transport `hVeq` of the preimage open is the only trace of
the factorization hypothesis left in the statement.

The second factor is handled by `Stacks.Conormal.OpenFactorizations.generator_eq_of_compEq`, whose
two restriction maps are homs from `⊤` to itself here and are deleted by `map_self`; see the
module docstring, which explains why this factor does have an elementwise description. -/
theorem hc_conormalSheafRestrictIsoOfLe (V : X.Opens) (hVU : V ≤ U)
    (hVeq : i ⁻¹ᵁ V = i' ⁻¹ᵁ (U.ι ⁻¹ᵁ V))
    (y₀ : (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.obj
      (.op (U.ι ⁻¹ᵁ V)))
    (y : (Stacks.ClosedImmersion.idealSheaf (i ∣_ V).toLRSHom.toShHom).val.obj (.op ⊤))
    (hy : ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
            (i' ∣_ (U.ι ⁻¹ᵁ V)).toLRSHom.toShHom))).val.app (.op ⊤)).hom
          (((Stacks.Conormal.Restriction.restrictIdealSheafIso' i' (U.ι ⁻¹ᵁ V)).hom.val.app
              (.op ⊤)).hom
            (((Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.map
              (homOfLE (Scheme.Opens.ι_image_top (U.ι ⁻¹ᵁ V)).le).op).hom y₀)) =
        ((SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
            (Scheme.Opens.isoOfLE hVU).hom.toLRSHom.toShHom)).val.app (.op ⊤)).hom
          (((kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
            (i ∣_ V).toLRSHom.toShHom))).val.app (.op ⊤)).hom y)) :
    ((Stacks.Conormal.AffineShape.conormalSheafRestrictIsoOfLe
            i U i' hfac V hVU).hom.val.app (.op ⊤)).hom
        ((((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso
            i V).app (Stacks.Conormal.conormalSheaf i)).hom.val.app (.op ⊤)).hom
          ((((Scheme.Modules.pushforward i).obj
              (Stacks.Conormal.conormalSheaf i)).val.map
            (eqToHom V.ι_image_top).op).hom
            (((Stacks.Conormal.conormalSheaf i).val.map (eqToHom hVeq).op).hom
              (((Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app
                (.op (U.ι ⁻¹ᵁ V))).hom y₀)))) =
      (((Scheme.Modules.pullbackPushforwardAdjunction (i ∣_ V)).unit.app
          (Stacks.ClosedImmersion.idealSheaf (i ∣_ V).toLRSHom.toShHom)).val.app (.op ⊤)).hom
        y := by
  subst hfac
  refine Eq.trans (congrArg (fun z =>
      ((Stacks.Conormal.AffineShape.conormalSheafRestrictIsoOfLe
            (i' ≫ U.ι) U i' rfl V hVU).hom.val.app (.op ⊤)).hom
        ((((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso
            (i' ≫ U.ι) V).app
              (Stacks.Conormal.conormalSheaf (i' ≫ U.ι))).hom.val.app (.op ⊤)).hom
          ((((Scheme.Modules.pushforward (i' ≫ U.ι)).obj
              (Stacks.Conormal.conormalSheaf (i' ≫ U.ι))).val.map
            (eqToHom V.ι_image_top).op).hom z)))
    (map_self (Stacks.Conormal.conormalSheaf (i' ≫ U.ι)) (eqToHom hVeq) _)) ?_
  refine Eq.trans (congrArg (fun z =>
      ((Stacks.Conormal.AffineShape.conormalSheafRestrictIsoOfLe
            (i' ≫ U.ι) U i' rfl V hVU).hom.val.app (.op ⊤)).hom z)
    (restrictPushforward_top (i' ≫ U.ι) V (Stacks.Conormal.conormalSheaf (i' ≫ U.ι)) _)) ?_
  refine Eq.trans (Stacks.Conormal.CotangentAppIsoGenerator.trans_val_app _ _ _ _) ?_
  refine Eq.trans (congrArg
      (fun z => ((Stacks.Conormal.AffineCotangent.Transport.idealSheafPullbackIsoOfIsoTarget
          (i' ∣_ (U.ι ⁻¹ᵁ V)) (Scheme.Opens.isoOfLE hVU) ((i' ≫ U.ι) ∣_ V)
            (Stacks.Conormal.AffineShape.morphismRestrict_comp_isoOfLE U i' V
              hVU)).symm.hom.val.app (.op ⊤)).hom z)
      (conormalSheafRestrictIso_unit_app_top (i' ≫ U.ι) U i' rfl (U.ι ⁻¹ᵁ V) y₀)) ?_
  have hxy : ((Stacks.Conormal.OpenFactorizations.idealRestrictHomOfCompEq
        (i' ∣_ (U.ι ⁻¹ᵁ V)) (Scheme.Opens.isoOfLE hVU).hom ((i' ≫ U.ι) ∣_ V)
        (Stacks.Conormal.AffineShape.morphismRestrict_comp_isoOfLE U i' V hVU)).val.app
        (.op ⊤)).hom y =
      ((Stacks.Conormal.Restriction.restrictIdealSheafIso' i' (U.ι ⁻¹ᵁ V)).hom.val.app
          (.op ⊤)).hom
        (((Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.map
          (homOfLE (Scheme.Opens.ι_image_top (U.ι ⁻¹ᵁ V)).le).op).hom y₀) := by
    refine Stacks.Conormal.Locality.idealSheaf_section_injective (i' ∣_ (U.ι ⁻¹ᵁ V)) ⊤ ?_
    refine Eq.trans ?_ hy.symm
    exact congrArg (fun g => ModuleCat.Hom.hom g y)
      (congr($(Stacks.Conormal.OpenFactorizations.idealRestrictHomOfCompEq_comp_ι
        (i' ∣_ (U.ι ⁻¹ᵁ V)) (Scheme.Opens.isoOfLE hVU).hom ((i' ≫ U.ι) ∣_ V)
        (Stacks.Conormal.AffineShape.morphismRestrict_comp_isoOfLE U i' V hVU)).val.app
          (.op ⊤)))
  have hgen := Stacks.Conormal.OpenFactorizations.generator_eq_of_compEq
    (i' ∣_ (U.ι ⁻¹ᵁ V)) (Scheme.Opens.isoOfLE hVU).hom ((i' ≫ U.ι) ∣_ V)
    (Stacks.Conormal.AffineShape.morphismRestrict_comp_isoOfLE U i' V hVU)
    ⊤ ⊤ le_rfl le_rfl y _ hxy
  have hT0 : (⊤ : (i' ⁻¹ᵁ (U.ι ⁻¹ᵁ V)).toScheme.Opens) ⟶
      (⊤ : (i' ⁻¹ᵁ (U.ι ⁻¹ᵁ V)).toScheme.Opens) := homOfLE le_rfl
  exact (((map_self _ hT0 _).symm.trans hgen).trans
    ((map_self _ hT0 _).trans (comp_val_app _ _ _ _))).symm

end Shapes

end Stacks.Tag08S2Locality

end
