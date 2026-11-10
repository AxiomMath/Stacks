module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import StacksFrontier.AlgebraicGeometry.Fibres.SectionsFromFibre
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.InfinitesimalIdempotentTower
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine
public import StacksFrontier.RingTheory.AdicCompletion.IntertwinedFiltration
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Stalk

/-!
# The stalk form of the theorem on formal functions, for the structure sheaf in degree zero

Let `f : X ⟶ Y` be a morphism of schemes and let `y` be a point of `Y`. [Stacks, Tag 02OD] — the
theorem on formal functions read at a stalk — says that for `Y` locally Noetherian, `f` proper
and `ℱ` coherent there is an isomorphism of `𝒪^∧_{Y,y}`-modules

  `(R ᵖ f_* ℱ) _y ^∧ ≅ lim_n H ᵖ (X_n, ℱ_n)`,

where `X_n` is the `n`-th infinitesimal neighbourhood of the fibre `X_y` and `ℱ_n = i_n ^* ℱ`.

This file sets up and *states* the case `p = 0`, `ℱ = 𝒪_X` of that conclusion,

  `(f_* 𝒪_X) _y ^∧ ≅ lim_n Γ(X_n, 𝒪_{X_n})`,

as the predicate `Stacks.FormalFunctions.IsFormalFunctionsStalk`, constructs the comparison map
of that statement — the restriction maps `(f_* 𝒪_X)_y ⟶ Γ(X_n, 𝒪_{X_n})` exist unconditionally,
`Stacks.FormalFunctions.infinitesimalStalkRestrict` — reduces the predicate to the two uniform
bounds of [Stacks, Tag 02OB] read at the stalk
(`Stacks.FormalFunctions.isFormalFunctionsStalk_of_uniformBounds`), and proves the reduction of
[Stacks, Tag 0G7X] to it. The two bounds are supplied, for `f` proper onto a locally Noetherian
base, in `StacksFrontier/AlgebraicGeometry/FormalFunctions/StalkFormalFunctionsFrom02O8.lean`, so
the predicate **is** proved there (`isFormalFunctionsStalk_of_isProper`). The declarations in
*this* file carry their inputs as named hypotheses and therefore carry **no** `@[stacks 0G7X]`
attribute; the tag itself is
`Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_isProper`, which adds the
[Stacks, Tag 0A0P] reduction of the general case to the locally Noetherian one.

## Main definitions

* `Stacks.FormalFunctions.infinitesimalBaseRingHom` — the ring map
  `𝒪_{Y,y} ⟶ Γ(X_n, 𝒪)` through which the local ring acts on everything on `X_n`. It kills
  `𝔪_y ^ n` (`infinitesimalBaseRingHom_eq_zero`) and is compatible with the transition
  morphisms (`infinitesimalBaseRingHom_transition`).
* `Stacks.FormalFunctions.infinitesimalFunctions` and
  `Stacks.FormalFunctions.infinitesimalFunctionsMap` — the inverse system
  `n ↦ Γ(X_n, 𝒪_{X_n})` of `𝒪_{Y,y}`-modules and its transition maps.
* `Stacks.FormalFunctions.pushforwardStalkModule` — the stalk `(f_* 𝒪_X)_y`, as an
  `𝒪_{Y,y}`-module.
* `Stacks.FormalFunctions.infinitesimalStalkRestrict` — **the canonical restriction map**
  `(f_* 𝒪_X)_y ⟶ Γ(X_n, 𝒪_{X_n})`, `𝒪_{Y,y}`-linear, taking the germ at `y` of a function on
  `f ⁻¹ U` to its restriction to `X_n`. It exists for every morphism `f`, with no hypothesis,
  because `X_n` lies over *every* open neighbourhood of `y`.
* `Stacks.FormalFunctions.stalkCompletionComparison` — the comparison map
  `(f_* 𝒪_X)_y ^∧ ⟶ lim_n Γ(X_n, 𝒪_{X_n})` assembled from a compatible family of restriction
  maps, and `Stacks.FormalFunctions.canonicalStalkComparison` — the same assembled from
  `infinitesimalStalkRestrict`.
* `Stacks.FormalFunctions.IsFormalFunctionsStalk` — the conclusion of [Stacks, Tag 02OD] at
  `p = 0` for the structure sheaf, in the shape just described: there are restriction maps
  `(f_* 𝒪_X)_y ⟶ Γ(X_n, 𝒪_{X_n})`, taking the germ of a function on `f ⁻¹ U` to its restriction
  to `X_n`, whose assembled comparison from the completed stalk is bijective.

## Main results

* `Stacks.FormalFunctions.pow_smul_top_le_ker` — `𝔪_y ^ n` annihilates `Γ(X_n, 𝒪_{X_n})`, hence
  kills the image of `𝔪_y ^ n (f_* 𝒪_X)_y` under any `𝒪_{Y,y}`-linear map to it. This is what
  makes the comparison map exist at all, and it is proved here rather than assumed.
* `Stacks.FormalFunctions.exists_apply_eq_proj` — every component of the comparison map is the
  corresponding restriction map applied to an element of the *uncompleted* stalk. This is the
  step "the map to `H⁰(X_y, 𝒪)` factors through the quotient by `𝔪_y`, so `e` already lifts to
  the uncompleted stalk" of the proof of [Stacks, Tag 0G7X].
* `Stacks.FormalFunctions.exists_towerLimit_of_succ` — a family compatible with the successor
  transitions lies in the inverse limit.
* `Stacks.FormalFunctions.infinitesimalRestrict_app` — the canonical restriction map carries the
  structure map of `f` on stalks to `infinitesimalBaseRingHom`. This is what makes it
  `𝒪_{Y,y}`-linear, and it is the defining square `i_n ≫ f = f_n ≫ c_n` of `X_n` read on
  sections.
* `Stacks.FormalFunctions.isFormalFunctionsStalk_of_uniformBounds` — **[Stacks, Tag 02OD] at
  `p = 0` for the structure sheaf, reduced to the two clauses of [Stacks, Tag 02OB] read at the
  stalk**: a uniform bound on the kernels of the canonical restriction maps and the stabilization
  of the images in the tower. The third hypothesis of the commutative-algebra core,
  `𝔪_y ^ n (f_* 𝒪_X)_y ⊆ ker`, is proved here and not assumed.
* `Stacks.FormalFunctions.exists_section_appLE_fiber_eq_of_isFormalFunctionsStalk` — **the
  reduction of [Stacks, Tag 0G7X] to the statement above.** An idempotent of `Γ(X_y, 𝒪)` is the
  restriction of a function on `f ⁻¹ U` for some open neighbourhood `U` of `y`, granted
  `IsFormalFunctionsStalk f y`.
* `Stacks.FormalFunctions.extendsOverNeighbourhood_of_uniformBounds` — the two previous results
  composed: [Stacks, Tag 0G7X] in the shape its consumers carry, from the two uniform bounds.

## Implementation notes

**What is stated and what is not.** `IsFormalFunctionsStalk` is the conclusion of
[Stacks, Tag 02OD] specialized to `p = 0` and `ℱ = 𝒪_X`, which is the case the proof of
[Stacks, Tag 0G7X] uses, and it is stated for an arbitrary morphism `f` — the source's standing
hypotheses (`Y` locally Noetherian, `f` proper) are *not* built into the predicate, so the
reduction below is stated at exactly the hypotheses [Stacks, Tag 0G7X] carries and the predicate
records which input is owed. Two shortfalls relative to the tag are recorded here rather than
hidden:

* the general `p` and general coherent `ℱ` are not stated, because the library has no map
  `H ᵖ (X, ℱ) ⟶ H ᵖ (X_n, ℱ_n)` on cohomology along `i_n` — the edge map of the Leray spectral
  sequence for `i_n` is available abstractly as `Stacks.Cohomology.RightDerivedEdge.edge` but is
  not instantiated at `(i_n)_*` and `Γ`, so the inverse system of the tag's right-hand side
  cannot yet be formed in positive degrees;
* the isomorphism is stated as `𝒪_{Y,y}`-linear, not `𝒪^∧_{Y,y}`-linear. Both sides carry an
  `𝒪^∧_{Y,y}`-action — the left by `AdicCompletion`, the right because `Γ(X_n, 𝒪)` is killed by
  `𝔪_y ^ n` — and the predicate does not assert that the comparison respects it.

**What is proved and what remains.** The comparison map of the tag is built here with no
hypothesis at all: `infinitesimalStalkRestrict`, assembled by `canonicalStalkComparison`. What
remains is its bijectivity, and `isFormalFunctionsStalk_of_uniformBounds` reduces that — through
`Stacks.IntertwinedFiltration.adicCompletionEquivTowerLimit`, the commutative-algebra core of
[Stacks, Tag 02OC] — to the two clauses of [Stacks, Tag 02OB] for the tower
`n ↦ Γ(X_n, 𝒪_{X_n})` with `M = (f_* 𝒪_X)_y` and `I = 𝔪_y`. Those two bounds were what was
missing, for two independent reasons, and **both are now discharged**.

*First*, the library's [Stacks, Tag 02OB]
(`Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient`) carries
[Stacks, Tag 02OA] as a hypothesis, which carries [Stacks, Tag 02O8]. Those links are now
joined, in
`StacksFrontier/AlgebraicGeometry/FormalFunctions/FormalFunctionsFrom02O8.lean`, so that 02OB and
02OC hold over the single hypothesis `h02O8`; and 02O8 itself,
`Stacks.Cohomology.FormalFunctions.isCohomologyReesFinite`, is proved unconditionally. Earlier
versions of this paragraph put [Stacks, Tag 0897] part (1) below 02O8 as a separate open link,
and then the sheaf-level identity `ReesSmulCompatible`; both have since been discharged. So
`IsFormalFunctionsStalk f y` IS proved for `f` proper onto a locally Noetherian base:
`Stacks.FormalFunctions.isFormalFunctionsStalk_of_isProper` of
`StacksFrontier/AlgebraicGeometry/FormalFunctions/StalkFormalFunctionsFrom02O8.lean`, with Tag 0G7X
there as `...extendsOverNeighbourhood_of_isLocallyNoetherian`.

*Second*, even granted 02OB, its statement is about the tower `n ↦ H⁰(X', 𝒪_{X'}/𝓘 ⁿ)` over an
affine base, not about `n ↦ Γ(X_n, 𝒪)` over the local ring, and transporting it needed two
identifications. **Both are now proved.**

* `Γ(X', 𝒪_{X'}) ≅ (f_* 𝒪_X)_y`, where `X' = X ×_Y Spec 𝒪_{Y,y}`. **This one is proved**, as
  `Stacks.FormalFunctions.exists_linearEquiv_pushforwardStalk_appTop_pullback` of
  `StacksFrontier/AlgebraicGeometry/FormalFunctions/PushforwardStalkBaseChange.lean`, for `f`
  quasi-compact and quasi-separated and with the normalisation that carries the pullback along
  `X' ⟶ X` of a section of `𝒪_X` over `f ⁻¹ᵁ U`, for *any* open neighbourhood `U` of `y`, to its
  germ at `y`; the surjectivity half, in the shape a consumer uses, is
  `Stacks.FormalFunctions.exists_appLE_eq_of_appTop_pullback`. That file does not route through
  flat base change for the direct image. It exhibits both sides as the localisation of
  `Γ(X, f ⁻¹ᵁ U₀)`, for an affine open `U₀ ∋ y`, at the image of the prime complement of `y`:
  the stalk by `AlgebraicGeometry.Scheme.pushforwardStalk_isLocalization`, and the global
  functions on the base change by Mathlib's
  `AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` — flatness of
  `Spec 𝒪_{Y,y} ⟶ Y` is `AlgebraicGeometry.flat_fromSpecStalk` — read through
  `Algebra.isLocalization_iff_isPushout`.

  An earlier note here said that the identification of the global sections of a quasi-coherent
  sheaf pulled back along `Spec 𝒪_{Y,y} ⟶ Y` with its stalk at `y` does not exist in this
  library. That was wrong: it is
  `AlgebraicGeometry.exists_fromSpecStalkSectionsStalkLinearEquiv` of
  `StacksFrontier/AlgebraicGeometry/PullbackSections/Stalk.lean`, which states the comparison
  `Γ(Spec 𝒪_{Y,y}, (Y.fromSpecStalk y)^* ℱ) ≅ ℱ_y` for quasi-coherent `ℱ` together with the
  normalisation carrying the pullback of a section over an affine `U ∋ y` to its germ at `y`. It
  is exactly the instantiation of `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` at
  `V = ⊤` that the note described as missing — legitimate because
  `⊤ ≤ (Spec 𝒪_{Y,y} ⟶ Y) ⁻¹ U`, which is `le_preimage_fromSpecStalk_of_mem` below — with the
  resulting tensor product identified with the stalk by uniqueness of localisations. So the
  route through flat base change for the direct image
  (`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.Affine.isIso_baseChangeNatTrans_of_flat`,
  [Stacks, Tag 02KH] part (1) at `i = 0`) is open as well; the file above takes the shorter one.
* `Γ(X_n, 𝒪_{X_n}) ≅ H⁰(X', 𝒪_{X'}/𝔪_y ⁿ 𝒪_{X'})`. **This one is proved too**, in two steps.
  `Stacks.FormalFunctions.infinitesimalNeighbourhoodIsoSubscheme` of
  `StacksFrontier/AlgebraicGeometry/FormalFunctions/InfinitesimalBaseIdeal.lean` identifies `X_n`
  with the closed subscheme of `X'` cut out by `(𝔪_y 𝒪_{X'}) ^ n` — the pasting of the two
  cartesian squares, `c_n` being by definition the closed immersion into `Spec 𝒪_{Y,y}` followed
  by `Spec 𝒪_{Y,y} ⟶ Y` — and carries the subscheme inclusion to `X_n ⟶ X'` and the inclusions
  of ideal-power subschemes to the transition morphisms. Then
  `Stacks.Cohomology.FormalFunctions.idealPowerQuotientSubschemeIso` of
  `StacksFrontier/AlgebraicGeometry/FormalFunctions/IdealPowerQuotientSections.lean` identifies
  `𝒪_{X'}/𝓘 ⁿ` with `(i_n)_* 𝒪` of that subscheme, together with the two squares the tower needs
  — naturality against `idealPowerQuotientDrop`, and compatibility with the quotient projection.

Routing through [Stacks, Tag 087U] instead of 02OC does not work:
`Stacks.Algebraization.isIso_cohomologyToLimit_of_isProper` requires the base ring to be
`J`-adically complete, and `𝒪_{Y,y}` is not. Its finiteness hypothesis `hfin` would indeed be
dischargeable from [Stacks, Tag 02O6]
(`AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology`, which is unconditional), but
completeness is not, so 087U would
compute `H⁰` of the base change to `Spec 𝒪^∧_{Y,y}` rather than the completed stalk and would
leave strictly more to do.

**The module structures.** `Γ(X_n, 𝒪)` and `(f_* 𝒪_X)_y` are rings, and they are made
`𝒪_{Y,y}`-modules through `infinitesimalBaseRingHom` and through the stalk map of the comorphism
of `f`. Both are introduced on a type synonym (`infinitesimalFunctions`,
`pushforwardStalkModule`) so that the `𝒪_{Y,y}`-action is a global instance and does not have to
be carried by `letI` into every statement, and so that it cannot collide with the ring's action
on itself.

## References

* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 0G7X](https://stacks.math.columbia.edu/tag/0G7X)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace Topology
open Stacks.IntertwinedFiltration

universe u

namespace Stacks.FormalFunctions

variable {X Y : Scheme.{u}}

/-! ### The base ring map of an infinitesimal neighbourhood -/

/-- **The ring map `𝒪_{Y,y} ⟶ Γ(X_n, 𝒪)`.** It is the composite of the quotient map
`𝒪_{Y,y} ⟶ 𝒪_{Y,y}/𝔪_y ^ n`, the identification of that ring with the global functions on its
spectrum, and the structure morphism `f_n : X_n ⟶ Spec (𝒪_{Y,y}/𝔪_y ^ n)`. It is through this
map that the local ring acts on everything on `X_n`. -/
public def infinitesimalBaseRingHom (f : X ⟶ Y) (y : Y) (n : ℕ) :
    Y.presheaf.stalk y →+* Γ(infinitesimalNeighbourhood f y n, ⊤) :=
  RingHom.comp
    (((Scheme.ΓSpecIso (stalkQuotient y n)).inv ≫
      (infinitesimalStructure f y n).appTop).hom)
    (toStalkQuotient y n).hom

/-- **The base ring map of `X_n` kills `𝔪_y ^ n`**, since the quotient map does. -/
public theorem infinitesimalBaseRingHom_eq_zero (f : X ⟶ Y) (y : Y) (n : ℕ)
    {r : Y.presheaf.stalk y} (hr : r ∈ stalkMaximalIdeal y ^ n) :
    infinitesimalBaseRingHom f y n r = 0 := by
  have h : (Ideal.Quotient.mk (stalkMaximalIdeal y ^ n)) r = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hr
  change (((Scheme.ΓSpecIso (stalkQuotient y n)).inv ≫
    (infinitesimalStructure f y n).appTop).hom) ((Ideal.Quotient.mk _) r) = 0
  rw [h, map_zero]

/-- **The base ring maps are compatible with the transition morphisms** `X_m ⟶ X_n` for
`m ≤ n`. -/
public theorem infinitesimalBaseRingHom_transition (f : X ⟶ Y) (y : Y) {m n : ℕ} (h : m ≤ n)
    (r : Y.presheaf.stalk y) :
    (infinitesimalTransition f y h).appTop.hom (infinitesimalBaseRingHom f y n r) =
      infinitesimalBaseRingHom f y m r := by
  have key : toStalkQuotient y n ≫ (Scheme.ΓSpecIso (stalkQuotient y n)).inv ≫
        (infinitesimalStructure f y n).appTop ≫ (infinitesimalTransition f y h).appTop =
      toStalkQuotient y m ≫ (Scheme.ΓSpecIso (stalkQuotient y m)).inv ≫
        (infinitesimalStructure f y m).appTop := by
    rw [← Scheme.Hom.comp_appTop, infinitesimalTransition_structure, Scheme.Hom.comp_appTop,
      show (baseTransition y h).appTop =
        (Spec.map (stalkQuotientFactor y h)).appTop from rfl,
      ← Scheme.ΓSpecIso_inv_naturality_assoc, ← Category.assoc,
      toStalkQuotient_comp_stalkQuotientFactor]
  exact ConcreteCategory.congr_hom key r

/-! ### The inverse system `n ↦ Γ(X_n, 𝒪)` of modules over the local ring -/

/-- **`Γ(X_n, 𝒪_{X_n})` as a module over the local ring `𝒪_{Y,y}`**, the scalars acting through
`infinitesimalBaseRingHom`. -/
public abbrev infinitesimalFunctions (f : X ⟶ Y) (y : Y) (n : ℕ) : Type u :=
  Γ(infinitesimalNeighbourhood f y n, ⊤)

/-- The `𝒪_{Y,y}`-module structure on `Γ(X_n, 𝒪_{X_n})`, the scalars acting through
`infinitesimalBaseRingHom`. -/
public instance moduleInfinitesimalFunctions (f : X ⟶ Y) (y : Y) (n : ℕ) :
    Module (Y.presheaf.stalk y) (infinitesimalFunctions f y n) :=
  Module.compHom (infinitesimalFunctions f y n) (infinitesimalBaseRingHom f y n)

/-- A scalar `r : 𝒪_{Y,y}` acts on `Γ(X_n, 𝒪_{X_n})` by multiplication with its image under
`infinitesimalBaseRingHom`. -/
public theorem infinitesimalFunctions_smul_def (f : X ⟶ Y) (y : Y) (n : ℕ)
    (r : Y.presheaf.stalk y) (x : infinitesimalFunctions f y n) :
    r • x = infinitesimalBaseRingHom f y n r * x :=
  rfl

/-- **The transition map `Γ(X_n, 𝒪) ⟶ Γ(X_m, 𝒪)` of the inverse system**, for `m ≤ n`:
restriction along the closed immersion `X_m ⟶ X_n`. -/
public def infinitesimalFunctionsMap (f : X ⟶ Y) (y : Y) (m n : ℕ) (h : m ≤ n) :
    infinitesimalFunctions f y n →ₗ[Y.presheaf.stalk y] infinitesimalFunctions f y m where
  toFun x := (infinitesimalTransition f y h).appTop.hom x
  map_add' a b := map_add _ a b
  map_smul' r x := by
    change (infinitesimalTransition f y h).appTop.hom
        (infinitesimalBaseRingHom f y n r * x) =
      infinitesimalBaseRingHom f y m r * (infinitesimalTransition f y h).appTop.hom x
    rw [map_mul, infinitesimalBaseRingHom_transition f y h r]

/-- The transition map `infinitesimalFunctionsMap` is the map on global sections of the
transition morphism `X_m ⟶ X_n`. -/
@[simp]
public theorem infinitesimalFunctionsMap_apply (f : X ⟶ Y) (y : Y) (m n : ℕ) (h : m ≤ n)
    (x : infinitesimalFunctions f y n) :
    infinitesimalFunctionsMap f y m n h x = (infinitesimalTransition f y h).appTop.hom x :=
  rfl

/-- The transition maps compose, because the transition morphisms do. -/
public theorem infinitesimalFunctionsMap_comp (f : X ⟶ Y) (y : Y) {k m n : ℕ} (h₁ : k ≤ m)
    (h₂ : m ≤ n) (h₃ : k ≤ n) (x : infinitesimalFunctions f y n) :
    infinitesimalFunctionsMap f y k m h₁ (infinitesimalFunctionsMap f y m n h₂ x) =
      infinitesimalFunctionsMap f y k n h₃ x := by
  change (infinitesimalTransition f y h₁).appTop.hom
      ((infinitesimalTransition f y h₂).appTop.hom x) =
    (infinitesimalTransition f y h₃).appTop.hom x
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, infinitesimalTransition_comp]

/-- The transition map at a reflexive inequality is the identity. -/
public theorem infinitesimalFunctionsMap_refl (f : X ⟶ Y) (y : Y) (n : ℕ) (h : n ≤ n)
    (x : infinitesimalFunctions f y n) : infinitesimalFunctionsMap f y n n h x = x := by
  change (infinitesimalTransition f y h).appTop.hom x = x
  rw [infinitesimalTransition_refl, Scheme.Hom.id_appTop]
  rfl

/-- **A family compatible with the successor transitions lies in the inverse limit.** -/
public theorem exists_towerLimit_of_succ (f : X ⟶ Y) (y : Y)
    (b : ∀ n, infinitesimalFunctions f y n)
    (hb : ∀ n, infinitesimalFunctionsMap f y n (n + 1) (Nat.le_succ n) (b (n + 1)) = b n) :
    ∃ z : towerLimit (infinitesimalFunctions f y) (infinitesimalFunctionsMap f y),
      (z : ∀ k, infinitesimalFunctions f y k) = b := by
  refine ⟨⟨b, ?_⟩, rfl⟩
  intro m n h
  induction n, h using Nat.le_induction with
  | base => exact infinitesimalFunctionsMap_refl f y m _ (b m)
  | succ n h ih =>
      refine ((infinitesimalFunctionsMap_comp f y h (Nat.le_succ n) _ (b (n + 1))).symm.trans
        ?_).trans ih
      exact congrArg (fun t => infinitesimalFunctionsMap f y m n h t) (hb n)

/-! ### The stalk of the direct image of the structure sheaf -/

/-- The direct image `f_* 𝒪_X` of the structure sheaf, as a presheaf of rings on `Y`. -/
public abbrev pushforwardStructurePresheaf (f : X ⟶ Y) := f.base _* X.presheaf

/-- The canonical ring map `𝒪_{Y,y} ⟶ (f_* 𝒪_X)_y` on stalks, induced by the comorphism
of `f`. -/
public def toPushforwardStalk (f : X ⟶ Y) (y : Y) :
    Y.presheaf.stalk y ⟶ (pushforwardStructurePresheaf f).stalk y :=
  (TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map f.c

/-- **The stalk `(f_* 𝒪_X)_y`, as a module over the local ring `𝒪_{Y,y}`.** -/
public abbrev pushforwardStalkModule (f : X ⟶ Y) (y : Y) : Type u :=
  (pushforwardStructurePresheaf f).stalk y

/-- The `𝒪_{Y,y}`-module structure on the stalk `(f_* 𝒪_X)_y`, the scalars acting through
`toPushforwardStalk`. -/
public instance modulePushforwardStalk (f : X ⟶ Y) (y : Y) :
    Module (Y.presheaf.stalk y) (pushforwardStalkModule f y) :=
  Module.compHom (pushforwardStalkModule f y) (toPushforwardStalk f y).hom

/-- The germ at `y` of a function on `f ⁻¹ U`, as an element of the stalk `(f_* 𝒪_X)_y`. -/
public def pushforwardStalkGerm (f : X ⟶ Y) (y : Y) (U : Y.Opens) (hy : y ∈ U)
    (s : Γ(X, f ⁻¹ᵁ U)) : pushforwardStalkModule f y :=
  ((pushforwardStructurePresheaf f).germ U y hy) s

/-- Every element of `(f_* 𝒪_X)_y` is the germ of a function on `f ⁻¹ U` for some open
neighbourhood `U` of `y`. -/
public theorem exists_pushforwardStalkGerm_eq (f : X ⟶ Y) (y : Y)
    (a : pushforwardStalkModule f y) :
    ∃ (U : Y.Opens) (hy : y ∈ U) (s : Γ(X, f ⁻¹ᵁ U)), pushforwardStalkGerm f y U hy s = a :=
  TopCat.Presheaf.exists_germ_eq (pushforwardStructurePresheaf f) a

/-! ### The restriction of a function to an infinitesimal neighbourhood -/

/-- Every infinitesimal neighbourhood of the fibre lies over every open neighbourhood of `y`:
the projection `i_n : X_n ⟶ X` has the fibre of `f` over `y` as its range. -/
public theorem top_le_preimage_infinitesimalι (f : X ⟶ Y) (y : Y) (n : ℕ) (U : Y.Opens)
    (hy : y ∈ U) :
    (⊤ : (infinitesimalNeighbourhood f y n).Opens) ≤ infinitesimalι f y n ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  intro x _
  change f.base ((infinitesimalι f y n).base x) ∈ U
  have hmem : f.base ((infinitesimalι f y n).base x) ∈
      Set.range (infinitesimalBase y n).base := by
    refine ⟨(infinitesimalStructure f y n).base x, ?_⟩
    exact congrArg (fun k : Scheme.Hom _ _ => k.base x) (infinitesimalι_comp f y n).symm
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (Y.presheaf.stalk y ⧸ stalkMaximalIdeal y ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr ((pow_zero _).trans Ideal.one_eq_top)
    obtain ⟨p, -⟩ := hmem
    refine absurd (Ideal.eq_top_iff_one p.asIdeal |>.mpr ?_) p.isPrime.ne_top
    have h0 : (1 : Y.presheaf.stalk y ⧸ stalkMaximalIdeal y ^ 0) = 0 :=
      Subsingleton.elim _ _
    exact h0 ▸ p.asIdeal.zero_mem
  · rw [range_infinitesimalBase y hn] at hmem
    have heq : f.base ((infinitesimalι f y n).base x) = y := hmem
    exact Set.mem_of_eq_of_mem heq hy

/-- **The restriction of a function on `f ⁻¹ U` to the `n`-th infinitesimal neighbourhood of the
fibre.** -/
public def infinitesimalRestrict (f : X ⟶ Y) (y : Y) (n : ℕ) (U : Y.Opens) (hy : y ∈ U)
    (s : Γ(X, f ⁻¹ᵁ U)) : infinitesimalFunctions f y n :=
  ((infinitesimalι f y n).appLE (f ⁻¹ᵁ U) ⊤
    (top_le_preimage_infinitesimalι f y n U hy)).hom s

/-! ### The canonical restriction map out of the stalk -/

/-- Every scheme lies over the whole of its target. -/
public theorem top_le_preimage_top {Z W : Scheme.{u}} (g : Z ⟶ W) :
    (⊤ : Z.Opens) ≤ g ⁻¹ᵁ (⊤ : W.Opens) := by simp

/-- `appLE` at `⊤` on both sides is `appTop`. -/
public theorem appLE_top_eq_appTop {Z W : Scheme.{u}} (g : Z ⟶ W) (e : (⊤ : Z.Opens) ≤ g ⁻¹ᵁ ⊤) :
    g.appLE ⊤ ⊤ e = g.appTop :=
  g.appLE_eq_app

/-- `appLE` only depends on the morphism, not on the proof that it maps the opens correctly. -/
public theorem appLE_congr_hom {Z W : Scheme.{u}} {g g' : Z ⟶ W} (hgg : g = g') (U : W.Opens)
    (V : Z.Opens) (e : V ≤ g ⁻¹ᵁ U) (e' : V ≤ g' ⁻¹ᵁ U) : g.appLE U V e = g'.appLE U V e' := by
  subst hgg
  rfl

/-- `appLE` into `⊤` followed by `appTop` of a further morphism is `appLE` of the composite. -/
private theorem appLE_top_comp_appTop {Z W V : Scheme.{u}} (f : Z ⟶ W) (g : W ⟶ V) (U : V.Opens)
    (e : ⊤ ≤ g ⁻¹ᵁ U) :
    g.appLE U ⊤ e ≫ f.appTop = (f ≫ g).appLE U ⊤
      ((top_le_preimage_top f).trans ((Opens.map f.base).map (homOfLE e)).le) := by
  rw [← appLE_top_eq_appTop f (top_le_preimage_top f), Scheme.Hom.appLE_comp_appLE]

/-- The whole of `Spec (𝒪_{Y,y}/𝔪_y ^ n)` lies over every open neighbourhood of `y`, since `c_n`
factors through `Spec 𝒪_{Y,y} ⟶ Y`. -/
public theorem top_le_preimage_infinitesimalBase (y : Y) (n : ℕ) (U : Y.Opens) (hy : y ∈ U) :
    (⊤ : (Spec (stalkQuotient y n)).Opens) ≤ infinitesimalBase y n ⁻¹ᵁ U :=
  fun p _ => le_preimage_fromSpecStalk_of_mem y U hy (x := (Spec.map (toStalkQuotient y n)).base p)
    trivial

/-- Restricting a function from `f ⁻¹ U` to `f ⁻¹ V` and then to `X_n` is restricting it to `X_n`
directly: the infinitesimal neighbourhood lies over both. -/
public theorem infinitesimalRestrict_res (f : X ⟶ Y) (y : Y) (n : ℕ) {U V : Y.Opens}
    (hVU : V ≤ U) (hyV : y ∈ V) (s : Γ(X, f ⁻¹ᵁ U)) :
    infinitesimalRestrict f y n V hyV
        ((X.presheaf.map ((Opens.map f.base).map (homOfLE hVU)).op).hom s) =
      infinitesimalRestrict f y n U (hVU hyV) s := by
  change ((infinitesimalι f y n).appLE (f ⁻¹ᵁ V) ⊤
      (top_le_preimage_infinitesimalι f y n V hyV)).hom
    ((X.presheaf.map ((Opens.map f.base).map (homOfLE hVU)).op).hom s) = _
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  rfl

/-- The restrictions to `X_n` of the functions on the `f ⁻¹ U`, for `U` an open neighbourhood of
`y`, as a cocone on the diagram whose colimit is the stalk `(f_* 𝒪_X)_y`. -/
public def infinitesimalRestrictCocone (f : X ⟶ Y) (y : Y) (n : ℕ) :
    Cocone ((OpenNhds.inclusion y).op ⋙ pushforwardStructurePresheaf f) where
  pt := Γ(infinitesimalNeighbourhood f y n, ⊤)
  ι :=
    { app U := (infinitesimalι f y n).appLE (f ⁻¹ᵁ U.unop.1) ⊤
        (top_le_preimage_infinitesimalι f y n U.unop.1 U.unop.2)
      naturality := fun U V i => by
        refine (Category.comp_id _).symm.trans ?_ |>.symm
        exact CommRingCat.hom_ext (RingHom.ext fun s =>
          (infinitesimalRestrict_res f y n (U := U.unop.1) (V := V.unop.1) i.unop.le
            V.unop.2 s).symm) }

/-- **The canonical restriction map `(f_* 𝒪_X)_y ⟶ Γ(X_n, 𝒪_{X_n})`**, as a ring map: the germ at
`y` of a function on `f ⁻¹ U` goes to its restriction to the `n`-th infinitesimal neighbourhood
of the fibre. It exists because `X_n` lies over *every* open neighbourhood of `y`, so the
restrictions form a cocone on the diagram computing the stalk. -/
public def infinitesimalStalkRestrictHom (f : X ⟶ Y) (y : Y) (n : ℕ) :
    (pushforwardStructurePresheaf f).stalk y ⟶ Γ(infinitesimalNeighbourhood f y n, ⊤) :=
  colimit.desc _ (infinitesimalRestrictCocone f y n)

/-- `infinitesimalStalkRestrictHom` sends the germ at `y` of a function on `f ⁻¹ U` to its
restriction to the `n`-th infinitesimal neighbourhood of the fibre. -/
@[simp]
public theorem infinitesimalStalkRestrictHom_germ (f : X ⟶ Y) (y : Y) (n : ℕ) (U : Y.Opens)
    (hy : y ∈ U) (s : Γ(X, f ⁻¹ᵁ U)) :
    (infinitesimalStalkRestrictHom f y n).hom (pushforwardStalkGerm f y U hy s) =
      infinitesimalRestrict f y n U hy s :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (infinitesimalRestrictCocone f y n) (op ⟨U, hy⟩)) s

/-- **The base ring map of `X_n` read on a neighbourhood of `y`**: the composite
`Γ(Y, U) ⟶ 𝒪_{Y,y} ⟶ 𝒪_{Y,y}/𝔪_y ^ n ≅ Γ(Spec (𝒪_{Y,y}/𝔪_y ^ n), ⊤)` is the map on sections of
`c_n : Spec (𝒪_{Y,y}/𝔪_y ^ n) ⟶ Y`. -/
public theorem germ_comp_toStalkQuotient_comp_ΓSpecIso_inv (y : Y) (n : ℕ) (U : Y.Opens)
    (hy : y ∈ U) :
    Y.presheaf.germ U y hy ≫ toStalkQuotient y n ≫
        (Scheme.ΓSpecIso (stalkQuotient y n)).inv =
      (infinitesimalBase y n).appLE U ⊤ (top_le_preimage_infinitesimalBase y n U hy) := by
  have hg : Y.presheaf.germ U y hy ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv =
      (Y.fromSpecStalk y).appLE U ⊤ (le_preimage_fromSpecStalk_of_mem y U hy) := by
    rw [← fromSpecStalk_appLE_germ Y U y hy (le_preimage_fromSpecStalk_of_mem y U hy),
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [Scheme.ΓSpecIso_inv_naturality, ← Category.assoc, hg, appLE_top_comp_appTop]
  exact appLE_congr_hom rfl U ⊤ _ _

/-- **The canonical restriction map to `X_n` carries the structure map of `f` on stalks to the
base ring map of `X_n`.** Both composites pull a function on an open neighbourhood `U` of `y`
back to `X_n`, one along `i_n ≫ f` and the other along `f_n ≫ c_n`, and those two morphisms
`X_n ⟶ Y` agree: that is the defining square of the fibre product `X_n`. -/
public theorem infinitesimalRestrict_app (f : X ⟶ Y) (y : Y) (n : ℕ) (U : Y.Opens) (hy : y ∈ U)
    (t : Γ(Y, U)) :
    infinitesimalRestrict f y n U hy ((f.app U).hom t) =
      infinitesimalBaseRingHom f y n (Y.presheaf.germ U y hy t) := by
  have hsq : (⊤ : (infinitesimalNeighbourhood f y n).Opens) ≤
      (infinitesimalStructure f y n ≫ infinitesimalBase y n) ⁻¹ᵁ U := by
    rw [← infinitesimalι_comp f y n]
    exact top_le_preimage_infinitesimalι f y n U hy
  have hfn : (infinitesimalBase y n).appLE U ⊤ (top_le_preimage_infinitesimalBase y n U hy) ≫
        (infinitesimalStructure f y n).appTop =
      (infinitesimalStructure f y n ≫ infinitesimalBase y n).appLE U ⊤ hsq := by
    exact appLE_top_comp_appTop _ _ _ _
  have key : f.app U ≫ (infinitesimalι f y n).appLE (f ⁻¹ᵁ U) ⊤
        (top_le_preimage_infinitesimalι f y n U hy) =
      Y.presheaf.germ U y hy ≫ toStalkQuotient y n ≫
        (Scheme.ΓSpecIso (stalkQuotient y n)).inv ≫
          (infinitesimalStructure f y n).appTop := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
      appLE_congr_hom (infinitesimalι_comp f y n) U ⊤ _ hsq, ← hfn,
      ← germ_comp_toStalkQuotient_comp_ΓSpecIso_inv y n U hy]
    simp only [Category.assoc]
  exact ConcreteCategory.congr_hom key t

/-- **The canonical restriction map is `𝒪_{Y,y}`-linear**: the scalar action on the stalk is
through the comorphism of `f` and the action on `Γ(X_n, 𝒪)` is through
`infinitesimalBaseRingHom`, and `infinitesimalRestrict_app` identifies the two. -/
public theorem infinitesimalStalkRestrictHom_toPushforwardStalk (f : X ⟶ Y) (y : Y) (n : ℕ)
    (r : Y.presheaf.stalk y) :
    (infinitesimalStalkRestrictHom f y n).hom ((toPushforwardStalk f y).hom r) =
      infinitesimalBaseRingHom f y n r := by
  obtain ⟨U, hyU, t, ht⟩ := TopCat.Presheaf.exists_germ_eq Y.presheaf r
  have hmap : (toPushforwardStalk f y).hom (Y.presheaf.germ U y hyU t) =
      pushforwardStalkGerm f y U hyU ((f.app U).hom t) :=
    ConcreteCategory.congr_hom
      (TopCat.Presheaf.stalkFunctor_map_germ U y hyU f.c) t
  rw [← ht, hmap, infinitesimalStalkRestrictHom_germ, infinitesimalRestrict_app]

/-- **The canonical restriction map `(f_* 𝒪_X)_y ⟶ Γ(X_n, 𝒪_{X_n})` as a map of
`𝒪_{Y,y}`-modules.** This is the family of maps whose existence
`Stacks.FormalFunctions.IsFormalFunctionsStalk` asserts; it is constructed here
unconditionally, so that only the bijectivity of the assembled comparison remains. -/
public def infinitesimalStalkRestrict (f : X ⟶ Y) (y : Y) (n : ℕ) :
    pushforwardStalkModule f y →ₗ[Y.presheaf.stalk y] infinitesimalFunctions f y n where
  toFun a := (infinitesimalStalkRestrictHom f y n).hom a
  map_add' a b := map_add _ a b
  map_smul' r a := by
    change (infinitesimalStalkRestrictHom f y n).hom ((toPushforwardStalk f y).hom r * a) =
      infinitesimalBaseRingHom f y n r * (infinitesimalStalkRestrictHom f y n).hom a
    rw [map_mul, infinitesimalStalkRestrictHom_toPushforwardStalk]

/-- `infinitesimalStalkRestrict` sends the germ at `y` of a function on `f ⁻¹ U` to its
restriction to the `n`-th infinitesimal neighbourhood of the fibre. -/
@[simp]
public theorem infinitesimalStalkRestrict_germ (f : X ⟶ Y) (y : Y) (n : ℕ) (U : Y.Opens)
    (hy : y ∈ U) (s : Γ(X, f ⁻¹ᵁ U)) :
    infinitesimalStalkRestrict f y n (pushforwardStalkGerm f y U hy s) =
      infinitesimalRestrict f y n U hy s :=
  infinitesimalStalkRestrictHom_germ f y n U hy s

/-- **The canonical restriction maps are compatible with the transitions of the inverse system**:
restricting to `X_n` and then to `X_m` is restricting to `X_m`, because the transition morphisms
are compatible with the projections `i_n`. -/
public theorem infinitesimalFunctionsMap_comp_infinitesimalStalkRestrict (f : X ⟶ Y) (y : Y)
    (m n : ℕ) (h : m ≤ n) :
    (infinitesimalFunctionsMap f y m n h).comp (infinitesimalStalkRestrict f y n) =
      infinitesimalStalkRestrict f y m := by
  refine LinearMap.ext fun a => ?_
  obtain ⟨U, hy, s, rfl⟩ := exists_pushforwardStalkGerm_eq f y a
  change (infinitesimalTransition f y h).appTop.hom
      (infinitesimalStalkRestrict f y n (pushforwardStalkGerm f y U hy s)) =
    infinitesimalStalkRestrict f y m (pushforwardStalkGerm f y U hy s)
  rw [infinitesimalStalkRestrict_germ, infinitesimalStalkRestrict_germ]
  change (infinitesimalTransition f y h).appTop.hom
      (((infinitesimalι f y n).appLE (f ⁻¹ᵁ U) ⊤
        (top_le_preimage_infinitesimalι f y n U hy)).hom s) = _
  rw [← CommRingCat.comp_apply, appLE_top_comp_appTop]
  exact ConcreteCategory.congr_hom
    (appLE_congr_hom (infinitesimalTransition_ι f y h) (f ⁻¹ᵁ U) ⊤ _
      (top_le_preimage_infinitesimalι f y m U hy)) s

/-! ### The comparison map and the statement of the theorem -/

/-- **`𝔪_y ^ n` annihilates `Γ(X_n, 𝒪_{X_n})`**, hence `𝔪_y ^ n (f_* 𝒪_X)_y` lies in the kernel
of every `𝒪_{Y,y}`-linear map `(f_* 𝒪_X)_y ⟶ Γ(X_n, 𝒪_{X_n})`. -/
public theorem pow_smul_top_le_ker (f : X ⟶ Y) (y : Y) (n : ℕ)
    (g : pushforwardStalkModule f y →ₗ[Y.presheaf.stalk y] infinitesimalFunctions f y n) :
    (stalkMaximalIdeal y ^ n) • (⊤ : Submodule (Y.presheaf.stalk y)
        (pushforwardStalkModule f y)) ≤ LinearMap.ker g := by
  refine Submodule.smul_le.mpr fun r hr x _ => ?_
  rw [LinearMap.mem_ker, map_smul, infinitesimalFunctions_smul_def,
    infinitesimalBaseRingHom_eq_zero f y n hr, zero_mul]

/-- **The comparison map `(f_* 𝒪_X)_y ^∧ ⟶ limₙ Γ(X_n, 𝒪_{X_n})`** assembled from a family of
`𝒪_{Y,y}`-linear maps compatible with the transitions. The `n`-th component of the image of a
Cauchy family is the `n`-th map applied to any representative of its `n`-th component, which is
legitimate because `𝔪_y ^ n` annihilates the target. -/
public def stalkCompletionComparison (f : X ⟶ Y) (y : Y)
    (q : ∀ n, pushforwardStalkModule f y →ₗ[Y.presheaf.stalk y] infinitesimalFunctions f y n)
    (hq : ∀ (m n : ℕ) (h : m ≤ n), (infinitesimalFunctionsMap f y m n h).comp (q n) = q m) :
    AdicCompletion (stalkMaximalIdeal y) (pushforwardStalkModule f y) →ₗ[Y.presheaf.stalk y]
      towerLimit (infinitesimalFunctions f y) (infinitesimalFunctionsMap f y) :=
  (towerComparison (infinitesimalFunctions f y) (infinitesimalFunctionsMap f y) q hq).comp
    (ofAdicCompletion (stalkMaximalIdeal y) (fun n => LinearMap.ker (q n))
      (antitone_ker (infinitesimalFunctions f y) (infinitesimalFunctionsMap f y) q hq)
      fun n => pow_smul_top_le_ker f y n (q n))

/-- **Every component of the comparison map comes from the uncompleted stalk.** This is the
step of the proof of [Stacks, Tag 0G7X] which observes that the map to the functions on the
fibre factors through the quotient by `𝔪_y`, so that an element of the completion already has
its image realized by an element of `(f_* 𝒪_X)_y`. -/
public theorem exists_apply_eq_proj (f : X ⟶ Y) (y : Y)
    (q : ∀ n, pushforwardStalkModule f y →ₗ[Y.presheaf.stalk y] infinitesimalFunctions f y n)
    (hq : ∀ (m n : ℕ) (h : m ≤ n), (infinitesimalFunctionsMap f y m n h).comp (q n) = q m)
    (z : AdicCompletion (stalkMaximalIdeal y) (pushforwardStalkModule f y)) (n : ℕ) :
    ∃ a : pushforwardStalkModule f y,
      q n a = towerLimit.proj n (stalkCompletionComparison f y q hq z) := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective
    (stalkMaximalIdeal y ^ n • (⊤ : Submodule (Y.presheaf.stalk y)
      (pushforwardStalkModule f y))) (z.val n)
  refine ⟨a, ?_⟩
  show q n a = _
  rw [towerLimit.proj_apply, show (stalkCompletionComparison f y q hq z :
      ∀ k, infinitesimalFunctions f y k) n =
    quotKerEmbed (infinitesimalFunctions f y) q n
      (Submodule.factor (pow_smul_top_le_ker f y n (q n)) (z.val n)) from rfl,
    ← ha]
  rfl

/-- **The conclusion of [Stacks, Tag 02OD] at `p = 0` for the structure sheaf**:

  `(f_* 𝒪_X)_y ^∧ ≅ limₙ Γ(X_n, 𝒪_{X_n})`.

Spelled out: there is a family of `𝒪_{Y,y}`-linear restriction maps
`q n : (f_* 𝒪_X)_y ⟶ Γ(X_n, 𝒪_{X_n})`, compatible with the transitions of the inverse system,
taking the germ at `y` of a function on `f ⁻¹ U` to its restriction to `X_n`, whose assembled
comparison map from the `𝔪_y`-adic completion of the stalk is bijective.

**This predicate is not proved anywhere in this library.** It is the statement of the tag, and
the file's implementation notes record exactly which inputs its proof is still missing; the
general-`p` and general-coherent-`ℱ` form of the tag is not stated at all, and neither is
`𝒪^∧_{Y,y}`-linearity of the comparison. -/
public def IsFormalFunctionsStalk (f : X ⟶ Y) (y : Y) : Prop :=
  ∃ (q : ∀ n, pushforwardStalkModule f y →ₗ[Y.presheaf.stalk y] infinitesimalFunctions f y n)
    (hq : ∀ (m n : ℕ) (h : m ≤ n), (infinitesimalFunctionsMap f y m n h).comp (q n) = q m),
    (∀ (n : ℕ) (U : Y.Opens) (hy : y ∈ U) (s : Γ(X, f ⁻¹ᵁ U)),
        q n (pushforwardStalkGerm f y U hy s) = infinitesimalRestrict f y n U hy s) ∧
      Function.Bijective (stalkCompletionComparison f y q hq)

/-- **The canonical comparison map `(f_* 𝒪_X)_y ^∧ ⟶ limₙ Γ(X_n, 𝒪_{X_n})`**, assembled from the
canonical restriction maps `Stacks.FormalFunctions.infinitesimalStalkRestrict`. The content of
[Stacks, Tag 02OD] at `p = 0` for the structure sheaf is that this map is bijective. -/
public abbrev canonicalStalkComparison (f : X ⟶ Y) (y : Y) :
    AdicCompletion (stalkMaximalIdeal y) (pushforwardStalkModule f y) →ₗ[Y.presheaf.stalk y]
      towerLimit (infinitesimalFunctions f y) (infinitesimalFunctionsMap f y) :=
  stalkCompletionComparison f y (infinitesimalStalkRestrict f y)
    (infinitesimalFunctionsMap_comp_infinitesimalStalkRestrict f y)

/-- **`IsFormalFunctionsStalk` is exactly the bijectivity of the canonical comparison map.** The
existential in the predicate is discharged by the canonical restriction maps, which this file
constructs unconditionally; only the bijectivity is in question. -/
public theorem isFormalFunctionsStalk_of_bijective (f : X ⟶ Y) (y : Y)
    (hbij : Function.Bijective (canonicalStalkComparison f y)) :
    IsFormalFunctionsStalk f y :=
  ⟨infinitesimalStalkRestrict f y,
    infinitesimalFunctionsMap_comp_infinitesimalStalkRestrict f y,
    fun n U hy s => infinitesimalStalkRestrict_germ f y n U hy s, hbij⟩

/-- **[Stacks, Tag 02OD] at `p = 0` for the structure sheaf, reduced to the two clauses of
[Stacks, Tag 02OB] read at the stalk.**

Let `c` be such that, for the canonical restriction maps `q n : (f_* 𝒪_X)_y ⟶ Γ(X_n, 𝒪)`,

* `ker (q n) ⊆ 𝔪_y ^ (n - c) (f_* 𝒪_X)_y` for `n ≥ c` — clause (1) of [Stacks, Tag 02OB]; and
* the image of `Γ(X_k, 𝒪) ⟶ Γ(X_n, 𝒪)` is the image of `q n` whenever `k ≥ n + c` — clause (3).

Then `IsFormalFunctionsStalk f y` holds. The containment `𝔪_y ^ n (f_* 𝒪_X)_y ⊆ ker (q n)`, the
third hypothesis of the commutative-algebra core
`Stacks.IntertwinedFiltration.adicCompletionEquivTowerLimit`, is **not** assumed: it is
`Stacks.FormalFunctions.pow_smul_top_le_ker`, proved in this file.

This is the whole of the source's argument for 02OD at `p = 0` except for the two uniform
bounds; see the implementation notes for what deriving those from the library's
[Stacks, Tag 02OB] still needs. -/
public theorem isFormalFunctionsStalk_of_uniformBounds (f : X ⟶ Y) (y : Y) (c : ℕ)
    (hker : ∀ n : ℕ, c ≤ n →
      LinearMap.ker (infinitesimalStalkRestrict f y n) ≤
        stalkMaximalIdeal y ^ (n - c) • (⊤ : Submodule (Y.presheaf.stalk y)
          (pushforwardStalkModule f y)))
    (hrange : ∀ (n k : ℕ) (h : n ≤ k), n + c ≤ k →
      LinearMap.range (infinitesimalFunctionsMap f y n k h) =
        LinearMap.range (infinitesimalStalkRestrict f y n)) :
    IsFormalFunctionsStalk f y :=
  isFormalFunctionsStalk_of_bijective f y
    (adicCompletionEquivTowerLimit (infinitesimalFunctions f y) (infinitesimalFunctionsMap f y)
      (infinitesimalStalkRestrict f y) (stalkMaximalIdeal y) c
      (infinitesimalFunctionsMap_comp_infinitesimalStalkRestrict f y)
      (fun n => pow_smul_top_le_ker f y n (infinitesimalStalkRestrict f y n)) hker
      hrange).bijective

/-! ### The reduction of Tag 0G7X -/

/-- **The tower of idempotents of `Stacks.FormalFunctions.infinitesimalIdempotent`, reindexed**
so that the term at `n` is a function on `X_n`. Since `infinitesimalIdempotent` starts at `X_1`,
the term at `n = 0` is its restriction to the (empty) zeroth neighbourhood. -/
public def infinitesimalIdempotentFamily (f : X ⟶ Y) (y : Y) (e : Γ(f.fiber y, ⊤))
    (he : IsIdempotentElem e) : (n : ℕ) → infinitesimalFunctions f y n
  | 0 => infinitesimalFunctionsMap f y 0 1 (Nat.zero_le 1)
      (infinitesimalIdempotent f y e he 0).1
  | n + 1 => (infinitesimalIdempotent f y e he n).1

/-- The reindexed tower is compatible with the successor transitions. -/
public theorem infinitesimalIdempotentFamily_restrict (f : X ⟶ Y) (y : Y) (e : Γ(f.fiber y, ⊤))
    (he : IsIdempotentElem e) (n : ℕ) :
    infinitesimalFunctionsMap f y n (n + 1) (Nat.le_succ n)
        (infinitesimalIdempotentFamily f y e he (n + 1)) =
      infinitesimalIdempotentFamily f y e he n := by
  cases n with
  | zero => rfl
  | succ k => exact infinitesimalIdempotent_restrict f y e he k

/-- The fibre lies over every open neighbourhood of `y`. -/
public theorem top_le_preimage_fiberι (f : X ⟶ Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) :
    (⊤ : (f.fiber y).Opens) ≤ f.fiberι y ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  intro x _
  change f.base ((f.fiberι y).base x) ∈ U
  rw [← Scheme.Hom.comp_apply, Scheme.Hom.fiber_fac]
  simpa using hy

/-- The first infinitesimal neighbourhood sits over an open neighbourhood of `y` compatibly with
the identification `X_y ≅ X_1`: restricting a function on `f ⁻¹ U` to `X_1` and then transporting
to the fibre is restricting it to the fibre. -/
public theorem appTop_infinitesimalRestrict_one (f : X ⟶ Y) (y : Y) (U : Y.Opens) (hy : y ∈ U)
    (s : Γ(X, f ⁻¹ᵁ U)) :
    (fiberIsoInfinitesimalNeighbourhoodOne f y).hom.appTop.hom
        (infinitesimalRestrict f y 1 U hy s) =
      ((f.fiberι y).appLE (f ⁻¹ᵁ U) ⊤ (top_le_preimage_fiberι f y U hy)).hom s := by
  have hcomp : (fiberIsoInfinitesimalNeighbourhoodOne f y).hom ≫ infinitesimalι f y 1 =
      f.fiberι y := pullback.lift_fst _ _ _
  have h2 : ((infinitesimalι f y 1).appLE (f ⁻¹ᵁ U) ⊤
        (top_le_preimage_infinitesimalι f y 1 U hy) ≫
      (fiberIsoInfinitesimalNeighbourhoodOne f y).hom.appTop) =
      (f.fiberι y).appLE (f ⁻¹ᵁ U) ⊤ (top_le_preimage_fiberι f y U hy) := by
    exact (appLE_top_comp_appTop _ _ _ _).trans (appLE_congr_hom hcomp _ _ _ _)
  rw [← h2]
  rfl

/-- **[Stacks, Tag 0G7X], reduced to the stalk form of the theorem on formal functions.**

Let `f : X ⟶ Y` be a morphism of schemes, let `y` be a point of `Y` and let `e` be an idempotent
global function on the scheme-theoretic fibre `X_y`. Granted `IsFormalFunctionsStalk f y` — the
conclusion of [Stacks, Tag 02OD] at `p = 0` for the structure sheaf — the function `e` is the
restriction of a function on `f ⁻¹ U` for some open neighbourhood `U` of `y`; equivalently, `e`
lies in the image of `(f_* 𝒪_X)_y ⟶ Γ(X_y, 𝒪_{X_y})`.

The proof is the source's: the fibre and all its infinitesimal neighbourhoods `X_n` have the
same underlying space, so `e` lifts to a compatible tower of idempotents `e_n ∈ Γ(X_n, 𝒪)`
(`Stacks.FormalFunctions.infinitesimalIdempotent`); that tower is an element of
`limₙ Γ(X_n, 𝒪)`, hence by the hypothesis the image of an element of the completed stalk; and
every component of that comparison is already realized on the uncompleted stalk
(`Stacks.FormalFunctions.exists_apply_eq_proj`), whose elements are germs of functions on the
`f ⁻¹ U`.

**No `@[stacks 0G7X]` attribute is attached, and none may be**: the statement is conditional on
`IsFormalFunctionsStalk f y`, which this library does not prove — see the implementation notes.
In particular the general case of the tag, where `f` is proper over an arbitrary (not
necessarily Noetherian) base, is not addressed at all: the source reduces it to the Noetherian
case by writing `f` as a limit of proper morphisms of finite presentation, and that reduction is
not carried out here. -/
public theorem exists_section_appLE_fiber_eq_of_isFormalFunctionsStalk (f : X ⟶ Y) (y : Y)
    (hFF : IsFormalFunctionsStalk f y) (e : Γ(f.fiber y, ⊤)) (he : IsIdempotentElem e) :
    ∃ (U : Y.Opens) (hy : y ∈ U) (a : Γ(X, f ⁻¹ᵁ U)),
      ((f.fiberι y).appLE (f ⁻¹ᵁ U) ⊤ (top_le_preimage_fiberι f y U hy)).hom a = e := by
  obtain ⟨q, hq, hnorm, hbij⟩ := hFF
  obtain ⟨z, hz⟩ := exists_towerLimit_of_succ f y (infinitesimalIdempotentFamily f y e he)
    (infinitesimalIdempotentFamily_restrict f y e he)
  obtain ⟨w, hw⟩ := hbij.2 z
  obtain ⟨α, hα⟩ := exists_apply_eq_proj f y q hq w 1
  obtain ⟨U, hy, s, hs⟩ := exists_pushforwardStalkGerm_eq f y α
  refine ⟨U, hy, s, ?_⟩
  have h1 : infinitesimalRestrict f y 1 U hy s = (infinitesimalIdempotent f y e he 0).1 := by
    rw [← hnorm 1 U hy s, hs, hα, hw, towerLimit.proj_apply, hz]
    rfl
  rw [← appTop_infinitesimalRestrict_one f y U hy s, h1,
    infinitesimalIdempotent_zero f y e he]

/-- **[Stacks, Tag 0G7X] in the exact shape the consumers in this library carry it**, reduced to
the stalk form of the theorem on formal functions.

`Stacks.AlgebraicGeometry.Fibres.ExtendsOverNeighbourhood f y e` is the predicate the tag
asserts, and the one its consumers in the Stein-factorization files quantified over as a
hypothesis `h0G7X` while the tag was open. This
declaration is therefore what would discharge those hypotheses — but only after
`IsFormalFunctionsStalk` is proved, which this library does not do, so **no `@[stacks 0G7X]`
attribute is attached here either** and none of the three hypotheses is discharged. -/
public theorem extendsOverNeighbourhood_of_isFormalFunctionsStalk (f : X ⟶ Y) (y : Y)
    (hFF : IsFormalFunctionsStalk f y) (e : Γ(f.fiber y, ⊤)) (he : IsIdempotentElem e) :
    Stacks.AlgebraicGeometry.Fibres.ExtendsOverNeighbourhood f y e := by
  obtain ⟨U, hy, a, ha⟩ := exists_section_appLE_fiber_eq_of_isFormalFunctionsStalk f y hFF e he
  exact ⟨U, hy, a, ha⟩

/-- **[Stacks, Tag 0G7X] in the consumers' shape, reduced to the two clauses of
[Stacks, Tag 02OB] read at the stalk.** This is the composite of
`isFormalFunctionsStalk_of_uniformBounds` with
`extendsOverNeighbourhood_of_isFormalFunctionsStalk`: it is the whole of 0G7X at the hypotheses
0G7X carries, granted only the two uniform bounds of [Stacks, Tag 02OB] for the canonical
restriction maps `(f_* 𝒪_X)_y ⟶ Γ(X_n, 𝒪)`.

**Still no `@[stacks 0G7X]` attribute**: the two bounds are hypotheses, and this library does not
prove them — see the implementation notes. -/
public theorem extendsOverNeighbourhood_of_uniformBounds (f : X ⟶ Y) (y : Y) (c : ℕ)
    (hker : ∀ n : ℕ, c ≤ n →
      LinearMap.ker (infinitesimalStalkRestrict f y n) ≤
        stalkMaximalIdeal y ^ (n - c) • (⊤ : Submodule (Y.presheaf.stalk y)
          (pushforwardStalkModule f y)))
    (hrange : ∀ (n k : ℕ) (h : n ≤ k), n + c ≤ k →
      LinearMap.range (infinitesimalFunctionsMap f y n k h) =
        LinearMap.range (infinitesimalStalkRestrict f y n))
    (e : Γ(f.fiber y, ⊤)) (he : IsIdempotentElem e) :
    Stacks.AlgebraicGeometry.Fibres.ExtendsOverNeighbourhood f y e :=
  extendsOverNeighbourhood_of_isFormalFunctionsStalk f y
    (isFormalFunctionsStalk_of_uniformBounds f y c hker hrange) e he

end Stacks.FormalFunctions

end

end
