module

public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.LinearAlgebra.Quotient.Card
public import Mathlib.RepresentationTheory.Submodule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.ConstantModuleFiltration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.PrimeToEllDictionary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.RankOneFiltration
public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.FundamentalGroupTheorem
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FunctorsHomomorphisms.Comparison
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricFibreDegree
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Filtering a locally constant `F_ℓ`-sheaf after a cover of degree prime to `ℓ`

Let `S` be a connected scheme, let `ℓ` be a prime number and let `F` be a finite type locally
constant sheaf of `F_ℓ`-vector spaces on `S_étale`. There is then a finite étale morphism
`f : T → S` whose degree is prime to `ℓ` and for which `f⁻¹F` carries a finite filtration whose
successive quotients are the constant sheaf `Z/ℓZ_T`.

The proof is the one of the source. The sheaf corresponds to a finite `F_ℓ`-vector space `V`
with a continuous action of `π₁(S, s̄)`; the image `G` of that action is a finite group, and the
surjection `ρ̄ : π₁(S, s̄) → G` is the monodromy of a Galois cover `Y → S`. For an `ℓ`-Sylow
subgroup `H ⊆ G` the cover `T = Y/H`, which is the cover attached by Tag 0BND (1) to the finite
`π₁(S, s̄)`-set `π₁(S, s̄)/ρ̄⁻¹(H)`, has degree `[G : H]`, prime to `ℓ`. The action of
`π₁(T, t̄)` on `V` is through `H`, and a representation of a finite `ℓ`-group on a finite
`F_ℓ`-vector space is a successive extension of copies of `Z/ℓZ` with trivial action
(`Representation.exists_sylow_relSeries_trivialRankOneStep`); transporting that filtration back
through the dictionary gives the filtration of `f⁻¹F`.

## Main definitions

* `Stacks.EtaleCohomology.ConstantRankOneStep`: one step of a filtration of a sheaf of
  `F_ℓ`-modules on a small étale site whose subquotient is the constant sheaf `Z/ℓZ`.
* `Stacks.EtaleCohomology.FundamentalGroupFGModuleDictionary`: the dictionary between locally
  constant sheaves of `F_ℓ`-modules and continuous representations of the étale fundamental
  group, in the form the proof of the tag consumes; see below.
* `Stacks.EtaleCohomology.FundamentalGroupModuleDictionary`: the same dictionary asked of *all*
  modules over the group ring, which is the form in which it was first carried as an explicit
  hypothesis; see the section on the two forms below.

## Main results

* `Stacks.EtaleCohomology.nonempty_fundamentalGroupFGModuleDictionary`: that dictionary is
  available for every finite type locally constant sheaf of `F_ℓ`-vector spaces.
* `Stacks.EtaleCohomology.exists_primeToEll_finiteEtale_constantFiltration_unconditional`:
  Tag 0A3R.
* `Stacks.EtaleCohomology.exists_primeToEll_finiteEtale_constantFiltration`: the same conclusion
  read off a given dictionary at a given geometric point.

## The dictionary

The translation between sheaves and representations is packaged as
`FundamentalGroupFGModuleDictionary`, whose fields are exactly the statements the proof consumes,
and which is discharged by `Stacks.EtaleCohomology.nonempty_fundamentalGroupFGModuleDictionary`:

* `V`, `ρ` and `isOpen_rho_eq` are **Tag 0DV5 (3)** in its `F_ℓ`-module form at the base point:
  the finite `F_ℓ`-vector space attached to `F` and its continuous monodromy action of
  `π₁(S, s̄)`, continuity being the openness of the preimage of each endomorphism. They are the
  value of the dictionary over `S`, read as a representation by
  `Stacks.GroupCohomology.exists_representation_isOpen_rep_eq`.
* `exists_pullbackFunctor` is **Tag 0DV5 (3)** over a connected finite étale cover `T` of `S`
  — connectedness being spelled as transitivity of `π₁(S, s̄)` on the geometric fibre, which is
  what **Tag 0BND (1)** turns it into — combined with **Remark 0DV6** and with the
  identification of the image of `π₁(T, t̄) → π₁(S, s̄)` with the stabiliser of the chosen point
  of the fibre: the inverse image `f⁻¹F` corresponds to `V` with the action of `π₁(T, t̄)`, and
  that action factors through any finite group `K` through which the stabiliser of the point
  acts, so the *finitely generated* modules over the group ring `F_ℓ[K]` map to sheaves on
  `T_étale` by an exact functor carrying `V` to `f⁻¹F` and a module with `ℓ` elements and trivial
  action to `Z/ℓZ_T`. Only exactness is assumed of that functor: a left exact functor between
  abelian categories is additive, by
  `CategoryTheory.Functor.additive_of_preserves_binary_products`.

The first field says nothing on its own — it asserts only that *some* finite `F_ℓ`-module with
a continuous action exists, untied to `F`. All the content is in the second, which couples `V`
to `F`, so the two are built together, driven by the second.

### Why the second field is restricted to the finitely generated modules

An infinite module over `F_ℓ[K]` corresponds to no locally constant sheaf, so a functor out of
*all* modules over the group ring cannot exist. The proof applies the functor only to
subquotients of the stalk, which are finite, so the field asks for a functor out of the full
subcategory cut out by `ModuleCat.isFG (MonoidAlgebra (ZMod ℓ) K)`, which is abelian by the
closure instances `ModuleCat.isClosedUnderSubobjects_isFG` and its companions; the `TransportFG`
section below works in that category, reading its cokernels through the exact inclusion
`CategoryTheory.ObjectProperty.preservesCokernels_ι`.

For the same reason the field asks the homomorphism `π : Stab → K` for open fibres rather than
leaving it bare: the action of `π₁(T, t̄)` on a module over `F_ℓ[K]` is continuous only because
of that, and at the call site it holds because `τ` is faithful there — `ρG` is injective on the
image of the monodromy, so the fibres of `π` are the fibres of `ρ`, which `isOpen_rho_eq` makes
open.

### The two forms of the dictionary

`FundamentalGroupModuleDictionary` is the same translation asked of *all* modules over the group
ring and with the stalk in `Type u`, which is the form in which the dictionary was first carried
as an explicit hypothesis, before Tag 0DV5 (3) discharged it. It is the hypothesis of
`Stacks.EtaleCohomology.exists_primeToEll_finiteEtale_constantFiltration`, which reads the
filtration off a given dictionary at a given geometric point through the `Transport` section; the
unconditional Tag 0A3R uses the finitely generated form instead and needs no hypothesis. Neither
form is derivable from the other: the one asks a functor of more modules, the other of a larger
universe.

### How the dictionary is built

* **The coefficient universe.** Tag 0DV5 (3) is stated at `ModuleCat.{u + 1}` and this file works
  at `ModuleCat.{max (u + 1) v}`, so `F` is first exhibited as the universe lift of a sheaf at
  `ModuleCat.{u + 1}` by
  `AlgebraicGeometry.exists_isFiniteTypeLocallyConstantModuleSheaf_smallEtale_uliftFunctor_iso`.
  The lift is exact and commutes with inverse image,
  `AlgebraicGeometry.preservesFiniteLimits_sheafCompose_smallEtale_moduleUliftFunctor` and
  `AlgebraicGeometry.smallEtaleSheafPullbackModuleUliftIso`.
* **One big étale site for `S` and for every cover.** Tag 0DV5 and Remark 0DV6 are stated for a
  big étale site, and Remark 0DV6 compares two schemes of *one* site, while the first field is
  chosen before the cover is known. `AlgebraicGeometry.BigEtaleSite.containing S` serves for
  both, because a big étale site containing `S` contains every finite étale cover of `S`:
  `AlgebraicGeometry.BigEtaleSite.contains_left_of_finiteEtaleOver`.
* **The point of the fibre as a geometric point.** The chosen point of the geometric fibre is a
  geometric point `t̄` of `T` lying over `s̄`,
  `AlgebraicGeometry.exists_geometricPoint_heq_finiteEtaleOverSourcePoint`, and the monodromy of
  the cover stabilises it, `AlgebraicGeometry.smul_finiteEtaleOverSourcePoint_eq` — the easy half
  of `AlgebraicGeometry.range_etaleFundamentalGroupMap_eq_stabilizer`. So the action of
  `π₁(T, t̄)` on the stalk factors through `K`.
* **Remark 0DV6 on Mathlib's small étale site**, for sheaves of modules, is
  `AlgebraicGeometry.nonempty_finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite_pullbackIso`
  and its inverse image is built by a left Kan extension, which
  `AlgebraicGeometry.etaleSiteSheafPullbackModuleIsoSheafPullback` identifies with the abstract
  left adjoint this file's conclusion uses.
* **The functor out of the group ring.** Modules over `F_ℓ[K]` are `F_ℓ`-modules with a
  `K`-action, `Stacks.GroupCohomology.moduleMonoidAlgebraActionEquivalence`, and with `K` finite
  and the fibres of `π` open the action of `π₁(T, t̄)` through `K` is continuous, so the finitely
  generated ones become finite modules with a continuous action by the exact functor
  `Stacks.GroupCohomology.groupRingFiniteTypeContinuousModule`. Composing with the inverse of
  Tag 0DV5 (3), the inclusion of the finite type locally constant sheaves — exact by Tag 093U (3)
  — and the universe lift gives the field's functor,
  `Stacks.EtaleCohomology.exists_pullbackFunctor_of_rep`.
* **The constant sheaf.** The value of Tag 0DV5 (3) on a constant sheaf of modules has trivial
  action and the cardinality of the module,
  `AlgebraicGeometry.rho_eq_one_moduleSheafEquivalenceEtaleSite_constantSheaf` and
  `AlgebraicGeometry.natCard_moduleSheafEquivalenceEtaleSite_constantSheaf`. That identification
  is a bijection of underlying sets and not `F_ℓ`-linear, and making it linear would need
  naturality of Tag 03RV in the index type, which the library does not have. Over the *prime*
  field `F_ℓ` it is not needed: two finite modules with trivial action and `ℓ` elements are
  isomorphic, `Stacks.GroupCohomology.nonempty_iso_of_rho_eq_one_of_natCard_eq`, and the source
  prescribes the successive quotients only up to isomorphism.

## Implementation notes

A finite filtration with prescribed successive quotients is recorded, as in
`Representation.TrivialRankOneStep`, by a `RelSeries` for the relation `ConstantRankOneStep` on
the lattice of subobjects of the sheaf: a pair of subobjects is a step when the first is
contained in the second and the quotient of the second by the first is the constant sheaf
`Z/ℓZ_T`. That the filtration runs from the zero subobject to the whole sheaf is stated as
`IsZero` of the first term and `IsIso` of the inclusion of the last, which are the conditions
`⊥` and `⊤` in the subobject lattice.

The degree of the cover is read off its geometric fibre by
`AlgebraicGeometry.isFiniteLocallyFreeOfRank_natCard_finiteEtaleFiber`: the rank in the sense of
Tag 02KA of a finite étale morphism over a connected base is the number of points of its fibre
at a geometric point, so the degree of `T → S` is the index of the Sylow subgroup, and the
primality to `ℓ` of that degree is a statement about the finite group `G`.

The module universe of the sheaves is `max (u + 1) v`, the shape in which sheafification on a
small étale site is automatic, while the stalk and the finite groups acting on it are taken in
`Type u`; a finite `F_ℓ`-vector space can always be chosen there, and the dictionary functor
bridges the two universes.

## References

* [Stacks Project, Tag 0A3R](https://stacks.math.columbia.edu/tag/0A3R)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
* [Stacks Project, Tag 0DV6](https://stacks.math.columbia.edu/tag/0DV6)
* [Stacks Project, Tag 0BND](https://stacks.math.columbia.edu/tag/0BND)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.EtaleCohomology
open scoped FintypeCatDiscrete SetRel

universe v u

namespace Stacks.EtaleCohomology

/-- Sheafification of presheaves of `F_ℓ`-modules on a small étale site. -/
private instance hasSheafifyModule (X : Scheme.{u}) (ℓ : ℕ) :
    HasSheafify (smallEtaleTopology X) (ModuleCat.{max (u + 1) v} (ZMod ℓ)) :=
  Stacks.ConstantSheaf.hasSheafify_moduleCat.{u + 1, u, 0, v} _ _

/-- Sheaves of `F_ℓ`-modules on a small étale site have an initial object. -/
private instance hasInitialSheafModule (X : Scheme.{u}) (ℓ : ℕ) :
    HasInitial (Sheaf (smallEtaleTopology X) (ModuleCat.{max (u + 1) v} (ZMod ℓ))) :=
  HasZeroObject.hasInitial

/-- The subobjects of a sheaf of `F_ℓ`-modules have a least element, the zero subobject. -/
private instance orderBotSubobjectSheafModule {X : Scheme.{u}} {ℓ : ℕ}
    (A : Sheaf (smallEtaleTopology X) (ModuleCat.{max (u + 1) v} (ZMod ℓ))) :
    OrderBot (Subobject A) :=
  Subobject.orderBot

/-- The constant sheaf `Z/ℓZ` on the small étale site. -/
@[sga "7 XXII 2.0"]
abbrev constantZMod (ℓ : ℕ) (X : Scheme.{u}) :
    Sheaf (smallEtaleTopology X) (ModuleCat.{max (u + 1) v} (ZMod ℓ)) :=
  (constantSheaf (smallEtaleTopology X) (ModuleCat.{max (u + 1) v} (ZMod ℓ))).obj
    (ModuleCat.of (ZMod ℓ) (ULift.{max (u + 1) v} (ZMod ℓ)))

/-- Inverse image of sheaves of `F_ℓ`-modules along a morphism of schemes. -/
abbrev smallEtalePullbackZMod (ℓ : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology Y) (ModuleCat.{max (u + 1) v} (ZMod ℓ)) ⥤
      Sheaf (smallEtaleTopology X) (ModuleCat.{max (u + 1) v} (ZMod ℓ)) :=
  (smallEtaleBaseChange f).sheafPullback (ModuleCat.{max (u + 1) v} (ZMod ℓ))
    (smallEtaleTopology Y) (smallEtaleTopology X)

/-- One step of a filtration of a sheaf of `F_ℓ`-modules on the small étale site of `X` whose
subquotient is the constant sheaf `Z/ℓZ_X`: the first subobject is contained in the second and
the quotient of the second by the first is that constant sheaf. -/
def ConstantRankOneStep (ℓ : ℕ) {X : Scheme.{u}}
    (A : Sheaf (smallEtaleTopology X) (ModuleCat.{max (u + 1) v} (ZMod ℓ))) :
    SetRel (Subobject A) (Subobject A) :=
  {p | ∃ h : p.1 ≤ p.2, Nonempty (cokernel (p.1.ofLE p.2 h) ≅ constantZMod ℓ X)}

/-! ### Invariant submodules as modules over the group ring -/

section GroupRing

variable {ℓ : ℕ} {K W : Type*} [Group K] [AddCommGroup W] [Module (ZMod ℓ) W]
  (τ : Representation (ZMod ℓ) K W)

/-- A submodule invariant under a representation, read as a submodule of the module over the
group ring. Its elements are those of the given submodule, so the two carry the same
cardinality. -/
private def invtAsSubmodule (N : Submodule (ZMod ℓ) W) (hN : ∀ g : K, ∀ x ∈ N, τ g x ∈ N) :
    Submodule (MonoidAlgebra (ZMod ℓ) K) τ.asModule where
  carrier := (N : Set W)
  add_mem' := N.add_mem
  zero_mem' := N.zero_mem
  smul_mem' r _ hx := τ.asAlgebraHom_mem_of_forall_mem N hN _ hx r

/-- Membership in the submodule over the group ring is membership in the given submodule. -/
private theorem mem_invtAsSubmodule {N : Submodule (ZMod ℓ) W}
    {hN : ∀ g : K, ∀ x ∈ N, τ g x ∈ N} {x : τ.asModule} :
    x ∈ invtAsSubmodule τ N hN ↔ x ∈ N := Iff.rfl

/-- One element of the group ring acts on the module over the group ring as the representation
does on the underlying vector space. -/
private theorem single_one_smul_eq (g : K) (x : τ.asModule) :
    MonoidAlgebra.single g (1 : ZMod ℓ) • x = τ g x := by
  rw [Representation.single_smul, one_smul]
  rfl

/-- **The subquotient of a rank one step has `ℓ` elements.** -/
private theorem card_quotient_range_inclusion [Finite W] {N₁ N₂ : Submodule (ZMod ℓ) W}
    {h₁ : ∀ g : K, ∀ x ∈ N₁, τ g x ∈ N₁} {h₂ : ∀ g : K, ∀ x ∈ N₂, τ g x ∈ N₂}
    (hle : invtAsSubmodule τ N₁ h₁ ≤ invtAsSubmodule τ N₂ h₂)
    (hcard : Nat.card N₂ = ℓ * Nat.card N₁) :
    Nat.card (invtAsSubmodule τ N₂ h₂ ⧸
      LinearMap.range (Submodule.inclusion hle)) = ℓ := by
  have hinj : Function.Injective (Submodule.inclusion hle) := Submodule.inclusion_injective hle
  have hsplit := Submodule.card_eq_card_quotient_mul_card
    (LinearMap.range (Submodule.inclusion hle))
  rw [Nat.card_congr (LinearEquiv.ofInjective _ hinj).toEquiv.symm] at hsplit
  have hpos : 0 < Nat.card N₁ := Nat.card_pos
  have hsplit' : Nat.card N₂ = Nat.card N₁ *
      Nat.card (invtAsSubmodule τ N₂ h₂ ⧸ LinearMap.range (Submodule.inclusion hle)) := hsplit
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [← hsplit', hcard, mul_comm]

/-- **The group acts trivially on the subquotient of a rank one step.** -/
private theorem single_one_smul_quotient_eq {N₁ N₂ : Submodule (ZMod ℓ) W}
    {h₁ : ∀ g : K, ∀ x ∈ N₁, τ g x ∈ N₁} {h₂ : ∀ g : K, ∀ x ∈ N₂, τ g x ∈ N₂}
    (hle : invtAsSubmodule τ N₁ h₁ ≤ invtAsSubmodule τ N₂ h₂)
    (htriv : ∀ g : K, ∀ x ∈ N₂, τ g x - x ∈ N₁) (g : K)
    (w : invtAsSubmodule τ N₂ h₂ ⧸ LinearMap.range (Submodule.inclusion hle)) :
    MonoidAlgebra.single g (1 : ZMod ℓ) • w = w := by
  induction w using Submodule.Quotient.induction_on with
  | H x =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    refine ⟨⟨MonoidAlgebra.single g (1 : ZMod ℓ) • x - x, ?_⟩, rfl⟩
    rw [mem_invtAsSubmodule, single_one_smul_eq]
    exact htriv g x.1 x.2

/-- The inclusion of an invariant submodule into the whole module is injective. -/
private instance mono_ofHom_invtAsSubmodule_subtype (N : Submodule (ZMod ℓ) W)
    (hN : ∀ g : K, ∀ x ∈ N, τ g x ∈ N) :
    Mono (ModuleCat.ofHom (invtAsSubmodule τ N hN).subtype) :=
  (ModuleCat.mono_iff_injective _).2 Subtype.val_injective

/-- The inclusion of the invariant submodule `⊤` into the whole module is an isomorphism. -/
private theorem isIso_ofHom_invtAsSubmodule_subtype {N : Submodule (ZMod ℓ) W}
    (hN : ∀ g : K, ∀ x ∈ N, τ g x ∈ N) (htop : N = ⊤) :
    IsIso (ModuleCat.ofHom (invtAsSubmodule τ N hN).subtype) :=
  have : Epi (ModuleCat.ofHom (invtAsSubmodule τ N hN).subtype) :=
    (ModuleCat.epi_iff_surjective _).2 fun x ↦
      ⟨⟨x, (mem_invtAsSubmodule τ).2 (Submodule.eq_top_iff'.1 htop x)⟩, rfl⟩
  isIso_of_mono_of_epi _

/-- The invariant submodule `⊥` is a zero module over the group ring. -/
private theorem isZero_invtAsSubmodule_of_eq_bot {N : Submodule (ZMod ℓ) W}
    (hN : ∀ g : K, ∀ x ∈ N, τ g x ∈ N) (hbot : N = ⊥) :
    IsZero (ModuleCat.of (MonoidAlgebra (ZMod ℓ) K) (invtAsSubmodule τ N hN)) :=
  have : Subsingleton (invtAsSubmodule τ N hN) := ⟨fun a b ↦ Subtype.ext <|
    ((Submodule.eq_bot_iff N).1 hbot a.1 a.2).trans ((Submodule.eq_bot_iff N).1 hbot b.1 b.2).symm⟩
  ModuleCat.isZero_of_subsingleton _

end GroupRing

/-! ### Transport of a filtration of the stalk to a filtration of the sheaf -/

section Transport

variable {ℓ : ℕ} {K W : Type u} [Group K] [AddCommGroup W] [Module (ZMod ℓ) W]
  {T : Scheme.{u}} {τ : Representation (ZMod ℓ) K W}
  {Φ : ModuleCat.{u} (MonoidAlgebra (ZMod ℓ) K) ⥤
    Sheaf (smallEtaleTopology T) (ModuleCat.{max (u + 1) v} (ZMod ℓ))}
  {A : Sheaf (smallEtaleTopology T) (ModuleCat.{max (u + 1) v} (ZMod ℓ))}
  (eTop : Φ.obj (ModuleCat.of (MonoidAlgebra (ZMod ℓ) K) τ.asModule) ≅ A)

/-- The subsheaf of `A` attached by the dictionary to a submodule invariant under `τ`. -/
private def transportMono (N : Submodule (ZMod ℓ) W) (hN : ∀ g : K, ∀ x ∈ N, τ g x ∈ N) :
    Φ.obj (ModuleCat.of (MonoidAlgebra (ZMod ℓ) K) (invtAsSubmodule τ N hN)) ⟶ A :=
  Φ.map (ModuleCat.ofHom (invtAsSubmodule τ N hN).subtype) ≫ eTop.hom

private instance monoTransportMono [PreservesFiniteLimits Φ] (N : Submodule (ZMod ℓ) W)
    (hN : ∀ g : K, ∀ x ∈ N, τ g x ∈ N) : Mono (transportMono eTop N hN) := by
  rw [transportMono]
  infer_instance

/-- **A rank one step of the filtration of the stalk gives a step of the filtration of the
sheaf whose quotient is the constant sheaf `Z/ℓZ`.** -/
private theorem transport_step [Finite W] [Φ.Additive] [PreservesFiniteLimits Φ]
    [PreservesFiniteColimits Φ]
    (hΦconst : ∀ W' : ModuleCat.{u} (MonoidAlgebra (ZMod ℓ) K), Nat.card W' = ℓ →
      (∀ (g : K) (w : W'), (MonoidAlgebra.single g (1 : ZMod ℓ)) • w = w) →
      Nonempty (Φ.obj W' ≅ constantZMod ℓ T))
    {N₁ N₂ : Submodule (ZMod ℓ) W} (h₁ : ∀ g : K, ∀ x ∈ N₁, τ g x ∈ N₁)
    (h₂ : ∀ g : K, ∀ x ∈ N₂, τ g x ∈ N₂)
    (hstep : (N₁, N₂) ∈ Representation.TrivialRankOneStep (⊤ : Subgroup K) τ) :
    (Subobject.mk (transportMono eTop N₁ h₁), Subobject.mk (transportMono eTop N₂ h₂)) ∈
      ConstantRankOneStep ℓ A := by
  have hsub : invtAsSubmodule τ N₁ h₁ ≤ invtAsSubmodule τ N₂ h₂ := fun _ hx ↦ hstep.1 hx
  have hcomm : Φ.map (ModuleCat.ofHom (Submodule.inclusion hsub)) ≫
      transportMono eTop N₂ h₂ = transportMono eTop N₁ h₁ := by
    rw [transportMono, transportMono, ← Category.assoc, ← Φ.map_comp]
    rfl
  obtain ⟨hmk, ⟨iso⟩⟩ := exists_cokernel_ofLE_iso_of_comm _ hcomm
  refine ⟨hmk, ⟨iso ≪≫ ?_⟩⟩
  exact (PreservesCokernel.iso Φ _).symm ≪≫ Φ.mapIso (ModuleCat.cokernelIsoRangeQuotient _) ≪≫
    (hΦconst _ (card_quotient_range_inclusion τ hsub hstep.2.2)
      (single_one_smul_quotient_eq τ hsub fun g x hx ↦ hstep.2.1 g trivial x hx)).some

/-- The zero submodule gives the zero subobject. -/
private theorem transport_isZero [Φ.Additive] [PreservesFiniteLimits Φ]
    {N : Submodule (ZMod ℓ) W} (hN : ∀ g : K, ∀ x ∈ N, τ g x ∈ N) (hbot : N = ⊥) :
    IsZero (Subobject.underlying.obj (Subobject.mk (transportMono eTop N hN))) := by
  exact IsZero.of_iso (Φ.map_isZero (isZero_invtAsSubmodule_of_eq_bot τ hN hbot))
    (Subobject.underlyingIso (transportMono eTop N hN))

/-- The whole stalk gives the whole sheaf. -/
private theorem transport_isIso [Φ.Additive] [PreservesFiniteLimits Φ]
    {N : Submodule (ZMod ℓ) W} (hN : ∀ g : K, ∀ x ∈ N, τ g x ∈ N) (htop : N = ⊤) :
    IsIso (Subobject.mk (transportMono eTop N hN)).arrow := by
  have := isIso_ofHom_invtAsSubmodule_subtype τ hN htop
  have : IsIso (transportMono eTop N hN) := by
    rw [transportMono]
    infer_instance
  exact (Subobject.isIso_arrow_iff_eq_top _).2 (Subobject.mk_eq_top_of_isIso _)

end Transport

/-! ### Transport over the finitely generated modules of the group ring -/

section TransportFG

variable {ℓ : ℕ} [NeZero ℓ] {K W : Type (u + 1)} [Group K] [Finite K] [AddCommGroup W]
  [Module (ZMod ℓ) W] [Finite W]
  {T : Scheme.{u}} {τ : Representation (ZMod ℓ) K W}
  {Φ : (ModuleCat.isFG.{u + 1} (MonoidAlgebra (ZMod ℓ) K)).FullSubcategory ⥤
    Sheaf (smallEtaleTopology T) (ModuleCat.{max (u + 1) v} (ZMod ℓ))}
  {A : Sheaf (smallEtaleTopology T) (ModuleCat.{max (u + 1) v} (ZMod ℓ))}
  (eTop : Φ.obj (asFiniteTypeGroupRingModule (ZMod ℓ) τ) ≅ A)

/-- A submodule invariant under `τ`, as a finitely generated module over the group ring: it is a
subset of a finite module, hence finite, and over the finite ring `F_ℓ[K]` a finite module is
finitely generated. -/
private def invtAsFGObject (N : Submodule (ZMod ℓ) W) (hN : ∀ g : K, ∀ x ∈ N, τ g x ∈ N) :
    (ModuleCat.isFG.{u + 1} (MonoidAlgebra (ZMod ℓ) K)).FullSubcategory :=
  ⟨ModuleCat.of (MonoidAlgebra (ZMod ℓ) K) (invtAsSubmodule τ N hN),
    (Stacks.GroupCohomology.moduleCat_isFG_iff_finite (MonoidAlgebra (ZMod ℓ) K) _).2 (by
      have : Finite τ.asModule := Finite.of_equiv W τ.asModuleEquiv.toEquiv.symm
      exact inferInstance)⟩

/-- The inclusion of an invariant submodule into the whole module, as a morphism of finitely
generated modules over the group ring. -/
private def invtAsFGObjectι (N : Submodule (ZMod ℓ) W) (hN : ∀ g : K, ∀ x ∈ N, τ g x ∈ N) :
    invtAsFGObject (τ := τ) N hN ⟶ asFiniteTypeGroupRingModule (ZMod ℓ) τ :=
  ObjectProperty.homMk (ModuleCat.ofHom (invtAsSubmodule τ N hN).subtype)

/-- The subsheaf of `A` attached by the dictionary to a submodule invariant under `τ`. -/
private def transportFGMono (N : Submodule (ZMod ℓ) W) (hN : ∀ g : K, ∀ x ∈ N, τ g x ∈ N) :
    Φ.obj (invtAsFGObject (τ := τ) N hN) ⟶ A :=
  Φ.map (invtAsFGObjectι N hN) ≫ eTop.hom

private instance monoTransportFGMono [PreservesFiniteLimits Φ] (N : Submodule (ZMod ℓ) W)
    (hN : ∀ g : K, ∀ x ∈ N, τ g x ∈ N) : Mono (transportFGMono eTop N hN) := by
  have : Mono (invtAsFGObjectι (τ := τ) N hN) :=
    (ObjectProperty.ι (ModuleCat.isFG.{u + 1} (MonoidAlgebra (ZMod ℓ) K))).mono_of_mono_map
      (mono_ofHom_invtAsSubmodule_subtype τ N hN)
  rw [transportFGMono]
  infer_instance

/-- **A rank one step of the filtration of the stalk gives a step of the filtration of the
sheaf whose quotient is the constant sheaf `Z/ℓZ`.** -/
private theorem transportFG_step [Φ.Additive] [PreservesFiniteLimits Φ]
    [PreservesFiniteColimits Φ]
    (hΦconst : ∀ W' : (ModuleCat.isFG.{u + 1} (MonoidAlgebra (ZMod ℓ) K)).FullSubcategory,
      Nat.card (ToType W'.obj) = ℓ →
      (∀ (g : K) (w : ToType W'.obj), (MonoidAlgebra.single g (1 : ZMod ℓ)) • w = w) →
      Nonempty (Φ.obj W' ≅ constantZMod ℓ T))
    {N₁ N₂ : Submodule (ZMod ℓ) W} (h₁ : ∀ g : K, ∀ x ∈ N₁, τ g x ∈ N₁)
    (h₂ : ∀ g : K, ∀ x ∈ N₂, τ g x ∈ N₂)
    (hstep : (N₁, N₂) ∈ Representation.TrivialRankOneStep (⊤ : Subgroup K) τ) :
    (Subobject.mk (transportFGMono eTop N₁ h₁), Subobject.mk (transportFGMono eTop N₂ h₂)) ∈
      ConstantRankOneStep ℓ A := by
  have hsub : invtAsSubmodule τ N₁ h₁ ≤ invtAsSubmodule τ N₂ h₂ := fun _ hx ↦ hstep.1 hx
  set incl : invtAsFGObject (τ := τ) N₁ h₁ ⟶ invtAsFGObject (τ := τ) N₂ h₂ :=
    ObjectProperty.homMk (ModuleCat.ofHom (Submodule.inclusion hsub)) with hincl
  have hcomm : Φ.map incl ≫ transportFGMono eTop N₂ h₂ = transportFGMono eTop N₁ h₁ := by
    rw [transportFGMono, transportFGMono, ← Category.assoc, ← Φ.map_comp]
    rfl
  obtain ⟨hmk, ⟨iso⟩⟩ := exists_cokernel_ofLE_iso_of_comm _ hcomm
  refine ⟨hmk, ⟨iso ≪≫ ?_⟩⟩
  have hιcok := ObjectProperty.preservesCokernels_ι
    (ModuleCat.isFG.{u + 1} (MonoidAlgebra (ZMod ℓ) K)) incl
  set j : ((ObjectProperty.ι (ModuleCat.isFG.{u + 1} (MonoidAlgebra (ZMod ℓ) K))).obj
      (cokernel incl)) ≅
      ModuleCat.of (MonoidAlgebra (ZMod ℓ) K)
        (invtAsSubmodule τ N₂ h₂ ⧸ LinearMap.range (Submodule.inclusion hsub)) :=
    PreservesCokernel.iso (ObjectProperty.ι _) incl ≪≫
      ModuleCat.cokernelIsoRangeQuotient _ with hj
  have hcardcok : Nat.card (ToType (cokernel incl).obj) = ℓ :=
    (Nat.card_congr j.toLinearEquiv.toEquiv).trans
      (card_quotient_range_inclusion τ hsub hstep.2.2)
  have htrivcok : ∀ (g : K) (w : ToType (cokernel incl).obj),
      (MonoidAlgebra.single g (1 : ZMod ℓ)) • w = w := by
    intro g w
    refine j.toLinearEquiv.injective ?_
    rw [map_smul]
    exact single_one_smul_quotient_eq τ hsub (fun g x hx ↦ hstep.2.1 g trivial x hx) g
      (j.toLinearEquiv w)
  exact (PreservesCokernel.iso Φ incl).symm ≪≫
    (hΦconst (cokernel incl) hcardcok htrivcok).some

/-- The zero submodule gives the zero subobject. -/
private theorem transportFG_isZero [Φ.Additive] [PreservesFiniteLimits Φ]
    {N : Submodule (ZMod ℓ) W} (hN : ∀ g : K, ∀ x ∈ N, τ g x ∈ N) (hbot : N = ⊥) :
    IsZero (Subobject.underlying.obj (Subobject.mk (transportFGMono eTop N hN))) := by
  have hz : IsZero (invtAsFGObject (τ := τ) N hN) := by
    rw [IsZero.iff_id_eq_zero]
    refine (ObjectProperty.ι
      (ModuleCat.isFG.{u + 1} (MonoidAlgebra (ZMod ℓ) K))).map_injective ?_
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
    exact (IsZero.iff_id_eq_zero _).1 (isZero_invtAsSubmodule_of_eq_bot τ hN hbot)
  exact IsZero.of_iso (Φ.map_isZero hz) (Subobject.underlyingIso (transportFGMono eTop N hN))

/-- The whole stalk gives the whole sheaf. -/
private theorem transportFG_isIso [Φ.Additive] [PreservesFiniteLimits Φ]
    {N : Submodule (ZMod ℓ) W} (hN : ∀ g : K, ∀ x ∈ N, τ g x ∈ N) (htop : N = ⊤) :
    IsIso (Subobject.mk (transportFGMono eTop N hN)).arrow := by
  have hisoι : IsIso ((ObjectProperty.ι
      (ModuleCat.isFG.{u + 1} (MonoidAlgebra (ZMod ℓ) K))).map
      (invtAsFGObjectι (τ := τ) N hN)) := isIso_ofHom_invtAsSubmodule_subtype τ hN htop
  have : IsIso (invtAsFGObjectι (τ := τ) N hN) :=
    isIso_of_reflects_iso (invtAsFGObjectι (τ := τ) N hN)
      (ObjectProperty.ι (ModuleCat.isFG.{u + 1} (MonoidAlgebra (ZMod ℓ) K)))
  have : IsIso (transportFGMono eTop N hN) := by
    rw [transportFGMono]
    infer_instance
  exact (Subobject.isIso_arrow_iff_eq_top _).2 (Subobject.mk_eq_top_of_isIso _)

end TransportFG

/-- **The dictionary between a locally constant sheaf of `F_ℓ`-vector spaces on `S_étale` and
the continuous representations of `π₁(S, s̄)`.** The fields are Tag 0DV5 (1) in its module form
at the base point and Tag 0DV5 (1) over a connected finite étale cover combined with Remark 0DV6
and with the identification of the image of `π₁(T, t̄) → π₁(S, s̄)` with a stabiliser. See the
discussion in the module documentation for what would discharge each of them. -/
structure FundamentalGroupModuleDictionary (ℓ : ℕ) {S : Scheme.{u}} [ConnectedSpace S]
    (s : GeometricPoint S)
    (F : Sheaf (smallEtaleTopology S) (ModuleCat.{max (u + 1) v} (ZMod ℓ))) where
  /-- **Tag 0DV5 (1)**, the module it attaches to `F`: a finite `F_ℓ`-vector space, the stalk of
  `F` at the geometric point. -/
  V : Type u
  [addCommGroup : AddCommGroup V]
  [moduleStructure : Module (ZMod ℓ) V]
  [finite : Finite V]
  /-- **Tag 0DV5 (1)**, the action it attaches to `F`: the monodromy action of `π₁(S, s̄)` on
  that vector space. -/
  ρ : Representation (ZMod ℓ) (EtaleFundamentalGroup S s) V
  /-- **Tag 0DV5 (1)**, continuity of that action: the elements of `π₁(S, s̄)` acting by a given
  endomorphism of the stalk form an open set. -/
  isOpen_rho_eq : ∀ φ : V →ₗ[ZMod ℓ] V, IsOpen {σ | ρ σ = φ}
  /-- **Tag 0DV5 (1)** over a connected finite étale cover `T` of `S`, combined with **Remark
  0DV6** and with the identification of the image of `π₁(T, t̄) → π₁(S, s̄)` with the stabiliser
  of a point of the fibre. Connectedness of `T` is spelled as transitivity of `π₁(S, s̄)` on the
  geometric fibre, which is what **Tag 0BND (1)** turns it into. The inverse image `f⁻¹F` then
  corresponds to `V` with the action of `π₁(T, t̄)`, and that action factors through any finite
  group `K` through which the stabiliser of the chosen point of the fibre acts. The
  correspondence is realized by an exact functor from modules over the group ring `F_ℓ[K]` to
  sheaves on `T_étale` which carries `V` to `f⁻¹F` and a module with `ℓ` elements and trivial
  action to the constant sheaf `Z/ℓZ_T`. Additivity of such a functor is automatic and so is
  not assumed. -/
  exists_pullbackFunctor : ∀ (T : FiniteEtaleOver S) (y : (finiteEtaleFiberFunctor s).obj T),
    (∀ z, ∃ σ : EtaleFundamentalGroup S s, σ • y = z) →
    ∀ (K : Type u) [Group K] [Finite K]
      (π : MulAction.stabilizer (EtaleFundamentalGroup S s) y →* K)
      (τ : Representation (ZMod ℓ) K V),
      (∀ σ : MulAction.stabilizer (EtaleFundamentalGroup S s) y, ρ σ.1 = τ (π σ)) →
      ∃ Φ : ModuleCat.{u} (MonoidAlgebra (ZMod ℓ) K) ⥤
          Sheaf (smallEtaleTopology T.left) (ModuleCat.{max (u + 1) v} (ZMod ℓ)),
        PreservesFiniteLimits Φ ∧ PreservesFiniteColimits Φ ∧
          Nonempty (Φ.obj (ModuleCat.of (MonoidAlgebra (ZMod ℓ) K) τ.asModule) ≅
            (smallEtalePullbackZMod ℓ T.hom).obj F) ∧
          ∀ W : ModuleCat.{u} (MonoidAlgebra (ZMod ℓ) K), Nat.card W = ℓ →
            (∀ (g : K) (w : W), (MonoidAlgebra.single g (1 : ZMod ℓ)) • w = w) →
            Nonempty (Φ.obj W ≅ constantZMod ℓ T.left)

/-- **The dictionary between a locally constant sheaf of `F_ℓ`-vector spaces on `S_étale` and
the continuous representations of `π₁(S, s̄)`, over the finitely generated modules of the group
ring.** The fields are Tag 0DV5 (3) in its module form at the base point and Tag 0DV5 (3) over a
connected finite étale cover combined with Remark 0DV6 and with the identification of the image
of `π₁(T, t̄) → π₁(S, s̄)` with a stabiliser. It is discharged by
`Stacks.EtaleCohomology.nonempty_fundamentalGroupFGModuleDictionary`. -/
structure FundamentalGroupFGModuleDictionary (ℓ : ℕ) [NeZero ℓ] {S : Scheme.{u}}
    [ConnectedSpace S] (s : GeometricPoint S)
    (F : Sheaf (smallEtaleTopology S) (ModuleCat.{max (u + 1) v} (ZMod ℓ))) where
  /-- **Tag 0DV5 (1)**, the module it attaches to `F`: a finite `F_ℓ`-vector space, the stalk of
  `F` at the geometric point. -/
  V : Type (u + 1)
  [addCommGroup : AddCommGroup V]
  [moduleStructure : Module (ZMod ℓ) V]
  [finite : Finite V]
  /-- **Tag 0DV5 (1)**, the action it attaches to `F`: the monodromy action of `π₁(S, s̄)` on
  that vector space. -/
  ρ : Representation (ZMod ℓ) (EtaleFundamentalGroup S s) V
  /-- **Tag 0DV5 (1)**, continuity of that action: the elements of `π₁(S, s̄)` acting by a given
  endomorphism of the stalk form an open set. -/
  isOpen_rho_eq : ∀ φ : V →ₗ[ZMod ℓ] V, IsOpen {σ | ρ σ = φ}
  /-- **Tag 0DV5 (1)** over a connected finite étale cover `T` of `S`, combined with **Remark
  0DV6** and with the identification of the image of `π₁(T, t̄) → π₁(S, s̄)` with the stabiliser
  of a point of the fibre. Connectedness of `T` is spelled as transitivity of `π₁(S, s̄)` on the
  geometric fibre, which is what **Tag 0BND (1)** turns it into. The inverse image `f⁻¹F` then
  corresponds to `V` with the action of `π₁(T, t̄)`, and that action factors through any finite
  group `K` through which the stabiliser of the chosen point of the fibre acts, by a homomorphism
  `π` whose fibres are open — which is what makes the action of `π₁(T, t̄)` on a module over the
  group ring continuous. The correspondence is realized by an exact functor from the *finitely
  generated* modules over the group ring `F_ℓ[K]` to sheaves on `T_étale` which carries `V` to
  `f⁻¹F` and a module with `ℓ` elements and trivial action to the constant sheaf `Z/ℓZ_T`.
  Additivity of such a functor is automatic and so is not assumed. -/
  exists_pullbackFunctor : ∀ (T : FiniteEtaleOver S) (y : (finiteEtaleFiberFunctor s).obj T),
    (∀ z, ∃ σ : EtaleFundamentalGroup S s, σ • y = z) →
    ∀ (K : Type (u + 1)) [Group K] [Finite K]
      (π : MulAction.stabilizer (EtaleFundamentalGroup S s) y →* K),
      (∀ k : K, IsOpen {σ : MulAction.stabilizer (EtaleFundamentalGroup S s) y | π σ = k}) →
      ∀ τ : Representation (ZMod ℓ) K V,
      (∀ σ : MulAction.stabilizer (EtaleFundamentalGroup S s) y, ρ σ.1 = τ (π σ)) →
      ∃ Φ : (ModuleCat.isFG.{u + 1} (MonoidAlgebra (ZMod ℓ) K)).FullSubcategory ⥤
          Sheaf (smallEtaleTopology T.left) (ModuleCat.{max (u + 1) v} (ZMod ℓ)),
        PreservesFiniteLimits Φ ∧ PreservesFiniteColimits Φ ∧
          Nonempty (Φ.obj (asFiniteTypeGroupRingModule (ZMod ℓ) τ) ≅
            (smallEtalePullbackZMod ℓ T.hom).obj F) ∧
          ∀ W : (ModuleCat.isFG.{u + 1} (MonoidAlgebra (ZMod ℓ) K)).FullSubcategory,
            Nat.card (ToType W.obj) = ℓ →
            (∀ (g : K) (w : ToType W.obj), (MonoidAlgebra.single g (1 : ZMod ℓ)) • w = w) →
            Nonempty (Φ.obj W ≅ constantZMod ℓ T.left)

/-! ### The dictionary is available -/

/-- **The dictionary of Stacks 0DV5 (3) with Remark 0DV6 is available for a finite type locally
constant sheaf of `F_ℓ`-vector spaces.** This discharges
`Stacks.EtaleCohomology.FundamentalGroupFGModuleDictionary`.

The sheaf is descended to the module universe `u + 1`, read through Tag 0DV5 (3) on Mathlib's
small étale site of a big étale site containing `S`, and its value is taken as the first field by
`Stacks.GroupCohomology.exists_representation_isOpen_rep_eq`. Over a finite étale cover `T` the
same big étale site serves, by
`AlgebraicGeometry.BigEtaleSite.contains_left_of_finiteEtaleOver`; the chosen point of the
geometric fibre is a geometric point `t` of `T` lying over `s`,
`AlgebraicGeometry.exists_geometricPoint_heq_finiteEtaleOverSourcePoint`, and the monodromy of the
cover lands in the stabiliser of that point, so the action of `π₁(T, t)` on the stalk factors
through `K`. Remark 0DV6 on Mathlib's site identifies the value of the dictionary over `T` on the
inverse image with the restriction of the value over `S`, and
`Stacks.EtaleCohomology.exists_pullbackFunctor_of_rep` builds the functor out of the group ring
from there. -/
theorem nonempty_fundamentalGroupFGModuleDictionary {ℓ : ℕ} (hℓ : ℓ.Prime) [NeZero ℓ]
    {S : Scheme.{u}} [ConnectedSpace S] (s : GeometricPoint S)
    (F : Sheaf (smallEtaleTopology S) (ModuleCat.{max (u + 1) v} (ZMod ℓ)))
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) (smallEtaleTopology S) F) :
    Nonempty (FundamentalGroupFGModuleDictionary.{v} ℓ s F) := by
  classical
  obtain ⟨F₀, hF₀, ⟨eF⟩⟩ :=
    exists_isFiniteTypeLocallyConstantModuleSheaf_smallEtale_uliftFunctor_iso.{v} S (ZMod ℓ) F hF
  set B := BigEtaleSite.containing S
  have hS : B.Contains S := BigEtaleSite.contains_containing S
  set XS : B.Scheme := ⟨S, hS⟩
  set A₀ : ObjectProperty.FullSubcategory
      (fun A : Sheaf XS.obj.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ)) ↦
        Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) XS.obj.smallEtaleTopology A) :=
    ⟨F₀, hF₀⟩
  obtain ⟨V, _, _, _, ρ, hρ, ⟨eρ⟩⟩ :=
    Stacks.GroupCohomology.exists_representation_isOpen_rep_eq.{u + 1} (ZMod ℓ)
      (EtaleFundamentalGroup S s)
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B XS s (ZMod ℓ)).functor.obj A₀)
  refine ⟨{ V := V, ρ := ρ, isOpen_rho_eq := hρ, exists_pullbackFunctor := ?_ }⟩
  intro T y htrans K _ _ π hπ τ hfac
  have hTconn : ConnectedSpace T.left := connectedSpace_left_of_exists_smul_eq htrans
  have : ConnectedSpace ((Functor.fromPUnit S).obj T.right) := ‹ConnectedSpace S›
  have : ConnectedSpace ((𝟭 Scheme.{u}).obj T.left) := hTconn
  obtain ⟨t, hts, hy⟩ := exists_geometricPoint_heq_finiteEtaleOverSourcePoint s T y
  subst hts
  have hy' : finiteEtaleOverSourcePoint (f := T.hom) T.prop t = y := eq_of_heq hy
  set XT : B.Scheme := ⟨T.left, B.contains_left_of_finiteEtaleOver T hS⟩
  set fB : XT ⟶ XS := ObjectProperty.homMk (show T.left ⟶ S from T.hom)
  set ψ := etaleFundamentalGroupMap fB.hom t
  have hmem : ∀ σ' : EtaleFundamentalGroup XT.obj t,
      ψ σ' ∈ MulAction.stabilizer (EtaleFundamentalGroup S (t.map T.hom)) y := by
    intro σ'
    rw [← hy']
    exact smul_finiteEtaleOverSourcePoint_eq T.prop t σ'
  set ψres : EtaleFundamentalGroup XT.obj t →*
      MulAction.stabilizer (EtaleFundamentalGroup S (t.map T.hom)) y :=
    { toFun := fun σ' ↦ ⟨ψ σ', hmem σ'⟩
      map_one' := by ext; simp
      map_mul' := fun a b ↦ by ext; simp }
  set π' := π.comp ψres
  have hπ'open : ∀ k : K, IsOpen {σ' : EtaleFundamentalGroup XT.obj t | π' σ' = k} := by
    intro k
    have hcont : Continuous ψres := continuous_induced_rng.2 ψ.continuous_toFun
    exact (hπ k).preimage hcont
  obtain ⟨α⟩ := nonempty_finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite_pullbackIso
    B fB (ZMod ℓ) t
  have hτρ : τ.comp π' = ρ.comp ψ.toMonoidHom :=
    MonoidHom.ext fun σ' ↦ (hfac (ψres σ')).symm
  have erep : Representation.Equiv (τ.comp π')
      (Stacks.ContinuousCohomology.rep (ZMod ℓ) (EtaleFundamentalGroup XT.obj t)
        ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B XT t (ZMod ℓ)).functor.obj
          ((etaleSiteFiniteTypeLocallyConstantModuleSheafPullback B fB (ZMod ℓ)).obj A₀)).obj) := by
    rw [hτρ]
    exact (repEquivComp (ZMod ℓ) (EtaleFundamentalGroup XT.obj t) eρ ψ.toMonoidHom).trans
      (repEquivOfIso (ZMod ℓ) (EtaleFundamentalGroup XT.obj t) (α.app A₀))
  obtain ⟨Φ, hL, hC, ⟨eTopA⟩, hconst⟩ :=
    exists_pullbackFunctor_of_rep.{v} B XT t hℓ
      ((etaleSiteFiniteTypeLocallyConstantModuleSheafPullback B fB (ZMod ℓ)).obj A₀) K π'
      hπ'open τ erep
  exact ⟨Φ, hL, hC, ⟨eTopA ≪≫ (sheafCompose XT.obj.smallEtaleTopology
        (ModuleCat.uliftFunctor.{v, u + 1} (ZMod ℓ))).mapIso
      ((etaleSiteSheafPullbackModuleIsoSheafPullback B fB (ZMod ℓ)).app F₀) ≪≫
    (smallEtaleSheafPullbackModuleUliftIso T.hom (ZMod ℓ) F₀).symm ≪≫
    (smallEtalePullbackZMod ℓ T.hom).mapIso eF⟩, hconst⟩

/-- If the fibres of a representation are open, so is the preimage of any subgroup of its
image. -/
private theorem isOpen_comap_rangeRestrict_asGroupHom {k G V : Type*} [CommSemiring k] [Group G]
    [TopologicalSpace G] [AddCommMonoid V] [Module k V] {ρ : Representation k G V}
    (hρ : ∀ φ : V →ₗ[k] V, IsOpen {σ | ρ σ = φ}) (H : Subgroup ρ.asGroupHom.range) :
    IsOpen (H.comap ρ.asGroupHom.rangeRestrict : Set G) := by
  have hcover : (H.comap ρ.asGroupHom.rangeRestrict : Set G) =
      ⋃ g : H, {σ | ρ σ = ((g : ρ.asGroupHom.range) : (V →ₗ[k] V)ˣ)} := by
    ext σ
    simp only [Set.mem_iUnion, SetLike.mem_coe, Subgroup.mem_comap, Set.mem_ofPred_eq]
    refine ⟨fun hσ ↦ ⟨⟨_, hσ⟩, (ρ.asGroupHom_apply σ).symm⟩, fun ⟨g, hg⟩ ↦ ?_⟩
    have : ρ.asGroupHom.rangeRestrict σ = (g : ρ.asGroupHom.range) :=
      Subtype.ext (Units.val_injective ((ρ.asGroupHom_apply σ).trans hg))
    rw [this]
    exact g.2
  rw [hcover]
  exact isOpen_iUnion fun _ ↦ hρ _

/-- A set identified equivariantly with `G ⧸ U` is the orbit of the point over the identity
coset. -/
private theorem exists_smul_symm_one_eq_of_equiv_quotient {G X : Type*} [Group G] [MulAction G X]
    {U : Subgroup G} (φ : X ≃ G ⧸ U) (hφ : ∀ (σ : G) (y : X), φ (σ • y) = σ • φ y) (z : X) :
    ∃ σ : G, σ • φ.symm ((1 : G) : G ⧸ U) = z := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (φ z)
  refine ⟨a, φ.injective ?_⟩
  rw [hφ, φ.apply_symm_apply, ← ha]
  change ((a * 1 : G) : G ⧸ U) = _
  rw [mul_one]

/-- For a set identified equivariantly with `G ⧸ U`, the stabilizer of the point over the
identity coset lies in `U`. -/
private theorem mem_of_smul_symm_one_eq_of_equiv_quotient {G X : Type*} [Group G] [MulAction G X]
    {U : Subgroup G} (φ : X ≃ G ⧸ U) (hφ : ∀ (σ : G) (y : X), φ (σ • y) = σ • φ y) {σ : G}
    (hσ : σ • φ.symm ((1 : G) : G ⧸ U) = φ.symm ((1 : G) : G ⧸ U)) : σ ∈ U := by
  have h₁ := congrArg φ hσ
  rw [hφ, φ.apply_symm_apply] at h₁
  have h₂ : ((σ * 1 : G) : G ⧸ U) = ((1 : G) : G ⧸ U) := h₁
  rw [mul_one] at h₂
  have h₃ : σ⁻¹ * 1 ∈ U := QuotientGroup.eq.mp h₂
  rw [mul_one] at h₃
  exact inv_mem_iff.mp h₃

/-- A set identified with the quotient by the preimage of a subgroup of index prime to `ℓ`
under a surjection has cardinality prime to `ℓ`. -/
private theorem not_dvd_natCard_of_equiv_quotient_comap {G G' X : Type*} [Group G] [Group G']
    {ℓ : ℕ} {f : G →* G'} (hf : Function.Surjective f) {H : Subgroup G'} (hH : ¬ ℓ ∣ H.index)
    (φ : X ≃ G ⧸ H.comap f) : ¬ ℓ ∣ Nat.card X := by
  rwa [Nat.card_congr φ, ← Subgroup.index_eq_card, Subgroup.index_comap_of_surjective _ hf]

/-- Every term of a rank one filtration starting at `⊥` is stable under the subgroup. -/
private theorem _root_.Representation.apply_mem_relSeries_trivialRankOneStep {ℓ : ℕ} {G V : Type*}
    [Group G] [AddCommGroup V] [Module (ZMod ℓ) V] {H : Subgroup G}
    {ρ : Representation (ZMod ℓ) G V} {Xs : RelSeries (Representation.TrivialRankOneStep H ρ)}
    (hXs : Xs.head = ⊥) : ∀ i, ∀ g ∈ H, ∀ x ∈ Xs i, ρ g x ∈ Xs i := by
  intro i
  refine Fin.cases (fun g _ x hx ↦ ?_) (fun j g hg x hx ↦ ?_) i
  · rw [(Submodule.eq_bot_iff _).1 hXs x hx, map_zero]
    exact Submodule.zero_mem _
  · exact Representation.TrivialRankOneStep.stable (Xs.step j) hg hx

/-- **A cover of degree prime to `ℓ` on whose fibre `π₁` acts through an `ℓ`-group.** For a finite
continuous representation of `π₁(S, s̄)` there are a finite étale cover `T` with a transitive fibre
of cardinality prime to `ℓ`, a finite group `H` through which the stabiliser of a point of the
fibre acts with open fibres, and a filtration of the representation of `H` by rank one steps. -/
private theorem exists_cover_sylow_filtration.{w} {ℓ : ℕ} (hℓ : ℓ.Prime) {S : Scheme.{u}}
    [ConnectedSpace S] (s : GeometricPoint S) {V : Type w} [AddCommGroup V] [Module (ZMod ℓ) V]
    [Finite V] (ρ : Representation (ZMod ℓ) (EtaleFundamentalGroup S s) V)
    (hρ : ∀ φ : V →ₗ[ZMod ℓ] V, IsOpen {σ | ρ σ = φ}) :
    ∃ (T : FiniteEtaleOver S) (y₀ : (finiteEtaleFiberFunctor s).obj T) (H : Type w) (_ : Group H)
      (_ : Finite H) (π : MulAction.stabilizer (EtaleFundamentalGroup S s) y₀ →* H)
      (τ : Representation (ZMod ℓ) H V),
      (∀ z, ∃ σ : EtaleFundamentalGroup S s, σ • y₀ = z) ∧
      (∀ k : H, IsOpen {σ : MulAction.stabilizer (EtaleFundamentalGroup S s) y₀ | π σ = k}) ∧
      (∀ σ : MulAction.stabilizer (EtaleFundamentalGroup S s) y₀, ρ σ.1 = τ (π σ)) ∧
      ¬ ℓ ∣ Nat.card ((finiteEtaleFiberFunctor s).obj T) ∧
      ∃ Xs : RelSeries (Representation.TrivialRankOneStep (⊤ : Subgroup H) τ),
        Xs.head = ⊥ ∧ Xs.last = ⊤ ∧ ∀ i, ∀ g : H, ∀ x ∈ Xs i, τ g x ∈ Xs i := by
  classical
  have : Finite (V →ₗ[ZMod ℓ] V) := Finite.of_injective _ DFunLike.coe_injective
  have : Finite (V →ₗ[ZMod ℓ] V)ˣ := Finite.of_injective Units.val Units.val_injective
  -- the image of the monodromy, a finite group acting on the stalk
  set Gρ : Subgroup (V →ₗ[ZMod ℓ] V)ˣ := ρ.asGroupHom.range
  set rb : EtaleFundamentalGroup S s →* Gρ := ρ.asGroupHom.rangeRestrict
  set ρG : Representation (ZMod ℓ) Gρ V := (Units.coeHom (V →ₗ[ZMod ℓ] V)).comp Gρ.subtype
  have hrb : ∀ σ, ρG (rb σ) = ρ σ := fun σ ↦ ρ.asGroupHom_apply σ
  -- an `ℓ`-Sylow subgroup and the rank one filtration it carries
  obtain ⟨H, hHidx, Xs, hXhead, hXlast⟩ :=
    Representation.exists_sylow_relSeries_trivialRankOneStep hℓ ρG
  -- the open subgroup of `π₁(S, s̄)` it cuts out
  set U : OpenSubgroup (EtaleFundamentalGroup S s) :=
    ⟨H.comap rb, isOpen_comap_rangeRestrict_asGroupHom hρ H⟩
  -- the cover `T = Y/H` and its fibre
  obtain ⟨T, φ, hφ⟩ := exists_finiteEtaleOver_quotient_fiber_equiv s U
  set y₀ := φ.symm ((1 : EtaleFundamentalGroup S s) :
    EtaleFundamentalGroup S s ⧸ U.toSubgroup)
  have hstab : ∀ σ : EtaleFundamentalGroup S s, σ • y₀ = y₀ → rb σ ∈ H :=
    fun _ ↦ mem_of_smul_symm_one_eq_of_equiv_quotient φ hφ
  set τ : Representation (ZMod ℓ) H V := ρG.comp H.subtype
  set π : MulAction.stabilizer (EtaleFundamentalGroup S s) y₀ →* H :=
    { toFun := fun σ ↦ ⟨rb σ.1, hstab σ.1 σ.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b ↦ by ext; simp }
  refine ⟨T, y₀, H, inferInstance, inferInstance, π, τ,
    exists_smul_symm_one_eq_of_equiv_quotient φ hφ, fun k ↦ ?_, fun σ ↦ (hrb σ.1).symm,
    not_dvd_natCard_of_equiv_quotient_comap (f := rb) ρ.asGroupHom.rangeRestrict_surjective
      hHidx φ,
    Xs.map ⟨id, fun h ↦ ⟨h.1, fun g _ x hx ↦ h.2.1 g.1 g.2 x hx, h.2.2⟩⟩, hXhead, hXlast,
    fun i g ↦ Representation.apply_mem_relSeries_trivialRankOneStep hXhead i g g.2⟩
  convert (hρ (ρG (k : Gρ))).preimage continuous_subtype_val using 1
  ext σ
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  exact ⟨fun hk ↦ (hrb σ.1).symm.trans (congrArg ρG (congrArg Subtype.val hk)),
    fun hk ↦ Subtype.ext (Subtype.ext (Units.val_injective ((hrb σ.1).trans hk)))⟩

/-- **Stacks Project, Tag 0A3R.** Let `S` be a connected scheme, let `ℓ` be a prime number and
let `F` be a finite type locally constant sheaf of `F_ℓ`-vector spaces on `S_étale`. Then there
is a finite étale morphism `f : T → S` of degree prime to `ℓ` such that `f⁻¹F` has a finite
filtration whose successive quotients are the constant sheaf `Z/ℓZ_T`.

The filtration is a chain of subobjects of `f⁻¹F` running from the zero subobject to the whole
sheaf, each step having the constant sheaf as its quotient. The local constancy of `F` enters
through the dictionary of Tag 0DV5 (3), which is
`Stacks.EtaleCohomology.nonempty_fundamentalGroupFGModuleDictionary`.

The dictionary is read at a geometric point, which the statement does not mention: a connected
space is nonempty, and `AlgebraicGeometry.GeometricPoint.ofPoint` puts a geometric point of `S`
above any of its points, so one is produced inside the proof rather than assumed. `NeZero ℓ`,
which the dictionary needs for the finiteness of `F_ℓ[K]`, comes from the primality of `ℓ`
likewise. -/
@[stacks 0A3R]
theorem exists_primeToEll_finiteEtale_constantFiltration_unconditional {ℓ : ℕ} (hℓ : ℓ.Prime)
    {S : Scheme.{u}} [ConnectedSpace S]
    (F : Sheaf (smallEtaleTopology S) (ModuleCat.{max (u + 1) v} (ZMod ℓ)))
    (_hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) (smallEtaleTopology S) F) :
    ∃ (T : Scheme.{u}) (f : T ⟶ S) (d : ℕ), IsFinite f ∧ Etale f ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d ∧ ¬ ℓ ∣ d ∧
      ∃ X : RelSeries (ConstantRankOneStep ℓ ((smallEtalePullbackZMod ℓ f).obj F)),
        IsZero (Subobject.underlying.obj X.head) ∧ IsIso X.last.arrow := by
  classical
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have s : GeometricPoint S := GeometricPoint.ofPoint S (Classical.arbitrary S)
  obtain ⟨D⟩ := nonempty_fundamentalGroupFGModuleDictionary.{v} hℓ s F _hF
  let _ := D.addCommGroup
  let _ := D.moduleStructure
  have _ := D.finite
  obtain ⟨T, y₀, H, _, _, π, τ, htrans, hπopen, hfac, hdeg, Xs, hXhead, hXlast, hinv⟩ :=
    exists_cover_sylow_filtration hℓ s D.ρ D.isOpen_rho_eq
  obtain ⟨Φ, _, _, ⟨eTop⟩, hΦconst⟩ := D.exists_pullbackFunctor T y₀ htrans H π hπopen τ hfac
  -- a left exact functor between abelian categories is additive
  have : Φ.Additive := Functor.additive_of_preserves_binary_products Φ
  refine ⟨T.left, T.hom, Nat.card ((finiteEtaleFiberFunctor s).obj T), T.prop.1, T.prop.2,
    isFiniteLocallyFreeOfRank_natCard_finiteEtaleFiber s T, hdeg,
    ⟨⟨Xs.length, fun i ↦ Subobject.mk (transportFGMono eTop (Xs i) (hinv i)), ?_⟩, ?_, ?_⟩⟩
  · -- every successive quotient is the constant sheaf
    exact fun j ↦
      transportFG_step eTop hΦconst (hinv j.castSucc) (hinv j.succ) (Xs.step j)
  · -- the filtration starts at the zero subobject
    exact transportFG_isZero eTop (hinv 0) hXhead
  · -- and ends at the whole sheaf
    exact transportFG_isIso eTop (hinv (Fin.last Xs.length)) hXlast

/-- **Stacks Project, Tag 0A3R.** Let `S` be a connected scheme, let `ℓ` be a prime number and
let `F` be a finite type locally constant sheaf of `F_ℓ`-vector spaces on `S_étale`. Then there
is a finite étale morphism `f : T → S` of degree prime to `ℓ` such that `f⁻¹F` has a finite
filtration whose successive quotients are the constant sheaf `Z/ℓZ_T`.

The filtration is a chain of subobjects of `f⁻¹F` running from the zero subobject to the whole
sheaf, each step having the constant sheaf as its quotient. The local constancy of `F` is not
used directly: it is the hypothesis under which the dictionary `D` is available, and it is kept
here because it is the hypothesis of the source. -/
theorem exists_primeToEll_finiteEtale_constantFiltration {ℓ : ℕ} (hℓ : ℓ.Prime)
    {S : Scheme.{u}} [ConnectedSpace S] (s : GeometricPoint S)
    (F : Sheaf (smallEtaleTopology S) (ModuleCat.{max (u + 1) v} (ZMod ℓ)))
    (_hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) (smallEtaleTopology S) F)
    (D : FundamentalGroupModuleDictionary ℓ s F) :
    ∃ (T : Scheme.{u}) (f : T ⟶ S) (d : ℕ), IsFinite f ∧ Etale f ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d ∧ ¬ ℓ ∣ d ∧
      ∃ X : RelSeries (ConstantRankOneStep ℓ ((smallEtalePullbackZMod ℓ f).obj F)),
        IsZero (Subobject.underlying.obj X.head) ∧ IsIso X.last.arrow := by
  classical
  let _ := D.addCommGroup
  let _ := D.moduleStructure
  have _ := D.finite
  obtain ⟨T, y₀, H, _, _, π, τ, htrans, -, hfac, hdeg, Xs, hXhead, hXlast, hinv⟩ :=
    exists_cover_sylow_filtration hℓ s D.ρ D.isOpen_rho_eq
  obtain ⟨Φ, _, _, ⟨eTop⟩, hΦconst⟩ := D.exists_pullbackFunctor T y₀ htrans H π τ hfac
  -- a left exact functor between abelian categories is additive
  have : Φ.Additive := Functor.additive_of_preserves_binary_products Φ
  refine ⟨T.left, T.hom, Nat.card ((finiteEtaleFiberFunctor s).obj T), T.prop.1, T.prop.2,
    isFiniteLocallyFreeOfRank_natCard_finiteEtaleFiber s T, hdeg,
    ⟨⟨Xs.length, fun i ↦ Subobject.mk (transportMono eTop (Xs i) (hinv i)), ?_⟩, ?_, ?_⟩⟩
  · -- every successive quotient is the constant sheaf
    exact fun j ↦ transport_step eTop hΦconst (hinv j.castSucc) (hinv j.succ) (Xs.step j)
  · -- the filtration starts at the zero subobject
    exact transport_isZero eTop (hinv 0) hXhead
  · -- and ends at the whole sheaf
    exact transport_isIso eTop (hinv (Fin.last Xs.length)) hXlast

end Stacks.EtaleCohomology

end
