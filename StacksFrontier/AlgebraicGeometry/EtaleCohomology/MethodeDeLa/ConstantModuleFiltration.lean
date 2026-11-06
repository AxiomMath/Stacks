module

public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.GroupTheory.Sylow
public import Mathlib.RepresentationTheory.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.PGroupFiltration
public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.FundamentalGroupTheorem
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FunctorsHomomorphisms.Comparison
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricFibreDegree
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
public import StacksCore.Tactic.StacksAttribute

/-!
# Filtering a locally constant sheaf of `Λ`-modules after a cover of degree prime to `ℓ`

Let `S` be an irreducible, geometrically unibranch scheme, let `ℓ` be a prime number, let `n ≥ 1`,
let `Λ` be a Noetherian ring and let `F` be a finite type locally constant sheaf of `Λ`-modules on
`S_étale` annihilated by `ℓ ^ n`. There is then a finite étale morphism `f : T → S` whose degree is
prime to `ℓ` and for which `f⁻¹F` carries a finite filtration whose successive quotients are of the
form `M_T` for finite `Λ`-modules `M`.

The proof is the one of the source. The sheaf corresponds, by Stacks Tag 0GIY, to a finite
`Λ`-module `V` with a continuous action of `π₁(S, s̄)`; the image `G` of that action is a finite
group, and the surjection `ρ̄ : π₁(S, s̄) → G` is the monodromy of a Galois cover `Y → S`. For an
`ℓ`-Sylow subgroup `H ⊆ G` the cover `T = Y/H`, which is the cover attached by Tag 0BND (1) to the
finite `π₁(S, s̄)`-set `π₁(S, s̄)/ρ̄⁻¹(H)`, has degree `[G : H]`, prime to `ℓ`. The action of
`π₁(T, t̄)` on `V` is through `H`, and Stacks Tag 0GIZ filters a module over the group ring of a
finite `ℓ`-group annihilated by `ℓ ^ n` with trivial action on every successive quotient;
transporting that filtration back through the dictionary gives the filtration of `f⁻¹F`.

## Main definitions

* `Stacks.EtaleCohomology.ConstantFiniteModuleStep`: one step of a filtration of a sheaf of
  `Λ`-modules on a small étale site whose subquotient is the constant sheaf of a finite
  `Λ`-module.
* `Stacks.EtaleCohomology.TrivialGroupRingActionStep`: one step of a filtration of a module over
  the group ring of `H` with trivial `H`-action on the quotient. This is the relation whose finite
  chains Tag 0GIZ produces.
* `Stacks.EtaleCohomology.FiniteModuleMonodromyDictionary`: the dictionary between finite type
  locally constant sheaves of `Λ`-modules and continuous finite `Λ`-modules over the étale
  fundamental group, carried as an explicit hypothesis; see below.

## Main results

* `Stacks.EtaleCohomology.exists_sylow_relSeries_trivialGroupRingActionStep`: the group-theoretic
  half of the method of the trace over a Noetherian coefficient ring — an `ℓ`-Sylow subgroup has
  index prime to `ℓ` and Tag 0GIZ filters the module over its group ring.
* `Stacks.EtaleCohomology.finite_representation_range`: a continuous representation of a compact
  group has finite image, which is why the monodromy group `G` above is finite. Over a Noetherian
  ring the stalk is a finite *module* and need not be a finite set, so finiteness of `G` cannot be
  read off the automorphism group of the stalk as it is for a prime field; compactness of
  `π₁(S, s̄)` is used instead.
* `Stacks.EtaleCohomology.exists_primeToEll_finiteEtale_finiteModuleFiltration`: Tag 0GJ0.

## The dictionary hypothesis

The translation between sheaves and modules is Stacks Tag 0GIY, which this library has only in the
restricted form `AlgebraicGeometry.finiteTypeLocallyConstantEquivContinuousModule`: that
declaration carries the topological invariance of the small étale site (Tag 04DZ), the equivalence
of finite étale covers along a universal homeomorphism (Tag 0BQN) and the tag itself for an
integral normal scheme as hypotheses. None of those is available here either, so the translation is
carried by the hypothesis `FiniteModuleMonodromyDictionary`, whose fields are exactly the
statements the proof consumes:

* `V`, `ρ`, `isOpen_rho_eq` and `annihilated` are **Tag 0GIY** at the base point: the finite
  `Λ`-module attached to `F`, its continuous monodromy action of `π₁(S, s̄)`, continuity being the
  openness of the preimage of each endomorphism, and the annihilation of `F` by `ℓ ^ n` read on
  that module.
* `exists_pullbackFunctor` is **Tag 0GIY** over a connected finite étale cover `T` of `S` —
  connectedness being spelled as transitivity of `π₁(S, s̄)` on the fibre, which is what Tag
  0BND (1) turns it into — combined with **Remark 0DV6** and with the identification of the image
  of `π₁(T, t̄) → π₁(S, s̄)` with the stabiliser of the chosen point of the fibre: the pullback
  `f⁻¹F` corresponds to `V` with the action of `π₁(T, t̄)`, and that action factors through any
  finite group `K` through which the stabiliser of the point acts, so the modules over the group
  ring `Λ[K]` map to sheaves on `T_étale` by an exact functor carrying `V` to `f⁻¹F` and a finite
  `Λ`-module with trivial action to the constant sheaf of a finite `Λ`-module. Only exactness is
  assumed of that functor: a left exact functor between abelian categories is additive, by
  `CategoryTheory.Functor.additive_of_preserves_binary_products`.

The irreducibility and geometric unibranchness of `S` are the hypotheses under which Tag 0GIY
holds, and they are stated here because the source states them; they are not used again once the
dictionary is granted. The Noetherian hypothesis on `Λ` is used directly, and is what makes the
successive quotients finite `Λ`-modules: a submodule of a finite module over a Noetherian ring is
finite, hence so is every subquotient of the stalk.

## Implementation notes

A finite filtration with prescribed successive quotients is recorded, as in
`Module.exists_relSeries_trivial_action_subquotient`, by a `RelSeries` for the relation
`ConstantFiniteModuleStep` on the lattice of subobjects of the sheaf: a pair of subobjects is a
step when the first is contained in the second and the quotient of the second by the first is the
constant sheaf of some finite `Λ`-module. That the filtration runs from the zero subobject to the
whole sheaf is stated as `IsZero` of the first term and `IsIso` of the inclusion of the last, which
are the conditions `⊥` and `⊤` in the subobject lattice.

The filtration of the stalk is produced by Tag 0GIZ as a chain of submodules over the group ring of
the Sylow subgroup, so no separate stability condition is carried: such a submodule is stable under
the group by construction. This is the one simplification over the prime field case of
`Stacks.EtaleCohomology.exists_primeToEll_finiteEtale_constantFiltration`, where the chain is one
of subspaces together with an invariance hypothesis.

The degree of the cover is read off its geometric fibre by
`AlgebraicGeometry.isFiniteLocallyFreeOfRank_natCard_finiteEtaleFiber`: the rank in the sense of
Tag 02KA of a finite étale morphism over a connected base is the number of points of its fibre at a
geometric point, so the degree of `T → S` is the index of the Sylow subgroup, and the primality to
`ℓ` of that degree is a statement about the finite group `G`.

The module universe of the sheaves is `max (u + 1) v`, the shape in which sheafification on a small
étale site is automatic, while the stalk and the finite groups acting on it are taken in `Type u`;
the dictionary functor bridges the two universes.

## References

* [Stacks Project, Tag 0GJ0](https://stacks.math.columbia.edu/tag/0GJ0)
* [Stacks Project, Tag 0GIY](https://stacks.math.columbia.edu/tag/0GIY)
* [Stacks Project, Tag 0GIZ](https://stacks.math.columbia.edu/tag/0GIZ)
* [Stacks Project, Tag 0DV6](https://stacks.math.columbia.edu/tag/0DV6)
* [Stacks Project, Tag 0BND](https://stacks.math.columbia.edu/tag/0BND)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped FintypeCatDiscrete SetRel

universe v u

namespace Stacks.EtaleCohomology

/-- Sheafification of presheaves of `Λ`-modules on a small étale site. -/
private instance hasSheafifyModuleCatOverRing (X : Scheme.{u}) (Λ : Type v) [CommRing Λ] :
    HasSheafify (smallEtaleTopology X) (ModuleCat.{max (u + 1) v} Λ) :=
  Stacks.ConstantSheaf.hasSheafify_moduleCat.{u + 1, u, v, v} _ _

/-- Sheaves of `Λ`-modules on a small étale site have an initial object. -/
private instance hasInitialSheafModuleCatOverRing (X : Scheme.{u}) (Λ : Type v) [CommRing Λ] :
    HasInitial (Sheaf (smallEtaleTopology X) (ModuleCat.{max (u + 1) v} Λ)) :=
  HasZeroObject.hasInitial

/-- The subobjects of a sheaf of `Λ`-modules have a least element, the zero subobject. -/
private instance orderBotSubobjectSheafModuleCatOverRing {X : Scheme.{u}} {Λ : Type v}
    [CommRing Λ] (A : Sheaf (smallEtaleTopology X) (ModuleCat.{max (u + 1) v} Λ)) :
    OrderBot (Subobject A) :=
  Subobject.orderBot

/-- Inverse image of sheaves of `Λ`-modules along a morphism of schemes. -/
abbrev smallEtalePullbackModuleCat (Λ : Type v) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology Y) (ModuleCat.{max (u + 1) v} Λ) ⥤
      Sheaf (smallEtaleTopology X) (ModuleCat.{max (u + 1) v} Λ) :=
  (smallEtaleBaseChange f).sheafPullback (ModuleCat.{max (u + 1) v} Λ)
    (smallEtaleTopology Y) (smallEtaleTopology X)

/-- One step of a filtration of a sheaf of `Λ`-modules on the small étale site of `X` whose
subquotient is the constant sheaf of a finite `Λ`-module: the first subobject is contained in the
second and the quotient of the second by the first is such a constant sheaf. -/
def ConstantFiniteModuleStep (Λ : Type v) [CommRing Λ] {X : Scheme.{u}}
    (A : Sheaf (smallEtaleTopology X) (ModuleCat.{max (u + 1) v} Λ)) :
    SetRel (Subobject A) (Subobject A) :=
  {p | ∃ h : p.1 ≤ p.2, ∃ M : ModuleCat.{max (u + 1) v} Λ, Module.Finite Λ M ∧
    Nonempty (cokernel (p.1.ofLE p.2 h) ≅
      (constantSheaf (smallEtaleTopology X) (ModuleCat.{max (u + 1) v} Λ)).obj M)}

/-! ### Transporting a chain of subobjects along an exact functor -/

/-- Two subobjects of `X` presented by monomorphisms `u` and `v` and a morphism `w : A ⟶ B` with
`w ≫ v = u` are comparable, and the quotient of the larger by the smaller is the cokernel of
`w`. -/
public theorem exists_cokernel_ofLE_iso_of_comm {C : Type*} [Category* C] [Abelian C]
    {X A B : C} {u : A ⟶ X} {v : B ⟶ X} [Mono u] [Mono v] (w : A ⟶ B) (hw : w ≫ v = u) :
    ∃ h : Subobject.mk u ≤ Subobject.mk v,
      Nonempty (cokernel ((Subobject.mk u).ofLE (Subobject.mk v) h) ≅ cokernel w) := by
  refine ⟨Subobject.mk_le_mk_of_comm w hw, ⟨cokernel.mapIso _ _ (Subobject.underlyingIso u)
    (Subobject.underlyingIso v) ?_⟩⟩
  rw [← cancel_mono v, Category.assoc, Category.assoc, hw,
    Subobject.underlyingIso_hom_comp_eq_mk, Subobject.underlyingIso_hom_comp_eq_mk,
    Subobject.ofLE_arrow]

/-! ### The filtration of the stalk -/

/-- The restriction of a representation to a subgroup. -/
def subgroupRepresentation {Λ : Type*} [CommRing Λ] {G V : Type*} [Group G] [AddCommGroup V]
    [Module Λ V] (ρ : Representation Λ G V) (H : Subgroup G) : Representation Λ H V :=
  ρ.comp H.subtype

/-- One step of a filtration of a module over the group ring of `H` on whose quotient `H` acts
trivially: the smaller submodule is contained in the larger, and every `g : H` moves an element of
the larger submodule by an element of the smaller one. Both terms are submodules over the group
ring, hence stable under `H` by construction.

This is the relation whose finite chains Stacks Tag 0GIZ,
`Module.exists_relSeries_trivial_action_subquotient`, produces. -/
def TrivialGroupRingActionStep (Λ : Type*) [CommRing Λ] (H : Type*) [Group H] (M : Type*)
    [AddCommGroup M] [Module (MonoidAlgebra Λ H) M] :
    SetRel (Submodule (MonoidAlgebra Λ H) M) (Submodule (MonoidAlgebra Λ H) M) :=
  {p | p.1 ≤ p.2 ∧ ∀ (g : H) (x : p.2), MonoidAlgebra.single g (1 : Λ) • (x : M) - x ∈ p.1}

/-- **The group-theoretic half of the method of the trace.** For a representation of a finite group
`G` on a `Λ`-module annihilated by `ℓ ^ n` there is a subgroup `H` whose index is prime to `ℓ` — an
`ℓ`-Sylow subgroup — such that the module over the group ring of `H` has a finite filtration
running from `⊥` to `⊤` on whose successive quotients `H` acts trivially.

The filtration is Stacks Tag 0GIZ applied to the Sylow subgroup, which is a finite `ℓ`-group; the
index of a Sylow subgroup is prime to `ℓ`. -/
theorem exists_sylow_relSeries_trivialGroupRingActionStep {Λ : Type*} [CommRing Λ]
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module Λ V] (ℓ n : ℕ) (hℓ : ℓ.Prime)
    (ρ : Representation Λ G V) (hann : ∀ x : V, (ℓ ^ n) • x = 0) :
    ∃ H : Subgroup G, ¬ ℓ ∣ H.index ∧
      ∃ X : RelSeries (TrivialGroupRingActionStep Λ H (subgroupRepresentation ρ H).asModule),
        X.head = ⊥ ∧ X.last = ⊤ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨P⟩ : Nonempty (Sylow ℓ G) := inferInstance
  exact ⟨(P : Subgroup G), P.not_dvd_index,
    Module.exists_relSeries_trivial_action_subquotient Λ _ _ ℓ n hℓ P.isPGroup'
      fun x => hann x⟩

/-- **A continuous representation of a compact group has finite image.** The elements acting by the
identity form an open subgroup, which in a compact group has finite index, and the image is the
quotient by that subgroup.

Over a Noetherian coefficient ring the stalk of a finite type locally constant sheaf is a finite
module and need not be a finite set, so the finiteness of the monodromy group cannot be read off
the automorphism group of the stalk; this is what replaces that step. -/
theorem finite_representation_range {Λ : Type*} [CommRing Λ] {W V : Type*} [Group W]
    [TopologicalSpace W] [IsTopologicalGroup W] [CompactSpace W] [AddCommGroup V] [Module Λ V]
    (ρ : Representation Λ W V) (hopen : ∀ φ : V →ₗ[Λ] V, IsOpen {σ | ρ σ = φ}) :
    Finite ρ.asGroupHom.range := by
  have hk : (ρ.asGroupHom.ker : Set W) = {σ | ρ σ = 1} := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_ofPred_eq]
    constructor
    · intro h
      have h' := congrArg Units.val h
      rw [Representation.asGroupHom_apply] at h'
      simp only [Units.val_one] at h'
      exact h'
    · intro h
      refine Units.ext ?_
      rw [Representation.asGroupHom_apply]
      simp only [Units.val_one]
      exact h
  have : Finite (W ⧸ ρ.asGroupHom.ker) :=
    Subgroup.quotient_finite_of_isOpen _ (hk ▸ hopen 1)
  exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ρ.asGroupHom).toEquiv

/-! ### Transport of a filtration of the stalk to a filtration of the sheaf -/

section Transport

variable {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ] {K V : Type u} [Group K]
  [AddCommGroup V] [Module Λ V] [Module.Finite Λ V]
  {T : Scheme.{u}} {τ : Representation Λ K V}
  {Φ : ModuleCat.{u} (MonoidAlgebra Λ K) ⥤
    Sheaf (smallEtaleTopology T) (ModuleCat.{max (u + 1) v} Λ)}
  {A : Sheaf (smallEtaleTopology T) (ModuleCat.{max (u + 1) v} Λ)}
  (eTop : Φ.obj (ModuleCat.of (MonoidAlgebra Λ K) τ.asModule) ≅ A)

/-- A submodule of the stalk over the group ring is a finite `Λ`-module: the stalk is a finite
module over the Noetherian ring `Λ`, hence Noetherian, so each of its `Λ`-submodules is finitely
generated. -/
private theorem finite_submodule_of_stalk (N : Submodule (MonoidAlgebra Λ K) τ.asModule) :
    Module.Finite Λ N := by
  have h : Module.Finite Λ (N.restrictScalars Λ) :=
    Module.Finite.iff_fg.2 (IsNoetherian.noetherian (R := Λ) (M := τ.asModule) _)
  exact h

/-- The subsheaf of `A` attached by the dictionary to a submodule of the stalk over the group
ring. -/
private def transportSubmodule (N : Submodule (MonoidAlgebra Λ K) τ.asModule) :
    Φ.obj (ModuleCat.of (MonoidAlgebra Λ K) N) ⟶ A :=
  Φ.map (ModuleCat.ofHom N.subtype) ≫ eTop.hom

private instance mono_ofHom_subtype_stalk (N : Submodule (MonoidAlgebra Λ K) τ.asModule) :
    Mono (ModuleCat.ofHom N.subtype) :=
  (ModuleCat.mono_iff_injective _).2 Subtype.val_injective

private instance monoTransportSubmodule [PreservesFiniteLimits Φ]
    (N : Submodule (MonoidAlgebra Λ K) τ.asModule) : Mono (transportSubmodule eTop N) := by
  have : Mono (Φ.map (ModuleCat.ofHom N.subtype)) := Φ.map_mono _
  exact mono_comp _ _

/-- **A step of the filtration of the stalk gives a step of the filtration of the sheaf whose
quotient is the constant sheaf of a finite `Λ`-module.** -/
private theorem transport_step [Φ.Additive] [PreservesFiniteLimits Φ]
    [PreservesFiniteColimits Φ]
    (hΦconst : ∀ (W : Type u) [AddCommGroup W] [Module Λ W] [Module (MonoidAlgebra Λ K) W]
      [IsScalarTower Λ (MonoidAlgebra Λ K) W], Module.Finite Λ W →
      (∀ (g : K) (w : W), MonoidAlgebra.single g (1 : Λ) • w = w) →
      ∃ M : ModuleCat.{max (u + 1) v} Λ, Module.Finite Λ M ∧
        Nonempty (Φ.obj (ModuleCat.of (MonoidAlgebra Λ K) W) ≅
          (constantSheaf (smallEtaleTopology T) (ModuleCat.{max (u + 1) v} Λ)).obj M))
    {N₁ N₂ : Submodule (MonoidAlgebra Λ K) τ.asModule} (hle : N₁ ≤ N₂)
    (htriv : ∀ (g : K) (x : N₂),
      MonoidAlgebra.single g (1 : Λ) • (x : τ.asModule) - x ∈ N₁) :
    (Subobject.mk (transportSubmodule eTop N₁), Subobject.mk (transportSubmodule eTop N₂)) ∈
      ConstantFiniteModuleStep Λ A := by
  have hcomm : Φ.map (ModuleCat.ofHom (Submodule.inclusion hle)) ≫
      transportSubmodule eTop N₂ = transportSubmodule eTop N₁ := by
    rw [transportSubmodule, transportSubmodule, ← Category.assoc, ← Φ.map_comp]
    rfl
  obtain ⟨hmk, ⟨iso⟩⟩ := exists_cokernel_ofLE_iso_of_comm _ hcomm
  have hfin : Module.Finite Λ N₂ := finite_submodule_of_stalk N₂
  have htrivq : ∀ (g : K) (w : N₂ ⧸ LinearMap.range (Submodule.inclusion hle)),
      MonoidAlgebra.single g (1 : Λ) • w = w := by
    intro g w
    induction w using Submodule.Quotient.induction_on with
    | H x =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      exact ⟨⟨MonoidAlgebra.single g (1 : Λ) • (x : τ.asModule) - x, htriv g x⟩, rfl⟩
  obtain ⟨M, hMfin, ⟨isoM⟩⟩ :=
    hΦconst (N₂ ⧸ LinearMap.range (Submodule.inclusion hle)) inferInstance htrivq
  refine ⟨hmk, M, hMfin, ⟨iso ≪≫ ?_⟩⟩
  exact (PreservesCokernel.iso Φ _).symm ≪≫
    Φ.mapIso (ModuleCat.cokernelIsoRangeQuotient _) ≪≫ isoM

omit [IsNoetherianRing Λ] [Module.Finite Λ V] in
/-- The zero submodule gives the zero subobject. -/
private theorem transport_isZero [Φ.Additive] [PreservesFiniteLimits Φ]
    {N : Submodule (MonoidAlgebra Λ K) τ.asModule} (hbot : N = ⊥) :
    IsZero (Subobject.underlying.obj (Subobject.mk (transportSubmodule eTop N))) := by
  have hsub : Subsingleton N := by
    subst hbot
    infer_instance
  have hz : IsZero (ModuleCat.of (MonoidAlgebra Λ K) N) := ModuleCat.isZero_of_subsingleton _
  have hΦz : IsZero (Φ.obj (ModuleCat.of (MonoidAlgebra Λ K) N)) := by
    rw [IsZero.iff_id_eq_zero] at hz ⊢
    rw [← Φ.map_id, hz, Φ.map_zero]
  exact IsZero.of_iso hΦz (Subobject.underlyingIso (transportSubmodule eTop N))

omit [IsNoetherianRing Λ] [Module.Finite Λ V] in
/-- The whole stalk gives the whole sheaf. -/
private theorem transport_isIso [Φ.Additive] [PreservesFiniteLimits Φ]
    {N : Submodule (MonoidAlgebra Λ K) τ.asModule} (htop : N = ⊤) :
    IsIso (Subobject.mk (transportSubmodule eTop N)).arrow := by
  have hepi : Epi (ModuleCat.ofHom N.subtype) :=
    (ModuleCat.epi_iff_surjective _).2 fun x ↦ ⟨⟨x, Submodule.eq_top_iff'.1 htop x⟩, rfl⟩
  have hiso : IsIso (ModuleCat.ofHom N.subtype) := isIso_of_mono_of_epi _
  have : IsIso (transportSubmodule eTop N) := by
    rw [transportSubmodule]
    infer_instance
  rw [← Subobject.underlyingIso_hom_comp_eq_mk (transportSubmodule eTop N)]
  infer_instance

include eTop in
/-- **Transport of a whole filtration of the stalk to a filtration of the sheaf.** A chain of
submodules of the stalk over the group ring running from `⊥` to `⊤`, with trivial action on every
successive quotient, becomes a chain of subobjects of the sheaf running from the zero subobject to
the whole sheaf whose successive quotients are constant sheaves of finite `Λ`-modules. -/
private theorem exists_relSeries_constantFiniteModuleStep [PreservesFiniteLimits Φ]
    [PreservesFiniteColimits Φ]
    (hΦconst : ∀ (W : Type u) [AddCommGroup W] [Module Λ W] [Module (MonoidAlgebra Λ K) W]
      [IsScalarTower Λ (MonoidAlgebra Λ K) W], Module.Finite Λ W →
      (∀ (g : K) (w : W), MonoidAlgebra.single g (1 : Λ) • w = w) →
      ∃ M : ModuleCat.{max (u + 1) v} Λ, Module.Finite Λ M ∧
        Nonempty (Φ.obj (ModuleCat.of (MonoidAlgebra Λ K) W) ≅
          (constantSheaf (smallEtaleTopology T) (ModuleCat.{max (u + 1) v} Λ)).obj M))
    (Xs : RelSeries (TrivialGroupRingActionStep Λ K τ.asModule))
    (hXhead : Xs.head = ⊥) (hXlast : Xs.last = ⊤) :
    ∃ X : RelSeries (ConstantFiniteModuleStep Λ A),
      IsZero (Subobject.underlying.obj X.head) ∧ IsIso X.last.arrow := by
  have : Φ.Additive := Functor.additive_of_preserves_binary_products Φ
  exact ⟨⟨Xs.length, fun i ↦ Subobject.mk (transportSubmodule eTop (Xs i)),
      fun j ↦ transport_step eTop hΦconst (Xs.step j).1 (Xs.step j).2⟩,
    transport_isZero eTop hXhead, transport_isIso eTop hXlast⟩

end Transport

/-! ### The cover attached to an open subgroup of the fundamental group -/

/-- The finite étale cover attached to a finite continuous `π₁(S, s̄)`-set by Tag 0BND (1),
together with the equivariant identification of its geometric fibre with that set. -/
public theorem exists_finiteEtaleOver_fiber_equiv {S : Scheme.{u}} [ConnectedSpace S]
    (s : GeometricPoint S) (A : ContAction FintypeCat.{u} (EtaleFundamentalGroup S s)) :
    ∃ (T : FiniteEtaleOver S) (e : (finiteEtaleFiberFunctor s).obj T ≃ A.obj.V),
      ∀ (σ : EtaleFundamentalGroup S s) (y : (finiteEtaleFiberFunctor s).obj T),
        e (σ • y) = (A.obj.ρ σ).asHom.hom (e y) := by
  obtain ⟨E, α, hα⟩ := exists_finiteEtaleEquivalence S s
  refine ⟨E.inverse.obj A, (α.app (E.inverse.obj A)).toEquiv.symm.trans
    (((forget₂ (ContAction FintypeCat.{u} (EtaleFundamentalGroup S s)) FintypeCat.{u} ⋙
      FintypeCat.incl).mapIso (E.counitIso.app A)).toEquiv), fun σ y ↦ ?_⟩
  have h₁ : (α.app (E.inverse.obj A)).toEquiv.symm (σ • y) =
      ((E.functor.obj (E.inverse.obj A)).obj.ρ σ).asHom.hom
        ((α.app (E.inverse.obj A)).toEquiv.symm y) := by
    apply (α.app (E.inverse.obj A)).toEquiv.symm_apply_eq.2
    refine ((hα (E.inverse.obj A) σ ((α.app (E.inverse.obj A)).toEquiv.symm y)).trans ?_).symm
    show (σ.asIso.hom.app (E.inverse.obj A)).hom
      ((α.app (E.inverse.obj A)).toEquiv ((α.app (E.inverse.obj A)).toEquiv.symm y)) = σ • y
    rw [Equiv.apply_symm_apply]
    rfl
  show (((forget₂ (ContAction FintypeCat.{u} (EtaleFundamentalGroup S s)) FintypeCat.{u} ⋙
    FintypeCat.incl).mapIso (E.counitIso.app A)).hom)
      ((α.app (E.inverse.obj A)).toEquiv.symm (σ • y)) = _
  rw [h₁]
  exact ConcreteCategory.congr_hom ((E.counitIso.app A).hom.hom.comm σ)
    ((α.app (E.inverse.obj A)).toEquiv.symm y)

/-- The finite étale cover attached to an open subgroup `U` of `π₁(S, s̄)`: its geometric fibre is
the coset space `π₁(S, s̄)/U` as a `π₁(S, s̄)`-set. -/
public theorem exists_finiteEtaleOver_quotient_fiber_equiv {S : Scheme.{u}} [ConnectedSpace S]
    (s : GeometricPoint S) (U : OpenSubgroup (EtaleFundamentalGroup S s)) :
    ∃ (T : FiniteEtaleOver S)
      (φ : (finiteEtaleFiberFunctor s).obj T ≃ EtaleFundamentalGroup S s ⧸ U.toSubgroup),
      ∀ (σ : EtaleFundamentalGroup S s) (y : (finiteEtaleFiberFunctor s).obj T),
        φ (σ • y) = σ • φ y := by
  have := compactSpace_etaleFundamentalGroup S s
  obtain ⟨T, e, he⟩ := exists_finiteEtaleOver_fiber_equiv s (quotientContActionSwitch U)
  refine ⟨T, e.trans (FintypeCat.uSwitchEquiv _), fun σ y ↦ ?_⟩
  show FintypeCat.uSwitchEquiv _ (e (σ • y)) = σ • FintypeCat.uSwitchEquiv _ (e y)
  rw [he]
  exact (FintypeCat.uSwitchEquiv_naturality ((quotientContAction U).obj.ρ σ).asHom (e y)).symm

/-- **The cover `Y/H` attached to a subgroup `H` of a discrete quotient of `π₁(S, s̄)`.** Its
geometric fibre is a single orbit of cardinality the index of `H`, and the stabiliser of its
distinguished point is carried into `H`.

This is the cover `T` of the source's proof, obtained from the open subgroup `ρ̄⁻¹(H)`. -/
private theorem exists_finiteEtaleOver_index_transitive_stabilizer {S : Scheme.{u}}
    [ConnectedSpace S] (s : GeometricPoint S) {G : Type u} [Group G]
    (rb : EtaleFundamentalGroup S s →* G) (hrbsurj : Function.Surjective rb) (H : Subgroup G)
    (hUopen : IsOpen ((H.comap rb : Subgroup (EtaleFundamentalGroup S s)) :
      Set (EtaleFundamentalGroup S s))) :
    ∃ (T : FiniteEtaleOver S) (y : (finiteEtaleFiberFunctor s).obj T),
      Nat.card ((finiteEtaleFiberFunctor s).obj T) = H.index ∧
      (∀ z, ∃ σ : EtaleFundamentalGroup S s, σ • y = z) ∧
      (∀ σ : EtaleFundamentalGroup S s, σ • y = y → rb σ ∈ H) := by
  set U : OpenSubgroup (EtaleFundamentalGroup S s) := ⟨H.comap rb, hUopen⟩ with hU
  obtain ⟨T, φ, hφ⟩ := exists_finiteEtaleOver_quotient_fiber_equiv s U
  set y₀ := φ.symm ((1 : EtaleFundamentalGroup S s) :
    EtaleFundamentalGroup S s ⧸ U.toSubgroup) with hy₀
  have hφy₀ : φ y₀ = ((1 : EtaleFundamentalGroup S s) :
      EtaleFundamentalGroup S s ⧸ U.toSubgroup) := φ.apply_symm_apply _
  refine ⟨T, y₀, ?_, ?_, ?_⟩
  · rw [Nat.card_congr φ, ← Subgroup.index_eq_card]
    show (H.comap rb).index = H.index
    rw [Subgroup.index_comap_of_surjective _ hrbsurj]
  · intro z
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (φ z)
    refine ⟨a, φ.injective ?_⟩
    rw [hφ, hφy₀, ← ha]
    show ((a * 1 : EtaleFundamentalGroup S s) : EtaleFundamentalGroup S s ⧸ U.toSubgroup) = _
    rw [mul_one]
  · intro σ hσ
    have h1 : σ • φ y₀ = φ y₀ := by rw [← hφ, hσ]
    rw [hφy₀] at h1
    have h2 : ((σ * 1 : EtaleFundamentalGroup S s) :
        EtaleFundamentalGroup S s ⧸ U.toSubgroup) = ((1 : EtaleFundamentalGroup S s) : _) := h1
    rw [mul_one] at h2
    have h3 : σ⁻¹ * 1 ∈ U.toSubgroup := QuotientGroup.eq.mp h2
    rw [mul_one] at h3
    exact U.toSubgroup.inv_mem h3

/-- The homomorphism from the stabiliser of a point of the geometric fibre to a subgroup of a
discrete quotient of `π₁(S, s̄)` which that stabiliser lands in. -/
private def stabilizerToSubgroup {S : Scheme.{u}} [ConnectedSpace S] (s : GeometricPoint S)
    {G : Type u} [Group G] (rb : EtaleFundamentalGroup S s →* G) {H : Subgroup G}
    {T : FiniteEtaleOver S} {y : (finiteEtaleFiberFunctor s).obj T}
    (hstab : ∀ σ : EtaleFundamentalGroup S s, σ • y = y → rb σ ∈ H) :
    MulAction.stabilizer (EtaleFundamentalGroup S s) y →* H where
  toFun σ := ⟨rb σ.1, hstab σ.1 σ.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

/-- **The preimage of a subgroup of the monodromy image is open.** It is the union, over the
elements of that subgroup, of the sets of elements of `π₁(S, s̄)` acting by a given endomorphism of
the stalk, each of which is open by continuity of the action. -/
private theorem isOpen_comap_subgroup_of_isOpen_rho_eq {Λ : Type v} [CommRing Λ]
    {W V : Type*} [Group W] [TopologicalSpace W] [AddCommGroup V] [Module Λ V]
    (ρ : Representation Λ W V) (hopen : ∀ φ : V →ₗ[Λ] V, IsOpen {σ | ρ σ = φ})
    (H : Subgroup ρ.asGroupHom.range) :
    IsOpen ((H.comap ρ.asGroupHom.rangeRestrict : Subgroup W) : Set W) := by
  have hinj : Function.Injective
      ((Units.coeHom (V →ₗ[Λ] V)).comp ρ.asGroupHom.range.subtype) :=
    fun _ _ hab ↦ Subtype.ext (Units.val_injective hab)
  have hcover : ((H.comap ρ.asGroupHom.rangeRestrict : Subgroup W) : Set W) =
      ⋃ g : H, {σ | ρ σ = ((Units.coeHom (V →ₗ[Λ] V)).comp
        ρ.asGroupHom.range.subtype) (g : ρ.asGroupHom.range)} := by
    ext σ
    simp only [Set.mem_iUnion, SetLike.mem_coe, Subgroup.mem_comap, Set.mem_ofPred_eq]
    refine ⟨fun hσ ↦ ⟨⟨ρ.asGroupHom.rangeRestrict σ, hσ⟩, (ρ.asGroupHom_apply σ).symm⟩, ?_⟩
    rintro ⟨g, hg⟩
    have hσg : ρ.asGroupHom.rangeRestrict σ = (g : ρ.asGroupHom.range) :=
      hinj ((ρ.asGroupHom_apply σ).trans hg)
    rw [hσg]
    exact g.2
  rw [hcover]
  exact isOpen_iUnion fun g ↦ hopen _

/-! ### The dictionary and the tag -/

/-- **The dictionary between a finite type locally constant sheaf of `Λ`-modules on `S_étale` and
the continuous finite `Λ`-modules over `π₁(S, s̄)`.** The fields are Stacks Tag 0GIY at the base
point and Tag 0GIY over a connected finite étale cover combined with Remark 0DV6 and with the
identification of the image of `π₁(T, t̄) → π₁(S, s̄)` with a stabiliser. See the discussion in the
module documentation for what would discharge each of them. -/
structure FiniteModuleMonodromyDictionary (Λ : Type v) [CommRing Λ] (ℓ n : ℕ) {S : Scheme.{u}}
    [ConnectedSpace S] (s : GeometricPoint S)
    (F : Sheaf (smallEtaleTopology S) (ModuleCat.{max (u + 1) v} Λ)) where
  /-- **Tag 0GIY**, the module it attaches to `F`: a finite `Λ`-module, the stalk of `F` at the
  geometric point. -/
  V : Type u
  [addCommGroup : AddCommGroup V]
  [moduleStructure : Module Λ V]
  [moduleFinite : Module.Finite Λ V]
  /-- **Tag 0GIY**, the action it attaches to `F`: the monodromy action of `π₁(S, s̄)` on that
  module. -/
  ρ : Representation Λ (EtaleFundamentalGroup S s) V
  /-- **Tag 0GIY**, continuity of that action: the elements of `π₁(S, s̄)` acting by a given
  endomorphism of the stalk form an open set. -/
  isOpen_rho_eq : ∀ φ : V →ₗ[Λ] V, IsOpen {σ | ρ σ = φ}
  /-- **Tag 0GIY**, the annihilation of `F` by `ℓ ^ n` read on the stalk. -/
  annihilated : ∀ x : V, (ℓ ^ n) • x = 0
  /-- **Tag 0GIY** over a connected finite étale cover `T` of `S`, combined with **Remark 0DV6**
  and with the identification of the image of `π₁(T, t̄) → π₁(S, s̄)` with the stabiliser of a
  point of the fibre. Connectedness of `T` is spelled as transitivity of `π₁(S, s̄)` on the
  geometric fibre, which is what **Tag 0BND (1)** turns it into. The inverse image `f⁻¹F` then
  corresponds to `V` with the action of `π₁(T, t̄)`, and that action factors through any finite
  group `K` through which the stabiliser of the chosen point of the fibre acts. The correspondence
  is realized by an exact functor from modules over the group ring `Λ[K]` to sheaves on `T_étale`
  which carries `V` to `f⁻¹F` and a finite `Λ`-module with trivial action to the constant sheaf of
  a finite `Λ`-module. Additivity of such a functor is automatic and so is not assumed. -/
  exists_pullbackFunctor : ∀ (T : FiniteEtaleOver S) (y : (finiteEtaleFiberFunctor s).obj T),
    (∀ z, ∃ σ : EtaleFundamentalGroup S s, σ • y = z) →
    ∀ (K : Type u) [Group K] [Finite K]
      (π : MulAction.stabilizer (EtaleFundamentalGroup S s) y →* K)
      (τ : Representation Λ K V),
      (∀ σ : MulAction.stabilizer (EtaleFundamentalGroup S s) y, ρ σ.1 = τ (π σ)) →
      ∃ Φ : ModuleCat.{u} (MonoidAlgebra Λ K) ⥤
          Sheaf (smallEtaleTopology T.left) (ModuleCat.{max (u + 1) v} Λ),
        PreservesFiniteLimits Φ ∧ PreservesFiniteColimits Φ ∧
          Nonempty (Φ.obj (ModuleCat.of (MonoidAlgebra Λ K) τ.asModule) ≅
            (smallEtalePullbackModuleCat Λ T.hom).obj F) ∧
          ∀ (W : Type u) [AddCommGroup W] [Module Λ W] [Module (MonoidAlgebra Λ K) W]
            [IsScalarTower Λ (MonoidAlgebra Λ K) W], Module.Finite Λ W →
            (∀ (g : K) (w : W), MonoidAlgebra.single g (1 : Λ) • w = w) →
            ∃ M : ModuleCat.{max (u + 1) v} Λ, Module.Finite Λ M ∧
              Nonempty (Φ.obj (ModuleCat.of (MonoidAlgebra Λ K) W) ≅
                (constantSheaf (smallEtaleTopology T.left)
                  (ModuleCat.{max (u + 1) v} Λ)).obj M)

/-- **Stacks Project, Tag 0GJ0.** Let `S` be an irreducible, geometrically unibranch scheme, let
`ℓ` be a prime number, let `n ≥ 1`, let `Λ` be a Noetherian ring and let `F` be a finite type
locally constant sheaf of `Λ`-modules on `S_étale` annihilated by `ℓ ^ n`. Then there is a finite
étale morphism `f : T → S` of degree prime to `ℓ` such that `f⁻¹F` has a finite filtration whose
successive quotients are of the form `M_T` for finite `Λ`-modules `M`.

The filtration is a chain of subobjects of `f⁻¹F` running from the zero subobject to the whole
sheaf, each step having the constant sheaf of a finite `Λ`-module as its quotient.

The irreducibility and geometric unibranchness of `S` and the local constancy of `F` are the
hypotheses under which the dictionary `D` of Stacks Tag 0GIY is available. The annihilation of `F`
by `ℓ ^ n` is stated twice: on the sections of `F`, as `_hann`, because the source states it there,
and on the module the dictionary attaches to `F`, as the field `D.annihilated`, because that is the
form Tag 0GIZ consumes. Transporting the first to the second is part of Tag 0GIY and so is part of
what `D` carries; nothing here derives one from the other. -/
@[stacks 0GJ0 "granted hypothesis D, the Stacks 0GIY dictionary in finite-module form"]
theorem exists_primeToEll_finiteEtale_finiteModuleFiltration {ℓ n : ℕ} (hℓ : ℓ.Prime)
    (_hn : 1 ≤ n) {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ]
    {S : Scheme.{u}} [IrreducibleSpace S] (_hS : IsGeometricallyUnibranch S)
    (s : GeometricPoint S)
    (F : Sheaf (smallEtaleTopology S) (ModuleCat.{max (u + 1) v} Λ))
    (_hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ (smallEtaleTopology S) F)
    (_hann : ∀ (U : S.Etale) (x : F.obj.obj (Opposite.op U)), (ℓ ^ n) • x = 0)
    (D : FiniteModuleMonodromyDictionary Λ ℓ n s F) :
    ∃ (T : Scheme.{u}) (f : T ⟶ S) (d : ℕ), IsFinite f ∧ Etale f ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d ∧ ¬ ℓ ∣ d ∧
      ∃ X : RelSeries (ConstantFiniteModuleStep Λ
          ((smallEtalePullbackModuleCat Λ f).obj F)),
        IsZero (Subobject.underlying.obj X.head) ∧ IsIso X.last.arrow := by
  classical
  let _ := D.addCommGroup
  let _ := D.moduleStructure
  have _ := D.moduleFinite
  have := compactSpace_etaleFundamentalGroup S s
  -- the image of the monodromy, a finite group acting on the stalk
  have hfinrange : Finite D.ρ.asGroupHom.range :=
    finite_representation_range D.ρ D.isOpen_rho_eq
  set rb : EtaleFundamentalGroup S s →* D.ρ.asGroupHom.range := D.ρ.asGroupHom.rangeRestrict
  set ρG : Representation Λ D.ρ.asGroupHom.range D.V :=
    (Units.coeHom (D.V →ₗ[Λ] D.V)).comp D.ρ.asGroupHom.range.subtype
  have hrb : ∀ σ, ρG (rb σ) = D.ρ σ := fun σ ↦ D.ρ.asGroupHom_apply σ
  have hrbsurj : Function.Surjective rb := D.ρ.asGroupHom.rangeRestrict_surjective
  -- an `ℓ`-Sylow subgroup and the filtration it carries
  obtain ⟨H, hHidx, Xs, hXhead, hXlast⟩ :=
    exists_sylow_relSeries_trivialGroupRingActionStep ℓ n hℓ ρG fun x ↦ D.annihilated x
  -- the cover `T = Y/H`, its degree and the stabiliser of its distinguished point
  obtain ⟨T, y₀, hdeg, htrans, hstab⟩ :=
    exists_finiteEtaleOver_index_transitive_stabilizer s rb hrbsurj H
      (isOpen_comap_subgroup_of_isOpen_rho_eq D.ρ D.isOpen_rho_eq H)
  -- the dictionary over the cover, for the Sylow subgroup
  have hfac : ∀ σ : MulAction.stabilizer (EtaleFundamentalGroup S s) y₀,
      D.ρ σ.1 = subgroupRepresentation ρG H (stabilizerToSubgroup s rb hstab σ) :=
    fun σ ↦ (hrb σ.1).symm
  obtain ⟨Φ, _, _, ⟨eTop⟩, hΦconst⟩ := D.exists_pullbackFunctor T y₀ htrans H
    (stabilizerToSubgroup s rb hstab) (subgroupRepresentation ρG H) hfac
  refine ⟨T.left, T.hom, Nat.card ((finiteEtaleFiberFunctor s).obj T), T.prop.1, T.prop.2,
    isFiniteLocallyFreeOfRank_natCard_finiteEtaleFiber s T, ?_, ?_⟩
  · rw [hdeg]
    exact hHidx
  · exact exists_relSeries_constantFiniteModuleStep eTop hΦconst Xs hXhead hXlast

end Stacks.EtaleCohomology

end
