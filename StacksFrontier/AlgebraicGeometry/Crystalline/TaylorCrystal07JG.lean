module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CoordinateOperatorsUnique
public import StacksFrontier.AlgebraicGeometry.Crystalline.LevelLimitPAdicComplete

/-!
# The functor of Tag 07JG with items (07JB), (07JD) and (07JE) proved

[Stacks, Lemma 60.17.3, Tag 07JG] asserts a functor from the crystals in quasi-coherent
`𝒪_{X/S}`-modules on `Cris(X/S)` to the pairs `(M, ∇)` satisfying its four items: `M` a
`p`-adically complete `D`-module (07JB), `∇` a connection (07JC), `∇` integrable (07JD) and `∇`
topologically quasi-nilpotent (07JE).

`Crystalline.firstOrderCrystalsToPairs` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalsToPairs.lean` is such a functor out of the
first-order comparison data over `D`, and it proves item (07JC) — the connection and its Leibniz
rule — from the comparison map.  The other three items it does not prove: they are the fields
`isPAdicallyComplete`, `isIntegrable`, `isTopologicallyQuasiNilpotent` and
`hasCoordinateOperators` of `Crystalline.FirstOrderCrystal`, which that functor copies into the
corresponding fields of `Crystalline.Pair`.

**This module replaces those four fields by the data the source's own proof works with, and
derives the four items from it.**  The source category is `Crystalline.TaylorCrystal`, whose
fields beyond the comparison map are:

* the tower `(M_e)` of levels, the transition maps, an exponent shift `N`, the annihilation
  `p^{N+e} M_e = 0`, and the identification `M ≅ lim_e M_e` — which is the source's
  `M = lim_e Γ(T_e, ℱ)` with `T_e = Spec(D_e)`;
* the coordinate operators `θ_i` and the composite operators `θ_K`, the identity
  `θ_K = ∏_i θ_i^{k_i}` the source reads off `D(2)`, the expansion `∇ m = ∑_i θ_i(m) d x_i` it
  reads off `D(1)`, and the `p`-adic convergence of that expansion over `D(1)`, in the form of
  the finiteness of `{K : θ_K(m) ∉ p M}`.

From these, (07JB) is `Crystalline.invLimit_isAdicComplete_of_shift` — [Stacks, Algebra Lemma
10.98.2, Tag 09B8] in the weaker form of [Stacks, Tag 0G1Q], with the shifted exponent the
levels of [Stacks, Proposition 60.21.1, Tag 07JN] are cut out at — transported along the
identification; (07JD) and (07JE) are `Crystalline.isIntegrable_of_isThetaMonomialFamily` and
`Crystalline.isTopologicallyQuasiNilpotent_of_isThetaMonomialFamily`, which remove the quantifier
over *all* coordinate expansions by `Crystalline.eq_of_isCoordinateExpansion`, the uniqueness of
the coordinate operators of a completed connection; and the non-vacuity clause
`hasCoordinateOperators` is the expansion itself.  None of the four predicates is weakened:
`Crystalline.IsPAdicallyComplete`, `Crystalline.IsIntegrable`,
`Crystalline.IsTopologicallyQuasiNilpotent` and the existential of `Crystalline.Pair` are used
exactly as `StacksFrontier/AlgebraicGeometry/Crystalline/CompletedConnection.lean` states them.

## Main definitions

Everything is in the namespace `Crystalline`.

* `Crystalline.TaylorCrystal` — **the source category**: a `D`-module with a first-order
  comparison datum, a tower of levels realising it as `lim_e M_e`, and the composite coordinate
  operators of the expansion over `D(1)`.
* `Crystalline.TaylorCrystal.toFirstOrderCrystal` — the object of
  `Crystalline.FirstOrderCrystal` it determines, whose four propositional fields are the four
  theorems below.
* `Crystalline.forgetToFirstOrderCrystal` — that assignment as a functor; the morphisms of
  `Crystalline.TaylorCrystal` are by definition the morphisms of the images, so it is faithful
  and full on the nose.
* `Crystalline.taylorCrystalsToPairs` — **[Stacks, Lemma 60.17.3, Tag 07JG]** in the affine
  algebraic form of this file.

## Main results

* `Crystalline.TaylorCrystal.isPAdicallyComplete` — **item (07JB)**, from the tower.
* `Crystalline.TaylorCrystal.isHausdorff` — the Hausdorff half of it, which is what items (07JD)
  and (07JE) consume.
* `Crystalline.TaylorCrystal.hasCoordinateOperators` — the non-vacuity clause of
  `Crystalline.Pair`.
* `Crystalline.TaylorCrystal.isIntegrable` — **item (07JD)**.
* `Crystalline.TaylorCrystal.isTopologicallyQuasiNilpotent` — **item (07JE)**.
* `Crystalline.taylorCrystalsToPairs_obj_nabla` — the connection of the image pair is the
  completed connection of the comparison datum, which is item (07JC).

## The generality achieved, and what is still carried

**The basis.**  Items (07JD) and (07JE) are proved for a `D`-module `Ω` with an honest
`Module.Basis ι D Ω` on the differentials `d x_i`, for an arbitrary index type `ι`, and
`Crystalline.TaylorCrystal` takes that basis among its parameters.  In the source's own situation
`Ω = Ω_D` is the `p`-adic completion of a direct sum over the coordinates, and it is free on the
`d x_i` **only when the coordinates are finitely many**: the sentence after (60.17.1.1) of
[Stacks, Tag 07J9] writes an element of `Ω_D` as `∑ f_i d x_i`, which for an infinite index set is
a convergent series and not a finite linear combination.  The same asymmetry is recorded, for the
companion hypothesis `hlift`, by
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedTensorFreeFinite.lean`, where finiteness is
not removable.  **So the generality reached here is: a finite set of coordinates** — or, more
precisely, any `(Ω, d x)` in which the differentials are a basis in the algebraic sense, which for
`Ω_D` means a finite index set.  For infinitely many coordinates a topological-basis form of
`Crystalline.eq_of_isCoordinateExpansion` would be needed, with the coordinate functionals of a
completed direct sum in place of `Crystalline.tensorCoordinate`; this module does not have it, and
the statements below do not silently cover that case — they ask for `Module.Basis ι D Ω`, which in
it does not exist.

**The monomial family.**  The identity `θ_K = ∏_i θ_i^{k_i}`, the field
`isThetaMonomialFamily`, is the one genuinely geometric input and it is not derived: the source
gets it by comparing coefficients of the two expansions of `c` in
`M ⊗̂_{D, q_2} D(2)`, using that `D(2)` is the `p`-adic completion of the divided power polynomial
ring on `ζ_i, ζ'_i` with `ζ''_i = ζ_i + ζ'_i`.  Its consequence `θ_i ∘ θ_j = θ_j ∘ θ_i` is
`Crystalline.IsThetaMonomialFamily.comm`, which is already the content of item (07JD) — what this
module adds on top of it is the quantifier.

**The convergence.**  The field `finite_thetaPow_notMem_pSmul` is the source's "as the sum
expressing `c(m ⊗ 1)` above has to converge `p`-adically we conclude that for each `i` and each
`m ∈ M` only a finite number of `θ_i^k(m)` are allowed to be nonzero modulo `p`", read as the
finiteness of the set of multi-indices.  It is not a strengthening of item (07JE):
`Crystalline.finite_thetaPow_notMem_pSmul_of_isTopologicallyQuasiNilpotent` derives it from that
item.

**The reduction from `Cris(X/S)`.**  What stands between the tag's own source and this one is
unchanged from `Crystalline.firstOrderCrystalsToPairs` and is listed in the module documentation
of `StacksFrontier/AlgebraicGeometry/Crystalline/CrystalsToPairs.lean`: the sections of
`SheafOfModules.pullback` as a base change, and the quasi-coherence clause.  **So the source of
the functor below is not the tag's source**; the functor out of the crystals in quasi-coherent
modules themselves is `Crystalline.GlobalCrystallineSituation.SmallSite.crystalPairFunctor` of
`SmallSite/CrystalPairFunctor07JG.lean`.  What the functor below gives is the four items of the
target, proved, over a source that packages the comparison datum, the tower and the coordinate
expansions which the source's proof *derives* from a crystal.

A crystal on `Cris(X/S)` determines the geometric comparison datum, functorially — that is
`Crystalline.GlobalCrystallineSituation.SmallSite.firstOrderComparison` and
`...firstOrderComparison_naturality` — and `M = lim_e Γ(T_e, ℱ)` over the levels of
[Stacks, Tag 07JN] is a `D`-module, functorially, by
`...SmallSite.LevelComparison07JG.functor` of
`StacksFrontier/AlgebraicGeometry/Crystalline/LevelFirstOrderCrystal.lean`.  The geometric half of
item (07JB) is that the limit of the sections over those levels is `p`-adically complete, by
`...SmallSite.isPAdicallyComplete_wholeSpaceLevelScalars_sections`.  Reading the comparison datum
on `M` is the base change `Crystalline.GlobalCrystallineSituation.FirstOrderIdealBaseChange`,
which comes from invertibility of the comparison map of *presheaves* of modules,
`...GlobalCrystallineSituation.IsCrystal`, and not from the sheaf-level crystal condition
`...SmallSite.IsSheafCrystal`, the two being separated by the sheafification unit of
`W ↦ 𝒪_{T'}(W) ⊗_{𝒪_T(W)} ℱ_T(W)`, which is where quasi-coherence enters.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
* [Stacks Project, Tag 07JC](https://stacks.math.columbia.edu/tag/07JC)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
* [Stacks Project, Algebra Lemma 10.98.2, Tag 09B8](https://stacks.math.columbia.edu/tag/09B8)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u v uA uI uM

namespace Crystalline

/-! ### The source category -/

/-- **The source of the functor of [Stacks, Lemma 60.17.3, Tag 07JG]**, carrying the data the
source's own proof produces rather than the conclusions it draws from them.

Beyond the first-order comparison datum `Crystalline.FirstOrderComparison` — from which item
(07JC), the connection `∇ : M → M ⊗̂_D Ω` and its Leibniz rule, is proved in
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalsToPairs.lean` — an object consists of:

* the tower of levels `M_e` with its transition maps and the identification `M ≅ lim_e M_e`,
  together with an exponent shift `N` and the annihilation `p^{N+e} M_e = 0`.  In the source
  `M_e = Γ(T_e, ℱ)` for `T_e = Spec(D_e)` and `M = lim_e M_e`; the shift is there because the
  levels of [Stacks, Proposition 60.21.1, Tag 07JN] are `D(n)/(p)^{N+e}`, and only the
  annihilation is asked for, not the source's stronger `M_e = M_{e+1}/p^e M_{e+1}`;
* the coordinate operators `θ_i` and the composite operators `θ_K` of the expansion
  `c(m ⊗ 1) = ∑_K θ_K(m) ⊗ ∏ ξ_i^{[k_i]}` over `D(1)`, with the identity `θ_K = ∏_i θ_i^{k_i}`
  the source obtains by comparing coefficients over `D(2)`, the degree-one reading
  `∇ m = ∑_i θ_i(m) d x_i`, and the `p`-adic convergence of the expansion in the form of the
  finiteness of `{K : θ_K(m) ∉ p M}`.

The four items of the tag are theorems about such an object, not fields of it:
`Crystalline.TaylorCrystal.isPAdicallyComplete`,
`Crystalline.FirstOrderComparison.completedConnection`,
`Crystalline.TaylorCrystal.isIntegrable` and
`Crystalline.TaylorCrystal.isTopologicallyQuasiNilpotent`.

The basis `b` of `Ω` on the differentials is a parameter and not a field, being data about
`(Ω, d x)` and the same for every object; see the module documentation for the generality that
costs. -/
public structure TaylorCrystal (A : Type uA) [CommRing A] (D : DividedPowerRing.{u})
    (g : A →+* D) (Omega : Type v) [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega]
    [IsCentralScalar D Omega] (d : DividedPowerDerivation A D g Omega) (p : ℕ) {ι : Type uI}
    (dx : ι → Omega) (b : Module.Basis ι D Omega) (hdx : ∀ i, dx i = b i) where
  /-- The underlying module `M`. -/
  carrier : Type uM
  /-- Its additive group structure. -/
  [addCommGroup : AddCommGroup carrier]
  /-- Its `D`-module structure. -/
  [module : Module D carrier]
  /-- The first-order comparison datum of the crystal, from which item (07JC) is proved. -/
  comparison : FirstOrderComparison A D g Omega d carrier
  /-- The levels `M_e = Γ(T_e, ℱ)` of the source's limit. -/
  levels : ℕ → Type uM
  /-- Their additive group structures. -/
  [levelAddCommGroup : ∀ n, AddCommGroup (levels n)]
  /-- Their `D`-module structures. -/
  [levelModule : ∀ n, Module D (levels n)]
  /-- The transition maps `M_{e+1} → M_e` of the tower. -/
  transition : ∀ n, levels (n + 1) →ₗ[D] levels n
  /-- The exponent shift `N` at which the levels are cut out. -/
  shift : ℕ
  /-- `p^{N+e}` annihilates the level `e`.  This is weaker than the source's
  `M_e = M_{e+1}/p^e M_{e+1}`, and is what the levels of [Stacks, Tag 07JN] satisfy. -/
  level_annihilate : ∀ n, DividedPowers.pAdicIdeal (A := (D : Type u)) p ^ (shift + n) •
    (⊤ : Submodule D (levels n)) = ⊥
  /-- The identification `M ≅ lim_e M_e` of the source's first paragraph. -/
  levelEquiv : carrier ≃ₗ[D] invLimit levels transition
  /-- The coordinate operators `θ_i` of the expansion over `D(1)`. -/
  theta : ι → (carrier → carrier)
  /-- The composite operators `θ_K` of that expansion. -/
  thetaPow : (ι →₀ ℕ) → (carrier → carrier)
  /-- `θ_K = ∏_i θ_i^{k_i}`, which the source gets by comparing coefficients over `D(2)`. -/
  isThetaMonomialFamily : IsThetaMonomialFamily carrier theta thetaPow
  /-- `∇ m = ∑_i θ_i(m) d x_i`, the degree-one part of the expansion. -/
  isCoordinateExpansion : IsCoordinateExpansion p D Omega dx
    (comparison.completedConnection p) theta
  /-- The `p`-adic convergence of the expansion over `D(1)`: for each `m` only finitely many
  multi-indices `K` have `θ_K(m) ∉ p M`. -/
  finite_thetaPow_notMem_pSmul : ∀ m : carrier,
    {K : ι →₀ ℕ | thetaPow K m ∉ pSmul p D carrier}.Finite

attribute [instance] TaylorCrystal.addCommGroup TaylorCrystal.module
  TaylorCrystal.levelAddCommGroup TaylorCrystal.levelModule

namespace TaylorCrystal

variable {A : Type uA} [CommRing A] {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type v}
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {p : ℕ} {ι : Type uI} {dx : ι → Omega}
  {b : Module.Basis ι D Omega} {hdx : ∀ i, dx i = b i}
  (P : TaylorCrystal.{u, v, uA, uI, uM} A D g Omega d p dx b hdx)

/-! ### Item (07JB) -/

/-- **Item (07JB) of [Stacks, Lemma 60.17.3, Tag 07JG]: `M` is a `p`-adically complete
`D`-module.**  The source's argument, with the one weakening recorded in
`StacksFrontier/AlgebraicGeometry/Crystalline/LevelLimitPAdicComplete.lean`: `M` is the limit of the
tower of levels, the level `e` is annihilated by `p^{N+e}`, and such a limit is `p`-adically
complete by `Crystalline.isPAdicallyComplete_invLimit_of_shift`, which is
[Stacks, Algebra Lemma 10.98.2, Tag 09B8] in the form of [Stacks, Tag 0G1Q] with the exponent
shifted.  Completeness then transports along the identification `M ≅ lim_e M_e`.

The relation `M_e = M_{e+1}/p^e M_{e+1}` the source cites the algebra lemma for is **not** used:
nothing is assumed of the transition maps, not even surjectivity. -/
public theorem isPAdicallyComplete : IsPAdicallyComplete p D P.carrier :=
  Stacks.Examples.isAdicComplete_of_linearEquiv P.levelEquiv
    (isPAdicallyComplete_invLimit_of_shift p (D : Type u) P.levels P.transition P.shift
      P.level_annihilate)

/-- **The Hausdorff half of item (07JB)**, which is what the proofs of items (07JD) and (07JE)
consume: a `p`-adically complete module has nothing in every `p^n M`. -/
public theorem isHausdorff :
    IsHausdorff (DividedPowers.pAdicIdeal (A := (D : Type u)) p) P.carrier := by
  have : IsAdicComplete (DividedPowers.pAdicIdeal (A := (D : Type u)) p) P.carrier :=
    P.isPAdicallyComplete
  infer_instance

/-! ### Items (07JD) and (07JE), and the non-vacuity of their statements -/

/-- **The non-vacuity clause of `Crystalline.Pair`**: the connection does have a family of
coordinate operators, namely the one carried.  Without it items (07JD) and (07JE), which quantify
over the coordinate expansions of `∇`, would be satisfied by a connection with none. -/
public theorem hasCoordinateOperators :
    ∃ theta : ι → (P.carrier → P.carrier),
      IsCoordinateExpansion p D Omega dx (P.comparison.completedConnection p) theta :=
  ⟨P.theta, P.isCoordinateExpansion⟩

/-- **Item (07JD) of [Stacks, Lemma 60.17.3, Tag 07JG]: the connection is integrable.**  The
carried operators commute by `Crystalline.IsThetaMonomialFamily.comm`, the source's
"`θ_i ∘ θ_j = θ_j ∘ θ_i` (this provides an alternative proof of the integrability of `∇`)"; and by
`Crystalline.eq_of_isCoordinateExpansion` — uniqueness of the coordinate operators, which the
basis of `Ω` and the Hausdorffness of item (07JB) supply — there is no other family to check.

`Crystalline.IsIntegrable` is the predicate unchanged, still quantified over every coordinate
expansion of `∇`. -/
public theorem isIntegrable :
    IsIntegrable p D Omega dx (P.comparison.completedConnection p) :=
  isIntegrable_of_isThetaMonomialFamily p (D : Type u) Omega P.carrier
    P.isThetaMonomialFamily P.isCoordinateExpansion b hdx P.isHausdorff

/-- **Item (07JE) of [Stacks, Lemma 60.17.3, Tag 07JG]: the connection is topologically
quasi-nilpotent.**  The pairs `(i, k)` with `k ≠ 0` inject into the multi-indices by
`K = k · e_i`, along which `θ_i^k = θ_{k · e_i}` by
`Crystalline.IsThetaMonomialFamily.single`, so the carried finiteness of
`{K : θ_K(m) ∉ p M}` — the `p`-adic convergence of the expansion over `D(1)` — bounds them; and
uniqueness of the coordinate operators again removes the quantifier. -/
public theorem isTopologicallyQuasiNilpotent :
    IsTopologicallyQuasiNilpotent p D Omega dx (P.comparison.completedConnection p) :=
  isTopologicallyQuasiNilpotent_of_isThetaMonomialFamily p (D : Type u) Omega P.carrier
    P.isThetaMonomialFamily P.isCoordinateExpansion b hdx P.isHausdorff
    P.finite_thetaPow_notMem_pSmul

/-! ### The object of `Crystalline.FirstOrderCrystal` it determines -/

/-- **The first-order crystal datum of a `Crystalline.TaylorCrystal`**: the same module and the
same comparison map, with the remaining four fields given by
`Crystalline.TaylorCrystal.isPAdicallyComplete`,
`Crystalline.TaylorCrystal.hasCoordinateOperators`, `Crystalline.TaylorCrystal.isIntegrable` and
`Crystalline.TaylorCrystal.isTopologicallyQuasiNilpotent`. -/
public def toFirstOrderCrystal :
    FirstOrderCrystal.{u, v, uA, uI, uM} A D g Omega d p dx where
  carrier := P.carrier
  comparison := P.comparison
  isPAdicallyComplete := P.isPAdicallyComplete
  hasCoordinateOperators := P.hasCoordinateOperators
  isIntegrable := P.isIntegrable
  isTopologicallyQuasiNilpotent := P.isTopologicallyQuasiNilpotent

/-- The module of `P.toFirstOrderCrystal` is the module of `P`. -/
@[simp] public theorem toFirstOrderCrystal_carrier :
    P.toFirstOrderCrystal.carrier = P.carrier := rfl

/-- The comparison map of `P.toFirstOrderCrystal` is the comparison map of `P`. -/
@[simp] public theorem toFirstOrderCrystal_comparison :
    P.toFirstOrderCrystal.comparison = P.comparison := rfl

end TaylorCrystal

/-! ### The category, and the functor of Tag 07JG -/

section Functor

variable (A : Type uA) [CommRing A] (D : DividedPowerRing.{u}) (g : A →+* D) (Omega : Type v)
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  (d : DividedPowerDerivation A D g Omega) (p : ℕ) {ι : Type uI} (dx : ι → Omega)
  (b : Module.Basis ι D Omega) (hdx : ∀ i, dx i = b i)

/-- A morphism of `Crystalline.TaylorCrystal` is a morphism of the first-order crystal data the
objects determine, that is a `D`-linear map compatible with the two comparison maps.  No condition
is imposed on the towers or on the coordinate operators: the latter are determined by the
connection anyway, by `Crystalline.eq_of_isCoordinateExpansion`. -/
public instance : Category (TaylorCrystal.{u, v, uA, uI, uM} A D g Omega d p dx b hdx) where
  Hom P Q := P.toFirstOrderCrystal ⟶ Q.toFirstOrderCrystal
  id P := CategoryStruct.id P.toFirstOrderCrystal
  comp f h := CategoryStruct.comp f h
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f h k := Category.assoc f h k

/-- **The forgetful functor to the first-order crystal data**, which forgets the tower of levels
and the composite coordinate operators and keeps the four items they prove.  It is the identity on
morphisms, the morphisms of the source being by definition those of the images. -/
public def forgetToFirstOrderCrystal :
    TaylorCrystal.{u, v, uA, uI, uM} A D g Omega d p dx b hdx ⥤
      FirstOrderCrystal.{u, v, uA, uI, uM} A D g Omega d p dx where
  obj P := P.toFirstOrderCrystal
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **Stacks Project, Lemma 60.17.3, Tag 07JG**, in the affine algebraic form of this file: the
functor out of `Crystalline.TaylorCrystal` to the pairs `(M, ∇)` satisfying items (07JB), (07JC),
(07JD) and (07JE), with all four items **proved** of the image pair.

**The source category is `Crystalline.TaylorCrystal` and not the crystals in quasi-coherent
`𝒪_{X/S}`-modules on `Cris(X/S)`.**  `Crystalline.TaylorCrystal` is the affine algebraic model
over `D` of the data a crystal supplies — the first-order comparison datum over the thickening of
[Stacks, Tag 07J2], the tower of levels realising `M = lim_e M_e`, and the composite coordinate
operators of the expansions over `D(1)` and `D(2)`.  The functor from the crystals themselves is
`Crystalline.GlobalCrystallineSituation.SmallSite.functor07JG` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalsQuasiCoherentToPairs.lean`, whose reduction
datum is the distance between the two; the last paragraph below says where that distance is
recorded.

* (07JB) is `Crystalline.TaylorCrystal.isPAdicallyComplete`, from the tower of levels.
* (07JC) is `Crystalline.FirstOrderComparison.completedConnection` together with
  `Crystalline.FirstOrderComparison.connection_leibniz`, from the comparison map.
* (07JD) is `Crystalline.TaylorCrystal.isIntegrable`.
* (07JE) is `Crystalline.TaylorCrystal.isTopologicallyQuasiNilpotent`.
* The non-vacuity clause `hasCoordinateOperators` of `Crystalline.Pair` is
  `Crystalline.TaylorCrystal.hasCoordinateOperators`.

The functor factors as `Crystalline.forgetToFirstOrderCrystal ⋙
Crystalline.firstOrderCrystalsToPairs`, so the connection of the image pair and the horizontality
of the image of a morphism are those of `Crystalline.firstOrderCrystalsToPairs` unchanged, and the
only difference is that its source does not carry the three items as fields.

What remains between this and the tag's own source — a crystal in quasi-coherent
`𝒪_{X/S}`-modules on `Cris(X/S)` — is listed in the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalsToPairs.lean`; the generality in the
coordinates, and the two inputs that are the source's `D(1)` and `D(2)` computations, are
discussed in the module documentation here. -/
public noncomputable def taylorCrystalsToPairs :
    TaylorCrystal.{u, v, uA, uI, uM} A D g Omega d p dx b hdx ⥤
      Pair.{u, v, uI, uM} p D Omega dx (derivationFun A D g Omega d) :=
  forgetToFirstOrderCrystal A D g Omega d p dx b hdx ⋙
    firstOrderCrystalsToPairs A D g Omega d p dx

/-- The functor is the forgetful functor followed by
`Crystalline.firstOrderCrystalsToPairs`, by definition. -/
public theorem taylorCrystalsToPairs_eq :
    taylorCrystalsToPairs A D g Omega d p dx b hdx =
      forgetToFirstOrderCrystal A D g Omega d p dx b hdx ⋙
        firstOrderCrystalsToPairs A D g Omega d p dx := rfl

/-- **Item (07JC) of the image pair**: its connection is the completed connection of the
comparison datum, whose Leibniz rule is
`Crystalline.FirstOrderComparison.connection_leibniz`. -/
@[simp] public theorem taylorCrystalsToPairs_obj_nabla
    (P : TaylorCrystal.{u, v, uA, uI, uM} A D g Omega d p dx b hdx) :
    ((taylorCrystalsToPairs A D g Omega d p dx b hdx).obj P).nabla =
      P.comparison.completedConnection p := rfl

/-- The image of a morphism is the same `D`-linear map. -/
@[simp] public theorem taylorCrystalsToPairs_map_toLinearMap
    {P Q : TaylorCrystal.{u, v, uA, uI, uM} A D g Omega d p dx b hdx} (f : P ⟶ Q) :
    ((taylorCrystalsToPairs A D g Omega d p dx b hdx).map f).toLinearMap = f.toLinearMap := rfl

end Functor

end Crystalline

end
