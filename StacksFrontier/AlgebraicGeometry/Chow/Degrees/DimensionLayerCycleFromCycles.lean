module

public import Mathlib.Logic.Equiv.Fin.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherenceClosure
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerCycleClass
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import StacksFrontier.CategoryTheory.Abelian.KZeroRealisation

/-!
# The map from cycles to the K-group of a dimension layer

Let `(S, δ)` be a base situation with a dimension function and let `X` be a scheme locally of
finite type over `S`. A `k`-cycle on `X` is a locally finite formal sum `∑ n_Z [Z]` of integral
closed subschemes of delta-dimension `k`. Splitting the coefficients into their positive and
negative parts and replacing each integral closed subscheme `Z` by the direct sum of `|n_Z|`
copies of the structure sheaf `𝒪_Z`, pushed forward to `X`, produces two coherent `𝒪_X`-modules
whose support has delta-dimension at most `k`, hence the element

`[⨁_{n_Z > 0} 𝒪_Z^{⊕n_Z}] - [⨁_{n_Z < 0} 𝒪_Z^{⊕-n_Z}]`

of the Grothendieck group of the dimension layer `Coh_{≤k}(X)/Coh_{≤k-1}(X)`. The assignment is
additive, so it is a homomorphism

`Z_k(X) ⟶ K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))`.

This is one of the two maps of Tag 02S9; the one in the opposite direction is
`Stacks.Chow.dimensionLayerCycleHom`.

The direct sums occurring here are infinite in general, and the content of the construction is
that they are nevertheless coherent modules of bounded support dimension. Coherence is local on
`X` by Stacks 01BY, and local finiteness of the family of closed subschemes makes the sum agree
with a finite sum on a neighbourhood of every point, where coherence is the closure of
coherent modules under finite direct sums. The support of a direct sum is contained in the union
of the supports, which bounds the delta-dimension by that of the individual summands.

## Main definitions

* `Stacks.Chow.integralComponentStructureSheaf` — the structure sheaf of the integral closed
  subscheme `closure {x}` with its reduced structure, pushed forward to `X`.
* `Stacks.Chow.cycleStructureSheaf` — the locally finite direct sum
  `⨁_x 𝒪_{closure {x}}^{⊕ n x}` attached to a function `n : X → ℕ`.
* `Stacks.Chow.DimensionCoefficients` — the functions `X → ℕ` with locally finite support, zero
  off the points of relative dimension `k`.
* `Stacks.Chow.cycleStructureSheafDimLE` and `Stacks.Chow.cycleStructureSheafClass` — that direct
  sum read as an object of `Coh_{≤k}(X)`, and its class in `K₀(Coh_{≤k}/Coh_{≤k-1})`.
* `Stacks.Chow.cyclePositivePart` and `Stacks.Chow.cycleNegativePart` — the positive and negative
  parts of the coefficient function of a `k`-cycle.
* `Stacks.Chow.cycleDimensionLayerHom` — the homomorphism
  `Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` of Tag 02S9.
* `Stacks.Chow.multiplicityCoefficients` — the multiplicity function `ξ ↦ m_{Z_ξ, F}` of a
  coherent module of support dimension at most `k`, as a nonnegative coefficient function.
* `Stacks.Chow.DimensionLayerIsStructureSheafSum` — the assertion that in the dimension layer
  every coherent module of support dimension at most `k` is the locally finite direct sum of the
  structure sheaves of the integral closed subschemes of its cycle, taken with multiplicity.
* `CategoryTheory.GrothendieckGroup.kZeroAddEquiv` — the comparison between the two presentations
  of the Grothendieck group of an abelian category used in this repository.

## Main results

* `Stacks.Chow.isCoherent_coproduct_of_locallyFinite` — a direct sum of coherent `𝒪_X`-modules
  whose supports form a locally finite family is coherent.
* `Stacks.Chow.isCoherent_cycleStructureSheaf` — in particular the locally finite direct sum of
  structure sheaves of integral closed subschemes is coherent.
* `Stacks.Chow.schemeDeltaDimension_reducedSupport_cycleStructureSheaf_le` — its support has
  delta-dimension at most `k` as soon as every point carrying a nonzero coefficient has relative
  dimension `k`.
* `Stacks.Chow.cycleStructureSheafClass_add` — the class of the direct sum attached to a sum of
  coefficient functions is the sum of the two classes.
* `Stacks.Chow.cycleDimensionLayerHom_apply` — the value of the homomorphism on a cycle
  `∑ n_Z[Z]` is `[⨁_{n_Z > 0} 𝒪_Z^{⊕n_Z}] - [⨁_{n_Z < 0} 𝒪_Z^{⊕-n_Z}]`.
* `Stacks.Chow.dimensionLayerCycle_cycleStructureSheafDimLE_apply` — the cycle of
  `⨁_x 𝒪_{closure {x}}^{⊕ n x}` has coefficient `n y` at every point `y`.
* `Stacks.Chow.dimensionLayerCycleHom_comp_cycleDimensionLayerHom` — **one of the two inverse
  identities of Tag 02S9**: the composite
  `Z_k(X) → K₀(Coh_{≤k}/Coh_{≤k-1}) → Z_k(X)` is the identity.
* `Stacks.Chow.injective_cycleDimensionLayerHom` and
  `Stacks.Chow.surjective_dimensionLayerCycleHom_of_cycleDimensionLayerHom` — the halves of the
  bijectivity of Tag 02S9 that follow. The surjectivity carries the name of the map it is proved
  through, because `Stacks.Chow.surjective_dimensionLayerCycleHom` is already the name of the
  same conclusion in
  `StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerClassOfCycle`, proved there through
  the rival construction of the map of Tag 02S9 and carrying a quasi-compactness hypothesis on
  `X` which the version here does not need.
* `Stacks.Chow.cycleDimensionLayerHom_dimensionLayerCycle_eq_cycleStructureSheafClass` — on the
  cycle of a coherent module the map `Z_k(X) → K₀(Coh_{≤k}/Coh_{≤k-1})` takes the value the class
  of the locally finite direct sum of the structure sheaves of the integral closed subschemes of
  that cycle, with no correction term.
* `Stacks.Chow.of_eq_of_lowerDimensionClass_kernel_cokernel` and
  `Stacks.Chow.dimensionLayerCycle_eq_of_lowerDimensionClass_kernel_cokernel` — a morphism of
  `Coh_{≤k}(X)` whose kernel and cokernel have support of delta-dimension at most `k - 1` leaves
  the class in `K₀(Coh_{≤k}/Coh_{≤k-1})` and the cycle unchanged.

## Implementation notes

The direct sum attached to `n : X → ℕ` is the categorical coproduct over the index type
`Σ x : X, Fin (n x)`, which repeats the structure sheaf of `closure {x}` exactly `n x` times.
Local finiteness of that family of supports is local finiteness of the support of `n` together
with the finiteness of each `Fin (n x)`: an open set meets `closure {x}` precisely when it
contains `x`, since opens are stable under generalization.

Additivity in the coefficient function is the decomposition of the index type along
`Fin (a x + b x) ≃ Fin (a x) ⊕ Fin (b x)`, which turns the coproduct into a binary coproduct of
the two summand coproducts, hence into a biproduct of the two classes in the Grothendieck group.
That identity is pulled back from the ambient category of all `𝒪_X`-modules to `Coh_{≤k}(X)`
along the two inclusions, which are fully faithful and preserve finite colimits. Additivity in
the *cycle* follows because the positive and negative parts of integers satisfy
`(u + v)⁺ + u⁻ + v⁻ = u⁺ + v⁺ + (u + v)⁻` in `ℕ`.

This repository carries two constructions of the Grothendieck group of an abelian category, both
realizing Stacks 02MU: `KZero`, on which `Stacks.Chow.coherentDimensionKZero` and
`Stacks.Chow.coherentDimensionLayerHom` are built, and
`CategoryTheory.GrothendieckGroup`, on which `Stacks.Chow.dimensionLayerCycleHom` and
`Stacks.Chow.dimensionLayerFinitePushforwardHom` are built. The homomorphism constructed here
lands in the latter, so that it composes with the cycle class homomorphism of Tag 02S9 and with
the direct image homomorphism of Tag 0FDR. `CategoryTheory.GrothendieckGroup.kZeroAddEquiv`
identifies the two, both being the free abelian group on the objects modulo the relations of the
short exact sequences; composing with it makes the homomorphism below usable against
`Stacks.Chow.coherentDimensionLayerHom`, whose target is the subgroup `Bₖ(X)` of Tag 02SC.

The inverse identity on `Z_k(X)` is reduced to the computation of the coefficient of the cycle of
`⨁_x 𝒪_{closure {x}}^{⊕ n x}` at a single point `y`, which needs no length computation for an
infinite direct sum: the coefficient function is split as `n = n' + N[y]` with `n' y = 0`, the
cycle class is additive along that splitting, the cycle of the direct sum attached to `n'`
vanishes at `y` because the closure of a point of relative dimension `k` other than `y` cannot
contain `y`, and the cycle of the direct sum attached to `N[y]` is computed by induction on `N`
from the case `N = 1`, where the direct sum is indexed by a one-element type and the coefficient
is the multiplicity one of Stacks 02QY.

## What is not proved

The other inverse identity of Tag 02S9 — that the composite
`K₀(Coh_{≤k}/Coh_{≤k-1}) → Z_k(X) → K₀(Coh_{≤k}/Coh_{≤k-1})` is the identity, equivalently that
`Stacks.Chow.cycleDimensionLayerHom` is surjective — is proved for a **Noetherian** `X` in
`StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass`, as
`Stacks.Chow.cycleDimensionLayerHom_comp_dimensionLayerCycleHom`, and with it the bijectivity of
the two maps, `Stacks.Chow.cycleDimensionLayerEquiv`. Over a scheme that is merely locally of
finite type over the base it is not formalized: the proof there runs the dévissage filtration of
Stacks 01YF, which needs `X` Noetherian, and the source's argument in general goes instead
through the locally finite direct sum `⨁_{p ≥ 0} F^p` of the terms of a filtration spread out
from the stalks at the generic points of the support.

The assertion `Stacks.Chow.DimensionLayerIsStructureSheafSum` to which the identity is reduced
below — that in the dimension layer a coherent module `F` of support dimension at most `k` is
*isomorphic* to the locally finite direct sum `⨁_ξ 𝒪_{Z_ξ}^{⊕ m_ξ}` of the structure sheaves of
the integral closed subschemes of `[F]_k = ∑ m_ξ [Z_ξ]` — is **false**, so it cannot be proved.
On `X = Spec k[t]` over `S = Spec k` with `δ = dim` and `k = 0` every nonzero coherent module has
support of delta-dimension `0`, so `Coh_{≤-1}(X) = 0` and the localization functor onto the layer
is an equivalence; for `F = 𝒪_X/(t²)` the cycle is `2[(t)]` and the direct sum is
`(𝒪_X/(t))^{⊕2}`, and a module of length two over a discrete valuation ring is not the square of
its residue field. The obstruction is general: at the generic point `ξ` of a component of
`Supp F` the stalk of the direct sum is a `κ(ξ)`-vector space of dimension `m_ξ` while `F_ξ`
merely has length `m_ξ`, so the two stalks agree exactly when `F_ξ` is semisimple.

What the two homomorphisms of Tag 02S9 need is the equality of the two *classes* in
`K₀(Coh_{≤k}/Coh_{≤k-1})`, which is `Stacks.Chow.DimensionLayerClassIsStructureSheafSum`. The
three theorems below that take `Stacks.Chow.DimensionLayerIsStructureSheafSum` as a hypothesis use
it only through `CategoryTheory.GrothendieckGroup.of_eq_of_iso`, hence follow from that weaker
assertion as well, as
`Stacks.Chow.cycleDimensionLayerHom_dimensionLayerCycle_of_classIsStructureSheafSum`,
`Stacks.Chow.cycleDimensionLayerHom_comp_dimensionLayerCycleHom_of_classIsStructureSheafSum` and
`Stacks.Chow.surjective_cycleDimensionLayerHom_of_classIsStructureSheafSum`; and
`Stacks.Chow.classIsStructureSheafSum_of_isStructureSheafSum` is the implication between the two
assertions. Everything else that the identity needs is unconditional: the negative part of
`[F]_k` vanishes and its positive part is the multiplicity function, so the value of the map from
cycles on `[F]_k` is a single class and not a difference.

## References

* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
* [Stacks Project, Tag 02MU](https://stacks.math.columbia.edu/tag/02MU)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
* [Stacks Project, Tag 02QR](https://stacks.math.columbia.edu/tag/02QR)
* [Stacks Project, Tag 02S8](https://stacks.math.columbia.edu/tag/02S8)
* [Stacks Project, Tag 02SC](https://stacks.math.columbia.edu/tag/02SC)
* [Stacks Project, Tag 0FDR](https://stacks.math.columbia.edu/tag/0FDR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace CategoryTheory.GrothendieckGroup

variable (𝒜 : Type*) [Category 𝒜] [Abelian 𝒜]

/-! ### The two presentations of the Grothendieck group -/

/-- The two presentations of the Grothendieck group of an abelian category are canonically
isomorphic: both are the free abelian group on the objects modulo the relation
`[X₂] = [X₁] + [X₃]` of a short exact sequence, and the isomorphism matches the class of an
object with the class of that object. -/
def kZeroAddEquiv : KZero 𝒜 ≃+ GrothendieckGroup 𝒜 where
  toFun := KZero.toGrothendieckGroup
  invFun := KZero.ofGrothendieckGroup
  map_add' := map_add _
  left_inv x := KZero.ofGrothendieckGroup_toGrothendieckGroup x
  right_inv x := by
    have h : (KZero.toGrothendieckGroup (𝒜 := 𝒜)).comp KZero.ofGrothendieckGroup =
        AddMonoidHom.id _ :=
      hom_ext fun A ↦ by
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, KZero.ofGrothendieckGroup_of,
          KZero.toGrothendieckGroup_mk, AddMonoidHom.id_apply]
    exact congrArg (fun φ : GrothendieckGroup 𝒜 →+ GrothendieckGroup 𝒜 ↦ φ x) h

end CategoryTheory.GrothendieckGroup

namespace Stacks.Chow

/-! ### Coproducts along a decomposition of the index type -/

/-- A coproduct is unchanged by reindexing along an equivalence of index types which matches the
two families up to isomorphism. -/
private def coproductReindexIso {D : Type*} [Category D] {J K : Type*}
    (F : J → D) (G : K → D) (e : J ≃ K) (φ : ∀ j, F j ≅ G (e j))
    [HasCoproduct F] [HasCoproduct G] : ∐ F ≅ ∐ G :=
  HasColimit.isoOfEquivalence (Discrete.equivalence e)
    (Discrete.natIso fun j ↦ (φ j.as).symm)

/-- A coproduct over a disjoint union of two index types is the binary coproduct of the
coproducts over the two summands. -/
private def coproductSumIso {D : Type*} [Category D] {J K : Type*} (F : J ⊕ K → D)
    [HasCoproduct F] [HasCoproduct fun j ↦ F (Sum.inl j)]
    [HasCoproduct fun k ↦ F (Sum.inr k)]
    [HasBinaryCoproduct (∐ fun j ↦ F (Sum.inl j)) (∐ fun k ↦ F (Sum.inr k))] :
    ∐ F ≅ (∐ fun j ↦ F (Sum.inl j)) ⨿ (∐ fun k ↦ F (Sum.inr k)) where
  hom := Sigma.desc fun s ↦ match s with
    | .inl j => Sigma.ι (fun j ↦ F (Sum.inl j)) j ≫ coprod.inl
    | .inr k => Sigma.ι (fun k ↦ F (Sum.inr k)) k ≫ coprod.inr
  inv := coprod.desc (Sigma.desc fun j ↦ Sigma.ι F (Sum.inl j))
    (Sigma.desc fun k ↦ Sigma.ι F (Sum.inr k))
  hom_inv_id := by
    refine Sigma.hom_ext _ _ fun s ↦ ?_
    rcases s with j | k
    · simp only [Sigma.ι_comp_desc_assoc, Category.assoc, Category.comp_id, coprod.inl_desc,
        Sigma.ι_comp_desc]
    · simp only [Sigma.ι_comp_desc_assoc, Category.assoc, Category.comp_id, coprod.inr_desc,
        Sigma.ι_comp_desc]
  inv_hom_id := by
    refine coprod.hom_ext ?_ ?_
    · rw [← Category.assoc, coprod.inl_desc]
      refine Sigma.hom_ext _ _ fun j ↦ ?_
      simp
    · rw [← Category.assoc, coprod.inr_desc]
      refine Sigma.hom_ext _ _ fun k ↦ ?_
      simp

/-- The coproduct over a subset of the index type on which a family is concentrated — all
members outside the subset being zero objects — is the whole coproduct. -/
private def coproductSubtypeIso {D : Type*} [Category D] [HasZeroMorphisms D]
    {J : Type*} (F : J → D) (T : Set J) [HasCoproduct F]
    [HasCoproduct fun j : T ↦ F j] (h : ∀ j, j ∉ T → IsZero (F j)) :
    (∐ fun j : T ↦ F j) ≅ ∐ F := by
  classical
  refine ⟨Sigma.desc fun j ↦ Sigma.ι F j,
    Sigma.desc fun j ↦ if hj : j ∈ T then Sigma.ι (fun j : T ↦ F j) ⟨j, hj⟩ else 0, ?_, ?_⟩
  · refine Sigma.hom_ext _ _ fun j ↦ ?_
    simp
  · refine Sigma.hom_ext _ _ fun j ↦ ?_
    by_cases hj : j ∈ T
    · simp [hj]
    · simp only [Sigma.ι_comp_desc_assoc, hj, ↓reduceDIte, zero_comp, Category.comp_id]
      exact (h j hj).eq_of_src _ _

/-! ### Coherence of a locally finite direct sum -/

/-- Coherence of a sheaf of modules is invariant under isomorphism: coherent modules form a weak
Serre subcategory, which is closed under isomorphisms. -/
private theorem isCoherent_of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (h : M.IsCoherent) : N.IsCoherent :=
  AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent
    ((Stacks.SheafOfModules.coherentModules X.ringCatSheaf).prop_of_iso e
      (AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent h))

/-- The restriction of an `𝒪_X`-module to an open subscheme disjoint from its support is a zero
object: every section over an open of that subscheme has vanishing germ at each of its points,
hence is zero. -/
private theorem isZero_restrict_of_disjoint_supp {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (h : Disjoint (U : Set X) (SheafOfModules.supp M)) :
    IsZero ((Scheme.Modules.restrictFunctor U.ι).obj M) := by
  refine (IsZero.iff_id_eq_zero _).2 ?_
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V ↦ ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
  change s = 0
  refine TopCat.Presheaf.section_ext ⟨M.presheaf, M.isSheaf⟩ (U.ι ''ᵁ V.unop) s 0 fun x hx ↦ ?_
  have hxU : (x : X) ∈ (U : Set X) := by
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have hn : (x : X) ∉ SheafOfModules.supp M := Set.disjoint_left.mp h hxU
  have hz : ∀ a : M.presheaf.stalk x, a = 0 := fun a ↦ by
    by_contra ha
    exact hn ⟨a, ha⟩
  exact (hz _).trans (hz _).symm

/-- The restriction of an `𝒪_X`-module to an open subscheme disjoint from its support is a zero
object. -/
alias isZero_restrictFunctor_obj_of_disjoint_supp := isZero_restrict_of_disjoint_supp

/-- **Stacks 01BY for an infinite direct sum.** A direct sum of coherent `𝒪_X`-modules whose
supports form a locally finite family of subsets of `X` is coherent.

Coherence is local on `X`, and every point has a neighbourhood meeting only finitely many of the
supports; over such a neighbourhood the direct sum agrees with the direct sum of that finite
subfamily, which is coherent. -/
theorem isCoherent_coproduct_of_locallyFinite {X : Scheme.{u}} {J : Type u}
    (F : J → X.Modules) (hF : ∀ j, (F j).IsCoherent)
    (hLF : LocallyFinite fun j ↦ SheafOfModules.supp (F j)) :
    (∐ F).IsCoherent := by
  classical
  have hloc : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ T : Finset J,
      ∀ j, j ∉ T → Disjoint (U : Set X) (SheafOfModules.supp (F j)) := by
    intro x
    obtain ⟨V, hV, hfin⟩ := hLF x
    obtain ⟨W, hWV, hW, hxW⟩ := mem_nhds_iff.mp hV
    exact ⟨⟨W, hW⟩, hxW, hfin.toFinset, fun j hj ↦ Set.disjoint_left.mpr fun y hyW hyF ↦
      hj (hfin.mem_toFinset.mpr ⟨y, hyF, hWV hyW⟩)⟩
  choose U hU T hT using hloc
  refine AlgebraicGeometry.Modules.isCoherent_of_restrict (∐ F) U ?_ fun x ↦ ?_
  · exact eq_top_iff.2 fun y _ ↦ Opens.mem_iSup.2 ⟨y, hU y⟩
  · have := fun j ↦ hF j
    have hcoh : (((Scheme.Modules.restrictFunctor (U x).ι).obj
        (∐ fun j : (T x : Set J) ↦ F j))).IsCoherent := by
      have : (∐ fun j : (T x : Set J) ↦ F j).IsCoherent :=
        AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent
          (Stacks.SheafOfModules.isCoherent_sigma (R := X.ringCatSheaf)
            (fun j : (T x : Set J) ↦ F j) fun j ↦
              AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent (hF j))
      exact AlgebraicGeometry.Modules.isCoherent_restrict _ (U x)
    refine isCoherent_of_iso ?_ hcoh
    refine (PreservesCoproduct.iso (Scheme.Modules.restrictFunctor (U x).ι)
      (fun j : (T x : Set J) ↦ F j)).trans ?_
    refine (coproductSubtypeIso
      (fun j ↦ (Scheme.Modules.restrictFunctor (U x).ι).obj (F j)) (T x : Set J) ?_).trans
      (PreservesCoproduct.iso (Scheme.Modules.restrictFunctor (U x).ι) F).symm
    intro j hj
    exact isZero_restrict_of_disjoint_supp (F j) (U x) (hT x j (by simpa using hj))

/-! ### The structure sheaf of an integral closed subscheme -/

/-- The structure sheaf of the integral closed subscheme `closure {x}` of `X`, carrying its
reduced induced structure, pushed forward to an `𝒪_X`-module. -/
def integralComponentStructureSheaf {X : Scheme.{u}} (x : X) : X.Modules :=
  (Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
    (Stacks.Ample.unitModule (integralComponentAt x).subscheme)

/-- The support of the structure sheaf of the integral closed subscheme attached to `x` is the
closure of `x`. -/
@[simp]
theorem supp_integralComponentStructureSheaf {X : Scheme.{u}} (x : X) :
    SheafOfModules.supp (integralComponentStructureSheaf x) = closure {x} := by
  rw [integralComponentStructureSheaf, supp_pushforwardStructureSheaf,
    Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]

/-- **Stacks 01Y6** for a closed immersion. The structure sheaf of the integral closed subscheme
attached to a point of a locally Noetherian scheme is coherent on the ambient scheme. -/
instance isCoherent_integralComponentStructureSheaf {X : Scheme.{u}} [IsLocallyNoetherian X]
    (x : X) : (integralComponentStructureSheaf x).IsCoherent :=
  isCoherent_pushforwardStructureSheaf _

/-! ### The locally finite direct sum attached to a coefficient function -/

/-- The direct sum `⨁_x 𝒪_{closure {x}}^{⊕ n x}` of `n x` copies of the structure sheaf of the
integral closed subscheme attached to `x`, over all points `x` of `X`. -/
def cycleStructureSheaf {X : Scheme.{u}} (n : X → ℕ) : X.Modules :=
  ∐ fun i : Σ x : X, Fin (n x) ↦ integralComponentStructureSheaf i.1

/-- For a function with locally finite support the family of supports of the summands of
`Stacks.Chow.cycleStructureSheaf` is locally finite: an open set meets `closure {x}` exactly when
it contains `x`, and only finitely many points of any neighbourhood carry a nonzero value. -/
private theorem locallyFinite_supp_cycleStructureSheaf {X : Scheme.{u}} (n : X → ℕ)
    (hn : LocallyFiniteSupport n) :
    LocallyFinite fun i : Σ x : X, Fin (n x) ↦
      SheafOfModules.supp (integralComponentStructureSheaf i.1) := by
  simp only [supp_integralComponentStructureSheaf]
  refine (locallyFinite_closure_singleton_iff (fun i : Σ x : X, Fin (n x) ↦ i.1)).2 fun x ↦ ?_
  obtain ⟨t, ht, hfin⟩ := hn x
  refine ⟨t, ht, ?_⟩
  have heq : {i : Σ x : X, Fin (n x) | i.1 ∈ t} = Sigma.fst ⁻¹' (t ∩ Function.support n) :=
    Set.ext fun i ↦ ⟨fun hi ↦ ⟨hi, i.2.pos.ne'⟩, fun hi ↦ hi.1⟩
  rw [heq]
  refine hfin.preimage' fun y _ ↦ ?_
  refine (Set.finite_range fun a : Fin (n y) ↦ (⟨y, a⟩ : Σ x : X, Fin (n x))).subset ?_
  rintro ⟨i₁, i₂⟩ hi
  have hiy : i₁ = y := hi
  subst hiy
  exact ⟨i₂, rfl⟩

/-- **The locally finite direct sum of structure sheaves of integral closed subschemes is a
coherent module.** For a function `n : X → ℕ` with locally finite support on a locally Noetherian
scheme the direct sum `⨁_x 𝒪_{closure {x}}^{⊕ n x}` is a coherent `𝒪_X`-module. -/
theorem isCoherent_cycleStructureSheaf {X : Scheme.{u}} [IsLocallyNoetherian X] (n : X → ℕ)
    (hn : LocallyFiniteSupport n) : (cycleStructureSheaf n).IsCoherent :=
  isCoherent_coproduct_of_locallyFinite _ (fun _ ↦ inferInstance)
    (locallyFinite_supp_cycleStructureSheaf n hn)

/-- **Stacks 01AT and 01AH.** The support of a direct sum of sheaves of modules is contained in
the union of the supports of the summands: the stalk functor preserves colimits, so a stalk of
the direct sum is the direct sum of the stalks. -/
private theorem supp_coproduct_subset {X : Scheme.{u}} {J : Type u} (F : J → X.Modules) :
    SheafOfModules.supp (∐ F) ⊆ ⋃ j, SheafOfModules.supp (F j) := by
  intro x hx
  by_contra hn
  have hz : ∀ j, IsZero ((SheafOfModules.stalkFunctor X.ringCatSheaf x).obj (F j)) := by
    intro j
    refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b ↦ ?_⟩
    have hj : x ∉ SheafOfModules.supp (F j) := fun h ↦ hn (Set.mem_iUnion.2 ⟨j, h⟩)
    have h0 : ∀ a : (SheafOfModules.stalkFunctor X.ringCatSheaf x).obj (F j), a = 0 := fun a ↦ by
      by_contra ha
      exact hj ⟨a, ha⟩
    exact (h0 a).trans (h0 b).symm
  have hzero : IsZero (∐ fun j ↦ (SheafOfModules.stalkFunctor X.ringCatSheaf x).obj (F j)) :=
    (IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ fun j ↦ (hz j).eq_of_src _ _)
  have hs := (PreservesCoproduct.iso (SheafOfModules.stalkFunctor X.ringCatSheaf x) F).isZero_iff
  obtain ⟨a, ha⟩ := hx
  exact ha ((ModuleCat.isZero_iff_subsingleton.mp (hs.mpr hzero)).elim _ _)

/-- **Stacks 01AT and 01AH.** The support of a direct sum of sheaves of modules is contained in
the union of the supports of the summands. -/
alias supp_sigma_subset_iUnion_supp := supp_coproduct_subset

/-- A point of the support of `Stacks.Chow.cycleStructureSheaf n` lies in the closure of a point
carrying a nonzero value of `n`. -/
private theorem exists_mem_closure_of_mem_supp_cycleStructureSheaf {X : Scheme.{u}} (n : X → ℕ)
    {y : X} (hy : y ∈ SheafOfModules.supp (cycleStructureSheaf n)) :
    ∃ x : X, n x ≠ 0 ∧ y ∈ closure {x} := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (supp_coproduct_subset _ hy)
  exact ⟨i.1, i.2.pos.ne', by rwa [supp_integralComponentStructureSheaf] at hi⟩

/-- **Stacks 02QP for the locally finite direct sum.** If every point carrying a nonzero value of
`n` has relative dimension `k`, the support of `⨁_x 𝒪_{closure {x}}^{⊕ n x}` has delta-dimension
at most `k`: it is contained in the union of the closures of those points, and each such closure
is an integral closed subscheme of delta-dimension `k`. -/
theorem schemeDeltaDimension_reducedSupport_cycleStructureSheaf_le (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) (n : X → ℕ)
    (hn : LocallyFiniteSupport n)
    (hk : ∀ x : X, n x ≠ 0 → relativeDimension C.dimensionFunction f x = k) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : (cycleStructureSheaf n).IsCoherent := isCoherent_cycleStructureSheaf n hn
    schemeDeltaDimension C ((reducedSupport (cycleStructureSheaf n)).subschemeι ≫ f) ≤
      (k : EInt) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : (cycleStructureSheaf n).IsCoherent := isCoherent_cycleStructureSheaf n hn
  refine schemeDeltaDimension_reducedSupport_le C f _ fun y hy ↦ ?_
  obtain ⟨x, hx, hyx⟩ := exists_mem_closure_of_mem_supp_cycleStructureSheaf n hy
  have hrange : y ∈ Set.range (integralComponentAt x).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]
    exact hyx
  obtain ⟨z, rfl⟩ := hrange
  exact relativeDimension_le_of_schemeDeltaDimension_le C f _
    (le_of_eq (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C f x (hk x hx))) z

/-! ### The index decomposition behind additivity -/

/-- The index type of the direct sum attached to a sum of two coefficient functions is the
disjoint union of the two index types, by `Fin (a + b) ≃ Fin a ⊕ Fin b` in each fibre. -/
private def sigmaFinAddEquiv {X : Type*} (a b : X → ℕ) :
    (Σ x : X, Fin (a x + b x)) ≃ (Σ x : X, Fin (a x)) ⊕ (Σ x : X, Fin (b x)) :=
  (Equiv.sigmaCongrRight fun x ↦ (finSumFinEquiv (m := a x) (n := b x)).symm).trans
    (Equiv.sigmaSumDistrib _ _)

/-- The decomposition of the index type preserves the point of `X` an index lies over. -/
private theorem sigmaFinAddEquiv_fst {X : Type*} (a b : X → ℕ)
    (i : Σ x : X, Fin (a x + b x)) :
    Sum.elim Sigma.fst Sigma.fst (sigmaFinAddEquiv a b i) = i.1 := by
  obtain ⟨x, k⟩ := i
  obtain ⟨s, rfl⟩ : ∃ s : Fin (a x) ⊕ Fin (b x), k = finSumFinEquiv s :=
    ⟨finSumFinEquiv.symm k, (finSumFinEquiv.apply_symm_apply k).symm⟩
  simp only [sigmaFinAddEquiv, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
    Equiv.symm_apply_apply]
  cases s <;> rfl

/-- The direct sum attached to a sum of two coefficient functions is the direct sum of the two
direct sums. -/
private def cycleStructureSheafAddIso {X : Scheme.{u}} (a b : X → ℕ) :
    cycleStructureSheaf (a + b) ≅ cycleStructureSheaf a ⨿ cycleStructureSheaf b :=
  coproductReindexIso (fun i : Σ x : X, Fin (a x + b x) ↦ integralComponentStructureSheaf i.1)
      (fun s : (Σ x : X, Fin (a x)) ⊕ (Σ x : X, Fin (b x)) ↦
        integralComponentStructureSheaf (Sum.elim Sigma.fst Sigma.fst s))
      (sigmaFinAddEquiv a b)
      (fun i ↦ eqToIso (congrArg integralComponentStructureSheaf
        (sigmaFinAddEquiv_fst a b i).symm)) ≪≫
    coproductSumIso fun s : (Σ x : X, Fin (a x)) ⊕ (Σ x : X, Fin (b x)) ↦
      integralComponentStructureSheaf (Sum.elim Sigma.fst Sigma.fst s)

/-! ### The dimension layer object and its class -/

/-- The nonnegative coefficient functions that can occur in a `k`-cycle: the functions
`X → ℕ` with locally finite support which vanish at every point whose relative dimension is not
`k`. -/
def DimensionCoefficients (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) : Type u :=
  {n : X → ℕ // LocallyFiniteSupport n ∧
    ∀ x : X, n x ≠ 0 → relativeDimension C.dimensionFunction f x = k}

namespace DimensionCoefficients

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)

/-- Two such coefficient functions are equal as soon as the underlying functions are. -/
theorem ext {p q : DimensionCoefficients C f k} (h : p.1 = q.1) : p = q :=
  Subtype.ext h

/-- Pointwise addition of coefficient functions: the sum again has locally finite support and
again vanishes off the points of relative dimension `k`. -/
instance : Add (DimensionCoefficients C f k) where
  add p q :=
    ⟨p.1 + q.1, fun x ↦ by
        obtain ⟨t, ht, hft⟩ := p.2.1 x
        obtain ⟨s, hs, hfs⟩ := q.2.1 x
        refine ⟨t ∩ s, Filter.inter_mem ht hs, (hft.union hfs).subset fun y hy ↦ ?_⟩
        have hy2 : p.1 y + q.1 y ≠ 0 := hy.2
        rcases Nat.eq_zero_or_pos (p.1 y) with h | h
        · exact Or.inr ⟨hy.1.2, by simp only [Function.mem_support]; omega⟩
        · exact Or.inl ⟨hy.1.1, h.ne'⟩,
      fun x hx ↦ by
        have hx2 : p.1 x + q.1 x ≠ 0 := hx
        rcases Nat.eq_zero_or_pos (p.1 x) with h | h
        · exact q.2.2 x (by omega)
        · exact p.2.2 x h.ne'⟩

/-- The underlying function of a sum of coefficient functions is the pointwise sum. -/
@[simp]
theorem coe_add (p q : DimensionCoefficients C f k) : (p + q).1 = p.1 + q.1 :=
  rfl

end DimensionCoefficients

/-- The locally finite direct sum `⨁_x 𝒪_{closure {x}}^{⊕ n x}` read as an object of
`Coh_{≤k}(X)`: it is coherent, and its support has delta-dimension at most `k`. -/
def cycleStructureSheafDimLE (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (p : DimensionCoefficients C f k) :
    CoherentModulesDimLE C f k :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : (cycleStructureSheaf p.1).IsCoherent := isCoherent_cycleStructureSheaf p.1 p.2.1
  ⟨⟨cycleStructureSheaf p.1,
      AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent inferInstance⟩,
    schemeDeltaDimension_reducedSupport_cycleStructureSheaf_le C f k p.1 p.2.1 p.2.2⟩

/-- The underlying `𝒪_X`-module of the object of `Coh_{≤k}(X)` attached to a coefficient function
is the locally finite direct sum. -/
@[simp]
theorem cycleStructureSheafDimLE_obj_obj (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (p : DimensionCoefficients C f k) :
    (cycleStructureSheafDimLE C f k p).obj.obj = cycleStructureSheaf p.1 :=
  rfl

/-- An isomorphism exhibiting a coherent `𝒪_X`-module as the direct sum of two coherent modules
is such an isomorphism in the category of coherent modules: the inclusion of coherent modules is
fully faithful and preserves finite colimits. -/
private def coherentCoprodIso {X : Scheme.{u}}
    (A B M : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)
    (e : (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι.obj M ≅
      ((Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι.obj A ⨿
        (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι.obj B)) : M ≅ A ⨿ B :=
  have : PreservesFiniteColimits (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι :=
    ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _
  (ObjectProperty.fullyFaithfulι _).preimageIso
    (e ≪≫ PreservesColimitPair.iso (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι A B)

/-- An isomorphism exhibiting an object of `Coh_{≤k}(X)` as the direct sum of two objects of
`Coh_{≤k}(X)` in the category of coherent modules is such an isomorphism in `Coh_{≤k}(X)`: the
inclusion is fully faithful and preserves finite colimits. -/
private def dimLECoprodIso (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (A B M : CoherentModulesDimLE C f k)
    (e : (coherentModulesDimLE C f k).ι.obj M ≅
      ((coherentModulesDimLE C f k).ι.obj A ⨿ (coherentModulesDimLE C f k).ι.obj B)) :
    M ≅ A ⨿ B :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    (e ≪≫ PreservesColimitPair.iso (coherentModulesDimLE C f k).ι A B)

/-- If the underlying `𝒪_X`-module of an object of `Coh_{≤k}(X)` is the direct sum of the
underlying modules of two others, its class in the Grothendieck group of the dimension layer is
the sum of their classes: a binary coproduct in an abelian category is a biproduct, hence an
extension of one summand by the other. -/
private theorem of_eq_add_of_coprodIso (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (A B M : CoherentModulesDimLE C f k)
    (e : M.obj.obj ≅ (A.obj.obj ⨿ B.obj.obj)) :
    GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj M) =
      GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj A) +
        GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj B) := by
  have e₂ := dimLECoprodIso C f k A B M (coherentCoprodIso A.obj B.obj M.obj e)
  rw [GrothendieckGroup.of_eq_of_iso
    (((lowerDimensionClass C f (k - 1) k).isoModSerre.Q).mapIso e₂),
    ← GrothendieckGroup.of_eq_of_iso
      (PreservesColimitPair.iso ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q) A B),
    ← GrothendieckGroup.of_eq_of_iso
      (biprod.isoCoprod
        (((lowerDimensionClass C f (k - 1) k).isoModSerre.Q).obj A)
        (((lowerDimensionClass C f (k - 1) k).isoModSerre.Q).obj B)),
    GrothendieckGroup.of_biprod]

/-- The class in `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` of the locally finite direct sum
`⨁_x 𝒪_{closure {x}}^{⊕ n x}` attached to a nonnegative coefficient function. -/
def cycleStructureSheafClass (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (p : DimensionCoefficients C f k) :
    GrothendieckGroup (coherentDimensionQuotient C f (k - 1) k) :=
  GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj
    (cycleStructureSheafDimLE C f k p))

/-- The class of the direct sum attached to a sum of two coefficient functions is the sum of the
two classes. -/
theorem cycleStructureSheafClass_add (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (p q : DimensionCoefficients C f k) :
    cycleStructureSheafClass C f k (p + q) =
      cycleStructureSheafClass C f k p + cycleStructureSheafClass C f k q :=
  of_eq_add_of_coprodIso C f k (cycleStructureSheafDimLE C f k p)
    (cycleStructureSheafDimLE C f k q) (cycleStructureSheafDimLE C f k (p + q))
    (cycleStructureSheafAddIso p.1 q.1)

/-! ### The homomorphism from the group of cycles -/

/-- A nonnegative function vanishing wherever the coefficient function of a `k`-cycle vanishes
has locally finite support and vanishes off the points of relative dimension `k`. -/
theorem dimensionCoefficients_of_cycle (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) (c : CycleGroup C f k) (n : X → ℕ)
    (hn : ∀ x : X, n x ≠ 0 → c.1 x ≠ 0) :
    LocallyFiniteSupport n ∧
      ∀ x : X, n x ≠ 0 → relativeDimension C.dimensionFunction f x = k := by
  refine ⟨fun x ↦ ?_, fun x hx ↦
    (mem_cyclesOfDimension_iff_forall_point C f k c.1).1 c.2 x (hn x hx)⟩
  obtain ⟨t, ht, hfin⟩ := c.1.locallyFiniteSupport x
  exact ⟨t, ht, hfin.subset fun y hy ↦ ⟨hy.1, hn y hy.2⟩⟩

/-- The positive part of the coefficient function of a `k`-cycle. -/
def cyclePositivePart (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (c : CycleGroup C f k) : DimensionCoefficients C f k :=
  ⟨fun x ↦ (c.1 x).toNat, dimensionCoefficients_of_cycle C f k c _ fun x hx ↦ by
    simp only [ne_eq, Int.toNat_eq_zero, not_le] at hx
    omega⟩

/-- The negative part of the coefficient function of a `k`-cycle. -/
def cycleNegativePart (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (c : CycleGroup C f k) : DimensionCoefficients C f k :=
  ⟨fun x ↦ (-(c.1 x)).toNat, dimensionCoefficients_of_cycle C f k c _ fun x hx ↦ by
    simp only [ne_eq, Int.toNat_eq_zero, not_le] at hx
    omega⟩

/-- The positive and negative parts of the coefficient functions of two `k`-cycles and of their
sum satisfy `(u + v)⁺ + u⁻ + v⁻ = u⁺ + v⁺ + (u + v)⁻`. -/
theorem cyclePositivePart_add_cycleNegativePart (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) (c c' : CycleGroup C f k) :
    cyclePositivePart C f k (c + c') + cycleNegativePart C f k c + cycleNegativePart C f k c' =
      cyclePositivePart C f k c + cyclePositivePart C f k c' +
        cycleNegativePart C f k (c + c') := by
  refine DimensionCoefficients.ext C f k ?_
  funext x
  change (c.1 x + c'.1 x).toNat + (-(c.1 x)).toNat + (-(c'.1 x)).toNat =
    (c.1 x).toNat + (c'.1 x).toNat + (-(c.1 x + c'.1 x)).toNat
  omega

/-- The element `[⨁_{n_Z > 0} 𝒪_Z^{⊕n_Z}] - [⨁_{n_Z < 0} 𝒪_Z^{⊕-n_Z}]` of
`K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` attached to a `k`-cycle `∑ n_Z[Z]`. -/
def cycleDimensionLayerClass (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (c : CycleGroup C f k) :
    GrothendieckGroup (coherentDimensionQuotient C f (k - 1) k) :=
  cycleStructureSheafClass C f k (cyclePositivePart C f k c) -
    cycleStructureSheafClass C f k (cycleNegativePart C f k c)

/-- The class attached to a sum of two `k`-cycles is the sum of the two classes. -/
theorem cycleDimensionLayerClass_add (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (c c' : CycleGroup C f k) :
    cycleDimensionLayerClass C f k (c + c') =
      cycleDimensionLayerClass C f k c + cycleDimensionLayerClass C f k c' := by
  have key := congrArg (cycleStructureSheafClass C f k)
    (cyclePositivePart_add_cycleNegativePart C f k c c')
  rw [cycleStructureSheafClass_add, cycleStructureSheafClass_add,
    cycleStructureSheafClass_add, cycleStructureSheafClass_add] at key
  simp only [cycleDimensionLayerClass]
  rw [← sub_eq_zero]
  have hrw : cycleStructureSheafClass C f k (cyclePositivePart C f k (c + c')) -
        cycleStructureSheafClass C f k (cycleNegativePart C f k (c + c')) -
      ((cycleStructureSheafClass C f k (cyclePositivePart C f k c) -
          cycleStructureSheafClass C f k (cycleNegativePart C f k c)) +
        (cycleStructureSheafClass C f k (cyclePositivePart C f k c') -
          cycleStructureSheafClass C f k (cycleNegativePart C f k c'))) =
      (cycleStructureSheafClass C f k (cyclePositivePart C f k (c + c')) +
          cycleStructureSheafClass C f k (cycleNegativePart C f k c) +
          cycleStructureSheafClass C f k (cycleNegativePart C f k c')) -
        (cycleStructureSheafClass C f k (cyclePositivePart C f k c) +
          cycleStructureSheafClass C f k (cyclePositivePart C f k c') +
          cycleStructureSheafClass C f k (cycleNegativePart C f k (c + c'))) := by
    abel
  rw [hrw, key, sub_self]

/-- **Stacks 02S9**, the map `Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))`. A `k`-cycle `∑ n_Z[Z]` is
sent to `[⨁_{n_Z > 0} 𝒪_Z^{⊕n_Z}] - [⨁_{n_Z < 0} 𝒪_Z^{⊕-n_Z}]`, the two locally finite direct
sums being coherent `𝒪_X`-modules whose support has delta-dimension at most `k`. -/
@[stacks 02S9 "the map `Z_k(X) → K₀(Coh_{≤k}/Coh_{≤k-1})`"]
def cycleDimensionLayerHom (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) :
    CycleGroup C f k →+ GrothendieckGroup (coherentDimensionQuotient C f (k - 1) k) :=
  AddMonoidHom.mk' (cycleDimensionLayerClass C f k) (cycleDimensionLayerClass_add C f k)

/-- **Stacks 02S9.** The homomorphism `Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` sends a `k`-cycle
`∑ n_Z[Z]` to the difference of the classes of the direct sums of the structure sheaves of the
integral closed subschemes occurring with positive, respectively negative, coefficient. -/
@[stacks 02S9 "the formula `∑ n_Z[Z] ↦ [⨁_{n_Z > 0} 𝒪_Z^{⊕n_Z}] - [⨁_{n_Z < 0} 𝒪_Z^{⊕-n_Z}]`"]
theorem cycleDimensionLayerHom_apply (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (c : CycleGroup C f k) :
    cycleDimensionLayerHom C f k c =
      GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj
          (cycleStructureSheafDimLE C f k (cyclePositivePart C f k c))) -
        GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj
          (cycleStructureSheafDimLE C f k (cycleNegativePart C f k c))) :=
  rfl

/-! ### The cycle of the locally finite direct sum -/

/-- Objects of `Coh_{≤k}(X)` with the same class in the dimension layer have the same cycle. -/
private theorem dimensionLayerCycle_eq_of_of_eq (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) {M M' : CoherentModulesDimLE C f k}
    (h : GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj M) =
      GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj M')) :
    dimensionLayerCycle C f k M = dimensionLayerCycle C f k M' := by
  simpa only [dimensionLayerCycleHom_of] using congrArg (dimensionLayerCycleHom C f k) h

/-- Isomorphic objects of `Coh_{≤k}(X)` have the same cycle. -/
private theorem dimensionLayerCycle_congr (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (M M' : CoherentModulesDimLE C f k)
    (e : M.obj.obj ≅ M'.obj.obj) :
    dimensionLayerCycle C f k M = dimensionLayerCycle C f k M' :=
  dimensionLayerCycle_eq_of_of_eq C f k (GrothendieckGroup.of_eq_of_iso
    (((lowerDimensionClass C f (k - 1) k).isoModSerre.Q).mapIso
      (dimLEIsoOfModuleIso C f k M M' e)))

/-- The cycle of the locally finite direct sum attached to a sum of two coefficient functions is
the sum of the two cycles. -/
private theorem dimensionLayerCycle_cycleStructureSheafDimLE_add (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    (p q : DimensionCoefficients C f k) :
    dimensionLayerCycle C f k (cycleStructureSheafDimLE C f k (p + q)) =
      dimensionLayerCycle C f k (cycleStructureSheafDimLE C f k p) +
        dimensionLayerCycle C f k (cycleStructureSheafDimLE C f k q) := by
  have h := congrArg (dimensionLayerCycleHom C f k) (cycleStructureSheafClass_add C f k p q)
  rw [map_add] at h
  simpa only [cycleStructureSheafClass, dimensionLayerCycleHom_of] using h

/-- The cycle of an object of `Coh_{≤k}(X)` vanishes at every point whose relative dimension is
not `k`. -/
private theorem dimensionLayerCycle_apply_of_relativeDimension_ne (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    (M : CoherentModulesDimLE C f k) {y : X}
    (hd : relativeDimension C.dimensionFunction f y ≠ k) :
    (dimensionLayerCycle C f k M).1 y = 0 :=
  have : _root_.SheafOfModules.IsCoherent M.obj.obj :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent M.obj.property
  cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C f M.obj.obj k M.property hd

/-- The coefficient at a point of relative dimension `k` of the cycle of an object of
`Coh_{≤k}(X)` is the multiplicity of the underlying module there. -/
private theorem dimensionLayerCycle_apply_of_relativeDimension_eq (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    (M : CoherentModulesDimLE C f k) {y : X}
    (hd : relativeDimension C.dimensionFunction f y = k) :
    (dimensionLayerCycle C f k M).1 y = sheafMultiplicity M.obj.obj y :=
  have : _root_.SheafOfModules.IsCoherent M.obj.obj :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent M.obj.property
  cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C f M.obj.obj k M.property hd

/-- The cycle of an object of `Coh_{≤k}(X)` vanishes at every point outside the support of the
underlying module. -/
private theorem dimensionLayerCycle_apply_eq_zero_of_notMem_supp (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    (M : CoherentModulesDimLE C f k) (y : X) (hy : y ∉ SheafOfModules.supp M.obj.obj) :
    (dimensionLayerCycle C f k M).1 y = 0 := by
  by_cases hd : relativeDimension C.dimensionFunction f y = k
  · exact (dimensionLayerCycle_apply_of_relativeDimension_eq C f k M hd).trans
      (sheafMultiplicity_eq_zero_of_notMem_supp _ hy)
  · exact dimensionLayerCycle_apply_of_relativeDimension_ne C f k M hd

/-- A point in the closure of a point of the same relative dimension is that point: the relative
dimension of Stacks 02JW drops strictly along a nontrivial specialization. -/
private theorem eq_of_mem_closure_of_relativeDimension_eq (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) {x y : X}
    (hx : relativeDimension C.dimensionFunction f x = k)
    (hy : relativeDimension C.dimensionFunction f y = k) (hmem : y ∈ closure {x}) : x = y := by
  obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction C.isUniversallyCatenary
    C.dimensionFunction f
  by_contra hne
  have hlt := d.strictAnti_specializes ((isGenericPoint_closure (x := x)).specializes hmem) hne
  rw [hd, hd, hx, hy] at hlt
  omega

/-- The coefficient function of the prime cycle `N[closure {y}]`: the value `N` at `y` and zero
elsewhere. -/
private def singleCoeff {X : Scheme.{u}} (y : X) (N : ℕ) : X → ℕ :=
  @Function.update ↥X _ (Classical.decEq ↥X) 0 y N

/-- The value of `Stacks.Chow.singleCoeff` at the point it is concentrated at. -/
private theorem singleCoeff_self {X : Scheme.{u}} (y : X) (N : ℕ) : singleCoeff y N y = N := by
  classical
  simp [singleCoeff]

/-- The value of `Stacks.Chow.singleCoeff` at any other point. -/
private theorem singleCoeff_of_ne {X : Scheme.{u}} {y x : X} (h : x ≠ y) (N : ℕ) :
    singleCoeff y N x = 0 := by
  classical
  simp [singleCoeff, h]

/-- A point carrying a nonzero value of `Stacks.Chow.singleCoeff` is the point it is concentrated
at. -/
private theorem eq_of_singleCoeff_ne_zero {X : Scheme.{u}} (y : X) (N : ℕ) {x : X}
    (h : singleCoeff y N x ≠ 0) : x = y := by
  by_contra hne
  exact h (singleCoeff_of_ne hne N)

/-- `Stacks.Chow.singleCoeff` with value zero is the zero function. -/
private theorem singleCoeff_zero_apply {X : Scheme.{u}} (y x : X) : singleCoeff y 0 x = 0 := by
  by_cases hx : x = y
  · subst hx
    exact singleCoeff_self x 0
  · exact singleCoeff_of_ne hx 0

/-- `Stacks.Chow.singleCoeff` is additive in its value. -/
private theorem singleCoeff_add {X : Scheme.{u}} (y : X) (N : ℕ) :
    singleCoeff y (N + 1) = singleCoeff y N + singleCoeff y 1 := by
  funext x
  by_cases hx : x = y
  · subst hx
    simp only [Pi.add_apply, singleCoeff_self]
  · simp only [Pi.add_apply, singleCoeff_of_ne hx]

/-- The index type of the direct sum attached to `Stacks.Chow.singleCoeff y 1` has exactly one
element, namely the unique index lying over `y`. -/
private instance uniqueSigmaFinSingleCoeff {X : Scheme.{u}} (y : X) :
    Unique (Σ x : X, Fin (singleCoeff y 1 x)) where
  default := ⟨y, ⟨0, by rw [singleCoeff_self]; omega⟩⟩
  uniq := by
    rintro ⟨x, m⟩
    have h0 : singleCoeff y 1 x ≠ 0 := by
      have := m.isLt
      omega
    obtain rfl : x = y := eq_of_singleCoeff_ne_zero y 1 h0
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and, Fin.ext_iff]
    have hlt := m.isLt
    have h1 : singleCoeff x 1 x = 1 := singleCoeff_self x 1
    omega

/-- The direct sum attached to `Stacks.Chow.singleCoeff y 1` is the structure sheaf of the
integral closed subscheme attached to `y`. -/
private def cycleStructureSheafSingleIso {X : Scheme.{u}} (y : X) :
    cycleStructureSheaf (singleCoeff y 1) ≅ integralComponentStructureSheaf y :=
  coproductUniqueIso
    fun i : Σ x : X, Fin (singleCoeff y 1 x) ↦ integralComponentStructureSheaf i.1

/-- The coefficient function of the prime cycle `N[closure {y}]`, as a nonnegative coefficient
function of delta-dimension `k`. -/
private def singlePart (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (y : X)
    (hy : relativeDimension C.dimensionFunction f y = k) (N : ℕ) :
    DimensionCoefficients C f k :=
  ⟨singleCoeff y N, fun _ ↦ ⟨Set.univ, Filter.univ_mem,
      (Set.finite_singleton y).subset fun z hz ↦ eq_of_singleCoeff_ne_zero y N hz.2⟩,
    fun x hx ↦ by rw [eq_of_singleCoeff_ne_zero y N hx]; exact hy⟩

/-- The coefficient function of `N + 1` times a prime cycle is the sum of the coefficient
functions of `N` times it and of it. -/
private theorem singlePart_add (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (y : X)
    (hy : relativeDimension C.dimensionFunction f y = k) (N : ℕ) :
    singlePart C f k y hy (N + 1) = singlePart C f k y hy N + singlePart C f k y hy 1 :=
  DimensionCoefficients.ext C f k (singleCoeff_add y N)

/-- The structure sheaf of the integral closed subscheme attached to a point of relative
dimension `k`, read as an object of `Coh_{≤k}(X)`. -/
private def integralComponentDimLE (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (y : X)
    (hy : relativeDimension C.dimensionFunction f y = k) : CoherentModulesDimLE C f k :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  ⟨⟨integralComponentStructureSheaf y,
      AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent inferInstance⟩,
    schemeDeltaDimension_reducedSupport_pushforwardStructureSheaf_le C f
      (integralComponentAt y).subschemeι
      (le_of_eq (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C f y hy))⟩

/-- **Stacks 02QY** at a point. The cycle of the structure sheaf of the integral closed subscheme
attached to `y` has coefficient one at `y`. -/
private theorem dimensionLayerCycle_integralComponentDimLE_apply_self (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) (y : X)
    (hy : relativeDimension C.dimensionFunction f y = k) :
    (dimensionLayerCycle C f k (integralComponentDimLE C f k y hy)).1 y = 1 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hDim := schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C f y hy
  have h := cycleAssociatedToClosedSubscheme_integralComponentAt_self C f y hDim
  rw [cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf C f
    (integralComponentAt y).subschemeι k (le_of_eq hDim)] at h
  exact h

/-- The cycle of the direct sum of `N` copies of the structure sheaf of the integral closed
subscheme attached to `y` has coefficient `N` at `y`. -/
private theorem dimensionLayerCycle_singlePart_apply (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) (y : X)
    (hy : relativeDimension C.dimensionFunction f y = k) (N : ℕ) :
    (dimensionLayerCycle C f k (cycleStructureSheafDimLE C f k (singlePart C f k y hy N))).1 y =
      (N : ℤ) := by
  induction N with
  | zero =>
    rw [Nat.cast_zero]
    refine dimensionLayerCycle_apply_eq_zero_of_notMem_supp C f k _ y fun hmem ↦ ?_
    obtain ⟨x, hx, -⟩ := exists_mem_closure_of_mem_supp_cycleStructureSheaf _ hmem
    exact hx (singleCoeff_zero_apply y x)
  | succ N ih =>
    have h1 : (dimensionLayerCycle C f k
        (cycleStructureSheafDimLE C f k (singlePart C f k y hy 1))).1 y = 1 := by
      rw [dimensionLayerCycle_congr C f k _ (integralComponentDimLE C f k y hy)
        (cycleStructureSheafSingleIso y)]
      exact dimensionLayerCycle_integralComponentDimLE_apply_self C f k y hy
    rw [singlePart_add, dimensionLayerCycle_cycleStructureSheafDimLE_add,
      cycleGroup_add_apply, ih, h1]
    omega

/-- The coefficient function of a `k`-cycle with its value at `y` removed. -/
private def offPart (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (p : DimensionCoefficients C f k) (y : X) :
    DimensionCoefficients C f k :=
  ⟨fun x ↦ p.1 x - singleCoeff y (p.1 y) x, by
    refine ⟨fun x ↦ ?_, fun x hx ↦ p.2.2 x ?_⟩
    · obtain ⟨t, ht, hfin⟩ := p.2.1 x
      refine ⟨t, ht, hfin.subset fun z hz ↦ ⟨hz.1, ?_⟩⟩
      have hz2 : p.1 z - singleCoeff y (p.1 y) z ≠ 0 := hz.2
      simp only [Function.mem_support]
      omega
    · have hx2 : p.1 x - singleCoeff y (p.1 y) x ≠ 0 := hx
      omega⟩

/-- Removing the value of a coefficient function at `y` and adding back the prime cycle it
carries there recovers the function. -/
private theorem offPart_add_singlePart (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (p : DimensionCoefficients C f k) (y : X)
    (hy : relativeDimension C.dimensionFunction f y = k) :
    offPart C f k p y + singlePart C f k y hy (p.1 y) = p := by
  refine DimensionCoefficients.ext C f k ?_
  funext x
  change p.1 x - singleCoeff y (p.1 y) x + singleCoeff y (p.1 y) x = p.1 x
  by_cases hx : x = y
  · subst hx
    rw [singleCoeff_self]
    omega
  · rw [singleCoeff_of_ne hx]
    omega

/-- **The cycle of the locally finite direct sum reads off the coefficient function.** The
coefficient at `y` of the cycle of `⨁_x 𝒪_{closure {x}}^{⊕ n x}` is `n y`: only the summands
concentrated at `y` contribute, since the closure of a point of relative dimension `k` contains
no other point of relative dimension `k`, and each of them contributes one. -/
theorem dimensionLayerCycle_cycleStructureSheafDimLE_apply (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    (p : DimensionCoefficients C f k) (y : X) :
    (dimensionLayerCycle C f k (cycleStructureSheafDimLE C f k p)).1 y = (p.1 y : ℤ) := by
  by_cases hd : relativeDimension C.dimensionFunction f y = k
  · have hoff : (dimensionLayerCycle C f k
        (cycleStructureSheafDimLE C f k (offPart C f k p y))).1 y = 0 := by
      refine dimensionLayerCycle_apply_eq_zero_of_notMem_supp C f k _ y fun hmem ↦ ?_
      obtain ⟨x, hx, hmc⟩ := exists_mem_closure_of_mem_supp_cycleStructureSheaf _ hmem
      have hx2 : p.1 x - singleCoeff y (p.1 y) x ≠ 0 := hx
      have hxy : x ≠ y := by
        intro h
        subst h
        rw [singleCoeff_self] at hx2
        omega
      exact hxy (eq_of_mem_closure_of_relativeDimension_eq C f k
        ((offPart C f k p y).2.2 x hx) hd hmc)
    calc (dimensionLayerCycle C f k (cycleStructureSheafDimLE C f k p)).1 y
        = (dimensionLayerCycle C f k (cycleStructureSheafDimLE C f k
            (offPart C f k p y + singlePart C f k y hd (p.1 y)))).1 y := by
          rw [offPart_add_singlePart]
      _ = (p.1 y : ℤ) := by
          rw [dimensionLayerCycle_cycleStructureSheafDimLE_add, cycleGroup_add_apply, hoff,
            dimensionLayerCycle_singlePart_apply, zero_add]
  · have hp : p.1 y = 0 := by
      by_contra h
      exact hd (p.2.2 y h)
    rw [hp, Nat.cast_zero]
    exact dimensionLayerCycle_apply_of_relativeDimension_ne C f k _ hd

/-- **Stacks 02S9**, one of the two inverse identities: the composite
`Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) → Z_k(X)` of the two maps of Tag 02S9 is the identity.

On a cycle `∑ n_Z[Z]` the two locally finite direct sums have cycles `∑_{n_Z > 0} n_Z[Z]` and
`∑_{n_Z < 0} (-n_Z)[Z]`, whose difference is the cycle one started with. -/
@[stacks 02S9 "the composite `Z_k(X) → K₀(Coh_{≤k}/Coh_{≤k-1}) → Z_k(X)` is the identity"]
theorem dimensionLayerCycleHom_comp_cycleDimensionLayerHom (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) :
    (dimensionLayerCycleHom C f k).comp (cycleDimensionLayerHom C f k) = AddMonoidHom.id _ := by
  refine AddMonoidHom.ext fun c ↦ ?_
  rw [AddMonoidHom.comp_apply, cycleDimensionLayerHom_apply, map_sub, dimensionLayerCycleHom_of,
    dimensionLayerCycleHom_of, AddMonoidHom.id_apply]
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  change (dimensionLayerCycle C f k
      (cycleStructureSheafDimLE C f k (cyclePositivePart C f k c))).1 y -
    (dimensionLayerCycle C f k
      (cycleStructureSheafDimLE C f k (cycleNegativePart C f k c))).1 y = c.1 y
  rw [dimensionLayerCycle_cycleStructureSheafDimLE_apply,
    dimensionLayerCycle_cycleStructureSheafDimLE_apply]
  change ((c.1 y).toNat : ℤ) - ((-(c.1 y)).toNat : ℤ) = c.1 y
  omega

/-- **Stacks 02S9.** The cycle class of the element of `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` attached
to a `k`-cycle is that cycle. -/
@[stacks 02S9 "`[⨁_{n_Z > 0} 𝒪_Z^{⊕n_Z}]_k - [⨁_{n_Z < 0} 𝒪_Z^{⊕-n_Z}]_k = ∑ n_Z[Z]`"]
theorem dimensionLayerCycleHom_cycleDimensionLayerHom (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) (c : CycleGroup C f k) :
    dimensionLayerCycleHom C f k (cycleDimensionLayerHom C f k c) = c :=
  congrArg (fun φ : CycleGroup C f k →+ CycleGroup C f k ↦ φ c)
    (dimensionLayerCycleHom_comp_cycleDimensionLayerHom C f k)

/-- **Stacks 02S9**, half of the bijectivity. The map
`Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` is injective, the cycle class homomorphism being a left
inverse of it. -/
@[stacks 02S9 "injectivity of `Z_k(X) → K₀(Coh_{≤k}/Coh_{≤k-1})`"]
theorem injective_cycleDimensionLayerHom (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) : Function.Injective (cycleDimensionLayerHom C f k) :=
  Function.LeftInverse.injective (g := dimensionLayerCycleHom C f k)
    (dimensionLayerCycleHom_cycleDimensionLayerHom C f k)

/-- **Stacks 02S9**, half of the bijectivity. The cycle class homomorphism
`K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) → Z_k(X)` is surjective: every `k`-cycle is the cycle class of the
element attached to it.

The same conclusion is proved, for a quasi-compact `X`, as
`Stacks.Chow.surjective_dimensionLayerCycleHom` in
`StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerClassOfCycle`, through the rival
construction of the map of Tag 02S9 recorded in
`StacksFrontier/AlgebraicGeometry/Chow/Degrees/DimensionLayerCycleClass.lean`. The version here
needs no quasi-compactness, the section it uses being `Stacks.Chow.cycleDimensionLayerHom`,
which is defined for every `X` locally of finite type over the base; hence the name, and hence
no quasi-compactness in the attribute below. -/
@[stacks 02S9 "surjectivity of `K₀(Coh_{≤k}/Coh_{≤k-1}) → Z_k(X)`, with no quasi-compactness"]
theorem surjective_dimensionLayerCycleHom_of_cycleDimensionLayerHom (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) : Function.Surjective (dimensionLayerCycleHom C f k) :=
  fun c ↦ ⟨cycleDimensionLayerHom C f k c, dimensionLayerCycleHom_cycleDimensionLayerHom C f k c⟩

/-! ### The multiplicity coefficients of a coherent module -/

/-- The coefficients of the cycle of a coherent `𝒪_X`-module are nonnegative: at a point of
relative dimension `k` the coefficient is the length of the stalk there, and at every other point
it vanishes. -/
theorem dimensionLayerCycle_nonneg (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (F : CoherentModulesDimLE C f k) (y : X) :
    0 ≤ (dimensionLayerCycle C f k F).1 y := by
  by_cases hd : relativeDimension C.dimensionFunction f y = k
  · rw [dimensionLayerCycle_apply_of_relativeDimension_eq C f k F hd]
    simp [sheafMultiplicity]
  · rw [dimensionLayerCycle_apply_of_relativeDimension_ne C f k F hd]

/-- The multiplicity function of a coherent `𝒪_X`-module whose support has delta-dimension at
most `k`: the coefficient function of the cycle `[F]_k`, read as a nonnegative coefficient
function. Its value at a point `ξ` of relative dimension `k` is the length `m_{Z_ξ, F}` of the
stalk `F_ξ`, and it vanishes at every other point. -/
def multiplicityCoefficients (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (F : CoherentModulesDimLE C f k) :
    DimensionCoefficients C f k :=
  cyclePositivePart C f k (dimensionLayerCycle C f k F)

/-- The multiplicity function of a coherent `𝒪_X`-module is the coefficient function of its
cycle. -/
@[simp]
theorem coe_multiplicityCoefficients (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (F : CoherentModulesDimLE C f k) (x : X) :
    ((multiplicityCoefficients C f k F).1 x : ℤ) = (dimensionLayerCycle C f k F).1 x :=
  Int.toNat_of_nonneg (dimensionLayerCycle_nonneg C f k F x)

/-- The negative part of the cycle of a coherent `𝒪_X`-module vanishes, its coefficients being
lengths of stalks. -/
theorem cycleNegativePart_dimensionLayerCycle (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) (F : CoherentModulesDimLE C f k) :
    (cycleNegativePart C f k (dimensionLayerCycle C f k F)).1 = 0 := by
  funext x
  have h := dimensionLayerCycle_nonneg C f k F x
  change (-(dimensionLayerCycle C f k F).1 x).toNat = 0
  omega

/-- A coefficient function which vanishes identically contributes the zero class: it is the sum
of two copies of itself, and the class is additive in the coefficient function. -/
theorem cycleStructureSheafClass_eq_zero (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (p : DimensionCoefficients C f k) (hp : p.1 = 0) :
    cycleStructureSheafClass C f k p = 0 := by
  have hpp : p + p = p :=
    DimensionCoefficients.ext C f k (by rw [DimensionCoefficients.coe_add, hp, add_zero])
  have h := cycleStructureSheafClass_add C f k p p
  rw [hpp] at h
  exact left_eq_add.mp h

/-- **The map from cycles, evaluated on the cycle of a coherent module.** On the cycle `[F]_k` of
a coherent `𝒪_X`-module whose support has delta-dimension at most `k`, the map
`Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` of Tag 02S9 takes the value the class of the locally
finite direct sum `⨁_ξ 𝒪_{Z_ξ}^{⊕ m_ξ}` of the structure sheaves of the integral closed
subschemes of `[F]_k`, with no correction term: the coefficients of `[F]_k` are lengths of
stalks, hence nonnegative, so its negative part is zero. -/
theorem cycleDimensionLayerHom_dimensionLayerCycle_eq_cycleStructureSheafClass
    (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    (F : CoherentModulesDimLE C f k) :
    cycleDimensionLayerHom C f k (dimensionLayerCycle C f k F) =
      cycleStructureSheafClass C f k (multiplicityCoefficients C f k F) := by
  have h : cycleDimensionLayerHom C f k (dimensionLayerCycle C f k F) =
      cycleStructureSheafClass C f k (multiplicityCoefficients C f k F) -
        cycleStructureSheafClass C f k
          (cycleNegativePart C f k (dimensionLayerCycle C f k F)) := rfl
  rw [h, cycleStructureSheafClass_eq_zero C f k _
    (cycleNegativePart_dimensionLayerCycle C f k F), sub_zero]

/-- The multiplicity function of the locally finite direct sum `⨁_x 𝒪_{closure {x}}^{⊕ n x}` is
`n`. -/
@[simp]
theorem multiplicityCoefficients_cycleStructureSheafDimLE (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    (p : DimensionCoefficients C f k) :
    multiplicityCoefficients C f k (cycleStructureSheafDimLE C f k p) = p := by
  refine DimensionCoefficients.ext C f k ?_
  funext x
  have h : ((multiplicityCoefficients C f k (cycleStructureSheafDimLE C f k p)).1 x : ℤ) =
      (p.1 x : ℤ) := by
    rw [coe_multiplicityCoefficients, dimensionLayerCycle_cycleStructureSheafDimLE_apply]
  exact Nat.cast_injective h

/-! ### Isomorphisms in a dimension layer -/

/-- A morphism of `Coh_{≤k}(X)` whose kernel and cokernel have support of delta-dimension at most
`k - 1` becomes an isomorphism in the dimension layer `Coh_{≤k}(X)/Coh_{≤k-1}(X)`: those are the
morphisms inverted by the localization functor at a Serre class. -/
theorem isIso_map_isoModSerreQ (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) {A B : CoherentModulesDimLE C f k} (φ : A ⟶ B)
    (hker : lowerDimensionClass C f (k - 1) k (kernel φ))
    (hcoker : lowerDimensionClass C f (k - 1) k (cokernel φ)) :
    IsIso ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.map φ) :=
  (ObjectProperty.SerreClassLocalization.isIso_map_iff
    (lowerDimensionClass C f (k - 1) k).isoModSerre.Q
    (lowerDimensionClass C f (k - 1) k) φ).mpr ⟨hker, hcoker⟩

/-- Two objects of `Coh_{≤k}(X)` joined by a morphism whose kernel and cokernel have support of
delta-dimension at most `k - 1` have the same class in `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))`. -/
theorem of_eq_of_lowerDimensionClass_kernel_cokernel (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) {A B : CoherentModulesDimLE C f k} (φ : A ⟶ B)
    (hker : lowerDimensionClass C f (k - 1) k (kernel φ))
    (hcoker : lowerDimensionClass C f (k - 1) k (cokernel φ)) :
    GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj A) =
      GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj B) :=
  have := isIso_map_isoModSerreQ C f k φ hker hcoker
  GrothendieckGroup.of_eq_of_iso
    (asIso ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.map φ))

/-- Two objects of `Coh_{≤k}(X)` joined by a morphism whose kernel and cokernel have support of
delta-dimension at most `k - 1` have the same cycle: the cycle is read off the class in the
dimension layer. -/
theorem dimensionLayerCycle_eq_of_lowerDimensionClass_kernel_cokernel (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    {A B : CoherentModulesDimLE C f k} (φ : A ⟶ B)
    (hker : lowerDimensionClass C f (k - 1) k (kernel φ))
    (hcoker : lowerDimensionClass C f (k - 1) k (cokernel φ)) :
    dimensionLayerCycle C f k A = dimensionLayerCycle C f k B :=
  dimensionLayerCycle_eq_of_of_eq C f k
    (of_eq_of_lowerDimensionClass_kernel_cokernel C f k φ hker hcoker)

/-! ### The remaining step of Tag 02S9 -/

/-- **The generic structure of a coherent module in a dimension layer.** The assertion that every
coherent `𝒪_X`-module `F` whose support has delta-dimension at most `k` is isomorphic, in the
dimension layer `Coh_{≤k}(X)/Coh_{≤k-1}(X)`, to the locally finite direct sum
`⨁_ξ 𝒪_{Z_ξ}^{⊕ m_ξ}` of the structure sheaves of the integral closed subschemes of its cycle
`[F]_k = ∑ m_ξ [Z_ξ]`, each repeated with its multiplicity. -/
def DimensionLayerIsStructureSheafSum (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) : Prop :=
  ∀ F : CoherentModulesDimLE C f k,
    Nonempty ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj
        (cycleStructureSheafDimLE C f k (multiplicityCoefficients C f k F)) ≅
      (lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj F)

/-- On the locally finite direct sums `⨁_x 𝒪_{closure {x}}^{⊕ n x}` themselves the generic
structure of a dimension layer holds, the multiplicity function of such a direct sum being
`n`. -/
theorem nonempty_iso_cycleStructureSheafDimLE (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) (p : DimensionCoefficients C f k) :
    Nonempty ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj
        (cycleStructureSheafDimLE C f k
          (multiplicityCoefficients C f k (cycleStructureSheafDimLE C f k p))) ≅
      (lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj
        (cycleStructureSheafDimLE C f k p)) := by
  rw [multiplicityCoefficients_cycleStructureSheafDimLE]
  exact ⟨Iso.refl _⟩

/-- Granting the generic structure of a dimension layer, the class of a coherent `𝒪_X`-module of
support dimension at most `k` in `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` is the image of its cycle
`[F]_k` under the map `Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` of Tag 02S9. -/
theorem cycleDimensionLayerHom_dimensionLayerCycle_of_isStructureSheafSum (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    (h : DimensionLayerIsStructureSheafSum C f k) (F : CoherentModulesDimLE C f k) :
    cycleDimensionLayerHom C f k (dimensionLayerCycle C f k F) =
      GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj F) := by
  rw [cycleDimensionLayerHom_dimensionLayerCycle_eq_cycleStructureSheafClass]
  exact GrothendieckGroup.of_eq_of_iso (h F).some

/-- Granting the generic structure of a dimension layer, the composite
`K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) → Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` of the two maps of
Tag 02S9 is the identity. -/
theorem cycleDimensionLayerHom_comp_dimensionLayerCycleHom_of_isStructureSheafSum
    (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    (h : DimensionLayerIsStructureSheafSum C f k) :
    (cycleDimensionLayerHom C f k).comp (dimensionLayerCycleHom C f k) = AddMonoidHom.id _ := by
  refine GrothendieckGroup.hom_ext fun Y ↦ ?_
  have e := (lowerDimensionClass C f (k - 1) k).isoModSerre.Q.objObjPreimageIso Y
  rw [← GrothendieckGroup.of_eq_of_iso e, AddMonoidHom.comp_apply, dimensionLayerCycleHom_of,
    AddMonoidHom.id_apply]
  exact cycleDimensionLayerHom_dimensionLayerCycle_of_isStructureSheafSum C f k h _

/-- Granting the generic structure of a dimension layer, the map
`Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` of Tag 02S9 is surjective. -/
theorem surjective_cycleDimensionLayerHom_of_isStructureSheafSum (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    (h : DimensionLayerIsStructureSheafSum C f k) :
    Function.Surjective (cycleDimensionLayerHom C f k) := fun x ↦
  ⟨dimensionLayerCycleHom C f k x, congrArg
    (fun φ : GrothendieckGroup (coherentDimensionQuotient C f (k - 1) k) →+
      GrothendieckGroup (coherentDimensionQuotient C f (k - 1) k) ↦ φ x)
    (cycleDimensionLayerHom_comp_dimensionLayerCycleHom_of_isStructureSheafSum C f k h)⟩

end Stacks.Chow

end
