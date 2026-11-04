module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Subgroups.Clopen
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFamilyPicardClass
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardFunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# The Picard scheme of a curve, for a representable Picard functor

Let `X` be a smooth curve over a field `k` whose Picard functor `Pic_{X/k}` of
[Stacks, Tag 0B9L] is representable (for a smooth projective curve over a separably closed field
this is [Stacks, Tag 0B9Z]). This file names the representing object and proves two parts of
[Stacks, Tag 0BA0]:

* a `ℤ`-indexed family of open immersions into `Pic_{X/k}` with pairwise disjoint ranges
  covering it exhibits `Pic_{X/k}` as the coproduct of its members, each of which is also closed;
* a scheme `H` representing the degree-`d` Hilbert functor of `X` carries a canonical morphism
  `γ_d : H ⟶ Pic_{X/k}`, the morphism that Yoneda assigns to the class of `𝒪(D)` for the
  universal family `D` on `X ×_k H` (an effective Cartier divisor by [Stacks, Tag 0B9D], see
  `Stacks.Hilbert.HilbertFamily.picardClass`).

## Main definitions

* `Stacks.PicardFunctor.picardSchemeOver` and `Stacks.PicardFunctor.picardScheme`: the object of
  the site representing the Picard functor, and its underlying scheme.
* `Stacks.PicardFunctor.hilbertToPicard`: the morphism `γ_d`.

## Main results

* `Stacks.PicardFunctor.isClosedImmersion_of_degreeDecomposition`: each member of the degree
  decomposition is a closed immersion.
* `Stacks.PicardFunctor.nonempty_isColimit_cofanMk_of_degreeDecomposition`: `Pic_{X/k}` is the
  coproduct of the members of the degree decomposition.
* `Stacks.PicardFunctor.homEquiv_comp_hilbertToPicard`: the `T`-point of `Pic_{X/k}` that `γ_d`
  assigns to a degree-`d` family `D` on `X ×_k T` is the class of `𝒪(D)`.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0B9D](https://stacks.math.columbia.edu/tag/0B9D)
* [Stacks Project, Tag 0B9L](https://stacks.math.columbia.edu/tag/0B9L)
* [Stacks Project, Tag 0B9Z](https://stacks.math.columbia.edu/tag/0B9Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.PicardFunctor

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)

section Representable

variable [(picardFunctor B hX hk f).IsRepresentable]

/-- **`Pic_{X/S}`, the Picard scheme**: the scheme of the site representing the Picard functor,
when it is representable ([Stacks, Tag 0B9Z]). -/
abbrev picardSchemeOver : BigFppfOver B (Spec (.of k)) hk := (picardFunctor B hX hk f).reprX

/-- The underlying scheme of `Pic_{X/S}`. -/
abbrev picardScheme : Scheme.{u} := B.inclusion.obj (picardSchemeOver B hX hk f).left

/-- The identification of the morphisms into the Picard scheme with the values of the Picard
functor, `Hom_S(T, Pic_{X/S}) ≃ Pic_{X/S}(T)`. -/
abbrev picardHomEquiv {T : BigFppfOver B (Spec (.of k)) hk} :
    (T ⟶ picardSchemeOver B hX hk f) ≃ (picardFunctor B hX hk f).obj (op T) :=
  (picardFunctor B hX hk f).representableBy.homEquiv

/-! ### Clause (1): the degree decomposition presents `Pic_{X/k}` as a disjoint union -/

variable {P : ℤ → Scheme.{u}} (j : ∀ d : ℤ, P d ⟶ picardScheme B hX hk f)

/-- **The members of the degree decomposition of `Pic_{X/k}` are closed.** Let `X` be a curve over
a field `k` whose Picard functor is representable, and let `Pic_{X/k}` be the representing scheme.
A `ℤ`-indexed family of open subschemes of `Pic_{X/k}` with pairwise disjoint ranges covering it
— the degree decomposition into the components `Pic^d_{X/k}` of [Stacks, Tag 0BA0] (1) — has
every member closed as well as open. -/
theorem isClosedImmersion_of_degreeDecomposition [∀ d, IsOpenImmersion (j d)]
    (hdisj : Pairwise fun d e => Disjoint (Set.range (j d).base) (Set.range (j e).base))
    (hcover : ⋃ d, Set.range (j d).base = Set.univ) (d : ℤ) :
    IsClosedImmersion (j d) :=
  IsClosedImmersion.of_isPreimmersion _
    (isClosed_range_of_pairwiseDisjoint_of_iUnion_range_eq_univ j hdisj hcover d)

/-- **`Pic_{X/k}` is the disjoint union of its degree components.** A `ℤ`-indexed family of open
subschemes of `Pic_{X/k}` with pairwise disjoint ranges covering it exhibits `Pic_{X/k}` as the
coproduct `∐_{d ∈ ℤ} Pic^d_{X/k}` of its members ([Stacks, Tag 0BA0] (1)). -/
theorem nonempty_isColimit_cofanMk_of_degreeDecomposition [∀ d, IsOpenImmersion (j d)]
    (hdisj : Pairwise fun d e => Disjoint (Set.range (j d).base) (Set.range (j e).base))
    (hcover : ⋃ d, Set.range (j d).base = Set.univ) :
    Nonempty (IsColimit (Cofan.mk (picardScheme B hX hk f) j)) :=
  nonempty_isColimit_cofanMk_of j (Opens.ext (by rwa [Opens.coe_iSup, Opens.coe_top]))
    fun _ _ hab => Opens.coe_disjoint.mp (hdisj hab)

end Representable

/-! ### Clause (4): the morphism `γ_d : Hilb^d_{X/k} ⟶ Pic_{X/k}` -/

section Gamma

variable [(picardFunctor B hX hk f).IsRepresentable]
  [SmoothOfRelativeDimension 1 (B.inclusion.map f)]

/-- A morphism of test schemes of the big fppf site, read as a morphism of schemes over the
base. -/
abbrev testMap {T U : BigFppfOver B (Spec (.of k)) hk} (t : T ⟶ U) :
    (Over.mk (B.inclusion.map T.hom) : Over (B.inclusion.obj (B.obj hk))) ⟶
      Over.mk (B.inclusion.map U.hom) :=
  Over.homMk (B.inclusion.map t.left) (by
    simp only [Over.mk_hom, ← Functor.map_comp, Over.w])

omit [(picardFunctor B hX hk f).IsRepresentable]
  [SmoothOfRelativeDimension 1 (B.inclusion.map f)] in
/-- The transition map of the base changes that the Picard presheaf restricts along is the one
the Hilbert functor restricts families along. -/
theorem familyBaseChangeMap_testMap {T U : BigFppfOver B (Spec (.of k)) hk} (t : T ⟶ U) :
    Stacks.Hilbert.familyBaseChangeMap (Over.mk (B.inclusion.map f)) (testMap B hk t) =
      baseChangeMap B hX hk f t :=
  rfl

variable {d : ℕ} (H : BigFppfOver B (Spec (.of k)) hk)
  (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map f))
    (Over.mk (B.inclusion.map H.hom)) d)

include hH

/-- The class in `Pic(X ×_k H)` of the invertible sheaf of the universal degree-`d` family on a
scheme representing the degree-`d` Hilbert functor of `X`. -/
def universalHilbertPicardClass : picardAt B hX hk f H :=
  (hH.family (𝟙 _)).picardClass

omit [(picardFunctor B hX hk f).IsRepresentable] in
/-- The universal class is the Picard class of the universal family's ideal sheaf. -/
theorem universalHilbertPicardClass_eq :
    universalHilbertPicardClass B hX hk f H hH = (hH.family (𝟙 _)).picardClass :=
  rfl

/-- **The morphism `γ_d : Hilb^d_{X/k} ⟶ Pic_{X/k}` of [Stacks, Tag 0BA0] (4).** Let `X` be a
curve smooth of relative dimension one over a field `k` whose Picard functor is representable, and
let `H` represent its degree-`d` Hilbert functor. Then `γ_d` is the morphism Yoneda assigns to the
class, in `Pic_{X/k}(H)`, of the invertible sheaf `𝒪(D)` of the universal degree-`d` family `D` on
`X ×_k H`, an effective Cartier divisor by [Stacks, Tag 0B9D]. -/
def hilbertToPicard : H ⟶ picardSchemeOver B hX hk f :=
  (picardHomEquiv B hX hk f).symm
    ((toPicardFunctor B hX hk f).app (op H) (universalHilbertPicardClass B hX hk f H hH))

/-- The point of `Pic_{X/k}` that `γ_d` is, read through `Hom_k(H, Pic_{X/k}) ≃ Pic_{X/k}(H)`,
is the class of the invertible sheaf of the universal degree-`d` family. -/
theorem homEquiv_hilbertToPicard :
    picardHomEquiv B hX hk f (hilbertToPicard B hX hk f H hH) =
      (toPicardFunctor B hX hk f).app (op H) (universalHilbertPicardClass B hX hk f H hH) :=
  Equiv.apply_symm_apply _ _

omit [(picardFunctor B hX hk f).IsRepresentable]
  [SmoothOfRelativeDimension 1 (B.inclusion.map f)] in
/-- The ideal of the family that a `T`-point `t` of `H` classifies is the inverse image of the
ideal of the universal family along the base change by `t`. -/
private theorem naturality_baseChangeMap {T : BigFppfOver B (Spec (.of k)) hk} (t : T ⟶ H) :
    (hH.family (testMap B hk t)).ideal =
      (hH.family (𝟙 (Over.mk (B.inclusion.map H.hom)))).ideal.comap
        (baseChangeMap B hX hk f t) := by
  simpa only [Category.comp_id, familyBaseChangeMap_testMap] using
    hH.naturality (testMap B hk t) (𝟙 (Over.mk (B.inclusion.map H.hom)))

omit [(picardFunctor B hX hk f).IsRepresentable] in
/-- **Restricting the universal class along a `T`-point of `H` gives the class of the family that
point classifies.** -/
theorem picardMap_universalHilbertPicardClass {T : BigFppfOver B (Spec (.of k)) hk} (t : T ⟶ H) :
    picardMap B hX hk f t (universalHilbertPicardClass B hX hk f H hH) =
      (hH.family (testMap B hk t)).picardClass :=
  Stacks.Hilbert.HilbertFamily.schemePullbackClass_picardClass
    (hH.family (𝟙 (Over.mk (B.inclusion.map H.hom)))) (hH.family (testMap B hk t))
    (baseChangeMap B hX hk f t) (naturality_baseChangeMap B hX hk f H hH t)

/-- **The defining property of `γ_d` in [Stacks, Tag 0BA0] (4).** The point of `Pic_{X/k}` that
`γ_d` assigns to a `T`-point `t` of `Hilb^d_{X/k}` — that is, to a degree-`d` family `D_t` on
`X ×_k T` — is the class of the invertible sheaf `𝒪(D_t)`. -/
theorem homEquiv_comp_hilbertToPicard {T : BigFppfOver B (Spec (.of k)) hk} (t : T ⟶ H) :
    picardHomEquiv B hX hk f (t ≫ hilbertToPicard B hX hk f H hH) =
      (toPicardFunctor B hX hk f).app (op T) (hH.family (testMap B hk t)).picardClass := by
  refine ((picardFunctor B hX hk f).representableBy.homEquiv_comp t
    (hilbertToPicard B hX hk f H hH)).trans ?_
  rw [homEquiv_hilbertToPicard, ← picardMap_universalHilbertPicardClass]
  exact (toPicardFunctor_app_naturality B hX hk f t
    (universalHilbertPicardClass B hX hk f H hH)).symm

end Gamma

end Stacks.PicardFunctor

end
