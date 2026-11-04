module

public import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.AlgebraicTopology.SimplicialSet.TrivialKanFibration
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Čech nerves of surjections and coskeletal trivial Kan fibrations

Trivial Kan fibrations between coskeletal simplicial sets, and the homotopy equivalence given by
the Čech nerve of a surjection.
-/

/-!
## Trivial Kan fibrations between coskeletal simplicial sets

A morphism `f : V ⟶ U` of simplicial sets is a *trivial Kan fibration* if `f₀ : V₀ → U₀` is
surjective and if, for every `n ≥ 1`, every commutative square whose left edge is the boundary
inclusion `∂Δ[n] ↪ Δ[n]` and whose right edge is `f` admits a diagonal filler `Δ[n] ⟶ V` making
both triangles commute; this is `SSet.trivialKanFibrations`, read through
`SSet.trivialKanFibrations_iff_surjective_and_hasLiftingProperty`.

Writing `sk_n` for the `n`-truncation functor and `cosk_n` for its right adjoint, such an `f` is a
trivial Kan fibration as soon as its components `fᵢ` are bijective for `i < n`, `fₙ` is surjective,
and the two units `U ⟶ cosk_n sk_n U` and `V ⟶ cosk_n sk_n V` are isomorphisms.

### Main results

* `SSet.trivialKanFibrations_of_coskeletal`: a morphism of simplicial sets whose
  components are bijective below degree `n`, surjective in degree `n`, and whose source and target
  are `n`-coskeletal, is a trivial Kan fibration.

### References

* [Stacks, Tag 08NL](https://stacks.math.columbia.edu/tag/08NL)
* [Stacks, Tag 01A6](https://stacks.math.columbia.edu/tag/01A6)
-/

section

@[expose] public section

open CategoryTheory SSet Simplicial Opposite

namespace SSet

/-- For `k.len < m`, every `k`-simplex of `Δ[m]` lies in the boundary `∂Δ[m]`. -/
public theorem boundary_obj_eq_top {m : ℕ} {k : SimplexCategory} (hk : k.len < m) :
    (∂Δ[m]).obj (op k) = ⊤ := by
  ext x
  simp only [Set.top_eq_univ, Set.mem_univ, iff_true, SSet.boundary, Set.mem_ofPred_eq]
  intro hsurj
  have hcard := Fintype.card_le_of_surjective _ hsurj
  simp only [Fintype.card_fin] at hcard
  omega

/-- A subcomplex inclusion is an isomorphism in a given degree when the subcomplex contains
everything in that degree. -/
public theorem isIso_subcomplex_ι_app {X : SSet} (A : X.Subcomplex) (k : SimplexCategoryᵒᵖ)
    (h : A.obj k = ⊤) : IsIso (A.ι.app k) := by
  rw [isIso_iff_bijective]
  refine ⟨fun a b hab => Subtype.ext hab, fun y => ⟨⟨y, ?_⟩, rfl⟩⟩
  rw [h]
  trivial

/-- For `m > n`, the `n`-truncation of the boundary inclusion `∂Δ[m] ↪ Δ[m]` is an isomorphism,
`∂Δ[m]` and `Δ[m]` agreeing on all simplices of dimension `≤ n`. -/
public theorem isIso_truncation_boundary_ι {n m : ℕ} (hnm : n < m) :
    IsIso ((truncation n).map (∂Δ[m]).ι) := by
  have happ : ∀ x : (SimplexCategory.Truncated n)ᵒᵖ,
      IsIso (((truncation n).map (∂Δ[m]).ι).app x) := by
    intro x
    rw [SSet.truncation, SimplicialObject.truncation, Functor.whiskeringLeft_obj_map,
      Functor.whiskerLeft_app]
    refine isIso_subcomplex_ι_app _ _ (boundary_obj_eq_top ?_)
    have hlen : ((SimplexCategory.Truncated.inclusion n).obj (unop x)).len ≤ n :=
      (unop x).property
    omega
  exact NatIso.isIso_of_isIso_app _

/-- Post-composition with `f` is injective on maps `Δ[k] ⟶ V` whenever the `k`-th component `fₖ`
is injective. -/
private theorem stdSimplex_postcomp_injective {V U : SSet} (f : V ⟶ U) (k : ℕ)
    (hf : Function.Injective (f.app (op ⦋k⦌))) :
    Function.Injective (fun a : Δ[k] ⟶ V => a ≫ f) := by
  intro a b hab
  refine yonedaEquiv.injective (hf ?_)
  simp only [← SSet.yonedaEquiv_comp]
  exact congrArg _ hab

/-- For `m' + 1 ≤ n`, post-composition with a morphism `f` whose components are bijective below
degree `n` is injective on maps `∂Δ[m'+1] ⟶ V`. -/
private theorem boundary_postcomp_injective {V U : SSet} (f : V ⟶ U) (n : ℕ)
    (h1 : ∀ i : ℕ, i < n → Function.Bijective (f.app (op ⦋i⦌)))
    (m' : ℕ) (hmn : m' + 1 ≤ n)
    (g g' : (∂Δ[m'+1] : SSet) ⟶ V) (hgg : g ≫ f = g' ≫ f) : g = g' := by
  apply SSet.boundary.hom_ext
  intro i
  apply stdSimplex_postcomp_injective f m' (h1 m' (by omega)).injective
  simp [hgg]

/-- Let `f` have bijective components below degree `n` and a surjective component in degree `n`.
Then for `1 ≤ m ≤ n` the boundary inclusion `∂Δ[m] ↪ Δ[m]` has the left lifting property with
respect to `f`. -/
private theorem hasLiftingProperty_le {V U : SSet} (f : V ⟶ U) (n : ℕ)
    (h1 : ∀ i : ℕ, i < n → Function.Bijective (f.app (op ⦋i⦌)))
    (h2 : Function.Surjective (f.app (op ⦋n⦌)))
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    HasLiftingProperty (∂Δ[m]).ι f := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hsurj : Function.Surjective (f.app (op ⦋m' + 1⦌)) :=
    (eq_or_lt_of_le hmn).elim (fun h => h ▸ h2) fun h => (h1 _ h).surjective
  constructor
  intro α β sq
  obtain ⟨y, hy⟩ := hsurj (yonedaEquiv β)
  have hr : yonedaEquiv.symm y ≫ f = β :=
    yonedaEquiv.injective (by rwa [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply])
  refine ⟨⟨⟨yonedaEquiv.symm y, ?_, hr⟩⟩⟩
  apply boundary_postcomp_injective f n h1 m' hmn
  rw [Category.assoc, hr, sq.w]

/-- **Stacks 01A6**.
Let `f : V ⟶ U` be a morphism of simplicial sets and let `n ≥ 0`. Assume:
1. `fᵢ` is bijective for every `i < n`;
2. `fₙ` is surjective;
3. the canonical (unit) morphism `U → cosk_n sk_n U` is an isomorphism;
4. the canonical (unit) morphism `V → cosk_n sk_n V` is an isomorphism.
Then `f` is a trivial Kan fibration. -/
@[stacks 01A6]
theorem trivialKanFibrations_of_coskeletal
    {V U : SSet} (f : V ⟶ U) (n : ℕ)
    (h1 : ∀ i : ℕ, i < n → Function.Bijective (f.app (op ⦋i⦌)))
    (h2 : Function.Surjective (f.app (op ⦋n⦌)))
    (h3 : IsIso ((coskAdj n).unit.app U))
    (h4 : IsIso ((coskAdj n).unit.app V)) :
    trivialKanFibrations f := by
  rw [trivialKanFibrations_iff_surjective_and_hasLiftingProperty]
  refine ⟨(Nat.eq_zero_or_pos n).elim (fun hn => hn ▸ h2) fun hn => (h1 0 hn).surjective, ?_⟩
  intro m hm
  rcases lt_or_ge n m with hnm | hmn
  · have earrow : Arrow.mk f ≅ Arrow.mk ((Truncated.cosk n).map ((truncation n).map f)) :=
      Arrow.isoMk (asIso ((coskAdj n).unit.app V)) (asIso ((coskAdj n).unit.app U)) (by simp)
    have : HasLiftingProperty ∂Δ[m].ι ((Truncated.cosk n).map ((truncation n).map f)) := by
      rw [← (coskAdj n).hasLiftingProperty_iff]
      have := isIso_truncation_boundary_ι hnm
      infer_instance
    exact HasLiftingProperty.of_arrow_iso_right ∂Δ[m].ι earrow.symm
  · exact hasLiftingProperty_le f n h1 h2 m hm hmn

end SSet

end

end

/-!
## A homotopy equivalence

Two lemmas about maps into a simplicial set which is determined by its low degrees.

Let `n : ℕ` and let `f₀, f₁ : V ⟶ U` be maps of simplicial sets whose components `V_i ⟶ U_i` agree
for `i < n`. If the canonical morphism `U ⟶ cosk_n sk_n U` is an isomorphism, then `f₀` is
homotopic to `f₁`, and no hypothesis on `V` is needed: coskeletality of `U` makes a morphism *into*
`U` the same thing as its `n`-truncation, whatever the source, since the adjunction `sk_n ⊣ cosk_n`
gives `Hom(X, U) = Hom(X, cosk_n sk_n U) = Hom(sk_n X, sk_n U)` for every simplicial set `X`. So a
homotopy may be prescribed on `n`-truncations, and the one built here is the source's:
`h_k(v, α) = f₀(v) = f₁(v)` for `k < n` and, in degree `n`, `h_n(v, α) = f₁(v)` if
`α : ⦋n⦌ ⟶ ⦋1⦌` is constant equal to `1` and `h_n(v, α) = f₀(v)` otherwise. Here `sk_n` is
restriction along `Δ_{≤ n} ⊆ Δ`, Mathlib's `SimplicialObject.truncation n`, and `cosk_n` is its
right adjoint `SimplicialObject.Truncated.cosk n`, so that the canonical morphism is the unit of
`SimplicialObject.coskAdj n`.

Let `f : A → B` be a map of sets and let `U` be the simplicial set whose `n`-simplices are the
`(n + 1)`-fold fibre product `A ×_B A ×_B ⋯ ×_B A`, a map `φ : ⦋n⦌ ⟶ ⦋m⦌` acting on coordinates by
`(a_0, …, a_m) ↦ (a_{φ 0}, …, a_{φ n})`, so that the faces of `U` forget a coordinate and its
degeneracies repeat one; this is the Čech nerve of `f`, augmented over the constant simplicial set
`B` by the projection to the base. If `f` is surjective, that augmentation is a trivial Kan
fibration, i.e. has the right lifting property with respect to every boundary inclusion
`∂Δ[n] ⟶ Δ[n]`. Only injectivity on vertices of the boundary inclusion is used: a lift is a map
sending each vertex `v` of `Δ[n]` to a point of `A` over its image in `B`, prescribed already for
the vertices coming from `∂Δ[n]`, and such a map extends over the remaining vertices because `f`
is surjective; the adjunction `Augmented.toArrow ⊣ augmentedCechNerve` turns it into the lift.

### Main results

* `SSet.nonempty_homotopy_of_app_eq_of_isCoskeletal`: two maps into an `n`-coskeletal simplicial
  set agreeing in all degrees `< n` admit a simplicial homotopy from the first to the second.
* `SSet.hasLiftingProperty_augmentedCechNerve_hom`: the augmentation `U ⟶ B` of the Čech nerve of
  a surjection of sets has the right lifting property with respect to every morphism of simplicial
  sets which is injective on vertices, hence with respect to every monomorphism.
* `SSet.trivialKanFibrations_augmentedCechNerve_hom_of_surjective`: the augmentation `U ⟶ B` of
  the Čech nerve of a surjection of sets `f : A → B` is a trivial Kan fibration.

### Implementation notes

* Coskeletality is the class `SimplicialObject.IsCoskeletal U n` rather than
  `IsIso ((coskAdj n).unit.app U)`; for simplicial sets the two are equivalent by
  `SimplicialObject.isCoskeletal_iff_isIso`, all the right Kan extensions in question existing in
  `Type u`, and the class form needs no Kan-extension hypotheses to be spelled and can be supplied
  by instance resolution. The degree `n` is an explicit argument: it appears in no other explicit
  one, and in particular not in the conclusion.
* Hypothesis (3) of [Stacks, Tag 01A9], that `V ⟶ cosk_n sk_n V` is an isomorphism, is dropped,
  since neither of the source's proofs uses it. The source invokes it only to know that `V × Δ[1]`
  is `n`-coskeletal, hence that a morphism out of it may be prescribed on `n`-truncations; but that
  reduction is a statement about the *target*, restriction `Hom(X, U) ⟶ Hom(sk_n X, sk_n U)` being
  bijective for `n`-coskeletal `U` and arbitrary `X`. The rest of the source's second proof is
  likewise free of `V`: the compatibility check for the prescribed `h` needs only agreement below
  degree `n` together with the fact that a monotone `φ : ⦋k⦌ ⟶ ⦋n⦌` with `k ≤ n` which is not
  bijective factors through some `⦋m⦌` with `m < n`, so that `f₀ ∘ V(φ) = f₁ ∘ V(φ)`, and the
  identification of the two ends follows from injectivity of the same restriction map.
* The conclusion of the first lemma is a single homotopy from `f₀` to `f₁`, rather than the
  source's conclusion that `f₀` and `f₁` are homotopic, i.e. related by the equivalence relation
  that generates ([Stacks, Definition 019K], [Stacks, Remark 019M]); both of the source's proofs
  produce one, and the homotopy in the other direction follows by exchanging `f₀` and `f₁`, the
  hypotheses being symmetric. The homotopy is `SSet.Homotopy`, the datum of a morphism
  `h : V ⊗ Δ[1] ⟶ U` with `ι₀ ≫ h = f₀` and `ι₁ ≫ h = f₁`; the monoidal product of simplicial
  sets is the cartesian one, so this is verbatim the source's `h : V × Δ[1] → U` recovering `f^i`
  along `e_i`. Mathlib's `SimplicialObject.Homotopy` is instead the combinatorial description of
  [Stacks, Remark 019M], and the bridge `SSet.Homotopy.toSimplicialObjectHomotopy` runs only from
  the former to the latter, so the form stated here is the one that yields both.
* Agreement is stated on the components at the objects `⦋i⦌` with `i < n`. Every object of `Δ` is
  of this form, so this says that the two `(n - 1)`-truncations agree, which cannot be spelled
  uniformly in `n`; for `n = 0` it is vacuous, the case the source discusses before the lemma.
* The Čech nerve of [Stacks, Example 016E] is `CategoryTheory.Arrow.cechNerve`, whose degree `n`
  part is `widePullback B (fun _ : Fin (n + 1) ↦ A) fun _ ↦ f` and whose value on `φ` reindexes
  the coordinates along `φ`. An augmented simplicial object *is* a morphism to a constant one, so
  the source's `U ⟶ B` is the augmentation `(Arrow.mk f).augmentedCechNerve.hom`, whose component
  in degree `n` is the projection `WidePullback.base`. All wide pullbacks of sets exist, so the
  hypothesis of Example 016E that the fibre products exist is automatic and surjectivity is the
  only hypothesis; for a map of sets it is equivalent to being an epimorphism
  (`CategoryTheory.epi_iff_surjective`), and the source's word is the one kept.

### References

* [Stacks, Tag 01A9](https://stacks.math.columbia.edu/tag/01A9)
* [Stacks, Tag 01AB](https://stacks.math.columbia.edu/tag/01AB)
* [Stacks, Tag 019K](https://stacks.math.columbia.edu/tag/019K)
* [Stacks, Tag 019M](https://stacks.math.columbia.edu/tag/019M)
* [Stacks, Tag 016E](https://stacks.math.columbia.edu/tag/016E)
-/

section

@[expose] public section

universe u v

section Coskeletal

open CategoryTheory Opposite Simplicial MonoidalCategory SimplicialObject

namespace SSet

/-- A morphism of `SimplexCategory` which is not surjective factors through an object of strictly
smaller length: the target has positive length, every morphism to `⦋0⦌` being surjective, and
missing a vertex `i` of it, the morphism factors through the face opposite to `i`. -/
private lemma exists_comp_eq_of_not_surjective {Δ Δ' : SimplexCategory} (φ : Δ' ⟶ Δ)
    (hφ : ¬Function.Surjective φ.toOrderHom) :
    ∃ (Θ : SimplexCategory) (ψ : Δ' ⟶ Θ) (θ : Θ ⟶ Δ), Θ.len < Δ.len ∧ φ = ψ ≫ θ := by
  obtain ⟨m, rfl⟩ : ∃ m, Δ = ⦋m + 1⦌ := by
    rcases hlen : Δ.len with _ | m
    · have : Subsingleton (Fin (Δ.len + 1)) := by
        rw [hlen]
        exact Fin.subsingleton_one
      exact absurd (fun j ↦ ⟨0, Subsingleton.elim _ _⟩) hφ
    · exact ⟨m, by rw [← hlen, Δ.mk_len]⟩
  obtain ⟨i, ψ, rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective φ hφ
  exact ⟨⦋m⦌, ψ, SimplexCategory.δ i, by simp, rfl⟩

section

variable {V U : SSet.{u}} (f₀ f₁ : V ⟶ U)

/-- The prescription, in a single degree: a simplex `v` of `V` and an interval coordinate
`α : Δ ⟶ ⦋1⦌` go to `f₁(v)` if `α` is constant equal to `1`, and to `f₀(v)` otherwise. -/
private def homotopyApp (Δ : SimplexCategory) (v : V.obj (op Δ))
    (α : (Δ[1] : SSet.{u}).obj (op Δ)) : U.obj (op Δ) :=
  if ∀ k, (stdSimplex.objEquiv α).toOrderHom k = 1 then f₁.app (op Δ) v else f₀.app (op Δ) v

/-- The prescription on an interval coordinate constant equal to `1` is `f₁`. -/
private lemma homotopyApp_of_forall_eq_one {Δ : SimplexCategory} (v : V.obj (op Δ))
    {α : (Δ[1] : SSet.{u}).obj (op Δ)} (hα : ∀ k, (stdSimplex.objEquiv α).toOrderHom k = 1) :
    homotopyApp f₀ f₁ Δ v α = f₁.app (op Δ) v :=
  ite_eq_left hα

/-- The prescription on an interval coordinate constant equal to `0` is `f₀`. -/
private lemma homotopyApp_of_forall_eq_zero {Δ : SimplexCategory} (v : V.obj (op Δ))
    {α : (Δ[1] : SSet.{u}).obj (op Δ)} (hα : ∀ k, (stdSimplex.objEquiv α).toOrderHom k = 0) :
    homotopyApp f₀ f₁ Δ v α = f₀.app (op Δ) v :=
  ite_eq_right fun h1 ↦ absurd ((hα 0).symm.trans (h1 0)) (by decide)

end

/-- If `φ` is surjective, the pullback `α ∘ φ` of an interval coordinate is constant equal to `1`
exactly when `α` is; the interval coordinate of a pulled-back simplex is the composite, which is
`SSet.stdSimplex.map_apply` read through `SSet.stdSimplex.objEquiv`. -/
private lemma forall_eq_one_map_iff {Δ Δ' : SimplexCategory} {φ : Δ' ⟶ Δ}
    (hφ : Function.Surjective φ.toOrderHom) (α : (Δ[1] : SSet.{u}).obj (op Δ)) :
    (∀ k, (stdSimplex.objEquiv ((Δ[1] : SSet.{u}).map φ.op α)).toOrderHom k = 1) ↔
      ∀ j, (stdSimplex.objEquiv α).toOrderHom j = 1 := by
  rw [stdSimplex.map_apply, Equiv.apply_symm_apply]
  exact (hφ.forall (p := fun j ↦ (stdSimplex.objEquiv α).toOrderHom j = 1)).symm

section

variable {V U : SSet.{u}} {n : ℕ} {f₀ f₁ : V ⟶ U} (h : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌))

include h

/-- `f₀` and `f₁` agree on the image of `V(φ) : V_Δ ⟶ V_Δ'` for every `φ : Δ' ⟶ Δ` which is not
surjective, provided `Δ.len ≤ n`: such a `φ` factors through an object of length `< n`, where `f₀`
and `f₁` agree. This is the source's "`f₀(y) = f₁(y)` for a degenerate `n`-simplex `y`". -/
private lemma app_map_eq_of_not_surjective {Δ Δ' : SimplexCategory} (hΔ : Δ.len ≤ n) (φ : Δ' ⟶ Δ)
    (hφ : ¬Function.Surjective φ.toOrderHom) (v : V.obj (op Δ)) :
    f₀.app (op Δ') (V.map φ.op v) = f₁.app (op Δ') (V.map φ.op v) := by
  obtain ⟨Θ, ψ, θ, hΘ, rfl⟩ := exists_comp_eq_of_not_surjective φ hφ
  simp only [op_comp, Functor.map_comp_apply, NatTrans.naturality_apply,
    h Θ.len (hΘ.trans_le hΔ)]

/-- Naturality of the prescription in degrees `≤ n`: the source's compatibility check. Either `φ`
is surjective, and then `α ∘ φ` is constant equal to `1` exactly when `α` is, so both sides take
the same branch, or `φ` is not surjective, and then `f₀` and `f₁` agree on the image of `V(φ)`, so
both branches give the same value. -/
private lemma homotopyApp_map {Δ Δ' : SimplexCategory} (hΔ : Δ.len ≤ n) (φ : Δ' ⟶ Δ)
    (v : V.obj (op Δ)) (α : (Δ[1] : SSet.{u}).obj (op Δ)) :
    homotopyApp f₀ f₁ Δ' (V.map φ.op v) ((Δ[1] : SSet.{u}).map φ.op α) =
      U.map φ.op (homotopyApp f₀ f₁ Δ v α) := by
  by_cases hφ : Function.Surjective φ.toOrderHom
  · simp only [homotopyApp, forall_eq_one_map_iff hφ]
    split_ifs <;> simp only [NatTrans.naturality_apply]
  · have hcol := app_map_eq_of_not_surjective h hΔ φ hφ v
    simp only [homotopyApp, NatTrans.naturality_apply] at hcol ⊢
    split_ifs <;> simp only [hcol]

/-- The prescription as a morphism of `n`-truncated simplicial sets. -/
private def truncatedHomotopy :
    (SimplexCategory.Truncated.inclusion n).op ⋙ (V ⊗ Δ[1]) ⟶
      (SimplexCategory.Truncated.inclusion n).op ⋙ U
    where
  app t := ↾fun x ↦ homotopyApp f₀ f₁ (unop t).obj x.1 x.2
  naturality t _ g := by
    ext x
    exact homotopyApp_map h (unop t).property g.unop.hom x.1 x.2

variable [U.IsCoskeletal n]

/-- The homotopy `V ⊗ Δ[1] ⟶ U`, obtained from the truncated prescription by the universal
property of `U` as a right Kan extension of its `n`-truncation. -/
private noncomputable def homotopyHom : V ⊗ Δ[1] ⟶ U :=
  Functor.liftOfIsRightKanExtension U (𝟙 ((SimplexCategory.Truncated.inclusion n).op ⋙ U)) _
    (truncatedHomotopy h)

/-- In degrees `≤ n`, the homotopy is the prescription it was built from. -/
private lemma homotopyHom_app (t : (SimplexCategory.Truncated n)ᵒᵖ)
    (y : (V ⊗ Δ[1] : SSet.{u}).obj (op (unop t).obj)) :
    (homotopyHom h).app (op (unop t).obj) y = homotopyApp f₀ f₁ (unop t).obj y.1 y.2 := by
  have e :=
    Functor.liftOfIsRightKanExtension_fac_app U
      (𝟙 ((SimplexCategory.Truncated.inclusion n).op ⋙ U)) _ (truncatedHomotopy h) t
  simp only [NatTrans.id_app] at e
  exact ConcreteCategory.congr_hom e y

end

/-- **Two maps into an `n`-coskeletal simplicial set agreeing below degree `n` are homotopic,
[Stacks, Tag 01A9].** Let `f₀, f₁ : V ⟶ U` be maps of simplicial sets whose components
`V_i ⟶ U_i` agree for every `i < n`, and assume that the canonical morphism
`U ⟶ cosk_n sk_n U` is an isomorphism, i.e. that `U` is `n`-coskeletal. Then there is a
simplicial homotopy `V ⊗ Δ[1] ⟶ U` from `f₀` to `f₁`; in particular `f₀` and `f₁` are homotopic.
No hypothesis on `V` is needed. -/
@[stacks 01A9 "the conclusion is strengthened from `f⁰` and `f¹` being homotopic to the \
  existence of a homotopy from `f⁰` to `f¹`, which is what both of the source's proofs \
  produce; hypothesis (3) of the source, that `V ⟶ cosk_n sk_n V` is an isomorphism, is \
  dropped, since neither of the source's proofs uses it: maps into an `n`-coskeletal object \
  are exactly maps of their `n`-truncations, by `coskAdj n`, for an arbitrary source; \
  coskeletality of `U` is Mathlib's `IsCoskeletal`, equivalent to the source's \
  `U ⟶ cosk_n sk_n U` being an isomorphism", sga "4 Vbis 3.0.2.4" "simplicial sets"]
theorem nonempty_homotopy_of_app_eq_of_isCoskeletal {V U : SSet.{u}} (n : ℕ) [U.IsCoskeletal n]
    (f₀ f₁ : V ⟶ U) (h : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    Nonempty (Homotopy f₀ f₁) := by
  refine ⟨Homotopy.ofEnds (homotopyHom h) ?_ ?_⟩ <;>
    refine
      Functor.hom_ext_of_isRightKanExtension U (𝟙 ((SimplexCategory.Truncated.inclusion n).op ⋙ U))
        _ _ ?_ <;>
    ext t y
  · exact (homotopyHom_app h t _).trans (homotopyApp_of_forall_eq_zero f₀ f₁ y fun _ ↦ rfl)
  · exact (homotopyHom_app h t _).trans (homotopyApp_of_forall_eq_one f₀ f₁ y fun _ ↦ rfl)

end SSet

end Coskeletal

section CechNerve

open CategoryTheory Limits Opposite SimplicialObject
open scoped Simplicial

/-- A map into the target of a surjection extends a prescribed lift along an injection: if
`f : A → B` is surjective, `i : K → L` is injective and `u : K → A` lifts `b ∘ i`, then some
`t : L → A` lifts `b` and restricts to `u` along `i`. Mathlib has no such lemma; its home is
`Mathlib/Logic/Function/Basic.lean`, and it is kept private here rather than exported from a file
about simplicial homotopy. -/
private lemma Function.Surjective.exists_extend {A B K L : Type*} {f : A → B} {i : K → L}
    {b : L → B} {u : K → A} (hf : Function.Surjective f) (hi : Function.Injective i)
    (hu : ∀ x, f (u x) = b (i x)) : ∃ t : L → A, (∀ v, f (t v) = b v) ∧ ∀ x, t (i x) = u x := by
  refine ⟨Function.extend i u fun v ↦ (hf (b v)).choose, fun v ↦ ?_, fun x ↦ hi.extend_apply u _ x⟩
  by_cases hv : ∃ x, i x = v
  · obtain ⟨x, rfl⟩ := hv
    rw [hi.extend_apply, hu]
  · rw [Function.extend_apply' _ _ _ hv]
    exact (hf (b v)).choose_spec

namespace SSet

/-- Two morphisms from an augmented simplicial object to an augmented Čech nerve agree as soon as
they agree on the point of the augmentation and their degree `0` components agree after composing
with the projection to the first factor: by `SimplicialObject.cechNerveEquiv`, those two data are
exactly a morphism of arrows out of `SimplicialObject.Augmented.toArrow`. -/
private lemma augmentedCechNerve_hom_ext {C : Type u} [Category.{v} C]
    [∀ (n : ℕ) (f : Arrow C),
        HasWidePullback f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]
    {X : SimplicialObject.Augmented C} {F : Arrow C} (g h : X ⟶ F.augmentedCechNerve)
    (hleft : g.left.app (op ⦋0⦌) ≫ WidePullback.π _ 0 = h.left.app (op ⦋0⦌) ≫ WidePullback.π _ 0)
    (hright : g.right = h.right) : g = h :=
  (cechNerveEquiv X F).symm.injective (Arrow.hom_ext _ _ hleft hright)

/-- **The augmentation of the Čech nerve of a surjection of sets has the right lifting property
with respect to every morphism of simplicial sets injective on vertices, [Stacks, Tag 01AB].**
Monomorphisms of simplicial sets are injective in every degree, so the class of morphisms covered
contains every monomorphism, and in particular the boundary inclusions `∂Δ[n] ⟶ Δ[n]` against which
`trivialKanFibrations` asks for lifts. -/
@[stacks 01AB "the lifting property proved is against every map injective on vertices, hence \
  against every monomorphism of simplicial sets, not only the boundary inclusions"]
lemma hasLiftingProperty_augmentedCechNerve_hom (F : Arrow (Type u))
    (hF : Function.Surjective F.hom) {K L : SSet.{u}} {i : K ⟶ L}
    (hi : Function.Injective (i.app (op ⦋0⦌))) :
    HasLiftingProperty i F.augmentedCechNerve.hom := by
  constructor
  intro α β sq
  have hu :
    ∀ x,
      F.hom (WidePullback.π (fun _ ↦ F.hom) 0 (α.app (op ⦋0⦌) x)) =
        β.app (op ⦋0⦌) (i.app (op ⦋0⦌) x) :=
    fun x ↦ by
    have h₁ :=
      ConcreteCategory.congr_hom (WidePullback.π_arrow (fun _ ↦ F.hom) 0) (α.app (op ⦋0⦌) x)
    have h₂ := ConcreteCategory.congr_hom (congr_app sq.w (op ⦋0⦌)) x
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h₁ h₂
    exact h₁.trans h₂
  obtain ⟨t, ht, hti⟩ := hF.exists_extend hi hu
  let M : SimplicialObject.Augmented (Type u) := { left := L, right := F.right, hom := β }
  let N : SimplicialObject.Augmented (Type u) := { left := K, right := F.right, hom := i ≫ β }
  obtain ⟨G, hGl, hGr⟩ :
    ∃ G : Augmented.toArrow.obj M ⟶ F,
      CommaMorphism.left G = ↾t ∧ CommaMorphism.right G = 𝟙 F.right :=
    ⟨{ left := ↾t, right := 𝟙 F.right,
       w := by
         ext v
         exact ht v },
      rfl, rfl⟩
  obtain ⟨ν, hνl, hνr⟩ : ∃ ν : N ⟶ M, ν.left = i ∧ ν.right = 𝟙 F.right :=
    ⟨{ left := i, right := 𝟙 F.right, w := rfl }, rfl, rfl⟩
  obtain ⟨p, hpl, hpr⟩ : ∃ p : N ⟶ F.augmentedCechNerve, p.left = α ∧ p.right = 𝟙 F.right :=
    ⟨{ left := α, right := 𝟙 F.right, w := sq.w }, rfl, rfl⟩
  have hπ := congrArg CommaMorphism.left ((cechNerveEquiv M F).symm_apply_apply G)
  simp only [cechNerveEquiv_symm_apply, equivalenceRightToLeft_left] at hπ
  rw [hGl] at hπ
  have hright : (cechNerveEquiv M F G).right = 𝟙 F.right := hGr
  refine ⟨⟨⟨(cechNerveEquiv M F G).left, ?_, ?_⟩⟩⟩
  · have key :=
      augmentedCechNerve_hom_ext (ν ≫ cechNerveEquiv M F G) p ?_
        (by
          rw [hpr, Comma.comp_right, hνr, hright]
          rfl)
    · rw [← hpl, ← key, Comma.comp_left, hνl]
    · rw [Comma.comp_left, NatTrans.comp_app, hνl, hpl]
      ext x
      exact (ConcreteCategory.congr_hom hπ (i.app (op ⦋0⦌) x)).trans (hti x)
  · refine (cechNerveEquiv M F G).w.trans ?_
    rw [hright]
    rfl

/-- **The Čech nerve of a surjection of sets is a trivial Kan fibration, [Stacks, Tag 01AB].**
Let `f : A ⟶ B` be a surjective map of sets and let `U` be the simplicial set with
`U_n = A ×_B A ×_B ⋯ ×_B A` (`n + 1` factors), the Čech nerve of `f`. Then the augmentation of
`U` over the constant simplicial set with value `B`, given in degree `n` by the projection
`(a_0, …, a_n) ↦ f a_0` to the base, is a trivial Kan fibration. -/
@[stacks 01AB "the simplicial set of the source's Example 016E is the Čech nerve \
  `(Arrow.mk f).cechNerve`, and the source's morphism from it to the constant simplicial \
  set with value `B` is the augmentation `(Arrow.mk f).augmentedCechNerve.hom`"]
theorem trivialKanFibrations_augmentedCechNerve_hom_of_surjective {A B : Type u} {f : A ⟶ B}
    (hf : Function.Surjective f) : trivialKanFibrations (Arrow.mk f).augmentedCechNerve.hom := by
  rintro _ _ _ ⟨n⟩
  refine hasLiftingProperty_augmentedCechNerve_hom (Arrow.mk f) hf ?_
  rw [← mono_iff_injective]
  infer_instance

end SSet

end CechNerve

end

end
