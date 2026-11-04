module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalPushforwardRational
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GysinOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Coproduct
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Definition

/-!
# Splitting a disconnected smooth projective scheme

A nonempty smooth projective scheme `X` over a field `k` which is not connected is the disjoint
union `X = X₁ ⨿ X₂` of two nonempty open and closed subschemes, each with fewer connected
components than `X` (a smooth projective scheme has finitely many, being Noetherian). Such a
splitting is the induction step of arguments reducing statements about smooth projective schemes
to connected ones.

If `X` is equidimensional of dimension `d`, so are `X₁` and `X₂`, and the Chow groups decompose:
for `α ∈ CH^p(X)` with inclusions `ιᵢ : Xᵢ ⟶ X`,

  `α = ι₁_* ι₁^! α + ι₂_* ι₂^! α`

in `CH_*(X) ⊗ 𝐐`. Indeed the Gysin map of an open immersion is restriction (Stacks 0FF4), and a
class on `X` is the sum of the pushforwards of its restrictions to the pieces of a decomposition
into open and closed subschemes.

## Main results

* `Stacks.Topology.natCard_connectedComponents_lt_of_isClopen`: a clopen subset with nonempty
  complement has fewer connected components than the whole space.
* `Stacks.Chow.properChowPushforward_chowGroupRestrict_add`: a Chow class is the sum of the
  pushforwards of its restrictions to the two pieces of a decomposition into open and closed
  subschemes.
* `Stacks.WeilCohomology.finite_connectedComponents`: a smooth projective scheme over `k` has
  finitely many connected components.
* `Stacks.WeilCohomology.codimensionToRationalChow_eq_add_of_isOpenImmersion`: the decomposition
  of `CH^p(X) ⊗ 𝐐` along two open immersions with disjoint images covering `X`.
* `Stacks.WeilCohomology.exists_clopen_split`: a disconnected nonempty smooth projective scheme
  splits into two nonempty open and closed subschemes with fewer connected components, along
  which its Chow classes decompose rationally.

## References

* [Stacks Project, Tag 0FF4](https://stacks.math.columbia.edu/tag/0FF4)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
-/

@[expose] public noncomputable section

open CategoryTheory hiding ConnectedComponents
open AlgebraicGeometry Stacks.Chow
open scoped TensorProduct

universe u

namespace Stacks.Topology

/-- **A clopen set with nonempty complement has fewer connected components**: for a space with
finitely many connected components and a clopen `s` with `sᶜ` nonempty, `s` has fewer connected
components than the whole space, the components of the space being those of `s` and of `sᶜ`. -/
theorem natCard_connectedComponents_lt_of_isClopen {α : Type*} [TopologicalSpace α]
    [Finite (ConnectedComponents α)] {s : Set α} (hs : IsClopen s) (hs' : sᶜ.Nonempty) :
    Nat.card (ConnectedComponents s) < Nat.card (ConnectedComponents α) := by
  let U : Bool → Set α := fun b ↦ cond b s sᶜ
  have hclopen : ∀ b, IsClopen (U b) := by
    rintro (_ | _)
    exacts [hs.compl, hs]
  have hdisj : Pairwise (Function.onFun Disjoint U) := by
    rintro (_ | _) (_ | _) h
    exacts [(h rfl).elim, disjoint_compl_left, disjoint_compl_right, (h rfl).elim]
  have hunion : ⋃ b, U b = Set.univ := Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 (by
    by_cases hx : x ∈ s
    exacts [⟨true, hx⟩, ⟨false, hx⟩])
  let e := ConnectedComponents.equivOfIsClopen hclopen hdisj hunion
  have : Finite (Σ b, ConnectedComponents (U b)) := Finite.of_equiv _ e
  have : ∀ b, Finite (ConnectedComponents (U b)) := fun b ↦
    Finite.of_injective _ (@sigma_mk_injective Bool (fun b ↦ ConnectedComponents (U b)) b)
  obtain ⟨x, hx⟩ := hs'
  have : Nonempty (ConnectedComponents (U false)) := ⟨ConnectedComponents.mk ⟨x, hx⟩⟩
  rw [Nat.card_congr e, Nat.card_sigma, Fintype.sum_bool]
  exact Nat.lt_add_of_pos_right Nat.card_pos

/-- **A nonempty space which is not connected has a nontrivial clopen subset**: a clopen `s`
with `s` and `sᶜ` both nonempty. -/
theorem exists_isClopen_nonempty_compl_nonempty {α : Type*} [TopologicalSpace α] [Nonempty α]
    (h : ¬ ConnectedSpace α) : ∃ s : Set α, IsClopen s ∧ s.Nonempty ∧ sᶜ.Nonempty := by
  have : ¬ PreconnectedSpace α := fun hp ↦ h { toPreconnectedSpace := hp, toNonempty := ‹_› }
  rw [preconnectedSpace_iff_clopen] at this
  push Not at this
  obtain ⟨s, hs, hne, hnu⟩ := this
  exact ⟨s, hs, hne, Set.nonempty_compl.2 hnu⟩

end Stacks.Topology

namespace Stacks.Chow

/-- **A Chow class is the sum of the pushforwards of its restrictions to two complementary open
and closed pieces.** For open immersions `m₁ : A₁ ⟶ Z`, `m₂ : A₂ ⟶ Z` which are proper, with
disjoint images covering `Z`, and `α ∈ CH_k(Z)`, `α = m₁_*(α|_{A₁}) + m₂_*(α|_{A₂})`. -/
theorem properChowPushforward_chowGroupRestrict_add (C : ChowSituation.{u})
    {Z A₁ A₂ : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (s₁ : A₁ ⟶ C.S)
    [LocallyOfFiniteType s₁] (s₂ : A₂ ⟶ C.S) [LocallyOfFiniteType s₂] (m₁ : A₁ ⟶ Z)
    [IsOpenImmersion m₁] [IsProper m₁] (m₂ : A₂ ⟶ Z) [IsOpenImmersion m₂] [IsProper m₂]
    (hm₁ : m₁ ≫ sZ = s₁) (hm₂ : m₂ ≫ sZ = s₂) (hcover : ∀ z, z ∈ Set.range m₁ ∨ z ∈ Set.range m₂)
    (hdisj : Disjoint (Set.range m₁) (Set.range m₂)) (k : ℤ) (α : chowGroup C sZ k) :
    properChowPushforward C s₁ sZ m₁ hm₁ k (properPushforwardDescends C _ _ _ _ _)
        (chowGroupRestrict C sZ s₁ m₁ hm₁ k α) +
      properChowPushforward C s₂ sZ m₂ hm₂ k (properPushforwardDescends C _ _ _ _ _)
        (chowGroupRestrict C sZ s₂ m₂ hm₂ k α) = α := by
  let W : ULift.{u} Bool → Scheme.{u} := fun i ↦ cond i.down A₁ A₂
  let s : ∀ i, W i ⟶ C.S := fun
    | ⟨true⟩ => s₁
    | ⟨false⟩ => s₂
  let m : ∀ i, W i ⟶ Z := fun
    | ⟨true⟩ => m₁
    | ⟨false⟩ => m₂
  have : ∀ i, LocallyOfFiniteType (s i) := fun
    | ⟨true⟩ => ‹LocallyOfFiniteType s₁›
    | ⟨false⟩ => ‹LocallyOfFiniteType s₂›
  have : ∀ i, IsOpenImmersion (m i) := fun
    | ⟨true⟩ => ‹IsOpenImmersion m₁›
    | ⟨false⟩ => ‹IsOpenImmersion m₂›
  have hm : ∀ i, m i ≫ sZ = s i := fun
    | ⟨true⟩ => hm₁
    | ⟨false⟩ => hm₂
  have hdec : IsClopenDecomposition fun i ↦ (m i).opensRange := by
    refine isClopenDecomposition_of_isOpenImmersion_cover m (fun z ↦ ?_) ?_
    · rcases hcover z with h | h
      exacts [⟨⟨true⟩, h⟩, ⟨⟨false⟩, h⟩]
    · rintro ⟨_ | _⟩ ⟨_ | _⟩ h
      exacts [(h rfl).elim, hdisj.symm, hdisj, (h rfl).elim]
  rw [← sub_eq_zero]
  refine eq_zero_of_chowGroupRestrict_eq_zero C sZ s m hm hdec k _ ?_
  have h₁₂ := chowGroupRestrict_properChowPushforward_of_disjoint C sZ s₁ s₂ m₁ hm₁ m₂ hm₂ hdisj
  have h₂₁ := chowGroupRestrict_properChowPushforward_of_disjoint C sZ s₂ s₁ m₂ hm₂ m₁ hm₁
    hdisj.symm
  rintro ⟨_ | _⟩
  · show chowGroupRestrict C sZ s₂ m₂ hm₂ k _ = 0
    simp [chowGroupRestrict_properChowPushforward_self, h₁₂]
  · show chowGroupRestrict C sZ s₁ m₁ hm₁ k _ = 0
    simp [chowGroupRestrict_properChowPushforward_self, h₂₁]

end Stacks.Chow

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

/-- **A smooth projective scheme over `k` has finitely many connected components**, being
Noetherian. -/
instance finite_connectedComponents (X : (SmoothProjectiveScheme k).FullSubcategory) :
    Finite (ConnectedComponents X.obj.left) :=
  haveI := isNoetherian_of_compactSpace (C := fieldChowSituation k) X.obj.hom
  TopologicalSpace.NoetherianSpace.finite_connectedComponents X.obj.left

/-! ### Parts of constant dimension along an open immersion -/

section Parts

variable {X U : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX]
  (sU : U ⟶ (fieldChowSituation k).S) [Smooth sU] {j : U ⟶ X} [IsOpenImmersion j]
  (hj : j ≫ sX = sU)

/-- The map `U_d ⟶ X_d` induced by an open immersion `j : U ⟶ X` is `j` on points. -/
theorem dimPart_ι_dimPartMap_apply (d : ℕ) (x : (dimPart sU d).toScheme) :
    (dimPart sX d).ι (dimPartMap sX sU hj d x) = j ((dimPart sU d).ι x) := by
  rw [← Scheme.Hom.comp_apply, dimPartMap_ι, Scheme.Hom.comp_apply]

/-- If `U` has constant relative dimension `d`, every point of `X_d` in the image of `j` is in
the image of `U_d ⟶ X_d`. -/
theorem mem_range_dimPartMap {d : ℕ} (hU : RelativeDimension sU d) {z : (dimPart sX d).toScheme}
    (hz : (dimPart sX d).ι z ∈ Set.range j) : z ∈ Set.range (dimPartMap sX sU hj d) := by
  obtain ⟨x, hx⟩ := hz
  have hx' : x ∈ dimPart sU d := by
    rw [dimPart_self_eq_top sU hU]
    trivial
  refine ⟨(⟨x, hx'⟩ : (dimPart sU d).toScheme), (dimPart sX d).ι.isOpenEmbedding.injective ?_⟩
  exact (dimPart_ι_dimPartMap_apply sX sU hj d _).trans hx

/-- The map `U_d ⟶ X_d` induced by an open immersion `j : U ⟶ X` is proper when `j` is. -/
theorem isProper_dimPartMap [IsProper j] (d : ℕ) : IsProper (dimPartMap sX sU hj d) := by
  have := (isClopenDecomposition_dimPart sU).isProper_ι d
  have : IsProper (dimPartMap sX sU hj d ≫ (dimPart sX d).ι) := by
    rw [dimPartMap_ι]
    infer_instance
  exact IsProper.of_comp _ (dimPart sX d).ι

end Parts

/-- **For `X` equidimensional of dimension `d`, the class of `α ∈ CH^p(X)` in `CH_*(X) ⊗ 𝐐` is
the pushforward of its component `α_d` on `X_d`.** -/
theorem codimensionToRationalChow_eq_rationalIncludePart
    {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ} (hX : RelativeDimension X.obj.hom d)
    (p : ℤ) (α : codimensionChowGroup k X.obj.hom p) :
    codimensionToRationalChow k X.obj.hom p α =
      rationalIncludePart k X.obj.hom d
        (DirectSum.of
          (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) (partBase X.obj.hom d) j)
          ((d : ℤ) - p) ((1 : ℚ) ⊗ₜ[ℤ] α d)) := by
  rw [codimensionToRationalChow_apply]
  refine Finset.sum_eq_single d (fun d' _ hd' => ?_) (fun hd => ?_)
  · rw [codimensionChowGroup_apply_eq_zero_of_ne hX p α hd', TensorProduct.tmul_zero, map_zero,
      map_zero]
  · have : IsEmpty (dimPart X.obj.hom d).toScheme :=
      ⟨fun y => hd ((mem_nonemptyDimParts k X.obj.hom).2 ⟨y.1, y.2⟩)⟩
    have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k) (partBase X.obj.hom d)
      ((d : ℤ) - p)
    rw [Subsingleton.elim (α d) 0, TensorProduct.tmul_zero, map_zero, map_zero]

/-- Pushing a class forward from `U_d` to `U` and then along an open immersion `j : U ⟶ X` of
smooth projective schemes is pushing it forward along `U_d ⟶ X_d` and then to `X`. -/
theorem properChowPushforward_dimPart_ι_comp {X U : (SmoothProjectiveScheme k).FullSubcategory}
    (j : U ⟶ X) [IsOpenImmersion j.hom.left] (d : ℕ) (m : ℤ)
    (y : chowGroup (fieldChowSituation k) (partBase U.obj.hom d) m) :
    haveI := (isClopenDecomposition_dimPart U.obj.hom).isProper_ι d
    haveI := (isClopenDecomposition_dimPart X.obj.hom).isProper_ι d
    haveI := isProper_dimPartMap X.obj.hom U.obj.hom (Over.w j.hom) d
    properChowPushforward (fieldChowSituation k) U.obj.hom X.obj.hom j.hom.left (Over.w j.hom) m
        (properPushforwardDescends _ _ _ _ _ _)
        (properChowPushforward (fieldChowSituation k) (partBase U.obj.hom d) U.obj.hom
          (dimPart U.obj.hom d).ι rfl m (properPushforwardDescends _ _ _ _ _ _) y) =
      properChowPushforward (fieldChowSituation k) (partBase X.obj.hom d) X.obj.hom
        (dimPart X.obj.hom d).ι rfl m (properPushforwardDescends _ _ _ _ _ _)
        (properChowPushforward (fieldChowSituation k) (partBase U.obj.hom d)
          (partBase X.obj.hom d) (dimPartMap X.obj.hom U.obj.hom (Over.w j.hom) d)
          (dimPartMap_comp_partBase _ _ _ d) m (properPushforwardDescends _ _ _ _ _ _) y) := by
  have := (isClopenDecomposition_dimPart U.obj.hom).isProper_ι d
  have := (isClopenDecomposition_dimPart X.obj.hom).isProper_ι d
  have := isProper_dimPartMap X.obj.hom U.obj.hom (Over.w j.hom) d
  have hw : ((dimPart U.obj.hom d).ι ≫ j.hom.left) ≫ X.obj.hom = partBase U.obj.hom d := by
    rw [Category.assoc, Over.w j.hom]
  rw [← properChowPushforward_comp_apply (fieldChowSituation k) _ _ _ (dimPart U.obj.hom d).ι
      j.hom.left _ rfl rfl (Over.w j.hom) hw m (properPushforwardDescends _ _ _ _ _ _)
      (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _),
    ← properChowPushforward_comp_apply (fieldChowSituation k) _ _ _
      (dimPartMap X.obj.hom U.obj.hom (Over.w j.hom) d) (dimPart X.obj.hom d).ι _
      (dimPartMap_ι _ _ _ d) (dimPartMap_comp_partBase _ _ _ d) rfl hw m
      (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
      (properPushforwardDescends _ _ _ _ _ _)]

/-- **The decomposition of `CH^p(X) ⊗ 𝐐` along two open immersions with disjoint images covering
`X`.** For morphisms `ι₁ : X₁ ⟶ X`, `ι₂ : X₂ ⟶ X` of smooth projective schemes over `k`, all
equidimensional of dimension `d`, which are open immersions with disjoint images covering `X`,
and `α ∈ CH^p(X)`, the classes in `CH_*(X) ⊗ 𝐐` satisfy `α = ι₁_* ι₁^! α + ι₂_* ι₂^! α`. -/
theorem codimensionToRationalChow_eq_add_of_isOpenImmersion
    {X X₁ X₂ : (SmoothProjectiveScheme k).FullSubcategory} (ι₁ : X₁ ⟶ X) (ι₂ : X₂ ⟶ X)
    [IsOpenImmersion ι₁.hom.left] [IsOpenImmersion ι₂.hom.left]
    (hcover : ∀ x, x ∈ Set.range ι₁.hom.left ∨ x ∈ Set.range ι₂.hom.left)
    (hdisj : Disjoint (Set.range ι₁.hom.left) (Set.range ι₂.hom.left)) {d : ℕ}
    (hX : RelativeDimension X.obj.hom d) (hX₁ : RelativeDimension X₁.obj.hom d)
    (hX₂ : RelativeDimension X₂.obj.hom d) (p : ℤ) (α : codimensionChowGroup k X.obj.hom p) :
    codimensionToRationalChow k X.obj.hom p α =
      codimensionToRationalChow k X.obj.hom p
          (equidimensionalPushforward ι₁ d d p p (by omega)
            (codimensionGysin X₁.obj.hom X.obj.hom (Over.w ι₁.hom) p α)) +
        codimensionToRationalChow k X.obj.hom p
          (equidimensionalPushforward ι₂ d d p p (by omega)
            (codimensionGysin X₂.obj.hom X.obj.hom (Over.w ι₂.hom) p α)) := by
  have := (isClopenDecomposition_dimPart X.obj.hom).isProper_ι d
  have := (isClopenDecomposition_dimPart X₁.obj.hom).isProper_ι d
  have := (isClopenDecomposition_dimPart X₂.obj.hom).isProper_ι d
  have := isProper_dimPartMap X.obj.hom X₁.obj.hom (Over.w ι₁.hom) d
  have := isProper_dimPartMap X.obj.hom X₂.obj.hom (Over.w ι₂.hom) d
  rw [codimensionToRationalChow_equidimensionalPushforward ι₁ hX₁ hX,
    codimensionToRationalChow_equidimensionalPushforward ι₂ hX₂ hX,
    codimensionToRationalChow_eq_rationalIncludePart hX₁,
    codimensionToRationalChow_eq_rationalIncludePart hX₂,
    codimensionToRationalChow_eq_rationalIncludePart hX]
  simp only [rationalProperChowPushforward_of_tmul]
  rw [codimensionGysin_of_isOpenImmersion X.obj.hom X₁.obj.hom (Over.w ι₁.hom) p α d,
    codimensionGysin_of_isOpenImmersion X.obj.hom X₂.obj.hom (Over.w ι₂.hom) p α d,
    properChowPushforward_dimPart_ι_comp ι₁, properChowPushforward_dimPart_ι_comp ι₂,
    ← map_add, ← TensorProduct.tmul_add, ← map_add]
  have hcover' : ∀ z, z ∈ Set.range (dimPartMap X.obj.hom X₁.obj.hom (Over.w ι₁.hom) d) ∨
      z ∈ Set.range (dimPartMap X.obj.hom X₂.obj.hom (Over.w ι₂.hom) d) := fun z ↦
    (hcover ((dimPart X.obj.hom d).ι z)).imp (mem_range_dimPartMap _ _ _ hX₁)
      (mem_range_dimPartMap _ _ _ hX₂)
  have hdisj' : Disjoint (Set.range (dimPartMap X.obj.hom X₁.obj.hom (Over.w ι₁.hom) d))
      (Set.range (dimPartMap X.obj.hom X₂.obj.hom (Over.w ι₂.hom) d)) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    exact Set.disjoint_left.1 hdisj ⟨(dimPart X₁.obj.hom d).ι a,
      (dimPart_ι_dimPartMap_apply _ _ _ d a).symm⟩ ⟨(dimPart X₂.obj.hom d).ι b,
      (dimPart_ι_dimPartMap_apply _ _ _ d b).symm.trans (congrArg _ hb)⟩
  rw [properChowPushforward_chowGroupRestrict_add (fieldChowSituation k) (partBase X.obj.hom d)
    _ _ _ _ _ _ hcover' hdisj']

/-- **A disconnected smooth projective scheme splits into two clopen pieces.** A nonempty smooth
projective scheme `X` over `k` which is not connected is the disjoint union of two nonempty open
and closed subschemes `X₁`, `X₂`, with inclusions `ι₁`, `ι₂` which are open and closed
immersions, each with fewer connected components than `X`. If `X` is equidimensional of
dimension `d`, so are `X₁` and `X₂`, and every `α ∈ CH^p(X)` has class
`ι₁_* ι₁^! α + ι₂_* ι₂^! α` in `CH_*(X) ⊗ 𝐐`. -/
theorem exists_clopen_split {X : (SmoothProjectiveScheme k).FullSubcategory} [Nonempty X.obj.left]
    (hX : ¬ ConnectedSpace X.obj.left) :
    ∃ (X₁ X₂ : (SmoothProjectiveScheme k).FullSubcategory) (ι₁ : X₁ ⟶ X) (ι₂ : X₂ ⟶ X),
      IsClosedImmersion ι₁.hom.left ∧ IsClosedImmersion ι₂.hom.left ∧
      IsOpenImmersion ι₁.hom.left ∧ IsOpenImmersion ι₂.hom.left ∧
      Nonempty X₁.obj.left ∧ Nonempty X₂.obj.left ∧
      Nat.card (ConnectedComponents X₁.obj.left) <
        Nat.card (ConnectedComponents X.obj.left) ∧
      Nat.card (ConnectedComponents X₂.obj.left) <
        Nat.card (ConnectedComponents X.obj.left) ∧
      ∀ (d : ℕ), RelativeDimension X.obj.hom d →
        RelativeDimension X₁.obj.hom d ∧ RelativeDimension X₂.obj.hom d ∧
        ∀ (p : ℤ) (α : codimensionChowGroup k X.obj.hom p),
          codimensionToRationalChow k X.obj.hom p α =
            codimensionToRationalChow k X.obj.hom p
              (equidimensionalPushforward ι₁ d d p p (by omega)
                (codimensionGysin X₁.obj.hom X.obj.hom (Over.w ι₁.hom) p α)) +
            codimensionToRationalChow k X.obj.hom p
              (equidimensionalPushforward ι₂ d d p p (by omega)
                (codimensionGysin X₂.obj.hom X.obj.hom (Over.w ι₂.hom) p α)) := by
  obtain ⟨s, hs, ⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩ := Topology.exists_isClopen_nonempty_compl_nonempty hX
  let U₁ : X.obj.left.Opens := ⟨s, hs.isOpen⟩
  let U₂ : X.obj.left.Opens := ⟨sᶜ, hs.compl.isOpen⟩
  have hU₁ : IsClopen (U₁ : Set X.obj.left) := hs
  have hU₂ : IsClopen (U₂ : Set X.obj.left) := hs.compl
  let ι₁ : SmoothProjectiveScheme.clopen X U₁ hU₁ ⟶ X := SmoothProjectiveScheme.homMk U₁.ι rfl
  let ι₂ : SmoothProjectiveScheme.clopen X U₂ hU₂ ⟶ X := SmoothProjectiveScheme.homMk U₂.ι rfl
  have : IsOpenImmersion ι₁.hom.left := inferInstanceAs (IsOpenImmersion U₁.ι)
  have : IsOpenImmersion ι₂.hom.left := inferInstanceAs (IsOpenImmersion U₂.ι)
  have hcover : ∀ x, x ∈ Set.range ι₁.hom.left ∨ x ∈ Set.range ι₂.hom.left := by
    intro x
    show x ∈ Set.range U₁.ι ∨ x ∈ Set.range U₂.ι
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact em (x ∈ s)
  have hdisj : Disjoint (Set.range ι₁.hom.left) (Set.range ι₂.hom.left) := by
    show Disjoint (Set.range U₁.ι) (Set.range U₂.ι)
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact disjoint_compl_right
  refine ⟨_, _, ι₁, ι₂, SmoothProjectiveScheme.isClosedImmersion_ι hU₁,
    SmoothProjectiveScheme.isClosedImmersion_ι hU₂, inferInstance, inferInstance,
    ⟨⟨x₁, hx₁⟩⟩, ⟨⟨x₂, hx₂⟩⟩,
    Topology.natCard_connectedComponents_lt_of_isClopen (α := X.obj.left) hs ⟨x₂, hx₂⟩,
    Topology.natCard_connectedComponents_lt_of_isClopen (α := X.obj.left) hs.compl
      ⟨x₁, fun h ↦ h hx₁⟩,
    fun d hd ↦ ?_⟩
  have h₁ : RelativeDimension (SmoothProjectiveScheme.clopen X U₁ hU₁).obj.hom d :=
    RelativeDimension.comp_isOpenImmersion U₁.ι X.obj.hom hd
  have h₂ : RelativeDimension (SmoothProjectiveScheme.clopen X U₂ hU₂).obj.hom d :=
    RelativeDimension.comp_isOpenImmersion U₂.ι X.obj.hom hd
  exact ⟨h₁, h₂, codimensionToRationalChow_eq_add_of_isOpenImmersion ι₁ ι₂ hcover hdisj hd h₁ h₂⟩

end Stacks.WeilCohomology

end
