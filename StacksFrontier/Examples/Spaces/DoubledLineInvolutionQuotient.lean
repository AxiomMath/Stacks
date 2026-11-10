module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeActionQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActionRelationSummands
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineRelationRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafDescent
public import StacksFrontier.Examples.Spaces.DoubledLineEtaleCovering
public import StacksFrontier.Examples.Spaces.NonSeparatedGroupSpace

/-!
# The involution quotient as the quotient of the doubled line by `\{±1\}`

Stacks 05ZI, after building the doubled-origin covering `Y ⟶ X` of the algebraic space
`X = 𝐀¹_k/\{x ∼ -x ∣ x ≠ 0\}`, gives a second, simpler argument: the scheme `Y` has a free action
of the group `G = \{+1, -1\}`, where `-1` swaps the two charts `Y₁, Y₂` and negates the
coordinate, and `X = Y/G` in the sense of Spaces, Definition 02Z3.

This file proves this. The group is `ℤˣ`, which is literally `\{+1, -1\}`.

## Main definitions

* `AlgebraicGeometry.AffineLineInvolution.doubledLineInvolution`: the involution of `Y`, as a
  morphism of the big fppf site. It carries the `b`-th chart to the other chart after negating
  the coordinate.
* `AlgebraicGeometry.AffineLineInvolution.doubledLineAction`: the action of `ℤˣ` on `Y` it
  generates.

## Main results

* `AlgebraicGeometry.AffineLineInvolution.actsNontriviallyOnFixedResidueFields_doubledLineAction`:
  the action is free in the sense of condition `(*)` of Stacks 02Z2.
* `AlgebraicGeometry.AffineLineInvolution.exists_iso_actionQuotient_doubledLineAction`: the
  involution quotient `X` is isomorphic to the quotient `Y/G` of Stacks 02Z3, by an isomorphism
  carrying the covering `Y ⟶ X` to the projection `Y ⟶ Y/G`.
* `AlgebraicGeometry.AffineLineInvolution.doubledLine_freeAction_quotient`: **Stacks 05ZI**, the
  remark's alternative construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Examples Stacks.Examples.AffineOverAlgebraicSpace

universe u

namespace AlgebraicGeometry.AffineLineInvolution

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))

/-! ### The involution of the doubled line -/

/-- The prescription of the involution on the `b`-th chart of the doubled line: negate the
coordinate and land in the other chart. -/
noncomputable def involutionChartMap (b : Bool) :
    yoneda.obj (affineLineChart k B hk) ⟶ yoneda.obj (doubledLineSite k B hk) :=
  yoneda.map (chartNeg k B hk ≫ doubledChartHom k B hk (!b))

/-- The prescriptions of the involution on the two charts agree on every common refinement of
the charts: on the overlap, which is the punctured line, the two charts agree, and negation
preserves the punctured line. -/
theorem involutionChartMap_compatible (b c : Bool)
    (Z : BigFppfOver B (Spec (.of k)) hk) (s : Z ⟶ affineLineChart k B hk)
    (t : Z ⟶ affineLineChart k B hk)
    (h : s ≫ doubledChartHom k B hk b = t ≫ doubledChartHom k B hk c) :
    yoneda.map s ≫ involutionChartMap k B hk b = yoneda.map t ≫ involutionChartMap k B hk c := by
  simp only [involutionChartMap, ← Functor.map_comp]
  congr 1
  by_cases hbc : b = c
  · subst hbc
    rw [(cancel_mono (doubledChartHom k B hk b)).mp h]
  · obtain ⟨hst, q, hq⟩ := eq_and_exists_punctured_factor k B hk hbc s t h
    subst hst
    rw [← hq, Category.assoc, Category.assoc, ← Category.assoc (puncturedChartInclusion k B hk),
      ← Category.assoc (puncturedChartInclusion k B hk), ← puncturedChartNeg_eq_comp]
    congr 1
    have h' := puncturedChartNeg_comp_doubledChartHom k B hk
    cases b <;> cases c
    · exact absurd rfl hbc
    · exact h'
    · exact h'.symm
    · exact absurd rfl hbc

/-- The involution of the doubled line, glued from its prescriptions on the two charts. -/
noncomputable def doubledLineInvolution : doubledLineSite k B hk ⟶ doubledLineSite k B hk :=
  yoneda.preimage (Space.exists_glue_of_mem_topology (BigFppfOver.topology B (Spec (.of k)) hk)
    (BigFppfOver.isSheaf_yoneda_obj B (Spec (.of k)) hk (doubledLineSite k B hk))
    (fun _ : Bool => affineLineChart k B hk) (doubledChartHom k B hk)
    (ofArrows_doubledChartHom_mem_topology k B hk) (involutionChartMap k B hk)
    (involutionChartMap_compatible k B hk)).choose

/-- **The involution swaps the two charts of the doubled line and negates the coordinate.** -/
theorem doubledChartHom_comp_doubledLineInvolution (b : Bool) :
    doubledChartHom k B hk b ≫ doubledLineInvolution k B hk =
      chartNeg k B hk ≫ doubledChartHom k B hk (!b) := by
  refine yoneda.map_injective ?_
  rw [Functor.map_comp, doubledLineInvolution, Functor.map_preimage]
  exact (Space.exists_glue_of_mem_topology (BigFppfOver.topology B (Spec (.of k)) hk)
    (BigFppfOver.isSheaf_yoneda_obj B (Spec (.of k)) hk (doubledLineSite k B hk))
    (fun _ : Bool => affineLineChart k B hk) (doubledChartHom k B hk)
    (ofArrows_doubledChartHom_mem_topology k B hk) (involutionChartMap k B hk)
    (involutionChartMap_compatible k B hk)).choose_spec b

/-- Two transformations from a representable presheaf to a sheaf are equal when they agree
along every arrow of a covering family. -/
private theorem hom_ext_of_ofArrows_mem_topology {C : Type*} [Category.{u} C]
    {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf J F) {W : C}
    {ι : Type*} {Y : ι → C} (f : ∀ i, Y i ⟶ W) (hR : Sieve.ofArrows Y f ∈ J W)
    {c d : yoneda.obj W ⟶ F} (h : ∀ i, yoneda.map (f i) ≫ c = yoneda.map (f i) ≫ d) : c = d := by
  refine Space.hom_ext_of_mem_topology J hF _ hR fun {Z} e he => ?_
  obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ e).1 he
  rw [Functor.map_comp, Category.assoc, Category.assoc, h i]

/-- Two morphisms out of the doubled line into a sheaf agree when they agree on both charts. -/
theorem doubledLine_hom_ext {F : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B (Spec (.of k)) hk) F)
    {f g : yoneda.obj (doubledLineSite k B hk) ⟶ F}
    (h : ∀ b, yoneda.map (doubledChartHom k B hk b) ≫ f =
      yoneda.map (doubledChartHom k B hk b) ≫ g) : f = g := by
  exact hom_ext_of_ofArrows_mem_topology hF _ (ofArrows_doubledChartHom_mem_topology k B hk) h

/-- **The involution of the doubled line is an involution.** -/
theorem doubledLineInvolution_comp_self :
    doubledLineInvolution k B hk ≫ doubledLineInvolution k B hk = 𝟙 _ := by
  refine yoneda.map_injective (doubledLine_hom_ext k B hk
    (BigFppfOver.isSheaf_yoneda_obj B (Spec (.of k)) hk (doubledLineSite k B hk)) fun b => ?_)
  rw [← Functor.map_comp, ← Functor.map_comp, ← Category.assoc,
    doubledChartHom_comp_doubledLineInvolution, Category.assoc,
    doubledChartHom_comp_doubledLineInvolution, ← Category.assoc, chartNeg_comp_chartNeg,
    Category.id_comp, Bool.not_not, Category.comp_id]

/-- The involution of the doubled line, as an automorphism. -/
noncomputable def doubledLineInvolutionIso : doubledLineSite k B hk ≅ doubledLineSite k B hk :=
  ⟨doubledLineInvolution k B hk, doubledLineInvolution k B hk,
    doubledLineInvolution_comp_self k B hk, doubledLineInvolution_comp_self k B hk⟩

/-- The involution of the doubled line, as an automorphism of the underlying scheme over the
ground field. -/
noncomputable def involutionAut : Aut (Space.underlyingOver B hk (doubledLineSite k B hk)) :=
  .of ((Over.post B.inclusion).mapIso (doubledLineInvolutionIso k B hk))

/-- The automorphism `involutionAut` squares to the identity. -/
theorem involutionAut_mul_self : involutionAut k B hk * involutionAut k B hk = 1 := by
  ext1
  rw [Aut.mul_asIso, Aut.one_asIso]
  ext1
  change (Over.post B.inclusion).map (doubledLineInvolution k B hk) ≫
      (Over.post B.inclusion).map (doubledLineInvolution k B hk) = 𝟙 _
  rw [← Functor.map_comp, doubledLineInvolution_comp_self, CategoryTheory.Functor.map_id]

/-- **The action of `G = \{+1, -1\} = ℤˣ` on the doubled line**: `-1` acts by the involution
which swaps the two charts and negates the coordinate. -/
noncomputable def doubledLineAction :
    ℤˣ →* Aut (Space.underlyingOver B hk (doubledLineSite k B hk)) where
  toFun u := if u = 1 then 1 else involutionAut k B hk
  map_one' := ite_eq_left rfl
  map_mul' u v := by
    have hsq := involutionAut_mul_self k B hk
    have hm : (-1 : ℤˣ) ≠ 1 := by decide
    rcases Int.units_eq_one_or u with rfl | rfl <;>
      rcases Int.units_eq_one_or v with rfl | rfl
    · simp only [mul_one]; exact (mul_one _).symm
    · simp only [one_mul, ite_eq_right hm]; exact (one_mul _).symm
    · simp only [mul_one, ite_eq_right hm]; exact (mul_one _).symm
    · simp only [ite_eq_right hm, show (-1 : ℤˣ) * -1 = 1 by decide]; exact hsq.symm

/-- The element `-1` acts on the doubled line by the involution. -/
theorem doubledLineAction_neg_one :
    (doubledLineAction k B hk (-1)).asIso.hom =
      (Over.post B.inclusion).map (doubledLineInvolution k B hk) := by
  have h : doubledLineAction k B hk (-1) = involutionAut k B hk :=
    show (if (-1 : ℤˣ) = 1 then 1 else involutionAut k B hk) = _ from ite_eq_right (by decide)
  rw [h]
  rfl

/-! ### The action is free -/

/-- The involution of the doubled line, as an endomorphism of its underlying scheme. -/
noncomputable abbrev involutionLeft : (doubledLine k).left ⟶ (doubledLine k).left :=
  (BigFppfOver.toScheme B (Spec (.of k)) hk).map (doubledLineInvolution k B hk)

/-- The involution of the doubled line, read on the underlying schemes: the `b`-th chart is
carried to the other chart after negating the coordinate. -/
theorem chart_comp_involutionLeft (b : Bool) :
    (doubledLineData k).chart b ≫ involutionLeft k B hk =
      (affineLineNeg k).left ≫ (doubledLineData k).chart (!b) := by
  have h := congrArg (BigFppfOver.toScheme B (Spec (.of k)) hk).map
    (doubledChartHom_comp_doubledLineInvolution k B hk b)
  simp only [Functor.map_comp, toScheme_map_doubledChartHom, toScheme_map_chartNeg] at h
  exact h

/-- **No point of the doubled line over a nonempty scheme is fixed by the involution.** Locally
the point lies in one chart `b`; the involution sends it to the other chart after negating the
coordinate, so the two charts would agree on it, and hence it would lie in the punctured line
and equal its own negative there. Away from characteristic two that forces the scheme to be
empty. -/
theorem isEmpty_of_comp_involutionLeft_eq (hchar : (2 : k) ≠ 0) {T : Scheme.{u}}
    (p : T ⟶ Spec (.of k)) (φ : T ⟶ (doubledLine k).left)
    (h : φ ≫ involutionLeft k B hk = φ) : IsEmpty T := by
  refine ⟨fun t => ?_⟩
  obtain ⟨b, y, hy⟩ := (doubledLineData k).exists_chart_eq (φ t)
  have hoi : IsOpenImmersion ((doubledLineData k).chart b) :=
    (doubledLineData k).isOpenImmersion_chart b
  let U : T.Opens := φ ⁻¹ᵁ ((doubledLineData k).chart b).opensRange
  have ht : t ∈ U := ⟨y, hy⟩
  have hrange : Set.range (U.ι ≫ φ) ⊆ Set.range ((doubledLineData k).chart b) := by
    rintro _ ⟨u, rfl⟩
    exact u.2
  let c : (U : Scheme.{u}) ⟶ (affineLine k).left :=
    IsOpenImmersion.lift ((doubledLineData k).chart b) (U.ι ≫ φ) hrange
  have hc : c ≫ (doubledLineData k).chart b = U.ι ≫ φ := IsOpenImmersion.lift_fac _ _ _
  have hsq : c ≫ (doubledLineData k).chart b =
      (c ≫ (affineLineNeg k).left) ≫ (doubledLineData k).chart (!b) := by
    rw [Category.assoc, ← chart_comp_involutionLeft k B hk, ← Category.assoc, hc,
      Category.assoc, h]
  have P := isPullback_doubledLineChart k (show b ≠ !b by cases b <;> decide)
  have hempty := isEmpty_of_comp_puncturedAffineLineOpen_ι_eq k hchar (U.ι ≫ p)
    (P.lift c (c ≫ (affineLineNeg k).left) hsq)
    (by rw [P.lift_snd, ← Category.assoc, P.lift_fst])
  exact hempty.false ⟨t, ht⟩

/-- The element `1` acts on the doubled line by the identity. -/
theorem doubledLineAction_one : (doubledLineAction k B hk 1).asIso.hom = 𝟙 _ := by
  rw [map_one]
  rfl

/-- **Stacks 02Z3: the action of `\{±1\}` on the doubled line is free**, in the sense of
condition `(*)` of Stacks 02Z2. No point over a nonempty scheme is fixed by the involution, by
`isEmpty_of_comp_involutionLeft_eq`. -/
theorem actsNontriviallyOnFixedResidueFields_doubledLineAction (hchar : (2 : k) ≠ 0) :
    Space.ActsNontriviallyOnFixedResidueFields
      (Space.underlyingOver B hk (doubledLineSite k B hk)) ℤˣ (doubledLineAction k B hk) := by
  refine Space.actsNontriviallyOnFixedResidueFields_of_actsFreelyOnNonemptyPoints _ _ _ ?_
  intro T hT x g g' hgg'
  by_contra hne
  have h1 := doubledLineAction_one k B hk
  have hfix : x ≫ (doubledLineAction k B hk (-1)).asIso.hom = x := by
    rcases Int.units_eq_one_or g with rfl | rfl <;>
      rcases Int.units_eq_one_or g' with rfl | rfl
    · exact absurd rfl hne
    · rw [h1, Category.comp_id] at hgg'
      exact hgg'.symm
    · rw [h1, Category.comp_id] at hgg'
      exact hgg'
    · exact absurd rfl hne
  rw [doubledLineAction_neg_one] at hfix
  obtain ⟨t⟩ := hT
  exact (isEmpty_of_comp_involutionLeft_eq k B hk hchar T.hom x.left
    (congrArg Over.Hom.left hfix)).false t

/-! ### The quotient `Y/G` is the involution quotient `X` -/

section Quotient

variable (hchar : (2 : k) ≠ 0)

include hchar in
/-- The scheme of arrows of the graph relation of the action of `\{±1\}` on the doubled line
lies in the site. -/
theorem contains_doubledLineActionRelationScheme :
    B.Contains (Space.actionRelationScheme
      (Space.underlyingOver B hk (doubledLineSite k B hk)) ℤˣ).left :=
  Space.contains_actionRelationScheme ℤˣ B hk (doubledLineSite k B hk)
    (doubledLineAction k B hk) (actsNontriviallyOnFixedResidueFields_doubledLineAction k B hk hchar)

/-- The summand of the graph relation indexed by a group element. -/
noncomputable abbrev relationSummand (g : ℤˣ) :
    doubledLineSite k B hk ⟶ Space.siteActionRelationScheme ℤˣ B hk (doubledLineSite k B hk)
      (contains_doubledLineActionRelationScheme k B hk hchar) :=
  Space.siteActionRelationInclusion ℤˣ B hk (doubledLineSite k B hk)
    (contains_doubledLineActionRelationScheme k B hk hchar) g

/-- Each summand of the graph relation, followed by the source map, is the identity. -/
theorem relationSummand_comp_source (g : ℤˣ) :
    relationSummand k B hk hchar g ≫ Space.siteActionRelationSource ℤˣ B hk
      (doubledLineSite k B hk) (contains_doubledLineActionRelationScheme k B hk hchar) = 𝟙 _ :=
  Space.siteActionRelationInclusion_comp_source ℤˣ B hk (doubledLineSite k B hk) _ g

/-- The summand of the graph relation indexed by `-1`, followed by the target map, is the
involution of the doubled line. -/
theorem relationSummand_neg_one_comp_target :
    relationSummand k B hk hchar (-1) ≫ Space.siteActionRelationTarget ℤˣ B hk
      (doubledLineSite k B hk) (contains_doubledLineActionRelationScheme k B hk hchar)
        (doubledLineAction k B hk) = doubledLineInvolution k B hk := by
  refine BigFppfOver.map_toScheme_injective B (Spec (.of k)) hk ?_
  refine (Space.toScheme_map_siteActionRelationInclusion_comp_target ℤˣ B hk
    (doubledLineSite k B hk) _ (doubledLineAction k B hk) (-1)).trans ?_
  rw [doubledLineAction_neg_one]
  rfl

/-- The summand of the graph relation indexed by `1`, followed by the target map, is `𝟙`. -/
theorem relationSummand_one_comp_target :
    relationSummand k B hk hchar 1 ≫ Space.siteActionRelationTarget ℤˣ B hk
      (doubledLineSite k B hk) (contains_doubledLineActionRelationScheme k B hk hchar)
        (doubledLineAction k B hk) = 𝟙 _ := by
  refine BigFppfOver.map_toScheme_injective B (Spec (.of k)) hk ?_
  refine (Space.toScheme_map_siteActionRelationInclusion_comp_target ℤˣ B hk
    (doubledLineSite k B hk) _ (doubledLineAction k B hk) 1).trans ?_
  rw [doubledLineAction_one]
  exact ((BigFppfOver.toScheme B (Spec (.of k)) hk).map_id _).symm

/-- A morphism out of the doubled line which coequalizes the two maps of the graph relation is
invariant under the involution. -/
theorem yoneda_involution_comp_of_coequalizes {P : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (κ : yoneda.obj (doubledLineSite k B hk) ⟶ P)
    (h : yoneda.map (Space.siteActionRelationSource ℤˣ B hk (doubledLineSite k B hk)
        (contains_doubledLineActionRelationScheme k B hk hchar)) ≫ κ =
      yoneda.map (Space.siteActionRelationTarget ℤˣ B hk (doubledLineSite k B hk)
        (contains_doubledLineActionRelationScheme k B hk hchar) (doubledLineAction k B hk)) ≫ κ) :
    yoneda.map (doubledLineInvolution k B hk) ≫ κ = κ := by
  have h' := congrArg (yoneda.map (relationSummand k B hk hchar (-1)) ≫ ·) h
  simp only [← Category.assoc, ← Functor.map_comp, relationSummand_comp_source,
    relationSummand_neg_one_comp_target, CategoryTheory.Functor.map_id, Category.id_comp] at h'
  exact h'.symm

/-- A morphism out of the doubled line invariant under the involution takes the same value on
the first chart as on the second chart precomposed with the negation. -/
private theorem yoneda_chartNeg_comp_doubledChartHom_comp_of_invariant (b : Bool)
    {P : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u} (κ : yoneda.obj (doubledLineSite k B hk) ⟶ P)
    (hκ : yoneda.map (doubledLineInvolution k B hk) ≫ κ = κ) :
    yoneda.map (chartNeg k B hk ≫ doubledChartHom k B hk (!b)) ≫ κ =
      yoneda.map (doubledChartHom k B hk b) ≫ κ := by
  rw [← doubledChartHom_comp_doubledLineInvolution, Functor.map_comp, Category.assoc, hκ]

variable [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)]

omit hchar in
/-- **The covering `Y ⟶ X` is invariant under the involution.** -/
theorem yoneda_involution_comp_coveringMorphism :
    yoneda.map (doubledLineInvolution k B hk) ≫ coveringMorphism k B hk =
      coveringMorphism k B hk := by
  refine doubledLine_hom_ext k B hk (involutionQuotient k B hk).property fun b => ?_
  rw [← Category.assoc, ← Functor.map_comp, doubledChartHom_comp_doubledLineInvolution,
    Functor.map_comp, Category.assoc, doubledChartHom_comp_coveringMorphism,
    doubledChartHom_comp_coveringMorphism, doubledChartQuotientMap_eq,
    doubledChartQuotientMap_eq, ← Category.assoc, ← Functor.map_comp]
  congr 2
  cases b
  · exact chartNeg_comp_chartNeg k B hk
  · exact Category.comp_id _

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- The summands of the graph relation cover its scheme of arrows. -/
theorem ofArrows_relationSummand_mem_topology :
    Sieve.ofArrows (fun _ : ℤˣ => doubledLineSite k B hk) (relationSummand k B hk hchar) ∈
      BigFppfOver.topology B (Spec (.of k)) hk
        (Space.siteActionRelationScheme ℤˣ B hk (doubledLineSite k B hk)
          (contains_doubledLineActionRelationScheme k B hk hchar)) := by
  apply Stacks.Examples.NonSeparatedGroupSpace.coproduct_sieve_mem B (Spec (.of k)) hk _ _ _
    (PreservesCoproduct.iso (Over.forget (Spec (.of k)))
      (fun _ : ℤˣ => Space.underlyingOver B hk (doubledLineSite k B hk))).symm
  intro g
  change Sigma.ι (fun _ : ℤˣ => (Space.underlyingOver B hk (doubledLineSite k B hk)).left) g ≫
      (PreservesCoproduct.iso (Over.forget (Spec (.of k)))
        (fun _ : ℤˣ => Space.underlyingOver B hk (doubledLineSite k B hk))).inv =
    (Sigma.ι (fun _ : ℤˣ => Space.underlyingOver B hk (doubledLineSite k B hk)) g).left
  rw [PreservesCoproduct.inv_hom]
  exact ι_comp_sigmaComparison (Over.forget (Spec (.of k)))
    (fun _ : ℤˣ => Space.underlyingOver B hk (doubledLineSite k B hk)) g

/-- **The covering `Y ⟶ X` coequalizes the two maps of the graph relation of the action.** -/
theorem coveringMorphism_coequalizes :
    yoneda.map (Space.siteActionRelationSource ℤˣ B hk (doubledLineSite k B hk)
        (contains_doubledLineActionRelationScheme k B hk hchar)) ≫ coveringMorphism k B hk =
      yoneda.map (Space.siteActionRelationTarget ℤˣ B hk (doubledLineSite k B hk)
        (contains_doubledLineActionRelationScheme k B hk hchar) (doubledLineAction k B hk)) ≫
        coveringMorphism k B hk := by
  refine hom_ext_of_ofArrows_mem_topology (involutionQuotient k B hk).property _
    (ofArrows_relationSummand_mem_topology k B hk hchar) fun g => ?_
  rw [← Category.assoc, ← Functor.map_comp, relationSummand_comp_source,
    CategoryTheory.Functor.map_id, Category.id_comp, ← Category.assoc, ← Functor.map_comp]
  rcases Int.units_eq_one_or g with rfl | rfl
  · rw [relationSummand_one_comp_target, CategoryTheory.Functor.map_id, Category.id_comp]
  · rw [relationSummand_neg_one_comp_target, yoneda_involution_comp_coveringMorphism]

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- On `Y₁ ⨿ Y₂`, a morphism from the doubled line invariant under the involution only sees
the first chart. -/
theorem yoneda_chartPairToDoubledLine_comp_eq_of_invariant
    (A : Sheaf (BigFppfOver.topology B (Spec (.of k)) hk) (Type u))
    (κ : yoneda.obj (doubledLineSite k B hk) ⟶ A.obj)
    (hκ : yoneda.map (doubledLineInvolution k B hk) ≫ κ = κ) :
    yoneda.map (chartPairToDoubledLine k B hk) ≫ κ =
      yoneda.map (chartPairToAffineLine k B hk ≫ doubledChartHom k B hk false) ≫ κ := by
  refine hom_ext_of_ofArrows_mem_topology A.property _
    (ofArrows_chartPairIncl_mem_topology k B hk) fun b => ?_
  rw [← Category.assoc, ← Functor.map_comp, chartPairIncl_comp_chartPairToDoubledLine,
    ← Category.assoc, ← Functor.map_comp, ← Category.assoc,
    chartPairIncl_comp_chartPairToAffineLine]
  cases b
  · rw [chartTwist_false, Category.id_comp]
  · rw [chartTwist_true, ← Bool.not_true]
    exact (yoneda_chartNeg_comp_doubledChartHom_comp_of_invariant k B hk true κ hκ).symm

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- The restriction to the first chart of a morphism from the doubled line invariant under the
involution coequalizes the relation of Stacks 02Z1. -/
theorem yoneda_relationSource_comp_eq_of_invariant
    (A : Sheaf (BigFppfOver.topology B (Spec (.of k)) hk) (Type u))
    (κ : yoneda.obj (doubledLineSite k B hk) ⟶ A.obj)
    (hκ : yoneda.map (doubledLineInvolution k B hk) ≫ κ = κ) :
    yoneda.map (relationSource k B hk) ≫ yoneda.map (doubledChartHom k B hk false) ≫ κ =
      yoneda.map (relationTarget k B hk) ≫ yoneda.map (doubledChartHom k B hk false) ≫ κ := by
  have hD := relationToChartPair_comp_chartPairToDoubledLine k B hk false
  rw [chartTwist_false, Category.id_comp] at hD
  have hrel : yoneda.map (chartSource k B hk ≫ doubledChartHom k B hk false) ≫ κ =
      yoneda.map (chartTarget k B hk ≫ doubledChartHom k B hk false) ≫ κ :=
    calc yoneda.map (chartSource k B hk ≫ doubledChartHom k B hk false) ≫ κ
        = yoneda.map (relationToChartPair k B hk false) ≫
            yoneda.map (chartPairToAffineLine k B hk ≫ doubledChartHom k B hk false) ≫ κ := by
          rw [← relationToChartPair_comp_chartPairToAffineLine k B hk false, Category.assoc,
            Functor.map_comp, Category.assoc]
      _ = yoneda.map (relationToChartPair k B hk false) ≫
            yoneda.map (chartPairToDoubledLine k B hk) ≫ κ := by
          rw [yoneda_chartPairToDoubledLine_comp_eq_of_invariant k B hk A κ hκ]
      _ = yoneda.map (chartTarget k B hk ≫ doubledChartHom k B hk false) ≫ κ := by
          rw [← Category.assoc, ← Functor.map_comp, hD]
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc] at hrel
  exact hrel

omit hchar in
/-- **A morphism from the doubled line into a sheaf which is invariant under the involution
factors through the covering `Y ⟶ X`.** Its restriction to the first chart coequalizes the
relation of Stacks 02Z1, which is checked through the lift `relationToChartPair` of that
relation to `Y₁ ⨿ Y₂`; so it descends to the quotient `X`, and the descended morphism restricts
correctly to both charts. -/
theorem exists_coveringMorphism_comp_eq_of_invariant
    (A : Sheaf (BigFppfOver.topology B (Spec (.of k)) hk) (Type u))
    (κ : yoneda.obj (doubledLineSite k B hk) ⟶ A.obj)
    (hκ : yoneda.map (doubledLineInvolution k B hk) ≫ κ = κ) :
    ∃ d : (involutionQuotient k B hk).obj ⟶ A.obj, coveringMorphism k B hk ≫ d = κ := by
  set κ' := yoneda.map (doubledChartHom k B hk false) ≫ κ with hκ'
  have hrel : yoneda.map (relationSource k B hk) ≫ κ' =
      yoneda.map (relationTarget k B hk) ≫ κ' :=
    yoneda_relationSource_comp_eq_of_invariant k B hk A κ hκ
  have es : (relationPointsIso k B hk).inv ≫ Stacks.Groupoids.sourceMap
        (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k) =
      yoneda.map (relationSource k B hk) ≫ (affineLinePointsIso k B hk).inv :=
    Space.pointsYonedaIso_inv_comp_whiskerLeft (Over.post (X := B.obj hk) B.inclusion)
      (V := relationChart k B hk) (W := affineLineChart k B hk) (involutionRelation k).source
  have et : (relationPointsIso k B hk).inv ≫ Stacks.Groupoids.targetMap
        (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k) =
      yoneda.map (relationTarget k B hk) ≫ (affineLinePointsIso k B hk).inv :=
    Space.pointsYonedaIso_inv_comp_whiskerLeft (Over.post (X := B.obj hk) B.inclusion)
      (V := relationChart k B hk) (W := affineLineChart k B hk) (involutionRelation k).target
  have hsrc : Stacks.Groupoids.sourceMap (Over.post (X := B.obj hk) B.inclusion)
        (involutionRelation k) ≫ (affineLinePointsIso k B hk).hom ≫ κ' =
      Stacks.Groupoids.targetMap (Over.post (X := B.obj hk) B.inclusion)
        (involutionRelation k) ≫ (affineLinePointsIso k B hk).hom ≫ κ' := by
    rw [← Iso.cancel_iso_inv_left (relationPointsIso k B hk)]
    calc (relationPointsIso k B hk).inv ≫ Stacks.Groupoids.sourceMap
          (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k) ≫
            (affineLinePointsIso k B hk).hom ≫ κ'
        = yoneda.map (relationSource k B hk) ≫ κ' := by
          rw [← Category.assoc, es, Category.assoc, Iso.inv_hom_id_assoc]
      _ = yoneda.map (relationTarget k B hk) ≫ κ' := hrel
      _ = _ := by rw [← Category.assoc _ (Stacks.Groupoids.targetMap _ _), et, Category.assoc,
            Iso.inv_hom_id_assoc]
  set d := Stacks.Groupoids.quotientSheafDesc (BigFppfOver.topology B (Spec (.of k)) hk)
    (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k) A
    ((affineLinePointsIso k B hk).hom ≫ κ') hsrc with hd
  have hdc : quotientChart k B hk ≫ d.hom = κ' := by
    have := Stacks.Groupoids.toQuotientSheaf_quotientSheafDesc
      (BigFppfOver.topology B (Spec (.of k)) hk) (Over.post (X := B.obj hk) B.inclusion)
      (involutionRelation k) A ((affineLinePointsIso k B hk).hom ≫ κ') hsrc
    rw [quotientChart, Category.assoc, hd, this, Iso.inv_hom_id_assoc]
  refine ⟨d.hom, doubledLine_hom_ext k B hk A.property fun b => ?_⟩
  rw [← Category.assoc, doubledChartHom_comp_coveringMorphism]
  cases b
  · rw [doubledChartQuotientMap_false, hdc]
  · rw [doubledChartQuotientMap_true, Category.assoc, hdc, hκ', ← Category.assoc,
      ← Functor.map_comp, ← Bool.not_true]
    exact yoneda_chartNeg_comp_doubledChartHom_comp_of_invariant k B hk true κ hκ

include hchar in
/-- **Stacks 02Z3 for the doubled line: the involution quotient `X` is the quotient `Y/G`.**
The covering `Y ⟶ X` coequalizes the graph relation of the action of `G = \{±1\}`, and every
morphism from `Y` into a sheaf which does so factors uniquely through it; so `X` is the quotient
sheaf of that relation, by an isomorphism carrying `Y ⟶ X` to the projection `Y ⟶ Y/G`. -/
theorem exists_iso_actionQuotient_doubledLineAction :
    ∃ e : (involutionQuotient k B hk).obj ≅
        Space.actionQuotient ℤˣ B hk (doubledLineSite k B hk) (doubledLineAction k B hk),
      coveringMorphism k B hk ≫ e.hom =
        Stacks.Groupoids.quotientChart (BigFppfOver.topology B (Spec (.of k)) hk)
          (Over.post B.inclusion) (doubledLineSite k B hk)
          (Space.actionRelation (Space.underlyingOver B hk (doubledLineSite k B hk)) ℤˣ
            (doubledLineAction k B hk)) := by
  refine Stacks.Groupoids.exists_iso_quotientSheaf_of_descent
    (BigFppfOver.topology B (Spec (.of k)) hk) (Over.post (X := B.obj hk) B.inclusion)
    (Space.siteActionRelationSource ℤˣ B hk (doubledLineSite k B hk)
      (contains_doubledLineActionRelationScheme k B hk hchar))
    (Space.siteActionRelationTarget ℤˣ B hk (doubledLineSite k B hk)
      (contains_doubledLineActionRelationScheme k B hk hchar) (doubledLineAction k B hk))
    (j := Space.actionRelation (Space.underlyingOver B hk (doubledLineSite k B hk)) ℤˣ
      (doubledLineAction k B hk))
    ?_ ?_ (involutionQuotient k B hk).property (coveringMorphism k B hk)
    (coveringMorphism_coequalizes k B hk hchar) ?_
  · simp only [Space.actionRelation, Stacks.Groupoids.PreRelation.source]
    exact (prod.lift_snd _ _).trans (Over.OverMorphism.ext rfl)
  · simp only [Space.actionRelation, Stacks.Groupoids.PreRelation.target]
    exact (prod.lift_fst _ _).trans (Over.OverMorphism.ext rfl)
  · intro A κ hκ
    obtain ⟨d, hd⟩ := exists_coveringMorphism_comp_eq_of_invariant k B hk A κ
      (yoneda_involution_comp_of_coequalizes k B hk hchar κ hκ)
    refine ⟨d, hd, fun d' hd' => ?_⟩
    exact Space.hom_ext_of_isLocallySurjective (coveringMorphism k B hk)
      (isLocallySurjective_coveringMorphism k B hk)
      ((isSheaf_iff_isSheaf_of_type _ _).1 A.property) (hd'.trans hd.symm)

end Quotient

/-- **Stacks 05ZI, the remark's alternative construction.** Away from characteristic two, the
affine line with its origin doubled carries an action of the group `G = \{+1, -1\} = ℤˣ` in
which `-1` swaps the two charts and negates the coordinate. This action is free in the sense of
condition `(*)` of Stacks 02Z2. The quotient `Y/G` of Spaces, Definition 02Z3, is an algebraic
space, and it is the algebraic space `X` of Stacks 05Z6: an isomorphism `X ≅ Y/G` carries the
covering `Y ⟶ X` of the remark to the projection `Y ⟶ Y/G`. -/
@[stacks 05ZI "the remark's alternative construction: G = {±1} acts freely on Y, -1 swapping \
the two charts and negating the coordinate, and X = Y/G in the sense of Spaces, Definition 02Z3"]
theorem doubledLine_freeAction_quotient (hchar : (2 : k) ≠ 0)
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] :
    (∀ b : Bool, doubledChartHom k B hk b ≫ doubledLineInvolution k B hk =
        chartNeg k B hk ≫ doubledChartHom k B hk (!b)) ∧
      (doubledLineAction k B hk (-1)).asIso.hom =
        (Over.post B.inclusion).map (doubledLineInvolution k B hk) ∧
      Space.ActsNontriviallyOnFixedResidueFields
        (Space.underlyingOver B hk (doubledLineSite k B hk)) ℤˣ (doubledLineAction k B hk) ∧
      IsAlgebraicSpace B (Spec (.of k)) hk
        (Space.actionQuotient ℤˣ B hk (doubledLineSite k B hk) (doubledLineAction k B hk)) ∧
      ∃ e : (involutionQuotient k B hk).obj ≅
          Space.actionQuotient ℤˣ B hk (doubledLineSite k B hk) (doubledLineAction k B hk),
        coveringMorphism k B hk ≫ e.hom =
          Stacks.Groupoids.quotientChart (BigFppfOver.topology B (Spec (.of k)) hk)
            (Over.post B.inclusion) (doubledLineSite k B hk)
            (Space.actionRelation (Space.underlyingOver B hk (doubledLineSite k B hk)) ℤˣ
              (doubledLineAction k B hk)) := by
  obtain ⟨e, he⟩ := exists_iso_actionQuotient_doubledLineAction k B hk hchar
  exact ⟨doubledChartHom_comp_doubledLineInvolution k B hk, doubledLineAction_neg_one k B hk,
    actsNontriviallyOnFixedResidueFields_doubledLineAction k B hk hchar,
    isAlgebraicSpace_of_iso B (Spec (.of k)) hk e.symm
      (isAlgebraicSpace_involutionQuotient_of_isAffineHom k B hk hchar), e, he⟩

end AlgebraicGeometry.AffineLineInvolution

end
