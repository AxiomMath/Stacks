module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Stalks of sheaves of sets at a point are exact

Let `p` be a point of a site `(C, J)`. The stalk at `p` of a presheaf of sets `F` is the colimit of
`F` over the opposite of the category of elements of the fiber functor of `p`, a filtered colimit;
Mathlib's `CategoryTheory.GrothendieckTopology.Point.presheafFiber` and
`CategoryTheory.GrothendieckTopology.Point.sheafFiber` are the stalk functors on presheaves and on
sheaves of sets. This file proves that the stalk of the sheafification of `F` is canonically
isomorphic to the stalk of `F`, and that both stalk functors are exact and preserve all small
colimits.

## Main definitions

* `stalkSheafificationComparison`: the comparison from the stalk of a presheaf of sets to the
  stalk of its sheafification, induced by the unit of sheafification.

## Main results

* `stalkSheafificationComparison_isIso`: the comparison is an isomorphism.
* `sheafStalk_preservesFiniteLimits`, `sheafStalk_preservesFiniteColimits` and
  `sheafStalk_preservesColimits`: the sheaf stalk functor is exact and preserves all small
  colimits.
* `presheafStalk_preservesFiniteLimits`, `presheafStalk_preservesFiniteColimits` and
  `presheafStalk_preservesColimits`: the presheaf stalk functor is exact and preserves all small
  colimits.
* `ColimFiniteLimits.colim_preservesFiniteLimits`: over a filtered index category, with no
  smallness assumption, `colim` into `Type w` preserves finite limits.

## Implementation notes

A point here is Mathlib's `CategoryTheory.GrothendieckTopology.Point`, a fibre functor in the
sense of SGA 4 IV 6.3 whose category of elements is cofiltered, so the stalks are filtered
colimits. Stacks 04EN is stated for the points of Stacks 00Y5, whose stalk colimits need not be
filtered; it is proved for those in
`StacksFrontier/CategoryTheory/Sites/Point/PrecoveragePoint.lean`
(`CategoryTheory.Precoverage.Point.isIso_stalkSheafificationComparison`,
`CategoryTheory.Precoverage.Point.sheafStalk_exact_preservesColimits` and
`CategoryTheory.Precoverage.Point.presheafStalk_exact_preservesColimits`), and the results of
this file are the corresponding statements for Mathlib's points.

The stalk functors are taken at the value category `Type w`, where `Point.{w, v, u}` has
`fiber : C ⥤ Type w` for `C : Type u` with `[Category.{v} C]`. Mathlib's instances saying that the
stalk functors preserve finite limits assume `LocallySmall.{w} C`; the finite-limit statements here
do not, and go through `ColimFiniteLimits.colim_preservesFiniteLimits` instead.

## References

* [Stacks Project, Tag 04EN](https://stacks.math.columbia.edu/tag/04EN), for the points of
  Stacks 00Y5 rather than Mathlib's points; see the implementation notes.
-/

open CategoryTheory CategoryTheory.Limits

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (p : J.Point)

/-- The comparison from the presheaf stalk functor at `p` to sheafification followed by the sheaf
stalk functor at `p`, obtained by whiskering the unit `toSheafification J (Type w)` of the
sheafification adjunction with the presheaf stalk functor. -/
noncomputable def stalkSheafificationComparison [HasWeakSheafify J (Type w)] :
    p.presheafFiber (A := Type w) ⟶
      presheafToSheaf J (Type w) ⋙ p.sheafFiber (A := Type w) :=
  Functor.whiskerRight (toSheafification J (Type w)) (p.presheafFiber (A := Type w))

/-- Precomposition with `(Functor.Elements.π p.fiber).op`, the first factor of `p.presheafFiber`,
preserves finite limits. -/
@[sga "4 I 5.0" "special case"]
theorem presheafStalkWhiskering_preservesFiniteLimits :
    PreservesFiniteLimits ((Functor.whiskeringLeft p.fiber.Elementsᵒᵖ Cᵒᵖ (Type w)).obj
      (Functor.Elements.π p.fiber).op) := by
  constructor
  intro K _ _
  apply preservesLimitsOfShape_of_evaluation
  intro k
  exact inferInstanceAs (PreservesLimitsOfShape K
    ((evaluation Cᵒᵖ (Type w)).obj ((Functor.Elements.π p.fiber).op.obj k)))

/-! ### Filtered colimits commute with finite limits in `Type`

A filtered colimit functor `colim : (K ⥤ Type w) ⥤ Type w` preserves finite limits, with no
smallness assumption on the filtered index category `K`. -/

namespace ColimFiniteLimits

variable {K : Type*} [Category K] [IsFiltered K] [HasColimitsOfShape K (Type w)]
variable {D : Type w} [SmallCategory D] [FinCategory D]

omit [IsFiltered K] in
private theorem ι_natural (F F' : K ⥤ Type w) (α : F ⟶ F') (k : K) (x : F.obj k) :
    colimit.ι F' k (α.app k x) = colimMap α (colimit.ι F k x) := by
  have h := ConcreteCategory.congr_hom (colimit.ι_map α k) x
  simp only [ConcreteCategory.comp_apply] at h
  exact h.symm

omit [IsFiltered K] in
private theorem ι_w_apply (F : K ⥤ Type w) {k k' : K} (g : k ⟶ k') (x : F.obj k) :
    colimit.ι F k' (F.map g x) = colimit.ι F k x := by
  have h := ConcreteCategory.congr_hom (colimit.w F g) x
  simp only [ConcreteCategory.comp_apply] at h
  exact h

omit [IsFiltered K] [HasColimitsOfShape K (Type w)] [FinCategory D] in
private theorem limit_ext (G : D ⥤ (K ⥤ Type w)) (c : K) (a b : (limit G).obj c)
    (h : ∀ j, (limit.π G j).app c a = (limit.π G j).app c b) : a = b := by
  apply (preservesLimitIso ((evaluation K (Type w)).obj c) G).toEquiv.injective
  apply Limits.Types.limit_ext
  intro j
  simp only [Iso.toEquiv_fun]
  have hπ := preservesLimitIso_hom_π ((evaluation K (Type w)).obj c) G j
  have ha := ConcreteCategory.congr_hom hπ a
  have hb := ConcreteCategory.congr_hom hπ b
  simp only [ConcreteCategory.comp_apply] at ha hb
  rw [ha, hb]; exact h j

omit [IsFiltered K] [HasColimitsOfShape K (Type w)] [FinCategory D] in
private theorem build_z (G : D ⥤ (K ⥤ Type w)) (k₀ : K) (v : ∀ j, (G.obj j).obj k₀)
    (hv : ∀ {j j'} (f : j ⟶ j'), (G.map f).app k₀ (v j) = v j') :
    ∃ z : (limit G).obj k₀, ∀ j, (limit.π G j).app k₀ z = v j := by
  let e : limit (G ⋙ (evaluation K (Type w)).obj k₀) :=
    Types.Limit.mk (G ⋙ (evaluation K (Type w)).obj k₀) (fun j => v j) (fun j j' f => hv f)
  refine ⟨(preservesLimitIso ((evaluation K (Type w)).obj k₀) G).inv e, fun j => ?_⟩
  have hπ := preservesLimitIso_inv_π ((evaluation K (Type w)).obj k₀) G j
  have key := ConcreteCategory.congr_hom hπ e
  simp only [ConcreteCategory.comp_apply] at key
  have hmk : (limit.π (G ⋙ (evaluation K (Type w)).obj k₀) j) e = v j :=
    Types.Limit.π_mk _ _ _ j
  calc (limit.π G j).app k₀ ((preservesLimitIso ((evaluation K (Type w)).obj k₀) G).inv e)
      = ((evaluation K (Type w)).obj k₀).map (limit.π G j)
          ((preservesLimitIso ((evaluation K (Type w)).obj k₀) G).inv e) := rfl
    _ = (limit.π (G ⋙ (evaluation K (Type w)).obj k₀) j) e := key
    _ = v j := hmk

private theorem merge_section (G : D ⥤ (K ⥤ Type w)) (s : ∀ j, colimit (G.obj j))
    (hs : ∀ {j j'} (f : j ⟶ j'), colimMap (G.map f) (s j) = s j') :
    ∃ (k₀ : K) (v : ∀ j, (G.obj j).obj k₀),
      (∀ j, colimit.ι (G.obj j) k₀ (v j) = s j) ∧
      (∀ {j j'} (f : j ⟶ j'), (G.map f).app k₀ (v j) = v j') := by
  classical
  choose kk yy hyy using fun j => Types.jointly_surjective' (s j)
  have key : ∀ {j j'} (f : j ⟶ j'),
      colimit.ι (G.obj j') (kk j) ((G.map f).app (kk j) (yy j)) = colimit.ι (G.obj j') (kk j') (yy
          j') := by
    intro j j' f
    rw [ι_natural (G.obj j) (G.obj j') (G.map f) (kk j) (yy j), hyy j, hs f, ← hyy j']
  choose mm uu vv eqq using fun (j j' : D) (f : j ⟶ j') =>
    (Types.FilteredColimit.colimit_eq_iff (G.obj j')).mp (key f)
  set Ok : Finset K := Finset.univ.image kk with hOk
  set Om : Finset K := Finset.univ.image (fun (t : Σ (p : D × D), (p.1 ⟶ p.2)) => mm t.1.1 t.1.2
      t.2) with hOm
  set O : Finset K := Ok ∪ Om with hO
  have hkk : ∀ j, kk j ∈ O := by
    intro j; rw [hO]; apply Finset.mem_union_left; rw [hOk]; exact Finset.mem_image_of_mem _
        (Finset.mem_univ j)
  have hmm : ∀ (j j' : D) (f : j ⟶ j'), mm j j' f ∈ O := by
    intro j j' f; rw [hO]; apply Finset.mem_union_right; rw [hOm]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ (⟨(j,j'), f⟩ : Σ (p : D × D), (p.1 ⟶ p.2)))
  let Hentry : Type _ := (X : K) ×' (Y : K) ×' (_ : X ∈ O) ×' (_ : Y ∈ O) ×' (X ⟶ Y)
  let Hu : Finset Hentry := Finset.univ.image
    (fun (t : Σ (p : D × D), (p.1 ⟶ p.2)) =>
      (⟨kk t.1.1, mm t.1.1 t.1.2 t.2, hkk t.1.1, hmm t.1.1 t.1.2 t.2, uu t.1.1 t.1.2 t.2⟩ : Hentry))
  let Hv : Finset Hentry := Finset.univ.image
    (fun (t : Σ (p : D × D), (p.1 ⟶ p.2)) =>
      (⟨kk t.1.2, mm t.1.1 t.1.2 t.2, hkk t.1.2, hmm t.1.1 t.1.2 t.2, vv t.1.1 t.1.2 t.2⟩ : Hentry))
  let H : Finset Hentry := Hu ∪ Hv
  have memu : ∀ (j j' : D) (f : j ⟶ j'),
      (⟨kk j, mm j j' f, hkk j, hmm j j' f, uu j j' f⟩ : Hentry) ∈ H := by
    intro j j' f; apply Finset.mem_union_left
    exact Finset.mem_image_of_mem _ (Finset.mem_univ (⟨(j,j'), f⟩ : Σ (p : D × D), (p.1 ⟶ p.2)))
  have memv : ∀ (j j' : D) (f : j ⟶ j'),
      (⟨kk j', mm j j' f, hkk j', hmm j j' f, vv j j' f⟩ : Hentry) ∈ H := by
    intro j j' f; apply Finset.mem_union_right
    exact Finset.mem_image_of_mem _ (Finset.mem_univ (⟨(j,j'), f⟩ : Σ (p : D × D), (p.1 ⟶ p.2)))
  have cu : ∀ (j j' : D) (f : j ⟶ j'),
      uu j j' f ≫ IsFiltered.toSup O H (hmm j j' f) = IsFiltered.toSup O H (hkk j) :=
    fun j j' f => IsFiltered.toSup_commutes O H (hkk j) (hmm j j' f) (memu j j' f)
  have cv : ∀ (j j' : D) (f : j ⟶ j'),
      vv j j' f ≫ IsFiltered.toSup O H (hmm j j' f) = IsFiltered.toSup O H (hkk j') :=
    fun j j' f => IsFiltered.toSup_commutes O H (hkk j') (hmm j j' f) (memv j j' f)
  refine ⟨IsFiltered.sup O H, fun j => (G.obj j).map (IsFiltered.toSup O H (hkk j)) (yy j), ?_, ?_⟩
  · intro j
    rw [ι_w_apply (G.obj j) (IsFiltered.toSup O H (hkk j)) (yy j), hyy j]
  · intro j j' f
    have nat := ((G.map f).naturality (IsFiltered.toSup O H (hkk j)))
    have lhs : (G.map f).app (IsFiltered.sup O H) ((G.obj j).map (IsFiltered.toSup O H (hkk j)) (yy
        j))
        = (G.obj j').map (IsFiltered.toSup O H (hkk j)) ((G.map f).app (kk j) (yy j)) := by
      have hh := ConcreteCategory.congr_hom nat (yy j)
      simp only [ConcreteCategory.comp_apply] at hh
      exact hh
    rw [lhs, ← cu j j' f]
    rw [Functor.map_comp, ConcreteCategory.comp_apply, eqq j j' f]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, cv j j' f]

private theorem merge_eq (G : D ⥤ (K ⥤ Type w)) (x x' : colimit (limit G))
    (hxx : ∀ j, colimMap (limit.π G j) x = colimMap (limit.π G j) x') : x = x' := by
  classical
  obtain ⟨a, p, hp⟩ := Types.jointly_surjective' x
  obtain ⟨b, q, hq⟩ := Types.jointly_surjective' x'
  have perj : ∀ j, colimit.ι (G.obj j) a ((limit.π G j).app a p) = colimit.ι (G.obj j) b ((limit.π
      G j).app b q) := by
    intro j
    rw [ι_natural (limit G) (G.obj j) (limit.π G j) a p,
        ι_natural (limit G) (G.obj j) (limit.π G j) b q, hp, hq, hxx j]
  choose cc gg hh eqq using fun j => (Types.FilteredColimit.colimit_eq_iff (G.obj j)).mp (perj j)
  set O : Finset K := insert a (insert b (Finset.univ.image cc)) with hO
  have ha : a ∈ O := by rw [hO]; exact Finset.mem_insert_self _ _
  have hb : b ∈ O := by rw [hO]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hc : ∀ j, cc j ∈ O := by
    intro j; rw [hO]; apply Finset.mem_insert_of_mem; apply Finset.mem_insert_of_mem
    exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
  let Hentry : Type _ := (X : K) ×' (Y : K) ×' (_ : X ∈ O) ×' (_ : Y ∈ O) ×' (X ⟶ Y)
  let Hg : Finset Hentry := Finset.univ.image (fun j : D => (⟨a, cc j, ha, hc j, gg j⟩ : Hentry))
  let Hh : Finset Hentry := Finset.univ.image (fun j : D => (⟨b, cc j, hb, hc j, hh j⟩ : Hentry))
  let HH : Finset Hentry := Hg ∪ Hh
  have memg : ∀ j, (⟨a, cc j, ha, hc j, gg j⟩ : Hentry) ∈ HH := by
    intro j; apply Finset.mem_union_left; exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
  have memh : ∀ j, (⟨b, cc j, hb, hc j, hh j⟩ : Hentry) ∈ HH := by
    intro j; apply Finset.mem_union_right; exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
  have cg : ∀ j, gg j ≫ IsFiltered.toSup O HH (hc j) = IsFiltered.toSup O HH ha :=
    fun j => IsFiltered.toSup_commutes O HH ha (hc j) (memg j)
  have ch : ∀ j, hh j ≫ IsFiltered.toSup O HH (hc j) = IsFiltered.toSup O HH hb :=
    fun j => IsFiltered.toSup_commutes O HH hb (hc j) (memh j)
  set c := IsFiltered.sup O HH with hcdef
  have hpq : (limit G).map (IsFiltered.toSup O HH ha) p = (limit G).map (IsFiltered.toSup O HH
      hb) q := by
    apply limit_ext G c
    intro j
    have natg := ConcreteCategory.congr_hom ((limit.π G j).naturality (IsFiltered.toSup O HH ha)) p
    have nath := ConcreteCategory.congr_hom ((limit.π G j).naturality (IsFiltered.toSup O HH hb)) q
    simp only [ConcreteCategory.comp_apply] at natg nath
    rw [natg, nath]
    rw [← cg j, ← ch j, Functor.map_comp, Functor.map_comp,
        ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, eqq j]
  rw [← hp, ← hq, ← ι_w_apply (limit G) (IsFiltered.toSup O HH ha) p,
      ← ι_w_apply (limit G) (IsFiltered.toSup O HH hb) q, hpq]

/-- For a filtered index category `K` (no smallness needed), `colim` preserves limits of
any finite shape `D`. -/
@[sga "4 I 2.8" "more general", sga "4 I 3.3" "special case", sga "4 II 4.3" "special case"]
theorem colim_preservesLimitsOfShape :
    PreservesLimitsOfShape D (colim (J := K) (C := Type w)) := by
  constructor
  intro G
  apply preservesLimit_of_preserves_limit_cone (limit.isLimit G)
  apply Nonempty.some
  rw [Types.isLimit_iff (colim.mapCone (limit.cone G))]
  intro s hs
  have hs' : ∀ {j j'} (f : j ⟶ j'), colimMap (G.map f) (s j) = s j' := fun f => by simpa using hs f
  obtain ⟨k₀, v, hv1, hv2⟩ := merge_section G s hs'
  obtain ⟨z, hz⟩ := build_z G k₀ v hv2
  have hx : ∀ j, colimMap (limit.π G j) (colimit.ι (limit G) k₀ z) = s j := by
    intro j
    rw [← ι_natural (limit G) (G.obj j) (limit.π G j) k₀ z, hz j, hv1 j]
  exact ⟨colimit.ι (limit G) k₀ z, hx,
    fun y hy => merge_eq G y _ fun j => (hy j).trans (hx j).symm⟩

/-- For a filtered index category `K` (no smallness needed), `colim` preserves all finite
limits. -/
@[sga "4 I 2.8" "more general", sga "4 I 3.3" "special case", sga "4 II 4.3" "special case"]
theorem colim_preservesFiniteLimits :
    PreservesFiniteLimits (colim (J := K) (C := Type w)) :=
  preservesFiniteLimits_of_preservesFiniteLimitsOfSize _
    (fun _ _ _ => colim_preservesLimitsOfShape)

end ColimFiniteLimits

/-- The colimit functor `colim : (p.fiber.Elementsᵒᵖ ⥤ Type w) ⥤ Type w` over the filtered
category `p.fiber.Elementsᵒᵖ` preserves finite limits. -/
theorem presheafStalkColim_preservesFiniteLimits :
    PreservesFiniteLimits (colim (J := p.fiber.Elementsᵒᵖ) (C := Type w)) :=
  ColimFiniteLimits.colim_preservesFiniteLimits

/-- The colimit functor `colim : (p.fiber.Elementsᵒᵖ ⥤ Type w) ⥤ Type w` preserves all small
colimits, being a left adjoint to the constant-diagram functor. -/
theorem presheafStalkColim_preservesColimits :
    PreservesColimits (colim (J := p.fiber.Elementsᵒᵖ) (C := Type w)) :=
  (colimConstAdj).leftAdjoint_preservesColimits

/-- Each component of `stalkSheafificationComparison p` is an isomorphism. -/
private theorem stalkSheafificationComparison_app_isIso [HasWeakSheafify J (Type w)]
    (F : Cᵒᵖ ⥤ Type w) : IsIso ((stalkSheafificationComparison.{w} p).app F) := by
  change IsIso ((p.presheafFiber (A := Type w)).map ((toSheafification J (Type w)).app F))
  exact p.W_isInvertedBy_presheafFiber _
    (GrothendieckTopology.W_adj_unit_app J (sheafificationAdjunction J (Type w)) F)

/-- Each component of `stalkSheafificationComparison p` is injective. -/
@[sga "4 VIII 3.9" "partial"]
theorem stalkSheafificationComparison_app_injective [HasWeakSheafify J (Type w)]
    (F : Cᵒᵖ ⥤ Type w) :
    Function.Injective ((stalkSheafificationComparison.{w} p).app F) :=
  have := stalkSheafificationComparison_app_isIso.{w} p F
  (ConcreteCategory.bijective_of_isIso _).1

/-- Each component of `stalkSheafificationComparison p` is surjective. -/
@[sga "4 VIII 3.9" "partial"]
theorem stalkSheafificationComparison_app_surjective [HasWeakSheafify J (Type w)]
    (F : Cᵒᵖ ⥤ Type w) :
    Function.Surjective ((stalkSheafificationComparison.{w} p).app F) :=
  have := stalkSheafificationComparison_app_isIso.{w} p F
  (ConcreteCategory.bijective_of_isIso _).2

/-- The comparison natural transformation `stalkSheafificationComparison p`, from the stalk at
`p` of a presheaf of sets to the stalk at `p` of its sheafification, is an isomorphism. -/
@[sga "4 IV 6.8.2" "formula (6.8.4)"]
theorem stalkSheafificationComparison_isIso [HasWeakSheafify J (Type w)] :
    IsIso (stalkSheafificationComparison.{w} p) := by
  have : ∀ F, IsIso ((stalkSheafificationComparison.{w} p).app F) := by
    intro F
    rw [isIso_iff_bijective]
    exact ⟨stalkSheafificationComparison_app_injective p F,
      stalkSheafificationComparison_app_surjective p F⟩
  exact NatIso.isIso_of_isIso_app _

/-- The presheaf stalk functor at `p` preserves finite limits, without a smallness assumption. -/
private theorem presheafFiber_preservesFiniteLimits :
    PreservesFiniteLimits (p.presheafFiber (A := Type w)) :=
  have := presheafStalkWhiskering_preservesFiniteLimits.{w} p
  have := presheafStalkColim_preservesFiniteLimits.{w} p
  comp_preservesFiniteLimits _ _

/-- The sheaf stalk functor at `p` preserves finite limits. -/
@[sga "4 VIII 3.5" "more general"]
theorem sheafStalk_preservesFiniteLimits [HasWeakSheafify J (Type w)] :
    PreservesFiniteLimits (p.sheafFiber (A := Type w)) := by
  -- Mathlib's instance for `p.sheafFiber` assumes `LocallySmall.{w} C`, which is not assumed here.
  change PreservesFiniteLimits (sheafToPresheaf J (Type w) ⋙ p.presheafFiber (A := Type w))
  have : PreservesFiniteLimits (sheafToPresheaf J (Type w)) := inferInstance
  have := presheafFiber_preservesFiniteLimits.{w} p
  exact comp_preservesFiniteLimits _ _

/-- The sheaf stalk functor at `p` preserves all small colimits. -/
@[sga "4 VIII 3.5" "more general"]
theorem sheafStalk_preservesColimits [HasWeakSheafify J (Type w)] :
    PreservesColimits (p.sheafFiber (A := Type w)) := inferInstance

/-- The sheaf stalk functor at `p` preserves finite colimits. -/
@[sga "4 VIII 3.5" "Clause a)"]
theorem sheafStalk_preservesFiniteColimits [HasWeakSheafify J (Type w)] :
    PreservesFiniteColimits (p.sheafFiber (A := Type w)) := by
  have := sheafStalk_preservesColimits.{w} p
  exact PreservesColimitsOfSize.preservesFiniteColimits (p.sheafFiber (A := Type w))

/-- The presheaf stalk functor at `p` preserves finite limits. -/
@[sga "4 VIII 3.5" "a) finite limits",
  sga "4 IV 6.8.6" "left-exactness clause of",
  sga "4 IV 6.8.7" "(iii)⇒(i), special case"]
theorem presheafStalk_preservesFiniteLimits :
    PreservesFiniteLimits (p.presheafFiber (A := Type w)) := by
  exact presheafFiber_preservesFiniteLimits.{w} p

/-- The presheaf stalk functor at `p` preserves all small colimits. -/
@[sga "4 VIII 3.5" "a) colimits", sga "4 IV 6.8.6" "partial"]
theorem presheafStalk_preservesColimits :
    PreservesColimits (p.presheafFiber (A := Type w)) := inferInstance

/-- The presheaf stalk functor at `p` preserves finite colimits. -/
theorem presheafStalk_preservesFiniteColimits :
    PreservesFiniteColimits (p.presheafFiber (A := Type w)) := by
  have := presheafStalk_preservesColimits.{w} p
  exact PreservesColimitsOfSize.preservesFiniteColimits (p.presheafFiber (A := Type w))
