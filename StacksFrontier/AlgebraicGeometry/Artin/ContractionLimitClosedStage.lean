module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitSpaceOpenIso
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# A closed subset of a Noetherian limit comes from a stage

Let `V = lim V_i` be a cofiltered limit of affine objects of the big fppf site with `V`
Noetherian. Every closed subset `Z ⊆ |V|` is the inverse image of a closed subset of some `|V_k|`:
`Z` is the vanishing locus of finitely many functions, and these come from a stage.

This is the step "descending `Z`" of the proof of Stacks 0GI5 (there quoted from Stacks 01ZM).

## Main results

* `AlgebraicGeometry.Space.exists_stage_preimage_eq_of_isClosed`

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A closed subset of a Noetherian limit of affine objects is the inverse image of a closed
subset of a stage.** -/
theorem exists_stage_preimage_eq_of_isClosed
    {I : Type u} [Category.{u} I] [IsCofiltered I] {E : I ⥤ BigFppfOver B S hS} {c : Cone E}
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hE : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i)))
    (hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt))
    (hNoeth : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj c.pt, ⊤))
    {Z : Set (points B S hS (yoneda.obj c.pt))} (hZ : IsClosed Z) :
    ∃ (k : I) (Zk : Set (points B S hS (yoneda.obj (E.obj k)))), IsClosed Zk ∧
      pointsMap B S hS _ (yoneda.map (c.π.app k)) ⁻¹' Zk = Z := by
  classical
  let T := BigFppfOver.toScheme B S hS
  let D := E ⋙ T
  have : ∀ i, IsAffine (D.obj i) := hE
  have : ∀ {i j : I} (f : i ⟶ j), AlgebraicGeometry.IsAffineHom (D.map f) :=
    fun _ => isAffineHom_of_isAffine _
  have : IsAffine (T.obj c.pt) := hpt
  obtain ⟨Iid, hI⟩ := exists_ideal_mem_iff_mem_zeroLocus B S hS c.pt hZ
  obtain ⟨gens, hgens⟩ := (IsNoetherian.noetherian Iid : Iid.FG)
  -- each generator comes from a stage
  have hlift : ∀ g : gens, ∃ (i : I) (t : Γ(D.obj i, ⊤)), g.1 = (T.map (c.π.app i)).appTop t :=
    fun g => exists_appTop_π_eq_of_isLimit D (T.mapCone c) hc g.1
  choose ig tg htg using hlift
  -- a common stage
  let Os : Finset I := Finset.univ.image ig
  obtain ⟨k, Tm, -⟩ := IsCofiltered.inf_exists Os ∅
  have hk : ∀ g, ig g ∈ Os := fun g => Finset.mem_image_of_mem _ (Finset.mem_univ g)
  let t' : gens → Γ(D.obj k, ⊤) := fun g => (T.map (E.map (Tm (hk g)))).appTop (tg g)
  have ht' : ∀ g, g.1 = (T.map (c.π.app k)).appTop (t' g) := fun g => by
    rw [htg g, ← c.w (Tm (hk g)), T.map_comp, Scheme.Hom.comp_appTop]
    rfl
  have hgz : (T.obj c.pt).zeroLocus (Iid : Set Γ(T.obj c.pt, ⊤)) =
      (T.obj c.pt).zeroLocus (gens : Set Γ(T.obj c.pt, ⊤)) := by
    rw [← hgens, Scheme.zeroLocus_span]
  refine ⟨k, schemePointsHomeomorph B S hS (E.obj k) ⁻¹'
    (T.obj (E.obj k)).zeroLocus (Set.range t'),
    (Scheme.zeroLocus_isClosed _ _).preimage (schemePointsHomeomorph B S hS _).continuous, ?_⟩
  ext x
  rw [Set.mem_preimage, Set.mem_preimage, hI x, hgz, schemePointsHomeomorph_apply,
    pointsToScheme_pointsMap_yoneda, Scheme.mem_zeroLocus_iff, Scheme.mem_zeroLocus_iff]
  constructor
  · intro h f hf hx
    refine h (t' ⟨f, hf⟩) ⟨_, rfl⟩ ?_
    have e : f = (T.map (c.π.app k)).appTop (t' ⟨f, hf⟩) := ht' ⟨f, hf⟩
    rwa [e, ← Scheme.preimage_basicOpen_top] at hx
  · rintro h _ ⟨g, rfl⟩ hx
    refine h g.1 g.2 ?_
    rwa [ht' g, ← Scheme.preimage_basicOpen_top]

/-- **A subset of `|V_i| ∖ Z` closed there, with empty inverse image in the limit, has empty
inverse image at a later stage** (Stacks 01Z4 applied to `C ∪ Z` and `Z`). -/
theorem exists_stage_preimage_eq_empty
    {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ LocallyNoetherianOver B S hS}
    {c : Cone D} (hc : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone c))
    (hD : ∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i))) (i : I)
    {Z C : Set (points B S hS (yoneda.obj (D.obj i).obj))} (hZ : IsClosed Z)
    (hCZ : IsClosed (C ∪ Z)) (hdisj : Disjoint C Z)
    (h : pointsMap B S hS (yoneda.obj c.pt.obj) (yoneda.map (c.π.app i).hom) ⁻¹' C = ∅) :
    ∃ (j : I) (f : j ⟶ i), pointsMap B S hS _ (yoneda.map (D.map f).hom) ⁻¹' C = ∅ := by
  obtain ⟨j, f, hf⟩ := Artin.exists_preimage_eq_of_isClosed hc hD i hCZ hZ (by
    rw [Set.preimage_union, h, Set.empty_union])
  refine ⟨j, f, Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_⟩
  have hx' : x ∈ pointsMap B S hS _ (yoneda.map (D.map f).hom) ⁻¹' (C ∪ Z) := Or.inl hx
  rw [hf] at hx'
  exact Set.disjoint_left.1 hdisj hx hx'

end AlgebraicGeometry.Space

end
