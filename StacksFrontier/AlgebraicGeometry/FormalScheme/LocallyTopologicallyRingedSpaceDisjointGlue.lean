module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsFull
public import StacksFrontier.AlgebraicGeometry.FormalScheme.LocallyTopologicallyRingedSpaceGlue
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Automorphisms glued over a disjoint union of opens

Let `Y` be a locally topologically ringed space, `V i` pairwise disjoint opens of `Y` with union
`W`, and `σ i` automorphisms of `Y` which are the identity on points. Then there is an automorphism
`φ` of `Y|_W`, the identity on points, which agrees with `σ i` over `V i` for every `i`. The `σ i`
need not come from a single automorphism of `Y` (or of `Y|_W`): this is how the twist of the
counterexample to the "if" direction of Stacks 0AIW is built, with a different automorphism over
each member of an infinite disjoint union.

## Main definitions

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.disjointGlueIso`: the automorphism `φ`.

## Main results

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.disjointGlueIso_base`: `φ` is the identity
  on points.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.ofRestrict_comp_disjointGlueIso_hom`: over
  `V i`, `φ` is `σ i`.

## References

* [Stacks Project, Tag 0AIW](https://stacks.math.columbia.edu/tag/0AIW)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.LocallyTopologicallyRingedSpace

variable {Y : LTRS.{u}} {ι : Type u} (V : ι → Opens Y)

/-- The member `V i` of the family, as an open of `Y|_W` for `W = ⨆ V`. -/
def disjointGlueCover (i : ι) : Opens (Y.restrict (iSup V)) :=
  (Opens.map (Y.ofRestrict (iSup V)).toHom.base).obj (V i)

/-- The members cover `Y|_W`. -/
theorem iSup_disjointGlueCover : iSup (disjointGlueCover V) = ⊤ := by
  refine eq_top_iff.mpr fun p _ => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp p.2
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

/-- Two morphisms out of a locally topologically ringed space with no points agree. -/
theorem hom_ext_of_isEmpty {Z Z' : LTRS.{u}} (h : IsEmpty Z) (f g : Z ⟶ Z') : f = g :=
  hom_ext_of_openCover (ι := PEmpty.{u + 1}) (fun _ => ⊤)
    (eq_top_iff.mpr fun z => (h.false z).elim) fun i => i.elim

/-- Two morphisms into `Y|_W` agree once composed with `Y|_W ⟶ Y`. -/
@[ega "I 10.2.3" "more general"]
theorem hom_ext_of_comp_ofRestrict {Z : LTRS.{u}} {W : Opens Y} {f g : Z ⟶ Y.restrict W}
    (h : f ≫ Y.ofRestrict W = g ≫ Y.ofRestrict W) : f = g := by
  have hr : Set.range (f ≫ Y.ofRestrict W).toHom.base ⊆
      Set.range (Y.ofRestrict W).toHom.base := by
    rintro _ ⟨z, rfl⟩; exact ⟨_, rfl⟩
  have key : ∀ k : Z ⟶ Y.restrict W, k ≫ Y.ofRestrict W = f ≫ Y.ofRestrict W →
      liftToRestrict W (f ≫ Y.ofRestrict W) hr = k := fun k hk =>
    (Hom.ext' (PresheafedSpace.IsOpenImmersion.lift_uniq (Y.ofRestrict W).toHom
      (f ≫ Y.ofRestrict W).toHom hr k.toHom (congrArg Hom.toHom hk))).symm
  exact (key f rfl).symm.trans (key g h.symm)

variable (σ : ι → (Y ⟶ Y)) (hσ : ∀ i y, (σ i).toHom.base y = y)

include hσ in
/-- `σ i` maps the points of `V i` into `W`, being the identity on points. -/
theorem range_disjointGluePiece_subset (i : ι) :
    Set.range ((Y.restrict (iSup V)).ofRestrict (disjointGlueCover V i) ≫
        Y.ofRestrict (iSup V) ≫ σ i).toHom.base ⊆
      Set.range (Y.ofRestrict (iSup V)).toHom.base := by
  rintro _ ⟨p, rfl⟩
  refine ⟨p.1, ?_⟩
  change _ = (σ i).toHom.base _
  rw [hσ]
  rfl

/-- The piece of the glued morphism over `V i`: `σ i`, read as a morphism into `Y|_W`. -/
noncomputable def disjointGluePiece (i : ι) :
    (Y.restrict (iSup V)).restrict (disjointGlueCover V i) ⟶ Y.restrict (iSup V) :=
  liftToRestrict (iSup V) _ (range_disjointGluePiece_subset V σ hσ i)

/-- The piece over `V i`, composed with `Y|_W ⟶ Y`, is `σ i`. -/
theorem disjointGluePiece_comp_ofRestrict (i : ι) :
    disjointGluePiece V σ hσ i ≫ Y.ofRestrict (iSup V) =
      (Y.restrict (iSup V)).ofRestrict (disjointGlueCover V i) ≫ Y.ofRestrict (iSup V) ≫ σ i :=
  liftToRestrict_comp_ofRestrict _ _ _

variable (hV : Pairwise fun i j => V i ⊓ V j = ⊥)

include hV in
/-- The pieces agree on the overlaps, which are empty for distinct members. -/
theorem existsUnique_disjointGlue :
    ∃! g : Y.restrict (iSup V) ⟶ Y.restrict (iSup V),
      ∀ i, (Y.restrict (iSup V)).ofRestrict (disjointGlueCover V i) ≫ g =
        disjointGluePiece V σ hσ i := by
  refine existsUnique_hom_of_openCover _ (iSup_disjointGlueCover V) _ fun i j => ?_
  by_cases hij : i = j
  · subst hij; rfl
  · refine hom_ext_of_isEmpty ⟨fun p => ?_⟩ _ _
    have h1 : p.1.1 ∈ V i ⊓ V j := ⟨p.2.1, p.2.2⟩
    rw [hV hij] at h1
    exact h1

/-- The automorphism glued from the `σ i`, as a morphism. -/
noncomputable def disjointGlue : Y.restrict (iSup V) ⟶ Y.restrict (iSup V) :=
  (existsUnique_disjointGlue V σ hσ hV).choose

/-- Over `V i` the glued morphism is the piece. -/
theorem ofRestrict_comp_disjointGlue (i : ι) :
    (Y.restrict (iSup V)).ofRestrict (disjointGlueCover V i) ≫ disjointGlue V σ hσ hV =
      disjointGluePiece V σ hσ i :=
  (existsUnique_disjointGlue V σ hσ hV).choose_spec.1 i

/-- Over `V i` the glued morphism is `σ i`. -/
theorem ofRestrict_comp_disjointGlue_comp_ofRestrict (i : ι) :
    (Y.restrict (iSup V)).ofRestrict (disjointGlueCover V i) ≫ disjointGlue V σ hσ hV ≫
        Y.ofRestrict (iSup V) =
      (Y.restrict (iSup V)).ofRestrict (disjointGlueCover V i) ≫ Y.ofRestrict (iSup V) ≫ σ i := by
  rw [← Category.assoc, ofRestrict_comp_disjointGlue, disjointGluePiece_comp_ofRestrict]

/-- The glued morphism is the identity on points. -/
theorem disjointGlue_base (p : Y.restrict (iSup V)) :
    (disjointGlue V σ hσ hV).toHom.base p = p := by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    (show p ∈ iSup (disjointGlueCover V) by rw [iSup_disjointGlueCover V]; trivial)
  have h : (Y.ofRestrict (iSup V)).toHom.base ((disjointGlue V σ hσ hV).toHom.base p) =
      (σ i).toHom.base p.1 :=
    congrArg (fun f => f.toHom.base ⟨p, hi⟩)
      (ofRestrict_comp_disjointGlue_comp_ofRestrict V σ hσ hV i)
  rw [hσ] at h
  exact Subtype.ext h

/-- The piece over `V i` is the identity on points. -/
theorem disjointGluePiece_base (i : ι)
    (p : (Y.restrict (iSup V)).restrict (disjointGlueCover V i)) :
    (disjointGluePiece V σ hσ i).toHom.base p = p.1 := by
  have h : (Y.ofRestrict (iSup V)).toHom.base ((disjointGluePiece V σ hσ i).toHom.base p) =
      (σ i).toHom.base p.1.1 :=
    congrArg (fun f => f.toHom.base p) (disjointGluePiece_comp_ofRestrict V σ hσ i)
  rw [hσ] at h
  exact Subtype.ext h

/-- Gluing the inverses of the `σ i` gives an inverse of the glued morphism. -/
theorem disjointGlue_comp_disjointGlue (τ : ι → (Y ⟶ Y)) (hτ : ∀ i y, (τ i).toHom.base y = y)
    (hστ : ∀ i, σ i ≫ τ i = 𝟙 Y) :
    disjointGlue V σ hσ hV ≫ disjointGlue V τ hτ hV = 𝟙 _ := by
  refine hom_ext_of_openCover _ (iSup_disjointGlueCover V) fun i => ?_
  refine hom_ext_of_comp_ofRestrict ?_
  have hrange : Set.range (disjointGluePiece V σ hσ i).toHom.base ⊆
      Set.range ((Y.restrict (iSup V)).ofRestrict (disjointGlueCover V i)).toHom.base := by
    rintro _ ⟨p, rfl⟩
    exact ⟨p, by rw [disjointGluePiece_base]; rfl⟩
  have hq := liftToRestrict_comp_ofRestrict _ _ hrange
  set q := liftToRestrict _ _ hrange
  calc (Y.restrict (iSup V)).ofRestrict (disjointGlueCover V i) ≫
        (disjointGlue V σ hσ hV ≫ disjointGlue V τ hτ hV) ≫ Y.ofRestrict (iSup V)
      = q ≫ ((Y.restrict (iSup V)).ofRestrict (disjointGlueCover V i) ≫
          disjointGlue V τ hτ hV ≫ Y.ofRestrict (iSup V)) := by
        rw [← Category.assoc, ← Category.assoc, ofRestrict_comp_disjointGlue, ← hq]
        simp only [Category.assoc]
    _ = q ≫ ((Y.restrict (iSup V)).ofRestrict (disjointGlueCover V i) ≫
          Y.ofRestrict (iSup V) ≫ τ i) := by
        rw [ofRestrict_comp_disjointGlue_comp_ofRestrict V τ hτ hV i]
    _ = (disjointGluePiece V σ hσ i ≫ Y.ofRestrict (iSup V)) ≫ τ i := by
        rw [← hq]; simp only [Category.assoc]
    _ = _ := by
        rw [disjointGluePiece_comp_ofRestrict]
        simp only [Category.assoc, hστ, Category.comp_id]

/-- The automorphism of `Y|_W` glued from automorphisms `σ i` of `Y` which are the identity on
points. -/
noncomputable def disjointGlueIso (σ : ι → (Y ≅ Y)) (hσ : ∀ i y, (σ i).hom.toHom.base y = y) :
    Y.restrict (iSup V) ≅ Y.restrict (iSup V) where
  hom := disjointGlue V (fun i => (σ i).hom) hσ hV
  inv := disjointGlue V (fun i => (σ i).inv) (fun i y => by
    conv_lhs => rw [← hσ i y]
    change ((σ i).hom ≫ (σ i).inv).toHom.base y = y
    rw [Iso.hom_inv_id]; rfl) hV
  hom_inv_id := disjointGlue_comp_disjointGlue V _ _ hV _ _ fun i => (σ i).hom_inv_id
  inv_hom_id := disjointGlue_comp_disjointGlue V _ _ hV _ _ fun i => (σ i).inv_hom_id

end AlgebraicGeometry.LocallyTopologicallyRingedSpace

end
