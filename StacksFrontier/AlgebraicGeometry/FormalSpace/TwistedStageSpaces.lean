module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.BoundedColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TwistedStageSchemes

/-!
# The two affine formal algebraic spaces behind the sharpness of representability

This file puts the two systems of affine schemes of
`StacksFrontier.AlgebraicGeometry.FormalSpace.TwistedStageSchemes` into a big fppf site and takes
their colimits, producing the target and the source of the morphism of Stacks 0CBE — the second
sense of the warning of Stacks 0AN7.

Everything is driven by one cardinal inequality, `#(Lam I) < B.cutoff`. Since the fixed
presenting ring surjects onto every stage ring, and a stage of the source is a pair of stage
rings, that single bound dominates every ring in sight; so every stage lies in the site, and the
uniform bound `μ = max ℵ₀ #(Lam I)` is exactly what
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_bounded_colimit` asks for. The
set-theoretic condition of Stacks 0AIS is therefore a *theorem* here and not a hypothesis — the
index may be uncountable, as it must be, because the bound replaces any appeal to the cofinality
of the cutoff.

## Main definitions

* `Stacks.Coherent.targetBigAffineDiagram` and `Stacks.Coherent.sourceBigAffineDiagram`: the two
  presentations, as diagrams of affine objects of the site over the base.
* `Stacks.Coherent.targetSpace` and `Stacks.Coherent.sourceSpace`: their colimits.

## Main results

* `Stacks.Coherent.mk_stageRing_le`, `Stacks.Coherent.mk_dualStage_le`: the single cardinal
  `#(Lam I)` dominates every ring of both systems.
* `Stacks.Coherent.contains_targetScheme`, `Stacks.Coherent.contains_sourceScheme`: every stage
  lies in the site.
* `Stacks.Coherent.isAffineFormalAlgebraicSpace_targetSpace` and
  `Stacks.Coherent.isAffineFormalAlgebraicSpace_sourceSpace`: both colimits are affine formal
  algebraic spaces.

## Implementation notes

The bound on the source's stages is where the shape of the construction pays off: a surjection
`Lam I → StageRing b` is `lamProj b`, so `#(StageRing b) ≤ #(Lam I)` needs no computation at
all, and `DualStage b` being `StageRing b × StageRing b` its cardinality is then
`#(Lam I) * #(Lam I) = #(Lam I)`, the ring being infinite. Nothing has to be said about the
cardinality of `Stage b`, which is a quotient and would otherwise have to be estimated.

The spaces are *defined* as `colimit`s, so their isomorphisms with the colimits of the
presentations are `Iso.refl`.
-/

@[expose] public noncomputable section

namespace Stacks.Coherent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.FormalSpace

universe u

variable {I : Type u} [LinearOrder I] [WellFoundedLT I]

/-! ### One cardinal dominates every ring of both systems -/

/-- The fixed presenting ring `Lam I` is infinite. -/
instance instInfiniteLam (I : Type u) [LinearOrder I] [WellFoundedLT I] : Infinite (Lam I) :=
  inferInstanceAs (Infinite (ℚ × Amb I))

/-- The fixed presenting ring is infinite, containing the rationals. -/
theorem aleph0_le_mk_lam (I : Type u) [LinearOrder I] [WellFoundedLT I] :
    Cardinal.aleph0.{u} ≤ Cardinal.mk (Lam I) :=
  Cardinal.aleph0_le_mk _

/-- Every stage ring of the target is dominated by the fixed presenting ring, which surjects
onto it. -/
theorem mk_stageRing_le (b : I) : Cardinal.mk (StageRing b) ≤ Cardinal.mk (Lam I) :=
  Cardinal.mk_le_of_surjective (lamProj_surjective b)

/-- Every stage ring of the source is dominated by the fixed presenting ring: it is a pair of
target stage rings, and the fixed ring is infinite. -/
theorem mk_dualStage_le (b : I) : Cardinal.mk (DualStage b) ≤ Cardinal.mk (Lam I) := by
  change Cardinal.mk (StageRing b × StageRing b) ≤ _
  simp only [Cardinal.mk_prod, Cardinal.lift_id]
  exact (mul_le_mul' (mk_stageRing_le b) (mk_stageRing_le b)).trans
    (Cardinal.mul_eq_self (aleph0_le_mk_lam I)).le

/-- The index is dominated by the fixed presenting ring: a point of the index gives the
finitely supported function taking the value one there, and that sits in the square-zero part. -/
theorem mk_index_le_mk_lam (I : Type u) [LinearOrder I] [WellFoundedLT I] :
    Cardinal.mk I ≤ Cardinal.mk (Lam I) :=
  Cardinal.mk_le_of_injective
    (f := fun i : I ↦ (TrivSqZeroExt.inr (Finsupp.single i (1 : ℚ)) : Lam I))
    fun _ _ hij ↦ Finsupp.single_left_injective one_ne_zero <| by
      simpa only [TrivSqZeroExt.snd_inr] using congrArg TrivSqZeroExt.snd hij

/-! ### The stages lie in the site -/

/-- The spectrum of a ring smaller than the cutoff lies in the site. -/
private theorem contains_spec_of_mk_lt (B : BigFppfSite.{u}) (R : Type u) [CommRing R]
    (h : Cardinal.mk R < B.cutoff) : B.Contains (Spec (CommRingCat.of R)) := by
  rw [BigFppfSite.Contains, Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff h

variable (B : BigFppfSite.{u}) (hcard : Cardinal.mk (Lam I) < B.cutoff)

include hcard in
/-- The base lies in the site. -/
theorem contains_baseScheme : B.Contains (baseScheme I) := by
  exact contains_spec_of_mk_lt B _ hcard

include hcard in
/-- Every stage of the target lies in the site. -/
theorem contains_targetScheme (b : I) : B.Contains ((targetSchemeDiagram I).obj b) := by
  rw [targetSchemeDiagram_obj]
  exact contains_spec_of_mk_lt B _ ((mk_stageRing_le b).trans_lt hcard)

include hcard in
/-- Every stage of the source lies in the site. -/
theorem contains_sourceScheme (hcnt : ∀ a : I, (Set.Iio a).Countable) (b : I) :
    B.Contains ((sourceSchemeDiagram hcnt).obj b) := by
  rw [sourceSchemeDiagram_obj]
  exact contains_spec_of_mk_lt B _ ((mk_dualStage_le b).trans_lt hcard)

/-! ### The index, lifted to the universe of the presentation -/

/-- The index of a presentation lives one universe up. -/
abbrev Index (I : Type u) := ULift.{u + 1} I

/-- The lifted index is nonempty when the index is. -/
instance instNonemptyIndex [Nonempty I] : Nonempty (Index I) := ⟨ULift.up (Classical.arbitrary I)⟩

/-- The lifted index is directed under its order. -/
instance instIsDirectedIndex : IsDirected (Index I) (· ≤ ·) :=
  ⟨fun i j ↦ ⟨ULift.up (max i.down j.down), le_max_left _ _, le_max_right _ _⟩⟩

/-! ### The two presentations inside the site -/

/-- A stage of the target, as an affine scheme over the base in the big fppf site. -/
def targetBigAffineObject (b : I) :
    BigAffineFppf B (baseScheme I) (contains_baseScheme B hcard) :=
  ⟨Over.mk (show B.obj (contains_targetScheme B hcard b) ⟶
      B.obj (contains_baseScheme B hcard) from
    ObjectProperty.homMk (targetStructureMap b)), by
      change IsAffine (Spec (CommRingCat.of (StageRing b)))
      infer_instance⟩

/-- The target's presentation: its directed system of affine schemes over the base, in the big
fppf site. -/
def targetBigAffineDiagram :
    Index I ⥤ BigAffineFppf B (baseScheme I) (contains_baseScheme B hcard) where
  obj b := targetBigAffineObject B hcard b.down
  map {s t} f := ObjectProperty.homMk (Over.homMk
      (ObjectProperty.homMk ((targetSchemeDiagram I).map
        (homOfLE (show s.down ≤ t.down from (leOfHom f : s ≤ t))))) (by
    apply ObjectProperty.hom_ext
    exact targetStructureMap_naturality (homOfLE (show s.down ≤ t.down from (leOfHom f : s ≤ t)))))
  map_id s := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact (targetSchemeDiagram I).map_id s.down
  map_comp {s t r} f g := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact (targetSchemeDiagram I).map_comp
      (homOfLE (show s.down ≤ t.down from (leOfHom f : s ≤ t)))
      (homOfLE (show t.down ≤ r.down from (leOfHom g : t ≤ r)))

/-- Every transition map of the target's presentation is a thickening. -/
theorem targetBigAffineDiagram_isThickening {s t : Index I} (f : s ⟶ t) :
    Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B (baseScheme I) (contains_baseScheme B hcard)).map
        ((targetBigAffineDiagram B hcard).map f)) :=
  targetSchemeDiagram_isThickening (homOfLE (show s.down ≤ t.down from (leOfHom f : s ≤ t)))

/-- A stage of the source, as an affine scheme over the base in the big fppf site. -/
def sourceBigAffineObject (hcnt : ∀ a : I, (Set.Iio a).Countable) (b : I) :
    BigAffineFppf B (baseScheme I) (contains_baseScheme B hcard) :=
  ⟨Over.mk (show B.obj (contains_sourceScheme B hcard hcnt b) ⟶
      B.obj (contains_baseScheme B hcard) from
    ObjectProperty.homMk (sourceStructureMap hcnt b)), by
      change IsAffine (Spec (CommRingCat.of (DualStage b)))
      infer_instance⟩

/-- The source's presentation: its directed system of affine schemes over the base, in the big
fppf site. -/
def sourceBigAffineDiagram (hcnt : ∀ a : I, (Set.Iio a).Countable) :
    Index I ⥤ BigAffineFppf B (baseScheme I) (contains_baseScheme B hcard) where
  obj b := sourceBigAffineObject B hcard hcnt b.down
  map {s t} f := ObjectProperty.homMk (Over.homMk
      (ObjectProperty.homMk ((sourceSchemeDiagram hcnt).map
        (homOfLE (show s.down ≤ t.down from (leOfHom f : s ≤ t))))) (by
    apply ObjectProperty.hom_ext
    exact sourceStructureMap_naturality hcnt
      (homOfLE (show s.down ≤ t.down from (leOfHom f : s ≤ t)))))
  map_id s := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact (sourceSchemeDiagram hcnt).map_id s.down
  map_comp {s t r} f g := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact (sourceSchemeDiagram hcnt).map_comp
      (homOfLE (show s.down ≤ t.down from (leOfHom f : s ≤ t)))
      (homOfLE (show t.down ≤ r.down from (leOfHom g : t ≤ r)))

/-- Every transition map of the source's presentation is a thickening. -/
theorem sourceBigAffineDiagram_isThickening (hcnt : ∀ a : I, (Set.Iio a).Countable)
    {s t : Index I} (f : s ⟶ t) :
    Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B (baseScheme I) (contains_baseScheme B hcard)).map
        ((sourceBigAffineDiagram B hcard hcnt).map f)) :=
  sourceSchemeDiagram_isThickening hcnt
    (homOfLE (show s.down ≤ t.down from (leOfHom f : s ≤ t)))

/-! ### The two spaces -/

/-- The target of the morphism: the colimit of the target's presentation. -/
def targetSpace : FppfSheaf B (baseScheme I) (contains_baseScheme B hcard) :=
  colimit (targetBigAffineDiagram B hcard ⋙
    BigAffineFppf.inclusion B (baseScheme I) (contains_baseScheme B hcard) ⋙
    Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B (baseScheme I) (contains_baseScheme B hcard)))

/-- The source of the morphism: the colimit of the source's presentation. -/
def sourceSpace (hcnt : ∀ a : I, (Set.Iio a).Countable) :
    FppfSheaf B (baseScheme I) (contains_baseScheme B hcard) :=
  colimit (sourceBigAffineDiagram B hcard hcnt ⋙
    BigAffineFppf.inclusion B (baseScheme I) (contains_baseScheme B hcard) ⋙
    Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B (baseScheme I) (contains_baseScheme B hcard)))

/-! ### Both colimits are affine formal algebraic spaces -/

/-- A presentation by affine schemes whose rings are all dominated by `Lam I` satisfies the
set-theoretic condition. -/
private theorem satisfiesSetTheoreticCondition_of_mk_le [Nonempty I]
    (D : Index I ⥤ BigAffineFppf B (baseScheme I) (contains_baseScheme B hcard))
    (hD : ∀ ⦃s t : Index I⦄ (f : s ⟶ t), Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B (baseScheme I) (contains_baseScheme B hcard)).map (D.map f)))
    (R : I → Type u) [∀ b, CommRing (R b)] (hR : ∀ b, Cardinal.mk (R b) ≤ Cardinal.mk (Lam I))
    (hobj : ∀ i : Index I, (BigAffineFppf.toScheme B (baseScheme I)
      (contains_baseScheme B hcard)).obj (D.obj i) = Spec (CommRingCat.of (R i.down))) :
    SatisfiesSetTheoreticCondition B (baseScheme I) (contains_baseScheme B hcard)
      (colimit (D ⋙ BigAffineFppf.inclusion B (baseScheme I) (contains_baseScheme B hcard) ⋙
        Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B (baseScheme I) (contains_baseScheme B hcard)))) := by
  refine satisfiesSetTheoreticCondition_of_bounded_colimit B (baseScheme I)
    (contains_baseScheme B hcard) D hD
    (μ := max Cardinal.aleph0.{u} (Cardinal.mk (Lam I)))
    (max_lt B.aleph0_lt_cutoff hcard) ?_ ?_ _ ⟨Iso.refl _⟩
  · rw [Cardinal.mk_uLift]
    exact Cardinal.lift_le.mpr ((mk_index_le_mk_lam I).trans (le_max_right _ _))
  · intro i
    rw [hobj, Scheme.size_Spec]
    exact max_le_max le_rfl (hR i.down)

include hcard in
/-- **Stacks 0AIS for the target.** The uniform bound `max ℵ₀ #(Lam I)` dominates the index and
every stage, so the set-theoretic condition is a theorem. -/
theorem satisfiesSetTheoreticCondition_targetSpace [Nonempty I] :
    SatisfiesSetTheoreticCondition B (baseScheme I) (contains_baseScheme B hcard)
      (targetSpace B hcard) :=
  satisfiesSetTheoreticCondition_of_mk_le B hcard (targetBigAffineDiagram B hcard)
    (fun {_ _} f ↦ targetBigAffineDiagram_isThickening B hcard f) StageRing (mk_stageRing_le ·)
    fun _ ↦ rfl

include hcard in
/-- **Stacks 0AIS for the source**, by the same bound. -/
theorem satisfiesSetTheoreticCondition_sourceSpace [Nonempty I]
    (hcnt : ∀ a : I, (Set.Iio a).Countable) :
    SatisfiesSetTheoreticCondition B (baseScheme I) (contains_baseScheme B hcard)
      (sourceSpace B hcard hcnt) :=
  satisfiesSetTheoreticCondition_of_mk_le B hcard (sourceBigAffineDiagram B hcard hcnt)
    (fun {_ _} f ↦ sourceBigAffineDiagram_isThickening B hcard hcnt f) DualStage (mk_dualStage_le ·)
    fun _ ↦ rfl

include hcard in
/-- **The target is an affine formal algebraic space.** -/
theorem isAffineFormalAlgebraicSpace_targetSpace [Nonempty I] :
    IsAffineFormalAlgebraicSpace B (baseScheme I) (contains_baseScheme B hcard)
      (targetSpace B hcard) :=
  ⟨satisfiesSetTheoreticCondition_targetSpace B hcard, Index I, inferInstance, inferInstance,
    inferInstance, targetBigAffineDiagram B hcard,
    fun {_ _} f ↦ targetBigAffineDiagram_isThickening B hcard f, ⟨Iso.refl _⟩⟩

include hcard in
/-- **The source is an affine formal algebraic space.** -/
theorem isAffineFormalAlgebraicSpace_sourceSpace [Nonempty I]
    (hcnt : ∀ a : I, (Set.Iio a).Countable) :
    IsAffineFormalAlgebraicSpace B (baseScheme I) (contains_baseScheme B hcard)
      (sourceSpace B hcard hcnt) :=
  ⟨satisfiesSetTheoreticCondition_sourceSpace B hcard hcnt, Index I, inferInstance,
    inferInstance, inferInstance, sourceBigAffineDiagram B hcard hcnt,
    fun {_ _} f ↦ sourceBigAffineDiagram_isThickening B hcard hcnt f, ⟨Iso.refl _⟩⟩

end Stacks.Coherent

end
