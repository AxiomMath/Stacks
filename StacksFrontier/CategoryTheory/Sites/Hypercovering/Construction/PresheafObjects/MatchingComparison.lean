module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.PresheafObjects.LocalPretopology

/-!
# Matching objects and fully faithful functors

The matching cone of a simplicial object in degree `n` and its universal property, the
comparison map between the matching object of a simplicial object and the matching object of
its image under a functor, and the bijection it induces for a fully faithful functor. In degree
one the matching object is a product of two copies of the degree-zero term, handled by
`zeroMatchingLift` and `zeroMatching_hom_ext`.

These are the matching-object ingredients of
`StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.PresheafObjects`.
-/

@[expose] public section

universe w v u q d e

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.CategoryTheory.Hypercovering

attribute [local implicit_reducible] mapFormalCoproduct

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]

section Matching

noncomputable section

universe va ua vb ub

variable {A : Type ua} [Category.{va} A] {D : Type ub} [Category.{vb} D]

open CategoryTheory.SimplicialObject

/-- The cone, over the diagram of lower-degree terms, whose limit is the matching object.

This is definitionally the cone `Functor.RightExtension.coneAt` of the coskeleton viewed as a
right Kan extension, but its point and projections are spelled out here as
`((cosk n).obj L).obj t` and `((cosk n).obj L).map a.hom ≫ counit.app _ |>.app a.right`. The
identification with `coneAt` is therefore discharged once, when `matchingIsLimit` below is
elaborated, instead of being re-checked at every use site: `coneAt` is a definition whose body
this module cannot see, so a projection out of it does not reduce and the defeq checks performed
while rewriting would fail.

`implicit_reducible` rather than an `abbrev`: the projections have to reduce in a defeq check,
but the cone must stay folded for `simp`, or `unit_matching_π` and `zeroMatchingLift_π` below no
longer match their own statements. -/
@[implicit_reducible]
def matchingCone (L : SimplicialObject A) (n : ℕ)
    [∀ F : SimplicialObject.Truncated A n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    (t : SimplexCategoryᵒᵖ) :
    Cone (StructuredArrow.proj t (SimplexCategory.Truncated.inclusion n).op ⋙
      (truncation n).obj L) where
  pt := ((cosk n).obj L).obj t
  π :=
    { app := fun a ↦ ((cosk n).obj L).map a.hom ≫ ((coskAdj n).counit.app _).app a.right
      naturality := fun _ _ φ ↦
        ((Functor.RightExtension.mk ((cosk n).obj L)
          ((coskAdj n).counit.app ((truncation n).obj L))).coneAt t).π.naturality φ }

/-- The matching cone is a limit cone: this is pointwise right Kan extension. -/
def matchingIsLimit (L : SimplicialObject A) (n : ℕ)
    [∀ F : SimplicialObject.Truncated A n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    (t : SimplexCategoryᵒᵖ) : IsLimit (matchingCone L n t) :=
  Functor.isPointwiseRightKanExtensionOfIsRightKanExtension
    ((cosk n).obj L) ((coskAdj n).counit.app _) t

/-- The coskeleton of a morphism of simplicial objects is compatible with the cones computing
the matching objects. -/
lemma coskeleton_map_comp_matchingCone_π {L L' : SimplicialObject A} (f : L ⟶ L') (n : ℕ)
    [∀ F : SimplicialObject.Truncated A n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    (r : SimplexCategoryᵒᵖ)
    (a : StructuredArrow r (SimplexCategory.Truncated.inclusion n).op) :
    ((cosk n).map f).app r ≫ (matchingCone L' n r).π.app a =
      (matchingCone L n r).π.app a ≫ ((truncation n).map f).app a.right := by
  have hnat : ((cosk n).map f).app r ≫ ((cosk n).obj L').map a.hom =
      ((cosk n).obj L).map a.hom ≫
        ((cosk n).map f).app ((SimplexCategory.Truncated.inclusion n).op.obj a.right) :=
    (((cosk n).map f).naturality a.hom).symm
  have h := NatTrans.congr_app ((coskAdj n).counit.naturality
    ((truncation n).map f)) a.right
  change ((cosk n).map f).app ((SimplexCategory.Truncated.inclusion n).op.obj a.right) ≫
      ((coskAdj n).counit.app ((truncation n).obj L')).app a.right =
    ((coskAdj n).counit.app ((truncation n).obj L)).app a.right ≫
      ((truncation n).map f).app a.right at h
  change ((cosk n).map f).app r ≫ (((cosk n).obj L').map a.hom ≫
      ((coskAdj n).counit.app ((truncation n).obj L')).app a.right) =
    (((cosk n).obj L).map a.hom ≫
      ((coskAdj n).counit.app ((truncation n).obj L)).app a.right) ≫
      ((truncation n).map f).app a.right
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k ↦ k ≫ ((coskAdj n).counit.app
        ((truncation n).obj L')).app a.right) hnat).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k ↦ ((cosk n).obj L).map a.hom ≫ k) h).trans
          (Category.assoc _ _ _).symm)))

lemma unit_matching_π (L : SimplicialObject A) (n : ℕ)
    [∀ F : SimplicialObject.Truncated A n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    (t : SimplexCategoryᵒᵖ)
    (a : StructuredArrow t (SimplexCategory.Truncated.inclusion n).op) :
    (((coskAdj n).unit.app L).app t) ≫ (matchingCone L n t).π.app a = L.map a.hom := by
  change (((coskAdj n).unit.app L).app t) ≫
    (((cosk n).obj L).map a.hom ≫ ((coskAdj n).counit.app _).app a.right) = _
  rw [← Category.assoc, ← ((coskAdj n).unit.app L).naturality a.hom,
    Category.assoc]
  have h := NatTrans.congr_app ((coskAdj n).left_triangle_components L) a.right
  change (((coskAdj n).unit.app L).app _) ≫
    (((coskAdj n).counit.app _).app a.right) = 𝟙 _ at h
  change L.map a.hom ≫ _ = _
  rw [h]
  exact Category.comp_id _

/-- The comparison map from the image of a matching object to the matching object of the
image. -/
def matchingComparison (G : A ⥤ D) (L : SimplicialObject A) (n : ℕ)
    [∀ F : SimplicialObject.Truncated A n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    [∀ F : SimplicialObject.Truncated D n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    (t : SimplexCategoryᵒᵖ) :
    G.obj (((cosk n).obj L).obj t) ⟶ ((cosk n).obj (L ⋙ G)).obj t :=
  (matchingIsLimit (L ⋙ G) n t).lift (G.mapCone (matchingCone L n t))

private lemma matchingComparison_π (G : A ⥤ D) (L : SimplicialObject A) (n : ℕ)
    [∀ F : SimplicialObject.Truncated A n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    [∀ F : SimplicialObject.Truncated D n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    (t : SimplexCategoryᵒᵖ)
    (a : StructuredArrow t (SimplexCategory.Truncated.inclusion n).op) :
    matchingComparison G L n t ≫ (matchingCone (L ⋙ G) n t).π.app a =
      G.map ((matchingCone L n t).π.app a) :=
  (matchingIsLimit (L ⋙ G) n t).fac _ a

lemma unit_matchingComparison (G : A ⥤ D) (L : SimplicialObject A) (n : ℕ)
    [∀ F : SimplicialObject.Truncated A n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    [∀ F : SimplicialObject.Truncated D n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    (t : SimplexCategoryᵒᵖ) :
    G.map (((coskAdj n).unit.app L).app t) ≫ matchingComparison G L n t =
      (((coskAdj n).unit.app (L ⋙ G)).app t) := by
  apply (matchingIsLimit (L ⋙ G) n t).hom_ext
  intro a
  rw [Category.assoc, matchingComparison_π, ← G.map_comp, unit_matching_π, unit_matching_π]
  rfl

lemma matchingComparison_injective (G : A ⥤ D) [G.Faithful]
    (L : SimplicialObject A) (n : ℕ)
    [∀ F : SimplicialObject.Truncated A n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    [∀ F : SimplicialObject.Truncated D n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    (t : SimplexCategoryᵒᵖ) {T : A}
    (a b : T ⟶ ((cosk n).obj L).obj t)
    (h : G.map a ≫ matchingComparison G L n t =
      G.map b ≫ matchingComparison G L n t) : a = b := by
  apply (matchingIsLimit L n t).hom_ext
  intro s
  apply G.map_injective
  simpa only [G.map_comp, Category.assoc, matchingComparison_π] using
    congrArg (fun f ↦ f ≫ (matchingCone (L ⋙ G) n t).π.app s) h

/-- **Every map out of an object in the image of a fully faithful functor into the matching
object of the image factors through the matching comparison.**

Together with `matchingComparison_injective` this says that precomposing with
`matchingComparison G L n t` is a *bijection* from `T ⟶ Mₙ(L)ₜ` to `G T ⟶ Mₙ(L ⋙ G)ₜ`.  No
preservation of limits by `G` is involved: a map `G T ⟶ Mₙ(L ⋙ G)ₜ` is a cone on
`G ∘ (truncation n).obj L` with vertex `G T`, its legs are `G` of unique maps by fullness, those
form a cone by faithfulness, and the matching object of `L` is the limit of that diagram. -/
lemma exists_matchingComparison_eq (G : A ⥤ D) (hG : G.FullyFaithful)
    (L : SimplicialObject A) (n : ℕ)
    [∀ F : SimplicialObject.Truncated A n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    [∀ F : SimplicialObject.Truncated D n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    (t : SimplexCategoryᵒᵖ) {T : A} (b : G.obj T ⟶ ((cosk n).obj (L ⋙ G)).obj t) :
    ∃ a : T ⟶ ((cosk n).obj L).obj t, G.map a ≫ matchingComparison G L n t = b := by
  have := hG.faithful
  refine ⟨(matchingIsLimit L n t).lift
    { pt := T
      π :=
        { app := fun s ↦ hG.preimage (b ≫ (matchingCone (L ⋙ G) n t).π.app s)
          naturality := fun s s' φ ↦ ?_ } }, ?_⟩
  · apply G.map_injective
    have h := (matchingCone (L ⋙ G) n t).π.naturality φ
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at h
    simp only [Functor.map_comp, hG.map_preimage, Functor.const_obj_obj, Functor.const_obj_map,
      Category.id_comp]
    rw [h, Category.assoc]
    rfl
  · apply (matchingIsLimit (L ⋙ G) n t).hom_ext
    intro s
    rw [Category.assoc, matchingComparison_π, ← G.map_comp, (matchingIsLimit L n t).fac,
      hG.map_preimage]

/-- The cone exhibiting a pair of maps into degree zero as a map into the degree-one matching
object. -/
@[implicit_reducible]
def zeroMatchingCone (L : SimplicialObject A) {T : A}
    (a b : T ⟶ L.obj (op (SimplexCategory.mk 0))) :
    Cone (StructuredArrow.proj (op (SimplexCategory.mk 1))
      (SimplexCategory.Truncated.inclusion 0).op ⋙ (truncation 0).obj L) where
  pt := T
  π := {
    app := fun s ↦
      let h : s.right.unop.obj = SimplexCategory.mk 0 :=
        SimplexCategory.ext (Nat.eq_zero_of_le_zero s.right.unop.property)
      (if s.hom.unop.toOrderHom 0 = 0 then b else a) ≫ L.map (eqToHom h).op
    naturality := by
      intro s t f
      rcases s with ⟨sl, ⟨⟨⟨m⟩, hm⟩⟩, g⟩
      rcases t with ⟨tl, ⟨⟨⟨n⟩, hn⟩⟩, h⟩
      have em : m = 0 := Nat.eq_zero_of_le_zero hm
      have en : n = 0 := Nat.eq_zero_of_le_zero hn
      subst m n
      have hf : f.right = 𝟙 _ := by
        apply Quiver.Hom.unop_inj
        apply ObjectProperty.hom_ext
        apply SimplexCategory.Hom.ext
        apply DFunLike.ext
        intro x
        change (_ : Fin 1) = _
        exact Subsingleton.elim _ _
      have egh : g = h := by simpa [hf] using (StructuredArrow.w f)
      subst h
      simp [hf] }

def zeroMatchingLift (L : SimplicialObject A)
    [∀ F : SimplicialObject.Truncated A 0,
      (SimplexCategory.Truncated.inclusion 0).op.HasPointwiseRightKanExtension F]
    {T : A} (a b : T ⟶ L.obj (op (SimplexCategory.mk 0))) :
    T ⟶ ((cosk 0).obj L).obj (op (SimplexCategory.mk 1)) :=
  (matchingIsLimit L 0 _).lift (zeroMatchingCone L a b)

lemma zeroMatchingLift_π (L : SimplicialObject A)
    [∀ F : SimplicialObject.Truncated A 0,
      (SimplexCategory.Truncated.inclusion 0).op.HasPointwiseRightKanExtension F]
    {T : A} (a b : T ⟶ L.obj (op (SimplexCategory.mk 0))) (i : Fin 2) :
    zeroMatchingLift L a b ≫ (matchingCone L 0 _).π.app
      (StructuredArrow.mk
        (Y := op (⟨SimplexCategory.mk 0, le_rfl⟩ : SimplexCategory.Truncated 0))
        (SimplexCategory.δ i).op) = if i = 0 then a else b := by
  rw [zeroMatchingLift, IsLimit.fac]
  fin_cases i <;> simp [zeroMatchingCone, SimplexCategory.δ]

/-- The two projections of the degree-one matching object of the zeroth truncation, at the two
face maps `⦋0⦌ ⟶ ⦋1⦌`. -/
abbrev zeroMatchingπ (L : SimplicialObject A)
    [∀ F : SimplicialObject.Truncated A 0,
      (SimplexCategory.Truncated.inclusion 0).op.HasPointwiseRightKanExtension F]
    (i : Fin 2) :
    ((cosk 0).obj L).obj (op (SimplexCategory.mk 1)) ⟶ L.obj (op (SimplexCategory.mk 0)) :=
  (matchingCone L 0 _).π.app
    (StructuredArrow.mk
      (Y := op (⟨SimplexCategory.mk 0, le_rfl⟩ : SimplexCategory.Truncated 0))
      (SimplexCategory.δ i).op)

/-- **A map into the degree-one matching object of the zeroth truncation is determined by its two
faces.**  The structured arrows indexing the matching cone have a degree-zero codomain and a
morphism `⦋0⦌ ⟶ ⦋1⦌`, of which there are exactly the two face maps, so `IsLimit.hom_ext` reduces
to the two projections `zeroMatchingπ`.

This is the converse of what `zeroMatchingLift` supplies, and it is what the reverse transfer of
hypercoverings along a fully faithful functor needs in degree one: there the map into the matching
object is given and its two faces are read off it, rather than the other way round. -/
lemma zeroMatching_hom_ext (L : SimplicialObject A)
    [∀ F : SimplicialObject.Truncated A 0,
      (SimplexCategory.Truncated.inclusion 0).op.HasPointwiseRightKanExtension F]
    {T : A} (x y : T ⟶ ((cosk 0).obj L).obj (op (SimplexCategory.mk 1)))
    (h : ∀ i : Fin 2, x ≫ zeroMatchingπ L i = y ≫ zeroMatchingπ L i) : x = y := by
  apply (matchingIsLimit L 0 _).hom_ext
  rintro ⟨⟨⟩, ⟨⟨⟨m⟩, hm⟩⟩, g⟩
  obtain rfl : m = 0 := Nat.eq_zero_of_le_zero hm
  obtain ⟨i, rfl⟩ : ∃ i : Fin 2, g = (SimplexCategory.δ i).op := by
    have hcases : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
    rcases hcases (g.unop.toOrderHom 0) with hj | hj
    on_goal 1 => refine ⟨1, ?_⟩
    on_goal 2 => refine ⟨0, ?_⟩
    all_goals
      apply Quiver.Hom.unop_inj
      apply SimplexCategory.Hom.ext
      apply DFunLike.ext
      intro z
      obtain rfl : z = 0 := Subsingleton.elim (α := Fin 1) z 0
      rw [hj]
      simp [SimplexCategory.δ]
  exact h i

end

end Matching

end Stacks.CategoryTheory.Hypercovering

end
