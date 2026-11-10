module

public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryEtaleNeighborhoodSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationUniqueLift
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPointsCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPointsEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPointsResidualSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPointsResidualSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedEtaleDiagonalComplementRange
public import StacksFrontier.CategoryTheory.Sites.JointCoverDescent

/-!
# Full faithfulness of the restriction functor of Stacks 0BHA

Let `X` be a decent algebraic space over a scheme `S`, let `x₁, …, xₙ ∈ |X|` be pairwise
distinct closed points and let `(Uᵢ, uᵢ) → (X, xᵢ)` be the chosen elementary étale
neighborhoods. The functor `F` of Stacks 0BHA restricts a modification of `X` away from
`{x₁, …, xₙ}` to the family of its base changes to the `Uᵢ`. Then `F` is fully faithful
(Stacks 0BHB).

## Main definitions

* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.coverPullbackObj`,
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods.coverPullbackHom` and
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods.coverPullbackToSpace`: the base change to a
  modification of the covering of `X` by the complement of the chosen points and the chosen
  neighborhoods, as a family indexed by `Option (Fin n)`, together with its two projections.

## Main results

* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.faithful_restrictionFunctor` and
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods.full_restrictionFunctor`: the functor `F` of
  Stacks 0BHA is faithful, respectively full.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.app_eq_of_coverPullbackHom_app_eq`: a family
  of morphisms into a modification, defined on the members of that covering and each lying over
  `X`, is constant on the fibres of the covering.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.mem_openAwayFromPoints_of_forall`: a section
  of `X` avoiding each chosen point separately avoids all of them;
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods.mem_openAwayFromSinglePoint_toSpaceHom_app`:
  a section of `X` in the image of `U_j` avoids every chosen point other than `x_j`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.sheafify_iSup_range_coverPullbackHom_eq_top`:
  the covering stays jointly covering after base change to an algebraic space over `X`, and
  `exists_diagonalComplement_openAwayFromSinglePoint` in the same namespace: the fibre square
  `Uᵢ ×_X Uᵢ` is covered by the diagonal together with a piece lying over `X ∖ {xᵢ}`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.openComplement_pointSubspace_eq`: the open
  complement of the subspace `{xᵢ}` is `X ∖ {xᵢ}`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.faithful_restrictionFunctor_of_cover` and
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods.full_restrictionFunctor_of_cover`: the same
  two conclusions from those two inputs.

## References

* [Stacks Project, Tag 0BH9](https://stacks.math.columbia.edu/tag/0BH9)
* [Stacks Project, Tag 0BHA](https://stacks.math.columbia.edu/tag/0BHA)
* [Stacks Project, Tag 0BHB](https://stacks.math.columbia.edu/tag/0BHB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

set_option synthInstance.maxHeartbeats 400000 in
-- `inferInstance` for `HasPullbacks` of presheaves on the big fppf site over `S`
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_ModificationsAtClosedPointsFullyFaithful
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site over `S`, as a high-priority shortcut. -/
local instance (priority := high) hasPullback_presheaf_ModificationsAtClosedPointsFullyFaithful
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace ClosedPointNeighborhoods

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {n : ℕ}
  (D : ClosedPointNeighborhoods B S hS n)

/-! ### Sections of `X` which avoid the chosen points -/

/-- A section of `X` which avoids each chosen point separately avoids all of them. -/
theorem mem_openAwayFromPoints_of_forall {A : (BigFppfOver B S hS)ᵒᵖ}
    (t : D.space.obj.obj A) (h : ∀ i, t ∈ (D.openAwayFromSinglePoint i).obj A) :
    t ∈ D.openAwayFromPoints.obj A := by
  rw [openAwayFromPoints, mem_openSubspaceOfPoints_iff]
  intro z hz
  simp only [Set.mem_compl_iff, Set.mem_range, not_exists]
  intro i hi
  have hti := h i
  rw [openAwayFromSinglePoint, mem_openSubspaceOfPoints_iff] at hti
  exact (hti hz) hi.symm

/-- A section of `X` in the image of the `j`th neighborhood avoids every chosen point other
than `x_j`. -/
theorem mem_openAwayFromSinglePoint_toSpaceHom_app {i j : Fin n} (hij : i ≠ j)
    {A : (BigFppfOver B S hS)ᵒᵖ} (v : (D.neighborhoodSpace j).obj.obj A) :
    (D.toSpaceHom j).hom.app A v ∈ (D.openAwayFromSinglePoint i).obj A := by
  obtain ⟨g, hg⟩ := D.exists_factor_openAwayFromSinglePoint hij
  rw [← hg]
  exact (g.app A v).2

/-! ### The covering of a modification -/

section

variable (M : Over D.space.obj)

/-- The base change to `M` of the covering of `X` by the complement of the chosen points and
the chosen neighborhoods. -/
abbrev coverPullbackObj : Option (Fin n) → ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  | none => pullback M.hom D.openAwayFromPoints.ι
  | some i => pullback M.hom (D.toSpaceHom i).hom

/-- The projections of the base-changed covering onto the modification. -/
abbrev coverPullbackHom : ∀ a, D.coverPullbackObj M a ⟶ M.left
  | none => pullback.fst M.hom D.openAwayFromPoints.ι
  | some i => pullback.fst M.hom (D.toSpaceHom i).hom

/-- The structure morphism of a member of the base-changed covering, as a morphism to `X`. -/
abbrev coverPullbackToSpace : ∀ a, D.coverPullbackObj M a ⟶ D.space.obj
  | none => pullback.snd M.hom D.openAwayFromPoints.ι ≫ D.openAwayFromPoints.ι
  | some i => pullback.snd M.hom (D.toSpaceHom i).hom ≫ (D.toSpaceHom i).hom

/-- The two morphisms from a member of the base-changed covering to `X` agree. -/
theorem coverPullbackHom_comp_hom (a : Option (Fin n)) :
    D.coverPullbackHom M a ≫ M.hom = D.coverPullbackToSpace M a := by
  cases a <;> exact pullback.condition

end

/-! ### Constancy on the fibres of the covering -/

variable {D}

/-- **A family of morphisms into a modification which lie over `X` is constant on the fibres of
the base-changed covering.** Two sections of two members with the same image in `M` have the
same image in `M'`. -/
theorem app_eq_of_coverPullbackHom_app_eq {M M' : Over D.space.obj}
    (hM' : IsIso (pullback.snd M'.hom D.openAwayFromPoints.ι))
    (hM'sheaf : Presieve.IsSheaf (BigFppfOver.topology B S hS) M'.left)
    (hdec : ∀ i : Fin n,
      ∃ C : Subfunctor (pullback (D.toSpaceHom i).hom (D.toSpaceHom i).hom),
        (Subfunctor.range (pullback.diagonal (D.toSpaceHom i).hom) ⊔ C).sheafify
            (BigFppfOver.topology B S hS) = ⊤ ∧
          C ≤ (D.openAwayFromSinglePoint i).preimage
            (pullback.fst (D.toSpaceHom i).hom (D.toSpaceHom i).hom ≫ (D.toSpaceHom i).hom))
    (γ : ∀ a, D.coverPullbackObj M a ⟶ M'.left)
    (hγ : ∀ a, γ a ≫ M'.hom = D.coverPullbackToSpace M a)
    (A : (BigFppfOver B S hS)ᵒᵖ) (a b : Option (Fin n))
    (c : (D.coverPullbackObj M a).obj A) (d : (D.coverPullbackObj M b).obj A)
    (h : (D.coverPullbackHom M a).app A c = (D.coverPullbackHom M b).app A d) :
    (γ a).app A c = (γ b).app A d := by
  have hover : ∀ (A' : (BigFppfOver B S hS)ᵒᵖ) (a : Option (Fin n))
      (c : (D.coverPullbackObj M a).obj A'),
      M'.hom.app A' ((γ a).app A' c) = M.hom.app A' ((D.coverPullbackHom M a).app A' c) := by
    intro A' a c
    rw [← NatTrans.comp_app_apply, hγ a, ← coverPullbackHom_comp_hom, NatTrans.comp_app_apply]
  have key : ∀ (A' : (BigFppfOver B S hS)ᵒᵖ) (a b : Option (Fin n))
      (c : (D.coverPullbackObj M a).obj A') (d : (D.coverPullbackObj M b).obj A'),
      (D.coverPullbackHom M a).app A' c = (D.coverPullbackHom M b).app A' d →
      M.hom.app A' ((D.coverPullbackHom M a).app A' c) ∈ D.openAwayFromPoints.obj A' →
      (γ a).app A' c = (γ b).app A' d := by
    intro A' a b c d hcd ht
    refine eq_of_app_eq_of_mem_of_isIso_pullback_snd B S hS M'.hom hM' _ ht _ _
      (hover A' a c) ?_
    rw [hover A' b d, ← hcd]
  have hsnd : ∀ (A' : (BigFppfOver B S hS)ᵒᵖ) {N : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (g : N ⟶ D.space.obj) (e : (pullback M.hom g).obj A'),
      g.app A' ((pullback.snd M.hom g).app A' e) =
        M.hom.app A' ((pullback.fst M.hom g).app A' e) := by
    intro A' N g e
    rw [← NatTrans.comp_app_apply, ← NatTrans.comp_app_apply, pullback.condition]
  have hnone : ∀ (A' : (BigFppfOver B S hS)ᵒᵖ)
      (e : (pullback M.hom D.openAwayFromPoints.ι).obj A'),
      M.hom.app A' ((pullback.fst M.hom D.openAwayFromPoints.ι).app A' e) ∈
        D.openAwayFromPoints.obj A' := by
    intro A' e
    rw [← hsnd]
    exact ((pullback.snd M.hom D.openAwayFromPoints.ι).app A' e).2
  have havoid : ∀ (A' : (BigFppfOver B S hS)ᵒᵖ) (i k : Fin n), k ≠ i →
      ∀ e : (pullback M.hom (D.toSpaceHom i).hom).obj A',
      M.hom.app A' ((pullback.fst M.hom (D.toSpaceHom i).hom).app A' e) ∈
        (D.openAwayFromSinglePoint k).obj A' := by
    intro A' i k hki e
    rw [← hsnd]
    exact D.mem_openAwayFromSinglePoint_toSpaceHom_app hki _
  cases a with
  | none => exact key A none b c d h (hnone A c)
  | some i =>
  cases b with
  | none =>
    refine key A (some i) none c d h ?_
    rw [h]
    exact hnone A d
  | some j =>
    have himg : M.hom.app A ((pullback.fst M.hom (D.toSpaceHom i).hom).app A c) =
        M.hom.app A ((pullback.fst M.hom (D.toSpaceHom j).hom).app A d) := congrArg _ h
    rcases eq_or_ne i j with rfl | hij
    · obtain ⟨C, hCtop, hCle⟩ := hdec i
      have hvv' : (D.toSpaceHom i).hom.app A
            ((pullback.snd M.hom (D.toSpaceHom i).hom).app A c) =
          (D.toSpaceHom i).hom.app A
            ((pullback.snd M.hom (D.toSpaceHom i).hom).app A d) := by
        rwa [hsnd A (D.toSpaceHom i).hom c, hsnd A (D.toSpaceHom i).hom d]
      obtain ⟨s, hs₁, hs₂⟩ := exists_pullback_obj B S hS (D.toSpaceHom i).hom
        (D.toSpaceHom i).hom _ _ hvv'
      have hsieve : (Subfunctor.range (pullback.diagonal (D.toSpaceHom i).hom) ⊔
          C).sieveOfSection s ∈ BigFppfOver.topology B S hS A.unop :=
        show s ∈ ((Subfunctor.range (pullback.diagonal (D.toSpaceHom i).hom) ⊔
          C).sheafify (BigFppfOver.topology B S hS)).obj A by rw [hCtop]; trivial
      refine (hM'sheaf _ hsieve).isSeparatedFor.ext fun Z g hg ↦ ?_
      rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
      have hfst : (pullback.fst (D.toSpaceHom i).hom (D.toSpaceHom i).hom).app (op Z)
            ((pullback (D.toSpaceHom i).hom (D.toSpaceHom i).hom).map g.op s) =
          (D.neighborhoodSpace i).obj.map g.op
            ((pullback.snd M.hom (D.toSpaceHom i).hom).app A c) := by
        rw [NatTrans.naturality_apply, hs₁]
      have hsndg : (pullback.snd (D.toSpaceHom i).hom (D.toSpaceHom i).hom).app (op Z)
            ((pullback (D.toSpaceHom i).hom (D.toSpaceHom i).hom).map g.op s) =
          (D.neighborhoodSpace i).obj.map g.op
            ((pullback.snd M.hom (D.toSpaceHom i).hom).app A d) := by
        rw [NatTrans.naturality_apply, hs₂]
      have hrestr : (pullback.fst M.hom (D.toSpaceHom i).hom).app (op Z)
            ((pullback M.hom (D.toSpaceHom i).hom).map g.op c) =
          (pullback.fst M.hom (D.toSpaceHom i).hom).app (op Z)
            ((pullback M.hom (D.toSpaceHom i).hom).map g.op d) := by
        rw [NatTrans.naturality_apply (pullback.fst M.hom (D.toSpaceHom i).hom) g.op c,
          NatTrans.naturality_apply (pullback.fst M.hom (D.toSpaceHom i).hom) g.op d]
        exact congrArg (M.left.map g.op) h
      rcases hg with hΔ | hC
      · obtain ⟨w, hw⟩ := hΔ
        have hcd : (pullback M.hom (D.toSpaceHom i).hom).map g.op c =
            (pullback M.hom (D.toSpaceHom i).hom).map g.op d :=
          pullback_obj_ext M.hom (D.toSpaceHom i).hom (op Z) _ _ hrestr
            (by rw [NatTrans.naturality_apply (pullback.snd M.hom (D.toSpaceHom i).hom) g.op c,
              NatTrans.naturality_apply (pullback.snd M.hom (D.toSpaceHom i).hom) g.op d,
              ← hfst, ← hsndg, ← hw, ← NatTrans.comp_app_apply, ← NatTrans.comp_app_apply,
              pullback.diagonal_fst, pullback.diagonal_snd])
        exact congrArg ((γ (some i)).app (op Z)) hcd
      · have hmem : (pullback.fst (D.toSpaceHom i).hom (D.toSpaceHom i).hom ≫
              (D.toSpaceHom i).hom).app (op Z)
              ((pullback (D.toSpaceHom i).hom (D.toSpaceHom i).hom).map g.op s) ∈
            (D.openAwayFromSinglePoint i).obj (op Z) := hCle _ hC
        rw [NatTrans.comp_app_apply, hfst] at hmem
        have hgoal : M.hom.app (op Z) ((pullback.fst M.hom (D.toSpaceHom i).hom).app (op Z)
            ((pullback M.hom (D.toSpaceHom i).hom).map g.op c)) ∈
              D.openAwayFromPoints.obj (op Z) := by
          refine D.mem_openAwayFromPoints_of_forall _ fun k ↦ ?_
          rcases eq_or_ne k i with rfl | hki
          · rw [← hsnd (op Z), NatTrans.naturality_apply (pullback.snd M.hom _) g.op c]
            exact hmem
          · exact havoid _ i k hki _
        exact key (op Z) (some i) (some i) _ _ hrestr hgoal
    · have hgoal : M.hom.app A ((pullback.fst M.hom (D.toSpaceHom i).hom).app A c) ∈
          D.openAwayFromPoints.obj A := by
        refine D.mem_openAwayFromPoints_of_forall _ fun k ↦ ?_
        rcases eq_or_ne k i with rfl | hki
        · rw [himg]
          exact havoid A j k hij d
        · exact havoid A i k hki c
      exact key A (some i) (some j) c d h hgoal

/-! ### Full faithfulness of the functor of Stacks 0BHA -/

variable (D)

/-- The underlying presheaf of the `i`th component of the functor of Stacks 0BHA at a
modification is the fibre product of that modification with the `i`th neighborhood. -/
theorem restrictionFunctor_obj_obj_left (i : Fin n) (Z : D.modificationsAwayFromPoints) :
    (D.restrictionFunctor.obj Z i).obj.left = pullback Z.obj.hom (D.toSpaceHom i).hom := rfl

/-- The `i`th component of a morphism in the target of the functor of Stacks 0BHA, read as a
morphism of fibre products. -/
def componentLeft {Z W : D.modificationsAwayFromPoints}
    (Φ : D.restrictionFunctor.obj Z ⟶ D.restrictionFunctor.obj W) (i : Fin n) :
    pullback Z.obj.hom (D.toSpaceHom i).hom ⟶ pullback W.obj.hom (D.toSpaceHom i).hom :=
  (Φ i).hom.left

/-- The `i`th component of a morphism in the target of the functor of Stacks 0BHA lies over the
`i`th neighborhood. -/
theorem componentLeft_comp_snd {Z W : D.modificationsAwayFromPoints}
    (Φ : D.restrictionFunctor.obj Z ⟶ D.restrictionFunctor.obj W) (i : Fin n) :
    D.componentLeft Φ i ≫ pullback.snd W.obj.hom (D.toSpaceHom i).hom =
      pullback.snd Z.obj.hom (D.toSpaceHom i).hom :=
  Over.w (Φ i).hom

/-- The `i`th component of the image of a morphism of modifications under the functor of
Stacks 0BHA is the base change of that morphism. -/
theorem restrictionFunctor_map_eq {Z W : D.modificationsAwayFromPoints} (φ : Z ⟶ W) (i : Fin n) :
    D.componentLeft (D.restrictionFunctor.map φ) i =
      pullback.lift (pullback.fst Z.obj.hom (D.toSpaceHom i).hom ≫ φ.hom.left)
        (pullback.snd Z.obj.hom (D.toSpaceHom i).hom) (by simp [pullback.condition]) := rfl

/-- The base change of a morphism of modifications, composed with the projection, is the
projection composed with the morphism. -/
theorem restrictionFunctor_map_comp_fst {Z W : D.modificationsAwayFromPoints} (φ : Z ⟶ W)
    (i : Fin n) :
    D.componentLeft (D.restrictionFunctor.map φ) i ≫
        pullback.fst W.obj.hom (D.toSpaceHom i).hom =
      pullback.fst Z.obj.hom (D.toSpaceHom i).hom ≫ φ.hom.left := by
  rw [D.restrictionFunctor_map_eq φ i, pullback.lift_fst]

/-- Two morphisms of modifications agree after base change to the complement of the chosen
points. -/
theorem fst_comp_hom_left_eq {Z W : D.modificationsAwayFromPoints} (φ ψ : Z ⟶ W) :
    pullback.fst Z.obj.hom D.openAwayFromPoints.ι ≫ φ.hom.left =
      pullback.fst Z.obj.hom D.openAwayFromPoints.ι ≫ ψ.hom.left := by
  refine lift_eq_of_isIso_pullback_snd B S hS W.obj.hom W.property.2
    (pullback.snd Z.obj.hom D.openAwayFromPoints.ι) _ _ ?_ ?_ <;>
    rw [Category.assoc, Over.w, pullback.condition]

/-- **The functor `F` of Stacks 0BHA is faithful**, given that the covering of `X` by the
complement of the chosen points and the chosen neighborhoods stays jointly covering after base
change to a modification. -/
theorem faithful_restrictionFunctor_of_cover
    (hcov : ∀ M : Over D.space.obj,
      (⨆ a, Subfunctor.range (D.coverPullbackHom M a)).sheafify
        (BigFppfOver.topology B S hS) = ⊤) :
    D.restrictionFunctor.Faithful where
  map_injective {Z W} φ ψ hφψ := by
    refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
    refine Presheaf.hom_ext_of_sheafify_iSup_range_eq_top _ (D.coverPullbackHom Z.obj)
      (hcov Z.obj) ((isSheaf_iff_isSheaf_of_type _ _).1 W.property.1.isSheaf) fun a ↦ ?_
    cases a with
    | none => exact D.fst_comp_hom_left_eq φ ψ
    | some i =>
      have h := congrArg
        (fun Φ ↦ D.componentLeft Φ i ≫ pullback.fst W.obj.hom (D.toSpaceHom i).hom) hφψ
      rwa [D.restrictionFunctor_map_comp_fst φ i, D.restrictionFunctor_map_comp_fst ψ i] at h

/-- **The functor `F` of Stacks 0BHA is full**, given the same covering property together with
the decomposition of each `Uᵢ ×_X Uᵢ` into the diagonal and its complement. -/
theorem full_restrictionFunctor_of_cover
    (hcov : ∀ M : Over D.space.obj,
      (⨆ a, Subfunctor.range (D.coverPullbackHom M a)).sheafify
        (BigFppfOver.topology B S hS) = ⊤)
    (hdec : ∀ i : Fin n,
      ∃ C : Subfunctor (pullback (D.toSpaceHom i).hom (D.toSpaceHom i).hom),
        (Subfunctor.range (pullback.diagonal (D.toSpaceHom i).hom) ⊔ C).sheafify
            (BigFppfOver.topology B S hS) = ⊤ ∧
          C ≤ (D.openAwayFromSinglePoint i).preimage
            (pullback.fst (D.toSpaceHom i).hom (D.toSpaceHom i).hom ≫ (D.toSpaceHom i).hom)) :
    D.restrictionFunctor.Full where
  map_surjective {Z W} Φ := by
    obtain ⟨γ₀, hγ₀⟩ := exists_lift_of_isIso_pullback_snd B S hS W.obj.hom W.property.2
      (pullback.fst Z.obj.hom D.openAwayFromPoints.ι ≫ Z.obj.hom)
      (pullback.snd Z.obj.hom D.openAwayFromPoints.ι) pullback.condition.symm
    let γ : ∀ a, D.coverPullbackObj Z.obj a ⟶ W.obj.left := fun a ↦
      match a with
      | none => γ₀
      | some i => D.componentLeft Φ i ≫ pullback.fst W.obj.hom (D.toSpaceHom i).hom
    have hγ : ∀ a, γ a ≫ W.obj.hom = D.coverPullbackToSpace Z.obj a := by
      intro a
      cases a with
      | none => exact hγ₀.trans pullback.condition
      | some i =>
        change (D.componentLeft Φ i ≫ pullback.fst W.obj.hom (D.toSpaceHom i).hom) ≫
          W.obj.hom = _
        rw [Category.assoc, pullback.condition, ← Category.assoc,
          D.componentLeft_comp_snd Φ i]
    have hWsheaf := (isSheaf_iff_isSheaf_of_type _ _).1 W.property.1.isSheaf
    obtain ⟨φ, hφ, -⟩ := Presheaf.existsUnique_hom_of_sheafify_iSup_range_eq_top _
      (D.coverPullbackHom Z.obj) (hcov Z.obj) hWsheaf γ
      (app_eq_of_coverPullbackHom_app_eq W.property.2 hWsheaf hdec γ hγ)
    have hover : φ ≫ W.obj.hom = Z.obj.hom := by
      refine Presheaf.hom_ext_of_sheafify_iSup_range_eq_top _ (D.coverPullbackHom Z.obj)
        (hcov Z.obj) ((isSheaf_iff_isSheaf_of_type _ _).1 D.space.property.isSheaf) fun a ↦ ?_
      rw [← Category.assoc, hφ a, hγ a, coverPullbackHom_comp_hom]
    refine ⟨ObjectProperty.homMk (Over.homMk φ hover), ?_⟩
    funext i
    refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
    change D.componentLeft
      (D.restrictionFunctor.map (ObjectProperty.homMk (Over.homMk φ hover))) i = D.componentLeft Φ i
    rw [D.restrictionFunctor_map_eq]
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst]
      exact hφ (some i)
    · rw [pullback.lift_snd, D.componentLeft_comp_snd Φ i]

/-! ### Discharging the two inputs -/

/-- The covering of `X` by the complement of the chosen points and the chosen neighborhoods,
base changed to an algebraic space over `X`, is jointly covering. -/
theorem sheafify_iSup_range_coverPullbackHom_eq_top (M : Over D.space.obj) :
    (⨆ a, Subfunctor.range (D.coverPullbackHom M a)).sheafify
      (BigFppfOver.topology B S hS) = ⊤ := by
  have heq : (⨆ a, Subfunctor.range (D.coverPullbackHom M a)) =
      ⨆ a, Subfunctor.range (pullback.fst M.hom (D.coverHom a)) := by
    refine iSup_congr fun a ↦ ?_
    cases a <;> rfl
  rw [heq]
  exact D.sheafify_iSup_range_pullback_fst_coverHom_eq_top M.hom

/-- The open complement of the subspace `{xᵢ}` is contained in the open subspace
`X ∖ {xᵢ}`. -/
theorem openComplement_pointSubspace_le (i : Fin n) :
    openComplement B S hS (D.pointSubspace i) ≤ D.openAwayFromSinglePoint i := by
  refine le_of_range_pointsMap_ι_subset B S hS
    (D.isOpenSubspace_openAwayFromSinglePoint i) ?_
  rw [range_pointsMap_ι_openComplement, D.range_pointsMap_ι_pointSubspace i,
    D.range_pointsMap_ι_openAwayFromSinglePoint i]

/-- **The open complement of the subspace `{xᵢ}` is the open subspace `X ∖ {xᵢ}`.** -/
theorem openComplement_pointSubspace_eq (i : Fin n) :
    openComplement B S hS (D.pointSubspace i) = D.openAwayFromSinglePoint i := by
  refine le_antisymm (D.openComplement_pointSubspace_le i)
    (le_of_range_pointsMap_ι_subset B S hS
      (isOpenSubspace_openComplement B S hS D.space.property (D.pointSubspace i)
        (D.isClosedSubspace_pointSubspace i)) ?_)
  rw [range_pointsMap_ι_openComplement, D.range_pointsMap_ι_pointSubspace i,
    D.range_pointsMap_ι_openAwayFromSinglePoint i]

/-- The fibre square `Uᵢ ×_X Uᵢ` is covered by the diagonal together with a subfunctor lying
over `X ∖ {xᵢ}`. -/
theorem exists_diagonalComplement_openAwayFromSinglePoint (i : Fin n) :
    ∃ C : Subfunctor (pullback (D.toSpaceHom i).hom (D.toSpaceHom i).hom),
      (Subfunctor.range (pullback.diagonal (D.toSpaceHom i).hom) ⊔ C).sheafify
          (BigFppfOver.topology B S hS) = ⊤ ∧
        C ≤ (D.openAwayFromSinglePoint i).preimage
          (pullback.fst (D.toSpaceHom i).hom (D.toSpaceHom i).hom ≫ (D.toSpaceHom i).hom) := by
  obtain ⟨C, hCtop, hCfst, -⟩ := exists_subfunctor_sheafify_sup_range_diagonal_eq_top B S hS
    (D.neighborhoodSpace i).property D.space.property (D.toSpaceHom i).hom
    (D.neighborhood i).etale_toSpace (D.isSeparated_toSpaceHom i) (D.pointSubspace i)
    (D.isIso_fromPreimage_pointSubspace i)
  exact ⟨C, hCtop, fun A x hx ↦ D.openComplement_pointSubspace_le i A (hCfst A hx)⟩

/-! ### Stacks 0BHB: the functor of Stacks 0BHA is fully faithful -/

/-- **The functor `F` of Stacks 0BHA is faithful.** A morphism of modifications of `X` away
from `{x₁, …, xₙ}` is determined by its base changes to the chosen neighborhoods. -/
theorem faithful_restrictionFunctor : D.restrictionFunctor.Faithful :=
  D.faithful_restrictionFunctor_of_cover D.sheafify_iSup_range_coverPullbackHom_eq_top

/-- **The functor `F` of Stacks 0BHA is full.** A family of morphisms between the base changes
to the chosen neighborhoods glues to a morphism of modifications. -/
theorem full_restrictionFunctor : D.restrictionFunctor.Full :=
  D.full_restrictionFunctor_of_cover D.sheafify_iSup_range_coverPullbackHom_eq_top
    D.exists_diagonalComplement_openAwayFromSinglePoint

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
