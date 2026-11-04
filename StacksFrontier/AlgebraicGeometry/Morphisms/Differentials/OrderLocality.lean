module

public import StacksFrontier.AlgebraicGeometry.Morphisms.DifferentialsAndValuative.AffineDifferentialOperators

/-!
# Locality of the order of a differential operator on the base

The order of a differential operator between sheaves of modules on a topological space is a
local condition on the base: a global operator which commutes with restriction of sections is
a differential operator of order at most `k` as soon as its restriction to each member of an
open cover is. For schemes this says that the order of a differential operator on `X/Y` may be
checked on any open cover of `X`, in particular on a cover by affine opens.

## Main results

* `DiffOp.isGlobalDiffOpOfOrder_of_cover`: the order of a natural global operator between
  sheaves of modules on a topological space is local on an arbitrary open cover.
* `DiffOp.isGlobalDiffOpOfOrder_iff_cover`: the same statement as an equivalence.
* `AlgebraicGeometry.isGlobalDiffOpOfOrder_of_cover`: the order of a differential operator on
  `X/Y` is local on an arbitrary open cover of `X`.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace DiffOp

variable {X : TopCat.{u}} {O O' : TopCat.Sheaf RingCat.{u} X} {F G : SheafOfModules.{u} O'}

/-- A morphism of sheaves of rings commutes with restriction of sections. -/
theorem sectionRingHom_naturality {C : Type*} [Category C] {J : GrothendieckTopology C}
    {P Q : Sheaf J RingCat} (φ : P ⟶ Q) {U V : Cᵒᵖ} (i : U ⟶ V) (a : P.obj.obj U) :
    Q.obj.map i (sectionRingHom φ U a) = sectionRingHom φ V (P.obj.map i a) :=
  (NatTrans.naturality_apply ((sheafToPresheaf J RingCat).map φ) i a).symm

/-- A global operator compatible with restriction over the whole space is compatible with
restriction over every open. -/
theorem GlobalOp.isNatural_restrict (D : GlobalOp F G) (hD : (D.restrict ⊤).IsNatural)
    (U : Opens X) : (D.restrict U).IsNatural := fun Y Y' h s ↦
  hD (Over.mk (homOfLE (le_top : Y.left ≤ ⊤))) (Over.mk (homOfLE (le_top : Y'.left ≤ ⊤)))
    (Over.homMk h.left (Subsingleton.elim _ _)) s

/-- Linearity over the sheaf of rings `O` of a natural global operator is a local condition on
an open cover of the space. -/
theorem GlobalOp.isO1Linear_of_cover (φ : O ⟶ O') (D : GlobalOp F G)
    (hnat : (D.restrict ⊤).IsNatural) {ι : Type*} (B : ι → Opens X)
    (hB : ∀ p : X, ∃ i, p ∈ B i) (hb : ∀ i, (D.restrict (B i)).IsO1Linear φ) (U : Opens X) :
    (D.restrict U).IsO1Linear φ := by
  intro Y a s
  refine TopCat.Presheaf.IsSheaf.section_ext (F := G.val.presheaf) G.isSheaf fun p hp ↦ ?_
  obtain ⟨i, hi⟩ := hB p
  refine ⟨Y.left ⊓ B i, inf_le_left, ⟨hp, hi⟩, ?_⟩
  have hle : Y.left ⊓ B i ≤ Y.left := inf_le_left
  have key : ∀ t : F.val.obj (op Y.left),
      G.val.presheaf.map (homOfLE hle).op (D (op Y.left) t) =
        D (op (Y.left ⊓ B i))
          (F.val.presheaf.map (homOfLE hle).op t) :=
    fun t ↦ (hnat (Over.mk (homOfLE (le_top : Y.left ⊓ B i ≤ ⊤)))
      (Over.mk (homOfLE (le_top : Y.left ≤ ⊤)))
      (Over.homMk (homOfLE hle)
        (Subsingleton.elim _ _)) t).symm
  have hsmul : ∀ (M : SheafOfModules.{u} O') (t : M.val.obj (op Y.left)),
      M.val.presheaf.map (homOfLE hle).op
          (sectionRingHom φ (op Y.left) a • t) =
        sectionRingHom φ (op (Y.left ⊓ B i))
            (O.obj.map (homOfLE hle).op a) •
          M.val.presheaf.map (homOfLE hle).op t :=
    fun M t ↦ (AlgebraicGeometry.AffineDiffOp.presheaf_map_smul M.val _ _ t).trans
      (congrArg
        (fun r ↦ r • M.val.presheaf.map (homOfLE hle).op t)
        (sectionRingHom_naturality φ _ a))
  exact ((key _).trans ((congrArg (fun t ↦ D (op (Y.left ⊓ B i)) t) (hsmul F s)).trans
    (hb i (Over.mk (homOfLE (inf_le_right : Y.left ⊓ B i ≤ B i))) _ _))).trans
      ((hsmul G (D (op Y.left) s)).trans
        (congrArg (fun t ↦ sectionRingHom φ (op (Y.left ⊓ B i))
          (O.obj.map (homOfLE hle).op a) • t) (key s))).symm

/-- The opens contained in some member of an open cover form a basis of the topology, indexed
by the pairs consisting of a member of the cover and an open contained in it. -/
theorem isBasis_coverSubsets {ι : Type*} (B : ι → Opens X) (hB : ∀ p : X, ∃ i, p ∈ B i) :
    Opens.IsBasis (Set.range (fun q : (i : ι) × {W : Opens X // W ≤ B i} ↦ q.2.1)) := by
  refine Opens.isBasis_iff_nbhd.2 fun {V x} hx ↦ ?_
  obtain ⟨i, hi⟩ := hB x
  exact ⟨V ⊓ B i, ⟨⟨i, ⟨V ⊓ B i, inf_le_right⟩⟩, rfl⟩, ⟨hx, hi⟩, inf_le_left⟩

/-- A global operator between sheaves of modules which commutes with restriction of sections is
a differential operator of order at most `k` as soon as its restriction to each member of an
arbitrary open cover is one. -/
theorem isGlobalDiffOpOfOrder_of_cover (φ : O ⟶ O')
    (hcomm : ∀ (V : (Opens X)ᵒᵖ) (r s : O'.obj.obj V), r * s = s * r) {k : ℕ} {ι : Type*}
    (B : ι → Opens X) (hB : ∀ p : X, ∃ i, p ∈ B i) (D : GlobalOp F G)
    (hnat : (D.restrict ⊤).IsNatural) (hb : ∀ i, IsDiffOpOfOrder φ k (D.restrict (B i))) :
    IsGlobalDiffOpOfOrder φ k D := by
  intro U
  have hU := D.isNatural_restrict hnat U
  refine AlgebraicGeometry.AffineDiffOp.rawOrder_of_sections φ hcomm (D.restrict U) hU ?_ ?_
  · exact D.isO1Linear_of_cover φ hnat B hB
      (fun i ↦ RawOp.isO1Linear_of_isDiffOpOfOrder φ k _ (hb i)) U
  · exact AlgebraicGeometry.AffineDiffOp.rawOrder_of_basic _ (isBasis_coverSubsets B hB)
      (D.restrict U) hU fun q _ ↦
        AlgebraicGeometry.AffineDiffOp.rawOrder_section φ (D.restrict (B q.1)) (hb q.1)
          (Over.mk (homOfLE q.2.2))

/-- The order of a natural global operator between sheaves of modules is local on an arbitrary
open cover: it is a differential operator of order at most `k` if and only if its restriction
to each member of the cover is. -/
theorem isGlobalDiffOpOfOrder_iff_cover (φ : O ⟶ O')
    (hcomm : ∀ (V : (Opens X)ᵒᵖ) (r s : O'.obj.obj V), r * s = s * r) {k : ℕ} {ι : Type*}
    (B : ι → Opens X) (hB : ∀ p : X, ∃ i, p ∈ B i) (D : GlobalOp F G)
    (hnat : (D.restrict ⊤).IsNatural) :
    IsGlobalDiffOpOfOrder φ k D ↔ ∀ i, IsDiffOpOfOrder φ k (D.restrict (B i)) :=
  ⟨fun h i ↦ h (B i), isGlobalDiffOpOfOrder_of_cover φ hcomm B hB D hnat⟩

end DiffOp

namespace AlgebraicGeometry

/-- A global operator between sheaves of modules on a scheme `X` which commutes with restriction
of sections is a differential operator of order at most `k` on `X/Y` as soon as its restriction
to each member of an arbitrary open cover of `X` is one. -/
theorem isGlobalDiffOpOfOrder_of_cover {X Y : Scheme.{u}} (f : X ⟶ Y) (k : ℕ)
    {F G : X.Modules} {ι : Type*} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (D : DiffOp.GlobalOp F G) (hnat : (D.restrict ⊤).IsNatural)
    (hD : ∀ i, DiffOp.IsDiffOpOfOrder f.relativeStructureSheafMap k (D.restrict (U i))) :
    DiffOp.IsGlobalDiffOpOfOrder f.relativeStructureSheafMap k D :=
  DiffOp.isGlobalDiffOpOfOrder_of_cover _ (fun V r s ↦ mul_comm (G := Γ(X, V.unop)) r s) U
    (fun p ↦ Opens.mem_iSup.1 (hU ▸ Opens.mem_top p)) D hnat hD

end AlgebraicGeometry

end
