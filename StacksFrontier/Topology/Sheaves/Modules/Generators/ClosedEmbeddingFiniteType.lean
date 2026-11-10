module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Basis.ModuleFMap

/-!
# Finite type modules and closed embeddings of ringed spaces

Let `i : Z ⟶ X` be a morphism of ringed spaces whose underlying continuous map is a closed
embedding and whose map on structure sheaves is (locally) surjective. Then a sheaf of
`𝒪_Z`-modules is of finite type exactly when its direct image is: pushforward along `i` both
preserves and reflects local generation by finitely many sections.

## Main definitions

* `Stacks.RingedSpace.modulePushforward`: direct image of a sheaf of modules along a morphism
  of ringed spaces.
* `Stacks.RingedSpace.IsFiniteType`: local generation by finitely many sections, in the
  section-and-local-span form the source uses.

## Main results

* `Stacks.RingedSpace.isFiniteType_modulePushforward_iff`: finite type is preserved and
  reflected by pushforward along such a morphism.

## Implementation notes

"Homeomorphism onto a closed subset" is `Topology.IsClosedEmbedding`, and surjectivity of the
structure-sheaf map is `Presheaf.IsLocallySurjective`, which is local surjectivity of the
underlying maps of sets — equivalent to surjectivity on stalks, as the source's proof uses. An
epimorphism of ring-valued sheaves would not suffice.

Finite type is stated here in the source's own terms — near each point there are finitely many
sections, and every section on a smaller open lies locally in their span — rather than through
Mathlib's `SheafOfModules.IsFiniteType`, because local membership is essential: generation as a
sheaf does not give generation of the module of sections over every open.

Sheaves of modules on a ringed space are `AlgebraicGeometry.RingedSpace.ModuleSheaf`, which
ties the space, coefficient and module universes together; the statement is therefore for
`RingedSpace.{u, u}` and `PresheafOfModules.{u}`.

## References

* [Stacks Project, Tag 01C4](https://stacks.math.columbia.edu/tag/01C4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.RingedSpace

/-- The direct image of a sheaf of modules along a morphism of ringed spaces. On an open `U` of
the target its sections are `F(i^{-1} U)`, with scalars restricted along the structure-sheaf
map. -/
@[ega "0 12.2.1" "partial", ega "0 4.2.1"]
noncomputable def modulePushforward {X Z : AlgebraicGeometry.RingedSpace.{u, u}} (i : Z ⟶ X)
    (F : AlgebraicGeometry.RingedSpace.ModuleSheaf Z) :
    AlgebraicGeometry.RingedSpace.ModuleSheaf X where
  toPresheaf := (PresheafOfModules.pushforward
    (Functor.whiskerRight i.hom.c (forget₂ CommRingCat RingCat))).obj F.toPresheaf
  isSheaf := TopCat.Sheaf.pushforward_sheaf_of_sheaf i.hom.base F.isSheaf

private lemma span_pushforward_subset {X Z : AlgebraicGeometry.RingedSpace.{u, u}} (i : Z ⟶ X)
    (F : AlgebraicGeometry.RingedSpace.ModuleSheaf Z) (W : Opens X) (n : ℕ)
    (s : Fin n → (modulePushforward i F).toPresheaf.obj (op W))
    (t : (modulePushforward i F).toPresheaf.obj (op W))
    (ht : t ∈ Submodule.span (X.presheafRing.obj (op W)) (Set.range s)) :
    ((id : (F.toPresheaf.obj (op ((Opens.map i.hom.base).obj W))) →
      (F.toPresheaf.obj (op ((Opens.map i.hom.base).obj W)))) t) ∈
      Submodule.span (Z.presheafRing.obj (op ((Opens.map i.hom.base).obj W)))
        (Set.range fun j => (id : (F.toPresheaf.obj (op ((Opens.map i.hom.base).obj W))) →
          (F.toPresheaf.obj (op ((Opens.map i.hom.base).obj W)))) (s j)) := by
  induction ht using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
  | smul r x hx ih =>
      change ((id : (Z.presheafRing.obj (op ((Opens.map i.hom.base).obj W))) →
          (Z.presheafRing.obj (op ((Opens.map i.hom.base).obj W))))
          ((i.hom.c.app (op W)).hom r)) •
        ((id : (F.toPresheaf.obj (op ((Opens.map i.hom.base).obj W))) →
          (F.toPresheaf.obj (op ((Opens.map i.hom.base).obj W)))) x) ∈ _
      exact Submodule.smul_mem _ _ ih

/-- A sheaf of modules is of finite type if every point has a neighbourhood with finitely many
sections which generate the sheaf there: every section on a smaller open belongs locally to the
span of their restrictions. -/
def IsFiniteType {X : AlgebraicGeometry.RingedSpace.{u, u}}
    (F : AlgebraicGeometry.RingedSpace.ModuleSheaf X) : Prop :=
  ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (n : ℕ)
    (s : Fin n → F.toPresheaf.obj (op U)),
    ∀ (V : Opens X) (hVU : V ≤ U) (t : F.toPresheaf.obj (op V)) (y : X), y ∈ V →
      ∃ (W : Opens X) (hWV : W ≤ V), y ∈ W ∧
        F.toPresheaf.map (homOfLE hWV).op t ∈
          Submodule.span (X.presheafRing.obj (op W))
            (Set.range fun j => F.toPresheaf.map (homOfLE (hWV.trans hVU)).op (s j))

/-- For an inducing map, `V ⊓ f(C)` has preimage `C` whenever `C` lies in the preimage of `V`. -/
private lemma preimage_inf_functorObj {X Z : TopCat} {f : Z ⟶ X} (hf : Topology.IsInducing f)
    (V : Opens X) (C : Opens Z) (h : C ≤ (Opens.map f).obj V) :
    (Opens.map f).obj (V ⊓ hf.functorObj C) = C := by
  ext q
  change (f q ∈ V ∧ f q ∈ hf.functorObj C) ↔ q ∈ C
  rw [hf.mem_functorObj_iff]
  exact ⟨And.right, fun hq => ⟨h hq, hq⟩⟩

/-- Restricting twice along `homOfLE` is restricting along the composite. -/
private lemma map_homOfLE_map_homOfLE {Y : TopCat} {R : (Opens Y)ᵒᵖ ⥤ RingCat.{u}}
    (P : PresheafOfModules.{u} R) {a b c : Opens Y} (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : a ≤ c)
    (x : P.obj (op c)) :
    P.map (homOfLE h₁).op (P.map (homOfLE h₂).op x) = P.map (homOfLE h₃).op x :=
  (P.map_comp_apply _ _ x).symm.trans
    (P.congr_map_apply (congrArg op (Subsingleton.elim _ _)) x)

private theorem isFiniteType_of_pushforward {X Z : AlgebraicGeometry.RingedSpace.{u, u}}
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i.hom.base)
    (F : AlgebraicGeometry.RingedSpace.ModuleSheaf Z)
    (h : IsFiniteType (modulePushforward i F)) : IsFiniteType F := by
  intro z
  obtain ⟨U, hzU, n, s, hs⟩ := h (i.hom.base z)
  let A : Opens Z := (Opens.map i.hom.base).obj U
  have hzA : z ∈ A := hzU
  refine ⟨A, hzA, n, s, ?_⟩
  intro B hBA t y hyB
  let V : Opens X := U ⊓ hi.isInducing.functorObj B
  have hVA : (Opens.map i.hom.base).obj V = B :=
    preimage_inf_functorObj hi.isInducing U B hBA
  let t' : (modulePushforward i F).toPresheaf.obj (op V) :=
    F.toPresheaf.map (eqToHom hVA).op t
  have hyV : y ∈ (Opens.map i.hom.base).obj V := hVA ▸ hyB
  obtain ⟨W, hWV, hyW, hspan⟩ := hs V inf_le_left t' (i.hom.base y) hyV
  let C : Opens Z := (Opens.map i.hom.base).obj W
  have hCB : C ≤ B := by
    rw [← hVA]
    exact fun q hq => hWV hq
  refine ⟨C, hCB, hyW, ?_⟩
  have h' := span_pushforward_subset i F W n
      (fun j => (modulePushforward i F).toPresheaf.map
        (homOfLE (hWV.trans (show V ≤ U from inf_le_left))).op (s j))
      ((modulePushforward i F).toPresheaf.map (homOfLE hWV).op t') hspan
  have h_t :
      ((modulePushforward i F).toPresheaf.map (homOfLE hWV).op) t' =
        F.toPresheaf.map (homOfLE hCB).op t := by
    have hh : (eqToHom hVA).op ≫ ((Opens.map i.hom.base).map (homOfLE hWV)).op =
        (homOfLE hCB).op :=
      congrArg op (Subsingleton.elim
        ((Opens.map i.hom.base).map (homOfLE hWV) ≫ eqToHom hVA) (homOfLE hCB))
    change F.toPresheaf.map ((Opens.map i.hom.base).map (homOfLE hWV)).op
        (F.toPresheaf.map (eqToHom hVA).op t) = _
    exact (F.toPresheaf.map_comp_apply (eqToHom hVA).op
      ((Opens.map i.hom.base).map (homOfLE hWV)).op t).symm.trans
      (F.toPresheaf.congr_map_apply hh t)
  have h_s (j : Fin n) :
      ((modulePushforward i F).toPresheaf.map
        (homOfLE (hWV.trans (show V ≤ U from inf_le_left))).op) (s j) =
      F.toPresheaf.map (homOfLE (show C ≤ A from
        fun q hq => (hWV.trans (show V ≤ U from inf_le_left)) hq)).op (s j) := by
    change F.toPresheaf.map
      ((Opens.map i.hom.base).map
        (homOfLE (hWV.trans (show V ≤ U from inf_le_left)))).op (s j) = _
    exact F.toPresheaf.congr_map_apply (congrArg op (Subsingleton.elim _ _)) (s j)
  rw [h_t] at h'
  simp_rw [h_s] at h'
  exact h'

private lemma locally_span_pushforward
    {X Z : AlgebraicGeometry.RingedSpace.{u, u}} (i : Z ⟶ X)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) i.hom.c]
    (F : AlgebraicGeometry.RingedSpace.ModuleSheaf Z) (W : Opens X) (n : ℕ)
    (s : Fin n → (modulePushforward i F).toPresheaf.obj (op W))
    (t : (modulePushforward i F).toPresheaf.obj (op W))
    (x : X) (hxW : x ∈ W)
    (ht : ((id : (F.toPresheaf.obj (op ((Opens.map i.hom.base).obj W))) →
      (F.toPresheaf.obj (op ((Opens.map i.hom.base).obj W)))) t) ∈
      Submodule.span (Z.presheafRing.obj (op ((Opens.map i.hom.base).obj W)))
        (Set.range fun j => (id : (F.toPresheaf.obj (op ((Opens.map i.hom.base).obj W))) →
          (F.toPresheaf.obj (op ((Opens.map i.hom.base).obj W)))) (s j))) :
    ∃ (V : Opens X) (hVW : V ≤ W), x ∈ V ∧
      (modulePushforward i F).toPresheaf.map (homOfLE hVW).op t ∈
        Submodule.span (X.presheafRing.obj (op V))
          (Set.range fun j => (modulePushforward i F).toPresheaf.map
            (homOfLE hVW).op (s j)) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun
    (Z.presheafRing.obj (op ((Opens.map i.hom.base).obj W)))).mp ht
  have hloc (j : Fin n) :=
    (inferInstance : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology X) i.hom.c).imageSieve_mem (c j) x hxW
  choose Vj ιj hj hxj using hloc
  choose aj haj using hj
  let V : Opens X := W ⊓ ⨅ j : Fin n, Vj j
  have hVW : V ≤ W := inf_le_left
  have hVj (j : Fin n) : V ≤ Vj j :=
    (inf_le_right : V ≤ ⨅ j : Fin n, Vj j).trans (iInf_le _ j)
  have hxV : x ∈ V := ⟨hxW, by simp only [Opens.coe_iInf, Set.mem_iInter]; exact hxj⟩
  refine ⟨V, hVW, hxV, ?_⟩
  let aV (j : Fin n) : X.presheafRing.obj (op V) :=
    X.presheafRing.map (homOfLE (hVj j)).op (aj j)
  have hco (j : Fin n) :
      (i.hom.c.app (op V)).hom (aV j) =
        Z.presheafRing.map ((Opens.map i.hom.base).map (homOfLE hVW)).op (c j) := by
    have hn := i.hom.c.naturality (homOfLE (hVj j)).op
    have hh := ConcreteCategory.congr_hom hn (aj j)
    calc
      _ = (((TopCat.Presheaf.pushforward CommRingCat i.hom.base).obj Z.presheaf).map
            (homOfLE (hVj j)).op).hom ((i.hom.c.app (op (Vj j))).hom (aj j)) := hh
      _ = _ := by
        rw [haj j]
        change (Z.presheafRing.map
          ((Opens.map i.hom.base).map (homOfLE (hVj j))).op)
          ((Z.presheafRing.map ((Opens.map i.hom.base).map (ιj j)).op) (c j)) = _
        let f : (op ((Opens.map i.hom.base).obj W) : (Opens Z)ᵒᵖ) ⟶
            op ((Opens.map i.hom.base).obj (Vj j)) :=
          ((Opens.map i.hom.base).map (ιj j)).op
        let g : (op ((Opens.map i.hom.base).obj (Vj j)) : (Opens Z)ᵒᵖ) ⟶
            op ((Opens.map i.hom.base).obj V) :=
          ((Opens.map i.hom.base).map (homOfLE (hVj j))).op
        have heq : f ≫ g = ((Opens.map i.hom.base).map (homOfLE hVW)).op :=
          congrArg op (Subsingleton.elim _ _)
        calc
          _ = (Z.presheafRing.map f ≫ Z.presheafRing.map g) (c j) :=
            (RingCat.comp_apply _ _ _).symm
          _ = (Z.presheafRing.map (f ≫ g)) (c j) :=
            ConcreteCategory.congr_hom (Z.presheafRing.map_comp f g).symm (c j)
          _ = (Z.presheafRing.map
              ((Opens.map i.hom.base).map (homOfLE hVW)).op) (c j) :=
            ConcreteCategory.congr_hom (congrArg Z.presheafRing.map heq) (c j)
  apply (Submodule.mem_span_range_iff_exists_fun (X.presheafRing.obj (op V))).2
  refine ⟨aV, ?_⟩
  let ρZ := ((Opens.map i.hom.base).map (homOfLE hVW)).op
  have hc' := congrArg
    (fun m : F.toPresheaf.obj (op ((Opens.map i.hom.base).obj W)) =>
      F.toPresheaf.map ρZ m) hc
  simp only [map_sum, F.toPresheaf.map_smul] at hc'
  dsimp only [ρZ] at hc'
  simp_rw [← hco] at hc'
  exact hc'

private lemma pushforward_section_eq_zero_of_preimage_bot
    {X Z : AlgebraicGeometry.RingedSpace.{u, u}} (i : Z ⟶ X)
    (F : AlgebraicGeometry.RingedSpace.ModuleSheaf Z)
    (W : Opens X) (hpre : (Opens.map i.hom.base).obj W = ⊥)
    (t : (modulePushforward i F).toPresheaf.obj (op W)) : t = 0 := by
  let G : TopCat.Sheaf AddCommGrpCat Z := ⟨F.toPresheaf.presheaf, F.isSheaf⟩
  have hsub : Subsingleton ((modulePushforward i F).toPresheaf.obj (op W)) :=
    AddCommGrpCat.subsingleton_of_isZero (G.isTerminalOfEqEmpty hpre).isZero
  exact hsub.elim _ _

private theorem isFiniteType_pushforward_of {X Z : AlgebraicGeometry.RingedSpace.{u, u}}
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i.hom.base)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) i.hom.c]
    (F : AlgebraicGeometry.RingedSpace.ModuleSheaf Z)
    (hF : IsFiniteType F) : IsFiniteType (modulePushforward i F) := by
  intro x
  by_cases hx : x ∈ Set.range i.hom.base
  · obtain ⟨z, rfl⟩ := hx
    obtain ⟨A, hzA, n, s, hs⟩ := hF z
    let U : Opens X := hi.isInducing.functorObj A
    have hUA : (Opens.map i.hom.base).obj U = A := hi.isInducing.map_functorObj A
    have hzU : i.hom.base z ∈ U := (hi.isInducing.mem_functorObj_iff A).mpr hzA
    refine ⟨U, hzU, n, fun j => F.toPresheaf.map (eqToHom hUA).op (s j), ?_⟩
    intro V hVU t y hyV
    by_cases hy : y ∈ Set.range i.hom.base
    · obtain ⟨z', rfl⟩ := hy
      let B : Opens Z := (Opens.map i.hom.base).obj V
      have hBA : B ≤ A := by
        rw [← hUA]
        exact fun q hq => hVU hq
      have hzB : z' ∈ B := hyV
      obtain ⟨C, hCB, hzC, hspan⟩ := hs B hBA t z' hzB
      obtain ⟨W, hWV, hWC, hzW⟩ : ∃ (W : Opens X) (_ : W ≤ V),
          (Opens.map i.hom.base).obj W = C ∧ i.hom.base z' ∈ W := by
        have hWC := preimage_inf_functorObj hi.isInducing V C hCB
        exact ⟨_, inf_le_left, hWC, by rw [← hWC] at hzC; exact hzC⟩
      let tW : (modulePushforward i F).toPresheaf.obj (op W) :=
        (modulePushforward i F).toPresheaf.map (homOfLE hWV).op t
      let sW (j : Fin n) : (modulePushforward i F).toPresheaf.obj (op W) :=
        (modulePushforward i F).toPresheaf.map
          (homOfLE (hWV.trans hVU)).op (F.toPresheaf.map (eqToHom hUA).op (s j))
      have hspanW :
          ((id : F.toPresheaf.obj (op ((Opens.map i.hom.base).obj W)) →
            F.toPresheaf.obj (op ((Opens.map i.hom.base).obj W))) tW) ∈
          Submodule.span (Z.presheafRing.obj (op ((Opens.map i.hom.base).obj W)))
            (Set.range fun j =>
              (id : F.toPresheaf.obj (op ((Opens.map i.hom.base).obj W)) →
              F.toPresheaf.obj (op ((Opens.map i.hom.base).obj W))) (sW j)) := by
        cases hWC
        have h_t : tW = F.toPresheaf.map (homOfLE hCB).op t := by
          change F.toPresheaf.map ((Opens.map i.hom.base).map (homOfLE hWV)).op t = _
          exact F.toPresheaf.congr_map_apply (congrArg op (Subsingleton.elim _ _)) t
        have h_s (j : Fin n) :
            sW j = F.toPresheaf.map (homOfLE (hCB.trans hBA)).op (s j) := by
          have hh : (eqToHom hUA).op ≫
              ((Opens.map i.hom.base).map (homOfLE (hWV.trans hVU))).op =
              (homOfLE (hCB.trans hBA)).op := congrArg op (Subsingleton.elim _ _)
          change F.toPresheaf.map
            ((Opens.map i.hom.base).map (homOfLE (hWV.trans hVU))).op
              (F.toPresheaf.map (eqToHom hUA).op (s j)) = _
          exact (F.toPresheaf.map_comp_apply (eqToHom hUA).op
            ((Opens.map i.hom.base).map (homOfLE (hWV.trans hVU))).op (s j)).symm.trans
            (F.toPresheaf.congr_map_apply hh (s j))
        rw [show ((id : F.toPresheaf.obj (op ((Opens.map i.hom.base).obj W)) →
          F.toPresheaf.obj (op ((Opens.map i.hom.base).obj W))) tW) =
            F.toPresheaf.map (homOfLE hCB).op t from h_t]
        simp_rw [h_s]
        exact hspan
      obtain ⟨W', hW'W, hzW', hspanX⟩ :=
        locally_span_pushforward i F W n sW tW (i.hom.base z') hzW hspanW
      refine ⟨W', hW'W.trans hWV, hzW', ?_⟩
      have h_t :
          (modulePushforward i F).toPresheaf.map (homOfLE (hW'W.trans hWV)).op t =
          (modulePushforward i F).toPresheaf.map (homOfLE hW'W).op tW := by
        have hh : (homOfLE hWV).op ≫ (homOfLE hW'W).op =
            (homOfLE (hW'W.trans hWV)).op := congrArg op (Subsingleton.elim _ _)
        exact ((modulePushforward i F).toPresheaf.congr_map_apply hh.symm t).trans
          ((modulePushforward i F).toPresheaf.map_comp_apply _ _ t)
      have h_s (j : Fin n) :
          (modulePushforward i F).toPresheaf.map
            (homOfLE (hW'W.trans (hWV.trans hVU))).op
            (F.toPresheaf.map (eqToHom hUA).op (s j)) =
          (modulePushforward i F).toPresheaf.map (homOfLE hW'W).op (sW j) := by
        have hh : (homOfLE (hWV.trans hVU)).op ≫ (homOfLE hW'W).op =
            (homOfLE (hW'W.trans (hWV.trans hVU))).op :=
          congrArg op (Subsingleton.elim _ _)
        exact ((modulePushforward i F).toPresheaf.congr_map_apply hh.symm _).trans
          ((modulePushforward i F).toPresheaf.map_comp_apply _ _ _)
      rw [h_t]
      simp_rw [h_s]
      exact hspanX
    · let W : Opens X := V ⊓
        ⟨(Set.range i.hom.base)ᶜ, hi.isClosed_range.isOpen_compl⟩
      have hWV : W ≤ V := inf_le_left
      have hyW : y ∈ W := ⟨hyV, hy⟩
      have hpre : (Opens.map i.hom.base).obj W = ⊥ :=
        le_antisymm (fun z hz => hz.2 ⟨z, rfl⟩) bot_le
      refine ⟨W, hWV, hyW, ?_⟩
      have ht0 := pushforward_section_eq_zero_of_preimage_bot i F W hpre
        ((modulePushforward i F).toPresheaf.map (homOfLE hWV).op t)
      rw [ht0]
      exact Submodule.zero_mem _
  · let U : Opens X := ⟨(Set.range i.hom.base)ᶜ, hi.isClosed_range.isOpen_compl⟩
    have hxU : x ∈ U := hx
    refine ⟨U, hxU, 0, Fin.elim0, ?_⟩
    intro V hVU t y hyV
    refine ⟨V, le_refl V, hyV, ?_⟩
    have hpre : (Opens.map i.hom.base).obj V = ⊥ :=
      le_antisymm (fun z hz => hVU hz ⟨z, rfl⟩) bot_le
    rw [pushforward_section_eq_zero_of_preimage_bot i F V hpre t, map_zero]
    exact Submodule.zero_mem _

/-- **Stacks Project, Tag 01C4.** Pushforward along a closed embedding of ringed spaces with a
surjective map on structure sheaves preserves and reflects finite type sheaves of modules. -/
@[stacks 01C4]
theorem isFiniteType_modulePushforward_iff
    {X Z : AlgebraicGeometry.RingedSpace.{u, u}} (i : Z ⟶ X)
    (hi : Topology.IsClosedEmbedding i.hom.base)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) i.hom.c]
    (F : AlgebraicGeometry.RingedSpace.ModuleSheaf Z) :
    IsFiniteType (modulePushforward i F) ↔ IsFiniteType F :=
  ⟨isFiniteType_of_pushforward i hi F, isFiniteType_pushforward_of i hi F⟩

end Stacks.RingedSpace

end
