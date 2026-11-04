module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfUniversallyClosedSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdeals
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentExtension

/-!
# The ideal of an affine thickening on an affine chart, as a directed union

Let `j : P ⟶ W` be a surjective closed immersion of algebraic spaces with `P` affine. This file
collects the facts about `W` needed to write the ideal of `P` on an affine étale chart of `W` as a
directed union of finitely generated invariant ideals (Stacks 0829 on charts,
`chartExtensionProperty_id`):

* `isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isClosedImmersion`: `W` is quasi-compact
  and quasi-separated: an affine algebraic space is quasi-compact and separated (Stacks 08GR),
  quasi-compactness passes to the target of a surjection (Stacks 040W) and separatedness to the
  target of a surjective universally closed morphism (Stacks 05Z2); a closed immersion is integral,
  hence universally closed.
* `exists_fg_invariant_submodule_of_qcqs`: on a qcqs algebraic space, finitely many sections of a
  quasi-coherent module over an affine chart lie in a finitely generated submodule whose two
  pullbacks along a pair of chart maps agree.
* `exists_directed_fg_invariant_ideals`: on a qcqs algebraic space, the defining ideal of a closed
  subspace on an affine chart is a directed union of finitely generated ideals whose extensions
  along a pair of maps of affine charts agree.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The target of a surjective closed immersion with affine source is quasi-compact and
quasi-separated.** -/
theorem isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isClosedImmersion
    {P W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (j : P ⟶ W) (hP : IsAlgebraicSpace B S hS P)
    (hW : IsAlgebraicSpace B S hS W) (hj : IsClosedImmersion B S hS j)
    (hsurj : IsSurjective B S hS j) (haff : IsAffineSpace B S hS P) :
    IsQuasiCompactSpace B S hS W ∧
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal W := by
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  let Ps : AlgebraicSpaces B S hS := ⟨P, hP⟩
  let V : SpacesEtale B S hS Ps := ⟨Over.mk (𝟙 Ps), fun U φ hφ ↦ hφ⟩
  have hPqcsep : IsQuasiCompactSeparated B S hS hZ P :=
    isQuasiCompactSeparated_of_isAffineSpace B S hS hZ Ps V haff
  have hclosed : UniversallyClosed B S hS j :=
    universallyClosed_of_isIntegralHom B S hS hP hW (isIntegralHom_of_isClosedImmersion B S hS j hj)
  refine ⟨IsQuasiCompactSpace.of_isSurjective B S hS hP hW hsurj hPqcsep.1, ?_⟩
  exact isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS hZ W
    (isAbsolutelySeparated_of_isSurjective_of_universallyClosed B S hS hZ hP hW j hsurj
      hclosed hPqcsep.2)

variable {B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
  {F : Modules.{u, u} B S hS X hX}

/-- **Finitely many sections of a quasi-coherent module over an affine chart of a qcqs algebraic
space lie in a finitely generated submodule whose two pullbacks to an affine chart over it agree**
(Stacks 0829 on charts). For `g₁, g₂ : T₂ ⟶ T` the spans of the restrictions of the submodule
along `g₁` and along `g₂` coincide: both are the sections over `T₂` of one finite type
quasi-coherent submodule of `F`. -/
theorem exists_fg_invariant_submodule_of_qcqs (hqc : IsQuasiCompactSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X)
    (hF : IsCartesianOnAffineCharts F) {T T₂ : SmallEtale B S hS X}
    (hT : IsAffine (chartScheme T)) (hT₂ : IsAffine (chartScheme T₂)) (g₁ g₂ : T₂ ⟶ T)
    (s : Finset (F.val.obj (Opposite.op T))) :
    ∃ M : Submodule (chartRing B S hS X hX T) (F.val.obj (Opposite.op T)), M.FG ∧
      (s : Set (F.val.obj (Opposite.op T))) ⊆ M ∧
      Submodule.span (chartRing B S hS X hX T₂) (chartRes F g₁ '' (M : Set _)) =
        Submodule.span (chartRing B S hS X hX T₂) (chartRes F g₂ '' (M : Set _)) := by
  obtain ⟨D, hD⟩ := (chartExtensionProperty_id B.contains_terminal hqc hqs hF).exists_forall_mem
    hF s (fun _ => T) (fun _ => T.1.hom) (fun _ => Category.comp_id _) (fun _ => hT) id
  refine ⟨D.obj T T.1.hom (Category.comp_id _), D.fg_obj hF hT _ _, fun x hx => hD x hx, ?_⟩
  rw [← D.obj_eq_span hF hT hT₂ g₁ T.1.hom (Category.comp_id _),
    ← D.obj_eq_span hF hT hT₂ g₂ T.1.hom (Category.comp_id _)]
  exact D.obj.congr T₂ ((CostructuredArrow.w g₁.hom).trans (CostructuredArrow.w g₂.hom).symm) _ _

variable (B S hS) in
/-- **The defining ideal of a closed subspace on an affine chart of a qcqs algebraic space is a
directed union of finitely generated invariant ideals** (Stacks 0829 on charts, read in the ring
of functions of the chart). For a pair of maps `g₁, g₂ : T₂ ⟶ T` of affine charts, the ideals of
the family have equal extensions along the two restrictions `𝒪(T) → 𝒪(T₂)`. The family is the
set of all such ideals contained in the defining ideal, ordered by inclusion. -/
theorem exists_directed_fg_invariant_ideals (X' : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X'.1) (hqc : IsQuasiCompactSpace B S hS X'.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X'.1)
    {T T₂ : SmallEtale B S hS X'.1} (hT : IsAffine (chartScheme T))
    (hT₂ : IsAffine (chartScheme T₂)) (g₁ g₂ : T₂ ⟶ T) :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (K : ι → Ideal (chartRing B S hS X'.1 X'.2 T)), Monotone K ∧
      (∀ i, (K i).map (chartRestrict (hF := X'.2) g₁) =
        (K i).map (chartRestrict (hF := X'.2) g₂)) ∧
      (∀ i, (K i).FG) ∧ ⨆ i, K i = definingIdealAt B S hS X' Z (Opposite.op T) := by
  classical
  let I : Ideal (chartRing B S hS X'.1 X'.2 T) := definingIdealAt B S hS X' Z (Opposite.op T)
  let I₂ : Ideal (chartRing B S hS X'.1 X'.2 T₂) := definingIdealAt B S hS X' Z (Opposite.op T₂)
  let ι := {J : Ideal (chartRing B S hS X'.1 X'.2 T) // J.FG ∧ J ≤ I ∧
    J.map (chartRestrict (hF := X'.2) g₁) = J.map (chartRestrict (hF := X'.2) g₂)}
  have hdir : IsDirected ι (· ≤ ·) := ⟨fun J J' => ⟨⟨J.1 ⊔ J'.1, Submodule.FG.sup J.2.1 J'.2.1,
    sup_le J.2.2.1 J'.2.2.1, by rw [Ideal.map_sup, Ideal.map_sup, J.2.2.2, J'.2.2.2]⟩,
    le_sup_left (a := J.1), le_sup_right (b := J'.1)⟩⟩
  have hne : Nonempty ι := ⟨⟨⊥, Submodule.fg_bot, bot_le, by rw [Ideal.map_bot, Ideal.map_bot]⟩⟩
  refine ⟨ι, inferInstance, hdir, hne, Subtype.val, fun _ _ h => h, fun J => J.2.2.2,
    fun J => J.2.1, le_antisymm (iSup_le fun J => J.2.2.1) fun a ha => ?_⟩
  let F := (definingIdealSheaf B S hS X' Z).toSheafOfModules
  obtain ⟨M, hMfg, hsM, hM⟩ := exists_fg_invariant_submodule_of_qcqs (F := F) hqc hqs
    (definingIdealSheaf_isCartesianOnAffineCharts B S hS X' Z) hT hT₂ g₁ g₂
    {(⟨a, ha⟩ : I)}
  let M' : Submodule (chartRing B S hS X'.1 X'.2 T) I := M
  let J : Ideal (chartRing B S hS X'.1 X'.2 T) := M'.map I.subtype
  have key : ∀ g : T₂ ⟶ T, J.map (chartRestrict (hF := X'.2) g) =
      (Submodule.span (chartRing B S hS X'.1 X'.2 T₂) (chartRes F g '' (M : Set _)) :
        Submodule (chartRing B S hS X'.1 X'.2 T₂) I₂).map I₂.subtype := by
    intro g
    rw [Submodule.map_span, Ideal.map]
    congr 1
    rw [Submodule.map_coe, Set.image_image]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨chartRes F g x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  have hJ : J ∈ {J : Ideal (chartRing B S hS X'.1 X'.2 T) | J.FG ∧ J ≤ I ∧
      J.map (chartRestrict (hF := X'.2) g₁) = J.map (chartRestrict (hF := X'.2) g₂)} :=
    ⟨hMfg.map _, Submodule.map_subtype_le _ _, by
      rw [key, key]; exact congrArg (Submodule.map I₂.subtype) hM⟩
  exact le_iSup (fun J : ι => J.1) ⟨J, hJ⟩
    ⟨⟨a, ha⟩, hsM (Finset.mem_coe.2 (Finset.mem_singleton_self _)), rfl⟩

end AlgebraicGeometry.Space
