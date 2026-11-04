module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Etale.Weakly
public import StacksFrontier.RingTheory.AbsolutelyFlat.Basic
public import StacksFrontier.RingTheory.WeaklyEtale.FormallyUnramified
public import StacksCore.Tactic.StacksAttribute

/-!
# Characterizations of weakly étale morphisms

Weak étaleness of a morphism of schemes can be checked on all pairs of affine opens, or on
suitable open or affine-open coverings of the target and of the inverse images of their
members. It is also preserved by restricting both source and target to open subschemes.

Two consequences of the affine-open criterion are recorded here: a weakly étale morphism is
formally unramified, and the source of a weakly étale morphism with reduced target is reduced.

## Main results

* `AlgebraicGeometry.weaklyEtale_tfae` gives the four equivalent characterizations of a weakly
  étale morphism.
* `AlgebraicGeometry.weaklyEtale_specMap_iff` is the affine case: `Spec` of a ring map is weakly
  étale exactly when the ring map is.
* `AlgebraicGeometry.WeaklyEtale.instResLE` says that the induced morphism between compatible
  open subschemes is weakly étale.
* `AlgebraicGeometry.instFormallyUnramified` gives formal unramifiedness of a weakly étale
  morphism.
* `AlgebraicGeometry.isReduced_of_weaklyEtale` shows that weakly étale morphisms preserve
  reducedness from target to source.

## Implementation notes

The four numbered conditions are recorded in source order using `List.TFAE`. Open coverings are
represented by families of opens satisfying `IsOpenCover`; a covering of an inverse image is
represented by an equality of its supremum with that inverse image. The first declaration covers
the four equivalent conditions. The existing Mathlib instance
`AlgebraicGeometry.WeaklyEtale.instResLE`, registered below, covers the final restriction
assertion.

Reducedness and weak étaleness are expressed by Mathlib's corresponding typeclasses on schemes
and morphisms.

## References

* [Stacks Project, Tag 094S](https://stacks.math.columbia.edu/tag/094S)
* [Stacks Project, Tag 094W](https://stacks.math.columbia.edu/tag/094W)
* [Stacks Project, Tag 094Y](https://stacks.math.columbia.edu/tag/094Y)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

private local instance : MorphismProperty.RespectsIso
    (fun {_ _ : CommRingCat.{u}} f ↦ WeaklyEtale (Spec.map f)) :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso _ fun f g e hf ↦
    (MorphismProperty.arrow_mk_iso_iff (P := @WeaklyEtale)
      (Arrow.isoMk (Scheme.Spec.mapIso (asIso e.inv.right).op)
        (Scheme.Spec.mapIso (asIso e.inv.left).op) (by
        change Spec.map e.inv.right ≫ Spec.map g.hom =
          Spec.map f.hom ≫ Spec.map e.inv.left
        simpa only [← Spec.map_comp] using (congrArg Spec.map e.inv.w).symm))).mp hf

/-- A morphism of affine schemes `Spec S ⟶ Spec R` is weakly étale exactly when the ring map
`R ⟶ S` it comes from is weakly étale: both conditions are flatness together with flatness of
the multiplication map `S ⊗_R S → S`. -/
theorem weaklyEtale_specMap_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    WeaklyEtale (Spec.map f) ↔
      @Algebra.WeaklyEtale R S _ _ f.hom.toAlgebra := by
  algebraize [f.hom]
  have : MorphismProperty.RespectsIso (@Flat) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [AlgebraicGeometry.weaklyEtale_iff, Algebra.weaklyEtale_iff,
    Flat.SpecMap_iff, show f = CommRingCat.ofHom (algebraMap R S) from rfl,
    diagonal_SpecMap R S,
    MorphismProperty.cancel_right_of_respectsIso (P := (@Flat)), Flat.SpecMap_iff]
  exact and_congr RingHom.flat_algebraMap_iff Iff.rfl

private lemma weaklyEtale_iff_appLE {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    WeaklyEtale (f.resLE V U e) ↔
      @Algebra.WeaklyEtale Γ(Y, V) Γ(X, U) _ _ (f.appLE V U e).hom.toAlgebra := by
  let : IsAffine U := hU
  let : IsAffine V := hV
  calc
    WeaklyEtale (f.resLE V U e) ↔
        WeaklyEtale (Spec.map (f.resLE V U e).appTop) :=
      MorphismProperty.arrow_mk_iso_iff (P := @WeaklyEtale)
        (arrowIsoSpecΓOfIsAffine (f.resLE V U e))
    _ ↔ WeaklyEtale (Spec.map (f.appLE V U e)) :=
      MorphismProperty.arrow_mk_iso_iff
        (P := fun {_ _} g ↦ WeaklyEtale (Spec.map g)) (arrowResLEAppIso f V U e)
    _ ↔ _ := weaklyEtale_specMap_iff _

/-- **Stacks Project, Tag 094S.** For a morphism of schemes, weak étaleness is equivalent to
weak étaleness of every induced map on affine-open sections, to admitting compatible open
coverings on which the restricted morphisms are weakly étale, and to the analogous condition for
affine-open coverings and their induced maps on sections. -/
@[stacks 094S "equivalent conditions"]
theorem weaklyEtale_tfae {X S : Scheme.{u}} (f : X ⟶ S) :
    let weaklyEtaleOn := fun (V : S.Opens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V) ↦
      @Algebra.WeaklyEtale Γ(S, V) Γ(X, U) _ _ (f.appLE V U e).hom.toAlgebra
    List.TFAE [
      WeaklyEtale f,
      ∀ (U : X.Opens), IsAffineOpen U →
        ∀ (V : S.Opens), IsAffineOpen V →
          ∀ (e : U ≤ f ⁻¹ᵁ V), weaklyEtaleOn V U e,
      ∃ (J : Type u) (V : J → S.Opens),
        IsOpenCover V ∧
          ∀ j, ∃ (I : Type u) (U : I → X.Opens)
            (hU : (⨆ i, U i) = f ⁻¹ᵁ (V j)),
            ∀ i, WeaklyEtale
              (f.resLE (V j) (U i) ((le_iSup U i).trans hU.le)),
      ∃ (J : Type u) (V : J → S.Opens),
        IsOpenCover V ∧
          (∀ j, IsAffineOpen (V j)) ∧
          ∀ j, ∃ (I : Type u) (U : I → X.Opens)
            (hU : (⨆ i, U i) = f ⁻¹ᵁ (V j)),
            (∀ i, IsAffineOpen (U i)) ∧
              ∀ i, weaklyEtaleOn (V j) (U i) ((le_iSup U i).trans hU.le)] := by
  dsimp only
  tfae_have 1 → 2 := fun _ U hU V hV e ↦
    (weaklyEtale_iff_appLE f V U e hU hV).mp inferInstance
  tfae_have 2 → 4 := by
    intro h
    refine ⟨S.affineOpens, (fun j ↦ j.1), iSup_affineOpens_eq_top S,
      fun j ↦ j.2, fun j ↦ ?_⟩
    let I := { U : X.affineOpens // (U : X.Opens) ≤ f ⁻¹ᵁ j.1 }
    let U : I → X.Opens := fun i ↦ i.1.1
    have hcover : (⨆ i, U i) = f ⁻¹ᵁ j.1 := by
      refine le_antisymm (iSup_le fun i ↦ i.2) ?_
      intro x hx
      obtain ⟨_, ⟨W : X.Opens, hW, rfl⟩, hxW, hWV⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hx (f ⁻¹ᵁ j.1).2
      exact (le_iSup U (⟨⟨W, hW⟩, hWV⟩ : I)) hxW
    exact ⟨I, U, hcover, fun i ↦ i.1.2, fun i ↦ h (U i) i.1.2 j.1 j.2 _⟩
  tfae_have 4 → 3 := by
    rintro ⟨J, V, hV, hVaff, h⟩
    refine ⟨J, V, hV, fun j ↦ ?_⟩
    obtain ⟨I, U, hU, hUaff, hw⟩ := h j
    exact ⟨I, U, hU, fun i ↦ (weaklyEtale_iff_appLE f (V j) (U i)
      ((le_iSup U i).trans hU.le) (hUaff i) (hVaff j)).mpr (hw i)⟩
  tfae_have 3 → 1 := by
    rintro ⟨J, V, hV, h⟩
    apply (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @WeaklyEtale) V hV).mpr
    intro j
    obtain ⟨I, U, hU, hw⟩ := h j
    let g := f.resLE (V j) (⨆ i, U i) hU.le
    have hg : WeaklyEtale g := by
      apply IsZariskiLocalAtSource.of_openCover (P := @WeaklyEtale)
        (𝒰 := Scheme.Opens.iSupOpenCover U)
      intro i
      show WeaklyEtale ((X.homOfLE (le_iSup U i)) ≫ g)
      rw [show X.homOfLE (le_iSup U i) ≫ g =
        f.resLE (V j) (U i) ((le_iSup U i).trans hU.le) by
          rw [← cancel_mono (V j).ι]
          simp [g, Scheme.Hom.resLE, Category.assoc]]
      exact hw i
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @WeaklyEtale)
      (X.isoOfEq hU).hom (f ∣_ V j)).mp hg
  tfae_finish

add_to_stacks 094S "restriction to open subschemes"
  AlgebraicGeometry.WeaklyEtale.instResLE

/-- **Stacks Project, Tag 094W.** A weakly étale morphism of schemes is formally
unramified. -/
@[stacks 094W]
instance instFormallyUnramified
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.WeaklyEtale f] :
    AlgebraicGeometry.FormallyUnramified f := by
  refine ⟨fun {U} hU {V} hV e ↦ ?_⟩
  let : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V e).hom.toAlgebra
  have h := ((weaklyEtale_tfae f).out 1 2).mp ‹WeaklyEtale f›
  exact formallyUnramified_of_flat_lmul _ _ (h V hV U hU e).flat_lmul'

/-- The source of a weakly étale morphism with reduced target is reduced. -/
@[stacks 094Y]
lemma isReduced_of_weaklyEtale
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.WeaklyEtale f] :
    AlgebraicGeometry.IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (show f x ∈ (⊤ : Y.Opens) from trivial) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ f ⁻¹ᵁ V from hxV) (f ⁻¹ᵁ V).2
    let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    have hwe := ((weaklyEtale_tfae f).out 1 2).mp ‹AlgebraicGeometry.WeaklyEtale f›
    have : Algebra.WeaklyEtale Γ(Y, V) Γ(X, U) := hwe U hU V hV hUV
    have : _root_.IsReduced Γ(X, U) :=
      (absolutelyFlat_and_isReduced_of_flat_lmul' Γ(Y, V) Γ(X, U)
        (Algebra.WeaklyEtale.flat_lmul' _ _)).2 inferInstance inferInstance
    have : AlgebraicGeometry.IsReduced (Scheme.Opens.toScheme U) := by
      have : _root_.IsReduced Γ(Scheme.Opens.toScheme U, ⊤) :=
        isReduced_of_injective (Scheme.Opens.topIso U).hom.hom
          (Scheme.Opens.topIso U).commRingCatIsoToRingEquiv.injective
      have : IsAffine (Scheme.Opens.toScheme U) := hU
      exact isReduced_of_isAffine_isReduced (Scheme.Opens.toScheme U)
    have : _root_.IsReduced ((Scheme.Opens.toScheme U).presheaf.stalk ⟨x, hxU⟩) :=
      isReduced_stalk_of_isReduced _ _
    exact isReduced_of_injective (Scheme.Opens.stalkIso U ⟨x, hxU⟩).inv.hom
      (Scheme.Opens.stalkIso U ⟨x, hxU⟩).symm.commRingCatIsoToRingEquiv.injective
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk X

end AlgebraicGeometry
