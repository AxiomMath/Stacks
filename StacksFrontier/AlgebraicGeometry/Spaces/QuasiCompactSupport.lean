module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable

/-!
# Quasi-compactness of an open subspace of a quasi-compact quasi-separated space

For an open subspace `U` of a quasi-compact and quasi-separated algebraic space `X`, the
inclusion `U ⟶ X` is quasi-compact exactly when `U` is quasi-compact. The nontrivial direction
is an instance of a general fact: a morphism from a quasi-compact algebraic space into a
quasi-separated one is quasi-compact.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_iff_isQuasiCompactSpace_openSubspace`: the inclusion
  of an open subspace of a quasi-compact and quasi-separated algebraic space is quasi-compact
  if and only if the open subspace is quasi-compact.
* `AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace`: a morphism from a
  quasi-compact algebraic space into a quasi-separated one is quasi-compact.
* `AlgebraicGeometry.Space.compactSpace_of_isAbsolutelyQuasiSeparated`: for a quasi-separated
  presheaf, the represented fibre product of two charts with quasi-compact schemes has a
  quasi-compact scheme.

## Implementation notes

Quasi-separatedness enters in the absolute form, over the terminal scheme `Spec ℤ`: the fibre
product `h_W ×_X h_P` of two charts is a base change of the diagonal of `X` along
`h_W ⨯ h_P ⟶ X ⨯ X`, and the product `h_W ⨯ h_P` is quasi-compact only because it is taken
over an affine base — a fibre product of two quasi-compact schemes over a general base scheme
`S` need not be quasi-compact. The passage to the big fppf site of the terminal scheme is
`CategoryTheory.OverShriek.relocalizePresheafFunctor`, which preserves fibre products and
carries representables to representables with the same underlying scheme
(`CategoryTheory.OverShriek.relocalizeYonedaIso`).

The third condition of Tag 0855, that the complement of `U` is the zero locus of a finite type
quasi-coherent ideal, is compared with quasi-compactness of `U` by
`AlgebraicGeometry.Space.isQuasiCompactSpace_of_hasFiniteTypeQuasicoherentIdealZeroLocus` and
`AlgebraicGeometry.Space.hasFiniteTypeQuasicoherentIdealZeroLocus_of_isQuasiCompactSpace`, and
the three conditions are assembled in `AlgebraicGeometry.Space.tfae_isQuasiCompact_openSubspace`.

## References

* [Stacks Project, Tag 0855](https://stacks.math.columbia.edu/tag/0855)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MorphismProperty

universe v u

namespace Stacks.Spaces

/-- If `p₁, p₂` exhibit `P` as the fibre product of `a : A ⟶ F` and `a' : A' ⟶ F`, then `P` is
the fibre product of the diagonal of `F` with `prod.map a a'`. -/
theorem isPullback_diag_prodMap {C : Type u} [Category.{v} C] {F A A' : C} {a : A ⟶ F} {a' : A' ⟶ F}
    [HasBinaryProduct F F] [HasBinaryProduct A A'] {P : C} {p₁ : P ⟶ A} {p₂ : P ⟶ A'}
    (h : IsPullback p₁ p₂ a a') :
    IsPullback (p₁ ≫ a) (prod.lift p₁ p₂) (diag F) (prod.map a a') := by
  have comm : (p₁ ≫ a) ≫ diag F = prod.lift p₁ p₂ ≫ prod.map a a' := by
    refine prod.hom_ext ?_ ?_ <;> simp [h.w]
  have h1 : ∀ s : PullbackCone (diag F) (prod.map a a'), s.fst = (s.snd ≫ prod.fst) ≫ a := by
    intro s
    simpa using s.condition =≫ prod.fst
  have h2 : ∀ s : PullbackCone (diag F) (prod.map a a'), s.fst = (s.snd ≫ prod.snd) ≫ a' := by
    intro s
    simpa using s.condition =≫ prod.snd
  refine ⟨⟨comm⟩, ⟨PullbackCone.IsLimit.mk comm
    (fun s => h.lift (s.snd ≫ prod.fst) (s.snd ≫ prod.snd) ((h1 s).symm.trans (h2 s))) ?_ ?_ ?_⟩⟩
  · intro s
    rw [← Category.assoc, h.lift_fst, h1]
  · intro s
    refine prod.hom_ext ?_ ?_ <;> simp [h.lift_fst, h.lift_snd]
  · intro s m hm₁ hm₂
    refine h.hom_ext ?_ ?_
    · rw [h.lift_fst, ← hm₂]; simp
    · rw [h.lift_snd, ← hm₂]; simp

/-- Compactness of the underlying space transfers along an isomorphism of schemes. -/
theorem compactSpace_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) (h : CompactSpace X) :
    CompactSpace Y :=
  @Homeomorph.compactSpace _ _ _ _ h (TopCat.homeoOfIso (asIso e.hom.base))

end Stacks.Spaces

namespace AlgebraicGeometry.Space

open Stacks.Spaces

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- The structure morphism of an object of the big fppf site over the terminal scheme is
quasi-compact as soon as its source is a quasi-compact scheme. -/
theorem quasiCompact_hom_of_compactSpace (A : BigFppfOver B (⊤_ Scheme.{u}) hZ)
    (hA : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj A)) :
    QuasiCompact (B.inclusion.map A.hom) := by
  have h : B.inclusion.map A.hom =
      (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj A) :
        _ ⟶ ⊤_ Scheme.{u}) := terminal.hom_ext _ _
  rw [h]
  exact (compactSpace_iff_quasiCompact _).mp hA

/-- A fibre product over the terminal scheme of two quasi-compact objects of the big fppf
site is quasi-compact. -/
theorem compactSpace_of_isPullback_hom {A A' P : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    {p₁ : P ⟶ A} {p₂ : P ⟶ A'} (hpb : IsPullback p₁.left p₂.left A.hom A'.hom)
    (hA : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj A))
    (hA' : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj A')) :
    CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj P) := by
  have hq : QuasiCompact (B.inclusion.map A.hom) := quasiCompact_hom_of_compactSpace B hZ A hA
  refine compactSpace_of_iso (hpb.map B.inclusion).isoPullback.symm ?_
  exact @QuasiCompact.compactSpace_of_compactSpace _ _
    (Limits.pullback.snd (B.inclusion.map A.hom) (B.inclusion.map A'.hom)) _ hA'

/-- For a quasi-separated presheaf `X` on the big fppf site of `S`,
the represented fibre product of two charts whose schemes are quasi-compact is again
quasi-compact. -/
theorem compactSpace_of_isAbsolutelyQuasiSeparated
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    {A W Q : BigFppfOver B S hS} {c : yoneda.obj A ⟶ X} {g : yoneda.obj W ⟶ X}
    {q₁ : Q ⟶ A} {q₂ : Q ⟶ W}
    (hsq : IsPullback (yoneda.map q₁) (yoneda.map q₂) c g)
    (hA : CompactSpace ((BigFppfOver.toScheme B S hS).obj A))
    (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W)) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj Q) := by
  set f : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  set L := OverShriek.relocalizePresheafFunctor f
  have hiso := OverShriek.relocalizeYonedaIso f
  have key : IsPullback (yoneda.map ((Over.map f).map q₁)) (yoneda.map ((Over.map f).map q₂))
      ((hiso.app A).inv ≫ L.map c) ((hiso.app W).inv ≫ L.map g) := by
    refine (hsq.map L).of_iso (hiso.app Q) (hiso.app A) (hiso.app W) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact hiso.hom.naturality q₁
    · exact hiso.hom.naturality q₂
    · simp
    · simp
  have : HasBinaryProducts (BigFppfOver B (⊤_ Scheme.{u}) hZ) :=
    CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback
  have hdiag := isPullback_diag_prodMap key
  set i := prodComparison (yoneda : BigFppfOver B (⊤_ Scheme.{u}) hZ ⥤ _)
    ((Over.map f).obj A) ((Over.map f).obj W) with hi
  have : IsIso i := by rw [hi]; infer_instance
  have hlift : yoneda.map (prod.lift ((Over.map f).map q₁) ((Over.map f).map q₂)) ≫ i =
      prod.lift (yoneda.map ((Over.map f).map q₁)) (yoneda.map ((Over.map f).map q₂)) := by
    refine prod.hom_ext ?_ ?_ <;> simp [hi, ← yoneda.map_comp]
  have hfinal : IsPullback (yoneda.map ((Over.map f).map q₁) ≫ ((hiso.app A).inv ≫ L.map c))
      (yoneda.map (prod.lift ((Over.map f).map q₁) ((Over.map f).map q₂))) (diag (L.obj X))
      (i ≫ prod.map ((hiso.app A).inv ≫ L.map c) ((hiso.app W).inv ≫ L.map g)) :=
    isPullback_of_iso_right (by rw [hlift]; exact hdiag)
  have hqc := hXqs.property _ _ _ hfinal
  have hprod : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj
      ((Over.map f).obj A ⨯ (Over.map f).obj W)) :=
    compactSpace_of_isPullback_hom B hZ
      (CategoryTheory.Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk prod.fst prod.snd)
        (prodIsProd _ _)) hA hW
  exact @QuasiCompact.compactSpace_of_compactSpace _ _
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map
      (prod.lift ((Over.map f).map q₁) ((Over.map f).map q₂))) hqc hprod

/-- A morphism from a quasi-compact algebraic space into a quasi-separated algebraic space is
quasi-compact. -/
@[stacks 073B "part (1)", sga "4 VI 1.14" "(i), algebraic spaces"]
theorem isQuasiCompact_of_isQuasiCompactSpace
    {X U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hUqc : IsQuasiCompactSpace B S hS U) (ι : U ⟶ X) :
    IsQuasiCompact B S hS ι := by
  intro Z _ hZqc g
  obtain ⟨W, a, hWc, hasurj, haet⟩ := hZqc
  obtain ⟨P, b, hPc, hbsurj, hbet⟩ := hUqc
  have haet' := presheaf_etale_of_isEtale B S hS haet
  have hbet' := presheaf_etale_of_isEtale B S hS hbet
  have sqA : IsPullback (pullback.fst (a ≫ g) ι) _ a (pullback.fst g ι) :=
    IsPullback.of_bot' (IsPullback.of_hasPullback (a ≫ g) ι)
      (IsPullback.of_hasPullback g ι)
  refine IsQuasiCompactSpace.of_surjective_etale B S hS
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sqA hasurj)
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sqA haet') ?_
  have sqB : IsPullback (pullback.snd (a ≫ g) (b ≫ ι)) _ b (pullback.snd (a ≫ g) ι) :=
    IsPullback.of_bot' (IsPullback.of_hasPullback (a ≫ g) (b ≫ ι)).flip
      (IsPullback.of_hasPullback (a ≫ g) ι).flip
  refine IsQuasiCompactSpace.of_surjective_etale B S hS
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sqB hbsurj)
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sqB hbet') ?_
  have : HasBinaryProducts (BigFppfOver B S hS) :=
    CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback
  have hrep := hX.diagonal_representable.of_diag (b ≫ ι)
  have hpb := hrep.isPullback' (a ≫ g)
  exact (isQuasiCompactSpace_yoneda_obj B S hS
    (compactSpace_of_isAbsolutelyQuasiSeparated B S hS hZ hXqs hpb hPc hWc)).of_iso B S hS
      hpb.flip.isoPullback

/-- For an open subspace of a quasi-compact and
quasi-separated algebraic space, quasi-compactness of the inclusion is equivalent to
quasi-compactness of its source. -/
@[stacks 0855 "parts (1) and (2)"]
theorem isQuasiCompact_iff_isQuasiCompactSpace_openSubspace
    (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (U : {U : Subfunctor X.1 // IsOpenSubspace B S hS U}) :
    IsQuasiCompact B S hS U.1.ι ↔ IsQuasiCompactSpace B S hS U.1.toFunctor := by
  refine ⟨fun h => ?_, fun h => isQuasiCompact_of_isQuasiCompactSpace B S hS hZ X.2 hXqs h _⟩
  exact (h X.1 X.2 hXqc (𝟙 X.1)).of_iso B S hS
    (IsPullback.of_vert_isIso (f := 𝟙 X.1) (fst := U.1.ι) (snd := 𝟙 U.1.toFunctor)
      ⟨by simp⟩).isoPullback.symm

end AlgebraicGeometry.Space

end
