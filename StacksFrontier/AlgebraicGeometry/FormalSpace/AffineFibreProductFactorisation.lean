module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProduct
import all StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillan

/-!
# Closed immersions into fibre products of affine formal algebraic spaces

A closed immersion of an affine scheme into a fibre product of two affine formal algebraic
spaces over a separated base factors through closed immersions into affine thickening stages of
the two factors, with surjective comparison map on coordinate rings. These results belong next
to `StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProduct` but are kept in a module of
their own, so that that module stays as it is on the base.

## Main results

* `exists_isClosedImmersion_factorisation_pullback`: A closed immersion of an affine scheme into
  `X ×_Z Y`, with `X` and `Y` affine formal algebraic spaces and `Z` separated, factors through
  closed immersions into affine thickening stages of `X` and `Y` such that the map from the tensor
  product of their coordinate rings to the coordinate ring of the affine scheme is surjective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

namespace AlgebraicGeometry.FormalSpace

universe u

section Comparison

variable {C : Type*} [Category C] [HasPullbacks C]

end Comparison

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A closed immersion of a represented sheaf into an fppf sheaf which factors through a
relative thickening out of another represented sheaf is a closed immersion of the representing
objects. -/
private theorem isClosedImmersion_map_of_isClosedImmersionInto
    {W : FppfSheaf B S hS} {T V : BigFppfOver B S hS}
    {f : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ W}
    (hf : IsClosedImmersionInto B S hS f)
    {γ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ W}
    (hγ : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) γ)
    {t : T ⟶ V}
    (ht : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map t ≫ γ = f) :
    IsClosedImmersion ((BigFppfOver.toScheme B S hS).map t) := by
  classical
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  have _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  have _ : F.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  have _ : F.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  obtain ⟨hfrep, hfci⟩ := hf
  obtain ⟨-, hγth⟩ := hγ
  have sq : IsPullback (F.map (hfrep.fst' γ)) (F.map (hfrep.snd γ)) f γ :=
    hfrep.isPullback' γ
  have hth : Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B S hS).map (hfrep.fst' γ)) :=
    hγth f (F.map (hfrep.snd γ)) (hfrep.fst' γ) sq.flip
  have _ : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (hfrep.fst' γ)) := hth.1
  have hmono : Mono (hfrep.fst' γ) :=
    (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  have hw : (𝟙 (F.obj T)) ≫ f = F.map t ≫ γ := by rw [Category.id_comp, ht]
  obtain ⟨s₀, hs₀⟩ := F.map_surjective (sq.lift (𝟙 (F.obj T)) (F.map t) hw)
  have h1 : s₀ ≫ hfrep.fst' γ = 𝟙 T := by
    apply F.map_injective
    rw [F.map_comp, hs₀, sq.lift_fst, F.map_id]
  have h3 : hfrep.fst' γ ≫ s₀ = 𝟙 _ := by
    rw [← cancel_mono (hfrep.fst' γ), Category.assoc, h1, Category.comp_id, Category.id_comp]
  have h2 : s₀ ≫ hfrep.snd γ = t := by
    apply F.map_injective
    rw [F.map_comp, hs₀, sq.lift_snd]
  have _ : IsIso s₀ := ⟨⟨hfrep.fst' γ, h1, h3⟩⟩
  rw [← h2, Functor.map_comp]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) _ _).mpr
    (hfci γ (F.map (hfrep.fst' γ)) (hfrep.snd γ) sq)

/-- If `w.appTop` is surjective and the tensor lift of `a.appTop` and `b.appTop` is surjective,
then so is the tensor lift of `(w ≫ a).appTop` and `(w ≫ b).appTop`. -/
private theorem surjective_tensorProduct_lift_appTop_comp {W V T₁ T₂ : Scheme.{u}}
    (w : W ⟶ V) (a : V ⟶ T₁) (b : V ⟶ T₂) (hw : Function.Surjective w.appTop)
    (hV : Function.Surjective (Algebra.TensorProduct.lift a.appTop.hom.toIntAlgHom
      b.appTop.hom.toIntAlgHom (fun _ _ ↦ Commute.all _ _))) :
    Function.Surjective (Algebra.TensorProduct.lift (w ≫ a).appTop.hom.toIntAlgHom
      (w ≫ b).appTop.hom.toIntAlgHom (fun _ _ ↦ Commute.all _ _)) := by
  intro z
  obtain ⟨y, rfl⟩ := hw z
  obtain ⟨x, rfl⟩ := hV y
  refine ⟨x, ?_⟩
  induction x with
  | tmul r₁ r₂ =>
    simp only [Algebra.TensorProduct.lift_tmul, Scheme.Hom.comp_appTop,
      CommRingCat.hom_comp, RingHom.toIntAlgHom_coe, RingHom.coe_comp, Function.comp_apply]
    exact (map_mul _ _ _).symm
  | add x₁ x₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- A closed immersion of an affine scheme of the site into a fibre product of two affine
formal algebraic spaces over a separated base factors through closed immersions into two
affine thickening stages, one of each factor, in such a way that the canonical map from the
tensor product over `ℤ` of the two coordinate rings of those stages to the coordinate ring of
the given affine scheme is surjective.

This is the content of the proof of **Stacks 0AN3, clause (1)** read on a single affine test
object. -/
theorem exists_isClosedImmersion_factorisation_pullback
    {X Y Z : FppfSheaf B S hS} (p : X ⟶ Z) (q : Y ⟶ Z)
    (hZrep : HasRepresentableRelativeProducts B S hS Z)
    (hZsep : IsSeparated B S hS Z)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (T : BigAffineFppf B S hS)
    {f : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      ((BigAffineFppf.inclusion B S hS).obj T) ⟶ pullback p q}
    (hf : IsClosedImmersionInto B S hS f) :
    ∃ (T₁ T₂ : BigAffineFppf B S hS)
      (h₁ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj T₁) ⟶ X)
      (h₂ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj T₂) ⟶ Y)
      (u₁ : (BigAffineFppf.inclusion B S hS).obj T ⟶ (BigAffineFppf.inclusion B S hS).obj T₁)
      (u₂ : (BigAffineFppf.inclusion B S hS).obj T ⟶ (BigAffineFppf.inclusion B S hS).obj T₂),
      IsClosedImmersionInto B S hS h₁ ∧ IsClosedImmersionInto B S hS h₂ ∧
        f ≫ pullback.fst p q =
          (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map u₁ ≫ h₁ ∧
        f ≫ pullback.snd p q =
          (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map u₂ ≫ h₂ ∧
        Function.Surjective
          (Algebra.TensorProduct.lift
            (((BigFppfOver.toScheme B S hS).map u₁).appTop.hom.toIntAlgHom)
            (((BigFppfOver.toScheme B S hS).map u₂).appTop.hom.toIntAlgHom)
            (fun _ _ ↦ Commute.all _ _)) := by
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let K := BigAffineFppf.inclusion B S hS
  let Q : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
  have _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  have _ : F.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  have _ : F.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  have _ : Q.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  have _ := MorphismProperty.relative_isStableUnderBaseChange (P := Q) (F := F)
  obtain ⟨T₁, g₁, h₁, -, ht₁, he₁⟩ :=
    ((isAffineFormalAlgebraicSpace_iff B S hS X).mp hX).1 T (f ≫ pullback.fst p q)
  obtain ⟨T₂, g₂, h₂, -, ht₂, he₂⟩ :=
    ((isAffineFormalAlgebraicSpace_iff B S hS Y).mp hY).1 T (f ≫ pullback.snd p q)
  have hrep : F.relativelyRepresentable (h₁ ≫ p) := hZrep (h₁ ≫ p)
  have hsq := hrep.isPullback' (h₂ ≫ q)
  obtain ⟨hVaff, hVsurj⟩ := hZsep (K.obj T₁) (K.obj T₂) (hrep.pullback (h₂ ≫ q))
    (h₁ ≫ p) (h₂ ≫ q) (hrep.fst' (h₂ ≫ q)) (hrep.snd (h₂ ≫ q))
    T₁.property T₂.property hsq
  obtain ⟨V, c₁, c₂, k₁, k₂, sq₁, sq₂, hmfst, hmsnd⟩ :=
    exists_pullback_comparison p q h₁ h₂ hsq
  have hi : F.map (F.preimage g₁) ≫ (h₁ ≫ p) = F.map (F.preimage g₂) ≫ (h₂ ≫ q) := by
    rw [F.map_preimage, F.map_preimage, ← Category.assoc, ← Category.assoc, he₁, he₂,
      Category.assoc, Category.assoc, pullback.condition]
  let w : K.obj T ⟶ hrep.pullback (h₂ ≫ q) :=
    hrep.lift' (F.preimage g₁) (F.preimage g₂) hi
  have hwfst : F.map w ≫ F.map (hrep.fst' (h₂ ≫ q)) = g₁ := by
    rw [← Functor.map_comp, hrep.lift'_fst, F.map_preimage]
  have hwsnd : F.map w ≫ F.map (hrep.snd (h₂ ≫ q)) = g₂ := by
    rw [← Functor.map_comp, hrep.lift'_snd, F.map_preimage]
  have hγth : Q.relative F (k₁ ≫ k₂) :=
    MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isPullback sq₁ ht₂)
      (MorphismProperty.of_isPullback sq₂ ht₁)
  have hfac : F.map w ≫ (k₁ ≫ k₂) = f := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hmfst, ← Category.assoc, hwfst, he₁]
    · rw [Category.assoc, hmsnd, ← Category.assoc, hwsnd, he₂]
  have _ := isClosedImmersion_map_of_isClosedImmersionInto B S hS hf hγth hfac
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj (hrep.pullback (h₂ ≫ q))) := hVaff
  obtain ⟨-, hwsurj⟩ :=
    IsClosedImmersion.isAffine_surjective_of_isAffine ((BigFppfOver.toScheme B S hS).map w)
  refine ⟨T₁, T₂, h₁, h₂, w ≫ hrep.fst' (h₂ ≫ q), w ≫ hrep.snd (h₂ ≫ q),
    MorphismProperty.relative_monotone (fun _ _ _ hth ↦ hth.1) h₁ ht₁,
    MorphismProperty.relative_monotone (fun _ _ _ hth ↦ hth.1) h₂ ht₂, ?_, ?_, ?_⟩
  · rw [Functor.map_comp, hwfst, he₁]
  · rw [Functor.map_comp, hwsnd, he₂]
  · simp only [Functor.map_comp]
    exact surjective_tensorProduct_lift_appTop_comp _ _ _ hwsurj hVsurj

end AlgebraicGeometry.FormalSpace

end
