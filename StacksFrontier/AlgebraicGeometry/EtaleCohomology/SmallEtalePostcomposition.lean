module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.Basic

/-!
# Composition with an étale morphism, on Mathlib's small étale sites

Let `w : Y ⟶ X` be an étale morphism of schemes. An étale scheme over `Y` is an étale scheme over
`X` through `w`, so composition with `w` is a functor `Σ_w : Y.Etale ⥤ X.Etale`; it is Mathlib's
`MorphismProperty.Over.map`, left adjoint to base change along `w`
(`MorphismProperty.Over.mapPullbackAdj`).

This file proves that `Σ_w` is a continuous functor of small étale sites. The direct image of
sheaves along `Σ_w`, which is restriction of a sheaf on `X_étale` to the étale schemes over `Y`,
is then left adjoint to the direct image along base change: it is an inverse image along `w`,
computed without any sheafification. `Σ_w` is not representably flat (it does not preserve the
final object), so continuity is proved from the two halves of Stacks 00WW: it preserves covering
sieves, and it preserves compatible families of sections.

## Main definitions

* `Stacks.EtaleCohomology.smallEtalePostcomp` — composition with `w`.
* `Stacks.EtaleCohomology.smallEtalePostcompAdj` — composition with `w` is left adjoint to base
  change along `w`.
* `Stacks.EtaleCohomology.smallEtaleRestrictionAdj` — the induced adjunction on sheaves: the
  restriction of sheaves along `Σ_w` is left adjoint to the direct image along `w`.

## Main results

* `Stacks.EtaleCohomology.smallEtalePostcomp_isContinuous` — `Σ_w` is continuous.

## References

* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 00WW](https://stacks.math.columbia.edu/tag/00WW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w' w u

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} (w : Y ⟶ X) [Etale w]

/-- **Composition with an étale morphism** `w : Y ⟶ X`, as a functor from the small étale site of
`Y` to that of `X`. -/
def smallEtalePostcomp (w : Y ⟶ X) [Etale w] : Y.Etale ⥤ X.Etale :=
  letI : MorphismProperty.IsStableUnderComposition (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  MorphismProperty.Over.map ⊤ (P := @Etale) (show Etale w from inferInstance)

/-- The scheme underlying `Σ_w V` is the scheme underlying `V`. -/
@[simp]
theorem smallEtalePostcomp_obj_left (V : Y.Etale) : ((smallEtalePostcomp w).obj V).left = V.left :=
  rfl

/-- The structure morphism of `Σ_w V` to `X` is the structure morphism of `V` followed by `w`. -/
@[simp]
theorem smallEtalePostcomp_obj_hom (V : Y.Etale) :
    ((smallEtalePostcomp w).obj V).hom = V.hom ≫ w :=
  rfl

/-- The morphism of schemes underlying `Σ_w g` is the one underlying `g`. -/
@[simp]
theorem smallEtalePostcomp_map_left {V V' : Y.Etale} (g : V ⟶ V') :
    ((smallEtalePostcomp w).map g).left = g.left :=
  rfl

/-- Composition with `w` is left adjoint to base change along `w`. -/
def smallEtalePostcompAdj : smallEtalePostcomp w ⊣ smallEtaleBaseChange w :=
  letI : MorphismProperty.IsStableUnderComposition (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  letI : MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) w :=
    ⟨fun _ _ ↦ inferInstance⟩
  letI : MorphismProperty.IsStableUnderBaseChangeAlong (@Etale : MorphismProperty Scheme.{u}) w :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  MorphismProperty.Over.mapPullbackAdj (@Etale : MorphismProperty Scheme.{u}) ⊤ w
    (show Etale w from inferInstance) trivial

/-- Composition with `w` carries covering sieves to covering sieves: a covering family is unchanged
as a family of schemes and arrows. -/
theorem smallEtalePostcomp_coverPreserving :
    CoverPreserving Y.smallEtaleTopology X.smallEtaleTopology (smallEtalePostcomp w) where
  cover_preserve {U R} hR := by
    rw [mem_smallEtaleTopology_iff] at hR ⊢
    intro x
    obtain ⟨V, f, hf, hy⟩ := hR x
    exact ⟨(smallEtalePostcomp w).obj V, (smallEtalePostcomp w).map f,
      Sieve.image_mem_functorPushforward _ R hf, hy⟩

/-- Composition with `w` preserves compatible families of sections. Given two morphisms
`f₁ : W ⟶ Σ_w Y₁` and `f₂ : W ⟶ Σ_w Y₂` of the small étale site of `X` whose composites into
`Σ_w Z` agree, `W` is itself étale over `Y` through `f₁`, and the two restrictions agree because
they are restrictions along that single lift. -/
theorem smallEtalePostcomp_compatiblePreserving :
    CompatiblePreserving.{w'} X.smallEtaleTopology (smallEtalePostcomp w) where
  compatible {ℱ Z T x hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ he} := by
    let a₁ : W.left ⟶ Y₁.left := f₁.left
    let a₂ : W.left ⟶ Y₂.left := f₂.left
    let b₁ : Y₁.left ⟶ Z.left := g₁.left
    let b₂ : Y₂.left ⟶ Z.left := g₂.left
    have hw₁ : a₁ ≫ Y₁.hom ≫ w = W.hom := MorphismProperty.Over.w f₁
    have hb₁ : b₁ ≫ Z.hom = Y₁.hom := MorphismProperty.Over.w g₁
    have hb₂ : b₂ ≫ Z.hom = Y₂.hom := MorphismProperty.Over.w g₂
    have hleft : a₁ ≫ b₁ = a₂ ≫ b₂ :=
      congrArg (fun k : W ⟶ (smallEtalePostcomp w).obj Z => k.left) he
    have : Etale ((a₁ ≫ Y₁.hom) ≫ w) := by
      rw [Category.assoc, hw₁]
      exact W.prop
    have : Etale (a₁ ≫ Y₁.hom) := Etale.of_comp _ w
    let W' : Y.Etale := Scheme.Etale.mk (a₁ ≫ Y₁.hom)
    let g₁' : W' ⟶ Y₁ := MorphismProperty.Over.homMk a₁ rfl trivial
    have h₂₁ : a₂ ≫ Y₂.hom = a₁ ≫ Y₁.hom := by
      rw [← hb₁, ← hb₂, ← Category.assoc, ← Category.assoc, hleft]
    let g₂' : W' ⟶ Y₂ := MorphismProperty.Over.homMk a₂ h₂₁ trivial
    have hcompat : g₁' ≫ g₁ = g₂' ≫ g₂ := MorphismProperty.Over.Hom.ext hleft
    have he' : 𝟙 W.left ≫ W.hom = (a₁ ≫ Y₁.hom) ≫ w := by
      rw [Category.id_comp, Category.assoc, hw₁]
    let e : (smallEtalePostcomp w).obj W' ≅ W := MorphismProperty.Over.isoMk (Iso.refl _) he'
    have key : ∀ {Y' : Y.Etale} (f : W ⟶ (smallEtalePostcomp w).obj Y') (g' : W' ⟶ Y')
        (s : ℱ.obj.obj (op ((smallEtalePostcomp w).obj Y'))),
        e.inv ≫ (smallEtalePostcomp w).map g' = f →
        ℱ.obj.map f.op s = ℱ.obj.map e.inv.op (ℱ.obj.map ((smallEtalePostcomp w).map g').op s) := by
      rintro Y' f g' s rfl
      rw [op_comp, Functor.map_comp]
      rfl
    rw [key f₁ g₁' _ (MorphismProperty.Over.Hom.ext (Category.id_comp a₁)),
      key f₂ g₂' _ (MorphismProperty.Over.Hom.ext (Category.id_comp a₂))]
    exact congrArg _ (hx g₁' g₂' hg₁ hg₂ hcompat)

/-- **Stacks 03S3.** Composition with an étale morphism is a continuous functor of small étale
sites. -/
instance smallEtalePostcomp_isContinuous :
    (smallEtalePostcomp w).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology :=
  Functor.isContinuous_of_coverPreserving (smallEtalePostcomp_compatiblePreserving w)
    (smallEtalePostcomp_coverPreserving w)

/-- **Restriction to the étale schemes over `Y` is an inverse image along `w`.** The direct image
of sheaves along composition with `w` is left adjoint to the direct image along base change. -/
def smallEtaleRestrictionAdj (A : Type w) [Category.{w'} A] :
    (smallEtalePostcomp w).sheafPushforwardContinuous A Y.smallEtaleTopology X.smallEtaleTopology ⊣
      (smallEtaleBaseChange w).sheafPushforwardContinuous A X.smallEtaleTopology
        Y.smallEtaleTopology :=
  (smallEtalePostcompAdj w).sheafPushforwardContinuous (E := A) _ _

end Stacks.EtaleCohomology
