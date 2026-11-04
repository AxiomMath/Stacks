module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.EpiResidueFields

/-!
# Epimorphisms detected on the fibres of a morphism

Three general facts used in the proof of Stacks 0DPA to show that `π^* π_* 𝒦(m) ⟶ 𝒦(m)` is
surjective for `K ∈ Quot^P(T)`:

* for an adjunction `F ⊣ G`, the counit at `M` is an epimorphism as soon as some morphism
  `F(B) ⟶ M` is (it factors through the counit);
* a morphism of short exact sequences (exact in the middle, with mono left map below) whose
  middle component is an isomorphism and whose right component is a monomorphism has an
  epimorphic left component;
* **Nakayama's lemma along the fibres of a morphism** `f : X ⟶ S`: a morphism of modules on `X`
  with target of finite type is an epimorphism as soon as its restriction to the fibre `X_s` is an
  epimorphism for every `s ∈ S` (every residue-field point of `X` factors through a fibre).

## Main results

* `AlgebraicGeometry.ProjectiveQuot.epi_counit_app_of_epi`.
* `AlgebraicGeometry.ProjectiveQuot.epi_τ₁_of_exact`.
* `AlgebraicGeometry.ProjectiveQuot.epi_of_forall_epi_pullback_fibre`.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 01BJ](https://stacks.math.columbia.edu/tag/01BJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveQuot

/-- **The counit at `M` is an epimorphism once some `F(B) ⟶ M` is**: every morphism
`F(B) ⟶ M` factors through the counit `F(G(M)) ⟶ M`. -/
theorem epi_counit_app_of_epi {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) {B : C} {M : D} (φ : F.obj B ⟶ M) [Epi φ] :
    Epi (adj.counit.app M) := by
  have h := adj.homEquiv_counit (g := adj.homEquiv _ _ φ)
  rw [Equiv.symm_apply_apply] at h
  exact epi_of_epi_fac h.symm

/-- **A morphism of exact sequences which is an isomorphism in the middle and a monomorphism on
the right is an epimorphism on the left**, when the left map of the target is a monomorphism. -/
theorem epi_τ₁_of_exact {C : Type*} [Category* C] [Abelian C] {S₁ S₂ : ShortComplex C}
    (φ : S₁ ⟶ S₂) (h₁ : S₁.Exact) (h₂ : S₂.Exact) [Mono S₂.f] [IsIso φ.τ₂] [Mono φ.τ₃] :
    Epi φ.τ₁ := by
  let S₃ : ShortComplex C := ShortComplex.mk (φ.τ₁ ≫ S₂.f) S₂.g (by simp)
  let ψ : S₁ ⟶ S₃ :=
    { τ₁ := 𝟙 _
      τ₂ := φ.τ₂
      τ₃ := φ.τ₃
      comm₁₂ := by simp [S₃, φ.comm₁₂]
      comm₂₃ := φ.comm₂₃ }
  have hk : Epi (kernel.lift S₂.g (φ.τ₁ ≫ S₂.f) S₃.zero) :=
    S₃.exact_iff_epi_kernel_lift.1 ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).1 h₁)
  have hk₂ : Epi (kernel.lift S₂.g S₂.f S₂.zero) :=
    (ShortComplex.exact_iff_epi_kernel_lift S₂).1 h₂
  have : Mono (kernel.lift S₂.g S₂.f S₂.zero) := mono_of_mono_fac (kernel.lift_ι _ _ _)
  have : IsIso (kernel.lift S₂.g S₂.f S₂.zero) := isIso_of_mono_of_epi _
  have hfac : φ.τ₁ ≫ kernel.lift S₂.g S₂.f S₂.zero = kernel.lift S₂.g (φ.τ₁ ≫ S₂.f) S₃.zero := by
    ext
    simp
  rw [← hfac] at hk
  exact (epi_comp_iff_of_isIso _ _).1 hk

/-- **Nakayama's lemma along the fibres of `f : X ⟶ S`.** Let `X_s ⟶ X`, `s ∈ S`, be the fibres
of `f` (any cartesian squares over `Spec κ(s) ⟶ S`). A morphism of modules on `X` whose target is
of finite type is an epimorphism as soon as its inverse image on every fibre is. -/
theorem epi_of_forall_epi_pullback_fibre {X S : Scheme.{u}} (f : X ⟶ S) {M N : X.Modules}
    (φ : M ⟶ N) (hN : N.IsFiniteType) (Xs : S → Scheme.{u}) (ι : ∀ s, Xs s ⟶ X)
    (p : ∀ s, Xs s ⟶ Spec (S.residueField s))
    (hpb : ∀ s, IsPullback (ι s) (p s) f (S.fromSpecResidueField s))
    (h : ∀ s, Epi ((Scheme.Modules.pullback (ι s)).map φ)) : Epi φ := by
  refine Scheme.Modules.epi_of_forall_epi_pullback_fromSpecResidueField φ hN fun x => ?_
  let s := f.base x
  let ℓ : Spec (X.residueField x) ⟶ Xs s :=
    (hpb s).lift (X.fromSpecResidueField x) (Spec.map (f.residueFieldMap x))
      (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x).symm
  let E : Scheme.Modules.pullback (ι s) ⋙ Scheme.Modules.pullback ℓ ≅
      Scheme.Modules.pullback (X.fromSpecResidueField x) :=
    Scheme.Modules.pullbackComp ℓ (ι s) ≪≫ Scheme.Modules.pullbackCongr ((hpb s).lift_fst _ _ _)
  have := h s
  have : Epi (E.hom.app M ≫ (Scheme.Modules.pullback (X.fromSpecResidueField x)).map φ) := by
    rw [← E.hom.naturality φ]
    exact epi_comp ((Scheme.Modules.pullback ℓ).map ((Scheme.Modules.pullback (ι s)).map φ)) _
  exact epi_of_epi (E.hom.app M) _

end AlgebraicGeometry.ProjectiveQuot

end
