module

public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothCriterion

/-!
# Smoothness from lifts against finite type first order thickenings

Let `f : X ⟶ S` be locally of finite presentation. To show that `f` is smooth it is enough to
solve, Zariski locally on `X`, the lifting problems of the infinitesimal lifting criterion
([Stacks, Tag 02H6]) for the first order thickenings `Spec Γ(X, V) ⟶ Spec C` where `C` is of
finite type over `Γ(S, U)` for affine opens `V ⊆ f⁻¹ U`. Indeed formal smoothness of the finitely
generated algebra `B = Γ(X, V)` over `A = Γ(S, U)` is the existence of a section of
`P ⧸ J ^ 2 ⟶ B` for a presentation `P = A[x₁, …, xₙ] ⟶ B` with kernel `J`, and `P ⧸ J ^ 2` is of
finite type over `A`.

The restriction to finite type thickenings matters when the points of `S` are only known as a
functor on a category of schemes of bounded size, as for the representing objects of a big site:
`Spec C` is then again of bounded size.

## Main results

* `Stacks.Smooth.formallySmooth_of_forall_section`: the ring-level criterion.
* `Stacks.Smooth.smooth_of_forall_lift`: the scheme-level criterion, allowing the lifting
  problems to be solved only on the affine opens of a family stable under shrinking and
  covering `X`.

## References

* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
* [Stacks Project, Tag 00TN](https://stacks.math.columbia.edu/tag/00TN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Smooth

/-- **Formal smoothness from sections of finite type square-zero thickenings.** Let `B` be a
finitely generated `A`-algebra. If every surjection `φ : C ⟶ B` of `A`-algebras with square-zero
kernel and `C` of finite type over `A` has an `A`-algebra section, then `B` is formally smooth
over `A`. -/
theorem formallySmooth_of_forall_section {A B : CommRingCat.{u}} (β : A ⟶ B)
    (hβ : β.hom.FiniteType)
    (H : ∀ (C : CommRingCat.{u}) (α : A ⟶ C) (_ : α.hom.FiniteType) (φ : C ⟶ B),
      Function.Surjective φ.hom → RingHom.ker φ.hom ^ 2 = ⊥ → α ≫ φ = β →
        ∃ ψ : B ⟶ C, ψ ≫ φ = 𝟙 B ∧ β ≫ ψ = α) :
    β.hom.FormallySmooth := by
  let : Algebra A B := β.hom.toAlgebra
  have hft : Algebra.FiniteType A B := hβ
  obtain ⟨n, p, hp⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  let J := RingHom.ker p.toRingHom
  let C : CommRingCat.{u} := CommRingCat.of (MvPolynomial (Fin n) A ⧸ J ^ 2)
  let α : A ⟶ C := CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A ⧸ J ^ 2))
  let φ : C ⟶ B := CommRingCat.ofHom p.kerSquareLift.toRingHom
  have hαft : α.hom.FiniteType := by
    change (algebraMap A (MvPolynomial (Fin n) A ⧸ J ^ 2)).FiniteType
    rw [RingHom.finiteType_algebraMap]
    infer_instance
  have hφ : Function.Surjective φ.hom := by
    intro b
    obtain ⟨x, rfl⟩ := hp b
    exact ⟨Ideal.Quotient.mk _ x, p.kerSquareLift_mk x⟩
  have hφ2 : RingHom.ker φ.hom ^ 2 = ⊥ := by
    change RingHom.ker p.kerSquareLift.toRingHom ^ 2 = ⊥
    rw [p.ker_kerSquareLift]
    exact Ideal.cotangentIdeal_square _
  have hαφ : α ≫ φ = β := by
    ext a
    change p.kerSquareLift (algebraMap A _ a) = algebraMap A B a
    exact p.kerSquareLift.commutes a
  obtain ⟨ψ, hψφ, hβψ⟩ := H C α hαft φ hφ hφ2 hαφ
  let g : B →ₐ[A] MvPolynomial (Fin n) A ⧸ J ^ 2 :=
    { toRingHom := ψ.hom
      commutes' := fun a => congrArg (fun k : A ⟶ C => k.hom a) hβψ }
  exact Algebra.FormallySmooth.of_split p g
    (AlgHom.ext fun b => congrArg (fun k : B ⟶ B => k.hom b) hψφ)

/-- **Smoothness of `appLE` from lifts against finite type first order thickenings.** If every
first order thickening `Spec Γ(X, V) ⟶ Spec C` with `C` of finite type over `Γ(S, U)`, compatible
with `f`, admits a lift `Spec C ⟶ X` of `V ⊆ X` over `S`, then `f.appLE U V e` is smooth. -/
theorem smooth_appLE_of_forall_lift {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    {U : S.Opens} {V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (hlift : ∀ (C : CommRingCat.{u}) (α : Γ(S, U) ⟶ C) (_ : α.hom.FiniteType) (φ : C ⟶ Γ(X, V)),
      Function.Surjective φ.hom → RingHom.ker φ.hom ^ 2 = ⊥ → α ≫ φ = f.appLE U V e →
        ∃ g' : Spec C ⟶ X, Spec.map φ ≫ g' = hV.fromSpec ∧ g' ≫ f = Spec.map α ≫ hU.fromSpec) :
    (f.appLE U V e).hom.Smooth := by
  have hfp : (f.appLE U V e).hom.FinitePresentation :=
    HasRingHomProperty.appLE @LocallyOfFinitePresentation f inferInstance ⟨U, hU⟩ ⟨V, hV⟩ e
  refine RingHom.smooth_def.mpr ⟨?_, hfp⟩
  refine formallySmooth_of_forall_section _ (RingHom.FiniteType.of_finitePresentation hfp)
    fun C α hα φ hφ hφ2 hαφ => ?_
  obtain ⟨g', hg'1, hg'2⟩ := hlift C α hα φ hφ hφ2 hαφ
  have hrange : Set.range g' ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := specMap_base_surjective hφ hφ2 y
    exact ⟨z, by rw [← hz, ← Scheme.Hom.comp_apply, hg'1]⟩
  let h0 : Spec C ⟶ Spec Γ(X, V) := IsOpenImmersion.lift hV.fromSpec g' hrange
  have hh0 : h0 ≫ hV.fromSpec = g' := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Spec.preimage h0, ?_, ?_⟩
  · apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_id, ← cancel_mono hV.fromSpec,
      Category.assoc, hh0, hg'1, Category.id_comp]
  · apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, ← cancel_mono hU.fromSpec, Category.assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e, ← Category.assoc, hh0, hg'2]

/-- **Smoothness from lifts against finite type first order thickenings, Zariski locally.** Let
`f : X ⟶ S` be locally of finite presentation and `W` a property of opens of `X`, stable under
shrinking, such that every point has an open neighbourhood satisfying `W`. Suppose that for all
affine opens `U ⊆ S` and `V ⊆ f⁻¹ U` with `W V`, every first order thickening
`Spec.map φ : Spec Γ(X, V) ⟶ Spec C` with `C` of finite type over `Γ(S, U)`, compatible with `f`,
admits a lift `Spec C ⟶ X` of `V ⊆ X` over `S`. Then `f` is smooth. -/
theorem smooth_of_forall_lift {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (W : X.Opens → Prop) (hWmono : ∀ V V' : X.Opens, V' ≤ V → W V → W V')
    (hW : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ W V)
    (hlift : ∀ (U : S.Opens) (V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
      (e : V ≤ f ⁻¹ᵁ U), W V →
      ∀ (C : CommRingCat.{u}) (α : Γ(S, U) ⟶ C) (_ : α.hom.FiniteType) (φ : C ⟶ Γ(X, V)),
        Function.Surjective φ.hom → RingHom.ker φ.hom ^ 2 = ⊥ → α ≫ φ = f.appLE U V e →
          ∃ g' : Spec C ⟶ X, Spec.map φ ≫ g' = hV.fromSpec ∧
            g' ≫ f = Spec.map α ≫ hU.fromSpec) :
    AlgebraicGeometry.Smooth f := by
  -- glue over a cover of `X` by affine opens satisfying `W`
  have hcov : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ W V := by
    intro x
    obtain ⟨V₀, hxV₀, hWV₀⟩ := hW x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVV₀⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxV₀ V₀.2
    exact ⟨V, hV, hxV, hWmono V₀ V hVV₀ hWV₀⟩
  have hsrc : IsZariskiLocalAtSource (@AlgebraicGeometry.Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have htgt : IsZariskiLocalAtTarget (@AlgebraicGeometry.Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  have hres : MorphismProperty.RespectsRight (@AlgebraicGeometry.Smooth.{u}) @IsOpenImmersion :=
    MorphismProperty.Respects.toRespectsRight
  refine IsZariskiLocalAtSource.iff_exists_resLE.mpr fun x => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨V₁, hV₁, hxV₁, hWV₁⟩ := hcov x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ V₁ ⊓ f ⁻¹ᵁ U from ⟨hxV₁, hxU⟩)
      (V₁ ⊓ f ⁻¹ᵁ U).2
  have hUa : IsAffine U := hU
  have hVa : IsAffine V := hV
  refine ⟨U, V, hxV, fun y hy => (hVle hy).2, ?_⟩
  rw [HasRingHomProperty.iff_appLE (P := @AlgebraicGeometry.Smooth)]
  intro U' V' e'
  rw [Scheme.Hom.resLE_appLE]
  have hU'a : IsAffineOpen ((Scheme.Opens.ι U) ''ᵁ U'.1) :=
    U'.2.image_of_isOpenImmersion (Scheme.Opens.ι U)
  have hV'a : IsAffineOpen ((Scheme.Opens.ι V) ''ᵁ V'.1) :=
    V'.2.image_of_isOpenImmersion (Scheme.Opens.ι V)
  exact smooth_appLE_of_forall_lift f hU'a hV'a _ (hlift _ _ hU'a hV'a _
    (hWmono V _ ((Scheme.Hom.image_le_opensRange _ _).trans (Scheme.Opens.opensRange_ι V).le)
      (hWmono V₁ V (fun y hy => (hVle hy).1) hWV₁)))

end Stacks.Smooth
