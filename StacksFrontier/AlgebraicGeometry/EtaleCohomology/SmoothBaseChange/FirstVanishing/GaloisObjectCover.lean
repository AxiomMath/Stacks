module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCover
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverSheets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.PointedGaloisCovering

/-!
# A Galois object of `FÉt_X` is a finite étale Galois cover with group its automorphisms

Let `X` be a connected scheme and `A` a Galois object of the Galois category `FÉt_X`. Then
`A ⟶ X`, with `Aut A` acting through inverses, is a finite étale Galois cover in the sense of
`AlgebraicGeometry.FiniteEtaleGaloisCover`: the map `∐_{σ ∈ Aut A} A ⟶ A ×_X A`,
`(σ, y) ↦ (y, σ⁻¹ y)`, is an isomorphism.

The summand at `σ` is the graph of an automorphism over the unramified `A ⟶ X`, an open
immersion whose image is the agreement locus of the two projections up to `σ⁻¹`
(`AlgebraicGeometry.Scheme.Hom.agreeLocus`). These loci cover `A ×_X A` because two morphisms
into a Galois cover differ near every point by an automorphism
(`AlgebraicGeometry.exists_aut_mem_agreeLocus`), and they are disjoint because an automorphism of
a connected cover is determined by one composite (`AlgebraicGeometry.aut_eq_of_comp_eq`). So the
comparison is an open immersion with dense — in fact full — image, hence an isomorphism.

## Main definitions

* `AlgebraicGeometry.FiniteEtaleGaloisCover.ofIsGalois` — the Galois cover attached to a Galois
  object of `FÉt_X`.

## References

* [Stacks Project, Section 03SF](https://stacks.math.columbia.edu/tag/03SF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [ConnectedSpace X]

/-- The action of `Aut A` on a finite étale cover `A` through inverses, as a monoid map from the
opposite group. -/
def autInvAction (A : FiniteEtaleOver X) : (Aut A)ᵐᵒᵖ →* Aut A :=
  (MulEquiv.inv' (Aut A)).symm.toMonoidHom

omit [ConnectedSpace X] in
/-- The action `autInvAction A` sends `MulOpposite.op σ` to `σ⁻¹`. -/
theorem autInvAction_op (A : FiniteEtaleOver X) (σ : Aut A) :
    autInvAction A (MulOpposite.op σ) = σ⁻¹ :=
  rfl

section PullbackSection

omit [ConnectedSpace X]

variable (A : FiniteEtaleOver X) {f : A.left ⟶ A.left}
  (hf : (pullback.fst A.hom A.hom ≫ f) ≫ A.hom = pullback.snd A.hom A.hom ≫ A.hom)
  {s : A.left ⟶ pullback A.hom A.hom} (hs₁ : s ≫ pullback.fst A.hom A.hom = 𝟙 _)
  (hs₂ : s ≫ pullback.snd A.hom A.hom = f)

include hs₁ hs₂ in
/-- The graph `s = (id, f)` of an endomorphism `f` of `A` over `X` lands in the agreement locus
of `p₁ ≫ f` and `p₂`. -/
private theorem range_subset_agreeLocus_of_pullback_section :
    Set.range s.base ⊆ (Scheme.Hom.agreeLocus A.hom (pullback.fst A.hom A.hom ≫ f)
      (pullback.snd A.hom A.hom) hf : Set (pullback A.hom A.hom).carrier) := by
  rintro _ ⟨y, rfl⟩
  refine Scheme.Hom.mem_agreeLocus_of_comp_eq A.hom _ _ hf s ?_ y
  rw [← Category.assoc, hs₁, Category.id_comp, hs₂]

include hs₁ hs₂ in
/-- On the agreement locus of `p₁ ≫ f` and `p₂`, the graph `s = (id, f)` retracts `p₁`. -/
private theorem agreeLocus_ι_fst_comp_pullback_section :
    ((Scheme.Hom.agreeLocus A.hom (pullback.fst A.hom A.hom ≫ f) (pullback.snd A.hom A.hom)
      hf).ι ≫ pullback.fst A.hom A.hom) ≫ s =
      (Scheme.Hom.agreeLocus A.hom (pullback.fst A.hom A.hom ≫ f)
        (pullback.snd A.hom A.hom) hf).ι := by
  apply pullback.hom_ext
  · rw [Category.assoc, hs₁]
    exact Category.comp_id _
  · rw [Category.assoc, hs₂]
    exact (Category.assoc _ _ _).trans (Scheme.Hom.agreeLocus_ι_comp A.hom _ _ hf)

include hf hs₁ hs₂ in
/-- The graph `s = (id, f)` of an endomorphism of the unramified `A ⟶ X` is an open immersion. -/
private theorem isOpenImmersion_of_pullback_section : IsOpenImmersion s := by
  let O := Scheme.Hom.agreeLocus A.hom (pullback.fst A.hom A.hom ≫ f)
    (pullback.snd A.hom A.hom) hf
  let l : A.left ⟶ O := IsOpenImmersion.lift O.ι s (by
    simpa only [Scheme.Opens.range_ι] using
      range_subset_agreeLocus_of_pullback_section A hf hs₁ hs₂)
  have hl : l ≫ O.ι = s := IsOpenImmersion.lift_fac _ _ _
  have : IsIso l := ⟨⟨O.ι ≫ pullback.fst A.hom A.hom, by rw [← Category.assoc, hl, hs₁], by
    rw [← cancel_mono O.ι, Category.assoc, hl,
      agreeLocus_ι_fst_comp_pullback_section A hf hs₁ hs₂, Category.id_comp]⟩⟩
  rw [← hl]
  infer_instance

include hs₁ hs₂ in
/-- The image of the graph `s = (id, f)` is the agreement locus of `p₁ ≫ f` and `p₂`. -/
private theorem range_eq_agreeLocus_of_pullback_section :
    Set.range s.base = (Scheme.Hom.agreeLocus A.hom (pullback.fst A.hom A.hom ≫ f)
      (pullback.snd A.hom A.hom) hf : Set (pullback A.hom A.hom).carrier) := by
  refine (range_subset_agreeLocus_of_pullback_section A hf hs₁ hs₂).antisymm fun z hz => ?_
  obtain ⟨w, rfl⟩ : z ∈ Set.range (Scheme.Hom.agreeLocus A.hom _ _ hf).ι.base := by
    simpa only [Scheme.Opens.range_ι] using hz
  refine ⟨((Scheme.Hom.agreeLocus A.hom _ _ hf).ι ≫ pullback.fst A.hom A.hom).base w, ?_⟩
  rw [← Scheme.Hom.comp_apply, agreeLocus_ι_fst_comp_pullback_section A hf hs₁ hs₂]

end PullbackSection

/-- Two automorphisms of a connected finite étale cover whose agreement loci meet are equal. -/
private theorem eq_of_mem_agreeLocus_aut (A : FiniteEtaleOver X) [IsConnected A] {σ τ : Aut A}
    (hσ : (pullback.fst A.hom A.hom ≫ σ.asIso.hom.left) ≫ A.hom = pullback.snd A.hom A.hom ≫ A.hom)
    (hτ : (pullback.fst A.hom A.hom ≫ τ.asIso.hom.left) ≫ A.hom = pullback.snd A.hom A.hom ≫ A.hom)
    {z : (pullback A.hom A.hom).carrier} (hzσ : z ∈ Scheme.Hom.agreeLocus A.hom _ _ hσ)
    (hzτ : z ∈ Scheme.Hom.agreeLocus A.hom _ _ hτ) : σ = τ := by
  let O₁ := Scheme.Hom.agreeLocus A.hom _ _ hσ
  let O₂ := Scheme.Hom.agreeLocus A.hom _ _ hτ
  let V : (pullback A.hom A.hom).Opens := O₁ ⊓ O₂
  have : Nonempty V := ⟨⟨z, hzσ, hzτ⟩⟩
  let j₁ : (V : Scheme.{u}) ⟶ O₁ := (pullback A.hom A.hom).homOfLE inf_le_left
  let j₂ : (V : Scheme.{u}) ⟶ O₂ := (pullback A.hom A.hom).homOfLE inf_le_right
  have hj : j₁ ≫ O₁.ι = j₂ ≫ O₂.ι := by simp only [j₁, j₂, Scheme.homOfLE_ι]
  have h₁ := congrArg (j₁ ≫ ·) (Scheme.Hom.agreeLocus_ι_comp A.hom _ _ hσ)
  have h₂ := congrArg (j₂ ≫ ·) (Scheme.Hom.agreeLocus_ι_comp A.hom _ _ hτ)
  simp only [← Category.assoc] at h₁ h₂
  rw [hj] at h₁
  exact aut_eq_of_comp_eq (j₂ ≫ O₂.ι ≫ pullback.fst A.hom A.hom) (τ := σ) (τ' := τ)
    (by simpa only [Category.assoc] using h₁.trans h₂.symm)

/-- **The comparison map of a Galois object is an isomorphism.** -/
theorem isIso_galoisCoverComparison_of_isGalois (A : FiniteEtaleOver X) [IsGalois A] :
    IsIso (Stacks.Descent.galoisCoverComparison A.hom
      (((MorphismProperty.Over.forget finiteEtale ⊤ X).mapAut A).comp (autInvAction A))) := by
  let p₁ := pullback.fst A.hom A.hom
  let p₂ := pullback.snd A.hom A.hom
  have hw : ∀ σ : Aut A, (σ⁻¹).asIso.hom.left ≫ A.hom = A.hom := fun σ => MorphismProperty.Over.w _
  have hO : ∀ σ : Aut A, (p₁ ≫ (σ⁻¹).asIso.hom.left) ≫ A.hom = p₂ ≫ A.hom := fun σ => by
    rw [Category.assoc, hw, pullback.condition]
  let s : Aut A → (A.left ⟶ pullback A.hom A.hom) := fun σ =>
    pullback.lift (𝟙 _) (σ⁻¹).asIso.hom.left (by rw [Category.id_comp, hw])
  have hs₁ : ∀ σ, s σ ≫ p₁ = 𝟙 _ := fun σ => pullback.lift_fst _ _ _
  have hs₂ : ∀ σ, s σ ≫ p₂ = (σ⁻¹).asIso.hom.left := fun σ => pullback.lift_snd _ _ _
  have hrange (σ : Aut A) := range_eq_agreeLocus_of_pullback_section A (hO σ) (hs₁ σ) (hs₂ σ)
  have : ∀ σ, IsOpenImmersion (s σ) := fun σ =>
    isOpenImmersion_of_pullback_section A (hO σ) (hs₁ σ) (hs₂ σ)
  have hdisj : Pairwise (Function.onFun Disjoint fun σ => Set.range (s σ).base) := by
    intro σ τ hστ
    change Disjoint (Set.range (s σ).base) (Set.range (s τ).base)
    rw [hrange σ, hrange τ, Set.disjoint_left]
    exact fun z hzσ hzτ => hστ (inv_injective (eq_of_mem_agreeLocus_aut A (hO σ) (hO τ) hzσ hzτ))
  have hsurj : Function.Surjective (Sigma.desc s).base := by
    intro z
    obtain ⟨τ, h, hz⟩ := exists_aut_mem_agreeLocus p₁ p₂ pullback.condition z
    obtain ⟨y, hy⟩ : z ∈ Set.range (s τ⁻¹).base := by
      rw [hrange]
      simp only [inv_inv]
      exact hz
    exact ⟨(Sigma.ι (fun _ : Aut A => A.left) τ⁻¹).base y, by
      rw [← Scheme.Hom.comp_apply, Sigma.ι_desc, hy]⟩
  change IsIso (Sigma.desc s)
  rw [isIso_iff_isOpenImmersion_and_surjective]
  exact ⟨isOpenImmersion_sigmaDesc _ s hdisj, ⟨hsurj⟩⟩

/-- **A Galois object of `FÉt_X` is a finite étale Galois cover with group its automorphism
group**, acting through inverses. -/
def FiniteEtaleGaloisCover.ofIsGalois (A : FiniteEtaleOver X) [IsGalois A] :
    FiniteEtaleGaloisCover X (Aut A) where
  obj := A
  connected := connectedSpace_left_of_isConnected A inferInstance
  action := autInvAction A
  comparisonIsIso := isIso_galoisCoverComparison_of_isGalois A

end AlgebraicGeometry

end
