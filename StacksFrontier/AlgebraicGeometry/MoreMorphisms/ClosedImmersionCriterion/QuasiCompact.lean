module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.LiftingProperties.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ClosedImmersionCriterion.Affine

/-!
# The extensive criterion for closed immersions

A quasi-compact morphism of schemes is a closed immersion exactly when every commutative
square out of the spectrum of an injective ring map admits a diagonal lift.

## Main results

* `AlgebraicGeometry.isClosedImmersion_iff_lifts_injective_specMap_of_quasiCompact`:
  **Stacks Tag 0H2S.** The lifting criterion for a quasi-compact morphism.

## Implementation notes

The affine case is `AlgebraicGeometry.isClosedImmersion_iff_lifts_injective_specMap`
(Stacks Tag 0H2P), and the two directions here reduce to it differently. For the forward
direction the square is pulled back along the map out of `Spec A`, where the pullback is a
closed immersion onto an affine scheme and the affine case applies directly. For the converse
the property is Zariski-local at the target, so it suffices to treat an affine target; there
the lifting hypothesis applied to the finite affine cover of `X` splits the unit
`X ⟶ Spec Γ(X, ⊤)`, which makes `X` affine and reduces again to the affine case.

The name differs from the affine criterion's only by the `_of_quasiCompact` suffix, because
the affine statement occupies the unsuffixed name in this namespace.

## References

* [Stacks Project, Tag 0H2S](https://stacks.math.columbia.edu/tag/0H2S)
* [Stacks Project, Tag 0H2P](https://stacks.math.columbia.edu/tag/0H2P)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry


private theorem closed_affine_target_of_lifting
    {X Y : Scheme.{u}} [IsAffine Y] {f : X ⟶ Y} [QuasiCompact f]
    (hlift : ∀ (A B : Type u) [CommRing A] [CommRing B] (ψ : A →+* B),
      Function.Injective ψ →
      ∀ (g : Spec (.of B) ⟶ X) (h : Spec (.of A) ⟶ Y),
        (Spec.map (CommRingCat.ofHom ψ) ≫ h = g ≫ f) →
        ∃ l : Spec (.of A) ⟶ X,
          (Spec.map (CommRingCat.ofHom ψ) ≫ l = g) ∧ (l ≫ f = h)) :
    IsClosedImmersion f := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 : X.OpenCover := X.affineCover.finiteSubcover
  let U : Scheme := ∐ fun i : 𝒰.I₀ => 𝒰.X i
  let π : U ⟶ X := Sigma.desc fun i => 𝒰.f i
  have hπi (i : 𝒰.I₀) : Sigma.ι (fun i => 𝒰.X i) i ≫ π = 𝒰.f i := by
    simp [π]
  let ψ : Γ(X, ⊤) →+* Γ(U, ⊤) := π.appTop.hom
  have hψ : Function.Injective ψ := by
    refine fun a b hab => 𝒰.ext_elem a b fun i => ?_
    have h := congrArg (Sigma.ι (fun i => 𝒰.X i) i).appTop.hom hab
    change (𝒰.f i).appTop.hom a = (𝒰.f i).appTop.hom b
    simpa only [← hπi i, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.comp_apply] using h
  let g : Spec (.of Γ(U, ⊤)) ⟶ X := U.isoSpec.inv ≫ π
  have hg : g ≫ X.toSpecΓ = Spec.map (CommRingCat.ofHom ψ) := by
    dsimp [g, ψ]
    rw [Category.assoc, Scheme.toSpecΓ_naturality]
    simp
  let q : Spec (.of Γ(X, ⊤)) ⟶ Y :=
    Spec.map f.appTop ≫ Y.isoSpec.inv
  have hsq : Spec.map (CommRingCat.ofHom ψ) ≫ q = g ≫ f := by
    dsimp only [q]
    rw [← hg, Category.assoc, ← Category.assoc X.toSpecΓ, ← Scheme.toSpecΓ_naturality f]
    simp
  obtain ⟨l, hl, _⟩ := hlift Γ(X, ⊤) Γ(U, ⊤) ψ hψ g q hsq
  have hsplit : g ≫ X.toSpecΓ ≫ l = g := by rw [← Category.assoc, hg, hl]
  have hπ : π ≫ X.toSpecΓ ≫ l = π := by simpa [g] using U.isoSpec.hom ≫= hsplit
  have hret : X.toSpecΓ ≫ l = 𝟙 X := by
    apply 𝒰.hom_ext
    intro i
    rw [← hπi i]
    simpa only [Category.assoc, Category.comp_id] using Sigma.ι (fun i => 𝒰.X i) i ≫= hπ
  have : IsSplitMono ((reflectorAdjunction Scheme.Spec).unit.app X) := ⟨⟨l, hret⟩⟩
  have : IsAffine X := essImage_Spec.mp (mem_essImage_of_unit_isSplitMono (i := Scheme.Spec))
  exact (isClosedImmersion_iff_lifts_injective_specMap f).2 hlift

private theorem lifting_of_pullback
    {X Y V : Scheme.{u}} (f : X ⟶ Y) (j : V ⟶ Y)
    (hlift : ∀ (A B : Type u) [CommRing A] [CommRing B] (ψ : A →+* B),
      Function.Injective ψ →
      ∀ (g : Spec (.of B) ⟶ X) (h : Spec (.of A) ⟶ Y),
        (Spec.map (CommRingCat.ofHom ψ) ≫ h = g ≫ f) →
        ∃ l : Spec (.of A) ⟶ X,
          (Spec.map (CommRingCat.ofHom ψ) ≫ l = g) ∧ (l ≫ f = h)) :
    ∀ (A B : Type u) [CommRing A] [CommRing B] (ψ : A →+* B),
      Function.Injective ψ →
      ∀ (g : Spec (.of B) ⟶ pullback f j) (h : Spec (.of A) ⟶ V),
        (Spec.map (CommRingCat.ofHom ψ) ≫ h = g ≫ pullback.snd f j) →
        ∃ l : Spec (.of A) ⟶ pullback f j,
          (Spec.map (CommRingCat.ofHom ψ) ≫ l = g) ∧ (l ≫ pullback.snd f j = h) := by
  intro A B _ _ ψ hψ g h hsq
  let i := Spec.map (CommRingCat.ofHom ψ)
  have : HasLiftingProperty i f := ⟨fun {g} {h} sq => by
    obtain ⟨l, hl₁, hl₂⟩ := hlift A B ψ hψ g h sq.w.symm
    exact ⟨⟨⟨l, hl₁, hl₂⟩⟩⟩⟩
  let sq : CommSq g i (pullback.snd f j) h := ⟨hsq.symm⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- A quasi-compact scheme morphism is a closed immersion exactly when maps out of
spectra lift against every injective homomorphism of commutative rings. -/
@[stacks 0H2S]
public theorem isClosedImmersion_iff_lifts_injective_specMap_of_quasiCompact
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] :
    IsClosedImmersion f ↔
      ∀ (A B : Type u) [CommRing A] [CommRing B] (ψ : A →+* B),
      Function.Injective ψ →
      ∀ (g : Spec (.of B) ⟶ X) (h : Spec (.of A) ⟶ Y),
        (Spec.map (CommRingCat.ofHom ψ) ≫ h = g ≫ f) →
        ∃ l : Spec (.of A) ⟶ X,
          (Spec.map (CommRingCat.ofHom ψ) ≫ l = g) ∧ (l ≫ f = h) := by
  refine ⟨fun hf A B _ _ ψ hψ g h hsq => ?_, fun hlift => ?_⟩
  · let p : pullback f h ⟶ Spec (.of A) := pullback.snd f h
    have : IsAffine (pullback f h) := isAffine_of_isAffineHom p
    let k : Spec (.of B) ⟶ pullback f h := pullback.lift g (Spec.map (CommRingCat.ofHom ψ)) hsq.symm
    have hq : Spec.map (CommRingCat.ofHom ψ) ≫ 𝟙 (Spec (.of A)) = k ≫ p := by
      simp only [Category.comp_id, k, p, pullback.lift_snd]
    obtain ⟨l, hl₁, hl₂⟩ :=
      (isClosedImmersion_iff_lifts_injective_specMap p).1 inferInstance
        A B ψ hψ k (𝟙 _) hq
    refine ⟨l ≫ pullback.fst f h, ?_, ?_⟩
    · simpa only [Category.assoc, k, pullback.lift_fst] using hl₁ =≫ pullback.fst f h
    · simpa only [p, Category.assoc, pullback.condition, Category.id_comp] using hl₂ =≫ h
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) Y.affineCover]
    intro i
    exact closed_affine_target_of_lifting (f := pullback.snd f (Y.affineCover.f i))
      (lifting_of_pullback f (Y.affineCover.f i) hlift)

end AlgebraicGeometry

end
