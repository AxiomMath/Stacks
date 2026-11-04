module

public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginSpecBaseChangeSplit
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DescentDataBridge

/-!
# A semilinear involution is a gluing isomorphism for a degree two Galois covering

Let `g : T ⟶ S` be a morphism whose self-product splits as `T ×_S T = T ⨿ T`, the first
projection being the identity on both summands and the second being `1 ⨿ s` for an involution
`s` of `T` over `S`; the covering `{Spec k' ⟶ Spec k}` of Stacks 03FN is such a morphism, with
`s` the nonidentity Galois automorphism.  Let `V` be a scheme over `T`, with structure morphism
`p : V ⟶ T`.

Under the splitting, `V ×_S T` and `T ×_S V` are both `V ⨿ V`, so an isomorphism between them
over `T ×_S T` is a pair of automorphisms of `V`, one over each summand: the identity over the
diagonal summand, and over the twisted summand an automorphism `τ` lying over `s`, that is a
*semilinear* automorphism, `τ ≫ p = p ≫ s`.  This file carries out that assembly: it turns a
semilinear automorphism into the isomorphism `Θ : V ×_S T ≅ T ×_S V` of literal fibre products
in exactly the shape `AlgebraicGeometry.exists_transition_of_pullbackIso` consumes, including
the invariance clause for any morphism out of `V` which `τ` fixes.

What is *not* here is the cocycle condition.  `AlgebraicGeometry.exists_transition_of_pullbackIso`
derives it from an extensionality hypothesis on `V` — morphisms into `V` are determined by
their composites with `p` and with an invariant morphism `b` — and for the twisted doubled
origin no such `b` exists among morphisms of schemes, because the separating morphism out of
`X_{k'}` is the morphism to the algebraic space `X`.  With the splitting of this file the
cocycle is instead the four-summand identity `τ ∘ τ = 1`, `τ ∘ 1 = τ`, `1 ∘ τ = τ`,
`1 ∘ 1 = 1`; supplying it is what remains before the closing clause of Stacks 03FN can be
assembled.

## Main results

* `AlgebraicGeometry.exists_pullbackIso_of_semilinear`: **a semilinear automorphism of `V` is a
  candidate gluing isomorphism** `V ×_S T ≅ T ×_S V`, lying over `T ×_S T` and leaving every
  `τ`-invariant morphism out of `V` invariant.
* `AlgebraicGeometry.TwistedDoubledOrigin.specGaloisAction_involutive`: the Galois
  automorphism, read on spectra, is an involution, and
  `AlgebraicGeometry.TwistedDoubledOrigin.isIso_specGaloisAction` that it is an isomorphism.
* `AlgebraicGeometry.TwistedDoubledOrigin.exists_pullbackIso_of_semilinear_specExtension`: the
  same statement for the covering `{Spec k' ⟶ Spec k}` of the example.

## Implementation notes

The two identifications are the two orientations of
`AlgebraicGeometry.isPullback_baseChange_split_of_isPullback`: its `IsPullback.isoPullback`
presents `V ⨿ V` as `V ×_S T`, and the `IsPullback.flip` of the same square presents it as
`T ×_S V`.  Conjugating `1 ⨿ τ` by the two gives `Θ`, and each of the three conclusions is
then proved by cancelling the first identification — an isomorphism, hence an epimorphism — and
comparing the two sides on each summand, where they are read off by `coprod.hom_ext`.  The
hypothesis that `s` is an involution is used exactly once, in the clause saying that `Θ` lies
over the first factor: there the twisted summand contributes `τ ≫ p ≫ s = p ≫ s ≫ s`.

## References

* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
* [Stacks Project, Tag 03FN](https://stacks.math.columbia.edu/tag/03FN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A semilinear automorphism is a candidate gluing isomorphism.** Let `g : T ⟶ S` be a
morphism whose self-product splits as `T ⨿ T` with second projection `1 ⨿ s`, let `s` be an
involution, let `p : V ⟶ T` be a scheme over `T` and let `τ` be an automorphism of `V` lying
over `s`.  Then there is an isomorphism `Θ : V ×_S T ≅ T ×_S V` of fibre products which lies
over `T ×_S T` and for which every `τ`-invariant morphism out of `V` is invariant; read through
the splitting of `V ×_S T` as `V ⨿ V`, its `V`-component is the identity on the first summand
and `τ` on the second.

The first three conclusions are precisely the hypotheses `hΘ1`, `hΘ2` and `hΘ3` of
`AlgebraicGeometry.exists_transition_of_pullbackIso`; only its extensionality hypothesis, which
is what produces the cocycle condition, is not supplied.  The last conclusion reads `Θ` off
summandwise, which is what a direct verification of the cocycle condition needs instead. -/
theorem exists_pullbackIso_of_semilinear {S T V : Scheme.{u}} {g : T ⟶ S} {s : T ⟶ T}
    (hsplit : IsPullback (coprod.desc (𝟙 T) (𝟙 T)) (coprod.desc (𝟙 T) s) g g)
    (hss : s ≫ s = 𝟙 T) (p : V ⟶ T) (τ : V ⟶ V) [IsIso τ] (hτ : τ ≫ p = p ≫ s) :
    ∃ Θ : pullback (p ≫ g) g ≅ pullback g (p ≫ g),
      Θ.hom ≫ pullback.fst g (p ≫ g) = pullback.fst (p ≫ g) g ≫ p ∧
      Θ.hom ≫ pullback.snd g (p ≫ g) ≫ p = pullback.snd (p ≫ g) g ∧
      (∀ {Y : Scheme.{u}} (b : V ⟶ Y), τ ≫ b = b →
        Θ.hom ≫ pullback.snd g (p ≫ g) ≫ b = pullback.fst (p ≫ g) g ≫ b) ∧
      (isPullback_baseChange_split_of_isPullback hsplit p).isoPullback.hom ≫
          Θ.hom ≫ pullback.snd g (p ≫ g) = coprod.desc (𝟙 V) τ := by
  have hV := isPullback_baseChange_split_of_isPullback hsplit p
  set e₁ := hV.isoPullback with he₁
  set e₂ := hV.flip.isoPullback with he₂
  have h1f : e₁.hom ≫ pullback.fst (p ≫ g) g = coprod.desc (𝟙 V) (𝟙 V) :=
    hV.isoPullback_hom_fst
  have h1s : e₁.hom ≫ pullback.snd (p ≫ g) g = coprod.desc p (p ≫ s) :=
    hV.isoPullback_hom_snd
  have h2f : e₂.hom ≫ pullback.fst g (p ≫ g) = coprod.desc p (p ≫ s) :=
    hV.flip.isoPullback_hom_fst
  have h2s : e₂.hom ≫ pullback.snd g (p ≫ g) = coprod.desc (𝟙 V) (𝟙 V) :=
    hV.flip.isoPullback_hom_snd
  set m : V ⨿ V ≅ V ⨿ V := coprod.mapIso (Iso.refl V) (asIso τ) with hm
  have hmhom : m.hom = coprod.map (𝟙 V) τ := rfl
  have hΘ : (e₁.symm ≪≫ m ≪≫ e₂).hom = e₁.inv ≫ coprod.map (𝟙 V) τ ≫ e₂.hom := rfl
  have hkey : τ ≫ p ≫ s = p := by
    rw [← Category.assoc, hτ, Category.assoc, hss, Category.comp_id]
  refine ⟨e₁.symm ≪≫ m ≪≫ e₂, ?_, ?_, ?_, ?_⟩
  · rw [hΘ, Category.assoc, Category.assoc, Iso.inv_comp_eq, h2f,
      ← Category.assoc e₁.hom, h1f]
    apply coprod.hom_ext <;> simp [hkey]
  · rw [hΘ, Category.assoc, Category.assoc, Iso.inv_comp_eq, ← Category.assoc e₂.hom, h2s,
      h1s]
    apply coprod.hom_ext <;> simp [hτ]
  · intro Y b hb
    rw [hΘ, Category.assoc, Category.assoc, Iso.inv_comp_eq, ← Category.assoc e₂.hom, h2s,
      ← Category.assoc e₁.hom, h1f]
    apply coprod.hom_ext <;> simp [hb]
  · rw [hΘ, Category.assoc, Iso.hom_inv_id_assoc, Category.assoc, h2s]
    apply coprod.hom_ext <;> simp

namespace TwistedDoubledOrigin

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- The Galois automorphism, read on spectra, is an isomorphism, being induced by a ring
isomorphism. -/
instance isIso_specGaloisAction (σ : K ≃ₐ[k] K) : IsIso (specGaloisAction k K σ) := by
  have he : (Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op).hom =
      specGaloisAction k K σ := by
    dsimp [specGaloisAction]
    congr 1
  rw [← he]
  exact (Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op).isIso_hom

variable [FiniteDimensional k K] [IsGalois k K]

/-- For a degree two extension the Galois automorphism, read on spectra, is an involution. -/
theorem specGaloisAction_involutive (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) :
    specGaloisAction k K σ ≫ specGaloisAction k K σ = 𝟙 (Spec (.of K)) := by
  have hσsq : σ.trans σ = 1 := by
    show σ * σ = 1
    simpa only [IsGalois.card_aut_eq_finrank, hdegree, pow_two] using
      (pow_card_eq_one' (x := σ))
  have hσring : (σ : K →+* K).comp (σ : K →+* K) = RingHom.id K :=
    RingHom.ext (AlgEquiv.ext_iff.mp hσsq)
  dsimp [specGaloisAction]
  rw [← Spec.map_comp, ← Spec.map_id, Spec.map_injective.eq_iff, ← CommRingCat.ofHom_comp,
    hσring]
  simp

/-- **A semilinear automorphism of a `k'`-scheme is a candidate gluing isomorphism for the
covering `{Spec k' ⟶ Spec k}`.** This is
`AlgebraicGeometry.exists_pullbackIso_of_semilinear` for the covering of Stacks 03FN: the
splitting of the self-product is
`AlgebraicGeometry.TwistedDoubledOrigin.isPullback_specExtension_split` and the involution is
`AlgebraicGeometry.TwistedDoubledOrigin.specGaloisAction_involutive`. -/
theorem exists_pullbackIso_of_semilinear_specExtension (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) {V : Scheme.{u}} (p : V ⟶ Spec (.of K)) (τ : V ⟶ V) [IsIso τ]
    (hτ : τ ≫ p = p ≫ specGaloisAction k K σ) :
    ∃ Θ : pullback (p ≫ specExtension k K) (specExtension k K) ≅
        pullback (specExtension k K) (p ≫ specExtension k K),
      Θ.hom ≫ pullback.fst (specExtension k K) (p ≫ specExtension k K) =
          pullback.fst (p ≫ specExtension k K) (specExtension k K) ≫ p ∧
      Θ.hom ≫ pullback.snd (specExtension k K) (p ≫ specExtension k K) ≫ p =
          pullback.snd (p ≫ specExtension k K) (specExtension k K) ∧
      (∀ {Y : Scheme.{u}} (b : V ⟶ Y), τ ≫ b = b →
        Θ.hom ≫ pullback.snd (specExtension k K) (p ≫ specExtension k K) ≫ b =
          pullback.fst (p ≫ specExtension k K) (specExtension k K) ≫ b) ∧
      (isPullback_specExtension_baseChange_split k K hdegree σ hσ p).isoPullback.hom ≫
          Θ.hom ≫ pullback.snd (specExtension k K) (p ≫ specExtension k K) =
        coprod.desc (𝟙 V) τ :=
  exists_pullbackIso_of_semilinear (isPullback_specExtension_split k K hdegree σ hσ)
    (specGaloisAction_involutive k K hdegree σ) p τ hτ

end TwistedDoubledOrigin

end AlgebraicGeometry

end
