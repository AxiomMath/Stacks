module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.SolutionRingedTopos

/-!
# Rigidity of the transported morphisms of ringed topoi

Let `i : X ⟶ X₁` be a morphism of ringed topoi whose direct image is an equivalence and let
`𝒜` be a sheaf of rings on `X`. For two maps `φ, φ' : i⁻¹𝒪_{X₁} ⟶ 𝒜` the morphisms of ringed
topoi `(i, φ), (i, φ') : (Sh(X), 𝒜) ⟶ X₁` have the same underlying morphism of topoi, and a
2-isomorphism between them is a natural automorphism `α` of `i_*` compatible with `φ` and `φ'`.
If `φ` and `φ'` agree after a map `r : 𝒜 ⟶ 𝒪_X` whose composite with `φ` is an epimorphism of
sheaves of sets, then `α` is the identity on `𝒪_X`; when every natural endomorphism of the
identity of `Sh(X)` fixing `𝒪_X` is the identity, `α` is then the identity, and so `φ = φ'`
(`eq_of_withRingsHom_twoIso`).

This is how part (2) of [Stacks Project, Tag 0D17] uses Stacks 04KL: the morphism of algebraic
spaces recovered from a morphism of small étale ringed topoi is unique, but it reproduces the
given morphism of ringed topoi only up to 2-isomorphism, so the identification of its effect on
structure sheaves needs this rigidity. The 2-isomorphisms moving between `transport` and
`(i, φ)` are `transportCompWithRingsTwoIso` and `twoIsoTransportOfCompWithRings`.

## Main results
* `AlgebraicGeometry.Space.FlatThickeningDeformation.eq_of_withRingsHom_twoIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.Space.FlatThickeningDeformation

section FullyFaithfulRigidity

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟] {F : 𝒞 ⥤ 𝒟}

/-- The natural endomorphism of the identity of `𝒞` underlying a natural endomorphism of a fully
faithful functor `F`. -/
def natTransIdOfFullyFaithful (hF : F.FullyFaithful) (α : F ⟶ F) : 𝟭 𝒞 ⟶ 𝟭 𝒞 where
  app c := hF.preimage (α.app c)
  naturality c c' g := hF.map_injective (by simp [α.naturality])

/-- A natural endomorphism `α` of a fully faithful functor `F` out of a category in which every
natural endomorphism of the identity fixing `P` is the identity is the identity, as soon as it
fixes `F P`. -/
theorem natTrans_eq_id_of_fullyFaithful (hF : F.FullyFaithful) (P : 𝒞)
    (hrigid : ∀ τ : 𝟭 𝒞 ⟶ 𝟭 𝒞, τ.app P = 𝟙 _ → τ = 𝟙 _) (α : F ⟶ F) (hα : α.app P = 𝟙 _) :
    α = 𝟙 _ := by
  have hτ := hrigid (natTransIdOfFullyFaithful hF α) (by
    change hF.preimage (α.app P) = 𝟙 P
    rw [hα, hF.preimage_id])
  ext c
  have h := congrArg (fun τ : 𝟭 𝒞 ⟶ 𝟭 𝒞 => F.map (τ.app c)) hτ
  simp only [natTransIdOfFullyFaithful, hF.map_preimage] at h
  exact h.trans (F.map_id c)

end FullyFaithfulRigidity

section AdjunctionRigidity

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟] {L : 𝒟 ⥤ 𝒞}
  {R : 𝒞 ⥤ 𝒟} (adj : L ⊣ R) [R.IsEquivalence] {Y : 𝒟} {M N : 𝒞}

/-- A natural endomorphism `α` of the right adjoint `R` (an equivalence) relating the adjuncts of
`a` and `a'` is the identity on `N` when `a ≫ r = a' ≫ r` is an epimorphism. -/
theorem natTrans_app_eq_id_of_homEquiv (a a' : L.obj Y ⟶ M) (r : M ⟶ N) (hr : a ≫ r = a' ≫ r)
    (hepi : Epi (a ≫ r)) (α : R ⟶ R) (hc : adj.homEquiv _ _ a ≫ α.app M = adj.homEquiv _ _ a') :
    α.app N = 𝟙 _ := by
  have hu : adj.homEquiv _ _ (a ≫ r) ≫ α.app N = adj.homEquiv _ _ (a ≫ r) := by
    rw [Adjunction.homEquiv_naturality_right, Category.assoc, α.naturality, ← Category.assoc,
      hc, ← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_right, hr]
  have : Epi (adj.homEquiv _ _ (a ≫ r)) := by
    rw [Adjunction.homEquiv_unit]
    infer_instance
  exact (cancel_epi _).1 (hu.trans (Category.comp_id _).symm)

omit [R.IsEquivalence] in
/-- Adjuncts related by the identity natural transformation are equal. -/
theorem eq_of_homEquiv_comp_id (a a' : L.obj Y ⟶ M) (α : R ⟶ R) (hα : α = 𝟙 _)
    (hc : adj.homEquiv _ _ a ≫ α.app M = adj.homEquiv _ _ a') : a = a' := by
  subst hα
  exact (adj.homEquiv _ _).injective ((Category.comp_id _).symm.trans hc)

end AdjunctionRigidity

section RingedGeneric

universe v₀ u₀ w₀

variable {X X₁ X₂ : RingedTopos.{v₀, u₀, w₀}}
  [X.J.HasSheafCompose (forget RingCat.{w₀})] [X₁.J.HasSheafCompose (forget RingCat.{w₀})]
  [X₂.J.HasSheafCompose (forget RingCat.{w₀})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w₀} RingCat.{w₀})]
  [X₁.J.HasSheafCompose (forget₂ CommRingCat.{w₀} RingCat.{w₀})]
  [X₂.J.HasSheafCompose (forget₂ CommRingCat.{w₀} RingCat.{w₀})]
  [X.J.HasSheafCompose (forget CommRingCat.{w₀})] [X₁.J.HasSheafCompose (forget CommRingCat.{w₀})]
  [X₂.J.HasSheafCompose (forget CommRingCat.{w₀})]

/-- **Rigidity of `(i, φ)`**: two morphisms of ringed topoi `(i, φ), (i, φ') : (Sh(X), 𝒜) ⟶ X₁`
with `i_*` an equivalence which are 2-isomorphic have `φ = φ'`, when `φ ≫ r = φ' ≫ r` for a map
`r : 𝒜 ⟶ 𝒪_X` with `φ ≫ r` an epimorphism of sheaves of sets, and every natural endomorphism of
the identity of `Sh(X)` fixing `𝒪_X` is the identity. -/
theorem eq_of_withRingsHom_twoIso (i : RingedToposHom X X₁)
    [i.toToposHom.pushforward.IsEquivalence] {A : Sheaf X.J CommRingCat.{w₀}}
    (φ φ' : (inverseImageCommRingFunctor i.toToposHom).obj X₁.O ⟶ A) (r : A ⟶ X.O)
    (hr : φ ≫ r = φ' ≫ r) (hepi : Epi (X.forgetRing.map (φ ≫ r)))
    (hrigid : ∀ τ : 𝟭 (Sheaf X.J (Type w₀)) ⟶ 𝟭 _, τ.app (X.forgetRing.obj X.O) = 𝟙 _ →
      τ = 𝟙 _)
    (θ : RingedToposHom.TwoIso (A := withRings X A) (withRingsHom i φ) (withRingsHom i φ')) :
    φ = φ' := by
  have hc := θ.commutes
  simp only [forgetFSharp_withRingsHom] at hc
  have hepi' : Epi (X.forgetRing.map φ ≫ X.forgetRing.map r) := by
    rwa [← Functor.map_comp]
  have hr' : X.forgetRing.map φ ≫ X.forgetRing.map r =
      X.forgetRing.map φ' ≫ X.forgetRing.map r := by
    simp only [← Functor.map_comp, hr]
  let α : i.toToposHom.pushforward ⟶ i.toToposHom.pushforward := θ.e.hom
  have hα : α = 𝟙 _ := natTrans_eq_id_of_fullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful i.toToposHom.pushforward) _ hrigid α
    (natTrans_app_eq_id_of_homEquiv i.toToposHom.adj (X.forgetRing.map φ)
      (X.forgetRing.map φ') (X.forgetRing.map r) hr' hepi' α hc)
  exact X.forgetRing.map_injective (eq_of_homEquiv_comp_id i.toToposHom.adj
    (X.forgetRing.map φ) (X.forgetRing.map φ') α hα hc)

variable (i : RingedToposHom X X₁) [i.toToposHom.pushforward.IsEquivalence]
  (i₂ : RingedToposHom X X₂)
  (σ : (inverseImageCommRingFunctor i₂.toToposHom).obj X₂.O ⟶
    (inverseImageCommRingFunctor i.toToposHom).obj X₁.O)

/-- **`transport ∘ (i, 𝟙) ≅ (i₂, σ)`** as morphisms out of `(Sh(X), i⁻¹𝒪_{X₁})`: the square
`transportSquare` for the morphisms `(i, 𝟙)` and `(i₂, σ)`. -/
def transportCompWithRingsTwoIso :
    RingedToposHom.TwoIso.{v₀, u₀, w₀, v₀, u₀, w₀}
      (A := withRings X ((inverseImageCommRingFunctor i.toToposHom).obj X₁.O))
      ((transport i i₂ σ).comp (withRingsHom i (𝟙 _))) (withRingsHom i₂ σ) :=
  transportSquare (X := withRings X ((inverseImageCommRingFunctor i.toToposHom).obj X₁.O))
    (withRingsHom i (𝟙 _)) (withRingsHom i₂ σ) σ (by
    rw [withRingsHom_fSharpInverseImage, withRingsHom_fSharpInverseImage]
    exact Category.comp_id _)

/-- **A morphism `g` with `g ∘ (i, 𝟙) ≅ (i₂, σ)` is 2-isomorphic to `transport`.** -/
def twoIsoTransportOfCompWithRings (g : RingedToposHom X₁ X₂)
    (hA : RingedToposHom.TwoIso.{v₀, u₀, w₀, v₀, u₀, w₀}
      (A := withRings X ((inverseImageCommRingFunctor i.toToposHom).obj X₁.O))
      (g.comp (withRingsHom i (𝟙 _))) (withRingsHom i₂ σ)) :
    RingedToposHom.TwoIso.{v₀, u₀, w₀, v₀, u₀, w₀} g (transport i i₂ σ) :=
  letI := isIso_withRingsHom_id_fSharp i
  (compCompInverseTwoIso i g).symm.trans
    ((RingedToposHom.TwoIso.associator
      (B := withRings X ((inverseImageCommRingFunctor i.toToposHom).obj X₁.O))
      (RingedToposHom.inverse
        (X := withRings X ((inverseImageCommRingFunctor i.toToposHom).obj X₁.O))
        (withRingsHom i (𝟙 _))) (withRingsHom i (𝟙 _)) g).trans
      (RingedToposHom.TwoIso.whiskerLeft
        (RingedToposHom.inverse
          (X := withRings X ((inverseImageCommRingFunctor i.toToposHom).obj X₁.O))
          (withRingsHom i (𝟙 _))) hA))

end RingedGeneric

end AlgebraicGeometry.Space.FlatThickeningDeformation

end
