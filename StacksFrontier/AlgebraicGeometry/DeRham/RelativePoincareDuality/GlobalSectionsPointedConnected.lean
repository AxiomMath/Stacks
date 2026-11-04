module

public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.GlobalSectionsUnramified
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Sections
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.IsIsoAppTop

/-!
# Global functions of a connected proper smooth scheme with a rational point

Let `Z` be proper and smooth over a field `k`, connected, with a `k`-rational point. Then
`Γ(Z, 𝒪_Z) = k`. Indeed `Z` is normal, so `Γ(Z, 𝒪_Z)` is a finite product of finite field
extensions of `k` ([Stacks, Tag 0BUG]); since `Z` is connected, `Γ(Z, 𝒪_Z)` has no idempotent other
than `0` and `1`, so there is exactly one factor; and evaluation at the rational point is a
`k`-algebra map from that field to `k`, hence injective.

## Main results

* `AlgebraicGeometry.finrank_globalSections_eq_one_of_section`: a connected proper smooth scheme
  over `k` with a `k`-rational point has `Γ(Z, 𝒪_Z)` one-dimensional over `k`.
* `AlgebraicGeometry.finrank_globalSections_fiber_eq_one_of_section`: the fibres of a proper smooth
  morphism `X ⟶ Spec B` with a section and with `B = Γ(X, 𝒪_X)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A nontrivial commutative ring whose only idempotents are `0` and `1`, and which is a finite
product of fields, has exactly one factor. -/
theorem eq_one_of_ringEquiv_pi_isField {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    {K : Fin n → Type*} [∀ i, CommRing (K i)] (hK : ∀ i, IsField (K i)) (e : R ≃+* ∀ i, K i)
    (hidem : ∀ x : R, IsIdempotentElem x → x = 0 ∨ x = 1) : n = 1 := by
  have hnt : ∀ i, (1 : K i) ≠ 0 := fun i h10 => by
    obtain ⟨a, b, hab⟩ := (hK i).exists_pair_ne
    exact hab (by rw [← mul_one a, ← mul_one b, h10, mul_zero, mul_zero])
  rcases Nat.lt_or_ge n 1 with h0 | h1
  · have : IsEmpty (Fin n) := by rw [Nat.lt_one_iff.mp h0]; infer_instance
    exact (one_ne_zero (e.injective (Subsingleton.elim _ _) : (1 : R) = 0)).elim
  by_contra hne
  let i₀ : Fin n := ⟨0, h1⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  have hi : IsIdempotentElem (e.symm (Pi.single i₀ 1)) := by
    show e.symm _ * e.symm _ = e.symm _
    rw [← map_mul, ← Pi.single_mul, one_mul]
  have hne : i₁ ≠ i₀ := by simp [i₁, i₀, Fin.ext_iff]
  rcases hidem _ hi with h | h
  · exact hnt i₀ (by simpa only [RingEquiv.apply_symm_apply, map_zero, Pi.zero_apply,
      Pi.single_eq_same] using congrArg (fun x => e x i₀) h)
  · exact hnt i₁ (Eq.symm <| by simpa only [RingEquiv.apply_symm_apply, map_one, Pi.one_apply,
      (Pi.single_eq_of_ne hne)] using congrArg (fun x => e x i₁) h)

/-- **The global functions of a connected proper smooth scheme with a rational point are the
base field.** For `h : Z ⟶ Spec k` proper and smooth with `Z` connected and with a section `σ`,
`Γ(Z, 𝒪_Z)` is one-dimensional over `k`. -/
theorem finrank_globalSections_eq_one_of_section (k : Type u) [Field k] {Z : Scheme.{u}}
    (h : Z ⟶ Spec (.of k)) [IsProper h] [Smooth h] [PreconnectedSpace Z]
    (σ : Spec (.of k) ⟶ Z) (hσ : σ ≫ h = 𝟙 _) :
    letI : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ h.appTop).hom.toAlgebra
    Module.finrank k Γ(Z, ⊤) = 1 := by
  let : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ h.appTop).hom.toAlgebra
  have : IsNormal Z := isNormal_of_isRegular Z (isRegular_of_smooth_over_field h)
  obtain ⟨D⟩ := globalSectionsFieldDecomposition_of_isNormal k h
  let ev : Γ(Z, ⊤) →ₐ[k] k :=
    { toRingHom := (σ.appTop ≫ (Scheme.ΓSpecIso (.of k)).hom).hom
      commutes' := fun r => by
        show ((Scheme.ΓSpecIso (.of k)).inv ≫ h.appTop ≫ σ.appTop ≫
          (Scheme.ΓSpecIso (.of k)).hom).hom r = r
        rw [← Category.assoc h.appTop, ← Scheme.Hom.comp_appTop, hσ]
        simp }
  have : Nontrivial Γ(Z, ⊤) :=
    ⟨⟨1, 0, fun h1 => one_ne_zero (show (1 : k) = 0 by simpa using congrArg ev h1)⟩⟩
  have hidem : ∀ e : Γ(Z, ⊤), IsIdempotentElem e → e = 0 ∨ e = 1 := fun e he =>
    Stacks.AlgebraicGeometry.ProperGeomConnected.isIdempotentElem_eq_zero_or_one
      (by simpa using isPreconnected_univ) he
  let E := D.algEquiv
  have : ∀ i, Module.Finite k (D.factor i) := D.factorModuleFinite
  have hN : D.numFactors = 1 :=
    eq_one_of_ringEquiv_pi_isField D.factorIsField E.toRingEquiv hidem
  let i₀ : Fin D.numFactors := ⟨0, by omega⟩
  have hall : ∀ i : Fin D.numFactors, i = i₀ := fun i => Fin.ext (by have := i.2; omega)
  have hinj : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    have hEx : ∀ i, E x i ≠ 0 := by
      intro i hi
      apply hx0
      apply E.injective
      funext j
      rw [hall j, ← hall i, hi, map_zero]
      rfl
    have hu : IsUnit (E x) := Pi.isUnit_iff.2 fun i => by
      obtain ⟨b, hb⟩ := (D.factorIsField i).mul_inv_cancel (hEx i)
      exact IsUnit.of_mul_eq_one b hb
    have hu' : IsUnit x := by simpa using hu.map E.symm
    have := hu'.map ev
    rw [hx] at this
    exact not_isUnit_zero this
  have : Module.Finite k Γ(Z, ⊤) := Module.Finite.equiv E.symm.toLinearEquiv
  have hle : Module.finrank k Γ(Z, ⊤) ≤ 1 := by
    simpa using LinearMap.finrank_le_finrank_of_injective (f := ev.toLinearMap) hinj
  exact le_antisymm hle Module.finrank_pos

/-- **The fibres of a proper smooth morphism with a section and with the right global functions
have the residue field as global functions.** For `g : X ⟶ Spec B` proper and smooth, with a
section and with `B ⟶ Γ(X, 𝒪_X)` bijective, every fibre `X_s` has `Γ(X_s, 𝒪) = κ(s)`: the fibres
are connected ([Stacks, Tag 03H2]) and the section gives a rational point. -/
theorem finrank_globalSections_fiber_eq_one_of_section {X : Scheme.{u}} {B : CommRingCat.{u}}
    (g : X ⟶ Spec B) [IsProper g] [Smooth g] [IsIso g.appTop] (σ : Spec B ⟶ X)
    (hσ : σ ≫ g = 𝟙 _) (s : Spec B) :
    letI : Algebra ((Spec B).residueField s) Γ(g.fiber s, ⊤) :=
      ((Scheme.ΓSpecIso (.of ((Spec B).residueField s))).inv ≫
        (g.fiberToSpecResidueField s).appTop).hom.toAlgebra
    Module.finrank ((Spec B).residueField s) Γ(g.fiber s, ⊤) = 1 := by
  have := Stacks.SteinFactorization.geometricallyConnected_of_isIso_appTop g
  have : IsProper (g.fiberToSpecResidueField s) :=
    MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback _ _) inferInstance
  have : Smooth (g.fiberToSpecResidueField s) :=
    MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback _ _) inferInstance
  let σs : Spec ((Spec B).residueField s) ⟶ g.fiber s :=
    pullback.lift ((Spec B).fromSpecResidueField s ≫ σ) (𝟙 _)
      (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])
  exact finrank_globalSections_eq_one_of_section ((Spec B).residueField s)
    (g.fiberToSpecResidueField s) σs (pullback.lift_snd _ _ _)

end AlgebraicGeometry
