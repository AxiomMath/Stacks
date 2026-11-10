module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-!
# Base change of the generic point of an integral affine scheme

Let `A` be a domain with fraction field `K`, and let `i : Spec A ⟶ Y` be a morphism of schemes.
If a morphism `r : V ⟶ Y` meets the image of `i` only in the image of the generic point of
`Spec A`, then the base change of `Spec K ⟶ Spec A ⟶ Y` along `r` is the base change of `i`
along `r`. In particular it is locally of finite presentation when `i` is.

## Main results

* `AlgebraicGeometry.exists_comp_specMap_fractionRing_eq`: a morphism to `Spec A` all of whose
  points map to the generic point factors through `Spec K`.
* `AlgebraicGeometry.locallyOfFinitePresentation_pullback_fst_fractionRing`: the base change of
  `Spec K ⟶ Y` along `r` is locally of finite presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe u

variable {A K : Type u} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

/-- **A morphism to the spectrum of a domain landing in the generic point factors through the
spectrum of the fraction field.** If `t : T ⟶ Spec A` sends every point of `T` to the zero
ideal, then `t` factors as `s ≫ Spec.map (algebraMap A K)` for some `s : T ⟶ Spec K`. -/
theorem exists_comp_specMap_fractionRing_eq {T : Scheme.{u}} (t : T ⟶ Spec (.of A))
    (ht : ∀ x, (t.base x).asIdeal = ⊥) :
    ∃ s : T ⟶ Spec (.of K), s ≫ Spec.map (CommRingCat.ofHom (algebraMap A K)) = t := by
  classical
  let e := ΓSpec.adjunction.homEquiv T (op (CommRingCat.of A))
  obtain ⟨φ, rfl⟩ := e.surjective t
  have hφ : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (e φ).appTop = φ.unop :=
    ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ.unop
  have hunit : ∀ y : nonZeroDivisors A, IsUnit (φ.unop.hom y) := by
    intro y
    refine RingedSpace.isUnit_of_isUnit_germ T.toRingedSpace ⊤ (φ.unop.hom y) fun x _ => ?_
    have hmem : x ∈ T.basicOpen
        ((e φ).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (y : A))) := by
      rw [← Scheme.preimage_basicOpen_top]
      change x ∈ e φ ⁻¹ᵁ (Spec (.of A)).basicOpen _
      rw [basicOpen_eq_of_affine (R := CommRingCat.of A) (y : A)]
      change (y : A) ∉ ((e φ).base x).asIdeal
      rw [ht x]
      exact fun h => nonZeroDivisors.ne_zero y.2 ((Ideal.mem_bot).1 h)
    have hy : φ.unop.hom y = (e φ).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (y : A)) := by
      rw [← hφ]; rfl
    rw [hy]
    exact (Scheme.mem_basicOpen_top _ _ _).1 hmem
  let ψ : CommRingCat.of K ⟶ Γ(T, ⊤) :=
    CommRingCat.ofHom (IsLocalization.lift (M := nonZeroDivisors A) (S := K) hunit)
  let ψ' : Scheme.Γ.rightOp.obj T ⟶ op (CommRingCat.of K) := ψ.op
  refine ⟨ΓSpec.adjunction.homEquiv T (op (CommRingCat.of K)) ψ', ?_⟩
  have h1 := ΓSpec.adjunction.homEquiv_naturality_right ψ' (CommRingCat.ofHom (algebraMap A K)).op
  refine h1.symm.trans (congrArg e ?_)
  apply Quiver.Hom.unop_inj
  ext a
  exact IsLocalization.lift_eq (M := nonZeroDivisors A) (S := K) hunit a

/-- **The base change of the generic point along a morphism meeting the closure only there.**
Let `i : Spec A ⟶ Y` be locally of finite presentation and let `r : V ⟶ Y` be such that every
point of `V` whose image lies in the image of `i` maps to the image of the generic point. Then
the base change of `Spec K ⟶ Spec A ⟶ Y` along `r` is locally of finite presentation. -/
theorem locallyOfFinitePresentation_pullback_fst_fractionRing {Y V : Scheme.{u}}
    (i : Spec (.of A) ⟶ Y) [LocallyOfFinitePresentation i] (r : V ⟶ Y)
    (hr : ∀ (v : V) (z : Spec (.of A)), r.base v = i.base z → z.asIdeal = ⊥) :
    LocallyOfFinitePresentation
      (pullback.fst r (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ i)) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap A K))
  have : IsPreimmersion g := IsPreimmersion.of_isLocalization (nonZeroDivisors A)
  have ht : ∀ x, ((pullback.snd r i).base x).asIdeal = ⊥ := by
    intro x
    refine hr ((pullback.fst r i).base x) _ ?_
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  obtain ⟨s, hs⟩ := exists_comp_specMap_fractionRing_eq (K := K) (pullback.snd r i) ht
  have hiso : IsIso (pullback.fst (pullback.snd r i) g) := by
    refine ⟨⟨pullback.lift (𝟙 _) s (by rw [Category.id_comp, hs]), ?_, pullback.lift_fst _ _ _⟩⟩
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp, ← cancel_mono g, Category.assoc,
        hs, pullback.condition]
  rw [← pullbackLeftPullbackSndIso_inv_fst]
  infer_instance

/-- `AlgebraicGeometry.locallyOfFinitePresentation_pullback_fst_fractionRing` for a source only
isomorphic to the spectrum of the fraction field. -/
theorem locallyOfFinitePresentation_pullback_fst_of_iso_fractionRing {Y V W : Scheme.{u}}
    (i : Spec (.of A) ⟶ Y) [LocallyOfFinitePresentation i] (r : V ⟶ Y)
    (hr : ∀ (v : V) (z : Spec (.of A)), r.base v = i.base z → z.asIdeal = ⊥)
    (j : W ⟶ Y) (e : W ≅ Spec (.of K))
    (hj : j = e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ i) :
    LocallyOfFinitePresentation (pullback.fst r j) := by
  have := locallyOfFinitePresentation_pullback_fst_fractionRing (K := K) i r hr
  subst hj
  rw [← pullbackLeftPullbackSndIso_inv_fst]
  infer_instance

end AlgebraicGeometry

end
