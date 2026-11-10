module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.SchemeTheoreticImage
public import StacksCore.Tactic.StacksAttribute

/-!
# Models of schemes over the fraction field of a discrete valuation ring

Let `R` be a discrete valuation ring with fraction field `K`. A *model* of a `K`-scheme `V` is a
finite-type flat `R`-scheme `X` together with an identification of its generic fibre with `V`.
The scheme-theoretic image in a model of a closed subscheme of its generic fibre is again a
model.

## Main definitions

* `Stacks.Models.IsModel` expresses that a finite-type flat `R`-scheme, together with a chosen
  identification of its generic fibre, is a model of a `K`-scheme.

## Main results

* `Stacks.Models.schemeTheoreticImage_isModel` says that the scheme-theoretic image of a closed
  immersion into the generic fibre of a model is a model.

## Implementation notes

A model includes its chosen generic-fibre isomorphism. The scheme-theoretic image is taken for
the composite from the closed subscheme through that isomorphism and the first pullback
projection. Finite type is represented, as in Mathlib, by local finite type together with
quasi-compactness.

Flatness of the image over `R` is checked on the affine charts of the closed subscheme cut out by
the kernel ideal sheaf. On such a chart the coordinate ring is `A ⧸ I` for `A` the coordinate ring
of an affine open of the model and `I` the kernel ideal; it embeds into the sections of the source
over the corresponding open, where every nonzero element of `R` acts invertibly, so it is
torsion-free and hence flat over the Bézout domain `R`.

## References

* [Stacks Project, Tag 0C2S](https://stacks.math.columbia.edu/tag/0C2S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Models

open AlgebraicGeometry

universe u

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- A finite-type flat `R`-scheme with a specified identification of its generic fibre with
the `K`-scheme `V`. -/
def IsModel {V X : Scheme.{u}} (v : V ⟶ Spec (CommRingCat.of K))
    (p : X ⟶ Spec (CommRingCat.of R))
    (e : V ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))) : Prop :=
  Flat p ∧ LocallyOfFiniteType p ∧ QuasiCompact p ∧
    e.hom ≫ pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R K))) = v

/-- The generic fibre of `Spec R` is an open subscheme of `Spec R`: the fraction field of a
discrete valuation ring is obtained by inverting a uniformizer. -/
theorem genericFiberSpec_isOpenImmersion :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away π K := by
    change IsLocalization (Submonoid.powers π) K
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_, n, rfl⟩
      exact isUnit_iff_ne_zero.mpr <| by simpa using pow_ne_zero n hπ.ne_zero
    · intro z
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R z
      obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (mem_nonZeroDivisors_iff_ne_zero.mp hb) hπ
      refine ⟨(a * (↑(v⁻¹) : R), ⟨π ^ n, ⟨n, rfl⟩⟩), ?_⟩
      have hπK : algebraMap R K π ≠ 0 := by simpa using hπ.ne_zero
      have hvK : algebraMap R K (v : R) ≠ 0 := by simp
      rw [hv]
      calc
        (algebraMap R K a / algebraMap R K (↑v * π ^ n)) * algebraMap R K (π ^ n) =
            algebraMap R K a / algebraMap R K (↑v) := by
              rw [map_mul]
              field_simp [hπK, hvK]
        _ = algebraMap R K (a * ↑(v⁻¹)) := by
          rw [map_mul]
          simp [div_eq_mul_inv]
    · intro x y hxy
      obtain rfl := IsFractionRing.injective R K hxy
      exact ⟨1, by simp⟩
  exact AlgebraicGeometry.IsOpenImmersion.of_isLocalization π

/-- An algebra over a Bézout domain `S` that embeds into an algebra in which every regular
element of `S` acts invertibly is flat: it is torsion-free, and over a Bézout domain a
torsion-free module is flat. -/
private theorem flat_of_injective_hom_into_unitScalarAlgebra
    {S A B : Type u} [CommRing S] [IsDomain S] [IsBezout S]
    [CommRing A] [Algebra S A] [CommRing B] [Algebra S B]
    (φ : A →ₐ[S] B) (hφ : Function.Injective φ)
    (hunit : ∀ s, IsRegular s → IsUnit (algebraMap S B s)) : Module.Flat S A := by
  have : Module.IsTorsionFree S B := by
    constructor
    intro s hs x y hxy
    apply (hunit s hs).mul_left_cancel
    simpa [Algebra.smul_def] using hxy
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  exact Function.Injective.moduleIsTorsionFree φ hφ (fun s a => by simp)

/-- If `φ.comp α` factors through the fraction field `K` of `R`, then `A ⧸ ker φ` is flat over
`R`. -/
private theorem flat_quotientMk_ker_comp_of_comp_eq {A B : Type u} [CommRing A] [CommRing B]
    (α : R →+* A) (φ : A →+* B) (θ : K →+* B) (hcomp : φ.comp α = θ.comp (algebraMap R K)) :
    ((Ideal.Quotient.mk (RingHom.ker φ)).comp α).Flat := by
  let : Algebra R A := α.toAlgebra
  let : Algebra R B := (θ.comp (algebraMap R K)).toAlgebra
  let φ' : A →ₐ[R] B := { toRingHom := φ, commutes' := RingHom.congr_fun hcomp }
  have hφ : ∀ a ∈ RingHom.ker φ, φ a = 0 := fun _ => RingHom.mem_ker.mp
  refine RingHom.flat_algebraMap_iff.mpr <| flat_of_injective_hom_into_unitScalarAlgebra
    (Ideal.Quotient.liftₐ _ φ' hφ) (RingHom.lift_injective_of_ker_le_ideal _ hφ le_rfl)
    fun r hr => ?_
  change IsUnit (θ (algebraMap R K r))
  exact IsUnit.map θ (isUnit_iff_ne_zero.mpr
    (fun h => hr.ne_zero (IsFractionRing.injective R K (by simpa using h))))

/-- On the affine chart over `U`, the scheme-theoretic image of `g` followed by `p` is the
spectrum of the quotient of `Γ(X, U)` by the kernel ideal of `g`. -/
private theorem subschemeCover_f_imageι_comp {S : CommRingCat.{u}} {V X : Scheme.{u}} (g : V ⟶ X)
    [QuasiCompact g] (p : X ⟶ Spec S) (U : X.affineOpens) :
    g.ker.subschemeCover.f U ≫ g.imageι ≫ p = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (g.ker.ideal U)).comp
        ((p.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso S).inv.hom) : S →+* _)) := by
  let qmk : CommRingCat.of Γ(X, U.1) ⟶ CommRingCat.of (Γ(X, U.1) ⧸ g.ker.ideal U) :=
    CommRingCat.ofHom (Ideal.Quotient.mk _)
  change (g.ker.subschemeCover.f U ≫ g.ker.subschemeι) ≫ p = _
  rw [g.ker.subschemeCover_map_subschemeι U, g.ker.glueDataObjι_ι U]
  calc
    _ = Spec.map qmk ≫ (U.2.fromSpec ≫ p) := rfl
    _ = Spec.map qmk ≫ (Spec.map (p.appLE ⊤ U.1 le_top) ≫ (isAffineOpen_top _).fromSpec) :=
      congrArg (fun k => Spec.map qmk ≫ k)
        ((isAffineOpen_top _).SpecMap_appLE_fromSpec p U.2 le_top).symm
    _ = _ := by
      simp [qmk, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec, Scheme.ΓSpecIso_inv]
      congr 2

/-- The scheme-theoretic image of a quasi-compact morphism to a flat `R`-scheme, whose composite
to `Spec R` factors through the generic fibre, is flat over `R`. Flatness is checked on the
affine charts of the closed subscheme cut out by the kernel ideal sheaf. -/
private theorem flat_imageι_comp {V₁ X₂ : Scheme.{u}}
    (v₁ : V₁ ⟶ Spec (CommRingCat.of K)) (p₂ : X₂ ⟶ Spec (CommRingCat.of R)) [Flat p₂]
    (g : V₁ ⟶ X₂) [QuasiCompact g]
    (hg : g ≫ p₂ = v₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    Flat (g.imageι ≫ p₂) := by
  let i := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let 𝒰 := g.ker.subschemeCover
  have : ∀ j, IsAffine (𝒰.openCover.X j) := fun j => Scheme.isAffine_affineOpenCover _ 𝒰 j
  apply HasRingHomProperty.of_source_openCover (P := @Flat) 𝒰.openCover
  intro U
  let U₀ : X₂.affineOpens := U
  let W : V₁.Opens := g ⁻¹ᵁ U₀.1
  let γR := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let γK := (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  let δ := (p₂.appLE ⊤ U₀.1 le_top).hom
  let α : R →+* Γ(X₂, U₀.1) := δ.comp γR
  let φ : Γ(X₂, U₀.1) →+* Γ(V₁, W) := (g.appLE U₀.1 W le_rfl).hom
  let θ : K →+* Γ(V₁, W) := (v₁.appLE ⊤ W (by simp)).hom.comp γK
  have hker : RingHom.ker φ = g.ker.ideal U₀ := by
    change RingHom.ker (g.appLE U₀.1 W le_rfl).hom = g.ker.ideal U₀
    rw [← Scheme.Hom.app_eq_appLE]
    exact (g.ker_apply U).symm
  have hcompCat : p₂.appLE ⊤ U₀.1 le_top ≫ g.appLE U₀.1 W le_rfl =
      i.appLE ⊤ ⊤ le_top ≫ v₁.appLE ⊤ W (by simp) := by
    calc
      _ = (g ≫ p₂).appLE ⊤ W (by simp) :=
        Scheme.Hom.appLE_comp_appLE g p₂ ⊤ U₀.1 W le_top le_rfl
      _ = (v₁ ≫ i).appLE ⊤ W (by simp) := by rw [hg]
      _ = _ := Scheme.Hom.appLE_comp_appLE v₁ i ⊤ ⊤ W le_top (by simp)
  have hi : (i.appLE ⊤ ⊤ le_top).hom.comp γR = γK.comp (algebraMap R K) := by
    have htop : i.appTop = i.appLE ⊤ ⊤ le_top := by
      simpa [Scheme.Hom.appTop] using (i.app_eq_appLE (U := ⊤))
    have h := congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K)))
    have h' : γK.comp (algebraMap R K) = i.appTop.hom.comp γR := by
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, γK, γR, i] using h
    rw [htop] at h'
    exact h'.symm
  have hcomp : φ.comp α = θ.comp (algebraMap R K) := by
    have hmaps : φ.comp δ = (v₁.appLE ⊤ W (by simp)).hom.comp (i.appLE ⊤ ⊤ le_top).hom :=
      congrArg CommRingCat.Hom.hom hcompCat
    dsimp only [α, θ]
    rw [← RingHom.comp_assoc, hmaps, RingHom.comp_assoc, hi, RingHom.comp_assoc]
  have hflat := flat_quotientMk_ker_comp_of_comp_eq α φ θ hcomp
  rw [hker] at hflat
  have hflatChart : Flat (g.ker.subschemeCover.f U₀ ≫ g.imageι ≫ p₂) := by
    rw [subschemeCover_f_imageι_comp g p₂ U₀]
    exact Flat.SpecMap_iff.2 hflat
  exact HasRingHomProperty.appTop (P := @Flat) _ hflatChart

/-- If `g = q ≫ a` with `q` a closed immersion and `a` an open immersion, then `q` identifies
the source of `g` with the base change along `a` of the scheme-theoretic image of `g`. -/
private theorem exists_isIso_comp_pullback_fst_eq {V X Y : Scheme.{u}} (q : V ⟶ X) (a : X ⟶ Y)
    (g : V ⟶ Y) [IsClosedImmersion q] [IsOpenImmersion a] [QuasiCompact g] (hqa : q ≫ a = g) :
    ∃ t : V ⟶ pullback a g.imageι, IsIso t ∧ t ≫ pullback.fst a g.imageι = q := by
  let j : V ⟶ pullback g a := pullback.lift (𝟙 V) q (by simpa using hqa.symm)
  have hj : j ≫ pullback.fst g a = 𝟙 V := pullback.lift_fst _ _ _
  have : IsSplitEpi (pullback.fst g a) := .mk' ⟨j, hj⟩
  have : IsIso (pullback.fst g a) := isIso_of_mono_of_isSplitEpi _
  have hfst : pullback.fst g a ≫ q = pullback.snd g a :=
    (cancel_mono a).1 <| by rw [Category.assoc, hqa, pullback.condition]
  have hkerq : q.ker = g.ker.comap a := by
    rw [← Scheme.Hom.ker_comp_of_isIso (pullback.fst g a) q, hfst]
    exact AlgebraicGeometry.ker_pullback_snd_eq_comap a g
  have htc : q ≫ a = g.toImage ≫ g.imageι := by rw [hqa, Scheme.Hom.toImage_imageι]
  refine ⟨pullback.lift q g.toImage htc, ?_, pullback.lift_fst _ _ _⟩
  refine IsClosedImmersion.isIso_of_ker_eq q (pullback.fst a g.imageι) _
    (pullback.lift_fst _ _ _) ?_
  rw [hkerq, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    Scheme.IdealSheafData.ker_subschemeι]

/-- **Stacks Project, Tag 0C2S.** The scheme-theoretic image of a closed immersion of
algebraic `K`-schemes in an `R`-model of its target is an `R`-model of its source. -/
@[stacks 0C2S]
theorem schemeTheoreticImage_isModel {V₁ V₂ X₂ : Scheme.{u}}
    (v₁ : V₁ ⟶ Spec (CommRingCat.of K)) (v₂ : V₂ ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType v₁] [QuasiCompact v₁]
    [LocallyOfFiniteType v₂] [QuasiCompact v₂]
    (f : V₁ ⟶ V₂) [IsClosedImmersion f] (hf : f ≫ v₂ = v₁)
    (p₂ : X₂ ⟶ Spec (CommRingCat.of R))
    (e₂ : V₂ ≅ pullback p₂ (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hX₂ : IsModel v₂ p₂ e₂) :
    let i := Spec.map (CommRingCat.ofHom (algebraMap R K))
    let g := f ≫ e₂.hom ≫ pullback.fst p₂ i
    ∃ e₁ : V₁ ≅ pullback (g.imageι ≫ p₂) i, IsModel v₁ (g.imageι ≫ p₂) e₁ := by
  intro i g
  obtain ⟨_, _, _, hgeneric₂⟩ := hX₂
  have : IsOpenImmersion i := genericFiberSpec_isOpenImmersion
  have hgbase : g ≫ p₂ = v₁ ≫ i := by
    simp only [g, i, Category.assoc]
    rw [pullback.condition, reassoc_of% hgeneric₂, reassoc_of% hf]
  obtain ⟨t, _, ht⟩ := exists_isIso_comp_pullback_fst_eq (f ≫ e₂.hom) (pullback.fst p₂ i) g
    (Category.assoc _ _ _)
  refine ⟨asIso t ≪≫ pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso p₂ i g.imageι,
    flat_imageι_comp v₁ p₂ g hgbase, inferInstance, inferInstance, ?_⟩
  change (t ≫ (pullbackSymmetry _ _).hom ≫ (pullbackRightPullbackFstIso p₂ i g.imageι).hom) ≫
    pullback.snd (g.imageι ≫ p₂) i = v₁
  simp only [Category.assoc, pullbackRightPullbackFstIso_hom_snd,
    pullbackSymmetry_hom_comp_snd_assoc, reassoc_of% ht]
  rw [hgeneric₂, hf]

end Stacks.Models
