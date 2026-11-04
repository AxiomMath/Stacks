module

public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Basic

/-!
# The two statements about `Proj.fromOfGlobalSections` that Tag 01NE's glueing needs

`StacksFrontier/AlgebraicGeometry/SectionsToProjectiveSpace/Basic.lean` reduces the morphism of
Stacks Tag 01NE for a nontrivial invertible sheaf to two statements about *Mathlib's*
`AlgebraicGeometry.Proj.fromOfGlobalSections`, stated there as the `Prop`s
`Stacks.SectionsToProjectiveSpace.HasPullbackNaturality` (naturality in the source scheme) and
`Stacks.SectionsToProjectiveSpace.HasUnitInvariance` (invariance under scaling the whole family of
sections by a unit). This file proves both, from the computation of the chart morphism on global
sections in the sibling file.

## The shape of both proofs

Two morphisms `X ⟶ Proj 𝒜` are compared over the cover of `X` by the nonvanishing loci of the
sections; on each chart both factor through `D₊(Tᵢ)`, which is affine, so the comparison is an
identity of ring homomorphisms out of `(A_{Tᵢ})₀`; and two such are equal as soon as they agree on
every fraction `p / Tᵢᵏ`
(`Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext`). On a fraction the value is
`(f p)|· · ((f Tᵢ)|·)⁻ᵏ`, so:

* scaling the family by a unit `u` multiplies `f p` by `u^{deg p} = u^{k}` and `f Tᵢ` by `u`,
  and the two cancel;
* pulling back along `g : Y ⟶ X` applies the ring homomorphism `g.appLE` to the whole expression,
  which is exactly the value of the pulled-back family.

## Main results

* `Stacks.ProjGlobalSectionsAppTop.hasUnitInvariance`:
  **`Stacks.SectionsToProjectiveSpace.HasUnitInvariance` holds.**
* `Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality`:
  **`Stacks.SectionsToProjectiveSpace.HasPullbackNaturality` holds.**
* `Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks`: the
  consequence, Tag 01NE's morphism for a nontrivial invertible sheaf over a base, now
  unconditional.

## Implementation notes

**`eval₂` of a homogeneous polynomial scales.**
`Stacks.ProjGlobalSectionsAppTop.eval₂_of_isHomogeneous` is the elementary fact that evaluating a
homogeneous polynomial of degree `m` at `a · gᵢ` multiplies the value by `aᵐ`. Mathlib has
`MvPolynomial.IsHomogeneous.eval₂` (the image is again homogeneous) but no scaling lemma, so it is
proved here from `MvPolynomial.eval₂_eq`.

**Inverses are never inverted.**
`Stacks.ProjGlobalSectionsAppTop.projAwayHom_apply_mk_of_mul_eq_one`
takes the inverse of `(f t)|·` as a *parameter*, with its defining equation, so each side of a
comparison is computed with whichever inverse makes the two sides match — the pulled-back
inverse on both sides for naturality, and `(u|· · (sᵢ)|·)⁻¹` written as
`((sᵢ)|·)⁻¹ · u|·` for unit invariance. No `Units` is ever transported and no inverse is ever
inverted; the remaining identities are `ring`.

**The two spellings of the integral model.** `projectiveSpaceAtUniverse n` and
`AlgebraicGeometry.Proj (coordGrading n)` are the same scheme but not the same expression, so a
goal mixing them is not type-correct at `implicit` transparency and `rw` refuses to fire; the
per-chart comparisons are therefore assembled with `Eq.trans` and `CategoryTheory.congrArg` in
term mode, which elaborates at default transparency.

## References

* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open HomogeneousLocalization

universe u

namespace Stacks.ProjGlobalSectionsAppTop

/-! ### Recognizing a chart morphism built from a second ring map -/

section Charts

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{u}} {t : A} {d : ℕ}

/-- The chart morphism restricted along an inclusion `V ≤ X_{f t}`, on global sections. -/
theorem homOfLE_toBasicOpenOfGlobalSections_appTop (f : A →+* Γ(X, ⊤)) (h0d : 0 < d)
    (hd : t ∈ 𝒜 d) {V : X.Opens} (hle : V ≤ X.basicOpen (f t)) :
    (Proj.basicOpenIsoAway 𝒜 t hd h0d).hom ≫ (Proj.basicOpen 𝒜 t).topIso.inv ≫
        (X.homOfLE hle ≫ Proj.toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd).appTop =
      CommRingCat.ofHom ((X.presheaf.map (homOfLE hle).op).hom.comp (projAwayHom 𝒜 f)) ≫
        V.topIso.inv := by
  rw [Scheme.Hom.comp_appTop, toBasicOpenOfGlobalSections_appTop_assoc 𝒜 f h0d hd,
    Stacks.ProjectiveFromSections.topIso_inv_homOfLE_appTop hle, CommRingCat.ofHom_comp,
    CommRingCat.ofHom_hom, Category.assoc]

/-- **Two ring maps whose chart morphisms have the same effect on sections have the same chart
morphism**, after restricting the larger chart to the smaller one. -/
theorem toBasicOpenOfGlobalSections_eq_of_projAwayHom (f₁ f₂ : A →+* Γ(X, ⊤)) (h0d : 0 < d)
    (hd : t ∈ 𝒜 d) (hle : X.basicOpen (f₂ t) ≤ X.basicOpen (f₁ t))
    (hψ : (X.presheaf.map (homOfLE hle).op).hom.comp (projAwayHom 𝒜 f₁) = projAwayHom 𝒜 f₂) :
    X.homOfLE hle ≫ Proj.toBasicOpenOfGlobalSections 𝒜 f₁ rfl h0d hd =
      Proj.toBasicOpenOfGlobalSections 𝒜 f₂ rfl h0d hd := by
  refine eq_toBasicOpenOfGlobalSections 𝒜 f₂ h0d hd _ ?_
  rw [homOfLE_toBasicOpenOfGlobalSections_appTop 𝒜 f₁ h0d hd hle, hψ]

/-- `AlgebraicGeometry.Scheme.Hom.resLE` on global sections is
`AlgebraicGeometry.Scheme.Hom.appLE`. -/
theorem topIso_inv_resLE_appTop {Y Z : Scheme.{u}} (g : Y ⟶ Z) {U : Z.Opens} {V : Y.Opens}
    (e : V ≤ g ⁻¹ᵁ U) :
    U.topIso.inv ≫ (g.resLE U V e).appTop = g.appLE U V e ≫ V.topIso.inv := by
  show U.topIso.inv ≫ (g.resLE U V e).app ⊤ = _
  rw [Scheme.Hom.resLE_app_top]
  exact Iso.inv_hom_id_assoc _ _

/-- The chart morphism precomposed with the restriction of `g : Y ⟶ X`, on global sections. -/
theorem resLE_toBasicOpenOfGlobalSections_appTop {Y : Scheme.{u}} (g : Y ⟶ X)
    (f : A →+* Γ(X, ⊤)) (h0d : 0 < d) (hd : t ∈ 𝒜 d) {V : Y.Opens}
    (e : V ≤ g ⁻¹ᵁ X.basicOpen (f t)) :
    (Proj.basicOpenIsoAway 𝒜 t hd h0d).hom ≫ (Proj.basicOpen 𝒜 t).topIso.inv ≫
        (g.resLE (X.basicOpen (f t)) V e ≫
          Proj.toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd).appTop =
      CommRingCat.ofHom ((g.appLE (X.basicOpen (f t)) V e).hom.comp (projAwayHom 𝒜 f)) ≫
        V.topIso.inv := by
  rw [Scheme.Hom.comp_appTop, toBasicOpenOfGlobalSections_appTop_assoc 𝒜 f h0d hd,
    topIso_inv_resLE_appTop, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Category.assoc]

/-- **The chart morphism of a pulled-back ring map is the restriction of `g` followed by the
chart morphism**, as soon as the ring homomorphisms agree. -/
theorem toBasicOpenOfGlobalSections_eq_of_projAwayHom_resLE {Y : Scheme.{u}} (g : Y ⟶ X)
    (f : A →+* Γ(X, ⊤)) (f' : A →+* Γ(Y, ⊤)) (h0d : 0 < d) (hd : t ∈ 𝒜 d)
    (e : Y.basicOpen (f' t) ≤ g ⁻¹ᵁ X.basicOpen (f t))
    (hψ : (g.appLE (X.basicOpen (f t)) (Y.basicOpen (f' t)) e).hom.comp (projAwayHom 𝒜 f) =
      projAwayHom 𝒜 f') :
    g.resLE (X.basicOpen (f t)) (Y.basicOpen (f' t)) e ≫
        Proj.toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd =
      Proj.toBasicOpenOfGlobalSections 𝒜 f' rfl h0d hd := by
  refine eq_toBasicOpenOfGlobalSections 𝒜 f' h0d hd _ ?_
  rw [resLE_toBasicOpenOfGlobalSections_appTop 𝒜 g f h0d hd e, hψ]

end Charts

/-! ### Evaluation of a homogeneous polynomial at a scaled family -/

/-- **Evaluating a homogeneous polynomial of degree `m` at `a · gᵢ` multiplies the value by
`aᵐ`.** -/
theorem eval₂_of_isHomogeneous {R S ι : Type*} [CommSemiring R] [CommSemiring S]
    (c : R →+* S) (a : S) (g : ι → S) {φ : MvPolynomial ι R} {m : ℕ}
    (hφ : φ.IsHomogeneous m) :
    MvPolynomial.eval₂ c (fun i => a * g i) φ = a ^ m * MvPolynomial.eval₂ c g φ := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hdeg : ∑ i ∈ e.support, e i = m := by
    simpa [Finsupp.weight_apply, Finsupp.sum] using hφ (MvPolynomial.mem_support_iff.mp he)
  have hprod : ∏ i ∈ e.support, (a * g i) ^ e i =
      (∏ i ∈ e.support, a ^ e i) * ∏ i ∈ e.support, g i ^ e i := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => mul_pow a (g i) (e i)
  rw [hprod, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-! ### Scaling a ring map by a unit -/

section Scaling

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{u}} {t : A} {d : ℕ}

/-- A ring homomorphism carries an inverse of `x` to an inverse of the image of `x`. -/
private theorem mul_map_eq_one {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {x y : R}
    {r : S} (hxy : x * y = 1) (h : φ x = r) : r * φ y = 1 := by
  rw [← h, ← map_mul, hxy, map_one]

/-- `a ^ k · x · cᵏ = x · (c · a)ᵏ`: the cancellation that makes the chart's ring homomorphism
blind to a scaling of the ring map. -/
theorem mul_pow_cancel {R : Type*} [CommRing R] (a c x y : R) (k : ℕ) (h : y = a ^ k * x) :
    y * c ^ k = x * (c * a) ^ k := by
  rw [h, mul_pow]; ring

/-- **The ring homomorphism of the chart does not change when the ring map is scaled by `a` in
each degree.** The hypotheses are exactly what a unit scaling of a family of sections provides:
the denominator `t` picks up `a` and a numerator of degree `k • d` picks up `aᵏ`. -/
theorem projAwayHom_comp_of_scaling (f₁ f₂ : A →+* Γ(X, ⊤)) (a : Γ(X, ⊤)) (hd : t ∈ 𝒜 d)
    (hle : X.basicOpen (f₂ t) ≤ X.basicOpen (f₁ t)) (ht : f₁ t = a * f₂ t)
    (hpow : ∀ (k : ℕ) (p : A), p ∈ 𝒜 (k • d) → f₁ p = a ^ k * f₂ p) :
    (X.presheaf.map (homOfLE hle).op).hom.comp (projAwayHom 𝒜 f₁) = projAwayHom 𝒜 f₂ := by
  refine away_ringHom_ext 𝒜 hd fun k p hp => ?_
  have hv₁ : resTop (X.basicOpen (f₁ t)) (f₁ t) * resTopBasicOpenInv (f₁ t) = 1 :=
    (isUnit_resTop_basicOpen (f₁ t)).unit.mul_inv
  have hc : resTop (X.basicOpen (f₂ t)) (f₁ t) *
      (X.presheaf.map (homOfLE hle).op).hom (resTopBasicOpenInv (f₁ t)) = 1 := by
    exact mul_map_eq_one _ hv₁ (resTop_resTop hle _)
  have hca : resTop (X.basicOpen (f₂ t)) (f₁ t) =
      resTop (X.basicOpen (f₂ t)) a * resTop (X.basicOpen (f₂ t)) (f₂ t) := by
    rw [ht, map_mul]
  rw [hca] at hc
  have hb : resTop (X.basicOpen (f₂ t)) (f₂ t) *
      ((X.presheaf.map (homOfLE hle).op).hom (resTopBasicOpenInv (f₁ t)) *
        resTop (X.basicOpen (f₂ t)) a) = 1 := by
    linear_combination hc
  rw [RingHom.comp_apply, projAwayHom_apply_mk_of_mul_eq_one 𝒜 f₁ hd k p hp hv₁,
    projAwayHom_apply_mk_of_mul_eq_one 𝒜 f₂ hd k p hp hb, map_mul, map_pow,
    resTop_resTop hle, hpow k p hp, map_mul, map_pow]
  exact mul_pow_cancel _ _ _ _ k rfl

end Scaling

/-! ### The two statements -/

section Statements

open Stacks.SectionsToProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} {n : ℕ}

/-- Scaling a family of sections by `a` multiplies `sectionsHom` on an element of degree `m` by
`aᵐ`. -/
theorem sectionsHom_scaled (a : Γ(X, ⊤)) (s : Fin (n + 1) → Γ(X, ⊤)) {m : ℕ}
    {p : coordRing.{u} n} (hp : p ∈ coordGrading.{u} n m) :
    sectionsHom (fun i => a * s i) p = a ^ m * sectionsHom s p :=
  eval₂_of_isHomogeneous _ a s ((MvPolynomial.mem_homogeneousSubmodule _ _).1 hp)

/-- Two chart morphisms on a restricted open, glued over `ι`, give the commutation with `g`. -/
private theorem comp_eq_comp_of_restrict {C : Type*} [Category C] {V U Y X T Z : C} (q : V ⟶ U)
    (ιV : V ⟶ Y) (ιU : U ⟶ X) (g : Y ⟶ X) (P : U ⟶ T) (Q : V ⟶ T) (I : T ⟶ Z) (FX : X ⟶ Z)
    (FY : Y ⟶ Z) (hq : q ≫ ιU = ιV ≫ g) (hkey : q ≫ P = Q) (hX : ιU ≫ FX = P ≫ I)
    (hY : ιV ≫ FY = Q ≫ I) : ιV ≫ FY = ιV ≫ g ≫ FX := by
  rw [hY, ← hkey, Category.assoc, ← hX, ← Category.assoc, hq, Category.assoc]

/-- **`Stacks.SectionsToProjectiveSpace.HasUnitInvariance`.** -/
theorem hasUnitInvariance : HasUnitInvariance.{u} := by
  intro X n u s hs hus
  have hcov : IsOpenCover
      (fun i : Fin (n + 1) => X.basicOpen (sectionsHom s (MvPolynomial.X i))) := by
    simpa [IsOpenCover] using iSup_basicOpen_eq_top s hs
  refine (X.openCoverOfIsOpenCover _ hcov).hom_ext _ _ fun (i : Fin (n + 1)) => ?_
  have hd : (MvPolynomial.X i : coordRing.{u} n) ∈ coordGrading.{u} n 1 :=
    X_mem_coordGrading_one i
  have heq : X.basicOpen (sectionsHom (fun j => (u : Γ(X, ⊤)) * s j) (MvPolynomial.X i)) =
      X.basicOpen (sectionsHom s (MvPolynomial.X i)) := by
    rw [sectionsHom_X, sectionsHom_X, Scheme.basicOpen_mul,
      X.basicOpen_of_isUnit u.isUnit, top_inf_eq]
  have hι : ∀ (s' : Fin (n + 1) → Γ(X, ⊤)) (hs' : Ideal.span (Set.range s') = ⊤),
      (X.basicOpen (sectionsHom s' (MvPolynomial.X i))).ι ≫ toProjectiveSpaceAtUniverse s' hs' =
        Proj.toBasicOpenOfGlobalSections (coordGrading.{u} n) (sectionsHom s') rfl Nat.one_pos
            hd ≫ (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)).ι :=
    fun _ _ => ι_comp_fromOfGlobalSections _ _ _ Nat.one_pos hd
  have key : X.homOfLE heq.ge ≫ Proj.toBasicOpenOfGlobalSections (coordGrading.{u} n)
        (sectionsHom fun j => (u : Γ(X, ⊤)) * s j) rfl Nat.one_pos hd =
      Proj.toBasicOpenOfGlobalSections (coordGrading.{u} n) (sectionsHom s) rfl Nat.one_pos hd :=
    toBasicOpenOfGlobalSections_eq_of_projAwayHom _ _ _ Nat.one_pos hd heq.ge
      (projAwayHom_comp_of_scaling _ _ _ (u : Γ(X, ⊤)) hd heq.ge (by simp)
        fun k p hp => by simpa using sectionsHom_scaled (u : Γ(X, ⊤)) s hp)
  rw [Scheme.openCoverOfIsOpenCover_f]
  have := comp_eq_comp_of_restrict (X.homOfLE heq.ge) _ _ (𝟙 X) _ _ _ _ _ (by simp) key
    (hι _ hus) (hι s hs)
  rw [Category.id_comp] at this
  exact this.symm

/-- Any ring homomorphism out of the universe copy of `ℤ` is the canonical one, so a ring
homomorphism of the targets does not change it. -/
theorem coeffHom_comp {R S : Type*} [Ring R] [Ring S] (φ : R →+* S) :
    φ.comp (coeffHom.{u} R) = coeffHom.{u} S := by
  ext a
  simp [coeffHom]

/-- **Pushing a family of sections forward along `g : Y ⟶ X` pushes `sectionsHom` forward.** -/
theorem sectionsHom_appTop {Y X : Scheme.{u}} {n : ℕ} (g : Y ⟶ X) (s : Fin (n + 1) → Γ(X, ⊤))
    (p : coordRing.{u} n) :
    sectionsHom (fun i => g.appTop (s i)) p = g.appTop (sectionsHom s p) := by
  refine MvPolynomial.induction_on
    (motive := fun q => sectionsHom (fun i => g.appTop (s i)) q = g.appTop (sectionsHom s q)) p
    (fun a => ?_) (fun q r hq hr => by simp [hq, hr]) (fun q j hq => by simp [hq])
  simp [sectionsHom, coeffHom]

/-- Restriction to `U` followed by `AlgebraicGeometry.Scheme.Hom.appLE` is `appTop` followed by
restriction to `V`. -/
theorem resTop_appLE {Y X : Scheme.{u}} (g : Y ⟶ X) {U : X.Opens} {V : Y.Opens}
    (e : V ≤ g ⁻¹ᵁ U) :
    X.presheaf.map (homOfLE (le_top (a := U))).op ≫ g.appLE U V e =
      g.appTop ≫ Y.presheaf.map (homOfLE (le_top (a := V))).op :=
  Scheme.Hom.map_appLE g e (homOfLE le_top).op

/-- `resTop_appLE` applied to a section. -/
theorem appLE_resTop {Y X : Scheme.{u}} (g : Y ⟶ X) {U : X.Opens} {V : Y.Opens}
    (e : V ≤ g ⁻¹ᵁ U) (a : Γ(X, ⊤)) :
    (g.appLE U V e).hom (resTop U a) = resTop V (g.appTop a) :=
  CategoryTheory.ConcreteCategory.congr_hom (resTop_appLE g e) a

/-- **`Stacks.SectionsToProjectiveSpace.HasPullbackNaturality`.** -/
theorem hasPullbackNaturality : HasPullbackNaturality.{u} := by
  intro Y X n g s hs hgs
  have hcov : IsOpenCover (fun i : Fin (n + 1) =>
      Y.basicOpen (sectionsHom (fun j => g.appTop (s j)) (MvPolynomial.X i))) := by
    simpa [IsOpenCover] using iSup_basicOpen_eq_top (fun j => g.appTop (s j)) hgs
  refine (Y.openCoverOfIsOpenCover _ hcov).hom_ext _ _ fun (i : Fin (n + 1)) => ?_
  have hd : (MvPolynomial.X i : coordRing.{u} n) ∈ coordGrading.{u} n 1 :=
    X_mem_coordGrading_one i
  have he : Y.basicOpen (sectionsHom (fun j => g.appTop (s j)) (MvPolynomial.X i)) =
      g ⁻¹ᵁ X.basicOpen (sectionsHom s (MvPolynomial.X i)) := by
    rw [sectionsHom_X, sectionsHom_X, Scheme.preimage_basicOpen]
    rfl
  have hιX : (X.basicOpen (sectionsHom s (MvPolynomial.X i))).ι ≫
        toProjectiveSpaceAtUniverse s hs =
      Proj.toBasicOpenOfGlobalSections (coordGrading.{u} n) (sectionsHom s) rfl Nat.one_pos hd ≫
        (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)).ι :=
    ι_comp_fromOfGlobalSections _ _ _ Nat.one_pos hd
  have hιY : (Y.basicOpen (sectionsHom (fun j => g.appTop (s j)) (MvPolynomial.X i))).ι ≫
        toProjectiveSpaceAtUniverse (fun j => g.appTop (s j)) hgs =
      Proj.toBasicOpenOfGlobalSections (coordGrading.{u} n)
          (sectionsHom fun j => g.appTop (s j)) rfl Nat.one_pos hd ≫
        (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)).ι :=
    ι_comp_fromOfGlobalSections _ _ _ Nat.one_pos hd
  have hstep : (g.appLE (X.basicOpen (sectionsHom s (MvPolynomial.X i)))
        (Y.basicOpen (sectionsHom (fun j => g.appTop (s j)) (MvPolynomial.X i))) he.le).hom
        (resTop (X.basicOpen (sectionsHom s (MvPolynomial.X i)))
          (sectionsHom s (MvPolynomial.X i))) =
      resTop (Y.basicOpen (sectionsHom (fun j => g.appTop (s j)) (MvPolynomial.X i)))
        (sectionsHom (fun j => g.appTop (s j)) (MvPolynomial.X i)) := by
    rw [appLE_resTop, sectionsHom_appTop g s (MvPolynomial.X i)]
  have hψ : (g.appLE (X.basicOpen (sectionsHom s (MvPolynomial.X i)))
        (Y.basicOpen (sectionsHom (fun j => g.appTop (s j)) (MvPolynomial.X i)))
        he.le).hom.comp (projAwayHom (coordGrading.{u} n) (sectionsHom s)) =
      projAwayHom (coordGrading.{u} n) (sectionsHom fun j => g.appTop (s j)) := by
    refine away_ringHom_ext _ hd fun k p hp => ?_
    have hv : resTop (X.basicOpen (sectionsHom s (MvPolynomial.X i)))
          (sectionsHom s (MvPolynomial.X i)) *
        resTopBasicOpenInv (sectionsHom s (MvPolynomial.X i)) = 1 :=
      (isUnit_resTop_basicOpen _).unit.mul_inv
    have hv' : resTop (Y.basicOpen (sectionsHom (fun j => g.appTop (s j)) (MvPolynomial.X i)))
          (sectionsHom (fun j => g.appTop (s j)) (MvPolynomial.X i)) *
        (g.appLE _ _ he.le).hom
          (resTopBasicOpenInv (sectionsHom s (MvPolynomial.X i))) = 1 := by
      exact mul_map_eq_one _ hv hstep
    rw [RingHom.comp_apply,
      projAwayHom_apply_mk_of_mul_eq_one _ (sectionsHom s) hd k p hp hv,
      projAwayHom_apply_mk_of_mul_eq_one _ (sectionsHom fun j => g.appTop (s j)) hd k p hp hv',
      map_mul, map_pow, appLE_resTop, sectionsHom_appTop g s p]
  have key := toBasicOpenOfGlobalSections_eq_of_projAwayHom_resLE (coordGrading.{u} n) g
    (sectionsHom s) (sectionsHom fun j => g.appTop (s j)) Nat.one_pos hd he.le hψ
  rw [Scheme.openCoverOfIsOpenCover_f]
  have := comp_eq_comp_of_restrict (g.resLE _ _ he.le) _ _ g _ _ _ _ _
    (Scheme.Hom.resLE_comp_ι _ _) key hιX hιY
  exact this.symm

/-! ### The consequence for Tag 01NE -/

/-- **Stacks Tag 01NE's morphism over a base scheme, for a nontrivial invertible sheaf with a
generating family of global sections** — `Stacks.ProjectiveFromSections` conditional result, now
unconditional. -/
theorem exists_hom_projectiveSpaceOver_of_generatesStalks {L : X.Modules}
    [Stacks.Ample.IsInvertibleModule X L] (s : Fin (n + 1) → Γ(L, ⊤))
    (hs : Stacks.ProjectiveFromSections.GeneratesStalks s) {S : Scheme.{u}} (f : X ⟶ S) :
    ∃ p : X ⟶ projectiveSpaceOver n S,
      p ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f ∧
      ∀ i, (Stacks.ProjectiveFromSections.nvCover s i).ι ≫ p ≫
          projectiveSpaceOver.toIntegralAtUniverse n S =
        toProjectiveSpaceAtUniverse (Stacks.ProjectiveFromSections.chartRatio s i)
          (Stacks.ProjectiveFromSections.span_range_chartRatio s i) :=
  Stacks.ProjectiveFromSections.exists_hom_projectiveSpaceOver_of_generatesStalks
    hasPullbackNaturality hasUnitInvariance s hs f

end Statements

end Stacks.ProjGlobalSectionsAppTop

end
