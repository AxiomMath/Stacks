module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsExtension
public import StacksFrontier.AlgebraicGeometry.DeRham.FormsDirectImageComparisonSections
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupCone
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineIsoCriterion
public import StacksCore.Tactic.StacksAttribute

/-!
# Clause (2) of Stacks 0FUR

In the standard situation of Section 50.16 of the source — `A = R[x₁, …, x_m, y₁, …, y_n]`
graded by `deg yⱼ = 1`, `X = Spec A`, the centre `Z = Spec(A₀) = 𝐀^m_S`, the projective bundle
`P = Proj(A) = 𝐏^{n-1}_Z` with `p : P ⟶ Z`, and the blowup `L = Proj(⨁_d A_{≥ d})` of `X` along `Z`
with its cone projection `π : L ⟶ P` and zero section `0 : P ⟶ L` — clause (2) of
[Stacks, Tag 0FUR] asserts that `Ω^a_{Z/S} ⟶ p_*Ω^a_{P/S}` is an isomorphism for every `a ≥ 0`.

The proof here deduces it from clause (1) and the cone structure. On global sections a form `ω`
on `P` is `0^*π^*ω`, because `π ∘ 0 = id`; by clause (1) the form `π^*ω` on `L` is `b^*θ` for a
form `θ` on `X`; and `b ∘ 0 = i ∘ p`, so `ω = 0^*b^*θ = p^*(i^*θ)`. A form `η` on `Z` with
`p^*η = 0` vanishes, because then `b^*q^*η = π^*p^*η = 0` for the retraction `q : X ⟶ Z`, so
`q^*η = 0` and `η = i^*q^*η = 0`. Both sides being quasi-coherent on the affine `Z`, the map is
an isomorphism.

## Main results

* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsPullback_id_top` and
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsPullback_comp_eq_top`: pulling back
  global forms along the identity, and along two equal composites.
* `Stacks.DeRham.CoordinateCone.bijective_coneFormsPullback_top`: clause (1), read on the cone.
* `Stacks.DeRham.CoordinateCone.isIso_coneBundleFormsDirectImage`: **clause (2) of
  [Stacks, Tag 0FUR]**, for every `n ≥ 1` and every `a ≥ 0`.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite MvPolynomial

universe u

/-! ### Pulling back global forms along composites -/

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y Y' W S : Scheme.{u}}

/-- Pulling back global forms along equal morphisms gives equal results. -/
private theorem relativeDifferentialFormsPullback_congr_top {k k' : W ⟶ X} (hk : k = k')
    (π : X ⟶ S) (π'' : W ⟶ S) (h₁ : k ≫ π = π'' ≫ 𝟙 S) (h₂ : k' ≫ π = π'' ≫ 𝟙 S) (d : ℤ)
    (ω : Γ(relativeDifferentialForms π d, ⊤)) :
    relativeDifferentialFormsPullback k π π'' (𝟙 S) h₁ d ⊤ ω =
      relativeDifferentialFormsPullback k' π π'' (𝟙 S) h₂ d ⊤ ω := by
  subst hk
  rfl

/-- Pulling back global forms along a composite is the iterated pullback. -/
private theorem relativeDifferentialFormsPullback_comp_top (f : Y ⟶ X) (g : W ⟶ Y)
    (πX : X ⟶ S) (πY : Y ⟶ S) (πW : W ⟶ S) (hf : f ≫ πX = πY ≫ 𝟙 S)
    (hg : g ≫ πY = πW ≫ 𝟙 S) (h : (g ≫ f) ≫ πX = πW ≫ 𝟙 S) (d : ℤ)
    (ω : Γ(relativeDifferentialForms πX d, ⊤)) :
    relativeDifferentialFormsPullback (g ≫ f) πX πW (𝟙 S) h d ⊤ ω =
      relativeDifferentialFormsPullback g πY πW (𝟙 S) hg d ⊤
        (relativeDifferentialFormsPullback f πX πY (𝟙 S) hf d ⊤ ω) :=
  Stacks.Gysin.relativeDifferentialFormsPullback_comp f g πX πY πW (𝟙 S) (𝟙 S) (𝟙 S) hf hg h d ⊤ ω

/-- **Pulling back global forms along the identity is the identity.** The pullback along `𝟙` is
bijective, and it is idempotent because `𝟙 ≫ 𝟙 = 𝟙`. -/
theorem relativeDifferentialFormsPullback_id_top (π : X ⟶ S) (h : 𝟙 X ≫ π = π ≫ 𝟙 S) (d : ℤ)
    (ω : Γ(relativeDifferentialForms π d, ⊤)) :
    relativeDifferentialFormsPullback (𝟙 X) π π (𝟙 S) h d ⊤ ω = ω := by
  refine (bijective_relativeDifferentialFormsPullback_of_isIso (𝟙 X) π π h d ⊤).1 ?_
  rw [← relativeDifferentialFormsPullback_comp_top (𝟙 X) (𝟙 X) π π π h h (by simp)]
  exact relativeDifferentialFormsPullback_congr_top (Category.id_comp (𝟙 X)) π π _ h d ω

/-- **Equal composites pull back global forms equally**: if `g ≫ f = g' ≫ f'`, then pulling a
global form back along `f` and then `g` agrees with pulling it back along `f'` and then `g'`. -/
theorem relativeDifferentialFormsPullback_comp_eq_top (f : Y ⟶ X) (g : W ⟶ Y) (f' : Y' ⟶ X)
    (g' : W ⟶ Y') (πX : X ⟶ S) (πY : Y ⟶ S) (πY' : Y' ⟶ S) (πW : W ⟶ S)
    (hf : f ≫ πX = πY ≫ 𝟙 S) (hg : g ≫ πY = πW ≫ 𝟙 S) (hf' : f' ≫ πX = πY' ≫ 𝟙 S)
    (hg' : g' ≫ πY' = πW ≫ 𝟙 S) (hcomm : g ≫ f = g' ≫ f') (d : ℤ)
    (ω : Γ(relativeDifferentialForms πX d, ⊤)) :
    relativeDifferentialFormsPullback g πY πW (𝟙 S) hg d ⊤
        (relativeDifferentialFormsPullback f πX πY (𝟙 S) hf d ⊤ ω) =
      relativeDifferentialFormsPullback g' πY' πW (𝟙 S) hg' d ⊤
        (relativeDifferentialFormsPullback f' πX πY' (𝟙 S) hf' d ⊤ ω) := by
  rw [← relativeDifferentialFormsPullback_comp_top f g πX πY πW hf hg (by simp [hf, hg]),
    ← relativeDifferentialFormsPullback_comp_top f' g' πX πY' πW hf' hg' (by simp [hf', hg'])]
  exact relativeDifferentialFormsPullback_congr_top hcomm πX πW _ _ d ω

/-- `relativeDifferentialFormsPullback_comp_eq_top` when the composite is the identity. -/
theorem relativeDifferentialFormsPullback_comp_eq_id_top (f : Y ⟶ X) (g : X ⟶ Y)
    (πX : X ⟶ S) (πY : Y ⟶ S) (hf : f ≫ πX = πY ≫ 𝟙 S) (hg : g ≫ πY = πX ≫ 𝟙 S)
    (hcomm : g ≫ f = 𝟙 X) (d : ℤ) (ω : Γ(relativeDifferentialForms πX d, ⊤)) :
    relativeDifferentialFormsPullback g πY πX (𝟙 S) hg d ⊤
        (relativeDifferentialFormsPullback f πX πY (𝟙 S) hf d ⊤ ω) = ω := by
  have h := relativeDifferentialFormsPullback_comp_eq_top f g (𝟙 X) (𝟙 X) πX πY πX πX hf hg
    (by simp) (by simp) (by simpa using hcomm) d ω
  rw [h, relativeDifferentialFormsPullback_id_top, relativeDifferentialFormsPullback_id_top]

end AlgebraicGeometry.Scheme.Hom

/-! ### Clause (2) of Tag 0FUR for the cone -/

namespace Stacks.DeRham.CoordinateCone

variable (R : Type u) [CommRing R] (m n : ℕ)

open Stacks.AlgebraicGeometry.ProjAndSpec Scheme.Hom
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation (truncationConeData)

/-- The projective bundle `P = Proj(A) = 𝐏^{n-1}_Z` of the standard coordinate situation. -/
abbrev coneBundle : Scheme.{u} := AlgebraicGeometry.Proj (yGrading R m n)

/-- The centre `Z = Spec(A₀) = 𝐀^m_S` of the standard coordinate situation. -/
abbrev coneCentre : Scheme.{u} := Spec (.of (yGrading R m n 0))

/-- The projection `p : P ⟶ Z`. -/
abbrev coneBundleToCentre : coneBundle R m n ⟶ coneCentre R m n :=
  Proj.toSpecZero (yGrading R m n)

/-- The closed immersion `i : Z ⟶ X`. -/
abbrev coneCentreToAmbient : coneCentre R m n ⟶ Stacks.DeRham.coordinateAmbient R m n :=
  zToX (yGrading R m n)

/-- The structure morphism `Z ⟶ S`. -/
abbrev coneCentreToBase : coneCentre R m n ⟶ Stacks.DeRham.coordinateBase R :=
  coneCentreToAmbient R m n ≫ Stacks.DeRham.coordinateAmbientToBase R m n

/-- The structure morphism `P ⟶ S`. -/
abbrev coneBundleToBase : coneBundle R m n ⟶ Stacks.DeRham.coordinateBase R :=
  coneBundleToCentre R m n ≫ coneCentreToBase R m n

/-- The structure morphism `L ⟶ X` of the cone `L = Proj(⨁_d A_{≥ d})`. -/
abbrev coneToAmbient := toSpecA (truncationConeData (yGrading R m n))

/-- The structure morphism `L ⟶ S` of the cone. -/
abbrev coneToBase := coneToAmbient R m n ≫ Stacks.DeRham.coordinateAmbientToBase R m n

/-- `Z ⟶ X ⟶ Z` is the identity: `A₀ ⟶ A ⟶ A₀` is. -/
theorem zToX_comp_xToZ : zToX (yGrading R m n) ≫ xToZ (yGrading R m n) = 𝟙 _ := by
  rw [zToX, xToZ, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  exact GradedRing.projZeroRingHom'_apply_coe _ a

/-- `X ⟶ Z ⟶ X` lies over `S`: the constants have degree zero. -/
theorem xToZ_comp_zToX_comp_toBase :
    xToZ (yGrading R m n) ≫ zToX (yGrading R m n) ≫ Stacks.DeRham.coordinateAmbientToBase R m n =
      Stacks.DeRham.coordinateAmbientToBase R m n ≫ 𝟙 _ := by
  rw [zToX, xToZ, Category.comp_id, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  change ((GradedRing.projZeroRingHom' (yGrading R m n) (C r) : yGrading R m n 0) :
    MvPolynomial (Fin m ⊕ Fin n) R) = C r
  have hC : (C r : MvPolynomial (Fin m ⊕ Fin n) R) ∈ yGrading R m n 0 :=
    isWeightedHomogeneous_C (yWeight m n) r
  exact congrArg Subtype.val (GradedRing.projZeroRingHom'_apply_coe (yGrading R m n) ⟨_, hC⟩)

/-- **Clause (1) of [Stacks, Tag 0FUR], read on the cone**: for `n ≥ 2`, pulling back global
`a`-forms from `X` to `L = Proj(⨁_d A_{≥ d})` is bijective. The cone is the blowup over `X`
(`coneBlowupIso_hom_comp`), and pulling back along an isomorphism is bijective. -/
theorem bijective_coneFormsPullback_top (hn : 1 ≤ n) (a : ℕ) :
    Function.Bijective (relativeDifferentialFormsPullback (coneToAmbient R m n)
      (Stacks.DeRham.coordinateAmbientToBase R m n) (coneToBase R m n) (𝟙 _) (by simp)
      (a : ℤ) ⊤) := by
  have hiso := coneBlowupIso_hom_comp R m n
  have h₂ : (coneBlowupIso R m n).hom ≫ Stacks.DeRham.coordinateBlowupToBase R m n =
      coneToBase R m n ≫ 𝟙 _ := by
    rw [Stacks.DeRham.coordinateBlowupToBase, ← Category.assoc, hiso, Category.comp_id]
  have h₃ : ((coneBlowupIso R m n).hom ≫ Stacks.DeRham.coordinateBlowupToAmbient R m n) ≫
      Stacks.DeRham.coordinateAmbientToBase R m n = coneToBase R m n ≫ 𝟙 _ := by
    rw [hiso, Category.comp_id]
  have hB : Function.Bijective (relativeDifferentialFormsPullback
      (Stacks.DeRham.coordinateBlowupToAmbient R m n)
      (Stacks.DeRham.coordinateAmbientToBase R m n)
      (Stacks.DeRham.coordinateBlowupToBase R m n) (𝟙 _) (by simp) (a : ℤ) ⊤) :=
    have := Stacks.DeRham.isIso_coordinateBlowupFormsDirectImage R m n hn a
    ConcreteCategory.bijective_of_isIso
      (Scheme.Modules.Hom.app (Stacks.DeRham.coordinateBlowupFormsDirectImage R m n a) ⊤)
  have hE := bijective_relativeDifferentialFormsPullback_of_isIso (coneBlowupIso R m n).hom
    (Stacks.DeRham.coordinateBlowupToBase R m n) (coneToBase R m n) h₂ (a : ℤ) ⊤
  have heq : (relativeDifferentialFormsPullback (coneToAmbient R m n)
      (Stacks.DeRham.coordinateAmbientToBase R m n) (coneToBase R m n) (𝟙 _) (by simp)
      (a : ℤ) ⊤) = fun ω => relativeDifferentialFormsPullback (coneBlowupIso R m n).hom
        (Stacks.DeRham.coordinateBlowupToBase R m n) (coneToBase R m n) (𝟙 _) h₂ (a : ℤ) ⊤
        (relativeDifferentialFormsPullback (Stacks.DeRham.coordinateBlowupToAmbient R m n)
          (Stacks.DeRham.coordinateAmbientToBase R m n)
          (Stacks.DeRham.coordinateBlowupToBase R m n) (𝟙 _) (by simp) (a : ℤ) ⊤ ω) := by
    funext ω
    exact (relativeDifferentialFormsPullback_congr_top hiso.symm _ _ _ h₃ _ ω).trans
      (relativeDifferentialFormsPullback_comp_top _ _ _ _ _ (by simp) h₂ h₃ _ ω)
  rw [heq]
  exact hE.comp hB

/-- **Pulling back global forms from the centre to the projective bundle is bijective**, for
every `n ≥ 1`. With `π : L ⟶ P` the cone projection and `0 : P ⟶ L` its zero section, a form `ω`
on `P` is `0^*π^*ω`; by clause (1) `π^*ω` is pulled back from a form `θ` on `X`, so
`ω = 0^*b^*θ = p^*i^*θ`, because `b ∘ 0 = i ∘ p`. Injectivity uses the retraction `X ⟶ Z`. -/
theorem bijective_coneBundleFormsPullback_top (hn : 1 ≤ n) (a : ℕ) :
    Function.Bijective (relativeDifferentialFormsPullback (coneBundleToCentre R m n)
      (coneCentreToBase R m n) (coneBundleToBase R m n) (𝟙 _) (by simp) (a : ℤ) ⊤) := by
  have hpi : pi (truncationConeData (yGrading R m n)) ≫ coneBundleToBase R m n =
      coneToBase R m n ≫ 𝟙 _ := by
    simp only [coneBundleToBase, coneCentreToBase, coneToBase, coneToAmbient]
    rw [← Category.assoc, pi_comp_toSpecZero, Category.assoc]
    have := xToZ_comp_zToX_comp_toBase R m n
    simp only [Category.comp_id] at this ⊢
    rw [this]
  have h0 : zeroSection (truncationConeData (yGrading R m n)) ≫ coneToBase R m n =
      coneBundleToBase R m n ≫ 𝟙 _ := by
    simp only [coneBundleToBase, coneCentreToBase, coneToBase, coneToAmbient]
    rw [← Category.assoc, zeroSection_comp_toSpecA]
    simp
  have hx : xToZ (yGrading R m n) ≫ coneCentreToBase R m n =
      Stacks.DeRham.coordinateAmbientToBase R m n ≫ 𝟙 _ :=
    xToZ_comp_zToX_comp_toBase R m n
  have hL := bijective_coneFormsPullback_top R m n hn a
  -- the four identities of the diagram, on global forms
  have I1 := fun ω => relativeDifferentialFormsPullback_comp_eq_id_top
    (pi (truncationConeData (yGrading R m n))) (zeroSection (truncationConeData (yGrading R m n)))
    (coneBundleToBase R m n) (coneToBase R m n) hpi h0 (zeroSection_comp_pi _) (a : ℤ) ω
  have I2 := fun θ => relativeDifferentialFormsPullback_comp_eq_top
    (coneToAmbient R m n) (zeroSection (truncationConeData (yGrading R m n)))
    (coneCentreToAmbient R m n) (coneBundleToCentre R m n)
    (Stacks.DeRham.coordinateAmbientToBase R m n) (coneToBase R m n) (coneCentreToBase R m n)
    (coneBundleToBase R m n) (by simp) h0 (by simp) (by simp) (zeroSection_comp_toSpecA _)
    (a : ℤ) θ
  have I3 := fun η => relativeDifferentialFormsPullback_comp_eq_id_top
    (xToZ (yGrading R m n)) (coneCentreToAmbient R m n)
    (coneCentreToBase R m n) (Stacks.DeRham.coordinateAmbientToBase R m n) hx (by simp)
    (zToX_comp_xToZ R m n) (a : ℤ) η
  have I4 := fun η => relativeDifferentialFormsPullback_comp_eq_top
    (xToZ (yGrading R m n)) (coneToAmbient R m n)
    (coneBundleToCentre R m n) (pi (truncationConeData (yGrading R m n)))
    (coneCentreToBase R m n) (Stacks.DeRham.coordinateAmbientToBase R m n)
    (coneBundleToBase R m n) (coneToBase R m n) hx (by simp) (by simp) hpi
    (pi_comp_toSpecZero _).symm (a : ℤ) η
  refine ⟨fun η₁ η₂ h => ?_, fun ω => ?_⟩
  · have h' := congrArg (relativeDifferentialFormsPullback
      (pi (truncationConeData (yGrading R m n))) (coneBundleToBase R m n) (coneToBase R m n)
      (𝟙 _) hpi (a : ℤ) ⊤) h
    rw [← I4, ← I4] at h'
    rw [← I3 η₁, ← I3 η₂, hL.1 h']
  · obtain ⟨θ, hθ⟩ := hL.2 (relativeDifferentialFormsPullback
      (pi (truncationConeData (yGrading R m n))) (coneBundleToBase R m n) (coneToBase R m n)
      (𝟙 _) hpi (a : ℤ) ⊤ ω)
    refine ⟨_, (I2 θ).symm.trans ?_⟩
    rw [hθ]
    exact I1 ω

/-- `A = R[x, y]` is of finite type over its degree-zero part `A₀ = R[x]`. -/
instance : Algebra.FiniteType (yGrading R m n 0) (MvPolynomial (Fin m ⊕ Fin n) R) :=
  Algebra.FiniteType.of_restrictScalars_finiteType R _ _

/-- **[Stacks, Tag 0FUR], clause (2).** In the standard situation of Section 50.16 — a ring `R`,
`S = Spec R`, `m ≥ 0`, `n ≥ 1`, `A = R[x₁, …, x_m, y₁, …, y_n]` graded by `deg xᵢ = 0`,
`deg yⱼ = 1`, the centre `Z = Spec(A₀) = 𝐀^m_S` and the projective bundle
`P = Proj(A) = 𝐏^{n-1}_Z` with its projection `p : P ⟶ Z` — the canonical map
`Ω^a_{Z/S} ⟶ p_*Ω^a_{P/S}` is an isomorphism for every `a ≥ 0`.

Both sides are quasi-coherent on the affine `Z`, and on global sections the map is bijective by
`bijective_coneBundleFormsPullback_top`: the cone `L = Proj(⨁_d A_{≥ d})` over `P` is the blowup
of `X = Spec A` along `Z`, a form on `P` is the restriction along the zero section of its pullback
to `L`, and by clause (1) that pullback comes from `X`. -/
@[stacks 0FUR "clause (2): Ω^a_{Z/S} ⟶ p_*Ω^a_{P/S} is an isomorphism, every a ≥ 0, every n ≥ 1, \
for P = Proj(A) and Z = Spec(A₀) as in Section 50.16"]
theorem isIso_coneBundleFormsDirectImage (hn : 1 ≤ n) (a : ℕ) :
    IsIso (formsDirectImageComparison (coneBundleToCentre R m n) (coneCentreToBase R m n)
      (a : ℤ)) := by
  have := isQuasicoherent_relativeDifferentialForms (coneCentreToBase R m n) a
  have := isQuasicoherent_relativeDifferentialForms
    (coneBundleToCentre R m n ≫ coneCentreToBase R m n) a
  exact Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top _
    ((ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_coneBundleFormsPullback_top R m n hn a))

end Stacks.DeRham.CoordinateCone

end
