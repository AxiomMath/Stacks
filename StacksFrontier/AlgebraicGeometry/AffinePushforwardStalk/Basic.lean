module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-!
# The stalk of an affine pushforward is a localization of the sections

Let `f : Y ⟶ X` be an affine morphism of schemes, let `U` be an affine open of `X` and let
`x ∈ U`. Then the stalk at `x` of `f_* 𝒪_Y` is the localization of `Γ(Y, f⁻¹U)` at the image of
the prime `p_x ⊆ Γ(X, U)` corresponding to `x`.

## Main results

* `AlgebraicGeometry.IsAffineOpen.mem_primeCompl_iff_mem_basicOpen`: a section of an affine open
  `U` lies outside the prime of `Γ(X, U)` attached to `x ∈ U` exactly when `x` lies in the basic
  open it determines.
* `AlgebraicGeometry.IsAffineOpen.isLocalization_pushforwardStalk`: for an affine morphism `f`,
  the stalk of `f_* 𝒪_Y` at `x ∈ U` is the localization of `Γ(Y, f⁻¹U)` at the image of
  `p_x ⊆ Γ(X, U)`.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- A section over an affine open `U` lies outside the prime of `Γ(X, U)` corresponding to a
point `x ∈ U` exactly when `x` lies in the basic open determined by that section. -/
public theorem IsAffineOpen.mem_primeCompl_iff_mem_basicOpen {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (r : Γ(X, U)) :
    r ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl ↔ x ∈ X.basicOpen r := by
  let := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
  have := hU.isLocalization_stalk (⟨x, hx⟩ : U)
  rw [Scheme.mem_basicOpen X r x hx]
  exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal r).symm

/-- For an affine morphism `f : Y ⟶ X`, an affine open `U` of `X` and a point `x ∈ U`, the stalk
at `x` of `f_* 𝒪_Y` is the localization of `Γ(Y, f⁻¹U)` at the image of the prime of `Γ(X, U)`
corresponding to `x`. -/
public theorem IsAffineOpen.isLocalization_pushforwardStalk {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsAffineHom f] {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    letI : Algebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    letI : Algebra Γ(Y, f ⁻¹ᵁ U) ((f.base _* Y.presheaf).stalk x) :=
      ((f.base _* Y.presheaf).germ U x hx).hom.toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, f ⁻¹ᵁ U)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) ((f.base _* Y.presheaf).stalk x) := by
  let : Algebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let : Algebra Γ(Y, f ⁻¹ᵁ U) ((f.base _* Y.presheaf).stalk x) :=
    ((f.base _* Y.presheaf).germ U x hx).hom.toAlgebra
  have hmem : ∀ (r : Γ(X, U)) (n : ℕ), x ∈ X.basicOpen r →
      (f.app U r) ^ n ∈ Algebra.algebraMapSubmonoid Γ(Y, f ⁻¹ᵁ U)
        (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl := fun r n hr ↦
    ⟨r ^ n, pow_mem ((hU.mem_primeCompl_iff_mem_basicOpen hx r).mpr hr) n, by
      rw [map_pow]; rfl⟩
  have hAway : ∀ r : Γ(X, U),
      letI : Algebra Γ(Y, f ⁻¹ᵁ U) ((f.base _* Y.presheaf).obj (op (X.basicOpen r))) :=
        ((f.base _* Y.presheaf).map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
      IsLocalization.Away (f.app U r) ((f.base _* Y.presheaf).obj (op (X.basicOpen r))) :=
    fun r ↦ (hU.preimage f).isLocalization_of_eq_basicOpen (f.app U r)
      ((Opens.map f.base).map (homOfLE (X.basicOpen_le r))) (Scheme.preimage_basicOpen f r)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨-, s, hs, rfl⟩
    change IsUnit ((f.base _* Y.presheaf).germ U x hx ((f.app U) s))
    rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx f.c s]
    exact ((X.mem_basicOpen s x hx).mp
      ((hU.mem_primeCompl_iff_mem_basicOpen hx s).mp hs)).map _
  · intro z
    obtain ⟨W, hxW, s, hs⟩ := (f.base _* Y.presheaf).exists_germ_eq z
    obtain ⟨r, hrW, hxr⟩ := hU.exists_basicOpen_le (⟨x, hxW⟩ : W) hx
    let : Algebra Γ(Y, f ⁻¹ᵁ U) ((f.base _* Y.presheaf).obj (op (X.basicOpen r))) :=
      ((f.base _* Y.presheaf).map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
    have := hAway r
    obtain ⟨⟨b, ⟨-, n, rfl⟩⟩, hb⟩ :=
      IsLocalization.surj (Submonoid.powers (f.app U r))
        (((f.base _* Y.presheaf).map (homOfLE hrW).op) s)
    refine ⟨⟨b, ⟨(f.app U r) ^ n, hmem r n hxr⟩⟩, ?_⟩
    have key := congrArg ((f.base _* Y.presheaf).germ (X.basicOpen r) x hxr) hb
    rw [RingHom.algebraMap_toAlgebra] at key
    simp only [map_mul] at key
    rwa [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply, hs] at key
  · intro b₁ b₂ h
    replace h : (f.base _* Y.presheaf).germ U x hx b₁
        = (f.base _* Y.presheaf).germ U x hx b₂ := h
    obtain ⟨W, hxW, iU, iV, e⟩ := (f.base _* Y.presheaf).germ_eq x hx hx b₁ b₂ h
    obtain ⟨r, hrW, hxr⟩ := hU.exists_basicOpen_le (⟨x, hxW⟩ : W) hx
    let : Algebra Γ(Y, f ⁻¹ᵁ U) ((f.base _* Y.presheaf).obj (op (X.basicOpen r))) :=
      ((f.base _* Y.presheaf).map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
    have := hAway r
    have e2 := congrArg ((f.base _* Y.presheaf).map (homOfLE hrW).op) e
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp,
      Subsingleton.elim (iU.op ≫ (homOfLE hrW).op) (homOfLE (X.basicOpen_le r)).op,
      Subsingleton.elim (iV.op ≫ (homOfLE hrW).op) (homOfLE (X.basicOpen_le r)).op] at e2
    obtain ⟨⟨-, n, rfl⟩, hc⟩ :=
      IsLocalization.exists_of_eq (M := Submonoid.powers (f.app U r))
        (S := ((f.base _* Y.presheaf).obj (op (X.basicOpen r)))) e2
    exact ⟨⟨(f.app U r) ^ n, hmem r n hxr⟩, hc⟩

end AlgebraicGeometry

end
