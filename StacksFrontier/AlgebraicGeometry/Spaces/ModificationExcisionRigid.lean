module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SubfunctorSectionLifting
public import StacksFrontier.CategoryTheory.DependentProduct

/-!
# The dependent product is rigid over the open complement

Stacks 0BGY produces the inverse of the base-change functor as the contravariant functor
`X(T) = {(w, y) | w : T → W, y : T ×_{w,W} V → Y over V}`, which is the dependent product
(Weil restriction) of `Y` along `f`. This file proves the first of the two computations the
source proof makes with it: over the open complement `W⁰`, where `Y → V` is an isomorphism,
the dependent product is `W⁰` itself. In the source this is the sentence "since `h⁻¹V⁰ → V⁰`
is an isomorphism, we see that if `w : T → W` maps into `W⁰`, then there is a unique choice
for `h`; in other words `X ×_{g,W} W⁰ = W⁰`".

## Main results

* `AlgebraicGeometry.Space.isIso_fromPreimage_depProdπ` and
  `AlgebraicGeometry.Space.isIso_pullback_snd_depProdπ`: **the computation
  `X ×_{g,W} W⁰ = W⁰` of Stacks 0BGY**, in the two interchangeable shapes.

## Implementation notes

Rigidity is proved on sections. A section of the dependent product over `A` lying over `W⁰` is
a pair `(w, y)` with `w` a section of `W⁰`; its second component is then forced, because every
`v : V` appearing in the family lies over a restriction of `w`, hence in `f⁻¹W⁰`, where
`Y → V` is an isomorphism and so exactly one value is available. Uniqueness is
`AlgebraicGeometry.Space.eq_of_app_eq_of_mem` and existence is
`AlgebraicGeometry.Space.exists_app_eq_of_mem`; the naturality of the resulting family is
itself forced by uniqueness, both sides lying over the same section of `V`.

Invertibility is checked on sections and transported by
`CategoryTheory.NatIso.isIso_of_isIso_app`, which is available because the two shapes of "is
an isomorphism over a subfunctor" are interchangeable
(`AlgebraicGeometry.Space.isIso_pullback_snd_of_isIso_fromPreimage`); the `fromPreimage` shape
is the one whose sections are a subtype, and so the one on which bijectivity is checkable.

`CategoryTheory.LocallySmall` for the presheaf category is a theorem rather than an instance,
so it is put in scope as a local instance: the statements below mention
`CategoryTheory.Presheaf.depProdπ`, whose elaboration needs it, so supplying it inside the
proofs would be too late.

## References

* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Presheaf Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Rigidity of the dependent product over the open complement -/

variable {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The computation `X ×_{g,W} W⁰ = W⁰` of Stacks 0BGY**, in the `fromPreimage` shape: if
`Y ⟶ V` is an isomorphism over `f⁻¹W₀`, then the dependent product of `Y` along `f` is an
isomorphism over `W₀`. -/
theorem isIso_fromPreimage_depProdπ (f : V ⟶ W) (W₀ : Subfunctor W) (Y : Over V)
    (hY : IsIso ((W₀.preimage f).fromPreimage Y.hom)) :
    IsIso (W₀.fromPreimage (depProdπ f Y)) := by
  classical
  -- The unique lift to `Y` of a section of `V` lying over `W₀`.
  have hex : ∀ {A : (BigFppfOver B S hS)ᵒᵖ} (v : V.obj A), f.app A v ∈ W₀.obj A →
      ∃ z : Y.left.obj A, Y.hom.app A z = v := fun {A} v hv =>
    exists_app_eq_of_mem B S hS Y.hom (W₀.preimage f) hY (A := A) (w := v) hv
  have huniq : ∀ {A : (BigFppfOver B S hS)ᵒᵖ} (v : V.obj A) (_ : f.app A v ∈ W₀.obj A)
      (z₁ z₂ : Y.left.obj A), Y.hom.app A z₁ = v → Y.hom.app A z₂ = v → z₁ = z₂ := by
    intro A v hv z₁ z₂ h₁ h₂
    refine eq_of_app_eq_of_mem B S hS Y.hom (W₀.preimage f) hY (h₁.trans h₂.symm) ?_
    show f.app A (Y.hom.app A z₁) ∈ W₀.obj A
    rwa [h₁]
  -- The forced second component of a section lying over `W₀`.
  have hsec : ∀ (A : (BigFppfOver B S hS)ᵒᵖ) (w : W.obj A), w ∈ W₀.obj A →
      DepProdSection f Y A.unop w := by
    intro A w hw
    have hmem : ∀ {A' : BigFppfOver B S hS} (h : A' ⟶ A.unop) (v : V.obj (op A')),
        f.app (op A') v = W.map h.op w → f.app (op A') v ∈ W₀.obj (op A') := by
      intro A' h v hv
      rw [hv]
      exact W₀.map h.op hw
    refine DepProdSection.mk' (fun h v hv => (hex v (hmem h v hv)).choose)
      (fun h v hv => (hex v (hmem h v hv)).choose_spec) ?_
    intro A₁ A₂ k h v hv
    have hk := hmem (k ≫ h) (V.map k.op v) (map_compat f k h hv)
    refine huniq _ hk _ _ ?_ (hex _ hk).choose_spec
    rw [NatTrans.naturality_apply Y.hom k.op, (hex v (hmem h v hv)).choose_spec]
  -- Invertibility, checked on sections.
  have happ : ∀ A : (BigFppfOver B S hS)ᵒᵖ,
      IsIso ((W₀.fromPreimage (depProdπ f Y)).app A) := by
    intro A
    rw [CategoryTheory.isIso_iff_bijective]
    constructor
    · rintro ⟨⟨w₁, y₁⟩, hp₁⟩ ⟨⟨w₂, y₂⟩, hp₂⟩ hpq
      refine Subtype.ext (depProdMk_ext f (congrArg Subtype.val hpq) ?_)
      intro A' h v hv hv'
      refine huniq v ?_ _ _ (y₁.over h v hv) (y₂.over h v hv')
      rw [hv]
      exact W₀.map h.op hp₁
    · rintro ⟨w, hw⟩
      exact ⟨⟨⟨w, hsec A w hw⟩, hw⟩, rfl⟩
  have _ := happ
  exact NatIso.isIso_of_isIso_app _

/-- **The computation `X ×_{g,W} W⁰ = W⁰` of Stacks 0BGY**, in the shape the definition of a
modification uses. -/
theorem isIso_pullback_snd_depProdπ (f : V ⟶ W) (W₀ : Subfunctor W) (Y : Over V)
    (hY : IsIso (pullback.snd Y.hom (W₀.preimage f).ι)) :
    IsIso (pullback.snd (depProdπ f Y) W₀.ι) :=
  isIso_pullback_snd_of_isIso_fromPreimage B S hS _ _
    (isIso_fromPreimage_depProdπ B S hS f W₀ Y
      (isIso_fromPreimage_of_isIso_pullback_snd Y.hom (W₀.preimage f) hY))

end AlgebraicGeometry.Space

end
