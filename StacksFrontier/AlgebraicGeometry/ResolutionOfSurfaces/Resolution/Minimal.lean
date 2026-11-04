module

public import StacksFrontier.AlgebraicGeometry.BirationalDenseOpenIso.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.IsoOverDenseOpen
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChangeBirational.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.Basic

/-!
# Minimal resolutions of singularities

A resolution of singularities `f : X ⟶ Y` of a Noetherian integral scheme is *minimal* if every
resolution of singularities of `Y` factors through it. The Stacks project uses the notion (for
instance in [Stacks, Tag 0EA2] and [Stacks, Tag 0EA3], "choose a minimal resolution of
singularities", with existence in [Stacks, Tag 0BGP]) without stating a definition in the chapter
on resolution of surfaces; the definition here is the standard one, and the factorization it
asks for is automatically unique (`AlgebraicGeometry.IsMinimalResolution.factor_unique`).

## Main definitions

* `AlgebraicGeometry.IsMinimalResolution`: `f` is a resolution of singularities of its target
  through which every resolution of singularities of the target factors.

## Main results

* `AlgebraicGeometry.IsMinimalResolution.exists_factor`: a resolution factors through a minimal
  one.
* `AlgebraicGeometry.IsModification.of_comp_eq`: the factor `h` in `h ≫ f = g`, for `f` and `g`
  modifications, is a modification.
* `AlgebraicGeometry.IsMinimalResolution.factor_unique`: the factorization is unique. This holds
  for any modification `f` in place of a minimal resolution: `f` is separated and is an
  isomorphism over a dense open of its target, and the source of a resolution is reduced.

## References

* [Stacks Project, Tag 0BGK](https://stacks.math.columbia.edu/tag/0BGK)
* [Stacks Project, Tag 0EA2](https://stacks.math.columbia.edu/tag/0EA2)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism `f : X ⟶ Y` to a Noetherian integral scheme is a **minimal resolution of
singularities** of `Y` if it is a resolution of singularities ([Stacks, Tag 0BGK]) and every
resolution of singularities `g : Z ⟶ Y` factors as `g = h ≫ f`. The factorization is then unique,
see `AlgebraicGeometry.IsMinimalResolution.factor_unique`. -/
def IsMinimalResolution {X Y : Scheme.{u}} [IsIntegral Y] [IsNoetherian Y] (f : X ⟶ Y) : Prop :=
  IsResolution f ∧ ∀ (Z : Scheme.{u}) (g : Z ⟶ Y), IsResolution g → ∃ h : Z ⟶ X, h ≫ f = g

namespace IsMinimalResolution

variable {X Y : Scheme.{u}} [IsIntegral Y] [IsNoetherian Y] {f : X ⟶ Y}

/-- A minimal resolution is a resolution. -/
theorem isResolution (hf : IsMinimalResolution f) : IsResolution f := hf.1

/-- Every resolution factors through a minimal resolution. -/
theorem exists_factor (hf : IsMinimalResolution f) {Z : Scheme.{u}} (g : Z ⟶ Y)
    (hg : IsResolution g) : ∃ h : Z ⟶ X, h ≫ f = g :=
  hf.2 Z g hg

end IsMinimalResolution

/-- An integral scheme has finitely many irreducible components. -/
private theorem finite_irreducibleComponents_of_isIntegral (X : Scheme.{u}) [IsIntegral X] :
    Finite (irreducibleComponents X) := by
  rw [irreducibleComponents_eq_singleton]; infer_instance

/-- **Morphisms into a modification agreeing after composition are equal**, when their source
is integral and maps birationally to the target: `f` is an isomorphism over a dense open `V`
([Stacks, Tag 0BAJ]), the two morphisms agree on the dense open preimage of `V`, and `f` is
separated. -/
theorem IsModification.ext_of_comp_eq {X Y Z : Scheme.{u}} [IsIntegral Y]
    {f : X ⟶ Y} (hf : IsModification f) {g : Z ⟶ Y} (hg : IsModification g)
    {h₁ h₂ : Z ⟶ X} (e₁ : h₁ ≫ f = g) (e₂ : h₂ ≫ f = g) : h₁ = h₂ := by
  have := hf.isProper
  have := hf.source_isIntegral
  have := hg.source_isIntegral
  have := finite_irreducibleComponents_of_isIntegral X
  have := finite_irreducibleComponents_of_isIntegral Y
  obtain ⟨V, hVd, hV⟩ := exists_dense_open_isIso_morphismRestrict_of_isBirational f
    hf.isBirational (Or.inr inferInstance) (Or.inl ⟨inferInstance, inferInstance⟩)
  -- The generic point of `Z` maps to the generic point of `Y`, which lies in `V`.
  have hgen : g (genericPoint Z) ∈ (V : Set Y) := by
    have hmem : g (genericPoint Z) ∈ genericPoints Y :=
      hg.isBirational.bijOn.mapsTo (by rw [genericPoints_eq_singleton]; rfl)
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hmem
    rw [hmem]
    obtain ⟨y, hy⟩ := hVd.nonempty
    exact (genericPoint_spec Y).mem_open_set_iff V.isOpen |>.2 ⟨y, trivial, hy⟩
  set W : Z.Opens := g ⁻¹ᵁ V
  have hWd : Dense (W : Set Z) := W.isOpen.dense ⟨genericPoint Z, hgen⟩
  have : IsDominant W.ι := Opens.isDominant_ι hWd
  refine ext_of_isDominant_of_isSeparated f (e₁.trans e₂.symm) W.ι ?_
  -- Both composites land in `f ⁻¹ᵁ V`, over which `f` is an isomorphism onto `V`.
  have hr : ∀ h : Z ⟶ X, h ≫ f = g → Set.range (W.ι ≫ h) ⊆ Set.range (f ⁻¹ᵁ V).ι := by
    intro h e
    rintro _ ⟨w, rfl⟩
    refine ⟨⟨(W.ι ≫ h) w, ?_⟩, rfl⟩
    change f ((W.ι ≫ h) w) ∈ (V : Set Y)
    rw [← Scheme.Hom.comp_apply, Category.assoc, e]
    exact w.2
  have key : IsOpenImmersion.lift (f ⁻¹ᵁ V).ι (W.ι ≫ h₁) (hr h₁ e₁) =
      IsOpenImmersion.lift (f ⁻¹ᵁ V).ι (W.ι ≫ h₂) (hr h₂ e₂) := by
    rw [← cancel_mono (f ∣_ V), ← cancel_mono V.ι, Category.assoc, Category.assoc,
      morphismRestrict_ι, ← Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc,
      IsOpenImmersion.lift_fac, Category.assoc, Category.assoc, e₁, e₂]
  rw [← IsOpenImmersion.lift_fac (f ⁻¹ᵁ V).ι (W.ι ≫ h₁) (hr h₁ e₁),
    ← IsOpenImmersion.lift_fac (f ⁻¹ᵁ V).ι (W.ι ≫ h₂) (hr h₂ e₂), key]

/-- **A factorization of a modification through a modification is a modification.** If
`h ≫ f = g` with `f` and `g` modifications of the integral scheme `Y`, then `h` is proper, since
`g` is proper and `f` is separated, and birational, since the generic points of the source of `f`
are exactly the preimages of the generic point of `Y`. -/
theorem IsModification.of_comp_eq {X Y Z : Scheme.{u}} [IsIntegral Y] {f : X ⟶ Y}
    (hf : IsModification f) {g : Z ⟶ Y} (hg : IsModification g) {h : Z ⟶ X} (e : h ≫ f = g) :
    haveI := hf.source_isIntegral
    IsModification h := by
  have := hf.isProper
  have := hf.source_isIntegral
  have := hg.source_isIntegral
  have : IsProper (h ≫ f) := e ▸ hg.isProper
  have := finite_irreducibleComponents_of_isIntegral X
  have := finite_irreducibleComponents_of_isIntegral Y
  refine ⟨isBirational_of_comp_of_isBirational h f (e ▸ hg.isBirational) hf.isBirational
    (preimage_genericPoints_eq_genericPoints_of_isBirational f hf.isBirational),
    IsProper.of_comp h f, inferInstance⟩

/-- **The factorization through a minimal resolution is unique.** -/
theorem IsMinimalResolution.factor_unique {X Y Z : Scheme.{u}} [IsIntegral Y] [IsNoetherian Y]
    {f : X ⟶ Y} (hf : IsMinimalResolution f) {g : Z ⟶ Y} (hg : IsResolution g)
    {h₁ h₂ : Z ⟶ X} (e₁ : h₁ ≫ f = g) (e₂ : h₂ ≫ f = g) : h₁ = h₂ :=
  hf.isResolution.isModification.ext_of_comp_eq hg.isModification e₁ e₂

/-- **Existence and uniqueness of the factorization through a minimal resolution.** -/
theorem IsMinimalResolution.existsUnique_factor {X Y Z : Scheme.{u}} [IsIntegral Y]
    [IsNoetherian Y] {f : X ⟶ Y} (hf : IsMinimalResolution f) (g : Z ⟶ Y)
    (hg : IsResolution g) : ∃! h : Z ⟶ X, h ≫ f = g := by
  obtain ⟨h, e⟩ := hf.exists_factor g hg
  exact ⟨h, e, fun h' e' => hf.factor_unique hg e' e⟩

end AlgebraicGeometry

end
