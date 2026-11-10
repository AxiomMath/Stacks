module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.FiniteCoverIsom
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.AffineFibreIso
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.SpecEssImage

/-!
# The 1-morphism `Spec` is bijective on the morphisms of a fibre over an affine object

Let `S` be a scheme of a big fppf site and let `d` be a positive natural number. Over an object
`V` of the big fppf site over `S` whose underlying scheme is affine, the functor induced on the
fibres over `V` by the 1-morphism `Spec` of Stacks 05YQ is bijective on every hom-set: two free
`d`-dimensional structures on the global sections of `V` have exactly as many isomorphisms as the
degree-`d` covers they attach.

This is the affine core of clause (1) of Stacks 02ZN for `Spec`, that is of clause (a) of the
proof of Stacks 05YQ. The passage from affine objects to arbitrary ones — where the clause is only
a *local* statement — is
`StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/FiniteFreeAlgebra/SpecLocallyBijective.lean`.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.fibreObj` and
  `AlgebraicGeometry.FiniteFreeAlgebra.fibreHomOfStructureIso`: the object and the morphism of the
  fibre over `V` of the pointwise groupoid fibration of free rank-`d` structures attached to a
  structure and to an isomorphism of structures.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.bijective_fibreHomOfStructureIso`: every morphism of the
  fibre over `V` comes from exactly one isomorphism of structures.
* `AlgebraicGeometry.FiniteFreeAlgebra.specCoverHom_id_injective` and
  `AlgebraicGeometry.FiniteFreeAlgebra.exists_structureIso_of_hom`: over an affine base, `Spec` is
  injective on the isomorphisms of structures, and every morphism of `ℋ_d` over the identity of
  the base between two `Spec` covers is `Spec` of an isomorphism of structures.
* `AlgebraicGeometry.FiniteFreeAlgebra.bijective_fiberFunctorOfCompEq_map`: **the affine core of
  clause (1) of Stacks 02ZN for `Spec`.** Over an affine object the fibre functor of `Spec` is
  bijective on hom-sets.

## Implementation notes

An object of the pointwise groupoid fibration is a pair `(V, m)` and a morphism is a pair
`(f, e)`, so a morphism of the fibre over `V` is a morphism whose base component lies over the
identity; `AlgebraicGeometry.FiniteFreeAlgebra.base_eq_id_of_isHomLift` turns that condition into
the equality `f = 𝟙 V` and hence identifies the hom-sets of the fibre with the isomorphisms of
structures, extension of scalars along the identity of `V` being the identity on the nose. The
remaining dependency of the fibre component on the base component is discharged by
`CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.ext` and
`CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.congr`, whose comparison isomorphism is here an
identity.

The affine content is entirely
`AlgebraicGeometry.FiniteFreeAlgebra.structureIsoEquivCoverIso`: injectivity is its injectivity
read through `AlgebraicGeometry.FiniteFreeAlgebra.structureIsoEquivCoverIso_hom_left`, and
surjectivity is its surjectivity, the isomorphism of covers being manufactured from a morphism of
`ℋ_d` over the identity by `CategoryTheory.IsPullback.isIso_fst_of_isIso` applied to the cartesian
square that the morphism carries. The passage between morphisms of `ℋ_d` and morphisms of schemes
is the extensionality lemma `AlgebraicGeometry.Stack.FiniteCover.Hom.ext` together with the
faithfulness of `AlgebraicGeometry.BigFppfOver.toScheme`.

`CategoryTheory.Functor.toPseudofunctor'` and
`AlgebraicGeometry.FiniteFreeAlgebra.specCoverObject` are plain definitions, so a goal mentioning
both a structure over `V` and an object of the fibre over `V`, or both `V` and the base object of
a `Spec` cover over `V`, is not type-correct at `implicit` transparency and `rw`/`simp` refuse it;
they are unfolded locally below, as in
`StacksFrontier/CategoryTheory/FiberedCategory/OfPresheaf.lean`.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

attribute [local instance] FiniteFreeAlgebra.groupoid

attribute [local implicit_reducible] Functor.toPseudofunctor'
  pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc FiniteFreeAlgebra.map
  specCoverObject

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S} {d : ℕ} [NeZero d]

/-! ### The fibre of the pointwise groupoid fibration over an object of the site -/

/-- The object of the fibre over `V` of the pointwise groupoid fibration of free rank-`d`
structures given by a free `d`-dimensional structure on the global sections of `V`. -/
abbrev fibreObj (V : BigFppfOver 𝒞 S hS)
    (m : FiniteFreeAlgebra Γ((BigFppfOver.toScheme 𝒞 S hS).obj V, ⊤) d) :
    (CategoryTheory.presheafOfGroupoids (ffaSitePresheaf 𝒞 S hS d)).p.Fiber V :=
  ⟨⟨V, m⟩, rfl⟩

/-- The morphism of the fibre over `V` attached to an isomorphism of free `d`-dimensional
structures on the global sections of `V`: its base component is the identity of `V` and its fibre
component is the isomorphism, extension of scalars along the identity being the identity. -/
def fibreHomOfStructureIso {V : BigFppfOver 𝒞 S hS}
    {m₁ m₂ : FiniteFreeAlgebra Γ((BigFppfOver.toScheme 𝒞 S hS).obj V, ⊤) d}
    (e : StructureIso m₁ m₂) : fibreObj V m₁ ⟶ fibreObj V m₂ :=
  ⟨⟨𝟙 V, e⟩, by
    exact CategoryTheory.Functor.IsHomLift.map
      (p := (CategoryTheory.presheafOfGroupoids (ffaSitePresheaf 𝒞 S hS d)).p)
      (a := ⟨V, m₁⟩) (b := ⟨V, m₂⟩) ⟨𝟙 V, e⟩⟩

/-- The morphism of the pointwise groupoid fibration underlying
`AlgebraicGeometry.FiniteFreeAlgebra.fibreHomOfStructureIso`. -/
@[simp]
theorem fiberInclusion_map_fibreHomOfStructureIso {V : BigFppfOver 𝒞 S hS}
    {m₁ m₂ : FiniteFreeAlgebra Γ((BigFppfOver.toScheme 𝒞 S hS).obj V, ⊤) d}
    (e : StructureIso m₁ m₂) :
    CategoryTheory.Functor.Fiber.fiberInclusion.map (fibreHomOfStructureIso e) =
      ⟨𝟙 V, e⟩ := rfl

/-- A morphism lying over `f` has image `f` under the projection. -/
private theorem map_eq_of_isHomLift {𝒮 𝒳 : Type*} [Category 𝒳] [Category 𝒮] {p : 𝒳 ⥤ 𝒮}
    {a b : 𝒳} {φ : a ⟶ b} {f : p.obj a ⟶ p.obj b} (h : p.IsHomLift f φ) : p.map φ = f :=
  haveI := h
  (IsHomLift.eq_of_isHomLift p f φ).symm

/-- **The base component of a morphism of the pointwise groupoid fibration lying over the identity
of `V` is the identity of `V`.** -/
theorem base_eq_id_of_isHomLift {V : BigFppfOver 𝒞 S hS}
    {m₁ m₂ : FiniteFreeAlgebra Γ((BigFppfOver.toScheme 𝒞 S hS).obj V, ⊤) d}
    (Ψ : (⟨V, m₁⟩ : (CategoryTheory.presheafOfGroupoids (ffaSitePresheaf 𝒞 S hS d)).obj) ⟶
      ⟨V, m₂⟩)
    (h : (CategoryTheory.presheafOfGroupoids (ffaSitePresheaf 𝒞 S hS d)).p.IsHomLift (𝟙 V) Ψ) :
    Ψ.base = 𝟙 V :=
  (map_eq_of_isHomLift h :)

/-- **The morphisms of the fibre over `V` are the isomorphisms of structures.** Every morphism of
the fibre comes from exactly one isomorphism of free `d`-dimensional structures on the global
sections of `V`. -/
theorem bijective_fibreHomOfStructureIso (V : BigFppfOver 𝒞 S hS)
    (m₁ m₂ : FiniteFreeAlgebra Γ((BigFppfOver.toScheme 𝒞 S hS).obj V, ⊤) d) :
    Function.Bijective
      (fun e : StructureIso m₁ m₂ => fibreHomOfStructureIso (𝒞 := 𝒞) (S := S) (hS := hS) e) := by
  constructor
  · intro e₁ e₂ h
    have h1 := CategoryTheory.Functor.Fiber.fiberInclusion.congr_map h
    rw [fiberInclusion_map_fibreHomOfStructureIso,
      fiberInclusion_map_fibreHomOfStructureIso] at h1
    have h2 : e₁ = e₂ ≫ 𝟙 m₂ := Pseudofunctor.CoGrothendieck.Hom.congr h1
    simpa using h2
  · intro ψ
    have hb : (CategoryTheory.Functor.Fiber.fiberInclusion.map ψ).base = 𝟙 V :=
      base_eq_id_of_isHomLift (V := V) (m₁ := m₁) (m₂ := m₂)
        (CategoryTheory.Functor.Fiber.fiberInclusion.map ψ) ψ.2
    refine ⟨(CategoryTheory.Functor.Fiber.fiberInclusion.map ψ).fiber ≫
      eqToHom (by rw [hb]; rfl), ?_⟩
    exact CategoryTheory.Functor.Fiber.hom_ext
      (Pseudofunctor.CoGrothendieck.Hom.ext _ _ hb.symm rfl)

/-! ### `Spec` on the morphisms of a fibre over an affine object -/

/-- The morphism of `ℋ_d` underlying the value of the fibre functor of `Spec` on
`AlgebraicGeometry.FiniteFreeAlgebra.fibreHomOfStructureIso`. -/
@[simp]
theorem fiberInclusion_map_map_fibreHomOfStructureIso {V : BigFppfOver 𝒞 S hS}
    {m₁ m₂ : FiniteFreeAlgebra Γ((BigFppfOver.toScheme 𝒞 S hS).obj V, ⊤) d}
    (e : StructureIso m₁ m₂) :
    CategoryTheory.Functor.Fiber.fiberInclusion.map
        ((CategoryTheory.Functor.fiberFunctorOfCompEq
          (isFibredOneMorphism_specFiniteCover 𝒞 S hS d).comp_eq V).map
            (fibreHomOfStructureIso e)) =
      specCoverHom (𝟙 V) e := rfl

/-- **Over an affine base `Spec` is injective on the isomorphisms of structures.** This is the
injectivity of `AlgebraicGeometry.FiniteFreeAlgebra.structureIsoEquivCoverIso`, read through the
agreement of that identification with `AlgebraicGeometry.FiniteFreeAlgebra.coverMap`. -/
theorem specCoverHom_id_injective (V : BigFppfOver 𝒞 S hS)
    [IsAffine ((BigFppfOver.toScheme 𝒞 S hS).obj V)]
    (m₁ m₂ : FiniteFreeAlgebra Γ((BigFppfOver.toScheme 𝒞 S hS).obj V, ⊤) d) :
    Function.Injective (fun e : StructureIso m₁ m₂ => specCoverHom (𝟙 V) e) := by
  intro e₁ e₂ h
  have h2 := congrArg (fun φ => (BigFppfOver.toScheme 𝒞 S hS).map
    (AlgebraicGeometry.Stack.FiniteCover.Hom.g φ)) h
  refine (structureIsoEquivCoverIso ((BigFppfOver.toScheme 𝒞 S hS).obj V) m₁ m₂).injective
    (Iso.ext (Over.OverMorphism.ext ?_))
  rw [structureIsoEquivCoverIso_hom_left, structureIsoEquivCoverIso_hom_left]
  exact h2

/-- **Over an affine base every morphism of `ℋ_d` over the identity of the base between two
`Spec` covers is `Spec` of an isomorphism of structures.** The cover component of such a morphism
sits in a cartesian square over an isomorphism, hence is an isomorphism, and
`AlgebraicGeometry.FiniteFreeAlgebra.structureIsoEquivCoverIso` turns the resulting isomorphism of
covers into an isomorphism of structures. -/
theorem exists_structureIso_of_hom (V : BigFppfOver 𝒞 S hS)
    [IsAffine ((BigFppfOver.toScheme 𝒞 S hS).obj V)]
    (m₁ m₂ : FiniteFreeAlgebra Γ((BigFppfOver.toScheme 𝒞 S hS).obj V, ⊤) d)
    (Ψ : specCoverObject V m₁ ⟶ specCoverObject V m₂) (hf : Ψ.f = 𝟙 V) :
    ∃ e : StructureIso m₁ m₂, specCoverHom (𝟙 V) e = Ψ := by
  have : IsIso Ψ.f := by
    rw [hf]
    exact CategoryTheory.IsIso.id V
  have : IsIso Ψ.g := Ψ.square.isIso_fst_of_isIso
  have hsq : IsPullback Ψ.g (specCoverObject V m₁).q (specCoverObject V m₂).q (𝟙 V) := by
    rw [← hf]
    exact Ψ.square
  have hw1 : Ψ.g ≫ (specCoverObject V m₂).q = (specCoverObject V m₁).q :=
    hsq.w.trans (Category.comp_id _)
  have hw : (BigFppfOver.toScheme 𝒞 S hS).map Ψ.g ≫
      (cover ((BigFppfOver.toScheme 𝒞 S hS).obj V) m₂).hom =
        (cover ((BigFppfOver.toScheme 𝒞 S hS).obj V) m₁).hom := by
    have h0 := congrArg (BigFppfOver.toScheme 𝒞 S hS).map hw1
    rwa [CategoryTheory.Functor.map_comp] at h0
  refine ⟨(structureIsoEquivCoverIso ((BigFppfOver.toScheme 𝒞 S hS).obj V) m₁ m₂).symm
    (Over.isoMk ((BigFppfOver.toScheme 𝒞 S hS).mapIso (asIso Ψ.g)) hw), ?_⟩
  refine AlgebraicGeometry.Stack.FiniteCover.Hom.ext hf.symm ?_
  refine (BigFppfOver.toScheme 𝒞 S hS).map_injective ?_
  change coverMap (𝟙 ((BigFppfOver.toScheme 𝒞 S hS).obj V))
      (toSpecΓ_id_naturality ((BigFppfOver.toScheme 𝒞 S hS).obj V)) _ =
    (BigFppfOver.toScheme 𝒞 S hS).map Ψ.g
  rw [← structureIsoEquivCoverIso_hom_left, Equiv.apply_symm_apply]
  rfl

/-- **Over an affine base `Spec` is bijective on the morphisms of a fibre attached to
isomorphisms of structures.** -/
theorem bijective_map_fibreHomOfStructureIso (V : BigFppfOver 𝒞 S hS)
    [IsAffine ((BigFppfOver.toScheme 𝒞 S hS).obj V)]
    (m₁ m₂ : FiniteFreeAlgebra Γ((BigFppfOver.toScheme 𝒞 S hS).obj V, ⊤) d) :
    Function.Bijective (fun e : StructureIso m₁ m₂ =>
      (CategoryTheory.Functor.fiberFunctorOfCompEq
        (isFibredOneMorphism_specFiniteCover 𝒞 S hS d).comp_eq V).map
          (fibreHomOfStructureIso e)) := by
  refine ⟨fun e₁ e₂ h => specCoverHom_id_injective V m₁ m₂
    (CategoryTheory.Functor.Fiber.fiberInclusion.congr_map h :
      specCoverHom (𝟙 V) e₁ = specCoverHom (𝟙 V) e₂), fun ψ => ?_⟩
  have hf : (CategoryTheory.Functor.Fiber.fiberInclusion.map ψ).f = 𝟙 V :=
    (map_eq_of_isHomLift ψ.2 :)
  obtain ⟨e, he⟩ := exists_structureIso_of_hom V m₁ m₂
    (CategoryTheory.Functor.Fiber.fiberInclusion.map ψ) hf
  exact ⟨e, CategoryTheory.Functor.Fiber.hom_ext he⟩

/-- **The affine core of clause (1) of Stacks 02ZN for the 1-morphism `Spec` of Stacks 05YQ**,
that is of clause (a) of the proof of 05YQ. Over an object `V` of the big fppf site over `S` whose
underlying scheme is affine, the functor induced by `Spec` on the fibres over `V` is bijective on
every hom-set. -/
theorem bijective_fiberFunctorOfCompEq_map (V : BigFppfOver 𝒞 S hS)
    [IsAffine ((BigFppfOver.toScheme 𝒞 S hS).obj V)]
    (x y : (CategoryTheory.presheafOfGroupoids (ffaSitePresheaf 𝒞 S hS d)).p.Fiber V) :
    Function.Bijective (fun m : x ⟶ y =>
      (CategoryTheory.Functor.fiberFunctorOfCompEq
        (isFibredOneMorphism_specFiniteCover 𝒞 S hS d).comp_eq V).map m) := by
  obtain ⟨⟨V₁, m₁⟩, hV₁⟩ := x
  obtain ⟨⟨V₂, m₂⟩, hV₂⟩ := y
  replace hV₁ : V = V₁ := hV₁.symm
  replace hV₂ : V = V₂ := hV₂.symm
  subst hV₁ hV₂
  exact (Function.Bijective.of_comp_iff _ (bijective_fibreHomOfStructureIso V m₁ m₂)).mp
    (bijective_map_fibreHomOfStructureIso V m₁ m₂)

end AlgebraicGeometry.FiniteFreeAlgebra

end
