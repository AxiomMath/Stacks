module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsFull
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsSupplement

/-!
# The functor of points of a formal scheme on all schemes

The functor of points `AlgebraicGeometry.formalSchemePointsFunctor`, sending a formal scheme `𝔛`
to the presheaf `h_𝔛` of its points on the category of all schemes, is fully faithful, with no
size hypothesis on the formal schemes involved.

## Main definitions

* `AlgebraicGeometry.fullyFaithfulFormalSchemePointsFunctor`: the functor of points on all
  schemes is a fully faithful embedding of formal schemes into presheaves on schemes.

## Main results

* `AlgebraicGeometry.exists_formalSchemePointsFunctor_map_eq`: every transformation
  `h_𝔛 → h_𝔜` is induced by a morphism of formal schemes `𝔛 → 𝔜`.
* `AlgebraicGeometry.bijective_formalSchemePointsFunctor_map`: the functor of points induces a
  bijection `Mor(𝔛, 𝔜) = Mor(h_𝔛, h_𝔜)`.
* `AlgebraicGeometry.full_formalSchemePointsFunctor`: the functor of points on all schemes is
  full.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

open TopologicalRing

section ChartRestrict

variable {X : LTRS.{u}} (U : Opens X) (A : Type u) [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A]
  (e : X.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding' ≅ Spf A)
  (V : Opens X)

end ChartRestrict

section Spf

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] (hA : IsAdmissible A)

variable {κ : Cardinal.{u}} {Y : FormalScheme.{u}}

end Spf

/-! ### Full faithfulness on the category of all schemes -/

/-- Every transformation `h_𝔛 → h_𝔜` of functors of points on the category of all schemes is
induced by a morphism of formal schemes `𝔛 → 𝔜`, with no size hypothesis. -/
@[stacks 0AI1 "surjectivity on all schemes: every transformation of functors of points is \
induced by a morphism of formal schemes, with no size hypothesis"]
theorem exists_formalSchemePointsFunctor_map_eq {X Y : FormalScheme.{u}}
    (φ : formalSchemePointsFunctor.obj X ⟶ formalSchemePointsFunctor.obj Y) :
    ∃ f : X ⟶ Y, formalSchemePointsFunctor.map f = φ := by
  obtain ⟨κ₀, hκ₀⟩ := exists_isSizeBoundedFormalScheme X.property
  have hex : ∀ κ, κ₀ ≤ κ → ∃ h : X ⟶ Y, ∀ (S : Scheme.{u}), S.size < κ →
      ∀ q : schemeToFormalScheme.obj S ⟶ X, q ≫ h = φ.app (op S) q := by
    intro κ hκ
    obtain ⟨h, hh⟩ := exists_formalSchemeFunctorOfPoints_map_eq (hκ₀.mono hκ)
      (((Functor.whiskeringLeft _ _ _).obj ((schemeCutoff κ).ι.op)).map φ)
    exact ⟨h, fun S hS q =>
      congrFun (congrArg (fun η => η.app (op (⟨S, hS⟩ : (schemeCutoff κ).FullSubcategory))) hh) q⟩
  obtain ⟨f, hf⟩ := hex κ₀ le_rfl
  refine ⟨f, ?_⟩
  ext T g
  obtain ⟨κ, hgt, -, -⟩ :=
    Cardinal.exists_isStrongPrelimit_gt_of_aleph0_lt_cof (max κ₀ T.unop.size)
  have hκ₀κ : κ₀ ≤ κ := ((le_max_left _ _).trans_lt hgt).le
  obtain ⟨f', hf'⟩ := hex κ hκ₀κ
  have hff : f' = f := by
    refine injective_formalSchemeFunctorOfPoints_map hκ₀ ?_
    ext S q
    exact (hf' S.unop.obj (S.unop.property.trans_le hκ₀κ) q).trans
      (hf S.unop.obj S.unop.property q).symm
  exact (congrArg (fun h : X ⟶ Y => g ≫ h) hff.symm).trans
    (hf' T.unop ((le_max_right _ _).trans_lt hgt) g)

/-- For formal schemes `𝔛` and `𝔜`, the functor of points on the category of all schemes induces
a bijection

`Mor_{Formal Schemes}(𝔛, 𝔜) = Mor_{PSh(Sch)}(h_𝔛, h_𝔜)`,

with no size hypothesis. -/
@[stacks 0AI1 "the bijection Mor(𝔛, 𝔜) = Mor(h_𝔛, h_𝔜) on all schemes, with no size \
hypothesis"]
theorem bijective_formalSchemePointsFunctor_map {X Y : FormalScheme.{u}} :
    Function.Bijective fun f : X ⟶ Y => formalSchemePointsFunctor.map f :=
  ⟨injective_formalSchemePointsFunctor_map, exists_formalSchemePointsFunctor_map_eq⟩

/-- The functor of points of formal schemes on the category of all schemes is full, with no size
hypothesis. -/
@[stacks 0AI1 "fullness of the functor of points on morphisms, with no size hypothesis",
  stacks 0AIR "fullness of the embedding by the functor of points, on all schemes"]
instance full_formalSchemePointsFunctor : formalSchemePointsFunctor.{u}.Full where
  map_surjective φ := exists_formalSchemePointsFunctor_map_eq φ

/-- Taking the functor of points on the category of all schemes is a fully faithful embedding of
the category of formal schemes into presheaves of sets on schemes. -/
@[stacks 0AIR "the assignment 𝔛 ↦ h_𝔛 is a fully faithful embedding of formal schemes into \
presheaves on schemes"]
noncomputable def fullyFaithfulFormalSchemePointsFunctor :
    formalSchemePointsFunctor.{u}.FullyFaithful :=
  .ofFullyFaithful formalSchemePointsFunctor

end AlgebraicGeometry

end
