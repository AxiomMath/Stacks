module

public import StacksFrontier.CategoryTheory.FiberedCategory.Strictification
public import StacksFrontier.CategoryTheory.Sites.Stackification.LocalEquality

/-! # Quotienting the morphisms of a fibred category by local equality

This is the first stage of the three-stage construction of the stackification of a fibred
category. Let `p : 𝒳 ⥤ 𝒮` be a category over a site `(𝒮, J)`. Local equality of morphisms
is a congruence (`CategoryTheory.Functor.congruence_locallyEqualRel`), so we may form the
quotient category

`CategoryTheory.Functor.MorQuotient p J`

with the same objects as `𝒳` and with morphisms the local-equality classes of morphisms of
`𝒳`. Since locally equal morphisms lie over the same morphism of `𝒮`, the structure functor
`p` descends to `CategoryTheory.Functor.morQuotientProj p J`, and the quotient functor
`CategoryTheory.Functor.toMorQuotient p J` is strictly over `𝒮`.

The source states, and omits, two checks at this stage: that the quotient functor preserves
strongly cartesian morphisms, and that the quotient is again a fibred category. Both are
proved here.

## Main definitions

* `CategoryTheory.Functor.MorQuotient`: the quotient category, `𝒮¹` in the source.
* `CategoryTheory.Functor.toMorQuotient`: the quotient functor, `G¹` in the source.
* `CategoryTheory.Functor.morQuotientProj`: the descended structure functor, `p¹`.

## Main results

* `CategoryTheory.Quotient.lift_spec`: the quotient functor is *strictly* over the base,
  `toMorQuotient ⋙ morQuotientProj = p`.
* `CategoryTheory.Functor.isStronglyCartesian_toMorQuotient_map`: the quotient functor
  preserves strongly cartesian morphisms. This needs no fibredness hypothesis.
* `CategoryTheory.Functor.isFibered_morQuotientProj`: if `p` is fibred then so is the
  descended structure functor.
* `CategoryTheory.Functor.isFibredOneMorphism_toMorQuotient`: the two checks above,
  packaged as the statement that `toMorQuotient` is a 1-morphism of fibred categories
  over `𝒮`.

## References

This is the first stage of the proof of Stacks 02ZN ("first, given `x` lying over `U` ...
we can quotient out by this equivalence relation to obtain a new category `𝒮¹`"), together
with the two checks the source omits ("one checks that `G¹` preserves strongly cartesian
morphisms and that `𝒮¹` is a fibred category over `𝒞`. Checks omitted.").
-/

@[expose] public section

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

open CategoryTheory Category

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- The category obtained from `𝒳` by identifying locally equal morphisms. This is the
category `𝒮¹` of the first stage of the construction of the stackification. Its objects are
those of `𝒳`; its morphisms are the local-equality classes of morphisms of `𝒳`. -/
abbrev MorQuotient (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) : Type u₂ :=
  CategoryTheory.Quotient (p.locallyEqualRel J)

/-- The quotient functor `𝒳 ⥤ MorQuotient p J`, which is the identity on objects and sends
a morphism to its local-equality class. This is the 1-morphism `G¹ : 𝒮 ⥤ 𝒮¹`. -/
@[implicit_reducible]
def toMorQuotient (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) : 𝒳 ⥤ p.MorQuotient J :=
  CategoryTheory.Quotient.functor _

/-- The structure functor of `𝒳` descends to the quotient, because locally equal morphisms
lie over the same morphism of the base. This is `p¹ : 𝒮¹ ⥤ 𝒞`. -/
@[implicit_reducible]
def morQuotientProj (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) : p.MorQuotient J ⥤ 𝒮 :=
  CategoryTheory.Quotient.lift _ p fun _ _ _ _ h ↦ h.1

variable {p : 𝒳 ⥤ 𝒮} {J : GrothendieckTopology 𝒮}

/-- The quotient functor is the identity on objects. -/
@[simp]
theorem toMorQuotient_obj (x : 𝒳) : (p.toMorQuotient J).obj x = ⟨x⟩ := rfl

/-- The descended structure functor sends an object of the quotient to the image under `p` of the
object of `𝒳` it comes from. -/
@[simp]
theorem morQuotientProj_obj (A : p.MorQuotient J) :
    (p.morQuotientProj J).obj A = p.obj A.as := rfl

/-- The descended structure functor sends the class of `φ` to `p.map φ`. -/
@[simp]
theorem morQuotientProj_map_toMorQuotient_map {x y : 𝒳} (φ : x ⟶ y) :
    (p.morQuotientProj J).map ((p.toMorQuotient J).map φ) = p.map φ := rfl

/-- The quotient functor is full: every morphism of the quotient is the class of a morphism
of `𝒳`. -/
instance full_toMorQuotient : (p.toMorQuotient J).Full :=
  CategoryTheory.Quotient.full_functor _

/-- Every morphism of the quotient category is the class of a morphism of `𝒳`. -/
theorem exists_eq_toMorQuotient_map {A B : p.MorQuotient J} (F : A ⟶ B) :
    ∃ f : A.as ⟶ B.as, (p.toMorQuotient J).map f = F :=
  ⟨(p.toMorQuotient J).preimage F, (p.toMorQuotient J).map_preimage F⟩

/-- **The quotient functor preserves strongly cartesian morphisms.** This is the first of
the two checks the source omits at this stage.

Existence of the factorization comes from the universal property in `𝒳` together with the
fact that every morphism of the quotient lifts to `𝒳`. Uniqueness is the interesting half:
two lifts of a factorization agree only *locally* a priori, and one has to see that they
therefore agree in the quotient. They do, because the uniqueness clause of the universal
property in `𝒳` can be applied after restricting along each member of the witnessing
covering sieve.

No fibredness hypothesis on `p` is needed. -/
theorem isStronglyCartesian_toMorQuotient_map {R S : 𝒮} (f : R ⟶ S) {x y : 𝒳} (φ : x ⟶ y)
    (hφ : p.IsStronglyCartesian f φ) :
    (p.morQuotientProj J).IsStronglyCartesian f ((p.toMorQuotient J).map φ) := by
  have := hφ
  have hcomp : p.toMorQuotient J ⋙ p.morQuotientProj J = p :=
    CategoryTheory.Quotient.lift_spec _ _ _
  refine
    { toIsHomLift :=
        isHomLift_map_of_comp_eq hcomp f φ
      universal_property' := ?_ }
  intro A' g Ψ hΨ
  -- Lift `Ψ` to a morphism `ψ` of `𝒳`.
  obtain ⟨ψ, hψ⟩ := exists_eq_toMorQuotient_map Ψ
  have : (p.morQuotientProj J).IsHomLift (g ≫ f) ((p.toMorQuotient J).map ψ) := by
    rw [hψ]; exact hΨ
  have : p.IsHomLift (g ≫ f) ψ :=
    isHomLift_of_isHomLift_map hcomp (g ≫ f) ψ
  -- Apply the universal property in `𝒳`.
  obtain ⟨χ, ⟨hχ₁, hχ₂⟩, huniq⟩ :=
    IsStronglyCartesian.universal_property' (p := p) (f := f) (φ := φ) (a' := A'.as) g ψ
  have := hχ₁
  refine ⟨(p.toMorQuotient J).map χ, ⟨?_, ?_⟩, ?_⟩
  · exact isHomLift_map_of_comp_eq hcomp g χ
  · rw [← Functor.map_comp, hχ₂, hψ]
  -- Uniqueness.
  · rintro X ⟨hX₁, hX₂⟩
    obtain ⟨χ', hχ'⟩ := exists_eq_toMorQuotient_map X
    subst hχ'
    have := hX₁
    have : p.IsHomLift g χ' :=
      isHomLift_of_isHomLift_map hcomp g χ'
    -- `χ' ≫ φ` and `ψ` are locally equal.
    have hloc : p.LocallyEqual J (χ' ≫ φ) ψ := by
      refine (CategoryTheory.Quotient.functor_map_eq_iff (p.locallyEqualRel J) _ _).mp ?_
      change (p.toMorQuotient J).map (χ' ≫ φ) = (p.toMorQuotient J).map ψ
      rw [Functor.map_comp, hX₂, hψ]
    obtain ⟨-, T, hT, hagree⟩ := hloc
    refine (CategoryTheory.Quotient.functor_map_eq_iff (p.locallyEqualRel J) _ _).mpr ?_
    -- The two lifts lie over the same morphism of the base.
    refine ⟨?_, T, hT, fun w ρ hρ ↦ ?_⟩
    · rw [IsHomLift.fac' p g χ', IsHomLift.fac' p g χ]
    · -- After restricting along `ρ`, both composites with `φ` agree, so the uniqueness
      -- clause of the universal property in `𝒳` applies.
      have : p.IsHomLift (p.map ρ ≫ g) (ρ ≫ χ') := inferInstance
      have : p.IsHomLift (p.map ρ ≫ g) (ρ ≫ χ) := inferInstance
      refine IsStronglyCartesian.ext p f φ (p.map ρ ≫ g) ?_
      have hkey := hagree ρ hρ
      rw [← hχ₂] at hkey
      simpa only [assoc] using hkey

/-- **The descended structure functor is fibred.** This is the second of the two checks the
source omits at this stage: push a strongly cartesian lift in `𝒳` forward to the quotient,
which is strongly cartesian by `isStronglyCartesian_toMorQuotient_map`. -/
instance isFibered_morQuotientProj [p.IsFibered] : (p.morQuotientProj J).IsFibered := by
  refine IsFibered.of_exists_isStronglyCartesian fun A R f ↦ ?_
  have ha : p.obj A.as = (p.morQuotientProj J).obj A := rfl
  have hcart : p.IsStronglyCartesian f (IsPreFibered.pullbackMap ha f) := inferInstance
  exact ⟨(p.toMorQuotient J).obj (IsPreFibered.pullbackObj ha f),
    (p.toMorQuotient J).map (IsPreFibered.pullbackMap ha f),
    isStronglyCartesian_toMorQuotient_map f _ hcart⟩

/-- **The quotient functor is a 1-morphism of fibred categories over `𝒮`.** This packages
the two checks the source omits at the first stage of the construction of the
stackification: `toMorQuotient` is strictly over the base and preserves strongly cartesian
morphisms. -/
theorem isFibredOneMorphism_toMorQuotient (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) :
    IsFibredOneMorphism p (p.morQuotientProj J) (p.toMorQuotient J) where
  comp_eq := CategoryTheory.Quotient.lift_spec _ _ _
  map_isStronglyCartesian := by
    intro R T f a b φ h
    exact isStronglyCartesian_toMorQuotient_map f φ h

end CategoryTheory.Functor
