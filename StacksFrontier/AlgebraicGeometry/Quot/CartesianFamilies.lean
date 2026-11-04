module

public import StacksCore.CategoryTheory.FiberedInGroupoids
public import StacksCore.Tactic.StacksAttribute
public import Mathlib.CategoryTheory.Widesubcategory
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStack
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.MultiplicativeClass
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.RestrictMorPresheaf

/-!
# Families of algebraic spaces with cartesian morphisms

Families of algebraic spaces over varying base schemes, with only the *cartesian* squares as
morphisms, form a category fibred in groupoids over the big fppf site. This holds for finite-type
families and for finitely presented, flat and proper families.

More generally, if `p : 𝒳 ⥤ 𝒮` is fibred and `P` is an object property closed under strongly
cartesian pullback, then the restriction of `p` to `P`, with only its strongly cartesian
morphisms, is fibred in groupoids.

## Main definitions

* `AlgebraicGeometry.CartesianFiniteTypeSpaces`: finite-type families of algebraic spaces over
  varying base schemes with cartesian morphisms.
* `AlgebraicGeometry.cartesianFiniteTypeProjection`: its projection to the big fppf site.
* `AlgebraicGeometry.isProperFlatSpace`: the finitely presented, flat and proper object property.
* `AlgebraicGeometry.CartesianProperFlatSpaces`: the families `AlgebraicGeometry.isProperFlatSpace`
  cuts out, with cartesian morphisms.
* `AlgebraicGeometry.cartesianProperFlatProjection`: their projection to the big fppf site.

## Main results

* `CategoryTheory.Functor.isFiberedInGroupoids_wideSubcategory`: the strongly cartesian
  morphisms of the restriction of a fibred functor to a property closed under strongly cartesian
  pullback form a category fibred in groupoids.
* `AlgebraicGeometry.cartesianFiniteTypeProjection_isFiberedInGroupoids`: the finite-type
  families form a category fibred in groupoids.
* `AlgebraicGeometry.cartesianProperFlatProjection_isFiberedInGroupoids`: the finitely
  presented, flat and proper families form a category fibred in groupoids.

## References

* [Stacks Project, Tag 0D1E](https://stacks.math.columbia.edu/tag/0D1E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- The strongly cartesian morphisms of a functor contain the identities and are closed under
composition, so they cut out a wide subcategory. -/
@[sga "1 VI 6.8" "partial"]
instance isMultiplicative_stronglyCartesianOver (p : 𝒳 ⥤ 𝒮) :
    (stronglyCartesianOver p).IsMultiplicative :=
  have : (stronglyCartesianOver p).ContainsIdentities := ⟨stronglyCartesianOver_id p⟩
  have : (stronglyCartesianOver p).IsStableUnderComposition :=
    ⟨stronglyCartesianOver_comp p⟩
  ⟨⟩

variable (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳) [p.IsFibered]

/-- Discarding every morphism of the restriction of `p` to `P` that is not strongly cartesian
over `p` leaves a category fibred in groupoids over `𝒮`, provided `P` is closed under strongly
cartesian pullback. -/
theorem isFiberedInGroupoids_wideSubcategory
    (hP : ClosedUnderStronglyCartesian p P) :
    (wideSubcategoryInclusion ((stronglyCartesianOver p).inverseImage P.ι) ⋙
      restrict p P).IsFiberedInGroupoids := by
  have : (restrict p P).IsFibered := isFibered_restrict_of_closed p P hP
  have key : ∀ {V U : 𝒮} {a b : P.FullSubcategory} (f : V ⟶ U) (φ : a ⟶ b),
      p.IsStronglyCartesian f (P.ι.map φ) → ((stronglyCartesianOver p).inverseImage P.ι) φ := by
    intro V U a b f φ h
    cases IsHomLift.domain_eq p f (P.ι.map φ)
    cases IsHomLift.codomain_eq p f (P.ι.map φ)
    obtain rfl : f = p.map (P.ι.map φ) := IsHomLift.eq_of_isHomLift p f (P.ι.map φ)
    exact h
  constructor
  · intro V U f x hx
    subst hx
    obtain ⟨y, φ, hφ⟩ := IsPreFibered.exists_isCartesian (restrict p P) rfl f
    have hcart : p.IsCartesian f (P.ι.map φ) := isCartesian_map_ι p P hP f φ hφ
    have hstrong : p.IsStronglyCartesian f (P.ι.map φ) :=
      IsFibered.isStronglyCartesian_of_isCartesian p f (P.ι.map φ)
    have hRφ := key f φ hstrong
    refine ⟨⟨y⟩, ⟨φ, hRφ⟩, ?_⟩
    have hlift : (restrict p P).IsHomLift f φ :=
      (isHomLift_restrict_iff p P f φ).2 hcart.toIsHomLift
    have hdom := IsHomLift.domain_eq (restrict p P) f φ
    cases hdom
    obtain rfl := IsHomLift.eq_of_isHomLift (restrict p P) f φ
    exact IsHomLift.map
      (p := wideSubcategoryInclusion ((stronglyCartesianOver p).inverseImage P.ι) ⋙
        restrict p P) ⟨φ, hRφ⟩
  · intro x y z φ ψ f hcomm
    obtain ⟨f, rfl⟩ :
        ∃ f' : p.obj (P.ι.obj z.obj) ⟶ p.obj (P.ι.obj y.obj), f' = f := ⟨f, rfl⟩
    have hφ : p.IsStronglyCartesian (p.map (P.ι.map φ.hom)) (P.ι.map φ.hom) := φ.property
    have hψ : p.IsStronglyCartesian (p.map (P.ι.map ψ.hom)) (P.ι.map ψ.hom) := ψ.property
    have hcomm' : f ≫ p.map (P.ι.map φ.hom) = p.map (P.ι.map ψ.hom) := hcomm
    have hlift : p.IsHomLift (f ≫ p.map (P.ι.map φ.hom)) (P.ι.map ψ.hom) := by
      rw [hcomm']
      exact IsHomLift.map (p := p) (P.ι.map ψ.hom)
    obtain ⟨χ, ⟨hχlift, hχfac⟩, hχuniq⟩ :=
      IsStronglyCartesian.universal_property p (p.map (P.ι.map φ.hom)) (P.ι.map φ.hom)
        f (f ≫ p.map (P.ι.map φ.hom)) rfl (P.ι.map ψ.hom)
    obtain ⟨χ₀, rfl⟩ := P.ι.map_surjective χ
    have hχfac₀ : P.ι.map χ₀ ≫ P.ι.map φ.hom = P.ι.map ψ.hom := hχfac
    have hχstrong : ((stronglyCartesianOver p).inverseImage P.ι) χ₀ := by
      have hcompstrong : p.IsStronglyCartesian (f ≫ p.map (P.ι.map φ.hom))
          (P.ι.map χ₀ ≫ P.ι.map φ.hom) := by
        rw [hcomm', hχfac₀]
        exact hψ
      exact key f χ₀ (IsStronglyCartesian.of_comp (p := p) (f := f) (g := p.map (P.ι.map φ.hom))
          (φ := P.ι.map χ₀) (ψ := P.ι.map φ.hom))
    have hqlift : (restrict p P).IsHomLift f χ₀ := (isHomLift_restrict_iff p P f χ₀).2 hχlift
    refine ⟨⟨χ₀, hχstrong⟩,
      ⟨(IsHomLift.eq_of_isHomLift (restrict p P) f χ₀).symm,
        WideSubcategory.hom_ext _ (P.ι.map_injective hχfac₀)⟩, ?_⟩
    rintro η ⟨hηeq, hηfac⟩
    have hηlift : p.IsHomLift f (P.ι.map η.hom) :=
      (isHomLift_restrict_iff p P f η.hom).1 (hηeq ▸ IsHomLift.map (p := restrict p P) η.hom)
    have hηfac' : η.hom ≫ φ.hom = ψ.hom := congrArg InducedWideCategory.Hom.hom hηfac
    exact WideSubcategory.hom_ext _ (P.ι.map_injective (hχuniq (P.ι.map η.hom) ⟨hηlift, by
      simpa only [Functor.map_comp] using congrArg P.ι.map hηfac'⟩))

end CategoryTheory.Functor

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Finite-type algebraic spaces over varying schemes in the big fppf site of `S`, with only the
cartesian squares as morphisms: the objects are those of `AlgebraicGeometry.FiniteTypeSpaces`,
and the morphisms are the strongly cartesian morphisms of the comma category, which are those
whose square of structure morphisms is cartesian. -/
abbrev CartesianFiniteTypeSpaces :=
  WideSubcategory
    ((stronglyCartesianOver (spacesProjection B S hS)).inverseImage
      (isFiniteTypeSpace B S hS).ι)

/-- The projection taking a finite-type family of algebraic spaces to its base scheme. -/
abbrev cartesianFiniteTypeProjection :
    CartesianFiniteTypeSpaces B S hS ⥤ BigFppfOver B S hS :=
  wideSubcategoryInclusion _ ⋙ finiteTypeSpacesProjection B S hS

/-- Finite-type algebraic spaces over varying base schemes, with cartesian squares as morphisms,
form a category fibred in groupoids over the big fppf site of `S`. -/
@[stacks 0D1E "finite-type families"]
theorem cartesianFiniteTypeProjection_isFiberedInGroupoids :
    (cartesianFiniteTypeProjection B S hS).IsFiberedInGroupoids :=
  have := spacesProjection_isFibered B S hS
  Functor.isFiberedInGroupoids_wideSubcategory (spacesProjection B S hS)
    (isFiniteTypeSpace B S hS) (closedUnderStronglyCartesian_isFiniteTypeSpace B S hS)

/-- An algebraic space over a scheme in the big fppf site of `S` whose structure morphism is of
finite presentation, flat and proper. -/
abbrev isProperFlatSpace : ObjectProperty
    (Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
  fun X ↦ Space.IsFinitePresentation B S hS X.hom ∧ Space.IsFlat B S hS X.hom ∧
    Space.IsProper B S hS X.hom

/-- A strongly cartesian morphism whose target is of finite presentation, flat and proper over
its base has source of finite presentation, flat and proper over its base. -/
theorem closedUnderStronglyCartesian_isProperFlatSpace :
    Functor.ClosedUnderStronglyCartesian (spacesProjection B S hS) (isProperFlatSpace B S hS) := by
  intro V U A C g m hm hC
  have hV : A.right = V := IsHomLift.domain_eq (spacesProjection B S hS) g m
  have hU : C.right = U := IsHomLift.codomain_eq (spacesProjection B S hS) g m
  subst hV hU
  have hg : m.right = g := by
    simpa using IsHomLift.fac' (spacesProjection B S hS) g m
  have hsq := isPullback_commaHomAsSpaceMap_of_isStronglyCartesian B S hS m (hg ▸ hm)
  exact Functor.isoOverId_of_prop (P := isProperFlatSpace B S hS)
    ⟨(Space.isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback hsq hC.1,
      (Space.isFlat_isStableUnderBaseChange B S hS).of_isPullback hsq hC.2.1,
      (Space.isProper_isStableUnderBaseChange B S hS).of_isPullback hsq hC.2.2⟩

/-- Finitely presented, flat and proper algebraic spaces over varying schemes in the big fppf site
of `S`, with only the cartesian squares as morphisms. -/
abbrev CartesianProperFlatSpaces :=
  WideSubcategory
    ((stronglyCartesianOver (spacesProjection B S hS)).inverseImage
      (isProperFlatSpace B S hS).ι)

/-- The projection taking a finitely presented, flat and proper family of algebraic spaces to its
base scheme. -/
abbrev cartesianProperFlatProjection :
    CartesianProperFlatSpaces B S hS ⥤ BigFppfOver B S hS :=
  wideSubcategoryInclusion _ ⋙ (isProperFlatSpace B S hS).ι ⋙ spacesProjection B S hS

/-- Algebraic spaces whose structure morphism is of finite presentation, flat and proper over a
varying base scheme, with cartesian squares as morphisms, form a category fibred in groupoids over
the big fppf site of `S`. -/
@[stacks 0D1E "finitely presented, flat and proper families"]
theorem cartesianProperFlatProjection_isFiberedInGroupoids :
    (cartesianProperFlatProjection B S hS).IsFiberedInGroupoids :=
  have := spacesProjection_isFibered B S hS
  Functor.isFiberedInGroupoids_wideSubcategory (spacesProjection B S hS)
    (isProperFlatSpace B S hS) (closedUnderStronglyCartesian_isProperFlatSpace B S hS)

end AlgebraicGeometry

end
