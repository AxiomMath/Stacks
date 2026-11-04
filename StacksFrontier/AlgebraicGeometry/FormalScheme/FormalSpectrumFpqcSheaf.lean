module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsAffine
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsFpqcReduction
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The functor of points of a formal spectrum is an fpqc sheaf

Let `A` be an admissible topological ring. This file proves the gluing clause of Stacks 0AI2 for
the formal spectrum `Spf A`: its functor of points is a sheaf for the fpqc topology on the
category of all schemes. That is the assertion Stacks 0AIE appeals to when it says that the
colimit formula `h_{Spf A} = colim h_{Spec (A/I)}` may be checked on affine schemes, both sides
being sheaves.

The obstruction described in
`StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsFpqcReduction` — that a morphism
`Spec S ⟶ 𝔛` into a general formal scheme need not factor through a single affine formal chart —
does not arise here, because `Spf A` *is* a single chart: by
`AlgebraicGeometry.exists_factor_spfQuotientPoint` a point of `Spf A` over an affine scheme
factors through one of the quotients `Spec (A/I)`. Descent is then descent for the *scheme*
`Spec (A/I)`, which the fpqc topology being subcanonical already supplies.

The bookkeeping is: a compatible one-element family of points of `Spf A` over `Spec S` factors
through some `Spec (A/I)`; the factoring morphism of schemes is itself compatible, because
`Spec (A/I) ⟶ Spf A` is injective on points over every test scheme
(`AlgebraicGeometry.eq_of_comp_spfQuotientPoint_eq`); it therefore descends to `Spec R`; and the
descended morphism, composed with `Spec (A/I) ⟶ Spf A`, is the required amalgamation. Uniqueness
is the separatedness clause of Stacks 0AI2, already proved.

## Main results

* `AlgebraicGeometry.hom_toSpec_ext`: a morphism into an affine scheme is determined by the
  homomorphism it induces on global sections.
* `AlgebraicGeometry.eq_of_comp_spfQuotientPoint_eq`: the morphism `Spec (A/I) ⟶ Spf A` of
  Stacks 0AHY is injective on points over every scheme.
* `AlgebraicGeometry.isSheafFor_singleton_formalSchemePoints_spfFormalScheme`: the sheaf
  condition for the one-element family spanned by a faithfully flat morphism of affine schemes.
* `AlgebraicGeometry.isSheaf_fpqcTopology_formalSchemePoints_spfFormalScheme`: **Stacks 0AI2**,
  the gluing clause included, for a formal spectrum; this is the sheaf property of the target of
  the comparison map of **Stacks 0AIE**.
* `AlgebraicGeometry.isSheaf_fpqcTopology_formalSchemePoints_of_isoSpf`: the same for a formal
  scheme isomorphic to a formal spectrum, that is for an affine formal scheme.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ)
* [Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
* [Stacks Project, Tag 0AIE](https://stacks.math.columbia.edu/tag/0AIE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

open TopologicalRing

/-- **A morphism into an affine scheme is determined by the homomorphism it induces on global
sections.** Both morphisms factor as the canonical `T ⟶ Spec Γ(T, 𝒪_T)` followed by the spectrum
of the induced homomorphism, by naturality of that canonical morphism. -/
@[ega "I 10.4.6" "partial"]
theorem hom_toSpec_ext {T : Scheme.{u}} {R : CommRingCat.{u}} {c d : T ⟶ Spec R}
    (hcd : Scheme.Hom.appTop c = Scheme.Hom.appTop d) : c = d := by
  have key (e : T ⟶ Spec R) :
      e = (T.toSpecΓ ≫ Spec.map (Scheme.Hom.appTop e)) ≫ Spec.map (Scheme.ΓSpecIso R).inv := by
    rw [← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [key c, key d, hcd]

section

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **The morphism `Spec (A/I) ⟶ Spf A` is injective on points over every scheme.** Two morphisms
`T ⟶ Spec (A/I)` inducing the same point of `Spf A` are equal: they induce the same homomorphism
`A → Γ(T, 𝒪_T)`, that homomorphism is the quotient map `A → A/I` followed by the one they induce,
and `A → A/I` is surjective, so the two homomorphisms `A/I → Γ(T, 𝒪_T)` agree; a morphism into an
affine scheme is determined by that datum. -/
theorem eq_of_comp_spfQuotientPoint_eq (hA : IsPreAdmissible A) (I : IdealsOfDefinition A)
    {T : Scheme.{u}} {c d : T ⟶ Spec (spfQuotient A I)}
    (h : (schemeToFormalScheme.map c).hom ≫ spfQuotientPoint A hA I
      = (schemeToFormalScheme.map d).hom ≫ spfQuotientPoint A hA I) : c = d := by
  have hepi : Epi (spfGammaComponentHom A I) := by
    rw [spfGammaComponentHom, spfGammaComponentHomOn]
    have : Epi (CommRingCat.ofHom (Ideal.Quotient.mk I.1)) :=
      ConcreteCategory.epi_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  refine hom_toSpec_ext ((cancel_epi (spfGammaComponentHom A I)).1 ?_)
  rw [← spfPointGammaHom_comp_spfQuotientPoint A hA I c,
    ← spfPointGammaHom_comp_spfQuotientPoint A hA I d]
  exact congrArg (spfPointGammaHom A hA) h

end

section

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]

/-- **The sheaf condition for the functor of points of a formal spectrum, for a one-element fpqc
covering of an affine scheme.** A point of `Spf A` over `Spec S` whose two pullbacks along a
faithfully flat `Spec S ⟶ Spec R` agree descends uniquely to a point over `Spec R`.

The point factors through a quotient `Spec (A/I)` by
`AlgebraicGeometry.exists_factor_spfQuotientPoint`, `Spec S` being affine. The factoring morphism
of schemes inherits the compatibility, because `Spec (A/I) ⟶ Spf A` is injective on points; it
descends because the functor of points of the *scheme* `Spec (A/I)` is an fpqc sheaf, the fpqc
topology being subcanonical; and the descended morphism composed with `Spec (A/I) ⟶ Spf A` is the
amalgamation. Uniqueness is
`AlgebraicGeometry.formalSchemeHom_ext_of_flat_of_jointlySurjective` for the one-element
family. -/
theorem existsUnique_comp_eq_of_forall_comp_eq (hA : IsAdmissible A)
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (hflat : Flat (Spec.map φ))
    (hsurj : Surjective (Spec.map φ))
    (x : schemeToFormalScheme.obj (Spec S) ⟶ spfFormalScheme A hA)
    (hx : ∀ {Z : Scheme.{u}} (q₁ q₂ : Z ⟶ Spec S), q₁ ≫ Spec.map φ = q₂ ≫ Spec.map φ →
      schemeToFormalScheme.map q₁ ≫ x = schemeToFormalScheme.map q₂ ≫ x) :
    ∃! y : schemeToFormalScheme.obj (Spec R) ⟶ spfFormalScheme A hA,
      schemeToFormalScheme.map (Spec.map φ) ≫ y = x := by
  have := hflat
  have := hsurj
  obtain ⟨I, a, ha⟩ := exists_factor_spfQuotientPoint A hA (Spec S) x.hom
  set ι : schemeToFormalScheme.obj (Spec (spfQuotient A I)) ⟶ spfFormalScheme A hA :=
    ObjectProperty.homMk (spfQuotientPoint A hA.1 I) with hι
  have hax : schemeToFormalScheme.map a ≫ ι = x := InducedCategory.hom_ext ha
  -- The factoring morphism of schemes is compatible, `Spec (A/I) ⟶ Spf A` being injective
  -- on points.
  have hcompat : ∀ {Z : Scheme.{u}} (q₁ q₂ : Z ⟶ Spec S),
      q₁ ≫ Spec.map φ = q₂ ≫ Spec.map φ →
      schemeToFormalScheme.map q₁ ≫ schemeToFormalScheme.map a
        = schemeToFormalScheme.map q₂ ≫ schemeToFormalScheme.map a := by
    intro Z q₁ q₂ hq
    have h := hx q₁ q₂ hq
    rw [← hax, ← Category.assoc, ← Category.assoc, ← schemeToFormalScheme.map_comp,
      ← schemeToFormalScheme.map_comp] at h
    have hscheme : q₁ ≫ a = q₂ ≫ a :=
      eq_of_comp_spfQuotientPoint_eq A hA.1 I
        (congrArg (fun m : schemeToFormalScheme.obj Z ⟶ spfFormalScheme A hA => m.hom) h)
    rw [← schemeToFormalScheme.map_comp, ← schemeToFormalScheme.map_comp, hscheme]
  -- The factoring morphism descends, the functor of points of a scheme being an fpqc sheaf.
  obtain ⟨t, ht⟩ : ∃ t : schemeToFormalScheme.obj (Spec R) ⟶
      schemeToFormalScheme.obj (Spec (spfQuotient A I)),
      schemeToFormalScheme.map (Spec.map φ) ≫ t = schemeToFormalScheme.map a := by
    obtain ⟨t, ht, -⟩ := Presieve.isSheafFor_singleton.1
      ((Presieve.isSheafFor_iff_generate (Presieve.singleton (Spec.map φ))).2
        (isSheaf_fpqcTopology_formalSchemePoints_schemeToFormalScheme
          (Spec (spfQuotient A I)) _
          (Scheme.Hom.generate_singleton_mem_propQCTopology (P := @Flat) (Spec.map φ) hflat)))
      (schemeToFormalScheme.map a) (fun {_} q₁ q₂ hq => hcompat q₁ q₂ hq)
    exact ⟨t, ht⟩
  refine ⟨t ≫ ι, ?_, fun z hz => ?_⟩
  · show schemeToFormalScheme.map (Spec.map φ) ≫ t ≫ ι = x
    rw [← Category.assoc, ht, hax]
  refine formalSchemeHom_ext_of_flat_of_jointlySurjective
    (V := fun _ : Unit => Spec S) (fun _ => Spec.map φ) (fun _ => hflat)
    (fun y => ⟨⟨⟩, hsurj.surj y⟩) fun _ => ?_
  rw [hz, ← Category.assoc, ht, hax]

/-- **The sheaf condition for the functor of points of a formal spectrum, for a one-element fpqc
covering of an affine scheme**, in the form the reduction of Stacks 0AI2 asks for. It is
`AlgebraicGeometry.existsUnique_comp_eq_of_forall_comp_eq` read through
`CategoryTheory.Presieve.isSheafFor_singleton`. -/
theorem isSheafFor_singleton_formalSchemePoints_spfFormalScheme (hA : IsAdmissible A)
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (hflat : Flat (Spec.map φ))
    (hsurj : Surjective (Spec.map φ)) :
    Presieve.IsSheafFor (formalSchemePoints (spfFormalScheme A hA))
      (Presieve.singleton (Spec.map φ)) :=
  Presieve.isSheafFor_singleton.2 fun x hx =>
    existsUnique_comp_eq_of_forall_comp_eq A hA φ hflat hsurj x fun q₁ q₂ hq => hx q₁ q₂ hq

end

end AlgebraicGeometry

end
