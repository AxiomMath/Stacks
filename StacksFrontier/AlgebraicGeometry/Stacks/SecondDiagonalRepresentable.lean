module

public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondRelativeDiagonalInertia
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.SecondDiagonal
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.FibredOneMorphism

/-!
# The second diagonal, the relative inertia and representability (Stacks 04YY)

Let `S` be a scheme contained in a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over `S`. **Stacks 04YY** says that the following are equivalent:

1. `f` is representable by algebraic spaces;
2. the second diagonal `Δ_{f, 2} = Δ_{Δ_f}` is an isomorphism;
3. the relative inertia group stack `I_{𝒳/𝒴}` is trivial over `𝒳`;
4. for every scheme `T` and every `x : T ⟶ 𝒳` the kernel of
   `Isom_𝒳(x, x) ⟶ Isom_𝒴(f ∘ x, f ∘ x)` is trivial.

Conditions (2), (3) and (4) are proved equivalent here, and the implication (1) ⟹ (2) is proved;
the converse (2) ⟹ (1) is
`isRepresentableByAlgebraicSpaces_of_isEquivalence_secondRelativeDiagonal` (namespace
`AlgebraicGeometry.Stack.AlgebraicStacks`), in
`StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentableUnconditional`.

The route is the source's. Condition (2) is fully faithfulness of `Δ_f` by Stacks 04Z7, hence —
since the relative diagonal is always faithful and is full exactly when `f` is faithful —
faithfulness of `f`. Condition (3) is condition (2) because `Δ_{f, 2}` *is* the neutral section
of `I_{𝒳/𝒴}`. Condition (4) is faithfulness of `f` read fibrewise: an endomorphism of an object
of `𝒳` killed by `f` lies over an identity, hence is an automorphism, and triviality of those
kernels is exactly injectivity of `f` on parallel morphisms.

## Main results

* `CategoryTheory.Functor.IsFiberedInGroupoids.faithful_iff_autKernel_trivial`: a 1-morphism of
  categories fibred in groupoids is faithful exactly when the kernel of every induced map on
  automorphism groups is trivial. This is **conditions (1) and (4) of Stacks 04YY** stripped of
  all geometry.
* `CategoryTheory.TwoFibreProductOver.isEquivalence_diagonal_diagonal_iff_faithful`: the second
  diagonal of a 1-morphism of categories fibred in groupoids is an equivalence exactly when the
  1-morphism is faithful.
* `AlgebraicGeometry.Stack.AlgebraicStacks.secondRelativeDiagonal_tfae`: **Stacks 04YY**, the
  equivalence of conditions (2), (3) and (4), for a 1-morphism of algebraic stacks, with the
  three pairwise equivalences also available separately.
* `AlgebraicStacks.isEquivalence_secondRelativeDiagonal_of_isRepresentableByAlgebraicSpaces`,
  in the namespace `AlgebraicGeometry.Stack`: **Stacks 04YY**, the implication (1) ⟹ (2).

## Implementation notes

An isomorphism of the 2-category of algebraic stacks is a 1-morphism whose underlying functor is
an equivalence of categories, which is how conditions (2) and (3) are stated; triviality of the
group stack `I_{𝒳/𝒴}` over `𝒳` is stated as its neutral section `e : 𝒳 ⟶ I_{𝒳/𝒴}` being such an
isomorphism, the "a group stack is trivial if and only if its identity section is an isomorphism"
of the source. Condition (4) is stated as triviality of the kernel on endomorphisms of an object
of the total category of `𝒳`: an object of `𝒳` over a scheme `T` *is* a 1-morphism `T ⟶ 𝒳`, the
sections of `Isom_𝒳(x, x)` over `T' ⟶ T` are the automorphisms of the pullback of `x`, and the
quantifier over all objects of `𝒳` covers all those pullbacks, so no sheaf-theoretic kernel need
be formed. The endomorphism is not required to be invertible: `f`-triviality forces it to lie
over an identity, and the fibres of `𝒳` are groupoids, so invertibility is automatic.

The equivalence (2) ⟺ (3) is the existing identification
`CategoryTheory.TwoFibreProductOver.isEquivalence_diagonal_diagonal_iff`, which needs no
hypothesis at all beyond `f` being a 1-morphism over the site.

The implication (2) ⟹ (1) is proved in
`StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentableUnconditional`: the source deduces it
from Stacks 04Y5, faithfulness ⟹ representability by algebraic spaces, whose proof needs the
bootstrap theorem Stacks 04S6, an import this file does not take.

The universes are those of the 2-category of algebraic stacks — morphism universe `u`, object
universe `u + 1` — because `AlgebraicGeometry.Stack.secondRelativeDiagonal` and
`AlgebraicGeometry.Stack.relativeInertiaNeutralSection` are stated there, for the reason recorded
in `StacksFrontier.AlgebraicGeometry.Stacks.SecondRelativeDiagonalInertia`.

## References

* [Stacks Project, Tag 04YY](https://stacks.math.columbia.edu/tag/04YY)
* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 04Z7](https://stacks.math.columbia.edu/tag/04Z7)
* [Stacks Project, Tag 034I](https://stacks.math.columbia.edu/tag/034I)
* [Stacks Project, Tag 07WG](https://stacks.math.columbia.edu/tag/07WG)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]
variable {𝒮' : Type u₃} [Category.{v₃} 𝒮']
variable {p𝒮 : 𝒮 ⥤ 𝒞} {p𝒮' : 𝒮' ⥤ 𝒞} {G : 𝒮 ⥤ 𝒮'}

/-- **The substantive half of conditions (1) and (4) of Stacks 04YY.** Let `p𝒮` and `p𝒮'` be
categories fibred in groupoids over `𝒞` and let `G` be a 1-morphism over `𝒞` such that every
endomorphism of an object of `𝒮` killed by `G` is an identity. Then `G` is faithful.

Two parallel morphisms `φ₁`, `φ₂ : x ⟶ y` with `G φ₁ = G φ₂` lie over a common morphism `f` of
`𝒞`; as `φ₂` is strongly cartesian over `f`, there is a unique `α : x ⟶ x` over `𝟙` with
`α ≫ φ₂ = φ₁`. Then `G α ≫ G φ₂ = 𝟙 ≫ G φ₂`, and `G φ₂` is strongly cartesian too, so
`G α = 𝟙` and the hypothesis gives `α = 𝟙`. -/
theorem IsFiberedInGroupoids.faithful_of_autKernel_trivial (hp : p𝒮.IsFiberedInGroupoids)
    (hp' : p𝒮'.IsFiberedInGroupoids) (hG : G ⋙ p𝒮' = p𝒮)
    (h : ∀ (x : 𝒮) (a : x ⟶ x), G.map a = 𝟙 (G.obj x) → a = 𝟙 x) : G.Faithful where
  map_injective {x y} φ₁ φ₂ hφ := by
    have hbase : p𝒮.map φ₁ = p𝒮.map φ₂ := by
      have h₁ := Functor.congr_hom hG φ₁
      have h₂ := Functor.congr_hom hG φ₂
      simp only [Functor.comp_map, hφ] at h₁ h₂
      have h₃ := h₁.symm.trans h₂
      simp only [cancel_epi, cancel_mono] at h₃
      exact h₃
    have : p𝒮.IsHomLift (p𝒮.map φ₂) φ₂ := IsHomLift.map (p := p𝒮) φ₂
    have : p𝒮.IsHomLift (p𝒮.map φ₂) φ₁ := hbase ▸ IsHomLift.map (p := p𝒮) φ₁
    have : p𝒮.IsStronglyCartesian (p𝒮.map φ₂) φ₂ := hp.isStronglyCartesian_homLift _ φ₂
    have hid : p𝒮.map φ₂ = 𝟙 (p𝒮.obj x) ≫ p𝒮.map φ₂ := (Category.id_comp _).symm
    obtain ⟨α, hαfac, hαlift⟩ :
        ∃ α : x ⟶ x, α ≫ φ₂ = φ₁ ∧ p𝒮'.IsHomLift (𝟙 (p𝒮.obj x)) (G.map α) := by
      refine ⟨Functor.IsStronglyCartesian.map p𝒮 (p𝒮.map φ₂) φ₂ hid φ₁,
        Functor.IsStronglyCartesian.fac p𝒮 (p𝒮.map φ₂) φ₂ hid φ₁, ?_⟩
      have := Functor.IsStronglyCartesian.map_isHomLift p𝒮 (p𝒮.map φ₂) φ₂ hid φ₁
      exact Functor.isHomLift_map_of_comp_eq hG _ _
    have : p𝒮'.IsHomLift (p𝒮.map φ₂) (G.map φ₂) := Functor.isHomLift_map_of_comp_eq hG _ φ₂
    have : p𝒮'.IsStronglyCartesian (p𝒮.map φ₂) (G.map φ₂) :=
      hp'.isStronglyCartesian_homLift _ _
    have := hαlift
    have : p𝒮'.IsHomLift (𝟙 (p𝒮.obj x)) (𝟙 (G.obj x)) := IsHomLift.id (Functor.congr_obj hG x)
    have hGα : G.map α = 𝟙 (G.obj x) :=
      Functor.IsCartesian.ext p𝒮' (p𝒮.map φ₂) (G.map φ₂) (G.map α) (𝟙 (G.obj x))
        (by rw [← G.map_comp, hαfac, hφ, Category.id_comp])
    rw [← hαfac, h x α hGα, Category.id_comp]

/-- **Conditions (1) and (4) of Stacks 04YY, without geometry.** A 1-morphism `G` of categories
fibred in groupoids over `𝒞` is faithful exactly when, for every object `x` of the source, every
endomorphism of `x` that `G` sends to an identity is itself an identity — that is, exactly when
the kernel of each induced map on automorphism groups is trivial. -/
@[sga "4 I 6.5.1" "more general"]
theorem IsFiberedInGroupoids.faithful_iff_autKernel_trivial (hp : p𝒮.IsFiberedInGroupoids)
    (hp' : p𝒮'.IsFiberedInGroupoids) (hG : G ⋙ p𝒮' = p𝒮) :
    G.Faithful ↔ ∀ (x : 𝒮) (a : x ⟶ x), G.map a = 𝟙 (G.obj x) → a = 𝟙 x :=
  ⟨fun hfaith x a ha => hfaith.map_injective (by simpa using ha),
    IsFiberedInGroupoids.faithful_of_autKernel_trivial hp hp' hG⟩

end CategoryTheory.Functor

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]
variable {𝒮' : Type u₃} [Category.{v₃} 𝒮']
variable {p𝒮 : 𝒮 ⥤ 𝒞} {p𝒮' : 𝒮' ⥤ 𝒞} {G : 𝒮 ⥤ 𝒮'}

/-- **Conditions (1) and (2) of Stacks 04YY, without geometry.** For a 1-morphism `G` of
categories fibred in groupoids over `𝒞`, the second diagonal
`Δ_{Δ_G} : 𝒮 ⥤ 𝒮 ×_{Δ_G, 𝒮 ×_{𝒮'} 𝒮, Δ_G} 𝒮` is an equivalence exactly when `G` is faithful.

By Stacks 04Z7 the second diagonal is an equivalence exactly when `Δ_G` is fully faithful; `Δ_G`
is faithful with no hypothesis, and it is full exactly when `G` is faithful. -/
theorem isEquivalence_diagonal_diagonal_iff_faithful (h𝒮 : p𝒮.IsFiberedInGroupoids)
    (h𝒮' : p𝒮'.IsFiberedInGroupoids) (hG : G ⋙ p𝒮' = p𝒮) :
    (diagonal (diagonal_comp_structureFunctor hG)).IsEquivalence ↔ G.Faithful := by
  have hprod : (structureFunctor p𝒮 p𝒮 p𝒮' G G).IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids p𝒮 p𝒮 p𝒮' G G h𝒮 h𝒮 h𝒮' hG hG
  rw [← full_and_faithful_iff_isEquivalence_diagonal h𝒮 hprod
    (diagonal_comp_structureFunctor hG)]
  refine ⟨fun h => faithful_of_full_diagonal hG h.1, fun h => ?_⟩
  have := h
  exact ⟨full_diagonal hG, faithful_diagonal hG⟩

end CategoryTheory.TwoFibreProductOver

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section FibredInGroupoids

variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- **Conditions (1) and (2) of Stacks 04YY for a 1-morphism of categories fibred in groupoids.**
The second relative diagonal `Δ_{f, 2}` of `f : 𝒳 ⟶ 𝒴` is an isomorphism exactly when the functor
underlying `f` is faithful. No algebraicity is used. -/
theorem isEquivalence_secondRelativeDiagonal_iff_faithful (f : 𝒳 ⟶ 𝒴) :
    Functor.IsEquivalence (secondRelativeDiagonal B S hS f).hom.toFunctor ↔
      (CatFiberedInGroupoids.homFunctor f).Faithful :=
  TwoFibreProductOver.isEquivalence_diagonal_diagonal_iff_faithful
    𝒳.isFiberedInGroupoids 𝒴.isFiberedInGroupoids f.hom.w

/-- **Conditions (2) and (3) of Stacks 04YY for a 1-morphism of categories fibred in groupoids.**
The second relative diagonal `Δ_{f, 2}` is an isomorphism exactly when the neutral section
`e : 𝒳 ⟶ I_{𝒳/𝒴}` of the relative inertia is, since the two are identified by the comparison
equivalence of Stacks 07WG. -/
theorem isEquivalence_secondRelativeDiagonal_iff_neutralSection (f : 𝒳 ⟶ 𝒴) :
    Functor.IsEquivalence (secondRelativeDiagonal B S hS f).hom.toFunctor ↔
      Functor.IsEquivalence (relativeInertiaNeutralSection B S hS f).hom.toFunctor :=
  TwoFibreProductOver.isEquivalence_diagonal_diagonal_iff f.hom.w

/-- **Conditions (3) and (4) of Stacks 04YY for a 1-morphism of categories fibred in groupoids.**
The neutral section of the relative inertia is an isomorphism exactly when, for every object `x`
of `𝒳`, the kernel of the induced map on automorphisms of `x` is trivial. -/
theorem isEquivalence_neutralSection_iff_autKernel_trivial (f : 𝒳 ⟶ 𝒴) :
    Functor.IsEquivalence (relativeInertiaNeutralSection B S hS f).hom.toFunctor ↔
      ∀ (x : 𝒳.val.obj) (a : x ⟶ x),
        (CatFiberedInGroupoids.homFunctor f).map a = 𝟙 _ → a = 𝟙 x :=
  (isEquivalence_secondRelativeDiagonal_iff_neutralSection B S hS f).symm.trans
    ((isEquivalence_secondRelativeDiagonal_iff_faithful B S hS f).trans
      (Functor.IsFiberedInGroupoids.faithful_iff_autKernel_trivial 𝒳.isFiberedInGroupoids
        𝒴.isFiberedInGroupoids f.hom.w))

/-- **The implication (1) ⟹ (2) of Stacks 04YY for a 1-morphism of categories fibred in
groupoids.** A 1-morphism representable by algebraic spaces has faithful underlying functor by
Stacks 04Y5, hence has isomorphic second relative diagonal. -/
theorem isEquivalence_secondRelativeDiagonal_of_isRepresentableByAlgebraicSpaces (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom) :
    Functor.IsEquivalence (secondRelativeDiagonal B S hS f).hom.toFunctor :=
  (isEquivalence_secondRelativeDiagonal_iff_faithful B S hS f).mpr
    (faithful_homFunctor_of_isRepresentableByAlgebraicSpaces B S hS f hf)

end FibredInGroupoids

namespace AlgebraicStacks

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 04YY, the equivalence of parts (2) and (3).** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks over `S`, the second diagonal `Δ_{f, 2}` is an isomorphism exactly when the
relative inertia group stack `I_{𝒳/𝒴}` is trivial over `𝒳`, that is, exactly when its neutral
section `e : 𝒳 ⟶ I_{𝒳/𝒴}` is an isomorphism. -/
@[stacks 04YY "the equivalence of parts (2) and (3)"]
theorem isEquivalence_secondRelativeDiagonal_iff_relativeInertiaTrivial (f : 𝒳 ⟶ 𝒴) :
    Functor.IsEquivalence (secondRelativeDiagonal B S hS f.hom).hom.toFunctor ↔
      Functor.IsEquivalence
        (relativeInertiaStackNeutralSection B S hS f).hom.hom.toFunctor :=
  isEquivalence_secondRelativeDiagonal_iff_neutralSection B S hS f.hom

/-- **Stacks 04YY, the equivalence of parts (3) and (4).** The relative inertia `I_{𝒳/𝒴}` of a
1-morphism of algebraic stacks is trivial over `𝒳` exactly when, for every scheme `T` and every
`x : T ⟶ 𝒳`, the kernel of `Isom_𝒳(x, x) ⟶ Isom_𝒴(f ∘ x, f ∘ x)` is trivial — stated as: every
endomorphism of an object of `𝒳` which `f` sends to an identity is an identity. -/
@[stacks 04YY "the equivalence of parts (3) and (4)"]
theorem relativeInertiaTrivial_iff_isomKernel_trivial (f : 𝒳 ⟶ 𝒴) :
    Functor.IsEquivalence
        (relativeInertiaStackNeutralSection B S hS f).hom.hom.toFunctor ↔
      ∀ (x : 𝒳.val.val.obj) (a : x ⟶ x),
        (CatFiberedInGroupoids.homFunctor f.hom).map a = 𝟙 _ → a = 𝟙 x :=
  isEquivalence_neutralSection_iff_autKernel_trivial B S hS f.hom

/-- **Stacks 04YY, the equivalence of parts (2), (3) and (4).** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks over `S` the following are equivalent: the second diagonal `Δ_{f, 2}` is an
isomorphism; the relative inertia `I_{𝒳/𝒴}` is trivial over `𝒳`; the kernel of the map on
`Isom` sheaves attached to any object of `𝒳` over a scheme is trivial. -/
@[stacks 04YY "the equivalence of parts (2), (3) and (4)"]
theorem secondRelativeDiagonal_tfae (f : 𝒳 ⟶ 𝒴) :
    List.TFAE
      [Functor.IsEquivalence (secondRelativeDiagonal B S hS f.hom).hom.toFunctor,
        Functor.IsEquivalence
          (relativeInertiaStackNeutralSection B S hS f).hom.hom.toFunctor,
        ∀ (x : 𝒳.val.val.obj) (a : x ⟶ x),
          (CatFiberedInGroupoids.homFunctor f.hom).map a = 𝟙 _ → a = 𝟙 x] := by
  tfae_have 1 ↔ 2 :=
    isEquivalence_secondRelativeDiagonal_iff_relativeInertiaTrivial B S hS f
  tfae_have 2 ↔ 3 := relativeInertiaTrivial_iff_isomKernel_trivial B S hS f
  tfae_finish

/-- **Stacks 04YY, the implication (1) ⟹ (2).** If a 1-morphism of algebraic stacks over `S` is
representable by algebraic spaces then its second diagonal `Δ_{f, 2}` is an isomorphism.

By Stacks 04Y5 representability by algebraic spaces makes the underlying functor faithful, and by
Stacks 04Z7 that is exactly the second diagonal being an isomorphism. -/
@[stacks 04YY "the implication (1) ⟹ (2)"]
theorem isEquivalence_secondRelativeDiagonal_of_isRepresentableByAlgebraicSpaces (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    Functor.IsEquivalence (secondRelativeDiagonal B S hS f.hom).hom.toFunctor :=
  Stack.isEquivalence_secondRelativeDiagonal_of_isRepresentableByAlgebraicSpaces B S hS f.hom hf

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
