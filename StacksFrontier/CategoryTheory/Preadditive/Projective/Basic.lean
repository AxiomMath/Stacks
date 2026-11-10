module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import StacksCore.Tactic.StacksAttribute

/-!
# Projective objects of abelian categories

Stacks, Homological Algebra, Section 12.28, dual to Section 12.27. The definition of a projective
object (013B), coproducts of projectives (013D) and enough projectives (013E) are Mathlib's; their
tags are attached below. This file adds the characterisation of projective objects (013C) and
functorial projective surjections (013F).
-/

@[expose] public section

add_to_stacks 013B CategoryTheory.Projective
add_to_sga "4 IV 2.6" "partial" CategoryTheory.Projective
add_to_sga "4 IV 7.6" CategoryTheory.Projective
add_to_sga "6 I 1.2" CategoryTheory.Projective
add_to_stacks 013D CategoryTheory.Projective.instSigmaObj
add_to_stacks 013E CategoryTheory.EnoughProjectives
add_to_sga "4 II 6.9" CategoryTheory.EnoughProjectives

section

/-!
## Characterizations of projective objects

Let `𝒜` be an abelian category and let `P` be an object of `𝒜`. The Stacks lemma
states the equivalence of four conditions:

1. `P` is projective.
2. The additive Hom functor `Hom(P, -) : 𝒜 ⥤ AddCommGrpCat` is exact, i.e. sends
   every short exact sequence to a short exact sequence in `AddCommGrpCat`.
3. Every short exact sequence ending in `P` splits.
4. `Ext^1(P, A) = 0` for every `A`.

The headline `projective_iff_every_ses_splits` records the full equivalence
`(1) ↔ (3)`. The forward implications `(1) → (2)` and `(1) → (4)` are recorded
separately as `homFunctor_shortExact_of_projective` and `ext_one_eq_zero_of_projective`.

The reverse directions `(2) → (1)` and `(4) → (1)` are not included here.
-/

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The additive Hom functor `Hom(P, -) : 𝒜 ⥤ AddCommGrpCat`. -/
@[ega "0 8.1.11" "special case"]
abbrev homFunctor (P : 𝒜) : 𝒜 ⥤ AddCommGrpCat.{v} :=
  preadditiveCoyoneda.obj (op P)

/-- Statement (2): the additive Hom functor `Hom(P, -) : 𝒜 ⥤ AddCommGrpCat` is exact,
in the most literal sense: every short exact sequence in `𝒜` is sent to a short exact
sequence in `AddCommGrpCat`. -/
def HomFunctorExact (P : 𝒜) : Prop :=
  ∀ (S : ShortComplex 𝒜), S.ShortExact →
    ((homFunctor P).mapShortComplex.obj S).ShortExact

/-- Statement (3): every short exact sequence ending in `P` splits. We quantify
directly over morphisms `f : A ⟶ B`, `g : B ⟶ P` to avoid an awkward `S.X₃ = P`
hypothesis. -/
def EverySESEndingInPSplits (P : 𝒜) : Prop :=
  ∀ ⦃A B : 𝒜⦄ (f : A ⟶ B) (g : B ⟶ P) (zero : f ≫ g = 0),
    (ShortComplex.mk f g zero).ShortExact →
      Nonempty (ShortComplex.mk f g zero).Splitting

/-- If `P` is projective, then the additive Hom functor `Hom(P, -)` sends every
short exact sequence in `𝒜` to a short exact sequence in `AddCommGrpCat`. -/
lemma homFunctorExact_of_projective {P : 𝒜} (hP : Projective P) :
    HomFunctorExact P := by
  intro S hS
  have := hS.mono_f
  have := hS.epi_g
  have hmono : Mono ((homFunctor P).mapShortComplex.obj S).f := by
    change Mono ((homFunctor P).map S.f); infer_instance
  have hepi : Epi ((homFunctor P).mapShortComplex.obj S).g := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro h
    exact ⟨hP.factorThru h S.g, hP.factorThru_comp h S.g⟩
  have hexact : ((homFunctor P).mapShortComplex.obj S).Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro h hh
    exact ⟨hS.exact.lift h hh, hS.exact.lift_f h hh⟩
  exact ShortComplex.ShortExact.mk hexact

/-- `(1) → (2)`: if `P` is projective then `Hom(P, -)` is exact. -/
@[stacks 013C "(1)⇒(2)"]
theorem homFunctor_shortExact_of_projective {P : 𝒜} [hP : Projective P]
    (S : ShortComplex 𝒜) (hS : S.ShortExact) :
    ((homFunctor P).mapShortComplex.obj S).ShortExact :=
  homFunctorExact_of_projective hP S hS

/-- If `P` is projective, then every short exact sequence ending in `P` splits. -/
@[sga "3 VIIB 1.4.3" "more general", sga "6 V 2.2.1" "special case"]
lemma everySESEndingInPSplits_of_projective {P : 𝒜} (hP : Projective P) :
    EverySESEndingInPSplits P := by
  intro A B f g zero hS
  have : Mono f := hS.mono_f
  have : Epi g := hS.epi_g
  have : Projective P := hP
  let s : P ⟶ B := Projective.factorThru (𝟙 P) g
  have hsg : s ≫ g = 𝟙 P := Projective.factorThru_comp (𝟙 P) g
  have hφg : (𝟙 B - g ≫ s) ≫ g = 0 := by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hsg, Category.comp_id,
      sub_self]
  obtain ⟨r, hrf⟩ : { r : B ⟶ A // r ≫ f = 𝟙 B - g ≫ s } :=
    KernelFork.IsLimit.lift' hS.fIsKernel (𝟙 B - g ≫ s) hφg
  have hfr : f ≫ r = 𝟙 A := by
    apply (cancel_mono f).mp
    rw [Category.assoc, hrf, Preadditive.comp_sub, Category.comp_id, ← Category.assoc, zero,
      Limits.zero_comp, sub_zero, Category.id_comp]
  have hid : r ≫ f + g ≫ s = 𝟙 B := by
    rw [hrf, sub_add_cancel]
  exact ⟨ShortComplex.Splitting.mk r s hfr hsg hid⟩

/-- If every short exact sequence ending in `P` splits, then `P` is projective. -/
@[sga "6 I 1.3.1" "(ii) ⇒ (i), special case"]
lemma projective_of_everySESEndingInPSplits {P : 𝒜}
    (h : EverySESEndingInPSplits P) : Projective P := by
  refine ⟨fun {E X} f e _ => ?_⟩
  let q₁ : pullback e f ⟶ E := pullback.fst e f
  let q₂ : pullback e f ⟶ P := pullback.snd e f
  have : Epi q₂ := inferInstance
  let S : ShortComplex 𝒜 := ShortComplex.mk (kernel.ι q₂) q₂ (kernel.condition q₂)
  have hSes : S.ShortExact :=
    { exact := ShortComplex.exact_kernel q₂
      mono_f := equalizer.ι_mono
      epi_g := inferInstance }
  obtain ⟨sp⟩ := h (kernel.ι q₂) q₂ (kernel.condition q₂) hSes
  have hs : sp.s ≫ q₂ = 𝟙 P := sp.s_g
  have hpb : q₁ ≫ e = q₂ ≫ f := pullback.condition
  refine ⟨sp.s ≫ q₁, ?_⟩
  rw [Category.assoc, hpb, ← Category.assoc, hs, Category.id_comp]

/-- **Stacks 013C** (narrowed). `(1) ↔ (3)`: `P` is projective iff every short exact
sequence ending in `P` splits.

The Stacks lemma states the equivalence of four conditions; this records the
equivalence between projectivity and the splitting property. The forward
implications to the other two conditions are given by
`homFunctor_shortExact_of_projective` and `ext_one_eq_zero_of_projective`. -/
@[stacks 013C "(1)⇔(3)",
  sga "3 VIIB 1.4.3" "more general",
  sga "6 I 1.3.1" "(i) ⇔ (ii), special case",
  sga "6 V 2.2.1" "special case"]
theorem projective_iff_every_ses_splits (P : 𝒜) :
    Projective P ↔ EverySESEndingInPSplits P :=
  ⟨everySESEndingInPSplits_of_projective, projective_of_everySESEndingInPSplits⟩

/-- `(1) → (4)`: if `P` is projective then `Ext^1(P, A) = 0` for every `A`.
We use the standard `HasExt` instance from `HasExt.standard 𝒜`. -/
@[stacks 013C "(1)⇒(4)"]
theorem ext_one_eq_zero_of_projective {P : 𝒜} [Projective P] (A : 𝒜) :
    haveI : HasExt.{max u v} 𝒜 := HasExt.standard 𝒜
    ∀ (e : Abelian.Ext.{max u v} P A 1), e = 0 := by
  have : HasExt.{max u v} 𝒜 := HasExt.standard 𝒜
  intro e
  exact Abelian.Ext.eq_zero_of_projective e

end

section

/-!
## Stacks Tag 013F

Let `𝒜` be an abelian category. We say `𝒜` has *functorial projective
surjections* if there exists a functor `P : 𝒜 ⥤ Arrow 𝒜` such that

1. `t ∘ P = id_𝒜` (the target of `P A` is `A`),
2. for every object `A`, the morphism `P A` is surjective, and
3. for every object `A`, the source `s (P A)` is a projective object.

Here `Arrow 𝒜` is the category of arrows of `𝒜`, with `t = Arrow.rightFunc`
the target functor and `s = Arrow.leftFunc` the source functor.
-/

open CategoryTheory

set_option linter.unusedSectionVars false

variable (𝒜 : Type*) [Category 𝒜] [Abelian 𝒜]

/-- Condition (1): composing `P : 𝒜 ⥤ Arrow 𝒜` with the target functor
`t = Arrow.rightFunc : Arrow 𝒜 ⥤ 𝒜` gives back the identity functor on `𝒜`.
This is the Lean translation of `t ∘ P = id_𝒜`. -/
def IsFunctorialProjectiveSurjections₁ (P : 𝒜 ⥤ Arrow 𝒜) : Prop :=
  P ⋙ Arrow.rightFunc = 𝟭 𝒜

/-- Condition (2): for every object `A`, the underlying morphism
`(P.obj A).hom` is an epimorphism — i.e. a surjection in the abelian
category `𝒜`. -/
def IsFunctorialProjectiveSurjections₂ (P : 𝒜 ⥤ Arrow 𝒜) : Prop :=
  ∀ A : 𝒜, Epi (P.obj A).hom

/-- Condition (3): for every object `A`, the source `s (P A) = (P.obj A).left`
is a projective object of `𝒜`. -/
def IsFunctorialProjectiveSurjections₃ (P : 𝒜 ⥤ Arrow 𝒜) : Prop :=
  ∀ A : 𝒜, Projective (P.obj A).left

/-- An abelian category `𝒜` *has functorial projective surjections* if there
exists a functor `P : 𝒜 ⥤ Arrow 𝒜` satisfying conditions (1), (2) and (3)
above. -/
@[stacks 013F]
def HasFunctorialProjectiveSurjections : Prop :=
  ∃ P : 𝒜 ⥤ Arrow 𝒜,
    IsFunctorialProjectiveSurjections₁ 𝒜 P ∧
    IsFunctorialProjectiveSurjections₂ 𝒜 P ∧
    IsFunctorialProjectiveSurjections₃ 𝒜 P

/-- Sanity check: an abelian category with functorial projective surjections
has enough projectives. For each `A`, `(P.obj A).left` is projective, and
transporting `(P.obj A).hom` along `(P.obj A).right = A` (from condition (1))
yields the required epimorphism. -/
theorem enoughProjectives_of_hasFunctorialProjectiveSurjections
    (h : HasFunctorialProjectiveSurjections 𝒜) : EnoughProjectives 𝒜 := by
  obtain ⟨P, h1, h2, h3⟩ := h
  refine ⟨fun A => ?_⟩
  have eq_A : (P.obj A).right = A := Functor.congr_obj h1 A
  have := h2 A
  have := h3 A
  exact ⟨.mk _ ((P.obj A).hom ≫ eqToHom eq_A)⟩

end
