module

public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Resolution functors

This file collects the formalizations of [Stacks, Tag 013W], [Stacks, Tag 013X],
[Stacks, Tag 05TJ], [Stacks, Tag 014W], [Stacks, Tag 05TK], [Stacks, Tag 013V], [Stacks, Tag 05TN].

## References

* [Stacks, Tag 013W](https://stacks.math.columbia.edu/tag/013W)
* [Stacks, Tag 013X](https://stacks.math.columbia.edu/tag/013X)
* [Stacks, Tag 05TJ](https://stacks.math.columbia.edu/tag/05TJ)
* [Stacks, Tag 014W](https://stacks.math.columbia.edu/tag/014W)
* [Stacks, Tag 05TK](https://stacks.math.columbia.edu/tag/05TK)
* [Stacks, Tag 013V](https://stacks.math.columbia.edu/tag/013V)
* [Stacks, Tag 05TN](https://stacks.math.columbia.edu/tag/05TN)
-/

section

/-!
# Resolution functors

Let `C` be an abelian category and let `ℐ = InjectiveObject C` be its strictly full additive
subcategory of injective objects. A *resolution functor* for `C`
(`HomotopyCategory.Plus.ResolutionFunctor`) is the object-wise data of a bounded below complex of
injectives `(j K).X₁`, i.e. an object of `K⁺(ℐ)`, together with a quasi-isomorphism
`(j K).w : K ⟶ (j K).X₁` in `K⁺(C)`, for every object `K` of `K⁺(C)`. This file proves that such
a `j` exists when `C` has enough injectives, that it is unique up to unique isomorphism, that it
is automatically a functor and automatically exact, and that it descends to a quasi-inverse of the
canonical functor `K⁺(ℐ) ⥤ D⁺(C)`.

All four statements rest on one lifting property. The cochain complex underlying an object of
`K⁺(ℐ)` is strictly bounded below with injective terms, hence K-injective, hence right orthogonal
to the acyclic complexes; since the quasi-isomorphisms of `K⁺(C)` are the morphisms inverted by
the localization at the acyclic objects, and since the inclusion `ι : K⁺(ℐ) ⥤ K⁺(C)` is fully
faithful, composition with a quasi-isomorphism `u : K ⟶ ι X` is a *bijection*
```
(X ⟶ Y) ≃ (K ⟶ ι Y)
```
for all objects `X`, `Y` of `K⁺(ℐ)` (`precompEquiv`). At the level of cochain complexes and
homotopies this is the conjunction of the existence [Stacks, Tag 013P] and the uniqueness
[Stacks, Tag 013S] of a lift along a quasi-isomorphism, and the K-injectivity input is
[Stacks, Tag 013R]; all three are Mathlib's.

*Existence* is then the choice of one right resolution per object, which `C` having enough
injectives provides because `HomotopyCategory.Plus.localizerMorphism C` is a right derivability
structure. *Uniqueness up to unique isomorphism* is the lifting property read as: there is
exactly one comparison morphism between two right resolutions of the same object, so every right
resolution is a terminal object of the category of right resolutions; it needs no hypothesis on
`C` beyond `Abelian C`. *Functoriality* is the same bijection, now natural in `Y`, hence the
hom-set form of an adjunction: `ι` is a right adjoint and `K ↦ (j K).X₁` is the object map of its
left adjoint, so the unique `j f` with `(j K).w ≫ ι (j f) = f ≫ (j L).w` assembles into a functor
and the family `(j K).w` into a natural transformation. *Exactness* is the source's `ξ`: the
unique `ξ_K : F(K⟦a⟧) ⟶ (F K)⟦a⟧` with `α_{K⟦a⟧} ≫ ι ξ_K = (α_K)⟦a⟧` is an isomorphism, being a
comparison of two quasi-isomorphisms out of `K⟦a⟧`, and it is the only commutation of `F` with the
shift compatible with `α`; exactness then follows because the quasi-isomorphisms of `K⁺(C)` are
compatible with the triangulation. *Descent* uses `F` and `α` for one thing only: the canonical
functor `G = ι ⋙ Q : K⁺(ℐ) ⥤ D⁺(C)` is fully faithful by the lifting property and the bijection
`Q` induces on morphisms into a K-injective complex, and `Q (α.app K) : Q K ≅ G (F K)` makes it
essentially surjective, hence an equivalence whose quasi-inverse factors `F` through `Q`.

## Main results

* `HomotopyCategory.Plus.nonempty_resolutionFunctor`: an abelian category with enough injectives
  admits a resolution functor.
* `HomotopyCategory.Plus.nonempty_isTerminal_rightResolution`: over an arbitrary abelian category,
  every right resolution of an object of `K⁺(C)` is a terminal object of the category of right
  resolutions of that object, i.e. a right resolution is unique up to unique isomorphism.
* `HomotopyCategory.Plus.existsUnique_functor_of_resolutionFunctor`: a resolution functor `j`
  extends to a functor `K⁺(C) ⥤ K⁺(ℐ)` whose comparison maps are the given ones, in exactly one
  way.
* `HomotopyCategory.Plus.commShiftOfQuasiIso`: the commutation of a resolution functor with the
  shift, the source's `ξ`. It is the only one compatible with the comparison maps
  (`HomotopyCategory.Plus.commShiftOfQuasiIso_compatibility`,
  `HomotopyCategory.Plus.eq_commShiftOfQuasiIso`), and the functor is triangulated for it
  (`HomotopyCategory.Plus.isTriangulated_of_quasiIso`).
* `HomotopyCategory.Plus.exists_equivalence_and_existsUnique_lift_of_quasiIso`: a resolution
  functor factors through the localization `Q : K⁺(C) ⥤ D⁺(C)` by a functor quasi-inverse to
  `K⁺(ℐ) ⥤ D⁺(C)`, uniquely up to a unique natural transformation over it.

## Implementation notes

Existence and uniqueness are two theorems rather than one, because their hypotheses differ:
`EnoughInjectives C` is exactly what makes the type of resolution functors nonempty and is a
hypothesis of existence alone, whereas uniqueness uses only that the `R.X₁` are complexes of
injectives and the `R.w` quasi-isomorphisms. Stating them together would attach
`EnoughInjectives C` to uniqueness as well, which is strictly weaker than the mathematics gives.

Uniqueness is stated as terminality of an arbitrary object of
`CategoryTheory.LocalizerMorphism.RightResolution`, which is how Mathlib packages "unique up to
unique isomorphism" and is the whole of the assertion: from terminality of `R` and of `R'` one
recovers both that there is exactly one `f : R'.X₁ ⟶ R.X₁` with `R'.w ≫ f = R.w`, a morphism
`R' ⟶ R` being exactly such an `f`, and that every such `f` is an isomorphism, a morphism between
terminal objects being invertible. The weaker `∃! f, (R.w ≫ f = R'.w ∧ IsIso f)` would permit a
second morphism compatible with the comparison maps that is not invertible.

The functor extending `j` is `Adjunction.leftAdjointOfEquiv` at the family of hom-set
equivalences, so its functoriality is not verified a second time; what is left to say is the
commutative square `w_comp_map`, which is `Equiv.apply_symm_apply`, and the uniqueness, which is
the injectivity half of the same equivalence. Since the object map of the extension is pinned by
the statement, uniqueness is an equality of functors, and no `eqToHom` appears: a competing
solution `(F, α)` prescribes the right resolutions themselves, so substituting that family for
`j` makes the two object maps identical and only the morphism maps remain to be compared.

The `2`-commutativity over `D⁺(C)` of the triangle formed by a resolution functor is not stated as
a further conjunct of `existsUnique_functor_of_resolutionFunctor`, because it carries no content
beyond the hypothesis that the components of `α` are quasi-isomorphisms: for any localization `L`
of `K⁺(C)` at the quasi-isomorphisms, `Functor.whiskerRight α L` is an isomorphism by
`Localization.inverts` and `NatIso.isIso_of_isIso_app`. Stating it would additionally force
`[HasDerivedCategory C]`, a hypothesis the mathematics does not use.

For the descent, the equivalence is obtained from `G` directly, as fully faithful plus essentially
surjective, and the factorization of `F` is read off from it; of the universal property of `Q`
only inversion of the quasi-isomorphisms and essential surjectivity are used. The comparison of
two factorizations is the full faithfulness of precomposition with a localization functor
(`Localization.fullyFaithfulWhiskeringLeft`), so it is proved for an arbitrary pair of lifts of
`F` rather than for the chosen one.

## References

* [Stacks, Tag 013X], [Stacks, Tag 014W], [Stacks, Tag 05TJ], [Stacks, Tag 05TK]
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace HomotopyCategory.Plus

variable {C : Type*} [Category C] [Abelian C]

/-! ### Resolution functors -/

section Definition

variable (C)

/-- A *resolution functor* for an abelian category `C` is the data of a bounded below
complex of injectives `(j K).X₁`, i.e. an object of `K⁺(ℐ)`, for every object `K` of
`K⁺(C)`, together with a quasi-isomorphism `(j K).w : K ⟶ (j K).X₁` in `K⁺(C)`: that is,
of a right resolution of every `K` for the inclusion `K⁺(ℐ) ⥤ K⁺(C)`. (Functoriality of
`K ↦ (j K).X₁` is automatic, see [Stacks, Tag 05TJ].) -/
@[stacks 013W]
public abbrev ResolutionFunctor :=
  ∀ K : HomotopyCategory.Plus C, (HomotopyCategory.Plus.localizerMorphism C).RightResolution K

end Definition

/-! ### The lifting property

Composition with a quasi-isomorphism into a bounded below complex of injectives is bijective.
-/

/-- An object of `K⁺(C)` whose underlying cochain complex is K-injective is right orthogonal to
the acyclic complexes: every morphism to it from an acyclic bounded below complex is zero. -/
private lemma rightOrthogonal_of_isKInjective (X : HomotopyCategory.Plus C)
    [CochainComplex.IsKInjective X.obj.as] :
    (subcategoryAcyclic C).rightOrthogonal X := by
  intro A f hA
  apply (HomotopyCategory.Plus.ι C).map_injective
  rw [Functor.map_zero]
  exact CochainComplex.IsKInjective.rightOrthogonal _ ((HomotopyCategory.Plus.ι C).map f) hA

/-- K-injectivity of the target makes precomposition with a quasi-isomorphism bijective: if
`w : K ⟶ L` is a quasi-isomorphism of `K⁺(C)` and the cochain complex underlying an object `X` of
`K⁺(C)` is K-injective, then precomposition with `w` is a bijection from the morphisms `L ⟶ X` of
`K⁺(C)` onto the morphisms `K ⟶ X`. -/
private lemma bijective_precomp_of_quasiIso {K L : HomotopyCategory.Plus C} (w : K ⟶ L)
    (hw : quasiIso C w) (X : HomotopyCategory.Plus C)
    [CochainComplex.IsKInjective X.obj.as] :
    Function.Bijective (fun g : L ⟶ X ↦ w ≫ g) := by
  have hX := rightOrthogonal_of_isKInjective X
  rw [← ObjectProperty.isLocal_trW] at hX
  exact hX w (by rwa [← quasiIso_eq_subcategoryAcyclic_trW])

/-- The cochain complex underlying the image in `K⁺(C)` of an object of `K⁺(ℐ)` is K-injective:
it is a bounded below complex of injective objects of `C`. This is Mathlib's instance for the same
complex viewed through `Functor.mapHomologicalComplex`, at the object of
`CochainComplex.Plus (InjectiveObject C)` carried by `X`. -/
private lemma isKInjective_localizerMorphism_functor_obj
    (X : HomotopyCategory.Plus (InjectiveObject C)) :
    CochainComplex.IsKInjective (((localizerMorphism C).functor.obj X).obj.as) :=
  have h (L : CochainComplex.Plus (InjectiveObject C)) :
      CochainComplex.IsKInjective
        (((InjectiveObject.ι C).mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj) :=
    inferInstance
  h ⟨X.obj.as, (HomotopyCategory.plus_quotient_obj_iff _).1 X.property⟩

/-- The lifting property, which carries every statement of this file: composition with a
quasi-isomorphism `u : K ⟶ ι X` of `K⁺(C)`, where `ι` denotes the inclusion `K⁺(ℐ) ⥤ K⁺(C)`, is a
bijection from the morphisms `X ⟶ Y` of `K⁺(ℐ)` onto the morphisms `K ⟶ ι Y` of `K⁺(C)`, because
`ι Y` is K-injective, hence right orthogonal to the acyclic complexes, and because `ι` is fully
faithful. -/
private lemma bijective_precomp_map {K : HomotopyCategory.Plus C}
    {X Y : HomotopyCategory.Plus (InjectiveObject C)}
    (u : K ⟶ (localizerMorphism C).functor.obj X) (hu : quasiIso C u) :
    Function.Bijective (fun g : X ⟶ Y ↦ u ≫ (localizerMorphism C).functor.map g) :=
  have := isKInjective_localizerMorphism_functor_obj Y
  (bijective_precomp_of_quasiIso u hu ((localizerMorphism C).functor.obj Y)).comp
    ⟨fun _ _ h ↦ Functor.map_injective _ h, Functor.map_surjective _⟩

/-- The lifting property as an equivalence of hom-sets; as `Y` varies it is natural in `Y`, which
is what exhibits `ι` as a right adjoint. -/
private noncomputable def precompEquiv {K : HomotopyCategory.Plus C}
    {X Y : HomotopyCategory.Plus (InjectiveObject C)}
    (u : K ⟶ (localizerMorphism C).functor.obj X) (hu : quasiIso C u) :
    (X ⟶ Y) ≃ (K ⟶ (localizerMorphism C).functor.obj Y) :=
  Equiv.ofBijective _ (bijective_precomp_map u hu)

/-- `precompEquiv u hu` is composition with `u`. -/
private lemma precompEquiv_apply {K : HomotopyCategory.Plus C}
    {X Y : HomotopyCategory.Plus (InjectiveObject C)}
    (u : K ⟶ (localizerMorphism C).functor.obj X) (hu : quasiIso C u) (g : X ⟶ Y) :
    precompEquiv u hu g = u ≫ (localizerMorphism C).functor.map g :=
  rfl

/-- Two morphisms of `K⁺(ℐ)` which agree after composition with a quasi-isomorphism
`u : K ⟶ ι X` of `K⁺(C)` are equal. -/
private lemma hom_ext {K : HomotopyCategory.Plus C}
    {X Y : HomotopyCategory.Plus (InjectiveObject C)}
    (u : K ⟶ (localizerMorphism C).functor.obj X) (hu : quasiIso C u) {g g' : X ⟶ Y}
    (h : u ≫ (localizerMorphism C).functor.map g = u ≫ (localizerMorphism C).functor.map g') :
    g = g' :=
  (bijective_precomp_map u hu).injective h

/-- Given a quasi-isomorphism `u : K ⟶ ι X` of `K⁺(C)` and an arbitrary morphism `f : K ⟶ ι Y`,
this is the unique morphism `X ⟶ Y` of `K⁺(ℐ)` whose image under `ι` satisfies `u ≫ ι g = f`. -/
private noncomputable def lift {K : HomotopyCategory.Plus C}
    {X Y : HomotopyCategory.Plus (InjectiveObject C)}
    (u : K ⟶ (localizerMorphism C).functor.obj X) (hu : quasiIso C u)
    (f : K ⟶ (localizerMorphism C).functor.obj Y) : X ⟶ Y :=
  ((bijective_precomp_map u hu).surjective f).choose

private lemma comp_map_lift {K : HomotopyCategory.Plus C}
    {X Y : HomotopyCategory.Plus (InjectiveObject C)}
    (u : K ⟶ (localizerMorphism C).functor.obj X) (hu : quasiIso C u)
    (f : K ⟶ (localizerMorphism C).functor.obj Y) :
    u ≫ (localizerMorphism C).functor.map (lift u hu f) = f :=
  ((bijective_precomp_map u hu).surjective f).choose_spec

/-- A morphism of `K⁺(ℐ)` which compares two quasi-isomorphisms from a fixed object of `K⁺(C)`
to bounded below complexes of injectives is an isomorphism. -/
private lemma isIso_of_comp_map_eq {K : HomotopyCategory.Plus C}
    {X Y : HomotopyCategory.Plus (InjectiveObject C)}
    (u : K ⟶ (localizerMorphism C).functor.obj X) (hu : quasiIso C u)
    (v : K ⟶ (localizerMorphism C).functor.obj Y) (hv : quasiIso C v) (f : X ⟶ Y)
    (hf : u ≫ (localizerMorphism C).functor.map f = v) : IsIso f := by
  obtain ⟨g, hg⟩ := (bijective_precomp_map v hv).surjective u
  replace hg : v ≫ (localizerMorphism C).functor.map g = u := hg
  refine ⟨g, hom_ext u hu ?_, hom_ext v hv ?_⟩
  · rw [Functor.map_comp, ← Category.assoc, hf, hg]
    simp
  · rw [Functor.map_comp, ← Category.assoc, hg, hf]
    simp

/-! ### Existence and uniqueness of a resolution functor -/

/-- Let `C` be an abelian category with enough injectives. Then a resolution functor for `C`
exists ([Stacks, Tag 013W]): every object `K` of `K⁺(C)` admits a bounded below complex of
injectives `(j K).X₁` together with a quasi-isomorphism `(j K).w : K ⟶ (j K).X₁` in `K⁺(C)`. -/
@[stacks 013X "T_013X, existence: a resolution functor exists when `C` has enough injectives",
  sga "4½ Etat_0 3.2.3" "(4) existence"]
public theorem nonempty_resolutionFunctor (C : Type*) [Category C] [Abelian C]
    [EnoughInjectives C] :
    Nonempty (HomotopyCategory.Plus.ResolutionFunctor C) :=
  ⟨fun _ => Classical.arbitrary _⟩

/-- A right resolution `R` of `X` for a localizer morphism `Φ` is terminal in the category of
right resolutions of `X` as soon as, for every right resolution `R'` of `X`, there is exactly
one morphism `f : R'.X₁ ⟶ R.X₁` of the source category with `R'.w ≫ Φ.functor.map f = R.w`: a
morphism `R' ⟶ R` of right resolutions is exactly such an `f`. -/
private noncomputable def isTerminalOfExistsUniqueHom {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂} {Φ : LocalizerMorphism W₁ W₂} {X : C₂}
    (R : Φ.RightResolution X)
    (h : ∀ R' : Φ.RightResolution X, ∃! f : R'.X₁ ⟶ R.X₁, R'.w ≫ Φ.functor.map f = R.w) :
    IsTerminal R :=
  IsTerminal.ofUniqueHom (fun R' ↦ ⟨(h R').choose, (h R').choose_spec.1⟩)
    fun R' m ↦ LocalizerMorphism.RightResolution.hom_ext
      ((h R').unique m.comm (h R').choose_spec.1)

/-- Let `C` be an abelian category. A right resolution of an object `K` of `K⁺(C)` is unique up
to unique isomorphism: every right resolution `R` of `K` is a terminal object of the category
`(localizerMorphism C).RightResolution K` of right resolutions of `K`, in which a morphism
`R' ⟶ R` is a morphism `f : R'.X₁ ⟶ R.X₁` of `K⁺(ℐ)` with `R'.w ≫ f = R.w` in `K⁺(C)`. So any
two right resolutions of `K` are related by exactly one morphism compatible with their
comparison maps, and every such morphism is an isomorphism; applied to two resolution functors
this is the uniqueness up to unique isomorphism of [Stacks, Tag 013X], and it needs no hypothesis
on `C` beyond `Abelian C`. -/
@[stacks 013X "T_013X, uniqueness up to unique isomorphism; no hypothesis on `C`",
  sga "4½ Etat_0 3.2.3" "(4) uniqueness"]
public theorem nonempty_isTerminal_rightResolution (C : Type*) [Category C] [Abelian C]
    {K : HomotopyCategory.Plus C} (R : (localizerMorphism C).RightResolution K) :
    Nonempty (IsTerminal R) :=
  ⟨isTerminalOfExistsUniqueHom R fun R' ↦ (bijective_precomp_map R'.w R'.hw).existsUnique R.w⟩

/-! ### A resolution functor is a functor, in a unique way -/

section Functoriality

variable (j : ∀ K : HomotopyCategory.Plus C, (localizerMorphism C).RightResolution K)

/-- The functor `K⁺(C) ⥤ K⁺(ℐ)` underlying a resolution functor. As `Y` varies,
`precompEquiv (j K).w (j K).hw` is a hom-set equivalence natural in `Y`, so the resolutions
exhibit `ι : K⁺(ℐ) ⥤ K⁺(C)` as a right adjoint with `K ↦ (j K).X₁` as the object map of its
left adjoint; this is that left adjoint. -/
private noncomputable def functorOfRightResolutions :
    HomotopyCategory.Plus C ⥤ HomotopyCategory.Plus (InjectiveObject C) :=
  Adjunction.leftAdjointOfEquiv (G := (localizerMorphism C).functor)
    (F_obj := fun K ↦ (j K).X₁) (fun K _ ↦ precompEquiv (j K).w (j K).hw)
    (fun _ _ _ _ _ ↦ by
      rw [precompEquiv_apply, precompEquiv_apply, Functor.map_comp, Category.assoc])

/-- The defining property of the morphism map of `functorOfRightResolutions j`: it is the
commutative square of the source. -/
private lemma w_comp_map {K L : HomotopyCategory.Plus C} (f : K ⟶ L) :
    (j K).w ≫ (localizerMorphism C).functor.map ((functorOfRightResolutions j).map f) =
      f ≫ (j L).w := by
  simp only [functorOfRightResolutions, Adjunction.leftAdjointOfEquiv_obj,
    Adjunction.leftAdjointOfEquiv_map]
  rw [← precompEquiv_apply (j K).w (j K).hw, Equiv.apply_symm_apply, precompEquiv_apply]
  simp

/-- The comparison maps `(j K).w` of a resolution functor, as a natural transformation
`𝟭 K⁺(C) ⟶ j ⋙ ι`. -/
private noncomputable def comparison : 𝟭 (HomotopyCategory.Plus C) ⟶ functorOfRightResolutions j ⋙
    (localizerMorphism C).functor where
  app K := (j K).w
  naturality {_K _L} f := (w_comp_map j f).symm

/-- Uniqueness: a functor whose comparison maps are the given ones is
`functorOfRightResolutions j`. -/
private lemma eq_functorOfRightResolutions
    (F : HomotopyCategory.Plus C ⥤ HomotopyCategory.Plus (InjectiveObject C))
    (α : 𝟭 (HomotopyCategory.Plus C) ⟶ F ⋙ (localizerMorphism C).functor)
    (hα : ∀ K, quasiIso C (α.app K))
    (h : ∀ K, LocalizerMorphism.RightResolution.mk (α.app K) (hα K) = j K) :
    F = functorOfRightResolutions j := by
  have hj : j = fun K ↦ LocalizerMorphism.RightResolution.mk (α.app K) (hα K) :=
    funext fun K ↦ (h K).symm
  subst hj
  refine CategoryTheory.Functor.hext (fun K ↦ rfl) fun K L f ↦ heq_of_eq ?_
  exact (precompEquiv (α.app K) (hα K)).injective ((α.naturality f).symm.trans
    (w_comp_map (fun K ↦ LocalizerMorphism.RightResolution.mk (α.app K) (hα K)) f).symm)

/-- Let `C` be an abelian category, `ℐ ⊆ C` its full additive subcategory of injective
objects, and let `j` be a resolution functor for `C`, i.e. a right resolution
`(j K).w : K ⟶ (j K).X₁` in `K⁺(ℐ)` of every object `K` of `K⁺(C)`. Then there is a unique
way to make `K ↦ (j K).X₁` into a functor `F : K⁺(C) ⥤ K⁺(ℐ)` for which the comparison
maps `(j K).w` form a natural transformation `𝟭 K⁺(C) ⟶ F ⋙ (K⁺(ℐ) ⥤ K⁺(C))`; the latter
is then a `2`-isomorphism over `D⁺(C)`, since its components are quasi-isomorphisms. -/
@[stacks 05TJ]
public theorem existsUnique_functor_of_resolutionFunctor (j : ResolutionFunctor C) :
    ∃! F : HomotopyCategory.Plus C ⥤ HomotopyCategory.Plus (InjectiveObject C),
      ∃ (α : 𝟭 (HomotopyCategory.Plus C) ⟶ F ⋙ (localizerMorphism C).functor)
        (hα : ∀ K, quasiIso C (α.app K)),
        ∀ K, LocalizerMorphism.RightResolution.mk (α.app K) (hα K) = j K := by
  refine ⟨functorOfRightResolutions j, ⟨comparison j, fun K ↦ (j K).hw, fun K ↦ rfl⟩, ?_⟩
  rintro F ⟨α, hα, h⟩
  exact eq_functorOfRightResolutions j F α hα h

end Functoriality

/-! ### A resolution functor is exact -/

section Exactness

/-- Two commutations of a functor with the shift which have the same isomorphisms are equal:
the two remaining fields of `Functor.CommShift` are propositions. -/
private lemma commShift_ext {D E : Type*} [Category D] [Category E] {G : D ⥤ E} {A : Type*}
    [AddMonoid A] [HasShift D A] [HasShift E A] : ∀ h₁ h₂ : G.CommShift A,
    (∀ (a : A) (X : D), (h₁.commShiftIso a).hom.app X = (h₂.commShiftIso a).hom.app X) →
      h₁ = h₂ := by
  rintro ⟨i₁, _z₁, _a₁⟩ ⟨i₂, _z₂, _a₂⟩ e
  obtain rfl : i₁ = i₂ := funext fun a ↦ Iso.ext (NatTrans.ext (funext (e a)))
  rfl

variable (F : HomotopyCategory.Plus C ⥤ HomotopyCategory.Plus (InjectiveObject C))
  (α : 𝟭 (HomotopyCategory.Plus C) ⟶ F ⋙ (localizerMorphism C).functor)
  (hα : ∀ K, quasiIso C (α.app K))

/-- Naturality of the comparison maps, in the form in which the proof uses it. -/
private lemma app_naturality {K L : HomotopyCategory.Plus C} (f : K ⟶ L) :
    α.app K ≫ (localizerMorphism C).functor.map (F.map f) = f ≫ α.app L :=
  (α.naturality f).symm

private lemma app_naturality_assoc {K L : HomotopyCategory.Plus C} {X : HomotopyCategory.Plus C}
    (f : K ⟶ L) (g : (localizerMorphism C).functor.obj (F.obj L) ⟶ X) :
    α.app K ≫ (localizerMorphism C).functor.map (F.map f) ≫ g = f ≫ α.app L ≫ g := by
  rw [← Category.assoc, app_naturality, Category.assoc]

/-- The comparison quasi-isomorphism from `K⟦a⟧` to the image of `(F K)⟦a⟧`. -/
private noncomputable def shiftedComparison (a : ℤ) (K : HomotopyCategory.Plus C) :
    K⟦a⟧ ⟶ (localizerMorphism C).functor.obj ((F.obj K)⟦a⟧) :=
  (α.app K)⟦a⟧' ≫ ((localizerMorphism C).functor.commShiftIso a).inv.app (F.obj K)

include hα in
private lemma quasiIso_shiftedComparison (a : ℤ) (K : HomotopyCategory.Plus C) :
    quasiIso C (shiftedComparison F α a K) :=
  (quasiIso C).comp_mem _ _ ((MorphismProperty.IsCompatibleWithShift.iff _ _ a).2 (hα K))
    (MorphismProperty.of_isIso _ _)

section

variable [F.CommShift ℤ]

/-- Compatibility of the comparison maps with the shift says exactly that each component of the
commutation fits the comparison square `α_{K⟦a⟧} ≫ ι ξ_K = (α_K)⟦a⟧`. -/
private lemma natTrans_commShift_iff :
    NatTrans.CommShift α ℤ ↔ ∀ (a : ℤ) (K : HomotopyCategory.Plus C),
      α.app (K⟦a⟧) ≫ (localizerMorphism C).functor.map ((F.commShiftIso a).hom.app K) =
        (α.app K)⟦a⟧' ≫ ((localizerMorphism C).functor.commShiftIso a).inv.app (F.obj K) := by
  constructor
  · intro hc a K
    have := hc
    have h := NatTrans.shift_app_comm (τ := α) a K
    rw [Functor.commShiftIso_id_hom_app, Functor.commShiftIso_comp_hom_app] at h
    refine (Iso.eq_comp_inv
      (((localizerMorphism C).functor.commShiftIso a).app (F.obj K))).2 ?_
    rw [Category.assoc]
    exact ((Category.id_comp _).symm.trans h).symm
  · intro hsq
    refine NatTrans.CommShift.of_core (fun a ↦ ⟨NatTrans.ext (funext fun K ↦ ?_)⟩)
    dsimp
    rw [Functor.commShiftIso_id_hom_app, Functor.commShiftIso_comp_hom_app, Category.id_comp,
      ← Category.assoc, hsq, Category.assoc, Iso.inv_hom_id_app]
    exact (Category.comp_id _).symm

end

include hα in
/-- The isomorphism `ξ_K : F(K⟦a⟧) ⟶ (F K)⟦a⟧` of `K⁺(ℐ)`: the unique morphism whose image in
`K⁺(C)` is compatible with the comparison quasi-isomorphisms. -/
private noncomputable def commShiftIsoApp (a : ℤ) (K : HomotopyCategory.Plus C) :
    F.obj (K⟦a⟧) ⟶ (F.obj K)⟦a⟧ :=
  lift (α.app (K⟦a⟧)) (hα _) (shiftedComparison F α a K)

include hα in
private lemma comp_map_commShiftIsoApp (a : ℤ) (K : HomotopyCategory.Plus C) :
    α.app (K⟦a⟧) ≫ (localizerMorphism C).functor.map (commShiftIsoApp F α hα a K) =
      (α.app K)⟦a⟧' ≫ ((localizerMorphism C).functor.commShiftIso a).inv.app (F.obj K) :=
  comp_map_lift _ _ _

include hα in
private lemma comp_map_commShiftIsoApp_assoc (a : ℤ) (K : HomotopyCategory.Plus C)
    {X : HomotopyCategory.Plus C}
    (g : (localizerMorphism C).functor.obj ((F.obj K)⟦a⟧) ⟶ X) :
    α.app (K⟦a⟧) ≫ (localizerMorphism C).functor.map (commShiftIsoApp F α hα a K) ≫ g =
      (α.app K)⟦a⟧' ≫
        ((localizerMorphism C).functor.commShiftIso a).inv.app (F.obj K) ≫ g := by
  rw [← Category.assoc, comp_map_commShiftIsoApp, Category.assoc]

include hα in
/-- The characterisation of the source's `ξ`, and the lemma the whole commutation rests on: a
morphism `F(K⟦a⟧) ⟶ (F K)⟦a⟧` whose image in `K⁺(C)` fits the comparison square is `ξ_K`. -/
private lemma eq_commShiftIsoApp (a : ℤ) (K : HomotopyCategory.Plus C)
    (ξ : F.obj (K⟦a⟧) ⟶ (F.obj K)⟦a⟧)
    (hξ : α.app (K⟦a⟧) ≫ (localizerMorphism C).functor.map ξ =
      (α.app K)⟦a⟧' ≫ ((localizerMorphism C).functor.commShiftIso a).inv.app (F.obj K)) :
    ξ = commShiftIsoApp F α hα a K :=
  hom_ext (α.app (K⟦a⟧)) (hα _) (hξ.trans (comp_map_commShiftIsoApp F α hα a K).symm)

include hα in
private lemma isIso_commShiftIsoApp (a : ℤ) (K : HomotopyCategory.Plus C) :
    IsIso (commShiftIsoApp F α hα a K) :=
  isIso_of_comp_map_eq (α.app (K⟦a⟧)) (hα _) _ (quasiIso_shiftedComparison F α hα a K) _
    (comp_map_commShiftIsoApp F α hα a K)

include hα in
private lemma commShiftIsoApp_naturality (a : ℤ) {K L : HomotopyCategory.Plus C} (f : K ⟶ L) :
    F.map (f⟦a⟧') ≫ commShiftIsoApp F α hα a L =
      commShiftIsoApp F α hα a K ≫ (F.map f)⟦a⟧' := by
  apply hom_ext (α.app (K⟦a⟧)) (hα _)
  rw [Functor.map_comp, Functor.map_comp, app_naturality_assoc, comp_map_commShiftIsoApp,
    ← Category.assoc (α.app (K⟦a⟧)), comp_map_commShiftIsoApp, Category.assoc,
    ← Functor.commShiftIso_inv_naturality, ← Category.assoc, ← Functor.map_comp,
    ← app_naturality, Functor.map_comp, Category.assoc]

include hα in
/-- The commutation isomorphism of a resolution functor with the shift by `a`. -/
private noncomputable def commShiftIsoOfQuasiIso (a : ℤ) :
    shiftFunctor (HomotopyCategory.Plus C) a ⋙ F ≅
      F ⋙ shiftFunctor (HomotopyCategory.Plus (InjectiveObject C)) a :=
  NatIso.ofComponents
    (fun K ↦ haveI := isIso_commShiftIsoApp F α hα a K; asIso (commShiftIsoApp F α hα a K))
    (fun f ↦ commShiftIsoApp_naturality F α hα a f)

include hα in
private lemma commShiftIsoOfQuasiIso_hom_app (a : ℤ) (K : HomotopyCategory.Plus C) :
    (commShiftIsoOfQuasiIso F α hα a).hom.app K = commShiftIsoApp F α hα a K := rfl

include hα in
/-- **The commutation of a resolution functor with the shift**, the source's `ξ`: its component
at `a` and `K` is the unique `ξ_K : F(K⟦a⟧) ⟶ (F K)⟦a⟧` with `α_{K⟦a⟧} ≫ ι ξ_K = (α_K)⟦a⟧`. It
is the only commutation compatible with `α` (`commShiftOfQuasiIso_compatibility`,
`eq_commShiftOfQuasiIso`), and `F` is exact for it (`isTriangulated_of_quasiIso`). -/
@[stacks 014W "the commutation with the shift itself; `commShiftOfQuasiIso_compatibility` is its \
compatibility with the comparison maps and `eq_commShiftOfQuasiIso` its uniqueness",
  instance_reducible, no_expose]
noncomputable def commShiftOfQuasiIso : F.CommShift ℤ where
  commShiftIso a := commShiftIsoOfQuasiIso F α hα a
  commShiftIso_zero := by
    refine Iso.ext (NatTrans.ext (funext fun K ↦ ?_))
    rw [commShiftIsoOfQuasiIso_hom_app]
    refine (eq_commShiftIsoApp F α hα 0 K _ ?_).symm
    symm
    rw [Functor.CommShift.isoZero_hom_app, Functor.map_comp, app_naturality_assoc,
      Functor.commShiftIso_zero, Functor.CommShift.isoZero_inv_app, ← Category.assoc,
      ← Category.assoc]
    congr 1
    exact (shiftFunctorZero (HomotopyCategory.Plus C) ℤ).hom.naturality (α.app K)
  commShiftIso_add a b := by
    refine Iso.ext (NatTrans.ext (funext fun K ↦ ?_))
    rw [commShiftIsoOfQuasiIso_hom_app]
    refine (eq_commShiftIsoApp F α hα (a + b) K _ ?_).symm
    symm
    rw [Functor.CommShift.isoAdd_hom_app, Functor.map_comp, Functor.map_comp, Functor.map_comp,
      app_naturality_assoc F α (L := (K⟦a⟧)⟦b⟧)
        ((shiftFunctorAdd (HomotopyCategory.Plus C) a b).hom.app K),
      commShiftIsoOfQuasiIso_hom_app, commShiftIsoOfQuasiIso_hom_app,
      comp_map_commShiftIsoApp_assoc, ← Functor.commShiftIso_inv_naturality_assoc,
      ← Functor.map_comp_assoc, comp_map_commShiftIsoApp, Functor.commShiftIso_add,
      Functor.CommShift.isoAdd_inv_app]
    simp [Functor.map_comp]

include hα in
/-- `commShiftOfQuasiIso` is compatible with the comparison maps `α`: each of its components
satisfies `α_{K⟦a⟧} ≫ ι ξ_K = (α_K)⟦a⟧`. -/
@[stacks 014W "the commutation is compatible with the comparison maps"]
lemma commShiftOfQuasiIso_compatibility :
    letI := commShiftOfQuasiIso F α hα
    NatTrans.CommShift α ℤ := by
  let _ := commShiftOfQuasiIso F α hα
  exact (natTrans_commShift_iff F α).2 fun a K ↦ comp_map_commShiftIsoApp F α hα a K

include hα in
/-- Uniqueness of the source's `ξ`: a commutation of `F` with the shift which is compatible with
the comparison maps `α` has `ξ` for each of its components, hence is `commShiftOfQuasiIso`. -/
@[stacks 014W "uniqueness of the commutation compatible with the comparison maps"]
lemma eq_commShiftOfQuasiIso :
    ∀ h : F.CommShift ℤ, (letI := h; NatTrans.CommShift α ℤ) →
      h = commShiftOfQuasiIso F α hα := by
  intro h hh
  let _ := h
  exact commShift_ext _ _ fun a K ↦
    eq_commShiftIsoApp F α hα a K _ ((natTrans_commShift_iff F α).1 hh a K)

include hα in
/-- A resolution functor is exact: it carries distinguished triangles of `K⁺(C)` to
distinguished triangles of `K⁺(ℐ)`, for its commutation with the shift. -/
@[stacks 014W "a resolution functor is exact"]
lemma isTriangulated_of_quasiIso :
    letI := commShiftOfQuasiIso F α hα
    F.IsTriangulated := by
  let _ := commShiftOfQuasiIso F α hα
  have : (quasiIso C).IsCompatibleWithTriangulation := by
    rw [quasiIso_eq_subcategoryAcyclic_trW]
    infer_instance
  refine ⟨fun T hT ↦ ?_⟩
  obtain ⟨N, g₂, g₃, hT'⟩ := distinguished_cocone_triangle (F.map T.mor₁)
  obtain ⟨c, hc, hc₂, hc₃⟩ := MorphismProperty.compatible_with_triangulation (W := quasiIso C)
    T ((localizerMorphism C).functor.mapTriangle.obj (Triangle.mk (F.map T.mor₁) g₂ g₃)) hT
    ((localizerMorphism C).functor.map_distinguished _ hT') (α.app T.obj₁) (α.app T.obj₂)
    (hα _) (hα _) (app_naturality F α T.mor₁).symm
  obtain ⟨u, hu⟩ := (precompEquiv (α.app T.obj₃) (hα _)).surjective c
  replace hu : α.app T.obj₃ ≫ (localizerMorphism C).functor.map u = c := hu
  have hiso : IsIso u := isIso_of_comp_map_eq (α.app T.obj₃) (hα _) c hc u hu
  subst hu
  replace hc₂ : T.mor₂ ≫ α.app T.obj₃ ≫ (localizerMorphism C).functor.map u =
      α.app T.obj₂ ≫ (localizerMorphism C).functor.map g₂ := hc₂
  replace hc₃ : T.mor₃ ≫ (α.app T.obj₁)⟦(1 : ℤ)⟧' =
      (α.app T.obj₃ ≫ (localizerMorphism C).functor.map u) ≫
        (localizerMorphism C).functor.map g₃ ≫
          ((localizerMorphism C).functor.commShiftIso 1).hom.app (F.obj T.obj₁) := hc₃
  refine isomorphic_distinguished _ hT' _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (@asIso _ _ _ _ u hiso) ?_ ?_ ?_)
  · change F.map T.mor₁ ≫ 𝟙 (F.obj T.obj₂) = 𝟙 (F.obj T.obj₁) ≫ F.map T.mor₁
    rw [Category.id_comp, Category.comp_id]
  · change F.map T.mor₂ ≫ u = 𝟙 (F.obj T.obj₂) ≫ g₂
    rw [Category.id_comp]
    apply hom_ext (α.app T.obj₂) (hα _)
    rw [Functor.map_comp, app_naturality_assoc]
    exact hc₂
  · have hξ : (F.commShiftIso (1 : ℤ)).hom.app T.obj₁ = commShiftIsoApp F α hα 1 T.obj₁ := rfl
    change (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
        (shiftFunctor (HomotopyCategory.Plus (InjectiveObject C)) 1).map (𝟙 (F.obj T.obj₁)) =
      u ≫ g₃
    rw [CategoryTheory.Functor.map_id]
    refine (Category.comp_id _).trans ?_
    rw [hξ]
    apply hom_ext (α.app T.obj₃) (hα _)
    rw [Functor.map_comp, Functor.map_comp, app_naturality_assoc, comp_map_commShiftIsoApp,
      ← Category.assoc, hc₃]
    simp

end Exactness

/-! ### Descent to a quasi-inverse of `K⁺(ℐ) ⥤ D⁺(C)` -/

section Descent

variable (C) in
/-- The canonical functor `G = ι ⋙ Q : K⁺(ℐ) ⥤ D⁺(𝒜)` from the homotopy category of bounded
below complexes of injectives to the bounded below derived category. -/
private noncomputable abbrev ιCompQh [HasDerivedCategory C] :
    HomotopyCategory.Plus (InjectiveObject C) ⥤ DerivedCategory.Plus C :=
  (localizerMorphism C).functor ⋙ DerivedCategory.Plus.Qh

variable [HasDerivedCategory C]

/-- **The content of [Stacks, Tag 013V] used here.** The canonical functor
`G = ι ⋙ Q : K⁺(ℐ) ⥤ D⁺(𝒜)` is fully faithful: on morphisms it is the composite of the
bijection given by full faithfulness of `ι` with the bijection `Q` induces on morphisms whose
target is K-injective, `ι Y` being a bounded below complex of injectives. -/
private lemma ιCompQh_map_bijective (X Y : HomotopyCategory.Plus (InjectiveObject C)) :
    Function.Bijective ((ιCompQh C).map : (X ⟶ Y) → _) :=
  (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective _ _
      (isKInjective_localizerMorphism_functor_obj Y)).comp
    ((Functor.FullyFaithful.ofFullyFaithful (localizerMorphism C).functor).map_bijective X Y)

section

variable {F : HomotopyCategory.Plus C ⥤ HomotopyCategory.Plus (InjectiveObject C)}
  {α : 𝟭 (HomotopyCategory.Plus C) ⟶ F ⋙ (localizerMorphism C).functor}
  (hα : ∀ K, quasiIso C (α.app K))

include hα

/-- The image of `α` in `D⁺(C)` is an isomorphism `Q ≅ F ⋙ G`: it is `α` whiskered into `Q`,
which inverts the quasi-isomorphisms. -/
private noncomputable def isoCompQh : DerivedCategory.Plus.Qh ≅ F ⋙ ιCompQh C :=
  have _ (K : HomotopyCategory.Plus C) :
      IsIso ((Functor.whiskerRight α DerivedCategory.Plus.Qh).app K) :=
    Localization.inverts DerivedCategory.Plus.Qh (quasiIso C) _ (hα K)
  have _ := NatIso.isIso_of_isIso_app (Functor.whiskerRight α DerivedCategory.Plus.Qh)
  (Functor.leftUnitor _).symm ≪≫ asIso (Functor.whiskerRight α DerivedCategory.Plus.Qh)

/-- `G` is essentially surjective: every object of `D⁺(C)` is isomorphic to some `Q K`, and
`Q (α.app K)` identifies that with `G (F K)`. -/
private lemma essSurj_ιCompQh : (ιCompQh C).EssSurj where
  mem_essImage K :=
    ⟨F.obj (DerivedCategory.Plus.Qh.objPreimage K),
      ⟨((isoCompQh hα).app _).symm ≪≫ DerivedCategory.Plus.Qh.objObjPreimageIso K⟩⟩

/-- `G = ι ⋙ Q : K⁺(ℐ) ⥤ D⁺(C)` is an equivalence. -/
private lemma isEquivalence_ιCompQh : (ιCompQh C).IsEquivalence :=
  ⟨⟨fun {_ _} ↦ (ιCompQh_map_bijective _ _).injective⟩,
    ⟨fun {_ _} ↦ (ιCompQh_map_bijective _ _).surjective⟩, essSurj_ιCompQh hα⟩

/-- The equivalence `D⁺(C) ≌ K⁺(ℐ)` inverse to `G`, so that its `inverse` is `G` on the
nose. -/
private noncomputable def equivalence :
    DerivedCategory.Plus C ≌ HomotopyCategory.Plus (InjectiveObject C) :=
  have _ := isEquivalence_ιCompQh hα
  (ιCompQh C).asEquivalence.symm

/-- The quasi-inverse of `G` is a factorization of `F` through `Q`: transport `Q ≅ F ⋙ G`
along `G ⋙ j' ≅ 𝟭 K⁺(ℐ)`. -/
private noncomputable def isoCompFunctor :
    DerivedCategory.Plus.Qh ⋙ (equivalence hα).functor ≅ F :=
  Functor.isoWhiskerRight (isoCompQh hα) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F (equivalence hα).counitIso ≪≫ F.rightUnitor

end

/-- Any two factorizations of a functor `F : K⁺(C) ⥤ K⁺(ℐ)` through the localization
`Q : K⁺(C) ⥤ D⁺(C)` are compared by exactly one natural transformation over `F`. -/
private theorem existsUnique_whiskerLeft_eq
    {F : HomotopyCategory.Plus C ⥤ HomotopyCategory.Plus (InjectiveObject C)}
    (j₁ j₂ : DerivedCategory.Plus C ⥤ HomotopyCategory.Plus (InjectiveObject C))
    (e₁ : DerivedCategory.Plus.Qh ⋙ j₁ ≅ F) (e₂ : DerivedCategory.Plus.Qh ⋙ j₂ ≅ F) :
    ∃! τ : j₁ ⟶ j₂,
      Functor.whiskerLeft DerivedCategory.Plus.Qh τ = e₁.hom ≫ e₂.inv :=
  have ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Plus.Qh
    (quasiIso C) (HomotopyCategory.Plus (InjectiveObject C))
  ⟨ff.preimage (X := j₁) (Y := j₂) (e₁.hom ≫ e₂.inv), ff.map_preimage _,
    fun _ hτ ↦ ff.map_injective (hτ.trans (ff.map_preimage _).symm)⟩

/-- Let `C` be an abelian category, `ℐ ⊆ C` its full additive subcategory of injective
objects, and let `F : K⁺(C) ⥤ K⁺(ℐ)` be a functor equipped with comparison maps
`α.app K : K ⟶ F K` in `K⁺(C)` that are quasi-isomorphisms, i.e. the functorial form of a
resolution functor ([Stacks, Tags 013W, 05TJ]). Then `F` factors through the localization
`Q : K⁺(C) ⥤ D⁺(C)` by a functor which is quasi-inverse to the canonical functor
`K⁺(ℐ) ⥤ D⁺(C)`, and the factorization is unique up to a unique natural transformation
over `F`. -/
@[stacks 05TK]
public theorem exists_equivalence_and_existsUnique_lift_of_quasiIso
    (F : HomotopyCategory.Plus C ⥤ HomotopyCategory.Plus (InjectiveObject C))
    (α : 𝟭 (HomotopyCategory.Plus C) ⟶ F ⋙ (localizerMorphism C).functor)
    (hα : ∀ K, quasiIso C (α.app K)) :
    (∃ e : DerivedCategory.Plus C ≌ HomotopyCategory.Plus (InjectiveObject C),
      e.inverse = (localizerMorphism C).functor ⋙ DerivedCategory.Plus.Qh ∧
        Nonempty (DerivedCategory.Plus.Qh ⋙ e.functor ≅ F)) ∧
    ∀ (j₁ j₂ : DerivedCategory.Plus C ⥤ HomotopyCategory.Plus (InjectiveObject C))
      (e₁ : DerivedCategory.Plus.Qh ⋙ j₁ ≅ F) (e₂ : DerivedCategory.Plus.Qh ⋙ j₂ ≅ F),
      ∃! τ : j₁ ⟶ j₂,
        Functor.whiskerLeft DerivedCategory.Plus.Qh τ = e₁.hom ≫ e₂.inv :=
  ⟨⟨equivalence hα, rfl, ⟨isoCompFunctor hα⟩⟩, existsUnique_whiskerLeft_eq⟩

end Descent

end HomotopyCategory.Plus

end

end

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

Stacks 013V, Proposition 13.23.1.

Let `A` be an abelian category with enough injectives, and let `I ⊆ A` be the strictly
full additive subcategory of injective objects.  Working with cochain complexes over the
cohomological complex shape (`ComplexShape.up ℤ`, differentials of degree `+1`), one forms

* the homotopy category `K(A)` (`HomotopyCategory A (ComplexShape.up ℤ)`) and its
  bounded-below injective part `K^+(I)`, the full subcategory of `K(A)` whose objects are
  *actual* bounded-below cochain complexes of injectives (not closed under isomorphism in
  `K(A)`),
* the derived category `D(A)` (`DerivedCategory A`) and its bounded-below part `D^+(A)`,

and the canonical functor of Definition 6: the restriction of the (triangulated)
localization functor `K(A) → D(A)` (`DerivedCategory.Qh`) to the bounded-below injective
complexes, corestricted to `D^+(A)`.

The theorem asserts that this functor is an equivalence of triangulated categories, the
conjunction of:

1. (Exactness.) It is a triangulated functor: additive, commuting with the shift, and
   sending distinguished triangles to distinguished triangles.

2. (Full faithfulness.) For bounded-below complexes of injectives `K, L`, the map
   `Hom_{K(A)}(K, L) → Hom_{D(A)}(Qh K, Qh L)` induced by `Qh` is a bijection.  (Source
   input: Stacks 05TG = `CochainComplex.IsKInjective.Qh_map_bijective`, valid because a
   bounded-below complex of injectives is K-injective,
   `CochainComplex.isKInjective_of_injective`.)

3. (Essential surjectivity.) Every object of `D^+(A)` is isomorphic in `D(A)` to the image
   of a bounded-below complex of injectives, i.e. admits an injective resolution.  (Source
   input: Stacks 013K.)
-/

open CategoryTheory Limits HomologicalComplex Pretriangulated

/-
## Formalization notes

* `K^+(I)` is realized as the *strict* image (NOT the iso-closure) of the property
  `injPlus A` on `CochainComplex A ℤ` under the homotopy-category quotient
  `K(A) → K(A)`.  An object lies in `homotopyInjPlus A` exactly when it is literally
  `Q K` for some genuine bounded-below cochain complex of injectives `K`; thus the objects
  of `K^+(I)` are exactly the actual bounded-below complexes of injectives, with morphisms
  the homotopy classes of chain maps.  This is the same pattern Mathlib uses for its own
  `HomotopyCategory.plus A := (CochainComplex.plus A).strictMap (HomotopyCategory.quotient ..)`.
* The remark of the source that `K^+(I)` is a full triangulated subcategory of `K(A)` is
  proved here: `homotopyInjPlus A` contains a zero object, is stable under the shift, and is
  closed (up to isomorphism, as required by `IsTriangulatedClosed₂`) under cones (the cone of
  a morphism of bounded-below complexes of injectives is again such a complex, since each
  term is a finite biproduct of injectives, hence injective).  These give
  `(homotopyInjPlus A).IsTriangulated`, which endows `KPlusInj A` with a `Pretriangulated`
  structure and makes the inclusion `K^+(I) ↪ K(A)` triangulated.
* `D^+(A)` is the bounded-below part of the standard t-structure on `D(A)`,
  `(DerivedCategory.TStructure.t).plus`, whose membership predicate is `∃ a, IsGE M a`,
  i.e. exactly the `+` condition.
* The functor of Definition 6, `QhPlus`, is the corestriction to `D^+(A)` of the composite
  `K^+(I) ↪ K(A) ⟶ D(A)`.  It inherits a `Functor.CommShift ℤ` structure from `Qh`, so the
  statement that it is *exact* is `(QhPlus A).IsTriangulated`.
* `HasDerivedCategory A` is a data hypothesis (not synthesized from `EnoughInjectives A`) and
  is assumed wherever the derived category appears.
-/

variable (A : Type*) [Category A] [Abelian A]

-- Main Definition(s)

/-- The property on cochain complexes (`ComplexShape.up ℤ`) of being bounded below
(`IsStrictlyGE` for some degree) and having injective terms.  This is the object-level
description of the genuine complexes making up `K^+(I)`. -/
@[sga "4½ Etat_0 1.2.3" "special case"]
def injPlus : ObjectProperty (CochainComplex A ℤ) :=
  fun K => (∃ n, K.IsStrictlyGE n) ∧ (∀ i, Injective (K.X i))

/-- The object property carving out `K^+(I) ⊆ K(A)`: the *strict* image (NOT iso-closure)
of `injPlus A` under the quotient functor `K(A) → K(A)`.  A homotopy class satisfies it iff
it is literally `Q K` for some genuine bounded-below cochain complex of injectives `K`. -/
@[sga "4½ Etat_0 1.2.3" "special case"]
def homotopyInjPlus : ObjectProperty (HomotopyCategory A (ComplexShape.up ℤ)) :=
  (injPlus A).strictMap (HomotopyCategory.quotient A (ComplexShape.up ℤ))

/-- The bounded-below homotopy category of injectives `K^+(I)`: its objects are the actual
bounded-below cochain complexes of injectives, morphisms the homotopy classes. -/
abbrev KPlusInj := (homotopyInjPlus A).FullSubcategory

/-- Membership criterion: the homotopy class `Q K` of a cochain complex `K` lies in `K^+(I)`
iff `K` is genuinely a bounded-below complex of injectives. -/
theorem homotopyInjPlus_quotient_obj_iff (K : CochainComplex A ℤ) :
    homotopyInjPlus A ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ↔ injPlus A K := by
  refine ⟨?_, ObjectProperty.strictMap.mk K⟩
  rintro ⟨_, h⟩
  exact h

-- Closure properties of `K^+(I)` (the "full triangulated subcategory" remark of the source).

/-- `injPlus` is stable under the shift on cochain complexes. -/
theorem injPlus_shift (K : CochainComplex A ℤ) (a : ℤ) (hK : injPlus A K) :
    injPlus A ((shiftFunctor (CochainComplex A ℤ) a).obj K) := by
  obtain ⟨⟨n, hn⟩, hinj⟩ := hK
  have := hn
  exact ⟨⟨n - a, CochainComplex.isStrictlyGE_shift K n a (n - a) (by omega)⟩, fun i ↦ hinj (i + a)⟩

/-- `K^+(I)` is stable under the shift in `K(A)`. -/
theorem homotopyInjPlus_shift (X : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ)
    (hX : homotopyInjPlus A X) :
    homotopyInjPlus A ((shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) n).obj X) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  rw [HomotopyCategory.shift_quotient_obj]
  rw [homotopyInjPlus_quotient_obj_iff] at hX ⊢
  exact injPlus_shift A K n hX

/-- `K^+(I)` contains a zero object (the zero complex is bounded below with injective—zero—
terms). -/
instance instHIPzero : (homotopyInjPlus A).ContainsZero := by
  obtain ⟨Z, hZ⟩ := (inferInstance : HasZeroObject (CochainComplex A ℤ))
  refine ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z, Functor.map_isZero _ hZ, ?_⟩
  rw [homotopyInjPlus_quotient_obj_iff]
  refine ⟨⟨0, ?_⟩, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i _
    exact Functor.map_isZero (HomologicalComplex.eval A (ComplexShape.up ℤ) i) hZ
  · intro i
    exact (Functor.map_isZero (HomologicalComplex.eval A (ComplexShape.up ℤ) i) hZ).injective

/-- `K^+(I)` is stable under the shift functors of `K(A)`. -/
instance instHIPshift : (homotopyInjPlus A).IsStableUnderShift ℤ :=
  ⟨fun n => ⟨fun X hX => by
    rw [ObjectProperty.prop_shift_iff]; exact homotopyInjPlus_shift A X n hX⟩⟩

/-- A biproduct of two zero objects is a zero object. -/
private theorem isZero_biprod_of_isZero {X Y : A} (h1 : IsZero X) (h2 : IsZero Y) :
    IsZero (X ⊞ Y) := by
  rw [IsZero.iff_id_eq_zero]
  apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
    simp [(IsZero.iff_id_eq_zero _).mp h1, (IsZero.iff_id_eq_zero _).mp h2]

/-- The mapping cone of a morphism of bounded-below complexes of injectives is again a
bounded-below complex of injectives: each term is a biproduct `K.X (i+1) ⊞ L.X i` of
injectives, hence injective, and the terms vanish below the common bound. -/
theorem injPlus_mappingCone (K L : CochainComplex A ℤ) (φ : K ⟶ L)
    (hK : injPlus A K) (hL : injPlus A L) :
    injPlus A (CochainComplex.mappingCone φ) := by
  obtain ⟨⟨nK, hnK⟩, hinjK⟩ := hK
  obtain ⟨⟨nL, hnL⟩, hinjL⟩ := hL
  have := hnK
  have := hnL
  have e (i : ℤ) : (CochainComplex.mappingCone φ).X i ≅ K.X (i + 1) ⊞ L.X i :=
    HomologicalComplex.homotopyCofiber.XIsoBiprod φ i (i + 1) (by simp)
  refine ⟨⟨min nK nL - 1, ?_⟩, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    refine IsZero.of_iso ?_ (e i)
    have h1 : IsZero (K.X (i + 1)) := CochainComplex.isZero_of_isStrictlyGE K nK (i + 1) (by omega)
    have h2 : IsZero (L.X i) := CochainComplex.isZero_of_isStrictlyGE L nL i (by omega)
    exact isZero_biprod_of_isZero A h1 h2
  · intro i
    have : Injective (K.X (i + 1)) := hinjK (i + 1)
    have : Injective (L.X i) := hinjL i
    exact Injective.of_iso (e i).symm inferInstance

/-- The cone closure: in a distinguished triangle `obj₁ ⟶ obj₂ ⟶ obj₃` with `obj₁` and
`obj₂` in `K^+(I)`, the third object `obj₃` is isomorphic to an object of `K^+(I)`.  This is
the mapping-cone case, proved by lifting the connecting map to a chain map and using
`injPlus_mappingCone`. -/
private theorem homotopyInjPlus_cone
    (T : Pretriangulated.Triangle (HomotopyCategory A (ComplexShape.up ℤ)))
    (hT : T ∈ Pretriangulated.distinguishedTriangles)
    (h1 : homotopyInjPlus A T.obj₁) (h2 : homotopyInjPlus A T.obj₂) :
    (homotopyInjPlus A).isoClosure T.obj₃ := by
  obtain ⟨K, hKeq⟩ := HomotopyCategory.quotient_obj_surjective T.obj₁
  obtain ⟨L, hLeq⟩ := HomotopyCategory.quotient_obj_surjective T.obj₂
  have hK : injPlus A K := by rwa [← homotopyInjPlus_quotient_obj_iff, hKeq]
  have hL : injPlus A L := by rwa [← homotopyInjPlus_quotient_obj_iff, hLeq]
  set g : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K ⟶
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L :=
    (eqToHom hKeq) ≫ T.mor₁ ≫ (eqToHom hLeq.symm) with hg
  obtain ⟨φ, hφ⟩ := Quot.exists_rep g
  set T₂ := CochainComplex.mappingCone.triangleh φ with hT₂def
  have hT₂ : T₂ ∈ Pretriangulated.distinguishedTriangles := ⟨K, L, φ, ⟨Iso.refl _⟩⟩
  have hcomm : T.mor₁ ≫ (eqToIso hLeq.symm).hom = (eqToIso hKeq.symm).hom ≫ T₂.mor₁ := by
    rw [show T₂.mor₁ = g from hφ, hg]
    simp
  have e := Pretriangulated.isoTriangleOfIso₁₂ T T₂ hT hT₂ (eqToIso hKeq.symm) (eqToIso hLeq.symm)
      hcomm
  have hmem : homotopyInjPlus A T₂.obj₃ := by
    change homotopyInjPlus A ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        (CochainComplex.mappingCone φ))
    rw [homotopyInjPlus_quotient_obj_iff]
    exact injPlus_mappingCone A K L φ hK hL
  exact ⟨T₂.obj₃, hmem, ⟨Pretriangulated.Triangle.π₃.mapIso e⟩⟩

/-- `K^+(I)` is closed under cones (the `IsTriangulatedClosed₂` field), obtained from the
cone closure by inverse rotation of the distinguished triangle. -/
theorem homotopyInjPlus_ext₂' :
    ∀ T ∈ Pretriangulated.distinguishedTriangles,
      (homotopyInjPlus A) T.obj₁ → (homotopyInjPlus A) T.obj₃ →
      (homotopyInjPlus A).isoClosure T.obj₂ := by
  intro T hT h1 h3
  have hinv1 : homotopyInjPlus A T.invRotate.obj₁ := by
    change homotopyInjPlus A ((shiftFunctor _ (-1 : ℤ)).obj T.obj₃)
    exact homotopyInjPlus_shift A T.obj₃ (-1) h3
  exact homotopyInjPlus_cone A T.invRotate (Pretriangulated.inv_rot_of_distTriang T hT) hinv1 h1

/-- `K^+(I)` is closed under extensions: in a distinguished triangle whose first and third
objects lie in `K^+(I)`, the second object is isomorphic to an object of `K^+(I)`. -/
instance instHIPclosed₂ : (homotopyInjPlus A).IsTriangulatedClosed₂ := ⟨homotopyInjPlus_ext₂' A⟩

/-- `K^+(I)` is a triangulated subcategory of `K(A)`; this endows `KPlusInj A` with a
`Pretriangulated` structure and makes the inclusion `K^+(I) ↪ K(A)` a triangulated
functor. -/
@[sga "4½ Etat_0 1.2.3" "special case"]
instance instHIPtriangulated : (homotopyInjPlus A).IsTriangulated := ⟨⟩

/-- The object property carving out `D^+(A) ⊆ D(A)`: the bounded-below part of the standard
t-structure, i.e. `∃ a, DerivedCategory.IsGE M a`. -/
@[sga "4 Vbis 1.3.8", sga "4 Vbis 2.4.1", sga "4½ Etat_0 3.1.3", sga "4½ Rapport 4.1"]
abbrev derivedPlus [HasDerivedCategory A] : ObjectProperty (DerivedCategory A) :=
  (DerivedCategory.TStructure.t (C := A)).plus

/-- The bounded-below derived category `D^+(A)`. -/
@[sga "4 Vbis 1.3.8",
  sga "4 Vbis 2.4.1",
  sga "4½ Etat_0 3.1.1",
  sga "4½ Etat_0 3.1.2",
  sga "4½ Etat_0 3.1.3",
  sga "4½ Rapport 4.1",
  sga "6 I 1.1.5" "the fiber D⁺(C_X)"]
abbrev DPlus [HasDerivedCategory A] := (derivedPlus A).FullSubcategory

/-- A bounded-below complex of injectives is sent by `Qh` into `D^+(A)`: this corestriction
is well defined because such a complex has bounded-below cohomology. -/
theorem qh_mem_derivedPlus [HasDerivedCategory A] (X : KPlusInj A) :
    derivedPlus A (DerivedCategory.Qh.obj ((homotopyInjPlus A).ι.obj X)) := by
  obtain ⟨X, hX⟩ := X
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  rw [homotopyInjPlus_quotient_obj_iff] at hX
  obtain ⟨⟨n, hn⟩, hinj⟩ := hX
  have := hn
  refine ⟨n, ?_⟩
  -- `Qh.obj ((quotient A _).obj K)` and `Q.obj K` are only *isomorphic* as far as the
  -- elaborator can see (the body of `HomologicalComplexUpToQuasiIso.Qh` is not exposed),
  -- so transport `IsGE` along `quotientCompQhIso` instead of asserting a defeq.
  have : (DerivedCategory.Q.obj K).IsGE n := by
    rw [DerivedCategory.isGE_Q_obj_iff]
    infer_instance
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((DerivedCategory.quotientCompQhIso A).symm.app K) n

/-- The canonical functor of Definition 6, `K^+(I) → D^+(A)`: the restriction of the
localization functor `DerivedCategory.Qh` to bounded-below injective complexes, corestricted
to `D^+(A)`.  It inherits a `CommShift ℤ` structure from `Qh`. -/
noncomputable def QhPlus [HasDerivedCategory A] : KPlusInj A ⥤ DPlus A :=
  (derivedPlus A).lift ((homotopyInjPlus A).ι ⋙ DerivedCategory.Qh) (qh_mem_derivedPlus A)

/-- `QhPlus` commutes with the shift: it inherits the `CommShift ℤ` structure from `Qh`
through the lift to the (shift-stable) subcategory `D^+(A)`.  This is what makes the
exactness statement `(QhPlus A).IsTriangulated` well posed. -/
noncomputable instance instQhPlusCommShift [HasDerivedCategory A] : (QhPlus A).CommShift ℤ := by
  unfold QhPlus
  infer_instance

/-- The functor of Definition 6 is the restriction of `Qh`: composing `QhPlus` with the
inclusion `D^+(A) ↪ D(A)` recovers `K^+(I) ↪ K(A) ⟶ D(A)`. -/
noncomputable def QhPlusCompιIso [HasDerivedCategory A] :
    QhPlus A ⋙ (derivedPlus A).ι ≅ (homotopyInjPlus A).ι ⋙ DerivedCategory.Qh :=
  (derivedPlus A).liftCompιIso _ _

-- Main Statement(s)

/-- **(Claim 1: Exactness.)** The functor of Definition 6 is exact, i.e. it is a triangulated
functor: it commutes with the shift (the `CommShift ℤ` structure on `QhPlus A`) and sends
distinguished triangles of `K^+(I)` to distinguished triangles of `D^+(A)`. -/
@[stacks 013V "(exactness)"]
theorem qhPlus_isTriangulated [HasDerivedCategory A] :
    (QhPlus A).IsTriangulated := by
  -- `QhPlus A` is the lift to the triangulated subcategory `D^+(A)` of the composite
  -- `(homotopyInjPlus A).ι ⋙ Qh`, which is a triangulated functor (`(homotopyInjPlus A).ι`
  -- is triangulated since `homotopyInjPlus A` is a triangulated subcategory, and `Qh` is
  -- triangulated).  `ObjectProperty.isTriangulated_lift` transfers exactness through the lift.
  unfold QhPlus
  exact ObjectProperty.isTriangulated_lift _ _ _

/-- **(Claim 2: Full faithfulness, the Hom-bijection form.)** For genuine
bounded-below complexes of injectives `K, L` (i.e. `injPlus A K`, `injPlus A L`), the map
`Hom_{K(A)}(Q K, Q L) → Hom_{D(A)}(Qh (Q K), Qh (Q L))` induced by `Qh` is a bijection.
This is the content of `CochainComplex.IsKInjective.Qh_map_bijective` applied to bounded-below
injective complexes, which are K-injective by `CochainComplex.isKInjective_of_injective`. -/
@[sga "4½ Etat_0 3.1.4" "(A)"]
theorem qhPlus_Qh_map_bijective [HasDerivedCategory A]
    (K L : CochainComplex A ℤ) (hL : injPlus A L) :
    Function.Bijective
      (fun f : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K ⟶
               (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L =>
        DerivedCategory.Qh.map f) := by
  -- A bounded-below complex of injectives `L` is K-injective
  -- (`CochainComplex.isKInjective_of_injective`), so Stacks 05TG
  -- (`CochainComplex.IsKInjective.Qh_map_bijective`) gives the bijection directly.
  obtain ⟨⟨n, hn⟩, hinj⟩ := hL
  have := hn
  have : ∀ (m : ℤ), Injective (L.X m) := hinj
  have : L.IsKInjective := CochainComplex.isKInjective_of_injective L n
  exact CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) L

/-- **(Claim 2': Full faithfulness, functor form.)** The functor of Definition 6 is fully
faithful. -/
@[sga "4½ Etat_0 3.1.4" "(A)"]
theorem qhPlus_fullyFaithful [HasDerivedCategory A] :
    Nonempty (QhPlus A).FullyFaithful := by
  -- It suffices that the composite `QhPlus A ⋙ (derivedPlus A).ι` is fully faithful,
  -- because `(derivedPlus A).ι` is faithful, and `Functor.FullyFaithful.ofCompFaithful` then
  -- transfers full faithfulness back to `QhPlus A`.  The composite is isomorphic (via
  -- `QhPlusCompιIso`) to `(homotopyInjPlus A).ι ⋙ Qh`, so it is fully faithful iff the latter
  -- is.  For `(homotopyInjPlus A).ι ⋙ Qh`, full faithfulness is the per-Hom bijectivity
  -- (`Functor.FullyFaithful.nonempty_iff_map_bijective`): its action on a Hom is
  -- `Qh.map ∘ ι.map`; `ι.map` is bijective (full+faithful inclusion) and `Qh.map` is bijective
  -- on these injective complexes by `qhPlus_Qh_map_bijective`.
  have hcomp : Nonempty ((homotopyInjPlus A).ι ⋙ DerivedCategory.Qh).FullyFaithful := by
    rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
    rintro ⟨X, hX⟩ ⟨Y, hY⟩
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    have hLinj : injPlus A L := (homotopyInjPlus_quotient_obj_iff A L).mp hY
    have hbij := qhPlus_Qh_map_bijective A K L hLinj
    have hι : Function.Bijective ((homotopyInjPlus A).ι.map :
        ((⟨_, hX⟩ : (homotopyInjPlus A).FullSubcategory) ⟶ ⟨_, hY⟩) → _) :=
      ((homotopyInjPlus A).fullyFaithfulι).map_bijective _ _
    have heq : ((homotopyInjPlus A).ι ⋙ DerivedCategory.Qh).map =
        (fun g => DerivedCategory.Qh.map g) ∘
          ((homotopyInjPlus A).ι.map :
            ((⟨_, hX⟩ : (homotopyInjPlus A).FullSubcategory) ⟶ ⟨_, hY⟩) → _) := rfl
    rw [heq]
    exact hbij.comp hι
  obtain ⟨hcomp⟩ := hcomp
  exact ⟨(hcomp.ofIso (QhPlusCompιIso A).symm).ofCompFaithful⟩

/-- **(Analytic kernel of Claim 3 = Stacks 013K, the injective resolution of a complex.)**
Every bounded-below cochain complex `P` (with `[P.IsStrictlyGE n]`) over an abelian category
with enough injectives admits a quasi-isomorphism `ι : P ⟶ I` into a genuine bounded-below
complex of injectives `I` (i.e. `injPlus A I`).

This is the one genuinely analytic input of the whole theorem (Stacks 013K, "every
bounded-below complex has an injective resolution").  It is realized in Mathlib by the
model-category factorization on `CochainComplex.Plus A`:

* Relax the bound on `P` to `n - 1` (so `P.IsStrictlyGE ((n-1)+1)`), pick a genuine zero
  object `Z` of `CochainComplex A ℤ` (also `IsStrictlyGE (n-1)`), and apply
  `CochainComplex.Plus.modelCategoryQuillen.cm5a` to the canonical map `hZ.from_ P : P ⟶ Z`.
  This factorization yields a bounded-below complex `I` (`I.IsStrictlyGE (n-1)`), together
  with a monomorphism quasi-isomorphism `ι : P ⟶ I` and a fibration `π : I ⟶ Z` which is
  `degreewiseEpiWithInjectiveKernel` and satisfies `ι ≫ π = hZ.from_ P`.
* `I.IsStrictlyGE (n-1)` gives the boundedness half of `injPlus A I`.
* For the injectivity half: at each degree `i`, `degreewiseEpiWithInjectiveKernel π` says
  `π.f i : I.X i ⟶ Z.X i` is an epi with injective kernel.  Since `Z.X i` is a zero object
  (`hZ`), `π.f i` is the zero map, whose kernel is all of `I.X i`; hence `I.X i` is the
  (injective) kernel, i.e. `Injective (I.X i)`.  The degreewise extraction unfolds
  `degreewiseEpiWithInjectiveKernel π i`, uses that the target `Z.X i` is zero to identify
  the kernel of `π.f i` with `I.X i`, and reads off injectivity of the kernel object. -/
@[sga "2 VIII 1.4" "more general",
  sga "4½ Etat_0 3.1.9" "special case",
  sga "4½ Etat_0 3.2.3" "Clause 4",
  sga "4½ Etat_0 4.2.3.1" "Corollary 1",
  sga "4½ Etat_0 4.2.3.2" "(2)"]
theorem exists_injPlus_quasiIso [EnoughInjectives A] (P : CochainComplex A ℤ) (n : ℤ)
    [P.IsStrictlyGE n] :
    ∃ (I : CochainComplex A ℤ) (ι : P ⟶ I), injPlus A I ∧ QuasiIso ι := by
  have : P.IsStrictlyGE ((n - 1) + 1) := by
    rw [sub_add_cancel]
    infer_instance
  -- Choose a genuine zero object `Z` of `CochainComplex A ℤ` and factor `P ⟶ Z` by `cm5a`.
  obtain ⟨Z, hZ⟩ := (inferInstance : HasZeroObject (CochainComplex A ℤ))
  have hZi (i : ℤ) : IsZero (Z.X i) :=
    Functor.map_isZero (HomologicalComplex.eval A (ComplexShape.up ℤ) i) hZ
  have : Z.IsStrictlyGE (n - 1) := (CochainComplex.isStrictlyGE_iff _ _).2 fun i _ ↦ hZi i
  obtain ⟨I, hI, ι, π, hmono, hqι, hπ, hcomp⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.cm5a (hZ.from_ P) (n - 1)
  have := hI
  refine ⟨I, ι, ⟨⟨n - 1, hI⟩, ?_⟩, hqι⟩
  -- Each `π.f i : I.X i ⟶ Z.X i` is `epiWithInjectiveKernel`; with `Z.X i` a zero object the
  -- kernel of `π.f i` is all of `I.X i`, forcing `Injective (I.X i)`.
  -- SANITY CHECK PASSED
  -- `Z` is a zero object, so each `π.f i : I.X i ⟶ Z.X i` is the zero map; its kernel is
  -- `I.X i` itself (`kernelZeroIsoSource`).  The `epiWithInjectiveKernel` datum gives
  -- `Injective (kernel (π.f i))`, which transports to `Injective (I.X i)`.
  intro i
  have hker : Injective (kernel (π.f i)) := (hπ i).2
  have hf : π.f i = 0 := (hZi i).eq_zero_of_tgt _
  rw [hf] at hker
  exact Injective.of_iso kernelZeroIsoSource hker

/-- **(Claim 3: Essential surjectivity, the injective-resolution form.)** Every
object `M` of `D^+(A)` is isomorphic in `D(A)` to `Qh (Q K)` for some *genuine* bounded-below
complex of injectives `K` (i.e. `injPlus A K`); equivalently, every bounded-below object of
the derived category admits an injective resolution.  (Source input: Stacks 013K.) -/
@[sga "4½ Etat_0 3.1.4" "(A)"]
theorem qhPlus_exists_injective_resolution [EnoughInjectives A] [HasDerivedCategory A]
    (M : DPlus A) :
    ∃ (K : CochainComplex A ℤ), injPlus A K ∧
      Nonempty ((derivedPlus A).ι.obj M ≅
        DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) := by
  -- `M` is bounded below: `(derivedPlus A) M.obj`, i.e. `∃ a, M.obj.IsGE a`.
  obtain ⟨n, hn⟩ := M.2
  -- Step 1 (reduce to a complex): by `exists_iso_Q_obj_of_isGE`, `M.obj ≅ Q.obj P` for some
  -- bounded-below complex `P` (`P.IsStrictlyGE n`).
  obtain ⟨P, hP, ⟨eP⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE (M.1) n
  have := hP
  -- Step 2 (analytic kernel = 013K): resolve `P` by a bounded-below complex of injectives,
  -- a quasi-iso `ι : P ⟶ I` with `injPlus A I`.
  obtain ⟨I, ι, hI, hqι⟩ := exists_injPlus_quasiIso A P n
  refine ⟨I, hI, ⟨?_⟩⟩
  -- Step 3: the quasi-iso `ι` becomes an iso `Q.obj P ≅ Q.obj I` in `D(A)`.
  have : IsIso (DerivedCategory.Q.map ι) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso A ι).mpr hqι
  -- Step 4: `Q.obj I ≅ Qh.obj (quotient.obj I)` via `quotientCompQhIso`. Assemble
  -- `M.obj ≅ Q.obj P ≅ Q.obj I ≅ Qh.obj (quotient.obj I)`.
  exact eP ≪≫ asIso (DerivedCategory.Q.map ι) ≪≫ (DerivedCategory.quotientCompQhIso A).symm.app I

/-- **(Claim 3': Essential surjectivity, functor form.)** The functor of Definition 6 is
essentially surjective. -/
@[sga "4½ Etat_0 3.1.4" "(A)"]
theorem qhPlus_essSurj [EnoughInjectives A] [HasDerivedCategory A] :
    (QhPlus A).EssSurj := by
  -- For `M : D^+(A)`, take its injective resolution `K` from
  -- `qhPlus_exists_injective_resolution`; then `X := Q K` is an object of `K^+(I)` whose
  -- image `QhPlus A |>.obj X` agrees with `Qh.obj (Q K)` after the inclusion to `D(A)`.  The
  -- iso `e : (derivedPlus A).ι.obj M ≅ Qh.obj (Q K)` reflects (through the fully faithful
  -- inclusion `(derivedPlus A).ι`) to an iso `QhPlus A |>.obj X ≅ M`.
  refine ⟨fun M ↦ ?_⟩
  obtain ⟨K, hK, ⟨e⟩⟩ := qhPlus_exists_injective_resolution A M
  exact ⟨⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K,
    (homotopyInjPlus_quotient_obj_iff A K).mpr hK⟩,
    ⟨(derivedPlus A).fullyFaithfulι.preimageIso ((QhPlusCompιIso A).app _ ≪≫ e.symm)⟩⟩

/-- **(Main theorem, Stacks 013V.)** The canonical functor `K^+(I) → D^+(A)` of Definition 6
is an equivalence of categories.  Combined with exactness (`qhPlus_isTriangulated`) this
exhibits it as an equivalence of triangulated categories. -/
@[stacks 013V, sga "4½ Etat_0 3.1.4" "the equivalence"]
theorem qhPlus_isEquivalence [EnoughInjectives A] [HasDerivedCategory A] :
    (QhPlus A).IsEquivalence := by
  -- Assemble the equivalence from full faithfulness (`qhPlus_fullyFaithful`) and essential
  -- surjectivity (`qhPlus_essSurj`): the `Functor.IsEquivalence` class is exactly
  -- `faithful ∧ full ∧ essSurj`.
  obtain ⟨hff⟩ := qhPlus_fullyFaithful A
  exact { faithful := hff.faithful, full := hff.full, essSurj := qhPlus_essSurj A }

end

end

section

/-!
# The right derived functor is computed by a resolution functor

Let `C` be an abelian category with enough injectives, `ℐ = InjectiveObject C` its strictly full
additive subcategory of injective objects, and `F : C ⥤ D` an additive functor into an abelian
category. Write `ι : K⁺(ℐ) ⥤ K⁺(C)` for the inclusion and `Q : K⁺(C) ⥤ D⁺(C)` for the localization
at the quasi-isomorphisms. Let `j' : D⁺(C) ⥤ K⁺(ℐ)` be a section up to isomorphism of the canonical
functor `ι ⋙ Q : K⁺(ℐ) ⥤ D⁺(C)`, i.e. the descent of a resolution functor, with
`ε : j' ⋙ ι ⋙ Q ≅ 𝟭 D⁺(C)`. Then the triangle `D⁺(C) ⥤ K⁺(ℐ) ⥤ D⁺(D)`, `RF` is `2`-commutative:
`RF K ≅ F(j' K)`.

The argument is the source's. The unit `F(K) ⟶ RF(Q K)` of the right derived functor is invertible
whenever `K` is a bounded below complex of injectives, because such a `K` computes `RF`; so the
unit whiskered along `ι` is an isomorphism `ι ⋙ F ⋙ Q ≅ ι ⋙ Q ⋙ RF` of functors `K⁺(ℐ) ⥤ D⁺(D)`.
Whiskering it with `j'` on the left and composing with `ε` whiskered by `RF` on the right gives
`j' ⋙ ι ⋙ F ⋙ Q ≅ j' ⋙ ι ⋙ Q ⋙ RF ≅ 𝟭 ⋙ RF = RF`, and its component at `X` is by construction
the unit at `ι (j' X)` followed by `RF (ε.hom.app X)`.

## Main results

* `CategoryTheory.Functor.exists_iso_rightDerivedFunctorPlus_of_comp_Qh_iso_id`: the right derived
  functor `RF` of `F` is isomorphic to `j'` followed by `F` applied degreewise on complexes of
  injectives, by the isomorphism whose component at `X` is the unit of `RF` at `ι (j' X)` followed
  by `RF (ε.hom.app X)`.

## Implementation notes

`rightDerivedFunctorPlusUnitIsoOfInjective` records the one input of the proof: the unit
`F.rightDerivedFunctorPlusUnit`, restricted along `ι`, is a natural isomorphism. It is stated on
`K⁺(ℐ)` rather than after precomposition with `j'`, which is where it is true for a reason and
where its naturality is that of the unit itself; the statement's isomorphism is then two
whiskerings of it, so no naturality square is verified by hand and the pinning of the components
holds by `rfl`.

Invertibility of each component is Mathlib's instance for the injective derivability structure,
which fires at the spelling `(HomotopyCategory.Plus.localizerMorphism C).functor` of `ι` used here;
[Stacks, Tag 05TH] is that fact, and it is not needed as a hypothesis. Neither is a resolution
functor in the sense of [Stacks, Tag 013W]: only `ε` is used, and it is `e.unitIso.symm` for the
equivalence `e` of [Stacks, Tag 05TK], whose `inverse` is `ι ⋙ Q` on the nose. So no statement of
[Stacks, Tags 013W, 05TH, 05TK] is used: those three enter the argument through the hypothesis
`(j', ε)` and through the instance above, not through a cited lemma.

## References

* [Stacks, Tag 05TN]; the resolution functor is [Stacks, Tag 013W], its descent
  [Stacks, Tag 05TK], and the invertibility of the unit on bounded below complexes of injectives
  [Stacks, Tag 05TH].
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

/-- The unit `F(K) ⟶ RF(Q K)` of the right derived functor of an additive functor `F : C ⥤ D`,
restricted to bounded below complexes of injectives, is a natural isomorphism
`ι ⋙ F ⋙ Q ≅ ι ⋙ Q ⋙ RF` of functors `K⁺(ℐ) ⥤ D⁺(D)`: its components are invertible because a
bounded below complex of injectives computes `RF` ([Stacks, Tag 05TH]), and its naturality is that
of `F.rightDerivedFunctorPlusUnith`. -/
private noncomputable def rightDerivedFunctorPlusUnitIsoOfInjective
    (F : C ⥤ D) [F.Additive] [EnoughInjectives C] :
    (HomotopyCategory.Plus.localizerMorphism C).functor ⋙
        F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      (HomotopyCategory.Plus.localizerMorphism C).functor ⋙
        DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus :=
  NatIso.ofComponents
    (fun K => asIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.localizerMorphism C).functor.obj K)))
    (fun _ => F.rightDerivedFunctorPlusUnith.naturality _)

/-- Let `F : C ⥤ D` be an additive functor between abelian categories with `C` having enough
injectives, let `ℐ ⊆ C` be the subcategory of injective objects, and let
`j' : D⁺(C) ⥤ K⁺(ℐ)` be a section up to isomorphism of the canonical functor
`K⁺(ℐ) ⥤ D⁺(C)`, i.e. the descent of a resolution functor
([Stacks, Tags 013W, 05TK]). Then the right derived functor `RF` of `F` is computed by
`F ∘ j'`: the triangle `D⁺(C) ⥤ K⁺(ℐ) ⥤ D⁺(D)`, `RF` is `2`-commutative, by the
`2`-isomorphism whose value at `X` is the unit of `RF` at the complex of injectives `j' X`
followed by `RF` applied to `ε.hom.app X`. -/
@[stacks 05TN]
public theorem exists_iso_rightDerivedFunctorPlus_of_comp_Qh_iso_id
    (F : C ⥤ D) [F.Additive] [EnoughInjectives C]
    (j' : DerivedCategory.Plus C ⥤ HomotopyCategory.Plus (InjectiveObject C))
    (ε : j' ⋙ (HomotopyCategory.Plus.localizerMorphism C).functor ⋙ DerivedCategory.Plus.Qh ≅
      𝟭 (DerivedCategory.Plus C)) :
    ∃ e : j' ⋙ (HomotopyCategory.Plus.localizerMorphism C).functor ⋙
        F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅ F.rightDerivedFunctorPlus,
      ∀ X, e.hom.app X = F.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.localizerMorphism C).functor.obj (j'.obj X)) ≫
          F.rightDerivedFunctorPlus.map (ε.hom.app X) :=
  ⟨Functor.isoWhiskerLeft j' (rightDerivedFunctorPlusUnitIsoOfInjective F) ≪≫
    Functor.isoWhiskerRight ε F.rightDerivedFunctorPlus, fun _ => rfl⟩

end CategoryTheory.Functor

end

end
