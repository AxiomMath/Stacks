module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Extensions and the first Ext group

Isomorphism classes of short exact sequences with fixed end terms are canonically identified
with the first derived `Ext` group. The identification is additive for Baer sums, natural in
both end terms, and it matches the connecting maps of the two long exact `Ext` sequences with
the pushout and pullback operations on extensions, and these compatibilities determine it
uniquely.

## Main definitions

* `CategoryTheory.Abelian.YonedaExtOne`: degree-one Yoneda extensions modulo equivalence.
* `CategoryTheory.Abelian.shortExactExtensionClass`: the class of a short exact sequence.
* `CategoryTheory.Abelian.ExtOneComparison`: a comparison equivalence with derived `Ext¹`
  together with the maps on classes induced by pushout and pullback.
* `CategoryTheory.Abelian.yonedaCovariantBoundary`,
  `CategoryTheory.Abelian.yonedaContravariantBoundary`: the boundary maps of the Yoneda
  six-term sequences.
* `CategoryTheory.Abelian.IsCanonicalExtOneComparison`: the properties — canonicity,
  additivity, naturality, and compatibility with connecting maps — that characterise the
  comparison.
* `CategoryTheory.Abelian.comparisonEquiv`, `CategoryTheory.Abelian.comparison`: the comparison
  itself, induced by the degree-one class map.

## Main results

* `CategoryTheory.Abelian.isCanonicalExtOneComparison_comparison`: the comparison has those
  properties.
* `CategoryTheory.Abelian.eq_comparison_of_isCanonical`: it is the only one that has them; the
  two are bundled as `CategoryTheory.Abelian.existsUnique_yonedaExtOneEquiv_ext`.

## References

* [Stacks Project, Tag 0AUL](https://stacks.math.columbia.edu/tag/0AUL)
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Abelian

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- The setoid of degree-one Yoneda extensions under equivalence of extensions. -/
def yonedaExtOneSetoid (B A : C) : Setoid (YonedaExtension B A 0) where
  r := YonedaExtension.Equivalent
  iseqv :=
    ⟨fun E => equivalent_of_extClassMap_eq E E rfl,
      fun h => equivalent_of_extClassMap_eq _ _ (extClassMap_eq_of_equivalent h).symm,
      fun h h' => equivalent_of_extClassMap_eq _ _
        ((extClassMap_eq_of_equivalent h).trans (extClassMap_eq_of_equivalent h'))⟩

/-- Isomorphism classes of short exact sequences `0 → A → E → B → 0`, presented as
degree-one Yoneda extensions. -/
abbrev YonedaExtOne (B A : C) := _root_.Quotient (yonedaExtOneSetoid B A)

/-- A short exact sequence regarded as a degree-one Yoneda extension. -/
def shortExactYonedaExtension {S : ShortComplex C} (hS : S.ShortExact) :
    YonedaExtension S.X₃ S.X₁ 0 where
  Z := ComposableArrows.mk₀ S.X₂
  f := S.f
  g := S.g
  mono_f := hS.mono_f
  exact := ComposableArrows.exact₁ _
  exact_g := hS.exact.exact_toComposableArrows
  epi_g := hS.epi_g

/-- The Yoneda extension class represented by a short exact sequence. -/
noncomputable def shortExactExtensionClass {S : ShortComplex C} (hS : S.ShortExact) :
    YonedaExtOne S.X₃ S.X₁ :=
  _root_.Quotient.mk _ (shortExactYonedaExtension hS)

/-- The canonical comparison data: an equivalence from Yoneda extension classes to derived
`Ext¹`, together with the maps on Yoneda classes induced by pushout in the second variable and
pullback in the first variable. -/
structure ExtOneComparison where
  /-- The comparison between Yoneda extension classes and derived `Ext¹`. -/
  equiv (B A : C) : YonedaExtOne B A ≃ Ext.{w} B A 1
  /-- The map induced by pushing out an extension along a map of its extended objects. -/
  covariantMap {A A' B : C} (a : A ⟶ A') : YonedaExtOne B A → YonedaExtOne B A'
  /-- The map induced by pulling back an extension along a map of its quotient objects. -/
  contravariantMap {A B B' : C} (b : B' ⟶ B) : YonedaExtOne B A → YonedaExtOne B' A

/-- The Yoneda boundary `Hom(X, M₃) → Ext(X, M₁)` attached to a short exact sequence
`0 → M₁ → M₂ → M₃ → 0`: pull the sequence back along the given morphism. -/
noncomputable def yonedaCovariantBoundary
    (c : ExtOneComparison (C := C))
    {S : ShortComplex C} (hS : S.ShortExact) (X : C) (u : X ⟶ S.X₃) :
    YonedaExtOne X S.X₁ :=
  c.contravariantMap u (shortExactExtensionClass hS)

/-- The Yoneda boundary `Hom(M₁, Y) → Ext(M₃, Y)` attached to a short exact sequence
`0 → M₁ → M₂ → M₃ → 0`: push the sequence out along the given morphism. -/
noncomputable def yonedaContravariantBoundary
    (c : ExtOneComparison (C := C))
    {S : ShortComplex C} (hS : S.ShortExact) (Y : C) (u : S.X₁ ⟶ Y) :
    YonedaExtOne S.X₃ Y :=
  c.covariantMap u (shortExactExtensionClass hS)

/-- Properties characterizing the canonical comparison from Yoneda extensions to derived
`Ext¹`. Besides its value on a representative, these record additivity for Baer sums,
naturality in each end term, and agreement with both connecting maps in the long exact
sequences. -/
structure IsCanonicalExtOneComparison (c : ExtOneComparison (C := C)) : Prop where
  /-- The comparison sends a short exact sequence to its derived extension class. -/
  class_eq : ∀ {S : ShortComplex C} (hS : S.ShortExact),
    c.equiv S.X₃ S.X₁ (shortExactExtensionClass hS) = hS.extClass
  /-- The covariant map is represented by pushout of short exact sequences. -/
  covariant_map_eq_pushout : ∀ {A A' B E E' : C}
      {i : A ⟶ E} {p : E ⟶ B} {z : i ≫ p = 0}
      {i' : A' ⟶ E'} {p' : E' ⟶ B} {z' : i' ≫ p' = 0}
      (h : (ShortComplex.mk i p z).ShortExact)
      (h' : (ShortComplex.mk i' p' z').ShortExact) (a : A ⟶ A') (v : E ⟶ E'),
    IsPushout i a v i' → v ≫ p' = p →
      c.covariantMap a (shortExactExtensionClass h) =
        shortExactExtensionClass h'
  /-- The contravariant map is represented by pullback of short exact sequences. -/
  contravariant_map_eq_pullback : ∀ {A B B' E E' : C}
      {i : A ⟶ E} {p : E ⟶ B} {z : i ≫ p = 0}
      {i' : A ⟶ E'} {p' : E' ⟶ B'} {z' : i' ≫ p' = 0}
      (h : (ShortComplex.mk i p z).ShortExact)
      (h' : (ShortComplex.mk i' p' z').ShortExact) (b : B' ⟶ B) (v : E' ⟶ E),
    IsPullback v p' p b → i' ≫ v = i →
      c.contravariantMap b (shortExactExtensionClass h) =
        shortExactExtensionClass h'
  /-- The comparison is natural in the covariant, extended object. -/
  covariant_naturality : ∀ {A A' B : C} (a : A ⟶ A') (x : YonedaExtOne B A),
    c.equiv B A' (c.covariantMap a x) =
      (c.equiv B A x).comp (Ext.mk₀ a) (add_zero 1)
  /-- The comparison is natural in the contravariant, quotient object. -/
  contravariant_naturality : ∀ {A B B' : C} (b : B' ⟶ B) (x : YonedaExtOne B A),
    c.equiv B' A (c.contravariantMap b x) =
      (Ext.mk₀ b).comp (c.equiv B A x) (zero_add 1)
  /-- The comparison takes a Baer sum to addition in derived `Ext¹`. -/
  map_baerSum : ∀ {A B E₁ E₂ E T : C}
      {i₁ : A ⟶ E₁} {p₁ : E₁ ⟶ B} {z₁ : i₁ ≫ p₁ = 0}
      {i₂ : A ⟶ E₂} {p₂ : E₂ ⟶ B} {z₂ : i₂ ≫ p₂ = 0}
      {i : A ⟶ E} {p : E ⟶ B} {z : i ≫ p = 0}
      {j : A ⟶ T} {q : T ⟶ B ⊞ B} {zT : j ≫ q = 0}
      (h₁ : (ShortComplex.mk i₁ p₁ z₁).ShortExact)
      (h₂ : (ShortComplex.mk i₂ p₂ z₂).ShortExact)
      (h : (ShortComplex.mk i p z).ShortExact)
      (_hT : (ShortComplex.mk j q zT).ShortExact)
      (a : E₁ ⊞ E₂ ⟶ T) (b : E ⟶ T),
    biprod.map i₁ i₂ ≫ a = biprod.desc (𝟙 A) (𝟙 A) ≫ j →
    a ≫ q = biprod.map p₁ p₂ →
    i ≫ b = j → b ≫ q = p ≫ biprod.lift (𝟙 B) (𝟙 B) →
      c.equiv B A (shortExactExtensionClass h) =
        c.equiv B A (shortExactExtensionClass h₁) +
          c.equiv B A (shortExactExtensionClass h₂)
  /-- The pullback boundary in the Yoneda six-term sequence agrees with the boundary in the
  covariant derived `Ext` long exact sequence. -/
  covariant_boundary_commutes : ∀ {S : ShortComplex C} (hS : S.ShortExact) (X : C)
      (u : X ⟶ S.X₃),
    c.equiv X S.X₁ (yonedaCovariantBoundary c hS X u) =
      hS.extClass.postcomp X rfl (Ext.mk₀ u)
  /-- The pushout boundary in the Yoneda six-term sequence agrees with the boundary in the
  contravariant derived `Ext` long exact sequence. -/
  contravariant_boundary_commutes : ∀ {S : ShortComplex C} (hS : S.ShortExact) (Y : C)
      (u : S.X₁ ⟶ Y),
    c.equiv S.X₃ Y (yonedaContravariantBoundary c hS Y u) =
      hS.extClass.precomp Y rfl (Ext.mk₀ u)

section Construction

omit [HasExt.{w} C] in
private theorem shortExactOfYoneda {B A : C} (E : YonedaExtension B A 0) :
    (ShortComplex.mk E.f E.g (comp_g_eq_zero E)).ShortExact where
  exact := (ShortComplex.exact_iff_exact_toComposableArrows _).2 E.exact_g

/-- **The comparison between isomorphism classes of extensions and derived `Ext¹`.** The class
map `CategoryTheory.Abelian.extClassMap` in degree one is surjective and identifies exactly the
equivalent extensions, so it descends to a bijection from `YonedaExtOne B A` onto
`Ext^1_𝒜(B, A)`. -/
@[sga "7 VII 3.2.5" "partial"]
noncomputable def comparisonEquiv (B A : C) :
    YonedaExtOne B A ≃ Ext.{w} B A 1 := by
  refine Equiv.ofBijective
    (_root_.Quotient.lift (extClassMap 0) fun _ _ hE => extClassMap_eq_of_equivalent hE)
    ⟨?_, ?_⟩
  · intro x y hxy
    induction x using _root_.Quotient.inductionOn with | _ E => ?_
    induction y using _root_.Quotient.inductionOn with | _ E' => ?_
    exact _root_.Quotient.sound (equivalent_of_extClassMap_eq E E' hxy)
  · intro x
    obtain ⟨E, rfl⟩ := surjective_extClassMap B A 0 x
    exact ⟨_root_.Quotient.mk _ E, rfl⟩

private lemma comparisonEquiv_mk {B A : C} (E : YonedaExtension B A 0) :
    comparisonEquiv B A (_root_.Quotient.mk _ E) = (shortExactOfYoneda E).extClass :=
  isExtClassMap_extClassMap.1 B A E (comp_g_eq_zero E) (shortExactOfYoneda E)

/-- **The canonical comparison data.** Its equivalence is `comparisonEquiv`, and its covariant
and contravariant maps are Yoneda composition with `Ext.mk₀` read through that equivalence. -/
@[stacks 0AUL "the comparison itself; `isCanonicalExtOneComparison_comparison` is its defining \
properties and `eq_comparison_of_isCanonical` their uniqueness"]
noncomputable def comparison : ExtOneComparison (C := C) where
  equiv := comparisonEquiv
  covariantMap a x := (comparisonEquiv _ _).symm
    ((comparisonEquiv _ _ x).comp (Ext.mk₀ a) (add_zero 1))
  contravariantMap b x := (comparisonEquiv _ _).symm
    ((Ext.mk₀ b).comp (comparisonEquiv _ _ x) (zero_add 1))

/-- `comparisonEquiv` sends the class of a short exact sequence to its derived extension
class. -/
lemma comparisonEquiv_shortExact {S : ShortComplex C} (hS : S.ShortExact) :
    comparisonEquiv S.X₃ S.X₁ (shortExactExtensionClass hS) = hS.extClass :=
  comparisonEquiv_mk _

private lemma comparisonEquiv_covariantMap {A A' B : C} (a : A ⟶ A') (x : YonedaExtOne B A) :
    comparisonEquiv B A' (comparison.covariantMap a x) =
      (comparisonEquiv B A x).comp (Ext.mk₀ a) (add_zero 1) :=
  Equiv.apply_symm_apply _ _

private lemma comparisonEquiv_contravariantMap {A B B' : C} (b : B' ⟶ B)
    (x : YonedaExtOne B A) :
    comparisonEquiv B' A (comparison.contravariantMap b x) =
      (Ext.mk₀ b).comp (comparisonEquiv B A x) (zero_add 1) :=
  Equiv.apply_symm_apply _ _

private lemma quotient_eq_shortExact {B A : C} (E : YonedaExtension B A 0) :
    _root_.Quotient.mk (yonedaExtOneSetoid B A) E =
      shortExactExtensionClass (shortExactOfYoneda E) :=
  (comparisonEquiv B A).injective ((comparisonEquiv_mk E).trans (comparisonEquiv_shortExact _).symm)

/-- **The comparison is canonical.** `comparison` sends a short exact sequence to its derived
extension class, represents its covariant and contravariant maps by pushout and pullback of
short exact sequences, is natural in both variables, takes Baer sums to sums in `Ext¹`, and
matches the boundary maps of the two long exact `Ext` sequences. -/
@[stacks 0AUL "the comparison has the announced properties: canonicity, representation of \
the two maps by pushout and pullback, naturality in both variables, additivity for Baer sums, \
and agreement with both connecting maps",
  ega "0 12.3.2" "more general",
  sga "7 VII 3.4" "special case"]
theorem isCanonicalExtOneComparison_comparison :
    IsCanonicalExtOneComparison (comparison (C := C)) := by
  constructor
  · exact comparisonEquiv_shortExact
  · intro A A' B E E' i p z i' p' z' h h' a v hp hv
    apply (comparisonEquiv B A').injective
    rw [comparisonEquiv_covariantMap, comparisonEquiv_shortExact (S := ShortComplex.mk i p z) h,
      comparisonEquiv_shortExact (S := ShortComplex.mk i' p' z') h']
    simpa using h.extClass_naturality h'
      { τ₁ := a, τ₂ := v, τ₃ := 𝟙 B, comm₁₂ := hp.w.symm, comm₂₃ := by simpa using hv }
  · intro A B B' E E' i p z i' p' z' h h' b v hp hv
    apply (comparisonEquiv B' A).injective
    rw [comparisonEquiv_contravariantMap,
      comparisonEquiv_shortExact (S := ShortComplex.mk i p z) h,
      comparisonEquiv_shortExact (S := ShortComplex.mk i' p' z') h']
    simpa using (h'.extClass_naturality h
      { τ₁ := 𝟙 A, τ₂ := v, τ₃ := b, comm₁₂ := by simpa using hv.symm, comm₂₃ := hp.w }).symm
  · exact comparisonEquiv_covariantMap
  · exact comparisonEquiv_contravariantMap
  · intro A B E₁ E₂ E T i₁ p₁ z₁ i₂ p₂ z₂ i p z j q zT h₁ h₂ h hT a b ha ha' hb hb'
    dsimp only [comparison]
    calc
      comparisonEquiv B A (shortExactExtensionClass h) = h.extClass :=
        comparisonEquiv_shortExact h
      _ = h₁.extClass + h₂.extClass :=
        (Ext.extClass_surjective_and_eq_iff_iso_and_baerSum C B A).2.2
          E₁ E₂ E T i₁ p₁ z₁ i₂ p₂ z₂ i p z j q zT h₁ h₂ h hT a b ha ha' hb hb'
      _ = comparisonEquiv B A (shortExactExtensionClass h₁) +
          comparisonEquiv B A (shortExactExtensionClass h₂) := by
        rw [comparisonEquiv_shortExact (S := ShortComplex.mk i₁ p₁ z₁) h₁,
          comparisonEquiv_shortExact (S := ShortComplex.mk i₂ p₂ z₂) h₂]
  · intro S hS X u
    exact (comparisonEquiv_contravariantMap _ _).trans (by rw [comparisonEquiv_shortExact]; rfl)
  · intro S hS Y u
    exact (comparisonEquiv_covariantMap _ _).trans (by rw [comparisonEquiv_shortExact]; rfl)

/-- **The canonical comparison is unique.** Any comparison with the properties of
`IsCanonicalExtOneComparison` is `comparison`. -/
@[stacks 0AUL "uniqueness of the canonical comparison"]
theorem eq_comparison_of_isCanonical (c' : ExtOneComparison (C := C))
    (hc' : IsCanonicalExtOneComparison c') : c' = comparison := by
  have hequiv : c'.equiv = (comparison (C := C)).equiv := by
    funext B A
    ext x
    induction x using _root_.Quotient.inductionOn with | _ E => ?_
    rw [quotient_eq_shortExact E]
    exact (hc'.class_eq (shortExactOfYoneda E)).trans
      (comparisonEquiv_shortExact (shortExactOfYoneda E)).symm
  cases c' with
  | mk equiv' covariantMap' contravariantMap' =>
    dsimp only [comparison] at hequiv ⊢
    cases hequiv
    congr
    · funext A A' B a x
      exact (comparisonEquiv B A').injective
        ((hc'.covariant_naturality a x).trans (comparisonEquiv_covariantMap a x).symm)
    · funext A B B' b x
      exact (comparisonEquiv B' A).injective
        ((hc'.contravariant_naturality b x).trans (comparisonEquiv_contravariantMap b x).symm)

/-- **Stacks 0AUL.** There is exactly one comparison between isomorphism classes of extensions
and derived `Ext¹` that sends a short exact sequence to its extension class, represents the
covariant and contravariant maps by pushout and pullback, is natural in both variables, takes
Baer sums to sums, and matches the boundary maps of the two long exact sequences. -/
@[ega "0 12.3.2" "more general", sga "7 VII 3.4" "special case"]
theorem existsUnique_yonedaExtOneEquiv_ext (C : Type u) [Category.{v} C] [Abelian C]
    [HasExt.{w} C] :
    ∃! c : ExtOneComparison (C := C), IsCanonicalExtOneComparison c :=
  ⟨comparison, isCanonicalExtOneComparison_comparison, eq_comparison_of_isCanonical⟩

end Construction

end CategoryTheory.Abelian

end
