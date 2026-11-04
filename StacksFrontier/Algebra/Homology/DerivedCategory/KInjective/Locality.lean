module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt
import StacksCore.Tactic.EgaSgaAttribute

/-!
# K-injective complexes

Let `A` be an abelian category, `K(A)` the homotopy category of `ℤ`-indexed cochain complexes in
`A` and `Qis(A)` the class of quasi-isomorphisms of `K(A)`, so that `D(A)` is the localization of
`K(A)` at `Qis(A)`. Let `F : K(A) ⥤ H` be a functor.

For an object `X` of `K(A)` the right derived functor `RF` is *defined at* `X` when the ind-object
$$ X/Qis(A) ⟶ H, \quad (s : X ⟶ X') ⟼ F(X') $$
is essentially constant, its value being `RF(X)`; this is the notion of Tag 05S9, transcribed as
`CategoryTheory.Functor.IsRightDerivedValueAt`. The object `X` *computes* `RF` (Tag 05SX) when
moreover the canonical map `F(X) ⟶ RF(X)` — the coprojection of the value cocone at the index
`𝟙 X`, which lies in `Qis(A)` — is an isomorphism.

This file proves two things about K-injective complexes. First, a K-injective complex `I`
computes `RF`, and `RF` is defined at every object of `K(A)` admitting a quasi-isomorphism to or
from `I`: every quasi-isomorphism `I ⟶ N` of `K(A)` has a unique left inverse (Tag 070I), so
`𝟙 I` is a terminal object of `I/Qis(A)`, the ind-object above is therefore essentially constant
with value `F(I)`, and the canonical map is an isomorphism. Second, if *every* complex admits a
quasi-isomorphism towards a K-injective complex, then every functor `F : K(A) ⥤ H` has a right
derived functor
$$ RF : D(A) ⟶ H, $$
i.e. `F` admits a left Kan extension along the localization functor `K(A) ⥤ D(A)`, and this
extension is pointwise: `RF` is defined at every object of `K(A)`. Moreover a K-injective complex
computes `RF`: the canonical map `F(I) ⟶ RF(I)` — the component at `I` of the unit of the Kan
extension — is an isomorphism, which is the source's `RF(I^∙) = F(I^∙)`.

Both proofs are one statement about a single object of an index category. Being K-injective says
that the image of `I` in `K(A)` is right orthogonal to the acyclic complexes
(`CochainComplex.isKInjective_iff_rightOrthogonal`), the acyclic complexes form a triangulated
subcategory whose associated class of morphisms is the quasi-isomorphisms
(`HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic`), and right orthogonality to a
triangulated subcategory *is* locality for that class of morphisms
(`CategoryTheory.ObjectProperty.isLocal_trW`): precomposition with a quasi-isomorphism is
bijective on morphisms into `I`. Hence for a quasi-isomorphism `s : X ⟶ I` of `K(A)` and any
other quasi-isomorphism `t : X ⟶ N` there is a *unique* `f : N ⟶ I` with `t ≫ f = s`, that is,
`s` is a terminal object of the index category `X/Qis(A)`; the ind-object is therefore
essentially constant with value `F(I)`, the value cocone being the one a terminal index induces
(`CategoryTheory.Limits.coconeOfDiagramTerminal`), and its coprojection at that index is an
identity. For the first assertion take `X = I` and `s = 𝟙`, which is the source's "`𝟙 I` is a
final object of `I/Qis(A)`". For the second, a quasi-isomorphism `X ⟶ I` is what the first case
of the hypothesis provides directly, while a quasi-isomorphism `s : I ⟶ X` admits a left inverse
`g : X ⟶ I` — locality of `I` again, applied to `s` — and `g` is a quasi-isomorphism because the
quasi-isomorphisms of a homotopy category have the two-out-of-three property. So the source's
appeal to Tag 05SB, the invariance of definedness along a quasi-isomorphism, is not needed: both
directions of "quasi-isomorphic to `I`" yield a quasi-isomorphism *to* `I`
(`exists_mem_hom_to_of_isLocal`), and the same terminal object serves.

In the Kan extension picture the same input about `I` says that
`L : Hom_{K(A)}(X, I) ⟶ Hom_D(L X, L I)` is bijective for *any* localization functor
`L : K(A) ⥤ D` for `Qis(A)`, by
`CategoryTheory.ObjectProperty.rightOrthogonal.map_bijective_of_isTriangulated`. Bijectivity says
exactly that `𝟙 (L I)` is a terminal object of the index category `CostructuredArrow L (L I)`, so
the colimit defining the pointwise left Kan extension at `L I` exists and is its value at that
terminal object; hence `F` has a pointwise right derived functor at `I`, and the coprojection at
the terminal index — the canonical map `F(I) ⟶ RF(I)` — is an isomorphism. The resolution
hypothesis propagates definedness from the K-injective complexes to all of `K(A)`, definedness
being invariant along quasi-isomorphisms.

This route replaces the source's appeal to the general criterion for right derivability (Tag
06XN) with `𝓘` the K-injective complexes: that criterion produces the value of `RF` as an
essentially constant ind-object over the filtered category `X/Qis(A)`, whereas for a K-injective
`I` the relevant index category has a terminal object outright, so no filteredness, no calculus
of fractions and no saturation of `Qis(A)` are needed. Condition (2) of Tag 06XN — that `F`
inverts a quasi-isomorphism between K-injective complexes — is subsumed: such a morphism is an
isomorphism of `K(A)` by Tag 070I.

## Main results

* `CategoryTheory.Functor.exists_isRightDerivedValueAt_and_isIso_of_isKInjective`: for a
  K-injective complex `I`, the object `(HomotopyCategory.quotient A _).obj I` of `K(A)` computes
  `RF`, and `RF` is defined at every object of `K(A)` admitting a quasi-isomorphism to or from
  it.
* `Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective`, in the
  `CategoryTheory` namespace:
  if every complex admits a quasi-isomorphism towards a K-injective complex, then any
  `F : K(A) ⥤ H` has a pointwise right derived functor with respect to `Qis(A)`, and for every
  localization functor `L` for `Qis(A)`, every right derived functor `(RF, α)` of `F` and every
  K-injective complex `I`, the canonical map `α.app I : F(I) ⟶ RF(I)` is an isomorphism.

## Implementation notes

*Which notion of right derived functor.* Two conditions occur here, and they are inequivalent; no
bridge between them is claimed. Tag 070Y uses the source's notion of definedness — essential
constancy of the ind-object on `X/Qis(A)`, i.e.
`CategoryTheory.Functor.IsRightDerivedValueAt` — and not Mathlib's
`CategoryTheory.Functor.HasPointwiseRightDerivedFunctorAt`, which asks that the colimit computing
the pointwise left Kan extension of `F` along a localization functor exist at the image of `X`.
The source's notion is what the second assertion of Tag 070Y needs: "computes `RF`" compares
`F(X)` with the value of the ind-object along the coprojection at the index `𝟙 X`, a morphism the
essentially constant ind-object carries, whereas a left Kan extension that is pointwise at a
single object provides no such comparison. The conclusion of Tag 070K, on the other hand, is the
*functor* `RF : D(A) ⥤ H`, which in the source is produced from everywhere-definedness by
Proposition 05SE; Mathlib's `Functor.IsRightDerivedFunctor α W` is exactly the defining property
of that functor — `RF` together with `α : F ⟶ L ⋙ RF` is a left Kan extension of `F` along a
localization functor `L` for `W` — and `Functor.HasRightDerivedFunctor` its existence, so that
statement is made in Mathlib's framework rather than in the source's essential-constancy
framework of Tag 05S9, in which the functor `RF` cannot be spoken of. Nothing of the source's
content is lost thereby: definedness at every object in the sense of Tag 05S9 is, under the
resolution hypothesis, already the content of Tag 070Y, every complex being quasi-isomorphic to a
K-injective one; and conversely the two conclusions of Tag 070K exhibit the value of the
ind-object at any complex as `F(I)` for `I` a K-injective resolution of it.

*Pointwise.* The first conclusion of Tag 070K is `HasPointwiseRightDerivedFunctor`, i.e. the left
Kan extension exists and is computed at each object as a colimit, and not merely
`HasRightDerivedFunctor`, which it implies by
`Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor`; this per-object form is the
one matching the source's "`RF` is defined at every object", and it is how Mathlib states the
bounded below analogue for a category with enough injectives.

*No smallness hypothesis.* `Hom`-sets of `D(A)` need not be small, so no `HasDerivedCategory A`
is assumed anywhere: `HasPointwiseRightDerivedFunctor` is phrased through the universe-bumped
localization `W.Q`, and the second conclusion of Tag 070K is stated for an *arbitrary*
localization functor `L` for `Qis(A)`, hence applies to `DerivedCategory.Qh` whenever a derived
category is chosen, and to `W.Q` always. Tag 070Y happens entirely inside `K(A)`, so Tag 070I
enters it only through the locality of `I`, which `CategoryTheory.ObjectProperty.isLocal_trW`
supplies directly; the left calculus of fractions that the transfer of definedness would use is
that of the triangulated subcategory of acyclic objects, available for every abelian `A`.

*Hypotheses on `F`.* The source works in Situation 05S8, with `F` an exact functor of
triangulated categories and `Qis(A)` a saturated multiplicative system compatible with the
triangulated structure. No conclusion below mentions shifts, triangles or additivity, and the
author's proofs use none of them, so `F : K(A) ⥤ H` is an arbitrary functor into an arbitrary
category. The class of morphisms is not a variable: it is pinned to `Qis(A)`, the source's, which
carries the multiplicativity and the left calculus of fractions used downstream as Mathlib
instances.

*Quasi-isomorphisms and the resolution hypothesis.* Both are the source's literal ones: a single
quasi-isomorphism between `X` and the K-injective complex, in either direction, for Tag 070Y, and
a quasi-isomorphism of complexes towards a K-injective complex for Tag 070K. Taking
quasi-isomorphisms in `K(A)` rather than between complexes is the same condition, since
`HomotopyCategory.quotient` is full and surjective on objects and
`HomotopyCategory.quotient_map_mem_quasiIso_iff` identifies the two classes of morphisms.

*K-injectivity.* This is Mathlib's class `CochainComplex.IsKInjective` on complexes, so a
K-injective object of `K(A)` appears as `(HomotopyCategory.quotient A _).obj I`. No generality is
lost: every object of `K(A)` is of this form, and K-injectivity is invariant under isomorphism in
`K(A)` (`CochainComplex.isKInjective_iff_of_iso`, via `HomotopyEquiv`).

*`RF(I) = F(I)`.* The source's equality is an equality of values, i.e. the assertion that the
canonical map is invertible ("`I` computes `RF`", Tag 05SX); it is rendered as `IsIso` of that
map, not as an equality of objects. The map itself is pinned rather than merely asserted to
exist: it is the coprojection of the value cocone at the index `𝟙` for Tag 070Y, and the
component `α.app ((HomotopyCategory.quotient A _).obj I)` of the unit of the Kan extension for
Tag 070K, and the assertion is that this specific morphism is invertible — for Tag 070K, for
*every* right derived functor of `F`.

*Auxiliary facts.* Four facts proved below are of general interest and are absent from Mathlib.
Mathlib's `CategoryTheory.CostructuredArrow.mkIdTerminal` produces the terminal object `𝟙 (S Y)`
of `CostructuredArrow S (S Y)` from `S` being full and faithful, which the localization
`K(A) ⥤ D(A)` is not; what the argument uses is bijectivity of `S` on morphisms *into the single
object* `Y`, and that is what `costructuredArrowMkIdTerminalOfBijective` assumes — the
Kan-extension-theoretic reading of "`Y` is local for the morphisms inverted by `S`". Dually,
`isTerminalUnderMk` says that a morphism of `W` whose target is `W`-local is a terminal object of
the category of `W`-morphisms under its source. The coprojection at a terminal index of the
cocone that this index induces is the identity (`coconeOfDiagramTerminal_ι_app_self`), which is
the whole of essential constancy at a terminal index. Finally, the quasi-isomorphisms of the
homotopy category of complexes of any shape have the two-out-of-three property
(`hasTwoOutOfThreeProperty_quasiIso`).

## References

* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K); the criterion the source
  applies is Tag 06XN, the splitting of quasi-isomorphisms out of a K-injective complex is
  Tag 070I, "defined at" and "computes" are Tags 05S9 and 05SX, "right derivable" is Tag 05SV and
  the functor on the localization is Tag 05SW.
* [Stacks Project, Tag 070Y](https://stacks.math.columbia.edu/tag/070Y); "defined at" is
  Tag 05S9, "computes" is Tag 05SX, the splitting of a quasi-isomorphism out of a K-injective
  complex is Tag 070I, and the invariance of definedness along a quasi-isomorphism is Tag 05SB.

## Tags

K-injective complex, right derived functor, derived category, homotopy category, quasi-isomorphism
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

/-! ### Terminal indices and locality -/

/-- The coprojection, at a terminal index, of the cocone that this index induces on a diagram is
the identity. -/
private lemma coconeOfDiagramTerminal_ι_app_self {J : Type u₁} [Category.{v₁} J] {H : Type u₂}
    [Category.{v₂} H] {t : J} (h : IsTerminal t) (G : J ⥤ H) :
    (coconeOfDiagramTerminal h G).ι.app t = 𝟙 (coconeOfDiagramTerminal h G).pt := by
  simp

/-- If a functor `S : C ⥤ D` is bijective on morphisms into a fixed object `Y : C`, then
`𝟙 (S.obj Y)` is a terminal object of `CostructuredArrow S (S.obj Y)`. This is
`CategoryTheory.CostructuredArrow.mkIdTerminal` with the full-and-faithful hypothesis on `S`
weakened to bijectivity at the single object `Y`. -/
private noncomputable def costructuredArrowMkIdTerminalOfBijective {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (S : C ⥤ D) {Y : C}
    (hS : ∀ X : C, Function.Bijective (S.map : (X ⟶ Y) → (S.obj X ⟶ S.obj Y))) :
    IsTerminal (CostructuredArrow.mk (𝟙 (S.obj Y))) :=
  IsTerminal.ofUniqueHom
    (fun c ↦ CostructuredArrow.homMk ((hS c.left).surjective c.hom).choose (by
      simp [((hS c.left).surjective c.hom).choose_spec]))
    (fun c m ↦ by
      ext
      simp only [CostructuredArrow.homMk_left]
      refine (hS c.left).injective ?_
      rw [((hS c.left).surjective c.hom).choose_spec]
      simpa using CostructuredArrow.w m)

/-- A morphism `s : X ⟶ Y` of `W` whose target is `W`-local is a terminal object of the category
`X/W` of morphisms of `W` out of `X`: for every `t : X ⟶ N` in `W` there is a unique `f : N ⟶ Y`
with `t ≫ f = s`. -/
private noncomputable def isTerminalUnderMk {D : Type u₁} [Category.{v₁} D]
    {W : MorphismProperty D} {X Y : D} (hY : W.isLocal Y) {s : X ⟶ Y} (hs : W s) :
    IsTerminal (MorphismProperty.Under.mk (⊤ : MorphismProperty D) s hs) :=
  IsTerminal.ofUniqueHom
    (fun t => MorphismProperty.Under.homMk _ ((hY t.hom t.prop).2 s).choose_spec)
    fun t m => MorphismProperty.Under.Hom.ext ((hY t.hom t.prop).1
      ((MorphismProperty.Under.w m).trans ((hY t.hom t.prop).2 s).choose_spec.symm))

/-- A `W`-local object is reached by a morphism of `W` from every object joined to it by a
morphism of `W` in *either* direction: a morphism `s : Y ⟶ X` of `W` out of a `W`-local `Y` has a
left inverse `g` because precomposition with `s` hits `𝟙 Y`, and then `W g` follows from
`s ≫ g = 𝟙 Y` by two-out-of-three. -/
private lemma exists_mem_hom_to_of_isLocal {D : Type u₁} [Category.{v₁} D]
    {W : MorphismProperty D} [W.ContainsIdentities] [W.HasTwoOutOfThreeProperty] {X Y : D}
    (hY : W.isLocal Y) (h : (∃ s : X ⟶ Y, W s) ∨ ∃ s : Y ⟶ X, W s) : ∃ s : X ⟶ Y, W s := by
  obtain ⟨s, hs⟩ | ⟨s, hs⟩ := h
  · exact ⟨s, hs⟩
  · obtain ⟨g, hg⟩ := (hY s hs).2 (𝟙 Y)
    have hg' : s ≫ g = 𝟙 Y := hg
    exact ⟨g, MorphismProperty.of_precomp _ s g hs (hg' ▸ MorphismProperty.id_mem W Y)⟩

/-- **Stacks 05S9** at a terminal index. If the index category `X/W` has a terminal object `s₀`,
the ind-object `X/W ⥤ H`, `(s : X ⟶ X') ↦ F(X')` is essentially constant with value `F(X'₀)`, a
value cocone being the one that the terminal object induces: its coprojection at `s₀` is the
identity, so the identity is a section of it, and the transition morphism out of `F(X')` given by
the unique morphism `s ⟶ s₀` factors through it trivially. -/
private lemma isRightDerivedValueAt_coconeOfDiagramTerminal {D : Type u₁} [Category.{v₁} D]
    {H : Type u₂} [Category.{v₂} H] (F : D ⥤ H) (W : MorphismProperty D) (X : D)
    {s₀ : W.Under ⊤ X} (h : IsTerminal s₀) :
    F.IsRightDerivedValueAt W X (coconeOfDiagramTerminal h
      (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F)) := by
  refine ⟨s₀, 𝟙 _, (Category.id_comp _).trans (coconeOfDiagramTerminal_ι_app_self h _),
    fun s => ⟨s₀, h.from s, h.from s₀, ?_⟩⟩
  show F.map (h.from s).right = F.map (h.from s).right ≫ 𝟙 _ ≫ F.map (h.from s₀).right
  simp

/-! ### K-injective complexes as local objects -/

/-- The quasi-isomorphisms of the homotopy category of complexes of any shape have the
two-out-of-three property, being detected by the homology functors, which have it. -/
private lemma hasTwoOutOfThreeProperty_quasiIso (C : Type u₁) [Category.{v₁} C] [Preadditive C]
    {ι : Type*} (c : ComplexShape ι) [CategoryWithHomology C] :
    (HomotopyCategory.quasiIso C c).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg n := by
    have := hg n
    have h := hfg n
    rw [Functor.map_comp] at h
    exact IsIso.of_isIso_comp_right _ ((HomotopyCategory.homologyFunctor C c n).map g)
  of_precomp f g hf hfg n := by
    have := hf n
    have h := hfg n
    rw [Functor.map_comp] at h
    exact IsIso.of_isIso_comp_left ((HomotopyCategory.homologyFunctor C c n).map f) _

/-- A cochain complex is K-injective iff its image in the homotopy category is local for the
quasi-isomorphisms, i.e. precomposition with a quasi-isomorphism of `K(A)` is bijective on
morphisms into it. -/
private lemma isKInjective_iff_isLocal_quasiIso {A : Type u₁} [Category.{v₁} A] [Abelian A]
    (I : CochainComplex A ℤ) :
    I.IsKInjective ↔ (HomotopyCategory.quasiIso A (.up ℤ)).isLocal
      ((HomotopyCategory.quotient A (.up ℤ)).obj I) := by
  rw [CochainComplex.isKInjective_iff_rightOrthogonal,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic, ObjectProperty.isLocal_trW]

/-- **Stacks 070I**, condition (3), for an arbitrary localization functor. If `I` is a K-injective
complex and `L : K(A) ⥤ D` is a localization functor for the quasi-isomorphisms of `K(A)`, then
`L` is bijective on morphisms into the image of `I` in `K(A)`: being K-injective says that this
image is right orthogonal to the acyclic complexes, and the class of morphisms attached to that
triangulated subcategory is the quasi-isomorphisms. -/
@[sga "4½ Etat_0 2.5.3" "(b), special case"]
private lemma map_bijective_of_isKInjective {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {D : Type u₃} [Category.{v₃} D] (L : HomotopyCategory A (ComplexShape.up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    {I : CochainComplex A ℤ} (hI : I.IsKInjective)
    (X : HomotopyCategory A (ComplexShape.up ℤ)) :
    Function.Bijective (L.map :
      (X ⟶ (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) → _) := by
  have : L.IsLocalization (HomotopyCategory.subcategoryAcyclic A).trW := by
    rwa [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact (CochainComplex.IsKInjective.rightOrthogonal I).map_bijective_of_isTriangulated L X

/-- For `I` K-injective, `𝟙 (L I)` is a terminal object of the index category
`CostructuredArrow L (L I)` computing the left Kan extension along `L` at `L I`. -/
private noncomputable def isTerminalMkIdOfIsKInjective {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {D : Type u₃} [Category.{v₃} D] (L : HomotopyCategory A (ComplexShape.up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    {I : CochainComplex A ℤ} (hI : I.IsKInjective) :
    IsTerminal (CostructuredArrow.mk
      (𝟙 (L.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))) :=
  costructuredArrowMkIdTerminalOfBijective L (map_bijective_of_isKInjective L hI)

/-- Every functor on `K(A)` has a pointwise right derived functor at a K-injective complex: the
colimit computing the pointwise left Kan extension there is a colimit over an index category with
a terminal object. -/
private lemma hasPointwiseRightDerivedFunctorAt_of_isKInjective
    {A : Type u₁} [Category.{v₁} A] [Abelian A] {H : Type u₂} [Category.{v₂} H]
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H) {I : CochainComplex A ℤ}
    (hI : I.IsKInjective) :
    F.HasPointwiseRightDerivedFunctorAt (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) := by
  rw [F.hasPointwiseRightDerivedFunctorAt_iff
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Q _]
  exact ⟨_, colimitOfDiagramTerminal (isTerminalMkIdOfIsKInjective _ hI) _⟩

/-! ### K-injective complexes compute right derived functors -/

namespace Functor

/-- **Stacks 070Y.** Let `A` be an abelian category and `F : K(A) ⥤ H` a functor on the homotopy
category of `ℤ`-indexed cochain complexes. Let `I` be a K-injective complex. Then:

* `I` computes the right derived functor `RF` relative to the quasi-isomorphisms of `K(A)`: the
  ind-object `I/Qis(A) ⥤ H`, `(s : I ⟶ N) ↦ F(N)`, is essentially constant, and the canonical
  map `F(I) ⟶ RF(I)`, i.e. the coprojection of its value cocone at the index `𝟙 I`, is an
  isomorphism;
* `RF` is defined at every object `X` of `K(A)` that is quasi-isomorphic to `I`, i.e. admits a
  quasi-isomorphism to or from `I` in `K(A)`.

The source assumes `F` exact between triangulated categories; neither conclusion uses this. -/
@[stacks 070Y]
public theorem exists_isRightDerivedValueAt_and_isIso_of_isKInjective
    {A : Type u₁} [Category.{v₁} A] [Abelian A] {H : Type u₂} [Category.{v₂} H]
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H)
    (I : CochainComplex A ℤ) [I.IsKInjective] :
    (∃ c, F.IsRightDerivedValueAt (HomotopyCategory.quasiIso A (.up ℤ))
        ((HomotopyCategory.quotient A (.up ℤ)).obj I) c ∧
        IsIso (c.ι.app (MorphismProperty.Under.mk ⊤
          (𝟙 ((HomotopyCategory.quotient A (.up ℤ)).obj I))
          (MorphismProperty.id_mem _ _)))) ∧
      ∀ X : HomotopyCategory A (.up ℤ),
        ((∃ s : X ⟶ (HomotopyCategory.quotient A (.up ℤ)).obj I,
            HomotopyCategory.quasiIso A (.up ℤ) s) ∨
          (∃ s : (HomotopyCategory.quotient A (.up ℤ)).obj I ⟶ X,
            HomotopyCategory.quasiIso A (.up ℤ) s)) →
        ∃ c, F.IsRightDerivedValueAt (HomotopyCategory.quasiIso A (.up ℤ)) X c := by
  have hI := (isKInjective_iff_isLocal_quasiIso I).1 inferInstance
  have := hasTwoOutOfThreeProperty_quasiIso A (ComplexShape.up ℤ)
  have hone := isTerminalUnderMk hI
    (MorphismProperty.id_mem (HomotopyCategory.quasiIso A (.up ℤ)) _)
  refine ⟨⟨_, isRightDerivedValueAt_coconeOfDiagramTerminal F _ _ hone,
    (colimitOfDiagramTerminal hone _).isIso_ι_app_of_isTerminal _ hone⟩, fun X hX => ?_⟩
  obtain ⟨g, hg⟩ := exists_mem_hom_to_of_isLocal hI hX
  exact ⟨_, isRightDerivedValueAt_coconeOfDiagramTerminal F _ _ (isTerminalUnderMk hI hg)⟩

/-- **Stacks 070K.** Let `A` be an abelian category such that every complex admits a
quasi-isomorphism towards a K-injective complex, and let `F : K(A) ⥤ D'` be a functor on the
homotopy category of `ℤ`-indexed cochain complexes. Then:

* `F` has a pointwise right derived functor with respect to the quasi-isomorphisms `Qis(A)` of
  `K(A)`; in particular `F.HasRightDerivedFunctor Qis(A)` holds, i.e. `F` has a right derived
  functor `RF : D(A) ⥤ D'`, a left Kan extension of `F` along the localization `K(A) ⥤ D(A)`;
* every K-injective complex `I` computes `RF`: for any localization functor `L` for `Qis(A)` and
  any right derived functor `RF` of `F` with unit `α : F ⟶ L ⋙ RF`, the canonical map
  `α.app I : F(I) ⟶ RF(I)` is an isomorphism, which is the source's `RF(I) = F(I)`.

The source assumes `F` exact between triangulated categories; neither conclusion uses this. -/
@[stacks 070K]
public theorem hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    {A : Type u₁} [Category.{v₁} A] [Abelian A] {H : Type u₂} [Category.{v₂} H]
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H)
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) :
    F.HasPointwiseRightDerivedFunctor (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ∧
      ∀ {D : Type u₃} [Category.{v₃} D] (L : HomotopyCategory A (ComplexShape.up ℤ) ⥤ D)
        [L.IsLocalization (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
        (RF : D ⥤ H) (α : F ⟶ L ⋙ RF)
        [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
        (I : CochainComplex A ℤ), I.IsKInjective →
          IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) := by
  have h₁ : F.HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨I, f, hI, hf⟩ := hA K
    rw [F.hasPointwiseRightDerivedFunctorAt_iff_of_mem _
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f)
      (by rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff])]
    exact hasPointwiseRightDerivedFunctorAt_of_isKInjective F hI
  refine ⟨h₁, ?_⟩
  intro D _ L _ RF α _ I hI
  have hpt := Functor.isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor
    (W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) (L := L) (F' := RF) (α := α)
  have hI' := hpt (L.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))
  simpa using hI'.isIso_ι_app_of_isTerminal _ (isTerminalMkIdOfIsKInjective L hI)

end Functor

end CategoryTheory

end

section

/-!
# K-injective complexes

Let `A` be an abelian category. Write `K(A)` for the homotopy category of `ℤ`-indexed cochain
complexes in `A`, whose morphisms are the homotopy classes of morphisms of complexes, and `D(A)`
for its localization at the quasi-isomorphisms. A cochain complex `I` is *K-injective* when
`Hom_{K(A)}(M, I) = 0` for every acyclic complex `M`.

Such an `I` sees no difference between the homotopy category and the derived category: maps into it
need not be computed by fractions. Precisely, `I` is K-injective if and only if precomposition with
every quasi-isomorphism `M ⟶ N` of `K(A)` is bijective on maps to `I`, if and only if the
localization map `Hom_{K(A)}(N, I) → Hom_{D(A)}(N, I)` is bijective for every `N`. This is what
makes K-injective complexes compute right derived functors on the unbounded derived category.
K-injectivity is moreover a two-out-of-three property along a distinguished triangle of `K(A)`.

Both results read K-injectivity of `I` as: the image of `I` in `K(A)` lies in the right orthogonal
of the acyclic complexes. The quasi-isomorphisms of `K(A)` are the morphisms whose cone is acyclic,
and the right orthogonal of a triangulated subcategory `P` is both the class of `P.trW`-local
objects, which is the second condition, and a triangulated subcategory in its own right, hence
closed under extensions in each of the three positions of a distinguished triangle. For the third
condition, a map to `I` in `D(A)` is a right fraction `f s⁻¹` with `s` a quasi-isomorphism, and
locality makes precomposition with `s` bijective, so the fraction is the image of exactly one
homotopy class; conversely an acyclic complex becomes a zero object of `D(A)`, so injectivity of
the localization map alone forces every morphism from an acyclic complex to `I` to be
null-homotopic.

## Main results

* `CochainComplex.isKInjective_tfae`: for a cochain complex `I`, K-injectivity, `W`-locality for
  the quasi-isomorphisms `W` of `K(A)`, and bijectivity of the localization maps
  `Hom_{K(A)}(N, I) → Hom_{D(A)}(N, I)` are equivalent.
* `CochainComplex.isKInjective_two_out_of_three_of_distTriang`: for a distinguished triangle of
  `K(A)` on complexes `K`, `L`, `M`, each of the three complexes is K-injective as soon as the
  other two are.

## Implementation notes

K-injectivity is Mathlib's class `CochainComplex.IsKInjective`: every morphism of complexes from an
acyclic complex to `I` is null-homotopic, which is `Hom_{K(A)}(M, I) = 0` since morphisms of `K(A)`
are homotopy classes. The second condition is `MorphismProperty.isLocal` for the class
`HomotopyCategory.quasiIso A (.up ℤ)` of morphisms of `K(A)` inducing isomorphisms on all homology
objects, rather than for the images of the quasi-isomorphisms of complexes; the two agree because
`HomotopyCategory.quotient` is full and surjective on objects and a morphism of complexes is a
quasi-isomorphism exactly when its homotopy class is one
(`HomotopyCategory.quotient_map_mem_quasiIso_iff`). That same class is the one at which `D(A)` is
the localization, so the third condition is stated for an arbitrary object `N` of `K(A)`, its map
being induced by the localization functor `DerivedCategory.Qh` and bijectivity for `I` K-injective
being `CochainComplex.IsKInjective.Qh_map_bijective`. The converse direction only needs that an
acyclic complex has zero image in `D(A)`, which holds at any localization at a class `P.trW` of
morphisms whose cone lies in `P` and is proved in that generality.

Morphisms of `D(A)` need not be small, so a chosen derived category with morphisms in `Type w` is
assumed as `HasDerivedCategory.{w} A`; it is needed only for the third condition, and
`HasDerivedCategory.standard` provides one for any abelian `A`. The equivalence does not depend on
the choice, `Qh` being a localization functor for the quasi-isomorphisms of `K(A)`.

The distinguished triangle of `CochainComplex.isKInjective_two_out_of_three_of_distTriang` is given
by three complexes and three morphisms between their images in `K(A)`. This is no restriction and
needs no coherence data: the objects of `K(A)` *are* the cochain complexes, so
`Pretriangulated.Triangle.mk T.mor₁ T.mor₂ T.mor₃` is an arbitrary distinguished triangle `T`,
after its objects have been destructured.

## References

* [Stacks Project, Tag 070I](https://stacks.math.columbia.edu/tag/070I)
* [Stacks Project, Tag 090X](https://stacks.math.columbia.edu/tag/090X)
-/

universe w v u

open CategoryTheory Limits Pretriangulated ZeroObject

/-- An object of a pretriangulated category satisfying an object property `P` becomes a zero object
in any localization at the class `P.trW` of morphisms whose cone satisfies `P`. -/
private lemma isZero_obj_of_isLocalization_trW {C : Type*} [Category C] {D : Type*} [Category D]
    [HasZeroMorphisms D] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)
    (L : C ⥤ D) [L.PreservesZeroMorphisms] [L.IsLocalization P.trW] {X : C} (hX : P X) :
    IsZero (L.obj X) :=
  have : IsIso (L.map (0 : (0 : C) ⟶ X)) :=
    Localization.inverts L P.trW _ (ObjectProperty.trW.mk P (contractible_distinguished₁ X) hX)
  (L.map_isZero (isZero_zero C)).of_iso (asIso (L.map (0 : (0 : C) ⟶ X))).symm

namespace CochainComplex

/-- **Stacks 070I.** Let `A` be an abelian category and `I` a cochain complex in `A`. The
following are equivalent: (1) `I` is K-injective; (2) for every quasi-isomorphism `M ⟶ N` in
`K(A)`, precomposition `Hom_{K(A)}(N, I) → Hom_{K(A)}(M, I)` is bijective; (3) for every `N` in
`K(A)`, the localization map `Hom_{K(A)}(N, I) → Hom_{D(A)}(N, I)` is bijective. -/
@[stacks 070I]
public theorem isKInjective_tfae {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (I : CochainComplex A ℤ) :
    List.TFAE
      [I.IsKInjective,
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).isLocal
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I),
        ∀ N : HomotopyCategory A (ComplexShape.up ℤ),
          Function.Bijective (DerivedCategory.Qh.map :
            (N ⟶ (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) → _)] := by
  tfae_have 1 ↔ 2 := isKInjective_iff_isLocal_quasiIso I
  tfae_have 1 → 3 := fun _ N ↦ IsKInjective.Qh_map_bijective N I
  tfae_have 3 → 1 := fun h ↦ (isKInjective_iff_rightOrthogonal I).2 fun {_} f hM ↦
    (h _).injective ((isZero_obj_of_isLocalization_trW _ _ hM).eq_of_src _ _)
  tfae_finish

/-- **Stacks 090X.** Let `A` be an abelian category and let `(K, L, M, f, g, h)` be a
distinguished triangle of the homotopy category `K(A)` of cochain complexes in `A`, where `K`,
`L`, `M` are cochain complexes. If two out of `K`, `L`, `M` are K-injective, then so is the
third. -/
@[stacks 090X]
public theorem isKInjective_two_out_of_three_of_distTriang
    {A : Type u} [Category.{v} A] [Abelian A] {K L M : CochainComplex A ℤ}
    (f : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)
    (g : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L ⟶
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj M)
    (h : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj M ⟶
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang (HomotopyCategory A (ComplexShape.up ℤ))) :
    (L.IsKInjective → M.IsKInjective → K.IsKInjective) ∧
      (K.IsKInjective → M.IsKInjective → L.IsKInjective) ∧
      (K.IsKInjective → L.IsKInjective → M.IsKInjective) := by
  simp only [isKInjective_iff_rightOrthogonal]
  exact ⟨ObjectProperty.ext_of_isTriangulatedClosed₁ _ _ hT,
    ObjectProperty.ext_of_isTriangulatedClosed₂ _ _ hT,
    ObjectProperty.ext_of_isTriangulatedClosed₃ _ _ hT⟩

end CochainComplex

end
