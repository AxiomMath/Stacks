module
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
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

/-!
# Exactness of sheaves is detected on the stalks

Let `(C, J)` be a site and let `{p_i}` be a *conservative* family of points, that is, a family of
points of the site whose fibre functors on sheaves of sets jointly reflect isomorphisms
(Stacks 00YK; `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints`). Then "exactness" of
sheaves may be checked stalkwise (Stacks 00YL): injectivity (1), surjectivity (2) and equality (3)
of maps of sheaves, and, for a finite diagram `G : K ⥤ Sh(C)` of sheaves, being a limit cone (4)
or a colimit cocone (5).

For (4) and (5) both directions come from the exactness of a stalk functor `F ↦ F_{p_i}`: it is a
filtered colimit of evaluations, hence commutes with finite limits, and it is a left adjoint, hence
commutes with colimits. Given preservation, a family of functors which jointly reflects
isomorphisms also reflects those limits and colimits that exist, by comparison with the actual
(co)limit (`CategoryTheory.JointlyReflectIsomorphisms.jointlyReflectsLimit` and
`…jointlyReflectsColimit`). Applied to kernels this is half of the statement that a sequence of
abelian sheaves is exact if and only if it is exact on all stalks (Stacks 05V3).

## Main results

All in the namespace `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints`, one per part of
Stacks 00YL:

* `injective_app_of_forall_injective_sheafFiber_map`: (1), stalkwise injective maps of sheaves of
  sets are injective.
* `isLocallySurjective_of_forall_surjective_sheafFiber_map`: (2), stalkwise surjective maps of
  sheaves of sets are surjective.
* `eq_of_forall_sheafFiber_map_eq`: (3), maps of sheaves equal on the stalks are equal.
* `nonempty_isLimit_iff`: (4), a cone over a finite diagram of sheaves is a limit if and only if it
  is one on all stalks.
* `nonempty_isColimit_iff`: (5), a cocone under a finite diagram of sheaves is a colimit if and
  only if it is one on all stalks.

## Implementation notes

* Parts (1) and (2) are stated, as in the source, for sheaves of sets, with "injective" and
  "surjective" in the sense of Stacks 00WM: injective on the sections over every object, and
  locally surjective (`CategoryTheory.Sheaf.IsLocallySurjective`). They are deduced from Mathlib's
  `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectMonomorphisms` and
  `…jointlyReflectEpimorphisms`, which give the corresponding statements for monomorphisms and
  epimorphisms of sheaves with values in a general category `A` (and carry the same parts of this
  tag in Mathlib), the injective and surjective maps of sheaves of sets being the monomorphisms and
  the epimorphisms (Stacks 00WN). Part (2) assumes `HasSheafify J (Type w)`, the existence of
  the sheafification of presheaves of sets, which holds for every site in the source's sense
  (the sheafification of Stacks 00W1), and through which surjectivity of a map of sheaves is
  identified with its being an epimorphism. Part (3) is Mathlib's `…jointlyFaithful`, for sheaves
  with values in `A`.
* Parts (4) and (5) are not one conjunction, because they do not hold under the same hypotheses and
  a conjunction would force each half to carry the other's. A stalk functor is only *left* exact,
  so (4) needs the shape `K` to be finite and needs `Limits.HasFiniteLimits A` and
  `AB5OfSize.{w, w} A` — exactly the hypotheses of Mathlib's general form of part (1). It is a
  *left adjoint*, so (5) holds for every shape and needs instead `Limits.HasProducts.{w} A`, for
  the skyscraper sheaf functor it is adjoint to, and `HasWeakSheafify J A`, for the colimit in
  `Sh(C)` it is compared with.
  It is stated, as in the source, for a finite diagram.
* No hypothesis on the shape beyond finiteness is needed: `Limits.HasFiniteLimits A` already gives
  `Limits.HasFiniteLimits (Sheaf J A)`, so the limit the two sides are compared with exists.
* "Is a limit" is spelled `Nonempty (Limits.IsLimit c)` rather than `Limits.IsLimit c`, because
  `IsLimit` is data and the source's assertion is an equivalence of propositions. Nothing is lost:
  `IsLimit c` is a subsingleton, and `Nonempty (IsLimit c)` is the form Mathlib itself uses for the
  proposition "this cone is a limit", both in a hypothesis (`Limits.ReflectsLimit.reflects`) and in
  a characterization (`CategoryTheory.Limits.Types.isLimit_iff`, whose name this one mutates).
* The cone is a parameter, so that the statement is the equivalence asserted of the one cone the
  source names, and the maps the source writes as `(q_j)_{p_i}` are thereby pinned: they are the
  image of `c` under the stalk functor, `(Φ.obj.sheafFiber).mapCone c`.
* The coefficients are a general category `A` rather than only `Type w` (the source's `Sh(C)` is
  sheaves of sets), in parts (3), (4) and (5), matching the general forms of parts (1) and (2),
  which Mathlib states for `A`; hence the concrete-category assumptions on `A` under which
  conservativity at `Type w` transfers to `A`-valued sheaves
  (`…IsConservativeFamilyOfPoints.jointlyReflectIsomorphisms`). Taking `A := Type w` recovers the
  source's statements for sheaves of sets, where only `LocallySmall.{w} C` remains, together with
  `HasWeakSheafify J (Type w)` in part (5), as in part (2).
* The category `A` is implicit, being determined by the diagram or the maps. The shape `K` is
  allowed to live in any universe, which is free: both
  `Limits.hasLimitsOfShape_of_hasFiniteLimits` and
  `Limits.preservesLimitsOfShapeOfPreservesFiniteLimits` are stated for a finite category in an
  arbitrary universe.

## References

* [Stacks 00YL](https://stacks.math.columbia.edu/tag/00YL)
  (`sites-lemma-check-exactness-stalks`), in the section "Sites with enough points" (Stacks 00YJ);
  the definition of a conservative family is Stacks 00YK, injections and surjections of sheaves are
  Stacks 00WN, and the application to abelian sheaves is Stacks 05V3.
* [SGA4], Exposé IV, 6.
-/

namespace CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints

section

universe w v' v u'' u' u
open CategoryTheory Limits

namespace Stacks.SitePoints.StalkwiseLimits

private theorem nonempty_isLimit_iff_proof {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {P : ObjectProperty (GrothendieckTopology.Point.{w} J)}
    (hP : P.IsConservativeFamilyOfPoints) {A : Type u'} [Category.{v'} A] [LocallySmall.{w} C]
    [HasColimitsOfSize.{w, w} A] [HasFiniteLimits A] [AB5OfSize.{w, w} A]
    {FC : A → A → Type*} {CC : A → Type w}
    [∀ X Y : A, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} A FC]
    [(forget A).ReflectsIsomorphisms] [PreservesFilteredColimitsOfSize.{w, w} (forget A)]
    [J.HasSheafCompose (forget A)]
    {K : Type u''} [SmallCategory K] [FinCategory K] {G : K ⥤ Sheaf J A} (c : Cone G) :
    Nonempty (IsLimit c) ↔
      ∀ Φ : P.FullSubcategory, Nonempty (IsLimit ((Φ.obj.sheafFiber (A := A)).mapCone c)) :=
  ⟨fun ⟨hc⟩ _Φ ↦ ⟨isLimitOfPreserves _ hc⟩,
    fun h ↦ ⟨(hP.jointlyReflectIsomorphisms A).jointlyReflectsLimit fun Φ ↦ (h Φ).some⟩⟩

end Stacks.SitePoints.StalkwiseLimits

@[expose] public section

open Stacks.SitePoints.StalkwiseLimits in
/-- **Stacks 00YL (4).** Let `(C, J)` be a site and let `P` be a conservative family of points of
it. Let `G : K ⥤ Sh(C)` be a finite diagram of sheaves with values in `A`. Then a cone over `G` is
a limit if and only if its image under every stalk functor `F ↦ F_{p_i}`, `p_i ∈ P`, is a limit. -/
@[stacks 00YL "(4): a cone over a finite diagram of sheaves is a limit if and only if it is one in
  every stalk at a conservative family of points."]
public theorem nonempty_isLimit_iff {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {P : ObjectProperty (GrothendieckTopology.Point.{w} J)}
    (hP : P.IsConservativeFamilyOfPoints) {A : Type u'} [Category.{v'} A] [LocallySmall.{w} C]
    [HasColimitsOfSize.{w, w} A] [HasFiniteLimits A] [AB5OfSize.{w, w} A]
    {FC : A → A → Type*} {CC : A → Type w}
    [∀ X Y : A, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} A FC]
    [(forget A).ReflectsIsomorphisms] [PreservesFilteredColimitsOfSize.{w, w} (forget A)]
    [J.HasSheafCompose (forget A)]
    {K : Type u''} [SmallCategory K] [FinCategory K] {G : K ⥤ Sheaf J A} (c : Cone G) :
    Nonempty (IsLimit c) ↔
      ∀ Φ : P.FullSubcategory, Nonempty (IsLimit ((Φ.obj.sheafFiber (A := A)).mapCone c)) := by
  apply Stacks.SitePoints.StalkwiseLimits.nonempty_isLimit_iff_proof ; assumption

/-- **Stacks 00YL (1).** Let `(C, J)` be a site and let `P` be a conservative family of points of
it. Let `φ : F ⟶ G` be a map of sheaves of sets. If every stalk map `φ_{p_i}`, `p_i ∈ P`, is
injective, then `φ` is injective, that is, injective on the sections over every object `U`
(Stacks 00WM (1)). -/
@[stacks 00YL "(1): a map of sheaves of sets which is injective on the stalks at a conservative
  family of points is injective."]
public theorem injective_app_of_forall_injective_sheafFiber_map {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {P : ObjectProperty (GrothendieckTopology.Point.{w} J)}
    (hP : P.IsConservativeFamilyOfPoints) [LocallySmall.{w} C] {F G : Sheaf J (Type w)}
    (φ : F ⟶ G)
    (h : ∀ Φ : P.FullSubcategory, Function.Injective (Φ.obj.sheafFiber.map φ)) (U : Cᵒᵖ) :
    Function.Injective (φ.hom.app U) := by
  have (Φ : P.FullSubcategory) : Mono (Φ.obj.sheafFiber.map φ) :=
    (mono_iff_injective _).2 (h Φ)
  have : Mono φ := (hP.jointlyReflectMonomorphisms (Type w)).mono φ
  have : Mono φ.hom := (sheafToPresheaf J (Type w)).map_mono φ
  exact (mono_iff_injective _).1 inferInstance

/-- **Stacks 00YL (2).** Let `(C, J)` be a site and let `P` be a conservative family of points of
it. Let `φ : F ⟶ G` be a map of sheaves of sets. If every stalk map `φ_{p_i}`, `p_i ∈ P`, is
surjective, then `φ` is surjective, that is, every section of `G` is locally in the image of `φ`
(Stacks 00WM (2); `CategoryTheory.Sheaf.IsLocallySurjective`). -/
@[stacks 00YL "(2): a map of sheaves of sets which is surjective on the stalks at a conservative
  family of points is surjective."]
public theorem isLocallySurjective_of_forall_surjective_sheafFiber_map {C : Type u}
    [Category.{v} C] {J : GrothendieckTopology C}
    {P : ObjectProperty (GrothendieckTopology.Point.{w} J)}
    (hP : P.IsConservativeFamilyOfPoints) [LocallySmall.{w} C] [HasSheafify J (Type w)]
    {F G : Sheaf J (Type w)} (φ : F ⟶ G)
    (h : ∀ Φ : P.FullSubcategory, Function.Surjective (Φ.obj.sheafFiber.map φ)) :
    Sheaf.IsLocallySurjective φ := by
  have (Φ : P.FullSubcategory) : Epi (Φ.obj.sheafFiber.map φ) :=
    (epi_iff_surjective _).2 (h Φ)
  have : Epi φ := (hP.jointlyReflectEpimorphisms (Type w)).epi φ
  exact (Sheaf.isLocallySurjective_iff_epi φ).2 this

/-- **Stacks 00YL (3).** Let `(C, J)` be a site and let `P` be a conservative family of points of
it. Two maps of sheaves `φ₁ φ₂ : F ⟶ G` which agree on the stalks at every `p_i ∈ P` are
equal. -/
@[stacks 00YL "(3): two maps of sheaves which agree on the stalks at a conservative family of
  points are equal."]
public theorem eq_of_forall_sheafFiber_map_eq {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {P : ObjectProperty (GrothendieckTopology.Point.{w} J)}
    (hP : P.IsConservativeFamilyOfPoints) {A : Type u'} [Category.{v'} A] [LocallySmall.{w} C]
    [HasColimitsOfSize.{w, w} A] [HasFiniteLimits A] [AB5OfSize.{w, w} A]
    {FC : A → A → Type*} {CC : A → Type w}
    [∀ X Y : A, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} A FC]
    [(forget A).ReflectsIsomorphisms] [PreservesFilteredColimitsOfSize.{w, w} (forget A)]
    [J.HasSheafCompose (forget A)] {F G : Sheaf J A} {φ₁ φ₂ : F ⟶ G}
    (h : ∀ Φ : P.FullSubcategory, Φ.obj.sheafFiber.map φ₁ = Φ.obj.sheafFiber.map φ₂) :
    φ₁ = φ₂ :=
  (hP.jointlyFaithful A).map_injective h

/-- **Stacks 00YL (5).** Let `(C, J)` be a site and let `P` be a conservative family of points of
it. Let `G : K ⥤ Sh(C)` be a finite diagram of sheaves with values in `A`. Then a cocone under `G`
is a colimit if and only if its image under every stalk functor `F ↦ F_{p_i}`, `p_i ∈ P`, is a
colimit. -/
@[stacks 00YL "(5): a cocone under a finite diagram of sheaves is a colimit if and only if it is
  one in every stalk at a conservative family of points."]
public theorem nonempty_isColimit_iff {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {P : ObjectProperty (GrothendieckTopology.Point.{w} J)}
    (hP : P.IsConservativeFamilyOfPoints) {A : Type u'} [Category.{v'} A] [LocallySmall.{w} C]
    [HasColimitsOfSize.{w, w} A] [HasWeakSheafify J A] [HasProducts.{w} A]
    {FC : A → A → Type*} {CC : A → Type w}
    [∀ X Y : A, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} A FC]
    [(forget A).ReflectsIsomorphisms] [PreservesFilteredColimitsOfSize.{w, w} (forget A)]
    [J.HasSheafCompose (forget A)]
    {K : Type u''} [SmallCategory K] [FinCategory K] {G : K ⥤ Sheaf J A} (c : Cocone G) :
    Nonempty (IsColimit c) ↔
      ∀ Φ : P.FullSubcategory, Nonempty (IsColimit ((Φ.obj.sheafFiber (A := A)).mapCocone c)) := by
  have : HasFiniteColimits A := hasFiniteColimits_of_hasColimitsOfSize A
  exact ⟨fun ⟨hc⟩ _Φ ↦ ⟨isColimitOfPreserves _ hc⟩,
    fun h ↦ ⟨(hP.jointlyReflectIsomorphisms A).jointlyReflectsColimit fun Φ ↦ (h Φ).some⟩⟩
end

end

end CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints
