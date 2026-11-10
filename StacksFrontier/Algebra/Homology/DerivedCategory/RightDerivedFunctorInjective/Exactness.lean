module

import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import all Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
import Mathlib.CategoryTheory.Functor.Derived.RightDerivedTriangulated
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.ENatToNat
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.Embedding.StupidTrunc
import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
import StacksFrontier.CategoryTheory.EssentiallyConstant.IndObject
public import StacksFrontier.CategoryTheory.Functor.Derived.Computing
import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt
import StacksFrontier.CategoryTheory.Functor.Derived.Shift
public import StacksFrontier.CategoryTheory.Functor.Derived.Triangle
import StacksFrontier.CategoryTheory.Triangulated.Elementary
public import StacksFrontier.CategoryTheory.Triangulated.Functor
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle

/-!
# Right derived functors and injective resolutions

Let `𝒜` and `ℬ` be abelian categories and let `F : 𝒜 ⥤ ℬ` be an additive functor. This file
collects the three facts that make an injective resolution compute the right derived functor of
`F` on bounded below derived categories.

A bounded below complex `K` of injective objects of `𝒜` is K-injective, so the localization
`Q⁺ : K⁺(𝒜) ⥤ D⁺(𝒜)` induces a bijection from `X ⟶ K` onto `Q⁺(X) ⟶ Q⁺(K)` for every `X`;
equivalently, every quasi-isomorphism out of `K` has a left inverse in `K⁺(𝒜)`. Consequently
`𝟙 Q⁺(K)` is a terminal object of `CostructuredArrow Q⁺ (Q⁺(K))`, the colimit computing the
pointwise left Kan extension along `Q⁺` at `Q⁺(K)` of an arbitrary functor `G : K⁺(𝒜) ⥤ ℋ`
exists, and the right derived functor of `G` is *defined at* `K`.

Assume now that `𝒜` has enough injectives, and let `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` be a right derived
functor of `K⁺(F) ⋙ Q⁺_ℬ` along `Q⁺_𝒜`, with unit `α : K⁺(F) ⋙ Q⁺_ℬ ⟶ Q⁺_𝒜 ⋙ RF`. Then `RF`
is an exact functor of triangulated categories. Writing `ι : K⁺(Inj 𝒜) ⥤ K⁺(𝒜)` for the functor
induced by the inclusion of the injective objects, `α` is invertible on the image of `ι` because
`ι` is the functor of a right derivability structure, so that `ι ⋙ Q⁺_𝒜 ⋙ RF` is isomorphic to
`ι ⋙ K⁺(F) ⋙ Q⁺_ℬ`, a composition of exact functors; and every arrow of `D⁺(𝒜)` is, up to
isomorphism of arrows, in the image of `ι ⋙ Q⁺_𝒜`, because every arrow of `K⁺(𝒜)` admits a
right resolution by an arrow between bounded below complexes of injectives.

Both facts together compute the higher right derived functors `R ⁱ F = H ⁱ ∘ RF ∘ (·[0])` on an
injective object `I`: the complex `I[n]` is a bounded below complex of injectives, so
`RF(I[n]) ≅ F(I)[n]`, and a complex concentrated in degree `n` has vanishing homology in every
other degree. Hence `R ⁱ F (I) = 0` for `i ≠ 0`, which is what makes injective objects acyclic.

The same computation on an injective resolution `X[0] ⟶ I` of an arbitrary object, `I` being
concentrated in degrees `≥ 0`, shows that `RF(X[0])` is cohomologically `≥ 0`, so that
`R ⁱ F = 0` for `i < 0`; exactness of `RF` then makes `R ⁰ F` left exact, and the canonical map
`F ⟶ R ⁰ F`, which is `H ⁰` of the unit `α` at the complexes `X[0]`, is an isomorphism precisely
when `F` itself is left exact — so it makes little sense to right derive a functor that is not
left exact.

An object `A` of `𝒜` is *right acyclic* for `F` when `A[0]` computes `RF`, that is when `α` is
invertible at `A[0]`. Since a morphism of `D⁺(ℬ)` is invertible exactly when it is invertible on
homology in every degree, and since `F(A)[0]` has homology `F(A)` in degree `0` and `0` elsewhere,
`A` is right acyclic for `F` if and only if `F(A) ⟶ R ⁰ F(A)` is an isomorphism and
`R ⁱ F(A) = 0` for all `i > 0`; for a left exact `F` the first condition is automatic. Reading
that criterion off the long exact sequence attached to a short exact sequence
`0 ⟶ A ⟶ B ⟶ C ⟶ 0` of `𝒜`, two right acyclic objects among `A`, `B`, `C` force the third to be
right acyclic — outright when the two are `A, C` or `A, B`, and, when they are `B, C`, under the
extra hypothesis that `F(B) ⟶ F(C)` be surjective, which the sequence does not otherwise provide;
in each case `0 ⟶ F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is again short exact.

Acyclicity spreads from single objects to complexes: a bounded below complex all of whose terms
are right acyclic for `F` computes `RF`. This is Leray's acyclicity lemma, and it is what makes
derived functors computable, a resolution by acyclic objects — flasque or injective sheaves for
`Rf_*`, a Čech complex, an affine cover — being usable in place of an injective resolution. Its
proof is the induction on the number of nonzero terms along the distinguished triangle
`(σ_{≥ a + 1}K, K, σ_{≤ a}K)` of a stupid truncation, followed by a degreewise comparison of the
long exact sequences of that triangle and of its image under `RF`.

The acyclicity arguments do not need injectives: if every object of `𝒜` merely embeds into an
object acyclic for `RF` in the source's partial sense ([Stacks, Tag 05SX]), then `RF` is defined
on all of `K⁺(𝒜)`, is exact, and is computed by bounded below complexes of acyclic objects
([Stacks, Tag 05TA]). The full subcategory of `K⁺(𝒜)` of complexes with acyclic terms carries a
right derivability structure, `F` inverts its quasi-isomorphisms because the cone of such a
quasi-isomorphism is an acyclic complex with acyclic terms, and the resulting derived functor
moves cohomology to the right, which is what Leray's comparison needs.

Finally, the family `{R ⁱ F, δ}_{i ≥ 0}`, with the connecting morphisms `δ` produced by the
homology sequence of the `RF`-image of the triangle of a short exact sequence, is a cohomological
`δ`-functor from `𝒜` to `ℬ`, and it is universal as soon as every object of `𝒜` admits a
monomorphism into an object that is right acyclic for `F`.

## Main results

* `HomotopyCategory.Plus.hasPointwiseRightDerivedFunctorAt_of_injective`: the right derived
  functor of any functor out of `K⁺(𝒜)` is defined at a bounded below complex of injectives.
* `CategoryTheory.Functor.isTriangulated_of_isRightDerivedFunctor_mapHomotopyCategoryPlus`: a
  right derived functor `D⁺(𝒜) ⥤ D⁺(ℬ)` of an additive functor `F : 𝒜 ⥤ ℬ`, where `𝒜` has
  enough injectives, is exact.
* `CategoryTheory.Functor.isZero_rightDerivedPlus_obj_injective`: `R ⁱ F (I) = 0` for `I`
  injective and `i ≠ 0`.
* `CategoryTheory.Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits`:
  `R ⁱ F = 0` for `i < 0`, the functor `R ⁰ F` is left exact, and `F ⟶ R ⁰ F` is an isomorphism
  if and only if `F` is left exact.
* `CategoryTheory.Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus`: right acyclicity
  of `A` is the invertibility of `F(A) ⟶ R ⁰ F(A)` together with `R ⁱ F(A) = 0` for `i > 0`, the
  first condition being automatic for a left exact `F`.
* `CategoryTheory.Functor.rightAcyclic_and_shortExact_map_of_shortExact`: two right acyclic
  objects in a short exact sequence force the third, and `F` takes the sequence to a short exact
  sequence.
* `CategoryTheory.Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic`: Leray's acyclicity
  lemma, a bounded below complex of right `F`-acyclic objects computes `RF`.
* `CategoryTheory.Functor.rightDerivedPlus_isDeltaFunctor_and_isUniversal`: the higher right
  derived functors form a cohomological `δ`-functor, universal when enough right acyclic objects
  are available.
* `CategoryTheory.Functor.hasDerivedFunctors_of_enough_acyclic_objects`: enough objects acyclic
  for `RF` (resp. `LF`) give an everywhere defined exact `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` (resp. `LF` on
  `D⁻`), computed by bounded below (resp. above) complexes of acyclic objects.

## Implementation notes

That the right derived functor of `G` is *defined at* `K` is
`Functor.HasPointwiseRightDerivedFunctorAt`: the pointwise left Kan extension of `G` along a
localization `L` of `K⁺(𝒜)` at the quasi-isomorphisms exists at `L(K)`. It does not depend on the
choice of `L` (`Functor.hasPointwiseRightDerivedFunctorAt_iff`), so it is verified along
`DerivedCategory.Plus.Qh` for the standard derived category and no `HasDerivedCategory 𝒜`
hypothesis appears; nor does `EnoughInjectives 𝒜`, and that is where termwise injectivity of `K`
does its work, since with enough injectives every functor out of `K⁺(𝒜)` is defined at every
object. The other half of "`K` computes the right derived functor of `G`" — invertibility of
`G(K) ⟶ RG(K)` — is not available at that generality: a Kan extension pointwise at one object is
not thereby compared with the value there, and the comparison goes through the right derivability
structure on `ι : K⁺(Inj 𝒜) ⥤ K⁺(𝒜)`, that is, again through enough injectives.

Exactness of a functor between triangulated categories presupposes a commutation with the shift,
which is *data*: hence the hypotheses `[RF.CommShift ℤ]` and `[NatTrans.CommShift α ℤ]`, the
latter tying that datum to the shift-commutation of the functor being derived. Exactness is
stated for an arbitrary right derived functor of `K⁺(F) ⋙ Q⁺_ℬ` along `Q⁺_𝒜`, since no step of
the argument uses more; the source's `RF` is the instantiation at `F.rightDerivedFunctorPlus` and
`F.rightDerivedFunctorPlusUnith`, and the induced exact functor `K⁺(𝒜) ⥤ D⁺(ℬ)` of part (2) is
`DerivedCategory.Plus.Qh ⋙ RF`.

The vanishing of `R ⁱ F (I)` is stated for `i ≠ 0` rather than the source's `i > 0`, and for an
arbitrary additive `F` rather than a left exact one, since `RF(I[0]) ≅ F(I)[0]` whichever the
additive `F`. For `i < 0` it also follows from [Stacks, Tag 05TD], but only there for a left exact
`F`, so the two overlap rather than either subsuming the other. The functor `R ⁱ F` is
`Functor.rightDerivedPlus` ([Stacks, Tag 015A]), indexed by `ℤ` as in the source; for Mathlib's
`ℕ`-indexed `Functor.rightDerived` the vanishing is
`Functor.isZero_rightDerived_obj_injective_succ`.

Where the argument does not need more, the pair `(RF, α)` is taken as data rather than
constructed, since any two right derived functors are uniquely isomorphic compatibly with their
units (`Functor.rightDerivedUnique`); specialising `RF` to `Functor.rightDerivedFunctorPlus` turns
`H ⁱ ∘ RF ∘ (·[0])` into the functor `R ⁱ F` of [Stacks, Tag 015A], which is the form the
statements about right acyclicity are made in, that predicate being defined with the canonical
unit. `R ⁱ F` is spelled as the composite
`DerivedCategory.Plus.singleFunctor 𝒜 0 ⋙ RF ⋙ DerivedCategory.Plus.homologyFunctor ℬ i`, and
`X ↦ X[0]` into `K⁺(𝒜)` is `HomotopyCategory.Plus.singleFunctor 𝒜 0`, whose composite with `Qh`
is `DerivedCategory.Plus.singleFunctor 𝒜 0`.

`EnoughInjectives 𝒜` is throughout the form in which the hypothesis that `RF` be *defined* is
used, and it is stronger than the existence of the colimit computing the Kan extension: that
colimit's universal property controls `Hom(RF(X), -)` and says nothing about `Hom(-, RF(X))`,
whereas both the propagation of "computes `RF`" along a distinguished triangle and the vanishing
of `H ⁱ(RF(K))` below the degrees `K` occupies are read off a factorization of `𝟙_{RF(K)}`
through a single `F(L)`, that is, off maps *into* `RF(K)`. With enough injectives the injective
derivability structure of `K⁺(𝒜)` supplies both, `α` being invertible at every bounded below
complex of injectives.

Two notions the arguments consume are absent from Mathlib and are built here. The inclusion
`σ_{≥ a}K ⟶ K` and the projection `K ⟶ σ_{≤ b}K` of stupid truncations are constructed for a
fixed complex (`ιStupidTrunc`, `πStupidTrunc`), assembled into a termwise split short exact
sequence and hence into a distinguished triangle of `K⁺(𝒜)`. And a cohomological `δ`-functor is
presented as what it is — a family of additive functors, connecting morphisms, exactness of the
long sequence at each of its spots, and naturality of the connecting morphisms in the short exact
sequence — both in the conclusion about `{R ⁱ F, δ}` and for the `δ`-functors quantified over in
its universality; exactness at a spot is stated as
`∃ hz : u ≫ v = 0, (ShortComplex.mk u v hz).Exact`, since for the spots adjacent to a connecting
morphism the vanishing of the composite is itself part of the assertion. Universality is
Grothendieck's criterion ([Stacks, Tag 010T]): a `δ`-functor effaceable in positive degrees is
universal.

The vanishing `R ⁱ F(A) = 0` in the acyclicity criterion is asserted for `i > 0` rather than
`i ≠ 0`; the two agree, since `R ⁱ F = 0` for `i < 0` always, and `i > 0` is the form in which
the criterion is used downstream.

## References

* [Stacks, Tag 05TH], part (1)
* [Stacks, Tag 0159], part (1)
* [Stacks, Tag 015B], part (3)
* [Stacks, Tag 05TD], right deriving is for left exact functors
* [Stacks, Tag 015C], right acyclicity as the vanishing of `R ⁱ F` in positive degrees
* [Stacks, Tag 015D], right acyclicity in a short exact sequence
* [Stacks, Tag 015E], Leray's acyclicity lemma
* [Stacks, Tag 05TE], the higher right derived functors as a universal `δ`-functor
* [Stacks, Tag 0157], right acyclic objects
* [Stacks, Tag 05TA], derived functors from acyclic resolutions
* [Stacks, Tag 015A], the definition of `R ⁱ F`
* [Stacks, Tag 010Q] and [Stacks, Tag 010T], `δ`-functors and Grothendieck's criterion
* [Stacks, Tag 0118], the distinguished triangle of a termwise split short exact sequence
* [Stacks, Tag 0152], the distinguished triangle of a short exact sequence of objects
* [Stacks, Tag 05S9], `RF` defined at an object, and [Stacks, Tag 05TC], `RF` moves cohomology to
  the right
* [Stacks, Tag 013P], the left inverse of a quasi-isomorphism out of a bounded below complex of
  injectives
-/

@[expose] public section

universe v₁ v₂ v₃ w₁ w₂ u₁ u₂ u₃

open CategoryTheory Limits

namespace CategoryTheory.CostructuredArrow

/-- If a functor `L : C ⥤ D` induces a bijection `(X ⟶ K) ≃ (L.obj X ⟶ L.obj K)` for every
`X : C`, then `𝟙 (L.obj K)`, as an object of `CostructuredArrow L (L.obj K)`, is terminal: the
unique map to it from `A` is the preimage of `A.hom` under `L.map`. This is
`CategoryTheory.CostructuredArrow.mkIdTerminal` with full faithfulness of `L` weakened to
bijectivity at the single object `K`. -/
private noncomputable def mkIdTerminalOfBijective {C : Type*} {D : Type*}
    [Category* C] [Category* D] (L : C ⥤ D) {K : C}
    (h : ∀ X : C, Function.Bijective (L.map : (X ⟶ K) → (L.obj X ⟶ L.obj K))) :
    IsTerminal (CostructuredArrow.mk (𝟙 (L.obj K)) : CostructuredArrow L (L.obj K)) :=
  IsTerminal.ofUniqueHom
    (fun A ↦ CostructuredArrow.homMk ((Equiv.ofBijective _ (h A.left)).symm A.hom)
      (by simpa using Equiv.ofBijective_apply_symm_apply _ (h A.left) A.hom))
    (fun A m ↦ CostructuredArrow.hom_ext _ _ ((h A.left).injective
      (by simpa [Equiv.ofBijective_apply_symm_apply] using CostructuredArrow.w m)))

end CategoryTheory.CostructuredArrow

namespace HomotopyCategory

/-- An object of the homotopy category of cochain complexes is bounded below iff its underlying
cochain complex is. This is `HomotopyCategory.plus_quotient_obj_iff` for a complex that is not
presented as a quotient. -/
private lemma plus_iff {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    HomotopyCategory.plus C X ↔ CochainComplex.plus C X.as := by
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  exact HomotopyCategory.plus_quotient_obj_iff M

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

/-- The underlying cochain complex of a bounded below object of the homotopy category whose
terms are injective objects is K-injective. This is `CochainComplex.isKInjective_of_injective`
with its hypothesis that the complex be strictly bounded below relaxed to the bounded belowness
carried by `HomotopyCategory.Plus C`. -/
private lemma isKInjective_as_of_plus (X : HomotopyCategory C (ComplexShape.up ℤ))
    (hX : HomotopyCategory.plus C X) [∀ n : ℤ, Injective (X.as.X n)] :
    CochainComplex.IsKInjective X.as := by
  obtain ⟨n, _⟩ := (CochainComplex.plus_iff _ _).1 ((plus_iff X).1 hX)
  exact CochainComplex.isKInjective_of_injective _ n

namespace Plus

section

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 05TH**, part (1), first half. Let `K` be a bounded below complex of injective
objects of an abelian category `C`. Then the right derived functor of any functor
`F : K⁺(C) ⥤ H` relative to the quasi-isomorphisms of `K⁺(C)` is defined at `K`, i.e. the
pointwise left Kan extension of `F` along a localization of `K⁺(C)` at the quasi-isomorphisms
exists at the image of `K`.

If `C` has enough injectives, this holds for every `K`; the content here is that termwise
injectivity of `K` suffices. -/
@[stacks 05TH "part (1): RF is defined at a bounded below complex of injectives"]
public instance hasPointwiseRightDerivedFunctorAt_of_injective {H : Type u₃} [Category.{v₃} H]
    (F : HomotopyCategory.Plus C ⥤ H) (K : HomotopyCategory.Plus C)
    [∀ n : ℤ, Injective (K.obj.as.X n)] :
    F.HasPointwiseRightDerivedFunctorAt (HomotopyCategory.Plus.quasiIso C) K := by
  rw [F.hasPointwiseRightDerivedFunctorAt_iff DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso C) K]
  have := (CostructuredArrow.mkIdTerminalOfBijective DerivedCategory.Plus.Qh fun X ↦
    DerivedCategory.Plus.Qh_map_bijective_of_isKInjective X K
      (isKInjective_as_of_plus K.obj K.property)).hasTerminal
  infer_instance

end

end Plus

end HomotopyCategory

namespace CategoryTheory.LocalizerMorphism

/-- If `Φ : LocalizerMorphism W₁ W₂` is such that the induced localizer morphism on arrow
categories has right resolutions, and if `L₂ : C₂ ⥤ D₂` is a localization functor for `W₂` which
is essentially surjective on arrows, then `Φ.functor ⋙ L₂` is essentially surjective on arrows:
any arrow of `D₂` comes from an arrow of `C₂`, which in turn admits a right resolution by an
arrow of `C₁`, and `L₂` inverts the two components of that resolution. -/
lemma essSurj_mapArrow_functor_comp {C₁ : Type*} {C₂ : Type*} {D₂ : Type*}
    [Category* C₁] [Category* C₂] [Category* D₂] {W₁ : MorphismProperty C₁}
    {W₂ : MorphismProperty C₂} (Φ : LocalizerMorphism W₁ W₂) [Φ.arrow.HasRightResolutions]
    (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂] [L₂.mapArrow.EssSurj] :
    (Φ.functor ⋙ L₂).mapArrow.EssSurj where
  mem_essImage f := by
    let r : Φ.arrow.RightResolution (L₂.mapArrow.objPreimage f) := Classical.arbitrary _
    have h₁ : IsIso (L₂.mapArrow.map r.w).left := Localization.inverts L₂ W₂ _ r.hw.1
    have h₂ : IsIso (L₂.mapArrow.map r.w).right := Localization.inverts L₂ W₂ _ r.hw.2
    have : IsIso (L₂.mapArrow.map r.w) := Arrow.isIso_of_isIso_left_of_isIso_right _
    exact ⟨r.X₁, ⟨(asIso (L₂.mapArrow.map r.w)).symm ≪≫ L₂.mapArrow.objObjPreimageIso f⟩⟩

end CategoryTheory.LocalizerMorphism

namespace CategoryTheory.Functor

open _root_.DerivedCategory

section

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D] (F : C ⥤ D) [F.Additive]
  [EnoughInjectives C] (RF : Plus C ⥤ Plus D)
  (α : F.mapHomotopyCategoryPlus ⋙ Plus.Qh ⟶ Plus.Qh ⋙ RF)

/-- The unit of a right derived functor of `K⁺(F) ⋙ Q⁺_ℬ` along `Q⁺_𝒜` is invertible after
whiskering with the functor `ι : K⁺(Inj 𝒜) ⥤ K⁺(𝒜)` induced by the inclusion of the injective
objects: on a bounded below complex of injectives, `RF` is computed by `F`. -/
private lemma isIso_whiskerLeft_injectiveObjectι
    [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso C)] :
    IsIso (whiskerLeft (InjectiveObject.ι C).mapHomotopyCategoryPlus α) :=
  have : ∀ X : HomotopyCategory.Plus (InjectiveObject C),
      IsIso ((whiskerLeft (InjectiveObject.ι C).mapHomotopyCategoryPlus α).app X) :=
    fun _ ↦ by dsimp; infer_instance
  NatIso.isIso_of_isIso_app _

/-- **Stacks 0159**, part (1). Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian
categories, where `𝒜` has enough injectives. Then any right derived functor
`RF : D⁺(𝒜) ⥤ D⁺(ℬ)` of `K⁺(F) ⋙ Q⁺_ℬ` along the localization `Q⁺_𝒜 : K⁺(𝒜) ⥤ D⁺(𝒜)` at the
quasi-isomorphisms, with unit `α`, is an exact functor of triangulated categories.

The source's `RF` is the case `RF := F.rightDerivedFunctorPlus` and
`α := F.rightDerivedFunctorPlusUnith`, with the commutation with the shift induced by the
universal property. The induced exact functor `K⁺(𝒜) ⥤ D⁺(ℬ)` of part (2) is then
`DerivedCategory.Plus.Qh ⋙ RF`. -/
@[stacks 0159 "part (1)", sga "4 XVII 1.2.2" "(ii), special case"]
public theorem isTriangulated_of_isRightDerivedFunctor_mapHomotopyCategoryPlus
    [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso C)]
    [RF.CommShift ℤ] [NatTrans.CommShift α ℤ] :
    RF.IsTriangulated :=
  have := (HomotopyCategory.Plus.localizerMorphism C).essSurj_mapArrow_functor_comp
    (Plus.Qh (C := C))
  have := isIso_whiskerLeft_injectiveObjectι F RF α
  let e := asIso (whiskerLeft (InjectiveObject.ι C).mapHomotopyCategoryPlus α)
  have : NatTrans.CommShift e.hom ℤ :=
    inferInstanceAs (NatTrans.CommShift
      (whiskerLeft (InjectiveObject.ι C).mapHomotopyCategoryPlus α) ℤ)
  have : ((InjectiveObject.ι C).mapHomotopyCategoryPlus ⋙ Plus.Qh ⋙ RF).IsTriangulated :=
    isTriangulated_of_iso e
  isTriangulated_of_precomp_iso
    (F := (InjectiveObject.ι C).mapHomotopyCategoryPlus ⋙ Plus.Qh) (G := RF) (associator _ _ _)

end

section HigherRightDerived

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [EnoughInjectives C]

/-- The `i`-th right derived functor `R^i F = H^i ∘ RF : 𝒜 ⥤ ℬ` of an additive functor
`F : 𝒜 ⥤ ℬ` between abelian categories, where `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is the right derived
functor of `F` on bounded below derived categories and `𝒜 → D⁺(𝒜)` sends an object to the
complex concentrated in degree `0`. -/
@[stacks 015A,
  ega "0 13.6.1",
  sga "4½ Etat_0 4.1" "right derived R^iF",
  sga "4½ Etat_0 4.1.5" "R^i f"]
public noncomputable def rightDerivedPlus (i : ℤ) : C ⥤ D :=
  DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor D i

end HigherRightDerived

section

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- The single functor into the bounded below derived category factors through the bounded below
homotopy category. -/
public noncomputable def singleFunctorPlusIsoCompQh (n : ℤ) :
    Plus.singleFunctor A n ≅ HomotopyCategory.Plus.singleFunctor A n ⋙ Plus.Qh :=
  fullyFaithfulCancelRight Plus.ι (singleFunctorIsoCompQh A n)

/-- The homology of the complex `X[n]` vanishes in every degree `i ≠ n`. -/
private lemma isZero_homologyFunctor_obj_singleFunctor_obj (i n : ℤ) (hi : i ≠ n) (X : B) :
    IsZero ((Plus.homologyFunctor B i).obj ((Plus.singleFunctor B n).obj X)) :=
  hi.lt_or_gt.elim (Plus.isZero_homology_of_isGE _ n i) (Plus.isZero_homology_of_isLE _ n i)

variable (F : A ⥤ B) [F.Additive] [EnoughInjectives A]
  (RF : Plus A ⥤ Plus B) (α : F.mapHomotopyCategoryPlus ⋙ Plus.Qh ⟶ Plus.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso A)]

/-- The unit of a right derived functor is invertible at the complex `I[n]` when `I` is an
injective object, that complex being a bounded below complex of injective objects. -/
private lemma isIso_app_singleFunctor_obj_of_injective (n : ℤ) (I : A) [Injective I] :
    IsIso (α.app ((HomotopyCategory.Plus.singleFunctor A n).obj I)) := by
  have : ∀ m : ℤ, Injective (((HomotopyCategory.Plus.singleFunctor A n).obj I).obj.as.X m) :=
    fun m ↦ inferInstanceAs
      (Injective (((HomologicalComplex.single A (ComplexShape.up ℤ) n).obj I).X m))
  infer_instance

/-- A right derived functor is computed by `F` on an injective object: for `I` injective,
`RF(I[n])` is `F(I)[n]`. -/
private noncomputable def objSingleFunctorObjIso (n : ℤ) (I : A) [Injective I] :
    RF.obj ((Plus.singleFunctor A n).obj I) ≅ (Plus.singleFunctor B n).obj (F.obj I) :=
  have := isIso_app_singleFunctor_obj_of_injective F RF α n I
  Plus.ι.preimageIso
    (Plus.ι.mapIso (RF.mapIso ((singleFunctorPlusIsoCompQh n).app I) ≪≫
        (asIso (α.app ((HomotopyCategory.Plus.singleFunctor A n).obj I))).symm) ≪≫
      Qh.mapIso ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app
        ((CochainComplex.singleFunctor A n).obj I)) ≪≫
      (quotientCompQhIso B).app _ ≪≫
      Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).app I))

include F α in
/-- The homology of `RF(I[n])` vanishes in every degree `i ≠ n` when `I` is injective. -/
private lemma isZero_homologyFunctor_obj_obj_singleFunctor_obj (i n : ℤ) (hi : i ≠ n)
    (I : A) [Injective I] :
    IsZero ((Plus.homologyFunctor B i).obj (RF.obj ((Plus.singleFunctor A n).obj I))) :=
  (isZero_homologyFunctor_obj_singleFunctor_obj i n hi (F.obj I)).of_iso
    ((Plus.homologyFunctor B i).mapIso (objSingleFunctorObjIso F RF α n I))

end

/-- **Injective objects are right acyclic**, [Stacks, Tag 015B] part (3): if `F : 𝒜 ⥤ ℬ` is an
additive functor between abelian categories, `𝒜` has enough injectives and `I` is an injective
object of `𝒜`, then the higher right derived functors of `F` vanish on `I` outside degree `0`:
`R ⁱ F (I) = 0` for `i ≠ 0`.

The source states this for `i > 0` and a left exact `F`; neither restriction is needed, as
`RF(I[0])` is `F(I)[0]`. -/
@[stacks 015B "part (3), for i ≠ 0 and an arbitrary additive functor",
  ega "0 17.2.2" "(ii), special case"]
public theorem isZero_rightDerivedPlus_obj_injective {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [EnoughInjectives A] (i : ℤ) (hi : i ≠ 0) (I : A) [Injective I] :
    IsZero ((F.rightDerivedPlus i).obj I) :=
  isZero_homologyFunctor_obj_obj_singleFunctor_obj F F.rightDerivedFunctorPlus
    F.rightDerivedFunctorPlusUnith i 0 hi I

-- `hasPointwiseRightDerivedFunctorAt_of_injective` above applies to an arbitrary functor out of
-- `K⁺(𝒜)` at an arbitrary object, so instance search reaches for it before the instance that
-- gets the same conclusion from `EnoughInjectives 𝒜`, and then embarks on proving termwise
-- injectivity of an unknown complex. The results below mention `F.rightDerivedFunctorPlus`, which
-- needs that conclusion at every object, so the cheap instance is given precedence here.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section

variable {A : Type*} [Category* A] [Abelian A]

/-- The object of `K⁺(A)` attached to a bounded below cochain complex. -/
public abbrev plusObj (K : CochainComplex A ℤ) (hK : CochainComplex.plus A K) :
    HomotopyCategory.Plus A :=
  (HomotopyCategory.Plus.quotient A).obj ⟨K, hK⟩

variable [HasDerivedCategory A]


/-- The image in `D⁺(A)` of a bounded below cochain complex, computed through the bounded below
homotopy category, is its image under `DerivedCategory.Plus.Q`. -/
noncomputable def qhQuotientIso (N : CochainComplex.Plus A) :
    Plus.Qh.obj ((HomotopyCategory.Plus.quotient A).obj N) ≅ Plus.Q.obj N :=
  Plus.ι.preimageIso
    ((Plus.QhCompιIsoιCompQh A).app _ ≪≫
      Qh.mapIso ((HomotopyCategory.Plus.quotientCompιIso A).app N) ≪≫
      (quotientCompQhIso A).app N.obj)

/-- The image in `D⁺(A)` of a cochain complex lying in degrees `≥ n` is `≥ n`. -/
lemma isGE_Q_obj (N : CochainComplex.Plus A) (n : ℤ) [N.obj.IsStrictlyGE n] :
    (Plus.Q.obj N).IsGE n := by
  rw [← Plus.isGE_ι_obj_iff]
  change (Q.obj N.obj).IsGE n
  have : N.obj.IsGE n := inferInstance
  infer_instance

/-- The image in `D⁺(A)` of a bounded below complex lying in degrees `≥ m`, computed through the
bounded below homotopy category, is `≥ m`. -/
lemma isGE_Qh_obj (L : CochainComplex A ℤ) (hL : CochainComplex.plus A L) (m : ℤ)
    (hm : CochainComplex.IsStrictlyGE L m) :
    (Plus.Qh.obj (plusObj L hL)).IsGE m := by
  have := hm
  have := isGE_Q_obj (⟨L, hL⟩ : CochainComplex.Plus A) m
  exact Plus.TStructure.t.isGE_of_iso (qhQuotientIso (⟨L, hL⟩ : CochainComplex.Plus A)).symm m

end

section

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B] (F : A ⥤ B)
  [F.Additive]

/-- `HomotopyCategory.singleFunctor` commutes with `F` and `F.mapHomotopyCategory`. This is the
homotopy category analogue of `CategoryTheory.Functor.mapCochainComplexSingleFunctor`, and like
it needs only the additivity of `F`. -/
public noncomputable def mapHomotopyCategorySingleFunctor (n : ℤ) :
    HomotopyCategory.singleFunctor A n ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      F ⋙ HomotopyCategory.singleFunctor B n :=
  Functor.isoWhiskerRight (HomotopyCategory.singleFunctorPostcompQuotientIso A n) _ ≪≫
    Functor.associator .. ≪≫
    Functor.isoWhiskerLeft _ (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)) ≪≫
    (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight
      (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n) _ ≪≫
    Functor.associator .. ≪≫
    Functor.isoWhiskerLeft F (HomotopyCategory.singleFunctorPostcompQuotientIso B n).symm

variable [HasDerivedCategory B]

/-- `F` commutes with `A ↦ A[n]`: the composite `A ↦ Qh(F(A[n]))`, which is the source of the
unit of a right derived functor of `F` at `A[n]`, is `A ↦ F(A)[n]`.

Every factor of the construction is already indexed by the degree, so the degree is only carried
along. The case `n = 0` is `CategoryTheory.Functor.mapSingleFunctorCompQhIso`, the spelling in
which the unit of a right derived functor is read in
`CategoryTheory.Functor.isoRightDerivedPlusZero`; the general case is what the degree-`n` form
`CategoryTheory.Functor.isoRightDerivedPlusSingle` of that isomorphism is read through. -/
public noncomputable def mapSingleFunctorCompQhIsoOfDegree (n : ℤ) :
    HomotopyCategory.Plus.singleFunctor A n ⋙ F.mapHomotopyCategoryPlus ⋙ Plus.Qh ≅
      F ⋙ Plus.singleFunctor B n :=
  Functor.fullyFaithfulCancelRight Plus.ι
    (((Functor.associator (HomotopyCategory.singleFunctor A n)
          (F.mapHomotopyCategory (ComplexShape.up ℤ)) DerivedCategory.Qh).symm ≪≫
        Functor.isoWhiskerRight (mapHomotopyCategorySingleFunctor F n) DerivedCategory.Qh ≪≫
        Functor.associator F (HomotopyCategory.singleFunctor B n) DerivedCategory.Qh ≪≫
        Functor.isoWhiskerLeft F (DerivedCategory.singleFunctorIsoCompQh B n).symm :
      _ ≅ F ⋙ DerivedCategory.singleFunctor B n))

/-- `F` commutes with `A ↦ A[0]`: the composite `A ↦ Qh(F(A[0]))`, which is the source of the
unit of a right derived functor of `F` at `A[0]`, is `A ↦ F(A)[0]`. This is the degree-zero case
of `CategoryTheory.Functor.mapSingleFunctorCompQhIsoOfDegree`. -/
public noncomputable def mapSingleFunctorCompQhIso :
    HomotopyCategory.Plus.singleFunctor A 0 ⋙ F.mapHomotopyCategoryPlus ⋙ Plus.Qh ≅
      F ⋙ Plus.singleFunctor B 0 :=
  mapSingleFunctorCompQhIsoOfDegree F 0

end

section

open Pretriangulated

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]

/-- A natural transformation between two functors that preserve the kernel of `g : Y₀ ⟶ Y₁` is
invertible at any kernel of `g` as soon as it is invertible at `Y₀` and at `Y₁`. -/
public lemma isIso_app_of_isLimit_kernelFork {G₁ G₂ : A ⥤ B}
    [G₁.PreservesZeroMorphisms] [G₂.PreservesZeroMorphisms]
    {X Y₀ Y₁ : A} {f : X ⟶ Y₀} {g : Y₀ ⟶ Y₁} (w : f ≫ g = 0)
    [PreservesLimit (parallelPair g 0) G₁] [PreservesLimit (parallelPair g 0) G₂]
    (η : G₁ ⟶ G₂) (hf : IsLimit (KernelFork.ofι f w))
    [IsIso (η.app Y₀)] [IsIso (η.app Y₁)] : IsIso (η.app X) := by
  have k₁ := KernelFork.mapIsLimit _ hf G₁
  have k₂ := KernelFork.mapIsLimit _ hf G₂
  have hnat : CategoryTheory.inv (η.app Y₀) ≫ G₁.map g =
      G₂.map g ≫ CategoryTheory.inv (η.app Y₁) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← η.naturality g, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  have w₂ : (G₂.map f ≫ CategoryTheory.inv (η.app Y₀)) ≫ G₁.map g = 0 := by
    rw [Category.assoc, hnat, ← Category.assoc, ← G₂.map_comp, w, G₂.map_zero, zero_comp]
  have hl : k₁.lift (KernelFork.ofι _ w₂) ≫ G₁.map f =
      G₂.map f ≫ CategoryTheory.inv (η.app Y₀) :=
    k₁.fac (KernelFork.ofι _ w₂) WalkingParallelPair.zero
  refine ⟨k₁.lift (KernelFork.ofι _ w₂), ?_, ?_⟩
  · refine Fork.IsLimit.hom_ext k₁ ?_
    dsimp
    rw [Category.assoc, hl, ← Category.assoc, ← η.naturality f, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
  · refine Fork.IsLimit.hom_ext k₂ ?_
    dsimp
    rw [Category.assoc, ← η.naturality f, ← Category.assoc, hl, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- An injective resolution of `X : A`, read in the bounded below homotopy category: a
quasi-isomorphism from the complex `X[0]` to a complex of injective objects which is
concentrated in degrees `≥ 0`. -/
@[sga "2 VIII 1.4" "special case"]
private lemma exists_quasiIso_injective_single [EnoughInjectives A] (X : A) :
    ∃ (L : CochainComplex.Plus A) (_ : ∀ n, Injective (L.obj.X n))
      (_ : CochainComplex.IsStrictlyGE L.obj 0)
      (s : (HomotopyCategory.Plus.singleFunctor A 0).obj X ⟶
        (HomotopyCategory.Plus.quotient A).obj L),
        HomotopyCategory.Plus.quasiIso A s := by
  obtain ⟨L, hL, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective
    (⟨(CochainComplex.singleFunctor A 0).obj X, 0, inferInstance⟩ : CochainComplex.Plus A) 0
  refine ⟨(InjectiveObject.ι A).mapCochainComplexPlus.obj L, fun n => (L.obj.X n).property,
    inferInstanceAs (CochainComplex.IsStrictlyGE
      (((InjectiveObject.ι A).mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj) 0),
    (HomotopyCategory.Plus.quotient A).map i, ?_⟩
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff (C := A)
    (c := ComplexShape.up ℤ) i.hom).2 hi

/-- The distinguished triangle in `D⁺(A)` attached to a short exact sequence of `A`. -/
public lemma exists_distTriang_singleFunctor [HasDerivedCategory A]
    {S : ShortComplex A} (hS : S.ShortExact) :
    ∃ δ, Triangle.mk ((Plus.singleFunctor A 0).map S.f) ((Plus.singleFunctor A 0).map S.g) δ
      ∈ distTriang (DerivedCategory.Plus A) := by
  obtain ⟨δ, hδ⟩ : ∃ δ : (Plus.singleFunctor A 0).obj S.X₃ ⟶
      ((Plus.singleFunctor A 0).obj S.X₁)⟦(1 : ℤ)⟧,
      Plus.ι.map δ ≫ (Plus.ι.commShiftIso (1 : ℤ)).hom.app
        ((Plus.singleFunctor A 0).obj S.X₁) = hS.singleδ :=
    ⟨Plus.ι.preimage (hS.singleδ ≫ (Plus.ι.commShiftIso (1 : ℤ)).inv.app
      ((Plus.singleFunctor A 0).obj S.X₁)), by
        rw [Functor.map_preimage]
        exact (Iso.eq_comp_inv ((Plus.ι.commShiftIso (1 : ℤ)).app
          ((Plus.singleFunctor A 0).obj S.X₁))).1 rfl⟩
  refine ⟨δ, ?_⟩
  rw [← Plus.ι.map_distinguished_iff]
  refine isomorphic_distinguished _ hS.singleTriangle_distinguished _
    (Triangle.isoMk _ _ ((Plus.singleFunctorιIso A 0).app S.X₁)
      ((Plus.singleFunctorιIso A 0).app S.X₂) ((Plus.singleFunctorιIso A 0).app S.X₃)
      ?_ ?_ ?_)
  · exact (Plus.singleFunctorιIso A 0).hom.naturality S.f
  · exact (Plus.singleFunctorιIso A 0).hom.naturality S.g
  · change (Plus.ι.map δ ≫ (Plus.ι.commShiftIso (1 : ℤ)).hom.app
          ((Plus.singleFunctor A 0).obj S.X₁)) ≫
        (shiftFunctor (DerivedCategory A) (1 : ℤ)).map
          (𝟙 ((DerivedCategory.singleFunctor A 0).obj S.X₁)) =
      𝟙 ((DerivedCategory.singleFunctor A 0).obj S.X₃) ≫ hS.singleδ
    exact (congrArg (fun v => (Plus.ι.map δ ≫ (Plus.ι.commShiftIso (1 : ℤ)).hom.app
          ((Plus.singleFunctor A 0).obj S.X₁)) ≫ v)
        (CategoryTheory.Functor.map_id (shiftFunctor (DerivedCategory A) (1 : ℤ))
          ((DerivedCategory.singleFunctor A 0).obj S.X₁))).trans
      ((Category.comp_id _).trans (hδ.trans (Category.id_comp _).symm))

section

variable (F : A ⥤ B) [F.Additive]

/-- The functor `F.mapHomotopyCategoryPlus` between bounded below homotopy categories is
induced by `F.mapHomotopyCategory (ComplexShape.up ℤ)`. -/
public noncomputable def mapHomotopyCategoryPlusCompιIso :
    F.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι B ≅
      HomotopyCategory.Plus.ι A ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) :=
  ObjectProperty.liftCompιIso ..

/-- `HomotopyCategory.Plus.singleFunctor` commutes with `F` and `F.mapHomotopyCategoryPlus`. -/
public noncomputable def mapHomotopyCategoryPlusSingleFunctor (n : ℤ) :
    HomotopyCategory.Plus.singleFunctor A n ⋙ F.mapHomotopyCategoryPlus ≅
      F ⋙ HomotopyCategory.Plus.singleFunctor B n :=
  Functor.fullyFaithfulCancelRight (HomotopyCategory.Plus.ι B)
    (Functor.associator .. ≪≫
      Functor.isoWhiskerLeft (HomotopyCategory.Plus.singleFunctor A n)
        (mapHomotopyCategoryPlusCompιIso F) ≪≫
      (Functor.associator ..).symm ≪≫
      Functor.isoWhiskerRight (HomotopyCategory.Plus.singleFunctorCompιIso A n)
        (F.mapHomotopyCategory (ComplexShape.up ℤ)) ≪≫
      mapHomotopyCategorySingleFunctor F n ≪≫
      Functor.isoWhiskerLeft F (HomotopyCategory.Plus.singleFunctorCompιIso B n).symm ≪≫
      (Functor.associator ..).symm)

end

variable [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]
  [EnoughInjectives A]
  (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
  (α : F.mapHomotopyCategoryPlus ⋙ Plus.Qh ⟶ Plus.Qh ⋙ RF)

/-- The unit of a right derived functor is invertible at a complex of injective objects. -/
private lemma isIso_α_app_quotient_obj
    [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso A)]
    (L : CochainComplex.Plus A) [inst : ∀ n, Injective (L.obj.X n)] :
    IsIso (α.app ((HomotopyCategory.Plus.quotient A).obj L)) := by
  have : ∀ n : ℤ, Injective (((HomotopyCategory.Plus.quotient A).obj L).obj.as.X n) :=
    fun n => inferInstance
  infer_instance

/-- `RF(X[0])` is cohomologically `≥ 0`: it is computed by `F` on an injective resolution
of `X`, which is a complex concentrated in degrees `≥ 0`. -/
private lemma isGE_RF_obj_single
    [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso A)] (X : A) :
    (RF.obj ((Plus.singleFunctor A 0).obj X)).IsGE 0 := by
  obtain ⟨L, hLinj, hLge, s, hs⟩ := exists_quasiIso_injective_single (A := A) X
  have hiso : IsIso (α.app ((HomotopyCategory.Plus.quotient A).obj L)) :=
    isIso_α_app_quotient_obj F RF α L (inst := hLinj)
  have : IsIso (Plus.Qh.map s) :=
    Localization.inverts Plus.Qh (HomotopyCategory.Plus.quasiIso A) s hs
  have : CochainComplex.IsStrictlyGE (F.mapCochainComplexPlus.obj L).obj 0 :=
    inferInstanceAs (CochainComplex.IsStrictlyGE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj) 0)
  have h : (Plus.Qh.obj ((HomotopyCategory.Plus.quotient B).obj
      (F.mapCochainComplexPlus.obj L))).IsGE 0 :=
    isGE_Qh_obj (F.mapCochainComplexPlus.obj L).obj
      (F.mapCochainComplexPlus.obj L).property 0 inferInstance
  refine Plus.TStructure.t.isGE_of_iso
    (?_ : Plus.Qh.obj ((HomotopyCategory.Plus.quotient B).obj (F.mapCochainComplexPlus.obj L)) ≅
      RF.obj ((Plus.singleFunctor A 0).obj X)) 0
  exact @asIso _ _ _ _ (α.app ((HomotopyCategory.Plus.quotient A).obj L)) hiso ≪≫
    (RF.mapIso (asIso (Plus.Qh.map s))).symm ≪≫
    (RF.mapIso ((singleFunctorPlusIsoCompQh 0).app X)).symm

/-- Part (1) of [Stacks, Tag 05TD]: `R ⁱ F = 0` for `i < 0`. -/
private lemma isZero_singleFunctor_comp_homologyFunctor
    [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso A)] (i : ℤ) (hi : i < 0) :
    IsZero (Plus.singleFunctor A 0 ⋙ RF ⋙ Plus.homologyFunctor B i) := by
  rw [Functor.isZero_iff]
  intro X
  have := isGE_RF_obj_single F RF α X
  exact Plus.isZero_homology_of_isGE _ 0 i hi

/-- Part (2) of [Stacks, Tag 05TD]: `R ⁰ F` is left exact. A short exact sequence of `A`
gives a distinguished triangle of `D⁺(A)`, whose image under the triangulated functor `RF` is
distinguished, and the long exact homology sequence of the homological functor `H ⁰` is exact
at the first two spots because `R⁻¹ F = 0`. -/
private lemma preservesFiniteLimits_singleFunctor_comp_homologyFunctor
    [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso A)] :
    PreservesFiniteLimits (Plus.singleFunctor A 0 ⋙ RF ⋙ Plus.homologyFunctor B 0) := by
  let := Functor.IsRightDerivedFunctor.commShift RF α (HomotopyCategory.Plus.quasiIso A) ℤ
  let := Functor.IsRightDerivedFunctor.natTrans_commShift RF α
    (HomotopyCategory.Plus.quasiIso A) ℤ
  have := isTriangulated_of_isRightDerivedFunctor_mapHomotopyCategoryPlus F RF α
  have : (Plus.singleFunctor A 0 ⋙ RF ⋙ Plus.homologyFunctor B 0).Additive := inferInstance
  rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  obtain ⟨δ, hT⟩ := exists_distTriang_singleFunctor (A := A) hS
  have hT' : RF.mapTriangle.obj
      (Triangle.mk ((Plus.singleFunctor A 0).map S.f) ((Plus.singleFunctor A 0).map S.g) δ)
        ∈ distTriang (DerivedCategory.Plus B) := RF.map_distinguished _ hT
  have hz : IsZero (((Plus.homologyFunctor B 0).shift (-1 : ℤ)).obj
      (RF.obj ((Plus.singleFunctor A 0).obj S.X₃))) := by
    have := isGE_RF_obj_single F RF α S.X₃
    exact Plus.isZero_homology_of_isGE _ 0 (-1) (by norm_num)
  refine ⟨(Plus.homologyFunctor B 0).homologySequence_exact₂ _ hT' 0, ?_⟩
  exact ((Plus.homologyFunctor B 0).homologySequence_mono_shift_map_mor₁_iff
    _ hT' (-1) 0 (by ring)).2 (hz.eq_of_src _ _)

/-- The source of `H ⁰(α)` at the complexes `X[0]` is `F`. -/
public noncomputable def rightDerivedZeroSourceIso :
    (HomotopyCategory.Plus.singleFunctor A 0 ⋙ F.mapHomotopyCategoryPlus ⋙ Plus.Qh) ⋙
      Plus.homologyFunctor B 0 ≅ F :=
  Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (mapHomotopyCategoryPlusSingleFunctor F 0) Plus.Qh ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F (singleFunctorPlusIsoCompQh (A := B) 0).symm)
      (Plus.homologyFunctor B 0) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F (Plus.singleFunctorCompHomologyFunctorIso (C := B) 0) ≪≫
    Functor.rightUnitor F

/-- The target of `H ⁰(α)` at the complexes `X[0]` is `R ⁰ F`. -/
public noncomputable def rightDerivedZeroTargetIso :
    (HomotopyCategory.Plus.singleFunctor A 0 ⋙ Plus.Qh ⋙ RF) ⋙ Plus.homologyFunctor B 0 ≅
      Plus.singleFunctor A 0 ⋙ RF ⋙ Plus.homologyFunctor B 0 :=
  Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (singleFunctorPlusIsoCompQh (A := A) 0).symm RF)
      (Plus.homologyFunctor B 0) ≪≫
    Functor.associator _ _ _

/-- Part (3) of [Stacks, Tag 05TD]: the canonical map `F ⟶ R ⁰ F` is an isomorphism if and
only if `F` is left exact.

Both directions go through the natural transformation `H ⁰(α)` at the complexes `X[0]`, whose
source is identified with `F` by `rightDerivedZeroSourceIso` and whose target with `R ⁰ F` by
`rightDerivedZeroTargetIso`.

Granted that, `⇒` is part (2) together with
`CategoryTheory.Limits.preservesFiniteLimits_of_natIso`, since the hypothesis then exhibits
`F ≅ R ⁰ F`.

For `⇐`, both `F` and `R ⁰ F` are left exact, and `H ⁰(α)` is invertible at an injective object
(`isIso_app_singleFunctor_obj_of_injective`). A transformation of left exact functors that is
invertible on injective objects is invertible everywhere, because every object of `A` is a
kernel of a map between two injective objects, namely the first two terms of an injective
resolution (`isIso_app_of_isLimit_kernelFork` applied to
`CategoryTheory.InjectiveResolution.isLimitKernelFork`). This is the same mathematics as
`CategoryTheory.InjectiveResolution.toRightDerivedZero'` and the instance
`CategoryTheory.InjectiveResolution.instIsIsoToRightDerivedZero'`, which Mathlib proves in the
`ℕ`-indexed model of injective resolutions. -/
private lemma isIso_homologyFunctor_map_α_app_iff
    [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso A)] :
    (∀ X : A, IsIso ((Plus.homologyFunctor B 0).map
        (α.app ((HomotopyCategory.Plus.singleFunctor A 0).obj X)))) ↔
      PreservesFiniteLimits F := by
  have h₂ := preservesFiniteLimits_singleFunctor_comp_homologyFunctor F RF α
  set β := Functor.whiskerRight (Functor.whiskerLeft
    (HomotopyCategory.Plus.singleFunctor A 0) α) (Plus.homologyFunctor B 0)
  have hβ : ∀ X : A, β.app X = (Plus.homologyFunctor B 0).map
      (α.app ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) := fun _ => rfl
  constructor
  · intro h
    have : ∀ X, IsIso (β.app X) := fun X => (hβ X) ▸ h X
    have : IsIso β := NatIso.isIso_of_isIso_app β
    exact preservesFiniteLimits_of_natIso
      ((rightDerivedZeroSourceIso F).symm ≪≫ asIso β ≪≫ rightDerivedZeroTargetIso RF).symm
  · intro hF X
    have i₁ : PreservesFiniteLimits ((HomotopyCategory.Plus.singleFunctor A 0 ⋙
        F.mapHomotopyCategoryPlus ⋙ Plus.Qh) ⋙ Plus.homologyFunctor B 0) :=
      preservesFiniteLimits_of_natIso (rightDerivedZeroSourceIso F).symm
    have i₂ : PreservesFiniteLimits ((HomotopyCategory.Plus.singleFunctor A 0 ⋙
        Plus.Qh ⋙ RF) ⋙ Plus.homologyFunctor B 0) :=
      preservesFiniteLimits_of_natIso (rightDerivedZeroTargetIso RF).symm
    have hinj : ∀ I : A, Injective I → IsIso (β.app I) := by
      intro I hI
      rw [hβ]
      have := isIso_app_singleFunctor_obj_of_injective F RF α 0 I
      infer_instance
    have P := injectiveResolution X
    have h₀ := hinj (P.cocomplex.X 0) (P.injective 0)
    have h₁ := hinj (P.cocomplex.X 1) (P.injective 1)
    rw [← hβ]
    exact isIso_app_of_isLimit_kernelFork P.ι_f_zero_comp_complex_d β P.isLimitKernelFork

end

/-- **Right deriving is for left exact functors**, [StacksProject 05TD].
Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories, where `𝒜` has enough
injectives, and let `RF : D⁺(𝒜) ⥤ D⁺(ℬ)`, with unit `α`, be a right derived functor of `F`
(which is then defined everywhere), so that `R ⁱ F = H ⁱ ∘ RF ∘ (·[0])`. Then
1. `R ⁱ F = 0` for `i < 0`,
2. `R ⁰ F` is left exact, and
3. the canonical map `F ⟶ R ⁰ F`, that is `H ⁰(α)` at the complexes `X[0]`, is an
   isomorphism if and only if `F` is left exact. -/
@[stacks 05TD "T_05TD", sga "2 IV 1.1"]
public theorem isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]
    [EnoughInjectives A]
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (α : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso A)] :
    (∀ i < 0, IsZero (DerivedCategory.Plus.singleFunctor A 0 ⋙ RF ⋙
        DerivedCategory.Plus.homologyFunctor B i)) ∧
      PreservesFiniteLimits (DerivedCategory.Plus.singleFunctor A 0 ⋙ RF ⋙
        DerivedCategory.Plus.homologyFunctor B 0) ∧
      ((∀ X : A, IsIso ((DerivedCategory.Plus.homologyFunctor B 0).map
          (α.app ((HomotopyCategory.Plus.singleFunctor A 0).obj X)))) ↔
        PreservesFiniteLimits F) :=
  ⟨fun i hi => isZero_singleFunctor_comp_homologyFunctor F RF α i hi,
    preservesFiniteLimits_singleFunctor_comp_homologyFunctor F RF α,
    isIso_homologyFunctor_map_α_app_iff F RF α⟩

section

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]

/-- The homology of `Qh(F(A[0]))` vanishes outside degree `0`, that complex being concentrated
in degree `0`. -/
private lemma isZero_homologyFunctor_obj_map_singleFunctor_obj (A : C) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((Plus.homologyFunctor D i).obj ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).obj
      ((HomotopyCategory.Plus.singleFunctor C 0).obj A))) :=
  (isZero_homologyFunctor_obj_singleFunctor_obj i 0 hi (F.obj A)).of_iso
    ((Plus.homologyFunctor D i).mapIso ((mapSingleFunctorCompQhIso F).app A))

end

section

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive] [EnoughInjectives C]

/-- `R ⁱ F(A)` is the `i`-th homology of the target of the unit of `RF` at `A[0]`. -/
private noncomputable def rightDerivedPlusObjIso (A : C) (i : ℤ) :
    (F.rightDerivedPlus i).obj A ≅ (Plus.homologyFunctor D i).obj
      ((Plus.Qh ⋙ F.rightDerivedFunctorPlus).obj
        ((HomotopyCategory.Plus.singleFunctor C 0).obj A)) :=
  (Plus.homologyFunctor D i).mapIso
    (F.rightDerivedFunctorPlus.mapIso ((singleFunctorPlusIsoCompQh 0).app A))

/-- Part (1) of [Stacks, Tag 015C]. -/
private lemma rightAcyclic_iff (A : C) :
    F.rightAcyclic A ↔
      (IsIso ((Plus.homologyFunctor D 0).map (F.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.singleFunctor C 0).obj A))) ∧
        ∀ i > 0, IsZero ((F.rightDerivedPlus i).obj A)) := by
  have hsrc := isZero_homologyFunctor_obj_map_singleFunctor_obj F A
  have hneg : ∀ i < 0, IsZero ((Plus.homologyFunctor D i).obj
      ((Plus.Qh ⋙ F.rightDerivedFunctorPlus).obj
        ((HomotopyCategory.Plus.singleFunctor C 0).obj A))) := fun i hi =>
    IsZero.of_iso (((Functor.isZero_iff _).1
      ((isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
        F F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnith).1 i hi) A))
      (rightDerivedPlusObjIso F A i).symm
  constructor
  · intro h
    have h' : IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor C 0).obj A)) := h
    refine ⟨inferInstance, fun i hi => ?_⟩
    exact IsZero.of_iso (IsZero.of_iso (hsrc i hi.ne')
      (asIso ((Plus.homologyFunctor D i).map (F.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj A)))).symm)
      (rightDerivedPlusObjIso F A i)
  · rintro ⟨h₀, hpos⟩
    change IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor C 0).obj A))
    rw [Plus.isIso_iff]
    intro i
    rcases lt_trichotomy i 0 with hi | rfl | hi
    · exact (hsrc i hi.ne).isIso (hneg i hi) _
    · exact h₀
    · exact (hsrc i hi.ne').isIso
        (IsZero.of_iso (hpos i hi) (rightDerivedPlusObjIso F A i).symm) _

/-- Part (2) of [Stacks, Tag 015C]: for a left exact `F`, the degree `0` condition of part (1)
holds automatically, by [Stacks, Tag 05TD] part (3). -/
private lemma rightAcyclic_iff_of_preservesFiniteLimits (A : C)
    (hF : PreservesFiniteLimits F) :
    F.rightAcyclic A ↔ ∀ i > 0, IsZero ((F.rightDerivedPlus i).obj A) := by
  rw [rightAcyclic_iff F A]
  exact and_iff_right
    ((isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
      F F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnith).2.2.2 hF A)

end

/-- **Characterization of right acyclic objects**, [StacksProject 015C].
Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories, where `𝒜` has enough
injectives, so that the right derived functor `RF : D⁺(𝒜) ⥤ D⁺(ℬ)`, with unit `α`, is
everywhere defined and `R ⁱ F = H ⁱ ∘ RF ∘ (·[0])`. Let `A` be an object of `𝒜`. Then
1. `A` is right acyclic for `F` if and only if the canonical map `F(A) ⟶ R ⁰ F(A)`, that is
   `H ⁰(α)` at `A[0]`, is an isomorphism and `R ⁱ F(A) = 0` for all `i > 0`, and
2. if `F` is left exact, then `A` is right acyclic for `F` if and only if `R ⁱ F(A) = 0` for
   all `i > 0`. -/
@[stacks 015C, sga "4 V 0.4"]
public theorem rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
    [EnoughInjectives C] (A : C) :
    (F.rightAcyclic A ↔
        (IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
            (F.rightDerivedFunctorPlusUnith.app
              ((HomotopyCategory.Plus.singleFunctor C 0).obj A))) ∧
          ∀ i > 0, IsZero ((F.rightDerivedPlus i).obj A))) ∧
      (PreservesFiniteLimits F →
        (F.rightAcyclic A ↔ ∀ i > 0, IsZero ((F.rightDerivedPlus i).obj A))) :=
  ⟨rightAcyclic_iff F A, fun hF => rightAcyclic_iff_of_preservesFiniteLimits F A hF⟩

end CategoryTheory.Functor

end
