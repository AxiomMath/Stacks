module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative

/-!
# Iterated pushforward along closed immersions, and the reduction of Stacks 09VC to Stacks 09VA

`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff` says that at a closed
immersion `i` the local condition of Stacks 09UI is pseudo-coherence of
`(Scheme.Modules.pushforward i).mapDerivedCategory.obj E`. To chain two closed immersions one
therefore needs to know that `mapDerivedCategory` is compatible with composition of functors, and
that `Scheme.Modules.pushforward` is compatible with composition of morphisms. This file supplies
the first — for an arbitrary pair of exact functors between abelian categories with derived
categories — and combines the two.

With that in hand, Stacks 09VC follows from Stacks 09VA by the argument the source gives. Two
closed immersions `i : X ⟶ 𝔸ⁿ_S` and `j : X ⟶ 𝔸ᵐ_S` over `S` are dominated by a single one:
`AlgebraicGeometry.AffineSpace.exists_isClosedImmersion_fin_add` produces closed immersions
`k : 𝔸ⁿ_S ⟶ 𝔸ⁿ⁺ᵐ_S` and `l : 𝔸ᵐ_S ⟶ 𝔸ⁿ⁺ᵐ_S` over `S` with `i ≫ k = j ≫ l`. Pseudo-coherence of
`i_*E` transports forward along `k` and back along `l`, and `i ≫ k = j ≫ l` identifies the two
intermediate objects. Only the transport is missing, and that transport *is* Stacks 09VA; it is
carried here as an explicit hypothesis, so that
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_of_transport`
is a complete proof of Stacks 09VC from Stacks 09VA, with no further gap.

## Main results

* `CategoryTheory.Functor.mapDerivedCategoryCompIsoOfCompIso`: an isomorphism `F ⋙ G ≅ H` of exact functors
  induces `F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory`.
* `CategoryTheory.Functor.mapDerivedCategoryCongr`: isomorphic exact functors induce isomorphic
  functors on derived categories.
* `AlgebraicGeometry.Scheme.Modules.mapDerivedCategoryPushforwardComp`: for closed immersions
  `f` and `g`, `f_*` followed by `g_*` on derived categories is `(f ≫ g)_*`.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_comp_iff`: the local
  condition of Stacks 09UI for a composite of closed immersions is pseudo-coherence of the
  iterated pushforward.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_of_transport`:
  **Stacks 09VC assuming Stacks 09VA.**

## Implementation notes

`CategoryTheory.Functor.mapDerivedCategoryCompIsoOfCompIso` is **not** built here. The development already
compares the degreewise action of a composite with the composite of the degreewise actions, in
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso`, and already transports the
degreewise action along an isomorphism of exact functors, in
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso`; the twisted comparison is their
composite, and that is how it is defined, so that the project has one construction of this
comparison rather than two. The evaluation
`CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_Q` on the image of a cochain complex is
unchanged, and it is the only thing any consumer uses.

`CategoryTheory.Functor.mapDerivedCategoryCongr`, on the other hand, is still obtained from
`CategoryTheory.Localization.liftNatIso` directly: `CategoryTheory.Functor.mapDerivedCategory` is
defined by lifting `F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q` through the
localization `DerivedCategory.Q`, Mathlib registers the corresponding
`CategoryTheory.Localization.Lifting` instance, and it suffices to produce the isomorphism of the
two composites with `DerivedCategory.Q`, which is `NatIso.mapHomologicalComplex`.

In the proof of Stacks 09VC the equality `i ≫ k = j ≫ l` cannot be used by `rw`: the goal mentions
`(Scheme.Modules.pushforward (i ≫ k)).mapDerivedCategory`, whose elaboration depends on the
instance `IsClosedImmersion (i ≫ k)`, so the rewrite motive is not type correct. It is used
through `AlgebraicGeometry.Scheme.Modules.pushforwardCongr` and
`CategoryTheory.Functor.mapDerivedCategoryCongr` instead.

The transport hypothesis is stated for closed immersions between affine spaces over `S` *over* `S`
— which is the only case the proof of Stacks 09VC needs, and the case in which the side condition
of Stacks 09VA (that the pushforward of the structure sheaf is pseudo-coherent) holds, because such
a closed immersion is cut out by a regular sequence of coordinates. Restricting the hypothesis this
way makes it weaker, hence the reduction stronger.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 36.61.2 (09VC)](https://stacks.math.columbia.edu/tag/09VC)
* [The Stacks Project, Lemma 36.60.9 (09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace CategoryTheory.Functor

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

section CompIso

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- An isomorphism `F ⋙ G ≅ H` between exact functors of abelian categories induces an
isomorphism `F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory`.

It is the untwisted comparison
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso`, which identifies
`(F ⋙ G).mapDerivedCategory` with `F.mapDerivedCategory ⋙ G.mapDerivedCategory`, followed by the
degreewise change of functor `Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso`
that `e` induces.  Both of those are lifts through the localization `DerivedCategory.Q`, so this
one is too, and `CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_Q` evaluates it on the
image of a cochain complex. -/
public def mapDerivedCategoryCompIsoOfCompIso
    {F : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {G : C₂ ⥤ C₃} [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {H : C₁ ⥤ C₃} [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory :=
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F G).symm ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso (F ⋙ G) H e

end CompIso

/-- Isomorphic exact functors of abelian categories induce isomorphic functors on derived
categories: the two lifts through `DerivedCategory.Q` are identified by
`NatIso.mapHomologicalComplex`. -/
public def mapDerivedCategoryCongr
    {F G : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    _ _
    (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e _) DerivedCategory.Q)

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.Modules

universe u

attribute [local instance] HasDerivedCategory.standard

/-- For closed immersions `f : X ⟶ Y` and `g : Y ⟶ Z` of schemes, pushing a complex forward along
`f` and then along `g` is pushing it forward along `f ≫ g`, as functors on derived categories.
Closedness of the immersions is what makes the three pushforwards exact, hence available on
derived categories at all. -/
public def mapDerivedCategoryPushforwardComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsClosedImmersion f] [IsClosedImmersion g] :
    (pushforward f).mapDerivedCategory ⋙ (pushforward g).mapDerivedCategory ≅
      (pushforward (f ≫ g)).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIsoOfCompIso (pushforwardComp f g)

/-- For closed immersions `i : X ⟶ Y` and `k : Y ⟶ Z` of schemes, the local condition of
Stacks 09UI for the composite `i ≫ k` holds for `E` and `m` if and only if the iterated
pushforward `k_*(i_*E)`, formed on derived categories, is `m`-pseudo-coherent on `Z` in the
sheaf-level sense of Stacks 08CB.

This is the form in which the proof of Stacks 09VC consumes the local condition: it factors a
single closed immersion into an affine space over the base through an intermediate affine
space. -/
public theorem isPseudoCoherentFromAfterPushforward_comp_iff {X Y Z : Scheme.{u}} (i : X ⟶ Y)
    (k : Y ⟶ Z) [IsClosedImmersion i] [IsClosedImmersion k] (E : DerivedCategory X.Modules)
    (m : ℤ) :
    IsPseudoCoherentFromAfterPushforward (i ≫ k) E m ↔
      RingedSpace.IsPseudoCoherentFrom (X := Z.toRingedSpace)
        ((pushforward k).mapDerivedCategory.obj
          ((pushforward i).mapDerivedCategory.obj E)) m := by
  rw [isPseudoCoherentFromAfterPushforward_iff]
  exact ⟨fun h => h.of_iso ((mapDerivedCategoryPushforwardComp i k).app E).symm,
    fun h => h.of_iso ((mapDerivedCategoryPushforwardComp i k).app E)⟩

/-- **SUPERSEDED — this statement is vacuous. Use
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_of_transport_fin`
in `StacksFrontier.AlgebraicGeometry.PseudoCoherent.KoszulPushforward` instead.**

The `transport` hypothesis below is asked for at *arbitrary* index types `ι κ : Type u`, and in
that generality it cannot be satisfied: Stacks 09VA does not apply to a closed immersion into an
infinite-dimensional affine space, where the side condition that the pushforward of the structure
sheaf be pseudo-coherent is false. Taking `ι = PEmpty` and `κ = ULift ℕ` with the zero section,
the ideal `(x₀, x₁, …)` is not finitely generated and stays so after inverting any `f` with
`f(0) ≠ 0`. So no consumer can ever discharge this hypothesis, and the claim in the next
paragraph that the proof below leaves "no further gap" is wrong: the gap is that the hypothesis
is unsatisfiable.

The conclusion is correct and the proof is sound; only the hypothesis is over-strong. The
replacement asks for `transport` just at the index types `ULift (Fin a)`, which is all this proof
ever applies it to, with a byte-identical conclusion — so it is strictly stronger, and usable.

**Stacks 09VC, granted Stacks 09VA.** Let `f : X ⟶ S` be a morphism of affine schemes locally
of finite type and let `E` be an object of the derived category of `𝒪_X`-modules. If
`m`-pseudo-coherence of the derived pushforward transports along closed immersions of affine
spaces over `S` — which is Stacks 09VA for those closed immersions, since the pushforward of the
structure sheaf along one of them is pseudo-coherent — then `m`-pseudo-coherence of the derived
pushforward of `E` along *some* closed immersion of `X` into an affine space over `S` factoring
`f` is equivalent to the same along *every* such closed immersion.

The proof is the one in the source. The implication from "every" to "some" is
`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_of_forall` and uses
nothing. For the converse, given closed immersions `i` and `j` factoring `f`,
`AlgebraicGeometry.AffineSpace.exists_isClosedImmersion_fin_add` produces closed immersions `k`
and `l` of their targets into a common affine space over `S`, over `S`, with `i ≫ k = j ≫ l`.
Transporting along `k` and back along `l`, and identifying `(i ≫ k)_*E` with `(j ≫ l)_*E`, carries
the hypothesis on `i` to the conclusion on `j`. -/
public theorem isPseudoCoherentFrom_some_iff_forall_of_transport
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules) (m : ℤ)
    (transport : ∀ {ι κ : Type u} (p : AffineSpace ι S ⟶ AffineSpace κ S) [IsClosedImmersion p],
      p ≫ (AffineSpace.over κ S).hom = (AffineSpace.over ι S).hom →
      ∀ A : DerivedCategory (AffineSpace ι S).Modules,
        RingedSpace.IsPseudoCoherentFrom (X := (AffineSpace ι S).toRingedSpace) A m ↔
          RingedSpace.IsPseudoCoherentFrom (X := (AffineSpace κ S).toRingedSpace)
            ((pushforward p).mapDerivedCategory.obj A) m) :
    (∃ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom = f ∧
          IsPseudoCoherentFromAfterPushforward i E m) ↔
      (∀ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S),
        IsClosedImmersion i →
          i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom = f →
            IsPseudoCoherentFromAfterPushforward i E m) := by
  refine ⟨?_, exists_isPseudoCoherentFromAfterPushforward_of_forall f E m⟩
  rintro ⟨n, i, hi, hiover, hPi⟩ n' j hj hjover
  have := hi
  have := hj
  obtain ⟨k, l, hk, hl, hko, hlo, hkl⟩ :=
    AffineSpace.exists_isClosedImmersion_fin_add i hiover j hjover
  have := hk
  have := hl
  rw [isPseudoCoherentFromAfterPushforward_iff] at hPi
  rw [isPseudoCoherentFromAfterPushforward_iff]
  rw [transport k hko] at hPi
  have h₁ := (isPseudoCoherentFromAfterPushforward_comp_iff i k E m).2 hPi
  rw [isPseudoCoherentFromAfterPushforward_iff] at h₁
  have h₂ := h₁.of_iso ((Functor.mapDerivedCategoryCongr (pushforwardCongr hkl)).app E)
  exact (transport l hlo _).2 ((isPseudoCoherentFromAfterPushforward_comp_iff j l E m).1
    ((isPseudoCoherentFromAfterPushforward_iff _ _ _).2 h₂))

end AlgebraicGeometry.Scheme.Modules

end
