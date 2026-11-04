module

public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCoarsening
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.OlssonLaszloSituation
import StacksCore.Tactic.StacksAttribute

/-!
# A weak Serre subcategory of modules for a finer topology, read for a coarser one

Let `C` be a category carrying two Grothendieck topologies, a finer one `J` (the topology `τ`
of the source) and a coarser one `J'` (the topology `τ'`), and let `R` be a sheaf of rings for
`J`.  Then `R` is also a sheaf of rings for `J'`, and the identity functor of `C` becomes the
comparison morphism of ringed sites

`ε : (C_τ, R_τ) ⟶ (C_τ', R_τ')`

whose direct image `ε_*` reads a `J`-sheaf of modules as a `J'`-sheaf of modules without
touching the underlying presheaf, and whose inverse image `ε^*` is `J`-sheafification.  Those
two functors are `SheafOfModules.ofLE` and `SheafOfModules.sheafifyOfLE`; this file adds their
exactness and then proves the first conclusion of Stacks 07A8.

Given a class `A` of `J`-sheaves of `R`-modules which is a weak Serre subcategory of
`Mod(R_τ)`, the image `A'` of `A` under `ε_*` is a weak Serre subcategory of `Mod(R_τ')`.
Note that the source's first assumption — every object of `A` is a sheaf for the finer
topology — is built into the shape of the statement: `A` is a class of `J`-sheaves of modules
to begin with, so `ε_*` applies to each of its objects.

## Main definitions

* `Stacks.Cohomology.CompareTopologies.pushforward` and `pullback`: `ε_*` and `ε^*`, as short
  names for `SheafOfModules.ofLE` and `SheafOfModules.sheafifyOfLE`.
* `Stacks.Cohomology.CompareTopologies.imageOfLE`: the class `A'`, the image of `A` under
  `ε_*`.

## Main results

* `Stacks.Cohomology.CompareTopologies.prop_pullback_obj`: `ε^*` carries `A'` into `A`.
* `Stacks.Cohomology.CompareTopologies.isIso_unit_app_of_imageOfLE`: the comparison
  `N ⟶ ε_*ε^*N` is invertible for `N` in `A'`.  Together with the previous item and
  `imageOfLE_pushforward_obj` this is the source's statement that `ε_*` and `ε^*` restrict to
  quasi-inverse equivalences between `A` and `A'`.
* `Stacks.Cohomology.CompareTopologies.isEquivalence_liftPushforward`: `ε_*` corestricted to `A'`
  is an equivalence `A ≌ A'`, which is assumption (2) of Stacks 0D7W for `ε`.
* `Stacks.Cohomology.CompareTopologies.isWeakSerre_imageOfLE`: the first conclusion of
  Stacks 07A8 — `A'` is a weak Serre subcategory of `Mod(R_τ')`.
* `Stacks.Cohomology.CompareTopologies.isWeakSerreClass_imageOfLE`: the same conclusion in the
  closure form `CategoryTheory.ObjectProperty.IsWeakSerreClass`.

## The argument

`ε^*` is exact: it preserves finite limits because it forgets to the underlying presheaf of
modules and then sheafifies, and both steps preserve finite limits, and it preserves finite
colimits because it is a left adjoint.  So a five term exact sequence `N₀ → ⋯ → N₄` of
`J'`-sheaves of modules is carried by `ε^*` to a five term exact sequence of `J`-sheaves of
modules; its four outer terms lie in `A` because `ε^*` carries `A'` into `A`, hence its middle
term lies in `A` because `A` is a weak Serre subcategory.  All five terms of `ε^*` of the
sequence now lie in `A`, so `ε_*` of it is again exact, and comparing the original sequence
with it along the unit of the adjunction — invertible at the four outer terms — the five lemma
makes the comparison invertible at the middle term too.  Therefore the middle term is `ε_*` of
an object of `A`, which is what `A'` means.

## Which spelling of "weak Serre subcategory"

The hypothesis and the conclusion are stated with `Stacks.WeakSerre.IsWeakSerre`, the five term
exactness form of Stacks 02MO, because that is exactly what the argument consumes and produces
and because the derived category results of Stacks 06UQ are stated in it.  A caller holding the
closure form `CategoryTheory.ObjectProperty.IsWeakSerreClass` of Stacks 0754 converts with
`Stacks.WeakSerre.isWeakSerre_of_isWeakSerreClass`; the conclusion is available in both forms.

## What is carried as a hypothesis

The source derives from its assumptions (3) and (4) that `R^pε_*F = 0` for `p > 0` and `F` in
`A`, by Stacks 072W, and concludes from this that `ε_*` carries an exact complex with terms in
`A` to an exact complex.  That derivation is not available at this point of the import graph —
it needs the acyclicity theory of right derived functors — so the implication itself is an
explicit hypothesis `hdev` of `isWeakSerre_imageOfLE`: *if* assumptions (3) and (4) hold,
*then* `ε_*` preserves exactness of a short complex whose three terms lie in `A`.  Assumptions
(3) and (4) are hypotheses of the theorem in the source's own form and are fed to `hdev`;
nothing else is assumed.

`hdev` is proved, over exactly assumptions (3) and (4), as
`Stacks.Cohomology.CompareTopologies.exact_map_pushforward_of_vanishing` in
`StacksFrontier/CategoryTheory/Sites/Cohomology/ChangeOfTopology/CoarseningDerivedEquivalence.lean`,
and the conclusion of this file with the hypothesis discharged is
`Stacks.Cohomology.CompareTopologies.isWeakSerreClass_imageOfLE_of_vanishing` there.

The second conclusion of 07A8, the equivalence of triangulated categories `D_A(R_τ) = D_A(R_τ')`
given by `ε^*` and `Rε_*`, is proved in that file as
`Stacks.Cohomology.CompareTopologies.derivedPullbackEquivalenceImageOfLE`. The source obtains it
from Stacks 0D7W, which the library has as
`Stacks.Cohomology.CohomologicalDescent.derivedPullbackEquivalenceUnboundedRelative`, and the total
right derived functor of `ε_*` on the unbounded derived category is
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforward` of the coarsening
morphism of ringed sites.

## References

* [Stacks Project, Tag 07A8](https://stacks.math.columbia.edu/tag/07A8)
* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.CompareTopologies

universe u v r m

/-- The five term sequence `mk₄ f₀ f₁ f₂ f₃` is exact as a `CategoryTheory.ComposableArrows`
when it is exact at each of its three inner objects. -/
private theorem exact_mk₄ {D : Type*} [Category D] [Abelian D]
    {X₀ X₁ X₂ X₃ X₄ : D} {f₀ : X₀ ⟶ X₁} {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃} {f₃ : X₃ ⟶ X₄}
    (w₀ : f₀ ≫ f₁ = 0) (w₁ : f₁ ≫ f₂ = 0) (w₂ : f₂ ≫ f₃ = 0)
    (e₀ : (ShortComplex.mk f₀ f₁ w₀).Exact) (e₁ : (ShortComplex.mk f₁ f₂ w₁).Exact)
    (e₂ : (ShortComplex.mk f₂ f₃ w₂).Exact) :
    (ComposableArrows.mk₄ f₀ f₁ f₂ f₃).Exact :=
  ComposableArrows.exact_of_δ₀ (ComposableArrows.exact₂_mk _ w₀ e₀)
    (ComposableArrows.exact_of_δ₀ (ComposableArrows.exact₂_mk _ w₁ e₁)
      (ComposableArrows.exact₂_mk _ w₂ e₂))

/-- **The five lemma, in the shape in which the proof of Stacks 07A8 uses it.**  Let `η : 𝟭 ⟶ T`
be a natural transformation of endofunctors of an abelian category and let `E` be a five term
exact sequence.  If `T` applied to `E` is again exact and `η` is invertible at the four outer
objects of `E`, then `η` is invertible at the middle object of `E`. -/
private theorem isIso_app_obj₂ {D : Type*} [Category D] [Abelian D] {T : D ⥤ D} (η : 𝟭 D ⟶ T)
    (E : WeakSerre.Exact5 D)
    (Z₀ : T.map E.f₀ ≫ T.map E.f₁ = 0) (Z₁ : T.map E.f₁ ≫ T.map E.f₂ = 0)
    (Z₂ : T.map E.f₂ ≫ T.map E.f₃ = 0)
    (F₀ : (ShortComplex.mk (T.map E.f₀) (T.map E.f₁) Z₀).Exact)
    (F₁ : (ShortComplex.mk (T.map E.f₁) (T.map E.f₂) Z₁).Exact)
    (F₂ : (ShortComplex.mk (T.map E.f₂) (T.map E.f₃) Z₂).Exact)
    (h₀ : IsIso (η.app E.obj₀)) (h₁ : IsIso (η.app E.obj₁))
    (h₃ : IsIso (η.app E.obj₃)) (h₄ : IsIso (η.app E.obj₄)) :
    IsIso (η.app E.obj₂) := by
  let φ : (ComposableArrows.mk₄ E.f₀ E.f₁ E.f₂ E.f₃) ⟶
      (ComposableArrows.mk₄ (T.map E.f₀) (T.map E.f₁) (T.map E.f₂) (T.map E.f₃)) :=
    ComposableArrows.homMk₄ (η.app E.obj₀) (η.app E.obj₁) (η.app E.obj₂) (η.app E.obj₃)
      (η.app E.obj₄)
      (by change E.f₀ ≫ η.app E.obj₁ = η.app E.obj₀ ≫ T.map E.f₀; exact η.naturality E.f₀)
      (by change E.f₁ ≫ η.app E.obj₂ = η.app E.obj₁ ≫ T.map E.f₁; exact η.naturality E.f₁)
      (by change E.f₂ ≫ η.app E.obj₃ = η.app E.obj₂ ≫ T.map E.f₂; exact η.naturality E.f₂)
      (by change E.f₃ ≫ η.app E.obj₄ = η.app E.obj₃ ≫ T.map E.f₃; exact η.naturality E.f₃)
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
    (exact_mk₄ E.zero₀ E.zero₁ E.zero₂ E.exact₁ E.exact₂ E.exact₃)
    (exact_mk₄ Z₀ Z₁ Z₂ F₀ F₁ F₂) φ
    (have := h₀; (inferInstance : Epi (η.app E.obj₀))) h₁ h₃
    (have := h₄; (inferInstance : Mono (η.app E.obj₄)))

variable {C : Type u} [Category.{v} C] {J J' : GrothendieckTopology C}
    (h : J' ≤ J) (R : Sheaf J RingCat.{r})

/-- `ε_*`: a sheaf of modules for the finer topology, read as a sheaf of modules for the coarser
one.  Neither the underlying presheaf of modules nor the morphisms change. -/
abbrev pushforward :
    _root_.SheafOfModules.{m} R ⥤ _root_.SheafOfModules.{m} (R.ofLE h) :=
  _root_.SheafOfModules.ofLE.{u, v, r, m} h R

/-- `ε_*` is additive, since it changes neither the presheaves nor the morphisms. -/
instance additive_pushforward : (pushforward.{u, v, r, m} h R).Additive where
  map_add := rfl

section Pullback

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]

/-- `ε^*`: sheafification for the finer topology, the left adjoint of `ε_*`. -/
noncomputable abbrev pullback :
    _root_.SheafOfModules.{m} (R.ofLE h) ⥤ _root_.SheafOfModules.{m} R :=
  _root_.SheafOfModules.sheafifyOfLE.{u, v, r, m} h R

/-- The adjunction `ε^* ⊣ ε_*`. -/
noncomputable abbrev adjunction :
    pullback.{u, v, r, m} h R ⊣ pushforward.{u, v, r, m} h R :=
  _root_.SheafOfModules.sheafifyOfLEAdjunction.{u, v, r, m} h R

/-- Reading a sheaf of modules for the coarser topology as a presheaf of modules preserves
finite limits, because limits of sheaves of modules are computed on the underlying presheaves
of modules. -/
instance preservesFiniteLimits_forgetOfLE :
    PreservesFiniteLimits (_root_.SheafOfModules.forgetOfLE.{u, v, r, m} h R) :=
  inferInstanceAs (PreservesFiniteLimits (_root_.SheafOfModules.forget.{m} (R.ofLE h)))

/-- `ε^*` preserves finite limits, being forgetting to presheaves of modules followed by
sheafification for the finer topology. -/
instance preservesFiniteLimits_pullback :
    PreservesFiniteLimits (pullback.{u, v, r, m} h R) :=
  comp_preservesFiniteLimits (_root_.SheafOfModules.forgetOfLE.{u, v, r, m} h R)
    (PresheafOfModules.sheafification.{m} (𝟙 R.obj))

/-- `ε^*` preserves finite colimits, being a left adjoint. -/
instance preservesFiniteColimits_pullback :
    PreservesFiniteColimits (pullback.{u, v, r, m} h R) :=
  have : PreservesColimitsOfSize.{0, 0} (pullback.{u, v, r, m} h R) :=
    (adjunction.{u, v, r, m} h R).leftAdjoint_preservesColimits
  inferInstance

/-- `ε^*` is additive, being left adjoint to an additive functor. -/
instance additive_pullback : (pullback.{u, v, r, m} h R).Additive :=
  (adjunction.{u, v, r, m} h R).left_adjoint_additive

end Pullback

variable (A : ObjectProperty (_root_.SheafOfModules.{m} R))

/-- The class `A'` of the source: the image of a class `A` of sheaves of modules for the finer
topology under `ε_*`, as a class of sheaves of modules for the coarser topology. -/
def imageOfLE : ObjectProperty (_root_.SheafOfModules.{m} (R.ofLE h)) :=
  fun N => ∃ M : _root_.SheafOfModules.{m} R, A M ∧
    Nonempty ((pushforward.{u, v, r, m} h R).obj M ≅ N)

/-- `ε_*` carries `A` into `A'`. -/
theorem imageOfLE_pushforward_obj {M : _root_.SheafOfModules.{m} R} (hM : A M) :
    imageOfLE.{u, v, r, m} h R A ((pushforward.{u, v, r, m} h R).obj M) :=
  ⟨M, hM, ⟨Iso.refl _⟩⟩

/-- The class `A'` is closed under isomorphisms. -/
instance isClosedUnderIsomorphisms_imageOfLE :
    (imageOfLE.{u, v, r, m} h R A).IsClosedUnderIsomorphisms where
  of_iso e := by
    rintro ⟨M, hM, ⟨f⟩⟩
    exact ⟨M, hM, ⟨f ≪≫ e⟩⟩

section PullbackOfImage

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]

/-- `ε^*` carries `A'` into `A`: an object of `A'` is isomorphic to `ε_*M` for some `M` of `A`,
and `ε^*ε_*M` is `M`. -/
theorem prop_pullback_obj (hA : A.IsClosedUnderIsomorphisms)
    {N : _root_.SheafOfModules.{m} (R.ofLE h)} (hN : imageOfLE.{u, v, r, m} h R A N) :
    A ((pullback.{u, v, r, m} h R).obj N) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hN
  exact hA.of_iso ((_root_.SheafOfModules.sheafifyOfLEObjOfLEIso.{u, v, r, m} h R M).symm ≪≫
    (pullback.{u, v, r, m} h R).mapIso e) hM

/-- The comparison `N ⟶ ε_*ε^*N` is invertible for `N` in `A'`, since `N` lies in the essential
image of the fully faithful functor `ε_*`. -/
theorem isIso_unit_app_of_imageOfLE
    {N : _root_.SheafOfModules.{m} (R.ofLE h)} (hN : imageOfLE.{u, v, r, m} h R A N) :
    IsIso ((adjunction.{u, v, r, m} h R).unit.app N) := by
  obtain ⟨M, -, ⟨e⟩⟩ := hN
  exact (Adjunction.isIso_unit_app_iff_mem_essImage _).mpr ⟨M, ⟨e⟩⟩

omit [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}] in
/-- **`ε_*` and `ε^*` restrict to quasi-inverse equivalences between `A` and `A'`**, which is the
first paragraph of the proof in the source.  The functor displayed here is `ε_*` corestricted to
`A'`; it is fully faithful because `ε_*` is, and essentially surjective because `A'` is by
definition the image of `A`.  Its quasi-inverse is the corestriction of `ε^*`, by
`Stacks.Cohomology.CompareTopologies.prop_pullback_obj` and
`isIso_unit_app_of_imageOfLE`.  This is assumption (2) of Stacks 0D7W for `ε`. -/
theorem isEquivalence_liftPushforward :
    ((imageOfLE.{u, v, r, m} h R A).lift (A.ι ⋙ pushforward.{u, v, r, m} h R)
      (fun M ↦ imageOfLE_pushforward_obj h R A M.property)).IsEquivalence := by
  have hess : ((imageOfLE.{u, v, r, m} h R A).lift (A.ι ⋙ pushforward.{u, v, r, m} h R)
      (fun M ↦ imageOfLE_pushforward_obj h R A M.property)).EssSurj := by
    refine ⟨fun N ↦ ?_⟩
    obtain ⟨M, hM, ⟨e⟩⟩ := N.property
    exact ⟨⟨M, hM⟩, ⟨ObjectProperty.isoMk _ e⟩⟩
  exact { }

/-- Let `J' ≤ J` be two topologies on `C` and let `R` be a sheaf of rings for the finer topology
`J`, so that the identity functor of `C` is the comparison morphism of ringed sites
`ε : (C_τ, R_τ) ⟶ (C_τ', R_τ')`. Let `A` be a class of sheaves of `R`-modules for `J` — the
source's assumption (1), that every object of `A` is a sheaf for the finer topology, is this — and
let `B` be a set of objects of `C`. Assume

1. `A` is a weak Serre subcategory of `Mod(R_τ)`,
2. every object of `C` has a `J'`-covering whose members lie in `B`,
3. for every `U` in `B` the cohomology `H^p_τ(U, F)` vanishes for `p > 0` and `F` in `A`.

Then the image `A'` of `A` under `ε_*` is a weak Serre subcategory of `Mod(R_τ')`.

The hypothesis `hdev` is the step of the source's proof that assumptions (2) and (3) above force
`ε_*` to carry an exact short complex with terms in `A` to an exact short complex. In the source
that step is Stacks 072W, identifying `R^pε_*` with the sheafification of `U ↦ H^p_τ(U, F)`,
followed by a dévissage. -/
@[stacks 07A8 "the weak Serre subcategory for the coarser topology"]
theorem isWeakSerre_imageOfLE [HasSheafify J' AddCommGrpCat.{m}]
    [J'.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [EnoughInjectives (_root_.SheafOfModules.{m} R)]
    (hA : WeakSerre.IsWeakSerre A) (B : Set C)
    (hB : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{max u v} U, 𝒰.sieve₀ ∈ J' U ∧ ∀ i, B (𝒰.X i))
    (hvan : ∀ U : C, B U → ∀ p : ℕ, 0 < p → ∀ F : _root_.SheafOfModules.{m} R, A F →
      IsZero (Stacks.Cohomology.moduleCohomology R U p F))
    (hdev : (∀ U : C, ∃ 𝒰 : PreZeroHypercover.{max u v} U, 𝒰.sieve₀ ∈ J' U ∧ ∀ i, B (𝒰.X i)) →
      (∀ U : C, B U → ∀ p : ℕ, 0 < p → ∀ F : _root_.SheafOfModules.{m} R, A F →
        IsZero (Stacks.Cohomology.moduleCohomology R U p F)) →
      ∀ S : ShortComplex (_root_.SheafOfModules.{m} R), S.Exact →
        A S.X₁ → A S.X₂ → A S.X₃ → (S.map (pushforward.{u, v, r, m} h R)).Exact) :
    WeakSerre.IsWeakSerre (imageOfLE.{u, v, r, m} h R A) := by
  have hpush := hdev hB hvan
  have hiso := hA.isClosedUnderIsomorphisms
  refine ⟨inferInstance, ?_, ?_⟩
  · obtain ⟨M, hM⟩ := hA.nonempty
    exact ⟨_, imageOfLE_pushforward_obj.{u, v, r, m} h R A hM⟩
  intro E h0 h1 h3 h4
  -- The four outer terms of `ε^*E` lie in `A`.
  have a0 : A ((pullback.{u, v, r, m} h R).obj E.obj₀) := prop_pullback_obj h R A hiso h0
  have a1 : A ((pullback.{u, v, r, m} h R).obj E.obj₁) := prop_pullback_obj h R A hiso h1
  have a3 : A ((pullback.{u, v, r, m} h R).obj E.obj₃) := prop_pullback_obj h R A hiso h3
  have a4 : A ((pullback.{u, v, r, m} h R).obj E.obj₄) := prop_pullback_obj h R A hiso h4
  -- `ε^*` is exact, so `ε^*E` is again a five term exact sequence.
  have z₀ : (pullback.{u, v, r, m} h R).map E.f₀ ≫ (pullback.{u, v, r, m} h R).map E.f₁ = 0 := by
    rw [← Functor.map_comp, E.zero₀, Functor.map_zero]
  have z₁ : (pullback.{u, v, r, m} h R).map E.f₁ ≫ (pullback.{u, v, r, m} h R).map E.f₂ = 0 := by
    rw [← Functor.map_comp, E.zero₁, Functor.map_zero]
  have z₂ : (pullback.{u, v, r, m} h R).map E.f₂ ≫ (pullback.{u, v, r, m} h R).map E.f₃ = 0 := by
    rw [← Functor.map_comp, E.zero₂, Functor.map_zero]
  have e₀ : (ShortComplex.mk ((pullback.{u, v, r, m} h R).map E.f₀)
      ((pullback.{u, v, r, m} h R).map E.f₁) z₀).Exact :=
    E.exact₁.map (pullback.{u, v, r, m} h R)
  have e₁ : (ShortComplex.mk ((pullback.{u, v, r, m} h R).map E.f₁)
      ((pullback.{u, v, r, m} h R).map E.f₂) z₁).Exact :=
    E.exact₂.map (pullback.{u, v, r, m} h R)
  have e₂ : (ShortComplex.mk ((pullback.{u, v, r, m} h R).map E.f₂)
      ((pullback.{u, v, r, m} h R).map E.f₃) z₂).Exact :=
    E.exact₃.map (pullback.{u, v, r, m} h R)
  -- Hence its middle term lies in `A`, since `A` is a weak Serre subcategory.
  have a2 : A ((pullback.{u, v, r, m} h R).obj E.obj₂) :=
    hA.mem_of_exact5
      { obj₀ := (pullback.{u, v, r, m} h R).obj E.obj₀
        obj₁ := (pullback.{u, v, r, m} h R).obj E.obj₁
        obj₂ := (pullback.{u, v, r, m} h R).obj E.obj₂
        obj₃ := (pullback.{u, v, r, m} h R).obj E.obj₃
        obj₄ := (pullback.{u, v, r, m} h R).obj E.obj₄
        f₀ := (pullback.{u, v, r, m} h R).map E.f₀
        f₁ := (pullback.{u, v, r, m} h R).map E.f₁
        f₂ := (pullback.{u, v, r, m} h R).map E.f₂
        f₃ := (pullback.{u, v, r, m} h R).map E.f₃
        zero₀ := z₀, zero₁ := z₁, zero₂ := z₂
        exact₁ := e₀, exact₂ := e₁, exact₃ := e₂ } a0 a1 a3 a4
  -- All five terms of `ε^*E` lie in `A`, so `ε_*ε^*E` is exact.
  have Z₀ : (pushforward.{u, v, r, m} h R).map ((pullback.{u, v, r, m} h R).map E.f₀) ≫
      (pushforward.{u, v, r, m} h R).map ((pullback.{u, v, r, m} h R).map E.f₁) = 0 := by
    rw [← Functor.map_comp, z₀, Functor.map_zero]
  have Z₁ : (pushforward.{u, v, r, m} h R).map ((pullback.{u, v, r, m} h R).map E.f₁) ≫
      (pushforward.{u, v, r, m} h R).map ((pullback.{u, v, r, m} h R).map E.f₂) = 0 := by
    rw [← Functor.map_comp, z₁, Functor.map_zero]
  have Z₂ : (pushforward.{u, v, r, m} h R).map ((pullback.{u, v, r, m} h R).map E.f₂) ≫
      (pushforward.{u, v, r, m} h R).map ((pullback.{u, v, r, m} h R).map E.f₃) = 0 := by
    rw [← Functor.map_comp, z₂, Functor.map_zero]
  have E₀ : (ShortComplex.mk
      ((pushforward.{u, v, r, m} h R).map ((pullback.{u, v, r, m} h R).map E.f₀))
      ((pushforward.{u, v, r, m} h R).map ((pullback.{u, v, r, m} h R).map E.f₁)) Z₀).Exact :=
    hpush _ e₀ a0 a1 a2
  have E₁ : (ShortComplex.mk
      ((pushforward.{u, v, r, m} h R).map ((pullback.{u, v, r, m} h R).map E.f₁))
      ((pushforward.{u, v, r, m} h R).map ((pullback.{u, v, r, m} h R).map E.f₂)) Z₁).Exact :=
    hpush _ e₁ a1 a2 a3
  have E₂ : (ShortComplex.mk
      ((pushforward.{u, v, r, m} h R).map ((pullback.{u, v, r, m} h R).map E.f₂))
      ((pushforward.{u, v, r, m} h R).map ((pullback.{u, v, r, m} h R).map E.f₃)) Z₂).Exact :=
    hpush _ e₂ a2 a3 a4
  -- Compare `E` with `ε_*ε^*E` along the unit and apply the five lemma.
  have h2 : IsIso ((adjunction.{u, v, r, m} h R).unit.app E.obj₂) :=
    isIso_app_obj₂ (adjunction.{u, v, r, m} h R).unit E Z₀ Z₁ Z₂ E₀ E₁ E₂
      (isIso_unit_app_of_imageOfLE h R A h0) (isIso_unit_app_of_imageOfLE h R A h1)
      (isIso_unit_app_of_imageOfLE h R A h3) (isIso_unit_app_of_imageOfLE h R A h4)
  have := h2
  exact ⟨(pullback.{u, v, r, m} h R).obj E.obj₂, a2,
    ⟨(asIso ((adjunction.{u, v, r, m} h R).unit.app E.obj₂)).symm⟩⟩

/-- The same statement as `Stacks.Cohomology.CompareTopologies.isWeakSerre_imageOfLE`, with the
conclusion phrased in the closure form `CategoryTheory.ObjectProperty.IsWeakSerreClass` of
Stacks 0754. -/
@[stacks 07A8 "the same conclusion in the closure form of Stacks 0754"]
theorem isWeakSerreClass_imageOfLE [HasSheafify J' AddCommGrpCat.{m}]
    [J'.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [EnoughInjectives (_root_.SheafOfModules.{m} R)]
    (hA : WeakSerre.IsWeakSerre A) (B : Set C)
    (hB : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{max u v} U, 𝒰.sieve₀ ∈ J' U ∧ ∀ i, B (𝒰.X i))
    (hvan : ∀ U : C, B U → ∀ p : ℕ, 0 < p → ∀ F : _root_.SheafOfModules.{m} R, A F →
      IsZero (Stacks.Cohomology.moduleCohomology R U p F))
    (hdev : (∀ U : C, ∃ 𝒰 : PreZeroHypercover.{max u v} U, 𝒰.sieve₀ ∈ J' U ∧ ∀ i, B (𝒰.X i)) →
      (∀ U : C, B U → ∀ p : ℕ, 0 < p → ∀ F : _root_.SheafOfModules.{m} R, A F →
        IsZero (Stacks.Cohomology.moduleCohomology R U p F)) →
      ∀ S : ShortComplex (_root_.SheafOfModules.{m} R), S.Exact →
        A S.X₁ → A S.X₂ → A S.X₃ → (S.map (pushforward.{u, v, r, m} h R)).Exact) :
    (imageOfLE.{u, v, r, m} h R A).IsWeakSerreClass := by
  have hA' := isWeakSerre_imageOfLE h R A hA B hB hvan hdev
  refine (ObjectProperty.isWeakSerreClass_iff_prop_obj₂_of_exact _).2 ⟨hA'.nonempty, ?_⟩
  intro S hS h₀ h₁ h₃ h₄
  exact hA'.mem_of_exact5
    { obj₀ := S.obj' 0, obj₁ := S.obj' 1, obj₂ := S.obj' 2, obj₃ := S.obj' 3, obj₄ := S.obj' 4
      f₀ := S.map' 0 1, f₁ := S.map' 1 2, f₂ := S.map' 2 3, f₃ := S.map' 3 4
      zero₀ := hS.toIsComplex.zero' 0 1 2
      zero₁ := hS.toIsComplex.zero' 1 2 3
      zero₂ := hS.toIsComplex.zero' 2 3 4
      exact₁ := hS.exact' 0 1 2
      exact₂ := hS.exact' 1 2 3
      exact₃ := hS.exact' 2 3 4 } h₀ h₁ h₃ h₄

end PullbackOfImage

end Stacks.Cohomology.CompareTopologies

end
