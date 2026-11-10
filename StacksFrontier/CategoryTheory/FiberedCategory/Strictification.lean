module

import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
public import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.EffectiveEpi.Comp

public import StacksFrontier.CategoryTheory.FibredOneMorphism
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Split
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Every fibred category is equivalent to a split one (Stacks 004A, 02XY)

Let `p : 𝒳 ⥤ 𝒞` be a fibred category. Stacks 004A says that there is a contravariant functor
`F : 𝒞 ⥤ Cat` — an honest functor into the 2-category of categories, not merely a pseudofunctor —
such that `𝒳` is equivalent to `𝒮_F` (Stacks 02XV) in the 2-category of fibred categories over
`𝒞`; in other words every fibred category is equivalent to a split one. Stacks 02XY is the same
statement for a category fibred in groupoids, with `F : 𝒞ᵒᵖ ⥤ Grpd`.

The construction is the source's. Fix the cleaving that `CategoryTheory.Functor.IsPreFibered`
provides, so that every `f : V ⟶ U` and every `x` of the fibre `𝒳_U` have a chosen pullback
`f^* x` (`CategoryTheory.Functor.pullbackFiber`). The split model `𝒮'` has as objects the pairs
`(x, f : V ⟶ U)` and as morphisms `(x₁, f₁) ⟶ (x₂, f₂)` the pairs `(g, φ)` with
`φ : f₁^* x₁ ⟶ f₂^* x₂` lying over `g`; the pullback functors `g^*(x, f) = (x, f ∘ g)` satisfy
`g₁^* ∘ g₂^* = (g₂ ∘ g₁)^*` on the nose, which is what makes `𝒮'` split. Here `𝒮'` is presented
through its fibres: `CategoryTheory.Functor.SplitFiber p V` is the fibre of `𝒮'` over `V`, the
pullback functors assemble into a functor `CategoryTheory.Functor.splitPresheaf p : 𝒞ᵒᵖ ⥤ Cat`,
and `𝒮'` is recovered as the Grothendieck construction `𝒮_F` of that functor, i.e. as
`CategoryTheory.presheafOfCategories (splitPresheaf p)`. The comparison functor
`CategoryTheory.Functor.toSplit` is the source's `𝒮 → 𝒮'`, `x ↦ (x, id_{p(x)})`.

## Main definitions

* `CategoryTheory.Functor.IsFibredEquivalenceOver`: an equivalence in the 2-category of fibred
  categories over `𝒞`;
* `CategoryTheory.Functor.SplitFiber`: the fibre over `V` of the split model `𝒮'`, and
  `CategoryTheory.Functor.SplitFiber.restrict` its pullback functors;
* `CategoryTheory.Functor.splitPresheaf`: the functor `F : 𝒞ᵒᵖ ⥤ Cat` of Stacks 004A, and
  `CategoryTheory.Functor.splitPresheafGrpd` the functor `F : 𝒞ᵒᵖ ⥤ Grpd` of Stacks 02XY;
* `CategoryTheory.Functor.toSplit`: the comparison functor `𝒮 → 𝒮'`.

## Main results

* `CategoryTheory.Functor.isFibredEquivalenceOver_of_fullyFaithful`: a fully faithful functor over
  `𝒞` which is essentially surjective by *vertical* isomorphisms is an equivalence in the
  2-category of fibred categories over `𝒞` — in particular it automatically preserves strongly
  cartesian morphisms (`CategoryTheory.Functor.isStronglyCartesian_map`), which is the verification
  the source flags and omits;
* `CategoryTheory.Functor.SplitFiber.restrict_id` and
  `CategoryTheory.Functor.SplitFiber.restrict_comp`: the strict functoriality of the pullback
  functors of `𝒮'`, i.e. `g₁^* ∘ g₂^* = (g₂ ∘ g₁)^*`;
* `CategoryTheory.Functor.exists_isFibredEquivalenceOver_presheafOfCategories`: Stacks 004A;
* `CategoryTheory.Functor.exists_isFibredEquivalenceOver_presheafOfGroupoids`: Stacks 02XY.

## Implementation notes

**The notion of equivalence used.** The source asks for an equivalence *in the 2-category of
fibred categories over `𝒞`*, and its proof is explicit that one must check that `𝒮 → 𝒮'` "maps
strongly cartesian morphisms to strongly cartesian morphisms". Accordingly
`CategoryTheory.Functor.IsFibredEquivalenceOver` asks for a 1-morphism of fibred categories
over `𝒞` in the sense of Stacks 4.33.9 (2), that is
`CategoryTheory.Functor.IsFibredOneMorphism`, admitting a 1-morphism of fibred categories in
the other direction together with unit and counit natural *isomorphisms* whose components are
vertical. None of the three notions already in the repository fits:
`CategoryTheory.IsFibredEquivalence` in `StacksFrontier/CategoryTheory/EquivalenceOver.lean` is
stated with the *weakly* cartesian `IsCartesianFunctorStrict` and its own module docstring says
it is superseded by `IsFibredOneMorphism` and retained only for
`StacksFrontier/CategoryTheory/FiberedInGroupoids/Representability/FibreFunctors.lean`;
`StacksRepresentableCFG.EquivalenceOver` in
`StacksFrontier/CategoryTheory/FiberedInGroupoids/Representability/Criterion.lean` has the right
shape for the unit and counit but imposes no cartesian condition, because it is used for
categories fibred in groupoids where preservation is automatic; and
`CategoryTheory.BasedCategory.IsoOver` is a strict *isomorphism* over `𝒞`, which is strictly
stronger than what 004A asserts. Verticality of a 2-morphism is expressed with Mathlib's
`CategoryTheory.Functor.IsHomLift` at an identity, which is the same condition as
`CategoryTheory.NatTrans.IsOver` of the superseded file.

**Relation to `Functor.IsSplitFibered` (Stacks 02XW).** 004A asserts an *equivalence*, whereas
`CategoryTheory.Functor.IsSplitFibered` is defined with a strict isomorphism over `𝒞`, so 004A is
not `∃ F, p.IsSplitFibered` for the same `p`: it says that `p` is equivalent over `𝒞` to
`presheafOfCategories F`, which is the category `𝒮_F` of Stacks 02XV that 02XW calls split. The
conclusion is therefore stated with `presheafOfCategories` directly. It is not restated using
`IsSplitFibered` applied to the target, because that predicate ties the universes of `F` to those
of the category being tested: the objects of `SplitFiber p V` live in `max u₁ u₂ v₁` for
`𝒞 : Type u₁` and `𝒳 : Type u₂`, while its morphisms live in `v₂`, and no instantiation of
`IsSplitFibered` has those two universes simultaneously.

**Base change of the chosen pullbacks.** The restriction maps of `SplitFiber` are built from
`CategoryTheory.Functor.pullbackFiberMap` of
`StacksFrontier/CategoryTheory/Sites/Descent/IsStack.lean` — the canonical morphism between the
chosen pullbacks of one object along two morphisms of a slice — rather than from
`CategoryTheory.Functor.pullbackFiberCompIso`; every identity between canonical comparisons
below is then proved from a single factorization through the chosen cartesian lifts, exactly as
`CategoryTheory.Functor.morRestrict` (Stacks 026A) is. `SplitFiber.restrictHom` is the
generalization of `morRestrict` to a pair of objects living over different objects of `𝒞` and
pulled back along different morphisms, which is what the objects of `SplitFiber p V` require.
-/

@[expose] public section

-- As in `StacksFrontier/CategoryTheory/Sites/Descent/IsStack.lean`: the instance arguments of
-- `IsHomLift` and `IsCartesian`, and the identification of a fibre object with its image in `𝒳`,
-- are only found after unfolding the relevant definitions.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

open Opposite Pseudofunctor Pseudofunctor.CoGrothendieck

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴]

/-! ### Equivalences in the 2-category of fibred categories over `𝒞` -/

/-- A functor `G` strictly over `𝒞` *reflects* `IsHomLift`: if `G.map φ` lies over `f` for the
target structure functor, then `φ` lies over `f` for the source one. This is the converse of
`CategoryTheory.Functor.isHomLift_map_of_comp_eq`. -/
lemma isHomLift_of_isHomLift_map {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {G : 𝒳 ⥤ 𝒴} (hG : G ⋙ q = p)
    {R T : 𝒞} (f : R ⟶ T) {a b : 𝒳} (φ : a ⟶ b) [q.IsHomLift f (G.map φ)] :
    p.IsHomLift f φ := by
  subst hG
  exact IsHomLift.of_fac' _ f φ (IsHomLift.domain_eq q f (G.map φ))
    (IsHomLift.codomain_eq q f (G.map φ)) (IsHomLift.fac' q f (G.map φ))

/-- The preimage under a fully faithful functor `G` of a morphism over `f` lies over `f` for
`G ⋙ q`. -/
private lemma isHomLift_preimage {q : 𝒴 ⥤ 𝒞} (G : 𝒳 ⥤ 𝒴) [G.Full] [G.Faithful] {R T : 𝒞}
    (f : R ⟶ T) {a b : 𝒳} (u : G.obj a ⟶ G.obj b) [q.IsHomLift f u] :
    (G ⋙ q).IsHomLift f (G.preimage u) :=
  have : q.IsHomLift f (G.map (G.preimage u)) := by rwa [G.map_preimage]
  isHomLift_of_isHomLift_map rfl f _

/-- A fully faithful functor over `𝒞` *reflects* strongly cartesian morphisms: the universal
property of `G.map φ` is tested against all objects of `𝒴`, hence in particular against the
objects in the image of `G`, and full faithfulness turns the resulting factorizations into
factorizations in `𝒳`. -/
lemma isStronglyCartesian_of_isStronglyCartesian_map {q : 𝒴 ⥤ 𝒞} (G : 𝒳 ⥤ 𝒴) [G.Full]
    [G.Faithful] {R T : 𝒞} (f : R ⟶ T) {a b : 𝒳} (φ : a ⟶ b)
    [q.IsStronglyCartesian f (G.map φ)] : (G ⋙ q).IsStronglyCartesian f φ where
  toIsHomLift := isHomLift_of_isHomLift_map rfl f φ
  universal_property' := by
    intro a' g φ' hφ'
    have : q.IsHomLift (g ≫ f) (G.map φ') := isHomLift_map_of_comp_eq rfl (g ≫ f) φ'
    obtain ⟨χ, ⟨hχ₁, hχ₂⟩, huniq⟩ :=
      IsStronglyCartesian.universal_property' (p := q) (f := f) (φ := G.map φ) g (G.map φ')
    have hmap : G.map (G.preimage χ) = χ := G.map_preimage χ
    refine ⟨G.preimage χ, ⟨?_, ?_⟩, ?_⟩
    · exact isHomLift_preimage G g χ
    · exact G.map_injective (by rw [G.map_comp, hmap, hχ₂])
    · intro ψ ⟨hψ₁, hψ₂⟩
      refine G.map_injective ?_
      rw [hmap]
      exact huniq (G.map ψ) ⟨isHomLift_map_of_comp_eq rfl g ψ, by rw [← G.map_comp, hψ₂]⟩

/-- A fully faithful functor over `𝒞` which is essentially surjective by *vertical* isomorphisms
*preserves* strongly cartesian morphisms: every object of `𝒴` is, up to a vertical isomorphism,
in the image of `G`, so the universal property of `φ` in `𝒳` suffices to test that of `G.map φ`
in `𝒴`. -/
@[sga "1 VI 5.3" "(i)"]
lemma isStronglyCartesian_map {q : 𝒴 ⥤ 𝒞} (G : 𝒳 ⥤ 𝒴) [G.Full] [G.Faithful]
    (hsurj : ∀ y : 𝒴, ∃ (x : 𝒳) (e : G.obj x ≅ y), q.IsHomLift (𝟙 (q.obj y)) e.hom)
    {R T : 𝒞} (f : R ⟶ T) {a b : 𝒳} (φ : a ⟶ b) [(G ⋙ q).IsStronglyCartesian f φ] :
    q.IsStronglyCartesian f (G.map φ) where
  toIsHomLift := isHomLift_map_of_comp_eq rfl f φ
  universal_property' := by
    intro y' g φ' hφ'
    obtain ⟨x', e, he⟩ := hsurj y'
    have hx' : q.obj (G.obj x') = q.obj y' := IsHomLift.domain_eq q (𝟙 (q.obj y')) e.hom
    -- The composite `e.hom ≫ ω` lies over `eqToHom hx' ≫ g₀` and is in the image of `G`.
    have hlift : ∀ {T' : 𝒞} {c : 𝒳} (g₀ : q.obj y' ⟶ T') (ω : y' ⟶ G.obj c)
        [q.IsHomLift g₀ ω],
        (G ⋙ q).IsHomLift (eqToHom hx' ≫ g₀) (G.preimage (e.hom ≫ ω)) := by
      intro T' c g₀ ω _
      have : q.IsHomLift (𝟙 (q.obj y') ≫ g₀) (e.hom ≫ ω) := IsHomLift.comp _ _ _ _ _
      have : q.IsHomLift (eqToHom hx' ≫ g₀) (e.hom ≫ ω) := by simpa using this
      exact isHomLift_preimage G _ _
    have hpre : G.map (G.preimage (e.hom ≫ φ')) = e.hom ≫ φ' := G.map_preimage _
    have := hlift (g ≫ f) φ'
    obtain ⟨χ, ⟨hχ₁, hχ₂⟩, huniq⟩ := IsStronglyCartesian.universal_property (p := G ⋙ q) f φ
      (eqToHom hx' ≫ g) (eqToHom hx' ≫ g ≫ f) (Category.assoc _ _ _).symm
      (G.preimage (e.hom ≫ φ'))
    have hχ₁' : q.IsHomLift (eqToHom hx' ≫ g) (G.map χ) := isHomLift_map_of_comp_eq rfl _ χ
    refine ⟨e.inv ≫ G.map χ, ⟨?_, ?_⟩, ?_⟩
    · have hinv : q.IsHomLift (𝟙 (q.obj y') ≫ eqToHom hx'.symm) e.inv := inferInstance
      have hinv' : q.IsHomLift (eqToHom hx'.symm) e.inv := by simpa using hinv
      have : q.IsHomLift (eqToHom hx'.symm ≫ eqToHom hx' ≫ g) (e.inv ≫ G.map χ) :=
        IsHomLift.comp _ _ _ _ _
      simpa using this
    · rw [Category.assoc, ← G.map_comp, hχ₂, hpre, Iso.inv_hom_id_assoc]
    · intro τ ⟨hτ₁, hτ₂⟩
      have hpre₂ : G.map (G.preimage (e.hom ≫ τ)) = e.hom ≫ τ := G.map_preimage _
      have := hlift g τ
      have hfac : G.preimage (e.hom ≫ τ) ≫ φ = G.preimage (e.hom ≫ φ') := by
        refine G.map_injective ?_
        rw [G.map_comp, hpre₂, hpre, Category.assoc, hτ₂]
      have hkey : G.preimage (e.hom ≫ τ) = χ := huniq _ ⟨this, hfac⟩
      have : e.hom ≫ τ = G.map χ := by rw [← hpre₂, hkey]
      rw [← this, Iso.inv_hom_id_assoc]

/-- A fully faithful functor over `𝒞` which is essentially surjective by vertical isomorphisms is
a 1-morphism of fibred categories over `𝒞` (Stacks 4.33.9 (2)). -/
lemma IsFibredOneMorphism.of_fullyFaithful {q : 𝒴 ⥤ 𝒞} (G : 𝒳 ⥤ 𝒴) [G.Full] [G.Faithful]
    (hsurj : ∀ y : 𝒴, ∃ (x : 𝒳) (e : G.obj x ≅ y), q.IsHomLift (𝟙 (q.obj y)) e.hom) :
    IsFibredOneMorphism (G ⋙ q) q G where
  comp_eq := rfl
  map_isStronglyCartesian := by
    intro R T f a b φ h
    have := h
    exact isStronglyCartesian_map G hsurj f φ

/-- An *equivalence in the 2-category of fibred categories over `𝒞`* between `p : 𝒳 ⥤ 𝒞` and
`q : 𝒴 ⥤ 𝒞`: a 1-morphism `G` of fibred categories over `𝒞` (Stacks 4.33.9 (2), i.e.
`CategoryTheory.Functor.IsFibredOneMorphism`) admitting a 1-morphism `H` of fibred categories over
`𝒞` in the other direction together with unit and counit natural *isomorphisms* whose components
are *vertical*, i.e. lie over identities of `𝒞`. Verticality is exactly the condition that the
unit and counit are 2-morphisms of the 2-category of categories over `𝒞`. -/
structure IsFibredEquivalenceOver (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (G : 𝒳 ⥤ 𝒴) : Prop where
  /-- `G` is a 1-morphism of fibred categories over `𝒞`. -/
  isFibredOneMorphism : IsFibredOneMorphism p q G
  /-- A quasi-inverse 1-morphism of fibred categories over `𝒞`, with vertical unit and counit. -/
  exists_inverse : ∃ (H : 𝒴 ⥤ 𝒳) (_ : IsFibredOneMorphism q p H) (η : 𝟭 𝒳 ≅ G ⋙ H)
    (_ : ∀ x : 𝒳, p.IsHomLift (𝟙 (p.obj x)) (η.hom.app x)) (ε : H ⋙ G ≅ 𝟭 𝒴),
    ∀ y : 𝒴, q.IsHomLift (𝟙 (q.obj y)) (ε.hom.app y)

/-- A fully faithful functor over `𝒞` which is essentially surjective by vertical isomorphisms is
an equivalence in the 2-category of fibred categories over `𝒞`.

This is the criterion the proof of Stacks 004A verifies: the source checks that `𝒮 → 𝒮'` is "an
equivalence of categories over `𝒞` which maps strongly cartesian morphisms to strongly cartesian
morphisms", and by `CategoryTheory.Functor.isStronglyCartesian_map` the second half is automatic
once the first is known in the vertical form. -/
lemma isFibredEquivalenceOver_of_fullyFaithful {q : 𝒴 ⥤ 𝒞} (G : 𝒳 ⥤ 𝒴) [G.Full] [G.Faithful]
    (hsurj : ∀ y : 𝒴, ∃ (x : 𝒳) (e : G.obj x ≅ y), q.IsHomLift (𝟙 (q.obj y)) e.hom) :
    IsFibredEquivalenceOver (G ⋙ q) q G := by
  choose obj e he using hsurj
  have hobj : ∀ y : 𝒴, q.obj (G.obj (obj y)) = q.obj y := fun y =>
    have := he y; IsHomLift.domain_eq q (𝟙 (q.obj y)) (e y).hom
  -- The quasi-inverse: `y ↦ obj y` on objects, and full faithfulness on morphisms.
  let H : 𝒴 ⥤ 𝒳 :=
    { obj := obj
      map := fun {y y'} u => G.preimage ((e y).hom ≫ u ≫ (e y').inv)
      map_id := fun y => G.map_injective (by simp)
      map_comp := fun {y y' y''} u u' => G.map_injective (by simp) }
  have hHmap : ∀ {y y' : 𝒴} (u : y ⟶ y'), G.map (H.map u) = (e y).hom ≫ u ≫ (e y').inv :=
    fun u => G.map_preimage _
  -- The counit.
  let ε : H ⋙ G ≅ 𝟭 𝒴 := NatIso.ofComponents e (fun {y y'} u => by simp [hHmap])
  -- The unit.
  let η : 𝟭 𝒳 ≅ G ⋙ H := NatIso.ofComponents (fun x => G.preimageIso (e (G.obj x)).symm)
    (fun ψ => G.map_injective (by simp [hHmap]))
  have hηapp : ∀ x : 𝒳, G.map (η.hom.app x) = (e (G.obj x)).inv := fun x => G.map_preimage _
  -- The quasi-inverse is strictly over `𝒞`.
  have hH : ∀ {y y' : 𝒴} (u : y ⟶ y'), (G ⋙ q).IsHomLift (q.map u) (H.map u) := by
    intro y y' u
    have h₀ := he y
    have h₁ : q.IsHomLift (𝟙 (q.obj y) ≫ q.map u ≫ 𝟙 (q.obj y')) ((e y).hom ≫ u ≫ (e y').inv) :=
      IsHomLift.comp _ _ _ _ _
    have h₂ : q.IsHomLift (q.map u) ((e y).hom ≫ u ≫ (e y').inv) := by simpa using h₁
    exact isHomLift_preimage G (q.map u) _
  have hHw : H ⋙ (G ⋙ q) = q :=
    Functor.ext hobj fun y y' u => have := hH u; IsHomLift.fac' (G ⋙ q) (q.map u) (H.map u)
  refine ⟨IsFibredOneMorphism.of_fullyFaithful G (fun y => ⟨obj y, e y, he y⟩), H, ?_, η, ?_, ε, ?_⟩
  · refine ⟨hHw, ?_⟩
    intro R T f y y' u hu
    have := hu
    obtain rfl : q.obj y = R := IsHomLift.domain_eq q f u
    obtain rfl : q.obj y' = T := IsHomLift.codomain_eq q f u
    have h₀ := he y
    have h₀' := he y'
    have h₁ : q.IsStronglyCartesian (𝟙 (q.obj y) ≫ f ≫ 𝟙 (q.obj y'))
        ((e y).hom ≫ u ≫ (e y').inv) := inferInstance
    have h₂ : q.IsStronglyCartesian f ((e y).hom ≫ u ≫ (e y').inv) := by simpa using h₁
    have h₃ : q.IsStronglyCartesian f (G.map (H.map u)) := by rwa [hHmap u]
    exact isStronglyCartesian_of_isStronglyCartesian_map G f (H.map u)
  · intro x
    have h₀ := he (G.obj x)
    have h₁ : q.IsHomLift (𝟙 (q.obj (G.obj x))) (e (G.obj x)).inv := inferInstance
    have h₂ : q.IsHomLift (𝟙 ((G ⋙ q).obj x)) (G.map (η.hom.app x)) := by rwa [hηapp x]
    exact isHomLift_of_isHomLift_map rfl _ _
  · exact he

/-! ### Base change of the chosen pullbacks along a morphism of the base

For `f : V ⟶ U` and `g : V' ⟶ V`, the chosen pullback `(g ≫ f)^* x` carries a canonical morphism
to `f^* x` over `g`, namely `CategoryTheory.Functor.pullbackFiberMap` along the morphism `g` of the
slice `𝒞/U` from `g ≫ f` to `f`. This, rather than the composite
`(g ≫ f)^* x ≅ g^* f^* x ⟶ f^* x` through `CategoryTheory.Functor.pullbackFiberCompIso`, is the
form used below: it is characterized directly by a factorization through the chosen cartesian
lifts, which is what every identity between canonical comparisons is proved by. -/

section PullbackFiberProj

variable {p : 𝒳 ⥤ 𝒞} [p.IsFibered]

/-- The canonical morphism `(g ≫ f)^* x ⟶ f^* x` lying over `g`. -/
noncomputable def pullbackFiberProj {U V V' : 𝒞} (x : p.Fiber U) (f : V ⟶ U) (g : V' ⟶ V) :
    (pullbackFiber p x (g ≫ f)).1 ⟶ (pullbackFiber p x f).1 :=
  pullbackFiberMap p x (g₁ := Over.mk (g ≫ f)) (g₂ := Over.mk f) (Over.homMk g rfl)

/-- The canonical morphism `(g ≫ f)^* x ⟶ f^* x` lies over `g`. -/
instance isHomLift_pullbackFiberProj {U V V' : 𝒞} (x : p.Fiber U) (f : V ⟶ U) (g : V' ⟶ V) :
    p.IsHomLift g (pullbackFiberProj x f g) :=
  pullbackFiberMap_isHomLift p x (g₁ := Over.mk (g ≫ f)) (g₂ := Over.mk f) (Over.homMk g rfl)

/-- The canonical morphism `(g ≫ f)^* x ⟶ f^* x` followed by the chosen cartesian lift of `f` is
the chosen cartesian lift of `g ≫ f`. -/
@[reassoc (attr := simp)]
lemma pullbackFiberProj_fac {U V V' : 𝒞} (x : p.Fiber U) (f : V ⟶ U) (g : V' ⟶ V) :
    pullbackFiberProj x f g ≫ IsPreFibered.pullbackMap x.2 f =
      IsPreFibered.pullbackMap x.2 (g ≫ f) :=
  pullbackFiberMap_fac p x _

/-- A morphism `(g ≫ f)^* x ⟶ f^* x` over `g` factoring the chosen cartesian lift of `g ≫ f`
through that of `f` is the canonical one: the latter's universal property pins it down. -/
lemma pullbackFiberProj_uniq {U V V' : 𝒞} (x : p.Fiber U) (f : V ⟶ U) (g : V' ⟶ V)
    (φ : (pullbackFiber p x (g ≫ f)).1 ⟶ (pullbackFiber p x f).1) [p.IsHomLift g φ]
    (hφ : φ ≫ IsPreFibered.pullbackMap x.2 f = IsPreFibered.pullbackMap x.2 (g ≫ f)) :
    φ = pullbackFiberProj x f g :=
  IsStronglyCartesian.ext p f (IsPreFibered.pullbackMap x.2 f) g
    (by rw [hφ, pullbackFiberProj_fac])

/-- The chosen pullbacks along two equal morphisms of the base are the same object, and the
`eqToHom` between them is compatible with the chosen cartesian lifts. -/
@[reassoc]
lemma eqToHom_comp_pullbackMap {U V : 𝒞} (x : p.Fiber U) {f f' : V ⟶ U} (hff' : f = f')
    (h : (pullbackFiber p x f).1 = (pullbackFiber p x f').1) :
    eqToHom h ≫ IsPreFibered.pullbackMap x.2 f' = IsPreFibered.pullbackMap x.2 f := by
  subst hff'
  simp

/-- Base change along an identity of the base is the canonical identification
`(𝟙 V ≫ f)^* x = f^* x`. -/
lemma pullbackFiberProj_id {U V : 𝒞} (x : p.Fiber U) (f : V ⟶ U)
    (h : (pullbackFiber p x (𝟙 V ≫ f)).1 = (pullbackFiber p x f).1) :
    pullbackFiberProj x f (𝟙 V) = eqToHom h := by
  have : p.IsHomLift (𝟙 V) (eqToHom h) :=
    IsHomLift.eqToHom_domain_lift_id h (pullbackFiber p x (𝟙 V ≫ f)).2
  exact (pullbackFiberProj_uniq x f (𝟙 V) (eqToHom h)
    (eqToHom_comp_pullbackMap x (Category.id_comp f) h)).symm

/-- Base change along a composite `g' ≫ g` of the base is base change along `g` after base change
along `g'`, up to the canonical identification `(g' ≫ g ≫ f)^* x = ((g' ≫ g) ≫ f)^* x`. -/
@[reassoc]
lemma pullbackFiberProj_comp {U V V' V'' : 𝒞} (x : p.Fiber U) (f : V ⟶ U) (g : V' ⟶ V)
    (g' : V'' ⟶ V') (h : (pullbackFiber p x (g' ≫ g ≫ f)).1 =
      (pullbackFiber p x ((g' ≫ g) ≫ f)).1) :
    pullbackFiberProj x (g ≫ f) g' ≫ pullbackFiberProj x f g =
      eqToHom h ≫ pullbackFiberProj x f (g' ≫ g) := by
  have h₁ : p.IsHomLift (g' ≫ g) (pullbackFiberProj x (g ≫ f) g' ≫ pullbackFiberProj x f g) :=
    inferInstance
  have h₂ : p.IsHomLift (g' ≫ g) (eqToHom h ≫ pullbackFiberProj x f (g' ≫ g)) := inferInstance
  refine IsStronglyCartesian.ext p f (IsPreFibered.pullbackMap x.2 f) (g' ≫ g) ?_
  rw [Category.assoc, pullbackFiberProj_fac, pullbackFiberProj_fac, Category.assoc,
    pullbackFiberProj_fac, eqToHom_comp_pullbackMap x (Category.assoc g' g f).symm]

/-! #### Mapping into a chosen pullback

A morphism `φ : z ⟶ y` of `𝒳` lying over `b : W ⟶ U`, with `z` in the fibre over `W` and `y` in the
fibre over `U`, factors uniquely through the chosen cartesian lift of `b` at `y` by a *vertical*
morphism `z ⟶ b^* y`. This is the universal property of the chosen pullback, packaged as a morphism
of the fibre over `W`. -/

/-- The vertical morphism `z ⟶ b^* y` through which a morphism `φ : z ⟶ y` over `b` factors. -/
noncomputable def toPullbackFiber (p : 𝒳 ⥤ 𝒞) [p.IsPreFibered] {W U : 𝒞} (z : p.Fiber W)
    (y : p.Fiber U) (b : W ⟶ U) (φ : z.1 ⟶ y.1) [p.IsHomLift b φ] :
    z ⟶ pullbackFiber p y b :=
  ⟨IsCartesian.map p b (IsPreFibered.pullbackMap y.2 b) φ, inferInstance⟩

/-- The vertical morphism `z ⟶ b^* y` followed by the chosen cartesian lift of `b` recovers `φ`. -/
@[reassoc (attr := simp)]
lemma toPullbackFiber_fac (p : 𝒳 ⥤ 𝒞) [p.IsPreFibered] {W U : 𝒞} (z : p.Fiber W) (y : p.Fiber U)
    (b : W ⟶ U) (φ : z.1 ⟶ y.1) [p.IsHomLift b φ] :
    Fiber.fiberInclusion.map (toPullbackFiber p z y b φ) ≫ IsPreFibered.pullbackMap y.2 b = φ :=
  IsCartesian.fac p b (IsPreFibered.pullbackMap y.2 b) φ

/-- The factorization of `φ` through the chosen cartesian lift of `b` is unique. -/
lemma toPullbackFiber_uniq (p : 𝒳 ⥤ 𝒞) [p.IsPreFibered] {W U : 𝒞} (z : p.Fiber W) (y : p.Fiber U)
    (b : W ⟶ U) (φ : z.1 ⟶ y.1) [p.IsHomLift b φ] (β : z ⟶ pullbackFiber p y b)
    (hβ : Fiber.fiberInclusion.map β ≫ IsPreFibered.pullbackMap y.2 b = φ) :
    β = toPullbackFiber p z y b φ :=
  fiber_hom_ext_of_cartesian b (IsPreFibered.pullbackMap y.2 b) inferInstance _ _
    (by rw [hβ, toPullbackFiber_fac])

end PullbackFiberProj

/-! ### The split model of a fibred category

Following the proof of Stacks 004A, the split model `𝒮'` of a fibred category `p : 𝒳 ⥤ 𝒞` has as
objects the pairs `(x, f)` with `f : V ⟶ U` a morphism of `𝒞` and `x` an object of the fibre `𝒳_U`,
its structure functor sends `(x, f : V ⟶ U)` to `V`, and a morphism
`(x₁, f₁ : V₁ ⟶ U₁) ⟶ (x₂, f₂ : V₂ ⟶ U₂)` is a pair `(g : V₁ ⟶ V₂, φ : f₁^* x₁ ⟶ f₂^* x₂)` with
`p(φ) = g`. Here that category is presented, equivalently, as the Grothendieck construction of a
presheaf of categories: `SplitFiber p V` is the fibre of `𝒮'` over `V`, i.e. the pairs `(x, f)`
whose `f` has source `V`, with the *vertical* morphisms between them, and the presheaf structure
is the pullback `g^*(x, f) = (x, f ∘ g)` of the last paragraph of the source's proof. -/

/-- An object of the fibre over `V` of the split model of a fibred category `p : 𝒳 ⥤ 𝒞`: a pair
`(x, f)` consisting of a morphism `f : V ⟶ U` of `𝒞` and an object `x` of the fibre `𝒳_U`. -/
structure SplitFiber (p : 𝒳 ⥤ 𝒞) (V : 𝒞) where
  /-- The object `U` of `𝒞` that `x` lies over. -/
  base : 𝒞
  /-- The object `x` of the fibre `𝒳_U`. -/
  obj : p.Fiber base
  /-- The morphism `f : V ⟶ U`. -/
  hom : V ⟶ base

namespace SplitFiber

section Basic

variable {p : 𝒳 ⥤ 𝒞} [p.IsPreFibered] {V : 𝒞}

/-- The object `f^* x` of the fibre `𝒳_V` that the pair `(x, f)` stands for, namely the chosen
pullback of `x` along `f`. -/
noncomputable abbrev toFiber (o : SplitFiber p V) : p.Fiber V :=
  pullbackFiber p o.obj o.hom

/-- The chosen cartesian lift `f^* x ⟶ x` of `f` attached to the pair `(x, f)`. -/
noncomputable abbrev proj (o : SplitFiber p V) : o.toFiber.1 ⟶ o.obj.1 :=
  IsPreFibered.pullbackMap o.obj.2 o.hom

/-- The category structure on the fibre of the split model: a morphism `(x₁, f₁) ⟶ (x₂, f₂)` is
*by definition* a morphism `f₁^* x₁ ⟶ f₂^* x₂` of the fibre `𝒳_V`, that is a morphism of `𝒳` lying
over `𝟙 V`. This is the source's "`φ : f₁^* x₁ ⟶ f₂^* x₂` with `p(φ) = id`", and it makes all three
category axioms hold on the nose, inherited from `𝒳_V`. -/
noncomputable instance category : Category.{v₂} (SplitFiber p V) where
  Hom o o' := o.toFiber ⟶ o'.toFiber
  id o := 𝟙 o.toFiber
  comp α β := α ≫ β
  id_comp _ := Category.id_comp _
  comp_id _ := Category.comp_id _
  assoc _ _ _ := Category.assoc _ _ _

/-- A morphism of `SplitFiber p V` read as a morphism of the fibre `𝒳_V`; the two hom types are
equal by definition. -/
def toFiberHom {o o' : SplitFiber p V} (α : o ⟶ o') : o.toFiber ⟶ o'.toFiber := α

/-- A morphism of the fibre `𝒳_V` read as a morphism of `SplitFiber p V`, the inverse of
`CategoryTheory.Functor.SplitFiber.toFiberHom`. -/
def ofFiberHom {o o' : SplitFiber p V} (α : o.toFiber ⟶ o'.toFiber) : o ⟶ o' := α

/-- Reading a morphism of the fibre as a morphism of `SplitFiber p V` and back is the identity. -/
@[simp] lemma toFiberHom_ofFiberHom {o o' : SplitFiber p V} (α : o.toFiber ⟶ o'.toFiber) :
    toFiberHom (ofFiberHom α) = α := rfl

/-- Reading a morphism of `SplitFiber p V` in the fibre and back is the identity. -/
@[simp] lemma ofFiberHom_toFiberHom {o o' : SplitFiber p V} (α : o ⟶ o') :
    ofFiberHom (toFiberHom α) = α := rfl

/-- Two morphisms of `SplitFiber p V` agree as soon as the underlying morphisms of the fibre do. -/
lemma toFiberHom_injective {o o' : SplitFiber p V} {α β : o ⟶ o'}
    (h : toFiberHom α = toFiberHom β) : α = β := h

/-- The identity of `o` is the identity of `o.toFiber` in the fibre. -/
@[simp] lemma toFiberHom_id (o : SplitFiber p V) : toFiberHom (𝟙 o) = 𝟙 o.toFiber := rfl

/-- Composition in `SplitFiber p V` is composition in the fibre `𝒳_V`. -/
@[simp] lemma toFiberHom_comp {o o' o'' : SplitFiber p V} (α : o ⟶ o') (β : o' ⟶ o'') :
    toFiberHom (α ≫ β) = toFiberHom α ≫ toFiberHom β := rfl

/-- An equality of objects of `SplitFiber p V` induces, in the fibre `𝒳_V`, the `eqToHom` between
the corresponding chosen pullbacks. -/
lemma toFiberHom_eqToHom {o o' : SplitFiber p V} (h : o = o') (h' : o.toFiber = o'.toFiber) :
    toFiberHom (eqToHom h) = eqToHom h' := by
  subst h
  simp

/-- An isomorphism of the fibre `𝒳_V` between the chosen pullbacks attached to two objects of
`SplitFiber p V` is an isomorphism of `SplitFiber p V`. -/
@[simps]
noncomputable def isoOfFiberIso {o o' : SplitFiber p V} (e : o.toFiber ≅ o'.toFiber) : o ≅ o' where
  hom := ofFiberHom e.hom
  inv := ofFiberHom e.inv
  hom_inv_id := toFiberHom_injective (by simp)
  inv_hom_id := toFiberHom_injective (by simp)

end Basic

section Restrict

variable {p : 𝒳 ⥤ 𝒞} [p.IsFibered] {V V' V'' : 𝒞}

/-- The morphism `(g ≫ f₁)^* x₁ ⟶ (g ≫ f₂)^* x₂` of `𝒳_{V'}` obtained from a morphism
`α : f₁^* x₁ ⟶ f₂^* x₂` of `𝒳_V` by base change along `g : V' ⟶ V`: the unique vertical morphism
whose composite with the chosen cartesian lift of `g ≫ f₂` at `x₂` is
`(g ≫ f₁)^* x₁ ⟶ f₁^* x₁ ⟶ f₂^* x₂ ⟶ x₂`.

This is the source's `g^* φ`. It generalizes `CategoryTheory.Functor.morRestrict` (Stacks 026A)
to a pair of objects living over *different* objects of `𝒞` and pulled back along *different*
morphisms, which is what the objects of `SplitFiber p V` require; the two agree when `x₁` and
`x₂` lie over one and the same `U` and `f₁ = f₂`. -/
noncomputable def restrictHom (g : V' ⟶ V) {o o' : SplitFiber p V} (α : o.toFiber ⟶ o'.toFiber) :
    pullbackFiber p o.obj (g ≫ o.hom) ⟶ pullbackFiber p o'.obj (g ≫ o'.hom) :=
  have h : p.IsHomLift (g ≫ 𝟙 V ≫ o'.hom) (pullbackFiberProj o.obj o.hom g ≫
      Fiber.fiberInclusion.map α ≫ o'.proj) := inferInstance
  have : p.IsHomLift (g ≫ o'.hom) (pullbackFiberProj o.obj o.hom g ≫
      Fiber.fiberInclusion.map α ≫ o'.proj) := by rwa [Category.id_comp] at h
  ⟨IsCartesian.map p (g ≫ o'.hom) (IsPreFibered.pullbackMap o'.obj.2 (g ≫ o'.hom))
      (pullbackFiberProj o.obj o.hom g ≫ Fiber.fiberInclusion.map α ≫ o'.proj),
    inferInstance⟩

/-- The defining factorization of base change: `g^* α` followed by the chosen cartesian lift of
`g ≫ f₂` is `(g ≫ f₁)^* x₁ ⟶ f₁^* x₁ ⟶ f₂^* x₂ ⟶ x₂`. -/
@[reassoc]
lemma restrictHom_fac (g : V' ⟶ V) {o o' : SplitFiber p V} (α : o.toFiber ⟶ o'.toFiber) :
    Fiber.fiberInclusion.map (restrictHom g α) ≫
        IsPreFibered.pullbackMap o'.obj.2 (g ≫ o'.hom) =
      pullbackFiberProj o.obj o.hom g ≫ Fiber.fiberInclusion.map α ≫ o'.proj := by
  have h : p.IsHomLift (g ≫ 𝟙 V ≫ o'.hom) (pullbackFiberProj o.obj o.hom g ≫
      Fiber.fiberInclusion.map α ≫ o'.proj) := inferInstance
  have : p.IsHomLift (g ≫ o'.hom) (pullbackFiberProj o.obj o.hom g ≫
      Fiber.fiberInclusion.map α ≫ o'.proj) := by rwa [Category.id_comp] at h
  exact IsCartesian.fac p (g ≫ o'.hom) (IsPreFibered.pullbackMap o'.obj.2 (g ≫ o'.hom)) _

/-- Base change along `g` is the unique vertical morphism with the factorization of
`CategoryTheory.Functor.SplitFiber.restrictHom_fac`. -/
lemma restrictHom_uniq (g : V' ⟶ V) {o o' : SplitFiber p V} (α : o.toFiber ⟶ o'.toFiber)
    (β : pullbackFiber p o.obj (g ≫ o.hom) ⟶ pullbackFiber p o'.obj (g ≫ o'.hom))
    (hβ : Fiber.fiberInclusion.map β ≫ IsPreFibered.pullbackMap o'.obj.2 (g ≫ o'.hom) =
      pullbackFiberProj o.obj o.hom g ≫ Fiber.fiberInclusion.map α ≫ o'.proj) :
    β = restrictHom g α :=
  fiber_hom_ext_of_cartesian (g ≫ o'.hom)
    (IsPreFibered.pullbackMap o'.obj.2 (g ≫ o'.hom)) inferInstance _ _
    (by rw [hβ, restrictHom_fac])

/-- Base change is natural with respect to the canonical morphisms `(g ≫ f)^* x ⟶ f^* x`. -/
@[reassoc]
lemma restrictHom_comp_pullbackFiberProj (g : V' ⟶ V) {o o' : SplitFiber p V}
    (α : o.toFiber ⟶ o'.toFiber) :
    Fiber.fiberInclusion.map (restrictHom g α) ≫ pullbackFiberProj o'.obj o'.hom g =
      pullbackFiberProj o.obj o.hom g ≫ Fiber.fiberInclusion.map α := by
  have h₁ : p.IsHomLift g (Fiber.fiberInclusion.map (restrictHom g α) ≫
      pullbackFiberProj o'.obj o'.hom g) := by
    have h : p.IsHomLift (𝟙 V' ≫ g) (Fiber.fiberInclusion.map (restrictHom g α) ≫
      pullbackFiberProj o'.obj o'.hom g) := inferInstance
    rwa [Category.id_comp] at h
  have h₂ : p.IsHomLift g (pullbackFiberProj o.obj o.hom g ≫ Fiber.fiberInclusion.map α) := by
    have h : p.IsHomLift (g ≫ 𝟙 V) (pullbackFiberProj o.obj o.hom g ≫
      Fiber.fiberInclusion.map α) := inferInstance
    rwa [Category.comp_id] at h
  refine IsStronglyCartesian.ext p o'.hom o'.proj g ?_
  rw [Category.assoc, Category.assoc, pullbackFiberProj_fac, restrictHom_fac]

/-- Base change of an identity is the identity. -/
@[simp]
lemma restrictHom_id (g : V' ⟶ V) (o : SplitFiber p V) :
    restrictHom g (𝟙 o.toFiber) = 𝟙 _ :=
  (restrictHom_uniq g (𝟙 o.toFiber) (𝟙 _) (by simp [Fiber.fiberInclusion])).symm

/-- Base change of a composite is the composite of the base changes. -/
lemma restrictHom_comp (g : V' ⟶ V) {o o' o'' : SplitFiber p V} (α : o.toFiber ⟶ o'.toFiber)
    (β : o'.toFiber ⟶ o''.toFiber) :
    restrictHom g (α ≫ β) = restrictHom g α ≫ restrictHom g β := by
  refine (restrictHom_uniq g (α ≫ β) _ ?_).symm
  rw [Functor.map_comp, Category.assoc, restrictHom_fac, restrictHom_comp_pullbackFiberProj_assoc,
    Functor.map_comp, Category.assoc]

/-- The pullback functor `g^*` of the split model, as in the last paragraph of the proof of
Stacks 004A: `g^*(x, f) = (x, f ∘ g)` on objects, and base change on morphisms. -/
noncomputable def restrict (p : 𝒳 ⥤ 𝒞) [p.IsFibered] (g : V' ⟶ V) :
    SplitFiber p V ⥤ SplitFiber p V' where
  obj o := ⟨o.base, o.obj, g ≫ o.hom⟩
  map α := ofFiberHom (restrictHom g (toFiberHom α))
  map_id o := toFiberHom_injective (by simp)
  map_comp α β := toFiberHom_injective (by simp [restrictHom_comp])

/-- Restriction along `g` precomposes the structure morphism with `g`. -/
lemma restrict_obj (g : V' ⟶ V) (o : SplitFiber p V) :
    (restrict p g).obj o = ⟨o.base, o.obj, g ≫ o.hom⟩ := rfl

/-- Restriction along `g` does not change the base object. -/
@[simp] lemma restrict_obj_base (g : V' ⟶ V) (o : SplitFiber p V) :
    ((restrict p g).obj o).base = o.base := rfl

/-- Restriction along `g` does not change the object of the fibre. -/
@[simp] lemma restrict_obj_obj (g : V' ⟶ V) (o : SplitFiber p V) :
    ((restrict p g).obj o).obj = o.obj := rfl

/-- The structure morphism of the restriction along `g` is `g ≫ o.hom`. -/
@[simp] lemma restrict_obj_hom (g : V' ⟶ V) (o : SplitFiber p V) :
    ((restrict p g).obj o).hom = g ≫ o.hom := rfl

/-- On morphisms, restriction along `g` is the base change `restrictHom g`. -/
@[simp] lemma toFiberHom_restrict_map (g : V' ⟶ V) {o o' : SplitFiber p V} (α : o ⟶ o') :
    toFiberHom ((restrict p g).map α) = restrictHom g (toFiberHom α) := rfl

/-- Restriction along an identity is the identity: the unit case of the source's
`g₁^* ∘ g₂^* = (g₂ ∘ g₁)^*`. -/
lemma restrict_id (p : 𝒳 ⥤ 𝒞) [p.IsFibered] (V : 𝒞) :
    restrict p (𝟙 V) = 𝟭 (SplitFiber p V) := by
  have hobj : ∀ o : SplitFiber p V, (restrict p (𝟙 V)).obj o = o := by
    intro o
    obtain ⟨U, x, f⟩ := o
    rw [restrict_obj, Category.id_comp]
  refine Functor.ext hobj fun o o' α => ?_
  refine toFiberHom_injective ?_
  rw [Functor.id_map, toFiberHom_restrict_map, toFiberHom_comp, toFiberHom_comp,
    toFiberHom_eqToHom (hobj o) (congrArg toFiber (hobj o)),
    toFiberHom_eqToHom (hobj o').symm (congrArg toFiber (hobj o').symm)]
  refine (restrictHom_uniq (𝟙 V) (toFiberHom α) _ ?_).symm
  simp only [Functor.map_comp, eqToHom_map, Category.assoc]
  rw [eqToHom_comp_pullbackMap o'.obj (Category.id_comp o'.hom).symm,
    ← pullbackFiberProj_id o.obj o.hom]

/-- Restriction along a composite is the composite of the restrictions: this is the source's
`g₁^* ∘ g₂^* = (g₂ ∘ g₁)^*`, which is what makes the model split. -/
lemma restrict_comp (p : 𝒳 ⥤ 𝒞) [p.IsFibered] (g : V' ⟶ V) (g' : V'' ⟶ V') :
    restrict p g ⋙ restrict p g' = restrict p (g' ≫ g) := by
  have hobj : ∀ o : SplitFiber p V,
      (restrict p g ⋙ restrict p g').obj o = (restrict p (g' ≫ g)).obj o := by
    intro o
    obtain ⟨U, x, f⟩ := o
    rw [Functor.comp_obj, restrict_obj, restrict_obj, restrict_obj, Category.assoc]
  refine Functor.ext hobj fun o o' α => ?_
  refine toFiberHom_injective ?_
  rw [Functor.comp_map, toFiberHom_restrict_map, toFiberHom_restrict_map, toFiberHom_comp,
    toFiberHom_comp, toFiberHom_restrict_map,
    toFiberHom_eqToHom (hobj o) (congrArg toFiber (hobj o)),
    toFiberHom_eqToHom (hobj o').symm (congrArg toFiber (hobj o').symm)]
  refine (restrictHom_uniq g' _ _ ?_).symm
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, proj, restrict_obj_base,
    restrict_obj_obj, restrict_obj_hom]
  rw [eqToHom_comp_pullbackMap o'.obj (Category.assoc g' g o'.hom), restrictHom_fac,
    restrictHom_fac, pullbackFiberProj_comp_assoc o.obj o.hom g g' (by rw [Category.assoc])]

end Restrict

end SplitFiber

/-! ### The presheaf of categories attached to a fibred category -/

/-- **Stacks 004A**, the contravariant functor `F : 𝒞 ⥤ Cat`: the fibre of the split model over
`V`, with the pullback functors of the last paragraph of the source's proof as its restriction
maps. Because those satisfy `g₁^* ∘ g₂^* = (g₂ ∘ g₁)^*` on the nose, this is an honest functor
into the 2-category `Cat` and not merely a pseudofunctor. -/
noncomputable def splitPresheaf (p : 𝒳 ⥤ 𝒞) [p.IsFibered] : 𝒞ᵒᵖ ⥤ Cat.{v₂, max u₁ u₂ v₁} where
  obj V := Cat.of (SplitFiber p V.unop)
  map g := (SplitFiber.restrict p g.unop).toCatHom
  map_id V := Cat.ext (by
    rw [Cat.Hom.id_toFunctor]
    exact SplitFiber.restrict_id p V.unop)
  map_comp g g' := Cat.ext (by
    rw [Cat.Hom.comp_toFunctor]
    exact (SplitFiber.restrict_comp p g.unop g'.unop).symm)

/-- The value of `splitPresheaf p` at `V` is the category `SplitFiber p V.unop`. -/
@[simp] lemma splitPresheaf_obj (p : 𝒳 ⥤ 𝒞) [p.IsFibered] (V : 𝒞ᵒᵖ) :
    (splitPresheaf p).obj V = Cat.of (SplitFiber p V.unop) := rfl

/-- The restriction functor of `splitPresheaf p` along `g` is `SplitFiber.restrict p g.unop`. -/
@[simp] lemma splitPresheaf_map (p : 𝒳 ⥤ 𝒞) [p.IsFibered] {V W : 𝒞ᵒᵖ} (g : V ⟶ W) :
    ((splitPresheaf p).map g).toFunctor = SplitFiber.restrict p g.unop := rfl

/-! ### The comparison functor `𝒮 ⥤ 𝒮'` and the equivalence -/

section ToSplit

variable (p : 𝒳 ⥤ 𝒞) [p.IsFibered]

/-- The object `(x, id_{p(x)})` of the fibre of the split model over `p.obj x`: the image of `x`
under the source's natural functor `𝒮 → 𝒮'`. -/
noncomputable abbrev splitSelf (x : 𝒳) : SplitFiber p (p.obj x) :=
  ⟨p.obj x, Fiber.mk rfl, 𝟙 (p.obj x)⟩

/-- The fibre component of the image of `ψ : x ⟶ y` under the source's natural functor `𝒮 → 𝒮'`:
the unique vertical morphism `(x, id) ⟶ p(ψ)^* (y, id)` whose composite with the chosen cartesian
lift is the composite `id^* x ⟶ x ⟶ y`. -/
noncomputable def toSplitHom {x y : 𝒳} (ψ : x ⟶ y) :
    splitSelf p x ⟶ (SplitFiber.restrict p (p.map ψ)).obj (splitSelf p y) :=
  have h : p.IsHomLift (𝟙 (p.obj x) ≫ p.map ψ ≫ 𝟙 (p.obj y)) ((splitSelf p x).proj ≫ ψ) :=
    inferInstance
  have : p.IsHomLift (p.map ψ ≫ 𝟙 (p.obj y)) ((splitSelf p x).proj ≫ ψ) := by
    rwa [Category.id_comp] at h
  SplitFiber.ofFiberHom (toPullbackFiber p (splitSelf p x).toFiber
    (Fiber.mk (rfl : p.obj y = p.obj y)) (p.map ψ ≫ 𝟙 (p.obj y)) ((splitSelf p x).proj ≫ ψ))

/-- The defining factorization of `CategoryTheory.Functor.toSplitHom`: the fibre component of the
image of `ψ`, followed by the chosen cartesian lift of `p(ψ)`, is `id^* x ⟶ x ⟶ y`. -/
@[reassoc (attr := simp)]
lemma toSplitHom_fac {x y : 𝒳} (ψ : x ⟶ y) :
    Fiber.fiberInclusion.map (SplitFiber.toFiberHom (toSplitHom p ψ)) ≫
        IsPreFibered.pullbackMap (Fiber.mk (rfl : p.obj y = p.obj y)).2 (p.map ψ ≫ 𝟙 (p.obj y)) =
      IsPreFibered.pullbackMap (Fiber.mk (rfl : p.obj x = p.obj x)).2 (𝟙 (p.obj x)) ≫ ψ := by
  rw [toSplitHom, SplitFiber.toFiberHom_ofFiberHom, toPullbackFiber_fac]

/-- The fibre component of the image of `ψ` is the unique vertical morphism with the factorization
of `CategoryTheory.Functor.toSplitHom_fac`. -/
lemma toSplitHom_uniq {x y : 𝒳} (ψ : x ⟶ y)
    (β : splitSelf p x ⟶ (SplitFiber.restrict p (p.map ψ)).obj (splitSelf p y))
    (hβ : Fiber.fiberInclusion.map (SplitFiber.toFiberHom β) ≫
        IsPreFibered.pullbackMap (Fiber.mk (rfl : p.obj y = p.obj y)).2 (p.map ψ ≫ 𝟙 (p.obj y)) =
      IsPreFibered.pullbackMap (Fiber.mk (rfl : p.obj x = p.obj x)).2 (𝟙 (p.obj x)) ≫ ψ) :
    β = toSplitHom p ψ :=
  SplitFiber.toFiberHom_injective (fiber_hom_ext_of_cartesian (p.map ψ ≫ 𝟙 (p.obj y))
    (IsPreFibered.pullbackMap (Fiber.mk (rfl : p.obj y = p.obj y)).2 (p.map ψ ≫ 𝟙 (p.obj y)))
    inferInstance _ _ (by rw [hβ, toSplitHom_fac]))

/-- The source's natural functor `𝒮 → 𝒮'` of the proof of Stacks 004A: an object `x` of `𝒳` lying
over `U` is sent to the pair `(x, id_U)`, and a morphism `ψ` to the pair `(p(ψ), ψ)`, the second
component being read through the universal property of the chosen pullbacks. -/
noncomputable def toSplit : 𝒳 ⥤ ∫ᶜ (splitPresheaf p).toPseudofunctor' where
  obj x := ⟨p.obj x, splitSelf p x⟩
  map ψ := { base := p.map ψ, fiber := toSplitHom p ψ }
  map_id x := by
    have hx : splitSelf p x = (SplitFiber.restrict p (p.map (𝟙 x))).obj (splitSelf p x) := by
      rw [Functor.map_id, SplitFiber.restrict_id]
      rfl
    refine CoGrothendieck.Hom.ext _ _ (by simp) ?_
    simp only [CoGrothendieck.categoryStruct_id_fiber, Functor.toPseudofunctor'_mapId,
      eqToIso.inv, Cat.eqToHom_app, eqToHom_trans]
    refine (toSplitHom_uniq p (𝟙 x) _ ?_).symm
    rw [SplitFiber.toFiberHom_eqToHom _ (congrArg SplitFiber.toFiber hx),
      eqToHom_map Fiber.fiberInclusion,
      eqToHom_comp_pullbackMap (Fiber.mk (rfl : p.obj x = p.obj x))
        (show 𝟙 (p.obj x) = p.map (𝟙 x) ≫ 𝟙 (p.obj x) by simp)]
    exact (Category.comp_id _).symm
  map_comp {x y z} ψ χ := by
    have hxz : (SplitFiber.restrict p (p.map ψ)).obj ((SplitFiber.restrict p (p.map χ)).obj
        (splitSelf p z)) = (SplitFiber.restrict p (p.map (ψ ≫ χ))).obj (splitSelf p z) := by
      rw [Functor.map_comp, ← SplitFiber.restrict_comp]
      rfl
    -- `SplitFiber.restrictHom_fac` restated with the projections of `(restrict p (p.map χ)).obj`
    -- evaluated, which is the form in which the goal below presents it.
    have hres : Fiber.fiberInclusion.map (SplitFiber.restrictHom (p.map ψ)
          (SplitFiber.toFiberHom (toSplitHom p χ))) ≫
        IsPreFibered.pullbackMap (Fiber.mk (rfl : p.obj z = p.obj z)).2
          (p.map ψ ≫ p.map χ ≫ 𝟙 (p.obj z)) =
      pullbackFiberProj (Fiber.mk (rfl : p.obj y = p.obj y)) (𝟙 (p.obj y)) (p.map ψ) ≫
        Fiber.fiberInclusion.map (SplitFiber.toFiberHom (toSplitHom p χ)) ≫
          IsPreFibered.pullbackMap (Fiber.mk (rfl : p.obj z = p.obj z)).2
            (p.map χ ≫ 𝟙 (p.obj z)) :=
      SplitFiber.restrictHom_fac (p.map ψ) (SplitFiber.toFiberHom (toSplitHom p χ))
    refine CoGrothendieck.Hom.ext _ _ (by simp) ?_
    simp only [CoGrothendieck.categoryStruct_comp_fiber, Functor.toPseudofunctor'_mapComp,
      eqToIso.inv, Cat.eqToHom_app, eqToHom_trans, Category.assoc]
    -- The composition of `∫ᶜ` reads the fibre of the composite through the pullback functors of
    -- the presheaf; spell those out as `SplitFiber.restrict`.
    change toSplitHom p (ψ ≫ χ) = toSplitHom p ψ ≫
      (SplitFiber.restrict p (p.map ψ)).map (toSplitHom p χ) ≫ eqToHom _
    refine (toSplitHom_uniq p (ψ ≫ χ) _ ?_).symm
    rw [SplitFiber.toFiberHom_comp, SplitFiber.toFiberHom_comp,
      SplitFiber.toFiberHom_restrict_map,
      SplitFiber.toFiberHom_eqToHom _ (congrArg SplitFiber.toFiber hxz),
      Fiber.fiberInclusion.map_comp, Fiber.fiberInclusion.map_comp, Category.assoc,
      Category.assoc, eqToHom_map Fiber.fiberInclusion,
      eqToHom_comp_pullbackMap (Fiber.mk (rfl : p.obj z = p.obj z))
        (show p.map ψ ≫ p.map χ ≫ 𝟙 (p.obj z) = p.map (ψ ≫ χ) ≫ 𝟙 (p.obj z) by simp),
      hres, toSplitHom_fac, pullbackFiberProj_fac_assoc, toSplitHom_fac_assoc]

/-- The comparison functor sends `x` to an object over `p.obj x`. -/
@[simp] lemma toSplit_obj_base (x : 𝒳) : ((toSplit p).obj x).base = p.obj x := rfl

/-- The base component of the image of `ψ` under the comparison functor is `p.map ψ`. -/
@[simp] lemma toSplit_map_base {x y : 𝒳} (ψ : x ⟶ y) : ((toSplit p).map ψ).base = p.map ψ := rfl

/-- The fibre component of the image of `ψ` under the comparison functor is `toSplitHom p ψ`. -/
@[simp] lemma toSplit_map_fiber {x y : 𝒳} (ψ : x ⟶ y) :
    ((toSplit p).map ψ).fiber = toSplitHom p ψ := rfl

/-- The comparison functor is strictly over `𝒞`. -/
lemma toSplit_comp_forget :
    toSplit p ⋙ CoGrothendieck.forget (splitPresheaf p).toPseudofunctor' = p := rfl

/-- The chosen cartesian lift of an identity is an isomorphism. -/
@[sga "1 VI 6.12" "special case"]
instance isIso_pullbackMap_id {T : 𝒞} (y : p.Fiber T) :
    IsIso (IsPreFibered.pullbackMap y.2 (𝟙 T)) := by
  rw [← pullbackFiberIdIso_hom_fac]
  infer_instance

/-- The comparison functor is faithful: a morphism of `𝒮'` between the images of `x` and `y`
determines its second component, and the chosen cartesian lift of an identity is an epimorphism. -/
instance : (toSplit p).Faithful where
  map_injective {x y} {ψ ψ'} h := by
    have hb : p.map ψ = p.map ψ' := congrArg CoGrothendieck.Hom.base h
    have hEq : (SplitFiber.restrict p (p.map ψ')).obj (splitSelf p y) =
        (SplitFiber.restrict p (p.map ψ)).obj (splitSelf p y) := by rw [hb]
    have hfib : toSplitHom p ψ = toSplitHom p ψ' ≫ eqToHom hEq := CoGrothendieck.Hom.congr h
    have hf' : Fiber.fiberInclusion.map (SplitFiber.toFiberHom (toSplitHom p ψ)) ≫
          IsPreFibered.pullbackMap (Fiber.mk (rfl : p.obj y = p.obj y)).2
            (p.map ψ ≫ 𝟙 (p.obj y)) =
        Fiber.fiberInclusion.map (SplitFiber.toFiberHom (toSplitHom p ψ' ≫ eqToHom hEq)) ≫
          IsPreFibered.pullbackMap (Fiber.mk (rfl : p.obj y = p.obj y)).2
            (p.map ψ ≫ 𝟙 (p.obj y)) := by
      rw [hfib]
    rw [toSplitHom_fac, SplitFiber.toFiberHom_comp, Fiber.fiberInclusion.map_comp,
      Category.assoc, SplitFiber.toFiberHom_eqToHom _ (congrArg SplitFiber.toFiber hEq),
      eqToHom_map Fiber.fiberInclusion,
      eqToHom_comp_pullbackMap (Fiber.mk (rfl : p.obj y = p.obj y))
        (show p.map ψ' ≫ 𝟙 (p.obj y) = p.map ψ ≫ 𝟙 (p.obj y) by rw [hb]),
      toSplitHom_fac] at hf'
    exact (cancel_epi (IsPreFibered.pullbackMap (Fiber.mk (rfl : p.obj x = p.obj x)).2
      (𝟙 (p.obj x)))).1 hf'

/-- The comparison functor is full: a morphism `(g, φ) : (x, id) ⟶ (y, id)` of `𝒮'` is the image of
the composite `x ⟶ id^* x ⟶ g^* y ⟶ y`. -/
instance : (toSplit p).Full where
  map_surjective {x y} u := by
    set ψ := _root_.CategoryTheory.inv
      (IsPreFibered.pullbackMap (Fiber.mk (rfl : p.obj x = p.obj x)).2 (𝟙 (p.obj x))) ≫
      Fiber.fiberInclusion.map (SplitFiber.toFiberHom u.fiber) ≫
        IsPreFibered.pullbackMap (Fiber.mk (rfl : p.obj y = p.obj y)).2
          (u.base ≫ 𝟙 (p.obj y)) with hψdef
    refine ⟨ψ, ?_⟩
    have hlift : p.IsHomLift u.base ψ := by
      have h0 : p.IsHomLift (𝟙 (p.obj x) ≫ 𝟙 (p.obj x) ≫ u.base ≫ 𝟙 (p.obj y)) ψ := by
        rw [hψdef]
        infer_instance
      simpa using h0
    have hb : p.map ψ = u.base := (IsHomLift.eq_of_isHomLift p u.base ψ).symm
    have hEq : (SplitFiber.restrict p u.base).obj (splitSelf p y) =
        (SplitFiber.restrict p (p.map ψ)).obj (splitSelf p y) := by rw [hb]
    refine CoGrothendieck.Hom.ext _ _ hb ?_
    simp only [toSplit_map_fiber]
    have key : (u.fiber ≫ eqToHom hEq : splitSelf p x ⟶ _) = toSplitHom p ψ := by
      refine toSplitHom_uniq p ψ _ ?_
      -- Spell out the fibre and the chosen cartesian lift, which the goal presents through the
      -- projections of `splitSelf p y`.
      change Fiber.fiberInclusion.map (SplitFiber.toFiberHom (u.fiber ≫ eqToHom hEq)) ≫
          IsPreFibered.pullbackMap (Fiber.mk (rfl : p.obj y = p.obj y)).2
            (p.map ψ ≫ 𝟙 (p.obj y)) =
        IsPreFibered.pullbackMap (Fiber.mk (rfl : p.obj x = p.obj x)).2 (𝟙 (p.obj x)) ≫ ψ
      rw [SplitFiber.toFiberHom_comp, Fiber.fiberInclusion.map_comp, Category.assoc,
        SplitFiber.toFiberHom_eqToHom _ (congrArg SplitFiber.toFiber hEq),
        eqToHom_map Fiber.fiberInclusion,
        eqToHom_comp_pullbackMap (Fiber.mk (rfl : p.obj y = p.obj y))
          (show u.base ≫ 𝟙 (p.obj y) = p.map ψ ≫ 𝟙 (p.obj y) by rw [hb]), hψdef]
      simp
    exact key.symm

/-- The image of `x` in `𝒮'`, read as an object of the fibre over any `W` equal to `p.obj x`. -/
lemma toSplit_obj_eq {x : 𝒳} {W : 𝒞} (h : p.obj x = W) :
    (toSplit p).obj x = ⟨W, ⟨p.obj x, Fiber.mk rfl, eqToHom h.symm⟩⟩ := by
  subst h
  refine CoGrothendieck.ext rfl ?_
  simp [toSplit, splitSelf]

/-- The comparison functor is essentially surjective by *vertical* isomorphisms: the object
`(x, f : V ⟶ U)` of `𝒮'` over `V` is isomorphic over `V` to the image of the chosen pullback
`f^* x`. -/
lemma toSplit_essSurj (Y : ∫ᶜ (splitPresheaf p).toPseudofunctor') :
    ∃ (x : 𝒳) (e : (toSplit p).obj x ≅ Y),
      (CoGrothendieck.forget (splitPresheaf p).toPseudofunctor').IsHomLift
        (𝟙 ((CoGrothendieck.forget (splitPresheaf p).toPseudofunctor').obj Y)) e.hom := by
  obtain ⟨V, o⟩ := Y
  have h : p.obj o.toFiber.1 = V := o.toFiber.2
  set o₀ : SplitFiber p V := ⟨p.obj o.toFiber.1, Fiber.mk rfl, eqToHom h.symm⟩ with ho₀
  have hobj : (toSplit p).obj o.toFiber.1 = ⟨V, o₀⟩ := toSplit_obj_eq p h
  have hvert : p.IsHomLift (𝟙 V) o₀.proj := by
    have h1 : p.IsHomLift (eqToHom h.symm) o₀.proj := inferInstance
    refine IsHomLift.of_fac' p (𝟙 V) o₀.proj o₀.toFiber.2 h ?_
    rw [IsHomLift.fac' p (eqToHom h.symm) o₀.proj]
    simp
  have hiso : IsIso o₀.proj := IsStronglyCartesian.isIso_of_base_isIso p (eqToHom h.symm) _
  refine ⟨o.toFiber.1, eqToIso hobj ≪≫
    (CoGrothendieck.ι (splitPresheaf p).toPseudofunctor' V).mapIso
      (SplitFiber.isoOfFiberIso (Fiber.isoMk (asIso o₀.proj) hvert)), ?_⟩
  have hbase : ∀ {A B : ∫ᶜ (splitPresheaf p).toPseudofunctor'} (hAB : A = B)
      (hb : A.base = B.base), (eqToHom hAB).base = eqToHom hb := by
    intro A B hAB hb
    subst hAB
    simp
  refine IsHomLift.of_fac' _ (𝟙 V) _ h rfl ?_
  simp [hbase hobj h]

/-- The comparison functor `𝒮 → 𝒮'` is an equivalence in the 2-category of fibred categories over
`𝒞`. This is the verification the source omits. -/
theorem isFibredEquivalenceOver_toSplit :
    IsFibredEquivalenceOver p (CoGrothendieck.forget (splitPresheaf p).toPseudofunctor')
      (toSplit p) :=
  isFibredEquivalenceOver_of_fullyFaithful (toSplit p) (toSplit_essSurj p)

/-- **Stacks 004A.**
Every fibred category `p : 𝒳 ⥤ 𝒞` is equivalent, in the 2-category of fibred categories over `𝒞`,
to the category `𝒮_F` (Stacks 02XV, `CategoryTheory.presheafOfCategories`) attached to a
contravariant functor `F : 𝒞 ⥤ Cat`; in other words, every fibred category is equivalent to a
split one. -/
@[stacks 004A]
theorem exists_isFibredEquivalenceOver_presheafOfCategories :
    ∃ (F : 𝒞ᵒᵖ ⥤ Cat.{v₂, max u₁ u₂ v₁}) (Φ : 𝒳 ⥤ (presheafOfCategories F).obj),
      IsFibredEquivalenceOver p (presheafOfCategories F).p Φ :=
  ⟨splitPresheaf p, toSplit p, isFibredEquivalenceOver_toSplit p⟩

/-- If `p` is fibred in groupoids then every fibre of the split model is a groupoid: its morphisms
are, by definition, morphisms of the fibres of `p`, and those are all invertible (Stacks 003V). -/
lemma SplitFiber.isGroupoid (hp : p.IsFiberedInGroupoids) (V : 𝒞) :
    IsGroupoid (SplitFiber p V) where
  all_isIso {o o'} α := by
    have : IsGroupoid (p.Fiber V) := hp.fiber_isGroupoid V
    exact ⟨SplitFiber.ofFiberHom (_root_.CategoryTheory.inv (SplitFiber.toFiberHom α)),
      SplitFiber.toFiberHom_injective (by simp),
      SplitFiber.toFiberHom_injective (by simp)⟩

/-- **Stacks 02XY**, the contravariant functor `F : 𝒞 ⥤ Groupoids`: the functor `F` of Stacks 004A,
upgraded to a presheaf of groupoids using that the fibres of a category fibred in groupoids are
groupoids. -/
noncomputable def splitPresheafGrpd (hp : p.IsFiberedInGroupoids) :
    𝒞ᵒᵖ ⥤ Grpd.{v₂, max u₁ u₂ v₁} where
  obj V := @Grpd.of (SplitFiber p V.unop) (@Groupoid.ofIsGroupoid _ _
    (SplitFiber.isGroupoid p hp V.unop))
  map g := SplitFiber.restrict p g.unop
  map_id V := SplitFiber.restrict_id p V.unop
  map_comp g g' := (SplitFiber.restrict_comp p g.unop g'.unop).symm

/-- The presheaf of groupoids of Stacks 02XY is the presheaf of categories of Stacks 004A. -/
lemma splitPresheafGrpd_comp_forgetToCat (hp : p.IsFiberedInGroupoids) :
    splitPresheafGrpd p hp ⋙ Grpd.forgetToCat = splitPresheaf p := rfl

end ToSplit

/-- **Stacks 02XY.**
Every category fibred in groupoids `p : 𝒳 ⥤ 𝒞` is equivalent, in the 2-category of fibred
categories over `𝒞`, to the category `𝒮_F` (Stacks 0049,
`CategoryTheory.presheafOfGroupoids`) attached to a contravariant functor
`F : 𝒞 ⥤ Groupoids`; in other words, every category fibred in groupoids is equivalent to a split
one. -/
@[stacks 02XY]
theorem exists_isFibredEquivalenceOver_presheafOfGroupoids (p : 𝒳 ⥤ 𝒞)
    (hp : p.IsFiberedInGroupoids) :
    ∃ (F : 𝒞ᵒᵖ ⥤ Grpd.{v₂, max u₁ u₂ v₁}) (Φ : 𝒳 ⥤ (presheafOfGroupoids F).obj),
      IsFibredEquivalenceOver p (presheafOfGroupoids F).p Φ :=
  have := hp.isFibered
  ⟨splitPresheafGrpd p hp, toSplit p, isFibredEquivalenceOver_toSplit p⟩

end Functor

end CategoryTheory
