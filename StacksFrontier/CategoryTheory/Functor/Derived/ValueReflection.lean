module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt

/-!
# Reflecting essential constancy, and a value of a right derived functor, along a functor

Let `M : J ⥤ 𝒞` be a diagram and let `G : 𝒞 ⥤ 𝒞'` be a functor. Essential constancy of `M`
(Stacks 05PU(1)) is carried *forward* by `G` with no hypothesis at all, because the witness is a
section of a coprojection and `G` has only to be applied to it; this is
`CategoryTheory.EssentiallyConstantInd.IsEssentiallyConstantWith.map`. The direction asked for by
the proof of [Stacks, Tag 09LK] is the opposite one: there the diagram
`(s : X ⟶ X') ↦ Hom(K, X')` takes values in the derived category of differential graded modules,
only its image in `D(Ab)` is known to be essentially constant, and the witness has to be carried
*backwards* along the forgetful functor.

This file settles what that costs.

## Main results

* `CategoryTheory.EssentiallyConstantInd.exists_isEssentiallyConstantWith_of_comp`: a full and
  faithful `G` whose source has split idempotents reflects essential constancy, *with* the index
  at which the witness sits. No hypothesis on `J` is used.
* `CategoryTheory.EssentiallyConstantInd.isEssentiallyConstantInd_of_comp`: the same for the
  predicate with the value quantified existentially.
* `CategoryTheory.Functor.exists_isRightDerivedValueAt_of_comp` and
  `CategoryTheory.Functor.IsRightDerivable.of_comp`: consequently, for `G` full and faithful with
  `𝒟'` idempotent complete, a value of `R(F ⋙ G)` at `X` produces a value of `RF` at `X`, and
  `F ⋙ G` right derivable makes `F` right derivable. This is the exact converse of
  `CategoryTheory.Functor.IsRightDerivedValueAt.comp`.
* `CategoryTheory.Functor.isEventuallyConstantFrom_of_comp`: *eventual* constancy, by contrast, is
  reflected by any `G` that reflects isomorphisms — a conservative functor suffices, and nothing
  else is needed.
* `CategoryTheory.Functor.not_isEventuallyConstantFrom_of_not_isIso_map`: the price of that
  strength, in the form in which eventual constancy of Deligne's ind-object is refuted — a single
  transition morphism out of the index whose image is not invertible suffices, because eventual
  constancy from an index quantifies over all of them.
* `CategoryTheory.EssentiallyConstantInd.not_reflects_isEssentiallyConstantInd_of_map_eq_zero`:
  the negative statement in the form in which it applies to a conservative functor between
  categories that have zero objects, which is the situation of the forgetful functor
  `D(E, d) ⥤ D(Ab)`. If `G` kills the transition morphisms of `M` cofinally, while no transition
  morphism of `M` out of some one index vanishes, then `M ⋙ G` is essentially constant and `M` is
  not. Its three ingredients are of independent use: cofinal vanishing makes a system essentially
  constant with value a zero object
  (`CategoryTheory.EssentiallyConstantInd.exists_isEssentiallyConstantWith_isZero`), a zero value
  forces cofinal vanishing
  (`CategoryTheory.EssentiallyConstantInd.IsEssentiallyConstantWith.exists_map_eq_zero`), and a
  conservative functor preserving zero morphisms reflects zero objects
  (`CategoryTheory.EssentiallyConstantInd.isZero_of_isZero_map`).
* `CategoryTheory.EssentiallyConstantInd.not_isEssentiallyConstantInd_collapsingSystem` together
  with
  `CategoryTheory.EssentiallyConstantInd.isEssentiallyConstantInd_collapsingSystem_comp_ι`:
  *essential* constancy, by contrast again, is **not** reflected by a conservative functor, and not
  even by a fully faithful one. The witness is the inclusion of the full subcategory of nonzero
  abelian groups and the filtered system over `ℕ` which is constant at `ℤ` with all non-identity
  transition maps zero: in `Ab` it is essentially constant with value the zero group, inside the
  subcategory it is not essentially constant at all.
  `CategoryTheory.EssentiallyConstantInd.exists_fullyFaithful_not_reflecting` packages this.
* `CategoryTheory.Functor.isRightDerivable_comp_and_not_isRightDerivable_of_map_eq_zero`: the
  criterion in the form of the implication Tag 09LK's proof needs — about right derivability
  itself, not about essential constancy of a diagram. For `W = ⊤` on `ℕ` the ind-object of
  Tag 05S9 at an object is the system read on the larger indices, so a conservative functor
  preserving zero morphisms which kills the one-step transition morphisms of an `ℕ`-indexed
  system no transition morphism of which vanishes makes `R(F ⋙ U)` everywhere defined and `RF`
  defined nowhere.
  `StacksFrontier/CategoryTheory/Functor/Derived/ValueReflectionCounterexample.lean`
  exhibits such a `U`, so the hypotheses are known to be consistent: conservativity, zero objects
  and split idempotents in the source do not reflect right derivability.

## Implementation notes

*Why full and faithful, and why idempotents.* Essential constancy of `M ⋙ G` at the cocone `t`,
the index `i` and the section `r` makes `e = c_i ∘ r` an idempotent endomorphism of `G(M_i)` whose
image is `t.pt`. Fullness produces `ε : M_i ⟶ M_i` with `G(ε) = e` and faithfulness makes `ε`
idempotent; splitting `ε` in `𝒞` gives an object `Y` with `G(Y) ≅ t.pt`, and then every
coprojection, the section and the cofinal factorisation are transported by taking preimages under
`G`, each identity being checked after applying `G` and concluded by faithfulness. Conservativity
is not used anywhere and would not do instead: see the counterexample below, where `G` is fully
faithful, hence conservative, and reflects nothing.

*What the counterexample shows, and what it does not.* It shows that no property of `G` alone — in
particular not the conservativity that is all the source's reason (compatibility of the forgetful
functor with cohomology) supplies — can reflect essential constancy: the hypothesis on `𝒞` is
indispensable, because the value of the system simply need not be an object of `𝒞`. Equivalently,
essential constancy is not invariant under enlarging the ambient category along a fully faithful
embedding, so it admits no characterisation that only mentions the image of the diagram. This is
why the route of looking for a reformulation of essential constancy that is a *property* rather
than a retraction datum, and transporting that, cannot work.

It does *not* by itself exhibit a failure for the forgetful functor `D(E, d) ⥤ D(Ab)` of
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedForgetful.lean`. For that functor the
hypothesis on the source category is the harmless one — such a derived category has countable
coproducts, hence is idempotent complete — and the hypothesis that fails is fullness. The
forgetful functor is not even faithful: for `E` the ordinary ring `ℤ[x]/(x²)` in degree `0` and
`M = E/(x) = ℤ`, the group `Ext¹_E(M, M)` is `ℤ`, while `Ext¹_ℤ(ℤ, ℤ) = 0`, so a nonzero morphism
`M ⟶ M[1]` of `D(E, d)` is carried to `0`. So the two results here bracket the gap in Tag 09LK's
proof from both sides: fullness suffices, and conservativity cannot be made to suffice.

*How that failure of faithfulness becomes a failure of reflection.* The criterion
`not_reflects_isEssentiallyConstantInd_of_map_eq_zero` turns an invisible morphism of infinite
order into a system that the forgetful functor does not reflect, so the gap is not an artefact of
the artificial source category of `collapsingSystem`, which has no zero object. With `E` and
`M = E/(x)` as above, let `P` be the two-periodic free resolution of `M`, `P⁻ᵏ = E` for `k ≥ 0`
with differential multiplication by `x`, and let `u : P ⟶ P[1]` be the homomorphism whose
degree-`j` component is `(-1)ʲ 𝟙`. Then `P` is a bounded-above complex of free `E`-modules,
hence K-projective, so a morphism out of it in `D(E, d)` vanishes exactly when it is
null-homotopic; an `E`-linear null-homotopy of `uᵏ` would be a family `aⱼ ∈ E` with
`± 𝟙 = ± x aⱼ + aⱼ₊₁ x`, which is impossible because `1 ∉ (x)`. So `uᵏ ≠ 0` for every `k`. Over
`ℤ` the obstruction disappears — `s(1) = 0`, `s(x) = ± 1` is a null-homotopy of the underlying map
of complexes of abelian groups, as it must be, the underlying complex of `P` being a projective
resolution of `ℤ` over `ℤ`, where `Extᵏ(ℤ, ℤ) = 0` for `k ≥ 1`. The `ℕ`-indexed system
`n ↦ P[n]` with transition morphisms `u[n]` therefore has an essentially constant image in
`D(Ab)`, with value the zero object, and is not essentially constant in `D(E, d)`. It is an
honest filtered system of differential graded modules, its colimit in those is the zero module,
and the coprojections are epimorphisms, which is why it also rules out building the
essential-constancy witness at the level of complexes and descending; see the implementation
notes of `StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomVariant.lean`. The Ext
computation it rests on is classical and is not formalised here, so what the file contains is the
criterion, not the instance.

*What is machine-checked about the forgetful functor, and what is not.* Three things are needed to
run the criterion at `DifferentialGradedModule.derivedForget`, and only two of them are available.
The source and the target have zero objects and zero morphisms (the derived category is a
localization at a class with a left calculus of fractions, hence preadditive, and the localization
of a category with a zero object has one). The invisible system of infinite order is the Ext
computation above, which is not formalised anywhere in this repository or in Mathlib. And
`(DifferentialGradedModule.derivedForget A).PreservesZeroMorphisms` — equivalently its
additivity — is not available either: the only property of that functor recorded in this
repository is `DifferentialGradedModule.derivedForget_reflectsIsomorphisms`. So the negative
statement *about that functor* is not available here; what is available is the criterion, and —
in `ValueReflectionCounterexample.lean` — a conservative functor between categories with zero
objects, idempotent complete at the source, for which the negative statement holds. The
properties of `derivedForget` that this repository does record are exactly the ones that
counterexample has, which is what rules out proving the implication from them.

*Why the detour through eventual constancy does not save the step either.* Conservativity does
reflect eventual constancy, so the step Tag 09LK needs would follow if essential constancy in
`D(Ab)` of the ind-objects that actually arise there forced eventual constancy of them. It does
not, and the failure is uniform:
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomEventualConstancy.lean` shows that for
the systems `(s : X ⟶ X') ↦ Hom(K, X')` the transition morphisms are exactly the images of the
quasi-isomorphisms under `X`, that `Hom(K, -)` inverts a quasi-isomorphism precisely when it kills
the acyclic third vertex of a distinguished triangle on it, and hence that unless `K` is
K-projective — in which case no derivation is needed at all — *no* such system, at *no* object and
from *no* index, is eventually constant, while at a zero object of `K(A)` the system is
essentially constant. So the gap between the two notions, which
`not_isEventuallyConstantFrom_of_not_isIso_map` measures, is maximal exactly where the step is
wanted.

## References

* [Stacks Project, Tag 05PU](https://stacks.math.columbia.edu/tag/05PU) for essential constancy,
  [Tag 05S9](https://stacks.math.columbia.edu/tag/05S9) for a value of a right derived functor and
  [Tag 09LK](https://stacks.math.columbia.edu/tag/09LK) for the statement whose proof needs the
  reflection.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.EssentiallyConstantInd

section Reflection

variable {J : Type u₁} [Category.{v₁} J] {C : Type u₂} [Category.{v₂} C]
  {C' : Type u₃} [Category.{v₃} C']

/-- **A full and faithful functor whose source splits idempotents reflects essential constancy.**
If the diagram `M ⋙ G` is essentially constant with respect to the cocone `t`, the index `i` and
the section `r`, and if `G` is full and faithful and idempotents split in `𝒞`, then `M` itself is
essentially constant, with a witness at the *same* index `i`.

The value is obtained by splitting, in `𝒞`, the preimage under `G` of the idempotent
`c_i ∘ r` of `G(M_i)` whose image is `t.pt`; the coprojections, the section and the cofinal
factorisation are then the `G`-preimages of the given ones, each identity being verified after
applying `G`. Nothing is assumed of the index category `J`, and conservativity of `G` is neither
used nor sufficient. -/
theorem exists_isEssentiallyConstantWith_of_comp [IsIdempotentComplete C] {M : J ⥤ C}
    (G : C ⥤ C') [G.Full] [G.Faithful] {t : Cocone (M ⋙ G)} {i : J}
    {r : t.pt ⟶ (M ⋙ G).obj i} (h : IsEssentiallyConstantWith (M ⋙ G) t i r) :
    ∃ (t' : Cocone M) (r' : t'.pt ⟶ M.obj i), IsEssentiallyConstantWith M t' i r' := by
  have hid : r ≫ t.ι.app i = 𝟙 t.pt := h.retraction
  have hid' : ∀ {Z : C'} (a : t.pt ⟶ Z), r ≫ t.ι.app i ≫ a = a := fun a => by
    simpa using (reassoc_of% hid) a
  -- the idempotent of `G (M i)` whose image is the value `t.pt`
  have hee : (t.ι.app i ≫ r) ≫ t.ι.app i ≫ r = t.ι.app i ≫ r := by
    rw [Category.assoc, hid']
  have hmap : G.map (G.preimage (t.ι.app i ≫ r)) = t.ι.app i ≫ r := G.map_preimage _
  have hidem : G.preimage (t.ι.app i ≫ r) ≫ G.preimage (t.ι.app i ≫ r)
      = G.preimage (t.ι.app i ≫ r) := by
    apply G.map_injective
    rw [G.map_comp, hmap, hee]
  obtain ⟨Y, incl, proj, hip, hpi⟩ :=
    IsIdempotentComplete.idempotents_split (M.obj i) (G.preimage (t.ι.app i ≫ r)) hidem
  -- the two mutually inverse comparisons between `t.pt` and `G Y`
  have hpi' : G.map proj ≫ G.map incl = t.ι.app i ≫ r := by rw [← G.map_comp, hpi, hmap]
  have hip' : G.map incl ≫ G.map proj = 𝟙 (G.obj Y) := by rw [← G.map_comp, hip, G.map_id]
  have hθθ' : r ≫ G.map proj ≫ G.map incl ≫ t.ι.app i = 𝟙 t.pt := by
    rw [← Category.assoc (G.map proj) (G.map incl) (t.ι.app i), hpi', Category.assoc, hid', hid]
  have hθ'θ : G.map incl ≫ t.ι.app i ≫ r ≫ G.map proj = 𝟙 (G.obj Y) := by
    rw [← Category.assoc (t.ι.app i) r (G.map proj), ← hpi', Category.assoc, hip',
      Category.comp_id, hip']
  have hθθ'' : ∀ {Z : C'} (a : t.pt ⟶ Z),
      r ≫ G.map proj ≫ G.map incl ≫ t.ι.app i ≫ a = a := fun a => by
    simpa using (reassoc_of% hθθ') a
  refine ⟨{ pt := Y
            ι := { app := fun j => G.preimage (t.ι.app j ≫ r ≫ G.map proj)
                   naturality := ?_ } },
          G.preimage (G.map incl ≫ t.ι.app i ≫ r), ?_, ?_⟩
  · intro j j' f
    apply G.map_injective
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, G.map_comp,
      G.map_preimage]
    rw [← Category.assoc]
    exact congrArg (· ≫ r ≫ G.map proj) (t.w f)
  · apply G.map_injective
    simp only [G.map_comp, G.map_preimage, G.map_id, Category.assoc, hid', hθ'θ]
  · intro j
    obtain ⟨k, σ, τ, hk⟩ := h.cofinal j
    refine ⟨k, σ, τ, ?_⟩
    apply G.map_injective
    rw [Functor.comp_map, Functor.comp_map] at hk
    simp only [G.map_comp, G.map_preimage, Category.assoc, hk, hθθ'']

/-- **A full and faithful functor whose source splits idempotents reflects essential constancy**,
for the predicate of Stacks 05PU(1) with the value quantified existentially: if `M ⋙ G` is an
essentially constant ind-object then so is `M`. -/
theorem isEssentiallyConstantInd_of_comp [IsIdempotentComplete C] {M : J ⥤ C} (G : C ⥤ C')
    [G.Full] [G.Faithful] (h : IsEssentiallyConstantInd (M ⋙ G)) :
    IsEssentiallyConstantInd M := by
  obtain ⟨t, i, r, hw⟩ := h
  obtain ⟨t', r', hw'⟩ := exists_isEssentiallyConstantWith_of_comp G hw
  exact ⟨t', i, r', hw'⟩

end Reflection

end CategoryTheory.EssentiallyConstantInd

namespace CategoryTheory.Functor

section EventuallyConstant

variable {J : Type u₁} [Category.{v₁} J] {C : Type u₂} [Category.{v₂} C]
  {C' : Type u₃} [Category.{v₃} C']

/-- **Eventual constancy is reflected by any conservative functor.** If all transition morphisms
of `M ⋙ G` out of `i₀` are isomorphisms and `G` reflects isomorphisms, then all transition
morphisms of `M` out of `i₀` are isomorphisms.

This is the one piece of the story for which conservativity is enough, and it is the reason the
distinction matters: Mathlib's `CategoryTheory.Functor.IsEventuallyConstantFrom` is strictly
stronger than essential constancy, and it is only the strictly stronger notion that a functor
compatible with cohomology can carry backwards. -/
theorem isEventuallyConstantFrom_of_comp {M : J ⥤ C} (G : C ⥤ C') [G.ReflectsIsomorphisms]
    {i₀ : J} (h : (M ⋙ G).IsEventuallyConstantFrom i₀) : M.IsEventuallyConstantFrom i₀ :=
  fun {_} f => by
    have : IsIso (G.map (M.map f)) := h f
    exact isIso_of_reflects_iso (M.map f) G

end EventuallyConstant

section EventuallyConstantIndObject

variable {D : Type u₁} [Category.{v₁} D] {D' : Type u₂} [Category.{v₂} D']

/-- **One transition morphism that `F` does not invert refutes eventual constancy of Deligne's
ind-object.** Let `g` be a morphism out of the target of the index `i₀` such that `i₀.hom ≫ g`
again lies in `W`, so that `g` is a transition morphism of the ind-object
`X/W ⟶ 𝒟'`, `(s : X ⟶ X') ↦ F(X')` out of `i₀`. If `F.map g` is not invertible, that ind-object
is not eventually constant from `i₀`.

Unlike essential constancy, eventual constancy from an index quantifies over *all* transition
morphisms out of it, so a single one suffices to refute it — and, by
`CategoryTheory.Functor.isEventuallyConstantFrom_of_comp`, it is the notion a conservative
functor transports. -/
theorem not_isEventuallyConstantFrom_of_not_isIso_map {F : D ⥤ D'} {W : MorphismProperty D}
    {X : D} (i₀ : W.Under ⊤ X) {Y : D} (g : i₀.right ⟶ Y) (hg : W (i₀.hom ≫ g))
    (hiso : ¬ IsIso (F.map g)) :
    ¬ (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F).IsEventuallyConstantFrom i₀ := by
  intro h
  exact hiso (h (MorphismProperty.Under.homMk (B := MorphismProperty.Under.mk ⊤ _ hg) g rfl))

end EventuallyConstantIndObject

section DerivedValue

open EssentiallyConstantInd

variable {D : Type u₁} [Category.{v₁} D] {D' : Type u₂} [Category.{v₂} D']
  {D'' : Type u₃} [Category.{v₃} D'']

/-- **A value of `R(F ⋙ G)` at `X` produces a value of `RF` at `X`**, for `G` full and faithful
with `𝒟'` idempotent complete. This is the converse of
`CategoryTheory.Functor.IsRightDerivedValueAt.comp`, which holds for an arbitrary `G`; the
cocone cannot be prescribed, since its vertex is manufactured by splitting an idempotent. -/
theorem exists_isRightDerivedValueAt_of_comp [IsIdempotentComplete D'] {F : D ⥤ D'}
    {W : MorphismProperty D} {X : D} (G : D' ⥤ D'') [G.Full] [G.Faithful]
    {c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ (F ⋙ G))}
    (h : (F ⋙ G).IsRightDerivedValueAt W X c) :
    ∃ c', F.IsRightDerivedValueAt W X c' := by
  obtain ⟨s₀, r, hw⟩ := ((F ⋙ G).isRightDerivedValueAt_iff W X c).1 h
  obtain ⟨c', r', hw'⟩ :=
    exists_isEssentiallyConstantWith_of_comp
      (M := MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F) G hw
  exact ⟨c', (F.isRightDerivedValueAt_iff W X c').2 ⟨s₀, r', hw'⟩⟩

/-- **Right derivability descends along a full and faithful functor** whose source splits
idempotents: if the right derived functor of `F ⋙ G` is everywhere defined, so is that of `F`.
This is the converse of `CochainComplex.isRightDerivable_homToDerivedCategoryForget`, and the
statement Tag 09LK's proof needs with `G` the forgetful functor `D(E, d) ⥤ D(Ab)` — which,
however, is neither full nor faithful. -/
theorem IsRightDerivable.of_comp [IsIdempotentComplete D'] {F : D ⥤ D'}
    {W : MorphismProperty D} (G : D' ⥤ D'') [G.Full] [G.Faithful]
    (h : (F ⋙ G).IsRightDerivable W) : F.IsRightDerivable W := fun X => by
  obtain ⟨c, hc⟩ := h X
  exact exists_isRightDerivedValueAt_of_comp G hc

end DerivedValue

end CategoryTheory.Functor

namespace CategoryTheory.EssentiallyConstantInd

/-!
### Zero values, and a criterion for non-reflection

A conservative functor reflects *zero* values, and that is enough to turn a failure of
faithfulness into a failure of reflection: a system whose transition morphisms are killed by `G`
has an essentially constant image with value a zero object, while the system itself cannot be
essentially constant unless its own transition morphisms vanish cofinally.
-/

section ZeroValue

open ZeroObject

variable {J : Type u₁} [Category.{v₁} J] {C : Type u₂} [Category.{v₂} C]
  {C' : Type u₃} [Category.{v₃} C']

/-- **A system whose transition morphisms vanish cofinally is essentially constant with value a
zero object.** The witness is the zero cocone, at an arbitrary index, with the zero section;
filteredness is used only to merge that index with the one supplied by the hypothesis. -/
theorem exists_isEssentiallyConstantWith_isZero [IsFiltered J] [HasZeroMorphisms C]
    [HasZeroObject C] (M : J ⥤ C) (h : ∀ j : J, ∃ (k : J) (τ : j ⟶ k), M.map τ = 0) :
    ∃ (t : Cocone M) (i : J) (r : t.pt ⟶ M.obj i),
      IsZero t.pt ∧ IsEssentiallyConstantWith M t i r := by
  obtain ⟨i⟩ : Nonempty J := IsFiltered.nonempty
  refine ⟨{ pt := 0, ι := { app := fun _ => 0, naturality := fun _ _ _ => by simp } }, i, 0,
    isZero_zero C, (isZero_zero C).eq_of_src _ _, fun j => ?_⟩
  obtain ⟨k, τ, hτ⟩ := h j
  refine ⟨IsFiltered.max k i, IsFiltered.rightToMax k i, τ ≫ IsFiltered.leftToMax k i, ?_⟩
  rw [M.map_comp, hτ, zero_comp]
  simp

/-- **A zero value forces the transition morphisms to vanish cofinally.** If `M` is essentially
constant with respect to a cocone whose vertex is a zero object, then every index admits an arrow
along which the transition morphism of `M` is zero: the cofinality clause factors that transition
morphism through the value. -/
theorem IsEssentiallyConstantWith.exists_map_eq_zero [HasZeroMorphisms C] {M : J ⥤ C}
    {t : Cocone M} {i : J} {r : t.pt ⟶ M.obj i} (h : IsEssentiallyConstantWith M t i r)
    (ht : IsZero t.pt) (j : J) : ∃ (k : J) (τ : j ⟶ k), M.map τ = 0 := by
  obtain ⟨k, σ, τ, hk⟩ := h.cofinal j
  exact ⟨k, τ, by rw [hk, ht.eq_of_tgt (t.ι.app j) 0, zero_comp]⟩

/-- **A conservative functor reflects zero objects**, as soon as it preserves zero morphisms: the
unique morphism `X ⟶ 0` is carried to a morphism between zero objects, hence to an isomorphism,
hence is one. A zero object in the source is needed, unlike for a *faithful* additive functor,
where the identity of the object is carried to zero and injectivity on morphisms finishes
(`AlgebraicGeometry.isZero_of_isZero_map`); the forgetful functor `D(E, d) ⥤ D(Ab)` is not
faithful, which is why this is the form used here. -/
theorem isZero_of_isZero_map [HasZeroObject C] [HasZeroMorphisms C] [HasZeroMorphisms C']
    (G : C ⥤ C') [G.PreservesZeroMorphisms] [G.ReflectsIsomorphisms] {X : C}
    (hX : IsZero (G.obj X)) : IsZero X := by
  have h0 : IsZero (G.obj (0 : C)) := by
    rw [IsZero.iff_id_eq_zero, ← G.map_id, (isZero_zero C).eq_of_src (𝟙 (0 : C)) 0, G.map_zero]
  have hiso : IsIso (G.map (0 : X ⟶ (0 : C))) := by
    rw [hX.eq_of_src (G.map (0 : X ⟶ (0 : C))) (hX.iso h0).hom]
    infer_instance
  have := isIso_of_reflects_iso (0 : X ⟶ (0 : C)) G
  exact IsZero.of_iso (isZero_zero C) (asIso (0 : X ⟶ (0 : C)))

/-- **A conservative functor cannot reflect essential constancy across a failure of
faithfulness.** If the image of `M` under a conservative `G` preserving zero morphisms is
essentially constant with value a zero object, and some index `j` of `M` admits *no* arrow along
which the transition morphism of `M` vanishes, then `M` is not essentially constant.

Any value of `M` would have zero image, hence be a zero object by conservativity, and then the
cofinality clause would make some transition morphism out of `j` vanish. -/
theorem not_isEssentiallyConstantInd_of_isZero_comp [HasZeroObject C] [HasZeroMorphisms C]
    [HasZeroMorphisms C'] {M : J ⥤ C} (G : C ⥤ C') [G.PreservesZeroMorphisms]
    [G.ReflectsIsomorphisms] {t : Cocone (M ⋙ G)} {i : J} {r : t.pt ⟶ (M ⋙ G).obj i}
    (h : IsEssentiallyConstantWith (M ⋙ G) t i r) (ht : IsZero t.pt) {j : J}
    (hj : ∀ (k : J) (τ : j ⟶ k), M.map τ ≠ 0) : ¬ IsEssentiallyConstantInd M := by
  rintro ⟨t', i', r', h'⟩
  have hz : IsZero t'.pt :=
    isZero_of_isZero_map G
      (ht.of_iso ((h'.map G).isColimit.coconePointUniqueUpToIso h.isColimit))
  obtain ⟨k, τ, hτ⟩ := h'.exists_map_eq_zero hz j
  exact hj k τ hτ

/-- **Essential constancy is not reflected by a conservative functor that kills a composable
family of nonzero morphisms.** Let `G` be conservative and preserve zero morphisms, let every
index of the filtered diagram `M` admit an arrow whose transition morphism `G` kills, and let
some index `j₀` admit no arrow along which the transition morphism of `M` itself vanishes. Then
`M ⋙ G` is essentially constant — with value a zero object — and `M` is not.

This is the criterion that reduces the reflection question for a *given* conservative functor to
an algebraic one: produce a cofinal family of morphisms that the functor kills and whose
composites never vanish. For the forgetful functor
`DifferentialGradedModule.derivedForget` of
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedForgetful.lean` such a family is a
self-extension of infinite order; see the implementation notes. -/
theorem not_reflects_isEssentiallyConstantInd_of_map_eq_zero [IsFiltered J] [HasZeroObject C]
    [HasZeroMorphisms C] [HasZeroObject C'] [HasZeroMorphisms C'] (M : J ⥤ C) (G : C ⥤ C')
    [G.PreservesZeroMorphisms] [G.ReflectsIsomorphisms]
    (hz : ∀ j : J, ∃ (k : J) (τ : j ⟶ k), G.map (M.map τ) = 0)
    {j₀ : J} (hne : ∀ (k : J) (τ : j₀ ⟶ k), M.map τ ≠ 0) :
    IsEssentiallyConstantInd (M ⋙ G) ∧ ¬ IsEssentiallyConstantInd M := by
  obtain ⟨t, i, r, ht, h⟩ := exists_isEssentiallyConstantWith_isZero (M ⋙ G) hz
  exact ⟨⟨t, i, r, h⟩, not_isEssentiallyConstantInd_of_isZero_comp G h ht hne⟩

end ZeroValue

/-!
### Conservativity, and even full faithfulness, does not reflect essential constancy
-/

/-- The property of being a nonzero abelian group, i.e. of having a nonzero identity morphism. -/
def NonzeroAb : ObjectProperty AddCommGrpCat.{0} := fun A => 𝟙 A ≠ 0

/-- The group of integers, as an object of the full subcategory of nonzero abelian groups. -/
def NonzeroAb.int : NonzeroAb.FullSubcategory :=
  ⟨AddCommGrpCat.of ℤ, by
    intro h
    have h1 : (𝟙 (AddCommGrpCat.of ℤ)) (1 : ℤ)
        = (0 : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ) 1 := by rw [h]
    simp at h1⟩

/-- The filtered system over `ℕ` which is constant at `ℤ`, viewed in the full subcategory of
nonzero abelian groups, and all of whose non-identity transition morphisms are zero.

Viewed in `Ab` this system is essentially constant with value the zero group
(`isEssentiallyConstantInd_collapsingSystem_comp_ι`); inside the subcategory it is not essentially
constant at all (`not_isEssentiallyConstantInd_collapsingSystem`), because the zero group has been
removed. -/
def collapsingSystem : ℕ ⥤ NonzeroAb.FullSubcategory where
  obj _ := NonzeroAb.int
  map {n m} _ := if n = m then 𝟙 _ else ObjectProperty.homMk 0
  map_id n := by simp
  map_comp {n m k} f g := by
    rcases eq_or_ne n m with hnm | hnm
    · subst hnm
      rcases eq_or_ne n k with hnk | hnk
      · simp [hnk]
      · simp [hnk]
    · have hnk : n ≠ k := fun h => hnm (le_antisymm (leOfHom f) (h ▸ leOfHom g))
      rcases eq_or_ne m k with hmk | hmk
      · subst hmk; simp [hnm]
      · apply ObjectProperty.hom_ext
        simp [hnm, hmk, hnk]

/-- Every non-identity transition morphism of `collapsingSystem` is zero. -/
theorem collapsingSystem_map_hom_of_ne {n m : ℕ} (f : n ⟶ m) (h : n ≠ m) :
    (collapsingSystem.map f).hom = 0 := by
  simp only [collapsingSystem, h, ite_false, ObjectProperty.homMk_hom]
  rfl

/-- **Essential constancy is not reflected by a fully faithful functor.** Inside the full
subcategory of nonzero abelian groups the system `collapsingSystem` is not essentially constant:
the cocone laws force every coprojection to be zero, so no section of a coprojection can be an
identity. -/
theorem not_isEssentiallyConstantInd_collapsingSystem :
    ¬ IsEssentiallyConstantInd collapsingSystem := by
  rintro ⟨t, i, r, hw⟩
  have hzero : ∀ n : ℕ, (t.ι.app n).hom = 0 := by
    intro n
    have hw' := congrArg InducedCategory.Hom.hom (t.w (homOfLE (Nat.le_succ n)))
    rw [ObjectProperty.FullSubcategory.comp_hom,
      collapsingSystem_map_hom_of_ne _ (Nat.ne_of_lt (Nat.lt_succ_self n))] at hw'
    rw [← hw', Limits.zero_comp]
  have hr := congrArg InducedCategory.Hom.hom hw.retraction
  rw [ObjectProperty.FullSubcategory.comp_hom, hzero i, Limits.comp_zero,
    ObjectProperty.FullSubcategory.id_hom] at hr
  exact t.pt.property hr.symm

/-- **The same system is essentially constant after the fully faithful inclusion into `Ab`**, with
value the zero group: every coprojection is zero, the identity of the zero group is zero, so the
zero morphism is a section of the coprojection at `0`, and the factorisation demanded of each
index is available because every non-identity transition morphism is zero. -/
theorem isEssentiallyConstantInd_collapsingSystem_comp_ι :
    IsEssentiallyConstantInd (collapsingSystem ⋙ NonzeroAb.ι) := by
  have hone : 𝟙 (AddCommGrpCat.of PUnit.{1}) = 0 := by ext
  refine ⟨{ pt := AddCommGrpCat.of PUnit.{1}
            ι := { app := fun _ => 0, naturality := ?_ } }, 0, 0, ?_, ?_⟩
  · intro j j' f
    simp
  · change (0 : AddCommGrpCat.of PUnit.{1} ⟶ _) ≫ 0 = 𝟙 _
    rw [Limits.comp_zero, hone]
  · intro j
    refine ⟨j + 1, homOfLE (Nat.zero_le _), homOfLE (Nat.le_succ j), ?_⟩
    change (collapsingSystem.map (homOfLE (Nat.le_succ j))).hom = _
    rw [collapsingSystem_map_hom_of_ne _ (Nat.ne_of_lt (Nat.lt_succ_self j))]
    simp

/-!
### From the criterion to right derivability itself

For `W = ⊤` on `ℕ` the ind-object `X/W ⟶ 𝒟'` of Tag 05S9 at the object `n` is the system read on
the indices `≥ n`, so a single `ℕ`-indexed system with the two properties of the criterion refutes
reflection of right derivability — the implication Tag 09LK's proof needs — at every object at
once. The statements are in `CategoryTheory.Functor`, after this section.
-/

/-- **Conservativity cannot reflect essential constancy.** There are a filtered index category, a
pair of categories, a fully faithful — hence conservative — functor between them and a diagram
which is not essentially constant but becomes so after the functor.

Consequently the hypothesis on the source category in
`CategoryTheory.EssentiallyConstantInd.exists_isEssentiallyConstantWith_of_comp` cannot be
dropped, and no reformulation of essential constancy that mentions only the image of the diagram
can exist. -/
theorem exists_fullyFaithful_not_reflecting :
    ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J)
      (C : Type 1) (_ : Category.{0} C) (C' : Type 1) (_ : Category.{0} C')
      (G : C ⥤ C') (_ : G.Full) (_ : G.Faithful) (M : J ⥤ C),
      IsEssentiallyConstantInd (M ⋙ G) ∧ ¬ IsEssentiallyConstantInd M :=
  ⟨ℕ, inferInstance, inferInstance, NonzeroAb.FullSubcategory, inferInstance,
    AddCommGrpCat.{0}, inferInstance, NonzeroAb.ι, inferInstance, inferInstance,
    collapsingSystem, isEssentiallyConstantInd_collapsingSystem_comp_ι,
    not_isEssentiallyConstantInd_collapsingSystem⟩

end CategoryTheory.EssentiallyConstantInd

namespace CategoryTheory.Functor

/-!
### Right derivability is not reflected by a conservative functor

An `ℕ`-indexed system in `𝒟'` none of whose transition morphisms vanishes, but whose one-step
transition morphisms are killed by `U`, is a counterexample to the implication

`(F ⋙ U).IsRightDerivable W ⟹ F.IsRightDerivable W`

at `W = ⊤` on `ℕ`: the ind-object of Tag 05S9 at the object `n` is the system read on the indices
`≥ n`, so the criterion
`CategoryTheory.EssentiallyConstantInd.not_reflects_isEssentiallyConstantInd_of_map_eq_zero`
applies at every object. This is the shape in which the step missing from the proof of
Tag 09LK fails for a conservative functor; whether it fails for
`DifferentialGradedModule.derivedForget` is the question of whether that functor admits such a
system, i.e. a self-extension of infinite order that it does not see.
-/

section NatIndObject

open Limits EssentiallyConstantInd
open scoped ZeroObject

variable {D' : Type u₁} [Category.{v₁} D'] {D'' : Type u₂} [Category.{v₂} D'']

/-- The ind-object `X/W ⟶ 𝒟'` of Tag 05S9 at the object `n` of `ℕ`, for `W = ⊤`: the system `F`
read on the indices `n ⟶ k`. -/
abbrev natTopIndObject (F : ℕ ⥤ D') (n : ℕ) : (⊤ : MorphismProperty ℕ).Under ⊤ n ⥤ D' :=
  MorphismProperty.Under.forget (⊤ : MorphismProperty ℕ) ⊤ n ⋙ Under.forget n ⋙ F

/-- The index `n ⟶ k` of the ind-object `CategoryTheory.Functor.natTopIndObject F n`. -/
def natTopUnder {n k : ℕ} (h : n ≤ k) : (⊤ : MorphismProperty ℕ).Under ⊤ n :=
  MorphismProperty.Under.mk ⊤ (homOfLE h) trivial

/-- A morphism of indices of `CategoryTheory.Functor.natTopIndObject F n`, out of an arbitrary
index. -/
def natTopUnderHom {n l : ℕ} (s : (⊤ : MorphismProperty ℕ).Under ⊤ n) (h : n ≤ l)
    (hsl : s.right ≤ l) : s ⟶ natTopUnder h :=
  MorphismProperty.Under.homMk (homOfLE hsl) (Subsingleton.elim _ _) trivial

/-- The morphism of `ℕ` underlying `natTopUnderHom s h hsl` is `homOfLE hsl`. -/
@[simp]
lemma natTopUnderHom_right {n l : ℕ} (s : (⊤ : MorphismProperty ℕ).Under ⊤ n) (h : n ≤ l)
    (hsl : s.right ≤ l) : (natTopUnderHom s h hsl).right = homOfLE hsl :=
  rfl

/-- **A functor killing the one-step transition morphisms of an `ℕ`-indexed system kills every
non-identity transition morphism of it**, the latter factoring through the former. -/
theorem comp_map_eq_zero_of_ne [HasZeroMorphisms D''] {F : ℕ ⥤ D'} {U : D' ⥤ D''}
    (hstep : ∀ n : ℕ, U.map (F.map (homOfLE n.le_succ)) = 0) {n m : ℕ} (f : n ⟶ m) (h : n ≠ m) :
    U.map (F.map f) = 0 := by
  have hlt : n + 1 ≤ m := Nat.succ_le_of_lt (lt_of_le_of_ne (leOfHom f) h)
  have hf : f = homOfLE n.le_succ ≫ homOfLE hlt := Subsingleton.elim _ _
  rw [hf, F.map_comp, U.map_comp, hstep, zero_comp]

/-- **The image under `U` of such a system is essentially constant with value a zero object, at
every object of `ℕ`.** The witness is the zero cocone with the zero section; the cofinality clause
holds at the index one step beyond the given one, where the transition morphism is killed. -/
theorem exists_isEssentiallyConstantWith_isZero_natTopIndObject [HasZeroObject D'']
    [HasZeroMorphisms D''] {F : ℕ ⥤ D'} {U : D' ⥤ D''}
    (hstep : ∀ n : ℕ, U.map (F.map (homOfLE n.le_succ)) = 0) (n : ℕ) :
    ∃ (t : Cocone (natTopIndObject (F ⋙ U) n)) (i : (⊤ : MorphismProperty ℕ).Under ⊤ n)
      (r : t.pt ⟶ (natTopIndObject (F ⋙ U) n).obj i),
      IsZero t.pt ∧ IsEssentiallyConstantWith (natTopIndObject (F ⋙ U) n) t i r := by
  refine ⟨{ pt := 0
            ι := { app := fun _ => 0, naturality := fun _ _ _ => by rw [comp_zero, zero_comp] } },
    natTopUnder (le_refl n), 0, isZero_zero D'', (isZero_zero D'').eq_of_src _ _, fun j => ?_⟩
  have hjn : n ≤ j.right := leOfHom j.hom
  have hj1 : n ≤ j.right + 1 := hjn.trans (Nat.le_succ _)
  refine ⟨natTopUnder hj1, natTopUnderHom _ hj1 hj1, natTopUnderHom j hj1 (Nat.le_succ _), ?_⟩
  have h0 : (natTopIndObject (F ⋙ U) n).map (natTopUnderHom j hj1 (Nat.le_succ _)) = 0 :=
    comp_map_eq_zero_of_ne hstep _ (Nat.ne_of_lt (Nat.lt_succ_self _))
  rw [h0]
  exact zero_comp.symm

/-- **Right derivability is not reflected by a conservative functor.** Let `U` be conservative and
preserve zero morphisms, between categories with zero objects, and let `F` be an `ℕ`-indexed system
in its source no transition morphism of which vanishes, while `U` kills the one-step transition
morphisms. Then, for `W = ⊤` on `ℕ`, the right derived functor of `F ⋙ U` is everywhere defined
and that of `F` is defined nowhere.

So the hypotheses `[G.Full] [G.Faithful]` of
`CategoryTheory.Functor.IsRightDerivable.of_comp` cannot be relaxed to conservativity, even with a
zero object and split idempotents available in the source: the counterexample of
`CategoryTheory.EssentiallyConstantInd.exists_fullyFaithful_not_reflecting` is not an artefact of
the source category it uses. What a given conservative functor has to be shown not to admit, if it
is to reflect right derivability, is a system of this kind. -/
theorem isRightDerivable_comp_and_not_isRightDerivable_of_map_eq_zero [HasZeroObject D']
    [HasZeroMorphisms D'] [HasZeroObject D''] [HasZeroMorphisms D''] (F : ℕ ⥤ D') (U : D' ⥤ D'')
    [U.PreservesZeroMorphisms] [U.ReflectsIsomorphisms]
    (hne : ∀ {n m : ℕ} (f : n ⟶ m), F.map f ≠ 0)
    (hstep : ∀ n : ℕ, U.map (F.map (homOfLE n.le_succ)) = 0) :
    (F ⋙ U).IsRightDerivable ⊤ ∧ ¬ F.IsRightDerivable (⊤ : MorphismProperty ℕ) := by
  refine ⟨fun n => ?_, fun h => ?_⟩
  · obtain ⟨t, i, r, -, hw⟩ := exists_isEssentiallyConstantWith_isZero_natTopIndObject hstep n
    exact ((F ⋙ U).exists_isRightDerivedValueAt_iff ⊤ n).2 ⟨t, i, r, hw⟩
  · obtain ⟨t, i, r, ht, hw⟩ := exists_isEssentiallyConstantWith_isZero_natTopIndObject hstep 0
    exact not_isEssentiallyConstantInd_of_isZero_comp (M := natTopIndObject F 0) U hw ht
      (j := natTopUnder (le_refl 0)) (fun _ τ => hne τ.right)
      ((F.exists_isRightDerivedValueAt_iff ⊤ 0).1 (h 0))

end NatIndObject

end CategoryTheory.Functor

end
