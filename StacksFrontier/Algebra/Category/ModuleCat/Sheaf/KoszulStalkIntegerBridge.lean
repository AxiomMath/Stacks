module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulStalk
public import StacksCore.Tactic.StacksAttribute

/-!
# The integer-indexed form of the stalk comparison for a Koszul complex

`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/KoszulStalk.lean` compares the complex of stalks
of a sheaf-level Koszul complex with the ring-level Koszul complex of the sequence of germs, as
an isomorphism of `ℕ`-indexed chain complexes of modules over the stalk. Several consumers of
that comparison instead meet it in `ℤ`-indexed form, and with the module structure forgotten:
the `ℕ`-indexed complex is extended by zero to `CochainComplex C ℤ` along
`ComplexShape.embeddingDownNat`, re-indexed to `ChainComplex C ℤ` along
`ComplexShape.embeddingDownIntUpInt`, and pushed to abelian groups along
`forget₂ (ModuleCat R) AddCommGrpCat`.

This file supplies that bridge. The transport of the isomorphism itself is *not* new
mathematics: the three steps are each an existing Mathlib functor, so the composite is a
functor and the isomorphism transports by `CategoryTheory.Functor.mapIso`. What is genuinely
missing from Mathlib, and is proved here, is the *exactness* half — Mathlib has
`HomologicalComplex.extend_exactAt_iff` for the extension step but no counterpart for the
restriction step, and no `ExactAt` transport along a single homology-preserving,
isomorphism-reflecting functor (only the `JointlyReflectIsomorphisms` family version). Since the
consumers use the comparison only to move exactness between the two indexings, that is the
content they need.

## Main definitions

* `Stacks.ChainComplexIntBridge.natToInt K` is the `ℤ`-indexed chain complex attached to an
  `ℕ`-indexed one by extending by zero and re-indexing, and
  `Stacks.ChainComplexIntBridge.natToIntFunctor` is it as a functor, namely the composite of
  Mathlib's `ComplexShape.Embedding.extendFunctor` and
  `ComplexShape.Embedding.restrictionFunctor`.
* `Stacks.ChainComplexIntBridge.natToIntXIso` identifies degree `(n : ℤ)` of `natToInt K` with
  degree `n` of `K`.
* `Stacks.ChainComplexIntBridge.natToIntAbFunctor R` is `natToIntFunctor` followed by
  `(forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.down ℤ)`, i.e. the whole
  bridge from `ChainComplex (ModuleCat R) ℕ` to `ChainComplex AddCommGrpCat ℤ`.
* `Stacks.RegularSequence.intStalkComplex` is the complex of stalks of a Koszul presentation in
  this `ℤ`-indexed form.

## Main results

* `Stacks.ChainComplexIntBridge.restriction_exactAt_iff`: exactness of `K.restriction e` in
  degree `j` is exactness of `K` in degree `e.f j`, given the matching of predecessors and
  successors. This is the restriction counterpart of Mathlib's
  `HomologicalComplex.extend_exactAt_iff`, built from `restrictionHomologyIso`.
* `Stacks.ChainComplexIntBridge.exactAt_mapHomologicalComplex_iff`: a functor which preserves
  homology and reflects isomorphisms neither creates nor destroys exactness.
* `Stacks.ChainComplexIntBridge.natToInt_exactAt_iff` and
  `Stacks.ChainComplexIntBridge.natToIntAb_exactAt_iff`: the `ℕ`-indexed complex is exact in
  degree `n` if and only if the bridged `ℤ`-indexed complex is exact in degree `(n : ℤ)`. In
  negative degrees the bridged complex is zero, hence exact
  (`Stacks.ChainComplexIntBridge.isZero_natToInt_X`,
  `Stacks.ChainComplexIntBridge.natToInt_exactAt_of_neg`).
* `Stacks.RegularSequence.seqComplexIsoIntStalkComplex`: the `ℤ`-indexed, abelian-group-valued
  form of `Stacks.RegularSequence.seqComplexIsoStalkComplex`.
* `Stacks.RegularSequence.exactAt_intStalkComplex_iff`: the `ℤ`-indexed complex of stalks is
  exact in degree `(n : ℤ)` if and only if the ring-level Koszul complex of the germ sequence is
  exact in degree `n`. Applying this in every positive degree tests acyclicity of the Koszul
  complex at `x`, and in degree one tests `H₁`-regularity of the germ sequence.

## Implementation notes

**Universes.** The `ℕ`-to-`ℤ` material in `Stacks.ChainComplexIntBridge` is universe
polymorphic in the ambient category. The `ModuleCat`/`AddCommGrpCat` composite
`natToIntAbFunctor` is stated for `R : Type u` with values in `ModuleCat.{u} R` and
`AddCommGrpCat.{u}`: a single universe, because `forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}`
is only defined when the module and the group live in the same universe. The Koszul
application inherits `RingedSpace.{u}` from `KoszulStalk.lean`, where it is *forced*, not
chosen — `TopCat.Presheaf.stalk` of a `CommRingCat.{u}`-valued presheaf requires the carrier to
be a `TopCat.{u}`, so a stalk statement about `RingedSpace.{u₁, u₂}` typechecks only for
`u₁ = u₂`. Nothing here narrows a universe that `KoszulStalk.lean` left open.

**Degrees are variables.** Every statement below keeps the degree a variable, both on the `ℕ`
side and on the `ℤ` side, and `natToInt_exactAt_iff'` is stated for an arbitrary integer degree
before being specialized to `(n : ℤ)`. Instantiating a degree to a numeral is left to the point
of use; doing it inside a statement forces `whnf` through the complex-shape embeddings and the
exterior-power quotients, which is expensive.

**Why `natToInt` and not just the functor.** The consumers meet the complex spelled
`(L.extend ComplexShape.embeddingDownNat).restriction ComplexShape.embeddingDownIntUpInt`, not
as `(natToIntFunctor C).obj L`. The two are definitionally equal but not syntactically so, and
`rw`/`simp` do not cross a functor-composition boundary of this shape. Hence both spellings are
provided, with `natToIntFunctor_obj` and `natToIntAbFunctor_obj` as `rfl`-lemmas relating them.

**Choice of the exactness predicate.** `HomologicalComplex.ExactAt` is used throughout rather
than `ShortComplex.Exact` of a hand-built short complex. `ExactAt i` unfolds to
`(K.sc i).Exact`, so nothing is lost, and it is the predicate Mathlib's
`extend_exactAt_iff`, `restrictionHomologyIso` and `JointlyReflectIsomorphisms.exactAt_iff`
speak about, so no short complex has to be exhibited by hand.

**No `@[stacks]` attribute.** The Stacks results in question (062K, 062L, 063C) are not covered
by this file: it carries no sheaf-theoretic content of its own, only the re-indexing of a
comparison proved in `KoszulStalk.lean`, which itself carries no tag. Tagging anything here
would place a tag on strictly less than a covering set.

## References

* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 062L](https://stacks.math.columbia.edu/tag/062L)
* [Stacks Project, Tag 063C](https://stacks.math.columbia.edu/tag/063C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.ChainComplexIntBridge

section General

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category C] [HasZeroMorphisms C]

/-- Exactness is invariant under isomorphism of complexes. The one-directional form is
Mathlib's `HomologicalComplex.ExactAt.of_iso`. -/
lemma exactAt_iff_of_iso {K L : HomologicalComplex C c} (e : K ≅ L) (i : ι) :
    K.ExactAt i ↔ L.ExactAt i :=
  ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

/-- **Exactness of a restriction.** The restriction of `K` along an embedding `e` of complex
shapes is exact in degree `j` exactly when `K` is exact in degree `e.f j`, provided the
predecessor and successor of `j` are carried by `e.f` to those of `e.f j`. This is the
counterpart for `HomologicalComplex.restriction` of Mathlib's
`HomologicalComplex.extend_exactAt_iff`. -/
lemma restriction_exactAt_iff (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff]
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    {i' j' k' : ι'} (hi' : e.f i = i') (hj' : e.f j = j') (hk' : e.f k = k')
    (hi'' : c'.prev j' = i') (hk'' : c'.next j' = k')
    [K.HasHomology j'] [(K.restriction e).HasHomology j] :
    (K.restriction e).ExactAt j ↔ K.ExactAt j' := by
  simp only [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').isZero_iff

end General

section Map

variable {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  [HasZeroObject C] [CategoryWithHomology C]

/-- **Exactness is detected by a single exact, conservative functor.** If `F` preserves homology
and reflects isomorphisms, then a complex in the source is exact in a degree exactly when its
image is. Mathlib proves the version for a family of functors which jointly reflect
isomorphisms; this is the one-functor case. -/
lemma exactAt_mapHomologicalComplex_iff (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [F.ReflectsIsomorphisms] [F.PreservesHomology]
    {α : Type*} {c : ComplexShape α} (K : HomologicalComplex C c) (a : α) :
    ((F.mapHomologicalComplex c).obj K).ExactAt a ↔ K.ExactAt a := by
  have h : JointlyReflectIsomorphisms (fun _ : Unit => F) :=
    { isIso := fun {_ _} g hg => by
        have := hg ()
        exact isIso_of_reflects_iso g F }
  rw [h.exactAt_iff K a]
  exact ⟨fun hK _ => hK, fun hK => hK ()⟩

end Map

section NatToInt

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

/-- **The integer-indexed form of an `ℕ`-indexed chain complex.** Extend by zero to a cochain
complex indexed by `ℤ` along `ComplexShape.embeddingDownNat`, then restore homological indexing
along `ComplexShape.embeddingDownIntUpInt`. Degree `(n : ℤ)` is degree `n`, and negative
degrees are zero. -/
@[sga "7 VII 3.1"]
noncomputable def natToInt (K : ChainComplex C ℕ) : ChainComplex C ℤ :=
  (K.extend ComplexShape.embeddingDownNat).restriction ComplexShape.embeddingDownIntUpInt

/-- `natToInt` as a functor: the composite of Mathlib's extension and restriction functors. -/
noncomputable def natToIntFunctor (C : Type*) [Category C] [HasZeroMorphisms C]
    [HasZeroObject C] : ChainComplex C ℕ ⥤ ChainComplex C ℤ :=
  ComplexShape.embeddingDownNat.extendFunctor C ⋙
    ComplexShape.embeddingDownIntUpInt.restrictionFunctor C

/-- The functor `natToIntFunctor C` sends a complex `K` to `natToInt K`. -/
lemma natToIntFunctor_obj (K : ChainComplex C ℕ) :
    (natToIntFunctor C).obj K = natToInt K := rfl

/-- Degree `(n : ℤ)` of the integer-indexed complex is degree `n` of the original. -/
noncomputable def natToIntXIso (K : ChainComplex C ℕ) (n : ℕ) :
    (natToInt K).X (n : ℤ) ≅ K.X n :=
  (K.extend ComplexShape.embeddingDownNat).restrictionXIso
      ComplexShape.embeddingDownIntUpInt (i := (n : ℤ)) rfl ≪≫
    K.extendXIso ComplexShape.embeddingDownNat rfl

/-- No natural number is carried by `embeddingDownNat` to `-n` for negative `n`. -/
private lemma embeddingDownNat_f_ne_neg (n : ℤ) (hn : n < 0) :
    ∀ m : ℕ, ComplexShape.embeddingDownNat.f m ≠ -n := fun m hm => by
  simp only [ComplexShape.embeddingDownNat_f] at hm
  omega

/-- The integer-indexed complex vanishes in negative degrees. -/
lemma isZero_natToInt_X (K : ChainComplex C ℕ) (n : ℤ) (hn : n < 0) :
    IsZero ((natToInt K).X n) :=
  ((K.extend ComplexShape.embeddingDownNat).restrictionXIso
      ComplexShape.embeddingDownIntUpInt (i := n) rfl).isZero_iff.2
    (K.isZero_extend_X ComplexShape.embeddingDownNat (-n) (embeddingDownNat_f_ne_neg n hn))

variable [CategoryWithHomology C]

/-- Exactness of the integer-indexed complex in an arbitrary integer degree, in terms of the
zero-extension. The degree is kept a variable here and specialized afterwards. -/
lemma natToInt_exactAt_iff' (K : ChainComplex C ℕ) (n : ℤ) :
    (natToInt K).ExactAt n ↔ (K.extend ComplexShape.embeddingDownNat).ExactAt (-n) :=
  restriction_exactAt_iff _ _ (n + 1) n (n - 1) (by simp) (by simp)
    (i' := -n - 1) (j' := -n) (k' := -n + 1) (by simp; ring) (by simp) (by simp; ring)
    (by simp) (by simp)

/-- **Exactness transports between the two indexings.** The `ℕ`-indexed complex is exact in
degree `n` exactly when its integer-indexed form is exact in degree `(n : ℤ)`. -/
lemma natToInt_exactAt_iff (K : ChainComplex C ℕ) (n : ℕ) :
    (natToInt K).ExactAt (n : ℤ) ↔ K.ExactAt n := by
  rw [natToInt_exactAt_iff',
    K.extend_exactAt_iff ComplexShape.embeddingDownNat (j := n) (j' := -(n : ℤ)) rfl]

/-- In negative degrees the integer-indexed complex is zero, hence exact. -/
lemma natToInt_exactAt_of_neg (K : ChainComplex C ℕ) (n : ℤ) (hn : n < 0) :
    (natToInt K).ExactAt n := by
  rw [natToInt_exactAt_iff']
  exact K.extend_exactAt ComplexShape.embeddingDownNat (-n) (embeddingDownNat_f_ne_neg n hn)

end NatToInt

section ModuleToAb

variable (R : Type u) [Ring R]

/-- **The whole bridge.** An `ℕ`-indexed chain complex of `R`-modules becomes a `ℤ`-indexed
chain complex of abelian groups: extend by zero, restore homological indexing, forget the
module structure. This is a composite of Mathlib functors, so it transports isomorphisms by
`CategoryTheory.Functor.mapIso`. -/
noncomputable def natToIntAbFunctor :
    ChainComplex (ModuleCat.{u} R) ℕ ⥤ ChainComplex AddCommGrpCat.{u} ℤ :=
  natToIntFunctor (ModuleCat.{u} R) ⋙
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.down ℤ)

/-- The bridge, written in the spelling the consumers use. -/
lemma natToIntAbFunctor_obj (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    (natToIntAbFunctor R).obj K =
      ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex
          (ComplexShape.down ℤ)).obj
        ((K.extend ComplexShape.embeddingDownNat).restriction
          ComplexShape.embeddingDownIntUpInt) := rfl

variable {R}

/-- Degree `(n : ℤ)` of the bridged complex is the underlying group of degree `n`. -/
noncomputable def natToIntAbXIso (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    ((natToIntAbFunctor R).obj K).X (n : ℤ) ≅
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj (K.X n) :=
  (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapIso (natToIntXIso K n)

/-- The bridged complex vanishes in negative degrees. -/
lemma isZero_natToIntAb_X (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℤ) (hn : n < 0) :
    IsZero (((natToIntAbFunctor R).obj K).X n) :=
  Functor.map_isZero (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (isZero_natToInt_X K n hn)

/-- **Exactness transports across the whole bridge.** Forgetting the module structure neither
creates nor destroys exactness, since `forget₂ (ModuleCat R) AddCommGrpCat` is exact and
reflects isomorphisms. -/
lemma natToIntAb_exactAt_iff (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    ((natToIntAbFunctor R).obj K).ExactAt (n : ℤ) ↔ K.ExactAt n :=
  (exactAt_mapHomologicalComplex_iff _ (natToInt K) (n : ℤ)).trans
    (natToInt_exactAt_iff K n)

/-- In negative degrees the bridged complex is exact. -/
lemma natToIntAb_exactAt_of_neg (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℤ) (hn : n < 0) :
    ((natToIntAbFunctor R).obj K).ExactAt n :=
  (exactAt_mapHomologicalComplex_iff _ (natToInt K) n).2 (natToInt_exactAt_of_neg K n hn)

end ModuleToAb

end Stacks.ChainComplexIntBridge

namespace Stacks.RegularSequence

open scoped ExteriorAlgebra

variable (X : RingedSpace.{u}) {r : ℕ} (f : Fin r → X.presheaf.obj (op (⊤ : Opens X)))
  (E : ℕ → PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat))
  (ξ : ∀ (n : ℕ) (U : Opens X), (E n).obj (op U) ≃ₗ[X.presheaf.obj (op U)]
    (⋀[X.presheaf.obj (op U)]^n (Fin r → X.presheaf.obj (op U))))
  (b : ∀ n : ℕ, (Fin n → Fin r) → (E n).obj (op (⊤ : Opens X)))
  (hξ : ∀ (n : ℕ) (U : Opens X) (i : Fin n → Fin r),
    ξ n U (wedgeSection X E b n i U) =
      exteriorPower.ιMulti (X.presheaf.obj (op U)) n
        (fun j => Pi.single (i j) (1 : X.presheaf.obj (op U))))
  (D : ∀ n : ℕ, E (n + 1) ⟶ E n)
  (hD : ∀ (n : ℕ) (U : Opens X) (s : (E (n + 1)).obj (op U)),
    ξ n U ((D n).app (op U) s) =
      Koszul.d (Koszul.seqDual (resSequence X f U)) n (ξ (n + 1) U s))

/-- **The integer-indexed complex of stalks.** The complex `stalkComplex` of
`KoszulStalk.lean`, extended by zero to negative degrees, re-indexed over `ℤ`, and with the
`O_{X,x}`-module structure forgotten. This is the form in which the comparison is met by
consumers phrased over `AddCommGrpCat` and `ChainComplex _ ℤ`. -/
noncomputable def intStalkComplex (x : X) : ChainComplex AddCommGrpCat.{u} ℤ :=
  (ChainComplexIntBridge.natToIntAbFunctor (X.presheaf.stalk x)).obj
    (stalkComplex X f E ξ b hξ D hD x)

/-- The integer-indexed complex of stalks, written in the spelling the consumers use. -/
lemma intStalkComplex_eq (x : X) :
    intStalkComplex X f E ξ b hξ D hD x =
      ((forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}).mapHomologicalComplex
          (ComplexShape.down ℤ)).obj
        (((stalkComplex X f E ξ b hξ D hD x).extend ComplexShape.embeddingDownNat).restriction
          ComplexShape.embeddingDownIntUpInt) := rfl

/-- Degree `(n : ℤ)` of the integer-indexed complex of stalks is the stalk of `E n`. -/
noncomputable def intStalkComplexXIso (x : X) (n : ℕ) :
    (intStalkComplex X f E ξ b hξ D hD x).X (n : ℤ) ≅
      AddCommGrpCat.of ((abVal X (E n)).stalk x) :=
  ChainComplexIntBridge.natToIntAbXIso (stalkComplex X f E ξ b hξ D hD x) n

/-- The integer-indexed complex of stalks vanishes in negative degrees. -/
lemma isZero_intStalkComplex_X (x : X) (n : ℤ) (hn : n < 0) :
    IsZero ((intStalkComplex X f E ξ b hξ D hD x).X n) :=
  ChainComplexIntBridge.isZero_natToIntAb_X (stalkComplex X f E ξ b hξ D hD x) n hn

/-- **The integer-indexed stalk comparison.** The `ℤ`-indexed, abelian-group-valued form of
`seqComplexIsoStalkComplex`: the bridged ring-level Koszul complex of the sequence of germs is
isomorphic to the bridged complex of stalks. It is obtained by transporting the `ℕ`-indexed
comparison along the bridge functor, so it is the same isomorphism, degreewise `toStalk`. -/
noncomputable def seqComplexIsoIntStalkComplex (x : X) :
    (ChainComplexIntBridge.natToIntAbFunctor (X.presheaf.stalk x)).obj
        (Koszul.seqComplex (germSequence X f x)) ≅
      intStalkComplex X f E ξ b hξ D hD x :=
  (ChainComplexIntBridge.natToIntAbFunctor (X.presheaf.stalk x)).mapIso
    (seqComplexIsoStalkComplex X f E ξ b hξ D hD x)

/-- **Exactness transport, the form the consumers need.** The integer-indexed complex of stalks
is exact in degree `(n : ℤ)` exactly when the ring-level Koszul complex of the sequence of germs
at `x` is exact in degree `n`. Applying this in every positive degree tests acyclicity of the
Koszul complex at `x`; applying it in degree one tests `H₁`-regularity of the germ sequence. -/
theorem exactAt_intStalkComplex_iff (x : X) (n : ℕ) :
    (intStalkComplex X f E ξ b hξ D hD x).ExactAt (n : ℤ) ↔
      (Koszul.seqComplex (germSequence X f x)).ExactAt n :=
  (ChainComplexIntBridge.natToIntAb_exactAt_iff (stalkComplex X f E ξ b hξ D hD x) n).trans
    (ChainComplexIntBridge.exactAt_iff_of_iso
      (seqComplexIsoStalkComplex X f E ξ b hξ D hD x) n).symm

/-- In negative degrees the integer-indexed complex of stalks is exact. -/
theorem exactAt_intStalkComplex_of_neg (x : X) (n : ℤ) (hn : n < 0) :
    (intStalkComplex X f E ξ b hξ D hD x).ExactAt n :=
  ChainComplexIntBridge.natToIntAb_exactAt_of_neg
    (stalkComplex X f E ξ b hξ D hD x) n hn

end Stacks.RegularSequence
