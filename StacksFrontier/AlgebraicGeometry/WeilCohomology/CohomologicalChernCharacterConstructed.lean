module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroupPullback
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.ChernCharacterExistence
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.RankReduction
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.CohomologicalChernCharacter
import all StacksFrontier.AlgebraicGeometry.WeilCohomology.CohomologicalChernCharacter

/-!
# The cohomological Chern character on `K₀(Vect(X))`, with the pullback constructed

This file proves Tag 0FIE in the form the source states it. The rule `ch^H` on `K₀(Vect(X))` of
`StacksFrontier.AlgebraicGeometry.WeilCohomology.CohomologicalChernCharacter` is built there from a
pullback homomorphism `κ` of `K₀(Vect(-))` carried as a hypothesis, and its uniqueness is proved
there on the class of a module of constant rank. Here `κ` is the constructed
`AlgebraicGeometry.VectorBundleKZero.pullbackRingHom`, the rank is arbitrary, and the cohomological
Chern character of a single module is Tag 0FI9's `Stacks.WeilCohomology.chernCharacterOfModule`.

## Main results

* `Stacks.WeilCohomology.exists_cohomologicalChernCharacter'`: **the existence half of Tag
  0FIE.** The cohomological Chern character of a single finite locally free module extends to a
  ring homomorphism on `K₀(Vect(X))` which is graded, compatible with pullbacks, and takes the
  value `exp(c_1^H(ℒ))` on an invertible module.
* `Stacks.WeilCohomology.eq_of_cohomologicalChernCharacter'`: **the uniqueness half of Tag
  0FIE.** Two rules compatible with pullbacks and with that value on invertible modules agree —
  on every class of `K₀(Vect(X))` and every object `X` of `𝒞`.
* `Stacks.WeilCohomology.ChernSituation.exists_cohomologicalChernCharacter`: **the existence
  half in the standing situation of Section 45.12**, where the Chern character of a single
  module is no longer a hypothesis but Tag 0FI9's
  `Stacks.WeilCohomology.chernCharacterOfModule`, and the `𝐐`-structure of `A` is read off data
  (D0) and (D1) rather than carried as a field.
* `Stacks.WeilCohomology.RationalChernSituation.exists_cohomologicalChernCharacter`: the same
  over `Stacks.WeilCohomology.RationalChernSituation`, which has that condition as a field.
* `Stacks.WeilCohomology.exists_cohomologicalChernCharacter_of_source`: **the existence half
  over the source's own data and conditions**, with no structure argument. It takes the
  `Stacks.WeilCohomology.ChernSetup`, the three remaining conditions of Section 45.12 in the
  source's own form and the `𝐐`-structure of (D0) and (D1), and builds the standing situation
  inside the proof by `Stacks.WeilCohomology.chernSituationOfSource`.
* `Stacks.WeilCohomology.ChernSetup.algebraMap_mem_grade_zero_of_isRationallyGraded` and
  `Stacks.WeilCohomology.ChernSetup.isRationallyGraded_of_algebraMap_mem_grade_zero`: the field
  `Stacks.WeilCohomology.RationalChernSituation.algebraMap_mem_grade_zero` **is** data (D0) and
  (D1) read for `A`, the two being equivalent over a `ChernSetup`.

## Implementation notes

Uniqueness is proved in three steps, following the source. Both rules being additive, they agree
as soon as they agree on the classes `[ℰ]`, which is
`AlgebraicGeometry.VectorBundleKZero.addHom_ext`. For `ℰ` of constant rank the splitting
principle of Tag 0FI7 supplies `p : P ⟶ X` with `p^*` injective on `A` and a filtration of
`p^*ℰ` with invertible successive quotients, which pins the value down. An arbitrary `ℰ` is
reduced to the constant-rank case by
`Stacks.WeilCohomology.SourceChernSetup.exists_clopenRankPieces`,
the transcription of clauses (1) and (2) and of condition (2): restriction to the rank loci is
injective on `A(X)` and `ℰ` has constant rank on each of them.

The pullback homomorphism of `K₀(Vect(-))` is
`AlgebraicGeometry.VectorBundleKZero.pullbackRingHom`, constructed from four properties of the
pullback of sheaves of modules: it preserves finite local freeness
(`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme`), it keeps a short exact
sequence of finite locally free modules short exact
(`AlgebraicGeometry.Scheme.Modules.shortExact_map_pullback_of_isFlat`, which is Tag 0G6R at the
scheme spelling), it carries a tensor product to the tensor product of the pullbacks (Tag 01CD) and
it carries `𝒪_Y` to `𝒪_X`.

## References

* [Stacks Project, Tag 0FIE](https://stacks.math.columbia.edu/tag/0FIE)
* [Stacks Project, Tag 0FI7](https://stacks.math.columbia.edu/tag/0FI7)
* [Stacks Project, Tag 0FI9](https://stacks.math.columbia.edu/tag/0FI9)
* [Stacks Project, Tag 0G6R](https://stacks.math.columbia.edu/tag/0G6R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v v₁ w

namespace Stacks.WeilCohomology

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

section

variable (𝔄 : SourceChernSetup.{u, v, v₁, w} C S) [∀ X : C, Algebra ℚ (𝔄.A X)]

/-- The degree-`n` part of the pullback of a cohomological Chern character along the morphism the
splitting principle produces, computed from the filtration: the class of `p^*ℰ` is the sum of the
classes of the invertible successive quotients, so the character of `p^*ℰ` is the sum of their
exponentials. -/
private theorem pull_coeff_eq_sum'
    {ch : ∀ X : C, VectorBundleKZero (S.obj X) →+* PowerSeries (𝔄.A X)}
    (hpull : ∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
      PowerSeries.map (𝔄.pull f) (ch Y α) = ch X (VectorBundleKZero.pullbackRingHom (S.map f) α))
    (hinv : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      ch X (VectorBundleKZero.classOf (S.obj X) L) =
        expFirstChernClass 𝔄.toChernSetup X (picardClassOf (S.obj X) L hL))
    {X P : C} (p : P ⟶ X) {E : (S.obj X).Modules}
    (hE : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E) {k : ℕ}
    (L : Fin k → (S.obj P).Modules)
    (hL : ∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj P).presheaf
      (S.obj P).ringCatSheaf.2 (L j))
    (hsum : VectorBundleKZero.classOf (S.obj P)
        ((Scheme.Modules.pullback (S.map p)).obj E) =
      ∑ j, VectorBundleKZero.classOf (S.obj P) (L j)) (n : ℕ) :
    𝔄.pull p (PowerSeries.coeff n (ch X (VectorBundleKZero.classOf (S.obj X) E))) =
      ∑ j, algebraMap ℚ (𝔄.A P) ((n.factorial : ℚ)⁻¹) *
        𝔄.c₁ P (picardClassOf (S.obj P) (L j) (hL j)) ^ n := by
  calc 𝔄.pull p (PowerSeries.coeff n (ch X (VectorBundleKZero.classOf (S.obj X) E)))
      = PowerSeries.coeff n
          (PowerSeries.map (𝔄.pull p) (ch X (VectorBundleKZero.classOf (S.obj X) E))) := by
        simp
    _ = ∑ j, PowerSeries.coeff n (ch P (VectorBundleKZero.classOf (S.obj P) (L j))) := by
        rw [hpull p _, VectorBundleKZero.pullbackRingHom_classOf (S.map p) E hE, hsum, map_sum]
        simp
    _ = ∑ j, algebraMap ℚ (𝔄.A P) ((n.factorial : ℚ)⁻¹) *
          𝔄.c₁ P (picardClassOf (S.obj P) (L j) (hL j)) ^ n :=
        Finset.sum_congr rfl fun j _ => by rw [hinv P (L j) (hL j), coeff_expFirstChernClass]

/-- The uniqueness of Tag 0FIE on the class of a module of **constant** rank, which is the case
the splitting principle reaches directly.

The splitting principle of Tag 0FI7 supplies `p : P ⟶ X` with `p^*` injective on `A` and a
filtration of `p^*ℰ` with invertible successive quotients. That filtration writes `[p^*ℰ]` as a
sum of classes of invertible modules in `K₀(Vect(P))`, where additivity and the prescribed value
determine the character; compatibility with pullbacks identifies the result with
`p^*ch^H([ℰ])`, and `p^*` is injective. -/
private theorem eq_classOf_of_isFiniteLocallyFreeOfRank
    {ch ch' : ∀ X : C, VectorBundleKZero (S.obj X) →+* PowerSeries (𝔄.A X)}
    (hpull : ∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
      PowerSeries.map (𝔄.pull f) (ch Y α) = ch X (VectorBundleKZero.pullbackRingHom (S.map f) α))
    (hpull' : ∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
      PowerSeries.map (𝔄.pull f) (ch' Y α) = ch' X (VectorBundleKZero.pullbackRingHom (S.map f) α))
    (hinv : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      ch X (VectorBundleKZero.classOf (S.obj X) L) =
        expFirstChernClass 𝔄.toChernSetup X (picardClassOf (S.obj X) L hL))
    (hinv' : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      ch' X (VectorBundleKZero.classOf (S.obj X) L) =
        expFirstChernClass 𝔄.toChernSetup X (picardClassOf (S.obj X) L hL))
    (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) :
    ch X (VectorBundleKZero.classOf (S.obj X) E) =
      ch' X (VectorBundleKZero.classOf (S.obj X) E) := by
  classical
  obtain ⟨P, p, -, hinj, hfil⟩ :=
    𝔄.exists_injective_hasInvertibleFiltration X Unit (fun _ => E) (fun _ => r) fun _ => hE
  obtain ⟨-, L, hL, hsum⟩ := (hfil ()).exists_classOf_eq_sum
  have hEflf : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E :=
    (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mpr
      hE.isFiniteLocallyFree
  refine PowerSeries.ext fun n => hinj ?_
  rw [pull_coeff_eq_sum' 𝔄 hpull hinv p hEflf L hL hsum n,
    pull_coeff_eq_sum' 𝔄 hpull' hinv' p hEflf L hL hsum n]

/-- **The uniqueness half of Stacks Tag 0FIE.** Two rules assigning to every object `X` of `𝒞` a
ring homomorphism `K₀(Vect(X)) ⟶ ∏_{i ≥ 0} H^{2i}(X)(i)`, compatible with pullbacks and taking
the value `exp(c_1^H(ℒ))` on every invertible module, are equal: they agree on every class of
`K₀(Vect(X))`, for every object `X` of `𝒞`.

Both rules are additive, so it is enough that they agree on the classes `[ℰ]` of finite locally
free modules, which generate `K₀(Vect(X))`. For `ℰ` of constant rank that is
`eq_classOf_of_isFiniteLocallyFreeOfRank`, read off the splitting principle. An arbitrary `ℰ` is
reduced to that case by `Stacks.WeilCohomology.SourceChernSetup.exists_clopenRankPieces`:
restriction
to the finitely many loci where the rank of `ℰ` is constant is injective on `A(X)` by condition
(2) of the situation, and both rules commute with those restrictions. -/
@[stacks 0FIE "uniqueness: two rules assigning to every object a ring homomorphism out of \
  `K₀(Vect(X))`, compatible with pullbacks and taking the value `exp(c₁^H(ℒ))` on an invertible \
  module, agree on every class and at every object. Every input is discharged here: \
  compatibility with pullbacks is read against the CONSTRUCTED pullback homomorphism \
  AlgebraicGeometry.VectorBundleKZero.pullbackRingHom of `K₀(Vect(-))`"]
theorem eq_of_cohomologicalChernCharacter'
    {ch ch' : ∀ X : C, VectorBundleKZero (S.obj X) →+* PowerSeries (𝔄.A X)}
    (hpull : ∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
      PowerSeries.map (𝔄.pull f) (ch Y α) = ch X (VectorBundleKZero.pullbackRingHom (S.map f) α))
    (hpull' : ∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
      PowerSeries.map (𝔄.pull f) (ch' Y α) = ch' X (VectorBundleKZero.pullbackRingHom (S.map f) α))
    (hinv : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      ch X (VectorBundleKZero.classOf (S.obj X) L) =
        expFirstChernClass 𝔄.toChernSetup X (picardClassOf (S.obj X) L hL))
    (hinv' : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      ch' X (VectorBundleKZero.classOf (S.obj X) L) =
        expFirstChernClass 𝔄.toChernSetup X (picardClassOf (S.obj X) L hL))
    (X : C) (α : VectorBundleKZero (S.obj X)) :
    ch X α = ch' X α := by
  classical
  refine DFunLike.congr_fun (VectorBundleKZero.addHom_ext
    (φ := (ch X).toAddMonoidHom) (ψ := (ch' X).toAddMonoidHom) fun E hE => ?_) α
  change ch X (VectorBundleKZero.classOf (S.obj X) E) =
    ch' X (VectorBundleKZero.classOf (S.obj X) E)
  obtain ⟨ι, -, P, p, r, -, hrank, hinj⟩ := 𝔄.exists_clopenRankPieces X E
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mp hE)
  refine PowerSeries.ext fun n => hinj (funext fun i => ?_)
  have key : PowerSeries.map (𝔄.pull (p i)) (ch X (VectorBundleKZero.classOf (S.obj X) E)) =
      PowerSeries.map (𝔄.pull (p i)) (ch' X (VectorBundleKZero.classOf (S.obj X) E)) := by
    rw [hpull (p i) _, hpull' (p i) _, VectorBundleKZero.pullbackRingHom_classOf (S.map (p i)) E hE]
    exact eq_classOf_of_isFiniteLocallyFreeOfRank 𝔄 hpull hpull' hinv hinv' (P i) _ (r i)
      (hrank i)
  simpa using congrArg (PowerSeries.coeff n) key

/-- **The existence half of Stacks Tag 0FIE.** The cohomological Chern character of a single
finite locally free module extends to a ring homomorphism
`ch^H : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} H^{2i}(X)(i)` for every object `X` of `𝒞`, which is graded,
compatible with pullbacks, and takes the value `exp(c_1^H(ℒ))` on an invertible module.

The extension is Tag 0FEM's universal property of the Grothendieck ring, applied to the given
additive, multiplicative and unital assignment; the grading and the compatibility with pullbacks
pass from the generators to all of `K₀(Vect(X))` because the graded series form a subgroup and
because both sides of the pullback equation are additive.

This statement takes the Chern character of a single module as data, so it does not
carry the tag. `Stacks.WeilCohomology.exists_cohomologicalChernCharacter_of_source`
is where [Stacks, Tag 0FIE]'s existence half sits: there the per-module character is
`Stacks.WeilCohomology.chernCharacterOfModule` and nothing is assumed beyond the data
and conditions of Sections 45.12 and 45.14. -/
theorem exists_cohomologicalChernCharacter'
    (chM : ∀ X : C, (S.obj X).Modules → PowerSeries (𝔄.A X))
    (hzero : ∀ (X : C) (M : (S.obj X).Modules),
      ¬ Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M → chM X M = 0)
    (hadd : ∀ (X : C) {E F G : (S.obj X).Modules} (f : E ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E →
        Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} F →
          Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} G →
            Mono f → Epi g → (ShortComplex.mk f g w).Exact →
              chM X F = chM X E + chM X G)
    (hmul : ∀ (X : C) (M N : (S.obj X).Modules),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M →
        Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} N →
          chM X (Scheme.Modules.tensorObjRingedSpace (S.obj X) M N) = chM X M * chM X N)
    (hone : ∀ X : C, chM X (SheafOfModules.unit (S.obj X).ringCatSheaf) = 1)
    (hgrade : ∀ (X : C) (M : (S.obj X).Modules), chM X M ∈ gradedPowerSeries 𝔄.toChernSetup X)
    (hinvM : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      chM X L = expFirstChernClass 𝔄.toChernSetup X (picardClassOf (S.obj X) L hL))
    (hpullM : ∀ {X Y : C} (f : X ⟶ Y) (E : (S.obj Y).Modules),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E →
        PowerSeries.map (𝔄.pull f) (chM Y E) =
          chM X ((Scheme.Modules.pullback (S.map f)).obj E)) :
    ∃ ch : ∀ X : C, VectorBundleKZero (S.obj X) →+* PowerSeries (𝔄.A X),
      (∀ (X : C) (M : (S.obj X).Modules),
          Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M →
          ch X (VectorBundleKZero.classOf (S.obj X) M) = chM X M) ∧
        (∀ (X : C) (α : VectorBundleKZero (S.obj X)), ch X α ∈ gradedPowerSeries 𝔄.toChernSetup X) ∧
          (∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
            PowerSeries.map (𝔄.pull f) (ch Y α) =
              ch X (VectorBundleKZero.pullbackRingHom (S.map f) α)) ∧
            ∀ (X : C) (L : (S.obj X).Modules)
              (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
                (S.obj X).ringCatSheaf.2 L),
              ch X (VectorBundleKZero.classOf (S.obj X) L) =
                expFirstChernClass 𝔄.toChernSetup X (picardClassOf (S.obj X) L hL) := by
  classical
  have hflf : ∀ {X Y : C} (f : X ⟶ Y) (E : (S.obj Y).Modules),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E →
        Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u}
          ((Scheme.Modules.pullback (S.map f)).obj E) := fun f E hE =>
    (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).mpr
      (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme (S.map f) E
        ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mp hE))
  choose ch hch _hchuniq using fun X : C =>
    AlgebraicGeometry.VectorBundleKZero.existsUnique_ringHom_of_tensorMultiplicative
      (S.obj X) (chM X) (hzero X) (fun f g w => hadd X f g w) (hmul X) (hone X)
  refine ⟨ch, hch, fun X α => ?_, fun {X Y} f α => ?_, fun X L hL => ?_⟩
  · refine mem_of_classOf_mem (ch X).toAddMonoidHom _ (fun M hM => ?_) α
    change ch X (VectorBundleKZero.classOf (S.obj X) M) ∈ gradedPowerSeries 𝔄.toChernSetup X
    rw [hch X M hM]
    exact hgrade X M
  · refine DFunLike.congr_fun (VectorBundleKZero.addHom_ext
      (φ := (PowerSeries.map (𝔄.pull f)).toAddMonoidHom.comp (ch Y).toAddMonoidHom)
      (ψ := (ch X).toAddMonoidHom.comp
        (VectorBundleKZero.pullbackRingHom (S.map f)).toAddMonoidHom) fun E hE => ?_) α
    change PowerSeries.map (𝔄.pull f) (ch Y (VectorBundleKZero.classOf (S.obj Y) E)) =
      ch X (VectorBundleKZero.pullbackRingHom (S.map f)
        (VectorBundleKZero.classOf (S.obj Y) E))
    rw [hch Y E hE, VectorBundleKZero.pullbackRingHom_classOf (S.map f) E hE,
      hch X _ (hflf f E hE), hpullM f E hE]
  · rw [hch X L (stacksFlf_of_isInvertible L hL), hinvM X L hL]

end

/-! ### The `𝐐`-structure of `A` read off (D1) -/

section

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- **(D1) read for `A`**: the graded pieces of `A(X)` are `𝐐`-subspaces, that is, `A` takes its
values in *graded* `𝐐`-algebras.

This is what data (D0) and (D1) of Section 45.14 say about `A(X) = ⨁_{i ≥ 0} H^{2i}(X)(i)`: by
(D1) the functor `H^*` lands in graded commutative `F`-algebras, so each graded piece of
`H^*(X)` is an `F`-submodule, and by (D0) the field `F` has characteristic zero, so `𝐐` maps to
`F` and each graded piece is in particular a `𝐐`-subspace.

It is *equivalent*, over a `Stacks.WeilCohomology.ChernSetup`, to the one-degree assertion that
the rationals lie in `A^0(X)`:
`Stacks.WeilCohomology.ChernSetup.algebraMap_mem_grade_zero_of_isRationallyGraded` and
`Stacks.WeilCohomology.ChernSetup.isRationallyGraded_of_algebraMap_mem_grade_zero` prove the two
implications, the first from `one_mem` and the second from `mul_mem`. -/
def ChernSetup.IsRationallyGraded (𝔄 : ChernSetup.{u, v, v₁, w} C S)
    [∀ X : C, Algebra ℚ (𝔄.A X)] : Prop :=
  ∀ (X : C) (i : ℕ) (q : ℚ) {a : 𝔄.A X}, a ∈ 𝔄.grade X i → q • a ∈ 𝔄.grade X i

/-- **The rationals lie in `A^0(X)`, derived from (D1) rather than assumed.** `algebraMap ℚ q` is
`q • 1`, the unit lies in `A^0(X)` by the field `Stacks.WeilCohomology.ChernSetup.one_mem`, and
`A^0(X)` is a `𝐐`-subspace by (D1). -/
theorem ChernSetup.algebraMap_mem_grade_zero_of_isRationallyGraded
    (𝔄 : ChernSetup.{u, v, v₁, w} C S) [∀ X : C, Algebra ℚ (𝔄.A X)]
    (hgr : 𝔄.IsRationallyGraded) (X : C) (q : ℚ) :
    algebraMap ℚ (𝔄.A X) q ∈ 𝔄.grade X 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact hgr X 0 q (𝔄.one_mem X)

/-- **The converse**: the rationals lying in `A^0(X)` makes every graded piece a `𝐐`-subspace,
because `q • a` is `algebraMap ℚ q * a` and multiplication adds degrees. So the field
`Stacks.WeilCohomology.RationalChernSituation.algebraMap_mem_grade_zero` is not an assumption
beyond (D0) and (D1): it is exactly their content for `A`. -/
theorem ChernSetup.isRationallyGraded_of_algebraMap_mem_grade_zero
    (𝔄 : ChernSetup.{u, v, v₁, w} C S) [∀ X : C, Algebra ℚ (𝔄.A X)]
    (hq : ∀ (X : C) (q : ℚ), algebraMap ℚ (𝔄.A X) q ∈ 𝔄.grade X 0) :
    𝔄.IsRationallyGraded := fun X i q {_a} ha => by
  rw [Algebra.smul_def]
  simpa using 𝔄.mul_mem X 0 i (hq X q) ha

/-! ### The existence half with the Chern character of a module discharged -/

/-- **The existence half of Stacks Tag 0FIE with the `𝐐`-structure of `A` taken from (D1).**

This is `Stacks.WeilCohomology.RationalChernSituation.exists_cohomologicalChernCharacter` with
the field `algebraMap_mem_grade_zero` of that situation replaced by
`Stacks.WeilCohomology.ChernSetup.IsRationallyGraded`, the assertion of data (D0) and (D1) of
Section 45.14 that `A` takes its values in graded `𝐐`-algebras. The field is *derived* from it
here, by `Stacks.WeilCohomology.ChernSetup.algebraMap_mem_grade_zero_of_isRationallyGraded`,
rather than assumed; the two are equivalent over a `ChernSetup`, so nothing is lost and nothing
beyond (D0) and (D1) is asked of the `𝐐`-structure.

The tag sits on `Stacks.WeilCohomology.exists_cohomologicalChernCharacter_of_source`, which is
this statement with the three remaining conditions of
`Stacks.WeilCohomology.ChernSituation` spelled out and the structure built inside the proof, so
that it has no structure argument. This statement is kept for consumers that already hold the
situation. -/
theorem ChernSituation.exists_cohomologicalChernCharacter
    (𝔖 : ChernSituation.{u, v, v₁, w} C S) [∀ X : C, Algebra ℚ (𝔖.A X)]
    (hgr : 𝔖.toChernSetup.IsRationallyGraded) :
    ∃ ch : ∀ X : C, VectorBundleKZero (S.obj X) →+* PowerSeries (𝔖.A X),
      (∀ (X : C) (M : (S.obj X).Modules),
          Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M →
          ch X (VectorBundleKZero.classOf (S.obj X) M) =
            chernCharacterOfModule 𝔖.isTotalChernClass_totalChernClass X M) ∧
        (∀ (X : C) (α : VectorBundleKZero (S.obj X)),
            ch X α ∈ gradedPowerSeries 𝔖.toChernSetup X) ∧
          (∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
            PowerSeries.map (𝔖.pull f) (ch Y α) =
              ch X (VectorBundleKZero.pullbackRingHom (S.map f) α)) ∧
            ∀ (X : C) (L : (S.obj X).Modules)
              (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
                (S.obj X).ringCatSheaf.2 L),
              ch X (VectorBundleKZero.classOf (S.obj X) L) =
                expFirstChernClass 𝔖.toChernSetup X (picardClassOf (S.obj X) L hL) :=
  _root_.Stacks.WeilCohomology.exists_cohomologicalChernCharacter' 𝔖.toSourceChernSetup
    (chernCharacterOfModule 𝔖.isTotalChernClass_totalChernClass)
    (fun X M h => chernCharacterOfModule_eq_zero _ X M h)
    (fun X {E F G} f g w hE _hF hG hmono hepi hex =>
      chernCharacterOfModule_add_of_shortExact (E := E) (F := F) (G := G) _ X f g w hE hG
        hmono hepi hex)
    (fun X M N hM hN => chernCharacterOfModule_mul _ X M N hM hN)
    (fun X => chernCharacterOfModule_unit _ X)
    (fun X M => mem_gradedPowerSeries.2 fun n =>
      coeff_chernCharacterOfModule_mem_grade
        (𝔖.toChernSetup.algebraMap_mem_grade_zero_of_isRationallyGraded hgr) _ X M n)
    (fun X L hL => PowerSeries.ext fun n => by
      rw [chernCharacterOfModule_invertible _ X L hL n, coeff_expFirstChernClass])
    (fun {_X _Y} f E hE => PowerSeries.ext fun n => by
      rw [PowerSeries.coeff_map, pull_coeff_chernCharacterOfModule _ f E
        ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mp hE) n])

/-- **The existence half of Stacks Tag 0FIE in the standing situation of Section 45.12**, with
the Chern character of a single module no longer assumed.

`Stacks.WeilCohomology.exists_cohomologicalChernCharacter` takes the per-module character `chM`
and its seven properties as hypotheses, because the source's proof of this tag cites the
existence half of Tag 0FI9 for them. In the standing situation
`Stacks.WeilCohomology.RationalChernSituation` that citation is a theorem of this repository:
`Stacks.WeilCohomology.chernCharacterOfModule` is the source's formula
`ch^A(ℰ) = r^A(ℰ) + ∑_{i ≥ 1} (1/i!) P_i(c_1^A(ℰ), …, c_i^A(ℰ))`, and its seven properties are

* `chernCharacterOfModule_eq_zero` — vanishing off the finite locally free modules;
* `chernCharacterOfModule_add_of_shortExact` — additivity along a short exact sequence;
* `chernCharacterOfModule_mul` — multiplicativity on a tensor product;
* `chernCharacterOfModule_unit` — the value `1` on `𝒪_X`;
* `coeff_chernCharacterOfModule_mem_grade` — the grading;
* `chernCharacterOfModule_invertible` — the value `exp(c₁^A(ℒ))` on an invertible module;
* `pull_coeff_chernCharacterOfModule` — compatibility with pullback.

The last three are stated coefficientwise and are read as statements about the power series by
`PowerSeries.ext`. The total Chern class those depend on is Tag 0FI5 in the same situation, and
Tag 0FI9's `𝐐`-algebra condition on `A(X)`, read with the grading, is the field
`Stacks.WeilCohomology.RationalChernSituation.algebraMap_mem_grade_zero` of the situation this is
stated over. Nothing is left over: the pullback homomorphism of `K₀(Vect(-))` is
`AlgebraicGeometry.VectorBundleKZero.pullbackRingHom`, which is constructed, and the field is
itself data (D0) and (D1) read for `A`, so this is
`Stacks.WeilCohomology.ChernSituation.exists_cohomologicalChernCharacter` above with that field
fed into `Stacks.WeilCohomology.ChernSetup.isRationallyGraded_of_algebraMap_mem_grade_zero`.

The tag sits on `Stacks.WeilCohomology.exists_cohomologicalChernCharacter_of_source`, which
takes the source's own conditions in place of either situation and builds them inside the proof.
This statement is kept for consumers that already hold a `RationalChernSituation`. -/
theorem RationalChernSituation.exists_cohomologicalChernCharacter
    (𝔖 : RationalChernSituation.{u, v, v₁, w} C S) :
    ∃ ch : ∀ X : C, VectorBundleKZero (S.obj X) →+* PowerSeries (𝔖.A X),
      (∀ (X : C) (M : (S.obj X).Modules),
          Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M →
          ch X (VectorBundleKZero.classOf (S.obj X) M) =
            chernCharacterOfModule 𝔖.isTotalChernClass_totalChernClass X M) ∧
        (∀ (X : C) (α : VectorBundleKZero (S.obj X)),
            ch X α ∈ gradedPowerSeries 𝔖.toChernSetup X) ∧
          (∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
            PowerSeries.map (𝔖.pull f) (ch Y α) =
              ch X (VectorBundleKZero.pullbackRingHom (S.map f) α)) ∧
            ∀ (X : C) (L : (S.obj X).Modules)
              (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
                (S.obj X).ringCatSheaf.2 L),
              ch X (VectorBundleKZero.classOf (S.obj X) L) =
                expFirstChernClass 𝔖.toChernSetup X (picardClassOf (S.obj X) L hL) :=
  𝔖.toChernSituation.exists_cohomologicalChernCharacter
    (𝔖.toChernSetup.isRationallyGraded_of_algebraMap_mem_grade_zero
      𝔖.algebraMap_mem_grade_zero)

/-! ### Tag 0FIE in the source's own situation -/

/-- **Stacks Project, Tag 0FIE, existence half.** In the standing situation of Section 45.12,
read with the `𝐐`-structure data (D0) and (D1) of Section 45.14 give, there is a rule assigning
to every object `X` of `𝒞` a ring homomorphism

`ch^H : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} H^{2i}(X)(i)`

which is graded, is compatible with pullbacks, and takes the value `exp(c_1^H(ℒ))` on every
invertible module. With `Stacks.WeilCohomology.eq_of_cohomologicalChernCharacter'` for
uniqueness this is the tag.

**What the situation is.** `Stacks.WeilCohomology.ChernSetup` is the source's own standing
situation — the data the source fixes, with clause (1), clause (2), clause (3)(a), condition
(1), condition (2), condition (4) and the grading `A(X) = ⨁_{i ≥ 0} A^i(X)`; in particular
`Stacks.WeilCohomology.ChernSetup.bundleDatum` is a definition and not a field. The section's
three remaining conditions, each in the source's own form, are the arguments `hpull`,
`hcompare` and `hdivisor` (`Stacks.WeilCohomology.PullbackFirstChernCondition`,
`Stacks.WeilCohomology.BundleCompareClause`, `Stacks.WeilCohomology.DivisorDatumClause`), and
the `𝐐`-structure is the `ℚ`-algebra structure on the `A X` together with
`Stacks.WeilCohomology.ChernSetup.IsRationallyGraded`, which is data (D0) and (D1) of Section
45.14 read for `A`. The `Stacks.WeilCohomology.ChernSituation` the development is written over
is assembled from those three by `Stacks.WeilCohomology.chernSituationOfSource` inside the
proof, so it is not an argument of this statement, and no
`Stacks.WeilCohomology.RationalChernSituation` occurs: condition (5), together with clause
(3)(c), is the argument `hdivisor` rather than a field, and the one-degree form of the
`𝐐`-structure is derived by
`Stacks.WeilCohomology.ChernSetup.algebraMap_mem_grade_zero_of_isRationallyGraded`.

**All three conditions are in the source's own form.** In particular
`Stacks.WeilCohomology.BundleCompareClause` is clause (3)(b) at `f^*ℰ` itself, and not at every
`ℰ'` carrying an isomorphism `f^*ℰ ≅ ℰ'` — that reading would be a closure property clauses (1),
(2) and (3) do not give, since at `f = 𝟙 X` it is the closure of `𝒞` under the `𝐏(ℰ') ⟶ 𝐏(ℰ)`
induced by an arbitrary `ℰ ≅ ℰ'`. The invariance of the total Chern class under an isomorphism of
modules, which `K₀(Vect(X))` forces on any rule out of it, and the pseudofunctoriality coherence
isomorphism `h^*(g^*ℰ) ≅ (h ∘ g)^*ℰ`, which the source has for free, are both theorems:
`Stacks.WeilCohomology.ChernSituation.chernSeries_eq_of_iso` and
`Stacks.WeilCohomology.ChernSituation.pull_chernSeries_coeff_of_iso`.

Nothing is assumed beyond that data and those conditions. The
cohomological Chern character of
a single finite locally free module, which the source's proof of this tag cites from the
existence half of Tag 0FI9 and which
`Stacks.WeilCohomology.exists_cohomologicalChernCharacter` leaves open as `chM` with seven
properties, is `Stacks.WeilCohomology.chernCharacterOfModule` with its seven lemmas; the total
Chern classes of Tag 0FI5 those rest on are
`Stacks.WeilCohomology.ChernSituation.isTotalChernClass_totalChernClass` at the constructed
situation; the rank class `r^A` is `Stacks.WeilCohomology.SourceChernSetup.rankClass`, built from
condition (2); and the pullback homomorphism of `K₀(Vect(-))` is
`AlgebraicGeometry.VectorBundleKZero.pullbackRingHom`. -/
@[stacks 0FIE "existence: the rule, as a ring homomorphism out of `K₀(Vect(X))` into \
  `∏_{i ≥ 0} H^{2i}(X)(i)`, together with its grading, its compatibility with the CONSTRUCTED \
  pullback homomorphism AlgebraicGeometry.VectorBundleKZero.pullbackRingHom of `K₀(Vect(-))` and \
  its \
  value `exp(c₁^H(ℒ))` on an invertible module, stated over the data and the conditions of \
  Sections 45.12 and 45.14 themselves and over NO structure argument. The standing situation is \
  the structure Stacks.WeilCohomology.ChernSetup -- the data the source fixes, with clause (1), \
  clause (2), clause (3)(a), condition (1), condition (2), condition (4) and the source's \
  grading A(X) = sum of the A^i(X) as isInternal_grade -- together with the section's three \
  remaining conditions: condition (3) at f^*L itself, in the source's own form \
  (PullbackFirstChernCondition); clause (3)(b) as the closure property IsBundleCompare at f^*E \
  itself, in the source's own form (BundleCompareClause); clause (3)(c) as the closure \
  property IsBundleEmbedding with condition \
  (5) read at c_1^A(O_P(P')) for the divisor module characterized divisor-theoretically by \
  IsSubbundleDivisorModule (DivisorDatumClause); and the Q-structure of A as data (D0) and (D1) \
  of Section 45.14 read for A, that is Stacks.WeilCohomology.ChernSetup.IsRationallyGraded. The \
  structure Stacks.WeilCohomology.ChernSituation is built inside the proof by \
  Stacks.WeilCohomology.chernSituationOfSource and is not an argument, and no \
  RationalChernSituation occurs. PROVED and not assumed: the cohomological Chern character of a \
  single finite locally free module, which the source's proof cites from Tag 0FI9's existence \
  half and which Stacks.WeilCohomology.exists_cohomologicalChernCharacter leaves open as `chM` \
  with seven properties, discharged here by Stacks.WeilCohomology.chernCharacterOfModule and \
  its seven lemmas; the total Chern classes of Tag 0FI5 those rest on, at the constructed \
  situation (ChernSituation.isTotalChernClass_totalChernClass); the rank class `r^A`, which is \
  Stacks.WeilCohomology.SourceChernSetup.rankClass, built from condition (2); the pullback \
  homomorphism of K_0(Vect(-)), which is AlgebraicGeometry.VectorBundleKZero.pullbackRingHom; the \
  Whitney formula this half needs, proved from clause (3)(c) with condition (5); and the \
  one-degree form of the Q-structure, the rationals lying in A^0(X), DERIVED from (D0) and (D1) \
  by Stacks.WeilCohomology.ChernSetup.algebraMap_mem_grade_zero_of_isRationallyGraded. Nothing \
  outside the data and the conditions of Sections 45.12 and 45.14 is assumed, and NO hypothesis \
  is read more strongly than the source states it: the invariance of the total Chern class \
  under an isomorphism of modules, which K_0(Vect(X)) forces on any rule out of it and which a \
  comparison of P(E) with P(E') would get only by asking clause (3)(b) at every module \
  isomorphic to f^*E, is PROVED (chernSeries_eq_of_iso), as is the pseudofunctoriality \
  coherence isomorphism h^*(g^*E) = (h . g)^*E (pull_chernSeries_coeff_of_iso)"]
theorem exists_cohomologicalChernCharacter_of_source (𝔄 : SourceChernSetup.{u, v, v₁, w} C S)
    [∀ X : C, Algebra ℚ (𝔄.A X)] (hgr : 𝔄.IsRationallyGraded)
    (hpull : PullbackFirstChernCondition 𝔄) (hcompare : BundleCompareClause 𝔄)
    (hdivisor : DivisorDatumClause 𝔄) :
    ∃ ch : ∀ X : C, VectorBundleKZero (S.obj X) →+* PowerSeries (𝔄.A X),
      (∀ (X : C) (M : (S.obj X).Modules),
          Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M →
          ch X (VectorBundleKZero.classOf (S.obj X) M) =
            chernCharacterOfModule (𝔄 := 𝔄) (chernSituationOfSource 𝔄 hpull hcompare
              hdivisor).isTotalChernClass_totalChernClass X M) ∧
        (∀ (X : C) (α : VectorBundleKZero (S.obj X)), ch X α ∈ gradedPowerSeries 𝔄.toChernSetup X) ∧
          (∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
            PowerSeries.map (𝔄.pull f) (ch Y α) =
              ch X (VectorBundleKZero.pullbackRingHom (S.map f) α)) ∧
            ∀ (X : C) (L : (S.obj X).Modules)
              (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
                (S.obj X).ringCatSheaf.2 L),
              ch X (VectorBundleKZero.classOf (S.obj X) L) =
                expFirstChernClass 𝔄.toChernSetup X (picardClassOf (S.obj X) L hL) :=
  let : ∀ X : C, Algebra ℚ ((chernSituationOfSource 𝔄 hpull hcompare hdivisor).A X) :=
    fun X => (inferInstance : Algebra ℚ (𝔄.A X))
  (chernSituationOfSource 𝔄 hpull hcompare hdivisor).exists_cohomologicalChernCharacter hgr

end

end Stacks.WeilCohomology

end
