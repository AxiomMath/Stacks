module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.SourceInverseLine
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.InverseLineDetermination

/-!
# The pins of Tag 0B3V's inverse-line factor

The base-change clause of [Stacks, Tag 0B3V] for the conormal isomorphism rests, through
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap_baseChange_of_twistedSourceBaseChange` and
`Stacks.ProjectiveBundleConormal.sourceCoherence`, on a single equation between two composites of
comparisons of tensor inverses — the *inverse-line factor*. Its two sides are

`g^*(inverseTwistBaseChangeIso ℰ Q e) ≫ Stacks.Divisors.inverseQuotientBaseChange`

and

`schemePullbackCompIso comm ≫ σ'^*(inverseTwistBundleBaseChangeIso) ≫`
`inverseTwistBaseChangeIso ℰ' Q' e'`,

five factors in all. Each is a comparison of two tensor inverses of an invertible module, so each
is determined by what it does to an evaluation pairing; the two composites are then equal because
the composites of the corresponding *positive*-line comparisons are equal, which is
`Stacks.ProjectiveBundleConormal.positiveLine_coherence`.

**This file supplies the pins of the three factors that can be pinned without new geometry**, and
the general apparatus they are stated in.

## Main results

* `Stacks.ProjectiveBundleConormal.pullbackPairing`: a pairing `A ⊗ B ⟶ 𝒪` pulled back along a
  morphism of schemes — Tag 01CD backwards, the pullback of the pairing, and
  `RingedSpaceModuleAdjunction.modulePullbackUnitIso`. Every pairing the inverse-line factor is
  pinned against is one of these, iterated at most twice.
* `Stacks.ProjectiveBundleConormal.pullbackPairing_pin`: **a pin pulls back.** If `δ ⊗ₘ u`
  carries `p'` back to `p`, then their pullbacks carry the pulled-back `p'` back to the
  pulled-back `p`. One `pullbackTensorComparison_naturality_tensorHom`; nothing is assumed of the
  pairings.
* `Stacks.ProjectiveBundleConormal.pullbackPairing_pullbackPairing`: a twice-pulled-back pairing
  written out as its five factors. **Taken in term mode**, for the reason recorded below.
* `Stacks.ProjectiveBundleConormal.schemePullbackCompIso_pin`: **the third factor's pin**, the
  square's identification against the twice-pulled-back pairing down either leg. This is
  `schemePullbackCompIso_tensorHom_comp_pullbackPairing` read at `pullbackPairing`.
* `Stacks.ProjectiveBundleConormal.inverseTwistBundleBaseChangeIso_pullback_pin`: **the fourth
  factor's pin**, the twist factor of `Φ` pulled back along `σ'`.
* `Stacks.ProjBundleInverseBaseChange.negOneTensorInverse_snake`: **the snake identity of Tag
  01CU's `(-1)`st tensor power.** The two ways of cancelling the middle factor of
  `L^{⊗ -1} ⊗ L ⊗ L^{⊗ -1}` agree, as soon as `L^{⊗ -1}` has trivial self-braiding. It is
  `Stacks.Monoidal.braidedSnakeHyp` fed by
  `Stacks.ProjBundleInverseBaseChange.negOneMulIso_eq_braiding`.
* `Stacks.ProjBundleInverseBaseChange.pin_invIso_negOne`: **the pin of the comparison of an
  arbitrary tensor inverse with the `(-1)`st tensor power**, which is the shape the remaining two
  factors are built in.

## Left pin or right pin

`StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.InvIsoLeftPin` and
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.InverseLineDetermination` develop the two
forms a comparison `u : a⁻¹ ⟶ b⁻¹` can be pinned along `ε : L₁ ≅ L₂` in,

`(ε ⊗ₘ u) ≫ b.mulIso = a.mulIso`    and    `u ▷ L₁ ≫ b⁻¹ ◁ ε ≫ b.mulIso' = a.mulIso'`,

and the first file's documentation recommends the left one, on the grounds that the pins of the
third and fourth factors arrive in it. **The right form is the reachable one, and
the reason is the snake.**

`Stacks.TensorPowers.TensorInverse.tensorHom_comp_mulIso_ofIso`, the left pin of the canonical
comparison, asks for the snake identity of its *source* inverse; the right pin
`Stacks.TensorPowers.TensorInverse.pin_invIso_ofIso` asks for it at the *target*, through
`TensorInverse.ofIso_snake`. In the first, second and fifth factors of the inverse-line factor
the source is always `Stacks.ProjBundleInverseBaseChange.pullbackTensorInverse` — the pullback of
a tensor inverse — and the target is always a plain
`Stacks.ProjBundleInverseBaseChange.negOneTensorInverse`. The snake of the latter is
`negOneTensorInverse_snake` below, two lines from `negOneMulIso_eq_braiding`. The snake of the
former is **not** available: it reduces, as
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.SourceBaseChange` records, to Tag 01CD's
comparison commuting with the braiding across the conjugation that
`Stacks.ProjBundleInverseBaseChange.pullbackTensorIso` carries, and that crossing is unpaid.

The third and fourth factors are indifferent: `schemePullbackCompIso_pin` holds for an arbitrary
pairing `p` of an arbitrary pair `(A, B)`, so reading it with the factors exchanged gives the
right form at no cost, and the fourth factor's left pin converts by one braiding, both of its
objects having trivial self-braiding.

## What is still owed

The first, second and fifth factors' pins at the monoidal structure of the conormal
construction, and the assembly.

`pin_invIso_negOne` is stated over `Stacks.SheafInternalHom.monoidalCategory`, which is where Tag
01CU's trivialisations live, while the pins above are stated over
`SheafOfModules.monoidalCategorySheafTensor`. The two are one re-seating apart
(`SheafOfModules.monoidalCategorySheafTensor_eq_reseat`) and
`CategoryTheory.MonoidalCategory.reseat_pin` crosses a pin between them, taking as hypotheses the
descriptions of the two re-seated pairings. Supplying those descriptions is what remains for the
first and fifth factors: the target's is `Stacks.ProjBundleInverseBaseChange.negOneMulIso`
conjugated, which its definition gives directly, and the source's is
`Stacks.ProjBundleInverseBaseChange.pullbackTensorInverse`'s `mulIso'` against `pullbackPairing`,
which is the recognition of `pullbackTensorIso` as `pullbackTensorComparisonIso` and of
`pullbackUnitMonoidalIso` as `modulePullbackUnitIso`.

The second factor is `Stacks.Divisors.inverseQuotientBaseChange`, which is **not** built as
`Stacks.TensorPowers.TensorInverse.invIso` but through
`Stacks.Divisors.isoTensorPowerNegOne`; its pin is
`Stacks.Divisors.inverseQuotientBaseChange_evaluation`, and that is already stated in the right
order `L^{⊗ -1} ⊗ L`, against the composite of Tag 01CU's successor comparison, the reindexing and
the `eqToHom` — the same composite that `negOneMulIso` is built from. So no braiding is owed
there; what is owed is the bridge
`Stacks.SheafOfModules.Invertible.tensorPowerSuccIso_eq` between the two developments of the
integer tensor powers, and the same pairing recognition as above.

**No `@[stacks 0B3V]` attribute is attached, and none is earned**: nothing here states any clause
of the tag. The inverse-line factor is not proved, so the base-change clause for the conormal
isomorphism is not proved.

## Implementation notes

`pullbackPairing_pullbackPairing` is proved in term mode, by `expandAux` over a bare category,
rather than by rewriting with `CategoryTheory.Functor.map_comp`. A goal naming both
`AlgebraicGeometry.Scheme.Modules` and
`SheafOfModules (Stacks.SheafOfModules.TensorSheafification.structureSheaf …)` under a `⊗` is not
type-correct at `implicit` transparency, which is where `rw` and `simp` work; the tactic reports
an application type mismatch on `MonoidalCategoryStruct.tensorObj`. The same reason makes
`schemePullbackCompIso_pin` close with `exact` rather than `simpa`: the unit object is
`SheafOfModules.unit (structureSheafRing _)` on one side and `𝟙_` on the other, and only `exact`
checks that at default transparency.

The two monoidal instances of this file are enabled separately.
`Stacks.SheafInternalHom.braidedCategory` and `symmetricCategory` are local to the abstract-site
section: with them in scope at the scheme spelling, synthesis of
`MonoidalCategoryStruct (Stacks.ProjBundleInverseBaseChange.Mods X)` fails — with this module's import closure, not with
`StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Basic`'s.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.ProjectiveBundleSplitting
open Stacks.SymGraded
open Stacks.SheafOfModules.TensorSheafification
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)

universe v u w

namespace Stacks.ProjBundleInverseBaseChange

open Stacks.TensorPowers Stacks.SheafOfModules
open Stacks.SheafOfModules.TensorPower (tensorPower)

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory

section Site

attribute [local instance] Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.symmetricCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (L : SheafOfModules.{w} (structureSheaf O hO))
  [Stacks.SheafOfModules.IsInvertible O hO L]

/-- **The snake identity of Tag 01CU's `(-1)`st tensor power.** The two ways of cancelling the
middle factor of `L^{⊗ -1} ⊗ L ⊗ L^{⊗ -1}` — reassociate and contract the right pair by the left
trivialisation `negOneMulIso'`, or contract the left pair by the right trivialisation
`negOneMulIso` — agree.

It is not a consequence of the monoidal axioms: it fails in super vector spaces, where the odd
line is invertible and its self-braiding is `-𝟙`. The hypothesis `hb`, that `L^{⊗ -1}` has
trivial self-braiding, is what rules that out, and the implication is
`Stacks.Monoidal.braidedSnakeHyp` once
`Stacks.ProjBundleInverseBaseChange.negOneMulIso_eq_braiding` has identified the right
trivialisation as the braiding followed by the left one. -/
theorem negOneTensorInverse_snake
    (hb : Stacks.GradedSections.HasTrivialSelfBraiding (tensorPower O hO L (-1))) :
    (α_ (negOneTensorInverse O hO L).inv L (negOneTensorInverse O hO L).inv).hom ≫
        (negOneTensorInverse O hO L).inv ◁ (negOneTensorInverse O hO L).mulIso.hom ≫
          (ρ_ (negOneTensorInverse O hO L).inv).hom =
      (negOneTensorInverse O hO L).mulIso'.hom ▷ (negOneTensorInverse O hO L).inv ≫
        (λ_ (negOneTensorInverse O hO L).inv).hom := by
  show _ = (negOneMulIso O hO L).hom ▷ _ ≫ _
  rw [negOneMulIso_eq_braiding]
  exact (Stacks.Monoidal.braidedSnakeHyp hb (negOneMulIso' O hO L)).symm

/-- **The right pin of a comparison with Tag 01CU's `(-1)`st tensor power.** For any two-sided
tensor inverse `a` of `L₁` and any `ε : L₁ ≅ L`, the canonical comparison of `a⁻¹` with
`L^{⊗ -1}` — the inverse object of `Stacks.TensorPowers.TensorInverse.ofIso ε` applied to
`Stacks.ProjBundleInverseBaseChange.negOneTensorInverse` — is pinned along `ε` against the right
trivialisation `negOneMulIso` of `L` and the right trivialisation of `a`.

This is `Stacks.TensorPowers.TensorInverse.pin_invIso_ofIso` with its snake hypothesis discharged
by `negOneTensorInverse_snake`. **Only the snake of the target is needed, and the target is
`negOneTensorInverse`** — the plain `(-1)`st power, not a pullback of one. That is what makes the
right form reachable here and the left form not: the left pin
`Stacks.TensorPowers.TensorInverse.tensorHom_comp_mulIso_ofIso` asks for the snake of the
*source* `a`, and in every application of Tag 0B3V's inverse-line factor the source is
`Stacks.ProjBundleInverseBaseChange.pullbackTensorInverse`, whose snake is not available. -/
theorem pin_invIso_negOne {L₁ : SheafOfModules.{w} (structureSheaf O hO)}
    (a : TensorInverse L₁) (ε : L₁ ≅ L)
    (hb : Stacks.GradedSections.HasTrivialSelfBraiding (tensorPower O hO L (-1))) :
    (TensorInverse.invIso a (TensorInverse.ofIso ε (negOneTensorInverse O hO L))).hom ▷ L₁ ≫
        tensorPower O hO L (-1) ◁ ε.hom ≫ (negOneMulIso O hO L).hom = a.mulIso'.hom :=
  TensorInverse.pin_invIso_ofIso a (negOneTensorInverse O hO L) ε
    (negOneTensorInverse_snake O hO L hb)

end Site

end Stacks.ProjBundleInverseBaseChange

namespace Stacks.ProjectiveBundleConormal

attribute [local instance] monoidalSheafTensor

variable {X X' : Scheme.{u}} (g : X' ⟶ X)
  (E : X.Modules) [E.IsQuasicoherent] (E' : X'.Modules) [E'.IsQuasicoherent]
  (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
  (Q : Stacks.Divisors.InvertibleQuotient X E) (Q' : Stacks.Divisors.InvertibleQuotient X' E')
  (hL : Q'.L ≅ (Scheme.Modules.pullback g).obj Q.L)

/-- **A pairing pulled back along a morphism of schemes.** Tag 01CD backwards splits the
pullback of the tensor product, the pullback of the pairing is taken, and
`RingedSpaceModuleAdjunction.modulePullbackUnitIso` reads `f^*𝒪_Z` as `𝒪_Y`. This is the shape
`Stacks.ProjectiveBundleConormal.pullbackInvertibleEvaluation` is built in, at `p` the evaluation
pairing of `𝒪(1)`. -/
def pullbackPairing {Y Z : Scheme.{u}} (f : Y ⟶ Z) (A B : Z.Modules)
    (p : A ⊗ B ⟶ 𝟙_ (Z.Modules)) :
    (Scheme.Modules.pullback f).obj A ⊗ (Scheme.Modules.pullback f).obj B ⟶
      𝟙_ (Y.Modules) :=
  (pullbackTensorComparisonIso f A B).inv ≫ (Scheme.Modules.pullback f).map p ≫
    (modulePullbackUnitIso f.toLRSHom.toShHom).hom

/-- The reassociation of `Stacks.ProjectiveBundleConormal.pullbackPairing_pin`, over a bare
category. -/
private theorem pinAux {D : Type u} [Category.{v} D] {S S' P P' U₀ I : D}
    (t : S ⟶ S') (bi : S' ⟶ P') (ai : S ⟶ P) (m : P ⟶ P') (mp : P' ⟶ U₀) (mc : P ⟶ U₀)
    (w : U₀ ⟶ I) (hkey : t ≫ bi = ai ≫ m) (hmc : m ≫ mp = mc) :
    t ≫ bi ≫ mp ≫ w = ai ≫ mc ≫ w := by
  rw [← hmc, ← Category.assoc, ← Category.assoc, ← Category.assoc, hkey]
  simp only [Category.assoc]

/-- **A pin pulls back.** If `δ ⊗ₘ u` carries the pairing `p'` back to `p`, then the pullbacks of
`δ` and `u` carry `pullbackPairing f _ _ p'` back to `pullbackPairing f _ _ p`. Nothing is assumed
of the pairings — they are bare morphisms out of a tensor product — so this is the single
transport law the inverse-line factor needs along each of its two pullbacks. One
`Stacks.ProjectiveBundleConormal.pullbackTensorComparison_naturality_tensorHom`, with the
reassociation paid by `pinAux` over a bare category. -/
theorem pullbackPairing_pin {Y Z : Scheme.{u}} (f : Y ⟶ Z) {A B A' B' : Z.Modules}
    (δ : A ⟶ A') (u : B ⟶ B') (p : A ⊗ B ⟶ 𝟙_ (Z.Modules))
    (p' : A' ⊗ B' ⟶ 𝟙_ (Z.Modules)) (h : (δ ⊗ₘ u) ≫ p' = p) :
    ((Scheme.Modules.pullback f).map δ ⊗ₘ (Scheme.Modules.pullback f).map u) ≫
        pullbackPairing f A' B' p' = pullbackPairing f A B p := by
  have hkey : ((Scheme.Modules.pullback f).map δ ⊗ₘ (Scheme.Modules.pullback f).map u) ≫
      (pullbackTensorComparisonIso f A' B').inv =
    (pullbackTensorComparisonIso f A B).inv ≫ (Scheme.Modules.pullback f).map (δ ⊗ₘ u) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
    exact (pullbackTensorComparison_naturality_tensorHom f δ u).symm
  rw [← h]
  exact pinAux _ _ _ _ _ _ _ hkey ((Scheme.Modules.pullback f).map_comp _ _).symm

/-- Expanding a pairing's middle factor, over a bare category. -/
private theorem expandAux {D : Type u} [Category.{v} D] {S P A₁ A₂ A₃ T : D}
    (c : S ⟶ P) (m : P ⟶ A₃) (a : P ⟶ A₁) (b : A₁ ⟶ A₂) (d : A₂ ⟶ A₃) (w : A₃ ⟶ T)
    (hm : m = a ≫ b ≫ d) :
    c ≫ m ≫ w = c ≫ a ≫ b ≫ d ≫ w := by
  rw [hm]; simp only [Category.assoc]

/-- A twice-pulled-back pairing, spelled out as five factors.

Taken in term mode: a goal naming both `AlgebraicGeometry.Scheme.Modules` and the monoidal unit
of the re-seated structure under a `⊗` is not type-correct at `implicit` transparency, where
`rw` and `simp` work, so `CategoryTheory.Functor.map_comp` cannot be applied by rewriting. -/
theorem pullbackPairing_pullbackPairing {Z₁ Z₂ W : Scheme.{u}} (i : Z₁ ⟶ Z₂) (k : Z₂ ⟶ W)
    (A B : W.Modules) (p : A ⊗ B ⟶ 𝟙_ (W.Modules)) :
    pullbackPairing i ((Scheme.Modules.pullback k).obj A) ((Scheme.Modules.pullback k).obj B)
        (pullbackPairing k A B p) =
      (pullbackTensorComparisonIso i ((Scheme.Modules.pullback k).obj A)
          ((Scheme.Modules.pullback k).obj B)).inv ≫
        (Scheme.Modules.pullback i).map (pullbackTensorComparisonIso k A B).inv ≫
          (Scheme.Modules.pullback i).map ((Scheme.Modules.pullback k).map p) ≫
            (Scheme.Modules.pullback i).map (modulePullbackUnitIso k.toLRSHom.toShHom).hom ≫
              (modulePullbackUnitIso i.toLRSHom.toShHom).hom :=
  expandAux _ _ _ _ _ _ (((Scheme.Modules.pullback i).map_comp _ _).trans
    (congrArg _ ((Scheme.Modules.pullback i).map_comp _ _)))

section Square

variable {Z₁ Z₂ W₁ W₂ : Scheme.{u}} {i : Z₁ ⟶ Z₂} {k : Z₂ ⟶ W₂} {f : Z₁ ⟶ W₁} {j : W₁ ⟶ W₂}

/-- **Factor 3 of the inverse-line factor: the square's identification is a left pin along
itself**, against the twice-pulled-back pairing down either leg. This is
`Stacks.ProjectiveBundleConormal.schemePullbackCompIso_tensorHom_comp_pullbackPairing` read at
`pullbackPairing`. -/
theorem schemePullbackCompIso_pin (e : i ≫ k = f ≫ j) (A B : W₂.Modules)
    (p : A ⊗ B ⟶ 𝟙_ (W₂.Modules)) :
    ((schemePullbackCompIso e A).hom ⊗ₘ (schemePullbackCompIso e B).hom) ≫
        pullbackPairing i ((Scheme.Modules.pullback k).obj A)
          ((Scheme.Modules.pullback k).obj B) (pullbackPairing k A B p) =
      pullbackPairing f ((Scheme.Modules.pullback j).obj A)
        ((Scheme.Modules.pullback j).obj B) (pullbackPairing j A B p) := by
  rw [pullbackPairing_pullbackPairing, pullbackPairing_pullbackPairing]
  exact schemePullbackCompIso_tensorHom_comp_pullbackPairing e A B p

end Square

/-- `Stacks.ProjectiveBundleConormal.pullbackInvertibleEvaluation` is the pullback of the
evaluation pairing of `𝒪(1)`. -/
theorem pullbackInvertibleEvaluation_hom :
    (pullbackInvertibleEvaluation g E E' hE).hom =
      pullbackPairing (bundleBaseChangeHom g E E' hE) (tautologicalTwist E (symPieces E))
        (inverseTautologicalTwist E)
        (invertibleEvaluation (tautologicalTwist E (symPieces E))).hom := rfl

/-- **Factor 4 of the inverse-line factor, pulled back to the section.** The twist factor of `Φ`
tensored with the comparison of the tautological twists, both pulled back along `σ'`, carries the
`σ'`-pullback of the evaluation pairing of `𝒪_{𝐏(ℰ')}(1)` back to the `σ'`-pullback of
`Stacks.ProjectiveBundleConormal.pullbackInvertibleEvaluation`.

This is `pullbackPairing_pin` at `σ'` applied to
`Stacks.ProjectiveBundleConormal.inverseTwistBundleBaseChangeIso_tensorHom_comp`; both pairings
are already taken over the re-seated structure, so no crossing is paid. -/
theorem inverseTwistBundleBaseChangeIso_pullback_pin {Y : Scheme.{u}}
    (σ' : Y ⟶ (bundle E').scheme) :
    ((Scheme.Modules.pullback σ').map (symTwistBundleBaseChangeIso g E E' hE).hom ⊗ₘ
          (Scheme.Modules.pullback σ').map
            (inverseTwistBundleBaseChangeIso g E E' hE).hom) ≫
        pullbackPairing σ' (tautologicalTwist E' (symPieces E'))
          (inverseTautologicalTwist E')
          (invertibleEvaluation (tautologicalTwist E' (symPieces E'))).hom =
      pullbackPairing σ'
        ((Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).obj
          (tautologicalTwist E (symPieces E)))
        ((Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).obj
          (inverseTautologicalTwist E))
        (pullbackInvertibleEvaluation g E E' hE).hom :=
  pullbackPairing_pin σ' _ _ _ _ (inverseTwistBundleBaseChangeIso_tensorHom_comp g E E' hE)

end Stacks.ProjectiveBundleConormal

end
