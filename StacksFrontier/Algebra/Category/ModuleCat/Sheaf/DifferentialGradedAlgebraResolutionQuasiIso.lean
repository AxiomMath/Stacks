module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAlgebraResolutionTower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedAlgebraTriangular
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionKernel
public import Mathlib.CategoryTheory.Abelian.Pseudoelements
public import StacksCore.Algebra.Homology.QuasiIso

/-!
# The free algebra on the generators of the tower is quasi-isomorphic to `B`

Let `(B, d)` be a sheaf of differential graded `O`-algebras and let
`SheafOfModules.resolutionHom : A = O⟨⨿ₖ Sₖ⟩ ⟶ B` be the homomorphism built from the tower of
stages `Aₖ`. It is a quasi-isomorphism, as in the closing paragraph of the proof of Tag 0FU2:
`Hⁿ(A) = colim Hⁿ(Aₖ)`, every map `Hⁿ(Aₖ) ⟶ Hⁿ(B)` is surjective from the first stage on, and
its kernel dies at the next stage.

The argument is run on `A` itself rather than on a colimit of cohomology sheaves.

* *Surjectivity.* A cocycle `b` of `B` of degree `n` is the primitive component of the boundary
  pair `(0, b)` of the base stage; the generator of `A` it names is closed and maps to `b`.
* *Injectivity.* Let `z` be a cocycle of `A` of degree `n + 1` whose image in `B` is `d(b)`.
  Locally `z` is a finite combination of words, hence comes from a stage `Aₖ`
  (`SheafOfModules.exists_stageIncl_eq_algToSheaf`); the comparison `Aₖ ⟶ A` is injective on
  sections, having a retraction (`SheafOfModules.stageRetraction`), so the preimage is a cocycle
  of `Aₖ`, and together with `b` it is a boundary pair of stage `k`. The generator of `A` it names
  has differential `z`. So `z` is locally a coboundary, and its class vanishes.

## Main results

* `SheafOfModules.injective_stageIncl`: the comparison of a stage with `A` is injective on
  sections.
* `SheafOfModules.exists_stageIncl_eq_algToSheaf`: every presentation element of `A` comes from a
  stage.
* `SheafOfModules.exists_local_boundary`: a cocycle of `A` whose image in `B` is a coboundary is
  locally a coboundary.
* `SheafOfModules.quasiIso_resolutionHom`: **`A ⟶ B` is a quasi-isomorphism.**

## References

* [Stacks Project, Tag 0FU2](https://stacks.math.columbia.edu/tag/0FU2)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf CategoryTheory.Abelian

universe t v u

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

namespace SheafOfModules

open Stacks Stacks.SheafOfGradedSets

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  {Osharp : Sheaf J CommRingCat.{t}}
  [HasWeakSheafify J (Type t)] [HasSheafify J AddCommGrpCat.{t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  (B : DifferentialGradedAlgebra.{t, t} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))

/-! ### Letters of a stage and letters of `A` -/

/-- The letter of `A` named by a letter of the `k`-th stage. -/
noncomputable def origLetter : (K : ℕ) → {U : Cᵒᵖ} → Letter (resolutionStage B K).F U →
    Letter (resolutionGens B) U
  | 0, _, x => x.1.down.elim0
  | K + 1, U, x => consCases (S := (resolutionStage B K).pairs) (F := (resolutionStage B K).F)
      (motive := fun _ => Letter (resolutionGens B) U) (fun y => ⟨⟨K⟩, y⟩)
      (fun x => origLetter K x) x

/-- The letter of `A` named by the new letter of stage `k + 1` attached to a boundary pair `y`
of stage `k` is the letter of level `k` attached to `y`. -/
theorem origLetter_new (K : ℕ) {U : Cᵒᵖ} (y : (resolutionStage B K).pairs.Index U) :
    origLetter B (K + 1) (newLetter y) = ⟨⟨K⟩, y⟩ := rfl

/-- The letter of `A` named by a letter of stage `k` viewed in stage `k + 1` is the letter of `A`
it names in stage `k`. -/
theorem origLetter_old (K : ℕ) {U : Cᵒᵖ} (x : Letter (resolutionStage B K).F U) :
    origLetter B (K + 1) (succLetter x) = origLetter B K x := rfl

/-- The letter of `A` named by a letter of a stage has the same degree. -/
theorem letterDeg_origLetter (K : ℕ) {U : Cᵒᵖ} (x : Letter (resolutionStage B K).F U) :
    letterDeg (origLetter B K x) = letterDeg x := by
  induction K with
  | zero => exact x.1.down.elim0
  | succ K ih =>
    induction x using consLetter_induction with
    | new y => rfl
    | old x => exact ih x

/-- The letter of `A` named by a letter of the `k`-th stage has level below `k`. -/
theorem origLetter_lt (K : ℕ) {U : Cᵒᵖ} (x : Letter (resolutionStage B K).F U) :
    (origLetter B K x).1.down < K := by
  induction K with
  | zero => exact x.1.down.elim0
  | succ K ih =>
    induction x using consLetter_induction with
    | new y => exact Nat.lt_succ_self K
    | old x => exact Nat.lt_succ_of_lt (ih x)

/-- The comparison of a stage with `A` sends the generator of a letter to the generator of the
letter of `A` it names. -/
theorem stageLetterMap_heq (K : ℕ) {U : Cᵒᵖ} (x : Letter (resolutionStage B K).F U) :
    HEq ((stageLetterMap B K).app U x)
      (algGen (Osharp := Osharp) (resolutionGens B) (origLetter B K x)) := by
  induction K with
  | zero => exact x.1.down.elim0
  | succ K ih =>
    induction x using consLetter_induction with
    | new y => exact HEq.rfl
    | old x => exact ih x

/-- Transport of a boundary pair along an equality of stages. -/
def castPairs {j K : ℕ} (h : j = K) {U : Cᵒᵖ} (s : (resolutionStage B j).pairs.Index U) :
    (resolutionStage B K).pairs.Index U :=
  h ▸ s

/-- Transport of a boundary pair along an equality of stages preserves its degree. -/
theorem castPairs_fst {j K : ℕ} (h : j = K) {U : Cᵒᵖ} (s : (resolutionStage B j).pairs.Index U) :
    (castPairs B h s).1 = s.1 := by
  subst h; rfl

/-- Transport of a boundary pair along an equality of stages commutes with restriction. -/
theorem castPairs_map {j K : ℕ} (h : j = K) {U V : Cᵒᵖ} (f : U ⟶ V)
    (s : (resolutionStage B j).pairs.Index U) :
    Index.map f (castPairs B h s) = castPairs B h (Index.map f s) := by
  subst h; rfl

/-- The letter of the `K`-th stage named by a letter of `A` of level below `K`. -/
noncomputable def toStage : (K : ℕ) → {U : Cᵒᵖ} → (x : Letter (resolutionGens B) U) →
    x.1.down < K → Letter (resolutionStage B K).F U
  | 0, _, x, h => absurd h (Nat.not_lt_zero x.1.down)
  | K + 1, _, x, h =>
    if hj : x.1.down = K then
      newLetter (S := (resolutionStage B K).pairs) (F := (resolutionStage B K).F)
        (castPairs B hj x.2)
    else
      succLetter (S := (resolutionStage B K).pairs) (F := (resolutionStage B K).F)
        (toStage K x (by omega))

/-- A letter of `A` of level `k` names the new letter of stage `k + 1` attached to its boundary
pair. -/
theorem toStage_succ_of_eq (K : ℕ) {U : Cᵒᵖ} (x : Letter (resolutionGens B) U)
    (h : x.1.down < K + 1) (hj : x.1.down = K) :
    toStage B (K + 1) x h = newLetter (S := (resolutionStage B K).pairs)
      (F := (resolutionStage B K).F) (castPairs B hj x.2) :=
  dite_eq_left hj

/-- A letter of `A` of level below `k` names, in stage `k + 1`, the letter it names in stage
`k`. -/
theorem toStage_succ_of_ne (K : ℕ) {U : Cᵒᵖ} (x : Letter (resolutionGens B) U)
    (h : x.1.down < K + 1) (hj : x.1.down ≠ K) :
    toStage B (K + 1) x h = succLetter (S := (resolutionStage B K).pairs)
      (F := (resolutionStage B K).F) (toStage B K x (by omega)) :=
  dite_eq_right hj

/-- The letter of a stage named by a letter of `A` has the same degree. -/
theorem letterDeg_toStage (K : ℕ) {U : Cᵒᵖ} (x : Letter (resolutionGens B) U)
    (h : x.1.down < K) : letterDeg (toStage B K x h) = letterDeg x := by
  induction K with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ K ih =>
    by_cases hj : x.1.down = K
    · rw [toStage_succ_of_eq B K x h hj]
      exact castPairs_fst B hj x.2
    · rw [toStage_succ_of_ne B K x h hj]
      exact ih (by omega)

/-- The letter of a stage named by a letter of `A` is compatible with restriction. -/
theorem toStage_map (K : ℕ) {U V : Cᵒᵖ} (f : U ⟶ V) (x : Letter (resolutionGens B) U)
    (h : x.1.down < K) : letterMap f (toStage B K x h) = toStage B K (letterMap f x) h := by
  induction K with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ K ih =>
    by_cases hj : x.1.down = K
    · rw [toStage_succ_of_eq B K x h hj, toStage_succ_of_eq B K (letterMap f x) h hj]
      exact congrArg (fun s => newLetter (S := (resolutionStage B K).pairs)
        (F := (resolutionStage B K).F) s) (castPairs_map B hj f x.2)
    · rw [toStage_succ_of_ne B K x h hj, toStage_succ_of_ne B K (letterMap f x) h hj]
      exact congrArg (fun s => succLetter (S := (resolutionStage B K).pairs)
        (F := (resolutionStage B K).F) s) (ih (by omega))

/-- The letter of the `k`-th stage named by the letter of `A` that a letter `x` of the `k`-th
stage names is `x`. -/
theorem toStage_origLetter (K : ℕ) {U : Cᵒᵖ} (x : Letter (resolutionStage B K).F U) :
    toStage B K (origLetter B K x) (origLetter_lt B K x) = x := by
  induction K with
  | zero => exact x.1.down.elim0
  | succ K ih =>
    induction x using consLetter_induction with
    | new y =>
      exact toStage_succ_of_eq B K _ _ rfl
    | old x =>
      have hne : (origLetter B K x).1.down ≠ K := Nat.ne_of_lt (origLetter_lt B K x)
      refine (toStage_succ_of_ne B K (origLetter B K x) _ hne).trans ?_
      exact congrArg (fun s => succLetter (S := (resolutionStage B K).pairs)
        (F := (resolutionStage B K).F) s) (ih x)

/-! ### A retraction of the comparison of a stage with `A` -/

/-- Equal letters have equal generators after transport to a common degree. -/
theorem castHom_algGen_congr {I : Type t} {𝒮 : I → SheafOfGradedSets.{t} J} {U : Cᵒᵖ}
    {x x' : Letter 𝒮 U} (e : x = x') {n : ℤ} (h : letterDeg x = n) (h' : letterDeg x' = n) :
    castHom (algPiece (Osharp := Osharp) 𝒮) h U (algGen (Osharp := Osharp) 𝒮 x) =
      castHom (algPiece (Osharp := Osharp) 𝒮) h' U (algGen (Osharp := Osharp) 𝒮 x') := by
  subst e; rfl

/-- The value of the retraction of `Aₖ ⟶ A` on the generator of a letter of `A`. -/
noncomputable def retractionApp (K : ℕ) (U : Cᵒᵖ) (x : Letter (resolutionGens B) U) :
    (algPiece (Osharp := Osharp) (resolutionStage B K).F (letterDeg x)).val.obj U :=
  if h : x.1.down < K then
    castHom (algPiece (Osharp := Osharp) (resolutionStage B K).F) (letterDeg_toStage B K x h) U
      (algGen (Osharp := Osharp) _ (toStage B K x h))
  else 0

/-- On a letter of level below `k`, `retractionApp` is the generator of the letter of the
`k`-th stage it names. -/
theorem retractionApp_of_lt (K : ℕ) (U : Cᵒᵖ) (x : Letter (resolutionGens B) U)
    (h : x.1.down < K) :
    retractionApp B K U x =
      castHom (algPiece (Osharp := Osharp) (resolutionStage B K).F) (letterDeg_toStage B K x h) U
        (algGen (Osharp := Osharp) _ (toStage B K x h)) :=
  dite_eq_left h

/-- On a letter of level at least `k`, `retractionApp` vanishes. -/
theorem retractionApp_of_not_lt (K : ℕ) (U : Cᵒᵖ) (x : Letter (resolutionGens B) U)
    (h : ¬ x.1.down < K) : retractionApp B K U x = 0 :=
  dite_eq_right h

/-- The letter map of the retraction of `Aₖ ⟶ A`: a letter of level below `k` goes to the
generator of the letter of the stage it names, every other letter to zero. -/
noncomputable def stageRetractionMap (K : ℕ) :
    LetterMap (resolutionGens B)
      (freeGradedAlgebra (Osharp := Osharp) (resolutionStage B K).F) where
  app U x := retractionApp B K U x
  naturality {U V} f x := by
    change Stacks.sectionRestrict (algPiece (Osharp := Osharp) (resolutionStage B K).F
      (letterDeg x)).val f (retractionApp B K U x) = retractionApp B K V (letterMap f x)
    by_cases h : x.1.down < K
    · rw [retractionApp_of_lt B K U x h, retractionApp_of_lt B K V (letterMap f x) h,
        sectionRestrict_castHom, algGen_naturality]
      exact castHom_algGen_congr (toStage_map B K f x h) _ _
    · rw [retractionApp_of_not_lt B K U x h, retractionApp_of_not_lt B K V (letterMap f x) h]
      exact map_zero _

/-- The retraction of `Aₖ ⟶ A`, degree by degree. -/
noncomputable abbrev stageRetraction (K : ℕ) (n : ℤ) :
    algPiece (Osharp := Osharp) (resolutionGens B) n ⟶
      algPiece (Osharp := Osharp) (resolutionStage B K).F n :=
  (stageRetractionMap B K).liftPiece n

/-- The degreewise lift of a letter map sends heterogeneously equal sections to heterogeneously
equal sections. -/
theorem liftPiece_heq {I I' : Type t} {𝒮 : I → SheafOfGradedSets.{t} J}
    {𝒮' : I' → SheafOfGradedSets.{t} J}
    (g : LetterMap 𝒮 (freeGradedAlgebra (Osharp := Osharp) 𝒮')) {n n' : ℤ} (e : n = n')
    {U : Cᵒᵖ} {z : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U}
    {z' : (algPiece (Osharp := Osharp) 𝒮 n').val.obj U} (hz : HEq z z') :
    HEq ((g.liftPiece n).val.app U z) ((g.liftPiece n').val.app U z') := by
  subst e
  rw [eq_of_heq hz]

/-- **The retraction is a retraction.** -/
theorem stageIncl_stageRetraction (K : ℕ) (n : ℤ) :
    stageIncl B K n ≫ stageRetraction B K n = 𝟙 _ := by
  refine algPiece_hom_ext_of_algGen (B := freeGradedAlgebra (Osharp := Osharp)
      (resolutionStage B K).F) (resolutionStage B K).F
    (fun n => stageIncl B K n ≫ stageRetraction B K n) (fun n => 𝟙 _) (fun m j U x y => ?_)
    (fun _ _ _ _ _ => rfl) (fun U => ?_) (fun _ => rfl) (fun U x => ?_) n
  · change (stageRetraction B K (m + j)).val.app U
      ((stageIncl B K (m + j)).val.app U ((algMul _ m j).app U x y)) = _
    rw [stageIncl_algMul]
    exact (stageRetractionMap B K).liftPiece_algMul m j U _ _
  · change (stageRetraction B K 0).val.app U ((stageIncl B K 0).val.app U ((algOne _).eval U)) = _
    rw [stageIncl_one]
    exact (stageRetractionMap B K).liftPiece_one U
  · change (stageRetraction B K (letterDeg x)).val.app U
      ((stageIncl B K (letterDeg x)).val.app U (algGen _ x)) = algGen _ x
    rw [stageIncl_algGen]
    have h1 := liftPiece_heq (stageRetractionMap B K) (letterDeg_origLetter B K x).symm
      (stageLetterMap_heq B K x)
    rw [(stageRetractionMap B K).liftPiece_algGen] at h1
    refine eq_of_heq (h1.trans ?_)
    change HEq (retractionApp B K U (origLetter B K x)) _
    rw [retractionApp_of_lt B K U _ (origLetter_lt B K x)]
    refine (heq_castHom _ _ U _).trans ?_
    rw [toStage_origLetter]

/-- **The comparison of a stage with `A` is injective on sections.** -/
theorem injective_stageIncl (K : ℕ) (n : ℤ) (U : Cᵒᵖ) :
    Function.Injective ((stageIncl B K n).val.app U) := by
  intro a b hab
  have h := congrArg ((stageRetraction B K n).val.app U) hab
  have e : ∀ z, (stageRetraction B K n).val.app U ((stageIncl B K n).val.app U z) = z :=
    fun z => congrArg (fun φ => φ.val.app U z) (stageIncl_stageRetraction B K n)
  rwa [e, e] at h

/-! ### Every presentation element of `A` comes from a stage -/

/-- The letter of `A` named by the letter of the `k`-th stage that a letter `x` of `A` of level
below `k` names is `x`. -/
theorem origLetter_toStage (K : ℕ) {U : Cᵒᵖ} (x : Letter (resolutionGens B) U)
    (h : x.1.down < K) : origLetter B K (toStage B K x h) = x := by
  induction K with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ K ih =>
    by_cases hj : x.1.down = K
    · rw [toStage_succ_of_eq B K x h hj, origLetter_new]
      obtain ⟨⟨j⟩, y⟩ := x
      change j = K at hj
      subst hj
      rfl
    · rw [toStage_succ_of_ne B K x h hj, origLetter_old]
      exact ih _

/-- Multiplication in the free graded algebra respects heterogeneous equality of its factors. -/
theorem algMul_heq {I : Type t} (𝒮 : I → SheafOfGradedSets.{t} J) {U : Cᵒᵖ} {m m' j j' : ℤ}
    (hm : m = m') (hj : j = j') {p : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U}
    {p' : (algPiece (Osharp := Osharp) 𝒮 m').val.obj U}
    {q : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U}
    {q' : (algPiece (Osharp := Osharp) 𝒮 j').val.obj U} (hp : HEq p p') (hq : HEq q q') :
    HEq ((algMul 𝒮 m j).app U p q) ((algMul 𝒮 m' j').app U p' q') := by
  subst hm
  subst hj
  cases hp
  cases hq
  rfl

/-- The word of `A` named by a word of the `k`-th stage. -/
noncomputable def origWord (K : ℕ) {U : Cᵒᵖ} (w : Word (resolutionStage B K).F U) :
    Word (resolutionGens B) U :=
  w.map (origLetter B K)

/-- The word of `A` named by a word of a stage has the same degree. -/
theorem wordDeg_origWord (K : ℕ) {U : Cᵒᵖ} (w : Word (resolutionStage B K).F U) :
    wordDeg (origWord B K w) = wordDeg w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    change wordDeg (origLetter B K x :: origWord B K w) = _
    rw [wordDeg_cons, wordDeg_cons, ih, letterDeg_origLetter]

/-- The comparison of a stage with `A` sends the section of a word to the section of the word it
names. -/
theorem wordEval_stageLetterMap (K : ℕ) {U : Cᵒᵖ} (w : Word (resolutionStage B K).F U) :
    HEq ((stageLetterMap B K).wordEval w)
      (algSec (Osharp := Osharp) (resolutionGens B) (origWord B K w)) := by
  induction w with
  | nil => exact HEq.rfl
  | cons x w ih =>
    have ec' : wordDeg (origLetter B K x :: origWord B K w : Word (resolutionGens B) U) =
        letterDeg (origLetter B K x) + wordDeg (origWord B K w) := wordDeg_cons _ _
    have hs := mulAt_algGen_algSec (Osharp := Osharp) (resolutionGens B) (origLetter B K x)
      (origWord B K w) ec'.symm
    refine (heq_castHom _ _ U _).trans ((algMul_heq (resolutionGens B)
      (letterDeg_origLetter B K x).symm (wordDeg_origWord B K w).symm
      (stageLetterMap_heq B K x) ih).trans ?_)
    exact (heq_castHom _ _ U _).symm.trans (heq_of_eq hs)

/-- The comparison of a stage with `A` sends the presentation element `r • w` of the stage to
the image of `r • w'` in `A`, where `w'` is the word of `A` named by `w`. -/
theorem liftAdd_algOf_stage (K : ℕ) {n : ℤ} {U : Cᵒᵖ}
    (w : WordIdx (resolutionStage B K).F n U) (r : secRing Osharp U) :
    (stageLetterMap B K).liftAdd n U (algOf _ n w r) =
      (algToSheaf (Osharp := Osharp) (resolutionGens B) n).app U
        (algOf _ n ⟨origWord B K w.1, (wordDeg_origWord B K w.1).trans w.2⟩ r) := by
  rw [LetterMap.liftAdd_apply, LetterMap.liftPres_algOf, algToSheaf_algOf]
  exact congrArg (r • ·) (Cofree.castHom_eq_castHom _ _ U (wordEval_stageLetterMap B K w.1))

/-- The word of the `k`-th stage naming a word of `A` all of whose letters have level below
`k`. -/
noncomputable def liftWord (K : ℕ) {U : Cᵒᵖ} :
    (w : Word (resolutionGens B) U) → (∀ x ∈ w, x.1.down < K) → Word (resolutionStage B K).F U
  | [], _ => []
  | x :: w, h => toStage B K x (h x List.mem_cons_self) ::
      liftWord K w (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- The word of `A` named by `liftWord B K w h` is `w`. -/
theorem origWord_liftWord (K : ℕ) {U : Cᵒᵖ} (w : Word (resolutionGens B) U)
    (h : ∀ x ∈ w, x.1.down < K) : origWord B K (liftWord B K w h) = w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    change origLetter B K (toStage B K x _) :: origWord B K (liftWord B K w _) = x :: w
    rw [origLetter_toStage, ih]

/-- Every word of `A` has all its letters of level below some `k`. -/
theorem exists_bound {U : Cᵒᵖ} (w : Word (resolutionGens B) U) :
    ∃ K : ℕ, ∀ x ∈ w, x.1.down < K := by
  induction w with
  | nil => exact ⟨0, fun _ h => absurd h List.not_mem_nil⟩
  | cons x w ih =>
    obtain ⟨K, hK⟩ := ih
    refine ⟨max K (x.1.down + 1), fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · omega
    · have := hK y hy
      omega

/-- **Every presentation element of `A` comes from every late enough stage.** -/
theorem exists_stage_lift {n : ℤ} {U : Cᵒᵖ} (a : algSections Osharp (resolutionGens B) n U) :
    ∃ K : ℕ, ∀ K' : ℕ, K ≤ K' → ∃ a' : algSections Osharp (resolutionStage B K').F n U,
      (stageLetterMap B K').liftAdd n U a' =
        (algToSheaf (Osharp := Osharp) (resolutionGens B) n).app U a := by
  induction a using algSections_induction with
  | hzero => exact ⟨0, fun K' _ => ⟨0, (map_zero _).trans (map_zero _).symm⟩⟩
  | hadd a b ha hb =>
    obtain ⟨K₁, h₁⟩ := ha
    obtain ⟨K₂, h₂⟩ := hb
    refine ⟨max K₁ K₂, fun K' hK => ?_⟩
    obtain ⟨a', ha'⟩ := h₁ K' (le_of_max_le_left hK)
    obtain ⟨b', hb'⟩ := h₂ K' (le_of_max_le_right hK)
    refine ⟨a' + b', ?_⟩
    rw [map_add, ha', hb']
    exact (map_add ((algToSheaf (Osharp := Osharp) (resolutionGens B) n).app U).hom a b).symm
  | hof w r =>
    obtain ⟨K, hK⟩ := exists_bound B w.1
    refine ⟨K, fun K' hK' => ?_⟩
    have h' : ∀ x ∈ w.1, x.1.down < K' := fun x hx => lt_of_lt_of_le (hK x hx) hK'
    have hdeg : wordDeg (liftWord B K' w.1 h') = n := by
      rw [← wordDeg_origWord, origWord_liftWord]
      exact w.2
    refine ⟨algOf _ n ⟨liftWord B K' w.1 h', hdeg⟩ r, ?_⟩
    rw [liftAdd_algOf_stage]
    have hw : (⟨origWord B K' (liftWord B K' w.1 h'), (wordDeg_origWord B K' _).trans hdeg⟩ :
        WordIdx (resolutionGens B) n U) = w := Subtype.ext (origWord_liftWord B K' w.1 h')
    rw [hw]

/-- A section of `algPiece` is locally the image of a presentation element. -/
private theorem exists_local_algToSheaf_eq {I : Type t} (𝒮 : I → SheafOfGradedSets.{t} J) (n : ℤ)
    (U : Cᵒᵖ) (z : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U) :
    ∃ S : Sieve U.unop, S ∈ J U.unop ∧ ∀ ⦃W : C⦄ (f : W ⟶ U.unop), S f →
      ∃ a₁ : algSections Osharp 𝒮 n (Opposite.op W),
        (algToSheaf (Osharp := Osharp) 𝒮 n).app (Opposite.op W) a₁ =
          Stacks.sectionRestrict (algPiece (Osharp := Osharp) 𝒮 n).val f.op z :=
  ⟨_, Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map
    (algToSheaf (Osharp := Osharp) 𝒮 n)) z, fun _ _ hf => by exact hf⟩

/-! ### The injectivity argument -/

/-- A stage section whose image in `A` is the restriction of a cocycle of `A` is a cocycle. -/
theorem stage_algD_eq_zero_of_stageIncl (m : ℤ) {V : Cᵒᵖ} {W : C} (f : W ⟶ V.unop) (K : ℕ)
    (c : ((resolutionAlgebra B).complex.cycles (m + 1)).val.obj V)
    (α : (algPiece (Osharp := Osharp) (resolutionStage B K).F (m + 1)).val.obj (Opposite.op W))
    (hαa : (stageIncl B K (m + 1)).val.app _ α =
      Stacks.sectionRestrict (algPiece (Osharp := Osharp) (resolutionGens B) (m + 1)).val f.op
        (homSections ((resolutionAlgebra B).complex.iCycles (m + 1)) V c)) :
    (algD _ (resolutionStage B K).δ (m + 1)).val.app _ α = 0 := by
  have hda : (algD (resolutionGens B) (resolutionδ B) (m + 1)).val.app V
      (homSections ((resolutionAlgebra B).complex.iCycles (m + 1)) V c) = 0 := by
    rw [← freeDGAlgebra_complex_d (resolutionGens B) (resolutionδ B) (resolution_hδ B)]
    exact (homSections_congr ((resolutionAlgebra B).complex.iCycles_d (m + 1) (m + 1 + 1)) V
      c).trans (homSections_zero V c)
  refine injective_stageIncl B K (m + 1 + 1) _ ?_
  refine (stageIncl_algD B K (m + 1) _ α).trans ?_
  refine (congrArg (fun z => (algD (resolutionGens B) (resolutionδ B) (m + 1)).val.app _ z)
    hαa).trans ?_
  refine (algD_naturality (resolutionGens B) (resolutionδ B) (m + 1) f.op _).symm.trans ?_
  rw [hda]
  exact (map_zero _).trans (map_zero _).symm

/-- A stage cocycle lifting the restriction of the cocycle component `a` of a boundary pair
`(a, b)` of `A ⟶ B` maps, on cycles, to the coboundary of the restriction of `b`. -/
theorem cyclesMap_stage_eq_toCycles (m : ℤ) {V : Cᵒᵖ} {W : C} (f : W ⟶ V.unop) (K : ℕ)
    (a : ((resolutionAlgebra B).complex.X (m + 1)).val.obj V) (b : (B.complex.X m).val.obj V)
    (hdb : homSections (B.complex.d m (m + 1)) V b =
      homSections ((resolutionHom B).toHomologicalComplex.f (m + 1)) V a)
    (α : (algPiece (Osharp := Osharp) (resolutionStage B K).F (m + 1)).val.obj (Opposite.op W))
    (hαa : (stageIncl B K (m + 1)).val.app _ α =
      Stacks.sectionRestrict (algPiece (Osharp := Osharp) (resolutionGens B) (m + 1)).val f.op a)
    (ξ : ((resolutionStage B K).A.complex.cycles (m + 1)).val.obj (Opposite.op W))
    (hξ : homSections ((resolutionStage B K).A.complex.iCycles (m + 1)) _ ξ = α) :
    homSections (HomologicalComplex.cyclesMap
        (resolutionStage B K).φ.toHomologicalComplex (m + 1)) _ ξ =
      homSections (B.complex.toCycles m (m + 1)) _
        (Stacks.sectionRestrict (B.complex.X m).val f.op b) := by
  refine injective_iCycles_sections B.complex (m + 1) _ ?_
  calc homSections (B.complex.iCycles (m + 1)) _ (homSections (HomologicalComplex.cyclesMap
          (resolutionStage B K).φ.toHomologicalComplex (m + 1)) _ ξ)
      = homSections ((resolutionStage B K).A.complex.iCycles (m + 1) ≫
          (resolutionStage B K).φ.toHomologicalComplex.f (m + 1)) _ ξ :=
        homSections_congr (HomologicalComplex.cyclesMap_i _ (m + 1)) _ ξ
    _ = ((resolutionStage B K).φ.toHomologicalComplex.f (m + 1)).val.app _ α := by
        rw [homSections_comp, hξ]
        rfl
    _ = ((resolutionHom B).toHomologicalComplex.f (m + 1)).val.app _
          (Stacks.sectionRestrict _ f.op a) :=
        (stageIncl_resolutionMap_app B K (m + 1) _ α).symm.trans
          (congrArg (fun z => ((resolutionMap B).liftPiece (m + 1)).val.app _ z) hαa)
    _ = Stacks.sectionRestrict (B.complex.X (m + 1)).val f.op
          (homSections ((resolutionHom B).toHomologicalComplex.f (m + 1)) V a) :=
        (homSections_naturality ((resolutionHom B).toHomologicalComplex.f (m + 1)) f.op a).symm
    _ = Stacks.sectionRestrict (B.complex.X (m + 1)).val f.op
          (homSections (B.complex.d m (m + 1)) V b) := by rw [hdb]
    _ = homSections (B.complex.d m (m + 1)) _ (Stacks.sectionRestrict _ f.op b) :=
        homSections_naturality _ f.op b
    _ = homSections (B.complex.iCycles (m + 1)) _ (homSections (B.complex.toCycles m (m + 1)) _
          (Stacks.sectionRestrict (B.complex.X m).val f.op b)) :=
        (homSections_congr (HomologicalComplex.toCycles_i _ m (m + 1)) _ _).symm

/-- **A boundary pair of `A ⟶ B` has a cocycle component which is locally a coboundary.** Locally
the cocycle comes from a stage, where it is again a cocycle; together with the primitive it is a
boundary pair of that stage, and the generator of `A` this pair names has the cocycle as its
differential. -/
theorem exists_local_boundary (m : ℤ) (V : Cᵒᵖ)
    (y : (algPairObj (resolutionHom B).toHomologicalComplex m).val.obj V) :
    ∃ S : Sieve V.unop, S ∈ J V.unop ∧ ∀ ⦃W : C⦄ (f : W ⟶ V.unop), S f →
      ∃ e : ((resolutionAlgebra B).complex.X m).val.obj (Opposite.op W),
        Stacks.sectionRestrict ((resolutionAlgebra B).complex.cycles (m + 1)).val f.op
            (homSections (algPairCycle (resolutionHom B).toHomologicalComplex m) V y) =
          homSections ((resolutionAlgebra B).complex.toCycles m (m + 1)) (Opposite.op W) e := by
  set A := resolutionAlgebra B
  set c := homSections (algPairCycle (resolutionHom B).toHomologicalComplex m) V y
  set a := homSections (A.complex.iCycles (m + 1)) V c
  set b := homSections (algPairPrimitive (resolutionHom B).toHomologicalComplex m) V y
  obtain ⟨S, hS, hS'⟩ := exists_local_algToSheaf_eq (resolutionGens B) (m + 1) V a
  refine ⟨S, hS, fun W f hf => ?_⟩
  obtain ⟨a₁, ha₁'⟩ := hS' f hf
  obtain ⟨K, hK⟩ := exists_stage_lift B (n := m + 1) (U := Opposite.op W) a₁
  obtain ⟨a₂, ha₂⟩ := hK K le_rfl
  let α : (algPiece (Osharp := Osharp) (resolutionStage B K).F (m + 1)).val.obj (Opposite.op W) :=
    algToSheafAdd _ (m + 1) _ a₂
  have hαa : (stageIncl B K (m + 1)).val.app _ α =
      Stacks.sectionRestrict (algPiece (Osharp := Osharp) (resolutionGens B) (m + 1)).val f.op a :=
    ((stageLetterMap B K).liftPiece_toSheaf (m + 1) _ a₂).trans (ha₂.trans ha₁')
  obtain ⟨ξ, hξ⟩ := exists_cycles_section (resolutionStage B K).A.complex (m + 1) _ α
    ((homSections_congr (freeDGAlgebra_complex_d _ _ _ (m + 1)) _ α).trans
      (stage_algD_eq_zero_of_stageIncl B m f K c α hαa))
  obtain ⟨yK, hyK₁, -⟩ := exists_algPair_section (resolutionStage B K).φ.toHomologicalComplex
    m _ ξ _ (cyclesMap_stage_eq_toCycles B m f K a b
      (algPairPrimitive_d (resolutionHom B).toHomologicalComplex m V y) α hαa ξ hξ)
  let ℓ : Letter (resolutionGens B) (Opposite.op W) := ⟨⟨K⟩, familyIndex m _ yK⟩
  refine ⟨algGen (Osharp := Osharp) (resolutionGens B) ℓ, ?_⟩
  refine injective_iCycles_sections A.complex (m + 1) _ ?_
  have e1 : homSections (A.complex.iCycles (m + 1)) (Opposite.op W)
      (Stacks.sectionRestrict (A.complex.cycles (m + 1)).val f.op c) =
        Stacks.sectionRestrict (A.complex.X (m + 1)).val f.op a :=
    (homSections_naturality (A.complex.iCycles (m + 1)) f.op c).symm
  have e2 : α = (resolutionStage B K).pairCycle (familyIndex m _ yK) := by
    change α = homSections (algPairCycle _ m ≫ (resolutionStage B K).A.complex.iCycles (m + 1))
      _ (familyPair (familyIndex m _ yK))
    rw [familyPair_familyIndex, homSections_comp, hyK₁, hξ]
  have e3 : homSections (A.complex.iCycles (m + 1)) (Opposite.op W)
      (homSections (A.complex.toCycles m (m + 1)) _
        (algGen (Osharp := Osharp) (resolutionGens B) ℓ)) =
      (algD (resolutionGens B) (resolutionδ B) (letterDeg ℓ)).val.app _
        (algGen (Osharp := Osharp) (resolutionGens B) ℓ) :=
    (homSections_congr (HomologicalComplex.toCycles_i _ m (m + 1)) _ _).trans
      (homSections_congr (freeDGAlgebra_complex_d _ _ _ m) _ _)
  rw [e1, e3, algD_algGen, resolutionδ_app, ← e2]
  exact hαa.symm

/-- **Every boundary pair of `A ⟶ B` has a cocycle component with vanishing class.** -/
theorem algPairCycle_comp_homologyπ (m : ℤ) :
    algPairCycle (resolutionHom B).toHomologicalComplex m ≫
      (resolutionAlgebra B).complex.homologyπ (m + 1) = 0 := by
  refine DifferentialGradedModule.eq_zero_of_sections _ fun V y => ?_
  obtain ⟨S, hS, h⟩ := exists_local_boundary B m V y
  refine ((resolutionAlgebra B).complex.homology (m + 1)).isSheaf.isSeparated V.unop S hS _ 0
    fun W f hf => ?_
  obtain ⟨e, he⟩ := h f hf
  change Stacks.sectionRestrict ((resolutionAlgebra B).complex.homology (m + 1)).val f.op
      (homSections ((resolutionAlgebra B).complex.homologyπ (m + 1)) V
        (homSections (algPairCycle (resolutionHom B).toHomologicalComplex m) V y)) =
    Stacks.sectionRestrict ((resolutionAlgebra B).complex.homology (m + 1)).val f.op 0
  rw [map_zero]
  refine (homSections_naturality ((resolutionAlgebra B).complex.homologyπ (m + 1)) f.op _).trans
    ?_
  change homSections ((resolutionAlgebra B).complex.homologyπ (m + 1)) _
    (Stacks.sectionRestrict _ f.op
      (homSections (algPairCycle (resolutionHom B).toHomologicalComplex m) V y)) = 0
  rw [he, ← homSections_comp]
  exact (homSections_congr ((resolutionAlgebra B).complex.toCycles_comp_homologyπ m (m + 1)) _
    e).trans (homSections_zero _ e)

/-- **`Hⁿ⁺¹(A) ⟶ Hⁿ⁺¹(B)` is a monomorphism.** -/
theorem mono_homologyMap_resolutionHom (m : ℤ) :
    Mono (HomologicalComplex.homologyMap (resolutionHom B).toHomologicalComplex (m + 1)) := by
  refine Pseudoelement.mono_of_zero_of_map_zero _ fun h hh => ?_
  obtain ⟨ξ, hξ⟩ := Pseudoelement.pseudo_surjective_of_epi
    ((resolutionAlgebra B).complex.homologyπ (m + 1)) h
  have hzero : Pseudoelement.pseudoApply (B.complex.homologyπ (m + 1))
      (Pseudoelement.pseudoApply (HomologicalComplex.cyclesMap
        (resolutionHom B).toHomologicalComplex (m + 1)) ξ) = 0 := by
    rw [← Pseudoelement.comp_apply, ← HomologicalComplex.homologyπ_naturality,
      Pseudoelement.comp_apply, hξ]
    exact hh
  have hexact : (ShortComplex.mk (B.complex.toCycles m (m + 1)) (B.complex.homologyπ (m + 1))
      (B.complex.toCycles_comp_homologyπ m (m + 1))).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (B.complex.homologyIsCokernel m (m + 1) (by simp))
  obtain ⟨μ, hμ⟩ := Pseudoelement.pseudo_exact_of_exact hexact _ hzero
  obtain ⟨y, hy, -⟩ := Pseudoelement.pseudo_pullback
    (f := HomologicalComplex.cyclesMap (resolutionHom B).toHomologicalComplex (m + 1))
    (g := B.complex.toCycles m (m + 1)) hμ.symm
  have hc : Limits.pullback.fst
      (HomologicalComplex.cyclesMap (resolutionHom B).toHomologicalComplex (m + 1))
      (B.complex.toCycles m (m + 1)) ≫ (resolutionAlgebra B).complex.homologyπ (m + 1) = 0 :=
    algPairCycle_comp_homologyπ B m
  rw [← hξ, ← hy, ← Pseudoelement.comp_apply, hc, Pseudoelement.zero_apply]

/-- **`Hⁿ(A) ⟶ Hⁿ(B)` is an epimorphism.** A cocycle `b` of `B` is the primitive component of the
boundary pair `(0, b)` of the base stage, and the generator of `A` named by that pair is a
cocycle mapping to `b`. -/
theorem epi_homologyMap_resolutionHom (n : ℤ) :
    Epi (HomologicalComplex.homologyMap (resolutionHom B).toHomologicalComplex n) := by
  refine epi_homologyMap_of_epi_cyclesMap _ n
    (epi_cyclesMap_of_exists_closed_preimage _ n fun U b hb => ?_)
  have hcond : homSections (HomologicalComplex.cyclesMap
        (resolutionStage B 0).φ.toHomologicalComplex (n + 1)) U 0 =
      homSections (B.complex.toCycles n (n + 1)) U b := by
    rw [map_zero]
    refine injective_iCycles_sections B.complex (n + 1) U ?_
    rw [map_zero, ← homSections_comp,
      homSections_congr (HomologicalComplex.toCycles_i _ n (n + 1))]
    exact hb.symm
  obtain ⟨p, hp₁, hp₂⟩ := exists_algPair_section (resolutionStage B 0).φ.toHomologicalComplex
    n U 0 b hcond
  let ℓ : Letter (resolutionGens B) U := ⟨⟨0⟩, familyIndex n U p⟩
  refine ⟨algGen (Osharp := Osharp) (resolutionGens B) ℓ, ?_, ?_⟩
  · refine (homSections_congr (freeDGAlgebra_complex_d _ _ _ n) U _).trans ?_
    change (algD (resolutionGens B) (resolutionδ B) (letterDeg ℓ)).val.app U
      (algGen (Osharp := Osharp) (resolutionGens B) ℓ) = 0
    rw [algD_algGen, resolutionδ_app]
    change (stageIncl B 0 (n + 1)).val.app U (homSections (algPairCycle _ n ≫
      (resolutionStage B 0).A.complex.iCycles (n + 1)) U (familyPair (familyIndex n U p))) = 0
    rw [familyPair_familyIndex, homSections_comp, hp₁, map_zero]
    exact map_zero ((stageIncl B 0 (n + 1)).val.app U).hom
  · change ((resolutionMap B).liftPiece (letterDeg ℓ)).val.app U
      (algGen (Osharp := Osharp) (resolutionGens B) ℓ) = b
    rw [(resolutionMap B).liftPiece_algGen]
    change homSections (algPairPrimitive _ n) U (familyPair (familyIndex n U p)) = b
    rw [familyPair_familyIndex, hp₂]

/-- **The homomorphism `A ⟶ B` of Tag 0FU2 is a quasi-isomorphism.** -/
theorem quasiIso_resolutionHom : QuasiIso (resolutionHom B).toHomologicalComplex := by
  rw [quasiIso_iff_isIso_homologyMap]
  intro n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := mono_homologyMap_resolutionHom B m
  have := epi_homologyMap_resolutionHom B (m + 1)
  exact isIso_of_mono_of_epi _

/-! ### The differential of `A` is triangular -/

/-- The word of `A` named by a word of the `k`-th stage has all its letters of level below `k`. -/
theorem wordBelow_origWord (K : ℕ) {U : Cᵒᵖ} (w : Word (resolutionStage B K).F U) :
    WordBelow (⟨K⟩ : ULift.{t} ℕ) (origWord B K w) := by
  intro x hx
  obtain ⟨x', -, rfl⟩ := List.mem_map.mp hx
  exact origLetter_lt B K x'

/-- The comparison of a stage with `A` carries every presentation element to the image of a
presentation element of `A` whose words have all their letters of level below the stage. -/
theorem exists_isPresBelow_liftAdd (K : ℕ) {n : ℤ} {U : Cᵒᵖ}
    (a : algSections Osharp (resolutionStage B K).F n U) :
    ∃ a' : algSections Osharp (resolutionGens B) n U, IsPresBelow (resolutionGens B) ⟨K⟩ a' ∧
      (algToSheaf (Osharp := Osharp) (resolutionGens B) n).app U a' =
        (stageLetterMap B K).liftAdd n U a := by
  induction a using algSections_induction with
  | hzero => exact ⟨0, IsPresBelow.zero _, (map_zero _).trans (map_zero _).symm⟩
  | hadd a b ha hb =>
    obtain ⟨a', ha', ea⟩ := ha
    obtain ⟨b', hb', eb⟩ := hb
    refine ⟨a' + b', ha'.add hb', ?_⟩
    rw [map_add, ← ea, ← eb]
    exact map_add ((algToSheaf (Osharp := Osharp) (resolutionGens B) n).app U).hom a' b'
  | hof w r =>
    exact ⟨_, isPresBelow_algOf _ (wordBelow_origWord B K w.1) r,
      (liftAdd_algOf_stage B K w r).symm⟩

/-- **The differential of `A` is triangular**: the differential of a generator adjoined at stage
`k` is locally a combination of words in the generators adjoined before stage `k`. This is the
situation of Tag 0FU1. -/
theorem resolutionδ_isTriangular :
    DerivationDatum.IsTriangular (resolutionGens B) (resolutionδ B) := by
  intro U x
  obtain ⟨⟨k⟩, y⟩ := x
  let z := (resolutionStage B k).pairCycle y
  obtain ⟨S, hS, hS'⟩ := exists_local_algToSheaf_eq (resolutionStage B k).F (y.1 + 1) U z
  refine ⟨S, hS, fun V f hf => ?_⟩
  obtain ⟨a₁, ha₁'⟩ := hS' f hf
  obtain ⟨a', ha', e⟩ := exists_isPresBelow_liftAdd B k a₁
  refine ⟨a', ha', e.trans ?_⟩
  refine ((stageLetterMap B k).liftPiece_toSheaf (y.1 + 1) _ a₁).symm.trans ?_
  rw [ha₁']
  exact (PresheafOfModules.naturality_apply (stageIncl B k (y.1 + 1)).val f.op z)

end SheafOfModules

end
