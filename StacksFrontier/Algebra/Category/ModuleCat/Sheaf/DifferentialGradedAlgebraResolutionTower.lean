module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedAlgebraLift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionBase
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# The tower of free differential graded algebras resolving a sheaf of differential graded algebras

Let `(C, O)` be a ringed site and let `(B, d)` be a sheaf of differential graded `O`-algebras.
The proof of Tag 0FU2 builds a sequence

`A₀ ⟶ A₁ ⟶ A₂ ⟶ ⋯ ⟶ B`

of free differential graded `O`-algebras, `Aᵢ = O⟨S₀ ⨿ ⋯ ⨿ Sᵢ₋₁⟩`, in which the generators
`Sᵢ` adjoined at stage `i` are the *boundary pairs* of `Aᵢ ⟶ B`: a generator of degree `n` is a
pair `(a, b)` of a cocycle `a` of `Aᵢ` of degree `n + 1` and a section `b` of `Bⁿ` with
`d(b)` the image of `a`, its differential is `a` and its image in `B` is `b`. This file builds
that sequence, and the free differential graded algebra `A = O⟨⨿ᵢ Sᵢ⟩` on all the generators at
once, with its homomorphism to `B`.

## The stages

The stage `Aᵢ` is `O⟨Fᵢ⟩` for a family `Fᵢ` of sheaves of graded sets indexed by `Fin i`, and
`Fᵢ₊₁` is `Fᵢ` with the new sheaf of generators *prepended* (`SheafOfModules.consFam`), so that
the old generators of `Aᵢ₊₁` are, letter for letter and definitionally, those of `Aᵢ`. The base
stage is `A₀ = O⟨∅⟩ = O`. Starting from `O` rather than from the free algebra on the closed
sections of `B` costs nothing: the generators adjoined at the first step are the boundary pairs
of `O ⟶ B`, and the pairs `(0, b)` among them are exactly the cocycles `b` of `B`.

## Main definitions

* `SheafOfModules.familyGradedSets P` is the sheaf of graded sets whose local sections of degree
  `n` carry a section of `P n`, for a family `P : ℤ → SheafOfModules R`.
* `SheafOfModules.algPairObj φ n` is the sheaf of boundary pairs of degree `n` of a morphism of
  complexes `φ : K ⟶ L`: the fibre product `Ker(d_K^{n+1}) ×_{Ker(d_L^{n+1})} Lⁿ`.
* `SheafOfModules.ResolutionStage B k` is a stage of the tower: a family of `k` sheaves of graded
  sets, a closed derivation datum on it, and a unital homomorphism `O⟨F⟩ ⟶ B`.
* `SheafOfModules.ResolutionStage.next` is the next stage.
* `SheafOfModules.resolutionStage B k` is the `k`-th stage, `SheafOfModules.resolutionGens B` the
  family of all generators, `SheafOfModules.resolutionAlgebra B` the free differential graded
  algebra on them and `SheafOfModules.resolutionHom B` its homomorphism to `B`.

## References

* [Stacks Project, Tag 0FU2](https://stacks.math.columbia.edu/tag/0FU2)
* [Stacks Project, Tag 0FU1](https://stacks.math.columbia.edu/tag/0FU1)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

namespace SheafOfModules

open Stacks Stacks.SheafOfGradedSets

/-! ### The sheaf of graded sets attached to a `ℤ`-indexed family of sheaves of modules -/

section FamilyGradedSets

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasWeakSheafify J (Type m)]

/-- A local section over `V` of the sheaf of graded sets attached to a family `P` of sheaves of
modules: a locally constant degree together with a section of `P n` over `V` in every degree
`n`. A local section of degree `n` carries the section of `P n` named by its `n`-th
component. -/
structure FamilySection (P : ℤ → SheafOfModules.{m} R) (V : Cᵒᵖ) : Type m where
  /-- The degree, as a section of the constant sheaf of integers. -/
  deg : (intSheaf J).obj.obj V
  /-- The section of `P n` over `V`. -/
  pair (n : ℤ) : (P n).val.obj V

variable {P : ℤ → SheafOfModules.{m} R}

/-- Two local sections are equal when their degrees and all their components agree. -/
@[ext] theorem FamilySection.ext {V : Cᵒᵖ} {s s' : FamilySection P V} (hdeg : s.deg = s'.deg)
    (hpair : ∀ n : ℤ, s.pair n = s'.pair n) : s = s' := by
  cases s
  cases s'
  simp_all only [FamilySection.mk.injEq, true_and]
  exact funext hpair

/-- Restriction of a local section of the sheaf of graded sets attached to a family. -/
noncomputable def FamilySection.restrict {V W : Cᵒᵖ} (f : V ⟶ W) (s : FamilySection P V) :
    FamilySection P W where
  deg := (intSheaf J).obj.map f s.deg
  pair n := Stacks.sectionRestrict (P n).val f (s.pair n)

/-- The components of a restricted local section are the restrictions of its components. -/
@[simp] theorem FamilySection.restrict_pair {V W : Cᵒᵖ} (f : V ⟶ W) (s : FamilySection P V)
    (n : ℤ) : (s.restrict f).pair n = Stacks.sectionRestrict (P n).val f (s.pair n) := rfl

variable (P) in
/-- The presheaf of local sections of the sheaf of graded sets attached to a family. -/
noncomputable def familyPresheaf : Cᵒᵖ ⥤ Type m where
  obj V := FamilySection P V
  map f := TypeCat.ofHom (FamilySection.restrict f)
  map_id V := by
    ext s
    · exact (intSheaf J).obj.map_id_apply V s.deg
    · exact Stacks.sectionRestrict_id (P _).val V (s.pair _)
  map_comp f g := by
    ext s
    · exact (intSheaf J).obj.map_comp_apply f g s.deg
    · exact Stacks.sectionRestrict_comp (P _).val f g (s.pair _)

variable (P) in
/-- The presheaf of local sections attached to a family of sheaves of modules is a sheaf. -/
theorem isSheaf_familyPresheaf : Presheaf.IsSheaf J (familyPresheaf P) := by
  have hdeg : Presieve.IsSheaf J (intSheaf J).obj :=
    (isSheaf_iff_isSheaf_of_type J _).mp (intSheaf J).property
  have hpair : ∀ n : ℤ, Presieve.IsSheaf J (Stacks.setSheaf (P n)).obj :=
    fun n => (isSheaf_iff_isSheaf_of_type J _).mp (Stacks.setSheaf (P n)).property
  rw [isSheaf_iff_isSheaf_of_type]
  intro X T hT y hy
  let ydeg : Presieve.FamilyOfElements (intSheaf J).obj T.arrows :=
    fun _ f hf => (y f hf).deg
  let ypair : ∀ n : ℤ, Presieve.FamilyOfElements (Stacks.setSheaf (P n)).obj T.arrows :=
    fun n _ f hf => (y f hf).pair n
  have hydeg : ydeg.Compatible := fun _ _ _ g₁ g₂ _ _ h₁ h₂ h =>
    congrArg FamilySection.deg (hy g₁ g₂ h₁ h₂ h)
  have hypair : ∀ n : ℤ, (ypair n).Compatible := fun n _ _ _ g₁ g₂ _ _ h₁ h₂ h =>
    congrArg (fun s => FamilySection.pair s n) (hy g₁ g₂ h₁ h₂ h)
  obtain ⟨td, htd, hud⟩ := hdeg T hT ydeg hydeg
  choose tp htp hup using fun n : ℤ => hpair n T hT (ypair n) (hypair n)
  refine ⟨⟨td, tp⟩, fun Y f hf => FamilySection.ext (htd f hf) fun n => htp n f hf, ?_⟩
  intro t' ht'
  refine FamilySection.ext
    (hud t'.deg fun _ f hf => congrArg FamilySection.deg (ht' f hf)) fun n => ?_
  exact hup n (t'.pair n) fun _ f hf => congrArg (fun s => FamilySection.pair s n) (ht' f hf)

variable (P) in
/-- **The sheaf of graded sets attached to a `ℤ`-indexed family of sheaves of modules**: its
degree morphism is the locally constant degree carried by a local section, and a local section
of degree `n` carries a section of `P n`. -/
noncomputable def familyGradedSets : Stacks.SheafOfGradedSets.{m} J where
  sheaf := ⟨familyPresheaf P, isSheaf_familyPresheaf P⟩
  degree := ⟨{ app := fun _ => TypeCat.ofHom FamilySection.deg, naturality := fun _ _ _ => rfl }⟩

/-- A local section has degree `n` exactly when its degree component is the constant section
`n`. -/
theorem familyGradedSets_hasDegree_iff (V : Cᵒᵖ) (s : (familyGradedSets P).sheaf.obj.obj V)
    (n : ℤ) : (familyGradedSets P).HasDegree V s n ↔ s.deg = intSection V n :=
  Iff.rfl

variable (P) in
/-- A section of `P n` over `V`, viewed as a local section of degree `n` of the sheaf of graded
sets attached to `P`: it carries the given section in degree `n` and zero in the others. -/
noncomputable def familySection (n : ℤ) (V : Cᵒᵖ) (y : (P n).val.obj V) : FamilySection P V where
  deg := intSection V n
  pair k := if h : n = k then castHom P h V y else 0

/-- The local section named by a section `y` of `P n` carries `y` in degree `n`. -/
@[simp] theorem familySection_pair_self (n : ℤ) (V : Cᵒᵖ) (y : (P n).val.obj V) :
    (familySection P n V y).pair n = y := by
  change (if h : n = n then castHom P h V y else 0) = y
  rw [dif_pos rfl]
  exact castHom_rfl P V y

/-- The local section named by a section of `P n` has degree `n`. -/
theorem familySection_hasDegree (n : ℤ) (V : Cᵒᵖ) (y : (P n).val.obj V) :
    (familyGradedSets P).HasDegree V (familySection P n V y) n :=
  rfl

/-- The homogeneous local section of degree `n` of the sheaf of graded sets attached to `P` named
by a section of `P n`. -/
noncomputable abbrev familyIndex (n : ℤ) (V : Cᵒᵖ) (y : (P n).val.obj V) :
    (familyGradedSets P).Index V :=
  ⟨n, familySection P n V y, familySection_hasDegree n V y⟩

/-- The section of `P n` carried by a homogeneous local section of degree `n`. -/
abbrev familyPair {V : Cᵒᵖ} (y : (familyGradedSets P).Index V) : (P y.1).val.obj V :=
  y.2.1.pair y.1

/-- The section carried by the homogeneous local section named by `y` is `y`. -/
@[simp] theorem familyPair_familyIndex (n : ℤ) (V : Cᵒᵖ) (y : (P n).val.obj V) :
    familyPair (familyIndex n V y) = y :=
  familySection_pair_self n V y

/-- The section carried by a restricted homogeneous local section is the restriction of the
section it carries. -/
theorem familyPair_map {V W : Cᵒᵖ} (f : V ⟶ W) (y : (familyGradedSets P).Index V) :
    familyPair (Index.map f y) = Stacks.sectionRestrict (P y.1).val f (familyPair y) :=
  rfl

end FamilyGradedSets

/-! ### Boundary pairs -/

section Pairs

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {K L : CochainComplex (SheafOfModules.{m} R) ℤ}

/-- **The sheaf of boundary pairs of degree `n`** of a morphism of complexes `φ : K ⟶ L`: the
fibre product `Ker(d_K^{n+1}) ×_{Ker(d_L^{n+1})} Lⁿ`, along the map induced by `φ` on cocycles
and the differential of `L`. A section is a cocycle `a` of `K` of degree `n + 1` and a section `b`
of `Lⁿ` with `d(b) = φ(a)`; it indexes a generator of degree `n` whose differential is `a`. -/
noncomputable def algPairObj (φ : K ⟶ L) (n : ℤ) : SheafOfModules.{m} R :=
  Limits.pullback (HomologicalComplex.cyclesMap φ (n + 1)) (L.toCycles n (n + 1))

/-- The cocycle component of a boundary pair. -/
noncomputable abbrev algPairCycle (φ : K ⟶ L) (n : ℤ) : algPairObj φ n ⟶ K.cycles (n + 1) :=
  Limits.pullback.fst _ _

/-- The primitive component of a boundary pair. -/
noncomputable abbrev algPairPrimitive (φ : K ⟶ L) (n : ℤ) : algPairObj φ n ⟶ L.X n :=
  Limits.pullback.snd _ _

/-- The two components of a boundary pair have the same image in `Ker(d_L^{n+1})`. -/
theorem algPair_condition (φ : K ⟶ L) (n : ℤ) :
    algPairCycle φ n ≫ HomologicalComplex.cyclesMap φ (n + 1) =
      algPairPrimitive φ n ≫ L.toCycles n (n + 1) :=
  Limits.pullback.condition

/-- **The defining condition of a boundary pair, on sections**: the differential of its primitive
component is the image of its cocycle component. -/
theorem algPairPrimitive_d (φ : K ⟶ L) (n : ℤ) (V : Cᵒᵖ) (y : (algPairObj φ n).val.obj V) :
    homSections (L.d n (n + 1)) V (homSections (algPairPrimitive φ n) V y) =
      homSections (φ.f (n + 1)) V
        (homSections (K.iCycles (n + 1)) V (homSections (algPairCycle φ n) V y)) := by
  have hmor : algPairPrimitive φ n ≫ L.d n (n + 1)
      = algPairCycle φ n ≫ K.iCycles (n + 1) ≫ φ.f (n + 1) := by
    rw [← HomologicalComplex.cyclesMap_i φ (n + 1), ← Category.assoc,
      algPair_condition, Category.assoc, HomologicalComplex.toCycles_i]
  exact homSections_congr hmor V y

/-- **A cocycle and a primitive of its image form a boundary pair**: the sections of the fibre
product are the compatible pairs of sections. -/
theorem exists_algPair_section (φ : K ⟶ L) (n : ℤ) (V : Cᵒᵖ) (ξ : (K.cycles (n + 1)).val.obj V)
    (b : (L.X n).val.obj V)
    (h : homSections (HomologicalComplex.cyclesMap φ (n + 1)) V ξ =
      homSections (L.toCycles n (n + 1)) V b) :
    ∃ y : (algPairObj φ n).val.obj V, homSections (algPairCycle φ n) V y = ξ ∧
      homSections (algPairPrimitive φ n) V y = b := by
  let E := SheafOfModules.forget.{m} R ⋙ PresheafOfModules.evaluation R.obj V ⋙
    CategoryTheory.forget (ModuleCat.{m} (R.obj.obj V))
  have hl : IsLimit (PullbackCone.mk (E.map (algPairCycle φ n)) (E.map (algPairPrimitive φ n))
      (by rw [← E.map_comp, ← E.map_comp, algPair_condition])) :=
    isLimitPullbackConeMapOfIsLimit E _ (pullbackIsPullback _ _)
  let p : CategoryTheory.Limits.Types.PullbackObj (E.map (HomologicalComplex.cyclesMap φ (n + 1)))
      (E.map (L.toCycles n (n + 1))) := ⟨(ξ, b), h⟩
  exact ⟨(PullbackCone.IsLimit.equivPullbackObj hl).symm p,
    PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst hl p,
    PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd hl p⟩

end Pairs

/-! ### Prepending a sheaf of graded sets to a finite family -/

section Cons

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  {Osharp : Sheaf J CommRingCat.{t}}
  [HasWeakSheafify J (Type t)] [HasSheafify J AddCommGrpCat.{t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}]

/-- The family `S, F₀, …, F_{k-1}` of `k + 1` sheaves of graded sets: `S` prepended to `F`. The
old members keep their sheaves on the nose, at the shifted index. -/
def consFam {k : ℕ} (S : SheafOfGradedSets.{t} J)
    (F : ULift.{t} (Fin k) → SheafOfGradedSets.{t} J) :
    ULift.{t} (Fin (k + 1)) → SheafOfGradedSets.{t} J :=
  fun j => Fin.cons (α := fun _ => SheafOfGradedSets.{t} J) S (fun i => F ⟨i⟩) j.down

/-- The empty family of sheaves of graded sets. -/
def emptyFam : ULift.{t} (Fin 0) → SheafOfGradedSets.{t} J := fun j => j.down.elim0

variable {k : ℕ} {S : SheafOfGradedSets.{t} J} {F : ULift.{t} (Fin k) → SheafOfGradedSets.{t} J}

/-- A letter of the prepended sheaf. -/
abbrev newLetter {U : Cᵒᵖ} (y : S.Index U) : Letter (consFam S F) U := ⟨⟨0⟩, y⟩

/-- A letter of the old family, read in the extended one. -/
abbrev succLetter {U : Cᵒᵖ} (x : Letter F U) : Letter (consFam S F) U := ⟨⟨x.1.down.succ⟩, x.2⟩

/-- Case analysis on the letters of an extended family. -/
def consCases {U : Cᵒᵖ} {motive : Letter (consFam S F) U → Sort*}
    (new : ∀ y : S.Index U, motive (newLetter y)) (old : ∀ x : Letter F U, motive (succLetter x))
    (x : Letter (consFam S F) U) : motive x :=
  match x with
  | ⟨⟨j⟩, y⟩ =>
    Fin.cases (motive := fun j => ∀ y : (consFam S F ⟨j⟩).Index U, motive ⟨⟨j⟩, y⟩)
      (fun y => new y) (fun i y => old ⟨⟨i⟩, y⟩) j y

/-- `consCases` on a new letter is given by the case for new letters. -/
@[simp] theorem consCases_new {U : Cᵒᵖ} {motive : Letter (consFam S F) U → Sort*}
    (new : ∀ y : S.Index U, motive (newLetter y)) (old : ∀ x : Letter F U, motive (succLetter x))
    (y : S.Index U) : consCases new old (newLetter y) = new y := rfl

/-- `consCases` on an old letter is given by the case for old letters. -/
@[simp] theorem consCases_old {U : Cᵒᵖ} {motive : Letter (consFam S F) U → Sort*}
    (new : ∀ y : S.Index U, motive (newLetter y)) (old : ∀ x : Letter F U, motive (succLetter x))
    (x : Letter F U) : consCases new old (succLetter x) = old x := rfl

/-- Every letter of an extended family is new or old. -/
theorem consLetter_induction {U : Cᵒᵖ} {P : Letter (consFam S F) U → Prop}
    (new : ∀ y : S.Index U, P (newLetter y)) (old : ∀ x : Letter F U, P (succLetter x))
    (x : Letter (consFam S F) U) : P x :=
  consCases new old x

/-- A letter map on an extended family, given on the new letters and by a letter map on the old
family. -/
def consLetterMap {T : GradedAlgebra.{t, t} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
    (L : LetterMap F T)
    (N : ∀ (U : Cᵒᵖ) (y : S.Index U), (T.piece y.1).val.obj U)
    (hN : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (y : S.Index U),
      Stacks.sectionRestrict (T.piece y.1).val f (N U y) = N V (Index.map f y)) :
    LetterMap (consFam S F) T where
  app U x := consCases (motive := fun x => (T.piece (letterDeg x)).val.obj U) (N U) (L.app U) x
  naturality {U V} f x := by
    induction x using consLetter_induction with
    | new y => exact hN f y
    | old x => exact L.naturality f x

/-- A derivation datum on an extended family, given on the new letters and on the old ones. -/
noncomputable def consDerivation
    (N : ∀ (U : Cᵒᵖ) (y : S.Index U),
      (algPiece (Osharp := Osharp) (consFam S F) (y.1 + 1)).val.obj U)
    (hN : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (y : S.Index U),
      Stacks.sectionRestrict (algPiece (Osharp := Osharp) (consFam S F) (y.1 + 1)).val f
        (N U y) = N V (Index.map f y))
    (O : ∀ (U : Cᵒᵖ) (x : Letter F U),
      (algPiece (Osharp := Osharp) (consFam S F) (letterDeg x + 1)).val.obj U)
    (hO : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : Letter F U),
      Stacks.sectionRestrict (algPiece (Osharp := Osharp) (consFam S F) (letterDeg x + 1)).val f
        (O U x) = O V (letterMap f x)) :
    DerivationDatum (consFam S F) Osharp where
  app U x := consCases (motive := fun x =>
    (algPiece (Osharp := Osharp) (consFam S F) (letterDeg x + 1)).val.obj U) (N U) (O U) x
  naturality {U V} f x := by
    induction x using consLetter_induction with
    | new y => exact hN f y
    | old x => exact hO f x

/-- The letter map of the inclusion of `O⟨F⟩` into `O⟨S ⨿ F⟩`: an old letter goes to its own
generator. -/
noncomputable def succLetterMap :
    LetterMap F (freeGradedAlgebra (Osharp := Osharp) (consFam S F)) where
  app U x := algGen (Osharp := Osharp) (consFam S F) (succLetter x)
  naturality f x := algGen_naturality (consFam S F) f (succLetter x)

/-- The letter map of a family of morphisms out of `O⟨F⟩`: a letter goes to the image of its
generator. -/
noncomputable def LetterMap.ofHom
    {T : GradedAlgebra.{t, t} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
    (φ : ∀ n, algPiece (Osharp := Osharp) F n ⟶ T.piece n) : LetterMap F T where
  app U x := (φ (letterDeg x)).val.app U (algGen (Osharp := Osharp) F x)
  naturality f x :=
    (PresheafOfModules.naturality_apply (φ (letterDeg x)).val f _).symm.trans
      (congrArg ((φ (letterDeg x)).val.app _) (algGen_naturality F f x))

/-- The letter map out of the empty family. -/
def emptyLetterMap (T : GradedAlgebra.{t, t} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)) :
    LetterMap (emptyFam (J := J)) T where
  app _ x := x.1.down.elim0
  naturality _ x := x.1.down.elim0

/-- The derivation datum on the empty family. -/
def emptyDerivation : DerivationDatum (emptyFam (J := J)) Osharp where
  app _ x := x.1.down.elim0
  naturality _ x := x.1.down.elim0

end Cons

/-! ### The differential of `O⟨S⟩` as a target -/

section FreeTarget

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  {Osharp : Sheaf J CommRingCat.{t}}
  [HasWeakSheafify J (Type t)] [HasSheafify J AddCommGrpCat.{t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  {I I' : Type t} {𝒮 : I → SheafOfGradedSets.{t} J} {𝒮' : I' → SheafOfGradedSets.{t} J}

/-- The differential of `O⟨S⟩` kills the unit. -/
theorem algD_algOne (δ : DerivationDatum (Osharp := Osharp) 𝒮) (U : Cᵒᵖ) :
    (algD 𝒮 δ 0).val.app U ((algOne (Osharp := Osharp) 𝒮).eval U) = 0 :=
  algD_algSec 𝒮 δ ([] : Word 𝒮 U)

/-- **A morphism of free graded algebras induced by a letter map commutes with the Leibniz
differentials** as soon as it does on the generators. -/
theorem LetterMap.algD_comp_liftPiece_free (δ : DerivationDatum (Osharp := Osharp) 𝒮)
    (δ' : DerivationDatum (Osharp := Osharp) 𝒮')
    (g : LetterMap 𝒮 (freeGradedAlgebra (Osharp := Osharp) 𝒮'))
    (hg : ∀ (U : Cᵒᵖ) (x : Letter 𝒮 U),
      (algD 𝒮' δ' (letterDeg x)).val.app U (g.app U x) =
        (g.liftPiece (letterDeg x + 1)).val.app U (δ.app U x)) (n : ℤ) :
    algD 𝒮 δ n ≫ g.liftPiece (n + 1) = g.liftPiece n ≫ algD 𝒮' δ' n :=
  g.algD_comp_liftPiece_of_derivation δ (algD 𝒮' δ')
    (fun h h₁ h₂ U a b => algD_mulAt 𝒮' δ' h h₁ h₂ U a b) (fun U => algD_algOne δ' U) hg n

/-- A morphism of free graded algebras induced by a letter map commutes with the Leibniz
differentials on sections, as soon as it does on the generators. -/
theorem LetterMap.liftPiece_algD_free (δ : DerivationDatum (Osharp := Osharp) 𝒮)
    (δ' : DerivationDatum (Osharp := Osharp) 𝒮')
    (g : LetterMap 𝒮 (freeGradedAlgebra (Osharp := Osharp) 𝒮'))
    (hg : ∀ (U : Cᵒᵖ) (x : Letter 𝒮 U),
      (algD 𝒮' δ' (letterDeg x)).val.app U (g.app U x) =
        (g.liftPiece (letterDeg x + 1)).val.app U (δ.app U x)) (n : ℤ) (U : Cᵒᵖ)
    (z : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U) :
    (g.liftPiece (n + 1)).val.app U ((algD 𝒮 δ n).val.app U z) =
      (algD 𝒮' δ' n).val.app U ((g.liftPiece n).val.app U z) :=
  homSections_congr (g.algD_comp_liftPiece_free δ δ' hg n) U z

/-- **A composite of a multiplicative unital family with the lift of a letter map is determined by
its values on the generators.** -/
private theorem comp_liftPiece_eq_of_algGen
    {T : GradedAlgebra.{t, t} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
    (f : ∀ n, algPiece (Osharp := Osharp) 𝒮 n ⟶ algPiece (Osharp := Osharp) 𝒮' n)
    (hf : ∀ (m j : ℤ) (U : Cᵒᵖ) (x : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U)
      (y : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U),
      (f (m + j)).val.app U ((algMul 𝒮 m j).app U x y) =
        (algMul 𝒮' m j).app U ((f m).val.app U x) ((f j).val.app U y))
    (hf₁ : ∀ U : Cᵒᵖ, (f 0).val.app U ((algOne (Osharp := Osharp) 𝒮).eval U) =
      (algOne (Osharp := Osharp) 𝒮').eval U)
    (g : LetterMap 𝒮' T) (ψ : ∀ n, algPiece (Osharp := Osharp) 𝒮 n ⟶ T.piece n)
    (hψ : ∀ (m j : ℤ) (U : Cᵒᵖ) (x : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U)
      (y : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U),
      (ψ (m + j)).val.app U ((algMul 𝒮 m j).app U x y) =
        (T.mul m j).app U ((ψ m).val.app U x) ((ψ j).val.app U y))
    (hψ₁ : ∀ U : Cᵒᵖ, (ψ 0).val.app U ((algOne (Osharp := Osharp) 𝒮).eval U) = T.one.eval U)
    (hgen : ∀ (U : Cᵒᵖ) (x : Letter 𝒮 U),
      (g.liftPiece (letterDeg x)).val.app U ((f (letterDeg x)).val.app U (algGen 𝒮 x)) =
        (ψ (letterDeg x)).val.app U (algGen 𝒮 x)) (n : ℤ) :
    f n ≫ g.liftPiece n = ψ n := by
  refine algPiece_hom_ext_of_algGen (B := T) 𝒮 (fun n => f n ≫ g.liftPiece n) ψ
    (fun m j U x y => ?_) hψ (fun U => ?_) hψ₁ hgen n
  · change (g.liftPiece (m + j)).val.app U ((f (m + j)).val.app U ((algMul 𝒮 m j).app U x y)) = _
    rw [hf, g.liftPiece_algMul]
    rfl
  · change (g.liftPiece 0).val.app U ((f 0).val.app U ((algOne 𝒮).eval U)) = _
    rw [hf₁, g.liftPiece_one]

end FreeTarget

/-! ### The stages of the tower -/

section Stages

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  {Osharp : Sheaf J CommRingCat.{t}}
  [HasWeakSheafify J (Type t)] [HasSheafify J AddCommGrpCat.{t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  (B : DifferentialGradedAlgebra.{t, t} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))

/-- **A stage of the tower of Tag 0FU2**: a family of `k` sheaves of graded sets, a closed
derivation datum on it — so that `O⟨F⟩` is a sheaf of differential graded algebras — and a
unital homomorphism `O⟨F⟩ ⟶ B`. -/
structure ResolutionStage (k : ℕ) where
  /-- The generators, in `k` groups. -/
  F : ULift.{t} (Fin k) → SheafOfGradedSets.{t} J
  /-- The differential on the generators. -/
  δ : DerivationDatum F Osharp
  /-- The differential of every generator is closed. -/
  hδ : ∀ (U : Cᵒᵖ) (x : Letter F U), (algD F δ (letterDeg x + 1)).val.app U (δ.app U x) = 0
  /-- The homomorphism to `B`. -/
  φ : freeDGAlgebra F δ hδ ⟶ B
  /-- The homomorphism to `B` is unital. -/
  hφ : ∀ U : Cᵒᵖ, (φ.toHomologicalComplex.f 0).val.app U
    ((freeDGAlgebra F δ hδ).one.eval U) = B.one.eval U

namespace ResolutionStage

variable {B} {k : ℕ} (s : ResolutionStage B k)

/-- The free differential graded algebra of a stage. -/
noncomputable abbrev A :
    DifferentialGradedAlgebra.{t, t} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp) :=
  freeDGAlgebra s.F s.δ s.hδ

/-- The sheaf of graded sets of boundary pairs of the homomorphism of a stage to `B`: the
generators adjoined at the next stage. -/
noncomputable abbrev pairs : SheafOfGradedSets.{t} J :=
  familyGradedSets (algPairObj s.φ.toHomologicalComplex)

/-- The cocycle component of a boundary pair: a closed section of the stage of degree one more
than the pair. -/
noncomputable abbrev pairCycle {U : Cᵒᵖ} (y : s.pairs.Index U) :
    (algPiece (Osharp := Osharp) s.F (y.1 + 1)).val.obj U :=
  homSections (algPairCycle s.φ.toHomologicalComplex y.1 ≫ s.A.complex.iCycles (y.1 + 1)) U
    (familyPair y)

/-- The primitive component of a boundary pair: a section of `B` of the degree of the pair. -/
noncomputable abbrev pairPrimitive {U : Cᵒᵖ} (y : s.pairs.Index U) :
    (B.complex.X y.1).val.obj U :=
  homSections (algPairPrimitive s.φ.toHomologicalComplex y.1) U (familyPair y)

/-- The cocycle component of a restricted boundary pair is the restriction of its cocycle
component. -/
theorem pairCycle_map {U V : Cᵒᵖ} (f : U ⟶ V) (y : s.pairs.Index U) :
    Stacks.sectionRestrict (algPiece (Osharp := Osharp) s.F (y.1 + 1)).val f (s.pairCycle y) =
      s.pairCycle (Index.map f y) :=
  homSections_naturality (algPairCycle s.φ.toHomologicalComplex y.1 ≫
    s.A.complex.iCycles (y.1 + 1)) f (familyPair y)

/-- The primitive component of a restricted boundary pair is the restriction of its primitive
component. -/
theorem pairPrimitive_map {U V : Cᵒᵖ} (f : U ⟶ V) (y : s.pairs.Index U) :
    Stacks.sectionRestrict (B.complex.X y.1).val f (s.pairPrimitive y) =
      s.pairPrimitive (Index.map f y) :=
  homSections_naturality (algPairPrimitive s.φ.toHomologicalComplex y.1) f (familyPair y)

/-- The cocycle component of a boundary pair is closed. -/
theorem algD_pairCycle {U : Cᵒᵖ} (y : s.pairs.Index U) :
    (algD s.F s.δ (y.1 + 1)).val.app U (s.pairCycle y) = 0 := by
  rw [← freeDGAlgebra_complex_d s.F s.δ s.hδ]
  have h : (algPairCycle s.φ.toHomologicalComplex y.1 ≫ s.A.complex.iCycles (y.1 + 1)) ≫
      s.A.complex.d (y.1 + 1) (y.1 + 1 + 1) = 0 := by
    rw [Category.assoc, HomologicalComplex.iCycles_d, comp_zero]
  exact (homSections_congr h U (familyPair y)).trans (homSections_zero U _)

/-- The differential of the primitive component of a boundary pair is the image of its cocycle
component. -/
theorem d_pairPrimitive {U : Cᵒᵖ} (y : s.pairs.Index U) :
    (B.complex.d y.1 (y.1 + 1)).val.app U (s.pairPrimitive y) =
      (s.φ.toHomologicalComplex.f (y.1 + 1)).val.app U (s.pairCycle y) :=
  algPairPrimitive_d s.φ.toHomologicalComplex y.1 U (familyPair y)

/-! #### The next stage -/

/-- The generators of the next stage: the boundary pairs prepended to the generators of this
one. -/
noncomputable abbrev nextF : ULift.{t} (Fin (k + 1)) → SheafOfGradedSets.{t} J :=
  consFam s.pairs s.F

/-- The inclusion of the generators of a stage into those of the next one. -/
noncomputable abbrev inclMap :
    LetterMap s.F (freeGradedAlgebra (Osharp := Osharp) s.nextF) :=
  succLetterMap (S := s.pairs) (F := s.F)

/-- The inclusion of a stage into the next one, degree by degree. -/
noncomputable abbrev incl (n : ℤ) :
    algPiece (Osharp := Osharp) s.F n ⟶ algPiece (Osharp := Osharp) s.nextF n :=
  s.inclMap.liftPiece n

/-- The inclusion of a stage into the next one is multiplicative. -/
theorem incl_algMul (m j : ℤ) (U : Cᵒᵖ) (x : (algPiece (Osharp := Osharp) s.F m).val.obj U)
    (y : (algPiece (Osharp := Osharp) s.F j).val.obj U) :
    (s.incl (m + j)).val.app U ((algMul s.F m j).app U x y) =
      (algMul s.nextF m j).app U ((s.incl m).val.app U x) ((s.incl j).val.app U y) :=
  s.inclMap.liftPiece_algMul m j U x y

/-- The inclusion of a stage into the next one preserves the unit. -/
theorem incl_one (U : Cᵒᵖ) :
    (s.incl 0).val.app U ((algOne (Osharp := Osharp) s.F).eval U) =
      (algOne (Osharp := Osharp) s.nextF).eval U :=
  s.inclMap.liftPiece_one U

/-- The inclusion of a stage into the next one sends a generator to the same generator, read as
an old letter. -/
theorem incl_algGen {U : Cᵒᵖ} (x : Letter s.F U) :
    (s.incl (letterDeg x)).val.app U (algGen (Osharp := Osharp) s.F x) =
      algGen (Osharp := Osharp) s.nextF (succLetter x) :=
  s.inclMap.liftPiece_algGen x

/-- The differential of the next stage on the generators: a new generator goes to the cocycle
component of its boundary pair, an old one to its old differential. -/
noncomputable def nextδ : DerivationDatum (Osharp := Osharp) s.nextF :=
  consDerivation (fun U y => (s.incl (y.1 + 1)).val.app U (s.pairCycle y))
    (fun {U V} f y =>
      (PresheafOfModules.naturality_apply (s.incl (y.1 + 1)).val f _).symm.trans
        (congrArg ((s.incl (y.1 + 1)).val.app V) (s.pairCycle_map f y)))
    (fun U x => (s.incl (letterDeg x + 1)).val.app U (s.δ.app U x))
    (fun {U V} f x =>
      (PresheafOfModules.naturality_apply (s.incl (letterDeg x + 1)).val f _).symm.trans
        (congrArg ((s.incl (letterDeg x + 1)).val.app V) (s.δ.naturality f x)))

/-- The differential of a new generator is the cocycle component of its boundary pair. -/
@[simp] theorem nextδ_new {U : Cᵒᵖ} (y : s.pairs.Index U) :
    s.nextδ.app U (newLetter y) = (s.incl (y.1 + 1)).val.app U (s.pairCycle y) := rfl

/-- The differential of an old generator is the image of its differential in the stage. -/
@[simp] theorem nextδ_old {U : Cᵒᵖ} (x : Letter s.F U) :
    s.nextδ.app U (succLetter x) = (s.incl (letterDeg x + 1)).val.app U (s.δ.app U x) := rfl

/-- The inclusion of a stage into the next one commutes with the differentials, on sections. -/
theorem incl_algD (n : ℤ) (U : Cᵒᵖ) (z : (algPiece (Osharp := Osharp) s.F n).val.obj U) :
    (s.incl (n + 1)).val.app U ((algD s.F s.δ n).val.app U z) =
      (algD s.nextF s.nextδ n).val.app U ((s.incl n).val.app U z) :=
  s.inclMap.liftPiece_algD_free s.δ s.nextδ
    (fun U x => algD_algGen s.nextF s.nextδ (succLetter x)) n U z

/-- The differential of the next stage is closed on the generators. -/
theorem next_hδ (U : Cᵒᵖ) (x : Letter s.nextF U) :
    (algD s.nextF s.nextδ (letterDeg x + 1)).val.app U (s.nextδ.app U x) = 0 := by
  induction x using consLetter_induction with
  | new y =>
    rw [nextδ_new, ← incl_algD, algD_pairCycle, map_zero]
  | old x =>
    rw [nextδ_old, ← incl_algD, s.hδ, map_zero]

/-- The next stage, as a sheaf of differential graded algebras. -/
noncomputable abbrev nextA :
    DifferentialGradedAlgebra.{t, t} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp) :=
  freeDGAlgebra s.nextF s.nextδ s.next_hδ

/-- **The inclusion of a stage into the next one**, a unital homomorphism of sheaves of
differential graded algebras. -/
noncomputable def inclHom : s.A ⟶ s.nextA :=
  s.inclMap.dgLift (B := s.nextA) s.δ s.hδ (fun U x => by
    rw [freeDGAlgebra_complex_d]
    exact algD_algGen s.nextF s.nextδ (succLetter x))

/-- The components of `inclHom` are the degreewise inclusions `incl`. -/
@[simp] theorem inclHom_f (n : ℤ) : s.inclHom.toHomologicalComplex.f n = s.incl n := rfl

/-- The letter map of the homomorphism of the next stage to `B`: a new generator goes to the
primitive component of its boundary pair, an old one to its old image. -/
noncomputable def nextMap : LetterMap s.nextF B.toGradedAlgebra :=
  consLetterMap (LetterMap.ofHom (fun n => s.φ.toHomologicalComplex.f n))
    (fun U y => s.pairPrimitive y) (fun f y => s.pairPrimitive_map f y)

/-- A new generator goes to the primitive component of its boundary pair. -/
@[simp] theorem nextMap_new {U : Cᵒᵖ} (y : s.pairs.Index U) :
    s.nextMap.app U (newLetter y) = s.pairPrimitive y := rfl

/-- An old generator goes to its image under the homomorphism of the stage to `B`. -/
@[simp] theorem nextMap_old {U : Cᵒᵖ} (x : Letter s.F U) :
    s.nextMap.app U (succLetter x) =
      (s.φ.toHomologicalComplex.f (letterDeg x)).val.app U (algGen (Osharp := Osharp) s.F x) :=
  rfl

/-- **The homomorphism of the next stage to `B` restricts to that of this stage.** -/
theorem incl_nextMap (n : ℤ) :
    s.incl n ≫ s.nextMap.liftPiece n = s.φ.toHomologicalComplex.f n :=
  comp_liftPiece_eq_of_algGen s.incl s.incl_algMul s.incl_one s.nextMap
    (fun n => s.φ.toHomologicalComplex.f n) s.φ.map_mul s.hφ (fun U x => by
      rw [s.incl_algGen]
      exact s.nextMap.liftPiece_algGen (succLetter x)) n

/-- The homomorphism of the next stage to `B` restricts to that of this stage, on sections. -/
theorem incl_nextMap_app (n : ℤ) (U : Cᵒᵖ) (z : (algPiece (Osharp := Osharp) s.F n).val.obj U) :
    (s.nextMap.liftPiece n).val.app U ((s.incl n).val.app U z) =
      (s.φ.toHomologicalComplex.f n).val.app U z :=
  homSections_congr (s.incl_nextMap n) U z

/-- The letter map of the next stage is compatible with the differentials. -/
theorem nextMap_d (U : Cᵒᵖ) (x : Letter s.nextF U) :
    (B.complex.d (letterDeg x) (letterDeg x + 1)).val.app U (s.nextMap.app U x) =
      (s.nextMap.liftPiece (letterDeg x + 1)).val.app U (s.nextδ.app U x) := by
  induction x using consLetter_induction with
  | new y =>
    rw [nextMap_new, nextδ_new, incl_nextMap_app]
    exact s.d_pairPrimitive y
  | old x =>
    rw [nextMap_old, nextδ_old, incl_nextMap_app, ← algD_algGen s.F s.δ x,
      ← freeDGAlgebra_complex_d s.F s.δ s.hδ]
    exact homSections_congr (s.φ.toHomologicalComplex.comm (letterDeg x) (letterDeg x + 1)) U
      (algGen (Osharp := Osharp) s.F x)

/-- **The next stage of the tower.** -/
noncomputable def next : ResolutionStage B (k + 1) where
  F := s.nextF
  δ := s.nextδ
  hδ := s.next_hδ
  φ := s.nextMap.dgLift s.nextδ s.next_hδ s.nextMap_d
  hφ := s.nextMap.dgLift_isUnital s.nextδ s.next_hδ s.nextMap_d

end ResolutionStage

end Stages

/-! ### The tower and the free algebra on all its generators -/

section Global

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  {Osharp : Sheaf J CommRingCat.{t}}
  [HasWeakSheafify J (Type t)] [HasSheafify J AddCommGrpCat.{t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  (B : DifferentialGradedAlgebra.{t, t} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))

/-- **The base stage of the tower**, `A₀ = O⟨∅⟩ = O` with its unit homomorphism to `B`. -/
noncomputable def ResolutionStage.base : ResolutionStage B 0 where
  F := emptyFam
  δ := emptyDerivation
  hδ _ x := x.1.down.elim0
  φ := (emptyLetterMap B.toGradedAlgebra).dgLift emptyDerivation (fun _ x => x.1.down.elim0)
    (fun _ x => x.1.down.elim0)
  hφ := (emptyLetterMap B.toGradedAlgebra).dgLift_isUnital emptyDerivation
    (fun _ x => x.1.down.elim0) (fun _ x => x.1.down.elim0)

/-- **The `k`-th stage of the tower of Tag 0FU2.** -/
noncomputable def resolutionStage : (k : ℕ) → ResolutionStage B k
  | 0 => ResolutionStage.base B
  | k + 1 => (resolutionStage k).next

/-- The `(k + 1)`-st stage of the tower is the next stage of the `k`-th. -/
theorem resolutionStage_succ (k : ℕ) :
    resolutionStage B (k + 1) = (resolutionStage B k).next := rfl

/-- **All the generators of the tower**: the boundary pairs adjoined at stage `k` form the
`k`-th member of the family. -/
noncomputable def resolutionGens : ULift.{t} ℕ → SheafOfGradedSets.{t} J :=
  fun k => (resolutionStage B k.down).pairs

/-- The letter map of the comparison of the `k`-th stage with the free algebra on all the
generators: each generator of the stage goes to the generator it names there. -/
noncomputable def stageLetterMap : (k : ℕ) →
    LetterMap (resolutionStage B k).F (freeGradedAlgebra (Osharp := Osharp) (resolutionGens B))
  | 0 => emptyLetterMap _
  | k + 1 => consLetterMap (stageLetterMap k)
      (fun U y => algGen (Osharp := Osharp) (resolutionGens B) ⟨⟨k⟩, y⟩)
      (fun f y => algGen_naturality (resolutionGens B) f ⟨⟨k⟩, y⟩)

/-- A generator adjoined at stage `k` goes to the generator it names in the free algebra on all
the generators. -/
theorem stageLetterMap_new (k : ℕ) {U : Cᵒᵖ} (y : (resolutionStage B k).pairs.Index U) :
    (stageLetterMap B (k + 1)).app U (newLetter y) =
      algGen (Osharp := Osharp) (resolutionGens B) ⟨⟨k⟩, y⟩ := rfl

/-- An old generator of stage `k + 1` goes where it goes from stage `k`. -/
theorem stageLetterMap_old (k : ℕ) {U : Cᵒᵖ} (x : Letter (resolutionStage B k).F U) :
    (stageLetterMap B (k + 1)).app U (succLetter x) = (stageLetterMap B k).app U x := rfl

/-- The comparison of the `k`-th stage with the free algebra on all the generators, degree by
degree. -/
noncomputable abbrev stageIncl (k : ℕ) (n : ℤ) :
    algPiece (Osharp := Osharp) (resolutionStage B k).F n ⟶
      algPiece (Osharp := Osharp) (resolutionGens B) n :=
  (stageLetterMap B k).liftPiece n

/-- The comparison of a stage with the free algebra on all the generators is multiplicative. -/
theorem stageIncl_algMul (k : ℕ) (m j : ℤ) (U : Cᵒᵖ)
    (x : (algPiece (Osharp := Osharp) (resolutionStage B k).F m).val.obj U)
    (y : (algPiece (Osharp := Osharp) (resolutionStage B k).F j).val.obj U) :
    (stageIncl B k (m + j)).val.app U ((algMul _ m j).app U x y) =
      (algMul (resolutionGens B) m j).app U ((stageIncl B k m).val.app U x)
        ((stageIncl B k j).val.app U y) :=
  (stageLetterMap B k).liftPiece_algMul m j U x y

/-- The comparison of a stage with the free algebra on all the generators preserves the unit. -/
theorem stageIncl_one (k : ℕ) (U : Cᵒᵖ) :
    (stageIncl B k 0).val.app U ((algOne (Osharp := Osharp) (resolutionStage B k).F).eval U) =
      (algOne (Osharp := Osharp) (resolutionGens B)).eval U :=
  (stageLetterMap B k).liftPiece_one U

/-- The comparison of a stage with the free algebra on all the generators sends a generator to
its image under `stageLetterMap`. -/
theorem stageIncl_algGen (k : ℕ) {U : Cᵒᵖ} (x : Letter (resolutionStage B k).F U) :
    (stageIncl B k (letterDeg x)).val.app U (algGen (Osharp := Osharp) _ x) =
      (stageLetterMap B k).app U x :=
  (stageLetterMap B k).liftPiece_algGen x

/-- **The comparisons are compatible with the inclusions of the tower.** -/
theorem incl_stageIncl (k : ℕ) (n : ℤ) :
    (resolutionStage B k).incl n ≫ stageIncl B (k + 1) n = stageIncl B k n :=
  comp_liftPiece_eq_of_algGen (resolutionStage B k).incl (resolutionStage B k).incl_algMul
    (resolutionStage B k).incl_one (stageLetterMap B (k + 1)) (stageIncl B k)
    (stageLetterMap B k).liftPiece_algMul (stageLetterMap B k).liftPiece_one (fun U x => by
      rw [(resolutionStage B k).incl_algGen]
      exact ((stageLetterMap B (k + 1)).liftPiece_algGen (succLetter x)).trans
        (stageIncl_algGen B k x).symm) n

/-- The comparisons are compatible with the inclusions of the tower, on sections. -/
theorem incl_stageIncl_app (k : ℕ) (n : ℤ) (U : Cᵒᵖ)
    (z : (algPiece (Osharp := Osharp) (resolutionStage B k).F n).val.obj U) :
    (stageIncl B (k + 1) n).val.app U (((resolutionStage B k).incl n).val.app U z) =
      (stageIncl B k n).val.app U z :=
  homSections_congr (incl_stageIncl B k n) U z

/-- **The differential of the free algebra on all the generators**: a generator adjoined at
stage `k` goes to the cocycle component of its boundary pair, read in the free algebra on all
the generators. -/
noncomputable def resolutionδ : DerivationDatum (Osharp := Osharp) (resolutionGens B) where
  app U x := (stageIncl B x.1.down (x.2.1 + 1)).val.app U
    ((resolutionStage B x.1.down).pairCycle x.2)
  naturality {U V} f x :=
    (PresheafOfModules.naturality_apply (stageIncl B x.1.down (x.2.1 + 1)).val f _).symm.trans
      (congrArg ((stageIncl B x.1.down (x.2.1 + 1)).val.app V)
        ((resolutionStage B x.1.down).pairCycle_map f x.2))

/-- The differential of a generator adjoined at stage `k` is the image of the cocycle component
of its boundary pair. -/
theorem resolutionδ_app (k : ℕ) {U : Cᵒᵖ} (y : (resolutionStage B k).pairs.Index U) :
    (resolutionδ B).app U ⟨⟨k⟩, y⟩ =
      (stageIncl B k (y.1 + 1)).val.app U ((resolutionStage B k).pairCycle y) := rfl

/-- The comparisons commute with the differentials on the generators. -/
theorem stageLetterMap_algD (k : ℕ) (U : Cᵒᵖ) (x : Letter (resolutionStage B k).F U) :
    (algD (resolutionGens B) (resolutionδ B) (letterDeg x)).val.app U
        ((stageLetterMap B k).app U x) =
      (stageIncl B k (letterDeg x + 1)).val.app U ((resolutionStage B k).δ.app U x) := by
  induction k with
  | zero => exact x.1.down.elim0
  | succ k ih =>
    induction x using consLetter_induction with
    | new y =>
      exact (algD_algGen _ _ (⟨⟨k⟩, y⟩ : Letter (resolutionGens B) U)).trans
        (incl_stageIncl_app B k _ U _).symm
    | old x =>
      exact (ih x).trans (incl_stageIncl_app B k _ U _).symm

/-- **The comparisons commute with the differentials.** -/
theorem stageIncl_algD (k : ℕ) (n : ℤ) (U : Cᵒᵖ)
    (z : (algPiece (Osharp := Osharp) (resolutionStage B k).F n).val.obj U) :
    (stageIncl B k (n + 1)).val.app U ((algD _ (resolutionStage B k).δ n).val.app U z) =
      (algD (resolutionGens B) (resolutionδ B) n).val.app U ((stageIncl B k n).val.app U z) :=
  (stageLetterMap B k).liftPiece_algD_free (resolutionStage B k).δ (resolutionδ B)
    (stageLetterMap_algD B k) n U z

/-- The differential of the free algebra on all the generators is closed on the generators. -/
theorem resolution_hδ (U : Cᵒᵖ) (x : Letter (resolutionGens B) U) :
    (algD (resolutionGens B) (resolutionδ B) (letterDeg x + 1)).val.app U
      ((resolutionδ B).app U x) = 0 := by
  obtain ⟨⟨k⟩, y⟩ := x
  refine (stageIncl_algD B k (y.1 + 1) U ((resolutionStage B k).pairCycle y)).symm.trans ?_
  exact (congrArg (fun z => (stageIncl B k (y.1 + 1 + 1)).val.app U z)
    ((resolutionStage B k).algD_pairCycle y)).trans (map_zero _)

/-- **The free differential graded algebra `A = O⟨⨿ₖ Sₖ⟩` on all the generators of the tower**,
the colimit of the tower. -/
noncomputable abbrev resolutionAlgebra :
    DifferentialGradedAlgebra.{t, t} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp) :=
  freeDGAlgebra (resolutionGens B) (resolutionδ B) (resolution_hδ B)

/-- The comparison of the `k`-th stage with `A`, as a homomorphism of sheaves of differential
graded algebras. -/
noncomputable def stageHom (k : ℕ) : (resolutionStage B k).A ⟶ resolutionAlgebra B :=
  (stageLetterMap B k).dgLift (B := resolutionAlgebra B) (resolutionStage B k).δ
    (resolutionStage B k).hδ (fun U x => by
      rw [freeDGAlgebra_complex_d]
      exact stageLetterMap_algD B k U x)

/-- The components of `stageHom` are the degreewise comparisons `stageIncl`. -/
@[simp] theorem stageHom_f (k : ℕ) (n : ℤ) :
    (stageHom B k).toHomologicalComplex.f n = stageIncl B k n := rfl

/-- The letter map of the homomorphism `A ⟶ B`: a generator goes to the primitive component of
its boundary pair. -/
noncomputable def resolutionMap : LetterMap (resolutionGens B) B.toGradedAlgebra where
  app U x := (resolutionStage B x.1.down).pairPrimitive x.2
  naturality f x := (resolutionStage B x.1.down).pairPrimitive_map f x.2

/-- The homomorphism `A ⟶ B` agrees with the homomorphism of each stage on its generators. -/
theorem resolutionMap_liftPiece_stageLetterMap (k : ℕ) {U : Cᵒᵖ}
    (x : Letter (resolutionStage B k).F U) :
    ((resolutionMap B).liftPiece (letterDeg x)).val.app U ((stageLetterMap B k).app U x) =
      ((resolutionStage B k).φ.toHomologicalComplex.f (letterDeg x)).val.app U
        (algGen (Osharp := Osharp) _ x) := by
  induction k with
  | zero => exact x.1.down.elim0
  | succ k ih =>
    induction x using consLetter_induction with
    | new y =>
      exact ((resolutionMap B).liftPiece_algGen (⟨⟨k⟩, y⟩ : Letter (resolutionGens B) U)).trans
        ((resolutionStage B k).nextMap.dgLift_algGen _ _ (resolutionStage B k).nextMap_d
          (newLetter y)).symm
    | old x =>
      exact (ih x).trans ((resolutionStage B k).nextMap.dgLift_algGen _ _
        (resolutionStage B k).nextMap_d (succLetter x)).symm

/-- **The homomorphism `A ⟶ B` restricts, at every stage, to the homomorphism of that stage.** -/
theorem stageIncl_resolutionMap (k : ℕ) (n : ℤ) :
    stageIncl B k n ≫ (resolutionMap B).liftPiece n =
      (resolutionStage B k).φ.toHomologicalComplex.f n :=
  comp_liftPiece_eq_of_algGen (stageIncl B k) (stageIncl_algMul B k) (stageIncl_one B k)
    (resolutionMap B) (fun n => (resolutionStage B k).φ.toHomologicalComplex.f n)
    (resolutionStage B k).φ.map_mul (resolutionStage B k).hφ (fun U x => by
      rw [stageIncl_algGen]
      exact resolutionMap_liftPiece_stageLetterMap B k x) n

/-- The homomorphism `A ⟶ B` restricts, at every stage, to the homomorphism of that stage, on
sections. -/
theorem stageIncl_resolutionMap_app (k : ℕ) (n : ℤ) (U : Cᵒᵖ)
    (z : (algPiece (Osharp := Osharp) (resolutionStage B k).F n).val.obj U) :
    ((resolutionMap B).liftPiece n).val.app U ((stageIncl B k n).val.app U z) =
      ((resolutionStage B k).φ.toHomologicalComplex.f n).val.app U z :=
  homSections_congr (stageIncl_resolutionMap B k n) U z

/-- The letter map of `A ⟶ B` is compatible with the differentials. -/
theorem resolutionMap_d (U : Cᵒᵖ) (x : Letter (resolutionGens B) U) :
    (B.complex.d (letterDeg x) (letterDeg x + 1)).val.app U ((resolutionMap B).app U x) =
      ((resolutionMap B).liftPiece (letterDeg x + 1)).val.app U ((resolutionδ B).app U x) := by
  obtain ⟨⟨k⟩, y⟩ := x
  exact ((resolutionStage B k).d_pairPrimitive y).trans
    (stageIncl_resolutionMap_app B k (y.1 + 1) U _).symm

/-- **The homomorphism `A ⟶ B` of Tag 0FU2.** -/
noncomputable def resolutionHom : resolutionAlgebra B ⟶ B :=
  (resolutionMap B).dgLift (resolutionδ B) (resolution_hδ B) (resolutionMap_d B)

/-- The homomorphism `A ⟶ B` is unital. -/
theorem resolutionHom_isUnital (U : Cᵒᵖ) :
    ((resolutionHom B).toHomologicalComplex.f 0).val.app U
      ((resolutionAlgebra B).one.eval U) = B.one.eval U :=
  (resolutionMap B).dgLift_isUnital _ _ _ U

end Global

end SheafOfModules

end
