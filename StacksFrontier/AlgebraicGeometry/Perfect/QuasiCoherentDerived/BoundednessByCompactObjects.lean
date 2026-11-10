module

public import StacksFrontier.AlgebraicGeometry.Perfect.ClassicalGeneratorOfPerfectComplexes
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulOrthogonality.AffineKoszulWindow
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.UniformBoundAnyModel
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasiCoherentDirectSumsLocallySmall
public import StacksFrontier.CategoryTheory.Triangulated.EventualOrthogonality

/-!
# Boundedness in `D_QCoh(𝒪_X)` is detected by the compact objects

Let `X` be a quasi-compact and quasi-separated scheme and let `E` be an object of `D_QCoh(𝒪_X)`.
Then `E` is bounded above (resp. below) if and only if for every compact object `P` of
`D_QCoh(𝒪_X)` the groups `Hom(P⟦-i⟧, E)` vanish for `i ≫ 0` (resp. `i ≪ 0`).

This is the geometric heart of [Stacks, Tags 0GEN and 0GEQ]: their condition (7)(a) for
`Hom` implies their condition (1). The proof is the source's induction over a finite affine
cover ([Stacks, Tag 08DR] in the form used for [Stacks, Tag 09IS]): write `X = U ∪ V` with `U` a
quasi-compact open covered by fewer affines, `V = Spec A` affine, and
`U ∩ V = D(f₁) ∪ … ∪ D(f_r) ⊆ V`.

* The object `K'` glued from `0` on `U` and the Koszul complex `K` of the `f_i` on `V`
  ([Stacks, Tag 0GEP]) is compact, so `Hom(K'⟦-i⟧, E) = 0` for `i ≫ 0`, hence
  `Hom(K⟦-i⟧, E|_V) = 0` for `i ≫ 0`.
* The cone `C` of the unit `E ⟶ Rj_{U,*}(E|_U)` vanishes on `U`, and on `V` it receives nothing
  from the `K⟦-i⟧` for `i ≫ 0`; so by the degreewise Koszul detection behind [Stacks, Tag 0GEJ]
  its cohomology vanishes in high degrees, i.e. `τ_{≥a}E = τ_{≥a}Rj_{U,*}(E|_U)`.
* Every compact object `P` of `D_QCoh(𝒪_U)` has `P ⊕ P⟦1⟧` equal to the restriction of a compact
  object `R_P` of `D_QCoh(𝒪_X)` ([Stacks, Tags 08EK and 08DG], the compact form of
  [Stacks, Tag 09IQ]); since `C` is bounded, [Stacks, Tag 0GEL] turns the vanishing of
  `Hom(R_P⟦-i⟧, E)` into that of `Hom(P⟦-i⟧, E|_U)`. So `E|_U` satisfies the hypothesis on `U`,
  hence is bounded by induction, and `Rj_{U,*}` preserves boundedness ([Stacks, Tag 08D5]).

The window statement used for [Stacks, Tag 0GEL] — a compact object of `D_QCoh(𝒪_X)` receives
nothing in high degrees into a bounded-above object, and nothing in low degrees into a
bounded-below one — is proved first, by the same induction; it is the part of
[Stacks, Tag 09M4] that is needed, and it is also the implication (1) ⟹ (2) of the two tags.

Everything is stated along a filter `l` on `ℤ` which is `atTop` (bounded above, `i ≫ 0`) or
`atBot` (bounded below, `i ≪ 0`), so that the two tags share one proof.

## Main results

* `Stacks.Duality.CompactBoundedness.window`: on a quasi-compact quasi-separated scheme, every
  compact object is eventually orthogonal to every object bounded along `l`.
* `Stacks.Duality.CompactBoundedness.detection`: on a quasi-compact quasi-separated scheme, an
  object eventually orthogonal to every compact object is bounded along `l`.

## Implementation notes

All derived categories are the locally small models
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, those of the compact generation theorem
`Stacks.Duality.QcqsGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory`, whose
gluing, lifting and base change statements are reused here.

## References

* [Stacks Project, Tag 0GEN](https://stacks.math.columbia.edu/tag/0GEN)
* [Stacks Project, Tag 0GEQ](https://stacks.math.columbia.edu/tag/0GEQ)
* [Stacks Project, Tag 0GEJ](https://stacks.math.columbia.edu/tag/0GEJ)
* [Stacks Project, Tag 0GEL](https://stacks.math.columbia.edu/tag/0GEL)
* [Stacks Project, Tag 09M4](https://stacks.math.columbia.edu/tag/09M4)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated Filter ZeroObject

universe w u₁ v₁ u

namespace Stacks.Duality.CompactBoundedness

/-! ### Boundedness along a filter -/

section Bdd

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- An object of `D(C)` is *bounded along `l`* if its cohomology vanishes in `l`-almost every
degree: for `l = atTop` this is boundedness above, for `l = atBot` boundedness below. -/
def Bdd (l : Filter ℤ) (M : DerivedCategory C) : Prop :=
  ∀ᶠ q in l, IsZero ((DerivedCategory.homologyFunctor C q).obj M)

variable {l : Filter ℤ}

/-- `atTop` and `atBot` are invariant under the translations of `ℤ`. -/
theorem tendsto_add (hl : l = atTop ∨ l = atBot) (k : ℤ) :
    Tendsto (fun i => i + k) l l := by
  rcases hl with rfl | rfl
  · exact tendsto_atTop_add_const_right _ k tendsto_id
  · exact tendsto_atBot_add_const_right _ k tendsto_id

/-- Boundedness along `l` is invariant under isomorphism. -/
theorem bdd_of_iso {M N : DerivedCategory C} (e : M ≅ N) (h : Bdd l M) : Bdd l N :=
  h.mono fun q hq => hq.of_iso ((DerivedCategory.homologyFunctor C q).mapIso e).symm

/-- A zero object is bounded along `l`. -/
theorem bdd_of_isZero {M : DerivedCategory C} (h : IsZero M) : Bdd l M :=
  Eventually.of_forall fun q => (DerivedCategory.homologyFunctor C q).map_isZero h

/-- For `l = atTop` or `l = atBot`, a shift of an object bounded along `l` is bounded along `l`. -/
theorem bdd_shift (hl : l = atTop ∨ l = atBot) {M : DerivedCategory C} (h : Bdd l M) (n : ℤ) :
    Bdd l (M⟦n⟧) :=
  ((tendsto_add hl n).eventually h).mono fun q hq =>
    hq.of_iso (((DerivedCategory.homologyFunctor C 0).shiftIso n q (q + n) (by omega)).app M)

/-- In a distinguished triangle, if the first and third objects are bounded along `l`, so is the
second. -/
theorem bdd_obj₂ (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (h₁ : Bdd l T.obj₁) (h₃ : Bdd l T.obj₃) : Bdd l T.obj₂ :=
  (h₁.and h₃).mono fun q ⟨a, c⟩ =>
    ((DerivedCategory.homologyFunctor C q).map_distinguished_exact T hT).isZero_X₂
      (a.eq_of_src _ _) (c.eq_of_tgt _ _)

/-- In a distinguished triangle, if the second and third objects are bounded along `l`, so is the
first. -/
theorem bdd_obj₁ (hl : l = atTop ∨ l = atBot) (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (h₂ : Bdd l T.obj₂) (h₃ : Bdd l T.obj₃) : Bdd l T.obj₁ :=
  bdd_obj₂ _ (inv_rot_of_distTriang T hT) (bdd_shift hl h₃ (-1)) h₂

/-- In a distinguished triangle, if the first and second objects are bounded along `l`, so is the
third. -/
theorem bdd_obj₃ (hl : l = atTop ∨ l = atBot) (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (h₁ : Bdd l T.obj₁) (h₂ : Bdd l T.obj₂) : Bdd l T.obj₃ :=
  bdd_obj₂ _ (rot_of_distTriang T hT) h₂ (bdd_shift hl h₁ 1)

/-- An object is bounded along `atTop` if and only if it is bounded above. -/
theorem bdd_atTop_iff (M : DerivedCategory C) : Bdd atTop M ↔ ∃ b : ℤ, M.IsLE b := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := eventually_atTop.1 h
    refine ⟨N, ?_⟩
    rw [DerivedCategory.isLE_iff]
    exact fun i hi => hN i hi.le
  · rintro ⟨b, hb⟩
    exact eventually_atTop.2 ⟨b + 1, fun i hi => DerivedCategory.isZero_of_isLE M b i (by omega)⟩

/-- An object is bounded along `atBot` if and only if it is bounded below. -/
theorem bdd_atBot_iff (M : DerivedCategory C) : Bdd atBot M ↔ ∃ b : ℤ, M.IsGE b := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := eventually_atBot.1 h
    refine ⟨N, ?_⟩
    rw [DerivedCategory.isGE_iff]
    exact fun i hi => hN i hi.le
  · rintro ⟨b, hb⟩
    exact eventually_atBot.2 ⟨b - 1, fun i hi => DerivedCategory.isZero_of_isGE M b i (by omega)⟩

end Bdd

/-! ### Boundedness on a scheme: restriction, locality, direct image -/

section Scheme

open Stacks.Duality.OpenImmersion Stacks.Duality.QcqsGeneration

variable {l : Filter ℤ}

/-- Restriction along an open immersion preserves boundedness, being exact. -/
theorem bdd_derivedRestrict {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    {M : DerivedCategory Y.Modules} (h : Bdd l M) : Bdd l ((derivedRestrict j).obj M) :=
  h.mono fun q hq => ((Scheme.Modules.restrictFunctor j).map_isZero hq).of_iso
    (((Scheme.Modules.restrictFunctor j).mapDerivedCategoryHomologyIso q).app M)

/-- A sheaf of modules vanishing on the two members of an open cover vanishes. -/
theorem isZero_of_isZero_restrictFunctor₂ {Y U V : Scheme.{u}} (jU : U ⟶ Y) (jV : V ⟶ Y)
    [IsOpenImmersion jU] [IsOpenImmersion jV]
    (hcov : ∀ y : Y, (∃ x, jU x = y) ∨ (∃ x, jV x = y)) {N : Y.Modules}
    (hU : IsZero ((Scheme.Modules.restrictFunctor jU).obj N))
    (hV : IsZero ((Scheme.Modules.restrictFunctor jV).obj N)) : IsZero N := by
  let Us : Bool → Scheme.{u} := fun b => cond b U V
  let js : ∀ b, Us b ⟶ Y := fun b => match b with
    | true => jU
    | false => jV
  have : ∀ b, IsOpenImmersion (js b) := fun b => by cases b <;> (dsimp [js]; infer_instance)
  have : IsIso (0 : (0 : Y.Modules) ⟶ N) := by
    refine isIso_of_isIso_restrictFunctor _ js (fun y => ?_) fun b => ?_
    · rcases hcov y with ⟨x, hx⟩ | ⟨x, hx⟩
      · exact ⟨true, x, hx⟩
      · exact ⟨false, x, hx⟩
    · refine isIso_of_source_target_iso_zero _
        ((Scheme.Modules.restrictFunctor (js b)).map_isZero (isZero_zero _)).isoZero ?_
      cases b
      · exact hV.isoZero
      · exact hU.isoZero
  exact (isZero_zero _).of_iso (asIso (0 : (0 : Y.Modules) ⟶ N)).symm

/-- Boundedness is local for a cover by two opens. -/
theorem bdd_of_bdd_derivedRestrict₂ {Y U V : Scheme.{u}} (jU : U ⟶ Y) (jV : V ⟶ Y)
    [IsOpenImmersion jU] [IsOpenImmersion jV]
    (hcov : ∀ y : Y, (∃ x, jU x = y) ∨ (∃ x, jV x = y)) {M : DerivedCategory Y.Modules}
    (hU : Bdd l ((derivedRestrict jU).obj M)) (hV : Bdd l ((derivedRestrict jV).obj M)) :
    Bdd l M :=
  (hU.and hV).mono fun q ⟨a, b⟩ => isZero_of_isZero_restrictFunctor₂ jU jV hcov
    (a.of_iso (((Scheme.Modules.restrictFunctor jU).mapDerivedCategoryHomologyIso q).app M).symm)
    (b.of_iso (((Scheme.Modules.restrictFunctor jV).mapDerivedCategoryHomologyIso q).app M).symm)

/-- **[Stacks, Tag 08D5]**: the derived direct image along a quasi-compact quasi-separated
morphism into a quasi-compact scheme preserves boundedness of objects with quasi-coherent
cohomology. Above, this is the uniform bound of part (2) of the tag; below it is left
t-exactness of a right derived functor. -/
theorem bdd_derivedPushforward (hl : l = atTop ∨ l = atBot) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y] {M : DerivedCategory X.Modules}
    (hM : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj M).IsQuasicoherent)
    (h : Bdd l M) : Bdd l ((Stacks.Duality.derivedPushforward f).obj M) := by
  rcases hl with rfl | rfl
  · obtain ⟨b, hb⟩ := (bdd_atTop_iff M).1 h
    obtain ⟨N, hN⟩ := Stacks.Duality.exists_isLE_derivedPushforward_obj_anyModel f
    exact (bdd_atTop_iff _).2 ⟨b + N, hN M hM b hb⟩
  · obtain ⟨b, hb⟩ := (bdd_atBot_iff M).1 h
    exact (bdd_atBot_iff _).2
      ⟨b, Stacks.DerivedFunctor.isGE_totalRightDerived_obj (Scheme.Modules.pushforward f) M b⟩

end Scheme

/-! ### Morphisms in `D_QCoh(𝒪_X)` -/

section QCoh

variable {Y : Scheme.{u}}

/-- The inclusion of `D_QCoh(𝒪_Y)` into `D(𝒪_Y)` is fully faithful and commutes with the shift,
so a group of morphisms out of a shift may be read in `D(𝒪_Y)`. -/
theorem subsingleton_shift_hom_iff (P M : Stacks.Duality.quasiCoherentDerivedCategory Y)
    (n : ℤ) : Subsingleton (P⟦n⟧ ⟶ M) ↔ Subsingleton (P.obj⟦n⟧ ⟶ M.obj) := by
  let D := DerivedCategoryB.derivedCategoryB (A := Y.Modules)
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf)
  exact (D.fullyFaithfulι.homEquiv (X := P⟦n⟧) (Y := M)).subsingleton_congr.trans
    (((D.ι.commShiftIso n).app P).homFromEquiv (Z := M.obj)).subsingleton_congr

/-- A zero object of `D(𝒪_Y)` underlies a zero object of `D_QCoh(𝒪_Y)`. -/
theorem isZero_of_isZero_obj {M : Stacks.Duality.quasiCoherentDerivedCategory Y}
    (h : IsZero M.obj) : IsZero M :=
  isZero_fullSubcategory_of_isZero_obj h

/-- A zero object of `D_QCoh(𝒪_Y)` underlies a zero object of `D(𝒪_Y)`. -/
private theorem isZero_obj_of_isZero {M : Stacks.Duality.quasiCoherentDerivedCategory Y}
    (h : IsZero M) : IsZero M.obj :=
  (DerivedCategoryB.derivedCategoryB (A := Y.Modules)
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι.map_isZero h

/-- In a distinguished triangle of `D_QCoh(𝒪_Y)`, if the first and second objects are bounded
along `l`, so is the third. -/
private theorem bdd_obj₃_of_distTriang {l : Filter ℤ} (hl : l = atTop ∨ l = atBot)
    (T : Triangle (Stacks.Duality.quasiCoherentDerivedCategory Y)) (hT : T ∈ distTriang _)
    (h₁ : Bdd l T.obj₁.obj) (h₂ : Bdd l T.obj₂.obj) : Bdd l T.obj₃.obj :=
  bdd_obj₃ hl (((DerivedCategoryB.derivedCategoryB (A := Y.Modules)
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι).mapTriangle.obj _)
    (((DerivedCategoryB.derivedCategoryB (A := Y.Modules)
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι).map_distinguished _ hT) h₁ h₂

/-- In a distinguished triangle of `D_QCoh(𝒪_Y)`, if the second and third objects are bounded
along `l`, so is the first. -/
private theorem bdd_obj₁_of_distTriang {l : Filter ℤ} (hl : l = atTop ∨ l = atBot)
    (T : Triangle (Stacks.Duality.quasiCoherentDerivedCategory Y)) (hT : T ∈ distTriang _)
    (h₂ : Bdd l T.obj₂.obj) (h₃ : Bdd l T.obj₃.obj) : Bdd l T.obj₁.obj :=
  bdd_obj₁ hl (((DerivedCategoryB.derivedCategoryB (A := Y.Modules)
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι).mapTriangle.obj _)
    (((DerivedCategoryB.derivedCategoryB (A := Y.Modules)
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι).map_distinguished _ hT) h₂ h₃

end QCoh

/-! ### The two statements proved by induction -/

section Statements

/-- **The window of a compact object.** On `Y`, every compact object `P` of `D_QCoh(𝒪_Y)` is
eventually orthogonal along `l` to every object of `D_QCoh(𝒪_Y)` bounded along `l`: for
`l = atTop`, `Hom(P⟦-i⟧, C) = 0` for `i ≫ 0` whenever `C` is bounded above. -/
def Window (Y : Scheme.{u}) (l : Filter ℤ) : Prop :=
  ∀ P : Stacks.Duality.quasiCoherentDerivedCategory Y, IsCompactObject.{u} P →
    ∀ C : Stacks.Duality.quasiCoherentDerivedCategory Y, Bdd l C.obj → EventuallyOrthogonal l P C

/-- **Detection of boundedness by the compact objects.** On `Y`, an object of `D_QCoh(𝒪_Y)`
which is eventually orthogonal along `l` to every compact object is bounded along `l`. -/
def Detection (Y : Scheme.{u}) (l : Filter ℤ) : Prop :=
  ∀ E : Stacks.Duality.quasiCoherentDerivedCategory Y,
    (∀ P : Stacks.Duality.quasiCoherentDerivedCategory Y, IsCompactObject.{u} P →
      EventuallyOrthogonal l P E) → Bdd l E.obj

/-- On a compactly generated `D_QCoh(𝒪_Y)` with a compact weak generator `G`, eventual
orthogonality to `E` passes from `G` to every compact object: the compact objects are the
triangulated envelope of `G` ([Stacks, Tag 09SR]), and eventual orthogonality propagates through
it ([Stacks, Tag 0ATH]). -/
theorem eventuallyOrthogonal_of_isCompactObject {Y : Scheme.{u}} {l : Filter ℤ}
    (hl : l = atTop ∨ l = atBot) (G : Stacks.Duality.quasiCoherentDerivedCategory Y)
    [IsCompactObject.{u} G] (hgen : (ObjectProperty.singleton G).IsWeakTriangulatedGenerator)
    (E : Stacks.Duality.quasiCoherentDerivedCategory Y) (hE : EventuallyOrthogonal l G E)
    (P : Stacks.Duality.quasiCoherentDerivedCategory Y) (hP : IsCompactObject.{u} P) :
    EventuallyOrthogonal l P E := by
  have h :=
    (isWeakTriangulatedGenerator_iff_triangEnvelope_eq_isCompactObject_and_isCompactlyGenerated
      G).1 hgen |>.1
  exact triangEnvelope_singleton_le_eventuallyOrthogonal (tendsto_add hl) G E hE P (by rwa [h])

end Statements

/-! ### The affine case of the window -/

section Affine

open Stacks.Koszul.Truncation Stacks.Duality.QcqsGeneration Stacks.Duality.OpenImmersion

variable (A : Type u) [CommRing A]

/-- The empty sequence in `A`. -/
abbrev emptySeq : Fin 0 → A := Fin.elim0

/-- The open complement of the empty sequence is the empty scheme. -/
instance : IsEmpty (openComplement (emptySeq A)).toScheme := by
  refine ⟨fun x => ?_⟩
  obtain ⟨y, hy⟩ := x
  rw [openComplement, TopologicalSpace.Opens.mem_iSup] at hy
  obtain ⟨i, -⟩ := hy
  exact i.elim0

/-- Every object of the derived category of an empty scheme is zero. -/
theorem isZero_of_isEmpty {Z : Scheme.{u}} [IsEmpty Z] (E : DerivedCategory Z.Modules) :
    IsZero E :=
  @isZero_of_isZero_derivedRestrict Z E Empty (fun i => i.elim) (fun i => i.elim)
    (fun i => i.elim) (fun y => (IsEmpty.false y).elim) (fun i => i.elim)

/-- The Koszul complex of the empty sequence, i.e. the structure sheaf, is a weak generator of
`D_QCoh(𝒪_{Spec A})`: this is the Koszul detection of [Stacks, Tag 09IR] for the empty sequence,
whose open complement is empty. -/
theorem isWeakTriangulatedGenerator_koszulQC_emptySeq :
    (ObjectProperty.singleton (koszulQC (emptySeq A))).IsWeakTriangulatedGenerator := by
  intro E hE
  rw [rightOrthogonal_shiftClosure_ofObj_iff] at hE
  have h' := (forall_hom_shift_eq_zero_iff _ _ _).1 (fun n g => hE PUnit.unit n g)
  refine isZero_of_isZero_obj (isZero_of_forall_hom_koszulObject_eq_zero (emptySeq A) E.obj E.2
    (isZero_of_isEmpty _) fun n g => ?_)
  have := h' n ((shiftFunctor _ n).map (koszulQC_obj_iso (emptySeq A)).hom ≫ g)
  rw [← cancel_epi ((shiftFunctor _ n).map (koszulQC_obj_iso (emptySeq A)).hom), this, comp_zero]

/-- The sheafified Koszul complex lives in non-positive degrees. -/
instance isLE_koszulObject {r : ℕ} (f : Fin r → A) : (koszulObject f).IsLE 0 := by
  have : (tilde.functor (CommRingCat.of A)).Faithful :=
    AlgebraicGeometry.tilde.fullyFaithfulFunctor.faithful
  have : CochainComplex.IsStrictlyLE (((tilde.functor (CommRingCat.of A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat)) 0 :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff _ _ 0).2 inferInstance
  infer_instance

/-- The Koszul complex of the empty sequence satisfies the window. -/
theorem eventuallyOrthogonal_koszulQC_emptySeq {l : Filter ℤ} (hl : l = atTop ∨ l = atBot)
    (C : Stacks.Duality.quasiCoherentDerivedCategory (Spec (CommRingCat.of A)))
    (hC : Bdd l C.obj) : EventuallyOrthogonal l (koszulQC (emptySeq A)) C := by
  have key : ∀ i : ℤ, Subsingleton ((koszulObject (emptySeq A))⟦-i⟧ ⟶ C.obj) →
      Subsingleton ((koszulQC (emptySeq A))⟦-i⟧ ⟶ C) := fun i h => by
    rw [subsingleton_shift_hom_iff]
    exact ⟨fun u v => (cancel_epi ((shiftFunctor _ (-i)).map
      (koszulQC_obj_iso (emptySeq A)).inv)).1 (Subsingleton.elim _ _)⟩
  rcases hl with rfl | rfl
  · obtain ⟨b, hb⟩ := (bdd_atTop_iff _).1 hC
    refine eventually_atTop.2 ⟨b + 1, fun i hi => key i ?_⟩
    exact subsingleton_hom_koszulObject_shift_of_isLE (emptySeq A) C.obj C.2 b (-i) hb
      (by push_cast; omega)
  · obtain ⟨b, hb⟩ := (bdd_atBot_iff _).1 hC
    refine eventually_atBot.2 ⟨b - 1, fun i hi => key i ⟨fun u v => ?_⟩⟩
    have : ((koszulObject (emptySeq A))⟦-i⟧).IsLE i :=
      DerivedCategory.TStructure.t.isLE_shift _ 0 (-i) i (by omega)
    rw [DerivedCategory.TStructure.t.zero_of_isLE_of_isGE u i b (by omega) inferInstance hb,
      DerivedCategory.TStructure.t.zero_of_isLE_of_isGE v i b (by omega) inferInstance hb]

/-- **The window on an affine scheme.** -/
theorem window_spec {l : Filter ℤ} (hl : l = atTop ∨ l = atBot) :
    Window (Spec (CommRingCat.of A)) l := by
  intro P hP C hC
  have := isCompactObject_koszulQC (emptySeq A)
  exact eventuallyOrthogonal_of_isCompactObject hl _
    (isWeakTriangulatedGenerator_koszulQC_emptySeq A) C
    (eventuallyOrthogonal_koszulQC_emptySeq A hl C hC) P hP

end Affine

/-! ### The induction principle over a finite affine cover -/

section Induction

open Stacks.Koszul.Truncation

/-- **Induction over a finite affine cover**: a property of schemes which holds for the empty
scheme, and which passes from a quasi-compact open `U` to `U ∪ Spec A` whenever the overlap is
`D(f₁) ∪ … ∪ D(f_r) ⊆ Spec A`, holds for every quasi-compact quasi-separated scheme. This is the
form of [Stacks, Tag 08DR] used for [Stacks, Tag 09IS]. -/
theorem induction_on_affineCover (P : Scheme.{u} → Prop)
    (hempty : ∀ Y : Scheme.{u}, IsEmpty Y → P Y)
    (hstep : ∀ (Y U : Scheme.{u}) [QuasiSeparatedSpace Y] [CompactSpace Y] [CompactSpace U]
      [QuasiSeparatedSpace U] (jU : U ⟶ Y) [IsOpenImmersion jU] (A : Type u) [CommRing A]
      (jV : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion jV] (r : ℕ) (f : Fin r → A)
      (iU : (openComplement f).toScheme ⟶ U) [IsOpenImmersion iU],
      IsPullback iU (openComplement f).ι jU jV →
      (∀ y : Y, (∃ x, jU x = y) ∨ (∃ x, jV x = y)) → P U → P Y)
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] : P X := by
  have hstep' : ∀ (Y : Scheme.{u}) [QuasiSeparatedSpace Y] [CompactSpace Y] (U : Y.Opens),
      IsCompact (U : Set Y) → ∀ (A : Type u) [CommRing A] (jV : Spec (CommRingCat.of A) ⟶ Y)
      [IsOpenImmersion jV], (∀ y : Y, y ∈ U ∨ (∃ x, jV x = y)) → P U.toScheme → P Y := by
    intro Y _ _ U hUc A _ jV _ hcov hU
    have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hUc
    have : QuasiSeparatedSpace U.toScheme := U.ι.isOpenEmbedding.quasiSeparatedSpace
    have hc := jV.isCompact_preimage hUc
    obtain ⟨s, hs⟩ :=
      Stacks.AlgebraicGeometry.InductionPrinciple.exists_finset_basicOpen_of_isCompact
        (isAffineOpen_top (Spec (CommRingCat.of A))) hc le_top
    let e := s.equivFin
    let f : Fin s.card → A := fun i => (Scheme.ΓSpecIso (CommRingCat.of A)).hom (e.symm i)
    have hW : jV ⁻¹ᵁ U = openComplement f := by
      rw [hs]
      refine le_antisymm (iSup₂_le fun g hg => ?_) (iSup_le fun i => ?_)
      · refine le_trans (le_of_eq ?_) (le_iSup _ (e ⟨g, hg⟩))
        congr 1
        simp [f]
      · refine le_trans (le_of_eq ?_)
          (le_iSup₂ (f := fun g _ => (Spec (CommRingCat.of A)).basicOpen g)
          (e.symm i).1 (e.symm i).2)
        congr 1
        simp [f]
    have key : ∀ (W : (Spec (CommRingCat.of A)).Opens), W = openComplement f →
        ∀ (iU : W.toScheme ⟶ U.toScheme) [IsOpenImmersion iU], IsPullback iU W.ι U.ι jV →
        P Y := by
      intro W hW' iU _ hsq
      subst hW'
      exact hstep Y U.toScheme U.ι A jV s.card f iU hsq (fun y => by
        rcases hcov y with hy | hy
        · exact Or.inl ⟨⟨y, hy⟩, rfl⟩
        · exact Or.inr hy) hU
    exact key _ hW (jV ∣_ U) (isPullback_morphismRestrict jV U)
  have hcover : ∀ (n : ℕ) (Y : Scheme.{u}) [QuasiSeparatedSpace Y] (V : Fin n → Y.Opens),
      (∀ i, IsAffineOpen (V i)) → (⨆ i, V i) = ⊤ → P Y := by
    intro n
    induction n with
    | zero =>
      intro Y _ V _ hcov
      refine hempty Y ⟨fun y => ?_⟩
      have hy : y ∈ (⊤ : Y.Opens) := trivial
      rw [← hcov] at hy
      simp at hy
    | succ n ih =>
      intro Y _ V hV hcov
      have hcomp : ∀ (m : ℕ) (W : Fin m → Y.Opens), (∀ i, IsAffineOpen (W i)) →
          IsCompact (((⨆ i, W i : Y.Opens)) : Set Y) := fun m W hW => by
        rw [TopologicalSpace.Opens.coe_iSup]
        exact isCompact_iUnion fun i => (hW i).isCompact
      have : CompactSpace Y := ⟨by
        have := hcomp _ V hV
        rwa [hcov, TopologicalSpace.Opens.coe_top] at this⟩
      let U : Y.Opens := ⨆ i : Fin n, V i.castSucc
      have hUc : IsCompact (U : Set Y) := hcomp _ _ fun i => hV _
      have : QuasiSeparatedSpace U.toScheme := U.ι.isOpenEmbedding.quasiSeparatedSpace
      have hIH := ih U.toScheme (fun i => U.ι ⁻¹ᵁ V i.castSucc)
        (fun i => (hV i.castSucc).preimage_of_isOpenImmersion U.ι (by
          rw [Scheme.Opens.opensRange_ι]
          exact le_iSup (fun i : Fin n => V i.castSucc) i))
        (by
          rw [← Scheme.Hom.preimage_iSup]
          exact Scheme.Opens.ι_preimage_self U)
      refine hstep' Y U hUc Γ(Y, V (Fin.last n)) (hV (Fin.last n)).fromSpec (fun y => ?_) hIH
      have hy : y ∈ (⊤ : Y.Opens) := trivial
      rw [← hcov, TopologicalSpace.Opens.mem_iSup] at hy
      obtain ⟨i, hi⟩ := hy
      refine Fin.lastCases
        (motive := fun i => y ∈ V i → y ∈ U ∨ ∃ x, (hV (Fin.last n)).fromSpec x = y)
        (fun h => Or.inr ?_) (fun j h => Or.inl ?_) i hi
      · have h' : y ∈ Set.range (hV (Fin.last n)).fromSpec := by
          rw [(hV (Fin.last n)).range_fromSpec]
          exact h
        exact h'
      · exact (TopologicalSpace.Opens.mem_iSup.mpr ⟨j, h⟩ : y ∈ U)
  obtain ⟨s, hs, hX⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (U := (⊤ : X.Opens))).mp (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ)
  let t := hs.toFinset
  let e := t.equivFin
  refine hcover t.card X (fun i => ((e.symm i).1 : X.Opens)) (fun i => (e.symm i).1.2) ?_
  rw [hX]
  refine le_antisymm (iSup_le fun i => ?_) (iSup₂_le fun W hW => ?_)
  · exact le_iSup₂ (f := fun (W : X.affineOpens) (_ : W ∈ s) => (W : X.Opens)) (e.symm i).1
      (hs.mem_toFinset.mp (e.symm i).2)
  · exact (le_iSup (fun i => ((e.symm i).1 : X.Opens))
      (e ⟨W, hs.mem_toFinset.mpr hW⟩)).trans' (by simp)

end Induction

/-! ### The inductive steps -/

section Step

open Stacks.Koszul.Truncation Stacks.Duality.QcqsGeneration Stacks.Duality.OpenImmersion

variable {Y : Scheme.{u}} [QuasiSeparatedSpace Y] [CompactSpace Y]
  {U : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U] (jU : U ⟶ Y) [IsOpenImmersion jU]
  {A : Type u} [CommRing A] (jV : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion jV]
  {r : ℕ} (f : Fin r → A) (iU : (openComplement f).toScheme ⟶ U) [IsOpenImmersion iU]
  (hsq : IsPullback iU (openComplement f).ι jU jV)
  (hcov : ∀ y : Y, (∃ x, jU x = y) ∨ (∃ x, jV x = y))

/-- The cone of the unit `M ⟶ Rj_*(M|_U)` of an open immersion `j` vanishes on `U`. -/
private theorem exists_distTriang_unit_isZero_restrict {Y U : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] [QuasiSeparatedSpace Y] [CompactSpace Y] [CompactSpace U]
    [QuasiSeparatedSpace U] (M : Stacks.Duality.quasiCoherentDerivedCategory Y) :
    ∃ (C : Stacks.Duality.quasiCoherentDerivedCategory Y)
      (π : _ ⟶ C) (δ : C ⟶ M⟦(1 : ℤ)⟧),
      Triangle.mk ((restrictedDerivedRestrictAdjunction j).unit.app M) π δ ∈ distTriang _ ∧
        IsZero ((restrictedDerivedRestrict j).obj C) := by
  let adj := restrictedDerivedRestrictAdjunction j
  obtain ⟨C, π, δ, hT⟩ := distinguished_cocone_triangle (adj.unit.app M)
  exact ⟨C, π, δ, hT, Triangle.isZero₃_of_isIso₁ _
    ((restrictedDerivedRestrict j).map_distinguished _ hT)
    (isIso_map_unit_of_isIso_counit adj M inferInstance)⟩

omit [CompactSpace U] [QuasiSeparatedSpace U] in
include hsq hcov in
/-- **An object of `D_QCoh(𝒪_Y)` vanishing on `U` comes from `Spec A`**: the unit
`N ⟶ Rj_{V,*}(N|_V)` is invertible. It is so on `Spec A` because `Rj_{V,*}` is fully faithful,
and on `U` both sides vanish, the target by base change to the overlap. -/
theorem isIso_unit_of_isZero_restrict' (N : Stacks.Duality.quasiCoherentDerivedCategory Y)
    (hN : IsZero ((restrictedDerivedRestrict jU).obj N)) :
    IsIso ((restrictedDerivedRestrictAdjunction jV).unit.app N) := by
  rw [isIso_restrictedDerivedRestrictAdjunction_unit_app_iff]
  have hNU : IsZero ((derivedRestrict jU).obj N.obj) := isZero_obj_of_isZero hN
  refine isIso_of_isIso_derivedRestrict₂ jU jV _ ?_ ?_ hcov
  · have : (Stacks.Duality.derivedPushforward iU).IsRightAdjoint := inferInstance
    refine isIso_of_source_target_iso_zero _ hNU.isoZero ?_
    exact baseChangeIso jV (openComplement f).ι jU iU hsq.flip _ ≪≫
      ((Stacks.Duality.derivedPushforward iU).map_isZero
        (isZero_derivedRestrict_comp_of_isZero (openComplement f).ι iU jV jU hsq.w.symm
          hNU)).isoZero
  · exact isIso_map_unit_of_isIso_counit (derivedRestrictPushforwardAdjunction jV) N.obj
      inferInstance

include hsq hcov in
/-- **The inductive step of the window.** If compact objects of `D_QCoh(𝒪_U)` satisfy the
window, so do those of `D_QCoh(𝒪_Y)`. For a compact `P` and a bounded `M`, the triangle
`M ⟶ Rj_{U,*}(M|_U) ⟶ C` has `Hom(P⟦-i⟧, Rj_{U,*}(M|_U)) = Hom((P|_U)⟦-i⟧, M|_U)`, controlled
on `U`, and `C ≅ Rj_{V,*}(C|_V)` bounded, controlled on the affine `Spec A`. -/
theorem window_of_step {l : Filter ℤ} (hl : l = atTop ∨ l = atBot) (hU : Window U l) :
    Window Y l := by
  let adjU := restrictedDerivedRestrictAdjunction jU
  let adjV := restrictedDerivedRestrictAdjunction jV
  let : (Stacks.Duality.quasiCoherentDerivedPushforward jU
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)).CommShift ℤ :=
    adjU.rightAdjointCommShift ℤ
  let : adjU.CommShift ℤ := adjU.commShift_of_leftAdjoint ℤ
  let : (Stacks.Duality.quasiCoherentDerivedPushforward jV
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jV)).CommShift ℤ :=
    adjV.rightAdjointCommShift ℤ
  let : adjV.CommShift ℤ := adjV.commShift_of_leftAdjoint ℤ
  let : adjV.IsTriangulated := Adjunction.IsTriangulated.mk' adjV
  have := adjV.isTriangulated_rightAdjoint
  have : (Stacks.Duality.quasiCoherentDerivedPushforward jU
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)).Additive :=
    adjU.right_adjoint_additive
  have : (Stacks.Duality.quasiCoherentDerivedPushforward jV
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jV)).Additive :=
    adjV.right_adjoint_additive
  have : ∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward jU
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)) :=
    preservesColimitsOfShape_discrete_restrictedDerivedPushforward jU
  have : ∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward jV
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jV)) :=
    preservesColimitsOfShape_discrete_restrictedDerivedPushforward jV
  intro P hP M hM
  obtain ⟨C, π, δ, hT, hCU⟩ := exists_distTriang_unit_isZero_restrict jU M
  have hMU : Bdd l ((restrictedDerivedRestrict jU).obj M).obj := bdd_derivedRestrict jU hM
  have hC : Bdd l C.obj :=
    bdd_obj₃_of_distTriang hl _ hT hM
      (bdd_derivedPushforward hl jU ((restrictedDerivedRestrict jU).obj M).2 hMU)
  have : IsIso (adjV.unit.app C) := isIso_unit_of_isZero_restrict' jU jV f iU hsq hcov C hCU
  have h2 : EventuallyOrthogonal l P C :=
    eventuallyOrthogonal_of_iso_target (asIso (adjV.unit.app C)).symm
      ((eventuallyOrthogonal_leftAdjoint_iff adjV P _).1
        (window_spec A hl _ (isCompactObject_map_of_adjunction adjV hP) _
          (bdd_derivedRestrict jV hC)))
  exact eventuallyOrthogonal_obj₂_target _ (inv_rot_of_distTriang _ hT)
    (eventuallyOrthogonal_shift_target (tendsto_add hl) h2 (-1))
    ((eventuallyOrthogonal_leftAdjoint_iff adjU P _).1
      (hU _ (isCompactObject_map_of_adjunction adjU hP) _ hMU))

end Step

/-! ### The window -/

/-- **The window of a compact object of `D_QCoh(𝒪_X)`**, for `X` quasi-compact and
quasi-separated: if `C` is bounded above (resp. below), then `Hom(P⟦-i⟧, C) = 0` for `i ≫ 0`
(resp. `i ≪ 0`) for every compact object `P`. This is the part of [Stacks, Tag 09M4] used for
[Stacks, Tags 0GEL and 0GEM]. -/
theorem window {l : Filter ℤ} (hl : l = atTop ∨ l = atBot) (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] : Window X l := by
  refine induction_on_affineCover (fun Y => Window Y l) (fun Y hY P _ M _ => ?_)
    (fun Y U _ _ _ _ jU _ A _ jV _ r f iU _ hsq hcov hU =>
      window_of_step jU jV f iU hsq hcov hl hU) X
  have := hY
  exact eventuallyOrthogonal_of_isZero_target (isZero_of_isZero_obj (isZero_of_isEmpty M.obj))

section Step2

open Stacks.Koszul.Truncation Stacks.Duality.QcqsGeneration Stacks.Duality.OpenImmersion

variable {Y : Scheme.{u}} [QuasiSeparatedSpace Y] [CompactSpace Y]
  {U : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U] (jU : U ⟶ Y) [IsOpenImmersion jU]
  {A : Type u} [CommRing A] (jV : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion jV]
  {r : ℕ} (f : Fin r → A) (iU : (openComplement f).toScheme ⟶ U) [IsOpenImmersion iU]
  (hsq : IsPullback iU (openComplement f).ι jU jV)
  (hcov : ∀ y : Y, (∃ x, jU x = y) ∨ (∃ x, jV x = y))

include hsq hcov in
/-- **The inductive step of the detection of boundedness.** Suppose that on `U` an object of
`D_QCoh(𝒪_U)` eventually orthogonal to every compact object is bounded. Then the same holds on
`Y`. This is the inductive step in the proof of [Stacks, Tags 0GEN and 0GEQ]. -/
theorem detection_of_step {l : Filter ℤ} (hl : l = atTop ∨ l = atBot) (hU : Detection U l) :
    Detection Y l := by
  let adjU := restrictedDerivedRestrictAdjunction jU
  let adjV := restrictedDerivedRestrictAdjunction jV
  let adjU' := restrictedDerivedRestrictAdjunction iU
  let adjV' := restrictedDerivedRestrictAdjunction (openComplement f).ι
  let : (Stacks.Duality.quasiCoherentDerivedPushforward jU
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)).CommShift ℤ :=
    adjU.rightAdjointCommShift ℤ
  let : adjU.CommShift ℤ := adjU.commShift_of_leftAdjoint ℤ
  let : (Stacks.Duality.quasiCoherentDerivedPushforward jV
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jV)).CommShift ℤ :=
    adjV.rightAdjointCommShift ℤ
  let : adjV.CommShift ℤ := adjV.commShift_of_leftAdjoint ℤ
  let : adjV.IsTriangulated := Adjunction.IsTriangulated.mk' adjV
  have := adjV.isTriangulated_rightAdjoint
  have : PreservesBinaryBiproducts (restrictedDerivedRestrict iU) :=
    have := adjU'.leftAdjoint_preservesColimits
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (Stacks.Duality.quasiCoherentDerivedPushforward jU
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)).Additive :=
    adjU.right_adjoint_additive
  have : (Stacks.Duality.quasiCoherentDerivedPushforward jV
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jV)).Additive :=
    adjV.right_adjoint_additive
  have : (Stacks.Duality.quasiCoherentDerivedPushforward iU
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs iU)).Additive :=
    adjU'.right_adjoint_additive
  have : ∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward jU
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)) :=
    preservesColimitsOfShape_discrete_restrictedDerivedPushforward jU
  have : ∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward jV
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jV)) :=
    preservesColimitsOfShape_discrete_restrictedDerivedPushforward jV
  have : ∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward iU
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs iU)) :=
    preservesColimitsOfShape_discrete_restrictedDerivedPushforward iU
  let βVU : ∀ A' : Stacks.Duality.quasiCoherentDerivedCategory U,
      (restrictedDerivedRestrict jV).obj ((Stacks.Duality.quasiCoherentDerivedPushforward jU
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)).obj A') ≅
      (Stacks.Duality.quasiCoherentDerivedPushforward (openComplement f).ι
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs
          (openComplement f).ι)).obj ((restrictedDerivedRestrict iU).obj A') := fun A' =>
    (DerivedCategoryB.derivedCategoryB (A := Spec (CommRingCat.of A) |>.Modules)
      (SheafOfModules.isQuasicoherent
        (Spec (CommRingCat.of A)).ringCatSheaf)).fullyFaithfulι.preimageIso
      (baseChangeIso jU iU jV (openComplement f).ι hsq A'.obj)
  let βUV : ∀ Q' : Stacks.Duality.quasiCoherentDerivedCategory (Spec (CommRingCat.of A)),
      (restrictedDerivedRestrict jU).obj ((Stacks.Duality.quasiCoherentDerivedPushforward jV
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jV)).obj Q') ≅
      (Stacks.Duality.quasiCoherentDerivedPushforward iU
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs iU)).obj
          ((restrictedDerivedRestrict (openComplement f).ι).obj Q') := fun Q' =>
    (DerivedCategoryB.derivedCategoryB (A := U.Modules)
      (SheafOfModules.isQuasicoherent U.ringCatSheaf)).fullyFaithfulι.preimageIso
      (baseChangeIso jV (openComplement f).ι jU iU hsq.flip Q'.obj)
  have hker : ∀ N : Stacks.Duality.quasiCoherentDerivedCategory Y,
      IsZero ((restrictedDerivedRestrict jV).obj N) → IsIso (adjU.unit.app N) :=
    fun N hN => isIso_unit_of_isZero_restrict jU jV f iU hsq hcov N hN
  intro E hE
  obtain ⟨K', hK'U, hK'V⟩ := exists_glue adjU adjV adjV' βVU βUV 0 (koszulQC f)
    (((restrictedDerivedRestrict iU).map_isZero (isZero_zero _)).iso
      (isZero_restrictedDerivedRestrict_koszulQC f))
  have hK'U0 : IsZero ((restrictedDerivedRestrict jU).obj K') :=
    (isZero_zero _).of_iso hK'U.some
  have hK'c : IsCompactObject.{u} K' :=
    isCompactObject_of_isCompactObject_restrict adjU adjV hker K'
      (isCompactObject_of_iso hK'U.some
        (isCompactObject_zero' (T := Stacks.Duality.quasiCoherentDerivedCategory U)))
      (isCompactObject_of_iso hK'V.some (isCompactObject_koszulQC f))
  have h1 : EventuallyOrthogonal l (koszulQC f) ((restrictedDerivedRestrict jV).obj E) := by
    refine (hE K' hK'c).mono fun i hi => ⟨fun a b => ?_⟩
    suffices hz : ∀ g : (koszulQC f)⟦-i⟧ ⟶ (restrictedDerivedRestrict jV).obj E, g = 0 from
      (hz a).trans (hz b).symm
    intro g
    obtain ⟨N, π, δ, hT, hNV⟩ := exists_distTriang_unit_isZero_restrict jV E
    have hK'n : IsZero ((restrictedDerivedRestrict jU).obj (K'⟦-i⟧)) :=
      ((shiftFunctor _ (-i)).map_isZero hK'U0).of_iso
        (((restrictedDerivedRestrict jU).commShiftIso (-i)).app K')
    let g₁ : (restrictedDerivedRestrict jV).obj (K'⟦-i⟧) ⟶ (restrictedDerivedRestrict jV).obj E :=
      ((restrictedDerivedRestrict jV).commShiftIso (-i)).hom.app K' ≫
        (shiftFunctor _ (-i)).map hK'V.some.hom ≫ g
    have hπ : adjV.homEquiv _ _ g₁ ≫ π = 0 :=
      eq_zero_of_isZero_obj_of_isIso_unit adjU hK'n (hker N hNV) _
    obtain ⟨h, hh⟩ := Triangle.coyoneda_exact₂ _ hT _ hπ
    have hh0 : h = 0 := @Subsingleton.elim _ hi _ _
    have hg₁ : g₁ = 0 := by
      rw [← (adjV.homEquiv _ _).symm_apply_apply g₁, hh, hh0, zero_comp,
        Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]
    have : g = (shiftFunctor _ (-i)).map hK'V.some.inv ≫
        ((restrictedDerivedRestrict jV).commShiftIso (-i)).inv.app K' ≫ g₁ := by
      simp [g₁, ← Functor.map_comp_assoc]
    rw [this, hg₁, comp_zero, comp_zero]
  obtain ⟨C, g₂, g₃, hT, hCU⟩ := exists_distTriang_unit_isZero_restrict jU E
  have hR : EventuallyOrthogonal l (koszulQC f)
      ((restrictedDerivedRestrict jV).obj ((Stacks.Duality.quasiCoherentDerivedPushforward jU
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)).obj
          ((restrictedDerivedRestrict jU).obj E))) := by
    have hE2 : ((ObjectProperty.singleton (koszulQC f)).shiftClosure ℤ).rightOrthogonal
        ((restrictedDerivedRestrict jV).obj ((Stacks.Duality.quasiCoherentDerivedPushforward jU
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)).obj
            ((restrictedDerivedRestrict jU).obj E))) :=
      ObjectProperty.prop_of_iso _ (βVU _).symm
        (rightOrthogonal_shiftClosure_singleton_rightAdjoint_obj adjV'
          (isZero_restrictedDerivedRestrict_koszulQC f) _)
    rw [rightOrthogonal_shiftClosure_ofObj_iff] at hE2
    exact Eventually.of_forall fun i =>
      ⟨fun a b => (hE2 PUnit.unit (-i) a).trans (hE2 PUnit.unit (-i) b).symm⟩
  have hCVo : EventuallyOrthogonal l (koszulQC f) ((restrictedDerivedRestrict jV).obj C) :=
    eventuallyOrthogonal_obj₃_target _ ((restrictedDerivedRestrict jV).map_distinguished _ hT) hR
      (eventuallyOrthogonal_shift_target (tendsto_add hl) h1 1)
  have hres : IsZero ((derivedRestrict (openComplement f).ι).obj
      ((restrictedDerivedRestrict jV).obj C).obj) :=
    isZero_derivedRestrict_comp_of_isZero (openComplement f).ι iU jV jU hsq.w.symm
      (isZero_obj_of_isZero hCU)
  have hCVb : Bdd l ((restrictedDerivedRestrict jV).obj C).obj := by
    refine hCVo.mono fun q hq => isZero_homology_of_forall_hom_koszulObject_eq_zero f _
      ((restrictedDerivedRestrict jV).obj C).2 hres q fun g => ?_
    rw [subsingleton_shift_hom_iff] at hq
    rw [← cancel_epi ((shiftFunctor _ (-q)).map (koszulQC_obj_iso f).hom),
      Subsingleton.elim ((shiftFunctor _ (-q)).map (koszulQC_obj_iso f).hom ≫ g) 0, comp_zero]
  have hCb : Bdd l C.obj :=
    bdd_of_bdd_derivedRestrict₂ jU jV hcov
      (bdd_of_isZero (isZero_obj_of_isZero hCU)) hCVb
  have hEU : ∀ P : Stacks.Duality.quasiCoherentDerivedCategory U, IsCompactObject.{u} P →
      EventuallyOrthogonal l P ((restrictedDerivedRestrict jU).obj E) := by
    intro P hP
    obtain ⟨Q, hQc, ⟨hQ⟩⟩ := exists_isCompactObject_restrict_iso_biprod_shift f
      ((restrictedDerivedRestrict iU).obj P) (isCompactObject_map_of_adjunction adjU' hP)
    let φ : (restrictedDerivedRestrict iU).obj (P ⊞ P⟦(1 : ℤ)⟧) ≅
        (restrictedDerivedRestrict (openComplement f).ι).obj Q :=
      (restrictedDerivedRestrict iU).mapBiprod _ _ ≪≫
        biprod.mapIso (Iso.refl _) (((restrictedDerivedRestrict iU).commShiftIso (1 : ℤ)).app _) ≪≫
        hQ.symm
    obtain ⟨R, ⟨hRU⟩, ⟨hRV⟩⟩ := exists_glue adjU adjV adjV' βVU βUV (P ⊞ P⟦(1 : ℤ)⟧) Q φ
    have hRc : IsCompactObject.{u} R :=
      isCompactObject_of_isCompactObject_restrict adjU adjV hker R
        (isCompactObject_of_iso hRU (isCompactObject_biprod hP (isCompactObject_shift hP 1)))
        (isCompactObject_of_iso hRV hQc)
    exact eventuallyOrthogonal_of_biprod_left (eventuallyOrthogonal_of_iso_source hRU
      ((eventuallyOrthogonal_leftAdjoint_iff adjU R _).2
        (eventuallyOrthogonal_obj₂_target _ hT (hE R hRc) (window hl Y R hRc C hCb))))
  have hRb : Bdd l ((Stacks.Duality.quasiCoherentDerivedPushforward jU
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)).obj
        ((restrictedDerivedRestrict jU).obj E)).obj :=
    bdd_derivedPushforward hl jU ((restrictedDerivedRestrict jU).obj E).2 (hU _ hEU)
  exact bdd_obj₁_of_distTriang hl _ hT hRb hCb

end Step2

/-- **Boundedness in `D_QCoh(𝒪_X)` is detected by the compact objects**, for `X` quasi-compact and
quasi-separated: an object `E` of `D_QCoh(𝒪_X)` such that, for every compact object `P`, the
groups `Hom(P⟦-i⟧, E)` vanish for `i ≫ 0` (resp. `i ≪ 0`), is bounded above (resp. below). This
is the implication from condition (7)(a) to condition (1) of [Stacks, Tags 0GEN and 0GEQ]. -/
theorem detection {l : Filter ℤ} (hl : l = atTop ∨ l = atBot) (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] : Detection X l := by
  refine induction_on_affineCover (fun Y => Detection Y l) (fun Y hY E _ => ?_)
    (fun Y U _ _ _ _ jU _ A _ jV _ r f iU _ hsq hcov hU =>
      detection_of_step jU jV f iU hsq hcov hl hU) X
  have := hY
  exact bdd_of_isZero (isZero_of_isEmpty E.obj)

end Stacks.Duality.CompactBoundedness

end
