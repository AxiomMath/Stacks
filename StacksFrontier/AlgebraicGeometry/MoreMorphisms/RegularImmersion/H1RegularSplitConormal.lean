module

public import StacksFrontier.AlgebraicGeometry.Conormal.SplitSequence
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.ConormalSequence
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.NoetherianSplitConormal
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute

/-!
# The split exact conormal sequence of an H1-regular immersion

For immersions `Z --i--→ Y --j--→ X` with `i` an `H1`-regular immersion the conormal sequence
`0 ⟶ i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0` is short exact and splits on a neighbourhood of
every point of `Z`.  This file records that conclusion as
`Stacks.AlgebraicGeometry.IsSplitExactConormalSequence`, whose local splitting is phrased for the
open-subscheme restriction `AlgebraicGeometry.Scheme.Modules.restrictFunctor` rather than for the
slice restriction `SheafOfModules.over` in which it is proved, and deduces the implications
`(2) ⇒ (3)`, `(2) ⇒ (1)` and `(1) ⇒ (3)` of Stacks tag 0690 and the three-way equivalence
itself.

## Main results

* `RegularIdealSheaf.isSplitExactConormalSequence_of_isH1RegularImmersion`: the conormal
  sequence of an `H1`-regular immersion is exact and locally split.
* `RegularIdealSheaf.exists_opens_isSplitExactConormalSequence_of_split`: `(2) ⇒ (3)` of Stacks
  tag 0690.
* `RegularIdealSheaf.exists_opens_isRegularImmersion_of_factors_of_split`: `(2) ⇒ (1)` of Stacks
  tag 0690.
* `RegularIdealSheaf.exists_opens_isSplitExactConormalSequence_of_factors`: `(1) ⇒ (3)` of Stacks
  tag 0690.
* `RegularIdealSheaf.tfae_isRegularImmersion_near`: the equivalence of the three conditions of
  Stacks tag 0690.

## Implementation notes

The two restrictions of a sheaf of modules to an open `V` — the slice restriction to `Over V`
and the restriction to the open subscheme `V` — agree by
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`, and a retraction crosses that natural
isomorphism by conjugation.

"Regular immersion in a neighbourhood of a point" is spelled as in Stacks tag 069E, by an open
subscheme of the source through which the immersion is restricted, so splitness of the conormal
sequence in a neighbourhood of `z` is splitness for the pair `(W.ι ≫ i, j)` on an open `W`
containing `z`.

## References

* [Stacks Project, Lemma 31.22.6 (Tag 063N)](https://stacks.math.columbia.edu/tag/063N)
* [Stacks Project, Lemma 31.22.9 (Tag 0690)](https://stacks.math.columbia.edu/tag/0690)
* [Stacks Project, Lemma 29.32.5 (Tag 062S)](https://stacks.math.columbia.edu/tag/062S)
* [Stacks Project, Lemma 31.21.3 (Tag 063K)](https://stacks.math.columbia.edu/tag/063K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

variable {Z Y X : Scheme.{u}}

/-! ### Transporting a retraction between the two restrictions to an open -/

/-- **A retraction crosses a natural isomorphism of functors by conjugation.**  If `α : F ≅ G`
and `F.map f` admits the retraction `r`, then `G.map f` admits the retraction obtained by
conjugating `r` with `α`. -/
private theorem natIso_retraction {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (α : F ≅ G) {A B : C} (f : A ⟶ B) (r : F.obj B ⟶ F.obj A) (hr : F.map f ≫ r = 𝟙 _) :
    G.map f ≫ (α.inv.app B ≫ r ≫ α.hom.app A) = 𝟙 _ := by
  rw [← Category.assoc, α.inv.naturality f, Category.assoc, ← Category.assoc (F.map f), hr,
    Category.id_comp]
  simp

/-- **A retraction of `F.map f` gives one of `G.map f` whenever `F ⋙ K ≅ G`.**  The retraction
is carried through `K` and then conjugated with the isomorphism. -/
private theorem exists_comp_natIso_retraction {C D E : Type*} [Category C] [Category D]
    [Category E] (F : C ⥤ D) (K : D ⥤ E) {G : C ⥤ E} (α : F ⋙ K ≅ G) {A B : C} (f : A ⟶ B)
    (r : F.obj B ⟶ F.obj A) (hr : F.map f ≫ r = 𝟙 _) :
    ∃ r' : G.obj B ⟶ G.obj A, G.map f ≫ r' = 𝟙 _ := by
  refine ⟨α.inv.app B ≫ K.map r ≫ α.hom.app A, natIso_retraction α f (K.map r) ?_⟩
  show K.map (F.map f) ≫ K.map r = 𝟙 _
  rw [← K.map_comp, hr, K.map_id]

/-- **A retraction of the slice restriction of a map gives one of its open-subscheme
restriction.**  The two restrictions of a sheaf of `𝒪_Z`-modules to an open `V` agree by
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`. -/
theorem exists_retraction_restrictFunctor_of_over (V : Z.Opens) {M N : Z.Modules} (f : M ⟶ N)
    (r : (_root_.SheafOfModules.overFunctor Z.ringCatSheaf V).obj N ⟶
      (_root_.SheafOfModules.overFunctor Z.ringCatSheaf V).obj M)
    (hr : (_root_.SheafOfModules.overFunctor Z.ringCatSheaf V).map f ≫ r = 𝟙 _) :
    ∃ r' : (Scheme.Modules.restrictFunctor V.ι).obj N ⟶
        (Scheme.Modules.restrictFunctor V.ι).obj M,
      (Scheme.Modules.restrictFunctor V.ι).map f ≫ r' = 𝟙 _ :=
  exists_comp_natIso_retraction _ _ (Scheme.Modules.overFunctorEquiv V) f r hr

/-! ### The conormal sequence of an H1-regular immersion -/

/-- **The conormal sequence of an `H1`-regular immersion is exact and locally split.**  For
immersions `Z --i--→ Y --j--→ X` with `i` an `H1`-regular immersion the sequence
`0 ⟶ i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0` is short exact and its left-hand map admits a
retraction on a neighbourhood of every point of `Z`. -/
@[ega "IV 16.9.13" "more general"]
theorem isSplitExactConormalSequence_of_isH1RegularImmersion (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] (hi : IsH1RegularImmersion i) :
    IsSplitExactConormalSequence i j where
  comp_eq_zero := Stacks.Immersion.conormalSequence_comp_zero i j
  shortExact := conormalSequence_shortExact i j hi
  locallySplit z := by
    obtain ⟨V, hzV, ⟨σ⟩⟩ := conormalSequence_locallySplit i j hi z
    obtain ⟨r, hr⟩ :=
      exists_retraction_restrictFunctor_of_over V (conormalSequenceLeftMap i j) σ.r σ.f_r
    exact ⟨V, hzV, r, hr⟩

/-- **The conormal sequence of a regular immersion is exact and locally split.**  A regular
immersion is `H1`-regular, so the sequence `0 ⟶ i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0` is short
exact and splits on a neighbourhood of every point of `Z`. -/
@[ega "IV 16.9.13" "more general"]
theorem isSplitExactConormalSequence_of_isRegularImmersion (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] (hi : IsRegularImmersion i) :
    IsSplitExactConormalSequence i j :=
  isSplitExactConormalSequence_of_isH1RegularImmersion i j
    (isH1RegularImmersion_of_isKoszulRegularImmersion i
      (isKoszulRegularImmersion_of_isRegularImmersion i hi))

/-- **An immersion regular near a point has split exact conormal sequence near that point.**
On an open `W` containing `z` over which `i` restricts to a regular immersion, the conormal
sequence of the pair `(W.ι ≫ i, j)` is exact and locally split. -/
theorem exists_opens_isSplitExactConormalSequence_near (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i]
    [IsImmersion j] (z : Z) (hi : ∃ W : Z.Opens, z ∈ W ∧ IsRegularImmersion (W.ι ≫ i)) :
    ∃ W : Z.Opens, z ∈ W ∧ IsSplitExactConormalSequence (W.ι ≫ i) j := by
  obtain ⟨W, hzW, hreg⟩ := hi
  exact ⟨W, hzW, isSplitExactConormalSequence_of_isRegularImmersion (W.ι ≫ i) j hreg⟩

/-! ### The remaining implications of Stacks tag 0690 -/

/-- **Stacks tag 0690, `(2) ⇒ (3)`.**  Let `i : Z ⟶ Y` and `j : Y ⟶ X` be immersions of schemes
and let `z : Z`.  If `i` and `i ≫ j` are regular immersions in a neighbourhood of `z`, then
`i ≫ j` is a regular immersion in a neighbourhood of `z` and the conormal sequence
`0 ⟶ i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0` is exact and locally split in a neighbourhood
of `z`. -/
@[stacks 0690 "(2) => (3)", ega "IV 19.1.5" "(iv)", sga "6 VII 4.2" "partial"]
theorem exists_opens_isSplitExactConormalSequence_of_split (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] (z : Z)
    (hi : ∃ W : Z.Opens, z ∈ W ∧ IsRegularImmersion (W.ι ≫ i))
    (hji : ∃ U : Z.Opens, z ∈ U ∧ IsRegularImmersion (U.ι ≫ (i ≫ j))) :
    (∃ U : Z.Opens, z ∈ U ∧ IsRegularImmersion (U.ι ≫ (i ≫ j))) ∧
      ∃ W : Z.Opens, z ∈ W ∧ IsSplitExactConormalSequence (W.ι ≫ i) j :=
  ⟨hji, exists_opens_isSplitExactConormalSequence_near i j z hi⟩

/-- **Regularity of an immersion restricted to an open passes to any open immersion landing in
that open.**  Regularity of an immersion into a locally Noetherian scheme is read on the kernels
of its maps of local rings, and those do not change along an open immersion on the source. -/
private theorem isRegularImmersion_comp_of_isOpenImmersion_le {Z' : Scheme.{u}} (a : Z' ⟶ Z)
    [IsOpenImmersion a] (f : Z ⟶ X) [IsImmersion f] [IsImmersion (a ≫ f)]
    [IsLocallyNoetherian X] {U : Z.Opens} (hle : ∀ w : Z', a.base w ∈ U)
    (h : IsRegularImmersion (U.ι ≫ f)) : IsRegularImmersion (a ≫ f) := by
  refine isRegularImmersion_of_exists_isRegular_ker_stalkMap (a ≫ f) fun w => ?_
  obtain ⟨rs, hrs, hgen⟩ :=
    exists_isRegular_ker_stalkMap_of_isRegularImmersion (U.ι ≫ f) h ⟨a.base w, hle w⟩
  exact ⟨rs, hrs, hgen.trans ((ker_stalkMap_comp_isOpenImmersion U.ι f ⟨a.base w, hle w⟩).trans
    (ker_stalkMap_comp_isOpenImmersion a f w).symm)⟩

/-- **Stacks tag 0690, `(2) ⇒ (1)`.**  Let `i : Z ⟶ Y` and `j : Y ⟶ X` be immersions of schemes
with `X` locally Noetherian and let `z : Z`.  If `i` and `i ≫ j` are regular immersions in a
neighbourhood of `z`, then `i` is a regular immersion in a neighbourhood of `z` and `j` is one in
a neighbourhood of `i z`. -/
@[stacks 0690 "(2) => (1)"]
theorem exists_opens_isRegularImmersion_of_factors_of_split (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] [IsLocallyNoetherian X] (z : Z)
    (hi : ∃ W : Z.Opens, z ∈ W ∧ IsRegularImmersion (W.ι ≫ i))
    (hji : ∃ U : Z.Opens, z ∈ U ∧ IsRegularImmersion (U.ι ≫ (i ≫ j))) :
    (∃ W : Z.Opens, z ∈ W ∧ IsRegularImmersion (W.ι ≫ i)) ∧
      ∃ V : Y.Opens, i.base z ∈ V ∧ IsRegularImmersion (V.ι ≫ j) := by
  obtain ⟨W, hzW, hregW⟩ := hi
  obtain ⟨U, hzU, hregU⟩ := hji
  have hY : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian j
  have hzW' : z ∈ W ⊓ U := ⟨hzW, hzU⟩
  have hregW' : IsRegularImmersion ((W ⊓ U).ι ≫ i) :=
    isRegularImmersion_comp_of_isOpenImmersion_le (W ⊓ U).ι i (fun w => w.2.1) hregW
  have hji' : ∃ U' : (W ⊓ U).toScheme.Opens, (⟨z, hzW'⟩ : (W ⊓ U).toScheme) ∈ U' ∧
      IsRegularImmersion (U'.ι ≫ (((W ⊓ U).ι ≫ i) ≫ j)) :=
    ⟨⊤, trivial, isRegularImmersion_comp_of_isOpenImmersion_le
      ((⊤ : (W ⊓ U).toScheme.Opens).ι ≫ (W ⊓ U).ι) (i ≫ j) (fun w => w.1.2.2) hregU⟩
  exact ⟨⟨W, hzW, hregW⟩, (exists_opens_isRegularImmersion_of_split ((W ⊓ U).ι ≫ i) j
    (isSplitExactConormalSequence_of_isRegularImmersion ((W ⊓ U).ι ≫ i) j hregW')
    ⟨z, hzW'⟩ hji').2⟩

/-- **Stacks tag 0690, `(1) ⇒ (3)`.**  Let `i : Z ⟶ Y` and `j : Y ⟶ X` be immersions of schemes
with `X` locally Noetherian and let `z : Z`.  If `i` is a regular immersion in a neighbourhood of
`z` and `j` is one in a neighbourhood of `i z`, then `i ≫ j` is a regular immersion in a
neighbourhood of `z` and the conormal sequence of the pair is exact and locally split in a
neighbourhood of `z`. -/
@[stacks 0690 "(1) => (3)",
  ega "IV 19.1.5" "partial",
  sga "6 VII 4.2" "partial",
  sga "6 VIII 1.3" "clause (i), special case"]
theorem exists_opens_isSplitExactConormalSequence_of_factors (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] [IsLocallyNoetherian X] (z : Z)
    (hi : ∃ W : Z.Opens, z ∈ W ∧ IsRegularImmersion (W.ι ≫ i))
    (hj : ∃ V : Y.Opens, i.base z ∈ V ∧ IsRegularImmersion (V.ι ≫ j)) :
    (∃ U : Z.Opens, z ∈ U ∧ IsRegularImmersion (U.ι ≫ (i ≫ j))) ∧
      ∃ W : Z.Opens, z ∈ W ∧ IsSplitExactConormalSequence (W.ι ≫ i) j :=
  ⟨exists_opens_isRegularImmersion_comp_of_factors i j z hi hj,
    exists_opens_isSplitExactConormalSequence_near i j z hi⟩

/-- **Stacks tag 0690.**  For immersions `i : Z ⟶ Y` and `j : Y ⟶ X` with `X` locally Noetherian
and `z : Z`, the following are equivalent: (1) `i` is a regular immersion near `z` and `j` is one
near `i z`; (2) `i` and `i ≫ j` are regular immersions near `z`; (3) `i ≫ j` is a regular
immersion near `z` and the conormal sequence of the pair is exact and locally split near `z`. -/
@[stacks 0690]
theorem tfae_isRegularImmersion_near (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j]
    [IsLocallyNoetherian X] (z : Z) :
    List.TFAE
      [(∃ W : Z.Opens, z ∈ W ∧ IsRegularImmersion (W.ι ≫ i)) ∧
          ∃ V : Y.Opens, i.base z ∈ V ∧ IsRegularImmersion (V.ι ≫ j),
        (∃ W : Z.Opens, z ∈ W ∧ IsRegularImmersion (W.ι ≫ i)) ∧
          ∃ U : Z.Opens, z ∈ U ∧ IsRegularImmersion (U.ι ≫ (i ≫ j)),
        (∃ U : Z.Opens, z ∈ U ∧ IsRegularImmersion (U.ι ≫ (i ≫ j))) ∧
          ∃ W : Z.Opens, z ∈ W ∧ IsSplitExactConormalSequence (W.ι ≫ i) j] := by
  tfae_have 1 → 2 := fun h =>
    ⟨h.1, exists_opens_isRegularImmersion_comp_of_factors i j z h.1 h.2⟩
  tfae_have 2 → 3 := fun h => exists_opens_isSplitExactConormalSequence_of_split i j z h.1 h.2
  tfae_have 3 → 1 := fun h => exists_opens_isRegularImmersion_of_split_near i j z h.1 h.2
  tfae_finish

end Stacks.AlgebraicGeometry.RegularIdealSheaf

end
