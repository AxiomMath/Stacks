module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Defs
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.Injectives.DerivedCategory.KInjectiveProducts
public import StacksCore.Algebra.Homology.QuasiIso
public import StacksCore.Algebra.Homology.ShortComplex.HomologicalComplex
import StacksCore.Tactic.StacksAttribute

/-!
# Representing a derived inverse system by a filtered complex

Let `A` be a Grothendieck abelian category, let `E` be an object of the unbounded derived
category `D(A)`, and let `F : ℤᵒᵖ ⥤ D(A)` be an inverse system of objects of `D(A)` indexed
by the integers, equipped with a compatible family of maps `φ : F ⟶ const E` to `E`. Such a
system can always be realized by a single filtered complex: there is a filtered cochain
complex `K` whose underlying complex represents `E` and whose filtration steps `F^pK`
represent the terms `F(p)`, compatibly with all transition maps and with all maps to `E`.

## Main results

* `Stacks.Injectives.exists_filteredComplex_representation`: the filtered complex, an
  isomorphism of its underlying complex with `E`, an isomorphism of the derived filtration
  diagram with the given inverse system, and the compatibility of the filtration inclusions
  with the given maps to `E`.

## References

* [Stacks Project, Tag 0ESJ](https://stacks.math.columbia.edu/tag/0ESJ)
-/

@[expose] public section

open CategoryTheory

universe w w' v u

namespace Stacks.Injectives

open CategoryTheory.Limits
open HomologicalComplex

variable {A : Type u} [Category.{v} A] [Abelian A]
  [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w'} A]

/-- A map in the derived category into a K-injective complex is the image of a genuine map
of cochain complexes. -/
private lemma exists_map_realizing {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w'} A] (X Y : CochainComplex A ℤ) [Y.IsKInjective]
    (f : DerivedCategory.Q.obj X ⟶ DerivedCategory.Q.obj Y) :
    ∃ g : X ⟶ Y, DerivedCategory.Q.map g = f := by
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let e := DerivedCategory.quotientCompQhIso A
  let target := (e.hom.app X) ≫ f ≫ (e.inv.app Y)
  obtain ⟨g', hgQh⟩ :=
    (CochainComplex.IsKInjective.Qh_map_bijective (q.obj X) Y).surjective target
  obtain ⟨g, hg⟩ := q.map_surjective g'
  refine ⟨g, ?_⟩
  apply (cancel_epi (e.hom.app X)).1
  calc
    e.hom.app X ≫ DerivedCategory.Q.map g =
        DerivedCategory.Qh.map (q.map g) ≫ e.hom.app Y :=
          (DerivedCategory.quotientCompQhIso_hom_naturality g).symm
    _ = target ≫ e.hom.app Y := by rw [hg, hgQh]
    _ = e.hom.app X ≫ f := by simp [target]

/-- Every object of the derived category is represented by a K-injective complex all of
whose terms are injective. -/
private lemma exists_kInjective_representation (E : DerivedCategory A) :
    ∃ (I : CochainComplex A ℤ), I.IsKInjective ∧
      (∀ n, Injective (I.X n)) ∧ Nonempty (DerivedCategory.Q.obj I ≅ E) := by
  have : (DerivedCategory.Q (C := A)).EssSurj := inferInstance
  obtain ⟨X, eX⟩ := Functor.EssSurj.mem_essImage (DerivedCategory.Q (C := A)) E
  obtain ⟨eX⟩ := eX
  let R := (kInjectiveResolutionFunctor A).obj X
  let r := (kInjectiveResolutionInclusion A).app X
  let : QuasiIso r := inferInstance
  exact ⟨R, inferInstance, (fun n => inferInstance),
    ⟨(asIso (DerivedCategory.Q.map r)).symm ≪≫ eX⟩⟩

omit [IsGrothendieckAbelian.{w, v, u} A] [HasDerivedCategory A] in
/-- A homotopy `α ≫ β₀ ~ γ` along a termwise monomorphism `α`, with injective target terms,
can be corrected to an equality: `β₀` may be modified by a null-homotopic map so that
`α ≫ β = γ` on the nose, without changing the induced map in the derived category. -/
private lemma homotopy_exists_comp_eq_and_Q_map {K L I : CochainComplex A ℤ}
    [∀ n, Injective (I.X n)] [HasDerivedCategory A]
    {α : K ⟶ L} [∀ n, Mono (α.f n)] {β₀ : L ⟶ I} {γ : K ⟶ I}
    (h : Homotopy (α ≫ β₀) γ) :
    ∃ β : L ⟶ I, α ≫ β = γ ∧ DerivedCategory.Q.map β = DerivedCategory.Q.map β₀ := by
  let lift : ∀ i j, L.X i ⟶ I.X j := fun i j =>
    if hij : (ComplexShape.up ℤ).Rel j i then
      Injective.factorThru (h.hom i j) (α.f i)
    else 0
  let c := Homotopy.nullHomotopicMap lift
  let β := β₀ - c
  have hfac : α ≫ β = γ := by
    show α ≫ (β₀ - Homotopy.nullHomotopicMap lift) = γ
    rw [Preadditive.comp_sub, Homotopy.comp_nullHomotopicMap]
    have hlift : (fun i j => α.f i ≫ lift i j) = h.hom := by
      funext i j
      by_cases hij : (ComplexShape.up ℤ).Rel j i
      · have heq : j + 1 = i := by simpa only [ComplexShape.up_Rel] using hij
        simp [lift, ComplexShape.up_Rel, heq, Injective.comp_factorThru]
      · have hn : ¬ j + 1 = i := by simpa only [ComplexShape.up_Rel] using hij
        simp [lift, ComplexShape.up_Rel, hn, h.zero i j hij]
    rw [hlift, ← h.sub_eq_nullHomotopicMap, sub_sub_cancel]
  have hnull : Homotopy c 0 := Homotopy.nullHomotopy lift (by
    intro i j hij
    have hn : ¬ j + 1 = i := by simpa only [ComplexShape.up_Rel] using hij
    simp [lift, ComplexShape.up_Rel, hn])
  have : Functor.Additive (DerivedCategory.Q (C := A)) := inferInstance
  have hc : DerivedCategory.Q.map c = 0 := by
    rw [DerivedCategory.Q_map_eq_of_homotopy (C := A) hnull]
    simp
  refine ⟨β, hfac, ?_⟩
  dsimp [β]
  rw [Functor.map_sub, hc, sub_zero]

omit [IsGrothendieckAbelian.{w, v, u} A] in
/-- Two maps of cochain complexes into a K-injective complex which agree in the derived
category are homotopic. -/
private lemma exists_homotopy_of_Q_map_eq {K I : CochainComplex A ℤ}
    [I.IsKInjective] {f g : K ⟶ I}
    (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    Nonempty (Homotopy f g) := by
  have : Functor.Additive (DerivedCategory.Q (C := A)) := inferInstance
  have hz : DerivedCategory.Q.map (f - g) = 0 := by
    rw [Functor.map_sub, h, sub_self]
  have h0 : Nonempty (Homotopy (f - g) 0) := by
    apply (HomotopyCategory.quotient_map_eq_zero_iff (f - g)).1
    apply (CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) I).injective
    rw [Functor.map_zero, ← cancel_mono ((DerivedCategory.quotientCompQhIso A).hom.app I)]
    simp only [DerivedCategory.quotientCompQhIso_hom_naturality, hz,
      comp_zero, zero_comp]
  obtain ⟨h0⟩ := h0
  exact ⟨Homotopy.equivSubZero.symm h0⟩

/-- A chosen K-injective complex with injective terms representing the `i`-th term of the
inverse system `F`. -/
private noncomputable def chosenModel (F : ℤᵒᵖ ⥤ DerivedCategory A) (i : ℤ) :
    CochainComplex A ℤ :=
  Classical.choose (exists_kInjective_representation (F.obj (Opposite.op i)))

/-- The chosen representative `chosenModel F i` is K-injective. -/
private lemma chosenModel_isKInjective (F : ℤᵒᵖ ⥤ DerivedCategory A) (i : ℤ) :
    (chosenModel F i).IsKInjective :=
  (Classical.choose_spec (exists_kInjective_representation (F.obj (Opposite.op i)))).1

/-- The isomorphism identifying the object represented by `chosenModel F i` with `F(i)`. -/
private noncomputable def chosenModelIso (F : ℤᵒᵖ ⥤ DerivedCategory A) (i : ℤ) :
    DerivedCategory.Q.obj (chosenModel F i) ≅ F.obj (Opposite.op i) :=
  Classical.choice
    (Classical.choose_spec (exists_kInjective_representation (F.obj (Opposite.op i)))).2.2

/-- A chosen cochain map realizing the transition map `F(i) ⟶ F(i+1)` of the inverse system
on the chosen representatives. -/
private noncomputable def rawTransition (F : ℤᵒᵖ ⥤ DerivedCategory A) (i : ℤ) :
    chosenModel F (i + 1) ⟶ chosenModel F i := by
  letI : (chosenModel F i).IsKInjective := chosenModel_isKInjective F i
  exact Classical.choose (exists_map_realizing (chosenModel F (i + 1)) (chosenModel F i)
    ((chosenModelIso F (i + 1)).hom ≫ F.map (opHomOfLE (show i ≤ i + 1 by omega)) ≫
      (chosenModelIso F i).inv))

/-- The defining property of `rawTransition`: it induces the transition map of `F`. -/
private lemma rawTransition_spec (F : ℤᵒᵖ ⥤ DerivedCategory A) (i : ℤ) :
    DerivedCategory.Q.map (rawTransition F i) =
      (chosenModelIso F (i + 1)).hom ≫
        F.map (opHomOfLE (show i ≤ i + 1 by omega)) ≫ (chosenModelIso F i).inv := by
  let : (chosenModel F i).IsKInjective := chosenModel_isKInjective F i
  exact Classical.choose_spec (exists_map_realizing (chosenModel F (i + 1))
    (chosenModel F i) ((chosenModelIso F (i + 1)).hom ≫
      F.map (opHomOfLE (show i ≤ i + 1 by omega)) ≫ (chosenModelIso F i).inv))

/-- A complex representing `F(-n)`, used as the `n`-th stage of the tower built in the
negative direction. -/
private structure NegativeTower (F : ℤᵒᵖ ⥤ DerivedCategory A) (n : ℕ) where
  /-- The complex. -/
  X : CochainComplex A ℤ
  /-- Its identification with `F(-n)` in the derived category. -/
  iso : DerivedCategory.Q.obj X ≅ F.obj (Opposite.op (-((n : ℤ))))

/-- A factorization of a map of cochain complexes as a degreewise split monomorphism
followed by a map admitting a retraction which is a homotopy inverse. -/
private structure MonoFactorization {K L : CochainComplex A ℤ} (f : K ⟶ L) where
  /-- The intermediate complex. -/
  middle : CochainComplex A ℤ
  /-- The degreewise split monomorphism out of the source. -/
  left : K ⟶ middle
  /-- The homotopy equivalence onto the target. -/
  right : middle ⟶ L
  /-- A section of `right`. -/
  retract : L ⟶ middle
  /-- The factorization identity. -/
  fac : left ≫ right = f
  /-- `left` is a split monomorphism in every degree. -/
  leftSplitMono : ∀ n, IsSplitMono (left.f n)
  /-- `retract` is a section of `right`. -/
  retractRight : retract ≫ right = 𝟙 L
  /-- `retract` is also a homotopy inverse of `right`. -/
  rightSectionHomotopy : Nonempty (Homotopy (right ≫ retract) (𝟙 middle))

/-- A chosen degreewise-split-mono factorization of a map of cochain complexes. -/
private noncomputable def chooseMonoFactorization {K L : CochainComplex A ℤ}
    (f : K ⟶ L) : MonoFactorization f := by
  choose M l r s h using CochainComplex.exists_factorization_isDegreewiseSplitMono f
  exact ⟨M, l, r, s, h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- The second map of a `MonoFactorization` is a homotopy equivalence. -/
private noncomputable def MonoFactorization.homotopyEquiv {A : Type u} [Category.{v} A] [Abelian A]
    {K L : CochainComplex A ℤ} {f : K ⟶ L}
    (D : MonoFactorization f) : HomotopyEquiv D.middle L where
  hom := D.right
  inv := D.retract
  homotopyHomInvId := D.rightSectionHomotopy.some
  homotopyInvHomId := Homotopy.ofEq D.retractRight

omit [IsGrothendieckAbelian.{w, v, u} A] [HasDerivedCategory.{w'} A] in
/-- The second map of a `MonoFactorization` is a homotopy equivalence, hence a
quasi-isomorphism. -/
private lemma monoFactorization_right_quasiIso {K L : CochainComplex A ℤ}
    {f : K ⟶ L} (D : MonoFactorization f) : QuasiIso D.right :=
  D.homotopyEquiv.quasiIso_hom

/-- A chosen cochain map from the `n`-th negative stage to the chosen representative of
`F(-(n+1))`, realizing the transition map of `F`. -/
private noncomputable def negativeTransition {F : ℤᵒᵖ ⥤ DerivedCategory A} (n : ℕ)
    (D : NegativeTower F n) : D.X ⟶ chosenModel F (-((n : ℤ) + 1)) := by
  letI : (chosenModel F (-((n : ℤ) + 1))).IsKInjective :=
    chosenModel_isKInjective F (-((n : ℤ) + 1))
  exact Classical.choose (exists_map_realizing D.X (chosenModel F (-((n : ℤ) + 1)))
    (D.iso.hom ≫ F.map (opHomOfLE (show -((n : ℤ) + 1) ≤ -((n : ℤ)) by omega)) ≫
      (chosenModelIso F (-((n : ℤ) + 1))).inv))

/-- The defining property of `negativeTransition`. -/
private lemma negativeTransition_spec {F : ℤᵒᵖ ⥤ DerivedCategory A} (n : ℕ)
    (D : NegativeTower F n) :
    DerivedCategory.Q.map (negativeTransition n D) =
      D.iso.hom ≫ F.map (opHomOfLE (show -((n : ℤ) + 1) ≤ -((n : ℤ)) by omega)) ≫
        (chosenModelIso F (-((n : ℤ) + 1))).inv := by
  let : (chosenModel F (-((n : ℤ) + 1))).IsKInjective :=
    chosenModel_isKInjective F (-((n : ℤ) + 1))
  exact Classical.choose_spec (exists_map_realizing D.X
    (chosenModel F (-((n : ℤ) + 1)))
    (D.iso.hom ≫ F.map (opHomOfLE (show -((n : ℤ) + 1) ≤ -((n : ℤ)) by omega)) ≫
      (chosenModelIso F (-((n : ℤ) + 1))).inv))

/-- The chosen factorization of `negativeTransition n D` through a degreewise split
monomorphism; its middle term is the next stage of the negative tower. -/
private noncomputable def negativeFactorization {F : ℤᵒᵖ ⥤ DerivedCategory A} (n : ℕ)
    (D : NegativeTower F n) : MonoFactorization (negativeTransition n D) :=
  chooseMonoFactorization (negativeTransition n D)

/-- The tower of complexes representing `F(0), F(-1), F(-2), …`, built so that consecutive
stages are related by a degreewise split monomorphism. -/
private noncomputable def negativeTower (F : ℤᵒᵖ ⥤ DerivedCategory A) :
    (n : ℕ) → NegativeTower F n
  | 0 => ⟨chosenModel F 0, chosenModelIso F 0⟩
  | n + 1 => by
      let D := negativeTower F n
      let T := negativeFactorization n D
      letI : QuasiIso T.right := monoFactorization_right_quasiIso T
      exact ⟨T.middle,
        (asIso (DerivedCategory.Q.map T.right)) ≪≫
          chosenModelIso F (-((n : ℤ) + 1))⟩

/-- Every stage of the negative tower is K-injective. -/
private lemma negativeTower_isKInjective (F : ℤᵒᵖ ⥤ DerivedCategory A) (n : ℕ) :
    ((negativeTower F n).X).IsKInjective := by
  induction n with
  | zero => simpa [negativeTower] using chosenModel_isKInjective F 0
  | succ n ih =>
      let D := negativeTower F n
      let T := negativeFactorization n D
      have : (chosenModel F (-((n : ℤ) + 1))).IsKInjective :=
        chosenModel_isKInjective F (-((n : ℤ) + 1))
      exact T.homotopyEquiv.symm.isKInjective

/-- The structural map from the `n`-th to the `(n+1)`-st stage of the negative tower. -/
private noncomputable def negativeDelta (F : ℤᵒᵖ ⥤ DerivedCategory A) (n : ℕ) :
    (negativeTower F n).X ⟶ (negativeTower F (n + 1)).X :=
  (negativeFactorization n (negativeTower F n)).left

/-- The structural maps of the negative tower are termwise monomorphisms. -/
private lemma negativeDelta_mono (F : ℤᵒᵖ ⥤ DerivedCategory A) (n : ℕ) :
    ∀ k, Mono ((negativeDelta F n).f k) := fun k =>
  ((negativeFactorization n (negativeTower F n)).leftSplitMono k).exists_splitMono.some.mono

/-- The structural maps of the negative tower induce the transition maps of `F`. -/
private lemma negativeDelta_spec (F : ℤᵒᵖ ⥤ DerivedCategory A) (n : ℕ) :
    DerivedCategory.Q.map (negativeDelta F n) =
      (negativeTower F n).iso.hom ≫
        F.map (opHomOfLE (show -((n : ℤ) + 1) ≤ -((n : ℤ)) by omega)) ≫
          (negativeTower F (n + 1)).iso.inv := by
  let D := negativeTower F n
  let T := negativeFactorization n D
  let : QuasiIso T.right := monoFactorization_right_quasiIso T
  show DerivedCategory.Q.map T.left = _
  apply (cancel_mono (DerivedCategory.Q.map T.right)).1
  rw [← DerivedCategory.Q.map_comp, T.fac, negativeTransition_spec]
  simp [D, negativeTower, T, Category.assoc]

/-- A chosen cochain map from the `n`-th negative stage to a K-injective representative `I`
of `E`, realizing the given map `F(-n) ⟶ E`. -/
private noncomputable def towerMapToE (E : DerivedCategory A)
    (F : ℤᵒᵖ ⥤ DerivedCategory A) (φ : F ⟶ (Functor.const ℤᵒᵖ).obj E)
    {I : CochainComplex A ℤ} (e : DerivedCategory.Q.obj I ≅ E) [I.IsKInjective]
    (n : ℕ) : (negativeTower F n).X ⟶ I :=
  Classical.choose (exists_map_realizing (negativeTower F n).X I
    ((negativeTower F n).iso.hom ≫ φ.app (Opposite.op (-((n : ℤ)))) ≫ e.inv))

/-- The defining property of `towerMapToE`. -/
private lemma towerMapToE_spec (E : DerivedCategory A)
    (F : ℤᵒᵖ ⥤ DerivedCategory A) (φ : F ⟶ (Functor.const ℤᵒᵖ).obj E)
    {I : CochainComplex A ℤ} (e : DerivedCategory.Q.obj I ≅ E) [I.IsKInjective]
    (n : ℕ) :
    DerivedCategory.Q.map (towerMapToE E F φ e n) =
      (negativeTower F n).iso.hom ≫ φ.app (Opposite.op (-((n : ℤ)))) ≫ e.inv :=
  Classical.choose_spec (exists_map_realizing (negativeTower F n).X I
    ((negativeTower F n).iso.hom ≫ φ.app (Opposite.op (-((n : ℤ)))) ≫ e.inv))

/-- The inductive step extending a map to `I` from the `n`-th negative stage to the
`(n+1)`-st one, strictly compatible with the structural map of the tower. -/
private noncomputable def extendNegativeMapToEData (E : DerivedCategory A)
    (F : ℤᵒᵖ ⥤ DerivedCategory A) (φ : F ⟶ (Functor.const ℤᵒᵖ).obj E)
    {I : CochainComplex A ℤ} (e : DerivedCategory.Q.obj I ≅ E) [I.IsKInjective]
    [∀ n, Injective (I.X n)] (n : ℕ)
    (prev : {f : (negativeTower F n).X ⟶ I //
      DerivedCategory.Q.map f =
        (negativeTower F n).iso.hom ≫ φ.app (Opposite.op (-((n : ℤ)))) ≫ e.inv}) :
    {f : (negativeTower F (n + 1)).X ⟶ I //
      DerivedCategory.Q.map f =
        (negativeTower F (n + 1)).iso.hom ≫
          φ.app (Opposite.op (-((n + 1 : ℤ)))) ≫ e.inv ∧
      negativeDelta F n ≫ f = prev.1} := by
  let δ := negativeDelta F n
  let raw := towerMapToE E F φ e (n + 1)
  have hQ : DerivedCategory.Q.map (δ ≫ raw) = DerivedCategory.Q.map prev.1 := by
    rw [Functor.map_comp, negativeDelta_spec, towerMapToE_spec, prev.2]
    simp [Category.assoc]
  let H := Classical.choice (exists_homotopy_of_Q_map_eq hQ)
  letI : ∀ k, Mono ((negativeDelta F n).f k) := negativeDelta_mono F n
  let ex := homotopy_exists_comp_eq_and_Q_map H
  let chosen := Classical.choose ex
  have hchosen := Classical.choose_spec ex
  exact ⟨chosen, ⟨hchosen.2.trans (towerMapToE_spec E F φ e (n + 1)), hchosen.1⟩⟩

/-- The maps from the stages of the negative tower to a K-injective representative of `E`,
chosen inductively so that they are strictly compatible with the tower. -/
private noncomputable def negativeMapToEData (E : DerivedCategory A)
    (F : ℤᵒᵖ ⥤ DerivedCategory A) (φ : F ⟶ (Functor.const ℤᵒᵖ).obj E)
    {I : CochainComplex A ℤ} (e : DerivedCategory.Q.obj I ≅ E) [I.IsKInjective]
    [∀ n, Injective (I.X n)] :
    (n : ℕ) → {f : (negativeTower F n).X ⟶ I //
      DerivedCategory.Q.map f =
        (negativeTower F n).iso.hom ≫ φ.app (Opposite.op (-((n : ℤ)))) ≫ e.inv}
  | 0 => ⟨towerMapToE E F φ e 0, towerMapToE_spec E F φ e 0⟩
  | n + 1 => by
      let step := extendNegativeMapToEData E F φ e n (negativeMapToEData E F φ e n)
      exact ⟨step.1, step.2.1⟩

/-- The maps of `negativeMapToEData` are compatible with the structural maps of the negative
tower. -/
private lemma negativeMapToEData_transition (E : DerivedCategory A)
    (F : ℤᵒᵖ ⥤ DerivedCategory A) (φ : F ⟶ (Functor.const ℤᵒᵖ).obj E)
    {I : CochainComplex A ℤ} (e : DerivedCategory.Q.obj I ≅ E) [I.IsKInjective]
    [∀ n, Injective (I.X n)] (n : ℕ) :
    negativeDelta F n ≫ (negativeMapToEData E F φ e (n + 1)).1 =
      (negativeMapToEData E F φ e n).1 :=
  (extendNegativeMapToEData E F φ e n (negativeMapToEData E F φ e n)).2.2

/-- The maps from the chosen representatives of `F(n)`, `n ≥ 0`, to a K-injective
representative of `E`, obtained by composing with the lifted transition maps. -/
private noncomputable def positiveMapToEData (E : DerivedCategory A)
    (F : ℤᵒᵖ ⥤ DerivedCategory A) (φ : F ⟶ (Functor.const ℤᵒᵖ).obj E)
    {I : CochainComplex A ℤ} (e : DerivedCategory.Q.obj I ≅ E) [I.IsKInjective] :
    (n : ℕ) → {f : chosenModel F n ⟶ I //
      DerivedCategory.Q.map f =
        (chosenModelIso F n).hom ≫ φ.app (Opposite.op (n : ℤ)) ≫ e.inv}
  | 0 => ⟨towerMapToE E F φ e 0, by
      simpa [negativeTower, chosenModelIso] using towerMapToE_spec E F φ e 0⟩
  | n + 1 => by
      let prev := positiveMapToEData E F φ e n
      let δ := rawTransition F n
      exact ⟨δ ≫ prev.1, by
        rw [Functor.map_comp, rawTransition_spec, prev.2]
        simp [Category.assoc]⟩

omit [IsGrothendieckAbelian.{w, v, u} A] [HasDerivedCategory.{w'} A] in
/-- The cone on an identity map is acyclic. -/
public lemma mappingCone_id_acyclic (K : CochainComplex A ℤ) :
    (CochainComplex.mappingCone (𝟙 K)).Acyclic := by
  have h : Homotopy (𝟙 (CochainComplex.mappingCone (𝟙 K))) 0 :=
    CochainComplex.mappingCone.liftHomotopy (𝟙 K) _ _
      (CochainComplex.mappingCone.snd (𝟙 K)) 0 (by simp) (by simp)
  rw [HomologicalComplex.acyclic_iff_isZero_homology]
  intro n
  have hn := h.homologyMap_eq n
  rw [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero] at hn
  exact (IsZero.iff_id_eq_zero _).2 hn

omit [IsGrothendieckAbelian.{w, v, u} A] in
/-- An acyclic complex represents a zero object of the derived category. -/
public lemma isZero_Q_obj_of_acyclic (K : CochainComplex A ℤ) (hK : K.Acyclic) :
    IsZero (DerivedCategory.Q.obj K) := by
  have hq : QuasiIso (0 : K ⟶ K) := by
    rw [quasiIso_iff_isIso_homologyMap]
    intro n
    have hn := (HomologicalComplex.acyclic_iff_isZero_homology K).1 hK n
    refine ⟨⟨0, ?_, ?_⟩⟩
    · simpa using hn.eq_of_src _ _
    · simpa using hn.eq_of_tgt _ _
  have : IsIso (0 : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj K) := by
    simpa using (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
  have hid : 𝟙 (DerivedCategory.Q.obj K) = 0 := by
    rw [← IsIso.hom_inv_id (0 : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj K), zero_comp]
  exact (IsZero.iff_id_eq_zero _).2 hid

/-- The K-injective resolution of the cone on `𝟙 K`: an acyclic K-injective complex into
which `K` embeds termwise. -/
private noncomputable def functorialNullModel (K : CochainComplex A ℤ) :
    CochainComplex A ℤ :=
  (kInjectiveResolutionFunctor A).obj
    (CochainComplex.mappingCone (𝟙 K))

/-- The embedding of `K` into `functorialNullModel K`. -/
private noncomputable def functorialNullModelInclusion (K : CochainComplex A ℤ) :
    K ⟶ functorialNullModel K :=
  CochainComplex.mappingCone.inr (𝟙 K) ≫
    (kInjectiveResolutionInclusion A).app
      (CochainComplex.mappingCone (𝟙 K))

omit [HasDerivedCategory.{w'} A] in
/-- `functorialNullModel K` is K-injective. -/
private lemma functorialNullModel_isKInjective (K : CochainComplex A ℤ) :
    (functorialNullModel K).IsKInjective :=
  kInjectiveResolutionFunctor_obj_isKInjective
    (M := CochainComplex.mappingCone (𝟙 K))

omit [HasDerivedCategory.{w'} A] in
/-- The embedding of `K` into `functorialNullModel K` is a monomorphism in every degree. -/
private lemma functorialNullModel_inclusion_mono (K : CochainComplex A ℤ) (n : ℤ) :
    Mono ((functorialNullModelInclusion K).f n) := by
  have : IsSplitMono ((CochainComplex.mappingCone.inr (𝟙 K)).f n) := IsSplitMono.mk'
    { retraction := (CochainComplex.mappingCone.snd (𝟙 K)).v n n (by omega)
      id := by simp }
  have := kInjectiveResolutionInclusion_f_mono A (CochainComplex.mappingCone (𝟙 K)) n
  exact mono_comp ((CochainComplex.mappingCone.inr (𝟙 K)).f n)
    (((kInjectiveResolutionInclusion A).app (CochainComplex.mappingCone (𝟙 K))).f n)

/-- `functorialNullModel K` represents a zero object of the derived category. -/
private lemma functorialNullModel_isZero (K : CochainComplex A ℤ) :
    IsZero (DerivedCategory.Q.obj (functorialNullModel K)) := by
  have := kInjectiveResolutionInclusion_quasiIso A (CochainComplex.mappingCone (𝟙 K))
  exact (isZero_Q_obj_of_acyclic _ (mappingCone_id_acyclic K)).of_iso
    (asIso (DerivedCategory.Q.map
      ((kInjectiveResolutionInclusion A).app (CochainComplex.mappingCone (𝟙 K))))).symm

/-- The complex representing `F(i)` used as the `i`-th stage of the tower: the chosen
representative for `i ≥ 0`, and the negative tower for `i < 0`. -/
private noncomputable def modelAt (F : ℤᵒᵖ ⥤ DerivedCategory A) : ℤ → CochainComplex A ℤ
  | .ofNat n => chosenModel F n
  | .negSucc n => (negativeTower F (n + 1)).X

/-- Every stage `modelAt F i` is K-injective. -/
private lemma modelAt_isKInjective (F : ℤᵒᵖ ⥤ DerivedCategory A) (i : ℤ) :
    (modelAt F i).IsKInjective := by
  cases i with
  | ofNat n => exact chosenModel_isKInjective F n
  | negSucc n => exact negativeTower_isKInjective F (n + 1)

/-- The identification of the object represented by `modelAt F i` with `F(i)`. -/
private noncomputable def modelIsoAt (F : ℤᵒᵖ ⥤ DerivedCategory A) (i : ℤ) :
    DerivedCategory.Q.obj (modelAt F i) ≅ F.obj (Opposite.op i) := by
  cases i with
  | ofNat n => exact chosenModelIso F n
  | negSucc n => exact (negativeTower F (n + 1)).iso

/-- At a natural number index, `modelIsoAt` is the chosen isomorphism. -/
private lemma modelIsoAt_nat (F : ℤᵒᵖ ⥤ DerivedCategory A) (n : ℕ) :
    modelIsoAt F (n : ℤ) = chosenModelIso F n := rfl

/-- At a successor of a natural number index, `modelIsoAt` is the chosen isomorphism. -/
private lemma modelIsoAt_nat_succ (F : ℤᵒᵖ ⥤ DerivedCategory A) (n : ℕ) :
    modelIsoAt F ((n : ℤ) + 1) = chosenModelIso F (n + 1) := by
  have h : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
  cases h
  rfl

/-- The chosen cochain map from the `i`-th stage to a K-injective representative of `E`. -/
private noncomputable def modelMapToEAt (E : DerivedCategory A)
    (F : ℤᵒᵖ ⥤ DerivedCategory A) (φ : F ⟶ (Functor.const ℤᵒᵖ).obj E)
    {I : CochainComplex A ℤ} (e : DerivedCategory.Q.obj I ≅ E) [I.IsKInjective]
    [∀ n, Injective (I.X n)]
    (i : ℤ) : modelAt F i ⟶ I := by
  cases i with
  | ofNat n => exact (positiveMapToEData E F φ e n).1
  | negSucc n => exact (negativeMapToEData E F φ e (n + 1)).1

/-- The map `modelMapToEAt` induces the given map `F(i) ⟶ E`. -/
private lemma modelMapToEAt_spec (E : DerivedCategory A)
    (F : ℤᵒᵖ ⥤ DerivedCategory A) (φ : F ⟶ (Functor.const ℤᵒᵖ).obj E)
    {I : CochainComplex A ℤ} (e : DerivedCategory.Q.obj I ≅ E) [I.IsKInjective]
    [∀ n, Injective (I.X n)]
    (i : ℤ) :
    DerivedCategory.Q.map (modelMapToEAt E F φ e i) =
      (modelIsoAt F i).hom ≫ φ.app (Opposite.op i) ≫ e.inv := by
  cases i with
  | ofNat n => exact (positiveMapToEData E F φ e n).2
  | negSucc n => exact (negativeMapToEData E F φ e (n + 1)).2

/-- The structural map from the `(i+1)`-st to the `i`-th stage of the tower. -/
private noncomputable def modelTransition (F : ℤᵒᵖ ⥤ DerivedCategory A) (i : ℤ) :
    modelAt F (i + 1) ⟶ modelAt F i := by
  cases i with
  | ofNat n => exact rawTransition F n
  | negSucc n =>
      have hn : (Int.negSucc n : ℤ) + 1 = -(n : ℤ) := by omega
      rw [hn]
      cases n with
      | zero => simpa [modelAt, negativeTower] using negativeDelta F 0
      | succ n =>
          change (negativeTower F (n + 1)).X ⟶ (negativeTower F (n + 2)).X
          exact negativeDelta F (n + 1)

/-- The structural maps of the tower induce the transition maps of `F`. -/
private lemma modelTransition_spec (F : ℤᵒᵖ ⥤ DerivedCategory A) (i : ℤ) :
    DerivedCategory.Q.map (modelTransition F i) =
      (modelIsoAt F (i + 1)).hom ≫
        F.map (opHomOfLE (show i ≤ i + 1 by omega)) ≫ (modelIsoAt F i).inv := by
  cases i with
  | ofNat n =>
      show DerivedCategory.Q.map (rawTransition F n) =
        (modelIsoAt F ((n : ℤ) + 1)).hom ≫
          F.map (opHomOfLE (show (n : ℤ) ≤ (n : ℤ) + 1 by omega)) ≫
            (modelIsoAt F (n : ℤ)).inv
      rw [modelIsoAt_nat_succ, modelIsoAt_nat]
      exact rawTransition_spec F n
  | negSucc n =>
      cases n with
      | zero =>
          show DerivedCategory.Q.map (negativeDelta F 0) = _
          let T := negativeFactorization 0 (negativeTower F 0)
          let : QuasiIso T.right := monoFactorization_right_quasiIso T
          let : IsIso (DerivedCategory.Q.map T.right) :=
            (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
          show DerivedCategory.Q.map (negativeDelta F 0) =
            (negativeTower F 0).iso.hom ≫
              F.map (opHomOfLE (show -1 ≤ 0 by omega)) ≫
                (negativeTower F 1).iso.inv
          simpa only [negativeTower] using negativeDelta_spec F 0
      | succ n =>
          show DerivedCategory.Q.map (negativeDelta F (n + 1)) =
            (negativeTower F (n + 1)).iso.hom ≫
              F.map (opHomOfLE (show Int.negSucc (n + 1) ≤ Int.negSucc (n + 1) + 1 by omega)) ≫
                (negativeTower F (n + 2)).iso.inv
          simpa only [negativeTower] using negativeDelta_spec F (n + 1)

/-- The maps to a representative of `E` are strictly compatible with the structural maps of
the tower. -/
private lemma modelMapToEAt_transition (E : DerivedCategory A)
    (F : ℤᵒᵖ ⥤ DerivedCategory A) (φ : F ⟶ (Functor.const ℤᵒᵖ).obj E)
    {I : CochainComplex A ℤ} (e : DerivedCategory.Q.obj I ≅ E) [I.IsKInjective]
    [∀ n, Injective (I.X n)]
    (i : ℤ) :
    modelTransition F i ≫ modelMapToEAt E F φ e i = modelMapToEAt E F φ e (i + 1) := by
  cases i with
  | ofNat n =>
      show rawTransition F n ≫ (positiveMapToEData E F φ e n).1 =
        (positiveMapToEData E F φ e (n + 1)).1
      rfl
  | negSucc n =>
      cases n with
      | zero =>
          show negativeDelta F 0 ≫ (negativeMapToEData E F φ e 1).1 =
            (positiveMapToEData E F φ e 0).1
          rw [negativeMapToEData_transition]
          rfl
      | succ n =>
          show negativeDelta F (n + 1) ≫
            (negativeMapToEData E F φ e (n + 2)).1 =
            (negativeMapToEData E F φ e (n + 1)).1
          exact negativeMapToEData_transition E F φ e (n + 1)

/-- The composite structural map from the `j`-th down to the `i`-th stage of the tower,
for `i ≤ j`. -/
private noncomputable def modelDescent (F : ℤᵒᵖ ⥤ DerivedCategory A) (i j : ℤ)
    (h : i ≤ j) : modelAt F j ⟶ modelAt F i :=
  Int.leInduction (motive := fun j _ => modelAt F j ⟶ modelAt F i)
    (𝟙 (modelAt F i)) (fun j _ f => modelTransition F j ≫ f) j h

/-- The recursion defining `modelDescent`. -/
private lemma modelDescent_succ (F : ℤᵒᵖ ⥤ DerivedCategory A) (i j : ℤ)
    (h : i ≤ j) :
    modelDescent F i (j + 1) (Int.le_add_one h) =
      modelTransition F j ≫ modelDescent F i j h := by
  simpa [modelDescent] using
    (Int.leInduction_add_one
      (base := 𝟙 (modelAt F i))
      (succ := fun j _ f => modelTransition F j ≫ f) j h)

/-- `modelDescent` is transitive. -/
private lemma modelDescent_comp (F : ℤᵒᵖ ⥤ DerivedCategory A)
    (i j k : ℤ) (hij : i ≤ j) (hjk : j ≤ k) :
    modelDescent F j k hjk ≫ modelDescent F i j hij =
      modelDescent F i k (le_trans hij hjk) := by
  refine Int.leInduction (motive := fun k hjk =>
      modelDescent F j k hjk ≫ modelDescent F i j hij =
        modelDescent F i k (le_trans hij hjk)) ?_ ?_ k hjk
  · simp [modelDescent, Int.leInduction_base]
  · intro k hjk ih
    rw [modelDescent_succ F j k hjk, Category.assoc, ih,
      modelDescent_succ F i k (le_trans hij hjk)]

/-- The maps to a representative of `E` are compatible with `modelDescent`. -/
private lemma modelDescent_mapToE (E : DerivedCategory A)
    (F : ℤᵒᵖ ⥤ DerivedCategory A) (φ : F ⟶ (Functor.const ℤᵒᵖ).obj E)
    {I : CochainComplex A ℤ} (e : DerivedCategory.Q.obj I ≅ E) [I.IsKInjective]
    [∀ n, Injective (I.X n)] (i j : ℤ) (h : i ≤ j) :
    modelDescent F i j h ≫ modelMapToEAt E F φ e i =
      modelMapToEAt E F φ e j := by
  refine Int.leInduction (motive := fun j h =>
      modelDescent F i j h ≫ modelMapToEAt E F φ e i =
        modelMapToEAt E F φ e j) ?_ ?_ j h
  · simp [modelDescent, Int.leInduction_base]
  · intro j hij ih
    rw [modelDescent_succ F i j hij, Category.assoc, ih, modelMapToEAt_transition]

/-- `modelDescent` induces the transition map of `F` from `j` down to `i`. -/
private lemma modelDescent_spec (F : ℤᵒᵖ ⥤ DerivedCategory A) (i j : ℤ)
    (h : i ≤ j) :
    DerivedCategory.Q.map (modelDescent F i j h) =
      (modelIsoAt F j).hom ≫ F.map (opHomOfLE h) ≫ (modelIsoAt F i).inv := by
  refine Int.leInduction (motive := fun j h =>
      DerivedCategory.Q.map (modelDescent F i j h) =
        (modelIsoAt F j).hom ≫ F.map (opHomOfLE h) ≫ (modelIsoAt F i).inv) ?_ ?_ j h
  · have hId : opHomOfLE (show i ≤ i from le_rfl) = 𝟙 (Opposite.op i) :=
      Subsingleton.elim _ _
    simp [modelDescent, Int.leInduction_base, hId]
  · intro j hij ih
    rw [modelDescent_succ F i j hij, Functor.map_comp, modelTransition_spec, ih]
    have hj : j ≤ j + 1 := by omega
    have hcomp : opHomOfLE hj ≫ opHomOfLE hij =
        opHomOfLE (show i ≤ j + 1 by omega) := Subsingleton.elim _ _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← F.map_comp_assoc, hcomp]

/-- The acyclic K-injective padding complex attached to the index `i`. -/
private noncomputable abbrev correctionModel (F : ℤᵒᵖ ⥤ DerivedCategory A) (i : ℤ) :
    CochainComplex A ℤ := functorialNullModel (modelAt F i)

/-- The padding complexes are K-injective. -/
private lemma correctionModel_isKInjective (F : ℤᵒᵖ ⥤ DerivedCategory A) (i : ℤ) :
    (correctionModel F i).IsKInjective := functorialNullModel_isKInjective _

/-- The padding complexes represent zero objects of the derived category. -/
private lemma correctionModel_isZero (F : ℤᵒᵖ ⥤ DerivedCategory A) (i : ℤ) :
    IsZero (DerivedCategory.Q.obj (correctionModel F i)) := functorialNullModel_isZero _

/-- If all but one factor of a product of K-injective complexes represents a zero object,
the remaining projection becomes an isomorphism in the derived category. -/
private lemma product_projection_isIso_of_isZero_factors {ι : Type w}
    (K : ι → CochainComplex A ℤ) (hK : ∀ i, (K i).IsKInjective)
    (i₀ : ι) (hzero : ∀ i, i ≠ i₀ → IsZero (DerivedCategory.Q.obj (K i))) :
    IsIso (DerivedCategory.Q.map (Pi.π K i₀)) := by
  let fan := productFanInDerivedCategory K
  obtain ⟨hfan⟩ := isLimit_productFanInDerivedCategory K hK
  let s : Fan (fun i => DerivedCategory.Q.obj (K i)) :=
    Fan.mk (DerivedCategory.Q.obj (K i₀)) (fun i => by
      by_cases hi : i = i₀
      · subst i
        exact 𝟙 _
      · exact 0)
  let g : DerivedCategory.Q.obj (K i₀) ⟶ DerivedCategory.Q.obj (∏ᶜ K) := hfan.lift s
  have hg (i : Discrete ι) : g ≫ fan.π.app i = s.proj i.as := hfan.fac s i
  have hleft : g ≫ DerivedCategory.Q.map (Pi.π K i₀) = 𝟙 _ := by
    simpa [fan, productFanInDerivedCategory, s] using hg ⟨i₀⟩
  have hright : DerivedCategory.Q.map (Pi.π K i₀) ≫ g = 𝟙 _ := by
    apply hfan.hom_ext
    rintro ⟨i⟩
    by_cases hi : i = i₀
    · subst i
      simpa [fan, productFanInDerivedCategory,
        Category.assoc] using congrArg (fun f => DerivedCategory.Q.map (Pi.π K i₀) ≫ f) hleft
    · exact (hzero i hi).eq_of_tgt _ _
  exact ⟨⟨g, hright, hleft⟩⟩

/-- The embedding of the `i`-th stage into the padding complex attached to an index `p ≤ i`,
obtained by descending to the `p`-th stage and then embedding. -/
private noncomputable def correctionFromModel (F : ℤᵒᵖ ⥤ DerivedCategory A)
    (i p : ℤ) (h : p ≤ i) : modelAt F i ⟶ correctionModel F p :=
  modelDescent F p i h ≫ functorialNullModelInclusion (modelAt F p)

/-- The maps `correctionFromModel` are compatible with `modelDescent`. -/
private lemma correctionFromModel_comp (F : ℤᵒᵖ ⥤ DerivedCategory A)
    (i j p : ℤ) (hpj : p ≤ j) (hji : j ≤ i) :
    modelDescent F j i hji ≫ correctionFromModel F j p hpj =
      correctionFromModel F i p (le_trans hpj hji) := by
  simp only [correctionFromModel]
  rw [← Category.assoc, modelDescent_comp F p j i hpj hji]

noncomputable section

/-- The index set of the ambient product: one copy of the representative of `E`, together
with one padding complex for each integer. -/
private abbrev AmbientIndex : Type w := ULift.{w, 0} (Option ℤ)

/-- The index of the representative of `E` in the ambient product. -/
private abbrev ambientNone : AmbientIndex := ⟨none⟩

/-- The index of the `p`-th padding complex in the ambient product. -/
private abbrev ambientSome (p : ℤ) : AmbientIndex := ⟨some p⟩

/-- The family of factors of the ambient product. -/
private abbrev ambientFactor (F : ℤᵒᵖ ⥤ DerivedCategory A)
    (I : CochainComplex A ℤ) : AmbientIndex → CochainComplex A ℤ
  | ⟨none⟩ => I
  | ⟨some p⟩ => correctionModel F p

/-- The ambient complex: the representative of `E` padded by all the correction complexes. -/
private abbrev ambientProduct (F : ℤᵒᵖ ⥤ DerivedCategory A)
    (I : CochainComplex A ℤ) : CochainComplex A ℤ :=
  Limits.piObj.{w, v, max u v} (ambientFactor F I)

/-- The index set of the `i`-th filtration step: one copy of the `i`-th stage, together with
one padding complex for each index strictly above `i`. -/
private abbrev StepIndex (i : ℤ) : Type w := ULift.{w, 0} (Option {p : ℤ // i < p})

/-- The index of the `i`-th stage in the `i`-th filtration step. -/
private abbrev stepNone (i : ℤ) : StepIndex i := ⟨none⟩

/-- The index of the `p`-th padding complex in the `i`-th filtration step. -/
private abbrev stepSome (i : ℤ) (p : {p : ℤ // i < p}) : StepIndex i := ⟨some p⟩

/-- The family of factors of the `i`-th filtration step. -/
private abbrev stepFactor (F : ℤᵒᵖ ⥤ DerivedCategory A) (i : ℤ) :
    StepIndex i → CochainComplex A ℤ
  | ⟨none⟩ => modelAt F i
  | ⟨some p⟩ => correctionModel F p.val

/-- The `i`-th filtration step: the `i`-th stage padded by the correction complexes attached
to the indices strictly above `i`. -/
private abbrev stepProduct (F : ℤᵒᵖ ⥤ DerivedCategory A) (i : ℤ) :
    CochainComplex A ℤ := Limits.piObj.{w, v, max u v} (stepFactor F i)

/-- The embedding of the `i`-th filtration step into the ambient complex: on the `E`-factor
it is the map to the representative of `E`, on a padding factor above `i` it is the identity,
and on a padding factor at or below `i` it is `correctionFromModel`. -/
private noncomputable def stepEmbedding (E : DerivedCategory A)
    (F : ℤᵒᵖ ⥤ DerivedCategory A) (φ : F ⟶ (Functor.const ℤᵒᵖ).obj E)
    {I : CochainComplex A ℤ} (e : DerivedCategory.Q.obj I ≅ E)
    [I.IsKInjective] [∀ n, Injective (I.X n)] (i : ℤ) :
    stepProduct F i ⟶ ambientProduct F I :=
  Pi.lift fun
    | ⟨none⟩ => Pi.π (stepFactor F i) (stepNone i) ≫ modelMapToEAt E F φ e i
    | ⟨some p⟩ => by
        by_cases hip : i < p
        · exact Pi.π (stepFactor F i) (stepSome i ⟨p, hip⟩) ≫ 𝟙 (correctionModel F p)
        · exact Pi.π (stepFactor F i) (stepNone i) ≫
            correctionFromModel F i p (le_of_not_gt hip)

/-- The components of `stepEmbedding`. -/
private lemma stepEmbedding_component (E : DerivedCategory A)
    (F : ℤᵒᵖ ⥤ DerivedCategory A) (φ : F ⟶ (Functor.const ℤᵒᵖ).obj E)
    {I : CochainComplex A ℤ} (e : DerivedCategory.Q.obj I ≅ E)
    [I.IsKInjective] [∀ n, Injective (I.X n)] (i : ℤ) (j : AmbientIndex) :
    stepEmbedding E F φ e i ≫ Pi.π (ambientFactor F I) j =
      match j with
      | .up none => Pi.π (stepFactor F i) (stepNone i) ≫ modelMapToEAt E F φ e i
      | .up (.some p) => if h : i < p then
          Pi.π (stepFactor F i) (stepSome i ⟨p, h⟩)
        else Pi.π (stepFactor F i) (stepNone i) ≫
          correctionFromModel F i p (le_of_not_gt h) := by
  rcases j with ⟨j⟩
  cases j with
  | none => rw [stepEmbedding, Pi.lift_comp_π]
  | some p =>
      by_cases h : i < p
      · rw [stepEmbedding, Pi.lift_comp_π]
        simp [stepFactor, ambientFactor, stepSome, h, Category.comp_id]
      · rw [stepEmbedding, Pi.lift_comp_π]
        simp [stepFactor, ambientFactor, stepNone, h]

/-- The comparison map from the `j`-th to the `i`-th filtration step, for `i ≤ j`. -/
private noncomputable def transitionStep (F : ℤᵒᵖ ⥤ DerivedCategory A)
    (i j : ℤ) (hij : i ≤ j) : stepProduct F j ⟶ stepProduct F i :=
  Pi.lift fun
    | ⟨none⟩ => Pi.π (stepFactor F j) (stepNone j) ≫ modelDescent F i j hij
    | ⟨some p⟩ => by
        by_cases hjp : j < p.val
        · exact Pi.π (stepFactor F j) (stepSome j ⟨p.val, hjp⟩) ≫ 𝟙 (correctionModel F p.val)
        · exact Pi.π (stepFactor F j) (stepNone j) ≫
            correctionFromModel F j p.val (le_of_not_gt hjp)

/-- The components of `transitionStep`. -/
private lemma transitionStep_component (F : ℤᵒᵖ ⥤ DerivedCategory A)
    (i j : ℤ) (hij : i ≤ j) (k : StepIndex i) :
    transitionStep F i j hij ≫ Pi.π (stepFactor F i) k =
      match k with
      | .up none => Pi.π (stepFactor F j) (stepNone j) ≫ modelDescent F i j hij
      | .up (.some p) => if h : j < p.val then
          Pi.π (stepFactor F j) (stepSome j ⟨p.val, h⟩)
        else Pi.π (stepFactor F j) (stepNone j) ≫
          correctionFromModel F j p.val (le_of_not_gt h) := by
  rcases k with ⟨k⟩
  cases k with
  | none => rw [transitionStep, Pi.lift_comp_π]
  | some p =>
      by_cases h : j < p.val
      · rw [transitionStep, Pi.lift_comp_π]
        simp [stepFactor, stepSome, h, Category.comp_id]
      · rw [transitionStep, Pi.lift_comp_π]
        simp [stepFactor, stepNone, h]

/-- The comparison maps between filtration steps are compatible with the embeddings into the
ambient complex. -/
private lemma transitionStep_comp_stepEmbedding (E : DerivedCategory A)
    (F : ℤᵒᵖ ⥤ DerivedCategory A) (φ : F ⟶ (Functor.const ℤᵒᵖ).obj E)
    {I : CochainComplex A ℤ} (e : DerivedCategory.Q.obj I ≅ E)
    [I.IsKInjective] [∀ n, Injective (I.X n)] (i j : ℤ) (hij : i ≤ j) :
    transitionStep F i j hij ≫ stepEmbedding E F φ e i = stepEmbedding E F φ e j := by
  apply Pi.hom_ext
  intro k
  cases k with
  | up k => cases k with
   | none =>
      rw [Category.assoc, stepEmbedding_component E F φ e i ambientNone,
        stepEmbedding_component E F φ e j ambientNone]
      show transitionStep F i j hij ≫
          (Pi.π (stepFactor F i) (stepNone i) ≫ modelMapToEAt E F φ e i) =
        Pi.π (stepFactor F j) (stepNone j) ≫ modelMapToEAt E F φ e j
      rw [← Category.assoc, transitionStep_component, Category.assoc]
      exact congrArg (fun f => Pi.π (stepFactor F j) (stepNone j) ≫ f)
        (modelDescent_mapToE E F φ e i j hij)
   | some p =>
      rw [Category.assoc, stepEmbedding_component E F φ e i (ambientSome p),
        stepEmbedding_component E F φ e j (ambientSome p)]
      by_cases hip : i < p
      · by_cases hjp : j < p <;> simp [hip, hjp, transitionStep_component]
      · have hjp : ¬ j < p := fun hjp => hip (lt_of_le_of_lt hij hjp)
        simp only [hip, ↓reduceDIte, hjp]
        rw [← Category.assoc, transitionStep_component]
        simp only
        rw [Category.assoc, correctionFromModel_comp F j i p (le_of_not_gt hip) hij]

/-- The isomorphism between the object represented by the ambient complex and `E`, given by
the projection onto the representative of `E`. -/
private noncomputable def ambientProductIso (E : DerivedCategory A)
    (F : ℤᵒᵖ ⥤ DerivedCategory A) {I : CochainComplex A ℤ}
    (e : DerivedCategory.Q.obj I ≅ E) [I.IsKInjective] :
    DerivedCategory.Q.obj (ambientProduct F I) ≅ E := by
  have hπ : IsIso (DerivedCategory.Q.map (Pi.π (ambientFactor F I) ambientNone)) :=
    product_projection_isIso_of_isZero_factors (ambientFactor F I)
      (by intro j; cases j with | up j => cases j with
          | none => exact inferInstance
          | some p => exact correctionModel_isKInjective F p)
      ambientNone (by intro j hj; cases j with | up j => cases j with
          | none => exact (hj rfl).elim
          | some p => exact correctionModel_isZero F p)
  letI := hπ
  exact asIso (DerivedCategory.Q.map (Pi.π (ambientFactor F I) ambientNone)) ≪≫ e

/-- The `i`-th filtration step represents `F(i)`. -/
private noncomputable def stepProductIso (F : ℤᵒᵖ ⥤ DerivedCategory A) (i : ℤ) :
    DerivedCategory.Q.obj (stepProduct F i) ≅ F.obj (Opposite.op i) := by
  have hπ : IsIso (DerivedCategory.Q.map (Pi.π (stepFactor F i) (stepNone i))) :=
    product_projection_isIso_of_isZero_factors (stepFactor F i)
      (by intro j; cases j with | up j => cases j with
          | none => exact modelAt_isKInjective F i
          | some p => exact correctionModel_isKInjective F p.val)
      (stepNone i) (by intro j hj; cases j with | up j => cases j with
          | none => exact (hj rfl).elim
          | some p => exact correctionModel_isZero F p.val)
  letI := hπ
  exact asIso (DerivedCategory.Q.map (Pi.π (stepFactor F i) (stepNone i))) ≪≫ modelIsoAt F i

/-- The embedding of a filtration step into the ambient complex is a monomorphism. -/
private lemma stepEmbedding_mono (E : DerivedCategory A)
    (F : ℤᵒᵖ ⥤ DerivedCategory A) (φ : F ⟶ (Functor.const ℤᵒᵖ).obj E)
    {I : CochainComplex A ℤ} (e : DerivedCategory.Q.obj I ≅ E)
    [I.IsKInjective] [∀ n, Injective (I.X n)] (i : ℤ) :
    Mono (stepEmbedding E F φ e i) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  refine ⟨fun {X} (f g : X ⟶ (stepProduct F i).X n) hfg => ?_⟩
  have hcomponent (j : AmbientIndex) :
      (stepEmbedding E F φ e i).f n ≫ (Pi.π (ambientFactor F I) j).f n =
        match j with
        | .up none => (Pi.π (stepFactor F i) (stepNone i)).f n ≫
          (modelMapToEAt E F φ e i).f n
        | .up (.some p) => if h : i < p then
            (Pi.π (stepFactor F i) (stepSome i ⟨p, h⟩)).f n
          else (Pi.π (stepFactor F i) (stepNone i)).f n ≫
            (correctionFromModel F i p (le_of_not_gt h)).f n := by
    rcases j with ⟨j⟩
    have hh := congrArg (fun f => f.f n) (stepEmbedding_component E F φ e i ⟨j⟩)
    cases j with
    | none => simpa [HomologicalComplex.comp_f, ambientFactor] using hh
    | some p =>
        by_cases hp : i < p <;>
          simpa [HomologicalComplex.comp_f, ambientFactor, hp] using hh
  have hsource : ∀ j : StepIndex i,
      f ≫ (Pi.π (stepFactor F i) j).f n = g ≫ (Pi.π (stepFactor F i) j).f n := by
    intro j
    cases j with
    | up j =>
      cases j with
      | none =>
          have hcoord := congrArg
            (fun z => z ≫ (Pi.π (ambientFactor F I) (ambientSome i)).f n) hfg
          rw [Category.assoc, hcomponent (ambientSome i), Category.assoc,
            hcomponent (ambientSome i)] at hcoord
          have := functorialNullModel_inclusion_mono (modelAt F i) n
          apply (cancel_mono
            ((functorialNullModelInclusion (modelAt F i)).f n)).1
          simpa [Category.assoc, correctionFromModel, modelDescent,
            Int.leInduction_base] using hcoord
      | some p =>
          have hcoord := congrArg
            (fun z => z ≫ (Pi.π (ambientFactor F I) (ambientSome p.val)).f n) hfg
          rw [Category.assoc, hcomponent (ambientSome p.val), Category.assoc,
            hcomponent (ambientSome p.val)] at hcoord
          simpa [p.property] using hcoord
  apply (cancel_mono (Stacks.DerivedProducts.evalProdIso (stepFactor F i) n).hom).1
  apply Limits.Pi.hom_ext
  intro j
  rw [Category.assoc, Stacks.DerivedProducts.evalProdIso_hom_π, Category.assoc,
    Stacks.DerivedProducts.evalProdIso_hom_π]
  exact hsource j

/-- The filtered complex representing the inverse system: the ambient complex, filtered by
the images of the filtration steps. -/
private noncomputable def representationFiltered (E : DerivedCategory A)
    (F : ℤᵒᵖ ⥤ DerivedCategory A) (φ : F ⟶ (Functor.const ℤᵒᵖ).obj E)
    {I : CochainComplex A ℤ} (e : DerivedCategory.Q.obj I ≅ E)
    [I.IsKInjective] [∀ n, Injective (I.X n)] : CochainComplex.Filtered A where
  X := ambientProduct F I
  filtration := {
    toMonoOver := {
      obj i := by
        letI : Mono (stepEmbedding E F φ e i.unop) :=
          stepEmbedding_mono E F φ e i.unop
        exact MonoOver.mk (stepEmbedding E F φ e i.unop)
      map {i j} f := by
        letI : Mono (stepEmbedding E F φ e i.unop) :=
          stepEmbedding_mono E F φ e i.unop
        letI : Mono (stepEmbedding E F φ e j.unop) :=
          stepEmbedding_mono E F φ e j.unop
        exact MonoOver.homMk
          (show stepProduct F i.unop ⟶ stepProduct F j.unop from
            transitionStep F j.unop i.unop (leOfHom f.unop))
          (transitionStep_comp_stepEmbedding E F φ e j.unop i.unop (leOfHom f.unop))
      map_id := fun _ => Subsingleton.elim _ _
      map_comp := fun _ _ => Subsingleton.elim _ _
    }
  }

/-- The isomorphisms `stepProductIso` are natural in the index. -/
private lemma stepProductIso_naturality (F : ℤᵒᵖ ⥤ DerivedCategory A)
    {i j : ℤᵒᵖ} (f : i ⟶ j) :
    DerivedCategory.Q.map (transitionStep F j.unop i.unop (leOfHom f.unop)) ≫
        (stepProductIso F j.unop).hom =
      (stepProductIso F i.unop).hom ≫ F.map f := by
  let h := leOfHom f.unop
  have hf : opHomOfLE h = f := Subsingleton.elim _ _
  show DerivedCategory.Q.map (transitionStep F j.unop i.unop h) ≫
      (DerivedCategory.Q.map (Pi.π (stepFactor F j.unop) (stepNone j.unop)) ≫
        (modelIsoAt F j.unop).hom) =
    (DerivedCategory.Q.map (Pi.π (stepFactor F i.unop) (stepNone i.unop)) ≫
      (modelIsoAt F i.unop).hom) ≫ F.map f
  rw [← Category.assoc, ← DerivedCategory.Q.map_comp, transitionStep_component,
    DerivedCategory.Q.map_comp, modelDescent_spec, hf]
  simp [Category.assoc]

end

/-- Let `A` be a Grothendieck abelian category, `E` an object of `D(A)`, and `F` an inverse
system of objects of `D(A)` indexed by `ℤᵒᵖ` together with a compatible family of maps `φ` from
`F` to the constant system at `E`. Then there is a filtered cochain complex `K` whose underlying
complex represents `E`, whose derived filtration diagram is isomorphic to `F`, and whose
filtration inclusions induce the maps `φ`. -/
@[stacks 0ESJ]
theorem exists_filteredComplex_representation
    (E : DerivedCategory A) (F : ℤᵒᵖ ⥤ DerivedCategory A)
    (φ : F ⟶ (Functor.const ℤᵒᵖ).obj E) :
    ∃ (K : CochainComplex.Filtered A)
      (e : DerivedCategory.Q.obj K.X ≅ E)
      (η : K.filtration.diagram ⋙ DerivedCategory.Q ≅ F),
      ∀ i : ℤᵒᵖ,
        DerivedCategory.Q.map (K.filtration.ι.app i) ≫ e.hom =
          η.hom.app i ≫ φ.app i := by
  obtain ⟨I, hI, hterms, ⟨e⟩⟩ := exists_kInjective_representation E
  let : I.IsKInjective := hI
  have : ∀ n, Injective (I.X n) := hterms
  let K : CochainComplex.Filtered A := representationFiltered E F φ e
  let eK : DerivedCategory.Q.obj K.X ≅ E := ambientProductIso E F e
  let η : K.filtration.diagram ⋙ DerivedCategory.Q ≅ F :=
    NatIso.ofComponents (fun i => by
      simpa [K, representationFiltered] using stepProductIso F i.unop) (by
      intro i j f
      exact stepProductIso_naturality F f)
  refine ⟨K, eK, η, fun i => ?_⟩
  show DerivedCategory.Q.map (stepEmbedding E F φ e i.unop) ≫
      (DerivedCategory.Q.map (Pi.π (ambientFactor F I) ambientNone) ≫ e.hom) =
    (DerivedCategory.Q.map (Pi.π (stepFactor F i.unop) (stepNone i.unop)) ≫
      (modelIsoAt F i.unop).hom) ≫ φ.app i
  have hcomponent := stepEmbedding_component E F φ e i.unop ambientNone
  rw [← Category.assoc, ← DerivedCategory.Q.map_comp, hcomponent]
  simp only [ambientNone, stepNone] at *
  rw [DerivedCategory.Q.map_comp, modelMapToEAt_spec]
  simp [Category.assoc]

end Stacks.Injectives
