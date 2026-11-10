module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.Algebra.Homology.StupidTruncation
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
public import StacksFrontier.Homology.KFlat.FilteredColimitShifts
import StacksCore.Tactic.StacksAttribute

/-!
# Compact objects of a derived category in terms of a generating set

Let `A` be a Grothendieck abelian category and let `S` be a set of objects of `A` such that every
object of `A` is a quotient of a direct sum of members of `S`, and such that `Hom(E, -)` commutes
with direct sums for every `E ∈ S`. Then every compact object of `D(A)` is a direct summand, in
`D(A)`, of a bounded complex whose terms are *finite* direct sums of members of `S`.

The proof has three movements. First, a compact object `K` is bounded above: writing the chosen
preimage of `K` as the colimit of its canonical tower of truncations `τ_{≤ n}`, compactness makes
the identity of `K` factor through one stage, so `K` is a retract of a complex that is bounded
above, and retracts inherit the vanishing of homology in high degrees. Second, resolving that
complex by the objects which are direct sums of members of `S` and then truncating stupidly from
below — again a colimit through which compactness lets `K` factor — produces a complex `L`,
bounded in both directions, all of whose terms are such direct sums, with `K` a retract of
`Q L`. Third, each term is cut down to a *finite* direct sum one degree at a time: compactness
of the members of `S`, applied to the differential leaving the previous degree, and compactness
of `K`, applied to the projection onto the complementary summand, together confine the relevant
data to a finite subset of the index set; the complementary summand is then split off by passing
to the kernel of a map to a single-degree complex, which preserves the retraction and leaves the
other degrees unchanged. Finitely many such steps, one for each degree in the bounded range,
finish the proof.

## Main results

* `Stacks.Cohomology.CompactObjects.exists_retract_finiteComplex_of_isCompactObject`: the lemma
  above, Tag 094B.

## Implementation notes

Compactness is `CategoryTheory.IsCompactObject`, which says exactly that the `Hom` functor out
of the object commutes with direct sums; it is used both in `A`, for the members of `S`, and in
`D(A)`, for the object being analysed.

The third movement needs `Q : C(A) ⥤ D(A)` to preserve coproducts indexed by an arbitrary type
of the Grothendieck universe `w`, since the index set supplied by the generation hypothesis is
an arbitrary type of that universe. For a Grothendieck abelian category this comes from AB4:
`CochainComplex.KFlat.CoproductBridge.preservesCoproducts_Q_of_grothendieck` assembles
`HasCoproducts` and `AB4OfSize.ofShape` into
`CochainComplex.KFlat.CoproductBridge.HasExactCoproducts` and concludes.
The countable-shape results of
`StacksFrontier/Algebra/Homology/DerivedCategory/Coproducts.lean` do not suffice here, and its
arbitrary-shape result assumes exact countable products, i.e. AB4*, which a Grothendieck
abelian category need not satisfy.

The bounds are the strict ones, `IsStrictlyGE`/`IsStrictlyLE`, so that "bounded complex" is a
statement about the terms rather than about homology, and the terms are presented as isomorphic
to a coproduct indexed by `Fin n`, which is what "finite direct sum" means here.

## References

* [Stacks Project, Tag 094B](https://stacks.math.columbia.edu/tag/094B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open scoped ZeroObject

universe z w v u

namespace Stacks.Cohomology.CompactObjects

private def isCoproductOfS {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] (S : Set A) : ObjectProperty A := fun X =>
  IsZero X ∨ ∃ (I : Type w) (E : I → A), (∀ i, E i ∈ S) ∧ Nonempty (X ≅ ∐ E)

private lemma has_exact_countable_direct_sums_of_grothendieck
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A] :
    HasExactCountableDirectSums A := by
  have : HasCoproducts.{0} A := hasCoproducts_shrink
  have : AB4OfSize.{0} A := AB4OfSize_shrink A
  exact ⟨inferInstance, fun J hJ => by
    have : Countable J := hJ
    have : HasExactColimitsOfShape (Discrete J) A := CountableAB4.ofShape J
    exact ⟨inferInstance, inferInstance⟩⟩

private noncomputable def isColimit_of_eventually_isIso_eval
    {A : Type u} [Category.{v} A] [Abelian A]
    {F : ℕ ⥤ CochainComplex A ℤ} {c : Cocone F}
    (n₀ : ℤ → ℕ)
    (h : ∀ i n, n₀ i ≤ n → IsIso ((c.ι.app n).f i)) : IsColimit c := by
  apply HomologicalComplex.isColimitOfEval
  intro i
  let E := HomologicalComplex.eval A (ComplexShape.up ℤ) i
  have hev : (F ⋙ E).IsEventuallyConstantFrom (n₀ i) := by
    intro n φ
    have : IsIso ((c.ι.app (n₀ i)).f i) := h i (n₀ i) le_rfl
    have : IsIso ((c.ι.app n).f i) := h i n (leOfHom φ)
    have heq : ((F ⋙ E).map φ) ≫ (c.ι.app n).f i = (c.ι.app (n₀ i)).f i :=
      congrArg (fun f : F.obj (n₀ i) ⟶ c.pt => f.f i) (c.w φ)
    exact IsIso.of_isIso_fac_right heq
  have : IsIso ((E.mapCocone c).ι.app (n₀ i)) := h i (n₀ i) le_rfl
  exact hev.isColimitOfIsIso (E.mapCocone c)

private lemma mem_of_isColimit {J : Type*} [Category J] {G : J ⥤ AddCommGrpCat.{v}}
    {c : Cocone G} (hc : IsColimit c) (S : AddSubgroup c.pt)
    (hS : ∀ (j : J) (x : G.obj j), ConcreteCategory.hom (c.ι.app j) x ∈ S)
    (a : c.pt) : a ∈ S := by
  let d : Cocone G := Cocone.mk (AddCommGrpCat.of S)
    { app := fun j => AddCommGrpCat.ofHom
        ((ConcreteCategory.hom (c.ι.app j)).codRestrict S (hS j))
      naturality := by
        intro j j' f
        ext x
        exact Subtype.ext (ConcreteCategory.congr_hom (c.ι.naturality f) x) }
  have h : hc.desc d ≫ AddCommGrpCat.ofHom S.subtype =
      AddCommGrpCat.ofHom (AddMonoidHom.id c.pt) := by
    refine hc.hom_ext fun j => ?_
    rw [← Category.assoc, hc.fac d j]
    ext x
    rfl
  have h' := ConcreteCategory.congr_hom h a
  simp only [ConcreteCategory.comp_apply, AddCommGrpCat.hom_ofHom,
    AddMonoidHom.id_apply] at h'
  exact h' ▸ (ConcreteCategory.hom (hc.desc d) a).2

private lemma preservesColimitsOfShape_discrete_nat_of_compact {D : Type u}
    [Category.{v} D] [Preadditive D] [HasCountableCoproducts D] (K : D)
    [IsCompactObject.{w} K] :
    PreservesColimitsOfShape (Discrete ℕ)
      (preadditiveCoyoneda.obj (Opposite.op K)) := by
  classical
  constructor
  intro F
  let E : ℕ → D := F.obj ∘ Discrete.mk
  let E' : ULift.{w} ℕ → D := E ∘ fun i => i.down
  let P := ∐ E
  let c₀ : Cofan E := Cofan.mk P (Limits.Sigma.ι E)
  have hc₀ : IsColimit c₀ := coproductIsCoproduct E
  let c : Cofan E' := Cofan.mk P (fun i => Limits.Sigma.ι E i.down)
  have hc : IsColimit c := Cofan.isColimitEquivOfEquiv Equiv.ulift c₀ hc₀
  have hbijLift : Function.Bijective
      (CategoryTheory.cofanMap K (fun i : ULift.{w} ℕ => Limits.Sigma.ι E i.down)) :=
    CategoryTheory.bijective_cofanMap K ‹IsCompactObject.{w} K› _ hc
  let eIdx : ℕ ≃ ULift.{w} ℕ :=
    ⟨ULift.up, ULift.down, fun _ => rfl, fun _ => rfl⟩
  let eDS : DirectSum ℕ (fun i => (K ⟶ E i)) ≃+
      DirectSum (ULift.{w} ℕ) (fun i => (K ⟶ E i.down)) := DirectSum.equivCongrLeft eIdx
  let φ : (DirectSum ℕ fun i => (K ⟶ E i)) →+ (K ⟶ P) :=
    DirectSum.toAddMonoid fun i => Preadditive.rightComp K (Limits.Sigma.ι E i)
  have hφ : φ = (CategoryTheory.cofanMap K
      (fun i : ULift.{w} ℕ => Limits.Sigma.ι E i.down)).comp eDS.toAddMonoidHom := by
    apply DirectSum.addHom_ext
    intro i f
    have heq : eDS (DirectSum.of _ i f) = DirectSum.of _ (ULift.up i) f :=
      DirectSum.equivCongrLeft_of (β := fun j : ℕ => (K ⟶ E j)) eIdx (ULift.up i) f
    change (DirectSum.toAddMonoid
        (fun j : ℕ => Preadditive.rightComp K (Limits.Sigma.ι E j)))
        (DirectSum.of (fun j : ℕ => (K ⟶ E j)) i f) =
      (CategoryTheory.cofanMap K (fun j : ULift.{w} ℕ => Limits.Sigma.ι E j.down))
        (eDS (DirectSum.of (fun j : ℕ => (K ⟶ E j)) i f))
    rw [DirectSum.toAddMonoid_of, heq, CategoryTheory.cofanMap_of]
    rfl
  have hbij : Function.Bijective φ := by
    rw [hφ]
    exact hbijLift.comp eDS.bijective
  have hα : ∀ i g, φ (DirectSum.of _ i g) = g ≫ Limits.Sigma.ι E i := by
    intro i g
    rw [DirectSum.toAddMonoid_of]
    rfl
  let ι₀ : (i : ℕ) → (K ⟶ E i) →+
      (((∐ fun i => (preadditiveCoyoneda.obj (Opposite.op K)).obj (E i)) :
        AddCommGrpCat.{v}) : Type v) :=
    fun i => (Limits.Sigma.ι (fun i => (preadditiveCoyoneda.obj (Opposite.op K)).obj (E i)) i).hom
  let β : DirectSum ℕ (fun i => (K ⟶ E i)) →+
      (((∐ fun i => (preadditiveCoyoneda.obj (Opposite.op K)).obj (E i)) :
        AddCommGrpCat.{v}) : Type v) := DirectSum.toAddMonoid ι₀
  have hβ : ∀ i g, β (DirectSum.of _ i g) = ι₀ i g := fun _ _ => DirectSum.toAddMonoid_of _ _ _
  have hsc : ∀ i g,
      (sigmaComparison (preadditiveCoyoneda.obj (Opposite.op K)) E).hom (ι₀ i g)
        = g ≫ Limits.Sigma.ι E i := by
    intro i g
    change ((Limits.Sigma.ι (fun i => (preadditiveCoyoneda.obj (Opposite.op K)).obj (E i)) i) ≫
      sigmaComparison (preadditiveCoyoneda.obj (Opposite.op K)) E).hom g = _
    rw [ι_comp_sigmaComparison]
    rfl
  have key : ∀ x, (sigmaComparison (preadditiveCoyoneda.obj (Opposite.op K)) E).hom
      (β x) = φ x := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp only [map_zero]; rfl
    | of i g => rw [hβ, hsc, hα]
    | add x y hx hy => simp only [map_add, hx, hy]; rfl
  have hβsurj : Function.Surjective β := fun z =>
    mem_of_isColimit (colimit.isColimit (Discrete.functor
      (fun i => (preadditiveCoyoneda.obj (Opposite.op K)).obj (E i)))) β.range
      (fun j x => ⟨DirectSum.of _ j.as x, hβ j.as x⟩) z
  have hscIso : IsIso (sigmaComparison (preadditiveCoyoneda.obj (Opposite.op K)) E) := by
    refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨fun a b hab => ?_, fun f => ?_⟩
    · obtain ⟨a', rfl⟩ := hβsurj a
      obtain ⟨b', rfl⟩ := hβsurj b
      rw [key, key] at hab
      exact congrArg β (hbij.1 hab)
    · obtain ⟨a', ha'⟩ := hbij.2 f
      exact ⟨β a', (key a').trans ha'⟩
  have : PreservesColimit (Discrete.functor E) (preadditiveCoyoneda.obj (Opposite.op K)) :=
    PreservesCoproduct.of_iso_comparison _ _
  exact preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

private lemma exists_retract_of_colimit
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{z} A]
    {F₀ : ℕ ⥤ CochainComplex A ℤ} {c₀ : Cocone F₀} (hc₀ : IsColimit c₀)
    (K : DerivedCategory A) [IsCompactObject.{w} K] (e₀ : DerivedCategory.Q.obj c₀.pt ≅ K) :
    ∃ n : ℕ, Nonempty (Retract K (DerivedCategory.Q.obj (F₀.obj n))) := by
  have : HasColimit F₀ := ⟨_, hc₀⟩
  let e : DerivedCategory.Q.obj (colimit F₀) ≅ K :=
    DerivedCategory.Q.mapIso ((colimit.isColimit F₀).coconePointUniqueUpToIso hc₀) ≪≫ e₀
  have : HasFilteredColimitsOfSize.{0, 0} A := hasFilteredColimitsOfSize_shrink
  have : AB5OfSize.{0, 0} A := AB5OfSize_shrink.{0, 0, w, w} A
  have : HasExactColimitsOfShape ℕ A := AB5OfSize.ofShape ℕ
  have : HasCountableCoproducts (DerivedCategory A) :=
    derivedCategory_hasCountableCoproducts A has_exact_countable_direct_sums_of_grothendieck
  have : HasCoproduct (F₀ ⋙ DerivedCategory.Q).obj := inferInstance
  have hH : CategoryTheory.Pretriangulated.IsHomotopyColimit (F₀ ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.obj (colimit F₀)) :=
    DerivedCategory.isHomotopyColimit_Q_obj_colimit F₀
  have : PreservesColimitsOfShape (Discrete ℕ)
      (preadditiveCoyoneda.obj (Opposite.op K)) :=
    preservesColimitsOfShape_discrete_nat_of_compact K
  obtain ⟨p₀, q₀, hT₀⟩ := hH
  let p := p₀ ≫ e.hom
  let q := e.inv ≫ q₀
  have hT : Triangle.mk (Limits.Sigma.desc fun n => Limits.Sigma.ι _ n -
      (F₀ ⋙ DerivedCategory.Q).map (homOfLE (Nat.le_succ n)) ≫
        Limits.Sigma.ι _ (n + 1)) p q ∈ distTriang (DerivedCategory A) :=
    isomorphic_distinguished _ hT₀ _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm (by simp) (by simp [p]) (by simp [q]))
  obtain ⟨hc, hcι⟩ :=
    CategoryTheory.Pretriangulated.exists_iso_colimit_preadditiveCoyoneda_of_isHomotopyColimit
      (F₀ ⋙ DerivedCategory.Q) K p q hT
  obtain ⟨n, x, hx⟩ := AddCommGrpCat.exists_ι_apply_eq
    (colimit.isColimit ((F₀ ⋙ DerivedCategory.Q) ⋙
      preadditiveCoyoneda.obj (Opposite.op K))) (ConcreteCategory.hom hc.inv (𝟙 K))
  have hfactor : x ≫ Limits.Sigma.ι (F₀ ⋙ DerivedCategory.Q).obj n ≫ p = 𝟙 K := by
    have key : ConcreteCategory.hom hc.hom
        (ConcreteCategory.hom (colimit.ι ((F₀ ⋙ DerivedCategory.Q) ⋙
          preadditiveCoyoneda.obj (Opposite.op K)) n) x) = 𝟙 K :=
      hx ▸ Iso.inv_hom_id_apply hc (𝟙 K)
    have h1 := ConcreteCategory.congr_hom (hcι n) x
    simp only [ConcreteCategory.comp_apply] at h1
    exact h1.symm.trans key
  exact ⟨n, ⟨⟨x, Limits.Sigma.ι (F₀ ⋙ DerivedCategory.Q).obj n ≫ p, hfactor⟩⟩⟩

private lemma exists_upper_cohomology_bound_of_compact
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{z} A]
    (K : DerivedCategory A) [IsCompactObject.{w} K] :
    ∃ b : ℤ, K.IsLE b := by
  let K₀ := DerivedCategory.Q.objPreimage K
  let eK := DerivedCategory.Q.objObjPreimageIso K
  let F₀ := CochainComplex.KFlat.truncLESequence K₀
  obtain ⟨n, ⟨r⟩⟩ :=
    exists_retract_of_colimit (CochainComplex.KFlat.truncLECocone_isColimit K₀) K eK
  refine ⟨n, ?_⟩
  rw [DerivedCategory.isLE_iff]
  intro i hi
  let H := DerivedCategory.homologyFunctor A i
  have hFn : IsZero (H.obj (DerivedCategory.Q.obj (F₀.obj n))) := by
    have : (DerivedCategory.Q.obj (F₀.obj n)).IsLE (n : ℤ) := by
      change (DerivedCategory.Q.obj (K₀.truncLE (n : ℤ))).IsLE (n : ℤ)
      rw [DerivedCategory.isLE_Q_obj_iff]
      infer_instance
    exact DerivedCategory.isZero_of_isLE _ (n : ℤ) i hi
  apply (IsZero.iff_id_eq_zero _).2
  have hz : H.map r.i = 0 := hFn.eq_of_tgt _ _
  simpa [hz] using (r.map H).retract.symm

open HomologicalComplex StacksDraft.StupidTruncation in
private noncomputable def stupidTruncSequence {A : Type u} [Category.{v} A] [Abelian A]
    (L : CochainComplex A ℤ) : ℕ ⥤ CochainComplex A ℤ :=
  (show Monotone (fun n : ℕ => (n : ℤ)) from fun _ _ h => Int.ofNat_le.mpr h).functor ⋙
    stupidTruncTower L

open HomologicalComplex StacksDraft.StupidTruncation in
private noncomputable def stupidTruncCocone {A : Type u} [Category.{v} A] [Abelian A]
    (L : CochainComplex A ℤ) : Cocone (stupidTruncSequence L) :=
  Cocone.mk L
    { app := fun n => ιStupidTrunc L (ComplexShape.embeddingUpIntGE (-(n : ℤ)))
      naturality := fun n m f => by
        change stupidTruncGEMapLE L (neg_le_neg (Int.ofNat_le.mpr (leOfHom f))) ≫ _ = _ ≫ 𝟙 L
        rw [stupidTruncGEMapLE_ι, Category.comp_id] }

open HomologicalComplex StacksDraft.StupidTruncation in
private noncomputable def stupidTruncCocone_isColimit
    {A : Type u} [Category.{v} A] [Abelian A] (L : CochainComplex A ℤ) :
    IsColimit (stupidTruncCocone L) := by
  apply isColimit_of_eventually_isIso_eval (fun i => (-i).toNat)
  intro i n hn
  change IsIso ((ιStupidTrunc L (ComplexShape.embeddingUpIntGE (-(n : ℤ)))).f i)
  rw [ιStupidTruncGE_f _ _ _ (by omega)]
  infer_instance

private lemma isCoproductOfS_of_iso {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] (S : Set A) {X Y : A} (e : X ≅ Y)
    (h : isCoproductOfS S Y) : isCoproductOfS S X := by
  rcases h with h | ⟨I, E, hE, ⟨e'⟩⟩
  · exact Or.inl (h.of_iso e)
  · exact Or.inr ⟨I, E, hE, ⟨e ≪≫ e'⟩⟩

open HomologicalComplex StacksDraft.StupidTruncation in
private lemma exists_retract_bounded_generator_complex
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{z} A]
    (S : Set A)
    (hS : ∀ X : A, ∃ (I : Type w) (E : I → A),
      (∀ i, E i ∈ S) ∧ ∃ f : (∐ E) ⟶ X, Epi f)
    (K : DerivedCategory A) [IsCompactObject.{w} K] :
    ∃ (L : CochainComplex A ℤ) (a b : ℤ),
      L.IsStrictlyGE a ∧ L.IsStrictlyLE b ∧
      (∀ i, isCoproductOfS S (L.X i)) ∧
      Nonempty (Retract K (DerivedCategory.Q.obj L)) := by
  obtain ⟨b, hb⟩ := exists_upper_cohomology_bound_of_compact K
  let K₀ := DerivedCategory.Q.objPreimage K
  let eK := DerivedCategory.Q.objObjPreimageIso K
  have : K₀.IsLE b := by
    rw [← DerivedCategory.isLE_Q_obj_iff]
    have := hb
    exact DerivedCategory.TStructure.t.isLE_of_iso eK.symm b
  let P := isCoproductOfS S
  have hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (f : Y ⟶ X), Epi f := by
    intro X
    obtain ⟨I, E, hE, f, hf⟩ := hS X
    exact ⟨∐ E, Or.inr ⟨I, E, hE, ⟨Iso.refl _⟩⟩, f, hf⟩
  have : P.ContainsZero := ⟨0, isZero_zero A, Or.inl (isZero_zero A)⟩
  obtain ⟨L, f, hf, hL, hLb⟩ :=
    (CochainComplex.exists_quasiIso_prop P hP b).2 K₀
  let F := stupidTruncSequence L
  let e : DerivedCategory.Q.obj L ≅ K := asIso (DerivedCategory.Q.map f) ≪≫ eK
  obtain ⟨n, r⟩ := exists_retract_of_colimit
    (stupidTruncCocone_isColimit L) K e
  have hge : (F.obj n).IsStrictlyGE (-(n : ℤ)) :=
    inferInstanceAs (CochainComplex.IsStrictlyGE
      (L.stupidTrunc (ComplexShape.embeddingUpIntGE (-(n : ℤ)))) (-(n : ℤ)))
  have hle : (F.obj n).IsStrictlyLE b :=
    inferInstanceAs (CochainComplex.IsStrictlyLE
      (L.stupidTrunc (ComplexShape.embeddingUpIntGE (-(n : ℤ)))) b)
  refine ⟨F.obj n, -(n : ℤ), b, hge, hle, ?_, r⟩
  intro i
  by_cases hi : -(n : ℤ) ≤ i
  · exact isCoproductOfS_of_iso S (stupidTruncGEXIso L _ i hi) (hL i)
  · exact Or.inl (CochainComplex.isZero_of_isStrictlyGE (F.obj n) (-(n : ℤ)) i (by omega))



private lemma exists_finite_support_of_compact
    {C : Type*} [Category C] [Preadditive C] {I : Type w}
    {E : I → C} {Y K : C} (ι : ∀ i, E i ⟶ Y)
    (hι : IsColimit (Cofan.mk Y ι)) [IsCompactObject.{w} K] (f : K ⟶ Y) :
    ∃ s : Finset I, ∀ (Z : C) (g : Y ⟶ Z),
      (∀ i ∈ s, ι i ≫ g = 0) → f ≫ g = 0 := by
  classical
  obtain ⟨d, rfl⟩ := (bijective_cofanMap K inferInstance ι hι).2 f
  refine ⟨d.support, fun Z g hg => ?_⟩
  rw [← DirectSum.sum_support_of d, map_sum, Preadditive.sum_comp]
  apply Finset.sum_eq_zero
  intro i hi
  rw [cofanMap_of, Category.assoc, hg i hi, comp_zero]

private abbrev isFiniteCoproductOfS {A : Type u} [Category.{v} A] [Abelian A]
    (S : Set A) (X : A) : Prop :=
  ∃ (n : ℕ) (E : Fin n → A), (∀ j, E j ∈ S) ∧ Nonempty (X ≅ ∐ E)

private lemma isFiniteCoproductOfS_of_isZero
    {A : Type u} [Category.{v} A] [Abelian A] (S : Set A) {X : A} (hX : IsZero X) :
    isFiniteCoproductOfS S X :=
  ⟨0, Fin.elim0, fun i => Fin.elim0 i,
    ⟨hX.iso ((IsZero.iff_id_eq_zero _).2 (Limits.Sigma.hom_ext _ _ fun i => Fin.elim0 i))⟩⟩

private lemma isFiniteCoproductOfS_of_iso
    {A : Type u} [Category.{v} A] [Abelian A] (S : Set A) {X Y : A}
    (e : X ≅ Y) (h : isFiniteCoproductOfS S Y) : isFiniteCoproductOfS S X := by
  obtain ⟨n, E, hE, ⟨e'⟩⟩ := h
  exact ⟨n, E, hE, ⟨e ≪≫ e'⟩⟩

private lemma exists_finite_support_from_finite_coproduct
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    (S : Set A) (hcompact : ∀ E ∈ S, IsCompactObject.{w} E)
    {X : A} (hX : isFiniteCoproductOfS S X) {I : Type w} (E : I → A)
    (f : X ⟶ ∐ E) :
    ∃ s : Finset I, ∀ (Z : A) (g : (∐ E) ⟶ Z),
      (∀ i ∈ s, Limits.Sigma.ι E i ≫ g = 0) → f ≫ g = 0 := by
  classical
  obtain ⟨n, F, hF, ⟨e⟩⟩ := hX
  have hs (j : Fin n) := by
    have := hcompact (F j) (hF j)
    exact exists_finite_support_of_compact (Limits.Sigma.ι E) (coproductIsCoproduct E)
      (Limits.Sigma.ι F j ≫ e.inv ≫ f)
  choose s hs using hs
  refine ⟨Finset.univ.biUnion s, fun Z g hg => ?_⟩
  apply (cancel_epi e.inv).1
  apply Limits.Sigma.hom_ext
  intro j
  simpa only [Category.assoc, comp_zero] using
    hs j Z g (fun i hi => hg i (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩))

section CoproductProjection

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
  {I : Type w} (E : I → A) (p : I → Prop)

private noncomputable def summandInclusion : (∐ fun i : {i // p i} => E i) ⟶ ∐ E :=
  Limits.Sigma.desc fun i => Limits.Sigma.ι E i.val

private noncomputable def summandProjection : (∐ E) ⟶ ∐ fun i : {i // p i} => E i := by
  classical
  exact Limits.Sigma.desc fun i => if h : p i then
    Limits.Sigma.ι (fun i : {i // p i} => E i) ⟨i, h⟩ else 0

open Classical in
private lemma ι_summandProjection (i : I) :
    Limits.Sigma.ι E i ≫ summandProjection E p =
      if h : p i then Limits.Sigma.ι (fun i : {i // p i} => E i) ⟨i, h⟩ else 0 := by
  classical
  simp [summandProjection]

private lemma summandInclusion_projection :
    summandInclusion E p ≫ summandProjection E p = 𝟙 _ := by
  classical
  apply Limits.Sigma.hom_ext
  intro i
  simp [summandInclusion, summandProjection, i.property]

private lemma summandInclusion_projection_compl :
    summandInclusion E p ≫ summandProjection E (fun i => ¬ p i) = 0 := by
  classical
  apply Limits.Sigma.hom_ext
  intro i
  simp [summandInclusion, summandProjection, i.property]

private lemma summand_decomposition :
    summandProjection E p ≫ summandInclusion E p +
      summandProjection E (fun i => ¬ p i) ≫ summandInclusion E (fun i => ¬ p i) = 𝟙 _ := by
  classical
  apply Limits.Sigma.hom_ext
  intro i
  by_cases hi : p i <;> simp [Preadditive.comp_add, summandProjection, summandInclusion, hi]

private lemma summandProjection_epi : Epi (summandProjection E p) :=
  epi_of_epi_fac (summandInclusion_projection E p)

private noncomputable def kernel_summandProjection_compl_iso :
    kernel (summandProjection E (fun i => ¬ p i)) ≅ ∐ fun i : {i // p i} => E i := by
  let S := ShortComplex.mk (summandInclusion E p)
    (summandProjection E (fun i => ¬ p i)) (summandInclusion_projection_compl E p)
  let spl : S.Splitting :=
    { r := summandProjection E p
      s := summandInclusion E (fun i => ¬ p i)
      f_r := summandInclusion_projection E p
      s_g := summandInclusion_projection E (fun i => ¬ p i)
      id := summand_decomposition E p }
  exact (kernelIsKernel S.g).conePointUniqueUpToIso spl.shortExact.fIsKernel

private lemma summandProjection_factor (q : I → Prop) (hpq : ∀ i, p i → q i) :
    ∃ r : (∐ fun i : {i // ¬ p i} => E i) ⟶ ∐ fun i : {i // ¬ q i} => E i,
      summandProjection E (fun i => ¬ p i) ≫ r = summandProjection E (fun i => ¬ q i) ∧
      (∀ (i : {i // ¬ p i}), q i → Limits.Sigma.ι _ i ≫ r = 0) := by
  classical
  let r : (∐ fun i : {i // ¬ p i} => E i) ⟶ ∐ fun i : {i // ¬ q i} => E i :=
    Limits.Sigma.desc fun i : {i // ¬ p i} =>
    if h : ¬ q i then Limits.Sigma.ι (fun i : {i // ¬ q i} => E i) ⟨i, h⟩ else 0
  refine ⟨r, ?_, ?_⟩
  · apply Limits.Sigma.hom_ext
    intro i
    by_cases hi : p i
    · simp [summandProjection, r, hi, hpq i hi]
    · by_cases hq : q i <;> simp [summandProjection, r, hi, hq]
  · intro i hi
    simp [r, hi]

end CoproductProjection

private lemma retract_kernel_of_comp_eq_zero
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{z} A]
    {L M : CochainComplex A ℤ} (π : L ⟶ M) [Epi π]
    {K : DerivedCategory A} (r : Retract K (DerivedCategory.Q.obj L))
    (h : r.i ≫ DerivedCategory.Q.map π = 0) :
    Nonempty (Retract K (DerivedCategory.Q.obj (kernel π))) := by
  let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel π }
  obtain ⟨i, hi⟩ := Triangle.coyoneda_exact₂ _
    (DerivedCategory.triangleOfSES_distinguished hS) r.i h
  change r.i = i ≫ DerivedCategory.Q.map (kernel.ι π) at hi
  refine ⟨⟨i, DerivedCategory.Q.map (kernel.ι π) ≫ r.r, ?_⟩⟩
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun f => f ≫ r.r) hi.symm).trans r.retract)

private noncomputable def kernel_single_X_iso
    {A : Type u} [Category.{v} A] [Abelian A] {L : CochainComplex A ℤ}
    {M : A} {c : ℤ} (π : L ⟶ (HomologicalComplex.single A (.up ℤ) c).obj M)
    (i : ℤ) (hi : i ≠ c) : (kernel π).X i ≅ L.X i := by
  have hzero : π.f i = 0 := (HomologicalComplex.isZero_single_obj_X (.up ℤ) c M i hi).eq_of_tgt _ _
  have : IsIso (kernel.ι (π.f i)) := kernel.ι_of_zero hzero
  exact PreservesKernel.iso (HomologicalComplex.eval A (.up ℤ) i) π ≪≫ asIso (kernel.ι (π.f i))

private lemma kernel_isStrictlyGE
    {A : Type u} [Category.{v} A] [Abelian A] {L M : CochainComplex A ℤ}
    (π : L ⟶ M) (a : ℤ) [L.IsStrictlyGE a] : (kernel π).IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact IsZero.of_mono ((kernel.ι π).f i) (L.isZero_of_isStrictlyGE a i hi)

private lemma kernel_isStrictlyLE
    {A : Type u} [Category.{v} A] [Abelian A] {L M : CochainComplex A ℤ}
    (π : L ⟶ M) (b : ℤ) [L.IsStrictlyLE b] : (kernel π).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact IsZero.of_mono ((kernel.ι π).f i) (L.isZero_of_isStrictlyLE b i hi)

private lemma finite_coproduct_of_finset
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    (S : Set A) {I : Type w} (E : I → A) (hE : ∀ i, E i ∈ S) (s : Finset I) :
    isFiniteCoproductOfS S (∐ fun i : s => E i) := by
  classical
  let e := Fintype.equivFin s
  exact ⟨Fintype.card s, fun j => E (e.symm j), fun j => hE _,
    ⟨HasColimit.isoOfEquivalence (Discrete.equivalence e)
      (Discrete.natIso fun i => eqToIso (by simp))⟩⟩

private lemma exists_retract_finite_term
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{z} A]
    (S : Set A) (hcompact : ∀ E ∈ S, IsCompactObject.{w} E)
    {K : DerivedCategory A} [IsCompactObject.{w} K]
    (L : CochainComplex A ℤ) (a b c : ℤ) [L.IsStrictlyGE a] [L.IsStrictlyLE b]
    (hprev : isFiniteCoproductOfS S (L.X (c - 1)))
    (hc : isCoproductOfS S (L.X c)) (r : Retract K (DerivedCategory.Q.obj L)) :
    ∃ L' : CochainComplex A ℤ,
      L'.IsStrictlyGE a ∧ L'.IsStrictlyLE b ∧
      isFiniteCoproductOfS S (L'.X c) ∧
      (∀ i, i ≠ c → Nonempty (L'.X i ≅ L.X i)) ∧
      Nonempty (Retract K (DerivedCategory.Q.obj L')) := by
  classical
  rcases hc with hzero | ⟨I, E, hE, ⟨e⟩⟩
  · exact ⟨L, inferInstance, inferInstance, isFiniteCoproductOfS_of_isZero S hzero,
      fun i _ => ⟨Iso.refl _⟩, ⟨r⟩⟩
  obtain ⟨s, hs⟩ := exists_finite_support_from_finite_coproduct S hcompact hprev E
    (L.d (c - 1) c ≫ e.hom)
  let p : I → Prop := fun i => i ∈ s
  let E' : {i // ¬ p i} → A := fun i => E i
  let pr := summandProjection E (fun i => ¬ p i)
  have hpr : L.d (c - 1) c ≫ (e.hom ≫ pr) = 0 := by
    rw [← Category.assoc]
    apply hs
    intro i hi
    simp [pr, summandProjection, p, hi]
  let T := HomologicalComplex.single A (.up ℤ) c
  let π₀ : L ⟶ T.obj (∐ E') :=
    HomologicalComplex.mkHomToSingle (e.hom ≫ pr) (fun i hi => by
      obtain rfl : i = c - 1 := by
        change i + 1 = c at hi
        omega
      exact hpr)
  let G := T ⋙ DerivedCategory.Q (C := A)
  have : PreservesColimitsOfShape (Discrete {i // ¬ p i}) (DerivedCategory.Q (C := A)) :=
    CochainComplex.KFlat.CoproductBridge.preservesCoproducts_Q_of_grothendieck _
  have hco : IsColimit (Cofan.mk (G.obj (∐ E')) (fun i => G.map (Limits.Sigma.ι E' i))) :=
    (isColimitMapCoconeCofanMkEquiv G E' (Limits.Sigma.ι E')).1
      (isColimitOfPreserves G (coproductIsCoproduct E'))
  obtain ⟨t, ht⟩ := exists_finite_support_of_compact _ hco (r.i ≫ DerivedCategory.Q.map π₀)
  let s' : Finset I := s ∪ t.image Subtype.val
  let q : I → Prop := fun i => i ∈ s'
  obtain ⟨ρ, hρ, hρzero⟩ := summandProjection_factor E p q
    (fun i hi => Finset.mem_union_left _ hi)
  let π : L ⟶ T.obj (∐ fun i : {i // ¬ q i} => E i) := π₀ ≫ T.map ρ
  have hπ : r.i ≫ DerivedCategory.Q.map π = 0 := by
    change r.i ≫ DerivedCategory.Q.map (π₀ ≫ T.map ρ) = 0
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc]
    refine ht _ _ fun i hi => ?_
    change G.map (Limits.Sigma.ι E' i) ≫ G.map ρ = 0
    rw [← G.map_comp, hρzero i (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)),
      G.map_zero]
  have hπc : π.f c = e.hom ≫ summandProjection E (fun i => ¬ q i) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) c _).inv := by
    dsimp only [π, HomologicalComplex.comp_f]
    rw [show π₀.f c = (e.hom ≫ pr) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) c _).inv from
      HomologicalComplex.mkHomToSingle_f _ _]
    simp only [T, HomologicalComplex.single_map_f_self, Category.assoc]
    rw [Iso.inv_hom_id_assoc, ← Category.assoc pr, hρ]
  have : Epi π := by
    apply HomologicalComplex.epi_of_epi_f
    intro i
    by_cases hi : i = c
    · subst i
      rw [hπc]
      have := summandProjection_epi E (fun i => ¬ q i)
      infer_instance
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) c _ i hi).epi _
  have e' : (kernel π).X c ≅ ∐ fun i : s' => E i :=
    PreservesKernel.iso (HomologicalComplex.eval A (.up ℤ) c) π ≪≫
      kernel.mapIso (π.f c) (summandProjection E (fun i => ¬ q i)) e
        (HomologicalComplex.singleObjXSelf (.up ℤ) c _) (by rw [hπc]; simp) ≪≫
      kernel_summandProjection_compl_iso E q
  exact ⟨kernel π, kernel_isStrictlyGE π a, kernel_isStrictlyLE π b,
    isFiniteCoproductOfS_of_iso S e' (finite_coproduct_of_finset S E hE s'),
    fun i hi => ⟨kernel_single_X_iso π i hi⟩, retract_kernel_of_comp_eq_zero π r hπ⟩

private lemma exists_retract_finite_terms_below
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{z} A]
    (S : Set A) (hcompact : ∀ E ∈ S, IsCompactObject.{w} E)
    {K : DerivedCategory A} [IsCompactObject.{w} K]
    (L : CochainComplex A ℤ) (a b : ℤ) [L.IsStrictlyGE a] [L.IsStrictlyLE b]
    (hL : ∀ i, isCoproductOfS S (L.X i))
    (r : Retract K (DerivedCategory.Q.obj L)) (n : ℕ) :
    ∃ L' : CochainComplex A ℤ,
      L'.IsStrictlyGE a ∧ L'.IsStrictlyLE b ∧
      (∀ i, a + (n : ℤ) ≤ i → isCoproductOfS S (L'.X i)) ∧
      (∀ i, i < a + (n : ℤ) → isFiniteCoproductOfS S (L'.X i)) ∧
      Nonempty (Retract K (DerivedCategory.Q.obj L')) := by
  induction n with
  | zero =>
    refine ⟨L, inferInstance, inferInstance, fun i _ => hL i, ?_, ⟨r⟩⟩
    intro i hi
    exact isFiniteCoproductOfS_of_isZero S (L.isZero_of_isStrictlyGE a i (by omega))
  | succ n ih =>
    obtain ⟨M, hMa, hMb, hM, hMf, ⟨rM⟩⟩ := ih
    have := hMa
    have := hMb
    obtain ⟨M', hM'a, hM'b, hMc, he, hr⟩ := exists_retract_finite_term S hcompact M a b
      (a + n) (hMf _ (by omega)) (hM _ le_rfl) rM
    refine ⟨M', hM'a, hM'b, ?_, ?_, hr⟩
    · intro i hi
      obtain ⟨e⟩ := he i (by omega)
      exact isCoproductOfS_of_iso S e (hM i (by omega))
    · intro i hi
      by_cases hic : i = a + n
      · subst i
        exact hMc
      · obtain ⟨e⟩ := he i hic
        exact isFiniteCoproductOfS_of_iso S e (hMf i (by omega))

/-- A compact derived object is a summand of a finite complex of finite sums
of compact generators of the abelian category. -/
@[stacks 094B]
public theorem exists_retract_finiteComplex_of_isCompactObject
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{z} A]
    (S : Set A)
    (hS : ∀ X : A, ∃ (I : Type w) (E : I → A),
      (∀ i, E i ∈ S) ∧ ∃ f : (∐ E) ⟶ X, Epi f)
    (hcompact : ∀ E ∈ S, IsCompactObject.{w} E)
    (K : DerivedCategory A) [IsCompactObject.{w} K] :
    ∃ (L : CochainComplex A ℤ) (a b : ℤ),
      L.IsStrictlyGE a ∧ L.IsStrictlyLE b ∧
      (∀ i : ℤ, ∃ (n : ℕ) (E : Fin n → A),
        (∀ j, E j ∈ S) ∧ Nonempty (L.X i ≅ ∐ E)) ∧
      Nonempty (Retract K (DerivedCategory.Q.obj L)) := by
  obtain ⟨M, a, b, hMa, hMb, hM, ⟨rM⟩⟩ := exists_retract_bounded_generator_complex S hS K
  have := hMa
  have := hMb
  obtain ⟨L, hLa, hLb, _, hLf, hr⟩ := exists_retract_finite_terms_below S hcompact M a b hM rM
    (b + 1 - a).toNat
  have := hLb
  refine ⟨L, a, b, hLa, hLb, ?_, hr⟩
  intro i
  by_cases hi : i < a + ((b + 1 - a).toNat : ℤ)
  · exact hLf i hi
  · exact isFiniteCoproductOfS_of_isZero S (L.isZero_of_isStrictlyLE b i (by omega))
end Stacks.Cohomology.CompactObjects

end
