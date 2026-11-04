module

import Mathlib.Algebra.Order.Ring.Star
public import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentability
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedColimits
import StacksFrontier.CategoryTheory.Triangulated.Elementary
public import StacksFrontier.CategoryTheory.Triangulated.Generators
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Compact objects and the thick subcategory they span

Let `D` be a (pre-)triangulated category with direct sums. An object `K` of `D` is *compact*
(`CategoryTheory.IsCompactObject`, [Stacks, Tag 07LS]) when the canonical map
`⨁ i, Hom(K, E i) ⟶ Hom(K, ∐ E)` is bijective for every family `E` whose direct sum exists. This
file develops the basic theory of the compact objects of `D`.

* The compact objects span a full subcategory `D_c` of `D` which is strictly full,
  (pre-)triangulated, saturated and Karoubian: it is closed under isomorphisms, contains the zero
  object, is stable under the shifts, is closed under extensions in distinguished triangles, is
  closed under passing to direct summands, and every idempotent in it splits. So `D_c` is a thick
  triangulated subcategory of `D`.
* Compactness is transferred along isomorphisms, adjunctions of additive functors, morphisms of
  distinguished triangles and full, faithful, additive functors (see the section docstring of
  *Transfer of compactness along a functor* below).

## Main results

* `isClosedUnderIsomorphisms_isTriangulated_isSaturated_and_isIdempotentComplete_isCompactObject`
  (in the `CategoryTheory` namespace): the property of being a compact object is closed under
  isomorphisms, is a triangulated subcategory of `D`, is saturated, and the full subcategory it
  spans is idempotent complete.
* `CategoryTheory.isCompactObject_sigma`: a finite direct sum of compact objects is compact.

## Implementation notes

*The compactness map.* Compactness of `K` is the bijectivity of `⨁ i, (K ⟶ E i) → (K ⟶ ∐ E)`. The
proofs below all go through the same two elementary transfer principles for such maps: bijectivity
passes along a commutative square with bijective horizontal maps (`Bijective.of_comm_bijective`)
and it descends to a retract (`Bijective.of_retract`). Formulating the bijectivity for an arbitrary
colimit cofan rather than for the chosen coproduct (`bijective_cofanMap`) is what makes the shift
case a one-line computation: the shift functor carries a colimit cofan of `E` to a colimit cofan of
the shifted family, and the hom-group bijection `(K⟦n⟧ ⟶ M) ≃+ (K ⟶ M⟦-n⟧)` commutes with
postcomposition on the nose. This compactness toolkit is shared by all four results of the file.

*The closure properties of `D_c`.* The source's four adjectives are read in Mathlib's vocabulary.
*Strictly full* is `ObjectProperty.IsClosedUnderIsomorphisms`: fullness is automatic for
`ObjectProperty.FullSubcategory`, so the content is closure under isomorphisms.
*(Pre-)triangulated subcategory* is `ObjectProperty.IsTriangulated`, from which `Pretriangulated`,
and `IsTriangulated` when `D` is triangulated, follow for the full subcategory by
`ObjectProperty.instPretriangulatedFullSubcategory` and
`ObjectProperty.instIsTriangulatedFullSubcategory`; stating it for the property rather than for the
subcategory is the stronger reading, as it also fixes which objects the subcategory has.
*Saturated* is `ObjectProperty.IsSaturated` ([Stacks, Tag 05RB]) and *Karoubian* is
`CategoryTheory.IsIdempotentComplete` ([Stacks, Tag 09SG]) of the full subcategory. Together with
the first conjunct, the extension property upgrades from `P.isoClosure` to `P`, i.e. to
`ObjectProperty.ext_of_isTriangulatedClosed₂` and its variants. The conjuncts are `Prop`-valued
classes, so a user installs the one wanted with `haveI` and then has the API of that class for
compact objects.

Closure under extensions is proved as `IsTriangulatedClosed₃`, which is the form the source's proof
takes, and `IsTriangulatedClosed₂` is deduced from it by rotation. In place of the source's appeal
to the five lemma the argument is the underlying diagram chase, carried out on the direct sums of
morphism groups: the four objects `X`, `Y`, `X⟦1⟧`, `Y⟦1⟧` of the two exact rows are compact, and
that is exactly what the chase consumes. The step of the chase that leaves the two given rows is
the exactness of `Hom(-, M)` at `X⟦1⟧`, recorded here as `triangle_yoneda_exact₁`, the missing
first member of Mathlib's family `Triangle.yoneda_exact₂`, `Triangle.yoneda_exact₃`. Karoubianness
of the subcategory is not proved inside it: the ambient category `D` is Karoubian by
[Stacks, Tag 05QW] (`Pretriangulated.isIdempotentComplete_of_hasCountableProducts_or_coproducts`),
whose second conjunct is the case of countable direct sums, so an idempotent of a compact object
splits in `D`, and the object it splits off is a retract of a compact object, hence compact. The
cokernels of split monomorphisms that the underlying criterion 05QV(2) asks for are supplied by
05QW itself, which is why they do not appear here.

## References

* [Stacks project, Tag 09QH](https://stacks.math.columbia.edu/tag/09QH)
* [Stacks project, Tag 07LS](https://stacks.math.columbia.edu/tag/07LS)
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits Preadditive Pretriangulated ZeroObject

/-! ### Compact objects -/

section CompactObject

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- An object `K` of a preadditive category is *compact* if for every family `E : I → C` whose
direct sum exists, the map `⨁ i, (K ⟶ E i) → (K ⟶ ∐ E)` sending a finitely supported family
`(f i)` to `∑ i, f i ≫ Sigma.ι E i` is bijective; that is, a morphism from `K` into a direct sum
factors through a finite subsum in exactly one way. -/
@[stacks 07LS]
public class IsCompactObject (K : C) : Prop where
  /-- For every family `E : I → C` admitting a direct sum, the canonical map from the direct sum
  of the groups `K ⟶ E i` to the group `K ⟶ ∐ E` is bijective. -/
  bijective_toAddMonoid_rightComp_sigmaι {I : Type w} [DecidableEq I] (E : I → C)
      [HasCoproduct E] :
    Function.Bijective
      (DirectSum.toAddMonoid fun i => Preadditive.rightComp K (Limits.Sigma.ι E i))

end CompactObject

/-! ### Two transfer principles for bijectivity -/

/-- Bijectivity transfers across a commutative square whose horizontal maps are bijective
(injectivity of the right-hand one is enough). -/
private lemma Bijective.of_comm_bijective {A B A' B' : Type*} {φ : A → B} {ψ : A' → B'}
    {α : A' → A} {β : B' → B} (hα : Function.Bijective α) (hβ : Function.Injective β)
    (hcomm : ∀ a, φ (α a) = β (ψ a)) (hφ : Function.Bijective φ) : Function.Bijective ψ := by
  refine ⟨fun a b hab => hα.1 (hφ.1 ?_), fun b => ?_⟩
  · rw [hcomm, hcomm, hab]
  · obtain ⟨a, ha⟩ := hφ.2 (β b)
    obtain ⟨a', rfl⟩ := hα.2 a
    exact ⟨a', hβ (by rw [← hcomm, ha])⟩

/-- Bijectivity descends to a retract: if `ψ` is a retract of `φ` in the category of maps, then
`ψ` is bijective as soon as `φ` is. -/
private lemma Bijective.of_retract {A B A' B' : Type*} {φ : A → B} {ψ : A' → B'}
    {α : A' → A} {β : A → A'} {γ : B' → B} {δ : B → B'}
    (hβα : ∀ a, β (α a) = a) (hδγ : ∀ b, δ (γ b) = b)
    (h₁ : ∀ a, φ (α a) = γ (ψ a)) (h₂ : ∀ a, ψ (β a) = δ (φ a))
    (hφ : Function.Bijective φ) : Function.Bijective ψ := by
  refine ⟨fun a b hab => ?_, fun b => ?_⟩
  · have h : α a = α b := hφ.1 (by rw [h₁, h₁, hab])
    rw [← hβα a, ← hβα b, h]
  · obtain ⟨a, ha⟩ := hφ.2 (γ b)
    exact ⟨β a, by rw [h₂, ha, hδγ]⟩

/-! ### Componentwise maps of direct sums -/

section DirectSumMap

variable {ι : Type*} {β : ι → Type*} {γ : ι → Type*}
  [∀ i, AddCommGroup (β i)] [∀ i, AddCommGroup (γ i)]

/-- The componentwise image of a family of additive maps, as a map of direct sums. -/
private def dsMap (f : ∀ i, β i →+ γ i) :
    (DirectSum ι fun i => β i) →+ DirectSum ι fun i => γ i :=
  DFinsupp.mapRange.addMonoidHom f

private lemma dsMap_apply (f : ∀ i, β i →+ γ i) (x : DirectSum ι fun i => β i) (i : ι) :
    dsMap f x i = f i (x i) :=
  rfl

private lemma dsMap_of [DecidableEq ι] (f : ∀ i, β i →+ γ i) (i : ι) (y : β i) :
    dsMap f (DirectSum.of β i y) = DirectSum.of γ i (f i y) := by
  refine DFinsupp.ext fun k => ?_
  rw [dsMap_apply]
  by_cases h : i = k
  · subst h; rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
  · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), DirectSum.of_eq_of_ne _ _ _ (Ne.symm h),
      map_zero]

private lemma bijective_dsMap (f : ∀ i, β i →+ γ i) (hf : ∀ i, Function.Bijective (f i)) :
    Function.Bijective (dsMap f) := by
  refine ⟨fun x y hxy => DFinsupp.ext fun i => (hf i).1 ?_, fun z => ?_⟩
  · rw [← dsMap_apply, ← dsMap_apply, hxy]
  · refine ⟨dsMap (fun i => (AddEquiv.ofBijective (f i) (hf i)).symm.toAddMonoidHom) z,
      DFinsupp.ext fun i => ?_⟩
    rw [dsMap_apply, dsMap_apply]
    exact (AddEquiv.ofBijective (f i) (hf i)).apply_symm_apply _

/-- A componentwise surjectivity statement lifts to the direct sums. -/
private lemma exists_dsMap_eq (f : ∀ i, β i →+ γ i)
    (z : DirectSum ι fun i => γ i) (h : ∀ i, ∃ y, f i y = z i) : ∃ x, dsMap f x = z := by
  classical
  refine ⟨DFinsupp.mk (DFinsupp.support z) fun i => (h i).choose, DFinsupp.ext fun i => ?_⟩
  rw [dsMap_apply, DFinsupp.mk_apply]
  split_ifs with hi
  · exact (h i).choose_spec
  · rw [map_zero, DFinsupp.notMem_support_iff.1 hi]

end DirectSumMap

/-! ### The compactness map of a cofan -/

section Preadditive

variable {D : Type u} [Category.{v} D] [Preadditive D]

/-- The map `⨁ i, (K ⟶ E i) → (K ⟶ S)` attached to a family of morphisms `E i ⟶ S`, sending a
finitely supported family `(f i)` to `∑ i, f i ≫ j i`. Compactness of `K` is its bijectivity
whenever the `j i` exhibit `S` as the direct sum of the `E i`. -/
def cofanMap (K : D) {I : Type*} [DecidableEq I] {E : I → D} {S : D}
    (j : ∀ i, E i ⟶ S) : (DirectSum I fun i => (K ⟶ E i)) →+ (K ⟶ S) :=
  DirectSum.toAddMonoid fun i => Preadditive.rightComp K (j i)

/-- On the `i`-th summand, `cofanMap K j` sends `y : K ⟶ E i` to `y ≫ j i`. -/
lemma cofanMap_of (K : D) {I : Type*} [DecidableEq I] {E : I → D} {S : D}
    (j : ∀ i, E i ⟶ S) (i : I) (y : K ⟶ E i) :
    cofanMap K j (DirectSum.of _ i y) = y ≫ j i :=
  DirectSum.toAddMonoid_of _ _ _

/-- Precomposition with `u : L ⟶ K`, componentwise on `⨁ i, (K ⟶ E i)`. -/
private def dsPrecomp {I : Type*} (E : I → D) {K L : D} (u : L ⟶ K) :
    (DirectSum I fun i => (K ⟶ E i)) →+ DirectSum I fun i => (L ⟶ E i) :=
  dsMap fun i => Preadditive.leftComp (E i) u

private lemma dsPrecomp_apply {I : Type*} (E : I → D) {K L : D} (u : L ⟶ K)
    (x : DirectSum I fun i => (K ⟶ E i)) (i : I) : dsPrecomp E u x i = u ≫ x i :=
  dsMap_apply _ _ _

private lemma dsPrecomp_id {I : Type*} (E : I → D) {K : D}
    (x : DirectSum I fun i => (K ⟶ E i)) : dsPrecomp E (𝟙 K) x = x :=
  DFinsupp.ext fun i => by rw [dsPrecomp_apply, Category.id_comp]

private lemma dsPrecomp_dsPrecomp {I : Type*} (E : I → D) {K L M : D} (u : L ⟶ K) (v : K ⟶ M)
    (x : DirectSum I fun i => (M ⟶ E i)) :
    dsPrecomp E u (dsPrecomp E v x) = dsPrecomp E (u ≫ v) x :=
  DFinsupp.ext fun i => by
    rw [dsPrecomp_apply, dsPrecomp_apply, dsPrecomp_apply, Category.assoc]

private lemma dsPrecomp_zero {I : Type*} (E : I → D) {K L : D}
    (x : DirectSum I fun i => (K ⟶ E i)) : dsPrecomp E (0 : L ⟶ K) x = 0 :=
  DFinsupp.ext fun i => by rw [dsPrecomp_apply, zero_comp, DFinsupp.zero_apply]

private lemma cofanMap_dsPrecomp {I : Type*} [DecidableEq I] {E : I → D} {S : D}
    (j : ∀ i, E i ⟶ S) {K L : D} (u : L ⟶ K) (x : DirectSum I fun i => (K ⟶ E i)) :
    cofanMap L j (dsPrecomp E u x) = u ≫ cofanMap K j x := by
  have h : (cofanMap L j).comp (dsPrecomp E u)
      = (Preadditive.leftComp S u).comp (cofanMap K j) := by
    refine DirectSum.addHom_ext fun i y => ?_
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, dsPrecomp, dsMap_of,
      cofanMap_of, Preadditive.leftComp, AddMonoidHom.mk'_apply, Category.assoc]
  simpa only [AddMonoidHom.coe_comp, Function.comp_apply, Preadditive.leftComp,
    AddMonoidHom.mk'_apply] using DFunLike.congr_fun h x

/-- Composition with an isomorphism is bijective on morphism groups. -/
private lemma bijective_rightComp_of_isIso (K : D) {S T : D} (v : S ⟶ T) [IsIso v] :
    Function.Bijective (Preadditive.rightComp K v) := by
  refine ⟨fun a b hab => ?_, fun g => ⟨g ≫ inv v, ?_⟩⟩
  · simpa only [Preadditive.rightComp, AddMonoidHom.mk'_apply, cancel_mono] using hab
  · simp [Preadditive.rightComp]

/-- The compactness map of a colimit cofan factors the compactness map of the chosen coproduct
through the canonical isomorphism of the two vertices. -/
private lemma cofanMap_eq_of_isColimit (K : D) {I : Type*} [DecidableEq I] {E : I → D} {S : D}
    (j : ∀ i, E i ⟶ S) (hc : IsColimit (Cofan.mk S j)) [HasCoproduct E]
    (x : DirectSum I fun i => (K ⟶ E i)) :
    cofanMap K j x = cofanMap K (Limits.Sigma.ι E) x ≫
      ((coproductIsCoproduct E).coconePointUniqueUpToIso hc).hom := by
  have hj : ∀ i, Limits.Sigma.ι E i ≫ ((coproductIsCoproduct E).coconePointUniqueUpToIso hc).hom
      = j i := fun i => (coproductIsCoproduct E).comp_coconePointUniqueUpToIso_hom hc ⟨i⟩
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, zero_comp]
  | of i y => rw [cofanMap_of, cofanMap_of, Category.assoc, hj]
  | add x y hx hy => rw [map_add, map_add, Preadditive.add_comp, hx, hy]

variable [HasCoproducts.{w} D]

omit [HasCoproducts.{w} D] in
private lemma bijective_cofanMap_sigmaι (K : D) (hK : IsCompactObject.{w} K) {I : Type w}
    [DecidableEq I] (E : I → D) [HasCoproduct E] :
    Function.Bijective (cofanMap K (Limits.Sigma.ι E)) :=
  hK.bijective_toAddMonoid_rightComp_sigmaι E

omit [HasCoproducts.{w} D] in
/-- Compactness tested against an arbitrary colimit cofan, not just the chosen coproduct. The
direct sum of the family need not exist in `D`: the cofan exhibits it. -/
lemma bijective_cofanMap (K : D) (hK : IsCompactObject.{w} K) {I : Type w}
    [DecidableEq I] {E : I → D} {S : D} (j : ∀ i, E i ⟶ S)
    (hc : IsColimit (Cofan.mk S j)) : Function.Bijective (cofanMap K j) := by
  have : HasCoproduct E := ⟨_, hc⟩
  have h : cofanMap K j = (Preadditive.rightComp K
      ((coproductIsCoproduct E).coconePointUniqueUpToIso hc).hom).comp
      (cofanMap K (Limits.Sigma.ι E)) :=
    AddMonoidHom.ext (cofanMap_eq_of_isColimit K j hc)
  rw [h]
  exact (bijective_rightComp_of_isIso K _).comp (bijective_cofanMap_sigmaι K hK E)

omit [HasCoproducts.{w} D] in
/-- A retract of a compact object is compact. -/
lemma isCompactObject_of_retract {X Y : D} (hX : IsCompactObject.{w} X)
    (i : Y ⟶ X) (e : X ⟶ Y) (hie : i ≫ e = 𝟙 Y) : IsCompactObject.{w} Y := by
  constructor
  intro I _ E _
  show Function.Bijective (cofanMap Y (Limits.Sigma.ι E))
  refine Bijective.of_retract (φ := cofanMap X (Limits.Sigma.ι E))
    (ψ := cofanMap Y (Limits.Sigma.ι E)) (α := dsPrecomp E e) (β := dsPrecomp E i)
    (γ := fun t => e ≫ t) (δ := fun t => i ≫ t) (fun a => ?_) (fun b => ?_)
    (fun a => cofanMap_dsPrecomp _ _ _) (fun a => cofanMap_dsPrecomp _ _ _)
    (bijective_cofanMap_sigmaι X hX E)
  · rw [dsPrecomp_dsPrecomp, hie, dsPrecomp_id]
  · rw [← Category.assoc, hie, Category.id_comp]

omit [HasCoproducts D] in
/-- Compactness is closed under isomorphisms. -/
lemma isClosedUnderIsomorphisms_isCompactObject :
    ObjectProperty.IsClosedUnderIsomorphisms (IsCompactObject.{w, _, _} (C := D)) :=
  ⟨fun φ hX => isCompactObject_of_retract hX φ.inv φ.hom φ.inv_hom_id⟩

end Preadditive

attribute [local instance] isClosedUnderIsomorphisms_isCompactObject

/-! ### Direct summands and the zero object -/

section Summands

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasCoproducts.{w} D]

omit [HasCoproducts D] in
/-- Compactness is saturated: a direct summand of a compact object is compact. -/
private lemma isSaturated_isCompactObject :
    ObjectProperty.IsSaturated (IsCompactObject.{w, _, _} (C := D)) where
  isoClosure_of_biprod_left {X Y} _ h := by
    rw [ObjectProperty.isoClosure_eq_self] at h ⊢
    exact isCompactObject_of_retract h biprod.inl biprod.fst biprod.inl_fst
  isoClosure_of_biprod_right {X Y} _ h := by
    rw [ObjectProperty.isoClosure_eq_self] at h ⊢
    exact isCompactObject_of_retract h biprod.inr biprod.snd biprod.inr_snd

end Summands

section Zero

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D]

/-- The zero object is compact. -/
private lemma isCompactObject_zero : IsCompactObject.{w} (0 : D) := by
  constructor
  intro I _ E _
  exact ⟨fun a b _ => DFinsupp.ext fun i => (isZero_zero D).eq_of_src _ _,
    fun t => ⟨0, (isZero_zero D).eq_of_src _ _⟩⟩

private lemma containsZero_isCompactObject :
    ObjectProperty.ContainsZero (IsCompactObject.{w, _, _} (C := D)) :=
  ⟨⟨0, isZero_zero D, isCompactObject_zero⟩⟩

end Zero

/-! ### Compactness and the shift -/

section Shift

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [HasCoproducts.{w} D]

/-- A shift of a compact object is compact. -/
lemma isCompactObject_shift {K : D} (hK : IsCompactObject.{w} K) (n : ℤ) :
    IsCompactObject.{w} (K⟦n⟧) := by
  classical
  constructor
  intro I _ E _
  show Function.Bijective (cofanMap (K⟦n⟧) (Limits.Sigma.ι E))
  have hc : IsColimit (Cofan.mk ((shiftFunctor D (-n)).obj (∐ E))
      fun i => (shiftFunctor D (-n)).map (Limits.Sigma.ι E i)) :=
    isColimitCofanMkObjOfIsColimit _ E _ (coproductIsCoproduct E)
  let ε : K ≅ (shiftFunctor D (-n)).obj (K⟦n⟧) :=
    (shiftFunctorCompIsoId D n (-n) (add_neg_cancel n)).symm.app K
  let W : ∀ M : D, (K⟦n⟧ ⟶ M) →+ (K ⟶ (shiftFunctor D (-n)).obj M) := fun M =>
    (Preadditive.leftComp ((shiftFunctor D (-n)).obj M) ε.hom).comp
      (shiftFunctor D (-n)).mapAddHom
  have hW : ∀ (M : D) (a : K⟦n⟧ ⟶ M), W M a = ε.hom ≫ (shiftFunctor D (-n)).map a :=
    fun _ _ => rfl
  have hWbij : ∀ M : D, Function.Bijective (W M) := by
    intro M
    refine ⟨fun a b hab => (shiftFunctor D (-n)).map_injective ?_, fun t => ?_⟩
    · rw [hW, hW] at hab
      exact (cancel_epi ε.hom).1 hab
    · obtain ⟨a, ha⟩ := (shiftFunctor D (-n)).map_surjective (ε.inv ≫ t)
      exact ⟨a, by rw [hW, ha, Iso.hom_inv_id_assoc]⟩
  have key : (cofanMap K fun i => (shiftFunctor D (-n)).map (Limits.Sigma.ι E i)).comp
        (dsMap fun i => W (E i))
      = (W (∐ E)).comp (cofanMap (K⟦n⟧) (Limits.Sigma.ι E)) := by
    refine DirectSum.addHom_ext fun i y => ?_
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, dsMap_of, cofanMap_of, hW,
      Functor.map_comp, Category.assoc]
  refine Bijective.of_comm_bijective (bijective_dsMap _ fun i => hWbij (E i)) (hWbij (∐ E)).1
    (fun a => ?_) (bijective_cofanMap K hK _ hc)
  simpa only [AddMonoidHom.coe_comp, Function.comp_apply] using DFunLike.congr_fun key a

private lemma isStableUnderShift_isCompactObject :
    ObjectProperty.IsStableUnderShift (IsCompactObject.{w, _, _} (C := D)) ℤ :=
  ⟨fun n => ⟨fun _ hX => isCompactObject_shift hX n⟩⟩

end Shift

/-! ### Compactness and the pre-triangulated structure -/

section Pretriangulated

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Exactness of `Hom(-, X)` at `T.obj₁⟦1⟧`, for `T` a distinguished triangle: this is the
first member of Mathlib's family `CategoryTheory.Pretriangulated.Triangle.yoneda_exact₂`,
`CategoryTheory.Pretriangulated.Triangle.yoneda_exact₃`. -/
private lemma triangle_yoneda_exact₁ (T : Triangle D) (hT : T ∈ distTriang D) {X : D}
    (f : T.obj₁⟦(1 : ℤ)⟧ ⟶ X) (hf : T.mor₃ ≫ f = 0) :
    ∃ g : T.obj₂⟦(1 : ℤ)⟧ ⟶ X, f = T.mor₁⟦(1 : ℤ)⟧' ≫ g := by
  have hrot : Triangle.mk T.mor₂ T.mor₃ (-T.mor₁⟦(1 : ℤ)⟧') ∈ distTriang D :=
    rot_of_distTriang T hT
  obtain ⟨g, hg⟩ := Pretriangulated.Triangle.yoneda_exact₃ _ hrot f hf
  exact ⟨-g, by simpa using hg⟩

/-- **The compactness map of the third vertex of a distinguished triangle**, against one given
cofan: it is bijective as soon as those of the first two vertices and of their shifts by `1` are.
No coproduct and no compactness against other families is involved, so this applies to
compactness relative to a class of objects. -/
lemma bijective_cofanMap_obj₃ (T : Triangle D) (hT : T ∈ distTriang D) {I : Type*}
    [DecidableEq I] {E : I → D} {S : D} (j : ∀ i, E i ⟶ S)
    (h₁ : Function.Bijective (cofanMap T.obj₁ j)) (h₂ : Function.Bijective (cofanMap T.obj₂ j))
    (h₁' : Function.Bijective (cofanMap (T.obj₁⟦(1 : ℤ)⟧) j))
    (h₂' : Function.Bijective (cofanMap (T.obj₂⟦(1 : ℤ)⟧) j)) :
    Function.Bijective (cofanMap T.obj₃ j) := by
  have lift : ∀ {A B C : D} (u : A ⟶ B) (w : B ⟶ C),
      (∀ {X : D} (f : B ⟶ X), u ≫ f = 0 → ∃ g : C ⟶ X, f = w ≫ g) →
      ∀ a : DirectSum I fun i => (B ⟶ E i), dsPrecomp E u a = 0 → ∃ b, dsPrecomp E w b = a :=
    fun u w ex a ha => exists_dsMap_eq (fun i => Preadditive.leftComp (E i) w) a fun i =>
      (ex (a i) (by rw [← dsPrecomp_apply, ha, DFinsupp.zero_apply])).imp fun _ hy => hy.symm
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    have hg : dsPrecomp E T.mor₂ a = 0 := by
      refine h₂.1 ?_
      rw [map_zero, cofanMap_dsPrecomp, ha, comp_zero]
    obtain ⟨b, hb'⟩ := lift T.mor₂ T.mor₃ (fun f => Triangle.yoneda_exact₃ T hT f) a hg
    have ht : T.mor₃ ≫ cofanMap (T.obj₁⟦(1 : ℤ)⟧) j b = 0 := by
      rw [← cofanMap_dsPrecomp, hb', ha]
    obtain ⟨s, hs⟩ := triangle_yoneda_exact₁ T hT _ ht
    obtain ⟨c, hc⟩ := h₂'.2 s
    have hb2 : b = dsPrecomp E (T.mor₁⟦(1 : ℤ)⟧') c := by
      refine h₁'.1 ?_
      rw [cofanMap_dsPrecomp, hc, ← hs]
    rw [← hb', hb2, dsPrecomp_dsPrecomp, comp_distTriang_mor_zero₃₁ T hT, dsPrecomp_zero]
  · intro t
    obtain ⟨v, hv⟩ := h₂.2 (T.mor₂ ≫ t)
    have hfv : dsPrecomp E T.mor₁ v = 0 := by
      refine h₁.1 ?_
      rw [map_zero, cofanMap_dsPrecomp, hv, ← Category.assoc,
        comp_distTriang_mor_zero₁₂ T hT, zero_comp]
    obtain ⟨y, hy'⟩ := lift T.mor₁ T.mor₂ (fun f => Triangle.yoneda_exact₂ T hT f) v hfv
    have hu : T.mor₂ ≫ (t - cofanMap T.obj₃ j y) = 0 := by
      rw [Preadditive.comp_sub, ← cofanMap_dsPrecomp, hy', hv, sub_self]
    obtain ⟨r, hr⟩ := Pretriangulated.Triangle.yoneda_exact₃ T hT _ hu
    obtain ⟨rc, hrc⟩ := h₁'.2 r
    refine ⟨y + dsPrecomp E T.mor₃ rc, ?_⟩
    rw [map_add, cofanMap_dsPrecomp, hrc, ← hr, add_sub_cancel]


section Coproducts

variable [HasCoproducts.{w} D]

/-- If the first two objects of a distinguished triangle are compact, so is the third. -/
lemma isCompactObject_obj₃ (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : IsCompactObject.{w} T.obj₁) (h₂ : IsCompactObject.{w} T.obj₂) :
    IsCompactObject.{w} T.obj₃ := by
  have h₁' : IsCompactObject.{w} (T.obj₁⟦(1 : ℤ)⟧) := isCompactObject_shift h₁ 1
  have h₂' : IsCompactObject.{w} (T.obj₂⟦(1 : ℤ)⟧) := isCompactObject_shift h₂ 1
  constructor
  intro I _ E _
  exact bijective_cofanMap_obj₃ T hT (Limits.Sigma.ι E) (bijective_cofanMap_sigmaι _ h₁ E)
    (bijective_cofanMap_sigmaι _ h₂ E) (bijective_cofanMap_sigmaι _ h₁' E)
    (bijective_cofanMap_sigmaι _ h₂' E)

/-- The direct sum of two compact objects is compact: it is the third vertex of the inverse
rotation of the split triangle `X ⟶ X ⊞ Y ⟶ Y ⟶ X⟦1⟧`, whose first two vertices are `Y⟦-1⟧`
and `X`. -/
lemma isCompactObject_biprod {X Y : D} [HasBinaryBiproduct X Y] (hX : IsCompactObject.{w} X)
    (hY : IsCompactObject.{w} Y) : IsCompactObject.{w} (X ⊞ Y) :=
  isCompactObject_obj₃ _ (inv_rot_of_distTriang _ (binaryBiproductTriangle_distinguished X Y))
    (isCompactObject_shift hY (-1)) hX

private lemma isTriangulatedClosed₃_isCompactObject :
    ObjectProperty.IsTriangulatedClosed₃ (IsCompactObject.{w, _, _} (C := D)) :=
  ObjectProperty.IsTriangulatedClosed₃.mk' fun T hT h₁ h₂ => isCompactObject_obj₃ T hT h₁ h₂

/-- The compact objects form a strictly full triangulated subcategory. -/
lemma isTriangulated_isCompactObject :
    ObjectProperty.IsTriangulated (IsCompactObject.{w, _, _} (C := D)) :=
  have := isStableUnderShift_isCompactObject.{w} (D := D)
  have := containsZero_isCompactObject.{w} (D := D)
  have := isTriangulatedClosed₃_isCompactObject.{w} (D := D)
  have := ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃
    (P := IsCompactObject.{w, _, _} (C := D))
  { }

/-- Compactness is closed under finite direct sums. -/
private lemma isClosedUnderFiniteCoproducts_isCompactObject :
    ObjectProperty.IsClosedUnderFiniteCoproducts (IsCompactObject.{w, _, _} (C := D)) :=
  have := isTriangulated_isCompactObject.{w} (D := D)
  ⟨fun _ _ ↦ ObjectProperty.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι _ _⟩

/-- **A finite direct sum of compact objects is compact.** The compact objects form a strictly
full triangulated subcategory (`CategoryTheory.isTriangulated_isCompactObject`), the full
subcategory it spans has finite coproducts and the inclusion preserves them, so the property of
being compact is closed under finite coproducts. This is the form in which the cells attached at
one stage of a cell tower are assembled: finitely many at a time, so that the stage stays
compact. -/
lemma isCompactObject_sigma {J : Type*} [Finite J] (Z : J → D) [HasCoproduct Z]
    (hZ : ∀ j, IsCompactObject.{w} (Z j)) : IsCompactObject.{w} (∐ Z) :=
  have := isClosedUnderFiniteCoproducts_isCompactObject.{w} (D := D)
  ObjectProperty.prop_coproduct (P := IsCompactObject.{w, _, _} (C := D)) hZ

private lemma isIdempotentComplete_fullSubcategory :
    IsIdempotentComplete
      (ObjectProperty.FullSubcategory (IsCompactObject.{w, _, _} (C := D))) := by
  have : IsIdempotentComplete D :=
    (isIdempotentComplete_of_hasCountableProducts_or_coproducts D).2
  constructor
  intro X p hp
  have hp' : p.hom ≫ p.hom = p.hom := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, hp]
  obtain ⟨Y, i, e, hie, hei⟩ := IsIdempotentComplete.idempotents_split X.obj p.hom hp'
  refine ⟨⟨Y, isCompactObject_of_retract X.property i e hie⟩,
    ObjectProperty.homMk i, ObjectProperty.homMk e, ?_, ?_⟩
  · ext
    simpa using hie
  · ext
    simpa using hei

/-- The compact objects of a pre-triangulated category `D` with direct sums form the objects of a
Karoubian, saturated, strictly full, pre-triangulated subcategory of `D`: the property of being
compact is closed under isomorphisms, is a triangulated subcategory of `D`, is saturated (closed
under direct summands), and idempotents split in the full subcategory it spans. -/
@[stacks 09QH]
public theorem
    isClosedUnderIsomorphisms_isTriangulated_isSaturated_and_isIdempotentComplete_isCompactObject :
    ObjectProperty.IsClosedUnderIsomorphisms (IsCompactObject.{w, _, _} (C := D)) ∧
      ObjectProperty.IsTriangulated (IsCompactObject.{w, _, _} (C := D)) ∧
      ObjectProperty.IsSaturated (IsCompactObject.{w, _, _} (C := D)) ∧
      IsIdempotentComplete
        (ObjectProperty.FullSubcategory (IsCompactObject.{w, _, _} (C := D))) :=
  ⟨isClosedUnderIsomorphisms_isCompactObject, isTriangulated_isCompactObject,
    isSaturated_isCompactObject, isIdempotentComplete_fullSubcategory⟩

end Coproducts

end Pretriangulated

/-! ### Transfer of compactness along a functor

Compactness of `K` is the bijectivity of the compactness maps `cofanMap K j` for colimit cofans
`j`, and that bijectivity is stable under the operations by which one family of morphisms is
produced from another. Isomorphisms of the family and of its vertex leave it unchanged
(`bijective_cofanMap_of_iso`), hence so does replacing the functor that produces the family by an
isomorphic one (`bijective_cofanMap_of_natIso`). An adjunction `L ⊣ G` of additive functors turns
the compactness map of `K` against a family `G.map (j i)` into the compactness map of `L.obj K`
against `j` (`bijective_cofanMap_of_adjunction`). In a morphism of distinguished triangles the
compactness maps at the three vertices form an exact ladder, so surjectivity at the second and at
the rotated first vertex, together with injectivity at the third, forces surjectivity at the first
(`surjective_cofanMap_of_triangleHom`). Finally compactness descends along a full, faithful,
additive functor preserving the direct sums being tested (`isCompactObject_of_fullyFaithful`), and
is therefore invariant under an additive equivalence
(`isCompactObject_iff_isCompactObject_obj`).

Unlike the compactness map of the chosen coproduct, `cofanMap K j` is injective for *every*
colimit cofan without any compactness hypothesis (`injective_cofanMap`): a summand is read off by
composing with the projection `Sigma.π`.
-/

section Transfer

universe v₂ u₂

variable {D : Type u} [Category.{v} D] [Preadditive D]

/-- `Bijective.of_comm_bijective` in the orientation used below: bijectivity travels from the top
to the bottom map of a commutative square whose vertical maps are bijections. -/
private lemma bijective_of_comm_equiv {A B A' B' : Type*} {f : A → B} {g : A' → B'}
    (α : A ≃ A') (β : B ≃ B') (h : ∀ x, g (α x) = β (f x)) (hf : Function.Bijective f) :
    Function.Bijective g :=
  Bijective.of_comm_bijective α.symm.bijective β.symm.injective
    (fun x => by
      have hx := h (α.symm x)
      rw [α.apply_symm_apply] at hx
      rw [hx, β.symm_apply_apply]) hf

/-- The direct sum of a family of bijective additive maps is bijective. -/
lemma bijective_directSumMap {ι : Type*} {β γ : ι → Type*}
    [∀ i, AddCommGroup (β i)] [∀ i, AddCommGroup (γ i)] (f : ∀ i, β i →+ γ i)
    (hf : ∀ i, Function.Bijective (f i)) : Function.Bijective (DirectSum.map f) :=
  bijective_dsMap f hf

/-- The equivalence of direct sums induced by a family of bijective additive maps. -/
private noncomputable def directSumEquivOfBijective {ι : Type*} {β γ : ι → Type*}
    [∀ i, AddCommGroup (β i)] [∀ i, AddCommGroup (γ i)] (f : ∀ i, β i →+ γ i)
    (hf : ∀ i, Function.Bijective (f i)) :
    (DirectSum ι fun i => β i) ≃ DirectSum ι fun i => γ i :=
  Equiv.ofBijective _ (bijective_directSumMap f hf)

/-- The equivalence of direct sums induced by a family of additive equivalences. -/
private noncomputable def directSumEquivOfAddEquiv {ι : Type*} {β γ : ι → Type*}
    [∀ i, AddCommGroup (β i)] [∀ i, AddCommGroup (γ i)] (e : ∀ i, β i ≃+ γ i) :
    (DirectSum ι fun i => β i) ≃ DirectSum ι fun i => γ i :=
  directSumEquivOfBijective (fun i => (e i).toAddMonoidHom) fun i => (e i).bijective

private lemma directSumEquivOfAddEquiv_apply {ι : Type*} {β γ : ι → Type*}
    [∀ i, AddCommGroup (β i)] [∀ i, AddCommGroup (γ i)] (e : ∀ i, β i ≃+ γ i)
    (x : DirectSum ι fun i => β i) :
    directSumEquivOfAddEquiv e x = DirectSum.map (fun i => (e i).toAddMonoidHom) x := rfl

/-- Componentwise exactness passes to the direct sums. -/
private lemma exact_directSumMap {ι : Type*} {α β γ : ι → Type*}
    [∀ i, AddCommGroup (α i)] [∀ i, AddCommGroup (β i)] [∀ i, AddCommGroup (γ i)]
    (f : ∀ i, α i →+ β i) (g : ∀ i, β i →+ γ i) (h : ∀ i, Function.Exact (f i) (g i)) :
    Function.Exact (DirectSum.map f) (DirectSum.map g) := by
  intro y
  constructor
  · intro hy
    exact exists_dsMap_eq f y fun i => (h i (y i)).1 (DFunLike.congr_fun hy i)
  · rintro ⟨x, rfl⟩
    exact DFinsupp.ext fun i => (h i (f i (x i))).2 ⟨x i, rfl⟩

/-- Composing the compactness map of the chosen coproduct with the projection onto a summand
reads off the corresponding component. -/
private lemma cofanMap_sigmaι_comp_sigmaπ (K : D) {I : Type*} [DecidableEq I] (E : I → D)
    [HasCoproduct E] (x : DirectSum I fun i => (K ⟶ E i)) (i : I) :
    cofanMap K (Limits.Sigma.ι E) x ≫ Limits.Sigma.π E i = x i := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, zero_comp, DFinsupp.zero_apply]
  | of j y =>
    rw [cofanMap_of, Category.assoc]
    by_cases hj : j = i
    · subst hj
      rw [Limits.Sigma.ι_π_eq_id, Category.comp_id, DirectSum.of_eq_same]
    · rw [Limits.Sigma.ι_π_of_ne E hj, comp_zero,
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm hj)]
  | add x y hx hy =>
    rw [map_add, Preadditive.add_comp, hx, hy, DFinsupp.add_apply]

/-- The compactness map of a colimit cofan is injective, with no compactness hypothesis. -/
lemma injective_cofanMap (K : D) {I : Type*} [DecidableEq I] {E : I → D} {S : D}
    (j : ∀ i, E i ⟶ S) (hc : IsColimit (Cofan.mk S j)) :
    Function.Injective (cofanMap K j) := by
  have : HasCoproduct E := ⟨_, hc⟩
  intro x y hxy
  rw [cofanMap_eq_of_isColimit K j hc, cofanMap_eq_of_isColimit K j hc] at hxy
  have hxy' := (cancel_mono ((coproductIsCoproduct E).coconePointUniqueUpToIso hc).hom).1 hxy
  refine DFinsupp.ext fun i => ?_
  rw [← cofanMap_sigmaι_comp_sigmaπ K E x i, ← cofanMap_sigmaι_comp_sigmaπ K E y i, hxy']

/-- The compactness map is natural in the family: a componentwise morphism of families over a
morphism of the vertices carries one compactness map to the other. -/
lemma cofanMap_naturality (K : D) {I : Type*} [DecidableEq I] {A B : I → D} {X Y : D}
    (a : ∀ i, A i ⟶ X) (b : ∀ i, B i ⟶ Y) (f : ∀ i, A i ⟶ B i) (g : X ⟶ Y)
    (h : ∀ i, a i ≫ g = f i ≫ b i) (x : DirectSum I fun i => (K ⟶ A i)) :
    cofanMap K b ((DirectSum.map fun i => Preadditive.rightComp K (f i)) x)
      = cofanMap K a x ≫ g := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, zero_comp]
  | of i y =>
    rw [DirectSum.map_of, cofanMap_of, cofanMap_of]
    show (y ≫ f i) ≫ b i = (y ≫ a i) ≫ g
    rw [Category.assoc, Category.assoc, h]
  | add x y hx hy => simp only [map_add, Preadditive.add_comp, hx, hy]

/-- Bijectivity of the compactness map is invariant under an isomorphism of the family and of its
vertex. -/
lemma bijective_cofanMap_of_iso (K : D) {I : Type*} [DecidableEq I] {A B : I → D} {X Y : D}
    (a : ∀ i, A i ⟶ X) (b : ∀ i, B i ⟶ Y) (e : ∀ i, A i ≅ B i) (eS : X ≅ Y)
    (h : ∀ i, a i ≫ eS.hom = (e i).hom ≫ b i)
    (ha : Function.Bijective (cofanMap K a)) : Function.Bijective (cofanMap K b) :=
  bijective_of_comm_equiv
    (directSumEquivOfBijective (fun i => Preadditive.rightComp K (e i).hom)
      fun i => bijective_rightComp_of_isIso K (e i).hom)
    (Equiv.ofBijective _ (bijective_rightComp_of_isIso K eS.hom))
    (fun x => cofanMap_naturality K a b (fun i => (e i).hom) eS.hom h x) ha

/-- Bijectivity of the compactness map against the image of a family under a functor depends on
the functor only up to natural isomorphism. -/
lemma bijective_cofanMap_of_natIso {E : Type u₂} [Category.{v₂} E] (K : D) {F G : E ⥤ D}
    (e : F ≅ G) {I : Type*} [DecidableEq I] {A : I → E} {X : E} (a : ∀ i, A i ⟶ X)
    (h : Function.Bijective (cofanMap K fun i => F.map (a i))) :
    Function.Bijective (cofanMap K fun i => G.map (a i)) :=
  bijective_cofanMap_of_iso K _ _ (fun i => e.app (A i)) (e.app X)
    (fun i => e.hom.naturality (a i)) h

section Adjunction

variable {E : Type u₂} [Category.{v₂} E] [Preadditive E]

/-- Along an adjunction `L ⊣ G` of additive functors, the compactness map of `K` against a family
of the shape `G.map (j i)` is the compactness map of `L.obj K` against `j`, read through the
adjunction bijections; so one is bijective when the other is. -/
lemma bijective_cofanMap_of_adjunction_of_bijective {L : D ⥤ E} {G : E ⥤ D} [L.Additive]
    [G.Additive] (adj : L ⊣ G) (K : D) {I : Type*} [DecidableEq I]
    {A : I → E} {S : E} (j : ∀ i, A i ⟶ S) (h : Function.Bijective (cofanMap (L.obj K) j)) :
    Function.Bijective (cofanMap K fun i => G.map (j i)) := by
  have hEq : (cofanMap K fun i => G.map (j i)).comp
        (DirectSum.map fun i => (adj.homAddEquiv K (A i)).toAddMonoidHom) =
      (adj.homAddEquiv K S).toAddMonoidHom.comp (cofanMap (L.obj K) j) := by
    refine DirectSum.addHom_ext fun i f => ?_
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, DirectSum.map_of,
      AddEquiv.coe_toAddMonoidHom, cofanMap_of, Adjunction.homAddEquiv_apply]
    exact (adj.homEquiv_naturality_right f (j i)).symm
  exact bijective_of_comm_equiv
    (directSumEquivOfAddEquiv fun i => adj.homAddEquiv K (A i))
    (adj.homAddEquiv K S).toEquiv
    (fun x => DFunLike.congr_fun hEq x) h

/-- Along an adjunction `L ⊣ G` of additive functors, the compactness map of `K` against a family
of the shape `G.map (j i)` is the compactness map of `L.obj K` against `j`, read through the
adjunction bijections. In particular it is bijective as soon as `L.obj K` is compact. -/
lemma bijective_cofanMap_of_adjunction {L : D ⥤ E} {G : E ⥤ D} [L.Additive] [G.Additive]
    (adj : L ⊣ G) (K : D) (hLK : IsCompactObject.{w} (L.obj K)) {I : Type w} [DecidableEq I]
    {A : I → E} {S : E} (j : ∀ i, A i ⟶ S) (hc : IsColimit (Cofan.mk S j)) :
    Function.Bijective (cofanMap K fun i => G.map (j i)) :=
  bijective_cofanMap_of_adjunction_of_bijective adj K j (bijective_cofanMap (L.obj K) hLK j hc)

/-- Compactness descends along a functor that is full, faithful, additive and preserves the direct
sums being tested. -/
lemma isCompactObject_of_fullyFaithful (F : D ⥤ E) [F.Full] [F.Faithful] [F.Additive]
    [∀ I : Type w, PreservesColimitsOfShape (Discrete I) F] (K : D)
    (hFK : IsCompactObject.{w} (F.obj K)) : IsCompactObject.{w} K := by
  classical
  constructor
  intro I _ A _
  let e (X : D) : (K ⟶ X) ≃+ (F.obj K ⟶ F.obj X) :=
    AddEquiv.ofBijective F.mapAddHom ⟨F.map_injective, F.map_surjective⟩
  have hc : IsColimit (Cofan.mk (F.obj (∐ A)) fun i => F.map (Limits.Sigma.ι A i)) :=
    (isColimitMapCoconeCofanMkEquiv F A (Limits.Sigma.ι A))
      (isColimitOfPreserves F (coproductIsCoproduct A))
  show Function.Bijective (cofanMap K (Limits.Sigma.ι A))
  refine bijective_of_comm_equiv
    (directSumEquivOfAddEquiv fun i => (e (A i)).symm) (e (∐ A)).symm.toEquiv (fun x => ?_)
    (bijective_cofanMap (F.obj K) hFK _ hc)
  refine (e (∐ A)).injective ?_
  rw [directSumEquivOfAddEquiv_apply,
    show (e (∐ A)) ((e (∐ A)).symm.toEquiv
        ((cofanMap (F.obj K) fun i => F.map (Limits.Sigma.ι A i)) x)) =
        (cofanMap (F.obj K) fun i => F.map (Limits.Sigma.ι A i)) x from
      (e (∐ A)).apply_symm_apply _]
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | of i f =>
    rw [DirectSum.map_of, cofanMap_of, cofanMap_of]
    show F.map ((e (A i)).symm f ≫ Limits.Sigma.ι A i) = _
    rw [F.map_comp]
    exact congrArg (fun g => g ≫ F.map (Limits.Sigma.ι A i)) ((e (A i)).apply_symm_apply f)
  | add x y hx hy => simp only [map_add, hx, hy]

end Adjunction

/-- Compactness is invariant under isomorphism. -/
lemma isCompactObject_of_iso {K L : D} (e : K ≅ L) (hL : IsCompactObject.{w} L) :
    IsCompactObject.{w} K :=
  isCompactObject_of_retract hL e.hom e.inv e.hom_inv_id

/-- Compactness is invariant under an additive equivalence of categories. -/
lemma isCompactObject_iff_isCompactObject_obj {E : Type u₂} [Category.{v₂} E] [Preadditive E]
    (F : D ⥤ E) [F.IsEquivalence] [F.Additive] (K : D) :
    IsCompactObject.{w} K ↔ IsCompactObject.{w} (F.obj K) := by
  have : F.asEquivalence.functor.Additive := ‹F.Additive›
  have : F.asEquivalence.inverse.Additive :=
    F.asEquivalence.toAdjunction.right_adjoint_additive
  refine ⟨fun h => ?_, fun h => isCompactObject_of_fullyFaithful F K h⟩
  exact isCompactObject_of_fullyFaithful F.asEquivalence.inverse _
    (isCompactObject_of_iso (F.asEquivalence.unitIso.app K).symm h)

end Transfer

section TransferTriangulated

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- In a family of morphisms `φ i : T i ⟶ U` of distinguished triangles, the compactness maps at
the three vertices sit in a ladder of exact sequences of abelian groups. Surjectivity at the
second vertex and at the first vertex of the inverse rotations, together with injectivity at the
third, give surjectivity at the first. -/
lemma surjective_cofanMap_of_triangleHom (K : D) {I : Type*} [DecidableEq I]
    (T : I → Triangle D) (U : Triangle D) (φ : ∀ i, T i ⟶ U)
    (hT : ∀ i, T i ∈ distTriang D) (hU : U ∈ distTriang D)
    (h₂ : Function.Surjective (cofanMap K fun i => (φ i).hom₂))
    (h₃ : Function.Injective (cofanMap K fun i => (φ i).hom₃))
    (h₀ : Function.Surjective (cofanMap K fun i => ((invRotate D).map (φ i)).hom₁)) :
    Function.Surjective (cofanMap K fun i => (φ i).hom₁) := by
  have he : ∀ i, Function.Exact (Preadditive.rightComp K (T i).mor₁)
      (Preadditive.rightComp K (T i).mor₂) := by
    intro i f
    constructor
    · intro hf
      obtain ⟨g, hg⟩ := (T i).coyoneda_exact₂ (hT i) f hf
      exact ⟨g, hg.symm⟩
    · rintro ⟨g, rfl⟩
      show (g ≫ (T i).mor₁) ≫ (T i).mor₂ = 0
      rw [Category.assoc, comp_distTriang_mor_zero₁₂ (T i) (hT i), comp_zero]
  intro f
  obtain ⟨b, hb⟩ := h₂ (f ≫ U.mor₁)
  have hb₀ : DirectSum.map (fun i => Preadditive.rightComp K (T i).mor₂) b = 0 := by
    apply h₃
    rw [map_zero, cofanMap_naturality K _ _ _ _ (fun i => (φ i).comm₂.symm), hb,
      Category.assoc, comp_distTriang_mor_zero₁₂ U hU, comp_zero]
  obtain ⟨a, ha⟩ := (exact_directSumMap _ _ he b).1 hb₀
  have ha' : cofanMap K (fun i => (φ i).hom₁) a ≫ U.mor₁ = f ≫ U.mor₁ := by
    rw [← cofanMap_naturality K _ _ _ _ (fun i => (φ i).comm₁.symm), ha, hb]
  obtain ⟨c, hc⟩ := U.invRotate.coyoneda_exact₂ (inv_rot_of_distTriang _ hU)
    (f - cofanMap K (fun i => (φ i).hom₁) a) (by
      show (f - _) ≫ U.mor₁ = 0
      rw [Preadditive.sub_comp, ha', sub_self])
  obtain ⟨z, hz⟩ := h₀ c
  let z' : DirectSum I fun i => (K ⟶ (T i).obj₁) :=
    DirectSum.map (fun i => Preadditive.rightComp K ((invRotate D).obj (T i)).mor₁) z
  have hz' : cofanMap K (fun i => (φ i).hom₁) z' = c ≫ U.invRotate.mor₁ :=
    (cofanMap_naturality K _ _ _ _
      (fun i => ((invRotate D).map (φ i)).comm₁.symm) z).trans
        (congrArg (fun g => g ≫ U.invRotate.mor₁) hz)
  refine ⟨a + z', ?_⟩
  rw [map_add, hz', ← hc]
  abel

end TransferTriangulated

end CategoryTheory

end
