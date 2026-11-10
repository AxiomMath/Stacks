module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.FiniteNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.CompositeFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import StacksFrontier.Topology.Separation.IsolatedPoint

/-!
# Splitting off the quasi-finite part by an elementary étale base change

Let `f : X ⟶ S` be separated and locally of finite type. Finitely many distinct isolated points
of one fibre of `f` can, after an elementary étale base change of `S`, be separated into finite
open-and-closed pieces of the base change, one for each chosen point, with a complementary piece
containing none of them.

When the fibre has only finitely many isolated points this gives a decomposition of the base
change into two open-and-closed pieces: one finite over the neighbourhood, carrying all the
isolated points, and a complement whose fibre over the distinguished point has no isolated
points at all — and is empty as soon as the set-theoretic fibre is finite.

## Main results

* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_decomposition`: the chosen isolated
  points lie in separate finite open-and-closed pieces after an elementary étale base change,
  with no chosen point left in the complementary piece.
* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_isCompl`: the two-piece decomposition
  splitting off the quasi-finite part.

## Implementation notes

In the first statement the pieces are indexed by `Option (Fin n)`: `none` is the complementary
piece and `some i` is the piece containing the `i`-th chosen point. That they decompose the base
change disjointly is expressed by requiring the coproduct descender to be an isomorphism.
Isolation in the fibre is stated topologically using the canonical point `f.asFiber (x i)`, and
equality of residue fields by the canonical residue-field map being an isomorphism.

In the second statement the decomposition into open and closed subschemes is represented by
complementary opens `W` and `V`; coercing an open to a scheme gives the corresponding open
subscheme. Emptiness of the last fibre is expressed by emptiness of its type of points.

## References

* [Stacks Project, Tag 02LN](https://stacks.math.columbia.edu/tag/02LN)
* [Stacks Project, Tag 02LP](https://stacks.math.columbia.edu/tag/02LP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-! ### Separating finitely many isolated fibre points -/

/-- Over the distinguished point of an elementary étale neighbourhood, the spectrum of the
tensor product of residue fields at a point of the base change is a single point. -/
private theorem EtaleNeighborhood.subsingleton_spec_tensor_of_isElementary (f : X ⟶ S) {s : S}
    {U : EtaleNeighborhood S s} (hU : U.IsElementary) (T : Scheme.Pullback.Triplet f U.toBase)
    (hyT : T.y = U.point) (hsT : T.s = U.toBase U.point) :
    Subsingleton (Spec T.tensor) := by
  have hUres : IsIso (U.toBase.residueFieldMap U.point) := (U.isElementary_iff).mp hU
  let T' : Scheme.Pullback.Triplet f U.toBase :=
    ⟨T.x, U.point, U.toBase U.point, T.hx.trans hsT, rfl⟩
  have hTeq : T = T' := Scheme.Pullback.Triplet.ext rfl hyT
  have hT'sub : Subsingleton (Spec T'.tensor) := by
    have : IsIso ((S.residueFieldCongr rfl).inv ≫ U.toBase.residueFieldMap U.point) := by
      simpa using hUres
    have hinl : IsIso T'.tensorInl := by
      dsimp [Scheme.Pullback.Triplet.tensorInl, Scheme.Pullback.Triplet.tensor]
      exact (IsPushout.of_hasPushout _ _).isIso_inl_of_isIso
    have : IsIso (Spec.map T'.tensorInl) := by infer_instance
    exact (Spec.map T'.tensorInl).isEmbedding.injective.subsingleton
  have : IsIso (Spec.map (Scheme.Pullback.Triplet.tensorCongr hTeq).inv) := by
    infer_instance
  exact (Spec.map (Scheme.Pullback.Triplet.tensorCongr hTeq).inv).isEmbedding.injective.subsingleton

/-- Two points of the base change along an elementary étale neighbourhood lying over its
distinguished point and over the same point of the source coincide. -/
private theorem EtaleNeighborhood.eq_of_fst_eq_of_snd_eq_point (f : X ⟶ S) {s : S}
    {U : EtaleNeighborhood S s} (hU : U.IsElementary) {x : X} (hx : f x = s)
    {a b : ↥(pullback f U.toBase)}
    (haX : pullback.fst f U.toBase a = x) (haU : pullback.snd f U.toBase a = U.point)
    (hbX : pullback.fst f U.toBase b = x) (hbU : pullback.snd f U.toBase b = U.point) :
    a = b := by
  let ca := Scheme.Pullback.carrierEquiv (f := f) (g := U.toBase) a
  let cb := Scheme.Pullback.carrierEquiv (f := f) (g := U.toBase) b
  have hT : ca.1 = cb.1 := by
    apply Scheme.Pullback.Triplet.ext
    · simpa [ca, cb, Scheme.Pullback.carrierEquiv] using haX.trans hbX.symm
    · simpa [ca, cb, Scheme.Pullback.carrierEquiv] using haU.trans hbU.symm
  have hcbS : cb.1.s = U.toBase U.point := by
    change f (pullback.fst f U.toBase b) = U.toBase U.point
    rw [hbX, hx, U.map_point]
  have hca : ca = cb := by
    rw [Scheme.Pullback.carrierEquiv_eq_iff]
    refine ⟨hT, ?_⟩
    have := EtaleNeighborhood.subsingleton_spec_tensor_of_isElementary f hU cb.1 hbU hcbS
    exact Subsingleton.elim _ _
  exact (Scheme.Pullback.carrierEquiv (f := f) (g := U.toBase)).injective hca

/-- The restriction of a finite morphism to a closed open subscheme of its source is finite. -/
private theorem isFinite_ι_comp_of_le_of_isClosed {Y Z : Scheme.{u}} {Q V : Y.Opens}
    (hle : Q ≤ V) (hQ : IsClosed (Q : Set Y)) (g : Y ⟶ Z) [IsFinite (V.ι ≫ g)] :
    IsFinite (Q.ι ≫ g) := by
  let k := Y.homOfLE hle
  have hrange : Set.range k = (k.opensRange : Set V) := by
    ext z
    simp
  have hrangeClosed : IsClosed ((Y.homOfLE hle).opensRange : Set V) := by
    rw [Scheme.opensRange_homOfLE]
    simpa only [TopologicalSpace.Opens.map_coe] using hQ.preimage (Scheme.Hom.continuous V.ι)
  have hkclosed : IsClosed (Set.range k) := hrange.symm ▸ hrangeClosed
  have : IsClosedImmersion k := IsClosedImmersion.of_isPreimmersion k hkclosed
  have hkcomp : k ≫ V.ι = Q.ι := Y.homOfLE_ι hle
  rw [← hkcomp]
  simpa [Category.assoc] using (inferInstance : IsFinite (k ≫ (V.ι ≫ g)))

/-- Restricting a morphism to a smaller open subscheme does not change whether its residue field
map at a point is an isomorphism. -/
private theorem isIso_residueFieldMap_ι_comp_of_le {Y Z : Scheme.{u}} {Q V : Y.Opens}
    (hle : Q ≤ V) (g : Y ⟶ Z) {y : (Q : Scheme.{u})} {v : (V : Scheme.{u})}
    (hyv : Y.homOfLE hle y = v)
    (hv : IsIso ((V.ι ≫ g).residueFieldMap v)) : IsIso ((Q.ι ≫ g).residueFieldMap y) := by
  have hcomp : Y.homOfLE hle ≫ V.ι ≫ g = Q.ι ≫ g := by
    rw [← Category.assoc, Y.homOfLE_ι hle]
  rw [← hcomp, Scheme.residueFieldMap_comp]
  have hfield_comp : IsIso ((V.ι ≫ g).residueFieldMap (Y.homOfLE hle y) ≫
      ((V : Scheme).residueFieldCongr hyv).hom) := by
    rw [Scheme.Hom.residueFieldMap_congr' (f := V.ι ≫ g) hyv]
    infer_instance
  exact IsIso.comp_isIso' ((isIso_comp_right_iff _ _).mp hfield_comp) inferInstance

/-- A smaller open subscheme containing the unique point of a fibre of a morphism still has it as
the unique point of the fibre. -/
private theorem fiber_ι_comp_eq_singleton_of_le {Y Z : Scheme.{u}} {Q V : Y.Opens}
    (hle : Q ≤ V) (g : Y ⟶ Z) (z : Z) {v : V} (hv : {y : V | (V.ι ≫ g) y = z} = {v})
    (hvQ : (v : Y) ∈ Q) : {y : Q | (Q.ι ≫ g) y = z} = {⟨v, hvQ⟩} := by
  have hle' : (Q : Set Y) ⊆ V := hle
  ext y
  constructor
  · intro hy
    have hyv : (⟨y.1, hle' y.2⟩ : V) = v := (Set.ext_iff.mp hv ⟨y.1, hle' y.2⟩).mp hy
    exact Set.mem_singleton_iff.mpr
      (Subtype.ext (congrArg Subtype.val hyv : y.1 = (v : Y)))
  · rintro rfl
    exact (Set.ext_iff.mp hv v).mpr rfl

/-- Finitely many closed open sets shrink to pairwise disjoint closed open sets, the `i`-th
keeping every point of the `i`-th set lying in none of the earlier ones. -/
private theorem _root_.TopologicalSpace.Opens.exists_pairwise_disjoint_isClosed_le
    {α : Type*} [TopologicalSpace α] {n : ℕ} (V : Fin n → TopologicalSpace.Opens α)
    (hV : ∀ i, IsClosed (V i : Set α)) :
    ∃ Q : Fin n → TopologicalSpace.Opens α, (∀ i, IsClosed (Q i : Set α)) ∧ (∀ i, Q i ≤ V i) ∧
      Pairwise (fun i k => Disjoint (Q i : Set α) (Q k)) ∧
      ∀ i, ∀ y ∈ V i, (∀ k : Fin n, k.val < i.val → y ∉ V k) → y ∈ Q i := by
  let Q (i : Fin n) : TopologicalSpace.Opens α :=
    ⟨(V i : Set α) \ ⋃ k : {k : Fin n // k.val < i.val}, (V k : Set α), by
      simpa [Set.sdiff_eq] using
        (V i).2.inter (isClosed_iUnion_of_finite fun k : {k : Fin n // k.val < i.val} =>
          hV k.val).isOpen_compl⟩
  refine ⟨Q, fun i => ?_, fun i => show (Q i : Set α) ⊆ V i from Set.sdiff_subset,
    fun i k hik => ?_, fun i y hy h => ?_⟩
  · dsimp only [Q]
    simpa [Set.sdiff_eq] using hV i |>.inter
      (isOpen_iUnion fun k : {k : Fin n // k.val < i.val} => (V k).2).isClosed_compl
  · change Disjoint (Q i : Set α) (Q k)
    rw [Set.disjoint_left]
    intro y hyi hyk
    by_cases hlt : i.val < k.val
    · exact hyk.2 (Set.mem_iUnion.mpr ⟨⟨i, hlt⟩, hyi.1⟩)
    · have hki : k.val < i.val :=
        lt_of_le_of_ne (le_of_not_gt hlt) (by simpa [Fin.ext_iff] using hik.symm)
      exact hyi.2 (Set.mem_iUnion.mpr ⟨⟨k, hki⟩, hyk.1⟩)
  · change y ∈ (V i : Set α) \ ⋃ k : {k : Fin n // k.val < i.val}, (V k : Set α)
    refine ⟨hy, fun hm => ?_⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hm
    exact h k.1 k.2 hk

/-- Pairwise disjoint opens together with the complement of their union decompose a scheme as
the coproduct of the corresponding open subschemes. -/
private theorem isIso_sigmaDesc_ι_of_option_compl {Y : Scheme.{u}} {n : ℕ}
    (T : Option (Fin n) → Y.Opens) (hT : (T none : Set Y) = (⋃ i, (T (some i) : Set Y))ᶜ)
    (hdisj : Pairwise fun i k : Fin n => Disjoint (T (some i) : Set Y) (T (some k))) :
    IsIso (Sigma.desc fun a => (T a).ι) := by
  have hr (a : Option (Fin n)) : (T a).ι.opensRange = T a := Scheme.Opens.opensRange_ι _
  have hcover : ⨆ a, (T a).ι.opensRange = ⊤ := by
    apply TopologicalSpace.Opens.ext
    ext y
    simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.mem_univ,
      iff_true, hr]
    by_cases hy : y ∈ ⋃ i, (T (some i) : Set Y)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_iUnion.mpr ⟨some i, hi⟩
    · exact Set.mem_iUnion.mpr ⟨none, by rw [hT]; exact hy⟩
  have hdisj' : Pairwise fun a b => Disjoint (T a).ι.opensRange (T b).ι.opensRange := by
    have hWQ (i : Fin n) : Disjoint (T none : Set Y) (T (some i)) := by
      rw [hT]
      exact disjoint_compl_left.mono_right (Set.subset_iUnion (fun k => (T (some k) : Set Y)) i)
    intro a b hab
    rw [hr, hr, ← TopologicalSpace.Opens.coe_disjoint]
    rcases a with _ | i <;> rcases b with _ | k
    · exact absurd rfl hab
    · exact hWQ k
    · exact (hWQ i).symm
    · exact hdisj (by simpa using hab)
  exact (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk Y fun a => (T a).ι)).mp
    (nonempty_isColimit_cofanMk_of _ hcover hdisj')

/-- If closed opens and the complement of their union are taken as open subschemes, each
inclusion is a closed immersion. -/
private theorem isClosedImmersion_ι_of_option_compl {Y : Scheme.{u}} {n : ℕ}
    (T : Option (Fin n) → Y.Opens) (hT : (T none : Set Y) = (⋃ i, (T (some i) : Set Y))ᶜ)
    (hclosed : ∀ i, IsClosed (T (some i) : Set Y)) (a : Option (Fin n)) :
    IsClosedImmersion (T a).ι := by
  apply IsClosedImmersion.of_isPreimmersion
  rcases a with _ | i
  · simpa [Scheme.Opens.range_ι, hT] using
      (isOpen_iUnion fun i => (T (some i)).2).isClosed_compl
  · simpa [Scheme.Opens.range_ι] using hclosed i

/-- **Stacks Project, Tag 02LN.** Finitely many distinct isolated points of a
fibre of a separated morphism locally of finite type split into separate finite
open-and-closed pieces after an elementary étale base change. -/
@[stacks 02LN, ega "IV 18.12.1" "separated case", ega "IV 18.12.3" "more general"]
public theorem exists_elementaryEtaleNeighborhood_decomposition
    (f : X ⟶ S) [LocallyOfFiniteType f] [IsSeparated f]
    (s : S) (n : ℕ) (x : Fin n → X) (hx : ∀ i, f (x i) = s)
    (hx_injective : Function.Injective x)
    (hx_isolated : ∀ i, IsOpen {f.asFiber (x i)}) :
    ∃ (U : EtaleNeighborhood S s) (_ : U.IsElementary)
      (P : Option (Fin n) → Scheme.{u})
      (j : ∀ a, P a ⟶ pullback f U.toBase)
      (_ : ∀ a, IsOpenImmersion (j a))
      (_ : ∀ a, IsClosedImmersion (j a))
      (_ : IsIso (Sigma.desc j))
      (v : ∀ i, P (some i))
      (_ : ∀ i, IsFinite (j (some i) ≫ pullback.snd f U.toBase)),
      (∀ i, (j (some i) ≫ pullback.fst f U.toBase) (v i) = x i) ∧
      (∀ i, {y : P (some i) |
          (j (some i) ≫ pullback.snd f U.toBase) y = U.point} = {v i}) ∧
      (∀ i, IsIso ((j (some i) ≫ pullback.fst f U.toBase).residueFieldMap (v i))) ∧
      (∀ y : P none,
        (j none ≫ pullback.snd f U.toBase) y = U.point →
          ∀ i, (j none ≫ pullback.fst f U.toBase) y ≠ x i) := by
  classical
  obtain ⟨U, hU, V, v, hfinite, hfiber, hpoint, hres⟩ :=
    exists_elementaryEtaleNeighborhood_finite_opens_of_isolated_fiber_points f s n x hx
      hx_isolated
  let Y := pullback f U.toBase
  have hVclosed (i : Fin n) : IsClosed (V i : Set Y) := by
    have := hfinite i
    have := IsProper.of_comp (V i).ι (pullback.snd f U.toBase)
    simpa [Scheme.Opens.range_ι] using Scheme.Hom.isClosedMap ((V i).ι) |>.isClosed_range
  obtain ⟨Q, hQclosed, hQV, hQdisj, hQmem⟩ :=
    TopologicalSpace.Opens.exists_pairwise_disjoint_isClosed_le V hVclosed
  let W : Y.Opens := ⟨(⋃ i, (Q i : Set Y))ᶜ, (isClosed_iUnion_of_finite hQclosed).isOpen_compl⟩
  let T : Option (Fin n) → Y.Opens := fun a =>
    match a with
    | none => W
    | some i => Q i
  let P : Option (Fin n) → Scheme.{u} := fun a => T a
  let j : ∀ a, P a ⟶ Y := fun a => (T a).ι
  have hvfiber (i : Fin n) : ((V i).ι ≫ pullback.snd f U.toBase) (v i) = U.point :=
    (Set.ext_iff.mp (hfiber i) (v i)).mpr rfl
  have hvQ (i : Fin n) : (v i : Y) ∈ Q i := by
    refine hQmem i _ (v i).property fun k hk hmk => ?_
    have hzeq : (⟨(v i : Y), hmk⟩ : V k) = v k :=
      (Set.ext_iff.mp (hfiber k) ⟨(v i : Y), hmk⟩).mp (hvfiber i)
    have hxx : x i = x k := calc
      x i = ((V i).ι ≫ pullback.fst f U.toBase) (v i) := (hpoint i).symm
      _ = ((V k).ι ≫ pullback.fst f U.toBase) ⟨(v i : Y), hmk⟩ := rfl
      _ = x k := by rw [hzeq, hpoint k]
    exact hk.ne (congrArg Fin.val (hx_injective hxx)).symm
  let v' : ∀ i, P (some i) := fun i => ⟨(v i : Y), hvQ i⟩
  have hfinite' (i : Fin n) : IsFinite (j (some i) ≫ pullback.snd f U.toBase) := by
    have := hfinite i
    exact isFinite_ι_comp_of_le_of_isClosed (hQV i) (hQclosed i) _
  refine ⟨U, hU, P, j, fun _ => inferInstance, isClosedImmersion_ι_of_option_compl T rfl hQclosed,
    isIso_sigmaDesc_ι_of_option_compl T rfl hQdisj, v', hfinite', hpoint, fun i =>
    fiber_ι_comp_eq_singleton_of_le (hQV i) _ U.point (hfiber i) (hvQ i), fun i => ?_, ?_⟩
  · have hkv : Y.homOfLE (hQV i) (v' i) = v i := by
      dsimp only [v']
      exact Scheme.homOfLE_apply' (hQV i) (v i : Y) (hvQ i)
    exact isIso_residueFieldMap_ι_comp_of_le (hQV i) _ hkv (hres i)
  · intro y hy i hyx
    have heq := EtaleNeighborhood.eq_of_fst_eq_of_snd_eq_point f hU (hx i)
      (a := j none y) (b := (V i).ι (v i)) hyx hy (hpoint i) (hvfiber i)
    have hmem : (j none y : Y) ∈ Q i := by simpa [heq] using hvQ i
    exact y.property (Set.mem_iUnion.mpr ⟨i, hmem⟩)


/-! ### Splitting off the quasi-finite part -/

/-- The coproduct over `Option α` is the binary coproduct of the component at `none` with the
coproduct of the remaining components. -/
private def sigmaOptionCoprodIso {α : Type} (P : Option α → Scheme.{u}) :
    P none ⨿ (∐ fun i : α => P (some i)) ≅ ∐ P where
  hom := coprod.desc (Sigma.ι P none) (Sigma.desc fun i => Sigma.ι P (some i))
  inv := Sigma.desc fun a => match a with
    | none => coprod.inl
    | some i => Sigma.ι (fun i : α => P (some i)) i ≫ coprod.inr
  hom_inv_id := by
    apply coprod.hom_ext
    · simp
    · apply Sigma.hom_ext
      intro i
      simp
  inv_hom_id := by
    apply Sigma.hom_ext
    intro a
    cases a with
    | none => simp
    | some i => simp [Category.assoc]

/-- Composing a family with an equivalence turns its range into a preimage. -/
private theorem range_equiv_comp {α β ι : Type*} (e : α ≃ β) (g : ι → α) :
    Set.range (e ∘ g) = e.symm ⁻¹' Set.range g := by
  rw [Set.range_comp, Equiv.image_eq_preimage_symm]

/-- If a family indexed by `Option α` exhibits its target as a coproduct, the components away
from `none` jointly give an open immersion. -/
private theorem isOpenImmersion_sigmaDesc_some {Y : Scheme.{u}} {α : Type}
    (P : Option α → Scheme.{u}) (j : ∀ a, P a ⟶ Y) [IsIso (Sigma.desc j)] :
    IsOpenImmersion (Sigma.desc fun i => j (some i)) := by
  have h : (Sigma.desc fun i => j (some i)) =
      coprod.inr ≫ (sigmaOptionCoprodIso P).hom ≫ Sigma.desc j := by
    apply Sigma.hom_ext
    intro i
    simp [sigmaOptionCoprodIso]
  rw [h]
  infer_instance

/-- If a family indexed by `Option α` exhibits its target as a coproduct, the image of the
`none` component is complementary to the joint image of the others. -/
private theorem isCompl_opensRange_sigmaDesc_some {Y : Scheme.{u}} {α : Type}
    (P : Option α → Scheme.{u}) (j : ∀ a, P a ⟶ Y) [IsOpenImmersion (j none)]
    [IsOpenImmersion (Sigma.desc fun i => j (some i))] [IsIso (Sigma.desc j)] :
    IsCompl (j none).opensRange (Sigma.desc fun i => j (some i)).opensRange := by
  let q := (sigmaOptionCoprodIso P).trans (asIso (Sigma.desc j))
  let E : ↥(P none ⨿ ∐ fun i => P (some i)) ≃ ↥Y :=
    { toFun := fun z => q.hom z
      invFun := fun z => q.inv z
      left_inv := fun z => by
        change (q.hom ≫ q.inv) z = z
        simp
      right_inv := fun z => by
        change (q.inv ≫ q.hom) z = z
        simp }
  have hrange {A : Scheme.{u}} (g : A ⟶ P none ⨿ ∐ fun i => P (some i)) (h : A ⟶ Y)
      (hg : g ≫ q.hom = h) : Set.range h = E.symm ⁻¹' Set.range g := by
    rw [← hg]
    exact range_equiv_comp E ⇑g
  have hW := hrange coprod.inl (j none) (by simp [q, sigmaOptionCoprodIso])
  have hV := hrange coprod.inr (Sigma.desc fun i => j (some i)) (by
    apply Sigma.hom_ext
    intro i
    simp [q, sigmaOptionCoprodIso])
  have hset : IsCompl (Set.range (j none)) (Set.range (Sigma.desc fun i => j (some i))) := by
    rw [hW, hV]
    exact (isCompl_range_inl_inr _ _).map (CompleteLatticeHom.setPreimage E.symm)
  convert hset using 1
  simp only [isCompl_iff, disjoint_iff, codisjoint_iff, ← TopologicalSpace.Opens.coe_inj]
  rfl

/-- The joint open immersion of finitely many components that are finite over a base is finite
over it once restricted to its image. -/
private theorem isFinite_opensRange_sigmaDesc_some_ι_comp {Y Z : Scheme.{u}} {α : Type}
    [Finite α] (P : Option α → Scheme.{u}) (j : ∀ a, P a ⟶ Y)
    [IsOpenImmersion (Sigma.desc fun i => j (some i))] (g : Y ⟶ Z)
    [∀ i, IsFinite (j (some i) ≫ g)] :
    IsFinite ((Sigma.desc fun i => j (some i)).opensRange.ι ≫ g) := by
  have hcomp : (Sigma.desc fun i => j (some i)) ≫ g = Sigma.desc fun i => j (some i) ≫ g := by
    apply Sigma.hom_ext
    intro i
    simp
  have : IsFinite ((Sigma.desc fun i => j (some i)) ≫ g) := by
    rw [hcomp]
    infer_instance
  have hrange : Set.range (Sigma.desc fun i => j (some i)) =
      Set.range (Sigma.desc fun i => j (some i)).opensRange.ι := by
    simp
  rw [← IsOpenImmersion.isoOfRangeEq_inv_fac _ _ hrange, Category.assoc]
  infer_instance

/-- Over an elementary étale neighbourhood, the fibre over the distinguished point of an open
subscheme of the base change embeds openly into the original fibre, over the source. -/
private theorem exists_isOpenImmersion_fiber_ι_comp_snd (f : X ⟶ S) (s : S)
    (U : EtaleNeighborhood S s) (hU : U.IsElementary) (W : (pullback f U.toBase).Opens) :
    ∃ J : (W.ι ≫ pullback.snd f U.toBase).fiber U.point ⟶ f.fiber s, IsOpenImmersion J ∧
      ∀ z, f.fiberι s (J z) = pullback.fst f U.toBase
        (W.ι ((W.ι ≫ pullback.snd f U.toBase).fiberι U.point z)) := by
  let m := fiberMapOfSourceHom W.ι (pullback.snd f U.toBase) U.point
  have : IsOpenImmersion m :=
    MorphismProperty.of_isPullback
      (fiberMapOfSourceHom_isPullback W.ι (pullback.snd f U.toBase) U.point).flip inferInstance
  refine ⟨m ≫ (fiberIsoOfIsElementary f s U hU).hom, inferInstance, fun z => ?_⟩
  have hproj : (m ≫ (fiberIsoOfIsElementary f s U hU).hom) ≫ f.fiberι s =
      (W.ι ≫ pullback.snd f U.toBase).fiberι U.point ≫ W.ι ≫ pullback.fst f U.toBase := by
    rw [Category.assoc, fiberIsoOfIsElementary_hom_fiberι, ← Category.assoc,
      fiberMapOfSourceHom_fiberι]
    simp only [Category.assoc]
  simpa only [Scheme.Hom.comp_apply] using congrArg (fun k => k z) hproj

/-- An isolated point of the fibre over `s` stays isolated in the fibre over its own image. -/
private theorem isOpen_singleton_asFiber_fiberHomeo (f : X ⟶ S) {s : S} {p : f.fiber s}
    (hp : IsIsolatedPoint p) : IsOpen {f.asFiber ((f.fiberHomeo s) p).1} := by
  set y := ((f.fiberHomeo s) p).1
  have hy : f y = s := ((f.fiberHomeo s) p).2
  have hi : IsOpen ({p} : Set (f.fiber s)) := hp
  have hset : f ⁻¹' {s} = f ⁻¹' {f y} := by
    ext z
    simp [hy]
  let H : f.fiber s ≃ₜ f.fiber (f y) :=
    (f.fiberHomeo s).trans <| (Homeomorph.setCongr hset).trans (f.fiberHomeo (f y)).symm
  have hpoint : H p = f.asFiber y := by
    have hmid : (Homeomorph.setCongr hset) ((f.fiberHomeo s) p) =
        (⟨y, rfl⟩ : f ⁻¹' {f y}) := by
      apply Subtype.ext
      change ((Set.equivOfEq hset) ((f.fiberHomeo s) p)).val = (f.fiberι s) p
      simpa [y, Scheme.Hom.fiberHomeo_apply] using
        congrArg Subtype.val (Set.equivOfEq_apply hset ((f.fiberHomeo s) p))
    change (f.fiberHomeo (f y)).symm ((Homeomorph.setCongr hset) ((f.fiberHomeo s) p)) =
      (f.fiberHomeo (f y)).symm ⟨y, rfl⟩
    rw [hmid]
  simpa [hpoint] using H.isOpen_image.mpr hi

/-- A space without isolated points admitting a continuous injection into a discrete space is
empty. -/
private theorem isEmpty_of_forall_not_isIsolatedPoint {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [DiscreteTopology β] {g : α → β} (hg : Continuous g)
    (hinj : Function.Injective g) (h : ∀ z : α, ¬ IsIsolatedPoint z) : IsEmpty α := by
  refine ⟨fun z => h z ?_⟩
  have hpre : g ⁻¹' {g z} = {z} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact hinj.eq_iff
  have hzopen : IsOpen ({z} : Set α) := by
    rw [← hpre]
    exact hg.isOpen_preimage _ (isOpen_discrete _)
  simpa [IsIsolatedPoint] using hzopen

/-- **Stacks Project, Tag 02LP.** After an elementary étale base change, the isolated
part of a fibre of a separated morphism locally of finite type splits off as a finite
open-and-closed subscheme.  The complementary fibre has no isolated points and is empty
when the original set-theoretic fibre is finite. -/
@[stacks 02LP, ega "IV 18.12.1" "separated case", ega "IV 18.12.3"]
public theorem exists_elementaryEtaleNeighborhood_isCompl
    (f : X ⟶ S) [LocallyOfFiniteType f] [IsSeparated f] (s : S)
    (hfinite : {x : f.fiber s | IsIsolatedPoint x}.Finite) :
    ∃ (U : EtaleNeighborhood S s),
      U.IsElementary ∧
      ∃ (W V : (pullback f U.toBase).Opens),
        IsCompl W V ∧
        IsFinite (V.ι ≫ pullback.snd f U.toBase) ∧
        (∀ x : (W.ι ≫ pullback.snd f U.toBase).fiber U.point,
          ¬ IsIsolatedPoint x) ∧
        ((f ⁻¹' {s}).Finite →
          IsEmpty ((W.ι ≫ pullback.snd f U.toBase).fiber U.point)) := by
  classical
  let : Fintype {x : f.fiber s // IsIsolatedPoint x} := hfinite.fintype
  let n := Fintype.card {x : f.fiber s // IsIsolatedPoint x}
  let ePoints : Fin n ≃ {x : f.fiber s // IsIsolatedPoint x} := (Fintype.equivFin _).symm
  let x : Fin n → X := fun i => ((f.fiberHomeo s) (ePoints i).val).1
  have hx : ∀ i, f (x i) = s := fun i => ((f.fiberHomeo s) (ePoints i).val).2
  have hxi : Function.Injective x := by
    intro i j hij
    apply ePoints.injective
    apply Subtype.ext
    apply (f.fiberι s).isEmbedding.injective
    simpa [x, Scheme.Hom.fiberHomeo_apply] using hij
  obtain ⟨U, hU, P, j, hjopen, -, hjiso, v, hjfinite, -, -, -, hnone⟩ :=
    exists_elementaryEtaleNeighborhood_decomposition f s n x hx hxi
      fun i => isOpen_singleton_asFiber_fiberHomeo f (ePoints i).property
  have := isOpenImmersion_sigmaDesc_some P j
  let W := (j none).opensRange
  obtain ⟨J, hJ, hJproj⟩ := exists_isOpenImmersion_fiber_ι_comp_snd f s U hU W
  have hW_noisolated :
      ∀ z : (W.ι ≫ pullback.snd f U.toBase).fiber U.point, ¬ IsIsolatedPoint z := by
    intro z hz
    have hJz : IsOpen ({J z} : Set (f.fiber s)) := by
      have hzopen : IsOpen ({z} : Set _) := by simpa [IsIsolatedPoint] using hz
      simpa only [Set.image_singleton] using J.isOpenEmbedding.isOpen_iff_image_isOpen.mp hzopen
    obtain ⟨i, hi⟩ := ePoints.surjective ⟨J z, hJz⟩
    have hiPoint : J z = (ePoints i).val := (congrArg Subtype.val hi).symm
    obtain ⟨a, ha⟩ : W.ι ((W.ι ≫ pullback.snd f U.toBase).fiberι U.point z) ∈
        Set.range (j none) := by
      rw [← show Set.range W.ι = Set.range (j none) by simp [W]]
      exact ⟨_, rfl⟩
    let h := W.ι ≫ pullback.snd f U.toBase
    have hzBase : h (h.fiberι U.point z) = U.point := by
      simpa [Scheme.Hom.fiberHomeo_apply] using (h.fiberHomeo U.point z).property
    refine hnone a ?_ i ?_
    · change pullback.snd f U.toBase (j none a) = U.point
      rw [ha]
      exact hzBase
    · change pullback.fst f U.toBase (j none a) = x i
      rw [ha, ← hJproj, hiPoint]
      simp [x, Scheme.Hom.fiberHomeo_apply]
  refine ⟨U, hU, W, _, isCompl_opensRange_sigmaDesc_some P j,
    isFinite_opensRange_sigmaDesc_some_ι_comp P j _, hW_noisolated, fun hfiniteFiber => ?_⟩
  let : Fintype (f ⁻¹' {s}) := hfiniteFiber.fintype
  have : Finite (f.fiber s) := Finite.of_injective (f.fiberHomeo s) (f.fiberHomeo s).injective
  exact isEmpty_of_forall_not_isIsolatedPoint J.isOpenEmbedding.continuous
    J.isOpenEmbedding.injective hW_noisolated

end AlgebraicGeometry

end
