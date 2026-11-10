module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.LocalStructure.OpenCopies
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic

/-!
# Étale local splitting of a separated morphism étale at finitely many points

Let `f : X ⟶ S` be a separated morphism of schemes which is étale at finitely many points
`x₁, …, xₙ` of a single fibre `f ⁻¹' {s}`. Over a suitable étale neighbourhood `(U, u)` of
`(S, s)` the base change decomposes as a finite disjoint union
`X ×_S U = W ⊔ ⨆_{i,j} V_{i,j}`, where each `V_{i,j}` maps isomorphically onto `U` and the fibre
of `W` over `u` contains no point lying above any of the `xᵢ`. If the `xᵢ` exhaust the fibre
`f ⁻¹' {s}`, that remaining fibre is empty.

## Main definitions

* `AlgebraicGeometry.Scheme.Opens.sectionOfIsIso` is the section of a morphism of schemes
  determined by an open subscheme of its source mapping isomorphically onto its target.

## Main results

* `AlgebraicGeometry.Scheme.Opens.isClosed_of_isIso_ι_comp`: such an open subscheme is closed
  when the morphism is separated.
* `AlgebraicGeometry.exists_etaleNeighborhood_disjoint_openCopies_decomposition`: the étale-local
  disjoint decomposition, together with its empty-remainder specialisation.

## Implementation notes

The finite disjoint union decomposition is recorded intrinsically, by pairwise disjoint open
subschemes whose supremum together with the remainder is the whole base change; the copies are
indexed by dependent pairs `⟨i, j⟩` with `i : Fin n` and `j : Fin (m i)`. The assertion about the
fibre of the remainder is written through its canonical fibre inclusion
`AlgebraicGeometry.Scheme.Hom.fiberι`, and the final implication is the "in particular" clause of
the source.

Separatedness enters only through the fact that an open subscheme mapping isomorphically onto the
base is also closed, which is what makes the union of the copies closed and hence its complement
open. Shrinking the base so that distinct copies become genuinely disjoint, rather than merely
disjoint over the distinguished point, removes from `U` the closed set of points at which one
section meets another copy.

Since the given points need not be distinct, the copies are produced for the (finite) set of
values of the family and transported back along a choice of index realising each value; the
multiplicity of a repeated index is set to zero.

## References

* [Stacks Project, Tag 04HM](https://stacks.math.columbia.edu/tag/04HM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Function

universe u

/-- An open set whose underlying set is closed has its pseudo-complement as a complement. -/
private lemma TopologicalSpace.Opens.sup_compl_eq_top_of_isClosed {T : Type*} [TopologicalSpace T]
    (O : TopologicalSpace.Opens T) (h : IsClosed (O : Set T)) : O ⊔ Oᶜ = ⊤ := by
  refine TopologicalSpace.Opens.ext ?_
  ext z
  refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
  by_cases hz : z ∈ O
  · exact Or.inl hz
  · exact Or.inr (TopologicalSpace.Opens.mem_compl.2 ⟨⟨(O : Set T)ᶜ, h.isOpen_compl⟩,
      TopologicalSpace.Opens.coe_disjoint.mp (Set.disjoint_left.mpr fun y hyO hyC ↦ hyO hyC), hz⟩)

/-- The supremum of finitely many open sets with closed underlying sets has closed underlying
set. -/
private lemma TopologicalSpace.Opens.isClosed_sSup_range {T : Type*} [TopologicalSpace T]
    {A : Type*} [Finite A] (O : A → TopologicalSpace.Opens T) (h : ∀ a, IsClosed (O a : Set T)) :
    IsClosed ((sSup (Set.range O) : TopologicalSpace.Opens T) : Set T) := by
  rw [TopologicalSpace.Opens.coe_sSup, Set.biUnion_range]
  exact isClosed_iUnion_of_finite h

namespace AlgebraicGeometry

/-- The section of `p : T ⟶ U` determined by an open subscheme `V` of `T` which maps
isomorphically onto `U`: the inverse of `V.ι ≫ p`, followed by the inclusion of `V`. -/
public def Scheme.Opens.sectionOfIsIso {T U : Scheme.{u}} (V : T.Opens) (p : T ⟶ U)
    [IsIso (V.ι ≫ p)] : U ⟶ T :=
  (asIso (V.ι ≫ p)).inv ≫ V.ι

/-- The section attached to an open subscheme mapping isomorphically onto the base is indeed a
section of the morphism. -/
@[simp]
public lemma Scheme.Opens.sectionOfIsIso_comp {T U : Scheme.{u}} (V : T.Opens) (p : T ⟶ U)
    [IsIso (V.ι ≫ p)] : V.sectionOfIsIso p ≫ p = 𝟙 U := by
  simp [Scheme.Opens.sectionOfIsIso]

/-- A point of an open subscheme which maps isomorphically onto the base is the value of the
corresponding section at its image. -/
public lemma Scheme.Opens.sectionOfIsIso_apply {T U : Scheme.{u}} (V : T.Opens) (p : T ⟶ U)
    [IsIso (V.ι ≫ p)] {z : T} (hz : z ∈ V) : V.sectionOfIsIso p (p z) = z := by
  obtain ⟨v, rfl⟩ : z ∈ Set.range V.ι := by rwa [Scheme.Opens.range_ι]
  have hcomp : V.ι ≫ p ≫ V.sectionOfIsIso p = V.ι := by
    dsimp only [Scheme.Opens.sectionOfIsIso]
    rw [asIso_inv, ← Category.assoc V.ι p, IsIso.hom_inv_id_assoc]
  have hfac : V.sectionOfIsIso p (p (V.ι v)) = (V.ι ≫ p ≫ V.sectionOfIsIso p) v := by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  rw [hfac, hcomp]

/-- The image of the section attached to an open subscheme mapping isomorphically onto the base
is that open subscheme. -/
public lemma Scheme.Opens.range_sectionOfIsIso {T U : Scheme.{u}} (V : T.Opens) (p : T ⟶ U)
    [IsIso (V.ι ≫ p)] : Set.range (V.sectionOfIsIso p).base = (V : Set T) := by
  refine Set.Subset.antisymm ?_ fun z hz ↦ ⟨p z, V.sectionOfIsIso_apply p hz⟩
  rintro _ ⟨w, rfl⟩
  have hmem : V.sectionOfIsIso p w ∈ Set.range V.ι.base := ⟨(asIso (V.ι ≫ p)).inv w, rfl⟩
  rwa [Scheme.Opens.range_ι] at hmem

/-- An open subscheme which maps isomorphically onto the target of a separated morphism is
closed: it is the image of a section, and a section of a separated morphism is a closed
immersion. -/
@[sga "1 II 4.17" "special case"]
public lemma Scheme.Opens.isClosed_of_isIso_ι_comp {T U : Scheme.{u}} (V : T.Opens) (p : T ⟶ U)
    [IsSeparated p] [IsIso (V.ι ≫ p)] : IsClosed (V : Set T) := by
  have hcomp : IsClosedImmersion (V.sectionOfIsIso p ≫ p) := by
    rw [V.sectionOfIsIso_comp p]
    infer_instance
  rw [← V.range_sectionOfIsIso p]
  exact (IsClosedImmersion.of_comp (V.sectionOfIsIso p) p).isClosedEmbedding.isClosed_range

/-- Finitely many open subschemes which map isomorphically onto the target of a separated
morphism and which pairwise avoid one another over a given point also pairwise avoid one another
over an open neighbourhood of that point. -/
private theorem exists_open_avoiding_section_images {T U : Scheme.{u}} {A : Type*} [Finite A]
    (p : T ⟶ U) [IsSeparated p] (V : A → T.Opens) (u : U)
    (hIso : ∀ a, IsIso ((V a).ι ≫ p))
    (hsep : ∀ a b, a ≠ b → ∀ z : T, z ∈ (V a).1 → z ∈ (V b).1 → p z ≠ u) :
    ∃ Q : U.Opens, u ∈ Q.1 ∧
      ∀ a b, a ≠ b → ∀ v : U, v ∈ Q.1 → (V a).sectionOfIsIso p v ∉ (V b).1 := by
  classical
  let bad (a b : A) : Set U := {v | a ≠ b ∧ (V a).sectionOfIsIso p v ∈ (V b).1}
  have hbadClosed (a b : A) : IsClosed (bad a b) := by
    by_cases hab : a = b
    · subst hab
      simp [bad]
    · have hpre : IsClosed {v : U | (V a).sectionOfIsIso p v ∈ (V b).1} :=
        ((V b).isClosed_of_isIso_ι_comp p).preimage ((V a).sectionOfIsIso p).continuous
      simpa [bad, hab] using hpre
  have hnot (a b : A) : u ∉ bad a b := by
    rintro ⟨hab, hb⟩
    have ha : (V a).sectionOfIsIso p u ∈ ((V a) : Set T) := by
      rw [← (V a).range_sectionOfIsIso p]
      exact ⟨u, rfl⟩
    refine hsep a b hab ((V a).sectionOfIsIso p u) ha hb ?_
    rw [← Scheme.Hom.comp_apply, (V a).sectionOfIsIso_comp p]
    simp
  refine ⟨⟨(⋃ a : A, ⋃ b : A, bad a b)ᶜ, (isClosed_iUnion_of_finite fun a ↦
    isClosed_iUnion_of_finite (hbadClosed a)).isOpen_compl⟩, fun hm ↦ ?_,
    fun a b hab v hv hvb ↦ hv (Set.mem_iUnion₂.2 ⟨a, b, hab, hvb⟩)⟩
  obtain ⟨a, b, hm⟩ := Set.mem_iUnion₂.1 hm
  exact hnot a b hm

/-- The morphism of base changes induced by the inclusion of an open subscheme of the base. -/
private def baseChangeRestrict {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (Q : Y.Opens) :
    pullback f (Q.ι ≫ g) ⟶ pullback f g :=
  (pullbackLeftPullbackSndIso f g Q.ι).inv ≫ pullback.fst (pullback.snd f g) Q.ι

private theorem baseChangeRestrict_fst {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (Q : Y.Opens) :
    baseChangeRestrict f g Q ≫ pullback.fst f g = pullback.fst f (Q.ι ≫ g) :=
  pullbackLeftPullbackSndIso_inv_fst f g Q.ι

private theorem baseChangeRestrict_snd {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (Q : Y.Opens) :
    baseChangeRestrict f g Q ≫ pullback.snd f g = pullback.snd f (Q.ι ≫ g) ≫ Q.ι := by
  dsimp only [baseChangeRestrict]
  rw [Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd]

private theorem baseChangeRestrict_snd_apply {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (Q : Y.Opens) (z : (pullback f (Q.ι ≫ g) : Scheme.{u})) :
    pullback.snd f g (baseChangeRestrict f g Q z) = Q.ι (pullback.snd f (Q.ι ≫ g) z) := by
  simpa [Scheme.Hom.comp_apply] using congrArg (fun k ↦ k z) (baseChangeRestrict_snd f g Q)

private theorem baseChangeRestrict_fst_apply {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (Q : Y.Opens) (z : (pullback f (Q.ι ≫ g) : Scheme.{u})) :
    pullback.fst f g (baseChangeRestrict f g Q z) = pullback.fst f (Q.ι ≫ g) z := by
  rw [← Scheme.Hom.comp_apply, baseChangeRestrict_fst]

/-- Preimages, in the base change over an open subscheme `Q` of the base, of open subschemes
mapping isomorphically onto the base whose sections over `Q` avoid one another, are pairwise
disjoint. -/
private theorem pairwise_disjoint_baseChangeRestrict_preimage {X Y S : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) (Q : Y.Opens) {A : Type*} (V : A → (pullback f g).Opens)
    (hIso : ∀ a, IsIso ((V a).ι ≫ pullback.snd f g))
    (hQsep : ∀ a b, a ≠ b → ∀ v : Y, v ∈ Q.1 →
      (V a).sectionOfIsIso (pullback.snd f g) v ∉ (V b).1) :
    Pairwise (Disjoint on fun a ↦ baseChangeRestrict f g Q ⁻¹ᵁ V a) := by
  intro a b hab
  change Disjoint (baseChangeRestrict f g Q ⁻¹ᵁ V a) (baseChangeRestrict f g Q ⁻¹ᵁ V b)
  rw [← TopologicalSpace.Opens.coe_disjoint]
  refine Set.disjoint_left.mpr fun z haz hbz ↦ ?_
  refine hQsep a b hab (Q.ι (pullback.snd f (Q.ι ≫ g) z)) (pullback.snd f (Q.ι ≫ g) z).property ?_
  rw [← baseChangeRestrict_snd_apply, (V a).sectionOfIsIso_apply (pullback.snd f g)
    (TopologicalSpace.Opens.mem_comap.1 haz)]
  exact TopologicalSpace.Opens.mem_comap.1 hbz

/-- An open subscheme of a base change which maps isomorphically onto the base stays isomorphic
to the base after restricting the base to an open subscheme. -/
private def copyIso {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (Q : Y.Opens)
    (V : (pullback f g).Opens) (hV : IsIso (V.ι ≫ pullback.snd f g)) :
    pullback V.ι (pullback.fst (pullback.snd f g) Q.ι) ≅ Q.toScheme :=
  have : IsIso (pullback.snd (V.ι ≫ pullback.snd f g) Q.ι) :=
    pullback_snd_iso_of_left_iso (V.ι ≫ pullback.snd f g) Q.ι
  pullbackRightPullbackFstIso (pullback.snd f g) Q.ι V.ι ≪≫
    asIso (pullback.snd (V.ι ≫ pullback.snd f g) Q.ι)

private theorem copyIso_hom {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (Q : Y.Opens)
    (V : (pullback f g).Opens) (hV : IsIso (V.ι ≫ pullback.snd f g)) :
    (copyIso f g Q V hV).hom =
      pullback.snd V.ι (pullback.fst (pullback.snd f g) Q.ι) ≫
        pullback.snd (pullback.snd f g) Q.ι := by
  simp [copyIso, pullbackRightPullbackFstIso_hom_snd]

/-- The comparison morphism between the two descriptions of the preimage of an open subscheme of
a base change inside the base change over an open subscheme of the base. -/
private def copyPreimageCompare {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (Q : Y.Opens)
    (V : (pullback f g).Opens) :
    pullback V.ι (baseChangeRestrict f g Q) ⟶
      pullback V.ι (pullback.fst (pullback.snd f g) Q.ι) :=
  pullback.map V.ι (baseChangeRestrict f g Q) V.ι (pullback.fst (pullback.snd f g) Q.ι)
    (𝟙 V.toScheme) (pullbackLeftPullbackSndIso f g Q.ι).inv (𝟙 (pullback f g))
    (by rw [Category.comp_id, Category.id_comp])
    (by dsimp only [baseChangeRestrict]; rw [Category.comp_id])

private instance isIso_copyPreimageCompare {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (Q : Y.Opens) (V : (pullback f g).Opens) : IsIso (copyPreimageCompare f g Q V) := by
  dsimp only [copyPreimageCompare]
  infer_instance

/-- The preimage, in the base change over an open subscheme of the base, of an open subscheme
mapping isomorphically onto the base is isomorphic to that open subscheme of the base. -/
private def copyPreimageIso {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (Q : Y.Opens)
    (V : (pullback f g).Opens) (hV : IsIso (V.ι ≫ pullback.snd f g)) :
    pullback V.ι (baseChangeRestrict f g Q) ≅ Q.toScheme :=
  asIso (copyPreimageCompare f g Q V) ≪≫ copyIso f g Q V hV

private theorem copyPreimageIso_hom {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (Q : Y.Opens)
    (V : (pullback f g).Opens) (hV : IsIso (V.ι ≫ pullback.snd f g)) :
    (copyPreimageIso f g Q V hV).hom =
      pullback.snd V.ι (baseChangeRestrict f g Q) ≫ pullback.snd f (Q.ι ≫ g) := by
  have ht : copyPreimageCompare f g Q V ≫
      pullback.snd V.ι (pullback.fst (pullback.snd f g) Q.ι) =
      pullback.snd V.ι (baseChangeRestrict f g Q) ≫
        (pullbackLeftPullbackSndIso f g Q.ι).inv := by
    dsimp only [copyPreimageCompare, pullback.map]
    rw [pullback.lift_snd]
  dsimp only [copyPreimageIso]
  rw [Iso.trans_hom, asIso_hom, copyIso_hom, ← Category.assoc, ht, Category.assoc,
    pullbackLeftPullbackSndIso_inv_snd_snd]

/-- After restricting the base to an open subscheme, the preimage of an open subscheme of a base
change which maps isomorphically onto the base again maps isomorphically onto the new base. -/
private theorem isIso_copyPreimage {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (Q : Y.Opens)
    (V : (pullback f g).Opens) (hV : IsIso (V.ι ≫ pullback.snd f g)) :
    IsIso ((baseChangeRestrict f g Q ⁻¹ᵁ V).ι ≫ pullback.snd f (Q.ι ≫ g)) := by
  have hrange : Set.range (pullback.snd V.ι (baseChangeRestrict f g Q)) =
      Set.range (baseChangeRestrict f g Q ⁻¹ᵁ V).ι := by
    rw [Scheme.Opens.range_ι]
    simpa using IsOpenImmersion.range_pullbackSnd V.ι (baseChangeRestrict f g Q)
  have hfac : (IsOpenImmersion.isoOfRangeEq (pullback.snd V.ι (baseChangeRestrict f g Q))
      (baseChangeRestrict f g Q ⁻¹ᵁ V).ι hrange).inv ≫
      pullback.snd V.ι (baseChangeRestrict f g Q) = (baseChangeRestrict f g Q ⁻¹ᵁ V).ι :=
    IsOpenImmersion.isoOfRangeEq_inv_fac _ _ hrange
  rw [← hfac, Category.assoc, ← copyPreimageIso_hom f g Q V hV]
  infer_instance

/-- A point of the fibre of the remainder `W` of a base change lies over the chosen point. -/
private theorem snd_fiberι_comp_apply {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (W : (pullback f g).Opens) (u : Y) (z : (W.ι ≫ pullback.snd f g).fiber u) :
    pullback.snd f g (((W.ι ≫ pullback.snd f g).fiberι u ≫ W.ι) z) = u := by
  simpa [Scheme.Hom.comp_apply] using (W.ι ≫ pullback.snd f g).apply_fiberι u z

/-- Shrinking the étale neighbourhood turns open subschemes of the base change which are copies
of the base and meet nowhere over the distinguished point into genuinely disjoint ones, whose
complement has a fibre over the distinguished point containing none of the given points. -/
private theorem exists_etaleNeighborhood_disjointOpenCopies_of_openCopies
    {X S : Scheme.{u}} {s : S} (f : X ⟶ S) [IsSeparated f] (U : EtaleNeighborhood S s)
    {ι : Type*} [Finite ι] (x : ι → X) (m : ι → ℕ)
    (V : (Σ i, Fin (m i)) → (pullback f U.toBase).Opens)
    (hIso : ∀ a, IsIso ((V a).ι ≫ pullback.snd f U.toBase))
    (hsep : ∀ a b, a ≠ b → ∀ z : (pullback f U.toBase : Scheme.{u}),
      z ∈ (V a).1 → z ∈ (V b).1 → pullback.snd f U.toBase z ≠ U.point)
    (hcover : ∀ i (z : (pullback f U.toBase : Scheme.{u})),
      pullback.snd f U.toBase z = U.point → pullback.fst f U.toBase z = x i →
        ∃ j : Fin (m i), z ∈ (V ⟨i, j⟩).1) :
    ∃ (U' : EtaleNeighborhood S s) (W : (pullback f U'.toBase).Opens)
      (V' : (Σ i, Fin (m i)) → (pullback f U'.toBase).Opens),
      sSup (Set.range V') ⊔ W = ⊤ ∧ Pairwise (Disjoint on V') ∧ (∀ a, Disjoint (V' a) W) ∧
        (∀ a, IsIso ((V' a).ι ≫ pullback.snd f U'.toBase)) ∧
        ∀ (z : (W.ι ≫ pullback.snd f U'.toBase).fiber U'.point) (i : ι),
          ((W.ι ≫ pullback.snd f U'.toBase).fiberι U'.point ≫ W.ι ≫
            pullback.fst f U'.toBase) z ≠ x i := by
  classical
  obtain ⟨Q, hQ, hQsep⟩ :=
    exists_open_avoiding_section_images (pullback.snd f U.toBase) V U.point hIso hsep
  let u : Q.toScheme := ⟨U.point, hQ⟩
  let g := baseChangeRestrict f U.toBase Q
  let V' : (Σ i, Fin (m i)) → (pullback f (Q.ι ≫ U.toBase)).Opens := fun a ↦ g ⁻¹ᵁ V a
  let W : (pullback f (Q.ι ≫ U.toBase)).Opens := (sSup (Set.range V'))ᶜ
  have hpairs : Pairwise (Disjoint on V') :=
    pairwise_disjoint_baseChangeRestrict_preimage f U.toBase Q V hIso hQsep
  have hdisjoint (a : Σ i, Fin (m i)) : Disjoint (V' a) W :=
    (le_sSup (show V' a ∈ Set.range V' from ⟨a, rfl⟩)).disjoint_compl_right
  have hIso' (a : Σ i, Fin (m i)) :
      IsIso ((V' a).ι ≫ pullback.snd f (Q.ι ≫ U.toBase)) :=
    isIso_copyPreimage f U.toBase Q (V a) (hIso a)
  have hcover' (i : ι) (z : (pullback f (Q.ι ≫ U.toBase) : Scheme.{u}))
      (hz : pullback.snd f (Q.ι ≫ U.toBase) z = u)
      (hzx : pullback.fst f (Q.ι ≫ U.toBase) z = x i) :
      ∃ j : Fin (m i), z ∈ (V' ⟨i, j⟩).1 := by
    have hzbase : pullback.snd f U.toBase (g z) = U.point := by
      rw [baseChangeRestrict_snd_apply, hz]
      rfl
    exact hcover i (g z) hzbase ((baseChangeRestrict_fst_apply f U.toBase Q z).trans hzx)
  have hno (z : (W.ι ≫ pullback.snd f (Q.ι ≫ U.toBase)).fiber u) (i : ι) :
      ((W.ι ≫ pullback.snd f (Q.ι ≫ U.toBase)).fiberι u ≫ W.ι ≫
        pullback.fst f (Q.ι ≫ U.toBase)) z ≠ x i := by
    intro hzi
    obtain ⟨j, hj⟩ := hcover' i _ (snd_fiberι_comp_apply f (Q.ι ≫ U.toBase) W u z) hzi
    exact (Set.disjoint_left.mp (TopologicalSpace.Opens.coe_disjoint.mpr (hdisjoint ⟨i, j⟩)))
      hj ((W.ι ≫ pullback.snd f (Q.ι ≫ U.toBase)).fiberι u z).2
  have hclosedEach (a : Σ i, Fin (m i)) :
      IsClosed ((V' a) : Set (pullback f (Q.ι ≫ U.toBase) : Scheme.{u})) :=
    have := hIso' a
    (V' a).isClosed_of_isIso_ι_comp (pullback.snd f (Q.ι ≫ U.toBase))
  have htop : sSup (Set.range V') ⊔ W = ⊤ :=
    (sSup (Set.range V')).sup_compl_eq_top_of_isClosed
      (TopologicalSpace.Opens.isClosed_sSup_range V' hclosedEach)
  exact ⟨U.restrict Q hQ, W, V', htop, hpairs, hdisjoint, hIso', hno⟩

/-- The copies produced for a family of points of a single fibre, indexed by the set of values of
that family rather than by its index type. -/
private theorem exists_etaleNeighborhood_openCopies_cover_range {X S : Scheme.{u}} (f : X ⟶ S)
    (n : ℕ) (x : Fin n → X) (s : S) (hx : ∀ i, f (x i) = s)
    (hetale : ∀ i, EtaleAt f (x i)) :
    ∃ (U : EtaleNeighborhood S s) (m : Set.range x → ℕ)
      (V : (Σ i, Fin (m i)) → (pullback f U.toBase).Opens),
      (∀ a, IsIso ((V a).ι ≫ pullback.snd f U.toBase)) ∧
        (∀ a b, a ≠ b → ∀ z : (pullback f U.toBase : Scheme.{u}),
          z ∈ (V a).1 → z ∈ (V b).1 → pullback.snd f U.toBase z ≠ U.point) ∧
        ∀ i (z : (pullback f U.toBase : Scheme.{u})),
          pullback.snd f U.toBase z = U.point → pullback.fst f U.toBase z = x i →
            ∃ j : Fin (m ⟨x i, ⟨i, rfl⟩⟩), z ∈ (V ⟨⟨x i, ⟨i, rfl⟩⟩, j⟩).1 := by
  classical
  let α : Type u := Set.range x
  let e : α ≃ Fin (Nat.card α) := Finite.equivFin α
  let y : Fin (Nat.card α) → X := fun i ↦ (e.symm i).1
  have hyinj : Function.Injective y := fun i j hij ↦ e.symm.injective (Subtype.ext hij)
  have hybase (i : Fin (Nat.card α)) : f (y i) = s := by
    obtain ⟨j, hj⟩ := (e.symm i).2
    exact (congrArg f hj).symm.trans (hx j)
  have hyetale (i : Fin (Nat.card α)) : EtaleAt f (y i) := by
    obtain ⟨j, hj⟩ := (e.symm i).2
    rw [show y i = x j from hj.symm]
    exact hetale j
  obtain ⟨U, m, V, hIso, hsep, hcover⟩ :=
    exists_etaleNeighborhood_openCopies_cover_fibers f (Nat.card α) y s hyinj hybase hyetale
  refine ⟨U, fun a ↦ m (e a), fun a ↦ V ⟨e a.1, a.2⟩, fun a ↦ hIso ⟨e a.1, a.2⟩, ?_, ?_⟩
  · intro a b hab z haz hbz
    refine hsep ⟨e a.1, a.2⟩ ⟨e b.1, b.2⟩ (fun h ↦ hab ?_) z haz hbz
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    simp only [Sigma.mk.injEq] at h
    exact Sigma.ext (e.injective h.1) h.2
  · intro i z hz hzx
    exact hcover (e ⟨x i, ⟨i, rfl⟩⟩) z hz (by simpa [y] using hzx)

/-- Transport of a dependent index along an equality of the bounds. -/
private lemma heq_fin_cast {n m : ℕ} (h : n = m) (i : Fin n) : Fin.cast h i ≍ i :=
  (Fin.heq_ext_iff h.symm).mpr rfl

/-- If no point of the fibre of the remainder `W` of a base change maps to one of the points
`x i`, and these points exhaust the fibre of `f` over `s`, then the fibre of `W` is empty. -/
private theorem isEmpty_fiber_of_forall_fst_ne {X S : Scheme.{u}} {s : S} (f : X ⟶ S)
    (U : EtaleNeighborhood S s) (W : (pullback f U.toBase).Opens) {ι : Type*} (x : ι → X)
    (hno : ∀ (z : (W.ι ≫ pullback.snd f U.toBase).fiber U.point) (i : ι),
      ((W.ι ≫ pullback.snd f U.toBase).fiberι U.point ≫ W.ι ≫
        pullback.fst f U.toBase) z ≠ x i)
    (hex : ∀ y : X, f y = s → ∃ i, y = x i) :
    IsEmpty ((W.ι ≫ pullback.snd f U.toBase).fiber U.point) := by
  refine ⟨fun z ↦ ?_⟩
  let z' : (pullback f U.toBase : Scheme.{u}) :=
    ((W.ι ≫ pullback.snd f U.toBase).fiberι U.point ≫ W.ι) z
  have hbase : pullback.snd f U.toBase z' = U.point :=
    snd_fiberι_comp_apply f U.toBase W U.point z
  have hpull : f (pullback.fst f U.toBase z') = U.toBase (pullback.snd f U.toBase z') := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun k : (pullback f U.toBase : Scheme.{u}) ⟶ S ↦ k z') pullback.condition
  rw [hbase] at hpull
  obtain ⟨i, hy⟩ := hex _ (hpull.trans U.map_point)
  exact hno z i (by simpa [z', Scheme.Hom.comp_apply] using hy)

/-- **Stacks Project, Tag 04HM.** After an étale base change, a separated morphism which is étale
at finitely many points over one point of the base is the disjoint union of copies of the new
base together with a remainder whose distinguished fibre contains none of those points. If the
given points exhaust the original fibre, that remaining fibre is empty. -/
@[stacks 04HM]
public theorem exists_etaleNeighborhood_disjoint_openCopies_decomposition
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (n : ℕ) (x : Fin n → X) (s : S)
    (hx : ∀ i, f (x i) = s) (hetale : ∀ i, EtaleAt f (x i)) :
    ∃ (U : EtaleNeighborhood S s) (W : (pullback f U.toBase).Opens) (m : Fin n → ℕ)
      (V : (Σ i, Fin (m i)) → (pullback f U.toBase).Opens),
      sSup (Set.range V) ⊔ W = ⊤ ∧ Pairwise (Disjoint on V) ∧ (∀ a, Disjoint (V a) W) ∧
        (∀ a, IsIso ((V a).ι ≫ pullback.snd f U.toBase)) ∧
        (∀ (z : (W.ι ≫ pullback.snd f U.toBase).fiber U.point) (i : Fin n),
          ((W.ι ≫ pullback.snd f U.toBase).fiberι U.point ≫ W.ι ≫
            pullback.fst f U.toBase) z ≠ x i) ∧
        ((∀ y : X, f y = s → ∃ i, y = x i) →
          IsEmpty ((W.ι ≫ pullback.snd f U.toBase).fiber U.point)) := by
  classical
  let α : Type u := Set.range x
  let pt (i : Fin n) : α := ⟨x i, ⟨i, rfl⟩⟩
  let rep (a : α) : Fin n := Classical.choose a.2
  have hrep (a : α) : x (rep a) = a.1 := Classical.choose_spec a.2
  have hptrep (a : α) : pt (rep a) = a := Subtype.ext (hrep a)
  obtain ⟨U₀, m₀, V₀, hIso₀, hsep₀, hcover₀⟩ :=
    exists_etaleNeighborhood_openCopies_cover_range f n x s hx hetale
  have hcoverα (a : α) (z : (pullback f U₀.toBase : Scheme.{u}))
      (hz : pullback.snd f U₀.toBase z = U₀.point)
      (hzx : pullback.fst f U₀.toBase z = a.1) :
      ∃ j : Fin (m₀ a), z ∈ (V₀ ⟨a, j⟩).1 := by
    obtain ⟨j, hj⟩ := hcover₀ (rep a) z hz (by rwa [hrep a])
    have he : m₀ (pt (rep a)) = m₀ a := congrArg m₀ (hptrep a)
    exact ⟨Fin.cast he j, (Sigma.ext (hptrep a) (heq_fin_cast he j).symm :
      (⟨pt (rep a), j⟩ : Σ a : α, Fin (m₀ a)) = ⟨a, Fin.cast he j⟩) ▸ hj⟩
  obtain ⟨U, W, Vα, htopα, hpairsα, hdisjointα, hIsoα, hnoα⟩ :=
    exists_etaleNeighborhood_disjointOpenCopies_of_openCopies f U₀ (fun a : α ↦ a.1) m₀ V₀
      hIso₀ hsep₀ hcoverα
  let m : Fin n → ℕ := fun i ↦ if i = rep (pt i) then m₀ (pt i) else 0
  have hactive (a : Σ i : Fin n, Fin (m i)) : a.1 = rep (pt a.1) := by
    by_contra h
    simpa [m, h] using a.2.isLt
  have hm (i : Fin n) (hi : i = rep (pt i)) : m i = m₀ (pt i) := ite_eq_left hi
  let label (a : Σ i : Fin n, Fin (m i)) : Σ a : α, Fin (m₀ a) :=
    ⟨pt a.1, Fin.cast (hm a.1 (hactive a)) a.2⟩
  let V : (Σ i : Fin n, Fin (m i)) → (pullback f U.toBase).Opens := fun a ↦ Vα (label a)
  have hlabel_injective : Function.Injective label := by
    intro a b hab
    have hi : a.1 = b.1 :=
      (hactive a).trans ((congrArg rep (congrArg Sigma.fst hab)).trans (hactive b).symm)
    exact Sigma.ext hi <| (heq_fin_cast (hm a.1 (hactive a)) a.2).symm.trans
      ((Sigma.ext_iff.mp hab).2.trans (heq_fin_cast (hm b.1 (hactive b)) b.2))
  have hcopies : Set.range V = Set.range Vα := by
    refine Set.ext fun Z ↦ ⟨fun ⟨a, ha⟩ ↦ ⟨label a, ha⟩, ?_⟩
    rintro ⟨b, rfl⟩
    have hpt : pt (rep b.1) = b.1 := hptrep b.1
    have hi : rep b.1 = rep (pt (rep b.1)) := (congrArg rep hpt).symm
    have hmi : m (rep b.1) = m₀ b.1 := (hm (rep b.1) hi).trans (congrArg m₀ hpt)
    refine ⟨⟨rep b.1, Fin.cast hmi.symm b.2⟩, congrArg Vα ?_⟩
    exact Sigma.ext hpt ((heq_fin_cast (hm (rep b.1) hi) (Fin.cast hmi.symm b.2)).trans
      (heq_fin_cast hmi.symm b.2))
  have hno (z : (W.ι ≫ pullback.snd f U.toBase).fiber U.point) (i : Fin n) :
      ((W.ι ≫ pullback.snd f U.toBase).fiberι U.point ≫ W.ι ≫
        pullback.fst f U.toBase) z ≠ x i := by
    simpa [pt] using hnoα z (pt i)
  exact ⟨U, W, m, V, by rwa [hcopies], fun a b hab ↦ hpairsα (hlabel_injective.ne hab),
    fun a ↦ hdisjointα (label a), fun a ↦ hIsoα (label a), hno,
    isEmpty_fiber_of_forall_fst_ne f U W x hno⟩

end AlgebraicGeometry

end
