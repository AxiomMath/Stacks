module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Full.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.SurjectiveComponents
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.NormalizedPointBlowupSequence

/-!
# Sequences of normalized point blowups under the local correspondence

Let `S` be a scheme with finitely many pairwise distinct closed points `s i` whose open complement
`U` has quasi-compact inclusion, and let `F` be the base-change functor of [Stacks, Tag 0BFU] from
finitely presented modifications of `S` which are isomorphisms over `U` to the product of the
corresponding categories over the `S_i = Spec 𝒪_{S, s i}`. [Stacks, Tag 0BFZ] asserts that, when
every quasi-compact open of `S` has finitely many irreducible components, an object `f : X ⟶ S`
is a finite sequence of normalized blowups at closed points lying over the `s i` if and only if
each of its localizations `g i : Y i ⟶ S_i` is a finite sequence of normalized blowups at closed
points lying over the closed point.

As stated this is false, and this file proves both the failure and the corrected statement.

* Without normality the equivalence fails. The normalized blowing up normalizes the whole blown-up
  scheme, so a single step changes `S` over every non-normal point, also away from the centre.
  `AlgebraicGeometry.not_factorsAsNormalizedPointBlowups_iff` refutes the statement under exactly
  its hypotheses on `S = Spec 𝔽₂ ⨿ Spec ℤ/4` with the point of `Spec 𝔽₂` distinguished: the open
  immersion `Spec ℤ/4 ⟶ S` is an object of the category of Tag 0BFU, its localization is empty,
  which is the normalized blowing up of the one-point scheme `S_1` at its point, but it is not a
  sequence of normalized blowups, since such a sequence is either the identity or has normal
  source, and `Spec ℤ/4` is not reduced.
* Over a normal base the equivalence holds:
  `AlgebraicGeometry.FinitePresentationAwayPointsSituation.factorsAsNormalizedPointBlowups_iff`.
  Necessity is `factorsAsNormalizedPointBlowups_of_corresponds`. For sufficiency the local
  sequences are lifted one step at a time, as in the proof of Tag 0BFY: a step at a closed point of
  the localization at `s i` is the localization of the normalized blowing up of the current global
  scheme at the image of that point, and, the global scheme being normal, that step is an
  isomorphism over the open complement and after localization at the other points. The global
  sequence so obtained is compared with `X` by descent along the covering of `S` by `U` and the
  `S_i`, which needs no finite presentation of the stages: their normalizations need not be
  finite.

## Main results

* `AlgebraicGeometry.FinitePresentationAwayPointsSituation.factorsAsNormalizedPointBlowups_iff`:
  [Stacks, Tag 0BFZ] for a normal base, both directions.
* `AlgebraicGeometry.not_factorsAsNormalizedPointBlowups_iff`: the statement of Tag 0BFZ is false
  without normality.
* `AlgebraicGeometry.LocalSchemesCover.nonempty_over_iso_of_isIso_complement` and
  `AlgebraicGeometry.FinitePresentationAwayPointsSituation.nonempty_over_iso_of_baseChange`: two
  objects of `Over S` which are isomorphisms over the open complement and have isomorphic
  localizations are isomorphic, with no finite presentation.
* `Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain.finite_irreducibleComponents`: the
  schemes of a normalized point blowup chain inherit finiteness of irreducible components of
  quasi-compact opens from the base.

## References

* [Stacks Project, Tag 0BFZ](https://stacks.math.columbia.edu/tag/0BFZ)
* [Stacks Project, Tag 0BFY](https://stacks.math.columbia.edu/tag/0BFY)
* [Stacks Project, Tag 0BFU](https://stacks.math.columbia.edu/tag/0BFU)
* [Stacks Project, Tag 0BBS](https://stacks.math.columbia.edu/tag/0BBS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

open Stacks.ResolutionOfSurfaces

/-- A point of a pullback has the same image in the base under both projections. -/
private theorem pullback_condition_apply {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (z : ↥(pullback f g)) : f (pullback.fst f g z) = g (pullback.snd f g z) := by
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]

/-- A scheme with finitely many points has finitely many irreducible components in every open. -/
private theorem finite_irreducibleComponents_of_finite {X : Scheme.{u}} [Finite X] :
    ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite := by
  intro U _
  have : Finite ↥U := Subtype.finite
  have : Finite (Set ↥U) := inferInstance
  exact (Set.finite_univ : (Set.univ : Set (Set ↥U)).Finite).subset (Set.subset_univ _)

/-- Two morphisms in `Over V` into an object whose structure morphism is an isomorphism are
equal. -/
private theorem over_hom_ext_of_isIso {V : Scheme.{u}} {P Q : Over V} (hQ : IsIso Q.hom)
    (a b : P ⟶ Q) : a = b :=
  Over.OverMorphism.ext ((cancel_mono _).mp ((Over.w a).trans (Over.w b).symm))

/-! ### Blowing up a point which is the whole scheme -/

/-- The blowup of a scheme at a closed point which is its only point is empty: by Tag 0BFM its
generic points correspond to the generic points of the base outside the centre, and there are
none. -/
theorem isEmpty_blowUp_vanishingIdeal_of_forall_eq {X : Scheme.{u}} (x : X)
    (hx : IsClosed ({x} : Set X)) (hX : ∀ y : X, y = x) :
    IsEmpty (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X))) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
  refine ⟨fun y => ?_⟩
  let Z : irreducibleComponents (blowUp I) :=
    ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
  have hmaps := (bijOn_genericPoints_blowUpToBase I).mapsTo (genericPoints.ofComponent Z).2
  refine hmaps.2 (Scheme.IdealSheafData.mem_supportSet_iff_mem_support.mpr ?_)
  show _ ∈ (I.support : Set X)
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact hX _

/-- The normalized blowup of a scheme at a closed point which is its only point is empty. -/
theorem isEmpty_normalizedBlowUpScheme_of_forall_eq {X : Scheme.{u}}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (hx : IsClosed ({x} : Set X)) (hall : ∀ y : X, y = x) :
    IsEmpty (Stacks.Blowup.normalizedBlowUpScheme X hX x hx) := by
  have := isEmpty_blowUp_vanishingIdeal_of_forall_eq x hx hall
  exact ⟨fun z => IsEmpty.false
    (Scheme.normalization _ (Stacks.Blowup.finite_irreducibleComponents_blowUp _ hX) z)⟩

namespace FinitePresentationAwayPointsSituation

variable (D : FinitePresentationAwayPointsSituation.{u})

/-- The inclusion of the open complement of the distinguished points, as an object of the
category of Tag 0BFU. -/
def complementObject : D.globalCategory :=
  ⟨Over.mk D.complement.ι, ⟨(inferInstance : LocallyOfFinitePresentation D.complement.ι),
      D.complement_quasiCompact, (inferInstance : QuasiSeparated D.complement.ι)⟩,
    (inferInstance : IsIso (pullback.snd D.complement.ι D.complement.ι))⟩

/-- If the distinguished point `s i` is isolated, the spectrum of its local ring has only one
point. -/
theorem eq_closedPoint_of_isOpen {i : Fin D.n} (hi : IsOpen ({D.points i} : Set D.S))
    (y : D.localScheme i) : y = IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i)) := by
  have hspec : D.S.fromSpecStalk (D.points i) y ⤳ D.points i := by
    have hr : D.S.fromSpecStalk (D.points i) y ∈
        Set.range (D.S.fromSpecStalk (D.points i)) := ⟨y, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at hr
  have hy : D.S.fromSpecStalk (D.points i) y = D.points i := hspec.mem_open hi rfl
  exact (D.S.fromSpecStalk (D.points i)).isEmbedding.injective
    (hy.trans Scheme.fromSpecStalk_closedPoint.symm)

/-- No point of the spectrum of the local ring at an isolated distinguished point lies over the
open complement. -/
theorem isEmpty_pullback_complement_of_isOpen {i : Fin D.n}
    (hi : IsOpen ({D.points i} : Set D.S)) :
    IsEmpty ↥(pullback D.complement.ι (D.S.fromSpecStalk (D.points i))) := by
  refine ⟨fun z => ?_⟩
  have hc := pullback_condition_apply D.complement.ι (D.S.fromSpecStalk (D.points i)) z
  rw [D.eq_closedPoint_of_isOpen hi
    (pullback.snd D.complement.ι (D.S.fromSpecStalk (D.points i)) z),
    Scheme.fromSpecStalk_closedPoint] at hc
  exact (pullback.fst D.complement.ι (D.S.fromSpecStalk (D.points i)) z).2 ⟨i, hc.symm⟩

/-- **Tag 0BFZ fails without normality.** Suppose every distinguished point is isolated, there
is at least one of them, and the open complement `U` is not normal. Then the open immersion
`U ⟶ S`, an object of the category of Tag 0BFU, is not a sequence of normalized blowups at closed
points lying over the distinguished points, whereas every local modification corresponding to it
is one: the local modifications are empty, and so is the normalized blowing up of the one-point
scheme `Spec 𝒪_{S, s i}` at its point. -/
theorem not_factorsAsNormalizedPointBlowups_complementObject (hn : 0 < D.n)
    (_hopen : ∀ i, IsOpen ({D.points i} : Set D.S)) (hU : ¬ IsNormal D.complement.toScheme) :
    ¬ FactorsAsNormalizedPointBlowups D.S (Set.range D.points) D.complementObject.obj.left
        D.complementObject.obj.hom := by
  rintro ⟨Y, f, hchain, e, he⟩
  cases hchain with
  | refl =>
    have hfac : e.hom = D.complement.ι := by
      change e.hom ≫ 𝟙 _ = D.complement.ι at he
      simpa using he
    have hmem := (e.inv (D.points ⟨0, hn⟩)).2
    have h1 : e.hom (e.inv (D.points ⟨0, hn⟩)) = D.points ⟨0, hn⟩ := by
      show (e.inv ≫ e.hom) (D.points ⟨0, hn⟩) = _
      rw [e.inv_hom_id]
      rfl
    have hval : D.complement.ι (e.inv (D.points ⟨0, hn⟩)) = D.points ⟨0, hn⟩ :=
      (congrArg (fun k : D.complementObject.obj.left ⟶ D.S => k (e.inv (D.points ⟨0, hn⟩)))
        hfac).symm.trans h1
    exact hmem ⟨⟨0, hn⟩, hval.symm⟩
  | step hh hW w hw hwT =>
    have : IsNormal (Stacks.Blowup.normalizedBlowUpScheme _ hW w hw) :=
      Scheme.isNormal_normalizationScheme _
        (Stacks.Blowup.finite_irreducibleComponents_blowUp _ hW)
    exact hU (isNormal_of_iso e)

/-- At an isolated distinguished point, every local modification corresponding to the open
immersion of the complement is a one-step sequence of normalized blowups: it is empty, and so is
the normalized blowing up of the one-point scheme `Spec 𝒪_{S, s i}` at its point. -/
theorem factorsAsNormalizedPointBlowups_of_isOpen (BC : BaseChangeFunctor D) {i : Fin D.n}
    (hi : IsOpen ({D.points i} : Set D.S)) (Y : D.localCategory i)
    (hY : BC.functor.obj D.complementObject i ≅ Y) :
    FactorsAsNormalizedPointBlowups (D.localScheme i)
      {IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))} Y.obj.left Y.obj.hom := by
  have hsub : Subsingleton (D.localScheme i) :=
    ⟨fun a b => (D.eq_closedPoint_of_isOpen hi a).trans (D.eq_closedPoint_of_isOpen hi b).symm⟩
  have : Finite (D.localScheme i) := Finite.of_subsingleton
  have hfin := finite_irreducibleComponents_of_finite (X := D.localScheme i)
  have hcp := IsLocalRing.isClosed_singleton_closedPoint (D.S.presheaf.stalk (D.points i))
  let E : Y.obj ≅ (Over.pullback (D.S.fromSpecStalk (D.points i))).obj
      (Over.mk D.complement.ι) :=
    (ObjectProperty.ι (IsFinitePresentationAway (D.puncturedLocalScheme i))).mapIso hY.symm ≪≫
      (BC.pullbackIso i).app D.complementObject
  have hYe : IsEmpty Y.obj.left := by
    have := D.isEmpty_pullback_complement_of_isOpen hi
    exact ⟨fun y => IsEmpty.false
      (α := ↥(pullback D.complement.ι (D.S.fromSpecStalk (D.points i)))) (E.hom.left y)⟩
  have hNe := isEmpty_normalizedBlowUpScheme_of_forall_eq hfin _ hcp
    (D.eq_closedPoint_of_isOpen hi)
  refine ⟨_, _, NormalizedPointBlowupChain.refl.step hfin _ hcp rfl,
    isInitialOfIsEmpty.uniqueUpToIso isInitialOfIsEmpty, isInitialOfIsEmpty.hom_ext _ _⟩

end FinitePresentationAwayPointsSituation

end AlgebraicGeometry


/-! ### Finiteness of irreducible components along a chain -/

namespace Stacks.ResolutionOfSurfaces

/-- Every scheme of a normalized point blowup chain over a scheme whose quasi-compact opens have
finitely many irreducible components again has that property: it is the base, or the
normalization of a blowup of the previous scheme, and both the blowup morphism and the
normalization morphism carry generic points injectively to generic points. -/
theorem NormalizedPointBlowupChain.finite_irreducibleComponents {X : Scheme.{u}} {T : Set X}
    {Y : Scheme.{u}} {f : Y ⟶ X} (h : NormalizedPointBlowupChain X T Y f)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite := by
  cases h with
  | refl => exact hX
  | step hh hW w hw hwT =>
    have hB := Stacks.Blowup.finite_irreducibleComponents_blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds _)) hW
    have hbij := Scheme.bijOn_genericPoints_normalization _ hB
    exact finite_irreducibleComponents_of_mapsTo_injOn_genericPoints _ hbij.mapsTo hbij.injOn hB

end Stacks.ResolutionOfSurfaces

namespace AlgebraicGeometry

open Stacks.ResolutionOfSurfaces

/-! ### Descent of isomorphisms near finitely many closed points -/

namespace LocalSchemesCover

variable {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → S)
  (hs : ∀ i, s i ∈ closedPoints S)

include hs in
/-- A family of morphisms between the base changes of `A` and `B` to the local schemes at the
points amalgamates to a morphism `A ⟶ B` over `S` as soon as `B` is an isomorphism over the open
complement: over the complement there is a unique morphism, and the compatibility over the
punctured local schemes holds because their target is again an isomorphism over its base. -/
theorem exists_over_hom_of_isIso_complement (hinj : Function.Injective s)
    (hqc : QuasiCompact (complementOfClosedPoints s hs).ι) {A B : Over S}
    (hB : IsIso ((Over.pullback (complementOfClosedPoints s hs).ι).obj B).hom)
    (gL : ∀ i, (Over.pullback (S.fromSpecStalk (s i))).obj A ⟶
      (Over.pullback (S.fromSpecStalk (s i))).obj B) :
    ∃ f : A ⟶ B, ∀ i, (Over.pullback (S.fromSpecStalk (s i))).map f = gL i := by
  set U := complementOfClosedPoints s hs with hU
  let gU : (Over.pullback U.ι).obj A ⟶ (Over.pullback U.ι).obj B :=
    Over.homMk (((Over.pullback U.ι).obj A).hom ≫ inv ((Over.pullback U.ι).obj B).hom)
      (by simp)
  have hsq : ∀ i, PuncturedCompatible s hs gU gL i := by
    intro i
    let E := Over.pullbackSquareObjIso (morphismRestrict_ι (S.fromSpecStalk (s i)) U) B
    have h0 : IsIso ((Over.pullback ((S.fromSpecStalk (s i)) ∣_ U)).obj
        ((Over.pullback U.ι).obj B)).hom :=
      (IsPullback.of_hasPullback ((Over.pullback U.ι).obj B).hom
        ((S.fromSpecStalk (s i)) ∣_ U)).isIso_snd_of_isIso
    have hEl : IsIso E.inv.left := inferInstanceAs (IsIso ((Over.forget _).map E.inv))
    have h1 : IsIso ((Over.pullback (((S.fromSpecStalk (s i)) ⁻¹ᵁ U).ι)).obj
        ((Over.pullback (S.fromSpecStalk (s i))).obj B)).hom := by
      have h2 : IsIso (E.inv.left ≫ ((Over.pullback ((S.fromSpecStalk (s i)) ∣_ U)).obj
        ((Over.pullback U.ι).obj B)).hom) := inferInstance
      have hw : E.inv.left ≫ ((Over.pullback ((S.fromSpecStalk (s i)) ∣_ U)).obj
          ((Over.pullback U.ι).obj B)).hom =
          ((Over.pullback (((S.fromSpecStalk (s i)) ⁻¹ᵁ U).ι)).obj
            ((Over.pullback (S.fromSpecStalk (s i))).obj B)).hom := Over.w E.inv
      rw [hw] at h2
      exact h2
    exact over_hom_ext_of_isIso h1 _ _
  obtain ⟨f, -, hf⟩ := exists_over_hom_of_baseChange s hs gU gL hinj hqc hsq
  exact ⟨f, hf⟩

include hs in
/-- Two objects of `Over S` which are isomorphisms over the open complement of the points are
isomorphic as soon as their base changes to the local schemes at the points are. -/
theorem nonempty_over_iso_of_isIso_complement (hinj : Function.Injective s)
    (hqc : QuasiCompact (complementOfClosedPoints s hs).ι) {A B : Over S}
    (hA : IsIso ((Over.pullback (complementOfClosedPoints s hs).ι).obj A).hom)
    (hB : IsIso ((Over.pullback (complementOfClosedPoints s hs).ι).obj B).hom)
    (e : ∀ i, (Over.pullback (S.fromSpecStalk (s i))).obj A ≅
      (Over.pullback (S.fromSpecStalk (s i))).obj B) :
    Nonempty (A ≅ B) := by
  have key : ∀ {A B : Over S}
      (_ : IsIso ((Over.pullback (complementOfClosedPoints s hs).ι).obj A).hom)
      (e : ∀ i, (Over.pullback (S.fromSpecStalk (s i))).obj A ≅
        (Over.pullback (S.fromSpecStalk (s i))).obj B) (f : A ⟶ B) (g : B ⟶ A)
      (_ : ∀ i, (Over.pullback (S.fromSpecStalk (s i))).map f = (e i).hom)
      (_ : ∀ i, (Over.pullback (S.fromSpecStalk (s i))).map g = (e i).inv), f ≫ g = 𝟙 A := by
    intro A B _ e f g hf hg
    refine over_hom_ext_of_baseChange s hs hqc _ _ ?_
    rintro (_ | i)
    · show (Over.pullback (complementOfClosedPoints s hs).ι).map _ =
        (Over.pullback (complementOfClosedPoints s hs).ι).map _
      exact over_hom_ext_of_isIso ‹_› _ _
    · show (Over.pullback (S.fromSpecStalk (s i))).map _ =
        (Over.pullback (S.fromSpecStalk (s i))).map _
      rw [CategoryTheory.Functor.map_comp, hf, hg, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  obtain ⟨f, hf⟩ := exists_over_hom_of_isIso_complement s hs hinj hqc hB (fun i => (e i).hom)
  obtain ⟨g, hg⟩ := exists_over_hom_of_isIso_complement s hs hinj hqc hA (fun i => (e i).inv)
  exact ⟨⟨f, g, key hA e f g hf hg, key hB (fun i => (e i).symm) g f hg hf⟩⟩

end LocalSchemesCover

/-! ### The normalized blowup away from its centre, after base change -/

/-- Base change along a morphism avoiding the image of the centre does not see the normalized
blowing up of a normal scheme at a closed point. -/
theorem nonempty_pullback_normalizedBlowUp_iso {S C T : Scheme.{u}} (p : C ⟶ S) [IsNormal C]
    (hC : ∀ U : C.Opens, IsCompact (U : Set C) → (irreducibleComponents U).Finite)
    (x : C) (hx : IsClosed ({x} : Set C)) (t : T ⟶ S) (ht : ∀ y, t y ≠ p x) :
    Nonempty ((Over.pullback t).obj (Over.mk (Stacks.Blowup.normalizedBlowUp C hC x hx ≫ p)) ≅
      (Over.pullback t).obj (Over.mk p)) := by
  set ν := Stacks.Blowup.normalizedBlowUp C hC x hx
  have hmiss : ∀ z : ↥(pullback p t),
      pullback.fst p t z ∈ (⟨({x} : Set C)ᶜ, hx.isOpen_compl⟩ : C.Opens) := by
    intro z
    show pullback.fst p t z ∉ ({x} : Set C)
    intro hz
    exact ht (pullback.snd p t z)
      ((pullback_condition_apply p t z).symm.trans (congrArg p (Set.mem_singleton_iff.mp hz)))
  have hiso : IsIso (pullback.snd ν (pullback.fst p t)) :=
    isIso_pullback_snd_of_isIso_morphismRestrict _ _ _
      (isIso_normalizedBlowUp_restrict_compl_singleton hC x hx) hmiss
  refine ⟨Over.isoMk ((pullbackRightPullbackFstIso p t ν).symm ≪≫
    asIso (pullback.snd ν (pullback.fst p t))) ?_⟩
  exact (Category.assoc _ _ _).trans (pullbackRightPullbackFstIso_inv_snd_snd p t ν)

/-- A closed point of the base change of `X` to the spectrum of the local ring at a closed point
`s` lying over the closed point of that spectrum maps to a closed point of `X`. -/
theorem isClosed_singleton_pullbackFst_fromSpecStalk {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (hs : IsClosed ({s} : Set S)) (y : ↥(pullback f (S.fromSpecStalk s)))
    (hy : IsClosed ({y} : Set ↥(pullback f (S.fromSpecStalk s))))
    (hys : pullback.snd f (S.fromSpecStalk s) y = IsLocalRing.closedPoint (S.presheaf.stalk s)) :
    IsClosed ({pullback.fst f (S.fromSpecStalk s) y} : Set X) := by
  set q := pullback.fst f (S.fromSpecStalk s)
  have hqy : f (q y) = s := by
    rw [pullback_condition_apply, hys, Scheme.fromSpecStalk_closedPoint]
  rw [← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm (fun z hz => ?_) subset_closure
  have hyz : q y ⤳ z := specializes_iff_mem_closure.mpr hz
  have hsz : s ⤳ f z := hqy ▸ hyz.map f.continuous
  have hzs : f z = s := Set.mem_singleton_iff.mp
    ((specializes_iff_forall_closed.mp hsz) {s} hs (Set.mem_singleton s))
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f)
    (g := S.fromSpecStalk s) z (IsLocalRing.closedPoint (S.presheaf.stalk s))
    (hzs.trans Scheme.fromSpecStalk_closedPoint.symm)
  have hyw : y ⤳ w := q.isEmbedding.isInducing.specializes_iff.mp (by rw [hw]; exact hyz)
  have hwy : w = y := Set.mem_singleton_iff.mp
    ((specializes_iff_forall_closed.mp hyw) {y} hy (Set.mem_singleton y))
  exact Set.mem_singleton_iff.mpr (hw.symm.trans (congrArg q hwy))

namespace FinitePresentationAwayPointsSituation

variable (D : FinitePresentationAwayPointsSituation.{u})

/-- Two objects of `Over S` which are isomorphisms over the open complement of the distinguished
points are isomorphic as soon as their base changes to the spectra of the local rings at the
distinguished points are. No finite presentation is needed. -/
theorem nonempty_over_iso_of_baseChange {A B : Over D.S}
    (hA : IsIso ((Over.pullback D.complement.ι).obj A).hom)
    (hB : IsIso ((Over.pullback D.complement.ι).obj B).hom)
    (e : ∀ i : Fin D.n, (Over.pullback (D.S.fromSpecStalk (D.points i))).obj A ≅
      (Over.pullback (D.S.fromSpecStalk (D.points i))).obj B) :
    Nonempty (A ≅ B) := by
  let s : ULift.{u} (Fin D.n) → D.S := fun i => D.points i.down
  have hs : ∀ i, s i ∈ closedPoints D.S := fun i =>
    mem_closedPoints_iff.mpr (D.points_closed i.down)
  have hinj : Function.Injective s := fun a b h => ULift.ext _ _ (D.points_injective h)
  have hU : complementOfClosedPoints s hs = D.complement := by
    apply Opens.ext
    apply Set.ext
    intro x
    show x ∈ (⋂ i : ULift.{u} (Fin D.n), ({D.points i.down} : Set D.S)ᶜ) ↔
      x ∈ (Set.range D.points)ᶜ
    simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_range]
    exact ⟨fun h ⟨i, hi⟩ => h ⟨i⟩ hi.symm, fun h i hi => h ⟨i.down, hi.symm⟩⟩
  have hqc : QuasiCompact (complementOfClosedPoints s hs).ι := by
    rw [hU]
    exact D.complement_quasiCompact
  rw [← hU] at hA hB
  exact LocalSchemesCover.nonempty_over_iso_of_isIso_complement s hs hinj hqc hA hB
    (fun i => e i.down)

/-- The spectrum of the local ring at `s j` does not meet `s i` for `j ≠ i`. -/
theorem fromSpecStalk_ne_points {i j : Fin D.n} (hij : j ≠ i) (y : D.localScheme j) :
    D.S.fromSpecStalk (D.points j) y ≠ D.points i := by
  intro hy
  have hr : D.S.fromSpecStalk (D.points j) y ∈ Set.range (D.S.fromSpecStalk (D.points j)) :=
    ⟨y, rfl⟩
  rw [Scheme.range_fromSpecStalk, hy] at hr
  have hmem : D.points j ∈ ({D.points i} : Set D.S) :=
    specializes_iff_forall_closed.mp hr _ (D.points_closed i) (by simp)
  exact hij (D.points_injective (Set.mem_singleton_iff.mp hmem))

/-- One step of the converse of Tag 0BFZ: a normalized blowing up of the localization at `s i`
of a global scheme `C` at a closed point over the closed point is the localization of the
normalized blowing up of `C` at the image of that point. -/
theorem exists_normalizedBlowUp_localization (i : Fin D.n) {C : Scheme.{u}} {p : C ⟶ D.S}
    (hC : ∀ U : C.Opens, IsCompact (U : Set C) → (irreducibleComponents U).Finite)
    {W : Scheme.{u}} {h : W ⟶ D.localScheme i}
    (eC : (Over.pullback (D.S.fromSpecStalk (D.points i))).obj (Over.mk p) ≅ Over.mk h)
    (hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite)
    (w : W) (hw : IsClosed ({w} : Set W))
    (hwc : h w = IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))) :
    ∃ (x : C) (hx : IsClosed ({x} : Set C)), p x = D.points i ∧
      Nonempty ((Over.pullback (D.S.fromSpecStalk (D.points i))).obj
          (Over.mk (Stacks.Blowup.normalizedBlowUp C hC x hx ≫ p)) ≅
        Over.mk (Stacks.Blowup.normalizedBlowUp W hW w hw ≫ h)) := by
  set g := D.S.fromSpecStalk (D.points i)
  set q := pullback.fst p g
  let d : W ⟶ pullback p g := eC.inv.left
  have hd : IsIso d := inferInstanceAs (IsIso ((Over.forget _).map eC.inv))
  have hdh : d ≫ pullback.snd p g = h := Over.w eC.inv
  obtain ⟨y, hyd⟩ : ∃ y, y = d w := ⟨_, rfl⟩
  have hy : IsClosed ({y} : Set ↥(pullback p g)) := by
    have hset : ({y} : Set ↥(pullback p g)) = (inv d) ⁻¹' ({w} : Set W) := by
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl
        rw [hyd]
        show (d ≫ inv d) w = w
        rw [IsIso.hom_inv_id]
        rfl
      · intro hz
        rw [hyd, ← hz]
        show z = (inv d ≫ d) z
        rw [IsIso.inv_hom_id]
        rfl
    rw [hset]
    exact hw.preimage (inv d).continuous
  have hys : pullback.snd p g y = IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i)) := by
    rw [← hwc, ← hdh, hyd]
    rfl
  set x := q y
  have hx : IsClosed ({x} : Set C) :=
    isClosed_singleton_pullbackFst_fromSpecStalk p (D.points i) (D.points_closed i) y hy hys
  have hpx : p x = D.points i := by
    show p (q y) = _
    rw [pullback_condition_apply, hys, Scheme.fromSpecStalk_closedPoint]
  obtain ⟨hy', hideal⟩ := vanishingIdeal_singleton_comap_pullbackFst p g x hx
    (pointToSpecStalk p x hpx) (pointToSpecStalk_comp_fromSpecStalk p x hpx) y rfl
  have hL := finite_irreducibleComponents_pullbackFst_fromSpecStalk p (D.points i) hC
  have : Flat q := flat_pullbackFst_fromSpecStalk p (D.points i)
  obtain ⟨m₁, hm₁⟩ := exists_isPullback_normalizedBlowUp_comap q hC hL x hx y hy' hideal
  obtain ⟨hw', hideal'⟩ := vanishingIdeal_singleton_comap_of_isIso d y hy' w hyd.symm
  obtain ⟨m₂, hm₂⟩ := exists_isPullback_normalizedBlowUp_comap d hL hW y hy' w hw' hideal'
  have hbot : IsPullback (d ≫ q) h p g := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ (asIso d) rfl hdh
    rw [Category.assoc, pullback.condition, ← Category.assoc, hdh]
  have htot := (hm₂.paste_horiz hm₁).paste_vert hbot
  refine ⟨x, hx, hpx, ⟨Over.isoMk htot.isoPullback.symm ?_⟩⟩
  exact htot.isoPullback_inv_snd

/-- The converse of Tag 0BFZ at one distinguished point: a sequence of normalized blowups of
`Spec 𝒪_{S, s i}` at closed points over the closed point lifts to a sequence of normalized
blowups of a global sequence `A` whose localization at `s i` is trivial, without changing `A`
at the other distinguished points or over the open complement. -/
theorem exists_normalizedPointBlowupChain_lift [IsNormal D.S]
    (hS : ∀ U : D.S.Opens, IsCompact (U : Set D.S) → (irreducibleComponents U).Finite)
    (i : Fin D.n) {A : Scheme.{u}} {pA : A ⟶ D.S}
    (hA : NormalizedPointBlowupChain D.S (Set.range D.points) A pA)
    (eA : (Over.pullback (D.S.fromSpecStalk (D.points i))).obj (Over.mk pA) ≅
      Over.mk (𝟙 (D.localScheme i)))
    {Z : Scheme.{u}} {q : Z ⟶ D.localScheme i}
    (hZ : NormalizedPointBlowupChain (D.localScheme i)
      {IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))} Z q) :
    ∃ (C : Scheme.{u}) (pC : C ⟶ D.S), NormalizedPointBlowupChain D.S (Set.range D.points) C pC ∧
      Nonempty ((Over.pullback (D.S.fromSpecStalk (D.points i))).obj (Over.mk pC) ≅
        Over.mk q) ∧
      (∀ j, j ≠ i → Nonempty ((Over.pullback (D.S.fromSpecStalk (D.points j))).obj (Over.mk pC) ≅
        (Over.pullback (D.S.fromSpecStalk (D.points j))).obj (Over.mk pA))) ∧
      Nonempty ((Over.pullback D.complement.ι).obj (Over.mk pC) ≅
        (Over.pullback D.complement.ι).obj (Over.mk pA)) := by
  induction hZ with
  | refl => exact ⟨A, pA, hA, ⟨eA⟩, fun _ _ => ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩
  | @step W h hh hW w hw hwT ih =>
    obtain ⟨C, pC, hC, ⟨eC⟩, hoth, ⟨eU⟩⟩ := ih
    have hCf := hC.finite_irreducibleComponents hS
    have : IsNormal C := hC.isNormal
    obtain ⟨x, hx, hpx, ⟨e'⟩⟩ := D.exists_normalizedBlowUp_localization i hCf eC hW w hw
      (Set.mem_singleton_iff.mp hwT)
    refine ⟨_, _, hC.step hCf x hx ⟨i, hpx.symm⟩, ⟨e'⟩, fun j hji => ?_, ?_⟩
    · obtain ⟨e₁⟩ := nonempty_pullback_normalizedBlowUp_iso pC hCf x hx
        (D.S.fromSpecStalk (D.points j))
        (fun y => by rw [hpx]; exact D.fromSpecStalk_ne_points hji y)
      exact ⟨e₁ ≪≫ (hoth j hji).some⟩
    · obtain ⟨e₁⟩ := nonempty_pullback_normalizedBlowUp_iso pC hCf x hx D.complement.ι
        (fun y => by
          rw [hpx]
          intro hy
          exact y.2 ⟨i, hy.symm⟩)
      exact ⟨e₁ ≪≫ eU⟩

/-- The converse of Tag 0BFZ before the comparison: sequences of normalized blowups of the
`Spec 𝒪_{S, s i}` at closed points over the closed points are the localizations of one sequence
of normalized blowups of `S` at closed points over the distinguished points, which is an
isomorphism over the open complement. -/
theorem exists_normalizedPointBlowupChain_of_local [IsNormal D.S]
    (hS : ∀ U : D.S.Opens, IsCompact (U : Set D.S) → (irreducibleComponents U).Finite)
    (Z : Fin D.n → Scheme.{u}) (q : ∀ i, Z i ⟶ D.localScheme i)
    (hZ : ∀ i, NormalizedPointBlowupChain (D.localScheme i)
      {IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))} (Z i) (q i)) :
    ∃ (A : Scheme.{u}) (pA : A ⟶ D.S), NormalizedPointBlowupChain D.S (Set.range D.points) A pA ∧
      (∀ i, Nonempty ((Over.pullback (D.S.fromSpecStalk (D.points i))).obj (Over.mk pA) ≅
        Over.mk (q i))) ∧
      IsIso ((Over.pullback D.complement.ι).obj (Over.mk pA)).hom := by
  classical
  have build : ∀ t : Finset (Fin D.n), ∃ (A : Scheme.{u}) (pA : A ⟶ D.S),
      NormalizedPointBlowupChain D.S (Set.range D.points) A pA ∧
      (∀ i ∈ t, Nonempty ((Over.pullback (D.S.fromSpecStalk (D.points i))).obj (Over.mk pA) ≅
        Over.mk (q i))) ∧
      (∀ i ∉ t, Nonempty ((Over.pullback (D.S.fromSpecStalk (D.points i))).obj (Over.mk pA) ≅
        Over.mk (𝟙 (D.localScheme i)))) ∧
      IsIso ((Over.pullback D.complement.ι).obj (Over.mk pA)).hom := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      refine ⟨D.S, 𝟙 D.S, .refl, by simp, fun i _ => ⟨Over.isoMk
        (asIso (pullback.snd (𝟙 D.S) (D.S.fromSpecStalk (D.points i)))) (by simp)⟩, ?_⟩
      exact (IsPullback.of_hasPullback (𝟙 D.S) D.complement.ι).isIso_snd_of_isIso
    | @insert i t hi ih =>
      obtain ⟨A, pA, hA, hdone, htodo, hAU⟩ := ih
      obtain ⟨B, pB, hB, ⟨eB⟩, hoth, ⟨eBU⟩⟩ :=
        D.exists_normalizedPointBlowupChain_lift hS i hA (htodo i hi).some (hZ i)
      refine ⟨B, pB, hB, fun j hj => ?_, fun j hj => ?_, ?_⟩
      · rcases Finset.mem_insert.mp hj with rfl | hj
        · exact ⟨eB⟩
        · exact ⟨(hoth j (fun h => hi (h ▸ hj))).some ≪≫ (hdone j hj).some⟩
      · exact ⟨(hoth j (fun h => hj (h ▸ Finset.mem_insert_self _ _))).some ≪≫
          (htodo j (fun h => hj (Finset.mem_insert_of_mem h))).some⟩
      · have : IsIso eBU.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eBU.hom))
        rw [← Over.w eBU.hom]
        infer_instance
  obtain ⟨A, pA, hA, hdone, -, hAU⟩ := build Finset.univ
  exact ⟨A, pA, hA, fun i => hdone i (Finset.mem_univ _), hAU⟩

/-- **Stacks Project, Tag 0BFZ**, for a normal base. Let `S, s i, S_i` be as in Tag 0BFU, with
`S` normal and every quasi-compact open of `S` having finitely many irreducible components, and
let `f : X ⟶ S` correspond to the `g i : Y i ⟶ S_i` under the base-change functor. Then `f` is a
finite sequence of normalized blowups at closed points lying over the distinguished points if and
only if, for each `i`, `g i` is a finite sequence of normalized blowups at closed points lying
over the closed point of `S_i`.

Normality is necessary: `AlgebraicGeometry.not_factorsAsNormalizedPointBlowups_iff` exhibits a
scheme satisfying the remaining hypotheses for which the equivalence fails. -/
@[stacks 0BFZ "corrected: S normal added, the statement being false without it; both directions"]
theorem factorsAsNormalizedPointBlowups_iff [IsNormal D.S]
    (hS : ∀ U : D.S.Opens, IsCompact (U : Set D.S) → (irreducibleComponents U).Finite)
    (BC : BaseChangeFunctor D) (X : D.globalCategory) (Y : ∀ i, D.localCategory i)
    (hY : ∀ i, BC.functor.obj X i ≅ Y i) :
    FactorsAsNormalizedPointBlowups D.S (Set.range D.points) X.obj.left X.obj.hom ↔
      ∀ i, FactorsAsNormalizedPointBlowups (D.localScheme i)
        {IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))} (Y i).obj.left
        (Y i).obj.hom := by
  refine ⟨fun h i => D.factorsAsNormalizedPointBlowups_of_corresponds BC X i (Y i) (hY i) h,
    fun h => ?_⟩
  choose Z q hZ e he using h
  obtain ⟨A, pA, hA, hloc, hAU⟩ := D.exists_normalizedPointBlowupChain_of_local hS Z q hZ
  obtain ⟨E⟩ := D.nonempty_over_iso_of_baseChange hAU X.property.2 (fun i =>
    (hloc i).some ≪≫ (Over.isoMk (e i) (he i)).symm ≪≫
      ((ObjectProperty.ι (IsFinitePresentationAway (D.puncturedLocalScheme i))).mapIso
        (hY i)).symm ≪≫ (BC.pullbackIso i).app X)
  exact factorsAsNormalizedPointBlowups_of_overIso E.symm ⟨A, pA, hA, Iso.refl _, by simp⟩

end FinitePresentationAwayPointsSituation

/-! ### A counterexample without normality -/

section Counterexample

variable (K A : Type u) [Field K] [CommRing A] [Finite (PrimeSpectrum A)]

/-- The point of `Spec K` as a point of `Spec K ⨿ Spec A`. -/
def inlPoint : ↥(Spec (.of K) ⨿ Spec (.of A)) :=
  (coprod.inl : Spec (.of K) ⟶ Spec (.of K) ⨿ Spec (.of A))
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)

omit [Finite (PrimeSpectrum A)] in
/-- The point of `Spec K` is the only point of `Spec K ⨿ Spec A` coming from `Spec K`. -/
theorem range_inl_eq_singleton_inlPoint :
    Set.range (coprod.inl : Spec (.of K) ⟶ Spec (.of K) ⨿ Spec (.of A)) = {inlPoint K A} := by
  have : Subsingleton (Spec (.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact congrArg _ (Subsingleton.elim _ _)
  · rintro rfl
    exact ⟨_, rfl⟩

omit [Finite (PrimeSpectrum A)] in
/-- The point of `Spec K` is isolated in `Spec K ⨿ Spec A`. -/
theorem isOpen_singleton_inlPoint : IsOpen ({inlPoint K A} : Set ↥(Spec (.of K) ⨿ Spec (.of A))) :=
  range_inl_eq_singleton_inlPoint K A ▸ (coprod.inl : Spec (.of K) ⟶ _).isOpenEmbedding.isOpen_range

omit [Finite (PrimeSpectrum A)] in
/-- The complement of the point of `Spec K` in `Spec K ⨿ Spec A` is the image of `Spec A`. -/
theorem compl_singleton_inlPoint :
    ({inlPoint K A} : Set ↥(Spec (.of K) ⨿ Spec (.of A)))ᶜ =
      Set.range (coprod.inr : Spec (.of A) ⟶ Spec (.of K) ⨿ Spec (.of A)) := by
  rw [← range_inl_eq_singleton_inlPoint]
  exact (isCompl_range_inl_inr _ _).compl_eq

omit [Finite (PrimeSpectrum A)] in
/-- The point of `Spec K` is closed in `Spec K ⨿ Spec A`. -/
theorem isClosed_singleton_inlPoint :
    IsClosed ({inlPoint K A} : Set ↥(Spec (.of K) ⨿ Spec (.of A))) := by
  rw [← isOpen_compl_iff, compl_singleton_inlPoint]
  exact (coprod.inr : Spec (.of A) ⟶ _).isOpenEmbedding.isOpen_range

/-- `Spec K ⨿ Spec A` has finitely many points when `Spec A` has. -/
instance finite_coprod_spec : Finite ↥(Spec (.of K) ⨿ Spec (.of A)) := by
  have : Finite (Spec (.of K)) := inferInstanceAs (Finite (PrimeSpectrum K))
  have : Finite (Spec (.of A)) := inferInstanceAs (Finite (PrimeSpectrum A))
  have h := (isCompl_range_inl_inr (Spec (.of K)) (Spec (.of A))).sup_eq_top
  refine Set.finite_univ_iff.mp ?_
  rw [← Set.top_eq_univ, ← h]
  exact (Set.finite_range _).union (Set.finite_range _)

/-- The open complement of the point of `Spec K` in `Spec K ⨿ Spec A`, in the form of Tag 0BFU. -/
abbrev inlComplement : (Spec (.of K) ⨿ Spec (.of A)).Opens :=
  rangeComplementOfClosedPoints (fun _ : Fin 1 => inlPoint K A)
    (fun _ => isClosed_singleton_inlPoint K A)

omit [Finite (PrimeSpectrum A)] in
/-- The open complement of the point of `Spec K` is the image of `Spec A`. -/
theorem coe_inlComplement :
    (inlComplement K A : Set ↥(Spec (.of K) ⨿ Spec (.of A))) =
      Set.range (coprod.inr : Spec (.of A) ⟶ Spec (.of K) ⨿ Spec (.of A)) := by
  rw [← compl_singleton_inlPoint]
  show (Set.range fun _ : Fin 1 => inlPoint K A)ᶜ = _
  rw [Set.range_const]

omit [Finite (PrimeSpectrum A)] in
/-- If `A` is not reduced, the open complement of the point of `Spec K` in `Spec K ⨿ Spec A`,
which is `Spec A`, is not normal. -/
theorem not_isNormal_inlComplement (hA : ¬ _root_.IsReduced A) :
    ¬ IsNormal (inlComplement K A).toScheme := by
  intro h
  let e : Spec (.of A) ≅ (inlComplement K A).toScheme :=
    IsOpenImmersion.isoOfRangeEq coprod.inr (inlComplement K A).ι
      (by rw [Scheme.Opens.range_ι, coe_inlComplement])
  have : IsNormal (Spec (.of A)) := isNormal_of_iso e
  exact hA ((affine_isReduced_iff (.of A)).mp inferInstance)

/-- The scheme `Spec K ⨿ Spec A` with the single distinguished point of `Spec K`. -/
def coprodSpecSituation : FinitePresentationAwayPointsSituation.{u} where
  S := Spec (.of K) ⨿ Spec (.of A)
  n := 1
  points := fun _ => inlPoint K A
  points_injective := fun a b _ => Subsingleton.elim a b
  points_closed := fun _ => isClosed_singleton_inlPoint K A
  complement_quasiCompact := by
    refine ⟨fun U _ _ => ?_⟩
    have : Finite ↥(inlComplement K A).toScheme :=
      Finite.of_injective _ (inlComplement K A).ι.isOpenEmbedding.injective
    exact (Set.toFinite _).isCompact

end Counterexample

/-- **Tag 0BFZ is false without normality.** The assertion of [Stacks, Tag 0BFZ] under exactly
its hypotheses — `S, s i, S_i` as in Tag 0BFU, every quasi-compact open of `S` with finitely many
irreducible components, `f : X ⟶ S` corresponding to the `g i : Y i ⟶ S_i` — fails: for
`S = Spec 𝔽₂ ⨿ Spec ℤ/4` with the point of `Spec 𝔽₂` distinguished, the open immersion of
`Spec ℤ/4` is an object of Tag 0BFU's category whose localization, the empty scheme, is the
normalized blowing up of the one-point local scheme at its point, while it is itself no sequence
of normalized blowups, every such sequence of positive length having normal source. The corrected
statement is `FinitePresentationAwayPointsSituation.factorsAsNormalizedPointBlowups_iff`. -/
theorem not_factorsAsNormalizedPointBlowups_iff :
    ¬ ∀ (D : FinitePresentationAwayPointsSituation.{u}) (BC : BaseChangeFunctor D)
      (X : D.globalCategory) (Y : ∀ i, D.localCategory i) (_ : ∀ i, BC.functor.obj X i ≅ Y i),
      (∀ U : D.S.Opens, IsCompact (U : Set D.S) → (irreducibleComponents U).Finite) →
      (FactorsAsNormalizedPointBlowups D.S (Set.range D.points) X.obj.left X.obj.hom ↔
        ∀ i, FactorsAsNormalizedPointBlowups (D.localScheme i)
          {IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))} (Y i).obj.left
          (Y i).obj.hom) := by
  intro h
  have : Finite (PrimeSpectrum (ULift.{u} (ZMod 4))) :=
    Finite.of_injective (fun p : PrimeSpectrum (ULift.{u} (ZMod 4)) =>
      (p.asIdeal : Set (ULift.{u} (ZMod 4))))
      (fun p q hpq => PrimeSpectrum.ext (SetLike.coe_injective hpq))
  have hA : ¬ _root_.IsReduced (ULift.{u} (ZMod 4)) := by
    intro hred
    have h2 : (⟨2⟩ : ULift.{u} (ZMod 4)) = 0 :=
      hred.eq_zero _ ⟨2, ULift.down_injective (by decide)⟩
    exact absurd (congrArg ULift.down h2) (by decide)
  have hfin : Finite ↥(coprodSpecSituation (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 4))).S :=
    finite_coprod_spec _ _
  have hopen : ∀ i, IsOpen ({(coprodSpecSituation (ULift.{u} (ZMod 2))
      (ULift.{u} (ZMod 4))).points i} : Set ↥(coprodSpecSituation (ULift.{u} (ZMod 2))
        (ULift.{u} (ZMod 4))).S) :=
    fun _ => isOpen_singleton_inlPoint _ _
  have hS : ∀ U : (coprodSpecSituation (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 4))).S.Opens,
      IsCompact (U : Set ↥(coprodSpecSituation (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 4))).S) →
        (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_of_finite
  exact FinitePresentationAwayPointsSituation.not_factorsAsNormalizedPointBlowups_complementObject
    (coprodSpecSituation (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 4))) Nat.one_pos hopen
    (not_isNormal_inlComplement _ _ hA)
    ((h _ (finitePresentationAwayPointsBaseChange _) _ _ (fun i => Iso.refl _) hS).mpr
      (fun i => FinitePresentationAwayPointsSituation.factorsAsNormalizedPointBlowups_of_isOpen
        _ _ (hopen i) _ (Iso.refl _)))

end AlgebraicGeometry

end
