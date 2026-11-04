module

public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.BaseChangeEquivalence
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.Fibre
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain
public import StacksCore.Tactic.StacksAttribute

/-!
# Localizing a sequence of blowups at closed points

Let `S` be a scheme and `s` an injective family of closed points of `S`. A morphism to `S` which
factors as a finite sequence of blowups at closed points lying over the `s j` stays such a
sequence after base change to the spectrum of the local ring at `s i`: a step whose centre lies
over `s i` becomes the blowup at the unique point above that centre, and a step whose centre
lies over another `s j` becomes an isomorphism, the centre having empty inverse image.

## Main definitions

* `Stacks.ResolutionOfSurfaces.FactorsAsPointBlowups` says that a morphism is, up to an
  isomorphism of its source, the composite of a `PointBlowupChain`. Unlike `PointBlowupChain`,
  which names the blown-up schemes themselves, this is invariant under isomorphism.
* `AlgebraicGeometry.pointToSpecStalk` is the canonical morphism from the spectrum of the
  residue field at a point of a scheme over `S` to the spectrum of the local ring of `S` at its
  image.

## Main results

* `AlgebraicGeometry.vanishingIdeal_singleton_comap` computes the inverse image of the ideal
  sheaf of a reduced closed point along an injective morphism that does not change the point's
  reduced closed subscheme: it is the ideal sheaf of the unique point above it.
  `AlgebraicGeometry.vanishingIdeal_singleton_comap_pullbackFst` is its case of a base change
  along a monomorphic preimmersion, which is the one that occurs here.
* `AlgebraicGeometry.isIso_blowUpToBase_of_support_eq_empty`: blowing up in an ideal with empty
  support does nothing.
* `Stacks.ResolutionOfSurfaces.FactorsAsPointBlowups.step` extends a factorization by the blowup
  at a closed point lying over the given set.
* `AlgebraicGeometry.factorsAsPointBlowups_pullback_fromSpecStalk` is one direction of Stacks
  Tag 0BFY: a sequence of blowups at closed points over the distinguished points localizes to a
  sequence of blowups at closed points over the closed point of `Spec 𝒪_{S, s i}`. The variant
  `AlgebraicGeometry.factorsAsPointBlowups_pullback_fromSpecStalk_of_factorsAsPointBlowups`
  assumes only that the morphism factors as such a sequence, and
  `AlgebraicGeometry.FinitePresentationAwayPointsSituation.factorsAsPointBlowups_of_corresponds`
  restates that for the local modifications corresponding to a global one under a base-change
  functor of Tag 0BFU.
* `AlgebraicGeometry.FinitePresentationAwayPointsSituation.factorsAsPointBlowups_of_baseChange_iso`
  is the step of the converse direction supplied by Tag 0BFV: granted the glueing theorem of Tag
  0E8Q, a global modification whose localizations agree with those of a sequence of blowups at
  closed points over the distinguished points is itself such a sequence.

## Implementation notes

`PointBlowupChain` is an inductive family indexed by the blown-up scheme, so the scheme produced
by a step is literally a `blowUp`, whereas a base change is only isomorphic to such a scheme.
`FactorsAsPointBlowups` adds that isomorphism, and `FactorsAsPointBlowups.step` absorbs the
comparison once, by flat base change along an isomorphism, so the induction that localizes a
chain never transports a chain along an isomorphism again.

Only the stated direction of Tag 0BFY is proved here, and the file therefore does not carry the
tag. The converse direction needs that the base-change functor of Tag 0BFU is an equivalence,
which is Tag 0BFV; that is available only under the glueing theorem of Tag 0E8Q, as
`AlgebraicGeometry.BaseChangeFunctor.isEquivalence`, and is what lets a global object be
recovered from its localizations. What remains for the converse is the construction of that
global object: from factorizations of the local modifications one must build a sequence of
blowups over `S`, blowing up at the closed points over `s i` that the fibre comparison of Tag
0BFX matches with the centres of the local sequences.

## References

* [Stacks Project, Tag 0BFY](https://stacks.math.columbia.edu/tag/0BFY)
* [Stacks Project, Tag 0BFU](https://stacks.math.columbia.edu/tag/0BFU)
* [Stacks Project, Tag 0BFV](https://stacks.math.columbia.edu/tag/0BFV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

/-- A morphism `p : Z ⟶ X` factors as a finite sequence of blowups at closed points lying over
`T ⊆ X` if some `PointBlowupChain` over `T` has source isomorphic to `Z` over `X`. -/
def FactorsAsPointBlowups (X : Scheme.{u}) (T : Set X) (Z : Scheme.{u}) (p : Z ⟶ X) : Prop :=
  ∃ (Y : Scheme.{u}) (f : Y ⟶ X), PointBlowupChain X T Y f ∧ ∃ e : Z ≅ Y, e.hom ≫ f = p

/-- The identity factors as the empty sequence of blowups. -/
theorem FactorsAsPointBlowups.refl {X : Scheme.{u}} (T : Set X) :
    FactorsAsPointBlowups X T X (𝟙 X) :=
  ⟨X, 𝟙 X, PointBlowupChain.refl, Iso.refl X, by simp⟩

/-- Factoring as a sequence of blowups is invariant under precomposition with an isomorphism. -/
theorem FactorsAsPointBlowups.of_iso {X : Scheme.{u}} {T : Set X} {Z Z' : Scheme.{u}}
    {p : Z ⟶ X} (h : FactorsAsPointBlowups X T Z p) (e : Z' ≅ Z) :
    FactorsAsPointBlowups X T Z' (e.hom ≫ p) := by
  obtain ⟨Y, f, hchain, d, hd⟩ := h
  exact ⟨Y, f, hchain, e ≪≫ d, by rw [Iso.trans_hom, Category.assoc, hd]⟩

/-- Factoring as a sequence of blowups depends only on the morphism. -/
theorem FactorsAsPointBlowups.congr {X : Scheme.{u}} {T : Set X} {Z : Scheme.{u}}
    {p p' : Z ⟶ X} (h : FactorsAsPointBlowups X T Z p) (hp : p = p') :
    FactorsAsPointBlowups X T Z p' := hp ▸ h

end Stacks.ResolutionOfSurfaces

namespace AlgebraicGeometry

open Stacks.ResolutionOfSurfaces

/-! ### The ideal sheaf of a reduced closed point under base change -/

/-- Factor the inclusion of the reduced closed subscheme at a point through a morphism through
which the residue-field point factors. -/
theorem exists_factor_subschemeι_vanishingIdeal_singleton {P W : Scheme.{u}} (q : P ⟶ W) (w : W)
    (hw : IsClosed ({w} : Set W)) (c : Spec (W.residueField w) ⟶ P)
    (hc : c ≫ q = W.fromSpecResidueField w) :
    let I := Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)
    ∃ m : I.subscheme ⟶ P, m ≫ q = I.subschemeι := by
  intro I
  have hci : IsClosedImmersion (W.fromSpecResidueField w) :=
    isClosed_singleton_iff_isClosedImmersion.mp hw
  rw [show I = (W.fromSpecResidueField w).ker from vanishingIdeal_singleton_eq_ker w hw]
  refine ⟨inv (W.fromSpecResidueField w).toImage ≫ c, ?_⟩
  change (inv (W.fromSpecResidueField w).toImage ≫ c) ≫ q =
    (W.fromSpecResidueField w).imageι
  rw [Category.assoc, hc, IsIso.inv_comp_eq]
  exact (W.fromSpecResidueField w).toImage_imageι.symm

/-- The support of the inverse image of the ideal sheaf of a reduced closed point `w` is the
preimage of `w`. -/
private theorem coe_support_comap_vanishingIdeal_singleton {P W : Scheme.{u}} (q : P ⟶ W) (w : W)
    (hw : IsClosed ({w} : Set W)) :
    (((Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).comap q).support : Set P) =
      q ⁻¹' {w} := by
  rw [Scheme.IdealSheafData.support_comap]
  exact congrArg (q ⁻¹' ·) (Scheme.IdealSheafData.coe_support_vanishingIdeal _)

/-- The inverse image of the ideal sheaf of a reduced closed point `w` along an injective
morphism `q` is the ideal sheaf of the unique point above `w`, provided the inverse image of the
reduced closed subscheme at `w` is unchanged, which is what the isomorphism hypothesis says. -/
theorem vanishingIdeal_singleton_comap {P W : Scheme.{u}} (q : P ⟶ W) (w : W)
    (hw : IsClosed ({w} : Set W)) (hinj : Function.Injective q.base)
    (hiso : IsIso (pullback.snd q
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).subschemeι))
    (z : P) (hzw : q z = w) :
    ∃ hz : IsClosed ({z} : Set P),
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).comap q =
        Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds P) := by
  have hpre : q ⁻¹' ({w} : Set W) = {z} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => hinj (h.trans hzw.symm), fun h => h ▸ hzw⟩
  have hz : IsClosed ({z} : Set P) := hpre ▸ hw.preimage q.continuous
  refine ⟨hz, ?_⟩
  have hsupp : ((Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).comap q).support =
      (⟨{z}, hz⟩ : Closeds P) := by
    apply SetLike.coe_injective
    rw [coe_support_comap_vanishingIdeal_singleton, hpre]
    rfl
  have : IsReduced (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have : IsReduced (pullback q
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).subschemeι) :=
    isReduced_of_isOpenImmersion (pullback.snd _ _)
  have : IsReduced ((Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).comap
      q).subscheme :=
    isReduced_of_isOpenImmersion
      ((Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).comapIso q).hom
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ hsupp

/-- The inverse image of the ideal sheaf of a reduced closed point along an isomorphism is the
ideal sheaf of the corresponding point. -/
theorem vanishingIdeal_singleton_comap_of_isIso {P W : Scheme.{u}} (q : P ⟶ W) [IsIso q] (w : W)
    (hw : IsClosed ({w} : Set W)) (z : P) (hzw : q z = w) :
    ∃ hz : IsClosed ({z} : Set P),
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).comap q =
        Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds P) :=
  vanishingIdeal_singleton_comap q w hw q.isEmbedding.injective inferInstance z hzw

/-- The inverse image of the ideal sheaf of a reduced closed point `w` of `W` along the
projection `W ×_S L ⟶ W` is the ideal sheaf of the unique point above `w`, for `g : L ⟶ S` a
monomorphic preimmersion through which the residue-field point of `w` factors. -/
theorem vanishingIdeal_singleton_comap_pullbackFst {S W L : Scheme.{u}} (p : W ⟶ S) (g : L ⟶ S)
    [Mono g] [IsPreimmersion g] (w : W) (hw : IsClosed ({w} : Set W))
    (k : Spec (W.residueField w) ⟶ L) (hk : k ≫ g = W.fromSpecResidueField w ≫ p)
    (z : ↥(pullback p g)) (hzw : pullback.fst p g z = w) :
    ∃ hz : IsClosed ({z} : Set ↥(pullback p g)),
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).comap
          (pullback.fst p g) =
        Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds ↥(pullback p g)) := by
  obtain ⟨m, hm⟩ := exists_factor_subschemeι_vanishingIdeal_singleton (pullback.fst p g) w hw
    (pullback.lift (W.fromSpecResidueField w) k hk.symm) (pullback.lift_fst _ _ _)
  exact vanishingIdeal_singleton_comap (pullback.fst p g) w hw
    (pullback.fst p g).isEmbedding.injective
    (isIso_pullback_snd_of_factorization _ _ m hm) z hzw

/-! ### Blowing up in an ideal with empty support -/

/-- Blowing up in an ideal sheaf with empty support changes nothing. -/
theorem isIso_blowUpToBase_of_support_eq_empty {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : (I.support : Set X) = ∅) : IsIso (blowUpToBase I) := by
  have hU : (⟨(I.support : Set X)ᶜ, I.support.isClosed.isOpen_compl⟩ : X.Opens) = ⊤ := by
    apply TopologicalSpace.Opens.ext
    ext y
    simp [hI]
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme)
    (f := blowUpToBase I)
    (fun _ : Unit => (⟨(I.support : Set X)ᶜ, I.support.isClosed.isOpen_compl⟩ : X.Opens))
    (by simpa using hU)).2 (fun _ => ?_)
  change IsIso (blowUpToBase I ∣_ _)
  exact isIso_blowUp_restrict_compl_support I

/-! ### Extending a factorization by one blowup -/

/-- Base change of a blowup along an isomorphism: the blowup in the inverse image of an ideal
along an isomorphism is the blowup in the ideal. -/
theorem exists_blowUp_iso_comap_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (I : Y.IdealSheafData) :
    ∃ d : blowUp (I.comap f) ≅ blowUp I,
      d.hom ≫ blowUpToBase I = blowUpToBase (I.comap f) ≫ f := by
  obtain ⟨h, hh⟩ := exists_isPullback_blowUpToBase_comap f I
  have : IsIso h := by
    rw [← hh.isoPullback_hom_snd]
    infer_instance
  exact ⟨asIso h, hh.w.symm⟩

/-- Transport of the factorization property along an equality of the blown-up ideal. -/
theorem factorsAsPointBlowups_blowUp_congr {X P : Scheme.{u}} {T : Set X}
    {I J : P.IdealSheafData} (h : I = J) {r : P ⟶ X}
    (hs : FactorsAsPointBlowups X T (blowUp J) (blowUpToBase J ≫ r)) :
    FactorsAsPointBlowups X T (blowUp I) (blowUpToBase I ≫ r) := by
  subst h
  exact hs

end AlgebraicGeometry

namespace Stacks.ResolutionOfSurfaces

/-- Blowing up a closed point lying over `T` extends a factorization as a sequence of blowups:
the blowup at the point is identified with the blowup at its image in the chain by flat base
change along the isomorphism. -/
theorem FactorsAsPointBlowups.step {X : Scheme.{u}} {T : Set X} {Z : Scheme.{u}} {p : Z ⟶ X}
    (h : FactorsAsPointBlowups X T Z p) (z : Z) (hz : IsClosed ({z} : Set Z))
    (hzT : p z ∈ T) :
    FactorsAsPointBlowups X T
      (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds Z)))
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds Z)) ≫ p) := by
  obtain ⟨Y, f, hchain, e, he⟩ := h
  have hz' : IsClosed ({e.hom z} : Set Y) := by
    have hset : ({e.hom z} : Set Y) = e.inv ⁻¹' ({z} : Set Z) := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun hy => by simp [hy], fun hy => by simp [← hy]⟩
    rw [hset]
    exact hz.preimage e.inv.continuous
  have hfz : f (e.hom z) ∈ T := by
    have hpz : f (e.hom z) = p z := by simpa using congrArg (fun k : Z ⟶ X => k.base z) he
    rwa [hpz]
  obtain ⟨hz'', hideal⟩ :=
    AlgebraicGeometry.vanishingIdeal_singleton_comap_of_isIso e.hom (e.hom z) hz' z rfl
  refine AlgebraicGeometry.factorsAsPointBlowups_blowUp_congr (r := p) hideal.symm ?_
  obtain ⟨d, hd⟩ := AlgebraicGeometry.exists_blowUp_iso_comap_of_isIso e.hom
    (Scheme.IdealSheafData.vanishingIdeal (⟨{e.hom z}, hz'⟩ : Closeds Y))
  refine ⟨_, _, hchain.step (e.hom z) hz' hfz, d, ?_⟩
  rw [← Category.assoc, hd, Category.assoc, he]

end Stacks.ResolutionOfSurfaces

namespace AlgebraicGeometry

open Stacks.ResolutionOfSurfaces

/-! ### The residue field of a point as a point of the local scheme of the base -/

/-- For a point `x` of a scheme over `S` lying over `s`, the canonical morphism from the spectrum
of the residue field at `x` to the spectrum of the local ring of `S` at `s`. -/
def pointToSpecStalk {S X : Scheme.{u}} (f : X ⟶ S) {s : S} (x : X) (hxs : f x = s) :
    Spec (X.residueField x) ⟶ Spec (S.presheaf.stalk s) :=
  Spec.map (S.residue s ≫ (S.residueFieldCongr hxs).inv ≫ f.residueFieldMap x)

/-- The morphism to the local scheme of the base refines the residue-field point of `x`. -/
theorem pointToSpecStalk_comp_fromSpecStalk {S X : Scheme.{u}} (f : X ⟶ S) {s : S} (x : X)
    (hxs : f x = s) :
    pointToSpecStalk f x hxs ≫ S.fromSpecStalk s = X.fromSpecResidueField x ≫ f := by
  calc pointToSpecStalk f x hxs ≫ S.fromSpecStalk s =
        Spec.map (f.residueFieldMap x) ≫
          Spec.map (S.residueFieldCongr hxs).inv ≫ S.fromSpecResidueField s := by
        simp [pointToSpecStalk, Scheme.fromSpecResidueField, Spec.map_comp, Category.assoc]
    _ = Spec.map (f.residueFieldMap x) ≫ S.fromSpecResidueField (f x) := by simp
    _ = X.fromSpecResidueField x ≫ f :=
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x

/-! ### Localizing a sequence of blowups -/

/-- A point of the base change of `W ⟶ S` to `Spec 𝒪_{S, s}` does not map to a point of `W`
lying over a closed point `t ≠ s`. -/
private theorem pullback_fst_fromSpecStalk_ne {S W : Scheme.{u}} (pW : W ⟶ S) {s t : S}
    (ht : IsClosed ({t} : Set S)) (hst : s ≠ t) {w : W} (hw : pW w = t)
    (y : ↥(pullback pW (S.fromSpecStalk s))) : pullback.fst pW (S.fromSpecStalk s) y ≠ w := by
  intro hy
  have hcond : pW (pullback.fst pW (S.fromSpecStalk s) y) =
      (S.fromSpecStalk s) (pullback.snd pW (S.fromSpecStalk s) y) :=
    congrArg (fun m : (pullback pW (S.fromSpecStalk s) ⟶ S) => m.base y)
      (pullback.condition (f := pW) (g := S.fromSpecStalk s))
  have hrange : t ∈ Set.range (S.fromSpecStalk s) := by
    refine ⟨pullback.snd pW (S.fromSpecStalk s) y, ?_⟩
    rw [← hcond, hy, hw]
  rw [Scheme.range_fromSpecStalk] at hrange
  exact hst (Set.mem_singleton_iff.mp (specializes_iff_forall_closed.mp hrange _ ht (by simp)))

/-- To factor the base change along `g` of a blowup of `W ⟶ S` as a sequence of blowups, it
suffices to factor the blowup of the base change of `W` in the inverse image of the ideal. -/
private theorem factorsAsPointBlowups_pullback_blowUpToBase {S W L : Scheme.{u}} (pW : W ⟶ S)
    (g : L ⟶ S) [Flat g] (I : W.IdealSheafData) {T : Set L}
    (h : FactorsAsPointBlowups L T (blowUp (I.comap (pullback.fst pW g)))
      (blowUpToBase (I.comap (pullback.fst pW g)) ≫ pullback.snd pW g)) :
    FactorsAsPointBlowups L T (pullback (blowUpToBase I ≫ pW) g)
      (pullback.snd (blowUpToBase I ≫ pW) g) := by
  obtain ⟨hb, hhb⟩ := exists_isPullback_blowUpToBase_comap (pullback.fst pW g) I
  have hinv : hhb.flip.isoPullback.inv ≫ blowUpToBase (I.comap (pullback.fst pW g)) =
      pullback.snd (blowUpToBase I) (pullback.fst pW g) := by
    rw [Iso.inv_comp_eq]
    exact hhb.flip.isoPullback_hom_snd.symm
  have h1 : FactorsAsPointBlowups L T (pullback (blowUpToBase I) (pullback.fst pW g))
      (pullback.snd (blowUpToBase I) (pullback.fst pW g) ≫ pullback.snd pW g) :=
    (h.of_iso hhb.flip.isoPullback.symm).congr (by rw [Iso.symm_hom, ← Category.assoc, hinv])
  refine (h1.of_iso (pullbackRightPullbackFstIso pW g (blowUpToBase I)).symm).congr ?_
  rw [Iso.symm_hom, Iso.inv_comp_eq]
  exact (pullbackRightPullbackFstIso_hom_snd pW g _).symm

/-- **Stacks Project, Tag 0BFY**, necessity. Let `s` be an injective family of closed points of
`S` and fix an index `i`. A morphism to `S` which factors as a finite sequence of blowups at
closed points lying over the `s j` becomes, after base change to `Spec 𝒪_{S, s i}`, a finite
sequence of blowups at closed points lying over the closed point: a step whose centre lies over
`s i` is the blowup at the unique point above that centre, and a step whose centre lies over
another `s j` becomes an isomorphism. -/
theorem factorsAsPointBlowups_pullback_fromSpecStalk {S : Scheme.{u}} {n : ℕ} (s : Fin n → S)
    (hinj : Function.Injective s) (hclosed : ∀ j, IsClosed ({s j} : Set S)) (i : Fin n)
    {Z : Scheme.{u}} {p : Z ⟶ S}
    (h : Stacks.ResolutionOfSurfaces.PointBlowupChain S (Set.range s) Z p) :
    FactorsAsPointBlowups (Spec (S.presheaf.stalk (s i)))
      {IsLocalRing.closedPoint (S.presheaf.stalk (s i))}
      (pullback p (S.fromSpecStalk (s i))) (pullback.snd p (S.fromSpecStalk (s i))) := by
  have hflat : Flat (S.fromSpecStalk (s i)) := flat_fromSpecStalk S (s i)
  induction h with
  | refl =>
    refine ((Stacks.ResolutionOfSurfaces.FactorsAsPointBlowups.refl
      ({IsLocalRing.closedPoint (S.presheaf.stalk (s i))} :
        Set (Spec (S.presheaf.stalk (s i))))).of_iso
      (asIso (pullback.snd (𝟙 S) (S.fromSpecStalk (s i))))).congr ?_
    simp
  | @step W pW hh w hw hwT ih =>
    obtain ⟨j, hj⟩ := hwT
    refine factorsAsPointBlowups_pullback_blowUpToBase pW (S.fromSpecStalk (s i)) _ ?_
    by_cases hji : j = i
    · subst hji
      have hwi : pW w = s j := hj.symm
      have hc : pW w = (S.fromSpecStalk (s j)) (IsLocalRing.closedPoint
          (S.presheaf.stalk (s j))) := by
        rw [hwi, Scheme.fromSpecStalk_closedPoint]
      obtain ⟨z, hzfst, hzsnd⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := pW) (g := S.fromSpecStalk (s j)) w
        (IsLocalRing.closedPoint (S.presheaf.stalk (s j))) hc
      obtain ⟨hz, hideal⟩ := vanishingIdeal_singleton_comap_pullbackFst pW
        (S.fromSpecStalk (s j)) w hw (pointToSpecStalk pW w hwi)
        (pointToSpecStalk_comp_fromSpecStalk pW w hwi) z hzfst
      exact factorsAsPointBlowups_blowUp_congr hideal
        (r := pullback.snd pW (S.fromSpecStalk (s j)))
        (Stacks.ResolutionOfSurfaces.FactorsAsPointBlowups.step ih z hz
          (Set.mem_singleton_iff.mpr hzsnd))
    · have hmiss : ∀ y : ↥(pullback pW (S.fromSpecStalk (s i))),
          pullback.fst pW (S.fromSpecStalk (s i)) y ≠ w :=
        pullback_fst_fromSpecStalk_ne pW (hclosed j) (fun h => hji (hinj h).symm) hj.symm
      have hsupp : (((Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).comap
          (pullback.fst pW (S.fromSpecStalk (s i)))).support :
            Set ↥(pullback pW (S.fromSpecStalk (s i)))) = ∅ := by
        rw [coe_support_comap_vanishingIdeal_singleton]
        exact Set.eq_empty_of_forall_notMem hmiss
      have hiso := isIso_blowUpToBase_of_support_eq_empty _ hsupp
      exact Stacks.ResolutionOfSurfaces.FactorsAsPointBlowups.of_iso ih (asIso (blowUpToBase
        ((Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).comap
          (pullback.fst pW (S.fromSpecStalk (s i))))))

/-- An isomorphism over the base transports a factorization as a sequence of blowups. -/
theorem factorsAsPointBlowups_of_overIso {L : Scheme.{u}} {T : Set L} {A B : Over L} (e : A ≅ B)
    (h : FactorsAsPointBlowups L T B.left B.hom) :
    FactorsAsPointBlowups L T A.left A.hom :=
  Stacks.ResolutionOfSurfaces.FactorsAsPointBlowups.congr
    (Stacks.ResolutionOfSurfaces.FactorsAsPointBlowups.of_iso h ((Over.forget L).mapIso e))
    (Over.w e.hom)

/-- **Stacks Project, Tag 0BFY**, necessity. If a morphism to `S` factors as a finite sequence
of blowups at closed points lying over an injective family of closed points `s`, then so does
its base change to `Spec 𝒪_{S, s i}`, over the closed point there. -/
theorem factorsAsPointBlowups_pullback_fromSpecStalk_of_factorsAsPointBlowups {S : Scheme.{u}}
    {n : ℕ} (s : Fin n → S) (hinj : Function.Injective s)
    (hclosed : ∀ j, IsClosed ({s j} : Set S)) (i : Fin n) {Z : Scheme.{u}} {p : Z ⟶ S}
    (h : FactorsAsPointBlowups S (Set.range s) Z p) :
    FactorsAsPointBlowups (Spec (S.presheaf.stalk (s i)))
      {IsLocalRing.closedPoint (S.presheaf.stalk (s i))}
      (pullback p (S.fromSpecStalk (s i))) (pullback.snd p (S.fromSpecStalk (s i))) := by
  obtain ⟨Y, f, hchain, e, he⟩ := h
  exact factorsAsPointBlowups_of_overIso
    ((Over.pullback (S.fromSpecStalk (s i))).mapIso
      (Over.isoMk e he : Over.mk p ≅ Over.mk f))
    (factorsAsPointBlowups_pullback_fromSpecStalk s hinj hclosed i hchain)

namespace FinitePresentationAwayPointsSituation

/-- **Stacks Project, Tag 0BFY**, necessity. If `f : X ⟶ S` factors as a finite sequence of
blowups at closed points lying over the distinguished points, then so does its base change to
the spectrum of the local ring at `s i`, over the closed point there. -/
theorem factorsAsPointBlowups_pullback (D : FinitePresentationAwayPointsSituation.{u})
    (X : D.globalCategory) (i : Fin D.n)
    (h : FactorsAsPointBlowups D.S (Set.range D.points) X.obj.left X.obj.hom) :
    FactorsAsPointBlowups (D.localScheme i)
      {IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))}
      (pullback X.obj.hom (D.S.fromSpecStalk (D.points i)))
      (pullback.snd X.obj.hom (D.S.fromSpecStalk (D.points i))) :=
  factorsAsPointBlowups_pullback_fromSpecStalk_of_factorsAsPointBlowups D.points
    D.points_injective D.points_closed i h

/-- **Stacks Project, Tag 0BFY**, necessity, in the language of Tag 0BFU. If `f : X ⟶ S` factors
as a finite sequence of blowups at closed points lying over the distinguished points, then every
local modification `g i : Y i ⟶ Spec 𝒪_{S, s i}` corresponding to it under a base-change functor
factors as a finite sequence of blowups at closed points lying over the closed point.

Sufficiency is not proved: it needs full faithfulness of the base-change functor, which is
[Stacks, Tag 0BFV] and is absent from this development. -/
@[stacks 0BFY "necessity"]
theorem factorsAsPointBlowups_of_corresponds (D : FinitePresentationAwayPointsSituation.{u})
    (BC : BaseChangeFunctor D) (X : D.globalCategory) (i : Fin D.n) (Y : D.localCategory i)
    (hY : BC.functor.obj X i ≅ Y)
    (h : FactorsAsPointBlowups D.S (Set.range D.points) X.obj.left X.obj.hom) :
    FactorsAsPointBlowups (D.localScheme i)
      {IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))} Y.obj.left Y.obj.hom :=
  factorsAsPointBlowups_of_overIso
    ((ObjectProperty.ι (IsFinitePresentationAway (D.puncturedLocalScheme i))).mapIso hY.symm ≪≫
      (BC.pullbackIso i).app X)
    (D.factorsAsPointBlowups_pullback X i h)

/-- **Stacks Project, Tag 0BFY**, sufficiency, the step supplied by Tag 0BFV. Granted the
glueing theorem of [Stacks, Tag 0E8Q], a modification of `S` supported at the distinguished
points is determined by its localizations: if the localizations of `Z` and of `X` agree and `Z`
factors as a finite sequence of blowups at closed points lying over the distinguished points,
then so does `X`.

Sufficiency itself is still not proved: it remains to construct, from local factorizations of
the `Y i`, a global `Z` whose localizations are the `Y i`. -/
theorem factorsAsPointBlowups_of_baseChange_iso
    (hE : GlueingNearClosedPointsEquivalence.{u})
    (D : FinitePresentationAwayPointsSituation.{u}) (BC : BaseChangeFunctor D)
    {X Z : D.globalCategory} (hXZ : BC.functor.obj Z ≅ BC.functor.obj X)
    (hZ : FactorsAsPointBlowups D.S (Set.range D.points) Z.obj.left Z.obj.hom) :
    FactorsAsPointBlowups D.S (Set.range D.points) X.obj.left X.obj.hom :=
  have : BC.functor.IsEquivalence := BC.isEquivalence hE
  factorsAsPointBlowups_of_overIso
    ((ObjectProperty.ι (IsFinitePresentationAway D.complement)).mapIso
      (BC.functor.preimageIso hXZ).symm) hZ

end FinitePresentationAwayPointsSituation

end AlgebraicGeometry
