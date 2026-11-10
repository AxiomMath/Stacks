module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Etale.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
public import StacksFrontier.Topology.Separation.IsolatedPoint
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapPullback
import StacksFrontier.AlgebraicGeometry.Morphisms.HenselianLocalFinitePiece

/-!
# An étale neighbourhood making a quasi-finite morphism finite

At a point isolated in its fibre, a locally finite type morphism becomes finite on an open
subscheme after an elementary étale change of the base. The open has exactly one point over
the distinguished point, with unchanged residue field. These properties persist under further
elementary étale neighbourhoods.

## Main definitions

* `Stacks.Flatness.IsFiniteNeighborhoodAt` records the finite open, unique point, and residue
  field properties.
* `Stacks.Flatness.FiniteNeighborhoodAt` packages the elementary étale neighbourhood and finite
  open.
* `Stacks.Flatness.finiteNeighborhoodAt` chooses this data at an isolated fibre point.
* `Stacks.Flatness.fiberAfterElementaryEtaleIso` identifies the fibre of the base change over
  the distinguished point of an elementary étale neighbourhood with the original fibre.

## Main results

* `Stacks.Flatness.exists_etaleNeighborhood_finiteAt` gives the finite-neighbourhood
  construction.
* `Stacks.Flatness.isFiniteNeighborhoodAt_baseChange` gives its persistence under elementary
  étale refinement.
* `Stacks.Flatness.pullback_fst_residueFieldMap_isIso_of_elementary`: over an elementary étale
  neighbourhood the residue field is unchanged at every point of the distinguished fibre.

## References

* [Stacks Project, Tag 02LK](https://stacks.math.columbia.edu/tag/02LK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace Stacks.Flatness

/-- Over an *elementary* étale neighbourhood `U` of `s`, the fibre of the base change
`X ×_S U ⟶ U` over the distinguished point is isomorphic to the fibre of `f` over `s`. -/
def fiberAfterElementaryEtaleIso {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) (U : EtaleNeighborhood S s) (hU : U.IsElementary) :
    (pullback.snd f U.toBase).fiber U.point ≅ f.fiber s := by
  have : IsIso U.residueFieldMap := hU
  let eSpec := Scheme.Spec.mapIso (asIso U.residueFieldMap).op
  have hbase : U.scheme.fromSpecResidueField U.point ≫ U.toBase =
      eSpec.hom ≫ S.fromSpecResidueField s := by
    dsimp [eSpec]
    simp [EtaleNeighborhood.residueFieldMap_def, Scheme.residueFieldCongr_fromSpecResidueField]
  let e₁ := pullbackLeftPullbackSndIso f U.toBase (U.scheme.fromSpecResidueField U.point)
  let h₂ := pullback.map f (S.fromSpecResidueField s) f
      (eSpec.hom ≫ S.fromSpecResidueField s) (𝟙 X) eSpec.inv (𝟙 S) (by simp) (by simp)
  have : IsIso h₂ := by
    dsimp [h₂]
    apply pullback.map_isIso
  exact e₁ ≪≫ pullback.congrHom rfl hbase ≪≫ (asIso h₂).symm

/-- The isomorphism `Stacks.Flatness.fiberAfterElementaryEtaleIso` is compatible with the
inclusions of the two fibres into `X`: it is covered by the first projection of the base
change. -/
lemma fiberAfterElementaryEtaleIso_fiberι {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) (U : EtaleNeighborhood S s) (hU : U.IsElementary) :
    (fiberAfterElementaryEtaleIso f s U hU).hom ≫ f.fiberι s =
      (pullback.snd f U.toBase).fiberι U.point ≫ pullback.fst f U.toBase := by
  have : IsIso U.residueFieldMap := hU
  let eSpec := Scheme.Spec.mapIso (asIso U.residueFieldMap).op
  have hbase : U.scheme.fromSpecResidueField U.point ≫ U.toBase =
      eSpec.hom ≫ S.fromSpecResidueField s := by
    dsimp [eSpec]
    simp [EtaleNeighborhood.residueFieldMap_def, Scheme.residueFieldCongr_fromSpecResidueField]
  let e₁ := pullbackLeftPullbackSndIso f U.toBase (U.scheme.fromSpecResidueField U.point)
  let h₂ := pullback.map f (S.fromSpecResidueField s) f
      (eSpec.hom ≫ S.fromSpecResidueField s) (𝟙 X) eSpec.inv (𝟙 S) (by simp) (by simp)
  have : IsIso h₂ := by
    dsimp [h₂]
    apply pullback.map_isIso
  let eCongr : pullback f (U.scheme.fromSpecResidueField U.point ≫ U.toBase) ≅
      pullback f (eSpec.hom ≫ S.fromSpecResidueField s) := pullback.congrHom rfl hbase
  have h₂fst : h₂ ≫ pullback.fst f (eSpec.hom ≫ S.fromSpecResidueField s) =
      pullback.fst f (S.fromSpecResidueField s) := by
    dsimp [h₂, pullback.map]
    rw [pullback.lift_fst]
    simp
  have hCongrfst : eCongr.hom ≫ pullback.fst f (eSpec.hom ≫ S.fromSpecResidueField s) =
      pullback.fst f (U.scheme.fromSpecResidueField U.point ≫ U.toBase) := by
    dsimp [eCongr, pullback.congrHom, pullback.map]
    rw [pullback.lift_fst]
    simp
  have htail : eCongr.hom ≫ (asIso h₂).symm.hom ≫ pullback.fst f (S.fromSpecResidueField s) =
      pullback.fst f (U.scheme.fromSpecResidueField U.point ≫ U.toBase) := by
    calc
      eCongr.hom ≫ (asIso h₂).symm.hom ≫ pullback.fst f (S.fromSpecResidueField s) =
          eCongr.hom ≫ (asIso h₂).symm.hom ≫ h₂ ≫
            pullback.fst f (eSpec.hom ≫ S.fromSpecResidueField s) := by rw [← h₂fst]
      _ = eCongr.hom ≫ pullback.fst f (eSpec.hom ≫ S.fromSpecResidueField s) := by simp
      _ = pullback.fst f (U.scheme.fromSpecResidueField U.point ≫ U.toBase) := hCongrfst
  change (e₁ ≪≫ eCongr ≪≫ (asIso h₂).symm).hom ≫
      pullback.fst f (S.fromSpecResidueField s) = _
  rw [Iso.trans_hom, Iso.trans_hom]
  calc
    e₁.hom ≫ eCongr.hom ≫ (asIso h₂).symm.hom ≫
        pullback.fst f (S.fromSpecResidueField s) =
        e₁.hom ≫ pullback.fst f (U.scheme.fromSpecResidueField U.point ≫ U.toBase) := by
          rw [← htail]
    _ = pullback.fst (pullback.snd f U.toBase)
          (U.scheme.fromSpecResidueField U.point) ≫ pullback.fst f U.toBase :=
        pullbackLeftPullbackSndIso_hom_fst f U.toBase (U.scheme.fromSpecResidueField U.point)

/-- Transporting `AlgebraicGeometry.Scheme.Hom.asFiber` along an equality of images is
inverted by the inclusion of the fibre. -/
lemma fiberι_cast_asFiber {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    {y : Y} (h : f x = y) : f.fiberι y (h ▸ f.asFiber x) = x := by
  cases h
  exact f.fiberι_asFiber x

/-- Transporting `AlgebraicGeometry.Scheme.Hom.asFiber` along an equality of images does not
change whether the resulting point is isolated in its fibre. -/
lemma isIsolatedPoint_cast_asFiber {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    {y : Y} (h : f x = y) :
    IsIsolatedPoint (h ▸ f.asFiber x) ↔ IsIsolatedPoint (f.asFiber x) := by
  cases h
  rfl

/-- In a pullback square, the residue field map of the projection `i` at `z` is an isomorphism
when that of the opposite map `b` is one at `j z`. -/
private lemma isIso_residueFieldMap_of_isPullback {X Y Z U : Scheme.{u}} {i : Z ⟶ X}
    {j : Z ⟶ U} {m : X ⟶ Y} {b : U ⟶ Y} (hpb : IsPullback i j m b) (z : Z)
    (h : IsIso (b.residueFieldMap (j z))) : IsIso (i.residueFieldMap z) := by
  have hfst : pullback.fst b m (hpb.flip.isoPullback.hom z) = j z := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun k : Z ⟶ U => k z) hpb.flip.isoPullback_hom_fst
  have hSnd := pullback_snd_residueFieldMap_isIso b m (hpb.flip.isoPullback.hom z)
    (by rw [hfst]; exact h)
  have hcomp : IsIso ((hpb.flip.isoPullback.hom ≫ pullback.snd b m).residueFieldMap z) := by
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' hSnd (by infer_instance)
  rwa [hpb.flip.isoPullback_hom_snd] at hcomp

/-- The projection to `X` of a base change along an elementary étale neighbourhood induces an
isomorphism on residue fields at every point lying over the distinguished point. -/
lemma pullback_fst_residueFieldMap_isIso_of_elementary
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (U : EtaleNeighborhood S s) (hU : U.IsElementary)
    (y : (pullback f U.toBase : Scheme).carrier)
    (hy : pullback.snd f U.toBase y = U.point) :
    IsIso ((pullback.fst f U.toBase).residueFieldMap y) := by
  have := U.isElementary_iff.mp hU
  exact isIso_residueFieldMap_of_isPullback (IsPullback.of_hasPullback f U.toBase) y
    (by rw [hy]; infer_instance)

/-- Base changing `X ×_S U ⟶ U` along a morphism `Up ⟶ U` gives `X ×_S Up ⟶ Up`: the
canonical comparison map and the second projections form a pullback square. -/
lemma pullbackMap_snd_isPullback {X S U Up : Scheme.{u}} (f : X ⟶ S)
    (u₀ : U ⟶ S) (u₁ : Up ⟶ U) :
    IsPullback
      (pullback.map f (u₁ ≫ u₀) f u₀ (𝟙 X) u₁ (𝟙 S) (by simp) (by simp))
      (pullback.snd f (u₁ ≫ u₀)) (pullback.snd f u₀) u₁ := by
  let e := pullbackLeftPullbackSndIso f u₀ u₁
  apply IsPullback.of_iso (IsPullback.of_hasPullback (pullback.snd f u₀) u₁)
    e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ rfl rfl
  · apply pullback.hom_ext
    · simp only [Iso.refl_hom, Category.comp_id, Category.assoc, pullback.map,
        pullback.lift_fst]
      rw [pullbackLeftPullbackSndIso_hom_fst]
    · simp only [Iso.refl_hom, Category.comp_id, Category.assoc, pullback.map,
        pullback.lift_snd]
      calc
        _ = pullback.snd (pullback.snd f u₀) u₁ ≫ u₁ := pullback.condition
        _ = (pullbackLeftPullbackSndIso f u₀ u₁).hom ≫ pullback.snd f (u₁ ≫ u₀) ≫ u₁ :=
          congrArg (fun k => k ≫ u₁) (pullbackLeftPullbackSndIso_hom_snd f u₀ u₁).symm
  · simp only [Iso.refl_hom, Category.comp_id]
    exact (pullbackLeftPullbackSndIso_hom_snd f u₀ u₁).symm

/-- If `y` is the only point of `X` over `y`, then after base change along an elementary étale
neighbourhood of `y` there is again exactly one point over the distinguished point. -/
lemma existsUnique_point_pullback_elementary {X Y : Scheme.{u}}
    (m : X ⟶ Y) (y : Y) (U : EtaleNeighborhood Y y) (hU : U.IsElementary)
    (huniq : ∃! x : X, m x = y) :
    ∃! z : (pullback m U.toBase : Scheme).carrier, pullback.snd m U.toBase z = U.point := by
  rcases huniq with ⟨x₀, hx₀, hxuniq⟩
  let e := fiberAfterElementaryEtaleIso m y U hU
  let p : m.fiber y := hx₀ ▸ m.asFiber x₀
  let q : (pullback.snd m U.toBase).fiber U.point := e.inv p
  let z₀ : (pullback m U.toBase : Scheme).carrier :=
    (pullback.snd m U.toBase).fiberι U.point q
  have hz₀ : pullback.snd m U.toBase z₀ = U.point := by
    simpa [z₀] using ((pullback.snd m U.toBase).fiberHomeo U.point q).2
  refine ⟨z₀, hz₀, ?_⟩
  intro z hz
  let qz : (pullback.snd m U.toBase).fiber U.point :=
    ((pullback.snd m U.toBase).fiberHomeo U.point).symm ⟨z, hz⟩
  have hqz : (pullback.snd m U.toBase).fiberι U.point qz = z :=
    congrArg Subtype.val <| (pullback.snd m U.toBase).fiberHomeo U.point |>.apply_symm_apply
      ⟨z, hz⟩
  have hmap : m.fiberι y (e.hom qz) = pullback.fst m U.toBase z := by
    have h := congrArg (fun k : (pullback.snd m U.toBase).fiber U.point ⟶ X => k qz)
      (fiberAfterElementaryEtaleIso_fiberι m y U hU)
    simpa only [Scheme.Hom.comp_apply, hqz] using h
  have hmap_to_base : m (m.fiberι y (e.hom qz)) = y := by
    simpa using (m.fiberHomeo y (e.hom qz)).2
  have hpoint : m.fiberι y (e.hom qz) = x₀ := hxuniq _ hmap_to_base
  have hEq : m.fiberHomeo y (e.hom qz) = m.fiberHomeo y p := by
    apply Subtype.ext
    calc
      (m.fiberHomeo y (e.hom qz)).1 = m.fiberι y (e.hom qz) := rfl
      _ = x₀ := hpoint
      _ = m.fiberι y p := (fiberι_cast_asFiber m x₀ hx₀).symm
      _ = (m.fiberHomeo y p).1 := rfl
  have hq : qz = q := by simpa [q] using congrArg e.inv ((m.fiberHomeo y).injective hEq)
  rw [← hqz, hq]

/-- The version of `Stacks.Flatness.existsUnique_point_pullback_elementary` for an abstract
pullback square rather than the chosen pullback. -/
lemma existsUnique_point_of_isPullback_elementary {X Y Z : Scheme.{u}}
    {i : Z ⟶ X} (m : X ⟶ Y) (y : Y)
    (U : EtaleNeighborhood Y y) (hU : U.IsElementary)
    {j : Z ⟶ U.scheme} (hpb : IsPullback i j m U.toBase)
    (huniq : ∃! x : X, m x = y) :
    ∃! z : Z.carrier, j z = U.point := by
  obtain ⟨q, hq, hquniq⟩ := existsUnique_point_pullback_elementary m y U hU huniq
  let e := hpb.isoPullback
  let z₀ : Z.carrier := e.inv q
  have hz₀ : j z₀ = U.point := by
    calc
      j z₀ = pullback.snd m U.toBase (e.hom z₀) := by
        have h := congrArg (fun k : Z ⟶ U.scheme => k z₀) hpb.isoPullback_hom_snd
        simpa only [Scheme.Hom.comp_apply] using h.symm
      _ = pullback.snd m U.toBase q := by simp [z₀]
      _ = U.point := hq
  refine ⟨z₀, hz₀, ?_⟩
  intro z hz
  have hqz : pullback.snd m U.toBase (e.hom z) = U.point := by
    calc
      pullback.snd m U.toBase (e.hom z) = j z := by
        have h := congrArg (fun k : Z ⟶ U.scheme => k z) hpb.isoPullback_hom_snd
        simpa only [Scheme.Hom.comp_apply] using h
      _ = U.point := hz
  simpa [z₀] using congrArg e.inv (hquniq (e.hom z) hqz)

/-- An equality of composites, read on a point. -/
private alias apply_eq_of_comp_eq := AlgebraicGeometry.Scheme.Hom.apply_eq_of_comp_eq

/-- The inclusion of an open subscheme induces isomorphisms on residue fields. -/
private lemma isIso_residueFieldMap_ι {X : Scheme.{u}} (W : X.Opens) (v : W.toScheme) :
    IsIso (W.ι.residueFieldMap v) := inferInstance

/-- If `P` lies over `q` and `P.comap (algebraMap A B) = q`, then bijectivity of the residue field
map of `P` over `q` gives bijectivity of the residue field map of `P` over its contraction. -/
lemma residueFieldMap_bijective_of_comap_eq
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (q : Ideal A) [q.IsPrime] (P : Ideal B) [P.IsPrime]
    (hcomap : P.comap (algebraMap A B) = q) [P.LiesOver q]
    (hbij : Function.Bijective
      (Ideal.ResidueField.mapₐ q P (Algebra.ofId A B) (P.over_def q))) :
    Function.Bijective
      (Ideal.ResidueField.mapₐ (P.comap (algebraMap A B)) P (Algebra.ofId A B) rfl) := by
  cases hcomap
  exact hbij

/-- A ring map inducing a bijection of residue fields at a prime induces an isomorphism of
residue fields on spectra. -/
lemma isIso_residueFieldMap_specMap_of_bijective
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (q : PrimeSpectrum B)
    (hbij : Function.Bijective
      (Ideal.ResidueField.mapₐ (q.asIdeal.comap (algebraMap A B)) q.asIdeal
        (Algebra.ofId A B) rfl)) :
    IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A B))).residueFieldMap q) := by
  let p : ↥(Spec (.of A)) := Spec.map (CommRingCat.ofHom (algebraMap A B)) q
  have : p.asIdeal.IsPrime := p.2
  have : q.asIdeal.IsPrime := q.isPrime
  let eA := Scheme.Spec.residueFieldIso (.of A) p
  let eB := Scheme.Spec.residueFieldIso (.of B) q
  let m := Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal (Algebra.ofId A B) rfl
  have hm : Function.Bijective (m : p.asIdeal.ResidueField → q.asIdeal.ResidueField) := hbij
  have : IsIso (CommRingCat.ofHom m.toRingHom) := (ConcreteCategory.isIso_iff_bijective _).2 hm
  have : IsLocalRing ((Spec (.of A)).presheaf.stalk p) :=
    (Spec.locallyRingedSpaceObj (.of A)).isLocalRing p
  have : IsLocalRing ((Spec (.of B)).presheaf.stalk q) :=
    (Spec.locallyRingedSpaceObj (.of B)).isLocalRing q
  let a := Spec.stalkIso (.of A) p
  let b := Spec.stalkIso (.of B) q
  have : IsLocalHom a.hom.hom := isLocalHom_of_iso a
  have : IsLocalHom b.hom.hom := isLocalHom_of_iso b
  let ell := CommRingCat.ofHom
    (Localization.localRingHom p.asIdeal q.asIdeal (algebraMap A B) rfl)
  have heA : eA.hom = CommRingCat.ofHom (IsLocalRing.ResidueField.map a.hom.hom) := by
    ext z
    rfl
  have heB : eB.hom = CommRingCat.ofHom (IsLocalRing.ResidueField.map b.hom.hom) := by
    ext z
    rfl
  have : IsLocalHom ell.hom :=
    Localization.isLocalHom_localRingHom p.asIdeal q.asIdeal (algebraMap A B) rfl
  have hmEq : CommRingCat.ofHom m.toRingHom =
      CommRingCat.ofHom (IsLocalRing.ResidueField.map ell.hom) := by
    ext z
    rfl
  have hstalk : a.hom ≫ ell ≫ b.inv =
      (Spec.map (CommRingCat.ofHom (algebraMap A B))).stalkMap q :=
    Scheme.localRingHom_comp_stalkIso (CommRingCat.ofHom (algebraMap A B)) q
  have hstalk' : a.hom ≫ ell =
      (Spec.map (CommRingCat.ofHom (algebraMap A B))).stalkMap q ≫ b.hom := by
    apply (cancel_mono b.inv).1
    calc
      (a.hom ≫ ell) ≫ b.inv = a.hom ≫ ell ≫ b.inv := Category.assoc _ _ _
      _ = (Spec.map (CommRingCat.ofHom (algebraMap A B))).stalkMap q := hstalk
      _ = ((Spec.map (CommRingCat.ofHom (algebraMap A B))).stalkMap q ≫ b.hom) ≫ b.inv := by
        symm
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : IsLocalHom ((Spec.map (CommRingCat.ofHom (algebraMap A B))).stalkMap q).hom :=
    (Spec.map (CommRingCat.ofHom (algebraMap A B))).prop q
  have hring : ell.hom.comp a.hom.hom =
      b.hom.hom.comp ((Spec.map (CommRingCat.ofHom (algebraMap A B))).stalkMap q).hom :=
    congrArg (fun k => CommRingCat.Hom.hom k) hstalk'
  have hmapEq : IsLocalRing.ResidueField.map (ell.hom.comp a.hom.hom) =
      IsLocalRing.ResidueField.map
        (b.hom.hom.comp ((Spec.map (CommRingCat.ofHom (algebraMap A B))).stalkMap q).hom) := by
    dsimp [p] at hring ⊢
    apply RingHom.ext
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    simp [IsLocalRing.ResidueField.map, hring]
  have hcompat : eA.hom ≫ CommRingCat.ofHom m.toRingHom =
      (Spec.map (CommRingCat.ofHom (algebraMap A B))).residueFieldMap q ≫ eB.hom := by
    rw [heA, heB, hmEq]
    apply CommRingCat.hom_ext
    ext z
    change IsLocalRing.ResidueField.map ell.hom
        (IsLocalRing.ResidueField.map a.hom.hom z) =
      IsLocalRing.ResidueField.map b.hom.hom (IsLocalRing.ResidueField.map
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).stalkMap q).hom z)
    calc
      _ = IsLocalRing.ResidueField.map (ell.hom.comp a.hom.hom) z :=
        IsLocalRing.ResidueField.map_map a.hom.hom ell.hom z
      _ = IsLocalRing.ResidueField.map
          (b.hom.hom.comp ((Spec.map (CommRingCat.ofHom (algebraMap A B))).stalkMap q).hom) z :=
        congrArg (fun g : _ →+* _ => g z) hmapEq
      _ = _ := (IsLocalRing.ResidueField.map_map
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).stalkMap q).hom b.hom.hom z).symm
  have : IsIso eA.hom := eA.isIso_hom
  have : IsIso eB.hom := eB.isIso_hom
  have : IsIso (eA.hom ≫ CommRingCat.ofHom m.toRingHom) := by infer_instance
  have h : IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A B))).residueFieldMap q ≫
      eB.hom) := by
    rw [← hcompat]
    infer_instance
  exact IsIso.of_isIso_comp_right _ eB.hom

/-- An open in an étale base change that is finite over the new base and has exactly one
point over the distinguished point, mapping to `x` with the same residue field. -/
def IsFiniteNeighborhoodAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (U : EtaleNeighborhood S (f x))
    (V : (pullback f U.toBase).Opens) : Prop :=
  IsFinite (V.ι ≫ pullback.snd f U.toBase) ∧
    (∃! v : V, (V.ι ≫ pullback.snd f U.toBase) v = U.point) ∧
    ∀ v : V, (V.ι ≫ pullback.snd f U.toBase) v = U.point →
      (V.ι ≫ pullback.fst f U.toBase) v = x ∧
        IsIso ((V.ι ≫ pullback.fst f U.toBase).residueFieldMap v)

/-- A finite open after an elementary étale change of the base, with its distinguished-fibre
and residue-field specifications. -/
structure FiniteNeighborhoodAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X) where
  /-- The elementary étale neighbourhood of the image point to which we pass. -/
  neighborhood : EtaleNeighborhood S (f x)
  /-- The neighbourhood is elementary. -/
  elementary : neighborhood.IsElementary
  /-- The open subscheme of the base change which is finite over the new base. -/
  openSubscheme : (pullback f neighborhood.toBase).Opens
  /-- The finiteness, uniqueness and residue-field properties of the open subscheme. -/
  spec : IsFiniteNeighborhoodAt f x neighborhood openSubscheme

/-- A locally finite type morphism becomes finite near a point isolated in its fibre after an
elementary étale base change. -/
@[stacks 02LK "existence", ega "IV 18.12.1"]
theorem exists_etaleNeighborhood_finiteAt {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) (hx : IsIsolatedPoint (f.asFiber x)) :
    Nonempty (FiniteNeighborhoodAt f x) := by
  classical
  have hq : f.QuasiFiniteAt x := (f.quasiFiniteAt_iff_isOpen_singleton_asFiber).mpr hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hUV : V ≤ f ⁻¹ᵁ U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).2
  have hfiniteType : (f.appLE U V hUV).hom.FiniteType := f.finiteType_appLE hU hV hUV
  algebraize [(f.appLE U V hUV).hom]
  have hpq : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.LiesOver
      (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal := by
    have hEq := (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hUV hxV).symm
    exact ⟨congr(($hEq).1)⟩
  have hquasi : Algebra.QuasiFiniteAt Γ(S, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    hq.quasiFiniteAt hV hU hUV hxV
  obtain ⟨R, _, _, _, P, hP, hPp, e, he, P', hP', hP'P, hP'q, heP', hbij, hfinite, hunique⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq
      (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hAwayFinite : (algebraMap R (Localization.Away e)).Finite :=
    RingHom.finite_algebraMap.mpr hfinite
  let φ : Γ(S, U) ⟶ CommRingCat.of R := CommRingCat.ofHom (algebraMap Γ(S, U) R)
  have hφ : φ.hom.Etale := RingHom.etale_algebraMap.mpr inferInstance
  have : Etale (Spec.map φ) := HasRingHomProperty.Spec_iff.mpr hφ
  let e₁ : Spec (CommRingCat.of (R ⊗[Γ(S, U)] Γ(X, V))) ≅
      pullback (Spec.map (f.appLE U V hUV)) (Spec.map φ) :=
    (pullbackSpecIso _ _ _).symm ≪≫ pullbackSymmetry _ _
  have he₁ : e₁.hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) := by
    dsimp [e₁, RingHom.algebraMap_toAlgebra]
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact pullbackSpecIso_inv_snd ..
  let g : Spec (CommRingCat.of (R ⊗[Γ(S, U)] Γ(X, V))) ⟶
      pullback f (Spec.map φ ≫ hU.fromSpec) :=
    e₁.hom ≫ pullback.map _ _ _ _ hV.fromSpec (𝟙 _) hU.fromSpec
      (IsAffineOpen.SpecMap_appLE_fromSpec ..) (by simp)
  have : IsOpenImmersion hV.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec hV
  have : IsOpenImmersion hU.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec hU
  have : Mono hU.fromSpec := inferInstance
  have : Etale (Spec.map φ ≫ hU.fromSpec) := by infer_instance
  have : IsOpenImmersion g := by
    dsimp [g]
    infer_instance
  let W₁ := g ''ᵁ PrimeSpectrum.basicOpen e
  have hsndSpec : e₁.hom ≫ pullback.snd (Spec.map (f.appLE U V hUV)) (Spec.map φ) =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := by
    change ((pullbackSpecIso _ R _).inv ≫
      (pullbackSymmetry (Spec.map φ) (Spec.map (f.appLE U V hUV))).hom) ≫
      pullback.snd (Spec.map (f.appLE U V hUV)) (Spec.map φ) = _
    calc
      _ = (pullbackSpecIso _ R _).inv ≫
          pullback.fst (Spec.map φ) (Spec.map (f.appLE U V hUV)) := by
        simp only [Category.assoc, pullbackSymmetry_hom_comp_snd]
      _ = _ := pullbackSpecIso_inv_fst Γ(S, U) R Γ(X, V)
  have hgsnd : g ≫ pullback.snd f (Spec.map φ ≫ hU.fromSpec) =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := by
    dsimp only [g]
    simp only [Category.assoc, pullback.map, pullback.lift_snd, Category.comp_id]
    exact hsndSpec
  have hWfinite : IsFinite (W₁.ι ≫ pullback.snd f (Spec.map φ ≫ hU.fromSpec)) := by
    let ι : Spec (CommRingCat.of (Localization.Away e)) ⟶
        pullback f (Spec.map φ ≫ hU.fromSpec) :=
      Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ g
    have hι : ι.opensRange = W₁ := by
      simp only [Scheme.Hom.opensRange_comp, ι, W₁]
      congr 1
      exact TopologicalSpace.Opens.ext <| PrimeSpectrum.localization_away_comap_range _ _
    have hResp : MorphismProperty.RespectsIso @IsFinite :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    rw [← hι, ← MorphismProperty.cancel_left_of_respectsIso @IsFinite
      (Scheme.Hom.isoOpensRange _).hom]
    have hcomp : (Scheme.Hom.isoOpensRange ι).hom ≫ ι.opensRange.ι ≫
        pullback.snd f (Spec.map φ ≫ hU.fromSpec) =
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away e))) := by
      rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
      calc
        ι ≫ pullback.snd f (Spec.map φ ≫ hU.fromSpec) =
            Spec.map (CommRingCat.ofHom (algebraMap (R ⊗[Γ(S, U)] Γ(X, V))
              (Localization.Away e))) ≫ g ≫
              pullback.snd f (Spec.map φ ≫ hU.fromSpec) := Category.assoc _ _ _
        _ = Spec.map (CommRingCat.ofHom (algebraMap (R ⊗[Γ(S, U)] Γ(X, V))
              (Localization.Away e))) ≫
              Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := by
          rw [hgsnd]
        _ = Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away e))) := by
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [hcomp]
    exact (IsFinite.SpecMap_iff _).2 hAwayFinite
  let U' : EtaleNeighborhood S (f x) :=
    { scheme := Spec (CommRingCat.of R)
      point := ⟨P, hP⟩
      toBase := Spec.map φ ≫ hU.fromSpec
      map_point := by
        have hp : (Spec.map φ) (⟨P, hP⟩ : PrimeSpectrum R) =
            hU.primeIdealOf ⟨f x, hxU⟩ := by
          apply PrimeSpectrum.ext
          change Ideal.under Γ(S, U) P = (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal
          exact (Ideal.over_def P _).symm
        change hU.fromSpec ((Spec.map φ) (⟨P, hP⟩ : PrimeSpectrum R)) = f x
        rw [hp]
        exact hU.fromSpec_primeIdealOf ⟨f x, hxU⟩ }
  have hpResidue : P.comap (algebraMap Γ(S, U) R) = (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal := by
    simpa only [Ideal.under] using (Ideal.over_def P _).symm
  have hbij' : Function.Bijective
      (Ideal.ResidueField.mapₐ
        ((⟨P, hP⟩ : PrimeSpectrum R).asIdeal.comap (algebraMap Γ(S, U) R))
        (⟨P, hP⟩ : PrimeSpectrum R).asIdeal (Algebra.ofId _ _) rfl) :=
    residueFieldMap_bijective_of_comap_eq
      (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal P hpResidue hbij
  have hspecres : IsIso ((Spec.map φ).residueFieldMap U'.point) :=
    isIso_residueFieldMap_specMap_of_bijective (⟨P, hP⟩ : PrimeSpectrum R) hbij'
  have hfromres : IsIso (hU.fromSpec.residueFieldMap ((Spec.map φ) U'.point)) := inferInstance
  have hU'elem : U'.IsElementary :=
    U'.isElementary_iff.mpr
      (isIso_residueFieldMap_comp (Spec.map φ) hU.fromSpec U'.point hspecres hfromres)
  refine ⟨⟨U', hU'elem, W₁, ?_⟩⟩
  let ψ : CommRingCat.of R ⟶ CommRingCat.of (R ⊗[Γ(S, U)] Γ(X, V)) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  have hgbase : g ≫ pullback.snd f U'.toBase = Spec.map ψ := hgsnd
  let q₀ : PrimeSpectrum (R ⊗[Γ(S, U)] Γ(X, V)) := ⟨P', hP'⟩
  have hq₀open : q₀ ∈ PrimeSpectrum.basicOpen e := heP'
  have hq₀base : Spec.map ψ q₀ = U'.point := by
    apply PrimeSpectrum.ext
    change P'.comap Algebra.TensorProduct.includeLeftRingHom = P
    exact (P'.over_def P).symm
  let v₀ : W₁ := ⟨g q₀, by
    change g q₀ ∈ g ''ᵁ PrimeSpectrum.basicOpen e
    exact ⟨q₀, hq₀open, rfl⟩⟩
  have hv₀base : (W₁.ι ≫ pullback.snd f U'.toBase) v₀ = U'.point :=
    (Scheme.Hom.comp_apply W₁.ι (pullback.snd f U'.toBase) v₀).trans
      ((apply_eq_of_comp_eq hgbase q₀).trans hq₀base)
  have hv₀x : (W₁.ι ≫ pullback.fst f U'.toBase) v₀ = x := by
    let ιR : CommRingCat.of Γ(X, V) ⟶ CommRingCat.of (R ⊗[Γ(S, U)] Γ(X, V)) :=
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
        Γ(X, V) →+* (R ⊗[Γ(S, U)] Γ(X, V)))
    have hprime : (⟨P'.comap ιR.hom, inferInstance⟩ : PrimeSpectrum Γ(X, V)) =
        hV.primeIdealOf ⟨x, hxV⟩ := PrimeSpectrum.ext hP'q
    have hgfst : g ≫ pullback.fst f U'.toBase = Spec.map ιR ≫ hV.fromSpec := by
      dsimp only [g, U']
      simp only [Category.assoc, pullback.map, pullback.lift_fst]
      rw [← Category.assoc, he₁]
    calc
      (W₁.ι ≫ pullback.fst f U'.toBase) v₀ = hV.fromSpec (Spec.map ιR q₀) :=
        (Scheme.Hom.comp_apply W₁.ι (pullback.fst f U'.toBase) v₀).trans
          ((apply_eq_of_comp_eq hgfst q₀).trans
            (Scheme.Hom.comp_apply (Spec.map ιR) hV.fromSpec q₀))
      _ = hV.fromSpec (hV.primeIdealOf ⟨x, hxV⟩) := congrArg hV.fromSpec hprime
      _ = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have hιres : IsIso (W₁.ι.residueFieldMap v₀) := isIso_residueFieldMap_ι W₁ v₀
  have hv₀res : IsIso ((W₁.ι ≫ pullback.fst f U'.toBase).residueFieldMap v₀) :=
    isIso_residueFieldMap_comp W₁.ι (pullback.fst f U'.toBase) v₀ hιres
      (pullback_fst_residueFieldMap_isIso_of_elementary f (f x) U' hU'elem v₀.1 hv₀base)
  have huniq (z : W₁) (hz : (W₁.ι ≫ pullback.snd f U'.toBase) z = U'.point) : z = v₀ := by
    have hmem := z.2
    change z.1 ∈ g ''ᵁ PrimeSpectrum.basicOpen e at hmem
    obtain ⟨q, hqe, hqz⟩ := hmem
    have hqbase : Spec.map ψ q = U'.point := by
      calc
        Spec.map ψ q = pullback.snd f U'.toBase (g q) := (apply_eq_of_comp_eq hgbase q).symm
        _ = pullback.snd f U'.toBase (W₁.ι z) := congrArg _ hqz
        _ = U'.point :=
          (Scheme.Hom.comp_apply W₁.ι (pullback.snd f U'.toBase) z).symm.trans hz
    have hqlies : q.asIdeal.LiesOver P := by
      refine ⟨?_⟩
      have heq := congrArg (fun y : PrimeSpectrum R => y.asIdeal) hqbase
      change P = q.asIdeal.comap Algebra.TensorProduct.includeLeftRingHom
      exact heq.symm
    have hnot : e ∉ q.asIdeal := hqe
    have hqP : q.asIdeal = P' := hunique q.asIdeal q.isPrime hqlies hnot
    exact Subtype.ext (hqz.symm.trans (congrArg g (PrimeSpectrum.ext hqP)))
  refine ⟨hWfinite, ⟨v₀, hv₀base, huniq⟩, ?_⟩
  intro z hz
  rw [huniq z hz]
  exact ⟨hv₀x, hv₀res⟩

/-- A choice of finite neighbourhood of a point isolated in its fibre. -/
noncomputable def finiteNeighborhoodAt {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) (hx : IsIsolatedPoint (f.asFiber x)) :
    FiniteNeighborhoodAt f x :=
  Classical.choice (exists_etaleNeighborhood_finiteAt f x hx)

/-- The pullback of a finite neighbourhood along any further elementary étale neighbourhood is
again a finite neighbourhood: finite over the new base, with a unique distinguished-fibre point
having the same residue field as the original point. -/
@[stacks 02LK "elementary étale refinement"]
theorem isFiniteNeighborhoodAt_baseChange {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (U : EtaleNeighborhood S (f x))
    (V : (pullback f U.toBase).Opens) (hV : IsFiniteNeighborhoodAt f x U V)
    (U' : EtaleNeighborhood U.scheme U.point) (hU' : U'.IsElementary) :
    IsFiniteNeighborhoodAt f x
      { scheme := U'.scheme
        point := U'.point
        toBase := U'.toBase ≫ U.toBase
        map_point := by simp [U'.map_point, U.map_point] }
      ((pullback.map f (U'.toBase ≫ U.toBase) f U.toBase
        (𝟙 X) U'.toBase (𝟙 S) (by simp) (by simp)) ⁻¹ᵁ V) := by
  classical
  let newBase := U'.toBase ≫ U.toBase
  let g := pullback.map f newBase f U.toBase (𝟙 X) U'.toBase (𝟙 S) (by simp) (by rfl)
  let W := g ⁻¹ᵁ V
  let i := g ∣_ V
  let m := V.ι ≫ pullback.snd f U.toBase
  have hpbMap := pullbackMap_snd_isPullback f U.toBase U'.toBase
  have hpbOpen := isPullback_morphismRestrict g V
  have hpb : IsPullback i (W.ι ≫ pullback.snd f newBase) m U'.toBase := by
    simpa [i, W, m, newBase, g] using (IsPullback.paste_vert hpbOpen hpbMap)
  have hfinite : IsFinite (W.ι ≫ pullback.snd f newBase) :=
    MorphismProperty.of_isPullback (P := @IsFinite) hpb hV.1
  obtain ⟨v₀, hv₀, hvuniq⟩ := hV.2.1
  obtain ⟨w, hw, hwuniq⟩ :=
    existsUnique_point_of_isPullback_elementary m U.point U' hU' hpb hV.2.1
  have hmw : m (i w) = U.point := by
    calc
      m (i w) = (i ≫ m) w := (Scheme.Hom.comp_apply i m w).symm
      _ = ((W.ι ≫ pullback.snd f newBase) ≫ U'.toBase) w :=
        congrArg (fun k : W.toScheme ⟶ U.scheme => k w) hpb.w
      _ = U'.toBase ((W.ι ≫ pullback.snd f newBase) w) := Scheme.Hom.comp_apply _ _ _
      _ = U.point := by rw [hw, U'.map_point]
  have hiw : i w = v₀ := hvuniq _ hmw
  have hiι : W.ι ≫ g = i ≫ V.ι := by
    dsimp [i]
    exact (morphismRestrict_ι g V).symm
  have hgfst : g ≫ pullback.fst f U.toBase = pullback.fst f newBase := by
    dsimp [g, newBase]
    simp only [pullback.map, pullback.lift_fst, Category.comp_id]
  have hprojX : W.ι ≫ pullback.fst f newBase = i ≫ (V.ι ≫ pullback.fst f U.toBase) := by
    calc
      W.ι ≫ pullback.fst f newBase = W.ι ≫ g ≫ pullback.fst f U.toBase := by rw [hgfst]
      _ = i ≫ (V.ι ≫ pullback.fst f U.toBase) :=
        congrArg (fun k : W.toScheme ⟶ pullback f U.toBase =>
          k ≫ pullback.fst f U.toBase) hiι
  have hxw : (W.ι ≫ pullback.fst f newBase) w = x := by
    calc
      (W.ι ≫ pullback.fst f newBase) w = (V.ι ≫ pullback.fst f U.toBase) (i w) := by
        have h := congrArg (fun k : W.toScheme ⟶ X => k w) hprojX
        simpa only [Scheme.Hom.comp_apply] using h
      _ = x := by rw [hiw]; exact (hV.2.2 v₀ hv₀).1
  have hiRes : IsIso (i.residueFieldMap w) :=
    isIso_residueFieldMap_of_isPullback hpb w (by rw [hw]; exact U'.isElementary_iff.mp hU')
  have hres : IsIso ((W.ι ≫ pullback.fst f newBase).residueFieldMap w) := by
    rw [hprojX, Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' (hV.2.2 (i w) hmw).2 hiRes
  refine ⟨hfinite, ⟨w, hw, hwuniq⟩, ?_⟩
  intro z hz
  obtain rfl := hwuniq z hz
  exact ⟨hxw, hres⟩

end Stacks.Flatness

end
