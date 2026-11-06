module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import StacksCore.FieldTheory.PurelyTranscendental
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.OneStep.BaseChange
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec

/-!
# Base change of a one-step dévissage at a point

A one-step dévissage at a point `x` survives base change along a morphism of pointed schemes
`(S', s') ⟶ (S, s)` with `S'` affine which induces an isomorphism `κ(s) ≅ κ(s')`. The
distinguished points of the base-changed dévissage are the unique points of the base-changed
schemes lying both over the original distinguished points and over `s'`.

## Main results

* `AlgebraicGeometry.OneStepDevissageAt.exists_baseChange`: the base-changed dévissage at the
  distinguished point, with its underlying dévissage and its two distinguished points
  identified with the given base-change data.

## Implementation notes

The result is stated for an arbitrary realization of the base-change data of
`AlgebraicGeometry.OneStepDevissage.BaseChangeData` rather than for one chosen construction.
The three distinguished points are not constructed but characterized: they are given as
arguments, by their images in the original schemes and in the new base. Uniqueness of such a
point is the only place where the hypothesis on residue fields is used for the source, and it
comes from the classification of the points of a fibre product: the residue-field tensor
product degenerates to a field, so its spectrum is a single point.

That the local dimension condition and the membership in the support persist is a purely
topological matter: the hypothesis on residue fields makes the comparison morphism from the
fibre of the base change to the original fibre an isomorphism, and the supports correspond
under it.

Heterogeneous equality is used to identify the resulting dévissage with the given one because
the type of a dévissage over a point depends on that point, and the new base point is only
*equal* to the image of the chosen source point, not syntactically it.

## References

* [Stacks Project, Tag 05H8](https://stacks.math.columbia.edu/tag/05H8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

section ResidueFields

/-- The spectrum of a ring isomorphic to a field is a single point. -/
private lemma subsingleton_spec_of_isIso_of_field {K : Type*} [Field K] (R : CommRingCat)
    (f : CommRingCat.of K ⟶ R) [IsIso f] : Subsingleton (Spec R) := by
  let e := Scheme.Spec.mapIso (asIso f).op
  let uK : Unique ↥(Spec (CommRingCat.of K)) :=
    AlgebraicGeometry.Scheme.instUniqueCarrierCarrierCommRingCatSpecOf
  refine ⟨fun p q => e.hom.homeomorph.injective ?_⟩
  exact (uK.uniq (e.hom p)).trans (uK.uniq (e.hom q)).symm

/-- The two images of a point under the two composites of a commutative square agree. -/
private lemma apply_eq_of_comp_eq {A B C D : Scheme.{u}} {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C}
    {d : C ⟶ D} (w : a ≫ b = c ≫ d) (z : A) : b (a z) = d (c z) := by
  rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]

/-- Residue-field maps along `e ≫ k` are isomorphisms if `k` is one at `e p`, for `e` an
isomorphism of schemes. -/
private lemma isIso_comp_residueFieldMap_of_iso {P Q R : Scheme.{u}} (e : P ⟶ Q) [IsIso e]
    (k : Q ⟶ R) (p : P) (hk : IsIso (k.residueFieldMap (e p))) :
    IsIso ((e ≫ k).residueFieldMap p) := by
  rw [Scheme.residueFieldMap_comp]
  exact IsIso.comp_isIso' hk inferInstance

/-- A point of a fibre product is determined by its two images as soon as one of the two
morphisms induces an isomorphism on residue fields at the relevant points. -/
private lemma pullback_point_eq_of_isIso_residueFieldMap
    {A B S : Scheme.{u}} (f : A ⟶ S) (g : B ⟶ S) (x : A) (y : B) (hxy : f x = g y)
    (hfield : IsIso ((S.residueFieldCongr hxy.symm).inv ≫ g.residueFieldMap y))
    (p q : ↥(pullback f g))
    (hp : pullback.fst f g p = x) (hq : pullback.snd f g p = y)
    (hp' : pullback.fst f g q = x) (hq' : pullback.snd f g q = y) : p = q := by
  let e := Scheme.Pullback.carrierEquiv (f := f) (g := g)
  have htrip : (e p).1 = (e q).1 :=
    Scheme.Pullback.Triplet.ext (hp.trans hp'.symm) (hq.trans hq'.symm)
  refine e.injective (Scheme.Pullback.carrierEquiv_eq_iff.mpr ⟨htrip, ?_⟩)
  set T : Scheme.Pullback.Triplet f g := (e q).1 with hT
  have hyT : T.y = y := hq'
  have : IsIso (g.residueFieldMap T.y) := by
    rw [hyT]
    exact CategoryTheory.IsIso.of_isIso_comp_left (S.residueFieldCongr hxy.symm).inv
      (g.residueFieldMap y)
  have : IsIso ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y) := inferInstance
  have hTiso : IsIso T.tensorInl := by
    show IsIso (CategoryTheory.Limits.pushout.inl _ _)
    exact CategoryTheory.Limits.pushout_inl_iso_of_right_iso _ _
  exact (@subsingleton_spec_of_isIso_of_field (A.residueField T.x) inferInstance T.tensor
    T.tensorInl hTiso).elim _ _

/-- In a fibre product `X ×_Y Y'`, if the left morphism induces an isomorphism on residue
fields at the image of `z`, then so does the projection to `Y'`. -/
private lemma isIso_pullback_snd_residueFieldMap
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (z : ↥(pullback f g))
    (hfx : IsIso (f.residueFieldMap (pullback.fst f g z))) :
    IsIso ((pullback.snd f g).residueFieldMap z) := by
  let T : Scheme.Pullback.Triplet f g := Scheme.Pullback.Triplet.ofPoint z
  let p := Scheme.Pullback.SpecOfPoint z
  have : IsIso (f.residueFieldMap T.x) := hfx
  have : IsIso (Y.residueFieldCongr T.hx).hom := (Y.residueFieldCongr T.hx).isIso_hom
  have : IsIso ((Y.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x) := inferInstance
  have : IsIso T.tensorInr := by
    show IsIso (pushout.inr ((Y.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
      ((Y.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y))
    exact CategoryTheory.Limits.pushout_inr_iso_of_left_iso _ _
  have : Field T.tensor :=
    (MulEquiv.isField (Field.toIsField (Y'.residueField T.y))
      (asIso T.tensorInr).symm.commRingCatIsoToRingEquiv.toMulEquiv).toField
  have : IsOpenImmersion (Spec.map T.tensorInr) := inferInstance
  have hp := Scheme.Pullback.isIso_residueFieldMap_specTensorTo_comp_residueFieldIso T p
  have : IsIso (T.SpecTensorTo.residueFieldMap p) :=
    IsIso.of_isIso_comp_right _ (Scheme.Spec.residueFieldIso T.tensor p).hom
  have hptComp : (T.SpecTensorTo ≫ pullback.snd f g) p =
      (Spec.map T.tensorInr ≫ Y'.fromSpecResidueField T.y) p := by
    rw [T.specTensorTo_snd]
  have hcomp : IsIso ((pullback.snd f g).residueFieldMap (T.SpecTensorTo p) ≫
      T.SpecTensorTo.residueFieldMap p) := by
    rw [← Scheme.residueFieldMap_comp, Scheme.Hom.residueFieldMap_congr T.specTensorTo_snd p,
      Scheme.residueFieldMap_comp]
    have hIsoFrom := isIso_residueFieldMap_fromSpecResidueField Y' T.y (Spec.map T.tensorInr p)
    have : IsIso ((Y'.fromSpecResidueField T.y).residueFieldMap (Spec.map T.tensorInr p)) :=
      hIsoFrom
    have : IsIso ((Spec.map T.tensorInr).residueFieldMap p) := inferInstance
    show IsIso ((Y'.residueFieldCongr hptComp).hom ≫
      (Y'.fromSpecResidueField T.y).residueFieldMap (Spec.map T.tensorInr p) ≫
        (Spec.map T.tensorInr).residueFieldMap p)
    exact IsIso.comp_isIso' (Y'.residueFieldCongr hptComp).isIso_hom
      (IsIso.comp_isIso' hIsoFrom inferInstance)
  have hIsoAtPoint : IsIso ((pullback.snd f g).residueFieldMap (T.SpecTensorTo p)) :=
    IsIso.of_isIso_comp_right ((pullback.snd f g).residueFieldMap (T.SpecTensorTo p))
      (T.SpecTensorTo.residueFieldMap p)
  rwa [Scheme.Pullback.SpecTensorTo_SpecOfPoint z] at hIsoAtPoint

/-- In a fibre product `X ×_Y Y'`, if the right morphism induces an isomorphism on residue
fields at the image of `z`, then so does the projection to `X`. -/
private lemma isIso_pullback_fst_residueFieldMap
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (z : ↥(pullback f g))
    (hgy : IsIso (g.residueFieldMap (pullback.snd f g z))) :
    IsIso ((pullback.fst f g).residueFieldMap z) := by
  have hz : pullback.fst g f ((pullbackSymmetry f g).hom z) = pullback.snd f g z := by
    rw [← Scheme.Hom.comp_apply, CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst]
  have hsecond : IsIso ((pullback.snd g f).residueFieldMap ((pullbackSymmetry f g).hom z)) :=
    isIso_pullback_snd_residueFieldMap g f _ (by rwa [hz])
  have hcomp := isIso_comp_residueFieldMap_of_iso (pullbackSymmetry f g).hom (pullback.snd g f) z
    hsecond
  rwa [pullbackSymmetry_hom_comp_snd] at hcomp

/-- In a cartesian square, if the right-hand morphism induces an isomorphism on residue fields
at the image of `p`, then so does the top morphism. -/
private lemma isIso_residueFieldMap_of_isPullback {P X Y S : Scheme.{u}} {i : P ⟶ X} {j : P ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (H : IsPullback i j f g) (p : P)
    (hg : IsIso (g.residueFieldMap (j p))) : IsIso (i.residueFieldMap p) := by
  have hqj : pullback.snd f g (H.isoPullback.hom p) = j p := by
    rw [← Scheme.Hom.comp_apply, H.isoPullback_hom_snd]
  have hfst : IsIso ((pullback.fst f g).residueFieldMap (H.isoPullback.hom p)) :=
    isIso_pullback_fst_residueFieldMap f g _ (by rwa [hqj])
  have hcomp := isIso_comp_residueFieldMap_of_iso H.isoPullback.hom (pullback.fst f g) p hfst
  rwa [H.isoPullback_hom_fst] at hcomp

/-- In a cartesian square, a point is determined by its two images as soon as the right-hand
morphism induces an isomorphism on residue fields at the relevant points. -/
private lemma eq_of_isPullback_of_isIso_residueFieldMap {P A B S : Scheme.{u}} {i : P ⟶ A}
    {j : P ⟶ B} {f : A ⟶ S} {g : B ⟶ S} (H : IsPullback i j f g) (x : A) (y : B)
    (hxy : f x = g y) (hfield : IsIso ((S.residueFieldCongr hxy.symm).inv ≫ g.residueFieldMap y))
    {p q : P} (hp : i p = x) (hq : j p = y) (hp' : i q = x) (hq' : j q = y) : p = q :=
  (Scheme.Hom.homeomorph H.isoPullback.hom).injective <|
    pullback_point_eq_of_isIso_residueFieldMap f g x y hxy hfield (H.isoPullback.hom p)
      (H.isoPullback.hom q) (by rwa [← Scheme.Hom.comp_apply, H.isoPullback_hom_fst])
      (by rwa [← Scheme.Hom.comp_apply, H.isoPullback_hom_snd])
      (by rwa [← Scheme.Hom.comp_apply, H.isoPullback_hom_fst])
      (by rwa [← Scheme.Hom.comp_apply, H.isoPullback_hom_snd])

/-- The residue-field maps around a commutative square of schemes commute, once the residue
fields at equal points are identified. -/
private lemma residueFieldMap_comp_eq_of_comm {P Y S' S : Scheme.{u}} {pY : P ⟶ Y} {g' : P ⟶ S'}
    {g : Y ⟶ S} {h : S' ⟶ S} (w : pY ≫ g = g' ≫ h) {s : S} {t : S'} {y : Y} {p : P}
    (ht : h t = s) (hgy : g y = s) (hp' : g' p = t) (hpy : pY p = y) :
    ((S.residueFieldCongr ht).inv ≫ h.residueFieldMap t) ≫
        (S'.residueFieldCongr hp').inv ≫ g'.residueFieldMap p =
      ((S.residueFieldCongr hgy).inv ≫ g.residueFieldMap y) ≫
        (Y.residueFieldCongr hpy).inv ≫ pY.residueFieldMap p := by
  subst ht hp' hpy
  have hsq := Scheme.Hom.residueFieldMap_congr w p
  simp only [Scheme.residueFieldMap_comp] at hsq
  change g.residueFieldMap (pY p) ≫ pY.residueFieldMap p =
    (S.residueFieldCongr hgy).hom ≫ h.residueFieldMap (g' p) ≫ g'.residueFieldMap p at hsq
  simp [hsq]

/-- Pure transcendence is transported along a ring isomorphism of the base field compatible
with the two algebra structures. -/
private lemma purelyTranscendental_of_ringEquiv_base {k k' K : Type u} [Field k] [Field k']
    [Field K] [Algebra k K] [Algebra k' K] (e : k' ≃+* k)
    (he : ∀ a, algebraMap k' K a = algebraMap k K (e a))
    [PurelyTranscendental k K] : PurelyTranscendental k' K := by
  obtain ⟨s, hind, hgen⟩ := PurelyTranscendental.exists_basis k K
  refine ⟨s, ?_, ?_⟩
  · show AlgebraicIndependent k' (fun i : s ↦ (i : K))
    refine algebraicIndependent_iff.2 fun p hp => ?_
    have hmap : MvPolynomial.aeval (fun i : s ↦ (i : K))
        (MvPolynomial.map e.toRingHom p) = 0 := by
      show MvPolynomial.eval₂ (algebraMap k K) (fun i : s ↦ (i : K))
        (MvPolynomial.map e.toRingHom p) = 0
      calc _ = MvPolynomial.eval₂ ((algebraMap k K).comp e.toRingHom)
              (fun i : s ↦ (i : K)) p :=
            MvPolynomial.eval₂_map e.toRingHom (fun i : s ↦ (i : K)) (algebraMap k K) p
        _ = MvPolynomial.eval₂ (algebraMap k' K) (fun i : s ↦ (i : K)) p := by
            congr 1
            ext a
            rw [RingHom.comp_apply]
            exact (he a).symm
        _ = 0 := by simpa [MvPolynomial.aeval_def] using hp
    exact (MvPolynomial.map_injective (f := e.toRingHom) e.injective)
      (by simpa using hind.eq_zero_of_aeval_eq_zero _ hmap)
  · rw [eq_top_iff]
    intro x _
    have hx : x ∈ IntermediateField.adjoin k s := by
      rw [hgen]
      trivial
    refine IntermediateField.adjoin_induction (F := k) (E := K) (s := s)
      (motive := fun y _ ↦ y ∈ IntermediateField.adjoin k' s)
      (fun y hy ↦ IntermediateField.subset_adjoin k' s hy) (fun a ↦ ?_)
      (fun _ _ _ _ hx hy ↦ add_mem hx hy) (fun _ _ hx ↦ inv_mem hx)
      (fun _ _ _ _ hx hy ↦ mul_mem hx hy) hx
    have hval : algebraMap k K a = algebraMap k' K (e.symm a) := by
      simpa using (he (e.symm a)).symm
    rw [hval]
    exact (IntermediateField.adjoin k' s).algebraMap_mem _

/-- In a cartesian square whose bottom morphism induces an isomorphism of residue fields, pure
transcendence of the residue field extension of the right-hand morphism passes to the left-hand
morphism. -/
private lemma purelyTranscendental_residueField_of_isPullback {P Y S' S : Scheme.{u}}
    {pY : P ⟶ Y} {g' : P ⟶ S'} {g : Y ⟶ S} {h : S' ⟶ S} (H : IsPullback pY g' g h)
    {s : S} {t : S'} {y : Y} {p : P} (ht : h t = s) (hgy : g y = s) (hp' : g' p = t)
    (hpy : pY p = y) [IsIso ((S.residueFieldCongr ht).inv ≫ h.residueFieldMap t)]
    (hPT : letI : Algebra (S.residueField s) (Y.residueField y) :=
        ((S.residueFieldCongr hgy).inv ≫ g.residueFieldMap y).hom.toAlgebra
      PurelyTranscendental (S.residueField s) (Y.residueField y)) :
    letI : Algebra (S'.residueField t) (P.residueField p) :=
      ((S'.residueFieldCongr hp').inv ≫ g'.residueFieldMap p).hom.toAlgebra
    PurelyTranscendental (S'.residueField t) (P.residueField p) := by
  have hmap : IsIso (h.residueFieldMap t) :=
    IsIso.of_isIso_comp_left (S.residueFieldCongr ht).inv (h.residueFieldMap t)
  have hmapY : IsIso (h.residueFieldMap (g' p)) := by
    rw [hp']
    exact hmap
  have hβraw : IsIso (pY.residueFieldMap p) := isIso_residueFieldMap_of_isPullback H p hmapY
  set K := S.residueField s
  set K' := S'.residueField t
  set L := Y.residueField y
  set L' := P.residueField p
  set α : CommRingCat.of K ⟶ CommRingCat.of K' :=
    (S.residueFieldCongr ht).inv ≫ h.residueFieldMap t
  set φold : CommRingCat.of K ⟶ CommRingCat.of L :=
    (S.residueFieldCongr hgy).inv ≫ g.residueFieldMap y
  set φnew : CommRingCat.of K' ⟶ CommRingCat.of L' :=
    (S'.residueFieldCongr hp').inv ≫ g'.residueFieldMap p
  set β : CommRingCat.of L ⟶ CommRingCat.of L' :=
    (Y.residueFieldCongr hpy).inv ≫ pY.residueFieldMap p with hβ
  have hβiso : IsIso β := by
    rw [hβ]
    infer_instance
  let eTop : L ≃+* L' := (asIso β).commRingCatIsoToRingEquiv
  let eBase : K' ≃+* K := (asIso α).symm.commRingCatIsoToRingEquiv
  let : Algebra K L := φold.hom.toAlgebra
  have hPTold : PurelyTranscendental K L := hPT
  let : Algebra K L' := (β.hom.comp φold.hom).toAlgebra
  let : Algebra K' L' := φnew.hom.toAlgebra
  have hPTmid : PurelyTranscendental K L' :=
    (AlgEquiv.ofRingEquiv (f := eTop) (fun a => rfl)).purelyTranscendental
  have hpath : α ≫ φnew = φold ≫ β := residueFieldMap_comp_eq_of_comm H.w ht hgy hp' hpy
  have hcompat : ∀ a : K', algebraMap K' L' a = algebraMap K L' (eBase a) := by
    intro a
    have hbase : α.hom (eBase a) = a := by
      show (asIso α).hom ((asIso α).inv a) = a
      simp
    calc φnew.hom a = (α ≫ φnew).hom (eBase a) := (congrArg φnew.hom hbase).symm
      _ = (φold ≫ β).hom (eBase a) :=
        congrArg (fun q : CommRingCat.of K ⟶ CommRingCat.of L' => q.hom (eBase a)) hpath
      _ = algebraMap K L' (eBase a) := rfl
  exact purelyTranscendental_of_ringEquiv_base eBase hcompat

end ResidueFields

section Fibre

variable {X S S' : Scheme.{u}}

/-- The comparison morphism from the fibre of a base change over `s'` to the fibre of the
original morphism over the image of `s'`. -/
private def fiberBaseChangeMap (f : X ⟶ S) (h : S' ⟶ S) (s' : S') :
    (pullback.snd f h).fiber s' ⟶ f.fiber (h s') :=
  pullback.map _ _ _ _ (pullback.fst f h) (Spec.map (h.residueFieldMap s')) h
    (IsPullback.of_hasPullback f h).w.symm (by simp)

/-- The comparison morphism is an isomorphism as soon as the base change induces an isomorphism
of residue fields at `s'`. -/
private lemma isIso_fiberBaseChangeMap (f : X ⟶ S) (h : S' ⟶ S) (s' : S')
    [IsIso (h.residueFieldMap s')] : IsIso (fiberBaseChangeMap f h s') := by
  have : IsIso (Spec.map (h.residueFieldMap s')) :=
    (Scheme.Spec.mapIso (asIso (h.residueFieldMap s')).op).isIso_hom
  have : HasPullback (f.fiberToSpecResidueField (h s'))
      (Spec.map (h.residueFieldMap s')) :=
    CategoryTheory.Limits.hasPullback_of_right_iso _ _
  have H := isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f h) s'
  have : IsIso (pullback.fst (f.fiberToSpecResidueField (h s'))
      (Spec.map (h.residueFieldMap s'))) :=
    CategoryTheory.Limits.pullback_fst_iso_of_right_iso _ _
  have hh : H.isoPullback.hom ≫ pullback.fst (f.fiberToSpecResidueField (h s'))
      (Spec.map (h.residueFieldMap s')) = fiberBaseChangeMap f h s' := H.isoPullback_hom_fst
  let eFst : pullback (f.fiberToSpecResidueField (h s')) (Spec.map (h.residueFieldMap s')) ≅
      f.fiber (h s') :=
    asIso (pullback.fst (f.fiberToSpecResidueField (h s')) (Spec.map (h.residueFieldMap s')))
  rw [← hh]
  show IsIso (H.isoPullback ≪≫ eFst).hom
  infer_instance

/-- The comparison morphism of fibres is compatible with the two inclusions of the fibres. -/
private lemma fiberBaseChangeMap_comp_fiberι (f : X ⟶ S) (h : S' ⟶ S) (s' : S') :
    fiberBaseChangeMap f h s' ≫ f.fiberι (h s') =
      (pullback.snd f h).fiberι s' ≫ pullback.fst f h :=
  pullback.lift_fst _ _ _

/-- The local dimension condition at a point of a fibre does not depend on how the base point
is written. -/
private lemma exists_fiber_dimension_of_eq (f : X ⟶ S) (F : X.Modules) {x : X} {s : S}
    (hxs : f x = s)
    (hmem : f.asFiber x ∈ SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
    (hdim : topologicalKrullDimAt
        (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
        ⟨f.asFiber x, hmem⟩ =
      topologicalKrullDim
        (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))) :
    ∃ hmem' : (f.fiberHomeo s).symm ⟨x, hxs⟩ ∈
        SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F),
      topologicalKrullDimAt (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F))
          ⟨_, hmem'⟩ =
        topologicalKrullDim
          (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) := by
  subst hxs
  exact ⟨hmem, hdim⟩

/-- A point `x'` of a base change lies in the support of the pulled-back module on its fibre,
with local dimension the dimension of that support, as soon as this holds for its image `x` in
the fibre over the image of `x'` and the base change induces an isomorphism of residue fields. -/
private lemma exists_fiber_dimension_baseChange (f : X ⟶ S) (h : S' ⟶ S) (F : X.Modules)
    [F.IsFiniteType] [((Scheme.Modules.pullback (pullback.fst f h)).obj F).IsFiniteType]
    (x' : ↥(pullback f h)) {x : X} (hx : pullback.fst f h x' = x)
    (hxy : f x = h (pullback.snd f h x')) [IsIso (h.residueFieldMap (pullback.snd f h x'))]
    (hmem : (f.fiberHomeo (h (pullback.snd f h x'))).symm ⟨x, hxy⟩ ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (h (pullback.snd f h x')))).obj F))
    (hdim : topologicalKrullDimAt
        (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (h (pullback.snd f h x')))).obj F))
        ⟨_, hmem⟩ =
      topologicalKrullDim
        (SheafOfModules.supp
          ((Scheme.Modules.pullback (f.fiberι (h (pullback.snd f h x')))).obj F))) :
    ∃ hmem' : (pullback.snd f h).asFiber x' ∈ SheafOfModules.supp
        ((Scheme.Modules.pullback ((pullback.snd f h).fiberι (pullback.snd f h x'))).obj
          ((Scheme.Modules.pullback (pullback.fst f h)).obj F)),
      topologicalKrullDimAt (SheafOfModules.supp
          ((Scheme.Modules.pullback ((pullback.snd f h).fiberι (pullback.snd f h x'))).obj
            ((Scheme.Modules.pullback (pullback.fst f h)).obj F))) ⟨_, hmem'⟩ =
        topologicalKrullDim (SheafOfModules.supp
          ((Scheme.Modules.pullback ((pullback.snd f h).fiberι (pullback.snd f h x'))).obj
            ((Scheme.Modules.pullback (pullback.fst f h)).obj F))) := by
  have : IsIso (fiberBaseChangeMap f h (pullback.snd f h x')) :=
    isIso_fiberBaseChangeMap f h (pullback.snd f h x')
  let fiberIso : (pullback.snd f h).fiber (pullback.snd f h x') ≅
      f.fiber (h (pullback.snd f h x')) :=
    asIso (fiberBaseChangeMap f h (pullback.snd f h x'))
  have fiberIso_fst : fiberIso.hom ≫ f.fiberι (h (pullback.snd f h x')) =
      (pullback.snd f h).fiberι (pullback.snd f h x') ≫ pullback.fst f h :=
    fiberBaseChangeMap_comp_fiberι f h (pullback.snd f h x')
  set oldFiberModule := (Scheme.Modules.pullback
    (f.fiberι (h (pullback.snd f h x')))).obj F with hOld
  set newFiberModule := (Scheme.Modules.pullback
    ((pullback.snd f h).fiberι (pullback.snd f h x'))).obj
      ((Scheme.Modules.pullback (pullback.fst f h)).obj F) with hNew
  have supp_old : SheafOfModules.supp oldFiberModule =
      ⇑(f.fiberι (h (pullback.snd f h x'))) ⁻¹' SheafOfModules.supp F := by
    rw [hOld, Stacks.Modules.supp_pullback]
  have supp_new : SheafOfModules.supp newFiberModule =
      ⇑((pullback.snd f h).fiberι (pullback.snd f h x')) ⁻¹'
        (⇑(pullback.fst f h) ⁻¹' SheafOfModules.supp F) := by
    rw [hNew, Stacks.Modules.supp_pullback, Stacks.Modules.supp_pullback]
  let oldPoint : f.fiber (h (pullback.snd f h x')) :=
    (f.fiberHomeo (h (pullback.snd f h x'))).symm ⟨x, hxy⟩
  have fiberIso_point : fiberIso.hom ((pullback.snd f h).asFiber x') = oldPoint := by
    refine (f.fiberι (h (pullback.snd f h x'))).isEmbedding.injective ?_
    rw [← Scheme.Hom.comp_apply, fiberIso_fst]
    simp [oldPoint, Scheme.Hom.fiberι_asFiber, hx]
  have hx_support : x ∈ SheafOfModules.supp F := by
    have hm := hmem
    rw [supp_old, Set.mem_preimage] at hm
    simpa using hm
  have new_support : (pullback.snd f h).asFiber x' ∈ SheafOfModules.supp newFiberModule := by
    rw [supp_new]
    simpa [Scheme.Hom.fiberι_asFiber, hx] using hx_support
  have support_homeo_iff (a : (pullback.snd f h).fiber (pullback.snd f h x')) :
      a ∈ SheafOfModules.supp newFiberModule ↔
        fiberIso.hom a ∈ SheafOfModules.supp oldFiberModule := by
    rw [supp_new, supp_old]
    show (pullback.fst f h ((pullback.snd f h).fiberι _ a) ∈ SheafOfModules.supp F) ↔
      f.fiberι _ (fiberIso.hom a) ∈ SheafOfModules.supp F
    have hp := congrArg
      (fun k : (pullback.snd f h).fiber (pullback.snd f h x') ⟶ X => k a) fiberIso_fst
    simpa only [Scheme.Hom.comp_apply] using hp.symm ▸ Iff.rfl
  let supportHomeo := fiberIso.hom.homeomorph.subtype support_homeo_iff
  have support_point_eq :
      supportHomeo ⟨(pullback.snd f h).asFiber x', new_support⟩ = ⟨oldPoint, hmem⟩ :=
    Subtype.ext fiberIso_point
  refine ⟨new_support, ?_⟩
  calc _ = topologicalKrullDimAt (SheafOfModules.supp oldFiberModule) ⟨oldPoint, hmem⟩ := by
        simpa [support_point_eq] using topologicalKrullDimAt_eq_of_homeomorph supportHomeo
          ⟨(pullback.snd f h).asFiber x', new_support⟩
    _ = topologicalKrullDim (SheafOfModules.supp oldFiberModule) := hdim
    _ = _ := (IsHomeomorph.topologicalKrullDim_eq _ supportHomeo.isHomeomorph).symm

end Fibre

namespace OneStepDevissageAt

/-- The fibre of the base-changed finite map over the new distinguished point `y'` is the single
point `z'`. -/
private lemma baseChange_fiber_eq_singleton {X S S' : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    {x : X} [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (D : OneStepDevissageAt f F x) {h : S' ⟶ S} [IsAffine S'] {x' : ↥(pullback f h)}
    {hs : h (pullback.snd f h x') = f x}
    (B : OneStepDevissage.BaseChangeData f F (f x) (pullback.snd f h x') h hs D.toOneStepDevissage)
    (huniq : ∀ p, pullback.fst f h p = x → pullback.snd f h p = pullback.snd f h x' → x' = p) :
    letI := B.locallyOfFiniteType
    letI := B.quasicoherent
    letI := B.finiteType
    ∀ {z' : B.devissage.Z} {y' : B.devissage.Y}, B.devissage.i z' = x' →
      B.devissage.π z' = y' → B.pY y' = D.y → B.devissage.g y' = pullback.snd f h x' →
      B.devissage.π ⁻¹' {y'} = {z'} := by
  intro z' y' hiz hpi_z hy hys
  have := B.locallyOfFiniteType
  have := B.quasicoherent
  have := B.finiteType
  refine Set.ext fun w => ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  refine ⟨fun hwy => ?_, fun hwz => by simp [hwz, hpi_z]⟩
  have hpZ : B.pZ w = D.z := by
    have hproj : B.pY (B.devissage.π w) = D.toOneStepDevissage.π (B.pZ w) :=
      (apply_eq_of_comp_eq B.z_square.w w).symm
    have hd : B.pZ w ∈ D.toOneStepDevissage.π ⁻¹' {D.y} := by
      simpa [Set.mem_preimage] using hproj.symm.trans (by simpa [hwy] using hy)
    simpa using (show B.pZ w ∈ ({D.z} : Set D.toOneStepDevissage.Z) by
      simpa [D.fiber_eq_singleton] using hd)
  have hxw : pullback.fst f h (B.devissage.i w) = x := by
    calc pullback.fst f h (B.devissage.i w) = D.toOneStepDevissage.i (B.pZ w) :=
          (apply_eq_of_comp_eq B.x_square.w w).symm
      _ = x := by rw [hpZ, D.i_z]
  have hsw : pullback.snd f h (B.devissage.i w) = pullback.snd f h x' := by
    rw [apply_eq_of_comp_eq B.devissage.over_base w, hwy, hys]
  exact B.devissage.closed_immersion.isClosedEmbedding.injective
    ((huniq _ hxw hsw).symm.trans hiz.symm)

/-- **Stacks Project, Tag 05H8.** A one-step dévissage at a point survives an affine pointed
base change which induces an isomorphism of residue fields: for the unique points `x'`, `z'`,
`y'` of the base-changed schemes lying over the original distinguished points and over the new
base point, the base-changed dévissage is a one-step dévissage at `x'` with distinguished
points `z'` and `y'`. -/
@[stacks 05H8]
theorem exists_baseChange {X S S' : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (D : OneStepDevissageAt f F x)
    (s' : S') (h : S' ⟶ S) (hs : h s' = f x) [IsAffine S']
    [IsIso ((S.residueFieldCongr hs).inv ≫ h.residueFieldMap s')]
    (B : OneStepDevissage.BaseChangeData f F (f x) s' h hs D.toOneStepDevissage) :
    letI := B.locallyOfFiniteType
    letI := B.quasicoherent
    letI := B.finiteType
    ∀ (x' : ↥(pullback f h)) (_ : pullback.fst f h x' = x)
      (_ : pullback.snd f h x' = s') (z' : B.devissage.Z) (_ : B.pZ z' = D.z)
      (_ : (B.devissage.π ≫ B.devissage.g) z' = s') (y' : B.devissage.Y)
      (_ : B.pY y' = D.y) (_ : B.devissage.g y' = s'),
      ∃ E : OneStepDevissageAt (pullback.snd f h)
          ((Scheme.Modules.pullback (pullback.fst f h)).obj F) x',
        HEq E.toOneStepDevissage B.devissage ∧ HEq E.z z' ∧ HEq E.y y' := by
  intro x' hx hxs z' hz hzs y' hy hys
  have := B.locallyOfFiniteType
  have := B.quasicoherent
  have := B.finiteType
  subst s'
  have hxy : f x = h (pullback.snd f h x') := by
    simpa [hx] using apply_eq_of_comp_eq (pullback.condition (f := f) (g := h)) x'
  have hfield : IsIso ((S.residueFieldCongr hxy.symm).inv ≫
      h.residueFieldMap (pullback.snd f h x')) := by
    simpa using (inferInstance : IsIso ((S.residueFieldCongr hs).inv ≫
      h.residueFieldMap (pullback.snd f h x')))
  have huniq (p : ↥(pullback f h)) (hp : pullback.fst f h p = x)
      (hq : pullback.snd f h p = pullback.snd f h x') : x' = p :=
    pullback_point_eq_of_isIso_residueFieldMap f h x _ hxy hfield x' p hx rfl hp hq
  have hfst_i : pullback.fst f h (B.devissage.i z') = x := by
    rw [← apply_eq_of_comp_eq B.x_square.w z', hz, D.i_z]
  have hsnd_i : pullback.snd f h (B.devissage.i z') = pullback.snd f h x' :=
    (apply_eq_of_comp_eq B.devissage.over_base z').trans hzs
  have hbaseY : D.toOneStepDevissage.g D.y = h (pullback.snd f h x') := D.g_y.trans hs.symm
  have hfieldY : IsIso ((S.residueFieldCongr hbaseY.symm).inv ≫
      h.residueFieldMap (pullback.snd f h x')) := by
    simpa [hbaseY, D.g_y] using (inferInstance : IsIso ((S.residueFieldCongr hs).inv ≫
      h.residueFieldMap (pullback.snd f h x')))
  have hp_pi : B.pY (B.devissage.π z') = D.y := by
    rw [← apply_eq_of_comp_eq B.z_square.w z', hz, D.π_z]
  have hpi_z : B.devissage.π z' = y' :=
    eq_of_isPullback_of_isIso_residueFieldMap B.y_square D.y (pullback.snd f h x') hbaseY
      hfieldY hp_pi (by simpa only [Scheme.Hom.comp_apply] using hzs) hy hys
  have : IsIso (h.residueFieldMap (pullback.snd f h x')) :=
    IsIso.of_isIso_comp_left (S.residueFieldCongr hxy.symm).inv _
  obtain ⟨hmem₀, hdim₀⟩ := exists_fiber_dimension_of_eq f F hxy D.mem_fiber_support D.dimension
  obtain ⟨hmem, hdim⟩ := exists_fiber_dimension_baseChange f h F x' hx hxy hmem₀ hdim₀
  have hiz : B.devissage.i z' = x' := (huniq _ hfst_i hsnd_i).symm
  exact ⟨{ toOneStepDevissage := B.devissage, mem_fiber_support := hmem, dimension := hdim,
           z := z', y := y', i_z := hiz, π_z := hpi_z, g_y := hys,
           fiber_eq_singleton := baseChange_fiber_eq_singleton D B huniq hiz hpi_z hy hys,
           residueField_purelyTranscendental :=
             purelyTranscendental_residueField_of_isPullback B.y_square hs D.g_y hys hy
               D.residueField_purelyTranscendental }, HEq.rfl, HEq.rfl, HEq.rfl⟩

end OneStepDevissageAt

end AlgebraicGeometry

end
