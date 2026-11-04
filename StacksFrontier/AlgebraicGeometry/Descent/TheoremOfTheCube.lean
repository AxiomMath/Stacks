module

public import StacksFrontier.AlgebraicGeometry.Descent.DescentLocusTriviality0BF3
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The theorem of the cube

Let `S` be a scheme, let `X`, `Y` and `Z` be schemes over `S` with sections `x : S ⟶ X` and
`y : S ⟶ Y` of the structure morphisms, and let `L` be an invertible module on
`X ×_S Y ×_S Z`. [Stacks, Tag 0BF4](https://stacks.math.columbia.edu/tag/0BF4) says that `L` is
trivial as soon as `X ⟶ S` and `Y ⟶ S` are flat proper morphisms of finite presentation with
geometrically integral fibres, the pullbacks of `L` along `x × 1 × 1` and `1 × y × 1` are
trivial, the restriction of `L` to one fibre `X ×_S Y ×_S z` is trivial, and `Z` is connected.

The argument of that theorem, once the three lemmas it cites are granted, is that the descent
locus of `L` along the projection `p : X ×_S Y ×_S Z ⟶ Z` is open and closed and nonempty, hence
all of `Z` by connectedness, so `L` is pulled back from `Z`; the section `(x ∘ h, y ∘ h, 1)` of
`p` then trivialises the module it is pulled back from. That argument is what is proved here, for
an arbitrary morphism `p` and an arbitrary descent locus of `L` along it.

## Main results

* `AlgebraicGeometry.IsDescentLocus.mem_range_hom_of_isTrivial_fiber`: a point over whose residue
  field `L` becomes trivial lies in the descent locus.
* `AlgebraicGeometry.IsDescentLocus.isOpen_range_hom`: a descent locus that contains a
  neighbourhood of each of its points has open image.
* `AlgebraicGeometry.IsDescentLocus.isOpenImmersion_hom`: such a descent locus is an open
  immersion, when it is a closed immersion.
* `AlgebraicGeometry.IsDescentLocus.isIso_hom_of_connectedSpace`: over a connected base, a closed
  nonempty descent locus of that kind is the whole base.
* `AlgebraicGeometry.IsDescentLocus.isTrivial_of_isIso_hom`: a module whose descent locus is the
  whole base, and which is trivial along one section of the morphism, is trivial.
* `AlgebraicGeometry.SheafOfModules.isTrivial_of_isTrivial_face_and_fiber`: the theorem of the
  cube, from a descent locus for `p` that is closed and contains a neighbourhood of each of its
  points.

## Implementation notes

The triple fibre product is `pullback (pullback.fst f g ≫ f) h`, the face `x × 1 × 1` is the
morphism `pullback.lift` builds from the section `x`, the fibre `X ×_S Y ×_S z` is the base change
of `p` along `Z.fromSpecResidueField z`, and triviality is
`AlgebraicGeometry.SheafOfModules.IsTrivial`.

Three inputs of the source's proof are not available in this library and so appear as explicit
hypotheses on the descent locus `D` of `L` along `p`:

* that the descent condition is *represented* at all, which is
  `AlgebraicGeometry.IsDescentLocus` and is the conclusion of
  [Stacks, Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP);
* that `D.hom` is a *closed* immersion, which is
  [Stacks, Tag 0BF0](https://stacks.math.columbia.edu/tag/0BF0);
* that each point of `D` has a neighbourhood in `Z` over which `L` descends, which is what
  [Stacks, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3) supplies — after rewriting `p` as
  the projection `(X ×_S Z) ×_Z (Y ×_S Z) ⟶ Z` — and which rests in turn on
  [Stacks, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2).

Granting those three, nothing else is needed: the flatness, properness and finite presentation of
`f` and `g`, the geometric integrality of their fibres, the invertibility of `L` and the second
face hypothesis are used in the source only to verify the hypotheses of those three lemmas, and so
appear in none of the results here. The `@[stacks 0BF4]` attribute on
`AlgebraicGeometry.SheafOfModules.isTrivial_of_isTrivial_face_and_fiber` therefore carries the
scope label `"assuming the conclusions of Tags 0BDP, 0BF0 and 0BF3 for the descent locus"`: the
tag asserts triviality outright, whereas what is proved here is its reduction to those three
inputs, and the label records that gap wherever the attribute is read.

## References

* [Stacks Project, Tag 0BF4](https://stacks.math.columbia.edu/tag/0BF4)
* [Stacks Project, Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP)
* [Stacks Project, Tag 0BF0](https://stacks.math.columbia.edu/tag/0BF0)
* [Stacks Project, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- Pointwise form of `k ≫ φ = m`. -/
private theorem apply_eq_of_comp_eq {W X Y : Scheme.{u}} {k : W ⟶ X} {φ : X ⟶ Y} {m : W ⟶ Y}
    (h : k ≫ φ = m) (w : W) : φ (k w) = m w := by
  rw [← Scheme.Hom.comp_apply, h]

/-- A point `x` lies in the range of `φ` if `Spec κ(x) ⟶ X` factors through `φ`. -/
theorem mem_range_of_comp_eq_fromSpecResidueField {W X : Scheme.{u}} {φ : W ⟶ X} {x : X}
    (k : Spec (X.residueField x) ⟶ W) (hk : k ≫ φ = X.fromSpecResidueField x) :
    x ∈ Set.range φ :=
  ⟨k (IsLocalRing.closedPoint (X.residueField x)),
    (apply_eq_of_comp_eq hk _).trans (Scheme.fromSpecResidueField_apply x _)⟩

namespace IsDescentLocus

variable {Z P : Scheme.{u}} {p : P ⟶ Z}
  {L : _root_.SheafOfModules.{u} (structureSheafRing P.toRingedSpace)} {D : Over Z}

/-- **A point over whose residue field the module becomes trivial lies in the descent locus.**
If the pullback of `L` to `P ×_Z Spec κ(z)` is trivial, then `z` lies in the image of `D`. -/
theorem mem_range_hom_of_isTrivial_fiber (hD : IsDescentLocus p L D) (z : Z)
    (hz : SheafOfModules.IsTrivial (pullback p (Z.fromSpecResidueField z)).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (pullback p (Z.fromSpecResidueField z)).IsSheaf)
      ((modulePullback
        (pullback.fst p (Z.fromSpecResidueField z)).toLRSHom.toShHom).obj L)) :
    z ∈ Set.range D.hom := by
  obtain ⟨k, hk⟩ := hD.factorsThrough_of_nonempty_iso_unit (Z.fromSpecResidueField z) hz
  exact mem_range_of_comp_eq_fromSpecResidueField k hk

/-- **A descent locus that contains a neighbourhood of each of its points factors each such
neighbourhood.** Each point `z` of the image of `D` has an open neighbourhood `U` whose inclusion
into `Z` factors through `D`. -/
theorem exists_hom_ι (hD : IsDescentLocus p L D)
    (hnbhd : ∀ z ∈ Set.range D.hom, ∃ U : Z.Opens, z ∈ U ∧ DescendsFromBase p L U.ι)
    {z : Z} (hz : z ∈ Set.range D.hom) :
    ∃ U : Z.Opens, z ∈ U ∧ ∃ k : U.toScheme ⟶ D.left, k ≫ D.hom = U.ι :=
  (hnbhd z hz).imp fun U => And.imp_right (hD.factorsThrough_iff U.ι).2

/-- **A descent locus that contains a neighbourhood of each of its points has open image.** -/
theorem isOpen_range_hom (hD : IsDescentLocus p L D)
    (hnbhd : ∀ z ∈ Set.range D.hom, ∃ U : Z.Opens, z ∈ U ∧ DescendsFromBase p L U.ι) :
    IsOpen (Set.range D.hom) := by
  refine isOpen_iff_forall_mem_open.2 fun z hz => ?_
  obtain ⟨U, hzU, k, hk⟩ := hD.exists_hom_ι hnbhd hz
  exact ⟨(U : Set Z), fun w hw => ⟨k ⟨w, hw⟩, (apply_eq_of_comp_eq hk _).trans (by simp)⟩,
    U.2, hzU⟩

/-- **A closed descent locus that contains a neighbourhood of each of its points is an open
immersion.** -/
theorem isOpenImmersion_hom (hD : IsDescentLocus p L D) (hclosed : IsClosedImmersion D.hom)
    (hnbhd : ∀ z ∈ Set.range D.hom, ∃ U : Z.Opens, z ∈ U ∧ DescendsFromBase p L U.ι) :
    IsOpenImmersion D.hom := by
  refine IsOpenImmersion.of_forall_source_exists D.hom hclosed.isClosedEmbedding.injective
    fun d => ?_
  obtain ⟨U, hzU, k, hk⟩ := hD.exists_hom_ι hnbhd ⟨d, rfl⟩
  let dpt : Spec (D.left.residueField d) ⟶ D.left := D.left.fromSpecResidueField d
  have hrange : Set.range (dpt ≫ D.hom) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨s, rfl⟩
    simpa [dpt] using hzU
  let spt : Spec (D.left.residueField d) ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι (dpt ≫ D.hom) hrange
  have hmem : d ∈ (pullback.fst D.hom U.ι).opensRange := by
    rw [Scheme.Hom.mem_opensRange]
    exact mem_range_of_comp_eq_fromSpecResidueField _
      (pullback.lift_fst dpt spt (IsOpenImmersion.lift_fac _ _ _).symm)
  refine ⟨pullback D.hom U.ι, pullback.fst D.hom U.ι, inferInstance, hmem, ?_⟩
  have hk' : k ≫ D.hom = 𝟙 U.toScheme ≫ U.ι := hk.trans (Category.id_comp _).symm
  let sect : U.toScheme ⟶ pullback D.hom U.ι := pullback.lift k (𝟙 U.toScheme) hk'
  have hsect : sect ≫ pullback.snd D.hom U.ι = 𝟙 U.toScheme :=
    pullback.lift_snd k (𝟙 U.toScheme) hk'
  have hsect' : pullback.snd D.hom U.ι ≫ sect = 𝟙 (pullback D.hom U.ι) := by
    refine (cancel_mono (pullback.snd D.hom U.ι)).1 ?_
    rw [Category.assoc, hsect, Category.comp_id, Category.id_comp]
  have : IsIso (pullback.snd D.hom U.ι) := ⟨⟨sect, hsect', hsect⟩⟩
  rw [pullback.condition]
  infer_instance

/-- **Over a connected base, a closed nonempty descent locus that contains a neighbourhood of
each of its points is the whole base.** That is, `D.hom` is an isomorphism. -/
theorem isIso_hom_of_connectedSpace (hD : IsDescentLocus p L D) [ConnectedSpace Z]
    (hclosed : IsClosedImmersion D.hom)
    (hnbhd : ∀ z ∈ Set.range D.hom, ∃ U : Z.Opens, z ∈ U ∧ DescendsFromBase p L U.ι)
    (hne : (Set.range D.hom).Nonempty) :
    IsIso D.hom := by
  have hclopen : IsClopen (Set.range D.hom) :=
    ⟨hclosed.isClosedEmbedding.isClosed_range, hD.isOpen_range_hom hnbhd⟩
  have := hD.isOpenImmersion_hom hclosed hnbhd
  refine isIso_of_isOpenImmersion_of_opensRange_eq_top D.hom (Opens.ext ?_)
  simpa [Scheme.Hom.coe_opensRange] using hclopen.eq_univ hne

/-- **A module whose descent locus is the whole base, and which is trivial along a section of the
morphism, is trivial.** If `D.hom` is an isomorphism, `δ` is a section of `p` and the pullback of
`L` along `δ` is trivial, then `L` is trivial. -/
theorem isTrivial_of_isIso_hom (hD : IsDescentLocus p L D) [IsIso D.hom]
    (δ : Z ⟶ P) (hδ : δ ≫ p = 𝟙 Z)
    (hδL : SheafOfModules.IsTrivial Z.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Z.IsSheaf)
      ((modulePullback δ.toLRSHom.toShHom).obj L)) :
    SheafOfModules.IsTrivial P.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) P.IsSheaf) L := by
  obtain ⟨N, _, ⟨e⟩⟩ := (hD.factorsThrough_iff (𝟙 Z)).1 ⟨inv D.hom, by simp⟩
  have hacond : (𝟙 P : P ⟶ P) ≫ p = p ≫ 𝟙 Z := by simp
  have hbcond : δ ≫ p = 𝟙 Z ≫ 𝟙 Z := by simp [hδ]
  let a : P ⟶ pullback p (𝟙 Z) := pullback.lift (𝟙 P) p hacond
  let b : Z ⟶ pullback p (𝟙 Z) := pullback.lift δ (𝟙 Z) hbcond
  have eComp : ∀ {T : Scheme.{u}} (u : pullback p (𝟙 Z) ⟶ T) (v : Z ⟶ T), b ≫ u = v →
      ∀ M : _root_.SheafOfModules.{u} (structureSheafRing T.toRingedSpace),
      (modulePullback v.toLRSHom.toShHom).obj M ≅
      (modulePullback b.toLRSHom.toShHom).obj ((modulePullback u.toLRSHom.toShHom).obj M) :=
    fun u v hv M => hv ▸ (modulePullbackComp b.toLRSHom.toShHom u.toLRSHom.toShHom).app M
  have eL := eComp (pullback.fst p (𝟙 Z)) δ (pullback.lift_fst δ (𝟙 Z) hbcond) L
  have eN := eComp (pullback.snd p (𝟙 Z)) (𝟙 Z) (pullback.lift_snd δ (𝟙 Z) hbcond) N
  have hN : SheafOfModules.IsTrivial Z.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Z.IsSheaf) N :=
    ⟨((modulePullbackId Z.toRingedSpace).app N).symm ≪≫ eN ≪≫
      (modulePullback b.toLRSHom.toShHom).mapIso e ≪≫ eL.symm ≪≫ hδL.some⟩
  have hLfst : SheafOfModules.IsTrivial (pullback p (𝟙 Z)).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (pullback p (𝟙 Z)).IsSheaf)
      ((modulePullback (pullback.fst p (𝟙 Z)).toLRSHom.toShHom).obj L) :=
    ⟨e.symm ≪≫ (SheafOfModules.isTrivial_modulePullback_scheme
      (pullback.snd p (𝟙 Z)) hN).some⟩
  exact ⟨((modulePullbackId P.toRingedSpace).app L).symm ≪≫
    (SheafOfModules.isTrivial_modulePullback_scheme_of_comp a (pullback.fst p (𝟙 Z)) (𝟙 P)
      (pullback.lift_fst (𝟙 P) p hacond) (L := L) hLfst).some⟩

end IsDescentLocus

namespace SheafOfModules

/-- **The theorem of the cube.** Let `f : X ⟶ S`, `g : Y ⟶ S` and `h : Z ⟶ S` be morphisms of
schemes, let `x` and `y` be sections of `f` and `g`, and let `L` be a sheaf of modules on
`X ×_S Y ×_S Z` whose pullback along the face `x × 1 × 1` is trivial and whose restriction to one
fibre `X ×_S Y ×_S z` is trivial. If `Z` is connected and `D` is a descent locus for `L` along the
projection to `Z` which is a closed immersion and contains a neighbourhood of each of its points,
then `L` is trivial. -/
@[stacks 0BF4 "assuming the conclusions of Tags 0BDP, 0BF0 and 0BF3 for the descent locus"]
theorem isTrivial_of_isTrivial_face_and_fiber {S X Y Z : Scheme.{u}} {D : Over Z}
    (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    (x : S ⟶ X) (hx : x ≫ f = 𝟙 S) (y : S ⟶ Y) (hy : y ≫ g = 𝟙 S) [ConnectedSpace Z]
    (L : _root_.SheafOfModules.{u}
      (structureSheafRing (pullback (pullback.fst f g ≫ f) h).toRingedSpace))
    (hD : IsDescentLocus (pullback.snd (pullback.fst f g ≫ f) h) L D)
    (hclosed : _root_.AlgebraicGeometry.IsClosedImmersion D.hom)
    (hnbhd : ∀ z ∈ Set.range D.hom, ∃ U : Z.Opens, z ∈ U ∧
      DescendsFromBase (pullback.snd (pullback.fst f g ≫ f) h) L U.ι)
    (hfaceX :
      let i : pullback g h ⟶ pullback (pullback.fst f g ≫ f) h :=
        pullback.lift
          (pullback.lift (pullback.fst g h ≫ g ≫ x) (pullback.fst g h)
            (by simp only [Category.assoc, hx, Category.comp_id]))
          (pullback.snd g h)
          (by rw [pullback.lift_fst_assoc]
              simp only [Category.assoc, hx, Category.comp_id, pullback.condition])
      IsTrivial (pullback g h).presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
          (pullback g h).IsSheaf)
        ((modulePullback i.toLRSHom.toShHom).obj L))
    (hfiber : ∃ z : Z,
      IsTrivial (pullback (pullback.snd (pullback.fst f g ≫ f) h)
          (Z.fromSpecResidueField z)).presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
          (pullback (pullback.snd (pullback.fst f g ≫ f) h)
            (Z.fromSpecResidueField z)).IsSheaf)
        ((modulePullback (pullback.fst (pullback.snd (pullback.fst f g ≫ f) h)
          (Z.fromSpecResidueField z)).toLRSHom.toShHom).obj L)) :
    IsTrivial (pullback (pullback.fst f g ≫ f) h).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (pullback (pullback.fst f g ≫ f) h).IsSheaf) L := by
  let iX : pullback g h ⟶ pullback (pullback.fst f g ≫ f) h :=
    pullback.lift
      (pullback.lift (pullback.fst g h ≫ g ≫ x) (pullback.fst g h)
        (by simp only [Category.assoc, hx, Category.comp_id]))
      (pullback.snd g h)
      (by rw [pullback.lift_fst_assoc]
          simp only [Category.assoc, hx, Category.comp_id, pullback.condition])
  let σ : Z ⟶ pullback g h := pullback.lift (h ≫ y) (𝟙 Z) (by simp [hy])
  have hδ : (σ ≫ iX) ≫ pullback.snd (pullback.fst f g ≫ f) h = 𝟙 Z := by
    rw [Category.assoc, pullback.lift_snd]
    exact pullback.lift_snd _ _ _
  obtain ⟨z, hz⟩ := hfiber
  have := hD.isIso_hom_of_connectedSpace hclosed hnbhd
    ⟨z, hD.mem_range_hom_of_isTrivial_fiber z hz⟩
  exact hD.isTrivial_of_isIso_hom (σ ≫ iX) hδ
    (isTrivial_modulePullback_scheme_of_comp σ iX (σ ≫ iX) rfl hfaceX)

-- Stacks Tag 0BF4 with all of its hypotheses, including the flatness, properness, finite
-- presentation and geometric integrality of `f` and `g`, the invertibility of `L` and the second
-- face hypothesis, together with the conclusions of Stacks Tags 0BDP, 0BF0 and 0BF3 as the
-- hypotheses `h0BDP`, `h0BF0` and `h0BF3` on a descent locus `D` for `L` along the projection to
-- `Z`. The fibre `X ×_S Y ×_S z` is the base change of the projection `X ×_S Y ×_S Z ⟶ Z` along
-- `Z.fromSpecResidueField z`.
example {S X Y Z : Scheme.{u}} {D : Over Z}
    (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    (x : S ⟶ X) (hx : x ≫ f = 𝟙 S) (y : S ⟶ Y) (hy : y ≫ g = 𝟙 S)
    [Flat f] [IsProper f] (_hfp : FinitePresentation f) [GeometricallyIntegral f]
    [Flat g] [IsProper g] (_hgp : FinitePresentation g) [GeometricallyIntegral g]
    [ConnectedSpace Z]
    (L : _root_.SheafOfModules.{u}
      (structureSheafRing (pullback (pullback.fst f g ≫ f) h).toRingedSpace))
    [IsInvertible (pullback (pullback.fst f g ≫ f) h).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (pullback (pullback.fst f g ≫ f) h).IsSheaf) L]
    (hfaceX :
      let i : pullback g h ⟶ pullback (pullback.fst f g ≫ f) h :=
        pullback.lift
          (pullback.lift (pullback.fst g h ≫ g ≫ x) (pullback.fst g h)
            (by simp only [Category.assoc, hx, Category.comp_id]))
          (pullback.snd g h)
          (by rw [pullback.lift_fst_assoc]
              simp only [Category.assoc, hx, Category.comp_id, pullback.condition])
      IsTrivial (pullback g h).presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
          (pullback g h).IsSheaf)
        ((modulePullback i.toLRSHom.toShHom).obj L))
    (_hfaceY :
      let i : pullback f h ⟶ pullback (pullback.fst f g ≫ f) h :=
        pullback.lift
          (pullback.lift (pullback.fst f h) (pullback.fst f h ≫ f ≫ y)
            (by simp only [Category.assoc, hy, Category.comp_id]))
          (pullback.snd f h)
          (by rw [pullback.lift_fst_assoc, pullback.condition])
      IsTrivial (pullback f h).presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
          (pullback f h).IsSheaf)
        ((modulePullback i.toLRSHom.toShHom).obj L))
    (hfiber : ∃ z : Z,
      IsTrivial (pullback (pullback.snd (pullback.fst f g ≫ f) h)
          (Z.fromSpecResidueField z)).presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
          (pullback (pullback.snd (pullback.fst f g ≫ f) h)
            (Z.fromSpecResidueField z)).IsSheaf)
        ((modulePullback (pullback.fst (pullback.snd (pullback.fst f g ≫ f) h)
          (Z.fromSpecResidueField z)).toLRSHom.toShHom).obj L))
    (h0BDP : IsDescentLocus (pullback.snd (pullback.fst f g ≫ f) h) L D)
    (h0BF0 : _root_.AlgebraicGeometry.IsClosedImmersion D.hom)
    (h0BF3 : ∀ z ∈ Set.range D.hom, ∃ U : Z.Opens, z ∈ U ∧
      DescendsFromBase (pullback.snd (pullback.fst f g ≫ f) h) L U.ι) :
    IsTrivial (pullback (pullback.fst f g ≫ f) h).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (pullback (pullback.fst f g ≫ f) h).IsSheaf) L :=
  isTrivial_of_isTrivial_face_and_fiber f g h x hx y hy L h0BDP h0BF0 h0BF3 hfaceX hfiber

end SheafOfModules

end AlgebraicGeometry

end
