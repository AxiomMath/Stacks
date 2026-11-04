module

public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocus0BDP
public import StacksFrontier.AlgebraicGeometry.Descent.TrivialOnOpen0BF3
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Descent from the base is triviality, for a module rigidified along a section

Let `p : P ⟶ S` be a morphism of schemes with a section `e : S ⟶ P`, and let `L` be a sheaf of
modules on `P` whose restriction along `e` is trivial. Then for every base change `g : T ⟶ S`
the descent condition `AlgebraicGeometry.DescendsFromBase p L g` of
[Stacks, Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP) holds *exactly* when the pullback
of `L` to `P ×_S T` is trivial. No hypothesis on the module witnessing the descent condition
and none on `T` is needed.

Consequently the conclusion of [Stacks, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3) is
*equivalent* to the descent condition holding on a neighbourhood of the point, which is what
Tag 0BF2 produces. The section there is `(σ, τ)`, along which the first face hypothesis of
0BF3 makes the module trivial.

## Main results

* `AlgebraicGeometry.SheafOfModules.isTrivial_modulePullback_fst_of_descendsFromBase`: for a
  module trivial along a section of `p`, the descent condition implies triviality of the
  pullback to the base change.
* `AlgebraicGeometry.SheafOfModules.descendsFromBase_iff_isTrivial_modulePullback_fst`: the two
  are equivalent, so the descent locus of such a module is its triviality locus.
* `AlgebraicGeometry.isDescentLocus_id_of_isTrivial`: the base itself is a descent locus for a
  trivial module.
* `AlgebraicGeometry.SheafOfModules.exists_descendsFromBase_iff_exists_isTrivial_on_open`: in
  the situation of Tag 0BF3, the conclusion of that tag is equivalent to the descent condition
  holding over some open neighbourhood of the point.

The `example` at the end of this file states Tag 0BF3 verbatim, with that equivalent descent
condition as its one added hypothesis, and proves it from the equivalence. It is an `example`
because several hypotheses of the tag (the flatness and properness of `f` and `g`, the
invertibility of `L`) are not used.

## Implementation notes

The hypothesis added to Tag 0BF3 is the conclusion of Tag 0BF2 at the two faces of the fibre
product. What Tag 0BF2 supplies and nothing here does is that the descent locus contains a
*neighbourhood* of the point, which in the source rests on the Künneth injectivity of
[Stacks, Tag 0BED](https://stacks.math.columbia.edu/tag/0BED) and on cohomology and base change
for perfect complexes.

## References

* [Stacks Project, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3)
* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
* [Stacks Project, Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

namespace SheafOfModules

/-- **The descent condition implies triviality, for a module trivial along a section.** Let
`e` be a section of `p : P ⟶ S` and let the pullback of `L` along `e` be trivial. If `L`
descends along a base change `g : T ⟶ S`, then the pullback of `L` to `P ×_S T` is trivial. -/
theorem isTrivial_modulePullback_fst_of_descendsFromBase {S P : Scheme.{u}} (p : P ⟶ S)
    (e : S ⟶ P) (he : e ≫ p = 𝟙 S)
    (L : _root_.SheafOfModules.{u} (structureSheafRing P.toRingedSpace))
    (hL : IsTrivial S.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) S.IsSheaf)
      ((modulePullback e.toLRSHom.toShHom).obj L))
    {T : Scheme.{u}} (g : T ⟶ S) (hd : DescendsFromBase p L g) :
    IsTrivial (pullback p g).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) (pullback p g).IsSheaf)
      ((modulePullback (pullback.fst p g).toLRSHom.toShHom).obj L) := by
  obtain ⟨N, _, ⟨iso⟩⟩ := hd
  set et : T ⟶ pullback p g := pullback.lift (g ≫ e) (𝟙 T) (by simp [he])
  have hfst : et ≫ pullback.fst p g = g ≫ e := pullback.lift_fst _ _ _
  have hsnd : et ≫ pullback.snd p g = 𝟙 T := pullback.lift_snd _ _ _
  have h1 : IsTrivial T.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) T.IsSheaf)
      ((modulePullback (et ≫ pullback.fst p g).toLRSHom.toShHom).obj L) := by
    rw [hfst]
    exact isTrivial_modulePullback_scheme_of_comp g e (g ≫ e) rfl hL
  have h4 : IsTrivial T.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) T.IsSheaf)
      ((modulePullback (Scheme.Hom.toLRSHom (𝟙 T)).toShHom).obj N) := by
    rw [← hsnd]
    exact ⟨(RingedSpaceModuleAdjunction.modulePullbackComp
      et.toLRSHom.toShHom (pullback.snd p g).toLRSHom.toShHom).app N ≪≫
      (modulePullback et.toLRSHom.toShHom).mapIso iso ≪≫
      ((RingedSpaceModuleAdjunction.modulePullbackComp
        et.toLRSHom.toShHom (pullback.fst p g).toLRSHom.toShHom).app L).symm ≪≫ h1.some⟩
  exact ⟨iso.symm ≪≫ (isTrivial_modulePullback_scheme_of_comp (pullback.snd p g) (𝟙 T)
    (pullback.snd p g) (Category.comp_id _) h4).some⟩

/-- **For a module trivial along a section, the descent locus is the triviality locus.** The
descent condition of Stacks Tag 0BDP along a base change `g : T ⟶ S` holds exactly when the
pullback of `L` to `P ×_S T` is trivial. -/
theorem descendsFromBase_iff_isTrivial_modulePullback_fst {S P : Scheme.{u}} (p : P ⟶ S)
    (e : S ⟶ P) (he : e ≫ p = 𝟙 S)
    (L : _root_.SheafOfModules.{u} (structureSheafRing P.toRingedSpace))
    (hL : IsTrivial S.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) S.IsSheaf)
      ((modulePullback e.toLRSHom.toShHom).obj L))
    {T : Scheme.{u}} (g : T ⟶ S) :
    DescendsFromBase p L g ↔
      IsTrivial (pullback p g).presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
          (pullback p g).IsSheaf)
        ((modulePullback (pullback.fst p g).toLRSHom.toShHom).obj L) :=
  ⟨isTrivial_modulePullback_fst_of_descendsFromBase p e he L hL g,
    descendsFromBase_of_nonempty_iso_unit p L g⟩

end SheafOfModules

/-- **The base is a descent locus for a trivial module.** If `E` on `X` is trivial then every
base change `g : T ⟶ S` satisfies the descent condition for `E`, so the identity of `S` has the
universal property of the descent locus of Stacks Tag 0BDP. -/
theorem isDescentLocus_id_of_isTrivial {X S : Scheme.{u}} (f : X ⟶ S)
    (E : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hE : SheafOfModules.IsTrivial X.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf) E) :
    IsDescentLocus f E (Over.mk (𝟙 S)) where
  isImmersion := by
    dsimp
    infer_instance
  finitePresentation :=
    show FinitePresentation (𝟙 S) from ⟨inferInstance, inferInstance, inferInstance⟩
  factorsThrough_iff {T} g :=
    ⟨fun _ ↦ descendsFromBase_of_nonempty_iso_unit f E g
      (SheafOfModules.isTrivial_modulePullback_scheme (pullback.fst f g) hE),
      fun _ ↦ ⟨g, Category.comp_id g⟩⟩

namespace SheafOfModules

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **The conclusion of Stacks Tag 0BF3 is the germ of the descent condition at the point.**
In the situation of that tag, there is an open neighbourhood `U` of `s` over which `L` is
trivial exactly when there is one along which `L` descends from the base in the sense of Stacks
Tag 0BDP. Of the hypotheses of Tag 0BF3 only the first face hypothesis is assumed. -/
theorem exists_descendsFromBase_iff_exists_isTrivial_on_open
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) (τ : S ⟶ Y) (hτ : τ ≫ g = 𝟙 S) (s : S)
    (L : _root_.SheafOfModules.{u} (structureSheafRing (pullback f g).toRingedSpace))
    (hfaceX :
      let i : X ⟶ pullback f g :=
        pullback.lift (𝟙 X) (f ≫ τ)
          (by simp only [Category.id_comp, Category.assoc, hτ, Category.comp_id])
      IsTrivial X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf)
        ((modulePullback i.toLRSHom.toShHom).obj L)) :
    (∃ U : S.Opens, s ∈ U ∧
        DescendsFromBase (pullback.fst f g ≫ f) L U.ι) ↔
      (∃ U : S.Opens, s ∈ U ∧
        (let P := pullback f g;
          let p : P ⟶ S := pullback.fst f g ≫ f;
          let W := pullback p U.ι;
          IsTrivial W.presheaf
            (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) W.IsSheaf)
            ((modulePullback (pullback.fst p U.ι).toLRSHom.toShHom).obj L))) := by
  have he : pullback.lift σ τ (by rw [hσ, hτ]) ≫ (pullback.fst f g ≫ f) = 𝟙 S := by
    rw [← Category.assoc, pullback.lift_fst, hσ]
  exact exists_congr fun U ↦ and_congr_right fun _ ↦
    descendsFromBase_iff_isTrivial_modulePullback_fst _ _ he L
      (isTrivial_modulePullback_sectionLift_of_isTrivial_face f g σ hσ τ hτ L hfaceX) U.ι

-- **Stacks Tag 0BF3**, stated verbatim, with the conclusion of Stacks Tag 0BF2 at the two
-- faces of the fibre product added as its one extra hypothesis `h0BF2`: the invertible module
-- `L` on `X ×_S Y` descends from the base over some open neighbourhood of `s`.
--
-- By `exists_descendsFromBase_iff_exists_isTrivial_on_open` the added hypothesis is equivalent
-- to the conclusion, under the first face hypothesis alone. The remaining hypotheses are carried
-- unchanged from the tag and are not used.
example
    [Flat f] [IsProper f] (_hfp : FinitePresentation f)
    (_hfO : ∀ {T : Scheme.{u}} (a : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd f a).toLRSHom.toShHom))
    [Flat g] [IsProper g] (_hgp : FinitePresentation g)
    (_hgO : ∀ {T : Scheme.{u}} (a : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd g a).toLRSHom.toShHom))
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (τ : S ⟶ Y) (hτ : τ ≫ g = 𝟙 S)
    (s : S)
    (L : _root_.SheafOfModules.{u} (structureSheafRing (pullback f g).toRingedSpace))
    [IsInvertible (pullback f g).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (pullback f g).IsSheaf) L]
    (hfaceX :
      let i : X ⟶ pullback f g :=
        pullback.lift (𝟙 X) (f ≫ τ) (by simp [Category.assoc, hτ])
      IsTrivial X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf)
        ((modulePullback i.toLRSHom.toShHom).obj L))
    (_hfaceY :
      let i : Y ⟶ pullback f g :=
        pullback.lift (g ≫ σ) (𝟙 Y) (by simp [Category.assoc, hσ])
      IsTrivial Y.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Y.IsSheaf)
        ((modulePullback i.toLRSHom.toShHom).obj L))
    (_hfiber :
      let P := pullback f g
      let p : P ⟶ S := pullback.fst f g ≫ f
      let W := pullback p (S.fromSpecResidueField s)
      IsTrivial W.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) W.IsSheaf)
        ((modulePullback (pullback.fst p (S.fromSpecResidueField s)).toLRSHom.toShHom).obj L))
    (h0BF2 : ∃ U : S.Opens, s ∈ U ∧
      DescendsFromBase (pullback.fst f g ≫ f) L U.ι) :
    ∃ U : S.Opens, s ∈ U ∧
      (let P := pullback f g
       let p : P ⟶ S := pullback.fst f g ≫ f
       let W := pullback p U.ι
       IsTrivial W.presheaf
         (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) W.IsSheaf)
         ((modulePullback (pullback.fst p U.ι).toLRSHom.toShHom).obj L)) :=
  (exists_descendsFromBase_iff_exists_isTrivial_on_open f g σ hσ τ hτ s L hfaceX).1 h0BF2

end SheafOfModules

end AlgebraicGeometry

end
