module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowFourierMukai
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherentPullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TransportAlongIso
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentLocal
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SideCondition
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas

/-!
# Pseudo-coherence of derived direct images: locality on the target and transport

Two reductions used to prove that derived direct image along a projective bundle preserves
pseudo-coherence ([Stacks, Tag 0CSD], pseudo-coherence half, for `X ×_A ℙᵐ_A ⟶ X`):

* `AlgebraicGeometry.isPseudoCoherent_derivedPushforward_of_local`: for `g : T ⟶ Y`, if around
  every point of `Y` there is an open `W` with `R(g ∣_ W)_*` preserving pseudo-coherence, then
  `Rg_*` preserves pseudo-coherence. This is [Stacks, Tag 08FE] together with the locality of
  pseudo-coherence ([Stacks, Tag 08CB]) and its stability under restriction to opens.
* `AlgebraicGeometry.isPseudoCoherent_derivedPushforward_of_iso`: the same property transports
  along isomorphisms of source and target.

Also `AlgebraicGeometry.isPseudoCoherent_of_forall_exists_derivedPullback_ι`, the locality of
pseudo-coherence phrased with derived pullbacks along open immersions.

## References

* [Stacks Project, Tag 0CSD](https://stacks.math.columbia.edu/tag/0CSD)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

open DerivedChow

/-- Pseudo-coherence on a scheme is local: it can be checked on the derived pullbacks to the
members of an open cover. -/
theorem isPseudoCoherent_of_forall_exists_derivedPullback_ι {Y : Scheme.{u}}
    (E : DerivedCategory Y.Modules)
    (h : ∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧ RingedSpace.IsPseudoCoherent
      (X := W.toScheme.toRingedSpace) ((derivedPullback (ofScheme W.ι)).obj E)) :
    RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace) E := by
  refine RingedSpace.isPseudoCoherent_of_forall E fun n => ?_
  refine RingedSpace.isPseudoCoherentFrom_of_local_restrict E n fun y => ?_
  obtain ⟨W, hy, hW⟩ := h y
  exact ⟨W, hy, RingedSpace.IsPseudoCoherentFrom.of_iso
    (X := Y.toRingedSpace.restrict W.isOpenEmbedding) (hW.isPseudoCoherentFrom n)
    ((Scheme.Modules.derivedRestrictModulesIsoDerivedPullback Y W).app E).symm⟩

/-- **Pseudo-coherence of a derived direct image is local on the target.** If around every point
of `Y` there is an open `W` such that `R(g ∣_ W)_*` carries pseudo-coherent objects to
pseudo-coherent objects, then so does `Rg_*`. This is [Stacks, Tag 08FE] together with the
locality of pseudo-coherence and its stability under restriction to opens. -/
theorem isPseudoCoherent_derivedPushforward_of_local {T Y : Scheme.{u}} (g : T ⟶ Y)
    (h : ∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧
      ∀ F : DerivedCategory (g ⁻¹ᵁ W).toScheme.Modules,
        RingedSpace.IsPseudoCoherent (X := (g ⁻¹ᵁ W).toScheme.toRingedSpace) F →
          RingedSpace.IsPseudoCoherent (X := W.toScheme.toRingedSpace)
            ((derivedPushforward (ofScheme (g ∣_ W))).obj F))
    (F : DerivedCategory T.Modules)
    (hF : RingedSpace.IsPseudoCoherent (X := T.toRingedSpace) F) :
    RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace)
      ((derivedPushforward (ofScheme g)).obj F) := by
  refine isPseudoCoherent_of_forall_exists_derivedPullback_ι _ fun y => ?_
  obtain ⟨W, hy, hW⟩ := h y
  refine ⟨W, hy, RingedSpace.IsPseudoCoherent.of_iso (X := W.toScheme.toRingedSpace)
    (hW _ (Scheme.Hom.isPseudoCoherent_derivedPullback (g ⁻¹ᵁ W).ι F hF))
    ((derivedPushforwardRestrictOpenIso g W).app F).symm⟩

/-- **Pseudo-coherence of derived direct images transports along isomorphisms.** Let
`g : T ⟶ Y` and `g' : T' ⟶ Y'` be identified by isomorphisms `T ≅ T'` and `Y ≅ Y'`. If `Rg'_*`
carries pseudo-coherent objects to pseudo-coherent objects, so does `Rg_*`. -/
theorem isPseudoCoherent_derivedPushforward_of_iso {T Y T' Y' : Scheme.{u}} (g : T ⟶ Y)
    (g' : T' ⟶ Y') (e : T ≅ T') (h : Y ≅ Y') (w : e.hom ≫ g' = g ≫ h.hom)
    (H : ∀ F' : DerivedCategory T'.Modules,
      RingedSpace.IsPseudoCoherent (X := T'.toRingedSpace) F' →
        RingedSpace.IsPseudoCoherent (X := Y'.toRingedSpace)
          ((derivedPushforward (ofScheme g')).obj F'))
    (F : DerivedCategory T.Modules)
    (hF : RingedSpace.IsPseudoCoherent (X := T.toRingedSpace) F) :
    RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace)
      ((derivedPushforward (ofScheme g)).obj F) := by
  have hiso : ∀ {A B : Scheme.{u}} (i : A ≅ B), ofScheme i.inv ≫ ofScheme i.hom = 𝟙 _ := fun i => by
    rw [ofScheme_comp, i.inv_hom_id, ofScheme_id]
  have he1 := hiso e
  have he2 := hiso e.symm
  have hh1 := hiso h
  have hh2 := hiso h.symm
  have hw : ofScheme e.inv ≫ ofScheme g = ofScheme g' ≫ ofScheme h.inv := by
    rw [ofScheme_comp, ofScheme_comp]
    congr 1
    rw [Iso.inv_comp_eq, ← Category.assoc, w, Category.assoc, h.hom_inv_id, Category.comp_id]
  set F' := (derivedPullback (ofScheme e.inv)).obj F
  have hF' : RingedSpace.IsPseudoCoherent (X := T'.toRingedSpace) F' :=
    Scheme.Hom.isPseudoCoherent_derivedPullback e.inv F hF
  set N := (derivedPushforward (ofScheme g')).obj F'
  have hN : RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace)
      ((derivedPullback (ofScheme h.hom)).obj N) :=
    Scheme.Hom.isPseudoCoherent_derivedPullback h.hom N (H F' hF')
  refine RingedSpace.IsPseudoCoherent.of_iso (X := Y.toRingedSpace) hN ?_
  exact derivedUnitIsoOfInverse (ofScheme h.inv) (ofScheme h.hom) hh1 hh2 _ ≪≫
    (derivedPushforward (ofScheme h.inv)).mapIso
      ((derivedPullbackFactorIso (ofScheme h.inv) (ofScheme h.hom) (𝟙 _) hh1 ≪≫
        Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso _).app N) ≪≫
    (derivedPushforwardFactorIso (ofScheme g') (ofScheme h.inv) _ rfl).app F' ≪≫
    ((derivedPushforwardFactorIso (ofScheme e.inv) (ofScheme g) _ hw).app F').symm ≪≫
    (derivedPushforward (ofScheme g)).mapIso
      (derivedUnitIsoOfInverse (ofScheme e.inv) (ofScheme e.hom) he1 he2 F).symm


end AlgebraicGeometry

end
