module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksCore.Tactic.StacksAttribute

/-!
# Étale neighbourhoods are almost cofiltered

Two étale neighbourhoods of a point admit a common refinement, and two morphisms of étale
neighbourhoods which induce the same map on residue fields become equal after passing to a
further refinement. The category of étale neighbourhoods of `(S, s)` is therefore cofiltered up
to the residue field data, which is what makes the colimit computations of Tag 05KS possible.

## Main results

* `AlgebraicGeometry.exists_common_refinement`: two neighbourhoods have a common refinement.
* `AlgebraicGeometry.exists_equalizing_refinement`: morphisms inducing the same residue field
  map are equalized by a refinement.
* `AlgebraicGeometry.fromSpecResidueField_comp_eq`: two morphisms of neighbourhoods inducing the
  same residue field map already agree on the spectrum of that residue field.

## Implementation notes

The first declaration states part (1) of the source lemma and the second states part (2). The
residue field maps in part (2) are transported along the given equalities of the images of the
distinguished point before they are compared.

The common refinement of part (1) is the fibre product of the two structure morphisms. For part
(2) one forms the morphism `U.scheme ⟶ V.scheme ×_S V.scheme` determined by the two morphisms
and pulls back the diagonal of `V.toBase` along it: the hypothesis on residue fields says
exactly that the distinguished point of `U` lands in the diagonal, so the pullback is again a
neighbourhood, and on it the two morphisms agree.

## References

* [Stacks Project, Tag 057A](https://stacks.math.columbia.edu/tag/057A)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Pulling back an étale morphism `b` along `a : U.scheme ⟶ Y` gives a refinement of `U` which
comes with a map to the source of `b`, provided the distinguished point of `U` and a point of that
source have the same image in `Y`. -/
private theorem exists_pullback_neighborhood {S : Scheme.{u}} {s : S} (U : EtaleNeighborhood S s)
    {Y Z : Scheme.{u}} (a : U.scheme ⟶ Y) (b : Z ⟶ Y) [Etale b] (z₀ : Z) (h : a U.point = b z₀) :
    ∃ (W : EtaleNeighborhood S s) (k : W ⟶ U) (m : W.scheme ⟶ Z),
      k.hom ≫ a = m ≫ b ∧ m W.point = z₀ := by
  obtain ⟨z, hzU, hzV⟩ := Scheme.Pullback.exists_preimage_pullback (f := a) (g := b) U.point z₀ h
  exact ⟨{ scheme := Limits.pullback a b
           point := z
           toBase := Limits.pullback.fst a b ≫ U.toBase
           map_point := by simpa [Scheme.Hom.comp_apply, hzU] using U.map_point },
    ⟨Limits.pullback.fst a b, rfl, hzU⟩, Limits.pullback.snd a b,
    Limits.pullback.condition, hzV⟩

/-- **Stacks Project, Tag 057A, part (1).** Two étale neighborhoods of a point
admit a common refinement. -/
@[stacks 057A "part (1)"]
theorem exists_common_refinement {S : Scheme.{u}} {s : S}
    (U V : EtaleNeighborhood S s) :
    ∃ W : EtaleNeighborhood S s, Nonempty ((W ⟶ U) × (W ⟶ V)) := by
  obtain ⟨W, k, m, hm, hmp⟩ := exists_pullback_neighborhood U U.toBase V.toBase V.point
    (U.map_point.trans V.map_point.symm)
  exact ⟨W, ⟨k, ⟨m, hm.symm.trans k.over, hmp⟩⟩⟩

section Equalizer

variable {S : Scheme.{u}} {s : S} {U V : EtaleNeighborhood S s}

/-- The map `Spec κ(U.point) ⟶ U.scheme` sends the closed point to the distinguished point. -/
private lemma fromSpecResidueField_closedPoint_eq (U : EtaleNeighborhood S s) :
    U.scheme.fromSpecResidueField U.point
        (IsLocalRing.closedPoint (U.scheme.residueField U.point)) = U.point :=
  Scheme.fromSpecResidueField_apply U.point _

/-- Two morphisms of étale neighbourhoods which agree on residue fields agree after
restriction to the spectrum of the residue field at the distinguished point: a morphism out of
the spectrum of a field is determined by its image point together with the induced map of
residue fields. -/
theorem fromSpecResidueField_comp_eq (f g : U ⟶ V)
    (hκ : (V.scheme.residueFieldCongr f.map_point).inv ≫
        f.hom.residueFieldMap U.point =
      (V.scheme.residueFieldCongr g.map_point).inv ≫
        g.hom.residueFieldMap U.point) :
    U.scheme.fromSpecResidueField U.point ≫ f.hom =
      U.scheme.fromSpecResidueField U.point ≫ g.hom := by
  let i : Spec (.of (↑(U.scheme.residueField U.point))) ⟶ U.scheme :=
    U.scheme.fromSpecResidueField U.point
  have hepoint : i (IsLocalRing.closedPoint (U.scheme.residueField U.point)) = U.point :=
    fromSpecResidueField_closedPoint_eq U
  have he : f.hom (i (IsLocalRing.closedPoint (U.scheme.residueField U.point))) =
      g.hom (i (IsLocalRing.closedPoint (U.scheme.residueField U.point))) := by
    simpa only [hepoint] using f.map_point.trans g.map_point.symm
  let d : U.scheme.residueField
      (i (IsLocalRing.closedPoint (U.scheme.residueField U.point))) ⟶
      U.scheme.residueField U.point :=
    @Scheme.descResidueField (↑(U.scheme.residueField U.point)) inferInstance
      U.scheme (i (IsLocalRing.closedPoint (U.scheme.residueField U.point)))
      (Scheme.stalkClosedPointTo i)
      (Scheme.isLocalHom_stalkClosedPointTo' i)
  have hdesc : d = (U.scheme.residueFieldCongr hepoint).hom := by
    rw [← Spec.map_inj, ← cancel_mono (U.scheme.fromSpecResidueField
      (i (IsLocalRing.closedPoint (U.scheme.residueField U.point))))]
    exact (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField
      (U.scheme.residueField U.point) U.scheme i).trans
      (Scheme.residueFieldCongr_fromSpecResidueField hepoint).symm
  have : IsLocalHom (Scheme.stalkClosedPointTo (i ≫ f.hom)).hom :=
    Scheme.isLocalHom_stalkClosedPointTo' (i ≫ f.hom)
  have : IsLocalHom (Scheme.stalkClosedPointTo (i ≫ g.hom)).hom :=
    Scheme.isLocalHom_stalkClosedPointTo' (i ≫ g.hom)
  apply (Scheme.SpecToEquivOfField (U.scheme.residueField U.point) V.scheme).injective
  rw [Scheme.SpecToEquivOfField_eq_iff]
  refine ⟨?_, ?_⟩
  · exact he
  · have hmain : Scheme.Hom.residueFieldMap f.hom
        (i (IsLocalRing.closedPoint (U.scheme.residueField U.point))) ≫ d =
        (V.scheme.residueFieldCongr he).hom ≫
          Scheme.Hom.residueFieldMap g.hom
            (i (IsLocalRing.closedPoint (U.scheme.residueField U.point))) ≫ d := by
      rw [hdesc, Scheme.Hom.residueFieldMap_congr' hepoint,
        Scheme.Hom.residueFieldMap_congr' hepoint]
      have hκ'' := congrArg ((V.scheme.residueFieldCongr (congrArg f.hom hepoint)).hom ≫ ·)
        (congrArg ((V.scheme.residueFieldCongr f.map_point).hom ≫ ·) hκ)
      simpa [Scheme.residueFieldCongr_trans_hom, ← Category.assoc, he] using hκ''
    simp only [Scheme.SpecToEquivOfField_apply_snd]
    exact (Scheme.descResidueField_stalkClosedPointTo_comp
      (K := ↑(U.scheme.residueField U.point)) (f := f.hom) i).trans (hmain.trans
      (congrArg ((V.scheme.residueFieldCongr he).hom ≫ ·)
        (Scheme.descResidueField_stalkClosedPointTo_comp
          (K := ↑(U.scheme.residueField U.point)) (f := g.hom) i).symm))

/-- **Stacks Project, Tag 057A, part (2).** Two neighborhood maps which induce
the same map on residue fields become equal after a refinement. -/
@[stacks 057A "part (2)"]
theorem exists_equalizing_refinement (f g : U ⟶ V)
    (hκ : (V.scheme.residueFieldCongr f.map_point).inv ≫
        f.hom.residueFieldMap U.point =
      (V.scheme.residueFieldCongr g.map_point).inv ≫
        g.hom.residueFieldMap U.point) :
    ∃ W : EtaleNeighborhood S s, ∃ h : W ⟶ U, h ≫ f = h ≫ g := by
  let i : Spec (.of (↑(U.scheme.residueField U.point))) ⟶ U.scheme :=
    U.scheme.fromSpecResidueField U.point
  let p₀ : Spec (U.scheme.residueField U.point) := default
  have hipoint : i p₀ = U.point := Scheme.fromSpecResidueField_apply U.point p₀
  have hfg : i ≫ f.hom = i ≫ g.hom := fromSpecResidueField_comp_eq f g hκ
  let D := Limits.pullback V.toBase V.toBase
  let q : U.scheme ⟶ D := Limits.pullback.lift f.hom g.hom (f.over.trans g.over.symm)
  have hqfst : q ≫ Limits.pullback.fst V.toBase V.toBase = f.hom :=
    Limits.pullback.lift_fst _ _ _
  have hqsnd : q ≫ Limits.pullback.snd V.toBase V.toBase = g.hom :=
    Limits.pullback.lift_snd _ _ _
  have hfac : i ≫ q = (i ≫ f.hom) ≫ Limits.pullback.diagonal V.toBase := by
    apply Limits.pullback.hom_ext <;> cat_disch
  have hqpoint : q U.point = Limits.pullback.diagonal V.toBase V.point := by
    have hp := congrArg (fun k : Spec (.of (U.scheme.residueField U.point)) ⟶ D =>
      k p₀) hfac
    simpa only [Scheme.Hom.comp_apply, hipoint, f.map_point] using hp
  have : Etale q := by
    apply MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale)
      q (Limits.pullback.fst V.toBase V.toBase ≫ V.toBase)
    · infer_instance
    · simpa only [← Category.assoc, hqfst, f.over] using
        (inferInstance : Etale U.toBase)
  obtain ⟨W, k, m, hm, -⟩ := exists_pullback_neighborhood U q (Limits.pullback.diagonal V.toBase)
    V.point hqpoint
  refine ⟨W, k, EtaleNeighborhood.Hom.ext ?_⟩
  simp only [EtaleNeighborhood.comp_hom, ← hqfst, ← hqsnd, reassoc_of% hm]
  simp

end Equalizer

end AlgebraicGeometry
