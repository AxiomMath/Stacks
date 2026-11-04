module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RelativeMayerVietoris
public import StacksFrontier.AlgebraicGeometry.InductionPrinciple.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomologyOnALargeSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.TorsionSheavesAndRestriction

/-!
# Finiteness of the cohomological dimension of a morphism: the reductions

Let `f : X ⟶ Y` be a quasi-compact quasi-separated morphism of schemes. This file proves the
two reductions in the proof of part (1) of [Stacks, Tag 0F10].

1. **Locality on the target.** If `Y` is covered by finitely many opens `V i` with
   `cd(f|_{V i}) < ∞`, then `cd(f) < ∞`. The higher direct image `Rⁿf_*F` restricted to `V` is
   `Rⁿ(f|_V)_*(F|_{f⁻¹V})`, since restriction to an open is exact, preserves injectives and
   commutes with direct images. A sheaf on `Y_étale` whose restrictions to an open cover vanish
   vanishes.
2. **Induction on the source.** If `X` is quasi-compact and quasi-separated, and `j ≫ f` has a
   finite bound on its higher direct images for every open immersion `j : Z ⟶ X` from an affine
   scheme, then `cd(f) < ∞`. This is the induction principle of [Stacks, Tag 08DR] with the
   relative Mayer--Vietoris sequence of [Stacks, Tag 0EYK] as the induction step.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isEtaleHigherDirectImageBound_of_cover`: the Mayer--Vietoris
  step. Bounds `a`, `b`, `c` for `f|_U`, `f|_V`, `f|_{U ∩ V}` with `U ∪ V = X` give the bound
  `max(a, b, c) + 1` for `f`.
* `AlgebraicGeometry.Scheme.Hom.etaleCohomologicalDimension_lt_top_of_isAffine_source`: the
  reduction to affine sources.
* `AlgebraicGeometry.Scheme.Hom.rightDerivedRestrictionIso`: `(Rⁿf_*F)|_V ≅ Rⁿ(f|_V)_*(F|_{f⁻¹V})`.
* `AlgebraicGeometry.Scheme.Hom.etaleCohomologicalDimension_lt_top_of_openCover`: the reduction to
  the members of a finite open cover of the target.

## Implementation notes

The induction on the source runs over the opens `W` of `X`, with the property that `j ≫ f` is
bounded for *every* open immersion `j` with image `W`. This makes the induction step
self-contained. For `j` with image `U ∪ V`, the preimages `j⁻¹U` and `j⁻¹V` cover the source
of `j`, and the composites `(j⁻¹U).ι ≫ j` are again open immersions, with image `U`. So no
scheme isomorphism has to be carried through a higher direct image.

## References

* [Stacks Project, Tag 0F10](https://stacks.math.columbia.edu/tag/0F10)
* [Stacks Project, Tag 0F0Z](https://stacks.math.columbia.edu/tag/0F0Z)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 0EYK](https://stacks.math.columbia.edu/tag/0EYK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped ZeroObject

universe u

namespace AlgebraicGeometry.Scheme.Hom

open Stacks.EtaleCohomology

/-- The restriction of a torsion abelian sheaf along an étale morphism is torsion. -/
theorem torsionSheafProperty_etaleRestriction {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    Stacks.Torsion.torsionSheafProperty U.smallEtaleTopology
      ((etaleRestriction.{u, u + 1} j).obj F) :=
  Stacks.Torsion.torsionSheafProperty_sheafPushforwardContinuous _ F hF

/-! ### The Mayer--Vietoris step -/

/-- **The Mayer--Vietoris step for higher direct images.** Let `f : X ⟶ Y` and let `U`, `V` be
opens covering `X`. If the higher direct images of torsion sheaves along `f|_U`, `f|_V` and
`f|_{U ∩ V}` vanish above `a`, `b` and `c`, then those along `f` vanish above
`max(a, b, c) + 1`. The window
`Rⁿc_*(F|_{U ∩ V}) ⟶ Rⁿ⁺¹f_*F ⟶ Rⁿ⁺¹a_*(F|_U) ⊕ Rⁿ⁺¹b_*(F|_V)` of [Stacks, Tag 0EYK] is exact
with vanishing ends. -/
theorem isEtaleHigherDirectImageBound_of_cover {X Y : Scheme.{u}} (f : X ⟶ Y) (U V : X.Opens)
    (hUV : U ⊔ V = ⊤) (a b c : ℕ) (ha : IsEtaleHigherDirectImageBound (U.ι ≫ f) a)
    (hb : IsEtaleHigherDirectImageBound (V.ι ≫ f) b)
    (hc : IsEtaleHigherDirectImageBound ((U ⊓ V).ι ≫ f) c) :
    IsEtaleHigherDirectImageBound f (max (max a b) c + 1 : ℕ) := by
  intro F hF i hi
  have hi' : max (max a b) c + 1 < i := by exact_mod_cast hi
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have hseq := RelativeMayerVietoris.cohomologySequence_exact.{u, u + 1} f U V hUV m F
  have hUz := ha _ (torsionSheafProperty_etaleRestriction U.ι F hF) (m + 1)
    (by exact_mod_cast (show a < m + 1 by omega))
  have hVz := hb _ (torsionSheafProperty_etaleRestriction V.ι F hF) (m + 1)
    (by exact_mod_cast (show b < m + 1 by omega))
  have hUVz := hc _ (torsionSheafProperty_etaleRestriction (U ⊓ V).ι F hF) m
    (by exact_mod_cast (show c < m by omega))
  let G := (CategoryTheory.evaluation (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})).obj F
  have : PreservesBinaryBiproducts G := preservesBinaryBiproducts_of_preservesBiproducts G
  exact (hseq.exact 2).isZero_of_both_isZero hUVz
    (((biprod_isZero_iff _ _).2 ⟨hUz, hVz⟩).of_iso (G.mapBiprod _ _))

/-! ### Induction on the source -/

/-- The property of an open `W` of `X` driving the induction on the source: for every open
immersion `j` with image `W`, the higher direct images along `j ≫ f` of torsion sheaves vanish
above some bound. -/
def HasOpenImmersionBound {X Y : Scheme.{u}} (f : X ⟶ Y) (W : X.Opens) : Prop :=
  ∀ (Z : Scheme.{u}) (j : Z ⟶ X) [IsOpenImmersion j], j.opensRange = W →
    ∃ d : ℕ, IsEtaleHigherDirectImageBound (j ≫ f) d

/-- The image of `(j⁻¹U).ι ≫ j` is `U` when `U` lies in the image of the open immersion `j`. -/
theorem opensRange_preimage_ι_comp {Z X : Scheme.{u}} (j : Z ⟶ X) [IsOpenImmersion j]
    (U : X.Opens) (hU : U ≤ j.opensRange) :
    ((j ⁻¹ᵁ U).ι ≫ j).opensRange = U := by
  rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
    Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.2 hU]

/-- **The induction step on the source.** -/
theorem hasOpenImmersionBound_sup {X Y : Scheme.{u}} (f : X ⟶ Y) (U V : X.Opens)
    (hU : HasOpenImmersionBound f U) (hV : HasOpenImmersionBound f V)
    (hUV : HasOpenImmersionBound f (U ⊓ V)) :
    HasOpenImmersionBound f (U ⊔ V) := by
  intro Z j _ hj
  have hUj : U ≤ j.opensRange := hj ▸ le_sup_left
  have hVj : V ≤ j.opensRange := hj ▸ le_sup_right
  have hUVj : U ⊓ V ≤ j.opensRange := le_trans inf_le_left hUj
  obtain ⟨a, ha⟩ := hU _ ((j ⁻¹ᵁ U).ι ≫ j) (opensRange_preimage_ι_comp j U hUj)
  obtain ⟨b, hb⟩ := hV _ ((j ⁻¹ᵁ V).ι ≫ j) (opensRange_preimage_ι_comp j V hVj)
  obtain ⟨c, hc⟩ := hUV _ ((j ⁻¹ᵁ (U ⊓ V)).ι ≫ j) (opensRange_preimage_ι_comp j _ hUVj)
  have hcover : j ⁻¹ᵁ U ⊔ j ⁻¹ᵁ V = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, hj.symm]
    exact Scheme.Hom.preimage_opensRange j
  refine ⟨max (max a b) c + 1, isEtaleHigherDirectImageBound_of_cover (j ≫ f) (j ⁻¹ᵁ U)
    (j ⁻¹ᵁ V) hcover a b c ?_ ?_ ?_⟩
  · simpa only [Category.assoc] using ha
  · simpa only [Category.assoc] using hb
  · rw [← Scheme.Hom.preimage_inf]
    simpa only [Category.assoc] using hc

/-- **The reduction to affine sources** (the induction on the source in the proof of
[Stacks, Tag 0F10], part (1)). Let `f : X ⟶ Y` with `X` quasi-compact and quasi-separated. If
for every open immersion `j : Z ⟶ X` from an affine scheme the higher direct images of torsion
sheaves along `j ≫ f` vanish above some bound, then `cd(f) < ∞`. -/
theorem etaleCohomologicalDimension_lt_top_of_isAffine_source {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace X] [QuasiSeparatedSpace X] [QuasiCompact f] [QuasiSeparated f]
    (h : ∀ (Z : Scheme.{u}) [IsAffine Z] (j : Z ⟶ X) [IsOpenImmersion j],
      ∃ d : ℕ, IsEtaleHigherDirectImageBound (j ≫ f) d) :
    etaleCohomologicalDimension f < ⊤ := by
  have htop : HasOpenImmersionBound f ⊤ :=
    Stacks.AlgebraicGeometry.InductionPrinciple.induction_top (HasOpenImmersionBound f)
      (fun V hV Z j _ hj => by
        have : IsAffine V.toScheme := hV
        let e : Z ≅ V.toScheme := IsOpenImmersion.isoOfRangeEq j V.ι (by
          rw [← Scheme.Hom.coe_opensRange, hj, ← Scheme.Hom.coe_opensRange,
            Scheme.Opens.opensRange_ι])
        have : IsAffine Z := IsAffine.of_isIso e.hom
        exact h Z j)
      (fun U V _ _ => hasOpenImmersionBound_sup f U V)
  obtain ⟨d, hd⟩ := htop X (𝟙 X) (Scheme.Hom.opensRange_of_isIso _)
  rw [Category.id_comp] at hd
  exact (etaleCohomologicalDimension_le f d hd).trans_lt (ENat.natCast_lt_top d)

/-! ### Locality on the target -/

/-- **The restriction of a higher direct image to an open of the target.** For `f : X ⟶ Y`, an
open `V` of `Y` and an abelian sheaf `F` on `X_étale`,
`(Rⁿf_*F)|_V ≅ Rⁿ(f|_V)_*(F|_{f⁻¹V})`. Restriction to `V` is exact, so it commutes with the
right derived functor on the left. On the right, restriction to `f⁻¹V` is exact and preserves
injectives, so it may be moved inside. In between, `(f_*G)|_V = (f|_V)_*(G|_{f⁻¹V})`, the square
being cartesian. -/
def rightDerivedRestrictionIso {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (n : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (etaleRestriction.{u, u + 1} V.ι).obj
        (((etaleAbelianDirectImage.{u, u + 1} f).rightDerived n).obj F) ≅
      ((etaleAbelianDirectImage.{u, u + 1} (f ∣_ V)).rightDerived n).obj
        ((etaleRestriction.{u, u + 1} (f ⁻¹ᵁ V).ι).obj F) :=
  ((Stacks.Cohomology.ColimitsOfCohomology.rightDerivedCompExactIso
      (etaleAbelianDirectImage.{u, u + 1} f) (etaleRestriction.{u, u + 1} V.ι) n).app F).symm ≪≫
    (Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
      (etaleAbelianRestrictionPushforwardIsoOfIsPullback.{u, u + 1}
          (isPullback_morphismRestrict f V) :
        etaleRestriction.{u, u + 1} (f ⁻¹ᵁ V).ι ⋙ etaleAbelianDirectImage.{u, u + 1} (f ∣_ V) ≅
          etaleAbelianDirectImage.{u, u + 1} f ⋙ etaleRestriction.{u, u + 1} V.ι).symm n).app F ≪≫
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
      (etaleRestriction.{u, u + 1} (f ⁻¹ᵁ V).ι) (etaleAbelianDirectImage.{u, u + 1} (f ∣_ V))
      n).app F

/-- The open immersions of a cover of `Y` by opens cover the final object of `Y_étale`. -/
theorem coversTop_smallEtaleObj_opens {Y : Scheme.{u}} {ι : Type*} (V : ι → Y.Opens)
    (hV : ∀ y : Y, ∃ i, y ∈ V i) :
    Y.smallEtaleTopology.CoversTop fun i => smallEtaleObj (V i).ι := by
  classical
  let U : ι → Y.Etale := fun i => smallEtaleObj (V i).ι
  let top : Y.Etale := smallEtaleObj (𝟙 Y)
  have : IsIso top.hom := by
    rw [smallEtaleObj_hom]
    exact IsIso.id Y
  let a : ∀ i, U i ⟶ top := fun i =>
    MorphismProperty.Over.homMk (V i).ι (Category.comp_id _) trivial
  refine (Y.smallEtaleTopology.coversTop_iff_of_isTerminal top (isTerminalOfIsIsoHom top) U).2
    (Y.smallEtaleTopology.superset_covering (Sieve.ofArrows_le_ofObjects U a) ?_)
  rw [ofArrows_mem_smallEtaleTopology_iff a]
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨i, hi⟩ := hV y
  exact Set.mem_iUnion.2 ⟨i, Set.mem_range.2 ⟨⟨y, hi⟩, rfl⟩⟩

/-- **An abelian sheaf on `Y_étale` whose restrictions to the members of an open cover vanish
vanishes.** -/
theorem isZero_of_isZero_etaleRestriction {Y : Scheme.{u}} {ι : Type*} (V : ι → Y.Opens)
    (hV : ∀ y : Y, ∃ i, y ∈ V i) (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h : ∀ i, IsZero ((etaleRestriction.{u, u + 1} (V i).ι).obj G)) : IsZero G := by
  have hφ : IsIso (0 : G ⟶ 0) := by
    refine isIso_of_isIso_etaleRestrictionAt (0 : G ⟶ 0) (fun i => (V i).ι)
      (coversTop_smallEtaleObj_opens V hV) fun i => ?_
    have h0 : IsZero ((etaleRestriction.{u, u + 1} (V i).ι).obj
        (0 : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})) :=
      Functor.map_isZero _ (isZero_zero _)
    exact ⟨⟨0, (h i).eq_of_src _ _, h0.eq_of_src _ _⟩⟩
  exact (isZero_zero _).of_iso (asIso (0 : G ⟶ 0))

/-- **The reduction to an open cover of the target** (the first reduction in the proof of
[Stacks, Tag 0F10], part (1)). Let `f : X ⟶ Y` be quasi-compact and quasi-separated and let
`V i` be finitely many opens covering `Y`. If the higher direct images of torsion sheaves along
each `f|_{V i}` vanish above some bound, then `cd(f) < ∞`. -/
theorem etaleCohomologicalDimension_lt_top_of_openCover {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] {ι : Type*} [Finite ι] (V : ι → Y.Opens)
    (hV : ∀ y : Y, ∃ i, y ∈ V i)
    (h : ∀ i, ∃ d : ℕ, IsEtaleHigherDirectImageBound (f ∣_ V i) d) :
    etaleCohomologicalDimension f < ⊤ := by
  classical
  have := Fintype.ofFinite ι
  choose d hd using h
  refine lt_of_le_of_lt (etaleCohomologicalDimension_le f ((Finset.univ.sup d : ℕ) : ℕ∞) ?_)
    (ENat.natCast_lt_top _)
  intro F hF n hn
  have hn' : Finset.univ.sup d < n := by exact_mod_cast hn
  refine isZero_of_isZero_etaleRestriction V hV _ fun i => ?_
  refine (hd i _ (torsionSheafProperty_etaleRestriction _ F hF) n ?_).of_iso
    (rightDerivedRestrictionIso f (V i) n F)
  exact_mod_cast lt_of_le_of_lt (Finset.le_sup (f := d) (Finset.mem_univ i)) hn'

end AlgebraicGeometry.Scheme.Hom

end
