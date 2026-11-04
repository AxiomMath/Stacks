module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.ProperVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CoefficientUniverseReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HigherDirectImageFilteredColimits
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftDerived

/-!
# Proper direct images of torsion sheaves at every coefficient universe

The proper base change theorem is available for abelian sheaves on small étale sites with
coefficients in `AddCommGrpCat.{u + 1}`. This file transports three of its consequences to
coefficients in `AddCommGrpCat.{max (u + 1) v}` for every universe `v`.

## Main results

* `Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_of_ulift_mono`,
  `Stacks.EtaleCohomology.isZero_inverseImage_rightDerived_of_ulift_mono` and
  `Stacks.EtaleCohomology.isZero_inverseImage_directImage_of_ulift_mono`: the reduction. For
  `g` proper, `R^q g_* N` vanishes, and so do `t⁻¹ R^q g_* N` and `t⁻¹ g_* N`, as soon as the
  same holds for every sheaf with coefficients in `AddCommGrpCat.{u + 1}` whose universe lift is
  a subsheaf of `N`.
* `Stacks.EtaleCohomology.isZero_etaleAbelianInverseImage_rightDerived_directImage_of_isProper`
  and `Stacks.EtaleCohomology.isZero_etaleAbelianInverseImage_directImage_of_isProper`, with
  their `_ulift` versions at every coefficient universe: for `g` proper and `c` arbitrary,
  `c⁻¹ R^q g_* N = 0` for a torsion `N`, and `c⁻¹ g_* N = 0` for any `N`, whenever `N` vanishes
  on everything lying over the image of `c`.
* `Stacks.EtaleCohomology.isZero_etaleAbelianInverseImage_directImage_of_refinement_ulift`:
  for `g` proper with `j ≫ g = k` and `N` vanishing away from `X`, `g_* N` vanishes on the
  complement of `k(X)`.
* `Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_of_refinement_ulift`: if
  moreover `N` is torsion, `R^q g_* N = 0` for `q > 0`.
* `Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_of_isProper_ulift`:
  [Stacks, Tag 095U] at every coefficient universe.

## References

* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
* [Stacks Project, Tag 0F7G](https://stacks.math.columbia.edu/tag/0F7G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.UniverseLift

universe v u

namespace Stacks.EtaleCohomology

/-! ### Subsheaves of lifts -/

section Subsheaves

variable {A : Scheme.{u}} {N : Sheaf A.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
  {G : Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1}} (ι : (etaleUlift.{v} A).obj G ⟶ N)
  [Mono ι]

include ι in
/-- A sheaf whose universe lift is a subsheaf of a torsion sheaf is torsion. -/
theorem torsionSheafProperty_of_etaleUlift_mono
    (hN : Stacks.Torsion.torsionSheafProperty A.smallEtaleTopology N) :
    Stacks.Torsion.torsionSheafProperty A.smallEtaleTopology G := by
  refine torsionSheafProperty_of_etaleUlift.{v} fun U x => ?_
  obtain ⟨R, hR, hx⟩ := hN U (ι.hom.app (Opposite.op U) x)
  refine ⟨R, hR, fun V f hf => (hx V f hf).imp fun n hn => ⟨hn.1, ?_⟩⟩
  apply (AddCommGrpCat.mono_iff_injective _).1
    (inferInstance : Mono (((sheafToPresheaf _ _).map ι).app (Opposite.op V)))
  rw [map_nsmul, map_zero, ← hn.2]
  exact congrArg (n • ·) (by simp)

include ι in
/-- A sheaf whose universe lift is a subsheaf of a sheaf vanishing away from `X` vanishes away
from `X`. -/
theorem isZero_etaleAbelianInverseImage_of_etaleUlift_mono {T : Scheme.{u}} (t : T ⟶ A)
    (hN : IsZero ((etaleAbelianInverseImage.{u, v} t).obj N)) :
    IsZero ((etaleAbelianInverseImage.{u, 0} t).obj G) := by
  have h₁ : IsZero ((etaleAbelianInverseImage.{u, v} t).obj ((etaleUlift.{v} A).obj G)) :=
    have : Mono ((etaleAbelianInverseImage.{u, v} t).map ι) := inferInstance
    hN.of_mono ((etaleAbelianInverseImage.{u, v} t).map ι)
  have h₂ : IsZero ((etaleUlift.{v} T).obj ((etaleAbelianInverseImage.{u, 0} t).obj G)) :=
    h₁.of_iso ((etaleAbelianInverseImageUliftIso.{v} t).app G).symm
  rw [IsZero.iff_id_eq_zero] at h₂ ⊢
  exact (fullyFaithfulUliftSheafFunctor.{v, u + 1} T.smallEtaleTopology).map_injective
    (by simpa using h₂)

end Subsheaves

/-! ### The reduction -/

section Reduction

variable {A B : Scheme.{u}} (g : A ⟶ B) [IsProper g]

/-- A proper morphism is quasi-compact. -/
lemma quasiCompact_of_isProper : QuasiCompact g :=
  ⟨fun _ _ hU => g.isProperMap.isCompact_preimage hU⟩

/-- A proper morphism is quasi-separated. -/
lemma quasiSeparated_of_isProper : QuasiSeparated g :=
  ⟨⟨fun _ _ hU => (pullback.diagonal g).isClosedEmbedding.isCompact_preimage hU⟩⟩

/-- A functor preserving filtered colimits vanishes at `N` if it vanishes at every universe lift
that is a subsheaf of `N`. -/
private theorem isZero_obj_of_etaleUlift_mono {D : Type*} [Category D] [HasZeroMorphisms D]
    (N : Sheaf A.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (R : Sheaf A.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤ D)
    (hR : ∀ (I : Type (max (u + 1) v)) [SmallCategory I] [IsFiltered I],
      PreservesColimitsOfShape I R)
    (h : ∀ (G : Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1})
      (ι : (etaleUlift.{v} A).obj G ⟶ N), Mono ι → IsZero (R.obj ((etaleUlift.{v} A).obj G))) :
    IsZero (R.obj N) := by
  obtain ⟨I, _, _, D, ι, ⟨hc⟩, hD⟩ := exists_isColimit_etaleUlift_mono.{v} N
  have := hR I
  refine (IsZero.iff_id_eq_zero _).2 ((isColimitOfPreserves R hc).hom_ext fun i => ?_)
  obtain ⟨hmono, G, ⟨e⟩⟩ := hD i
  exact ((h G (e.hom ≫ ι.app i) inferInstance).of_iso (R.mapIso e.symm)).eq_of_src _ _

/-- **`R^q g_*` vanishes at `N` as soon as it vanishes at every sheaf with coefficients in
`AddCommGrpCat.{u + 1}` whose universe lift is a subsheaf of `N`**, for `g` proper. -/
theorem isZero_rightDerived_etaleAbelianDirectImage_of_ulift_mono (q : ℕ)
    (N : Sheaf A.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (h : ∀ (G : Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1})
      (ι : (etaleUlift.{v} A).obj G ⟶ N), Mono ι →
        IsZero (((etaleAbelianDirectImage.{u, 0} g).rightDerived q).obj G)) :
    IsZero (((etaleAbelianDirectImage.{u, v} g).rightDerived q).obj N) := by
  have := quasiCompact_of_isProper g
  have := quasiSeparated_of_isProper g
  refine isZero_obj_of_etaleUlift_mono.{v} N _
    (preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage_of_qcqs.{v} g q) fun G ι hι => ?_
  exact ((etaleUlift.{v} B).map_isZero (h G ι hι)).of_iso
    ((rightDerivedSheafPushforwardContinuousULiftIso.{v, u + 1} B.smallEtaleTopology
      A.smallEtaleTopology (smallEtaleBaseChange g) q).app G).symm

/-- **`t⁻¹ g_*` vanishes at `N` as soon as it vanishes at every sheaf with coefficients in
`AddCommGrpCat.{u + 1}` whose universe lift is a subsheaf of `N`**, for `g` proper. -/
theorem isZero_inverseImage_directImage_of_ulift_mono {T : Scheme.{u}} (t : T ⟶ B)
    (N : Sheaf A.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (h : ∀ (G : Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1})
      (ι : (etaleUlift.{v} A).obj G ⟶ N), Mono ι →
        IsZero ((etaleAbelianInverseImage.{u, 0} t).obj
          ((etaleAbelianDirectImage.{u, 0} g).obj G))) :
    IsZero ((etaleAbelianInverseImage.{u, v} t).obj
      ((etaleAbelianDirectImage.{u, v} g).obj N)) := by
  have := quasiCompact_of_isProper g
  have := quasiSeparated_of_isProper g
  have : ∀ (I : Type (max (u + 1) v)) [SmallCategory I] [IsFiltered I],
      PreservesColimitsOfShape I (etaleAbelianInverseImage.{u, v} t) := fun I _ _ =>
    (etaleAbelianInverseImageDirectImageAdj.{u, v} t).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have : ∀ (I : Type (max (u + 1) v)) [SmallCategory I] [IsFiltered I],
      PreservesColimitsOfShape I (etaleAbelianDirectImage.{u, v} g) := fun I _ _ => by
    have := preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage_of_qcqs.{v} g 0 I
    exact preservesColimitsOfShape_of_natIso
      (etaleAbelianDirectImage.{u, v} g).rightDerivedZeroIsoSelf
  refine isZero_obj_of_etaleUlift_mono.{v} N (etaleAbelianDirectImage.{u, v} g ⋙
    etaleAbelianInverseImage.{u, v} t) (fun I _ _ => inferInstance) fun G ι hι => ?_
  exact ((etaleUlift.{v} T).map_isZero (h G ι hι)).of_iso
    ((etaleAbelianInverseImageUliftIso.{v} t).app ((etaleAbelianDirectImage.{u, 0} g).obj G))

/-- **`t⁻¹ ∘ R^q g_*` vanishes at `N` as soon as it vanishes at every sheaf with coefficients in
`AddCommGrpCat.{u + 1}` whose universe lift is a subsheaf of `N`**, for `g` proper. -/
theorem isZero_inverseImage_rightDerived_of_ulift_mono {T : Scheme.{u}} (t : T ⟶ B) (q : ℕ)
    (N : Sheaf A.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (h : ∀ (G : Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1})
      (ι : (etaleUlift.{v} A).obj G ⟶ N), Mono ι →
        IsZero ((etaleAbelianInverseImage.{u, 0} t).obj
          (((etaleAbelianDirectImage.{u, 0} g).rightDerived q).obj G))) :
    IsZero ((etaleAbelianInverseImage.{u, v} t).obj
      (((etaleAbelianDirectImage.{u, v} g).rightDerived q).obj N)) := by
  have := quasiCompact_of_isProper g
  have := quasiSeparated_of_isProper g
  have : ∀ (I : Type (max (u + 1) v)) [SmallCategory I] [IsFiltered I],
      PreservesColimitsOfShape I (etaleAbelianInverseImage.{u, v} t) := fun I _ _ =>
    (etaleAbelianInverseImageDirectImageAdj.{u, v} t).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have := preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage_of_qcqs.{v} g q
  refine isZero_obj_of_etaleUlift_mono.{v} N ((etaleAbelianDirectImage.{u, v} g).rightDerived q ⋙
    etaleAbelianInverseImage.{u, v} t) (fun I _ _ => inferInstance) fun G ι hι => ?_
  have h₁ : IsZero ((etaleAbelianInverseImage.{u, v} t).obj ((etaleUlift.{v} B).obj
      (((etaleAbelianDirectImage.{u, 0} g).rightDerived q).obj G))) :=
    ((etaleUlift.{v} T).map_isZero (h G ι hι)).of_iso
      ((etaleAbelianInverseImageUliftIso.{v} t).app
        (((etaleAbelianDirectImage.{u, 0} g).rightDerived q).obj G))
  exact h₁.of_iso ((etaleAbelianInverseImage.{u, v} t).mapIso
    ((rightDerivedSheafPushforwardContinuousULiftIso.{v, u + 1} B.smallEtaleTopology
      A.smallEtaleTopology (smallEtaleBaseChange g) q).app G).symm)

end Reduction

/-! ### Higher direct images as cohomology sheaves of the derived direct image -/

section Homology

attribute [local instance] HasDerivedCategory.standard

/-- The higher direct image `R^q f_* M` of an abelian sheaf is the `q`-th cohomology sheaf of
the unbounded derived direct image of `M` placed in degree zero. -/
def etaleAbelianRightDerivedDirectImageIsoHomology {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℕ)
    (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    ((etaleAbelianDirectImage.{u, v} f).rightDerived q).obj M ≅
      (DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
        q).obj ((etaleAbelianDerivedDirectImage.{u, v} f).obj
          ((DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj M)) :=
  ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
    (etaleAbelianDirectImage.{u, v} f) (etaleAbelianDerivedDirectImage.{u, v} f)
    (etaleAbelianDerivedDirectImageUnit.{u, v} f)
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective q).app M).symm

end Homology

/-! ### Proper direct images vanish over a locus the sheaf misses -/

section Closed

attribute [local instance] HasDerivedCategory.standard

variable {A B W : Scheme.{u}} (g : A ⟶ B) [IsProper g] (c : W ⟶ B)

omit [IsProper g] in
/-- The projection of `A ×_B W` to `A` lands over the image of `c`. -/
lemma range_pullback_fst_subset_preimage_range :
    Set.range (pullback.fst g c).base ⊆ g.base ⁻¹' Set.range c.base := by
  rintro _ ⟨p, rfl⟩
  exact ⟨(pullback.snd g c).base p, by
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩

/-- **`c⁻¹ R^q g_* N = 0` for every `q`**, for `g` proper, `c` arbitrary and `N` a torsion sheaf
whose inverse image to everything lying over the image of `c` vanishes, with coefficients in
`AddCommGrpCat.{u + 1}`. -/
theorem isZero_etaleAbelianInverseImage_rightDerived_directImage_of_isProper
    (N : Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hN : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ A), Set.range t.base ⊆ g.base ⁻¹' Set.range c.base →
      IsZero ((etaleAbelianInverseImage.{u, 0} t).obj N))
    (hT : Stacks.Torsion.torsionSheafProperty A.smallEtaleTopology N) (q : ℕ) :
    IsZero ((etaleAbelianInverseImage.{u, 0} c).obj
      (((etaleAbelianDirectImage.{u, 0} g).rightDerived q).obj N)) := by
  have sq := IsPullback.of_hasPullback g c
  have hP : IsZero ((etaleAbelianInverseImage.{u, 0} (pullback.fst g c)).obj N) :=
    hN _ (range_pullback_fst_subset_preimage_range g c)
  have := isIso_etaleAbelianSheafDerivedBaseChange_of_isProper g c (pullback.fst g c)
    (pullback.snd g c) sq N hT
  refine IsZero.of_iso ?_ ((etaleAbelianInverseImage.{u, 0} c).mapIso
    (etaleAbelianRightDerivedDirectImageIsoHomology.{0, u} g q N))
  refine IsZero.of_iso ?_ (((etaleAbelianInverseImage.{u, 0} c).mapDerivedCategoryHomologyIso
    q).app _).symm
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ q).mapIso
    (asIso (etaleAbelianSheafDerivedBaseChange.{u, 0} g c (pullback.fst g c)
      (pullback.snd g c) sq.w N)))
  refine (etaleAbelianDerivedDirectImage.{u, 0} (pullback.snd g c) ⋙
    DerivedCategory.homologyFunctor _ q).map_isZero ?_
  refine IsZero.of_iso ?_ (((etaleAbelianInverseImage.{u, 0}
    (pullback.fst g c)).mapDerivedCategorySingleFunctor 0).app N)
  exact (DerivedCategory.singleFunctor _ 0).map_isZero hP

end Closed

section ClosedUlift

variable {A B W : Scheme.{u}} (g : A ⟶ B) [IsProper g] (c : W ⟶ B)

/-- **`c⁻¹ g_* N = 0`**, for `g` proper, `c` arbitrary and `N` an abelian sheaf whose inverse
image to everything lying over the image of `c` vanishes, with coefficients in
`AddCommGrpCat.{u + 1}`. -/
theorem isZero_etaleAbelianInverseImage_directImage_of_isProper
    (N : Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hN : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ A), Set.range t.base ⊆ g.base ⁻¹' Set.range c.base →
      IsZero ((etaleAbelianInverseImage.{u, 0} t).obj N)) :
    IsZero ((etaleAbelianInverseImage.{u, 0} c).obj
      ((etaleAbelianDirectImage.{u, 0} g).obj N)) := by
  have sq := IsPullback.of_hasPullback g c
  have := isIso_etaleAbelianBaseChange_of_isProper g c (pullback.fst g c) (pullback.snd g c) sq
  refine IsZero.of_iso ?_ ((asIso (etaleAbelianBaseChange.{u, 0} g c (pullback.fst g c)
    (pullback.snd g c) sq.w)).app N)
  exact (etaleAbelianDirectImage.{u, 0} (pullback.snd g c)).map_isZero
    (hN _ (range_pullback_fst_subset_preimage_range g c))

/-- **`c⁻¹ R^q g_* N = 0` for every `q`, at every coefficient universe**, for `g` proper, `c`
arbitrary and `N` a torsion sheaf whose inverse image to everything lying over the image of `c`
vanishes. -/
theorem isZero_etaleAbelianInverseImage_rightDerived_directImage_of_isProper_ulift
    (N : Sheaf A.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hN : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ A), Set.range t.base ⊆ g.base ⁻¹' Set.range c.base →
      IsZero ((etaleAbelianInverseImage.{u, v} t).obj N))
    (hT : Stacks.Torsion.torsionSheafProperty A.smallEtaleTopology N) (q : ℕ) :
    IsZero ((etaleAbelianInverseImage.{u, v} c).obj
      (((etaleAbelianDirectImage.{u, v} g).rightDerived q).obj N)) := by
  refine isZero_inverseImage_rightDerived_of_ulift_mono.{v, u} g c q N fun G ι _ => ?_
  exact isZero_etaleAbelianInverseImage_rightDerived_directImage_of_isProper g c G
    (fun _ t ht => isZero_etaleAbelianInverseImage_of_etaleUlift_mono ι t (hN t ht))
    (torsionSheafProperty_of_etaleUlift_mono ι hT) q

/-- **`c⁻¹ g_* N = 0`, at every coefficient universe**, for `g` proper, `c` arbitrary and `N` an
abelian sheaf whose inverse image to everything lying over the image of `c` vanishes. -/
theorem isZero_etaleAbelianInverseImage_directImage_of_isProper_ulift
    (N : Sheaf A.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hN : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ A), Set.range t.base ⊆ g.base ⁻¹' Set.range c.base →
      IsZero ((etaleAbelianInverseImage.{u, v} t).obj N)) :
    IsZero ((etaleAbelianInverseImage.{u, v} c).obj
      ((etaleAbelianDirectImage.{u, v} g).obj N)) := by
  refine isZero_inverseImage_directImage_of_ulift_mono.{v, u} g c N fun G ι _ => ?_
  exact isZero_etaleAbelianInverseImage_directImage_of_isProper g c G
    (fun _ t ht => isZero_etaleAbelianInverseImage_of_etaleUlift_mono ι t (hN t ht))

end ClosedUlift

/-! ### The consequences of proper base change at every coefficient universe -/

section Refinement

variable {X A B : Scheme.{u}} {j : X ⟶ A} {k : X ⟶ B} {g : A ⟶ B} [IsOpenImmersion j]
  [IsOpenImmersion k] (hjk : j ≫ g = k)
  (N : Sheaf A.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
  (hN : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ A), Disjoint (Set.range t.base) (Set.range j.base) →
    IsZero ((etaleAbelianInverseImage.{u, v} t).obj N))

include hjk hN in
/-- **`g_* N` vanishes on the complement of `X`**, at every coefficient universe, for `g` proper
and `N` vanishing away from `X`. -/
theorem isZero_etaleAbelianInverseImage_directImage_of_refinement_ulift [IsProper g] :
    IsZero ((etaleAbelianInverseImage.{u, v} (openImmersionComplementι k)).obj
      ((etaleAbelianDirectImage.{u, v} g).obj N)) := by
  refine isZero_inverseImage_directImage_of_ulift_mono.{v, u} g (openImmersionComplementι k) N
    fun G ι _ => ?_
  exact isZero_etaleAbelianInverseImage_directImage_of_refinement hjk G
    (fun _ t ht => isZero_etaleAbelianInverseImage_of_etaleUlift_mono ι t (hN t ht))

include hjk hN in
/-- **`R^q g_* N = 0` for `q > 0`**, at every coefficient universe, for `g` proper and `N` a
torsion sheaf vanishing away from `X`. -/
theorem isZero_rightDerived_etaleAbelianDirectImage_of_refinement_ulift [IsProper g]
    (hT : Stacks.Torsion.torsionSheafProperty A.smallEtaleTopology N) (q : ℕ) (hq : 0 < q) :
    IsZero (((etaleAbelianDirectImage.{u, v} g).rightDerived q).obj N) := by
  refine isZero_rightDerived_etaleAbelianDirectImage_of_ulift_mono.{v, u} g q N fun G ι _ => ?_
  let : HasDerivedCategory (Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    HasDerivedCategory.standard _
  have hac : (etaleAbelianDirectImage.{u, 0} g).rightAcyclic G :=
    (rightAcyclic_etaleAbelianDirectImage_iff.{u, 0} g G).2 fun p hp =>
      isZero_homology_etaleAbelianDerivedDirectImage_of_refinement hjk G
        (fun _ t ht => isZero_etaleAbelianInverseImage_of_etaleUlift_mono ι t (hN t ht))
        (torsionSheafProperty_of_etaleUlift_mono ι hT) p hp
  rw [Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived] at hac
  exact hac q hq

end Refinement

/-- **[Stacks, Tag 095U] at every coefficient universe.** Let `f : X ⟶ Y` be a proper morphism
all of whose fibres have dimension `≤ n`. Then for every torsion abelian sheaf `F` on `X_étale`
with coefficients in `AddCommGrpCat.{max (u + 1) v}`, `R^q f_* F = 0` for every `q > 2n`. -/
theorem isZero_rightDerived_etaleAbelianDirectImage_of_isProper_ulift {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] (n : ℕ) (hfib : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ n)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (q : ℕ) (hq : 2 * n < q) :
    IsZero (((etaleAbelianDirectImage.{u, v} f).rightDerived q).obj F) := by
  refine isZero_rightDerived_etaleAbelianDirectImage_of_ulift_mono.{v, u} f q F fun G ι _ => ?_
  exact isZero_rightDerived_etaleAbelianDirectImage_of_isProper f n hfib G
    (torsionSheafProperty_of_etaleUlift_mono ι hF) q hq

end Stacks.EtaleCohomology

end
