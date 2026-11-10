module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StratificationRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StratificationSurgery
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerre.FiniteLocallyConstantAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.SmallEtaleStability
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ProperFinitenessStatement

/-!
# Extension by zero of the restriction of a constructible sheaf to a retrocompact open

Let `j : U ⟶ X` be a quasi-compact open immersion and let `F` be a constructible abelian sheaf on
the small étale site of `X`. Then `j_! j^{-1} F` is constructible. This is the case of Stacks 03S8
(2) and 095M used in remark (b) of the proof of Tag 0GJA, for an arbitrary coefficient universe
`AddCommGrpCat.{max (u + 1) v}` and with no hypothesis on `X`.

The proof refines, on each affine open `W` of `X`, the stratification of `W` adapted to `F` by the
two-piece partition `{W ∩ U, W ∖ U}`, which is a constructible partition of `W` because `U` is
retrocompact. On a stratum lying over `U` the inverse image of the counit `j_! j^{-1} F ⟶ F` is
invertible, so the inverse image of `j_! j^{-1} F` is that of `F`, finite locally constant; on a
stratum lying over the complement of `U` the inverse image of `j_! j^{-1} F` is zero.

Constructibility is stated on the size-bounded small étale site of Tag 021B and read on Mathlib's
small étale site through `AlgebraicGeometry.SmallEtale.sheafEquiv`, while extension by zero and the
two facts about strata are proved on Mathlib's site. They are carried across by
`AlgebraicGeometry.SmallEtale.restrictionPullbackBaseChangeIso`, the compatibility of the
equivalence with inverse image along a morphism of the big étale site.

## Main results

* `Stacks.EtaleCohomology.isIso_sheafPullback_map_counit_of_range_subset`: the inverse image of
  the counit `j_! j^{-1} F ⟶ F` to a scheme of the big étale site lying over `U` is invertible.
* `Stacks.EtaleCohomology.isZero_sheafPullback_extensionByZero_of_disjoint`: the inverse image of
  an extension by zero to a scheme of the big étale site lying over the complement of `U` is zero.
* `Stacks.EtaleCohomology.isConstructibleEtaleAbelianSheaf_extensionByZero_etaleRestriction`:
  `j_! j^{-1} F` is constructible for `j` a quasi-compact open immersion and `F` constructible.

## References

* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 095M](https://stacks.math.columbia.edu/tag/095M)
* [Stacks Project, Tag 0GJA](https://stacks.math.columbia.edu/tag/0GJA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u})
  [∀ (T T' : B.Scheme) (f : T' ⟶ T),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v}
      (AlgebraicGeometry.SmallEtale.topology B T.obj T.property)
      (AlgebraicGeometry.SmallEtale.topology B T'.obj T'.property)).IsRightAdjoint]

/-- The comparison of inverse images along `p` with the restriction to Mathlib's small étale
sites. -/
private noncomputable def restrictionPullbackIso {S T : B.Scheme} (p : T ⟶ S) :=
  SmallEtale.restrictionPullbackBaseChangeIso B AddCommGrpCat.{max (u + 1) v} p
    (etaleAbelianInverseImageDirectImageAdj.{u, v} (B.inclusion.map p))
    (Functor.sheafAdjunctionContinuous _ _ _ _)

/-- **The inverse image of the counit of `j_! ⊣ j^{-1}` to a scheme lying over `U` is
invertible**, read on the small étale site of Tag 021B. Let `j : U ⟶ S` be an open immersion and
let `p : T ⟶ S` be a morphism of the big étale site whose image lies in that of `j`. Then the
inverse image along `p` of the counit `j_! j^{-1} F ⟶ F`, transported to the size-bounded site by
`AlgebraicGeometry.SmallEtale.sheafEquiv`, is an isomorphism. -/
public theorem isIso_sheafPullback_map_counit_of_range_subset {S : B.Scheme} {U : Scheme.{u}}
    (j : U ⟶ S.obj) [IsOpenImmersion j]
    (F : Sheaf S.obj.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) {T : B.Scheme}
    (p : T ⟶ S) (hp : Set.range (B.inclusion.map p).base ⊆ Set.range j.base) :
    IsIso (((AlgebraicGeometry.smallEtaleBaseChange B p).sheafPullback
      AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).map
        ((SmallEtale.sheafEquiv B S.obj S.property AddCommGrpCat.{max (u + 1) v}).inverse.map
          ((extensionByZeroAdj.{u, v} j).counit.app F))) := by
  have h : IsIso ((etaleAbelianInverseImage.{u, v} (B.inclusion.map p)).map
      ((extensionByZeroAdj.{u, v} j).counit.app F)) :=
    isIso_etaleAbelianInverseImage_map_counit_of_factors (B.inclusion.map p) j
      (IsOpenImmersion.lift j (B.inclusion.map p) hp) (IsOpenImmersion.lift_fac _ _ _) F
  exact (NatIso.isIso_map_iff (restrictionPullbackIso B p)
    ((extensionByZeroAdj.{u, v} j).counit.app F)).mpr
    (Functor.map_isIso (SmallEtale.sheafEquiv B T.obj T.property
      AddCommGrpCat.{max (u + 1) v}).inverse _)

/-- **The inverse image of an extension by zero to a scheme lying over the complement vanishes**,
read on the small étale site of Tag 021B. Let `j : U ⟶ S` be étale and let `p : T ⟶ S` be a
morphism of the big étale site whose image is disjoint from that of `j`. Then the inverse image
along `p` of `j_! G`, transported to the size-bounded site by
`AlgebraicGeometry.SmallEtale.sheafEquiv`, is zero. -/
public theorem isZero_sheafPullback_extensionByZero_of_disjoint {S : B.Scheme} {U : Scheme.{u}}
    (j : U ⟶ S.obj) [Etale j]
    (G : Sheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) {T : B.Scheme}
    (p : T ⟶ S) (hp : Disjoint (Set.range (B.inclusion.map p).base) (Set.range j.base)) :
    IsZero (((AlgebraicGeometry.smallEtaleBaseChange B p).sheafPullback
      AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).obj
        ((SmallEtale.sheafEquiv B S.obj S.property AddCommGrpCat.{max (u + 1) v}).inverse.obj
          ((extensionByZero.{u, v} j).obj G))) := by
  let e := SmallEtale.sheafEquiv B T.obj T.property AddCommGrpCat.{max (u + 1) v}
  have h : IsZero ((etaleAbelianInverseImage.{u, v} (B.inclusion.map p)).obj
      ((extensionByZero.{u, v} j).obj G)) :=
    isZero_etaleAbelianInverseImage_extensionByZero_of_disjoint.{u, v}
      (B.inclusion.map p) j hp G
  exact (IsZero.of_full_of_faithful_of_isZero e.functor _
    (h.of_iso (e.counitIso.app _))).of_iso ((restrictionPullbackIso B p).app _)

variable [∀ (T : B.Scheme) (V : AlgebraicGeometry.SmallEtale B T.obj T.property),
  HasWeakSheafify ((AlgebraicGeometry.SmallEtale.topology B T.obj T.property).over V)
    AddCommGrpCat.{max (u + 1) v}]

/-- **Extension by zero of the restriction to a retrocompact open preserves constructibility.**
Let `j : U ⟶ X` be a quasi-compact open immersion and let `F` be a constructible abelian sheaf on
the small étale site of `X`. Then `j_! j^{-1} F` is constructible. This is Stacks 03S8 (2), or
095M, for the open subscheme `U`, as used in remark (b) of the proof of Tag 0GJA. -/
public theorem isConstructibleEtaleAbelianSheaf_extensionByZero_etaleRestriction
    {X : Scheme.{u}} (hX : B.Contains X) {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : IsConstructibleEtaleAbelianSheaf.{u, v} B X hX F) :
    IsConstructibleEtaleAbelianSheaf.{u, v} B X hX
      ((extensionByZero.{u, v} j).obj ((etaleRestriction.{u, v} j).obj F)) := by
  intro W
  obtain ⟨s, hs⟩ := hF W
  have : IsAffine W.1 := W.2
  set R : Set X := Set.range j.base
  have hRo : IsOpen R := j.isOpenEmbedding.isOpen_range
  have hRcon : Topology.IsConstructible (W.1.ι.base ⁻¹' R) := by
    have hRc : IsCompact (W.1.ι.base ⁻¹' R) := by
      rw [← Scheme.Pullback.range_snd]
      exact isCompact_range (pullback.snd j W.1.ι).base.hom.continuous
    exact hRc.isConstructible (hRo.preimage W.1.ι.base.hom.continuous)
  -- The partition of `W` into the parts inside and outside `U`.
  let A : Fin 2 → Set X := ![(W.1 : Set X) ∩ R, (W.1 : Set X) \ R]
  have hlc : ∀ i, IsLocallyClosed (A i) := by
    intro i; fin_cases i
    · exact (W.1.2.inter hRo).isLocallyClosed
    · exact W.1.2.isLocallyClosed.inter hRo.isClosed_compl.isLocallyClosed
  have hsub : ∀ i, A i ⊆ (W.1 : Set X) := by
    intro i; fin_cases i
    · exact Set.inter_subset_left
    · exact Set.sdiff_subset
  have hι : ∀ x : W.1.toScheme, W.1.ι.base x ∈ (W.1 : Set X) := fun x => by
    rw [← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩
  have hcon : ∀ i, Topology.IsConstructible (W.1.ι.base ⁻¹' A i) := by
    intro i; fin_cases i
    · have h : W.1.ι.base ⁻¹' ((W.1 : Set X) ∩ R) = W.1.ι.base ⁻¹' R := by
        ext x; simp [hι x]
      exact (congrArg Topology.IsConstructible h).mpr hRcon
    · have h : W.1.ι.base ⁻¹' ((W.1 : Set X) \ R) = (W.1.ι.base ⁻¹' R)ᶜ := by
        ext x; simp [hι x]
      exact (congrArg Topology.IsConstructible h).mpr hRcon.compl
  have hdisj : ∀ i k, i ≠ k → Disjoint (A i) (A k) := by
    intro i k hik; fin_cases i <;> fin_cases k
    · exact absurd rfl hik
    · exact Set.disjoint_left.2 fun x hx hx' => hx'.2 hx.2
    · exact Set.disjoint_left.2 fun x hx hx' => hx.2 hx'.2
    · exact absurd rfl hik
  have hcov : (W.1 : Set X) = ⋃ i, A i := by
    ext x; simp [A, Fin.exists_fin_two]; tauto
  let t := ConstructibleStratification.ofPartition B (B.obj X hX) W.1 A hlc hsub hcon hdisj hcov
  -- The common refinement of the two stratifications works.
  refine ⟨s.inf t, fun k => ?_⟩
  obtain ⟨l, g, hg⟩ := ConstructibleStratification.inf_factorsThroughStrata_left s t k
  obtain ⟨m, g', hg'⟩ := ConstructibleStratification.inf_factorsThroughStrata_right s t k
  have hrange : Set.range (B.inclusion.map ((s.inf t).inclusion k)).base ⊆ A m := by
    rw [← hg', ConstructibleStratification.range_map_comp,
      ← ConstructibleStratification.range_inclusion_ofPartition B (B.obj X hX) W.1 A hlc hsub
        hcon hdisj hcov m]
    exact Set.image_subset_range _ _
  fin_cases m
  · have hiso := isIso_sheafPullback_map_counit_of_range_subset.{u, v} B (S := B.obj X hX) j F
      ((s.inf t).inclusion k) (hrange.trans Set.inter_subset_right)
    refine ConstantSheaf.isFiniteLocallyConstant_congr _ (@asIso _ _ _ _ _ hiso).symm (hF := ?_)
    have hFk := AlgebraicGeometry.isFiniteLocallyConstant_smallEtaleSheafPullback' B
      AddCommGrpCat.{max (u + 1) v} g _ (hH := hs l)
    rw [← hg]
    exact ConstantSheaf.isFiniteLocallyConstant_congr _
      ((smallEtaleSheafPullbackCompIso B _ _ _ g (s.inclusion l) _).app _) (hF := hFk)
  · let := SmallEtale.hasSheafify_addCommGrp.{v} B ((s.inf t).piece k).obj
      ((s.inf t).piece k).property
    let : Abelian (Sheaf (SmallEtale.topology B ((s.inf t).piece k).obj
        ((s.inf t).piece k).property) AddCommGrpCat.{max (u + 1) v}) :=
      CategoryTheory.sheafIsAbelian
    exact ConstantSheaf.isFiniteLocallyConstant_congr _
      ((isZero_zero _).iso (isZero_sheafPullback_extensionByZero_of_disjoint.{u, v} B
        (S := B.obj X hX) j _ ((s.inf t).inclusion k)
        (Set.disjoint_of_subset_left hrange (Set.disjoint_left.2 fun _ hx => hx.2))))
      (hF := ConstantSheaf.isFiniteLocallyConstant_zero.{u, u + 1, v} _)

end Stacks.EtaleCohomology

end
