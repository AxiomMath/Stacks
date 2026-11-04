module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedSubschemeBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Compatibilities
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.HilbertCycleOfClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.RestrictedBaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyBaseChange

/-!
# Base change of the members of `Hilb(X/S, r)`

Let `f : X ⟶ S` be locally of finite presentation and let `Z ⊆ X` be a member of
`Hilb(X/S, r)`: a closed subscheme, flat, of finite presentation and of relative dimension at
most `r` over `S`. For a morphism `g : S' ⟶ S` the inverse image of `Z` in `X ×_S S'` is a
member of `Hilb(X ×_S S'/S', r)`, and by Tag 0H4T its cycle class is the base change of the cycle
class of `Z`. Consequently the image of the cycle class map of Tag 0H6V is stable under base
change: if `g^*α` is a cycle class for `g : S' ⟶ S`, then so is `(h ≫ g)^*α` for every
`h : S'' ⟶ S'`.

## Main definitions

* `Stacks.Chow.HilbertCycleDatum.baseChange` — the inverse image of a member of `Hilb(X/S, r)`
  in `X ×_S S'`, a member of `Hilb(X ×_S S'/S', r)`.
* `Stacks.Chow.HilbertCycleDatum.restrict` — the inverse image of a member of `Hilb(X/S, r)`
  along an isomorphism `j : U ⟶ X` of schemes over `S`.

## Main results

* `Stacks.Chow.HilbertCycleDatum.cycleFamily_baseChange` — the cycle class of the base change is
  the base change of the cycle class.
* `Stacks.Chow.HilbertCycleDatum.cycleFamily_restrict` — the cycle class of the restriction is
  the fibrewise restriction of the cycle class.
* `Stacks.Chow.pullbackInCycleClassImage_comp` — if `g^*α` is a cycle class then so is
  `(h ≫ g)^*α`.

## References

* [Stacks Project, Tag 0H4T](https://stacks.math.columbia.edu/tag/0H4T)
* [Stacks Project, Tag 0H6V](https://stacks.math.columbia.edu/tag/0H6V)
* [Stacks Project, Tag 0H4P](https://stacks.math.columbia.edu/tag/0H4P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

namespace HilbertCycleDatum

variable {X S S' U : Scheme.{u}} {f : X ⟶ S} {r : ℕ}

/-! ### Base change -/

/-- The inverse image in `X ×_S S'` of a closed subscheme `Z ⊆ X` is the base change of `Z`
along `g : S' ⟶ S`, as a closed subscheme of `X ×_S S'` over `S'`. -/
theorem isPullback_comap_fst_subschemeι (W : X.IdealSheafData) (g : S' ⟶ S) :
    IsPullback (Scheme.IdealSheafData.subschemeMap _ _ (pullback.fst f g)
        (W.le_map_comap (pullback.fst f g)))
      ((W.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g) (W.subschemeι ≫ f) g :=
  (isPullback_comap_subschemeι W (pullback.fst f g)).paste_vert (IsPullback.of_hasPullback f g)

/-- **The base change of a member of `Hilb(X/S, r)`** along `g : S' ⟶ S`: the inverse image of
the closed subscheme in `X ×_S S'`. -/
def baseChange (Z : HilbertCycleDatum f r) (g : S' ⟶ S) :
    HilbertCycleDatum (pullback.snd f g) r where
  ideal := Z.ideal.comap (pullback.fst f g)
  flat := MorphismProperty.of_isPullback (isPullback_comap_fst_subschemeι Z.ideal g) Z.flat
  locallyFinitePresentation := MorphismProperty.of_isPullback
    (isPullback_comap_fst_subschemeι Z.ideal g) Z.locallyFinitePresentation
  quasiCompact :=
    MorphismProperty.of_isPullback (isPullback_comap_fst_subschemeι Z.ideal g) Z.quasiCompact
  relativeDimensionLE := by
    have := Z.locallyFinitePresentation
    exact RelativeDimensionLE.of_isPullback (isPullback_comap_fst_subschemeι Z.ideal g)
      Z.relativeDimensionLE

/-- The ideal sheaf of the base change of `Z` along `g` is the inverse image of the ideal sheaf of
`Z` under the projection `X ×_S S' ⟶ X`. -/
@[simp]
theorem baseChange_ideal (Z : HilbertCycleDatum f r) (g : S' ⟶ S) :
    (Z.baseChange g).ideal = Z.ideal.comap (pullback.fst f g) :=
  rfl

/-- **Tag 0H4T for members of `Hilb`.** The cycle class of the base change of a member of
`Hilb(X/S, r)` along `g : S' ⟶ S` is the base change along `g` of its cycle class. -/
theorem cycleFamily_baseChange [LocallyOfFinitePresentation f] (Z : HilbertCycleDatum f r)
    (g : S' ⟶ S) :
    (Z.baseChange g).cycleFamily (pullback.snd f g) = baseChangeFamily f g r (Z.cycleFamily f) := by
  rw [cycleFamily_eq_familyAssociatedToClosedSubscheme (pullback.snd f g) (Z.baseChange g),
    cycleFamily_eq_familyAssociatedToClosedSubscheme f Z,
    familyAssociatedToClosedSubscheme_baseChange f g Z.ideal.subschemeι r
      (Z.topologicalKrullDim_pullback_fiberι_le f)]
  exact familyAssociatedToClosedSubscheme_eq_of_iso (pullback.snd f g)
    (Z.ideal.comap (pullback.fst f g)).subschemeι
    (pullback.snd Z.ideal.subschemeι (pullback.fst f g))
    (Z.ideal.comapIso (pullback.fst f g) ≪≫ pullbackSymmetry _ _)
    (by rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd,
      Scheme.IdealSheafData.comapIso_hom_fst]) r

/-- The cycle class map commutes with base change. -/
theorem cycleClassMap_map_baseChange [LocallyOfFinitePresentation f] (g : S' ⟶ S)
    (c : FreeAbelianGroup (HilbertCycleDatum f r)) :
    cycleClassMap (pullback.snd f g) r (FreeAbelianGroup.map (fun Z ↦ Z.baseChange g) c) =
      baseChangeFamily f g r (cycleClassMap f r c) := by
  induction c using FreeAbelianGroup.induction_on with
  | zero =>
    simp only [map_zero]
    exact (baseChangeFamilyHom f g r).map_zero.symm
  | of Z =>
    rw [FreeAbelianGroup.map_of_apply, cycleClassMap_of, cycleClassMap_of, cycleFamily_baseChange]
  | neg Z ih =>
    rw [map_neg, map_neg, map_neg, ih]
    exact ((baseChangeFamilyHom f g r).map_neg _).symm
  | add a b iha ihb =>
    rw [map_add, map_add, map_add, iha, ihb]
    exact ((baseChangeFamilyHom f g r).map_add _ _).symm

/-! ### Restriction along an isomorphism over the base -/

end HilbertCycleDatum

/-- The fibre map of the square with right-hand column the identity of the base is the fibre map
of the open immersion of the source. -/
theorem restrictedFiberMap_id_eq_fiberRestrict {X S U : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S)
    (j : U ⟶ X) (h : j ≫ f = fU) (h' : j ≫ f = fU ≫ 𝟙 S) (t : S) :
    restrictedFiberMap f fU j (𝟙 S) h' t = fiberRestrict f fU j h t := by
  refine pullback.hom_ext (?_ : _ ≫ f.fiberι t = _ ≫ f.fiberι t)
    (?_ : _ ≫ f.fiberToSpecResidueField t = _ ≫ f.fiberToSpecResidueField t)
  · exact (restrictedFiberMap_fiberι f fU j (𝟙 S) h' t).trans (fiberRestrict_fiberι f fU j h t).symm
  · refine (restrictedFiberMap_comp_fiberToSpecResidueField f fU j (𝟙 S) h' t).trans ?_
    rw [fiberRestrict_fiberToSpecResidueField, Scheme.residueFieldMap_id]
    simp

/-- **Tag 0H4T, restriction along an open immersion of the source over the same base.** The
fibrewise restriction of `[Z/X/S]_r` along an open immersion `j : U ⟶ X` of schemes over `S` is
the family `[Z ×_X U/U/S]_r` of the inverse image of `Z` in `U`. -/
theorem familyAssociatedToClosedSubscheme_fiberCycleRestrict {X S U Z : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [IsOpenImmersion j] (h : j ≫ f = fU) (i : Z ⟶ X) [IsClosedImmersion i] (r : ℕ) (s : S)
    (hdim : topologicalKrullDim ↥(pullback i (f.fiberι s)) ≤ (r : WithBot ℕ∞)) :
    fiberCycleRestrict f fU j h s r (familyAssociatedToClosedSubscheme f i r s) =
      familyAssociatedToClosedSubscheme fU (pullback.fst j i) r s := by
  have h' : j ≫ f = fU ≫ 𝟙 S := by rw [h, Category.comp_id]
  rw [← familyAssociatedToClosedSubscheme_openRestriction_apply f fU j (𝟙 S) h' i r s hdim]
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x => ?_)
  rw [fiberCycleRestrict_apply, (restrictedFamily f fU j (𝟙 S) h' r
    (familyAssociatedToClosedSubscheme f i r)).2 s x,
    restrictedFiberMap_id_eq_fiberRestrict f fU j h h' s]
  rfl

namespace HilbertCycleDatum

variable {X S S' U : Scheme.{u}} {f : X ⟶ S} {r : ℕ}

/-- The inverse image of a closed subscheme along an isomorphism `j : U ⟶ X` over `S` is, as a
scheme over `S`, isomorphic to the closed subscheme itself. -/
theorem comap_subschemeι_comp_eq {fU : U ⟶ S} (W : X.IdealSheafData) (j : U ⟶ X)
    (h : j ≫ f = fU) :
    (W.comap j).subschemeι ≫ fU =
      Scheme.IdealSheafData.subschemeMap _ _ j (W.le_map_comap j) ≫ W.subschemeι ≫ f := by
  rw [← h, ← Category.assoc, ← Category.assoc, (isPullback_comap_subschemeι W j).w]

/-- **The restriction of a member of `Hilb(X/S, r)`** along an isomorphism `j : U ⟶ X` of schemes
over `S`: the inverse image of the closed subscheme in `U`. -/
def restrict (Z : HilbertCycleDatum f r) {fU : U ⟶ S} (j : U ⟶ X) [IsIso j] (h : j ≫ f = fU) :
    HilbertCycleDatum fU r where
  ideal := Z.ideal.comap j
  flat := by
    have := Z.flat
    have : IsIso (Scheme.IdealSheafData.subschemeMap _ _ j (Z.ideal.le_map_comap j)) :=
      (isPullback_comap_subschemeι Z.ideal j).isIso_fst_of_isIso
    rw [comap_subschemeι_comp_eq Z.ideal j h]
    infer_instance
  locallyFinitePresentation := by
    have := Z.locallyFinitePresentation
    have : IsIso (Scheme.IdealSheafData.subschemeMap _ _ j (Z.ideal.le_map_comap j)) :=
      (isPullback_comap_subschemeι Z.ideal j).isIso_fst_of_isIso
    rw [comap_subschemeι_comp_eq Z.ideal j h]
    infer_instance
  quasiCompact := by
    have := Z.quasiCompact
    have : IsIso (Scheme.IdealSheafData.subschemeMap _ _ j (Z.ideal.le_map_comap j)) :=
      (isPullback_comap_subschemeι Z.ideal j).isIso_fst_of_isIso
    rw [comap_subschemeι_comp_eq Z.ideal j h]
    infer_instance
  relativeDimensionLE := by
    have := Z.locallyFinitePresentation
    have : IsIso (Scheme.IdealSheafData.subschemeMap _ _ j (Z.ideal.le_map_comap j)) :=
      (isPullback_comap_subschemeι Z.ideal j).isIso_fst_of_isIso
    have hsq : IsPullback (Scheme.IdealSheafData.subschemeMap _ _ j (Z.ideal.le_map_comap j))
        ((Z.ideal.comap j).subschemeι ≫ fU) (Z.ideal.subschemeι ≫ f) (𝟙 S) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, comap_subschemeι_comp_eq Z.ideal j h]⟩
    exact RelativeDimensionLE.of_isPullback hsq Z.relativeDimensionLE

/-- The ideal sheaf of the restriction of `Z` along `j` is the inverse image of the ideal sheaf of
`Z` under `j`. -/
@[simp]
theorem restrict_ideal (Z : HilbertCycleDatum f r) {fU : U ⟶ S} (j : U ⟶ X) [IsIso j]
    (h : j ≫ f = fU) : (Z.restrict j h).ideal = Z.ideal.comap j :=
  rfl

/-- The cycle class of the restriction of a member of `Hilb(X/S, r)` along an isomorphism over
`S` is the fibrewise restriction of its cycle class. -/
theorem cycleFamily_restrict [LocallyOfFinitePresentation f] (Z : HilbertCycleDatum f r)
    {fU : U ⟶ S} [LocallyOfFinitePresentation fU] (j : U ⟶ X) [IsIso j] (h : j ≫ f = fU) :
    (Z.restrict j h).cycleFamily fU =
      fun s => fiberCycleRestrict f fU j h s r (Z.cycleFamily f s) := by
  funext s
  rw [cycleFamily_eq_familyAssociatedToClosedSubscheme fU (Z.restrict j h),
    cycleFamily_eq_familyAssociatedToClosedSubscheme f Z,
    familyAssociatedToClosedSubscheme_fiberCycleRestrict f fU j h Z.ideal.subschemeι r s
      (Z.topologicalKrullDim_pullback_fiberι_le f s)]
  exact congrFun (familyAssociatedToClosedSubscheme_eq_of_iso fU (Z.ideal.comap j).subschemeι
    (pullback.fst j Z.ideal.subschemeι) (Z.ideal.comapIso j)
    (Scheme.IdealSheafData.comapIso_hom_fst _ _) r) s

/-- The cycle class map commutes with restriction along an isomorphism over the base. -/
theorem cycleClassMap_map_restrict [LocallyOfFinitePresentation f] {fU : U ⟶ S}
    [LocallyOfFinitePresentation fU] (j : U ⟶ X) [IsIso j] (h : j ≫ f = fU)
    (c : FreeAbelianGroup (HilbertCycleDatum f r)) :
    cycleClassMap fU r (FreeAbelianGroup.map (fun Z ↦ Z.restrict j h) c) =
      fun s => fiberCycleRestrict f fU j h s r (cycleClassMap f r c s) := by
  induction c using FreeAbelianGroup.induction_on with
  | zero =>
    funext s
    simp
  | of Z =>
    rw [FreeAbelianGroup.map_of_apply, cycleClassMap_of, cycleClassMap_of, cycleFamily_restrict]
  | neg Z ih =>
    funext s
    rw [map_neg, map_neg, map_neg, ih, Pi.neg_apply, Pi.neg_apply, map_neg]
  | add a b iha ihb =>
    funext s
    rw [map_add, map_add, map_add, iha, ihb, Pi.add_apply, Pi.add_apply, map_add]

end HilbertCycleDatum

/-! ### The image of the cycle class map along composites and isomorphisms -/

variable {X S S' S'' U : Scheme.{u}}

/-- If the base change of `α` along `g : S' ⟶ S` is a cycle class, then so is its base change
along any composite `h ≫ g`. -/
theorem pullbackInCycleClassImage_comp (f : X ⟶ S) [LocallyOfFinitePresentation f]
    [QuasiCompact f] (r : ℕ) (α : FamilyOfCycles f r) (g : S' ⟶ S) (h : S'' ⟶ S')
    (hα : PullbackInCycleClassImage f r α g) : PullbackInCycleClassImage f r α (h ≫ g) := by
  obtain ⟨c, hc⟩ := hα
  let E := pullbackLeftPullbackSndIso f g h
  have hE : E.inv ≫ pullback.snd (pullback.snd f g) h = pullback.snd f (h ≫ g) := by
    rw [Iso.inv_comp_eq, pullbackLeftPullbackSndIso_hom_snd]
  refine ⟨FreeAbelianGroup.map (fun Z ↦ Z.restrict E.inv hE)
    (FreeAbelianGroup.map (fun Z ↦ Z.baseChange h) c), ?_⟩
  rw [HilbertCycleDatum.cycleClassMap_map_restrict, HilbertCycleDatum.cycleClassMap_map_baseChange,
    hc, baseChangeFamily_baseChangeFamily_comp]
  funext s
  rw [fiberCycleRestrict_fiberCycleRestrict]
  exact fiberCycleRestrict_eq_self _ _ _ E.inv_hom_id s r _

/-- The property that `g^*α` is a cycle class is invariant under an isomorphism `j : U ⟶ X` of
schemes over `S`, the family being restricted along `j`. -/
theorem pullbackInCycleClassImage_of_restrict (f : X ⟶ S) [LocallyOfFinitePresentation f]
    [QuasiCompact f] (fU : U ⟶ S) [LocallyOfFinitePresentation fU] [QuasiCompact fU]
    (j : U ⟶ X) [IsIso j] (h : j ≫ f = fU) (r : ℕ) (α : FamilyOfCycles f r) (g : S' ⟶ S)
    (hα : PullbackInCycleClassImage f r α g) :
    PullbackInCycleClassImage fU r (fun s => fiberCycleRestrict f fU j h s r (α s)) g := by
  obtain ⟨c, hc⟩ := hα
  have : IsIso (pullbackRestrict f fU j h g) := by
    dsimp only [pullbackRestrict]
    infer_instance
  refine ⟨FreeAbelianGroup.map (fun Z ↦ Z.restrict (pullbackRestrict f fU j h g)
    (pullbackRestrict_snd f fU j h g)) c, ?_⟩
  rw [HilbertCycleDatum.cycleClassMap_map_restrict, hc]
  funext t
  exact (baseChangeFamily_fiberCycleRestrict f fU j h g r α t).symm

end Stacks.Chow

end
