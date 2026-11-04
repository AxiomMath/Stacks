module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CapClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedSubschemeComposition
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedSubschemeRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleClassAfterProperCover
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FamilyOpenCover
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FiberCycleFiniteSum
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.HilbertCycleExtend
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleRestriction
import StacksFrontier.AlgebraicGeometry.BlowupAmpleFamily.Coproduct

/-!
# The coproduct clause of the Noetherian induction for Tag 0H59

[Tag 0H59](https://stacks.math.columbia.edu/tag/0H59) says that for `f : X ⟶ S` of finite type
with `S` Noetherian, `r ≥ 0` and `α` a relative `r`-cycle on `X/S`, there is a proper, completely
decomposed (Definition [0GTI](https://stacks.math.columbia.edu/tag/0GTI)) morphism `g : S' ⟶ S`
with `g^*α` in the image of the cycle class map
[0H58](https://stacks.math.columbia.edu/tag/0H58). Its proof is a Noetherian induction on closed
subschemes of `S` with three clauses: the empty base, binary coproducts of bases, and an integral
base. The induction itself, and the empty clause, are
`Stacks.Chow.exists_isProper_isCompletelyDecomposed_pullbackInCycleClassImage` and
`Stacks.Chow.pullbackInCycleClassImage_of_isEmpty`; the integral clause is
`Stacks.Chow.exists_isProper_pullbackInCycleClassImage_of_isIntegral`.

This file provides the cycle-theoretic half of the coproduct clause. Given cycle classes over `T₁`
and over `T₂` realising `g₁^*α` and `g₂^*α`, it produces a cycle class over `T₁ ⨿ T₂` and shows
that *every* family of cycles whose restrictions along the two coproduct inclusions are `g₁^*α`
and `g₂^*α` is the cycle class of that class. That `g^*α`, `g = coprod.desc g₁ g₂`, has those
restrictions is the clause of [Tag 0H4R](https://stacks.math.columbia.edu/tag/0H4R) saying that
base change commutes with restriction to an open subscheme of the base,
`Stacks.Chow.restrictedFamily_baseChangeFamily`; the coproduct clause itself is
`Stacks.Chow.pullbackInCycleClassImage_coprod_desc`, and Tag 0H59 is
`Stacks.Chow.exists_isProper_isCompletelyDecomposed_relativeCycleClassMap_eq`.

## Main definitions

* `Stacks.Chow.restrictedFamilyHom` — restriction of families of cycles along a commutative
  square of open immersions, as a homomorphism of abelian groups.
* `Stacks.Chow.coprodBaseChangeInl`, `Stacks.Chow.coprodBaseChangeInr` — the base change of `X`
  along one summand of `coprod.desc g₁ g₂`, viewed inside the base change along the whole
  morphism.

## Main results

* `Stacks.Chow.HilbertCycleDatum.topologicalKrullDim_pullback_fiberι_le` — a member of
  `Hilb(X/S, r)` satisfies the subscheme-level fibre dimension bound `dim(Z ×_X X_s) ≤ r` of
  Example 0H4S.
* `Stacks.Chow.HilbertCycleDatum.cycleFamily_eq_familyAssociatedToClosedSubscheme` — the cycle
  class `[Z/X/S]_r` of Tag 0H6V is the family of Example 0H4S attached to the closed subscheme.
* `Stacks.Chow.HilbertCycleDatum.restrictedFamily_cycleFamily_extend` — the cycle class of
  `Stacks.Chow.HilbertCycleDatum.extend`, restricted back along the same clopen immersion, is the
  cycle class one started from.
* `Stacks.Chow.HilbertCycleDatum.restrictedFamily_cycleFamily_eq_zero_of_disjoint` — the cycle
  class of a member of `Hilb` restricts to zero along an open immersion whose range misses the
  subscheme.
* `Stacks.Chow.exists_cycleClassMap_restrictedFamily_eq` — for a pair of disjoint clopen pieces,
  two classes on the pieces assemble to a class on the whole whose cycle class restricts to the
  two given ones.
* `Stacks.Chow.familyOfCycles_eq_of_isPullback_pair` — a family of cycles is determined by its
  restrictions along two cartesian squares of open immersions whose base maps cover.
* `Stacks.Chow.exists_restrictedFamily_eq_baseChangeFamily_coprod` — a family over `T₁ ⨿ T₂`
  restricting to `g₁^*α` and `g₂^*α` exists.
* `Stacks.Chow.exists_cycleClassMap_eq_of_restrictedFamily_coprod` — the coproduct clause for a
  family presented by its restrictions.

## Implementation notes

The restriction behaviour of the cycle class map comes from
`Stacks.Chow.familyAssociatedToClosedSubscheme_openRestriction` (Tag 0H4T), whose hypothesis is
the dimension bound on `Z ×_X X_s`, while a `Stacks.Chow.HilbertCycleDatum` carries only
`RelativeDimensionLE (Z ⟶ S) r`.
`Stacks.Chow.HilbertCycleDatum.structureModule_fiberSupport_dimension_le` bounds the dimension of
the fibrewise support of `i_* 𝒪_Z`, and
`Stacks.Chow.supp_pullback_fiberι_pushforwardStructureSheaf` identifies that support with the
image of `Z ×_X X_s` under a closed immersion, which gives
`Stacks.Chow.HilbertCycleDatum.topologicalKrullDim_pullback_fiberι_le`.

For the extension `Stacks.Chow.HilbertCycleDatum.extend` of a datum along a closed immersion `j`,
the square comparing the original closed subscheme with the pushed-forward one has
`AlgebraicGeometry.Scheme.IdealSheafData.mapSubschemeIso` along the top and `j` along the bottom,
so it is cartesian by `CategoryTheory.IsPullback.of_horiz_isIso_mono`, and
`Stacks.Chow.familyAssociatedToClosedSubscheme_eq_of_iso` applies.

`Stacks.Chow.familyOfCycles_eq_of_coprod_base` is stated for the squares
`pullback.snd p coprod.inl`, whereas the squares here have `pullback f g₁` on the corner. So
rigidity is proved for an arbitrary pair of squares,
`Stacks.Chow.familyOfCycles_eq_of_isPullback_pair`, assuming only that the part of the source
lying over the open part of the base is covered by the open subscheme; for a cartesian square
that is `Stacks.Chow.range_eq_preimage_range_of_isPullback`.

## References

* [Stacks Project, Lemma 0H59](https://stacks.math.columbia.edu/tag/0H59)
* [Stacks Project, Equation 0H58](https://stacks.math.columbia.edu/tag/0H58)
* [Stacks Project, Definition 0GTI](https://stacks.math.columbia.edu/tag/0GTI)
* [Stacks Project, Lemma 081R](https://stacks.math.columbia.edu/tag/081R)
* [Stacks Project, Section 0H6V](https://stacks.math.columbia.edu/tag/0H6V)
* [Stacks Project, Lemma 0H4R](https://stacks.math.columbia.edu/tag/0H4R)
* [Stacks Project, Lemma 0H4S](https://stacks.math.columbia.edu/tag/0H4S)
* [Stacks Project, Lemma 0H4T](https://stacks.math.columbia.edu/tag/0H4T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

namespace HilbertCycleDatum

variable {X S : Scheme.{u}} {r : ℕ}

/-! ### A member of `Hilb` as a closed subscheme of Example 0H4S -/

/-- The cycle class `[Z/X/S]_r` of a member of `Hilb(X/S, r)` is the family of cycles attached to
the direct image of its structure sheaf. -/
theorem cycleFamily_eq (f : X ⟶ S) [LocallyOfFinitePresentation f] (Z : HilbertCycleDatum f r) :
    Z.cycleFamily f =
      familyAssociatedToModule f Z.structureModule r
        (Z.structureModule_fiberSupport_dimension_le f) :=
  rfl

/-- The module whose associated family is the cycle class of a member of `Hilb(X/S, r)` is the
direct image of the structure sheaf of the closed subscheme. -/
theorem structureModule_eq (f : X ⟶ S) (Z : HilbertCycleDatum f r) :
    Z.structureModule =
      (Scheme.Modules.pushforward Z.ideal.subschemeι).obj (Ample.unitModule Z.ideal.subscheme) :=
  rfl

/-- The support of that module is exactly the closed subscheme. -/
theorem supp_structureModule (f : X ⟶ S) (Z : HilbertCycleDatum f r) :
    SheafOfModules.supp Z.structureModule =
      Set.range (ConcreteCategory.hom Z.ideal.subschemeι.base) :=
  supp_pushforwardStructureSheaf Z.ideal.subschemeι

/-- A member `Z` of `Hilb(X/S, r)` satisfies the subscheme-level fibre dimension bound of Example
0H4S: for every `s : S`, the fibre product `Z ×_X X_s` has dimension at most `r`. -/
theorem topologicalKrullDim_pullback_fiberι_le (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (Z : HilbertCycleDatum f r) (s : S) :
    topologicalKrullDim (pullback Z.ideal.subschemeι (f.fiberι s) : Scheme.{u}) ≤
      (r : WithBot ℕ∞) := by
  refine le_of_eq_of_le ?_ (Z.structureModule_fiberSupport_dimension_le f s)
  rw [structureModule_eq, supp_pullback_fiberι_pushforwardStructureSheaf Z.ideal.subschemeι f s]
  exact IsHomeomorph.topologicalKrullDim_eq _
    (IsClosedImmersion.isClosedEmbedding
      (pullback.snd Z.ideal.subschemeι (f.fiberι s))).isEmbedding.toHomeomorph.isHomeomorph

/-- **The cycle class of Tag 0H6V is the family of Example 0H4S.** For a member of
`Hilb(X/S, r)`, `[Z/X/S]_r` as computed from the direct image of the structure sheaf agrees with
`[Z/X/S]_r` as computed from the closed subscheme. -/
theorem cycleFamily_eq_familyAssociatedToClosedSubscheme (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (Z : HilbertCycleDatum f r) :
    Z.cycleFamily f = familyAssociatedToClosedSubscheme f Z.ideal.subschemeι r :=
  (familyAssociatedToClosedSubscheme_eq_familyAssociatedToModule f Z.ideal.subschemeι r
    (Z.topologicalKrullDim_pullback_fiberι_le f)).symm

/-! ### Restricting the cycle class of a member of `Hilb` -/

/-- **Tag 0H4T for the cycle class map.** The restriction of the cycle class of a member of
`Hilb(X/S, r)` along a commutative square of open immersions is the family of Example 0H4S of the
inverse image `Z ∩ U` of the closed subscheme. -/
theorem restrictedFamily_cycleFamily {U V : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (fU : U ⟶ V) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [IsOpenImmersion j] (i : V ⟶ S) [IsOpenImmersion i] (h : j ≫ f = fU ≫ i)
    (Z : HilbertCycleDatum f r) :
    (restrictedFamily f fU j i h r (Z.cycleFamily f)).1 =
      familyAssociatedToClosedSubscheme fU (pullback.fst j Z.ideal.subschemeι) r := by
  rw [Z.cycleFamily_eq_familyAssociatedToClosedSubscheme f]
  exact familyAssociatedToClosedSubscheme_openRestriction f fU j i h Z.ideal.subschemeι r
    (Z.topologicalKrullDim_pullback_fiberι_le f)

/-- **Vanishing of the restriction away from the subscheme.** If the open subscheme `U ⊆ X`
misses the closed subscheme of a member of `Hilb(X/S, r)` then the restriction of its cycle class
to `U/V` is zero. -/
theorem restrictedFamily_cycleFamily_eq_zero_of_disjoint {U V : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (fU : U ⟶ V) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [IsOpenImmersion j] (i : V ⟶ S) [IsOpenImmersion i] (h : j ≫ f = fU ≫ i)
    (Z : HilbertCycleDatum f r)
    (hdisj : Disjoint (Set.range (ConcreteCategory.hom j.base))
      (Set.range (ConcreteCategory.hom Z.ideal.subschemeι.base))) :
    (restrictedFamily f fU j i h r (Z.cycleFamily f)).1 = 0 := by
  rw [Z.cycleFamily_eq f, familyAssociatedToModule_openRestriction f fU j i h Z.structureModule r
    (Z.structureModule_fiberSupport_dimension_le f)]
  have hsupp : SheafOfModules.supp ((Scheme.Modules.pullback j).obj Z.structureModule) = ∅ := by
    rw [Stacks.Modules.supp_pullback, Z.supp_structureModule f, Set.eq_empty_iff_forall_notMem]
    exact fun u hu ↦ Set.disjoint_left.mp hdisj ⟨u, rfl⟩ hu
  funext t
  apply Subtype.ext
  ext x
  rw [familyAssociatedToModule_apply_coeff, Stacks.Modules.supp_pullback, hsupp,
    Set.preimage_empty]
  simp

/-- **Extending a member of `Hilb` and restricting back gives the cycle class one started
from.** Let `j : U ⟶ X` be a clopen immersion over a quasi-compact open immersion `i : V ⟶ S` of
the base, and let `Z` be a member of `Hilb(U/V, r)`. The cycle class of the extension
`Stacks.Chow.HilbertCycleDatum.extend` of `Z`, restricted along the same square, is the cycle
class of `Z`. -/
theorem restrictedFamily_cycleFamily_extend {U V : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (fU : U ⟶ V) [LocallyOfFinitePresentation fU] (j : U ⟶ X)
    [IsClosedImmersion j] [IsOpenImmersion j] (i : V ⟶ S) [IsOpenImmersion i] [QuasiCompact i]
    (h : j ≫ f = fU ≫ i) (Z : HilbertCycleDatum fU r) :
    (restrictedFamily f fU j i h r ((extend f fU j i r Z h).cycleFamily f)).1 =
      Z.cycleFamily fU := by
  have hsq : IsPullback (Scheme.IdealSheafData.mapSubschemeIso Z.ideal j).hom
      Z.ideal.subschemeι (Z.ideal.map j).subschemeι j :=
    IsPullback.of_horiz_isIso_mono
      ⟨Scheme.IdealSheafData.mapSubschemeIso_hom_subschemeι Z.ideal j⟩
  rw [restrictedFamily_cycleFamily f fU j i h (extend f fU j i r Z h),
    Z.cycleFamily_eq_familyAssociatedToClosedSubscheme fU]
  exact (familyAssociatedToClosedSubscheme_eq_of_iso fU Z.ideal.subschemeι
    (pullback.fst j (Z.ideal.map j).subschemeι) hsq.flip.isoPullback
    hsq.flip.isoPullback_hom_fst r).symm

/-- The closed subscheme cut out by a pushed-forward ideal sheaf lies in the image of the closed
immersion it was pushed along. -/
theorem range_subschemeι_map_subset {Y : Scheme.{u}} (I : Y.IdealSheafData) (j : Y ⟶ X)
    [IsClosedImmersion j] :
    Set.range (ConcreteCategory.hom (I.map j).subschemeι.base) ⊆
      Set.range (ConcreteCategory.hom j.base) := by
  rintro _ ⟨z, rfl⟩
  refine ⟨I.subschemeι ((Scheme.IdealSheafData.mapSubschemeIso I j).inv z), ?_⟩
  have hz : (Scheme.IdealSheafData.mapSubschemeIso I j).hom
      ((Scheme.IdealSheafData.mapSubschemeIso I j).inv z) = z := by
    change ((Scheme.IdealSheafData.mapSubschemeIso I j).inv ≫
      (Scheme.IdealSheafData.mapSubschemeIso I j).hom) z = z
    rw [Iso.inv_hom_id]
    rfl
  have := congrArg (fun m : I.subscheme ⟶ X =>
      m ((Scheme.IdealSheafData.mapSubschemeIso I j).inv z))
    (Scheme.IdealSheafData.mapSubschemeIso_hom_subschemeι I j)
  simpa only [Scheme.Hom.comp_apply, hz] using this.symm

end HilbertCycleDatum

/-! ### Restriction as a homomorphism -/

/-- Restriction of families of cycles along a commutative square of open immersions, packaged as
a homomorphism of abelian groups. -/
def restrictedFamilyHom {W T W₁ T₁ : Scheme.{u}} (p : W ⟶ T) [LocallyOfFiniteType p]
    (p₁ : W₁ ⟶ T₁) [LocallyOfFiniteType p₁] (j : W₁ ⟶ W) [IsOpenImmersion j]
    (i : T₁ ⟶ T) [IsOpenImmersion i] (h : j ≫ p = p₁ ≫ i) (r : ℕ) :
    FamilyOfCycles p r →+ FamilyOfCycles p₁ r where
  toFun α := (restrictedFamily p p₁ j i h r α).1
  map_zero' := by
    funext t
    apply Subtype.ext
    ext x
    rw [(restrictedFamily p p₁ j i h r 0).2 t x]
    rfl
  map_add' α β := by
    funext t
    apply Subtype.ext
    ext x
    rw [(restrictedFamily p p₁ j i h r (α + β)).2 t x]
    change _ = ((restrictedFamily p p₁ j i h r α).1 t).1 x +
      ((restrictedFamily p p₁ j i h r β).1 t).1 x
    rw [(restrictedFamily p p₁ j i h r α).2 t x, (restrictedFamily p p₁ j i h r β).2 t x]
    rfl

/-- `Stacks.Chow.restrictedFamilyHom` is `Stacks.Chow.restrictedFamily`. -/
@[simp]
theorem restrictedFamilyHom_apply {W T W₁ T₁ : Scheme.{u}} (p : W ⟶ T) [LocallyOfFiniteType p]
    (p₁ : W₁ ⟶ T₁) [LocallyOfFiniteType p₁] (j : W₁ ⟶ W) [IsOpenImmersion j]
    (i : T₁ ⟶ T) [IsOpenImmersion i] (h : j ≫ p = p₁ ≫ i) (r : ℕ) (α : FamilyOfCycles p r) :
    restrictedFamilyHom p p₁ j i h r α = (restrictedFamily p p₁ j i h r α).1 :=
  rfl

/-! ### Assembling a cycle class from two disjoint clopen pieces -/

section Assembly

variable {W T W₁ T₁ W₂ T₂ : Scheme.{u}} (p : W ⟶ T) [LocallyOfFinitePresentation p]
  [QuasiCompact p] (p₁ : W₁ ⟶ T₁) [LocallyOfFinitePresentation p₁] [QuasiCompact p₁]
  (j₁ : W₁ ⟶ W) [IsClosedImmersion j₁] [IsOpenImmersion j₁] (i₁ : T₁ ⟶ T) [IsOpenImmersion i₁]
  [QuasiCompact i₁] (h₁ : j₁ ≫ p = p₁ ≫ i₁) (r : ℕ)

omit [QuasiCompact p] [QuasiCompact p₁] in
/-- The cycle class of an extended member of `Hilb`, restricted back along the same clopen
immersion, is the cycle class of the member one started from. -/
theorem restrictedFamilyHom_cycleClassMap_map_extend
    (c : FreeAbelianGroup (HilbertCycleDatum p₁ r)) :
    restrictedFamilyHom p p₁ j₁ i₁ h₁ r (cycleClassMap p r
        (FreeAbelianGroup.map (fun Z ↦ HilbertCycleDatum.extend p p₁ j₁ i₁ r Z h₁) c)) =
      cycleClassMap p₁ r c := by
  refine DFunLike.congr_fun (FreeAbelianGroup.lift_ext
    (((restrictedFamilyHom p p₁ j₁ i₁ h₁ r).comp (cycleClassMap p r)).comp
      (FreeAbelianGroup.map fun Z ↦ HilbertCycleDatum.extend p p₁ j₁ i₁ r Z h₁))
    (cycleClassMap p₁ r) fun Z ↦ ?_) c
  change restrictedFamilyHom p p₁ j₁ i₁ h₁ r (cycleClassMap p r
      (FreeAbelianGroup.map (fun Z ↦ HilbertCycleDatum.extend p p₁ j₁ i₁ r Z h₁)
        (FreeAbelianGroup.of Z))) = cycleClassMap p₁ r (FreeAbelianGroup.of Z)
  rw [FreeAbelianGroup.map_of_apply, cycleClassMap_of, cycleClassMap_of,
    restrictedFamilyHom_apply,
    HilbertCycleDatum.restrictedFamily_cycleFamily_extend p p₁ j₁ i₁ h₁ Z]

omit [QuasiCompact p] [QuasiCompact p₁] [IsClosedImmersion j₁] [QuasiCompact i₁] in
/-- The cycle class of a member of `Hilb` extended along one clopen immersion restricts to zero
along a clopen immersion with disjoint range. -/
theorem restrictedFamilyHom_cycleClassMap_map_extend_eq_zero
    (p₂ : W₂ ⟶ T₂) [LocallyOfFinitePresentation p₂] (j₂ : W₂ ⟶ W) [IsClosedImmersion j₂]
    (i₂ : T₂ ⟶ T) [IsOpenImmersion i₂] [QuasiCompact i₂] (h₂ : j₂ ≫ p = p₂ ≫ i₂)
    (hdisj : Disjoint (Set.range (ConcreteCategory.hom j₁.base))
      (Set.range (ConcreteCategory.hom j₂.base)))
    (c : FreeAbelianGroup (HilbertCycleDatum p₂ r)) :
    restrictedFamilyHom p p₁ j₁ i₁ h₁ r (cycleClassMap p r
        (FreeAbelianGroup.map (fun Z ↦ HilbertCycleDatum.extend p p₂ j₂ i₂ r Z h₂) c)) = 0 := by
  refine DFunLike.congr_fun (FreeAbelianGroup.lift_ext
    (((restrictedFamilyHom p p₁ j₁ i₁ h₁ r).comp (cycleClassMap p r)).comp
      (FreeAbelianGroup.map fun Z ↦ HilbertCycleDatum.extend p p₂ j₂ i₂ r Z h₂))
    0 fun Z ↦ ?_) c
  change restrictedFamilyHom p p₁ j₁ i₁ h₁ r (cycleClassMap p r
    (FreeAbelianGroup.map (fun Z ↦ HilbertCycleDatum.extend p p₂ j₂ i₂ r Z h₂)
      (FreeAbelianGroup.of Z))) = 0
  rw [FreeAbelianGroup.map_of_apply, cycleClassMap_of, restrictedFamilyHom_apply]
  exact HilbertCycleDatum.restrictedFamily_cycleFamily_eq_zero_of_disjoint p p₁ j₁ i₁ h₁
    (HilbertCycleDatum.extend p p₂ j₂ i₂ r Z h₂)
    (hdisj.mono_right (HilbertCycleDatum.range_subschemeι_map_subset Z.ideal j₂))

omit [QuasiCompact p] [QuasiCompact p₁] in
/-- **The cycle-class half of the coproduct step of Tag 0H59.** Let `p : W ⟶ T` be of finite
presentation and let `j₁ : W₁ ⟶ W` and `j₂ : W₂ ⟶ W` be clopen immersions with disjoint ranges,
over quasi-compact clopen immersions `i₁ : T₁ ⟶ T` and `i₂ : T₂ ⟶ T` of the base. Given cycle
classes `c₁` on `W₁/T₁` and `c₂` on `W₂/T₂` there is a cycle class `c` on `W/T` whose associated
family of cycles restricts, along the two squares, to the families of `c₁` and of `c₂`. -/
theorem exists_cycleClassMap_restrictedFamily_eq
    (p₂ : W₂ ⟶ T₂) [LocallyOfFinitePresentation p₂] [QuasiCompact p₂] (j₂ : W₂ ⟶ W)
    [IsClosedImmersion j₂] [IsOpenImmersion j₂] (i₂ : T₂ ⟶ T) [IsOpenImmersion i₂] [QuasiCompact i₂]
    (h₂ : j₂ ≫ p = p₂ ≫ i₂)
    (hdisj : Disjoint (Set.range (ConcreteCategory.hom j₁.base))
      (Set.range (ConcreteCategory.hom j₂.base)))
    (c₁ : FreeAbelianGroup (HilbertCycleDatum p₁ r))
    (c₂ : FreeAbelianGroup (HilbertCycleDatum p₂ r)) :
    ∃ c : FreeAbelianGroup (HilbertCycleDatum p r),
      (restrictedFamily p p₁ j₁ i₁ h₁ r (cycleClassMap p r c)).1 = cycleClassMap p₁ r c₁ ∧
        (restrictedFamily p p₂ j₂ i₂ h₂ r (cycleClassMap p r c)).1 = cycleClassMap p₂ r c₂ := by
  refine ⟨FreeAbelianGroup.map (fun Z ↦ HilbertCycleDatum.extend p p₁ j₁ i₁ r Z h₁) c₁ +
    FreeAbelianGroup.map (fun Z ↦ HilbertCycleDatum.extend p p₂ j₂ i₂ r Z h₂) c₂, ?_, ?_⟩
  · change restrictedFamilyHom p p₁ j₁ i₁ h₁ r (cycleClassMap p r _) = _
    rw [map_add, map_add, restrictedFamilyHom_cycleClassMap_map_extend p p₁ j₁ i₁ h₁ r c₁,
      restrictedFamilyHom_cycleClassMap_map_extend_eq_zero p p₁ j₁ i₁ h₁ r p₂ j₂ i₂ h₂ hdisj c₂,
      add_zero]
  · change restrictedFamilyHom p p₂ j₂ i₂ h₂ r (cycleClassMap p r _) = _
    rw [map_add, map_add, restrictedFamilyHom_cycleClassMap_map_extend p p₂ j₂ i₂ h₂ r c₂,
      restrictedFamilyHom_cycleClassMap_map_extend_eq_zero p p₂ j₂ i₂ h₂ r p₁ j₁ i₁ h₁
        hdisj.symm c₁, zero_add]

end Assembly

/-! ### Rigidity along a pair of cartesian squares -/

/-- In a cartesian square the image of the top edge is the inverse image of the image of the
bottom edge. -/
theorem range_eq_preimage_range_of_isPullback {P W A B : Scheme.{u}} {q : P ⟶ W} {w' : P ⟶ A}
    {w : W ⟶ B} {g : A ⟶ B} (L : IsPullback q w' w g) :
    Set.range (q : P → W) = (w : W → B) ⁻¹' Set.range (g : A → B) := by
  have hsurj : Function.Surjective (L.isoPullback.hom : P → (pullback w g : Scheme.{u})) :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso L.isoPullback)).surjective
  have h1 : (q : P → W) =
      (fun z : (pullback w g : Scheme.{u}) => (pullback.fst w g) z) ∘
        (fun z : P => (L.isoPullback.hom) z) := by
    funext z
    exact (congrArg (fun m : P ⟶ W => m z) L.isoPullback_hom_fst).symm
  rw [h1, Set.range_comp, hsurj.range_eq, Set.image_univ,
    AlgebraicGeometry.Scheme.Pullback.range_fst]

/-- The comparison map of fibres attached to a commutative square of open immersions is
surjective as soon as the part of the source lying over the open part of the base is covered by
the open subscheme — in particular whenever the square is cartesian. -/
theorem surjective_restrictedFiberMap_of_preimage_subset_range {W T W₁ T₁ : Scheme.{u}}
    (p : W ⟶ T) [LocallyOfFiniteType p] (p₁ : W₁ ⟶ T₁) [LocallyOfFiniteType p₁] (j : W₁ ⟶ W)
    [IsOpenImmersion j] (i : T₁ ⟶ T) [IsOpenImmersion i] (h : j ≫ p = p₁ ≫ i)
    (hrange : (p : W → T) ⁻¹' Set.range (i : T₁ → T) ⊆ Set.range (j : W₁ → W)) (t : T₁) :
    Function.Surjective (restrictedFiberMap p p₁ j i h t) := by
  intro x
  have hpw : p (p.fiberι (i t) x) = i t := (p.range_fiberι (i t)).le ⟨x, rfl⟩
  have hmem : p.fiberι (i t) x ∈ (p : W → T) ⁻¹' Set.range (i : T₁ → T) := by
    rw [Set.mem_preimage, hpw]
    exact ⟨t, rfl⟩
  obtain ⟨v, hv⟩ := hrange hmem
  have hsquare : i (p₁ v) = p (j v) := by
    simpa only [Scheme.Hom.comp_apply] using (congrArg (fun m : W₁ ⟶ T => m v) h).symm
  have hpv : p₁ v = t :=
    (Scheme.Hom.isOpenEmbedding i).injective (by rw [hsquare, hv, hpw])
  obtain ⟨y, hy⟩ := (p₁.range_fiberι t).ge hpv
  refine ⟨y, (Scheme.Hom.isEmbedding (p.fiberι (i t))).injective ?_⟩
  have hfib := congrArg (fun m : p₁.fiber t ⟶ W => m y) (restrictedFiberMap_fiberι p p₁ j i h t)
  simp only [Scheme.Hom.comp_apply] at hfib
  rw [hfib, hy, hv]

/-- Two families of cycles with the same restriction along a cartesian square of open immersions
agree over every point in the range of the base map. -/
theorem fiberCycle_eq_of_restrictedFamily_eq_of_isPullback {W T W₁ T₁ : Scheme.{u}} (p : W ⟶ T)
    [LocallyOfFiniteType p] (p₁ : W₁ ⟶ T₁) [LocallyOfFiniteType p₁] (j : W₁ ⟶ W)
    [IsOpenImmersion j] (i : T₁ ⟶ T) [IsOpenImmersion i] (h : j ≫ p = p₁ ≫ i)
    (hrange : (p : W → T) ⁻¹' Set.range (i : T₁ → T) ⊆ Set.range (j : W₁ → W)) {r : ℕ}
    (β γ : FamilyOfCycles p r)
    (hres : (restrictedFamily p p₁ j i h r β).1 = (restrictedFamily p p₁ j i h r γ).1) (t : T₁) :
    β (i t) = γ (i t) := by
  refine Subtype.ext <| Function.locallyFinsuppWithin.ext fun y => ?_
  obtain ⟨x, rfl⟩ :=
    surjective_restrictedFiberMap_of_preimage_subset_range p p₁ j i h hrange t y
  simpa only [(restrictedFamily p p₁ j i h r β).2 t x, (restrictedFamily p p₁ j i h r γ).2 t x]
    using congrArg (fun δ : FamilyOfCycles p₁ r => (δ t : AlgebraicCycle (p₁.fiber t) ℤ) x) hres

/-- **Rigidity along two cartesian squares whose base maps cover.** A family of cycles on the
fibres of `W/T` is determined by its restrictions along two commutative squares of open
immersions whose base maps cover `T` and each of which is cartesian. -/
theorem familyOfCycles_eq_of_isPullback_pair {W T W₁ T₁ W₂ T₂ : Scheme.{u}} (p : W ⟶ T)
    [LocallyOfFiniteType p] (p₁ : W₁ ⟶ T₁) [LocallyOfFiniteType p₁] (j₁ : W₁ ⟶ W)
    [IsOpenImmersion j₁] (i₁ : T₁ ⟶ T) [IsOpenImmersion i₁] (h₁ : j₁ ≫ p = p₁ ≫ i₁)
    (hrange₁ : (p : W → T) ⁻¹' Set.range (i₁ : T₁ → T) ⊆ Set.range (j₁ : W₁ → W))
    (p₂ : W₂ ⟶ T₂) [LocallyOfFiniteType p₂] (j₂ : W₂ ⟶ W) [IsOpenImmersion j₂]
    (i₂ : T₂ ⟶ T) [IsOpenImmersion i₂] (h₂ : j₂ ≫ p = p₂ ≫ i₂)
    (hrange₂ : (p : W → T) ⁻¹' Set.range (i₂ : T₂ → T) ⊆ Set.range (j₂ : W₂ → W))
    (hcover : ∀ t : T, t ∈ Set.range (i₁ : T₁ → T) ∨ t ∈ Set.range (i₂ : T₂ → T)) {r : ℕ}
    (β γ : FamilyOfCycles p r)
    (hres₁ : (restrictedFamily p p₁ j₁ i₁ h₁ r β).1 = (restrictedFamily p p₁ j₁ i₁ h₁ r γ).1)
    (hres₂ : (restrictedFamily p p₂ j₂ i₂ h₂ r β).1 =
      (restrictedFamily p p₂ j₂ i₂ h₂ r γ).1) :
    β = γ := by
  funext t
  rcases hcover t with ⟨u, rfl⟩ | ⟨u, rfl⟩
  · exact fiberCycle_eq_of_restrictedFamily_eq_of_isPullback p p₁ j₁ i₁ h₁ hrange₁ β γ hres₁ u
  · exact fiberCycle_eq_of_restrictedFamily_eq_of_isPullback p p₂ j₂ i₂ h₂ hrange₂ β γ hres₂ u

/-! ### The two summands of a coproduct base -/

section CoprodBase

variable {X S T₁ T₂ : Scheme.{u}} (f : X ⟶ S) (g₁ : T₁ ⟶ S) (g₂ : T₂ ⟶ S)

/-- The first inclusion of a binary coproduct of schemes is a closed immersion: its range is the
complement of the range of the second inclusion, which is open. -/
alias isClosedImmersion_coprodInl := Stacks.BlowupAmpleFamily.isClosedImmersion_inl

/-- The second inclusion of a binary coproduct of schemes is a closed immersion. -/
alias isClosedImmersion_coprodInr := Stacks.BlowupAmpleFamily.isClosedImmersion_inr

/-- The base change of `X` along the first summand `g₁`, viewed inside the base change along
`coprod.desc g₁ g₂`. -/
def coprodBaseChangeInl :
    (pullback f g₁ : Scheme.{u}) ⟶ pullback f (coprod.desc g₁ g₂) :=
  pullback.lift (pullback.fst f g₁) (pullback.snd f g₁ ≫ coprod.inl)
    (by rw [Category.assoc, coprod.inl_desc]; exact pullback.condition)

/-- The base change of `X` along the second summand `g₂`, viewed inside the base change along
`coprod.desc g₁ g₂`. -/
def coprodBaseChangeInr :
    (pullback f g₂ : Scheme.{u}) ⟶ pullback f (coprod.desc g₁ g₂) :=
  pullback.lift (pullback.fst f g₂) (pullback.snd f g₂ ≫ coprod.inr)
    (by rw [Category.assoc, coprod.inr_desc]; exact pullback.condition)

/-- `Stacks.Chow.coprodBaseChangeInl` lies over the first coproduct inclusion of the base. -/
theorem coprodBaseChangeInl_snd :
    coprodBaseChangeInl f g₁ g₂ ≫ pullback.snd f (coprod.desc g₁ g₂) =
      pullback.snd f g₁ ≫ coprod.inl :=
  pullback.lift_snd _ _ _

/-- `Stacks.Chow.coprodBaseChangeInr` lies over the second coproduct inclusion of the base. -/
theorem coprodBaseChangeInr_snd :
    coprodBaseChangeInr f g₁ g₂ ≫ pullback.snd f (coprod.desc g₁ g₂) =
      pullback.snd f g₂ ≫ coprod.inr :=
  pullback.lift_snd _ _ _

/-- The square exhibiting the base change along `g₁` as the part of the base change along
`coprod.desc g₁ g₂` lying over the first summand is cartesian. -/
theorem isPullback_coprodBaseChangeInl :
    IsPullback (coprodBaseChangeInl f g₁ g₂) (pullback.snd f g₁)
      (pullback.snd f (coprod.desc g₁ g₂)) (coprod.inl : T₁ ⟶ T₁ ⨿ T₂) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f (coprod.desc g₁ g₂)) ?_
    (coprodBaseChangeInl_snd f g₁ g₂) (IsPullback.of_hasPullback f (coprod.desc g₁ g₂))
  rw [show coprodBaseChangeInl f g₁ g₂ ≫ pullback.fst f (coprod.desc g₁ g₂) =
      pullback.fst f g₁ from pullback.lift_fst _ _ _,
    show (coprod.inl : T₁ ⟶ T₁ ⨿ T₂) ≫ coprod.desc g₁ g₂ = g₁ from coprod.inl_desc _ _]
  exact IsPullback.of_hasPullback f g₁

/-- The analogue of `Stacks.Chow.isPullback_coprodBaseChangeInl` for the second summand. -/
theorem isPullback_coprodBaseChangeInr :
    IsPullback (coprodBaseChangeInr f g₁ g₂) (pullback.snd f g₂)
      (pullback.snd f (coprod.desc g₁ g₂)) (coprod.inr : T₂ ⟶ T₁ ⨿ T₂) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f (coprod.desc g₁ g₂)) ?_
    (coprodBaseChangeInr_snd f g₁ g₂) (IsPullback.of_hasPullback f (coprod.desc g₁ g₂))
  rw [show coprodBaseChangeInr f g₁ g₂ ≫ pullback.fst f (coprod.desc g₁ g₂) =
      pullback.fst f g₂ from pullback.lift_fst _ _ _,
    show (coprod.inr : T₂ ⟶ T₁ ⨿ T₂) ≫ coprod.desc g₁ g₂ = g₂ from coprod.inr_desc _ _]
  exact IsPullback.of_hasPullback f g₂

/-- The first base change is an open immersion, being a base change of `coprod.inl`. -/
instance isOpenImmersion_coprodBaseChangeInl :
    IsOpenImmersion (coprodBaseChangeInl f g₁ g₂) := by
  rw [← (isPullback_coprodBaseChangeInl f g₁ g₂).isoPullback_hom_fst]
  infer_instance

/-- The second base change is an open immersion, being a base change of `coprod.inr`. -/
instance isOpenImmersion_coprodBaseChangeInr :
    IsOpenImmersion (coprodBaseChangeInr f g₁ g₂) := by
  rw [← (isPullback_coprodBaseChangeInr f g₁ g₂).isoPullback_hom_fst]
  infer_instance

/-- The first base change is a closed immersion, being a base change of `coprod.inl`. -/
instance isClosedImmersion_coprodBaseChangeInl :
    IsClosedImmersion (coprodBaseChangeInl f g₁ g₂) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsClosedImmersion.{u}) (isPullback_coprodBaseChangeInl f g₁ g₂).flip
    (isClosedImmersion_coprodInl T₁ T₂)

/-- The second base change is a closed immersion, being a base change of `coprod.inr`. -/
instance isClosedImmersion_coprodBaseChangeInr :
    IsClosedImmersion (coprodBaseChangeInr f g₁ g₂) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsClosedImmersion.{u}) (isPullback_coprodBaseChangeInr f g₁ g₂).flip
    (isClosedImmersion_coprodInr T₁ T₂)

/-- The two base changes have disjoint ranges: each is the inverse image of the range of a
coproduct inclusion, and those are disjoint. -/
theorem disjoint_range_coprodBaseChange :
    Disjoint (Set.range (ConcreteCategory.hom (coprodBaseChangeInl f g₁ g₂).base))
      (Set.range (ConcreteCategory.hom (coprodBaseChangeInr f g₁ g₂).base)) := by
  rw [range_eq_preimage_range_of_isPullback (isPullback_coprodBaseChangeInl f g₁ g₂),
    range_eq_preimage_range_of_isPullback (isPullback_coprodBaseChangeInr f g₁ g₂)]
  exact Disjoint.preimage _ (isCompl_range_inl_inr T₁ T₂).disjoint

/-- Every point of a binary coproduct of schemes lies in the range of one of the two
inclusions. -/
theorem mem_range_coprod_inl_or_inr (A B : Scheme.{u}) (t : (A ⨿ B : Scheme.{u})) :
    t ∈ Set.range (coprod.inl : A ⟶ A ⨿ B) ∨ t ∈ Set.range (coprod.inr : B ⟶ A ⨿ B) := by
  obtain ⟨u | u, rfl⟩ := (coprodMk A B).surjective t
  · exact Or.inl ⟨u, (coprodMk_inl A B u).symm⟩
  · exact Or.inr ⟨u, (coprodMk_inr A B u).symm⟩

end CoprodBase

/-! ### The coproduct clause of Tag 0H59, for a family presented by its restrictions -/

/-- Cycle classes over the two summands extend to a cycle class over `T₁ ⨿ T₂` restricting to
`g₁^*α` and `g₂^*α`. -/
private theorem exists_cycleClassMap_restrictedFamily_eq_baseChangeFamily_coprod
    {X S T₁ T₂ : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f] (r : ℕ)
    (α : FamilyOfCycles f r) (g₁ : T₁ ⟶ S) (g₂ : T₂ ⟶ S) (H₁ : PullbackInCycleClassImage f r α g₁)
    (H₂ : PullbackInCycleClassImage f r α g₂) :
    ∃ c : FreeAbelianGroup (HilbertCycleDatum (pullback.snd f (coprod.desc g₁ g₂)) r),
      (restrictedFamily (pullback.snd f (coprod.desc g₁ g₂)) (pullback.snd f g₁)
          (coprodBaseChangeInl f g₁ g₂) coprod.inl (coprodBaseChangeInl_snd f g₁ g₂) r
          (cycleClassMap (pullback.snd f (coprod.desc g₁ g₂)) r c)).1 =
        baseChangeFamily f g₁ r α ∧
      (restrictedFamily (pullback.snd f (coprod.desc g₁ g₂)) (pullback.snd f g₂)
          (coprodBaseChangeInr f g₁ g₂) coprod.inr (coprodBaseChangeInr_snd f g₁ g₂) r
          (cycleClassMap (pullback.snd f (coprod.desc g₁ g₂)) r c)).1 =
        baseChangeFamily f g₂ r α := by
  have hinl : IsClosedImmersion (coprod.inl : T₁ ⟶ T₁ ⨿ T₂) := isClosedImmersion_coprodInl T₁ T₂
  have hinr : IsClosedImmersion (coprod.inr : T₂ ⟶ T₁ ⨿ T₂) := isClosedImmersion_coprodInr T₁ T₂
  obtain ⟨c₁, hc₁⟩ := H₁
  obtain ⟨c₂, hc₂⟩ := H₂
  obtain ⟨c, hcl, hcr⟩ := exists_cycleClassMap_restrictedFamily_eq
    (pullback.snd f (coprod.desc g₁ g₂)) (pullback.snd f g₁) (coprodBaseChangeInl f g₁ g₂)
    coprod.inl (coprodBaseChangeInl_snd f g₁ g₂) r (pullback.snd f g₂)
    (coprodBaseChangeInr f g₁ g₂) coprod.inr (coprodBaseChangeInr_snd f g₁ g₂)
    (disjoint_range_coprodBaseChange f g₁ g₂) c₁ c₂
  exact ⟨c, hcl.trans hc₁, hcr.trans hc₂⟩

/-- Whenever `g₁^*α` and `g₂^*α` are in the image of their cycle class maps, there exists a family
of cycles on the fibres of `X ×_S (T₁ ⨿ T₂) / (T₁ ⨿ T₂)` whose restrictions along the two
coproduct inclusions are `g₁^*α` and `g₂^*α`. -/
theorem exists_restrictedFamily_eq_baseChangeFamily_coprod {X S T₁ T₂ : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] (r : ℕ) (α : FamilyOfCycles f r)
    (g₁ : T₁ ⟶ S) (g₂ : T₂ ⟶ S) (H₁ : PullbackInCycleClassImage f r α g₁)
    (H₂ : PullbackInCycleClassImage f r α g₂) :
    ∃ β : FamilyOfCycles (pullback.snd f (coprod.desc g₁ g₂)) r,
      (restrictedFamily (pullback.snd f (coprod.desc g₁ g₂)) (pullback.snd f g₁)
          (coprodBaseChangeInl f g₁ g₂) coprod.inl (coprodBaseChangeInl_snd f g₁ g₂) r β).1 =
        baseChangeFamily f g₁ r α ∧
      (restrictedFamily (pullback.snd f (coprod.desc g₁ g₂)) (pullback.snd f g₂)
          (coprodBaseChangeInr f g₁ g₂) coprod.inr (coprodBaseChangeInr_snd f g₁ g₂) r β).1 =
        baseChangeFamily f g₂ r α :=
  let ⟨_, h₁, h₂⟩ :=
    exists_cycleClassMap_restrictedFamily_eq_baseChangeFamily_coprod f r α g₁ g₂ H₁ H₂
  ⟨_, h₁, h₂⟩

/-- **The coproduct clause of the Noetherian induction for Tag 0H59, for a family of cycles
presented by its restrictions to the two summands.**

Let `f : X ⟶ S` be of finite presentation, let `r ≥ 0` and let `α` be a family of `r`-cycles on
the fibres of `X/S`. Let `g₁ : T₁ ⟶ S` and `g₂ : T₂ ⟶ S` be morphisms for which `g₁^*α` and
`g₂^*α` lie in the image of the cycle class map of Tag 0H6V, and let `β` be **any** family of
`r`-cycles on the fibres of `X ×_S (T₁ ⨿ T₂) / (T₁ ⨿ T₂)` whose restrictions along the two
coproduct inclusions are `g₁^*α` and `g₂^*α`. Then `β` lies in the image of the cycle class map. -/
theorem exists_cycleClassMap_eq_of_restrictedFamily_coprod {X S T₁ T₂ : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] (r : ℕ) (α : FamilyOfCycles f r)
    (g₁ : T₁ ⟶ S) (g₂ : T₂ ⟶ S) (H₁ : PullbackInCycleClassImage f r α g₁)
    (H₂ : PullbackInCycleClassImage f r α g₂)
    (β : FamilyOfCycles (pullback.snd f (coprod.desc g₁ g₂)) r)
    (hβ₁ : (restrictedFamily (pullback.snd f (coprod.desc g₁ g₂)) (pullback.snd f g₁)
        (coprodBaseChangeInl f g₁ g₂) coprod.inl (coprodBaseChangeInl_snd f g₁ g₂) r β).1 =
      baseChangeFamily f g₁ r α)
    (hβ₂ : (restrictedFamily (pullback.snd f (coprod.desc g₁ g₂)) (pullback.snd f g₂)
        (coprodBaseChangeInr f g₁ g₂) coprod.inr (coprodBaseChangeInr_snd f g₁ g₂) r β).1 =
      baseChangeFamily f g₂ r α) :
    ∃ c : FreeAbelianGroup (HilbertCycleDatum (pullback.snd f (coprod.desc g₁ g₂)) r),
      cycleClassMap (pullback.snd f (coprod.desc g₁ g₂)) r c = β := by
  obtain ⟨c, hcl, hcr⟩ :=
    exists_cycleClassMap_restrictedFamily_eq_baseChangeFamily_coprod f r α g₁ g₂ H₁ H₂
  refine ⟨c, familyOfCycles_eq_of_isPullback_pair (pullback.snd f (coprod.desc g₁ g₂))
    (pullback.snd f g₁) (coprodBaseChangeInl f g₁ g₂) coprod.inl
    (coprodBaseChangeInl_snd f g₁ g₂)
    (le_of_eq (range_eq_preimage_range_of_isPullback
      (isPullback_coprodBaseChangeInl f g₁ g₂)).symm)
    (pullback.snd f g₂) (coprodBaseChangeInr f g₁ g₂) coprod.inr
    (coprodBaseChangeInr_snd f g₁ g₂)
    (le_of_eq (range_eq_preimage_range_of_isPullback
      (isPullback_coprodBaseChangeInr f g₁ g₂)).symm)
    (mem_range_coprod_inl_or_inr T₁ T₂) _ β ?_ ?_⟩
  · rw [hcl, hβ₁]
  · rw [hcr, hβ₂]

end Stacks.Chow

end
