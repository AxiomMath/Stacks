module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.BlowUpFreeChartGlue
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Local

/-!
# Descending a bundle through a modification that is free near the centre

Let `b : X' ⟶ X` be a morphism of schemes, let `U` and `V` be two opens covering `X`, assume that
`b` is an isomorphism over `V`, and let `G` be a finite locally free module on `X'` which is free
on an index type `I` over `b ⁻¹ᵁ U`, the freeness witnessed by a morphism
`α : 𝒪_{X'}^{⊕I} ⟶ G` invertible there.  Then `G` descends: there is a finite locally free module
`N` on `X` whose restriction to `U` is free on `I` and whose restriction to `V` is the inverse
image of `G` along the section of `b` over `V`.

This is the Zariski glueing step of the essential surjectivity half of [Stacks, Tag 0EXD] for the
almost blowup square of [Stacks, Example 0EVH] with a free module on the centre, stated with the
two opens, the modification and the comparison `α` as variables.  The glueing itself is
`AlgebraicGeometry.TwoOpensGlue.exists_restrict_iso_of_middle`, which asks for no cocycle: all
that has to be produced is, for each of the two opens, an identification of the restriction of
its module to the overlap with one module there.  Over `U` the module is already free, so that
identification is `Stacks.Modules.restrictFreeIso`; over `V` it is `α` restricted along the
section, which is invertible because the section over the overlap factors through `b ⁻¹ᵁ U`.

## Main definitions

* `AlgebraicGeometry.freeChartBaseSection`: the section of `b` over an open on which it is
  invertible.
* `AlgebraicGeometry.sectionCompPreimageLift`: the factorisation through `b ⁻¹ᵁ U` of the section
  of `b` precomposed with an open immersion landing in `U`.
* `AlgebraicGeometry.sectionFreeIso`: the comparison, through `α`, of the inverse image of `G`
  along the section with the free module.
* `AlgebraicGeometry.overlapToRight`: the inclusion of the overlap `U ⊓ V` into `V`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_free`: a free module on a finite index
  type is finite locally free.
* `AlgebraicGeometry.nonempty_pullback_iso_free_of_range_subset`: a trivialisation over an open
  of the base transports to the inverse image along any morphism landing in that open.
* `AlgebraicGeometry.range_subset_range_preimage_ι`: a morphism to `X'` whose composite with `b`
  lands in `U` lands in `b ⁻¹ᵁ U`.
* `AlgebraicGeometry.isIso_restrictFunctor_map_sectionComp`: `α` stays invertible after
  restriction along the section of `b` precomposed with an open immersion landing in `U`.
* `AlgebraicGeometry.exists_isFiniteLocallyFree_restrict_iso_of_isIso_restrict_free`: the
  descent of `G` to a finite locally free module `N` on `X`, as above.

## Implementation notes

Everything before the final theorem is stated for an arbitrary open immersion `k` into the open
`V` whose composite with the inclusion of `V` lands in `U`, not for the inclusion of the overlap
`U ⊓ V` into `V`.  The final theorem then feeds it `AlgebraicGeometry.overlapToRight`, which is
`AlgebraicGeometry.TwoOpensGlue.mid U V ⟨true⟩` written with `V` itself as codomain instead of the
member of the two-element family of opens.  The two are the same morphism, but only the former
spelling lets `IsOpenImmersion` and `IsIso (b ∣_ V)` be resolved: instance search does not perform
the reduction of that family at its index, even though the elaborator does when checking an
explicit application against its expected type.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### A free module is finite locally free -/

/-- **A free module on a finite index type is finite locally free**, with the whole scheme as the
trivialising neighbourhood of every point. -/
theorem Scheme.Modules.isFiniteLocallyFree_free {X : Scheme.{u}} (I : Type u) [Finite I] :
    Scheme.Modules.IsFiniteLocallyFree
      (_root_.SheafOfModules.free (R := X.ringCatSheaf) I) :=
  fun _ => ⟨⊤, trivial, I, ‹Finite I›, ⟨Stacks.Modules.restrictFreeIso (⊤ : X.Opens).ι I⟩⟩

/-! ### Transporting a trivialisation over an open to an inverse image -/

/-- **A trivialisation of `N` over an open `U` of the base transports to the inverse image of `N`
along any morphism landing in `U`.** The morphism factors through `U` by the universal property of
open immersions, restriction along the inclusion of `U` agrees with the inverse image by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, and the inverse image of a free
module is free on the same index type. The morphism is not assumed to be an open immersion. -/
theorem nonempty_pullback_iso_free_of_range_subset {X Z : Scheme.{u}} (z : Z ⟶ X) (U : X.Opens)
    (hz : Set.range z.base ⊆ (U : Set X)) {N : X.Modules} {I : Type u}
    (e : Scheme.Modules.restrict N U.ι ≅
      _root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) I) :
    Nonempty ((Scheme.Modules.pullback z).obj N ≅
      _root_.SheafOfModules.free (R := Z.ringCatSheaf) I) := by
  have hrange : Set.range z.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact hz
  have hfac : IsOpenImmersion.lift U.ι z hrange ≫ U.ι = z :=
    IsOpenImmersion.lift_fac _ _ _
  exact ⟨(Scheme.Modules.pullbackCongr hfac).symm.app N ≪≫
    (Scheme.Modules.pullbackComp (IsOpenImmersion.lift U.ι z hrange) U.ι).symm.app N ≪≫
    (Scheme.Modules.pullback (IsOpenImmersion.lift U.ι z hrange)).mapIso
      (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app N).symm ≪≫ e) ≪≫
    Scheme.Modules.pullbackFreeIso (IsOpenImmersion.lift U.ι z hrange) I⟩

/-! ### The point-set range inclusion -/

/-- **A morphism to `X'` whose composite with `b` lands in `U` lands in `b ⁻¹ᵁ U`.** -/
theorem range_subset_range_preimage_ι {X X' W : Scheme.{u}} (b : X' ⟶ X) (U : X.Opens)
    (p : W ⟶ X') {q : W ⟶ X} (hq : p ≫ b = q)
    (hqU : Set.range q.base ⊆ (U : Set X)) :
    Set.range p.base ⊆ Set.range (b ⁻¹ᵁ U).ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  have hb : b.base (p.base x) = q.base x :=
    (Scheme.Hom.comp_apply p b x).symm.trans (by rw [hq])
  change b.base (p.base x) ∈ (U : Set X)
  rw [hb]
  exact hqU ⟨x, rfl⟩

/-! ### The section of a morphism over an open on which it is invertible -/

section Section

variable {X X' : Scheme.{u}} (b : X' ⟶ X) (V : X.Opens) [IsIso (b ∣_ V)]

/-- **The section of `b` over an open on which it is invertible**: the inverse of the restricted
morphism followed by the inclusion of the preimage. -/
def freeChartBaseSection : V.toScheme ⟶ X' :=
  inv (b ∣_ V) ≫ (b ⁻¹ᵁ V).ι

/-- The section of `b` over `V` is an open immersion. -/
instance isOpenImmersion_freeChartBaseSection : IsOpenImmersion (freeChartBaseSection b V) :=
  inferInstanceAs (IsOpenImmersion (inv (b ∣_ V) ≫ (b ⁻¹ᵁ V).ι))

/-- **The section of `b` over `V` is a section**: composed with `b` it is the inclusion of `V`. -/
@[simp] theorem freeChartBaseSection_comp : freeChartBaseSection b V ≫ b = V.ι := by
  have h : (b ⁻¹ᵁ V).ι ≫ b = (b ∣_ V) ≫ V.ι := (morphismRestrict_ι b V).symm
  rw [freeChartBaseSection, Category.assoc, h, IsIso.inv_hom_id_assoc]

end Section

/-! ### The comparison of the inverse image along the section with the free module -/

section SectionComp

variable {X X' T : Scheme.{u}} (b : X' ⟶ X) {U V : X.Opens} [IsIso (b ∣_ V)]
  (k : T ⟶ V.toScheme) (hkU : Set.range (k ≫ V.ι).base ⊆ (U : Set X))

/-- The section of `b` over `V`, precomposed with an open immersion into `V`. -/
def sectionComp : T ⟶ X' := k ≫ freeChartBaseSection b V

/-- The section of `b` over `V`, precomposed with an open immersion into `V` and followed by `b`,
is that open immersion followed by the inclusion of `V`. -/
@[simp] theorem sectionComp_comp : sectionComp b k ≫ b = k ≫ V.ι := by
  rw [sectionComp, Category.assoc, freeChartBaseSection_comp]

include hkU in
/-- **The section of `b` over `V`, precomposed with an open immersion landing in `U`, factors
through `b ⁻¹ᵁ U`.** -/
theorem range_sectionComp_subset :
    Set.range (sectionComp b k).base ⊆ Set.range (b ⁻¹ᵁ U).ι.base :=
  range_subset_range_preimage_ι b U (sectionComp b k) (sectionComp_comp b k) hkU

/-- The factorisation through `b ⁻¹ᵁ U` of the section of `b` over `V` precomposed with an open
immersion landing in `U`. -/
def sectionCompPreimageLift : T ⟶ (b ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift (b ⁻¹ᵁ U).ι (sectionComp b k) (range_sectionComp_subset b k hkU)

/-- The factorisation through `b ⁻¹ᵁ U`, followed by the inclusion of `b ⁻¹ᵁ U`, is the section
of `b` over `V` precomposed with `k`. -/
@[simp] theorem sectionCompPreimageLift_comp :
    sectionCompPreimageLift b k hkU ≫ (b ⁻¹ᵁ U).ι = sectionComp b k :=
  IsOpenImmersion.lift_fac _ _ _

variable [IsOpenImmersion k]

/-- The section of `b` over `V` precomposed with an open immersion into `V` is an open
immersion. -/
instance isOpenImmersion_sectionComp : IsOpenImmersion (sectionComp b k) :=
  inferInstanceAs (IsOpenImmersion (k ≫ freeChartBaseSection b V))

/-- The factorisation through `b ⁻¹ᵁ U` of the section of `b` over `V` precomposed with an open
immersion landing in `U` is an open immersion. -/
instance isOpenImmersion_sectionCompPreimageLift :
    IsOpenImmersion (sectionCompPreimageLift b k hkU) :=
  haveI : IsOpenImmersion (sectionCompPreimageLift b k hkU ≫ (b ⁻¹ᵁ U).ι) := by
    rw [sectionCompPreimageLift_comp]; infer_instance
  IsOpenImmersion.of_comp (sectionCompPreimageLift b k hkU) (b ⁻¹ᵁ U).ι

variable {I : Type u} {G : X'.Modules} (α : _root_.SheafOfModules.free.{u} I ⟶ G)

include hkU in
/-- **`α` stays invertible after restriction along the section of `b` precomposed with an open
immersion landing in `U`**, because that composite factors through `b ⁻¹ᵁ U`, over which `α` is
invertible. -/
theorem isIso_restrictFunctor_map_sectionComp
    (hα : IsIso ((Scheme.Modules.restrictFunctor (b ⁻¹ᵁ U).ι).map α)) :
    IsIso ((Scheme.Modules.restrictFunctor (sectionComp b k)).map α) :=
  Scheme.Modules.isIso_restrictFunctor_map_of_fac α (b ⁻¹ᵁ U).ι (sectionCompPreimageLift b k hkU)
    (sectionCompPreimageLift_comp b k hkU) hα

/-- **The comparison, through `α`, of the inverse image of `G` along the section of `b` over `V`
with the free module**, over an open immersion into `V` landing in `U`. -/
def sectionFreeIso (hα : IsIso ((Scheme.Modules.restrictFunctor (b ⁻¹ᵁ U).ι).map α)) :
    Scheme.Modules.restrict (Scheme.Modules.restrict G (freeChartBaseSection b V)) k ≅
      _root_.SheafOfModules.free (R := T.ringCatSheaf) I :=
  haveI := isIso_restrictFunctor_map_sectionComp b k hkU α hα
  (restrictCompIso k (freeChartBaseSection b V) rfl G).symm ≪≫
    (asIso ((Scheme.Modules.restrictFunctor (sectionComp b k)).map α)).symm ≪≫
    Stacks.Modules.restrictFreeIso (sectionComp b k) I

end SectionComp

/-! ### The descent -/

section Descent

variable {X X' : Scheme.{u}} (b : X' ⟶ X) {U V : X.Opens} [IsIso (b ∣_ V)]
  {I : Type u} {G : X'.Modules} (α : _root_.SheafOfModules.free.{u} I ⟶ G)

/-- The overlap lies in the range of the inclusion of `V`. -/
theorem inf_le_opensRange_ι_right : U ⊓ V ≤ V.ι.opensRange := by
  rw [Scheme.Opens.opensRange_ι]
  exact inf_le_right

/-- **The inclusion of the overlap into `V`**, in the spelling whose codomain is `V` itself.
It agrees with `AlgebraicGeometry.TwoOpensGlue.mid U V ⟨true⟩`, whose codomain is instead the
member of the two-element family of opens. -/
def overlapToRight : (U ⊓ V).toScheme ⟶ V.toScheme :=
  openLift V.ι (inf_le_opensRange_ι_right (U := U) (V := V))

/-- The inclusion of the overlap into `V` is an open immersion. -/
instance isOpenImmersion_overlapToRight :
    IsOpenImmersion (overlapToRight (U := U) (V := V)) :=
  inferInstanceAs
    (IsOpenImmersion (openLift V.ι (inf_le_opensRange_ι_right (U := U) (V := V))))

/-- The inclusion of the overlap into `V`, composed with the inclusion of `V`, is the inclusion
of the overlap. -/
@[simp] theorem overlapToRight_comp :
    overlapToRight (U := U) (V := V) ≫ V.ι = (U ⊓ V).ι :=
  openLift_comp _ _

/-- The inclusion of the overlap into `V`, composed with the inclusion of `V`, lands in `U`. -/
theorem range_overlapToRight_comp_subset :
    Set.range (overlapToRight (U := U) (V := V) ≫ V.ι).base ⊆ (U : Set X) := by
  rw [overlapToRight_comp, Scheme.Opens.range_ι]
  exact inf_le_left

/-- The comparisons over the overlap of the restrictions of the two modules with the free module:
over `U` the module is free, over `V` it is identified with the free module through `α`. -/
def overlapIsoFamily (hα : IsIso ((Scheme.Modules.restrictFunctor (b ⁻¹ᵁ U).ι).map α)) :
    ∀ i, Scheme.Modules.restrict
        (TwoOpensGlue.mdl U V (_root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)
          (Scheme.Modules.restrict G (freeChartBaseSection b V)) i)
        (TwoOpensGlue.mid U V i) ≅
      _root_.SheafOfModules.free (R := (U ⊓ V).toScheme.ringCatSheaf) I
  | ⟨false⟩ => Stacks.Modules.restrictFreeIso (TwoOpensGlue.mid U V ⟨false⟩) I
  | ⟨true⟩ =>
      sectionFreeIso b (V := V) (overlapToRight (U := U) (V := V))
        (range_overlapToRight_comp_subset (U := U) (V := V)) α hα

/-- **A finite locally free module on `X'`, free over the preimage of `U` and pulled back along
the section of `b` over `V`, descends to a finite locally free module on `X`.**

The glueing is `AlgebraicGeometry.TwoOpensGlue.exists_restrict_iso_of_middle`, which asks only
for the two comparisons over the overlap and no cocycle; those are
`AlgebraicGeometry.overlapIsoFamily`.  Finite local freeness of the glued module is checked on
the two opens of the cover by
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_iSup_eq_top`. -/
theorem exists_isFiniteLocallyFree_restrict_iso_of_isIso_restrict_free
    (hUV : U ⊔ V = ⊤) [Finite I] (hG : Scheme.Modules.IsFiniteLocallyFree G)
    (hα : IsIso ((Scheme.Modules.restrictFunctor (b ⁻¹ᵁ U).ι).map α)) :
    ∃ N : X.Modules, Scheme.Modules.IsFiniteLocallyFree N ∧
      Nonempty (Scheme.Modules.restrict N U.ι ≅
        _root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) I) ∧
      Nonempty (Scheme.Modules.restrict N V.ι ≅
        Scheme.Modules.restrict G (freeChartBaseSection b V)) := by
  obtain ⟨N, ⟨eU⟩, ⟨eV⟩⟩ := TwoOpensGlue.exists_restrict_iso_of_middle U V
    (_root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)
    (Scheme.Modules.restrict G (freeChartBaseSection b V)) (overlapIsoFamily b α hα)
  refine ⟨N, ?_, ⟨eU⟩, ⟨eV⟩⟩
  have hiSup : (⨆ i, TwoOpensGlue.opn U V i) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hUV]
    exact sup_le (le_iSup_of_le ⟨false⟩ le_rfl) (le_iSup_of_le ⟨true⟩ le_rfl)
  refine Scheme.Modules.isFiniteLocallyFree_of_iSup_eq_top (TwoOpensGlue.opn U V) hiSup ?_
  intro i
  match i with
  | ⟨false⟩ =>
      exact Scheme.Modules.IsFiniteLocallyFree.of_iso eU.symm
        (Scheme.Modules.isFiniteLocallyFree_free I)
  | ⟨true⟩ =>
      exact Scheme.Modules.IsFiniteLocallyFree.of_iso eV.symm
        (Scheme.Modules.IsFiniteLocallyFree.restrict (freeChartBaseSection b V) hG)

end Descent

end AlgebraicGeometry

end
