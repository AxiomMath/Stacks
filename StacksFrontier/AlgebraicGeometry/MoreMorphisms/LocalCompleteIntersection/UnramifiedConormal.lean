module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Perfect
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.Implications
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.ConormalLocallyFree
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag
public import StacksFrontier.AlgebraicGeometry.Thickenings.ImmersionConormalIdentification
public import StacksFrontier.AlgebraicGeometry.Thickenings.OpenRestriction
public import StacksFrontier.AlgebraicGeometry.Thickenings.UnramifiedPairConormalSequence
public import StacksFrontier.AlgebraicGeometry.Thickenings.UnramifiedPairSplitConormalSequence
public import StacksFrontier.Topology.Sheaves.RecoveryExtend.FiniteLocallyFreeRetract

/-!
# Unramified local complete intersection morphisms

A local complete intersection morphism of schemes is unramified exactly when it is formally
unramified, because such a morphism is locally of finite type. In that case its conormal sheaf
is finite locally free.

## Main results

* `AlgebraicGeometry.unramified_iff_formallyUnramified_of_isLocalCompleteIntersectionMorphism`:
  the two conditions agree on a local complete intersection morphism.
* `AlgebraicGeometry.isFiniteLocallyFree_universalConormalSheaf_of_isKoszulRegularImmersion`: the
  conormal sheaf of a Koszul-regular immersion is finite locally free.
* `AlgebraicGeometry.isFiniteLocallyFree_universalConormalSheaf_of_isLocalCompleteIntersection`:
  the conormal sheaf of a formally unramified local complete intersection morphism is finite
  locally free.
* `AlgebraicGeometry.universalConormalSheafRestrictIso`: Stacks 04FA, the restriction of the
  conormal sheaf to compatible opens, as an isomorphism.

## Implementation notes

The equivalence is Stacks 02HE, which characterises unramifiedness as local finite type together
with formal unramifiedness, against the local finite type of a local complete intersection
morphism; the latter comes from finite type at every point, which is part (1) of Stacks 069F.

Finite local freeness of the conormal sheaf is local on the source, by
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_iSup_eq_top`, and is proved on two
nested covers. On an open `U` of the source carrying a factorization `U ⟶ P ⟶ S` of the
morphism into a Koszul-regular immersion followed by a smooth morphism, Stacks 04FA identifies
the restriction of the conormal sheaf with the conormal sheaf of `U` over `S`. That restriction
statement produces a morphism to an open of the target, so the factorization is read over the
open subscheme `(⊤ : S.Opens).toScheme`, by composing the smooth morphism with the inverse of
`AlgebraicGeometry.Scheme.topIso`, which is again smooth. On a smaller open `W` of `U` the
conormal sheaf of `U` over `S` is a direct summand of that of `U` over `P`, which is finite
locally free because the immersion is Koszul-regular, hence quasi-regular; Stacks 0BCI concludes.

The direct-summand input is the locally split clause of Stacks 067W,
`Stacks.ConormalSequenceUnramifiedPair.exists_retraction_restrict_universalConormalTransitivityMap`:
the canonical transitivity map of Stacks 067V admits a retraction after restriction to a
neighbourhood of every point of the source. Nothing here is conditional.

## References

* [The Stacks Project, Lemma 37.62.22 (06B9)](https://stacks.math.columbia.edu/tag/06B9)
* [The Stacks Project, Lemma 37.6.9 (02HE)](https://stacks.math.columbia.edu/tag/02HE)
* [The Stacks Project, Definition 37.62.2 (069F)](https://stacks.math.columbia.edu/tag/069F)
* [The Stacks Project, Lemma 37.11.13 (067W)](https://stacks.math.columbia.edu/tag/067W)
* [The Stacks Project, Lemma 31.22.5 (063M)](https://stacks.math.columbia.edu/tag/063M)
* [The Stacks Project, Lemma 37.9.5 (04FA)](https://stacks.math.columbia.edu/tag/04FA)
* [The Stacks Project, Lemma 17.19.4 (0BCI)](https://stacks.math.columbia.edu/tag/0BCI)
-/

@[expose] public section

open CategoryTheory
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.Thickenings (universalConormalSheaf universalFirstOrderThickening)
open Stacks.ConormalSequenceUnramifiedPair
  (exists_retraction_restrict_universalConormalTransitivityMap)

universe u

namespace AlgebraicGeometry

/-- A local complete intersection morphism of schemes is unramified if and only if it is
formally unramified. -/
@[stacks 06B9 "the equivalence: a local complete intersection morphism is unramified if and
only if it is formally unramified"]
theorem unramified_iff_formallyUnramified_of_isLocalCompleteIntersectionMorphism
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : IsLocalCompleteIntersectionMorphism f) :
    Unramified f ↔ FormallyUnramified f :=
  (unramified_iff_locallyOfFiniteType_and_formallyUnramified f).trans
    ⟨And.right, fun h ↦ ⟨locallyOfFiniteType_of_isLocalCompleteIntersectionMorphism hf, h⟩⟩

/-- The conormal sheaf of a Koszul-regular immersion of schemes, in the sense of Stacks 04F4, is
finite locally free. -/
@[stacks 063M "condition (2) for a Koszul-regular immersion, for the conormal sheaf of Tag
04F4. Condition (1) is at RegularImmersion/FinitePresentation.lean; condition (2) does not
need Tag 063H, and is
proved at RegularImmersion/ConormalLocallyFree.lean by a route through Tags 063G, 08RK, 01R3,
00NX and 05JM that never uses 063H"]
theorem isFiniteLocallyFree_universalConormalSheaf_of_isKoszulRegularImmersion
    {Z P : Scheme.{u}} (i : Z ⟶ P) [IsImmersion i] (hi : IsKoszulRegularImmersion i) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} (universalConormalSheaf i) :=
  SheafOfModules.IsFiniteLocallyFree.of_iso
    (h := isFiniteLocallyFree_conormalSheaf_of_isQuasiRegularImmersion i
      (isQuasiRegularImmersion_of_isH1RegularImmersion i
        (isH1RegularImmersion_of_isKoszulRegularImmersion i hi)))
    (Stacks.Thickenings.immersionConormalSheafIsoUniversalConormalSheaf i)

/-- **Stacks 04FA, the restriction of the conormal sheaf, as an isomorphism.** For opens `U` of
the source and `V` of the target of a formally unramified morphism `f : X ⟶ S` with
`f (U) ⊆ V`, the restriction to `U` of the conormal sheaf of `f` is the conormal sheaf of the
restriction of `f` to a morphism `U ⟶ V`. -/
@[stacks 04FA "restriction of the conormal sheaf to an open, as an isomorphism of sheaves of
modules on that open"]
noncomputable def universalConormalSheafRestrictIso {X S : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] {V : S.Opens} {U : X.Opens} (hUV : U ≤ f ⁻¹ᵁ V)
    [FormallyUnramified (f.resLE V U hUV)] :
    (Scheme.Modules.restrictFunctor U.ι).obj (universalConormalSheaf f) ≅
      universalConormalSheaf (f.resLE V U hUV) :=
  have hm : IsIso (C := U.toScheme.Modules) (Stacks.Thickenings.universalImmersionConormalSheafMap
      (universalFirstOrderThickening (f.resLE V U hUV)) (universalFirstOrderThickening f)
      U.ι V.ι (Scheme.Hom.resLE_comp_ι f hUV)) :=
    Stacks.Thickenings.isIso_universalConormalSheafMap_resLE f hUV
  (Scheme.Modules.restrictFunctorIsoPullback U.ι).app (universalConormalSheaf f) ≪≫
    @asIso U.toScheme.Modules _ _ _ _ hm

/-- A sheaf of modules on a scheme that is finite locally free on an open neighbourhood of every
point is finite locally free. -/
private theorem isFiniteLocallyFree_of_locally {Z : Scheme.{u}} (M : Z.Modules)
    (h : ∀ z : Z, ∃ W : Z.Opens, z ∈ W ∧
      Scheme.Modules.IsFiniteLocallyFree ((Scheme.Modules.restrictFunctor W.ι).obj M)) :
    Scheme.Modules.IsFiniteLocallyFree M := by
  choose W hzW hW using h
  exact Scheme.Modules.isFiniteLocallyFree_of_iSup_eq_top W
    (le_antisymm le_top fun z _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hzW z⟩) hW

/-- A sheaf of modules on a scheme that is, near every point, a direct summand of a finite
locally free sheaf of modules is itself finite locally free; this is Stacks 0BCI read on an open
cover. -/
private theorem isFiniteLocallyFree_of_locally_retract {Z : Scheme.{u}} (M : Z.Modules)
    (h : ∀ z : Z, ∃ W : Z.Opens, z ∈ W ∧ ∃ N : W.toScheme.Modules,
      Scheme.Modules.IsFiniteLocallyFree N ∧
        ∃ (s : (Scheme.Modules.restrictFunctor W.ι).obj M ⟶ N)
          (r : N ⟶ (Scheme.Modules.restrictFunctor W.ι).obj M), s ≫ r = 𝟙 _) :
    Scheme.Modules.IsFiniteLocallyFree M := by
  refine isFiniteLocallyFree_of_locally M fun z ↦ ?_
  obtain ⟨W, hzW, N, hN, s, r, hsr⟩ := h z
  refine ⟨W, hzW, ?_⟩
  have : ∀ w : W.toScheme.toTopCat, IsLocalRing (ToType (W.toScheme.sheaf.presheaf.stalk w)) :=
    fun w ↦ W.toScheme.toLocallyRingedSpace.isLocalRing w
  refine (Scheme.Modules.isFiniteLocallyFree_iff _).mpr ?_
  exact Stacks.SheafOfModules.isFiniteLocallyFree_of_retract
    (X := W.toScheme.toTopCat) (O := W.toScheme.sheaf) ⟨⟨s, r, hsr⟩⟩
    ((Scheme.Modules.isFiniteLocallyFree_iff N).mp hN)

/-- The conormal sheaf of a formally unramified local complete intersection morphism of schemes
is finite locally free. -/
@[stacks 06B9 "finite local freeness of the conormal sheaf of a local complete intersection
morphism. Tag 063H is NOT needed: the Koszul-regular factor is quasi-regular, and condition (2)
of Tag 063M is available for those"]
theorem isFiniteLocallyFree_universalConormalSheaf_of_isLocalCompleteIntersection
    {X S : Scheme.{u}} (f : X ⟶ S) [FormallyUnramified f]
    (hf : IsLocalCompleteIntersectionMorphism f) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} (universalConormalSheaf f) := by
  refine (Scheme.Modules.isFiniteLocallyFree_iff _).mp ?_
  refine isFiniteLocallyFree_of_locally _ fun x ↦ ?_
  obtain ⟨-, U, hxU, P, i, π, hi, hiK, hπ, hfac⟩ := hf x
  have : IsImmersion i := hi
  have : Smooth π := hπ
  refine ⟨U, hxU, ?_⟩
  have hUV : U ≤ f ⁻¹ᵁ (⊤ : S.Opens) := by simp
  have : FormallyUnramified (f.resLE (⊤ : S.Opens) U hUV) :=
    Stacks.Thickenings.formallyUnramified_resLE f hUV
  refine Scheme.Modules.IsFiniteLocallyFree.of_iso
    (universalConormalSheafRestrictIso f hUV).symm ?_
  have hij : i ≫ (π ≫ S.topIso.inv) = f.resLE (⊤ : S.Opens) U hUV := by
    rw [← Category.assoc, ← hfac, ← Scheme.Hom.resLE_comp_ι f hUV, Category.assoc]
    simp
  have hsm : Stacks.Smooth.FormallySmoothScheme (π ≫ S.topIso.inv) :=
    ((Stacks.Smooth.smooth_iff_locallyOfFinitePresentation_and_formallySmooth
      (π ≫ S.topIso.inv)).mp inferInstance).2
  have hD : Scheme.Modules.IsFiniteLocallyFree (universalConormalSheaf i) :=
    (Scheme.Modules.isFiniteLocallyFree_iff (universalConormalSheaf i)).mpr
      (isFiniteLocallyFree_universalConormalSheaf_of_isKoszulRegularImmersion i hiK)
  refine isFiniteLocallyFree_of_locally_retract _ fun y ↦ ?_
  obtain ⟨W, hyW, r, hr⟩ :=
    exists_retraction_restrict_universalConormalTransitivityMap
      i (f.resLE (⊤ : S.Opens) U hUV) (π ≫ S.topIso.inv) hij hsm y
  exact ⟨W, hyW, _, hD.restrict W.ι, _, r, hr⟩

end AlgebraicGeometry

end
