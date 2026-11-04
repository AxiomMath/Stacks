module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedImmersionsPushforward.SetSheafEssentialImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralUniversallyInjectivePushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedGeometricStalkSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence

/-!
# Abelian sheaves supported on a closed subscheme

Let `i : Z ⟶ X` be a closed immersion. An abelian sheaf `G` on Mathlib's small étale site of `X`
whose stalks vanish at the geometric points of `X` lying outside `Z` is the direct image of its
inverse image: the unit `G ⟶ i_* i⁻¹ G` is an isomorphism. This is Stacks 04CA (2) for abelian
sheaves on the small étale site `AlgebraicGeometry.Scheme.smallEtaleTopology`; in particular the
proposition `Stacks.EtaleCohomology.AbelianEssImageClosedImmersion`, the form of that statement
used for integral universally injective morphisms, holds.

This is the step of the proof of Stacks 0F0V which writes a higher direct image supported on a
divisor as a direct image from that divisor.

## Main results

* `Stacks.EtaleCohomology.isZero_smallEtaleStalkAb_pushforwardAb_of_notMem_range`: a direct image
  from a closed subscheme has vanishing stalks away from it.
* `Stacks.EtaleCohomology.isIso_smallEtaleAdjunctionAb_unit_app_of_isZero_stalk`: the unit
  `G ⟶ i_* i⁻¹ G` is an isomorphism when the stalks of `G` vanish away from `Z`.
* `Stacks.EtaleCohomology.abelianEssImageClosedImmersion`: Stacks 04CA (2) in the form
  `Stacks.EtaleCohomology.AbelianEssImageClosedImmersion`.

## Implementation notes

Stalks at geometric points detect isomorphisms
(`Stacks.EtaleCohomology.isIso_iff_forall_isIso_smallEtaleStalkAb`). At a geometric point lying
over `Z` the point lifts to `Z`, the stalk of an inverse image is the stalk at the image point
(`Stacks.EtaleCohomology.smallEtaleStalkPullbackAbIso`), and the inverse image of the unit is an
isomorphism by the triangle identity, the counit being an isomorphism since `i_*` is fully
faithful. At a geometric point outside `Z` both stalks vanish; for the direct image this is read
the stalk at a geometric point of the open complement `U` of the inverse image to `U`, and the
restriction to `U` of a direct image from `Z` vanishes
(`Stacks.EtaleCohomology.isZero_etaleRestriction_etaleAbelianDirectImage`).

## References

* [Stacks Project, Tag 04CA](https://stacks.math.columbia.edu/tag/04CA)
* [Stacks Project, Tag 0F0V](https://stacks.math.columbia.edu/tag/0F0V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- **An abelian étale sheaf with vanishing stalks is zero.** -/
public theorem isZero_of_forall_isZero_smallEtaleStalkAb {X : Scheme.{u}}
    (G : Sheaf (smallEtaleTopology X) Ab.{u + 1})
    (hG : ∀ s : GeometricPoint X, IsZero ((smallEtaleStalkAb s.hom).obj G)) : IsZero G := by
  have hiso : IsIso (0 : G ⟶ G) :=
    (isIso_iff_forall_isIso_smallEtaleStalkAb _).2 fun s =>
      ⟨⟨0, (hG s).eq_of_src _ _, (hG s).eq_of_src _ _⟩⟩
  refine (IsZero.iff_id_eq_zero G).2 ?_
  rw [← IsIso.hom_inv_id (0 : G ⟶ G), zero_comp]

/-- A geometric point of `X` whose closed point lies in an open `U` factors through `U`. -/
public theorem exists_lift_opens_of_closedPoint_mem {X : Scheme.{u}} (U : X.Opens)
    {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ X)
    (hs : s (IsLocalRing.closedPoint Ω) ∈ (U : Set X)) :
    ∃ s' : Spec (.of Ω) ⟶ U.toScheme, s' ≫ U.ι = s := by
  have hrange : Set.range s ⊆ (U : Set X) := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z (IsLocalRing.closedPoint Ω)]
    exact hs
  exact ⟨IsOpenImmersion.lift U.ι s (by simpa using hrange), IsOpenImmersion.lift_fac _ _ _⟩

/-- If the restriction of an abelian sheaf `G` to an open `U` vanishes, its stalk at a geometric
point whose closed point lies in `U` vanishes. -/
private theorem isZero_stalk_of_isZero_pullback_opens {X : Scheme.{u}} (U : X.Opens)
    (G : Sheaf (smallEtaleTopology X) Ab.{u + 1}) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (hs : s (IsLocalRing.closedPoint Ω) ∈ (U : Set X))
    (hG : IsZero ((smallEtalePullbackAb U.ι).obj G)) : IsZero ((smallEtaleStalkAb s).obj G) := by
  obtain ⟨s', hs'⟩ := exists_lift_opens_of_closedPoint_mem U s hs
  have h := ((smallEtaleStalkAb s').map_isZero hG).of_iso
    ((smallEtaleStalkPullbackAbIso U.ι s').app G).symm
  rwa [hs'] at h

/-- A geometric point of `X` whose closed point lies in the image of a closed immersion
`i : Z ⟶ X` factors through `i`. -/
public theorem exists_lift_of_closedPoint_mem_range {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ X)
    (hs : s (IsLocalRing.closedPoint Ω) ∈ Set.range i) :
    ∃ b : Spec (.of Ω) ⟶ Z, b ≫ i = s := by
  let q := pullback.snd i s
  have : Surjective q := ⟨fun z => by
    change z ∈ Set.range q
    rw [show Set.range q = s ⁻¹' Set.range i from Scheme.Pullback.range_snd i s]
    exact (Subsingleton.elim z (IsLocalRing.closedPoint Ω)) ▸ hs⟩
  have : IsIso q := isIso_of_isClosedImmersion_of_surjective q
  refine ⟨inv q ≫ pullback.fst i s, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact IsIso.inv_hom_id_assoc q s

/-- **A direct image from a closed subscheme has vanishing stalks away from it.** For a closed
immersion `i : Z ⟶ X`, an abelian sheaf `H` on `Z_ét` and a geometric point `s` of `X` whose
image does not lie in `Z`, the stalk of `i_*H` at `s` is zero. -/
public theorem isZero_smallEtaleStalkAb_pushforwardAb_of_notMem_range {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (H : Sheaf (smallEtaleTopology Z) Ab.{u + 1})
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (hs : s (IsLocalRing.closedPoint Ω) ∉ Set.range i) :
    IsZero ((smallEtaleStalkAb s).obj ((smallEtalePushforwardAb i).obj H)) := by
  let U := openComplement i
  have hij : Set.range U.ι.base = (Set.range i.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    rfl
  have hzero : IsZero ((smallEtalePullbackAb U.ι).obj ((smallEtalePushforwardAb i).obj H)) :=
    (isZero_etaleRestriction_etaleAbelianDirectImage.{u, u + 1} i U.ι hij H).of_iso
      ((smallEtalePullbackAbIsoEtaleAbelianInverseImage U.ι).app _ ≪≫
        (etaleAbelianInverseImageRestrictionIso.{u, u + 1} U.ι).app _)
  exact isZero_stalk_of_isZero_pullback_opens U _ s hs hzero

/-- **Stacks 04CA (2), the converse half, for abelian sheaves on Mathlib's small étale site.** Let
`i : Z ⟶ X` be a closed immersion and `G` an abelian sheaf on `X_ét` whose stalk vanishes at
every geometric point of `X` not lying over `Z`. Then the unit `G ⟶ i_* i⁻¹ G` is an
isomorphism. -/
public theorem isIso_smallEtaleAdjunctionAb_unit_app_of_isZero_stalk {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (G : Sheaf (smallEtaleTopology X) Ab.{u + 1})
    (hG : ∀ s : GeometricPoint X, s.hom (IsLocalRing.closedPoint s.residueField) ∉ Set.range i →
      IsZero ((smallEtaleStalkAb s.hom).obj G)) :
    IsIso ((smallEtaleAdjunctionAb i).unit.app G) := by
  let adj := smallEtaleAdjunctionAb i
  have hfull : (smallEtalePushforwardAb i).Full :=
    inferInstanceAs (((smallEtaleBaseChange i).sheafPushforwardContinuous Ab.{u + 1}
      (smallEtaleTopology X) (smallEtaleTopology Z)).Full)
  have hfaith : (smallEtalePushforwardAb i).Faithful :=
    inferInstanceAs (((smallEtaleBaseChange i).sheafPushforwardContinuous Ab.{u + 1}
      (smallEtaleTopology X) (smallEtaleTopology Z)).Faithful)
  refine (isIso_iff_forall_isIso_smallEtaleStalkAb _).2 fun s => ?_
  by_cases hs : s.hom (IsLocalRing.closedPoint s.residueField) ∈ Set.range i
  · -- the geometric point lifts to `Z`
    obtain ⟨b, hb⟩ := exists_lift_of_closedPoint_mem_range i s.hom hs
    have hpb : IsIso ((smallEtalePullbackAb i).map (adj.unit.app G)) := by
      have htri : (smallEtalePullbackAb i).map (adj.unit.app G) ≫
          adj.counit.app ((smallEtalePullbackAb i).obj G) = 𝟙 _ :=
        adj.left_triangle_components G
      have : IsIso (adj.counit.app ((smallEtalePullbackAb i).obj G)) := by
        have := adj.counit_isIso_of_R_fully_faithful
        infer_instance
      have : IsIso ((smallEtalePullbackAb i).map (adj.unit.app G) ≫
          adj.counit.app ((smallEtalePullbackAb i).obj G)) := by
        rw [htri]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (adj.counit.app ((smallEtalePullbackAb i).obj G))
    have hcomp : IsIso ((smallEtalePullbackAb i ⋙ smallEtaleStalkAb b).map (adj.unit.app G)) :=
      inferInstanceAs (IsIso ((smallEtaleStalkAb b).map
        ((smallEtalePullbackAb i).map (adj.unit.app G))))
    have h := (NatIso.isIso_map_iff (smallEtaleStalkPullbackAbIso i b) (adj.unit.app G)).1 hcomp
    rwa [hb] at h
  · -- both stalks vanish
    exact ⟨⟨0, (hG s hs).eq_of_src _ _,
      (isZero_smallEtaleStalkAb_pushforwardAb_of_notMem_range i
        ((smallEtalePullbackAb i).obj G) s.hom hs).eq_of_src _ _⟩⟩

/-- **Stacks 04CA (2) for abelian sheaves on Mathlib's small étale site.** For a closed immersion
`j : Z ⟶ W` and an open `U` of `W` complementary to its image, an abelian sheaf on `W_ét` is a
direct image along `j` exactly when its restriction to `U` vanishes. -/
public theorem abelianEssImageClosedImmersion : AbelianEssImageClosedImmersion.{u} := by
  intro Z W j _ U hU G
  constructor
  · rintro ⟨H, ⟨e⟩⟩
    refine IsZero.of_iso ?_ ((smallEtalePullbackAb U.ι).mapIso e.symm)
    refine isZero_of_forall_isZero_smallEtaleStalkAb _ fun s => ?_
    refine (isZero_smallEtaleStalkAb_pushforwardAb_of_notMem_range j H (s.hom ≫ U.ι) ?_).of_iso
      ((smallEtaleStalkPullbackAbIso U.ι s.hom).app _)
    have hmem : (s.hom ≫ U.ι) (IsLocalRing.closedPoint s.residueField) ∈ (U : Set W) :=
      (s.hom (IsLocalRing.closedPoint s.residueField)).property
    rwa [hU] at hmem
  · intro hG
    refine ⟨(smallEtalePullbackAb j).obj G,
      ⟨(@asIso _ _ _ _ _ (isIso_smallEtaleAdjunctionAb_unit_app_of_isZero_stalk j G ?_)).symm⟩⟩
    intro s hs
    exact isZero_stalk_of_isZero_pullback_opens U G s.hom (by rwa [hU]) hG

end Stacks.EtaleCohomology

end
