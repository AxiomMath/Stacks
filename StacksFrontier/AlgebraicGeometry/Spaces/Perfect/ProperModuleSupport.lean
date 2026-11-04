module

public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingGeneratorOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealZeroLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupportSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType

/-!
# Modules with proper support on an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type and let `F` be a finite type quasi-coherent `𝒪_X`-module.  **Stacks 0CZI** asserts that
the following are equivalent: the support of `F` is proper over `Y`; the scheme-theoretic
support of `F`, Stacks 07U1, is proper over `Y`; and `F` is the direct image of a finite type
quasi-coherent module from *some* closed subspace of `X` which is proper over `Y`.

The support of `F` is closed by Stacks 07TZ, so Definition 0CZD applies to it, and the
scheme-theoretic support is a closed subspace whose set of points is exactly that support
(Stacks 07U0, part (4)).  Since properness over the base of a closed subspace depends only on
its set of points — Stacks 0CZC — the first two conditions agree.  The second implies the third
by the existence clause of Stacks 07U0, and the third implies the first because the support of a
module annihilated by the ideal cutting out a closed subspace lies in the set of points of that
subspace, where Stacks 0CZE applies.

## Main results

* `AlgebraicGeometry.Space.supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport`: the support
  of a finite type module is the set of points of its scheme-theoretic support, part (4) of
  Stacks 07U0.
* `AlgebraicGeometry.Space.supportOfSheaf_subset_range_pointsMap_of_annihilatedByKerIdeal`: the
  support of a module annihilated by the ideal cutting out a closed subspace is contained in the
  set of points of that closed subspace.
* `AlgebraicGeometry.Space.isProperOver_range_pointsMap_of_isProper`: the set of points of a
  closed subspace proper over the base is proper over the base in the sense of Stacks 0CZD.
* `AlgebraicGeometry.Space.hasProperSupport_tfae`: **Stacks 0CZI**, the three conditions are
  equivalent.

## Implementation notes

The implication (2) ⟹ (3) rests on
`AlgebraicGeometry.Space.exists_module_on_schemeTheoreticSupport`, the existence clause of
Stacks 07U0, which is the essential-image assertion of Stacks 04CJ, part (3) — equivalently
Stacks 04E5, part (2) — at the inclusion of the scheme-theoretic support: a quasi-coherent
`𝒪_X`-module annihilated by the ideal cutting out a closed subspace is the direct image of a
quasi-coherent module on it.  That assertion is proved for every closed immersion by
`AlgebraicGeometry.Space.isQuasicoherentEssImagePushforward_of_isClosedImmersion`, from the
essential-image clause of Stacks 08KS and quasi-coherence of the inverse image, Stacks 03GA.
The implications (1) ⟹ (2) and (3) ⟹ (1) use neither.

Finite type is taken twice, in the two forms the inputs consume: the categorical
`SheafOfModules.IsFiniteTypeOnSite` which the support statements of Stacks 07TZ and part (4) of
Stacks 07U0 use, and the sectionwise `CategoryTheory.PresheafOfModules.IsFiniteType` of
Stacks 03DL(5) which the construction of the closed subspace cut out by the annihilator ideal
uses.  This matches
`AlgebraicGeometry.Space.exists_isClosedSubspace_schemeTheoreticSupport` and
`AlgebraicGeometry.Space.isFiniteTypeOnSite_module_on_closedSubspace`, which take one each.

Condition (1) is `AlgebraicGeometry.Space.HasProperSupport`, which carries closedness of the
support as an existential witness; for a module of finite type that witness is supplied by
Stacks 07TZ and the condition is just properness of the support over `Y`.

## References

* [Stacks Project, Lemma 76.40.6 (Tag 0CZI)](https://stacks.math.columbia.edu/tag/0CZI)
* [Stacks Project, Tag 07U0](https://stacks.math.columbia.edu/tag/07U0)
* [Stacks Project, Tag 07U1](https://stacks.math.columbia.edu/tag/07U1)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 0CZC](https://stacks.math.columbia.edu/tag/0CZC)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 0CZE](https://stacks.math.columbia.edu/tag/0CZE)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X Y : AlgebraicSpaces B S hS) (f : X.1 ⟶ Y.1)
    (hf : IsLocallyOfFiniteType B S hS f)

/-! ### The annihilator ideal at a chart and vanishing of sections -/

/-- **A module whose annihilator ideal is the whole structure sheaf on a chart has no nonzero
sections over any chart over it.**  The unit function lies in the annihilator ideal, so it kills
the sections over every chart over the one in question, and it acts as the identity. -/
private theorem subsingleton_of_annihilatorIdealAt_eq_top (F : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS X.1) (hV : annihilatorIdealAt B S hS X F (op V) = ⊤)
    (W : SmallEtale B S hS X.1) (g : W ⟶ V) :
    Subsingleton (F.val.obj (op W)) := by
  have h1 := (Ideal.eq_top_iff_one (annihilatorIdealAt B S hS X F (op V))).mp hV
  have key : ∀ t : F.val.obj (op W), t = 0 := fun t => by
    have ht := h1 (op W) g.op t
    simp only [map_one] at ht
    exact (one_smul (chartRing B S hS X.1 X.2 W) t).symm.trans ht
  exact ⟨fun a b => (key a).trans (key b).symm⟩

/-- **The annihilator ideal is the whole structure sheaf on a chart over which the module has
no nonzero sections.** -/
private theorem annihilatorIdealAt_eq_top_of_subsingleton (F : Modules.{u, u} B S hS X.1 X.2)
    (U : SmallEtale B S hS X.1)
    (h : ∀ W : SmallEtale B S hS X.1, (W ⟶ U) → Subsingleton (F.val.obj (op W))) :
    annihilatorIdealAt B S hS X F (op U) = ⊤ := by
  refine top_le_iff.1 fun a _ W g t => ?_
  exact @Subsingleton.elim _ (h W.unop g.unop) _ 0

/-! ### The support of a module against a closed subspace -/

/-- **The support of a module annihilated by the ideal cutting out a closed subspace is
contained in the set of points of that subspace.**

The set of points of a closed subspace is the zero locus of its defining ideal sheaf, and that
ideal sheaf lies in the annihilator ideal sheaf of the module; so on a chart where the defining
ideal is the whole structure sheaf the annihilator ideal is too, and there the module has no
nonzero sections over any chart over it, which keeps the support out of the image of that
chart. -/
theorem supportOfSheaf_subset_range_pointsMap_of_annihilatedByKerIdeal
    (F : Modules.{u, u} B S hS X.1 X.2) (Z : ClosedSubspaces B S hS X.1)
    (hann : AnnihilatedByKerIdeal B S hS (closedSubspaceInclusion B S hS X Z) F) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) ⊆
      Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) := by
  rw [range_pointsMap_ι_eq_idealZeroLocus B S hS X Z]
  refine supportOfSheaf_subset_idealZeroLocus_of_forall_subsingleton B S hS X F _
    fun V hV W g => ?_
  have hle := definingIdealSheaf_le_annihilatorIdealSheaf B S hS X F Z hann
  have htop : annihilatorIdealAt B S hS X F (op V) = ⊤ :=
    top_le_iff.1 fun _ _ => hle (op V) (hV.ge Submodule.mem_top)
  exact subsingleton_of_annihilatorIdealAt_eq_top B S hS X F V htop W g

/-- **The set of points of a closed subspace proper over the base is proper over the base** in
the sense of Stacks 0CZD.  This is one half of Stacks 0CZC applied to the closed subspace
itself. -/
theorem isProperOver_range_pointsMap_of_isProper (Z : ClosedSubspaces B S hS X.1)
    (hZp : IsProper B S hS (Z.1.ι ≫ f)) :
    IsProperOver B S hS X.2 Y.2 f hf (Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι))
      (isClosed_range_pointsMap_of_isClosedImmersion B S hS X.2 Z.1.ι Z.2.2) :=
  (isProper_reducedClosedSubspace_iff_exists B S hS X.2 Y.2 f hf _ _).2
    ⟨Z.1, Z.2, rfl, hZp⟩

/-- **The support of a finite type `𝒪_X`-module is the set of points of its scheme-theoretic
support.**

The point set of a closed subspace is the zero locus of its defining ideal sheaf, and the ideal
sheaf cutting out the scheme-theoretic support is the annihilator ideal of `F`; so the claim is
that the support of `F` is the zero locus of its annihilator ideal sheaf.  One inclusion needs
only that the unit function lies in the annihilator ideal wherever that ideal is the whole of
`𝒪_X`, so `F` vanishes on every chart over such a chart and its support misses the image.  The
other is where finite type enters: off the support every geometric stalk of `F` vanishes, and
for a module of finite type that produces a small étale neighbourhood over which `F` has no
nonzero sections at all, hence a chart whose image contains the point and on which the
annihilator ideal is everything.

That the scheme-theoretic support is a closed subspace cut out by the annihilator ideal sheaf
is `AlgebraicGeometry.Space.exists_isClosedSubspace_schemeTheoreticSupport`, which quasi-
coherence and finite type supply.

This is part (4) of [Stacks, Tag 07U0] for the module on the ambient space. -/
@[stacks 07U0 "part (4): the support of F is the point set of its scheme-theoretic support"]
theorem supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (hFft : SheafOfModules.IsFiniteTypeOnSite F) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) =
      Set.range (pointsMap B S hS (schemeTheoreticSupport B S hS X F).toFunctor
        (schemeTheoreticSupport B S hS X F).ι) := by
  have _ := hFft
  obtain ⟨hZ, hid⟩ := exists_isClosedSubspace_schemeTheoreticSupport B S hS X F hF
    (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite F hFft)
  rw [range_pointsMap_ι_eq_idealZeroLocus B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩, hid]
  refine subset_antisymm (supportOfSheaf_subset_idealZeroLocus_of_forall_subsingleton B S hS X F
    _ fun V hV W g => subsingleton_of_annihilatorIdealAt_eq_top B S hS X F V hV W g) ?_
  intro x hx
  by_contra hns
  obtain ⟨p, hp⟩ := exists_geometricRepresentative B S hS X.1 x
  have hsub : Subsingleton (stalkSet p
      (((SheafOfModules.toSheaf _).obj F).obj ⋙ forget AddCommGrpCat.{u})) := by
    by_contra hc
    exact hns ⟨p, hp, hc⟩
  obtain ⟨N, hN⟩ :=
    exists_zero_neighborhood_of_isFiniteTypeOnSite B S hS X.1 X.2 (𝟙 F) p hsub
  refine (mem_idealZeroLocus_iff B S hS X _ x).1 hx N.chart
    (annihilatorIdealAt_eq_top_of_subsingleton B S hS X F N.chart hN) ?_
  exact ⟨(neighborhoodPoint B S hS X.1 N).image,
    (neighborhoodPoint_image B S hS X.1 N).trans hp⟩

/-! ### Stacks 0CZI -/

/-- **Stacks 0CZI.**  Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is
locally of finite type and let `F` be a finite type quasi-coherent `𝒪_X`-module.  The following
are equivalent:

1. the support of `F` is proper over `Y`;
2. the scheme-theoretic support of `F`, Stacks 07U1, is proper over `Y`;
3. there are a closed subspace `Z ⊆ X` and a finite type quasi-coherent `𝒪_Z`-module `G` with
   `Z → Y` proper and `(Z → X)_* G = F`.

The support of `F` is closed by Stacks 07TZ, so Definition 0CZD applies to it; the
scheme-theoretic support is a closed subspace whose set of points is that support by Stacks 07U0
part (4), so (1) and (2) agree by Stacks 0CZC, which says that properness over the base of a
closed subspace depends only on its set of points.  (2) implies (3) by the existence clause of
Stacks 07U0, together with part (3) of the same lemma for finite type of the module.  (3)
implies (1) because the support of `F` is contained in the set of points of `Z`, which is proper
over `Y` by Stacks 0CZC, so Stacks 0CZE applies. -/
@[stacks 0CZI]
theorem hasProperSupport_tfae (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (hFft : SheafOfModules.IsFiniteTypeOnSite F)
    (hft : PresheafOfModules.IsFiniteType (smallEtaleRingedSite B S hS X.1 X.2).J F.val) :
    List.TFAE
      [HasProperSupport B S hS X.2 Y.2 f hf ((SheafOfModules.toSheaf _).obj F),
        IsProper B S hS ((schemeTheoreticSupport B S hS X F).ι ≫ f),
        ∃ (Z : ClosedSubspaces B S hS X.1)
          (G : Modules.{u, u} B S hS (closedSubspaceToSpace B S hS X Z).1
            (closedSubspaceToSpace B S hS X Z).2),
          G.IsQuasicoherentOnSite ∧ SheafOfModules.IsFiniteTypeOnSite G ∧
            IsProper B S hS (Z.1.ι ≫ f) ∧
            Nonempty ((modulePushforward B S hS
              (closedSubspaceInclusion B S hS X Z)).obj G ≅ F)] := by
  have _ := hFft
  obtain ⟨hZ, hid⟩ := exists_isClosedSubspace_schemeTheoreticSupport B S hS X F hF hft
  have hsuppcl : IsClosed (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F)) :=
    isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.2 F
  have hrange : Set.range (pointsMap B S hS (schemeTheoreticSupport B S hS X F).toFunctor
      (schemeTheoreticSupport B S hS X F).ι) =
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) :=
    (supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport B S hS X F hF hFft).symm
  tfae_have 1 → 2 := by
    rintro ⟨hcl, hp⟩
    exact (exists_isProper_closedSubspace_iff_forall B S hS X.2 Y.2 f hf _ hcl).1
      ((isProper_reducedClosedSubspace_iff_exists B S hS X.2 Y.2 f hf _ hcl).1 hp)
      (schemeTheoreticSupport B S hS X F) hZ hrange
  tfae_have 2 → 3 := by
    intro h2
    obtain ⟨hZ', G, hGqc, ⟨e⟩⟩ :=
      exists_module_on_schemeTheoreticSupport B S hS X F hF hft
    exact ⟨⟨schemeTheoreticSupport B S hS X F, hZ'⟩, G, hGqc,
      isFiniteTypeOnSite_module_on_closedSubspace B S hS X F hFft
        ⟨schemeTheoreticSupport B S hS X F, hZ'⟩ G e, h2, ⟨e⟩⟩
  tfae_have 3 → 1 := by
    rintro ⟨Z, G, -, -, hZp, ⟨e⟩⟩
    refine ⟨hsuppcl, isProperOver_of_subset B S hS X.2 Y.2 f hf _ _ hsuppcl
      (isClosed_range_pointsMap_of_isClosedImmersion B S hS X.2 Z.1.ι Z.2.2)
      (supportOfSheaf_subset_range_pointsMap_of_annihilatedByKerIdeal B S hS X F Z
        (annihilatedByKerIdeal_of_essImage_modulePushforward B S hS
          (closedSubspaceInclusion B S hS X Z) ⟨G, ⟨e⟩⟩))
      (isProperOver_range_pointsMap_of_isProper B S hS X Y f hf Z hZp)⟩
  tfae_finish

end AlgebraicGeometry.Space

end
