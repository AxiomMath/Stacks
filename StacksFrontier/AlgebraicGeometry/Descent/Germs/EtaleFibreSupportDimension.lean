module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleLocalDimension
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.FibrePoints
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType

/-!
# Fibres, supports and dimension along an étale morphism

Tag 04N4 says that an étale morphism of schemes preserves the local Krull dimension at
corresponding points. This module draws the three consequences needed to transport the numerical
data of a one-step dévissage (Tag 05H5) across an étale localization of the source.

First, the preimage of a closed subset along an étale morphism has, at each point, the same local
dimension as the subset has at the image point; hence it has the same dimension as the subset as
soon as that dimension is attained at one point whose image is chosen, and then it is attained at
that point too.

Second, for an étale `u : X ⟶ Y` over `g : Y ⟶ S` the fibres of `u ≫ g` and of `g` over a point
of `S` have equal dimension, provided both are geometrically irreducible there, since they are
étale over one another and the dimension of an irreducible scheme over a field is its dimension
at any point (Tag 0A21).

Third, combining the two: if the support of a finite-type module on `X` is the preimage of the
support of one on `Y`, the dimension of the support on the fibre of `u ≫ g`, and the fact that it
is attained at the chosen point, are inherited from `Y`.

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_preimage_eq_of_etale`.
* `AlgebraicGeometry.topologicalKrullDim_preimage_eq_of_etale`.
* `AlgebraicGeometry.topologicalKrullDim_fiber_comp_eq_of_etale`.
* `AlgebraicGeometry.exists_mem_supp_fiber_dimension_of_etale`.

## Implementation notes

For the first statement the closed subset is realized as a closed subscheme — the vanishing ideal
sheaf of the closed set — so that Tag 04N4 can be applied to the base change of the étale
morphism along the closed immersion; the two closed immersions then identify the closed set and
its preimage with the two schemes homeomorphically.

The comparison morphism of fibres is `AlgebraicGeometry.Scheme.Hom.fiberMapComp`; it is étale
whenever `u` is, being the base change of `u` up to an isomorphism of pullbacks.

## References

* [Stacks Project, Tag 04N4](https://stacks.math.columbia.edu/tag/04N4)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Preimages of closed subsets -/

/-- The preimage of a closed subset along an étale morphism has the same local dimension at a
point as the subset has at the image of that point. -/
theorem topologicalKrullDimAt_preimage_eq_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
    (C : Set Y) (hC : IsClosed C) (x : f ⁻¹' C) :
    topologicalKrullDimAt (f ⁻¹' C) x = topologicalKrullDimAt C ⟨f x, x.property⟩ := by
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨C, hC⟩ : TopologicalSpace.Closeds Y)
  have hI : Set.range I.subschemeι = C := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal _
  let a : pullback f I.subschemeι ⟶ X := pullback.fst f I.subschemeι
  let d : pullback f I.subschemeι ⟶ I.subscheme := pullback.snd f I.subschemeι
  have ha : Set.range a = f ⁻¹' C := by
    rw [Scheme.Pullback.range_fst, hI]
  let eX : (pullback f I.subschemeι : Scheme.{u}) ≃ₜ (f ⁻¹' C) :=
    (IsClosedImmersion.isClosedEmbedding a).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr ha)
  let eY : (I.subscheme : Scheme.{u}) ≃ₜ C :=
    (IsClosedImmersion.isClosedEmbedding I.subschemeι).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr hI)
  have hx : a (eX.symm x) = x.val := congrArg Subtype.val (eX.apply_symm_apply x)
  have he : eY (d (eX.symm x)) = ⟨f x, x.property⟩ := by
    apply Subtype.ext
    show I.subschemeι (d (eX.symm x)) = f x
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, hx]
  calc
    topologicalKrullDimAt (f ⁻¹' C) x = topologicalKrullDimAt _ (eX.symm x) :=
      topologicalKrullDimAt_eq_of_homeomorph eX.symm x
    _ = topologicalKrullDimAt I.subscheme (d (eX.symm x)) :=
      topologicalKrullDimAt_eq_of_etale d _
    _ = topologicalKrullDimAt C (eY (d (eX.symm x))) :=
      topologicalKrullDimAt_eq_of_homeomorph eY _
    _ = _ := congrArg _ he

/-- If the dimension of a closed subset is attained as a local dimension at the image of a point
of the preimage along an étale morphism, then the preimage has the same dimension, and attains it
at that point. -/
theorem topologicalKrullDim_preimage_eq_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
    (C : Set Y) (hC : IsClosed C) (x : f ⁻¹' C)
    (hx : topologicalKrullDimAt C ⟨f x, x.property⟩ = topologicalKrullDim C) :
    topologicalKrullDim (f ⁻¹' C) = topologicalKrullDim C ∧
      topologicalKrullDimAt (f ⁻¹' C) x = topologicalKrullDim (f ⁻¹' C) := by
  have hlocal := (topologicalKrullDimAt_preimage_eq_of_etale f C hC x).trans hx
  have hdim : topologicalKrullDim (f ⁻¹' C) = topologicalKrullDim C := by
    refine le_antisymm ?_ ?_
    · rw [topologicalKrullDim_eq_iSup_localKrullDim]
      refine iSup_le fun p => ?_
      rw [← topologicalKrullDimAt_eq_localKrullDim,
        topologicalKrullDimAt_preimage_eq_of_etale f C hC p]
      exact topologicalKrullDimAt_le_topologicalKrullDim _
    · rw [← hlocal]
      exact topologicalKrullDimAt_le_topologicalKrullDim _
  exact ⟨hdim, hlocal.trans hdim.symm⟩

/-! ### Fibres of a composition with an étale morphism -/

/-- The fibre of `u ≫ g` over a point is the base change of `u` along the inclusion of the fibre
of `g` over that point, with `AlgebraicGeometry.Scheme.Hom.fiberMapComp` as the projection. -/
theorem isPullback_fiberMapComp {X Y S : Scheme.{u}} (u : X ⟶ Y) (g : Y ⟶ S) (s : S) :
    IsPullback ((u ≫ g).fiberι s) (Scheme.Hom.fiberMapComp u g s) u (g.fiberι s) := by
  refine IsPullback.of_iso_pullback ⟨(Scheme.Hom.fiberMapComp_fiberι u g s).symm⟩
    (pullbackRightPullbackFstIso g (S.fromSpecResidueField s) u).symm ?_ rfl
  show (pullbackRightPullbackFstIso g (S.fromSpecResidueField s) u).inv ≫
    pullback.fst u (pullback.fst g (S.fromSpecResidueField s)) =
      pullback.fst (u ≫ g) (S.fromSpecResidueField s)
  exact pullbackRightPullbackFstIso_inv_fst _ _ _

/-- The comparison morphism from the fibre of `u ≫ g` to the fibre of `g` is étale when `u`
is. -/
instance etale_fiberMapComp {X Y S : Scheme.{u}} (u : X ⟶ Y) (g : Y ⟶ S) (s : S) [Etale u] :
    Etale (Scheme.Hom.fiberMapComp u g s) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (self := Etale.etale_isStableUnderBaseChange) (isPullback_fiberMapComp u g s) ‹Etale u›

/-- The comparison morphism of fibres carries the canonical point of the fibre of `u ≫ g`
through a point of the source to the canonical point of the fibre of `g`. -/
private lemma fiberMapComp_asFiber {X Y S : Scheme.{u}} (u : X ⟶ Y) (g : Y ⟶ S) (x : X) :
    Scheme.Hom.fiberMapComp u g (g (u x)) ((u ≫ g).asFiber x) = g.asFiber (u x) :=
  Scheme.Hom.fiberMapComp_asFiberAt u g x (g (u x)) rfl

/-- For an étale `u` over `g`, with both composites having geometrically irreducible fibres, the
fibres of `u ≫ g` and of `g` over a point have the same dimension. -/
theorem topologicalKrullDim_fiber_comp_eq_of_etale {X Y S : Scheme.{u}} (u : X ⟶ Y) (g : Y ⟶ S)
    [Etale u] [LocallyOfFiniteType g] [GeometricallyIrreducible g]
    [GeometricallyIrreducible (u ≫ g)] (s : S) :
    topologicalKrullDim ((u ≫ g).fiber s) = topologicalKrullDim (g.fiber s) := by
  let a := Scheme.Hom.fiberMapComp u g s
  let x : (u ≫ g).fiber s := Classical.choice inferInstance
  have : LocallyOfFiniteType (g.fiberToSpecResidueField s) := by
    show LocallyOfFiniteType (pullback.snd g (S.fromSpecResidueField s))
    infer_instance
  have : LocallyOfFiniteType ((u ≫ g).fiberToSpecResidueField s) := by
    show LocallyOfFiniteType (pullback.snd (u ≫ g) (S.fromSpecResidueField s))
    infer_instance
  rw [topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible (S.residueField s) _
      ((u ≫ g).fiberToSpecResidueField s) x,
    topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible (S.residueField s) _
      (g.fiberToSpecResidueField s) (a x)]
  exact topologicalKrullDimAt_eq_of_etale a x

/-! ### The support of a module on a fibre -/

/-- Let `u : X ⟶ Y` be étale over `g : Y ⟶ S`, let `F` on `Y` and `N` on `X` be of finite type
with the support of `N` the preimage of the support of `F`, and let `x : X`. If the support of
`F` on the fibre of `g` through `u x` has its dimension attained at `u x`, then the same holds
for `N` on the fibre of `u ≫ g` through `x`, and the two dimensions agree. -/
theorem exists_mem_supp_fiber_dimension_of_etale {X Y S : Scheme.{u}} (u : X ⟶ Y) (g : Y ⟶ S)
    [Etale u] (F : Y.Modules) (N : X.Modules) [F.IsFiniteType] [N.IsFiniteType]
    (hN : SheafOfModules.supp N = u ⁻¹' SheafOfModules.supp F) (x : X)
    (hx : g.asFiber (u x) ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (g.fiberι (g (u x)))).obj F))
    (hd : topologicalKrullDimAt
        (SheafOfModules.supp ((Scheme.Modules.pullback (g.fiberι (g (u x)))).obj F))
        ⟨g.asFiber (u x), hx⟩ =
      topologicalKrullDim
        (SheafOfModules.supp ((Scheme.Modules.pullback (g.fiberι (g (u x)))).obj F))) :
    ∃ hx' : (u ≫ g).asFiber x ∈
      SheafOfModules.supp ((Scheme.Modules.pullback ((u ≫ g).fiberι ((u ≫ g) x))).obj N),
      topologicalKrullDim
          (SheafOfModules.supp ((Scheme.Modules.pullback ((u ≫ g).fiberι ((u ≫ g) x))).obj N)) =
        topologicalKrullDim
          (SheafOfModules.supp ((Scheme.Modules.pullback (g.fiberι (g (u x)))).obj F)) ∧
      topologicalKrullDimAt
          (SheafOfModules.supp ((Scheme.Modules.pullback ((u ≫ g).fiberι ((u ≫ g) x))).obj N))
          ⟨(u ≫ g).asFiber x, hx'⟩ =
        topologicalKrullDim
          (SheafOfModules.supp
            ((Scheme.Modules.pullback ((u ≫ g).fiberι ((u ≫ g) x))).obj N)) := by
  let a := Scheme.Hom.fiberMapComp u g (g (u x))
  let C := SheafOfModules.supp ((Scheme.Modules.pullback (g.fiberι (g (u x)))).obj F)
  have : ((Scheme.Modules.pullback (g.fiberι (g (u x)))).obj F).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType (g.fiberι (g (u x))).toLRSHom.toShHom F
  have hs : SheafOfModules.supp
      ((Scheme.Modules.pullback ((u ≫ g).fiberι ((u ≫ g) x))).obj N) = a ⁻¹' C := by
    dsimp only [C]
    rw [Stacks.Modules.supp_pullback, Stacks.Modules.supp_pullback, hN]
    ext p
    show u ((u ≫ g).fiberι _ p) ∈ SheafOfModules.supp F ↔
      g.fiberι _ (a p) ∈ SheafOfModules.supp F
    have hh : g.fiberι (g (u x)) (a p) = u ((u ≫ g).fiberι (g (u x)) p) :=
      congrArg (fun k => k p) (Scheme.Hom.fiberMapComp_fiberι u g (g (u x)))
    exact (congrArg (fun y => y ∈ SheafOfModules.supp F) hh.symm).to_iff
  have hp : a ((u ≫ g).asFiber x) = g.asFiber (u x) := fiberMapComp_asFiber u g x
  have hx' : (u ≫ g).asFiber x ∈ a ⁻¹' C := by
    show a _ ∈ C
    rw [hp]
    exact hx
  have hd' : topologicalKrullDimAt C ⟨a ((u ≫ g).asFiber x), hx'⟩ = topologicalKrullDim C := by
    convert hd using 1
    exact congrArg _ (Subtype.ext hp)
  rw [hs]
  exact ⟨hx', topologicalKrullDim_preimage_eq_of_etale a C (SheafOfModules.isClosed_supp _)
    ⟨(u ≫ g).asFiber x, hx'⟩ hd'⟩

end AlgebraicGeometry

end
