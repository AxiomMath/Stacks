module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.Main
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupportDetection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DenseSubsiteSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperGeometricFibreStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperCohomologicalDimension.GeometricFibres
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalkFrameworkBridge
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images of a sheaf supported on a quasi-finite image

Let `h : Y ⟶ Z` be a proper morphism of schemes, `f : X ⟶ Y` a morphism with `f ≫ h` locally
quasi-finite, and `G` a torsion abelian sheaf on `Y_étale` whose geometric stalks vanish away
from the image of `f`. Then `R^q h_* G = 0` for every `q > 0`.

This is the vanishing at the heart of the proofs of [Stacks, Tag 0F7G] and [Stacks, Tag 0F7B],
where `G = f_! F` is a direct image with compact support: its stalks are sums of stalks of `F`
over the geometric fibres of `f` ([Stacks, Tag 0F5F]), so they vanish away from `f(X)`. The proof
is the source's. By proper base change ([Stacks, Tag 0DDF]) the stalk of `R^q h_* G` at a geometric
point `z̄` is `H^q(Y_z̄, G|_{Y_z̄})`. The restriction `G|_{Y_z̄}` is supported on the image of
`X ×_Y Y_z̄ = X ×_Z z̄`, which is locally quasi-finite over the separably closed field of `z̄`;
every point of that image is closed in `Y_z̄`, so [Stacks, Tag 0F1F] kills
`H^q(Y_z̄, G|_{Y_z̄})`.

## Main results

* `AlgebraicGeometry.isClosed_singleton_apply_of_locallyQuasiFinite`: for `a : T ⟶ W` and a
  separated `b : W ⟶ Spec Ω` over a field with `a ≫ b` locally quasi-finite, every point of the
  image of `a` is closed.
* `Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_of_support_range`: the
  vanishing of `R^q h_* G` for `q > 0`.

## References

* [Stacks Project, Tag 0F7G](https://stacks.math.columbia.edu/tag/0F7G)
* [Stacks Project, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
* [Stacks Project, Tag 0DDF](https://stacks.math.columbia.edu/tag/0DDF)
* [Stacks Project, Tag 0F1F](https://stacks.math.columbia.edu/tag/0F1F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/-! ### Closed points in the image of a quasi-finite scheme over a field -/

namespace AlgebraicGeometry

/-- **Points in the image of a locally quasi-finite scheme over a field are closed.** Let
`b : W ⟶ Spec Ω` be separated, over a field `Ω`, and let `a : T ⟶ W` be such that `a ≫ b` is
locally quasi-finite. Then `a(t)` is a closed point of `W` for every `t : T`: the fibre of `a ≫ b`
is all of `T`, which is therefore discrete, so `{t}` is an open subscheme finite over `Spec Ω`;
it is then proper over `Spec Ω`, hence proper over the separated `W`, and its image `{a(t)}` is
closed. -/
public theorem isClosed_singleton_apply_of_locallyQuasiFinite {Ω : Type u} [Field Ω]
    {T W : Scheme.{u}} (a : T ⟶ W) (b : W ⟶ Spec (.of Ω)) [IsSeparated b]
    [LocallyQuasiFinite (a ≫ b)] (t : T) : IsClosed ({a t} : Set W) := by
  have hpre : (a ≫ b) ⁻¹' {(a ≫ b) t} = Set.univ :=
    Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _
  have hdisc := (a ≫ b).isDiscrete_preimage_singleton ((a ≫ b) t)
  rw [hpre, isDiscrete_univ_iff] at hdisc
  let U : T.Opens := ⟨{t}, isOpen_discrete _⟩
  have : Finite U := show Finite ({t} : Set T) from (Set.finite_singleton t).to_subtype
  have : IsArtinianRing (CommRingCat.of Ω) := inferInstanceAs (IsArtinianRing Ω)
  have : IsLocallyArtinian (Spec (.of Ω)) := inferInstance
  have : CompactSpace U := Finite.compactSpace
  have : QuasiCompact (U.ι ≫ a ≫ b) := quasiCompact_of_compactSpace _
  have : LocallyQuasiFinite (U.ι ≫ a ≫ b) := inferInstance
  have : IsFinite (U.ι ≫ a ≫ b) := IsFinite.of_locallyQuasiFinite _
  have : UniversallyClosed ((U.ι ≫ a) ≫ b) := by
    rw [Category.assoc]; infer_instance
  have : UniversallyClosed (U.ι ≫ a) := UniversallyClosed.of_comp_of_isSeparated _ b
  have hrange : Set.range (U.ι ≫ a) = {a t} := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    exact Set.image_singleton
  rw [← hrange]
  exact (U.ι ≫ a).isClosedMap.isClosed_range

end AlgebraicGeometry

/-! ### The vanishing -/

namespace Stacks.EtaleCohomology

open Stacks.Cohomology.DenseSubsiteSheaf

attribute [local instance] SmallEtale.isGrothendieckAbelian_sheaf_succ

section Bounded

variable (B : BigEtaleSite.{u}) (W : Scheme.{u}) (hW : B.Contains W)

/-- The embedding of the size-bounded small étale site in Mathlib's carries the final object
`W / W` to the final object of Mathlib's site, the identity of `W`. -/
private def isTerminal_toEtaleSite_final :
    IsTerminal ((SmallEtale.toEtaleSite B W hW).obj (SmallEtale.final B W hW)) :=
  have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  MorphismProperty.Over.mkIdTerminal _ _

private theorem hasLimitsOfShape_structuredArrow_toEtaleSite :
    ∀ T : (W.Etale)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow T (SmallEtale.toEtaleSite B W hW).op) AddCommGrpCat.{u + 1} :=
  fun _ => hasLimitsOfShape_of_essentiallySmall.{u} _ _

end Bounded

/-- **The stalks of the restriction of a sheaf to a geometric fibre vanish at the non-closed
points**, when the stalks of the sheaf vanish away from the image of `f` and `f ≫ h` is locally
quasi-finite: a geometric point of `Y_ȳ` over the image of `f` lifts to `X ×_Y Y_ȳ = X ×_Z ȳ`,
which is locally quasi-finite over the field of `ȳ`, so it lies over a closed point. -/
private theorem isZero_sheafFiber_inverseImage_of_not_isClosed {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (h : Y ⟶ Z) [IsSeparated h] [LocallyQuasiFinite (f ≫ h)] {Ω : Type u} [Field Ω]
    (y : Spec (.of Ω) ⟶ Z) (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hsupp : ∀ p : GeometricPoint Y, p.hom default ∉ Set.range f →
      IsZero ((((pointSmallEtale p.hom).ulift.{u + 1}).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj G))
    (p : GeometricPoint (pullback h y))
    (hp : ¬ IsClosed ({p.hom default} : Set ↥(pullback h y))) :
    IsZero ((((pointSmallEtale p.hom).ulift.{u + 1}).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj
        ((etaleAbelianInverseImage.{u, 0} (pullback.fst h y)).obj G)) := by
  refine IsZero.of_iso (hsupp (p.map (pullback.fst h y)) fun ⟨x, hx⟩ ↦ hp ?_)
    ((etaleAbelianInverseImageSheafFiberIso.{u, 0} (pullback.fst h y) p.hom).app G)
  change f x = (p.hom ≫ pullback.fst h y) default at hx
  rw [Scheme.Hom.comp_apply] at hx
  obtain ⟨t, -, ht⟩ := Scheme.Pullback.exists_preimage_pullback (f := f)
    (g := pullback.fst h y) x (p.hom default) hx
  have : LocallyQuasiFinite (pullback.snd f (pullback.fst h y) ≫ pullback.snd h y) := by
    rw [← pullbackRightPullbackFstIso_hom_snd]
    infer_instance
  rw [← ht]
  exact isClosed_singleton_apply_of_locallyQuasiFinite (pullback.snd f (pullback.fst h y))
    (pullback.snd h y) t

/-- **The higher direct images along a proper morphism of a torsion sheaf supported on a
quasi-finite image vanish.** Let `h : Y ⟶ Z` be proper and `f : X ⟶ Y` a morphism with `f ≫ h`
locally quasi-finite, and let `G` be a torsion abelian sheaf on `Y_étale` whose stalks vanish at
every geometric point (with algebraically closed field) not lying over a point of `f(X)`. Then
`R^q h_* G = 0` for `q > 0`.

By [Stacks, Tag 0DDF] the stalk of `R^q h_* G` at a geometric point `ȳ` of `Z` is
`H^q(Y_ȳ, G|_{Y_ȳ})`. The sheaf `G|_{Y_ȳ}` is supported at closed points of the geometric fibre
(`isZero_sheafFiber_inverseImage_of_not_isClosed`), which is of finite type over the separably
closed field of `ȳ`, so its higher cohomology vanishes by [Stacks, Tag 0F1F], read on the
size-bounded small étale site of a big étale site containing `Y_ȳ` and carried back to Mathlib's
small étale site. This is the vanishing used in the proofs of [Stacks, Tag 0F7G] and
[Stacks, Tag 0F7B]. -/
@[sga "4 XIV 1.11" "R^q f_*C = 0 for q > 0"]
public theorem isZero_rightDerived_etaleAbelianDirectImage_of_support_range
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z) [IsProper h] [LocallyQuasiFinite (f ≫ h)]
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology G)
    (hsupp : ∀ p : GeometricPoint Y, p.hom default ∉ Set.range f →
      IsZero ((((pointSmallEtale p.hom).ulift.{u + 1}).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj G))
    (q : ℕ) (hq : 0 < q) :
    IsZero (((etaleAbelianDirectImage.{u, 0} h).rightDerived q).obj G) := by
  refine isZero_of_forall_isZero_sheafFiber_residueGeometricPoint.{u, 0} _ fun z ↦ ?_
  let y := residueGeometricPoint Z z
  let W := pullback h y
  let := hasExt_sheaf_smallEtale_succ W
  let P := (etaleAbelianInverseImage.{u, 0} (pullback.fst h y)).obj G
  let B := BigEtaleSite.containing W
  have hW : B.Contains W := BigEtaleSite.contains_containing W
  let ρ := (SmallEtale.toEtaleSite B W hW).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B W hW) W.smallEtaleTopology
  have hclosed : supportSheaf B W hW (ρ.obj P) ⊆ {w : W | IsClosed ({w} : Set W)} := by
    refine supportSheaf_subset_closedPoints_of_forall_isZero_etaleStalk B W hW (ρ.obj P)
      fun p hp ↦ ?_
    refine IsZero.of_iso ?_ (smallEtaleStalkAb_sheafEquiv_obj_iso B
      (BigEtaleSite.obj B W hW) p (ρ.obj P)).symm
    refine IsZero.of_iso ?_ ((smallEtaleStalkAb p.hom).mapIso
      ((SmallEtale.sheafEquiv B W hW AddCommGrpCat.{u + 1}).counitIso.app P))
    refine IsZero.of_iso ?_
      ((GrothendieckTopology.Point.uliftPresheafFiberIso.{u + 1}
        (pointSmallEtale p.hom)).app P.obj).symm
    exact isZero_sheafFiber_inverseImage_of_not_isClosed f h y G hsupp p hp
  have hsub : Subsingleton (Sheaf.H.{u + 1} P q) := by
    have := hasLimitsOfShape_structuredArrow_toEtaleSite B W hW
    refine subsingleton_H_of_subsingleton_H_restriction_of_isDenseSubsite
      (SmallEtale.topology B W hW) W.smallEtaleTopology (SmallEtale.toEtaleSite B W hW)
      (SmallEtale.finalIsTerminal B W hW) (isTerminal_toEtaleSite_final B W hW) P q ?_
    exact (subsingleton_sheafH_and_epi_counit_of_supportSheaf_subset_closedPoints B
      (SeparableClosure (Z.residueField z)) (BigEtaleSite.obj B W hW) (pullback.snd h y)
      (ρ.obj P) hclosed).1 q hq
  exact (AddCommGrpCat.isZero_of_subsingleton _).of_iso
    (etaleAbelianSheafFiberRightDerivedDirectImageIsoOfIsProper h y G hG q)

end Stacks.EtaleCohomology

end
