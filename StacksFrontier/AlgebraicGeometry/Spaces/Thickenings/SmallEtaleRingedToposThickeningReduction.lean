module

public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Reduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePushforwardNilpotentKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposIsoOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoAtlasReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpCompFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SmallEtaleRingedToposThickening

/-!
# A thickening of small étale ringed topoi induces an isomorphism of reductions

Let `i : Z ⟶ Z'` be a morphism of algebraic spaces over a scheme `S` whose morphism of small
étale ringed topoi `i_small` is a thickening of ringed topoi (Stacks 08M6): its direct image is an
equivalence and its structure map is surjective with locally nilpotent kernel.  This file proves
that the morphism `c : Z_red ⟶ Z'_red` of the reductions (Stacks 047X) induced by `i` is an
isomorphism of algebraic spaces.  This is the first half of the implication (2) ⇒ (1) of
Stacks 0D16.

The reductions `r : Z_red ⟶ Z` and `r' : Z'_red ⟶ Z'` are thickenings of algebraic spaces, so by
the implication (1) ⇒ (2)
(`AlgebraicGeometry.Space.isThickening_smallEtaleRingedToposHom_of_isThickeningHom`) their small
étale ringed topos morphisms are thickenings, and `c ≫ r' = r ≫ i`.

* The direct image of `c` is an equivalence: `c_* ⋙ r'_* ≅ r_* ⋙ i_*` by the composition law of
  Stacks 03G8, and `r'_*`, `r_*`, `i_*` are equivalences.
* The structure map `c♯` is surjective: the structure map of `r ≫ i = c ≫ r'` is
  `i♯` followed by `i_*(r♯)`, and is also `r'♯` followed by `r'_*(c♯)`, up to isomorphisms; the
  first is surjective, so `r'_*(c♯)` is, and the direct image along the equivalence `r'_*`
  reflects surjectivity.
* The structure map `c♯` is injective: the kernel of `i♯ ≫ i_*(r♯)` is locally nilpotent, the
  kernel of `i_*(r♯)` being the direct image of the locally nilpotent kernel of `r♯`
  (`AlgebraicGeometry.Space.kernelIsLocallyNilpotent_pushforward`); as `r'♯` is surjective the
  kernel of `r'_*(c♯)` is locally nilpotent, and `r'_*𝒪_{Z'_red}` has no non-zero nilpotent
  sections, its sections being functions on reduced schemes.  So `r'_*(c♯)` is injective, and
  then so is `c♯`.

Hence `(c_small, c♯)` is an isomorphism of ringed topoi, and `c` is an isomorphism of algebraic
spaces by `AlgebraicGeometry.Space.isIso_of_isIso_smallEtaleRingedToposHom`.

## Main definitions

* `AlgebraicGeometry.Space.spaceReduction`, `AlgebraicGeometry.Space.spaceReductionι`: the
  reduction of an algebraic space as an algebraic space, with its inclusion.
* `AlgebraicGeometry.Space.spaceReductionMap`: the morphism of reductions induced by a morphism
  of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.isThickeningHom_spaceReductionι`: the inclusion of the reduction is a
  thickening.
* `AlgebraicGeometry.Space.isIso_spaceReductionMap_of_isThickening`: if `i_small` is a thickening
  of ringed topoi, the induced morphism of reductions is an isomorphism.

## References

* [Stacks Project, Tag 0D16](https://stacks.math.columbia.edu/tag/0D16)
* [Stacks Project, Tag 047X](https://stacks.math.columbia.edu/tag/047X)
* [Stacks Project, Tag 08M6](https://stacks.math.columbia.edu/tag/08M6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The direct image of sheaves of rings along an equivalence of topoi -/

section Pushforward

variable {X Y : AlgebraicSpaces B S hS}
  (t : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))

/-- On underlying sheaves of sets, the direct image of a map of sheaves of commutative rings is
the direct image of the underlying map of sheaves of sets. -/
theorem forgetRing_map_pushforwardCommRingFunctor_map
    {R R' : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}} (φ : R ⟶ R') :
    (smallEtaleRingedTopos B S hS Y).forgetRing.map
        ((pushforwardCommRingFunctor t.toToposHom).map φ) =
      t.toToposHom.pushforward.map ((smallEtaleRingedTopos B S hS X).forgetRing.map φ) := by
  ext V y
  exact congrArg (fun m => (m.hom.app V).hom y)
    (Stacks.Sheaves.ToposPullback.forgetCommRingSheaf_map_pullbackCommRingSheafMap
      (SmallEtale.topology B S hS Y.1) t.toToposHom.pushforward φ)

/-- A map of sheaves of commutative rings on a small étale site is locally surjective exactly
when its underlying map of sheaves of sets is an epimorphism. -/
theorem isLocallySurjective_iff_epi_forgetRing_map {W : AlgebraicSpaces B S hS}
    {R R' : Sheaf (SmallEtale.topology B S hS W.1) CommRingCat.{u}} (φ : R ⟶ R') :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS W.1) φ.hom ↔
      Epi ((smallEtaleRingedTopos B S hS W).forgetRing.map φ) := by
  rw [← Sheaf.isLocallySurjective_iff_epi, Presheaf.isLocallySurjective_iff_whisker_forget]
  rfl

/-- The direct image along an equivalence of topoi preserves and reflects surjective maps of
sheaves of commutative rings. -/
private theorem isLocallySurjective_pushforward_iff [t.toToposHom.pushforward.IsEquivalence]
    {R R' : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}} (φ : R ⟶ R') :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Y.1)
        ((pushforwardCommRingFunctor t.toToposHom).map φ).hom ↔
      Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1) φ.hom := by
  rw [isLocallySurjective_iff_epi_forgetRing_map, isLocallySurjective_iff_epi_forgetRing_map,
    forgetRing_map_pushforwardCommRingFunctor_map]
  exact t.toToposHom.pushforward.epi_map_iff_epi _

/-- The direct image along an equivalence of topoi preserves surjective maps of sheaves of
commutative rings. -/
theorem isLocallySurjective_pushforward [t.toToposHom.pushforward.IsEquivalence]
    {R R' : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}} {φ : R ⟶ R'}
    (hφ : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1) φ.hom) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Y.1)
      ((pushforwardCommRingFunctor t.toToposHom).map φ).hom :=
  (isLocallySurjective_pushforward_iff t φ).2 hφ

/-- The direct image along an equivalence of topoi reflects surjective maps of sheaves of
commutative rings. -/
theorem isLocallySurjective_of_pushforward [t.toToposHom.pushforward.IsEquivalence]
    {R R' : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}} {φ : R ⟶ R'}
    (hφ : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Y.1)
      ((pushforwardCommRingFunctor t.toToposHom).map φ).hom) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1) φ.hom :=
  (isLocallySurjective_pushforward_iff t φ).1 hφ

/-- The direct image along an equivalence of topoi reflects injective maps of sheaves of
commutative rings. -/
theorem injective_of_pushforward [t.toToposHom.pushforward.IsEquivalence]
    {R R' : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}} {φ : R ⟶ R'}
    (hφ : ∀ V, Function.Injective
      (((pushforwardCommRingFunctor t.toToposHom).map φ).hom.app V)) (U) :
    Function.Injective (φ.hom.app U) := by
  have hmono : Mono ((smallEtaleRingedTopos B S hS Y).forgetRing.map
      ((pushforwardCommRingFunctor t.toToposHom).map φ)) :=
    (sheafToPresheaf _ _).mono_of_mono_map
      ((NatTrans.mono_iff_mono_app _).2 fun V => (mono_iff_injective _).2 (hφ V))
  rw [forgetRing_map_pushforwardCommRingFunctor_map] at hmono
  have := t.toToposHom.pushforward.mono_of_mono_map hmono
  have h : Mono ((sheafToPresheaf _ _).map
      ((smallEtaleRingedTopos B S hS X).forgetRing.map φ)) := inferInstance
  exact (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 h U)

end Pushforward

/-! ### The reduction of an algebraic space -/

section Reduction

/-- The reduction of an algebraic space (Stacks 047X), as an algebraic space. -/
abbrev spaceReduction (X : AlgebraicSpaces B S hS) : AlgebraicSpaces B S hS :=
  ⟨(reduction B S hS X.1 X.2).toFunctor,
    (isAlgebraicSpaceStructure_reduction B S hS X.1 X.2).isClosedSubspace.1⟩

/-- The inclusion of the reduction of an algebraic space. -/
abbrev spaceReductionι (X : AlgebraicSpaces B S hS) : spaceReduction X ⟶ X :=
  ObjectProperty.homMk (reduction B S hS X.1 X.2).ι

/-- **The inclusion of the reduction is a thickening** (Stacks 05ZK): the reduction is a closed
subspace with all the points of the space. -/
theorem isThickeningHom_spaceReductionι (X : AlgebraicSpaces B S hS) :
    IsThickeningHom B S hS (spaceReductionι X) := by
  have : Mono (spaceReductionι X).hom := inferInstanceAs (Mono (reduction B S hS X.1 X.2).ι)
  rw [isThickeningHom_iff_of_mono]
  show IsThickening B S hS X (Subfunctor.range (reduction B S hS X.1 X.2).ι)
  rw [Subfunctor.range_ι]
  exact ⟨(isAlgebraicSpaceStructure_reduction B S hS X.1 X.2).isClosedSubspace,
    surjective_pointsMap_ι_reduction B S hS X.1 X.2⟩

/-- A morphism of algebraic spaces restricts to the reductions (Stacks 03JJ: the reduction of the
source is reduced, and the reduction of the target has every point). -/
theorem exists_spaceReductionMap {Z Z' : AlgebraicSpaces B S hS} (i : Z ⟶ Z') :
    ∃ g : (spaceReduction Z).1 ⟶ (reduction B S hS Z'.1 Z'.2).toFunctor,
      g ≫ (reduction B S hS Z'.1 Z'.2).ι = (reduction B S hS Z.1 Z.2).ι ≫ i.hom :=
  (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS Z'.2 (spaceReduction Z).2
    _ (isAlgebraicSpaceStructure_reduction B S hS Z'.1 Z'.2).isClosedSubspace
    (hasEtaleLocalProperty_isReduced_reduction B S hS Z.1 Z.2) _).2
      (by simp [range_pointsMap_ι_reduction])

/-- The morphism of reductions induced by a morphism of algebraic spaces. -/
def spaceReductionMap {Z Z' : AlgebraicSpaces B S hS} (i : Z ⟶ Z') :
    spaceReduction Z ⟶ spaceReduction Z' :=
  ObjectProperty.homMk (exists_spaceReductionMap i).choose

/-- The morphism of reductions is compatible with the two inclusions. -/
theorem spaceReductionMap_comp {Z Z' : AlgebraicSpaces B S hS} (i : Z ⟶ Z') :
    spaceReductionMap i ≫ spaceReductionι Z' = spaceReductionι Z ≫ i :=
  ObjectProperty.hom_ext _ (exists_spaceReductionMap i).choose_spec

/-- The étale charts of the reduction are reduced schemes. -/
theorem isReduced_chartSch_spaceReduction (X : AlgebraicSpaces B S hS)
    (W : SmallEtale B S hS (spaceReduction X).1) : IsReduced (chartSch W) :=
  (exists_atlas_iff_forall_etale B S hS (spaceReduction X).1
    (fun T : Scheme.{u} => IsReduced T) (spaceReduction X).2).1
      (hasEtaleLocalProperty_isReduced_reduction B S hS X.1 X.2)
    W.obj.left W.obj.hom W.2

end Reduction

/-! ### The structure map of a composite -/

/-- The structure map of the morphism of small étale ringed topoi of a composite `f ≫ p` is the
structure map of `p`, followed by the direct image along `p` of the structure map of `f`, followed
by an isomorphism. -/
theorem smallEtaleRingedToposHom_fSharp_comp_eq {X' X Y : AlgebraicSpaces B S hS} (f : X' ⟶ X)
    (p : X ⟶ Y) :
    (smallEtaleRingedToposHom B S hS (f ≫ p)).fSharp =
      (smallEtaleRingedToposHom B S hS p).fSharp ≫
        (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS p).toToposHom).map
          (smallEtaleRingedToposHom B S hS f).fSharp ≫
        ((pushforwardStructureCompIso B S hS f p (smallEtaleRingedTopos B S hS X').O).hom ≫
          (smallEtaleRingedToposHom_compRingIso B S hS f p).hom.app
            (smallEtaleRingedTopos B S hS X').O) := by
  rw [← smallEtaleRingedToposHom_comp_fSharp B S hS f p,
    smallEtaleRingedToposHom_comp_fSharp_eq']
  simp only [Category.assoc]

/-! ### The morphism of reductions -/

/-- In a square `c ≫ r' = r ≫ i` whose sides `i`, `r`, `r'` induce thickenings of small étale
ringed topoi, the direct image along `c` is an equivalence of topoi. -/
theorem isEquivalence_pushforward_of_comp_eq {Z Z' Zr Zr' : AlgebraicSpaces B S hS}
    {i : Z ⟶ Z'} {c : Zr ⟶ Zr'} {r : Zr ⟶ Z} {r' : Zr' ⟶ Z'} (hc : c ≫ r' = r ≫ i)
    (hi : Deformation.ToposThickening.IsThickening.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS i))
    (hr : Deformation.ToposThickening.IsThickening.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS r))
    (hr' : Deformation.ToposThickening.IsThickening.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS r')) :
    (smallEtaleRingedToposHom B S hS c).toToposHom.pushforward.IsEquivalence := by
  have := hr.1
  have := hr'.1
  have := hi.1
  have : ((smallEtaleRingedToposHom B S hS c).toToposHom.pushforward ⋙
      (smallEtaleRingedToposHom B S hS r').toToposHom.pushforward).IsEquivalence :=
    Functor.isEquivalence_of_iso (F := (smallEtaleRingedToposHom B S hS r).toToposHom.pushforward ⋙
        (smallEtaleRingedToposHom B S hS i).toToposHom.pushforward)
      ((smallEtaleRingedToposHom_compTwoIso B S hS r i).e ≪≫ eqToIso (by rw [hc]) ≪≫
        (smallEtaleRingedToposHom_compTwoIso B S hS c r').e.symm)
  exact Functor.isEquivalence_of_comp_right _
    (smallEtaleRingedToposHom B S hS r').toToposHom.pushforward

/-- In a square `c ≫ r' = r ≫ i` whose sides `i`, `r`, `r'` induce thickenings of small étale
ringed topoi, the structure map of `c` is surjective. -/
theorem isLocallySurjective_fSharp_of_comp_eq {Z Z' Zr Zr' : AlgebraicSpaces B S hS}
    {i : Z ⟶ Z'} {c : Zr ⟶ Zr'} {r : Zr ⟶ Z} {r' : Zr' ⟶ Z'} (hc : c ≫ r' = r ≫ i)
    (hi : Deformation.ToposThickening.IsThickening.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS i))
    (hr : Deformation.ToposThickening.IsThickening.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS r))
    (hr' : Deformation.ToposThickening.IsThickening.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS r')) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Zr'.1)
      (smallEtaleRingedToposHom B S hS c).fSharp.hom := by
  have := hi.1
  have := hr'.1
  have hp := isLocallySurjective_pushforward (smallEtaleRingedToposHom B S hS i) hr.2.1
  have h2 : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Z'.1)
      (smallEtaleRingedToposHom B S hS (c ≫ r')).fSharp.hom := by
    rw [hc, smallEtaleRingedToposHom_fSharp_comp_eq r i]
    have := hi.2.1
    exact inferInstance
  have h3 := (isLocallySurjective_iff_epi_forgetRing_map _).1 h2
  have h4 : (smallEtaleRingedTopos B S hS Z').forgetRing.map
        (smallEtaleRingedToposHom B S hS r').fSharp ≫
      ((smallEtaleRingedTopos B S hS Z').forgetRing.map
        ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS r').toToposHom).map
          (smallEtaleRingedToposHom B S hS c).fSharp) ≫
      (smallEtaleRingedTopos B S hS Z').forgetRing.map
        ((pushforwardStructureCompIso B S hS c r' (smallEtaleRingedTopos B S hS Zr).O).hom ≫
          (smallEtaleRingedToposHom_compRingIso B S hS c r').hom.app
            (smallEtaleRingedTopos B S hS Zr).O)) =
      (smallEtaleRingedTopos B S hS Z').forgetRing.map
        (smallEtaleRingedToposHom B S hS (c ≫ r')).fSharp := by
    simp only [smallEtaleRingedToposHom_fSharp_comp_eq c r', Functor.map_comp]
  exact isLocallySurjective_of_pushforward (smallEtaleRingedToposHom B S hS r')
    ((isLocallySurjective_iff_epi_forgetRing_map _).2
      ((epi_comp_iff_of_isIso _ _).1 (epi_of_epi_fac h4)))

/-- In a square `c ≫ r' = r ≫ i` whose sides `i`, `r`, `r'` induce thickenings of small étale
ringed topoi, the direct image along `r'` of the structure map of `c` has locally nilpotent
kernel. -/
theorem kernelIsLocallyNilpotent_pushforward_fSharp_of_comp_eq
    {Z Z' Zr Zr' : AlgebraicSpaces B S hS} {i : Z ⟶ Z'} {c : Zr ⟶ Zr'} {r : Zr ⟶ Z}
    {r' : Zr' ⟶ Z'} (hc : c ≫ r' = r ≫ i)
    (hi : Deformation.ToposThickening.IsThickening.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS i))
    (hr : Deformation.ToposThickening.IsThickening.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS r))
    (hr' : Deformation.ToposThickening.IsThickening.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS r')) :
    KernelIsLocallyNilpotent (SmallEtale.topology B S hS Z'.1)
      ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS r').toToposHom).map
        (smallEtaleRingedToposHom B S hS c).fSharp) := by
  have hk : KernelIsLocallyNilpotent (SmallEtale.topology B S hS Z'.1)
      (smallEtaleRingedToposHom B S hS (c ≫ r')).fSharp := by
    have := hi.1
    rw [hc, smallEtaleRingedToposHom_fSharp_comp_eq r i]
    exact KernelIsLocallyNilpotent.comp hi.2.2
      ((kernelIsLocallyNilpotent_pushforward (smallEtaleRingedToposHom B S hS i) _
        hr.2.2).comp_isIso _)
  rw [smallEtaleRingedToposHom_fSharp_comp_eq c r'] at hk
  exact KernelIsLocallyNilpotent.of_comp_isIso _
    (KernelIsLocallyNilpotent.of_comp_of_isLocallySurjective hr'.2.1 hk)

/-- **A square of morphisms of algebraic spaces whose three other sides are thickenings of small
étale ringed topoi, with reduced charts on the corner, gives an isomorphism of small étale ringed
topoi.**  Given `c ≫ r' = r ≫ i` with `i_small`, `r_small` and `r'_small` thickenings of ringed
topoi and every étale chart of the source of `r'` reduced, the direct image of `c` is an
equivalence and its structure map is an isomorphism. -/
theorem isEquivalence_and_isIso_of_comp_eq {Z Z' Zr Zr' : AlgebraicSpaces B S hS}
    {i : Z ⟶ Z'} {c : Zr ⟶ Zr'} {r : Zr ⟶ Z} {r' : Zr' ⟶ Z'} (hc : c ≫ r' = r ≫ i)
    (hi : Deformation.ToposThickening.IsThickening.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS i))
    (hr : Deformation.ToposThickening.IsThickening.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS r))
    (hr' : Deformation.ToposThickening.IsThickening.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS r'))
    (hred : ∀ W : SmallEtale B S hS Zr'.1, IsReduced (chartSch W)) :
    (smallEtaleRingedToposHom B S hS c).toToposHom.pushforward.IsEquivalence ∧
      IsIso (smallEtaleRingedToposHom B S hS c).fSharp := by
  refine ⟨isEquivalence_pushforward_of_comp_eq hc hi hr hr', ?_⟩
  have hsurj := isLocallySurjective_fSharp_of_comp_eq hc hi hr hr'
  have hk3 := kernelIsLocallyNilpotent_pushforward_fSharp_of_comp_eq hc hi hr hr'
  have hredsec : ∀ (V : SmallEtale B S hS Z'.1)
      (x : ToType (((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS r').toToposHom).obj
        (smallEtaleRingedTopos B S hS Zr').O).obj.obj (op V))),
      IsNilpotent x → x = 0 := by
    intro V x hx
    refine pushforwardEval_ext (smallEtaleRingedToposHom B S hS r') fun U s => ?_
    have hR : _root_.IsReduced (ToType
        ((smallEtaleRingedTopos B S hS Zr').O.obj.obj (op U))) :=
      @IsReduced.component_reduced (chartSch U) (hred U) ⊤
    exact (hR.eq_zero _ (hx.map _)).trans (map_zero _).symm
  have hinj : ∀ V, Function.Injective
      (((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS r').toToposHom).map
        (smallEtaleRingedToposHom B S hS c).fSharp).hom.app V) := by
    rintro ⟨V⟩
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨T, hT, hTx⟩ := hk3 (op V) x hx
    have hsep := ((isSheaf_iff_isSheaf_of_type _ _).mp
      ((smallEtaleRingedTopos B S hS Z').forgetRing.obj
        ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS r').toToposHom).obj
          (smallEtaleRingedTopos B S hS Zr').O)).property).isSeparated T hT
    refine hsep.ext fun W p hp => ?_
    refine (hredsec W _ (hTx p hp)).trans ?_
    exact (map_zero ((((pushforwardCommRingFunctor
      (smallEtaleRingedToposHom B S hS r').toToposHom).obj
        (smallEtaleRingedTopos B S hS Zr').O).obj.map p.op).hom)).symm
  have hinjc : ∀ U, Function.Injective ((smallEtaleRingedToposHom B S hS c).fSharp.hom.app U) := by
    have := hr'.1
    exact injective_of_pushforward (smallEtaleRingedToposHom B S hS r') hinj
  exact (Sheaf.isLocallyBijective_iff_isIso _).1
    ⟨Presheaf.isLocallyInjective_of_injective _ _ hinjc, hsurj⟩

/-- **If `i_small` is a thickening of ringed topoi, the morphism of reductions induced by `i` is
an isomorphism of algebraic spaces.** -/
theorem isIso_spaceReductionMap_of_isThickening {Z Z' : AlgebraicSpaces B S hS} {i : Z ⟶ Z'}
    (hi : Deformation.ToposThickening.IsThickening.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS i)) :
    IsIso (spaceReductionMap i) := by
  obtain ⟨h1, h2⟩ := isEquivalence_and_isIso_of_comp_eq (spaceReductionMap_comp i) hi
    (isThickening_smallEtaleRingedToposHom_of_isThickeningHom (isThickeningHom_spaceReductionι Z))
    (isThickening_smallEtaleRingedToposHom_of_isThickeningHom
      (isThickeningHom_spaceReductionι Z'))
    (isReduced_chartSch_spaceReduction Z')
  exact isIso_of_isIso_smallEtaleRingedToposHom (spaceReductionMap i)

end AlgebraicGeometry.Space

end
