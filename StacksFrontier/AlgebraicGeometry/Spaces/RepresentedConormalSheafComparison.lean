module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.SectionwiseKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedDefiningIdealSheafObject
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedUniversalThickeningConormal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalRepresentable
public import StacksFrontier.AlgebraicGeometry.Thickenings.ImmersionConormalIdentification
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The conormal sheaf of a morphism of representable algebraic spaces

Let `g : V ⟶ U` be a morphism of algebraic spaces over a scheme `S` whose source and target are
representable, and let `s` be a universal first-order thickening of `g` in the space-level sense
of Stacks 0607.  This file proves that the conormal sheaf `𝒞_{V/U}` of `s` is finite locally free
on the small étale site of `V` as soon as the conormal sheaf of Stacks 04F4 of the corresponding
morphism of *schemes* is finite locally free in the sense of Stacks 01C6 (2).

That implication is the comparison which clause (2) of Stacks 06CB was granted as a hypothesis;
the file `Conormal.lean` under
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/LocalCompleteIntersection/`
discharges that hypothesis with the main result below.

## Main results

* `Stacks.Thickenings.universalConormalSheafIsoThickening`: the conormal sheaf of Stacks 04F4 of a
  formally unramified morphism of schemes is the conormal sheaf of the inclusion of **any**
  universal first-order thickening of that morphism, not only of the one
  `Stacks.Thickenings.universalFirstOrderThickening` chooses.
* `Stacks.Thickenings.pushforwardSchemeConormalSheafIso`: for a closed immersion factored as an
  isomorphism followed by a second closed immersion, the direct image along that isomorphism of
  the conormal sheaf of the composite is the conormal sheaf of the second factor.
* `Stacks.Thickenings.schemeConormalSheafIsoPullbackDefiningIdealOfHom`: the conormal sheaf built
  from `Stacks.ClosedImmersion.idealSheaf` on the underlying ringed space is the Zariski pullback
  of `Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom`.
* `Stacks.Thickenings.isFiniteLocallyFree_pullback_definingIdealOfHom`: the three combined, as
  the transport of finite local freeness that the space-level statement consumes.
* `AlgebraicGeometry.Space.representingObjIso` and
  `AlgebraicGeometry.Space.representingObjIso_hom_comp_representingHom`: the source of a closed
  immersion of the site is, over its target, the object representing the closed subspace cut out
  by its Yoneda image.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_conormalSheaf_representable`: **the
  comparison**, with nothing assumed beyond the scheme-level finite local freeness.

## The four bridges

The space-level side is proved:
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_conormalModule_representable` carries finite
local freeness from the Zariski pullback, along the representing closed immersion of schemes, of
the defining ideal sheaf of that immersion onto the conormal module of Stacks 04CN of a closed
subspace of a representable algebraic space, and
`AlgebraicGeometry.Space.exists_schemeThickening_conormalSheafIso_of_isRepresentable` presents the
conormal sheaf of `s` as such a conormal module, for a closed immersion `i : V₀ ⟶ W` of the site
whose scheme image is a universal first-order thickening of the morphism of schemes.  What this
file adds is the passage from the scheme-level conormal sheaf of Stacks 04F4 to that Zariski
pullback, in four steps.

1. `Stacks.Thickenings.universalConormalSheaf` is built from the thickening
   `Stacks.Thickenings.universalFirstOrderThickening` chooses, and through
   `AlgebraicGeometry.Scheme.Hom.liftCoborder`.  `Stacks.Immersion.conormalSheafSelfIso` removes
   the factorisation.
2. The chosen thickening is identified with the one coming from the site by
   `Stacks.Thickenings.UniversalFirstOrderThickening.canonicalIso`, and
   `Stacks.ClosedImmersion.conormalSheafIsoOfSquare` carries the conormal sheaf across that
   square — whose left-hand arrow is the identity, so the pullback it introduces is removed by
   `RingedSpaceModuleAdjunction.modulePullbackId`.  Steps 1 and 2 are
   `Stacks.Thickenings.universalConormalSheafIsoThickening`, which is
   `Stacks.Thickenings.universalConormalSheafIsoFirstOrderNeighbourhood` with the first-order
   infinitesimal neighbourhood replaced by an arbitrary universal first-order thickening and the
   immersion hypothesis dropped.
3. The closed immersion of the site and the representing closed immersion of the subspace it cuts
   out differ by an isomorphism of their sources, which
   `AlgebraicGeometry.Space.representingObjIso` produces from
   `AlgebraicGeometry.Space.representingIso` and `CategoryTheory.Subfunctor.toRange`, invertible
   because the Yoneda image of a closed immersion is a monomorphism
   (`AlgebraicGeometry.Space.mono_of_isClosedImmersion`).  The conormal sheaf crosses that
   isomorphism by `Stacks.ClosedImmersion.pushforwardConormalSheafIsoOfSquare`, in the *direct
   image* form rather than the inverse-image one, so that finite local freeness travels forwards
   along `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree.pushforward_of_iso`.
4. The two presentations of the ideal sheaf — the categorical kernel
   `Stacks.ClosedImmersion.idealSheaf`, which the scheme-level conormal sheaf pulls back, and the
   sectionwise kernel `Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom`, which the
   space-level statement is stated against — are identified by
   `Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso`, and the two inverse images
   are the same functor: `AlgebraicGeometry.Scheme.Modules.pullback` of a morphism of schemes is
   `RingedSpaceModuleAdjunction.modulePullback` of the underlying morphism of ringed spaces by
   `rfl`, the corresponding records for the two categories and for the structure map being
   `Stacks.RingedSpaceModules.schemeModules_eq` and
   `Stacks.RingedSpaceModules.structureSheafHom_eq`.  That step is therefore in term mode: `rw`
   does not cross the equality, because `TopCat.Sheaf` stays folded at the transparency its
   motive check runs at.

## Implementation notes

Every bridge is stated at variable schemes with the factorisation `e ≫ j = k` as a hypothesis
and only then instantiated at the data the space-level proof produces.  This is not presentation.
Written out at the concrete datum, the objects of steps 3 and 4 are inverse images of kernels of
structure maps of morphisms of the site, and deciding one spelling against another forces `whnf`
through the whole construction; stated abstractly they are instantiated by unification, and the
factorisation is discharged by `subst` rather than by unfolding a composite.  For the same reason
the step-3 and step-4 isomorphisms are definitions rather than `have`s inside one proof, and the
transport of finite local freeness through them is a separate statement again.

**A note on the spellings of the structure sheaf.**  Nothing here writes
`CategoryTheory.Sheaf.ringSheaf`, `AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom` or any
tensor-side spelling of the structure sheaf of rings.  What it does do is *name* existing constants
— `Stacks.Thickenings.schemeConormalSheaf`, `Stacks.ClosedImmersion.idealSheaf` and
`AlgebraicGeometry.Scheme.Modules` — whose types mention `structureSheafRing`, and rely on the
`rfl` between the two spellings of the category of modules on a scheme.  This uses only the
canonical spelling, `structureSheafRing`.

## References

* [Stacks Project, Tag 06CB](https://stacks.math.columbia.edu/tag/06CB)
* [Stacks Project, Tag 04F4](https://stacks.math.columbia.edu/tag/04F4)
* [Stacks Project, Tag 04F5](https://stacks.math.columbia.edu/tag/04F5)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 0607](https://stacks.math.columbia.edu/tag/0607)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Thickenings

/-! ### The conormal sheaf at an arbitrary universal first-order thickening -/

variable {Z X : Scheme.{u}} (h : Z ⟶ X) [FormallyUnramified h]

/-- **The square of ringed spaces behind
`Stacks.Thickenings.universalConormalSheafIsoThickening`.**  The inclusion of `Z` into the chosen
universal first-order thickening, followed by the canonical isomorphism onto the ambient scheme
of another one, is the inclusion of `Z` into that other one; passing to underlying ringed spaces
preserves composition on the nose. -/
theorem toShHom_inclusion_canonicalIso (t : UniversalFirstOrderThickening h) :
    (universalFirstOrderThickening h).inclusion.toLRSHom.toShHom ≫
        (RingedSpace.ringedSpaceIso
          (UniversalFirstOrderThickening.canonicalIso
            (universalFirstOrderThickening h) t)).hom =
      (Iso.refl Z.toLocallyRingedSpace.toRingedSpace).hom ≫ t.inclusion.toLRSHom.toShHom := by
  refine Eq.trans ?_ (Category.id_comp _).symm
  exact congrArg (fun p : Z ⟶ t.ambient => p.toLRSHom.toShHom)
    (UniversalFirstOrderThickening.canonicalMap_inclusion (universalFirstOrderThickening h) t)

/-- **The conormal sheaf of Stacks 04F4 is the conormal sheaf of the inclusion of any universal
first-order thickening.**  For a formally unramified morphism `h : Z ⟶ X` of schemes and a
universal first-order thickening `t` of `h`, the conormal sheaf `𝒞_{Z/X}` — built from the
thickening `Stacks.Thickenings.universalFirstOrderThickening` chooses, and through the
factorisation `AlgebraicGeometry.Scheme.Hom.liftCoborder` — is
`Stacks.Thickenings.schemeConormalSheaf` of the inclusion of `t`.

This is `Stacks.Thickenings.universalConormalSheafIsoFirstOrderNeighbourhood` with the first-order
infinitesimal neighbourhood replaced by `t` and the hypothesis that `h` be an immersion dropped;
uniqueness of the universal first-order thickening, in the form
`Stacks.Thickenings.UniversalFirstOrderThickening.canonicalIso`, is what makes the two agree. -/
noncomputable def universalConormalSheafIsoThickening (t : UniversalFirstOrderThickening h) :
    universalConormalSheaf h ≅ schemeConormalSheaf t.inclusion :=
  (Stacks.Immersion.conormalSheafSelfIso (universalFirstOrderThickening h).inclusion).symm ≪≫
    Stacks.ClosedImmersion.conormalSheafIsoOfSquare
      (Iso.refl Z.toLocallyRingedSpace.toRingedSpace)
      (RingedSpace.ringedSpaceIso (UniversalFirstOrderThickening.canonicalIso
        (universalFirstOrderThickening h) t))
      (universalFirstOrderThickening h).inclusion.toLRSHom.toShHom
      t.inclusion.toLRSHom.toShHom
      (toShHom_inclusion_canonicalIso h t) ≪≫
    (modulePullbackId Z.toLocallyRingedSpace.toRingedSpace).app _

/-! ### The conormal sheaf across an isomorphism of the source -/

/-- **The conormal sheaf of a morphism of schemes factored through an isomorphism of its
source.**  If `k = e ≫ j` with `e : A ≅ R` an isomorphism of schemes, the direct image along `e`
of the conormal sheaf of `k` is the conormal sheaf of `j`.

The factorisation is a hypothesis so that the statement can be instantiated by unification; this
is `Stacks.ClosedImmersion.pushforwardConormalSheafIsoOfSquare` at the square with lower
horizontal arrow `j`, left vertical arrow `e` and right vertical arrow the identity. -/
noncomputable def pushforwardSchemeConormalSheafIso {A R X' : Scheme.{u}} (e : A ≅ R)
    (j : R ⟶ X') (k : A ⟶ X') (hk : e.hom ≫ j = k) :
    (modulePushforward (RingedSpace.ringedSpaceIso e).hom).obj (schemeConormalSheaf k) ≅
      schemeConormalSheaf j :=
  Stacks.ClosedImmersion.pushforwardConormalSheafIsoOfSquare
    (RingedSpace.ringedSpaceIso e) (Iso.refl X'.toLocallyRingedSpace.toRingedSpace)
    k.toLRSHom.toShHom j.toLRSHom.toShHom
    (by subst hk; exact Category.comp_id _)

/-! ### The two presentations of the ideal sheaf -/

/-- **The conormal sheaf of a morphism of schemes is the Zariski pullback of its defining ideal
sheaf.**  `Stacks.Thickenings.schemeConormalSheaf` pulls back the categorical kernel
`Stacks.ClosedImmersion.idealSheaf` along the underlying morphism of ringed spaces, while
`Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom` is the sectionwise kernel of the
same morphism of structure sheaves; the two kernels are identified by
`Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso`, and
`AlgebraicGeometry.Scheme.Modules.pullback` *is* the ringed-space inverse image, by the `rfl` of
`Stacks.RingedSpaceModules.pullback_eq`. -/
@[sga "7 VI 4.7"]
noncomputable def schemeConormalSheafIsoPullbackDefiningIdealOfHom {Z' U' : Scheme.{u}}
    (j : Z' ⟶ U') :
    (Scheme.Modules.pullback j).obj
        (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom j).toSheafOfModules ≅
      schemeConormalSheaf j :=
  (modulePullback j.toLRSHom.toShHom).mapIso
    (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso j)

/-! ### The transport of finite local freeness -/

/-- **The scheme-level transport the space-level comparison consumes.**  Let `h : Z ⟶ X` be a
formally unramified morphism of schemes, `t` a universal first-order thickening of `h`, and let
the inclusion of `t` factor as an isomorphism `e : Z ≅ R` followed by a morphism
`j : R ⟶ t.ambient`.  If the conormal sheaf `𝒞_{Z/X}` of Stacks 04F4 is finite locally free in
the sense of Stacks 01C6 (2), then so is the Zariski pullback along `j` of the defining ideal
sheaf of `j`.

The three bridges of this file are composed here, and finite local freeness travels across the
isomorphism of the source by
`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree.pushforward_of_iso`, read through
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff`. -/
theorem isFiniteLocallyFree_pullback_definingIdealOfHom
    (t : UniversalFirstOrderThickening h) {R : Scheme.{u}} (e : Z ≅ R) (j : R ⟶ t.ambient)
    (hfac : e.hom ≫ j = t.inclusion)
    (hflf : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (universalConormalSheaf h)) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback j).obj
        (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom j).toSheafOfModules) := by
  have h1 : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (schemeConormalSheaf t.inclusion) :=
    SheafOfModules.IsFiniteLocallyFree.of_iso (h := hflf) (universalConormalSheafIsoThickening h t)
  have h2 : Scheme.Modules.IsFiniteLocallyFree (X := R)
      ((modulePushforward (RingedSpace.ringedSpaceIso e).hom).obj
        (schemeConormalSheaf t.inclusion)) :=
    Scheme.Modules.IsFiniteLocallyFree.pushforward_of_iso e
      ((Scheme.Modules.isFiniteLocallyFree_iff (X := Z) (schemeConormalSheaf t.inclusion)).2 h1)
  have h3 : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (schemeConormalSheaf j) :=
    SheafOfModules.IsFiniteLocallyFree.of_iso
      (h := (Scheme.Modules.isFiniteLocallyFree_iff (X := R)
        ((modulePushforward (RingedSpace.ringedSpaceIso e).hom).obj
          (schemeConormalSheaf t.inclusion))).1 h2)
      (pushforwardSchemeConormalSheafIso e j t.inclusion hfac)
  exact SheafOfModules.IsFiniteLocallyFree.of_iso (h := h3)
    (schemeConormalSheafIsoPullbackDefiningIdealOfHom j).symm

end Stacks.Thickenings

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The representing object of the subspace cut out by a closed immersion of the site -/

/-- **The Yoneda image of the representing morphism of a closed subspace of a representable
algebraic space.**  It is `AlgebraicGeometry.Space.representingIso` followed by the inclusion of
the subspace: the commutativity of the representability square of that inclusion at the identity
chart.

This is the underlying morphism of presheaves of
`AlgebraicGeometry.Space.representedSpaceMap_representingHom`, in the form in which full
faithfulness of `CategoryTheory.yoneda` can be used on it. -/
theorem yoneda_map_representingHom (T : BigFppfOver B S hS)
    (Z : ClosedSubspaces B S hS (yoneda.obj T)) :
    yoneda.map (representingHom B S hS T Z) = (representingIso B S hS T Z).hom ≫ Z.1.ι :=
  ((Z.2.2.rep.w (𝟙 (yoneda.obj T))).trans (Category.comp_id _)).symm

/-- **The source of a closed immersion of the site represents the closed subspace its Yoneda
image cuts out.**  For `i : V₀ ⟶ W` whose underlying morphism of schemes is a closed immersion,
`V₀` is isomorphic to `AlgebraicGeometry.Space.representingObj` of the closed subspace
`Subfunctor.range (yoneda.map i)` of `yoneda.obj W`.

On presheaves the isomorphism is `CategoryTheory.Subfunctor.toRange` of `yoneda.map i`, which
is invertible because `yoneda.map i` is a monomorphism
(`AlgebraicGeometry.Space.mono_of_isClosedImmersion`), followed by the inverse of
`AlgebraicGeometry.Space.representingIso`; it descends to the site because `CategoryTheory.yoneda`
is fully faithful.  That it is an isomorphism *over* `W` is
`AlgebraicGeometry.Space.representingObjIso_hom_comp_representingHom`. -/
noncomputable def representingObjIso {V₀ W : BigFppfOver B S hS} (i : V₀ ⟶ W)
    (hci : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i))
    (hcs : IsClosedSubspace B S hS (Subfunctor.range (yoneda.map i))) :
    V₀ ≅ representingObj B S hS W ⟨Subfunctor.range (yoneda.map i), hcs⟩ :=
  haveI : Mono (yoneda.map i) := mono_of_isClosedImmersion B S hS (yoneda.map i)
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) i).2 hci)
  yoneda.preimageIso (asIso (Subfunctor.toRange (yoneda.map i)) ≪≫
    (representingIso B S hS W ⟨Subfunctor.range (yoneda.map i), hcs⟩).symm)

/-- The Yoneda image of a closed immersion of the site is a monomorphism. -/
private theorem mono_yoneda_map_of_isClosedImmersion {V₀ W : BigFppfOver B S hS} (i : V₀ ⟶ W)
    (hci : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i)) :
    Mono (yoneda.map i) :=
  mono_of_isClosedImmersion B S hS (yoneda.map i)
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) i).2 hci)

/-- **`AlgebraicGeometry.Space.representingObjIso` is an isomorphism over the target**: composed
with the representing morphism of the subspace it is the closed immersion itself.  So the two
closed immersions into `W` — the given one and the representing one — differ by an isomorphism of
their sources, which is what carries the conormal sheaf from one to the other. -/
theorem representingObjIso_hom_comp_representingHom {V₀ W : BigFppfOver B S hS} (i : V₀ ⟶ W)
    (hci : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i))
    (hcs : IsClosedSubspace B S hS (Subfunctor.range (yoneda.map i))) :
    (representingObjIso B S hS i hci hcs).hom ≫
        representingHom B S hS W ⟨Subfunctor.range (yoneda.map i), hcs⟩ = i := by
  have := mono_yoneda_map_of_isClosedImmersion B S hS i hci
  refine yoneda.map_injective ?_
  rw [Functor.map_comp, yoneda_map_representingHom B S hS W
    ⟨Subfunctor.range (yoneda.map i), hcs⟩]
  change yoneda.map (yoneda.preimage (asIso (Subfunctor.toRange (yoneda.map i)) ≪≫
      (representingIso B S hS W ⟨Subfunctor.range (yoneda.map i), hcs⟩).symm).hom) ≫
      (representingIso B S hS W ⟨Subfunctor.range (yoneda.map i), hcs⟩).hom ≫
        (Subfunctor.range (yoneda.map i)).ι = _
  rw [Functor.map_preimage, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  exact Subfunctor.toRange_ι (yoneda.map i)

/-! ### The comparison -/

/-- **The comparison with the scheme-level conormal sheaf, with nothing assumed.**  Let
`g : V ⟶ U` be a morphism of algebraic spaces over `S` whose source and target are representable
by schemes, let `s` be a universal first-order thickening of `g` in the sense of Stacks 0607, and
suppose the conormal sheaf of Stacks 04F4 of the corresponding morphism of schemes is finite
locally free in the sense of Stacks 01C6 (2).  Then the conormal sheaf `𝒞_{V/U}` of `s` is finite
locally free on the small étale site of `V`, in the sense of clause (2) of Stacks 03DL.

Nothing about local complete intersections enters: the antecedent carries the whole mathematical
content, and this is the comparison that clause (2) of Stacks 06CB used to be granted as a
hypothesis.

`AlgebraicGeometry.Space.exists_schemeThickening_conormalSheafIso_of_isRepresentable` presents the
conormal sheaf of `s` as the conormal module of Stacks 04CN of the closed subspace cut out by a
closed immersion `i : V₀ ⟶ W` of the site whose scheme image is a scheme-level universal
first-order thickening, pulled back along an isomorphism;
`Stacks.Thickenings.isFiniteLocallyFree_pullback_definingIdealOfHom`
carries the hypothesis onto the Zariski pullback of the defining ideal sheaf of the representing
closed immersion, the factorisation it needs being
`AlgebraicGeometry.Space.representingObjIso_hom_comp_representingHom`; and
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_conormalModule_representable` carries that onto
the conormal module. -/
theorem isFiniteLocallyFreeOnSite_conormalSheaf_representable
    {V U : AlgebraicSpaces B S hS} [V.obj.IsRepresentable] [U.obj.IsRepresentable]
    {g : V ⟶ U} (s : UniversalFirstOrderThickening B S hS g)
    [_root_.AlgebraicGeometry.FormallyUnramified ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (V.obj.reprW.hom ≫ g.hom ≫ U.obj.reprW.inv)))]
    (hflf : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.Thickenings.universalConormalSheaf ((BigFppfOver.toScheme B S hS).map
        (yoneda.preimage (V.obj.reprW.hom ≫ g.hom ≫ U.obj.reprW.inv))))) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (conormalSheaf B S hS s) := by
  obtain ⟨W, i, p, hcs, -, huS, ⟨eiso⟩⟩ :=
    exists_schemeThickening_conormalSheafIso_of_isRepresentable B S hS s
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) :=
    huS.isFirstOrderThickening.1
  have := mono_yoneda_map_of_isClosedImmersion B S hS i hci
  have hrep := Stacks.Thickenings.isFiniteLocallyFree_pullback_definingIdealOfHom
      ((BigFppfOver.toScheme B S hS).map
        (yoneda.preimage (V.obj.reprW.hom ≫ g.hom ≫ U.obj.reprW.inv)))
      { ambient := (BigFppfOver.toScheme B S hS).obj W
        inclusion := (BigFppfOver.toScheme B S hS).map i
        toBase := (BigFppfOver.toScheme B S hS).map p
        isUniversal := huS }
      ((BigFppfOver.toScheme B S hS).mapIso (representingObjIso B S hS i hci hcs))
      ((BigFppfOver.toScheme B S hS).map
        (representingHom B S hS W ⟨Subfunctor.range (yoneda.map i), hcs⟩))
      (((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
        (congrArg (BigFppfOver.toScheme B S hS).map
          (representingObjIso_hom_comp_representingHom B S hS i hci hcs)))
      hflf
  have hmod := isFiniteLocallyFreeOnSite_conormalModule_representable B S hS W
    ⟨Subfunctor.range (yoneda.map i), hcs⟩ hrep
  refine SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso eiso.symm ?_
  exact (isFiniteLocallyFreeOnSite_modulePullback_iff B S hS
    (ObjectProperty.homMk (V.obj.reprW.inv ≫ Subfunctor.toRange (yoneda.map i)) :
      V ⟶ (⟨(Subfunctor.range (yoneda.map i)).toFunctor, hcs.1⟩ : AlgebraicSpaces B S hS))
    (isEtale_of_isIso B S hS (V.obj.reprW.inv ≫ Subfunctor.toRange (yoneda.map i)))
    (isSurjective_of_isIso B S hS (V.obj.reprW.inv ≫ Subfunctor.toRange (yoneda.map i)))
    _).1 hmod

end AlgebraicGeometry.Space

end
