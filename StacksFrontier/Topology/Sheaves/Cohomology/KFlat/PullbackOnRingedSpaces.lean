module

public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace
public import StacksFrontier.Homology.KFlat.Pullback
public import StacksFrontier.Homology.KFlat.Iso
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Topology.Sheaves.Modules.StalkKFlat

/-!
# Pullback preserves K-flatness, from the stalk criterion

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces. Stacks 06YC says that the
degreewise pullback `f^*K` of a K-flat complex `K` of `𝒪_Y`-modules is a K-flat complex of
`𝒪_X`-modules, and the proof in the source is three steps:

* read K-flatness stalkwise on both spaces (Stacks 06YB);
* identify the stalk of the pullback with a base change of the stalk, `(f^*K)_x =
  K_{f(x)} ⊗_{𝒪_{Y,f(x)}} 𝒪_{X,x}` (Stacks 0098);
* use that extension of scalars preserves K-flatness of a complex of modules (Stacks 06Y1).

Only the third is available here. Stacks 06YB and Stacks 0098 are each the subject of separate
work, so they are carried as the explicit hypotheses `StalkCriterion` and
`PullbackStalkComplexes`, in the shape the two developments already in the tree make writable:
06YB against `Stacks.SheafOfModules.IsKFlat` and
`AlgebraicGeometry.SheafOfModules.KFlatStalkwise`, and 0098 against
`AlgebraicGeometry.SheafOfModules.stalkComplex`.

**Nothing in this file carries the `06YC` attribute**, because every statement of the pullback
assertion here carries those two hypotheses, which the tag's own statement does not have.

## Main definitions

* `Stacks.SheafOfModules.KFlatPullback.StalkCriterion`: Stacks 06YB at a ringed space, the
  hypothesis.
* `Stacks.SheafOfModules.KFlatPullback.PullbackStalkComplexes`: Stacks 0098 at the level of
  complexes, the hypothesis.

## Main results

* `Stacks.SheafOfModules.KFlatPullback.kFlat_pullback`: **Stacks 06YC**, granted the two
  hypotheses.
* `Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback`: the same conclusion at the retyped
  pullback functor
  `StacksDraft.KFlat.modulePullback`, which is the shape
  `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.PullbackKFlatInput.kFlat_pullback` consumes.
* `Stacks.SheafOfModules.KFlatPullback.kFlat_of_stalkIso`: `CochainComplex.KFlat.of_iso` at a
  stalk ring of a sheaf of commutative rings.

## Implementation notes

Everything about stalk rings is phrased over a sheaf of commutative rings on
`Opens.grothendieckTopology T` for `T : TopCat`, never over a ringed space, and is applied to
`Z.sheaf` at the use site. The reason is recorded in
`StacksFrontier.Topology.Sheaves.Modules.StalkTensor`: the instance making the `RingCat`-valued
stalk of a sheaf of commutative rings into a commutative ring is keyed on the site spelling,
and `TopCat.Sheaf` is a `def` whose universes are `max`-shaped, so the synthesis of
`CommRing (𝒪_{Z,z})` for `Z : RingedSpace` gets *stuck* on `max ?u ?v =?= u` rather than
failing. A declaration keyed on the site spelling can still be *applied* to `Z.sheaf`, because
unification unfolds the `def`; that is why `siteStalkRing`, `extendStalk`,
`kFlat_extendStalk` and `kFlat_of_stalkIso` all take the sheaf of rings as an explicit
argument.

`PullbackStalkComplexes` asks for the base-change ring map existentially rather than naming the
germ map `𝒪_{Y,f(x)} ⟶ 𝒪_{X,x}`. This is deliberate and makes the hypothesis weaker: Stacks
06Y1 preserves K-flatness along *any* ring homomorphism, so which one appears is immaterial
here, and the hypothesis is implied by Stacks 0098 without any compatibility clause having to
be stated or checked.

The pullback functor is `RingedSpaceModuleAdjunction.modulePullback f`, the spelling of the
tag's own statement. The warning in `StacksFrontier.Homology.KFlat.Pullback` that this spelling
cannot appear inside a K-flatness assertion is about
`CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)`; against
`Stacks.SheafOfModules.IsKFlat X.sheaf` it elaborates, which is why both spellings are
available below and `kFlat_modulePullback` is `kFlat_pullback` with no transport.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 06XZ](https://stacks.math.columbia.edu/tag/06XZ)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
* [Stacks Project, Tag 06Y9](https://stacks.math.columbia.edu/tag/06Y9)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

noncomputable section

namespace Stacks.SheafOfModules.KFlatPullback

section Site

variable {T : TopCat.{u}}
  (R : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})

/-- The stalk ring at a point of `T`, in the spelling
`AlgebraicGeometry.SheafOfModules.stalkComplex` takes its modules over: the `RingCat`-valued
stalk of the underlying sheaf of rings of `R`. It is a commutative ring by
`StacksDraft.StalkTensor.commRing_stalk_ringSheaf`, which is found by synthesis here and is
*not* found for the structure sheaf of a ringed space. -/
abbrev siteStalkRing (t : T) : Type u :=
  ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) (Stacks.SheafOfModules.Tensor.ringSheaf R).obj t)

variable {T' : TopCat.{u}}
  (R' : CategoryTheory.Sheaf (Opens.grothendieckTopology T') CommRingCat.{u})

/-- Degreewise extension of scalars along a homomorphism between two stalk rings, carrying a
complex of modules over the stalk of `R` at `t` to a complex of modules over the stalk of `R'`
at `t'`.

This is `CochainComplex.extendScalarsLarge` and nothing else; the point of the declaration is
that its two commutative-ring instances are resolved here, where the site spelling of the
sheaf of rings makes them available. -/
def extendStalk (t : T) (t' : T') (φ : siteStalkRing R t →+* siteStalkRing R' t') :
    CochainComplex (ModuleCat.{u} (siteStalkRing R t)) ℤ ⥤
      CochainComplex (ModuleCat.{u} (siteStalkRing R' t')) ℤ :=
  CochainComplex.extendScalarsLarge.{u, u, u} φ

/-- **Stacks 06Y1 between stalk rings.** Extension of scalars along a homomorphism of stalk
rings carries a K-flat complex to a K-flat complex. This is
`CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars` read through `extendStalk`. -/
theorem kFlat_extendStalk (t : T) (t' : T') (φ : siteStalkRing R t →+* siteStalkRing R' t')
    (K : CochainComplex (ModuleCat.{u} (siteStalkRing R t)) ℤ)
    (hK : CochainComplex.KFlat.{u, u} K) :
    CochainComplex.KFlat.{u, u} ((extendStalk R R' t t' φ).obj K) :=
  CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} φ K hK

end Site

/-- `CochainComplex.KFlat.of_iso` at a stalk ring, with the sheaf of rings passed explicitly so
that the commutative-ring instance is the one the site spelling makes available. -/
theorem kFlat_of_stalkIso {T : TopCat.{u}}
    (R : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}) (t : T)
    {K L : CochainComplex (ModuleCat.{u} (siteStalkRing R t)) ℤ} (e : K ≅ L)
    (hK : CochainComplex.KFlat.{u, u} K) : CochainComplex.KFlat.{u, u} L :=
  CochainComplex.KFlat.of_iso (R := siteStalkRing R t) e hK

/-- **Stacks 06YB at a ringed space, as a hypothesis.** A complex of `𝒪_Z`-modules is K-flat if
and only if, at every point of `Z`, the complex of modules over the stalk ring obtained by
taking stalks degreewise is K-flat in the sense of Stacks 06XZ.

The two implications are separate fields, because they are used at different ringed spaces and
are of very different difficulty. `kFlat_of_kFlatStalkwise` is used on the source of the
morphism; in the source it is the easy half, following from Stacks 01AG because tensor products
and direct sums commute with taking stalks. `kFlatStalkwise_of_kFlat` is used on the target; in
the source it is the half proved by pushing forward a skyscraper.

Both are stated at a ringed space rather than at a ringed site, which is the weakest form that
suffices: a proof of the criterion over a sheaf of commutative rings on `Opens T` yields these
by instantiation at `Z.sheaf`. -/
structure StalkCriterion : Prop where
  /-- Stalkwise K-flatness over the stalk rings implies K-flatness. -/
  kFlat_of_kFlatStalkwise : ∀ (Z : RingedSpace.{u, u})
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) ℤ),
    AlgebraicGeometry.SheafOfModules.KFlatStalkwise Z.sheaf M →
      Stacks.SheafOfModules.IsKFlat Z.sheaf M
  /-- K-flatness implies stalkwise K-flatness over the stalk rings. -/
  kFlatStalkwise_of_kFlat : ∀ (Z : RingedSpace.{u, u})
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) ℤ),
    Stacks.SheafOfModules.IsKFlat Z.sheaf M →
      AlgebraicGeometry.SheafOfModules.KFlatStalkwise Z.sheaf M

/-- **Stacks 0098 at the level of complexes, as a hypothesis.** For a morphism of ringed spaces
`f : X ⟶ Y`, a point `x` of `X` and a complex `M` of `𝒪_Y`-modules, the stalk complex of the
degreewise pullback `f^*M` at `x` is an extension of scalars of the stalk complex of `M` at
`f(x)`.

In the source the ring map is the germ map `𝒪_{Y,f(x)} ⟶ 𝒪_{X,x}` of `f`; here it is only
asked to exist. That is weaker, and enough: Stacks 06Y1 preserves K-flatness along an arbitrary
ring homomorphism, so no compatibility of the ring map with `f` is needed downstream. -/
structure PullbackStalkComplexes : Prop where
  /-- The stalk of a pullback is a base change of the stalk. -/
  exists_extendStalk_iso : ∀ {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (x : X.carrier)
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ),
    ∃ φ : siteStalkRing Y.sheaf (f.hom.base x) →+* siteStalkRing X.sheaf x,
      Nonempty (AlgebraicGeometry.SheafOfModules.stalkComplex X.sheaf x
          (((RingedSpaceModuleAdjunction.modulePullback f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) ≅
        (extendStalk Y.sheaf X.sheaf (f.hom.base x) x φ).obj
          (AlgebraicGeometry.SheafOfModules.stalkComplex Y.sheaf (f.hom.base x) M))

/-- **Stacks 06YC**, granted Stacks 06YB and the complex-level form of Stacks 0098. The
degreewise pullback of a K-flat complex of `𝒪_Y`-modules along a morphism of ringed spaces
`f : X ⟶ Y` is a K-flat complex of `𝒪_X`-modules.

The proof is the one in the source. K-flatness of `f^*K` is tested at a point `x` of `X` by the
stalk criterion; there the stalk complex of `f^*K` is an extension of scalars of the stalk
complex of `K` at `f(x)`, which is K-flat by the stalk criterion applied on `Y`; and extension
of scalars preserves K-flatness, which is Stacks 06Y1. -/
theorem kFlat_pullback (hYB : StalkCriterion.{u}) (h98 : PullbackStalkComplexes.{u})
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (hK : Stacks.SheafOfModules.IsKFlat Y.sheaf K) :
    Stacks.SheafOfModules.IsKFlat X.sheaf
      (((RingedSpaceModuleAdjunction.modulePullback f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) := by
  refine hYB.kFlat_of_kFlatStalkwise X _ fun x => ?_
  obtain ⟨φ, ⟨e⟩⟩ := h98.exists_extendStalk_iso f x K
  exact kFlat_of_stalkIso X.sheaf x e.symm
    (kFlat_extendStalk Y.sheaf X.sheaf (f.hom.base x) x φ _
      (hYB.kFlatStalkwise_of_kFlat Y K hK (f.hom.base x)))

/-- **Stacks 06YC in the shape
  `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.PullbackKFlatInput.kFlat_pullback`
    consumes**: the
pullback functor is the retyping `StacksDraft.KFlat.modulePullback` and K-flatness is
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat`. Both differ from the spellings of
  `kFlat_pullback` by a `rfl`, so this is
that theorem and no transport. -/
theorem kFlat_modulePullback (hYB : StalkCriterion.{u}) (h98 : PullbackStalkComplexes.{u})
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) (hK :
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K) :
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X (((StacksDraft.KFlat.modulePullback
      f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K) :=
  kFlat_pullback hYB h98 f K hK

end Stacks.SheafOfModules.KFlatPullback

end

end
