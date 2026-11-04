module

public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.PullbackFromTheStalkCriterion
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.KFlatResolvingDatum
public import StacksFrontier.Homology.KFlat.AcyclicModule
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic
import StacksCore.Tactic.StacksAttribute

/-!
# The derived pullback–pushforward adjunction on a ringed space, with no datum left over

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  `StacksDraft.Ch20.Sec28.Tag079W`
proves the adjunction `Lf^* ⊣ Rf_*` relative to a *resolving datum* for `f^*`, and
`StacksDraft.Ch20.Sec27Pullback.Tag06YJ` instantiates that datum at the K-flat complexes and
discharges its resolving half.  The remaining half was
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.PullbackInvertsQuasiIso f
  (Stacks.Cohomology.KFlatDerivedPullback.IsKFlat Y)`: degreewise `f^*` carries a
quasi-isomorphism *between K-flat complexes* to an isomorphism of `D(𝒪_X)`.  This file proves
it, and so states Tag 079W with no hypothesis beyond the morphism.

## Main results

* `CochainComplex.KFlat.acyclic_extendScalarsLarge_of_kFlat_of_acyclic`: extension of scalars
  along an arbitrary ring map carries an acyclic K-flat complex of `R`-modules to an acyclic
  complex of `S`-modules.
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.acyclic_pullback_of_kFlat_of_acyclic`:
  degreewise `f^*` carries an acyclic
  K-flat complex of `𝒪_Y`-modules to an acyclic complex of `𝒪_X`-modules.
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackInvertsQuasiIso_isKFlat`: the second
  half of the resolving datum at
  the K-flat class, which was the last input of Tags 06YJ and 079W.
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction`,
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_unit_fac` and
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_counit_fac`: **Tag 079W**,
    unconditionally.

## Implementation notes

*The model of the derived category is free.*  `derivedAdjunction` and its two compatibility
statements take `[HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]` and
`[HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))]` as binders, as
`StacksDraft.Ch20.Sec28.Tag079W` does and for the reason given there: only at the locally small
model of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` does `D(𝒪_X)` have the direct
sums that the compact-generation statements of Tags 09IS and 0A9A need, and a statement proved
for `HasDerivedCategory.standard` says nothing about that model.  With that file imported both
binders are discharged by synthesis, including for a morphism of *schemes* read through
`Scheme.Hom.toLRSHom`, so Tag 079W is available as stated for an arbitrary such morphism.  The
first two steps below are statements about acyclicity of cochain complexes and mention no
derived category at all; the `omit` lines keep them that way.

*The shape of the argument.*  The three statements above are the three steps, and only the
first two carry mathematics.  Acyclicity of `f^* C` for an acyclic K-flat `C` is tested at the
stalks (`AlgebraicGeometry.SheafOfModules.acyclic_iff_forall_stalk_acyclic`, the module form of
Tag 01AG); there the stalk of `f^* C` is an extension of scalars of the stalk of `C` along the
germ map (Tag 0098, as `Stacks.SheafOfModules.KFlatPullback.pullbackStalkComplexes`), the stalk of
  `C` is acyclic by
the same criterion and K-flat by the stalk criterion for K-flatness (Tag 06YB, as
`Stacks.SheafOfModules.KFlatPullback.stalkCriterion`), and the module-level statement closes it.
  The passage from
that to `PullbackInvertsQuasiIso` is formal: a quasi-isomorphism `s` of `K(𝒪_Y)` sits in a
distinguished triangle whose third vertex is acyclic, and K-flat by the two-out-of-three
property of Tag 06Y2 (`CochainComplex.KFlatBifunctor.kFlat_obj₃_of_distTriang`); degreewise
`f^*` is a triangulated functor on homotopy categories, so it carries that triangle to a
distinguished one whose third vertex is acyclic by the previous step, which says exactly that
`f^* s` is a quasi-isomorphism.

*Why the module-level step is the unit of the tensor product.*
`CochainComplex.KFlat.acyclic_tensorObj_extendScalars_of_kFlat_of_acyclic` makes
`Tot(G ⊗_S (S ⊗_R C))` acyclic for *every* complex `G` of `S`-modules.  Taking `G` to be
`HomologicalComplex.tensorUnit` and composing with `HomologicalComplex.leftUnitor` is what turns
that into acyclicity of `S ⊗_R C` itself.  No separate comparison between the total complex and
a degreewise tensor product is needed, because the unitor of the monoidal structure on complexes
*is* that comparison at the unit.

*The stalk step is stated at a ringed site, not at a ringed space, and this is not a choice.*
`CochainComplex.KFlat` takes its modules over a `CommRing`, so the `Ring` instance in its
`ModuleCat` is `CommRing.toRing`, whereas
`AlgebraicGeometry.SheafOfModules.stalkComplex` lands in `ModuleCat` at the `Ring` instance the
`RingCat`-valued stalk carries.  The two are definitionally equal, but writing
`CochainComplex.KFlat (stalkComplex Y.sheaf y C)` by hand asks the elaborator to solve
`CommRing.toRing ?inst =?= RingCat.instRingObjForgetRingHomCarrier` with `?inst` unknown, and
the `CommRing` it must then find — `StacksDraft.StalkTensor.commRing_stalk_ringSheaf` — is found
by synthesis only at the site spelling of the sheaf of rings, not for `Y.sheaf` read as the
structure sheaf of a ringed space.  The ringed-space spelling fails with an
application type mismatch between those two `ModuleCat` instances, and the surrounding proof
exhausts its heartbeats on it.  So `acyclic_extendStalk` below is stated in the `Site` variable
shape of `StacksDraft.Ch20.Sec26.PullbackKFlat`, exactly as its neighbour
`Stacks.SheafOfModules.KFlatPullback.kFlat_extendStalk` is, and every consumer passes its arguments
  explicitly rather
than writing their types.

*The bifunctor K-flatness instances.*  At a ringed space the site `Opens X` has its object
universe equal to its morphism universe, so the general instances present search with
`max ?u ?v =?= u`, which is *stuck* rather than failing; pinning
`J := Opens.grothendieckTopology Y.carrier` solves it.  This file does not seat them itself: they
are synthesized from the global instances of `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback`
in `StacksFrontier/Topology/Sheaves/Cohomology/KFlat/OnARingedSpace.lean`, which this file reaches
publicly through its import of `KFlat.PullbackFromTheStalkCriterion`.

## References

* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
* [Stacks Project, Tag 06Y2](https://stacks.math.columbia.edu/tag/06Y2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace MonoidalCategory
open RingedSpaceModuleAdjunction

noncomputable section

namespace CochainComplex.KFlat

/-- **Extension of scalars carries an acyclic K-flat complex to an acyclic complex.**  For a ring
map `φ : R →+* S` and a complex `C` of `R`-modules which is both K-flat and acyclic, the complex
`S ⊗_R C` of `S`-modules is acyclic.

Neither hypothesis on `C` can be dropped, and no hypothesis on `φ` is needed — in particular `S`
is not assumed flat over `R`.  This is
`CochainComplex.KFlat.acyclic_tensorObj_extendScalars_of_kFlat_of_acyclic` at the unit complex,
read through the left unitor of the monoidal structure on complexes of `S`-modules. -/
theorem acyclic_extendScalarsLarge_of_kFlat_of_acyclic.{v, uR, uS}
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] (φ : R →+* S)
    {C : CochainComplex (ModuleCat.{max v uR uS} R) ℤ}
    (hC : CochainComplex.KFlat.{uR, max v uS} C) (hCac : C.Acyclic) :
    ((CochainComplex.extendScalarsLarge.{v, uR, uS} φ).obj C).Acyclic := by
  let _ : MonoidalCategoryStruct (ModuleCat.{max v uR uS} S) :=
    ModuleCat.liftedModuleMonoidalStruct.{uS, max v uR}
  let _ : MonoidalCategory (ModuleCat.{max v uR uS} S) :=
    ModuleCat.liftedModuleMonoidal.{uS, max v uR}
  let _ : MonoidalPreadditive (ModuleCat.{max v uR uS} S) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uS, max v uR}
  have h := acyclic_tensorObj_extendScalars_of_kFlat_of_acyclic.{v, uR, uS} φ hC hCac
    (HomologicalComplex.tensorUnit (ModuleCat.{max v uR uS} S) (ComplexShape.up ℤ))
  exact fun i => HomologicalComplex.ExactAt.of_iso (h i) (HomologicalComplex.leftUnitor _)

end CochainComplex.KFlat

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u w₁ w₂

section Site

variable {T : TopCat.{u}}
  (R : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  {T' : TopCat.{u}}
  (R' : CategoryTheory.Sheaf (Opens.grothendieckTopology T') CommRingCat.{u})

/-- **Extension of scalars between stalk rings carries an acyclic K-flat complex to an acyclic
complex.**  This is `CochainComplex.KFlat.acyclic_extendScalarsLarge_of_kFlat_of_acyclic` read
through `Stacks.SheafOfModules.KFlatPullback.extendStalk`; the point of the restatement is that the
  commutative-ring
instance on the stalk is resolved here, in the site spelling where synthesis finds it. -/
theorem acyclic_extendStalk (t : T) (t' : T')
    (φ : Stacks.SheafOfModules.KFlatPullback.siteStalkRing R t →+*
      Stacks.SheafOfModules.KFlatPullback.siteStalkRing R' t')
    (K : CochainComplex (ModuleCat.{u} (Stacks.SheafOfModules.KFlatPullback.siteStalkRing R t)) ℤ)
    (hK : CochainComplex.KFlat.{u, u} K) (hKac : K.Acyclic) :
    ((Stacks.SheafOfModules.KFlatPullback.extendStalk R R' t t' φ).obj K).Acyclic :=
  CochainComplex.KFlat.acyclic_extendScalarsLarge_of_kFlat_of_acyclic.{u, u, u} φ hK hKac

end Site


variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
  [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))]

omit [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
  [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))] in
/-- **Degreewise pullback carries an acyclic K-flat complex to an acyclic complex.**  This is
where the geometry of `f` enters: `f^*` is not exact, and the conclusion is false without
K-flatness of `K`.

The proof is the one in the source.  Acyclicity of `f^* K` is tested at each point `x` of `X`;
there the stalk complex of `f^* K` is an extension of scalars of the stalk complex of `K` at
`f(x)` along the germ map, by Tag 0098; the stalk complex of `K` is acyclic because `K` is, and
K-flat because `K` is, by Tag 06YB; and extension of scalars of an acyclic K-flat complex of
modules is acyclic. -/
theorem acyclic_pullback_of_kFlat_of_acyclic
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
      Y.sheaf)) ℤ)
    (hK : Stacks.SheafOfModules.IsKFlat Y.sheaf K) (hKac : K.Acyclic) :
    (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  refine (AlgebraicGeometry.SheafOfModules.acyclic_iff_forall_stalk_acyclic
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf) _).2 fun x => ?_
  obtain ⟨φ, ⟨e⟩⟩ :=
    Stacks.SheafOfModules.KFlatPullback.pullbackStalkComplexes.{u}.exists_extendStalk_iso f x K
  exact fun i => HomologicalComplex.ExactAt.of_iso
    (acyclic_extendStalk Y.sheaf X.sheaf (f.hom.base x) x φ _
      (Stacks.SheafOfModules.KFlatPullback.stalkCriterion.kFlatStalkwise_of_kFlat Y K hK
        (f.hom.base x))
      ((AlgebraicGeometry.SheafOfModules.acyclic_iff_forall_stalk_acyclic
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.sheaf) K).1 hKac (f.hom.base x)) i)
    e.symm

omit [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))] in
/-- **The second half of the resolving datum for `f^*` at the K-flat class**: degreewise
pullback carries a quasi-isomorphism between K-flat complexes of `𝒪_Y`-modules to an
isomorphism of `D(𝒪_X)`.  Together with
  `Stacks.Cohomology.KFlatDerivedPullback.hasResolutions_isKFlat` this completes
the datum, so the derived pullback exists and Tag 079W holds unconditionally.

Everything here is formal.  Complete `s` to a distinguished triangle of `K(𝒪_Y)`: its third
vertex is acyclic because `s` is a quasi-isomorphism, and K-flat by the two-out-of-three
property of Tag 06Y2.  Degreewise `f^*` is a triangulated functor on homotopy categories, so it
carries that triangle to a distinguished triangle of `K(𝒪_X)` whose third vertex is acyclic by
`acyclic_pullback_of_kFlat_of_acyclic`; that says exactly that `f^* s` is a quasi-isomorphism,
and the localization functor inverts those. -/
theorem pullbackInvertsQuasiIso_isKFlat :
    PullbackInvertsQuasiIso f (Stacks.Cohomology.KFlatDerivedPullback.IsKFlat Y) := by
  intro K M s hs hK hM
  obtain ⟨Z, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle s
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at hs
  have hZac : Z.as.Acyclic :=
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic Z.as).1
      (((HomotopyCategory.subcategoryAcyclic
        (SheafOfModules.{u} (structureSheafRing Y))).trW_iff_of_distinguished _ hT).1 hs)
  have hZflat : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y Z.as :=
    CochainComplex.KFlatBifunctor.kFlat_obj₃_of_distTriang
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf) s g h hT hK hM
  have hFZ : HomotopyCategory.subcategoryAcyclic (SheafOfModules.{u} (structureSheafRing X))
      (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).obj Z) :=
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2
      (acyclic_pullback_of_kFlat_of_acyclic f Z.as hZflat hZac)
  have hFs : HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)
      (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map s) := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact ⟨_, _, _, ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map_distinguished
      _ hT, hFZ⟩
  exact Localization.inverts DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    _ hFs

/-- **The derived pullback `Lf^*` exists**, for every morphism of ringed spaces: the K-flat
complexes are a resolving datum for `f^*`.  This is Tag 06YJ, and it is seated as an instance so
that `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f` is available with no
  hypothesis. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy :
    (pullbackOnHomotopy f).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :=
  pullbackOnHomotopy_hasLeftDerivedFunctor f (Stacks.Cohomology.KFlatDerivedPullback.IsKFlat Y)
    (Stacks.Cohomology.KFlatDerivedPullback.hasResolutions_isKFlat Y)
    (pullbackInvertsQuasiIso_isKFlat f)

/-- **The adjunction `Lf^* ⊣ Rf_*`** on the unbounded derived categories of sheaves of modules
over ringed spaces, for an arbitrary morphism of ringed spaces. -/
@[stacks 079W "derived adjunction", sga "4 XVII 2.3.7" "ringed spaces case"]
def derivedAdjunction : derivedPullback f ⊣ derivedPushforward f :=
  derivedPullbackPushforwardAdjunction f (Stacks.Cohomology.KFlatDerivedPullback.IsKFlat Y)
    (Stacks.Cohomology.KFlatDerivedPullback.hasResolutions_isKFlat Y)
    (pullbackInvertsQuasiIso_isKFlat f)

/-- The derived unit agrees with the ordinary unit after applying the canonical comparison
maps. -/
@[stacks 079W "canonical unit"]
theorem derivedAdjunction_unit_fac
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :
    (derivedAdjunction f).unit.app (DerivedCategory.Qh.obj M) ≫
        (derivedPushforward f).map ((derivedPullbackComparison f).app M) =
      DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction f).unit.app M) ≫
        (derivedPushforwardUnit f).app
          (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) :=
  derivedPullbackPushforwardAdjunction_unit_fac f
    (Stacks.Cohomology.KFlatDerivedPullback.IsKFlat Y)
    (Stacks.Cohomology.KFlatDerivedPullback.hasResolutions_isKFlat Y)
    (pullbackInvertsQuasiIso_isKFlat f) M

/-- The derived counit agrees with the ordinary counit after applying the canonical comparison
maps. -/
@[stacks 079W "canonical counit"]
theorem derivedAdjunction_counit_fac
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedPullback f).map ((derivedPushforwardUnit f).app K) ≫
        (derivedAdjunction f).counit.app (DerivedCategory.Qh.obj K) =
      (derivedPullbackComparison f).app
          (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((homotopyPullbackPushforwardAdjunction f).counit.app K) :=
  derivedPullbackPushforwardAdjunction_counit_fac f
    (Stacks.Cohomology.KFlatDerivedPullback.IsKFlat Y)
    (Stacks.Cohomology.KFlatDerivedPullback.hasResolutions_isKFlat Y)
    (pullbackInvertsQuasiIso_isKFlat f) K

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

end

end
