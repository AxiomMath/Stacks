module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedPullbackOfInternalHomOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedGlobalSectionsOfToposHom
import StacksCore.Tactic.StacksAttribute

/-!
# The global derived hom along a morphism of ringed topoi

Let `f : (Sh(C'), O') ⟶ (Sh(C), O)` be a morphism of ringed topoi and let `K`, `L` be objects of
`D(O)`. Stacks 0B6E asserts a canonical map

`RHom_O(K, L) ⟶ RHom_{O'}(Lf^* K, Lf^* L)`

in `D(Γ(C, O))`, obtained by taking global sections of the map
`Lf^* RSheafHom(K, L) ⟶ RSheafHom(Lf^* K, Lf^* L)` of Stacks 08JF. The target is read in
`D(Γ(C, O))` through restriction of scalars along the ring map `Γ(C, O) ⟶ Γ(C', O')` of `f`.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.globalSectionsRestrict`: restriction of scalars along
  `Γ(C, O) ⟶ Γ(C', O')`, on derived categories.
* `AlgebraicGeometry.RingedToposHom.derivedGlobalSectionsPullbackMap`: the map
  `RΓ(C, M) ⟶ RΓ(C', Lf^* M)` in `D(Γ(C, O))`.
* `AlgebraicGeometry.RingedToposHom.globalDerivedHomPullbackMap`: **Stacks 0B6E**, the canonical
  map `RHom_O(K, L) ⟶ RHom_{O'}(Lf^* K, Lf^* L)` in `D(Γ(C, O))`.

## Implementation notes

The global sections of a map `M ⟶ Rf_* N` of `D(O)` are read through the identification
`RΓ(C, Rf_* N) = RΓ(C', N)` of Stacks 0D6H on the unbounded derived category, with its scalars
kept, which is `Stacks.Cohomology.LerayOfToposHom.derivedGlobalSectionsPushforwardIso`. The
composite `RΓ(C, M) ⟶ RΓ(C, Rf_* Lf^* M) = RΓ(C', Lf^* M)` along the unit of `Lf^* ⊣ Rf_*` is
`Stacks.Cohomology.LerayOfToposHom.derivedGlobalSectionsSemilinearMap`, stated for derived global
sections with scalars restricted along ring maps; here those ring maps are identities, and the
two identity restrictions are removed by `ModuleCat.restrictScalarsId`.

The morphism of ringed topoi is taken in the sense of Stacks 01D3, part (2), with both ringed
topoi at `RingedTopos.{u, u, u}`, as for the map of Stacks 08JF it is built from
(`AlgebraicGeometry.RingedToposHom.derivedPullbackSheafHomMap`).

## References

* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.SiteModules

universe u

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

namespace AlgebraicGeometry.RingedToposHom

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : RingedToposHom X Y)

/-- Restriction of scalars along the ring map `Γ(C, O) ⟶ Γ(C', O')` of a morphism of ringed topoi
`f : (Sh(C'), O') ⟶ (Sh(C), O)`, on derived categories. -/
abbrev globalSectionsRestrict
    [HasDerivedCategory (ModuleCat.{u}
      (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))]
    [HasDerivedCategory (ModuleCat.{u}
      (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))] :
    DerivedCategory (ModuleCat.{u}
        (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⥤
      DerivedCategory (ModuleCat.{u}
        (GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :=
  (ModuleCat.restrictScalars
    (Stacks.Cohomology.LerayOfToposHom.toposGlobalSectionsRingHom f)).mapDerivedCategory

attribute [local instance 10000] HasDerivedCategory.standard

/-- Derived global sections with scalars restricted along the identity are derived global
sections. -/
def derivedGlobalSectionsRestrictIdIso (Z : RingedTopos.{u, u, u}) :
    Stacks.DerivedFunctor.totalRightDerived
        (globalSectionsFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O) ⋙
          ModuleCat.restrictScalars (RingHom.id _)) ≅
      RingedSite.derivedGlobalSectionsModules (RingedTopos.toRingedSite Z) :=
  Stacks.DerivedFunctor.totalRightDerivedIsoOfIso _
    (Functor.isoWhiskerLeft _ (ModuleCat.restrictScalarsId _) ≪≫ Functor.rightUnitor _)

/-- **The map `RΓ(C, M) ⟶ RΓ(C', Lf^* M)` in `D(Γ(C, O))`** along a morphism of ringed topoi
`f : (Sh(C'), O') ⟶ (Sh(C), O)`, the target read through restriction of scalars along
`Γ(C, O) ⟶ Γ(C', O')`: derived global sections of the unit `M ⟶ Rf_* Lf^* M` of the derived
adjunction of Stacks 07A6, followed by `RΓ(C, Rf_* N) = RΓ(C', N)` of Stacks 0D6H. -/
def derivedGlobalSectionsPullbackMap
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (RingedSite.derivedGlobalSectionsModules (RingedTopos.toRingedSite Y)).obj M ⟶
      (globalSectionsRestrict f).obj
        ((RingedSite.derivedGlobalSectionsModules (RingedTopos.toRingedSite X)).obj
          ((derivedPullback f).obj M)) :=
  (derivedGlobalSectionsRestrictIdIso Y).inv.app M ≫
    Stacks.Cohomology.LerayOfToposHom.derivedGlobalSectionsSemilinearMap.{u, u, u, u, 0, 0, u, u}
      f (RingHom.id _) (RingHom.id _)
      (Stacks.Cohomology.LerayOfToposHom.toposGlobalSectionsRingHom f) rfl M ≫
    (globalSectionsRestrict f).map ((derivedGlobalSectionsRestrictIdIso X).hom.app _)

/-- **Stacks 0B6E: the global derived hom along a morphism of ringed topoi.** For a morphism of
ringed topoi `f : (Sh(C'), O') ⟶ (Sh(C), O)` in the sense of Stacks 01D3, part (2), and objects
`K`, `L` of `D(O)`, the canonical map

`RHom_O(K, L) ⟶ RHom_{O'}(Lf^* K, Lf^* L)`

in `D(Γ(C, O))`, the target read through restriction of scalars along `Γ(C, O) ⟶ Γ(C', O')`. It is
the global sections of the map `Lf^* RSheafHom(K, L) ⟶ RSheafHom(Lf^* K, Lf^* L)` of Stacks 08JF
(`AlgebraicGeometry.RingedToposHom.derivedPullbackSheafHomMap`): `RΓ(C, -)` of the unit
`RSheafHom(K, L) ⟶ Rf_* Lf^* RSheafHom(K, L)`, read as a map into `RΓ(C', Lf^* RSheafHom(K, L))`,
followed by `RΓ(C', -)` of the map of Stacks 08JF. -/
@[stacks 0B6E "the canonical map RHom_O(K, L) -> RHom_O'(Lf^*K, Lf^*L) in D(Γ(O)) along a
morphism of ringed topoi f, given by global sections of the map of Tag 08JF"]
def globalDerivedHomPullbackMap
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    ((RingedSite.globalDerivedHomModules (RingedTopos.toRingedSite Y)).obj (op K)).obj L ⟶
      (globalSectionsRestrict f).obj
        (((RingedSite.globalDerivedHomModules (RingedTopos.toRingedSite X)).obj
          (op ((derivedPullback f).obj K))).obj ((derivedPullback f).obj L)) :=
  derivedGlobalSectionsPullbackMap f
      (((RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite Y)).obj (op K)).obj L) ≫
    (globalSectionsRestrict f).map
      ((RingedSite.derivedGlobalSectionsModules (RingedTopos.toRingedSite X)).map
        (derivedPullbackSheafHomMap f K L))

end AlgebraicGeometry.RingedToposHom

end
