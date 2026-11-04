module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.RingTheory.Support.GoingDown
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# Universal openness from a flat module with full support

A morphism of schemes locally of finite presentation which carries a finite type quasi-coherent
module with full support, flat over the target, is universally open. Taking the structure sheaf
as that module, a flat morphism locally of finite presentation is universally open.

The hypotheses are stable under base change, so it is enough to see that such a morphism is
generalizing, openness then being Tag 01U1. Generalizing is local on source and target, hence a
statement about a ring map `Γ(Y, V) → Γ(X, U)` on compatible affine opens. There the module of
sections `N = Γ(F, U)` is a finite `Γ(X, U)`-module, flat over `Γ(Y, V)`, whose support is all of
`Spec Γ(X, U)`; so `Spec Γ(X, U) = Supp(N) → Spec Γ(Y, V)` is generalizing by the going-down
property of a finite flat module (Tag 080T).

## Main results

* `AlgebraicGeometry.generalizingMap_of_isFlatOver_of_supp_eq_univ`: such a morphism is
  generalizing.
* `AlgebraicGeometry.universallyOpen_of_isFlatOver_of_supp_eq_univ` is the statement of the tag.
* `AlgebraicGeometry.universallyOpen_of_flat_of_locallyOfFinitePresentation`: a flat morphism
  locally of finite presentation is universally open.

## Implementation notes

The support of the module is `AlgebraicGeometry.SheafOfModules.supp`, flatness over the target is
the stalkwise predicate `AlgebraicGeometry.IsFlatOver` of Tag 08KT, and universal openness is
Mathlib's `AlgebraicGeometry.UniversallyOpen`.

## References

* [Stacks Project, Tag 0CVT](https://stacks.math.columbia.edu/tag/0CVT)
* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
* [Stacks Project, Tag 01U4](https://stacks.math.columbia.edu/tag/01U4)
* [Stacks Project, Tag 080T](https://stacks.math.columbia.edu/tag/080T)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- If the support of a quasi-coherent module is the whole scheme, then on every affine open the
support of its module of sections is the whole spectrum. -/
private theorem support_sections_eq_univ {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    (hsupp : SheafOfModules.supp F = Set.univ) (U : X.affineOpens) :
    Module.support Γ(X, U.1) Γ(F, U.1) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro p
  set x : U.1 := U.2.isoSpec.inv p with hx
  have hxprime : U.2.primeIdealOf x = p := by
    change U.2.isoSpec.hom (U.2.isoSpec.inv p) = p
    exact congrArg (fun q : Spec Γ(X, U.1) ⟶ Spec Γ(X, U.1) => q p) U.2.isoSpec.inv_hom_id
  rw [← hxprime]
  have hxfull : (x : X) ∈ SheafOfModules.supp F := by rw [hsupp]; exact Set.mem_univ _
  simpa using (Scheme.Modules.mem_support_sections_iff_mem_supp F U (x : X) x.2).mpr hxfull

/-- **Stacks Project, Tag 0CVT**, the generalizing half. A morphism carrying a finite type
quasi-coherent module of full support which is flat over the target is generalizing.

Being generalizing is local on source and target, so the statement reduces to a ring map on
compatible affine opens; there the module of sections is finite over the source and flat over the
target, and its support is everything, so going-down for a finite flat module applies. -/
public theorem generalizingMap_of_isFlatOver_of_supp_eq_univ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hsupp : SheafOfModules.supp F = Set.univ)
    (hflat : IsFlatOver f.toLRSHom.toShHom F) : GeneralizingMap f := by
  have := HasRingHomProperty.of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget.{u}
    (topologically GeneralizingMap)
  change topologically GeneralizingMap f
  rw [HasRingHomProperty.iff_appLE (P := topologically GeneralizingMap)]
  intro U V hVU
  algebraize [(f.appLE U.1 V.1 hVU).hom]
  have hcrit := ((isFlatOver_tfae f F).out 1 2).mp hflat
  let : Module Γ(Y, U.1) Γ(F, V.1) :=
    Module.compHom Γ(F, V.1) (f.appLE U.1 V.1 hVU).hom
  have hsuppN : Module.support Γ(X, V.1) Γ(F, V.1) = Set.univ :=
    support_sections_eq_univ F hsupp V
  have : IsScalarTower Γ(Y, U.1) Γ(X, V.1) Γ(F, V.1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat Γ(Y, U.1) Γ(F, V.1) := hcrit V.1 V.2 U.1 U.2 hVU
  have : Module.Finite Γ(X, V.1) Γ(F, V.1) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F V.2
  have hgen : GeneralizingMap
      (suppMap (R := Γ(Y, U.1)) (S := Γ(X, V.1)) (N := Γ(F, V.1))) := generalizingMap_suppMap
  change GeneralizingMap fun q : PrimeSpectrum Γ(X, V.1) =>
    PrimeSpectrum.comap (f.appLE U.1 V.1 hVU).hom q
  intro q q' hqq'
  have hq : q ∈ Module.support Γ(X, V.1) Γ(F, V.1) := hsuppN.symm ▸ Set.mem_univ _
  obtain ⟨qsub, hqsub, hqmap⟩ := hgen (a := ⟨q, hq⟩) (b := q')
    (by simpa [suppMap, RingHom.algebraMap_toAlgebra] using hqq')
  exact ⟨qsub.val, (subtype_specializes_iff qsub ⟨q, hq⟩).mp hqsub, by
    simpa [suppMap, RingHom.algebraMap_toAlgebra] using hqmap⟩

/-- **Stacks Project, Tag 0CVT.** A morphism of schemes locally of finite presentation admitting
a finite type quasi-coherent module of full support which is flat over the target is universally
open. -/
@[stacks 0CVT, ega "IV 11.3.1" "f|U open", ega "IV 2.4.6"]
public theorem universallyOpen_of_isFlatOver_of_supp_eq_univ {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hsupp : SheafOfModules.supp F = Set.univ)
    (hflat : IsFlatOver f.toLRSHom.toShHom F) : UniversallyOpen f := by
  refine ⟨MorphismProperty.universally_mk' (topologically @IsOpenMap) f ?_⟩
  intro T g _
  have hpull : IsPullback (Limits.pullback.snd g f) (Limits.pullback.fst g f) f g :=
    (IsPullback.of_hasPullback g f).flip
  have hFqc : F.IsQuasicoherent := inferInstance
  have hF' : ((Scheme.Modules.pullback (Limits.pullback.snd g f)).obj F).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _
      (Limits.pullback.snd g f).toLRSHom.toShHom F hFqc
  have hF'ft : ((Scheme.Modules.pullback (Limits.pullback.snd g f)).obj F).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType (Limits.pullback.snd g f).toLRSHom.toShHom F
  have hF'supp :
      SheafOfModules.supp ((Scheme.Modules.pullback (Limits.pullback.snd g f)).obj F) =
        Set.univ := by
    rw [Stacks.Modules.supp_pullback]; simp [hsupp]
  exact isOpenMap_of_generalizingMap _
    (generalizingMap_of_isFlatOver_of_supp_eq_univ _ _ hF'supp
      (@modulePullback_isFlatOver _ _ _ _ _ _ _ _ hpull F hFqc hflat))

/-- **Stacks Project, Tag 01UA.** A flat morphism of schemes which is locally of finite
presentation is universally open. -/
@[stacks 01UA,
  ega "IV 15.2.1",
  ega "IV 2.4.6",
  sga "3 VIB 4.3",
  sga "3 XVI 2.1" "more general",
  sga "6 VIII 1.3" "more general"]
public theorem universallyOpen_of_flat_of_locallyOfFinitePresentation {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] : UniversallyOpen f :=
  UniversallyOpen.of_flat f

end AlgebraicGeometry

end
