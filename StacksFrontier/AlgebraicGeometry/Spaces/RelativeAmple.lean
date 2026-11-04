module

public import StacksFrontier.AlgebraicGeometry.Ample.DescentStep
public import StacksFrontier.AlgebraicGeometry.AmplePullback.QuasiAffineUnitIso
public import StacksFrontier.AlgebraicGeometry.RelativelyAmple.Separated
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relatively ample invertible modules on an algebraic space

An invertible module on an algebraic space `X` is ample relative to `f : X ⟶ Y` when `f` is
representable and, for every scheme `Z` over `Y`, the pullback of the module to the scheme
`X ×_Y Z` is ample relative to `X ×_Y Z ⟶ Z` in the sense of Stacks 01VH.

## Main definitions

* `AlgebraicGeometry.Space.idEtaleChart`: a scheme over the base, read as the identity étale
  chart of the algebraic space it represents.
* `AlgebraicGeometry.Space.baseChangeModule`: the pullback of a module on `X` to a scheme
  mapping to `X`, read as a module on that scheme, with
  `AlgebraicGeometry.Space.baseChangeModuleMapIso` its functoriality in the module and
  `AlgebraicGeometry.Space.baseChangeModuleCompIso` its compatibility with composition.
* `AlgebraicGeometry.Space.IsRelativelyAmple`: **Stacks 0D31**, relative ampleness for a
  morphism of algebraic spaces.
* `AlgebraicGeometry.Space.baseChangeUnitModuleIso`: the base change of the structure sheaf of
  `X` is the structure sheaf of the base-change scheme.

## Main results

* `AlgebraicGeometry.Space.isRelativelyAmple_baseChange`: **Stacks 0D33.** Relative ampleness
  is stable under arbitrary base change of algebraic spaces.
* `AlgebraicGeometry.Space.isQuasiAffineHom_iff_isRelativelyAmple_unit`: **Stacks 0GUQ.** A
  morphism of algebraic spaces is quasi-affine if and only if the structure sheaf of its source
  is relatively ample.
* `AlgebraicGeometry.Space.IsRelativelyAmple.relativelyRepresentable` and
  `AlgebraicGeometry.Space.IsRelativelyAmple.isRelativelyAmple_baseChange`: the two defining
  conditions, usable without unfolding the definition.
* `AlgebraicGeometry.Space.isRelativelyAmple_congr`: relative ampleness depends only on the
  isomorphism class of the module.
* `AlgebraicGeometry.Space.IsRelativelyAmple.relativelyRepresentable`,
  `AlgebraicGeometry.Space.IsRelativelyAmple.isQuasiCompact` and
  `AlgebraicGeometry.Space.IsRelativelyAmple.isSeparated`: **Stacks 0D34**, the
  representability, quasi-compactness and separatedness of a morphism carrying a relatively
  ample module.

## Implementation notes

**Base changes are quantified as cartesian squares.** A morphism `Z ⟶ Y` from a scheme need
not come with a chosen fibre product `X ×_Y Z`, and when `f` is representable that fibre
product is a scheme only up to isomorphism. The condition is therefore stated for every
cartesian square whose two left-hand corners are representable: for schemes `T` and `U` over
the base, a morphism `yoneda.obj T ⟶ Y`, and a cartesian square identifying `yoneda.obj U`
with the fibre product, the pullback of the module to `U` is ample relative to `U ⟶ T`.
Representability of `f` guarantees that such a square exists over every `Z ⟶ Y`, and any two
of them are isomorphic, so this is the source's condition.

**The module on the base change.** The pullback of a module on `X` along a morphism of
algebraic spaces is `AlgebraicGeometry.Space.modulePullback` of Stacks 03LU, which produces a
module on the small étale site of the source. Since the source here is the algebraic space
represented by a scheme `U`, the module is then read on the Zariski site of `U` by
`AlgebraicGeometry.Space.restrictToChartScheme` at the identity étale chart of `yoneda.obj U`,
which is what makes the scheme-level relative ampleness of Stacks 01VH apply to it.

**Invertibility of the base change is asserted, not assumed.** Relative ampleness of a module
on a scheme is only defined for an invertible module, so the condition on a base change has to
produce that invertibility. It is stated existentially rather than taken as a hypothesis on the
module upstairs: invertibility is a `Prop`, so by proof irrelevance `∃ h, P h` is `P h₀` for any
proof `h₀`, and the clause is exactly the source's "the pullback is ample". The definition
consequently does not assume `L` invertible — on an invertible `L` it is Stacks 0D31 verbatim,
and on a general `L` it is the same condition, which forces each base change to be invertible.

## References

* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
* [Stacks Project, Tag 0D33](https://stacks.math.columbia.edu/tag/0D33)
* [Stacks Project, Tag 0D34](https://stacks.math.columbia.edu/tag/0D34)
* [Stacks Project, Tag 0GUQ](https://stacks.math.columbia.edu/tag/0GUQ)
* [Stacks Project, Tag 03HD](https://stacks.math.columbia.edu/tag/03HD)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
* [Stacks Project, Tag 03WL](https://stacks.math.columbia.edu/tag/03WL)
* [Stacks Project, Tag 0891](https://stacks.math.columbia.edu/tag/0891)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A scheme as the identity chart of the algebraic space it represents -/

/-- The identity morphism of the algebraic space represented by a scheme `U` over the base,
read as an étale chart of that algebraic space: the identity of a representable presheaf is a
representable étale morphism. -/
def idEtaleChart (U : BigFppfOver B S hS) : SmallEtale B S hS (yoneda.obj U) :=
  ⟨CostructuredArrow.mk (𝟙 (yoneda.obj U)), by
    apply presheaf_id_of_iso B S hS
    intro V W f hf
    have : IsIso f := hf
    change Etale ((BigFppfOver.toScheme B S hS).map f)
    infer_instance⟩

/-- The scheme underlying `AlgebraicGeometry.Space.idEtaleChart` is the scheme one started
with. -/
theorem chartScheme_idEtaleChart (U : BigFppfOver B S hS) :
    chartScheme (idEtaleChart B S hS U) = (BigFppfOver.toScheme B S hS).obj U :=
  rfl

/-! ### The pullback of a module to a scheme over an algebraic space -/

/-- The pullback of a module on an algebraic space `X` along a morphism `p` from the algebraic
space represented by a scheme `U`, read as a module on `U` itself: the small étale pullback of
Stacks 03LU, restricted to the Zariski site of `U` by
`AlgebraicGeometry.Space.restrictToChartScheme`. -/
def baseChangeModule {X : AlgebraicSpaces B S hS} (L : Modules.{u, u} B S hS X.1 X.2)
    (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X.1) :
    ((BigFppfOver.toScheme B S hS).obj U).Modules :=
  restrictToChartScheme B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
    ((modulePullback B S hS (ObjectProperty.homMk p :
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj L)
    (idEtaleChart B S hS U)

/-- An isomorphism of modules on an algebraic space induces one of their pullbacks to a scheme
over it. -/
def baseChangeModuleMapIso {X : AlgebraicSpaces B S hS} {L L' : Modules.{u, u} B S hS X.1 X.2}
    (e : L ≅ L') (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X.1) :
    baseChangeModule B S hS L U p ≅ baseChangeModule B S hS L' U p :=
  (restrictToChartSchemeFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
    (idEtaleChart B S hS U)).mapIso
      ((modulePullback B S hS (ObjectProperty.homMk p :
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶
          X)).mapIso e)

/-- Pulling a module back along a composite `yoneda.obj U ⟶ X' ⟶ X` is pulling it back along
`p : X' ⟶ X` and then to `U`. -/
def baseChangeModuleCompIso {X X' : AlgebraicSpaces B S hS} (p : X' ⟶ X)
    (L : Modules.{u, u} B S hS X.1 X.2) (U : BigFppfOver B S hS)
    (pU : yoneda.obj U ⟶ X'.1) :
    baseChangeModule B S hS L U (pU ≫ p.hom) ≅
      baseChangeModule B S hS ((modulePullback B S hS p).obj L) U pU :=
  (restrictToChartSchemeFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      (idEtaleChart B S hS U)).mapIso
    (eqToIso (congrArg
        (fun k : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X =>
          (modulePullback B S hS k).obj L)
        (ObjectProperty.hom_ext _ rfl :
          (ObjectProperty.homMk pU : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
              AlgebraicSpaces B S hS) ⟶ X') ≫ p =
            ObjectProperty.homMk (pU ≫ p.hom))).symm ≪≫
      ((modulePullbackCompIso B S hS (ObjectProperty.homMk pU :
          (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X')
        p).app L).symm)

/-! ### Stacks 0D31: relative ampleness -/

/-- **Stacks 0D31.** A module `L` on an algebraic space `X` is *ample relative to*
`f : X ⟶ Y`, or *`f`-ample*, when `f` is representable and, for every scheme `T` over the base
with a morphism to `Y` and every cartesian square identifying the fibre product with a scheme
`U`, the pullback of `L` to `U` is invertible and ample relative to `U ⟶ T` in the sense of
Stacks 01VH. -/
@[stacks 0D31]
def IsRelativelyAmple {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (L : Modules.{u, u} B S hS X.1 X.2) : Prop :=
  yoneda.relativelyRepresentable f.hom ∧
    ∀ (T U : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y.1) (p : yoneda.obj U ⟶ X.1) (q : U ⟶ T),
      IsPullback p (yoneda.map q) f.hom g →
        ∃ hL : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
            (baseChangeModule B S hS L U p),
          @Stacks.RelativeAmple.IsRelativelyAmple _ _ ((BigFppfOver.toScheme B S hS).map q)
            (baseChangeModule B S hS L U p) hL

variable {B S hS}

/-- **Stacks 0D34, representability.** A relatively ample module is ample relative to a
representable morphism. -/
@[stacks 0D34 "representable"]
theorem IsRelativelyAmple.relativelyRepresentable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {L : Modules.{u, u} B S hS X.1 X.2} (h : IsRelativelyAmple B S hS f L) :
    yoneda.relativelyRepresentable f.hom := h.1

/-- The pullback of a relatively ample module to a scheme base change is invertible and
relatively ample there. -/
theorem IsRelativelyAmple.isRelativelyAmple_baseChange {X Y : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {L : Modules.{u, u} B S hS X.1 X.2} (h : IsRelativelyAmple B S hS f L)
    (T U : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y.1) (p : yoneda.obj U ⟶ X.1) (q : U ⟶ T)
    (hsq : IsPullback p (yoneda.map q) f.hom g) :
    ∃ hL : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
        (baseChangeModule B S hS L U p),
      @Stacks.RelativeAmple.IsRelativelyAmple _ _ ((BigFppfOver.toScheme B S hS).map q)
        (baseChangeModule B S hS L U p) hL := h.2 T U g p q hsq

/-- Invertibility and relative ampleness of a module on a scheme transfer along an isomorphism. -/
private theorem exists_isRelativelyAmple_of_iso {U T : Scheme.{u}} {f : U ⟶ T}
    {M N : U.Modules} (e : M ≅ N)
    (h : ∃ hM : Stacks.Ample.IsInvertibleModule U M,
      @Stacks.RelativeAmple.IsRelativelyAmple _ _ f M hM) :
    ∃ hN : Stacks.Ample.IsInvertibleModule U N,
      @Stacks.RelativeAmple.IsRelativelyAmple _ _ f N hN := by
  obtain ⟨hM, hamp⟩ := h
  have : Stacks.Ample.IsInvertibleModule U N :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e
  exact ⟨inferInstance, (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e).mp hamp⟩

/-- Relative ampleness depends only on the isomorphism class of the module. -/
theorem isRelativelyAmple_congr {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {L L' : Modules.{u, u} B S hS X.1 X.2} (e : L ≅ L') :
    IsRelativelyAmple B S hS f L ↔ IsRelativelyAmple B S hS f L' := by
  have key : ∀ {M N : Modules.{u, u} B S hS X.1 X.2}, (M ≅ N) →
      IsRelativelyAmple B S hS f M → IsRelativelyAmple B S hS f N := fun i ⟨hrep, h⟩ =>
    ⟨hrep, fun T U g p q hsq =>
      exists_isRelativelyAmple_of_iso (baseChangeModuleMapIso B S hS i U p) (h T U g p q hsq)⟩
  exact ⟨key e, key e.symm⟩

/-- **Stacks 0D34, quasi-compactness.** A morphism of algebraic spaces admitting a relatively
ample module is quasi-compact.

Relative ampleness on a scheme contains quasi-compactness of the morphism, so every scheme base
change of `f` is quasi-compact; for a representable morphism that is quasi-compactness of `f`
itself, by `AlgebraicGeometry.Space.presheaf_quasiCompact_iff_isQuasiCompact` (Stacks 03HD). -/
@[stacks 0D34 "quasi-compact"]
theorem IsRelativelyAmple.isQuasiCompact {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {L : Modules.{u, u} B S hS X.1 X.2} (h : IsRelativelyAmple B S hS f L) :
    IsQuasiCompact B S hS f.hom := by
  refine (presheaf_quasiCompact_iff_isQuasiCompact B S hS h.1).mp ⟨h.1, ?_⟩
  intro T U g p q hsq
  obtain ⟨hInv, hAmp⟩ := h.2 T U g p q hsq
  exact hAmp.1

/-- **Stacks 0D34, separatedness.** A morphism of algebraic spaces admitting a relatively ample
module is separated.

Every scheme base change of `f` carries a relatively ample invertible module, hence is a
separated morphism of schemes by Stacks 01VI
(`AlgebraicGeometry.Scheme.Modules.IsRelativelyAmple.isSeparated`); for a representable
morphism that is separatedness of `f` itself, by `AlgebraicGeometry.Space.isSeparated_iff_presheaf`
(Stacks 03KY). -/
@[stacks 0D34 "separated", ega "II 4.6.3" "more general"]
theorem IsRelativelyAmple.isSeparated {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {L : Modules.{u, u} B S hS X.1 X.2} (h : IsRelativelyAmple B S hS f L) :
    IsSeparated B S hS f.hom := by
  refine (isSeparated_iff_presheaf B S hS f.hom X.2 Y.2 h.1).mpr ⟨h.1, ?_⟩
  intro T U g p q hsq
  obtain ⟨hInv, hAmp⟩ := h.2 T U g p q hsq
  exact @AlgebraicGeometry.Scheme.Modules.IsRelativelyAmple.isSeparated _ _ _ _ hInv hAmp

/-! ### Stacks 0D33: base change -/

/-- **Stacks 0D33.** Relative ampleness is stable under arbitrary base change of algebraic
spaces: if `L` is `f`-ample and `f' : X' ⟶ Y'` is the base change of `f : X ⟶ Y` along
`Y' ⟶ Y`, then the pullback of `L` to `X'` is `f'`-ample. -/
@[stacks 0D33]
theorem isRelativelyAmple_baseChange {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {g : Y' ⟶ Y} {p : X' ⟶ X} {f' : X' ⟶ Y'} (hsq : IsPullback p f' f g)
    (L : Modules.{u, u} B S hS X.1 X.2) (hL : IsRelativelyAmple B S hS f L) :
    IsRelativelyAmple B S hS f' ((modulePullback B S hS p).obj L) := by
  have hsq' : IsPullback p.hom f'.hom f.hom g.hom := AlgebraicSpaces.isPullback_hom B S hS hsq
  refine ⟨(Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
    hsq' hL.1, fun T U gT pU q htest => ?_⟩
  exact exists_isRelativelyAmple_of_iso (baseChangeModuleCompIso B S hS p L U pU)
    (hL.2 T U (gT ≫ g.hom) (pU ≫ p.hom) q (htest.paste_horiz hsq'))

/-! ### Stacks 0GUQ: quasi-affine morphisms -/

/-- **The base change of the structure sheaf of an algebraic space is the structure sheaf of the
base-change scheme.**  For a scheme `U` over the base and a morphism `p` to `X` from the
algebraic space that `U` represents, the `𝒪_X`-module `𝒪_X` read on `U` by
`AlgebraicGeometry.Space.baseChangeModule` is `𝒪_U`.

This is `AlgebraicGeometry.Space.modulePullbackUnitIso` carried through the restriction to the
identity étale chart of `yoneda.obj U`, followed by
`AlgebraicGeometry.Space.restrictToChartSchemeUnitIso` at that chart; the scheme of the chart is
`U` itself by `AlgebraicGeometry.Space.chartScheme_idEtaleChart`. -/
def baseChangeUnitModuleIso (X : AlgebraicSpaces B S hS) (U : BigFppfOver B S hS)
    (p : yoneda.obj U ⟶ X.1) :
    baseChangeModule B S hS
        (SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) U p ≅
      Stacks.Ample.unitModule ((BigFppfOver.toScheme B S hS).obj U) :=
  (restrictToChartSchemeFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
        (idEtaleChart B S hS U)).mapIso
      (modulePullbackUnitIso B S hS (ObjectProperty.homMk p :
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X)) ≪≫
    restrictToChartSchemeUnitIso B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      (idEtaleChart B S hS U)

/-- **Stacks 0GUQ.** A morphism `f : X ⟶ Y` of algebraic spaces is quasi-affine if and only if
the structure sheaf `𝒪_X` is `f`-relatively ample.

Quasi-affineness of Stacks 03WL is identified with its representable form by
`AlgebraicGeometry.Space.isQuasiAffineHom_tfae_of_isAlgebraicSpace`, and that form quantifies
over exactly the cartesian squares relative ampleness does; on each of them the equivalence is
the scheme-level Stacks 0891 in the shape
`Stacks.AmplePullback.isRelativelyAmple_iff_isQuasiAffineHom_of_iso_unitModule`, applied through
`AlgebraicGeometry.Space.baseChangeUnitModuleIso`. -/
@[stacks 0GUQ, ega "II 5.1.6" "more general"]
theorem isQuasiAffineHom_iff_isRelativelyAmple_unit {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    IsQuasiAffineHom B S hS f.hom ↔
      IsRelativelyAmple B S hS f
        (SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) := by
  refine Iff.trans ((isQuasiAffineHom_tfae_of_isAlgebraicSpace X.2 Y.2 f.hom).out 2 1) ?_
  constructor
  · rintro ⟨hrep, h⟩
    refine ⟨hrep, fun T U g p q hsq => ?_⟩
    have : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
        (baseChangeModule B S hS
          (SheafOfModules.unit
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))
          U p) :=
      Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _
        (baseChangeUnitModuleIso X U p).symm
    exact ⟨inferInstance,
      (Stacks.AmplePullback.isRelativelyAmple_iff_isQuasiAffineHom_of_iso_unitModule
        _ _ (baseChangeUnitModuleIso X U p)).mpr (h g p q hsq)⟩
  · rintro ⟨hrep, h⟩
    refine ⟨hrep, fun T U g p q hsq => ?_⟩
    obtain ⟨hL, hamp⟩ := h T U g p q hsq
    have := hL
    exact (Stacks.AmplePullback.isRelativelyAmple_iff_isQuasiAffineHom_of_iso_unitModule
      _ _ (baseChangeUnitModuleIso X U p)).mp hamp

end AlgebraicGeometry.Space

end
