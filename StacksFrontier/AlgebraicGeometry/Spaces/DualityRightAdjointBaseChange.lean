module

public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependence
public import StacksFrontier.CategoryTheory.Adjunction.RightAdjointBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# The right adjoint of pushforward on D_QCoh of algebraic spaces and its base change map

Let `S` be a scheme and consider a commutative square of algebraic spaces over `S`

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

of quasi-compact and quasi-separated algebraic spaces. Write `a : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` and
`a' : D_QCoh(𝒪_{Y'}) ⥤ D_QCoh(𝒪_{X'})` for the right adjoints of `Rf_*` and `Rf'_*`
(Stacks 0E55). The base change map `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ L(g')^*` of Stacks 07A7, restricted to
`D_QCoh`, has a mate `Rg'_* ∘ a' ⟶ a ∘ Rg_*` between the right adjoints (Stacks 0E5B).

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentDerivedRightAdjoint` and
  `AlgebraicGeometry.Space.quasicoherentDerivedRightAdjointAdjunction`: the right adjoint `a` of
  `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` for a morphism of quasi-compact quasi-separated algebraic
  spaces, with its adjunction.
* `AlgebraicGeometry.Space.quasicoherentDerivedBaseChange`: the base change map
  `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ L(g')^*` on `D_QCoh`.
* `AlgebraicGeometry.Space.quasicoherentDerivedRightAdjointBaseChange`: the transformation
  `Rg'_* ∘ a' ⟶ a ∘ Rg_*` between the right adjoints.

## Main results

* `AlgebraicGeometry.Space.isIso_quasicoherentDerivedBaseChange_app_iff`: the base change map on
  `D_QCoh` is invertible at `K` exactly when the base change map of Stacks 07A7 is.

## References

* [Stacks Project, Tag 0E5B](https://stacks.math.columbia.edu/tag/0E5B)
* [Stacks Project, Tag 0E55](https://stacks.math.columbia.edu/tag/0E55)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-! ### The right adjoint of pushforward -/

section RightAdjoint

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hXqc : IsQuasiCompactSpace B S hS X.1)
  (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
  (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)

/-- **The right adjoint `a` of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`** for a morphism of
quasi-compact and quasi-separated algebraic spaces (Stacks 0E55). -/
def quasicoherentDerivedRightAdjoint :
    QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2 ⥤
      QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 :=
  haveI := isLeftAdjoint_quasicoherentDerivedPushforward hZ f hXqc hXqs hYqs
  (quasicoherentDerivedPushforward B S hS f
    (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom)
    (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom)).rightAdjoint

/-- The adjunction `Rf_* ⊣ a`. Its counit is the trace map `Tr_f : Rf_* ∘ a ⟶ 1` and its unit
`η_f : 1 ⟶ a ∘ Rf_*` (Stacks 0E5K). -/
def quasicoherentDerivedRightAdjointAdjunction
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom) :
    quasicoherentDerivedPushforward B S hS f hfqc hfqs ⊣
      quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs :=
  haveI := isLeftAdjoint_quasicoherentDerivedPushforward hZ f hXqc hXqs hYqs
  Adjunction.ofIsLeftAdjoint _

end RightAdjoint

/-! ### The base change map on `D_QCoh` -/

section BaseChange

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)
  (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
  (hf'qc : IsQuasiCompact B S hS f'.hom) (hf'qs : IsQuasiSeparated B S hS f'.hom)

/-- **The base change map `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ L(g')^*` on `D_QCoh`** of a commutative square
of algebraic spaces with `f` and `f'` quasi-compact and quasi-separated: the base change map of
Stacks 07A7 (`AlgebraicGeometry.Space.smallEtaleDerivedModuleBaseChangeMap`) at each object. -/
def quasicoherentDerivedBaseChange :
    quasicoherentDerivedPushforward B S hS f hfqc hfqs ⋙ quasicoherentDerivedModulePullback g ⟶
      quasicoherentDerivedModulePullback g' ⋙
        quasicoherentDerivedPushforward B S hS f' hf'qc hf'qs where
  app K := ObjectProperty.homMk (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' w K.obj)
  naturality _ _ u := ObjectProperty.hom_ext _
    (smallEtaleDerivedModuleBaseChangeMap_naturality B S hS f g f' g' w u.hom)

/-- The component of the base change map on `D_QCoh` at `K` is the base change map of
Stacks 07A7 at the underlying object of `D(𝒪_X)`. -/
@[simp]
theorem quasicoherentDerivedBaseChange_app_hom
    (K : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    ((quasicoherentDerivedBaseChange f g f' g' w hfqc hfqs hf'qc hf'qs).app K).hom =
      smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' w K.obj :=
  rfl

/-- The base change map on `D_QCoh` is invertible at `K` exactly when the base change map of
Stacks 07A7 is invertible at the underlying object of `D(𝒪_X)`. -/
theorem isIso_quasicoherentDerivedBaseChange_app_iff
    (K : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    IsIso ((quasicoherentDerivedBaseChange f g f' g' w hfqc hfqs hf'qc hf'qs).app K) ↔
      IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' w K.obj) := by
  exact (isIso_iff_of_reflects_iso
    ((quasicoherentDerivedBaseChange f g f' g' w hfqc hfqs hf'qc hf'qs).app K)
    (ObjectProperty.ι _)).symm

/-- The base change map on `D_QCoh` is invertible as soon as the base change map of Stacks 07A7
is invertible at every object with quasi-coherent cohomology. -/
theorem isIso_quasicoherentDerivedBaseChange
    (h : ∀ K : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
      IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' w K.obj)) :
    IsIso (quasicoherentDerivedBaseChange f g f' g' w hfqc hfqs hf'qc hf'qs) :=
  have : ∀ K, IsIso ((quasicoherentDerivedBaseChange f g f' g' w hfqc hfqs hf'qc hf'qs).app K) :=
    fun K ↦ (isIso_quasicoherentDerivedBaseChange_app_iff f g f' g' w hfqc hfqs hf'qc hf'qs K).2
      (h K)
  NatIso.isIso_of_isIso_app _

end BaseChange

/-! ### The base change map of the right adjoints -/

section RightAdjointBaseChange

variable {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
  (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
  (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
  (hY'qc : IsQuasiCompactSpace B S hS Y'.1) (hY'qs : IsAbsolutelyQuasiSeparated B S hS hZ Y'.1)

include sq hXqc hYqs hY'qc in
/-- In a cartesian square with `X` and `Y'` quasi-compact and `Y` quasi-separated, the fibre
product `X'` is quasi-compact. -/
theorem isQuasiCompactSpace_of_isPullback : IsQuasiCompactSpace B S hS X'.1 :=
  isQuasiCompactSpace_of_isQuasiCompact B S hS Y'.2 hY'qc f'.hom
    (IsQuasiCompact.of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS sq)
      (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom))

include sq hXqs hY'qs in
/-- In a cartesian square with `X` and `Y'` quasi-separated, the fibre product `X'` is
quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_of_isPullback :
    IsAbsolutelyQuasiSeparated B S hS hZ X'.1 :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ X'.2 hY'qs
    (isQuasiSeparated_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS sq)
      (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom))

/-- For a cartesian square of algebraic spaces with `X` and `Y'` quasi-compact and
quasi-separated and `Y` quasi-separated, the transformation `Rg'_* ∘ a' ⟶ a ∘ Rg_*` between the
right adjoints `a`, `a'` of `Rf_*`, `Rf'_*` on `D_QCoh` (Stacks 0E55): the mate of the base change
map `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ L(g')^*` of Stacks 07A7. -/
@[stacks 0E5B]
def quasicoherentDerivedRightAdjointBaseChange :
    quasicoherentDerivedRightAdjoint hZ f'
          (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc)
          (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) hY'qs ⋙
        quasicoherentDerivedPushforward B S hS g'
          (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ X.2 hXqs
            (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc) g'.hom)
          (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X'.2
            (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) g'.hom) ⟶
      quasicoherentDerivedPushforward B S hS g
          (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hY'qc g.hom)
          (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ Y'.2 hY'qs g.hom) ⋙
        quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs :=
  RightAdjointBaseChange.rightAdjointMate
    (quasicoherentDerivedRightAdjointAdjunction hZ f hXqc hXqs hYqs
      (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom)
      (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom))
    (quasicoherentDerivedRightAdjointAdjunction hZ f'
      (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc)
      (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) hY'qs
      (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y'.2 hY'qs
        (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc) f'.hom)
      (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X'.2
        (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) f'.hom))
    (quasicoherentDerivedModuleAdjunction B S hS g
      (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hY'qc g.hom)
      (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ Y'.2 hY'qs g.hom))
    (quasicoherentDerivedModuleAdjunction B S hS g'
      (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ X.2 hXqs
        (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc) g'.hom)
      (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X'.2
        (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) g'.hom))
    (quasicoherentDerivedBaseChange f g f' g' sq.w
      (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom)
      (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom)
      (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y'.2 hY'qs
        (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc) f'.hom)
      (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X'.2
        (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) f'.hom))

end RightAdjointBaseChange

end AlgebraicGeometry.Space

end
