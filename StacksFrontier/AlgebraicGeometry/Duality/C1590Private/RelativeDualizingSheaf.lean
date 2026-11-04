module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexRigidity
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDuality
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackTopDegree
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreePullbackNaturality
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularAnyModel
public import StacksFrontier.Homology.DerivedCategory.Bridge.Pullback
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeCurveDegree

/-!
# The relative dualizing sheaf of a proper flat morphism

Let `f : X ⟶ S` be a proper, flat morphism of finite presentation with `S` quasi-compact and
quasi-separated. Its *relative dualizing complex* is `ω^•_{X/S} = a(𝒪_S)` (Stacks 0B6S), where
`a` is the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_S)` (Stacks 0A9E); the *relative
dualizing sheaf* is its cohomology sheaf `ω_{X/S} = H^{-1}(ω^•_{X/S})` (Stacks 0E6Q).

This file sets up the two objects and their formation along base change. The relative dualizing
complex commutes with arbitrary base change of quasi-compact quasi-separated bases (Stacks 0E6N,
through Stacks 0E6C; here `Stacks.Duality.twistedInverseImageStructureSheafBaseChangeIso`). When
`ω^•_{X/S}` has no cohomology above degree `-1`, which is the case for families of curves with
Cohen–Macaulay fibres (Stacks 0E6P), the top degree comparison `H^{-1}(L(g')^*K) = (g')^*H^{-1}(K)`
turns this into the base change isomorphism `(g')^*ω_{X/S} ≅ ω_{X'/S'}`. Over a field the two
objects are the dualizing complex and the dualizing sheaf of Stacks 0BS2, by definition; so the
pullback of `ω_{X/S}` to a fibre `X_s` is the dualizing sheaf of the proper `κ(s)`-scheme `X_s`.

## Main definitions

* `AlgebraicGeometry.C1590Private.relativeDualizingComplex`: `ω^•_{X/S} = a(𝒪_S)`.
* `AlgebraicGeometry.C1590Private.relativeDualizingSheaf`: `ω_{X/S} = H^{-1}(ω^•_{X/S})`.
* `AlgebraicGeometry.C1590Private.relativeDualizingComplexBaseChangeIso`:
  `L(g')^*ω^•_{X/S} ≅ ω^•_{X'/S'}` for a cartesian square.
* `AlgebraicGeometry.C1590Private.relativeDualizingSheafBaseChangeIsoOfIsLE`:
  `(g')^*ω_{X/S} ≅ ω_{X'/S'}` when `ω^•_{X/S}` has no cohomology above degree `-1`.
* `AlgebraicGeometry.C1590Private.relativeDualizingSheafFibreIsoOfIsLE`: the pullback of
  `ω_{X/S}` to the fibre `X_s` is `Stacks.Duality.dualizingSheafOverField` of `X_s ⟶ Spec κ(s)`.

## Main results

* `AlgebraicGeometry.C1590Private.relativeDualizingSheaf_eq_dualizingSheafOverField`: over a
  field, `ω_{X/k}` is the dualizing sheaf of Stacks 0BS2.

## References

* [Stacks Project, Tag 0E6N](https://stacks.math.columbia.edu/tag/0E6N)
* [Stacks Project, Tag 0E6Q](https://stacks.math.columbia.edu/tag/0E6Q)
* [Stacks Project, Tag 0B6S](https://stacks.math.columbia.edu/tag/0B6S)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Duality Stacks.Duality.DerivedPushforward

universe u

namespace AlgebraicGeometry.C1590Private

section TopDegree

open StacksDraft.DerivedModel

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The top cohomology of a derived pullback, at the locally small model.** For `K` in
`D(𝒪_Y)` with no cohomology above degree `d`, `H^d(Lf^*K) ≅ f^*H^d(K)`, for the derived pullback
`Stacks.Duality.derivedPullback`. -/
def homologyDerivedPullbackTopDegreeIso (K : DerivedCategory Y.Modules) (d : ℤ)
    (hK : K.IsLE d) :
    (DerivedCategory.homologyFunctor X.Modules d).obj ((Stacks.Duality.derivedPullback f).obj K) ≅
      (Scheme.Modules.pullback f).obj ((DerivedCategory.homologyFunctor Y.Modules d).obj K) :=
  let eY := Scheme.Modules.derivedModelEquiv Y
  let K' := eY.inverse.obj K
  have hK' : @DerivedCategory.IsLE Y.Modules _ _ (HasDerivedCategory.standard _) K' d :=
    (isLE_modelEquiv_iff (HasDerivedCategory.standard _) (Scheme.Modules.hasDerivedCategory Y)
      K' d).1
      (haveI : DerivedCategory.TStructure.t.IsLE ((𝟭 (DerivedCategory Y.Modules)).obj K) d := hK
      DerivedCategory.TStructure.t.isLE_of_iso (eY.counitIso.app K).symm d)
  (DerivedCategory.homologyFunctor X.Modules d).mapIso
      ((Stacks.Duality.derivedPullback f).mapIso (eY.counitIso.app K).symm ≪≫
        ((schemeDerivedPullbackStandardModelEquivIso f).app K').symm) ≪≫
    (modelHomologyFunctorIso (HasDerivedCategory.standard _) (Scheme.Modules.hasDerivedCategory X)
      d).app _ ≪≫
    Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback
      f.toLRSHom.toShHom K' d hK' ≪≫
    (Scheme.Modules.pullback f).mapIso
      ((modelHomologyFunctorIso (HasDerivedCategory.standard _)
          (Scheme.Modules.hasDerivedCategory Y) d).app K').symm ≪≫
    (Scheme.Modules.pullback f).mapIso
      ((DerivedCategory.homologyFunctor Y.Modules d).mapIso (eY.counitIso.app K))

/-- **The derived pullback is right t-exact, at the locally small model.** If `K ∈ D(𝒪_Y)` has no
cohomology above degree `d`, neither has `Lf^*K`, for the derived pullback
`Stacks.Duality.derivedPullback`. -/
theorem isLE_derivedPullback_obj (K : DerivedCategory Y.Modules) (d : ℤ) (hK : K.IsLE d) :
    ((Stacks.Duality.derivedPullback f).obj K).IsLE d := by
  let eY := Scheme.Modules.derivedModelEquiv Y
  let K' := eY.inverse.obj K
  have hK' : @DerivedCategory.IsLE Y.Modules _ _ (HasDerivedCategory.standard _) K' d :=
    (isLE_modelEquiv_iff (HasDerivedCategory.standard _) (Scheme.Modules.hasDerivedCategory Y)
      K' d).1
      (have : DerivedCategory.TStructure.t.IsLE ((𝟭 (DerivedCategory Y.Modules)).obj K) d := hK
      DerivedCategory.TStructure.t.isLE_of_iso (eY.counitIso.app K).symm d)
  have h₁ := (@DerivedCategory.isLE_iff X.Modules _ _ (HasDerivedCategory.standard _) _ d).1
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.isLE_derivedPullback_obj'
      f.toLRSHom.toShHom K' d hK')
  rw [DerivedCategory.isLE_iff]
  exact fun i hi => (h₁ i hi).of_iso ((DerivedCategory.homologyFunctor X.Modules i).mapIso
      ((Stacks.Duality.derivedPullback f).mapIso (eY.counitIso.app K).symm ≪≫
        ((schemeDerivedPullbackStandardModelEquivIso f).app K').symm) ≪≫
      (modelHomologyFunctorIso (HasDerivedCategory.standard _)
        (Scheme.Modules.hasDerivedCategory X) i).app _)

end TopDegree

section Definitions

variable {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f]

/-- **The relative dualizing complex `ω^•_{X/S} = a(𝒪_S)`** of a proper morphism `f : X ⟶ S`
over a quasi-compact quasi-separated base (Stacks 0B6S, 0E6N): the value at `𝒪_S` of the right
adjoint `a` of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_S)` (Stacks 0A9E). -/
def relativeDualizingComplex :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    quasiCoherentDerivedCategory X :=
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
    (derivedStructureSheaf S)

/-- **The relative dualizing sheaf `ω_{X/S} = H^{-1}(ω^•_{X/S})`** (Stacks 0E6Q). -/
def relativeDualizingSheaf : X.Modules :=
  (DerivedCategory.homologyFunctor X.Modules (-1)).obj (relativeDualizingComplex f).obj

end Definitions

section OverField

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- **Over a field the relative dualizing complex is the dualizing complex of Stacks 0BS2.** -/
theorem relativeDualizingComplex_eq_dualizingComplexOverField :
    relativeDualizingComplex f = dualizingComplexOverField f :=
  rfl

/-- **Over a field the relative dualizing sheaf is the dualizing sheaf of Stacks 0BS2.** -/
theorem relativeDualizingSheaf_eq_dualizingSheafOverField :
    relativeDualizingSheaf f = dualizingSheafOverField f :=
  rfl

end OverField

section BaseChange

/-- The base change of a proper morphism along a cartesian square is proper. -/
theorem isProper_of_isPullback {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S}
    {g : S' ⟶ S} (sq : IsPullback g' f' f g) [IsProper f] : IsProper f' :=
  MorphismProperty.of_isPullback sq inferInstance

variable {X' X S' S : Scheme.{u}} [CompactSpace S'] [QuasiSeparatedSpace S'] [CompactSpace S]
  [QuasiSeparatedSpace S] {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
  (sq : IsPullback g' f' f g) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]

/-- **The relative dualizing complex commutes with base change** (Stacks 0E6N, 0E6C): for a
cartesian square of quasi-compact quasi-separated bases, `L(g')^*ω^•_{X/S} ≅ ω^•_{X'/S'}`. -/
def relativeDualizingComplexBaseChangeIso :
    haveI := isProper_of_isPullback sq
    (Stacks.Duality.derivedPullback g').obj (relativeDualizingComplex f).obj ≅
      (relativeDualizingComplex f').obj :=
  haveI := isProper_of_isPullback sq
  (ObjectProperty.ι _).mapIso (twistedInverseImageStructureSheafBaseChangeIso sq).symm

/-- **Base change of the relative dualizing sheaf** (Stacks 0E6P): if `ω^•_{X/S}` has no
cohomology above degree `-1`, then for a cartesian square of quasi-compact quasi-separated bases
`(g')^*ω_{X/S} ≅ ω_{X'/S'}`. -/
def relativeDualizingSheafBaseChangeIsoOfIsLE
    (hK : (relativeDualizingComplex f).obj.IsLE (-1)) :
    haveI := isProper_of_isPullback sq
    (Scheme.Modules.pullback g').obj (relativeDualizingSheaf f) ≅ relativeDualizingSheaf f' :=
  haveI := isProper_of_isPullback sq
  (homologyDerivedPullbackTopDegreeIso g' (relativeDualizingComplex f).obj (-1) hK).symm ≪≫
    (DerivedCategory.homologyFunctor X'.Modules (-1)).mapIso
      (relativeDualizingComplexBaseChangeIso sq)

end BaseChange

section Fibre

variable {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] (f : X ⟶ S) [IsProper f]
  [Flat f] [LocallyOfFinitePresentation f]

/-- The fibre `X_s ⟶ Spec κ(s)` of a proper morphism is proper, with the residue field read as
`CommRingCat.of κ(s)`. -/
instance isProper_fiberToSpecResidueField_commRingCatOf (s : S) :
    IsProper (X := f.fiber s) (Y := Spec (CommRingCat.of (S.residueField s)))
      (f.fiberToSpecResidueField s) :=
  isProper_of_isPullback (IsPullback.of_hasPullback f (S.fromSpecResidueField s))

/-- **The relative dualizing sheaf restricts to the dualizing sheaf of each fibre**: if
`ω^•_{X/S}` has no cohomology above degree `-1`, the pullback of `ω_{X/S}` to the fibre `X_s` is
the dualizing sheaf `ω_{X_s}` of the proper `κ(s)`-scheme `X_s` (Stacks 0BS2). -/
def relativeDualizingSheafFibreIsoOfIsLE
    (hK : (relativeDualizingComplex f).obj.IsLE (-1)) (s : S) :
    (Scheme.Modules.pullback (f.fiberι s)).obj (relativeDualizingSheaf f) ≅
      dualizingSheafOverField (k := S.residueField s) (f.fiberToSpecResidueField s) :=
  relativeDualizingSheafBaseChangeIsoOfIsLE (IsPullback.of_hasPullback f (S.fromSpecResidueField s))
    hK

end Fibre

end AlgebraicGeometry.C1590Private

end
