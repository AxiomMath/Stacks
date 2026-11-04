module

public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatSource.Global
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.BaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.AffineStageDescent.ProperSmoothModel
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.MayerVietorisTorDimension
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherentPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalPerfectness
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
import StacksCore.Tactic.StacksAttribute

/-!
# The derived direct image of the relative differential forms of a smooth morphism

For a proper smooth morphism `f : X ⟶ S`, the derived direct image `Rf_*Ω^p_{X/S}` is a
perfect object of `D(𝒪_S)` (`isPerfect_derivedPushforward_forms`) whose formation commutes with
arbitrary change of base (`isIso_derivedBaseChangeMap_forms`): the two assertions of
[Stacks, Tag 0FM0] for the forms. Base change holds because `Ω^p_{X/S}` is flat over `S` and over
`X` and pulls back to `Ω^p_{X'/S'}` (Stacks 0FL5). Perfectness holds over a Noetherian base by
Stacks 0B6G, is transported along base change, and the general case follows by absolute
Noetherian approximation over affine opens and locality of perfectness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Modules (toShHom_comm)
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedBaseChange
open Stacks.AlgebraicGeometry.FlatSourceBaseChange

universe u

namespace AlgebraicGeometry.ProperSmoothDeRham

noncomputable section

attribute [local instance 10000] HasDerivedCategory.standard

variable {X X' S S' : Scheme.{u}}

/-- The sheaf `Ω^p_{X/S}` placed in degree zero, as an object of the unbounded derived category
of `𝒪_X`-modules. -/
abbrev formsObj (f : X ⟶ S) (p : ℕ) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
  DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
    ((HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ) 0).obj (Scheme.Hom.relativeDifferentialForms f (p : ℤ))))

/-- **The canonical comparison `L(g')^*Ω^p_{X/S} ⟶ Ω^p_{X'/S'}`** attached to a commutative
square of schemes: the comparison of derived and underived pullback, followed by the canonical
map `(g')^*Ω^p_{X/S} ⟶ Ω^p_{X'/S'}` on differential forms of Stacks 07HX. -/
def formsBaseChangeComparison (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (w : g' ≫ f = f' ≫ g) (p : ℕ) :
    (derivedPullback g'.toLRSHom.toShHom).obj (formsObj f p) ⟶ formsObj f' p :=
  (derivedPullbackComparison g'.toLRSHom.toShHom).app _ ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex (modulePullback g'.toLRSHom.toShHom)
          (ComplexShape.up ℤ) 0).hom.app (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) ≫
        (HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))
          (ComplexShape.up ℤ) 0).map
          (Scheme.Hom.relativeDifferentialFormsMap g' f f' g w (p : ℤ))))

/-- **The sheaf `Ω^p_{X/S}` of a smooth morphism is flat as an `𝒪_X`-module**: it is finite
locally free. -/
theorem isFlat_relativeDifferentialForms (f : X ⟶ S) [Smooth f] (p : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) :=
  AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree _
    (isFiniteLocallyFree_relativeDifferentialForms f p)

/-- **The comparison `L(g')^*Ω^p_{X/S} ⟶ Ω^p_{X'/S'}` is invertible** for a cartesian square
with `f` smooth: `Ω^p_{X/S}` is flat, so its derived pullback is its pullback, and the canonical
map on differential forms is invertible by Stacks 0FL5. -/
theorem isIso_formsBaseChangeComparison {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S}
    {g : S' ⟶ S} (hsq : IsPullback g' f' f g) [Smooth f] (p : ℕ) :
    IsIso (formsBaseChangeComparison g' f' f g hsq.w p) := by
  have := isIso_derivedPullbackComparison_single_of_isFlat g'.toLRSHom.toShHom _
    (isFlat_relativeDifferentialForms f p)
  have h₀ : @IsIso (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)) _ _ _
      (Scheme.Hom.relativeDifferentialFormsMap g' f f' g hsq.w (p : ℤ)) :=
    Scheme.Hom.isIso_relativeDifferentialFormsMap_of_isPullback g' f f' g hsq (p : ℤ)
  let e : (HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ) 0 ⋙ (modulePullback g'.toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) ≅
      (HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))
        (ComplexShape.up ℤ) 0).obj (Scheme.Hom.relativeDifferentialForms f' (p : ℤ)) :=
    (HomologicalComplex.singleMapHomologicalComplex (modulePullback g'.toLRSHom.toShHom)
        (ComplexShape.up ℤ) 0).app _ ≪≫
      (HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))
        (ComplexShape.up ℤ) 0).mapIso
        (@asIso (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)) _ _ _ _ h₀)
  have key : formsBaseChangeComparison g' f' f g hsq.w p =
      (derivedPullbackComparison g'.toLRSHom.toShHom).app _ ≫
        (DerivedCategory.Qh.mapIso
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso e)).hom := rfl
  rw [key]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ this (Iso.isIso_hom _)

/-- **Base change for `Rf_*Ω^p_{X/S}`.** Let `f : X ⟶ S` be a proper smooth morphism of schemes
and let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square. Then the canonical map

`Lg^*Rf_*Ω^p_{X/S} ⟶ Rf'_*L(g')^*Ω^p_{X/S} ⟶ Rf'_*Ω^p_{X'/S'}`

— the derived base change map of Stacks 08HY followed by `Rf'_*` of the comparison
`formsBaseChangeComparison` — is an isomorphism. -/
@[stacks 0FM0 "formation of Rf_*Omega^p_X/S commutes with arbitrary change of base: for a \
proper smooth f and any cartesian square the derived base change map of Tag 08HY at Omega^p_X/S \
followed by Rf'_* of the canonical map L(g')^*Omega^p_X/S -> Omega^p_X'/S' is an isomorphism"]
theorem isIso_derivedBaseChangeMap_forms {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S}
    {g : S' ⟶ S} (hsq : IsPullback g' f' f g) [IsProper f] [Smooth f] (p : ℕ) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom (toShHom_comm hsq.w) (formsObj f p) ≫
      (derivedPushforward f'.toLRSHom.toShHom).map
        (formsBaseChangeComparison g' f' f g hsq.w p)) := by
  have := isIso_derivedBaseChangeMap_single hsq
    ⟨Scheme.Hom.relativeDifferentialForms f (p : ℤ),
      Scheme.Hom.isQuasicoherent_relativeDifferentialForms f p⟩
    (isFlatOver_relativeDifferentialForms f p) (isFlat_relativeDifferentialForms f p)
  have := isIso_formsBaseChangeComparison hsq p
  infer_instance

/-- The base change isomorphism `Lg^*Rf_*Ω^p_{X/S} ≅ Rf'_*Ω^p_{X'/S'}` of
`isIso_derivedBaseChangeMap_forms`. -/
def formsBaseChangeIso {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (hsq : IsPullback g' f' f g) [IsProper f] [Smooth f] (p : ℕ) :
    (derivedPullback g.toLRSHom.toShHom).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj (formsObj f p)) ≅
      (derivedPushforward f'.toLRSHom.toShHom).obj (formsObj f' p) :=
  haveI := isIso_derivedBaseChangeMap_forms hsq p
  asIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
      g.toLRSHom.toShHom (toShHom_comm hsq.w) (formsObj f p) ≫
    (derivedPushforward f'.toLRSHom.toShHom).map (formsBaseChangeComparison g' f' f g hsq.w p))

/-- **`Ω^p_{X/S}` placed in degree zero is a perfect object of `D(𝒪_X)`** for a smooth
morphism: it is finite locally free. -/
theorem isPerfect_formsObj (f : X ⟶ S) [Smooth f] (p : ℕ) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) (formsObj f p) :=
  have := isFiniteLocallyFree_relativeDifferentialForms f p
  ⟨(HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ) 0).obj (Scheme.Hom.relativeDifferentialForms f (p : ℤ)),
    isPerfectComplex_single_of_isFiniteLocallyFree X _
      (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _),
    ⟨((DerivedCategory.quotientCompQhIso _).app _).symm⟩⟩

/-- **Perfectness of `Rf_*Ω^p_{X/S}` over a Noetherian base**: this is Stacks 0B6G, a smooth
morphism being flat and locally of finite presentation, hence perfect. -/
theorem isPerfect_derivedPushforward_forms_of_isNoetherian (f : X ⟶ S) [IsNoetherian S]
    [IsProper f] [Smooth f] (p : ℕ) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforward f.toLRSHom.toShHom).obj (formsObj f p)) :=
  Stacks.AlgebraicGeometry.PerfectProperDirectImage.isPerfect_derivedPushforward_of_isPerfect f
    (formsObj f p) (isPerfect_formsObj f p)

/-- **Perfectness of `Rf_*Ω^p_{X/S}` transported along a base change.** For a cartesian square
with `f` proper smooth, if `Rf_*Ω^p_{X/S}` is perfect then so is `Rf'_*Ω^p_{X'/S'}`: it is the
derived pullback of the former by the base change isomorphism. -/
theorem isPerfect_derivedPushforward_forms_of_isPullback {g' : X' ⟶ X} {f' : X' ⟶ S'}
    {f : X ⟶ S} {g : S' ⟶ S} (hsq : IsPullback g' f' f g) [IsProper f] [Smooth f] (p : ℕ)
    (h : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforward f.toLRSHom.toShHom).obj (formsObj f p))) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S'.toRingedSpace)
      ((derivedPushforward f'.toLRSHom.toShHom).obj (formsObj f' p)) :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (formsBaseChangeIso hsq p)
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
      g.toLRSHom.toShHom _ h)

/-- **Perfectness of `Rf_*Ω^p_{X/S}` over an affine base**, by absolute Noetherian
approximation: `f` is the base change of a proper smooth morphism to a Noetherian scheme. -/
theorem isPerfect_derivedPushforward_forms_of_isAffine (f : X ⟶ S) [IsAffine S]
    [IsProper f] [Smooth f] (p : ℕ) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforward f.toLRSHom.toShHom).obj (formsObj f p)) := by
  obtain ⟨T, Y, h, q, q', hT, hpr, hsm, hpb⟩ := exists_isPullback_isNoetherian_properSmooth f
  exact isPerfect_derivedPushforward_forms_of_isPullback hpb p
    (isPerfect_derivedPushforward_forms_of_isNoetherian h p)

/-- **Perfectness of `Rf_*Ω^p_{X/S}`.** For a proper smooth morphism of schemes `f : X ⟶ S`
the derived direct image `Rf_*Ω^p_{X/S}` is a perfect object of `D(𝒪_S)`. Perfectness is local
on `S`, its restriction to an affine open `V` is the derived direct image of `Ω^p` along the
base change of `f` to `V` by base change, and over an affine base this is
`isPerfect_derivedPushforward_forms_of_isAffine`. -/
@[stacks 0FM0 "Rf_*Omega^p_X/S is a perfect object of D(O_S) for a proper smooth f, for every \
p >= 0, over an arbitrary base"]
theorem isPerfect_derivedPushforward_forms (f : X ⟶ S) [IsProper f] [Smooth f] (p : ℕ) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforward f.toLRSHom.toShHom).obj (formsObj f p)) := by
  refine Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect _ fun x => ?_
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  refine ⟨V, hxV, ?_⟩
  have : IsAffine (V : Scheme.{u}) := hV
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    ((AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoDerivedPullback S.toRingedSpace
      V).app _ ≪≫ formsBaseChangeIso (IsPullback.of_hasPullback f V.ι) p).symm
    (isPerfect_derivedPushforward_forms_of_isAffine (pullback.snd f V.ι) p)

end

end AlgebraicGeometry.ProperSmoothDeRham
