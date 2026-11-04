module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Double
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Deformation.Artin.Infinitesimal.AutomorphismFunctor
public import StacksFrontier.Deformation.Artin.Infinitesimal.CanonicalElement
public import StacksFrontier.Deformation.Artin.Obstruction
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveCotangentPresentation
public import StacksFrontier.Deformation.Artin.Obstruction.Theory
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Strong
public import StacksFrontier.Homology.DoubleExtend

/-!
# Naive obstruction theories

A *naive obstruction theory* for a category fibred in groupoids `𝒳` over the big fppf site of
a base scheme `S` satisfying (RS*) replaces the abstract obstruction modules of Stacks 07YG by
`Ext` groups out of a single complex. To every object `x` of `𝒳` lying over the spectrum of an
`S`-algebra `A`, together with an affine open `Spec Λ ⊆ S` through which `Spec A → S` factors,
it attaches an object `E_x` of `D⁻(A)` and a map `ξ_x : E_x → NL_{A/Λ}`, identifies the
infinitesimal-automorphism and tangent functors of `x` with `Ext^{-1}_A(E_x, −)` and
`Ext^0_A(E_x, −)`, and makes `E_x` functorial in `(x, A)`; the vanishing of
`E_x → NL_{A/Λ} → NL_{A/A'}` is then exactly the liftability of `x` over a square-zero
thickening `A' → A`.

## Main definitions

* `Deformation.Artin.restrictScalarsHom` — the morphism `M ⟶ Res_f N` of `A`-modules
  attached to an `f`-semilinear map, for a ring map `f : A → C`.
* `Deformation.Artin.derivedRestrictScalarsCompOfEq` — restriction of scalars along a composite
  of ring maps, on derived categories.
* `Deformation.Artin.naiveCotangentSourceMap` — the morphism `NL_{A/Λ} ⟶ NL_{C/Λ}` of
  `D(A)` attached to a ring map `A → C` over `Λ`: functoriality of the naive cotangent
  complex in its *first* variable, in the derived category.
* `Deformation.Artin.naiveCotangentToDifferentials` — the canonical morphism
  `NL_{A/Λ} ⟶ Ω_{A/Λ}[0]` of `D(A)`.
* `Deformation.Artin.extPushforward`, `Deformation.Artin.extRestrictScalars` — the two
  functorialities of `Ext^i_A(E, −)` used to state the compatibilities: pushing a class
  along a map of coefficient modules, and pulling a class back along a morphism
  `E ⟶ Res_f F` over a change of rings.
* `Deformation.Artin.AffineChart` — an affine open `Spec Λ ⊆ S` of the base.
* `Deformation.Artin.ChartedObject` — the index of clause (1) of the source: an object of
  `𝒳` over the spectrum of an `S`-algebra `A` together with a factorization of
  `Spec A → S` through a fixed affine chart `Spec Λ ⊆ S`, which is what `NL_{A/Λ}` needs.
* `Deformation.Artin.IsSquareZeroLiftBaseChange`,
  `Deformation.Artin.IsInfinitesimalAutomorphismBaseChange` — the canonical transitions of
  Stacks 07YA on lifts and on infinitesimal automorphisms across a ring map `A → C`, as the
  property that pins them down: pullback along the induced map `Spec C[N] → Spec A[M]`.
* `Deformation.Artin.NaiveObstructionTheory` — **Stacks 07YP**, a naive obstruction theory.

## Implementation notes

`Ext` is the `ℤ`-indexed `CategoryTheory.DerivedCategory.Ext X Y i = Hom_{D(A)}(X, Y⟦i⟧)` of
`StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic`, so the source's `Ext^{-1}_A(E_x, M)`
is `DerivedCategory.Ext E_x (M[0]) (-1)` on the nose and no shift has to be absorbed into the
coefficient module. With Mathlib's convention `(M[0]⟦i⟧)^j = (M[0])^{i + j}`, the complex
`M[0]⟦i⟧` is the source's `M[i]`, so `DerivedCategory.Ext E_x (M[0]) i` is the source's
`Ext^i_A(E_x, M)`.

Clause (1) of the source writes `NL_{A/Λ}` for a choice of affine open `Spec Λ ⊆ S` containing
the image of `Spec A`, but the quantification "for every `(x, A)`" leaves that choice implicit.
Here the chart is part of the index: a `Deformation.Artin.ChartedObject` is an object over an
`S`-algebra together with the chart and the resulting `Λ`-algebra structure. The chart is a
single parameter of the structure, as it must be: clause (1) of the source uses the *same* `Λ`
for `A` and for every `B` receiving a ring map from `A`, since condition (i) compares
`NL_{A/Λ}` with `NL_{B/Λ}`. The chart is recorded as an open immersion `Spec Λ ⟶ S` rather
than as an affine open subscheme of `S`; the two data determine each other, and because an
open immersion is a monomorphism the factorization of `Spec A → S` through it is unique, so
the `Λ`-algebra structure on `A` is determined by the geometry and nothing is added by
recording it.

The tangent and infinitesimal-automorphism functors of Stacks 07Y9 are functors on
`Deformation.Artin.SiteModule A B`, the `A`-modules whose trivial square-zero extension occurs
in the chosen big site, whereas `Ext^i_A(E_x, −)` is defined on all of `ModuleCat A`. The
transformations of clause (2) are therefore stated pointwise on site modules, on the
underlying `A`-module of each; this is the restriction of the `Ext` functor along the
forgetful functor `SiteModule A B ⥤ ModuleCat A`, written out rather than named. For the same
reason their values lie in different universes — `Ext` in `Type (u + 1)`, the tangent module
in `Type (max (u + 1) v w)` and the infinitesimal automorphisms in `Type w` — so the
transformations are plain functions together with their additivity and naturality rather than
morphisms of `ModuleCat A`. That is not a weakening: the `A`-module structure on the tangent
and infinitesimal-automorphism functors is the unique one compatible with the finite products
(Stacks 06I6), hence the action of `a : A` is induced by the module map `a • − : M → M`, as it
is on `Ext^i_A(E_x, −)`; so a natural additive transformation is automatically `A`-linear.

Three constructions the source uses are not in Mathlib and are built here. Functoriality of
the naive cotangent complex in its first variable,
`Deformation.Artin.naiveCotangentSourceMap`, is the derived-category form of
`NaiveCotangent.nlMapBase`: for a ring map `A → C` over `Λ` the two complexes live over
different rings, so the morphism is one of `D(A)` after restriction of scalars, obtained by
`HomologicalComplex.mkHomFromDouble` on the two `HomologicalComplex.double` complexes followed
by `DerivedCategory.Q.map` and the factorization of
`CategoryTheory.Functor.mapDerivedCategory`. The comparison
`Deformation.Artin.derivedRestrictScalarsCompOfEq` of restriction along a composite is the
field-free form of `DerivedCategory.derivedRestrictScalarsComp`, needed for condition (ii).
The projection `Deformation.Artin.naiveCotangentToDifferentials` is the chain map which is
zero in degree `-1` and `Algebra.Extension.toKaehler` in degree `0`.

Following the house style of `Deformation.Artin.ObstructionTheory`, the conditions which
assert that an induced map exists *and* satisfies a formula are written as existentials whose
first conjunct pins the map down. Each such formula determines its map uniquely — the
transition maps of Stacks 07YA are characterised by pullback of lifts along a cartesian
arrow — so the existential forms are equivalent to the universally quantified ones and in
addition assert existence; they are not weaker. The ring map `A[M] → C[N]` and the morphism of
spectra it induces are supplied the same way, by their values, so no choice of representative
of `Spec` of a ring map enters.

The algebra structures which the naive cotangent complexes need — `Algebra A C` for a ring map
`A → C` of the site, `Algebra Λ A'` and `Algebra A' A` for a deformation situation — are taken
as instance arguments of the conditions and pinned to the given ring maps by an equation. This
avoids transporting along `RingHom.toAlgebra` inside the types of the fields, and quantifying
over all such structures is no weaker: the equations determine them.

The source's standing hypothesis that `S` is locally Noetherian is not needed to form the
definition and so is not imposed; the results which consume a naive obstruction theory carry
it themselves. The source's condition (v) states the vanishing in
`Hom_A(E_x, NL_{A/A'}) = Ext^0_A(E_x, NL_{A/A'}) = Ext^1_A(E_x, I)`; those are three
descriptions of one group, and the condition is recorded as the vanishing of the composite
morphism of `D(A)`.

The source has two typographical slips which are corrected here: clause (1) writes
`ξ_x : E → NL_{A/Λ}` for `ξ_x : E_x → NL_{A/Λ}`, and condition (v) writes
`Hom_A(E_x, NL_{A/Λ})` for `Hom_A(E_x, NL_{A/A'})`.

## References

* [Stacks Project, Tag 07YP](https://stacks.math.columbia.edu/tag/07YP)
* [Stacks Project, Tag 07YA](https://stacks.math.columbia.edu/tag/07YA)
* [Stacks Project, Tag 07YC](https://stacks.math.columbia.edu/tag/07YC)
* [Stacks Project, Tag 07YG](https://stacks.math.columbia.edu/tag/07YG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open ComplexShape (upIntRelNegOneZero)

universe u v w

namespace Deformation.Artin

attribute [local instance] HasDerivedCategory.standard

/-! ### Semilinear maps and restriction of scalars -/

/-- The morphism `M ⟶ Res_f N` of `A`-modules attached to an `f`-semilinear map of underlying
modules, for a ring map `f : A → C`. -/
public def restrictScalarsHom {A C : Type u} [CommRing A] [CommRing C] (f : A →+* C)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} C} (φ : M.carrier → N.carrier)
    (hadd : ∀ m m', φ (m + m') = φ m + φ m')
    (hsmul : ∀ (a : A) (m : M.carrier), φ (a • m) = f a • φ m) :
    M ⟶ (ModuleCat.restrictScalars f).obj N :=
  ConcreteCategory.ofHom { toFun := φ, map_add' := hadd, map_smul' := hsmul }

/-- Restricting scalars along a composite of ring maps agrees with restricting along the two
maps in turn, on derived categories. -/
public def derivedRestrictScalarsCompOfEq {A C D : Type u} [CommRing A] [CommRing C] [CommRing D]
    (f : A →+* C) (g : C →+* D) (gf : A →+* D) (hgf : gf = g.comp f) :
    (ModuleCat.restrictScalars.{u} g).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{u} f).mapDerivedCategory ≅
      (ModuleCat.restrictScalars.{u} gf).mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} D) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (ModuleCat.restrictScalars.{u} g).mapDerivedCategory ⋙
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategory)
    (DerivedCategory.Q ⋙ (ModuleCat.restrictScalars.{u} gf).mapDerivedCategory)
    ((ModuleCat.restrictScalars.{u} g).mapDerivedCategory ⋙
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategory)
    (ModuleCat.restrictScalars.{u} gf).mapDerivedCategory
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (ModuleCat.restrictScalars.{u} g).mapDerivedCategoryFactors _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso
        (ModuleCat.restrictScalarsComp' f g gf hgf).symm (ComplexShape.up ℤ)) _ ≪≫
      (ModuleCat.restrictScalars.{u} gf).mapDerivedCategoryFactors.symm)

/-! ### The naive cotangent complex in its first variable -/

section NaiveCotangent

/-- The two-term complex of the canonical presentation, placed in cohomological degrees `-1`
and `0`: the complex whose image in the derived category is
`Deformation.Artin.derivedNaiveCotangentComplex`. -/
public abbrev naiveCotangentDouble (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A] :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  HomologicalComplex.double
    (ModuleCat.ofHom (Algebra.Generators.self Λ A).toExtension.cotangentComplex)
    upIntRelNegOneZero

variable (Λ A C : Type u) [CommRing Λ] [CommRing A] [CommRing C]
  [Algebra Λ A] [Algebra Λ C] [Algebra A C] [IsScalarTower Λ A C]

/-- The chain map underlying `Deformation.Artin.naiveCotangentSourceMap`: the comparison
`NL_{A/Λ} ⟶ NL_{C/Λ}` of two-term complexes induced by the canonical morphism of
presentations, viewed over `A` by restriction of scalars. -/
public def naiveCotangentSourceChainMap :
    naiveCotangentDouble Λ A ⟶
      ((ModuleCat.restrictScalars.{u} (algebraMap A C)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (naiveCotangentDouble Λ C) := by
  let P := Algebra.Generators.self Λ A
  let P' := Algebra.Generators.self Λ C
  let g := P.defaultHom P'
  let R := ModuleCat.restrictScalars.{u} (algebraMap A C)
  let hrel := upIntRelNegOneZero
  have hne : (-1 : ℤ) ≠ 0 := by omega
  let m₁ : ModuleCat.of A P.toExtension.Cotangent ⟶
      R.obj (ModuleCat.of C P'.toExtension.Cotangent) :=
    restrictScalarsHom _ (Algebra.Extension.Cotangent.map g.toExtensionHom)
      (fun z z' => map_add _ z z') (fun a z => by
        rw [map_smul, ← IsScalarTower.algebraMap_smul C a
          (Algebra.Extension.Cotangent.map g.toExtensionHom z)])
  let m₀ : ModuleCat.of A P.toExtension.CotangentSpace ⟶
      R.obj (ModuleCat.of C P'.toExtension.CotangentSpace) :=
    restrictScalarsHom _ (Algebra.Extension.CotangentSpace.map g.toExtensionHom)
      (fun z z' => map_add _ z z') (fun a z => by
        rw [map_smul, ← IsScalarTower.algebraMap_smul C a
          (Algebra.Extension.CotangentSpace.map g.toExtensionHom z)])
  refine HomologicalComplex.mkHomFromDouble hrel hne
    (m₁ ≫ (R.mapIso (HomologicalComplex.doubleXIso₀
      (ModuleCat.ofHom P'.toExtension.cotangentComplex) hrel)).inv)
    (m₀ ≫ (R.mapIso (HomologicalComplex.doubleXIso₁
      (ModuleCat.ofHom P'.toExtension.cotangentComplex) hrel hne)).inv) ?_ ?_
  · have hmap : m₁ ≫ R.map (ModuleCat.ofHom P'.toExtension.cotangentComplex) =
        ModuleCat.ofHom P.toExtension.cotangentComplex ≫ m₀ :=
      ModuleCat.hom_ext (LinearMap.ext fun z =>
        (Algebra.Extension.CotangentSpace.map_cotangentComplex g.toExtensionHom z).symm)
    have hinv : (R.mapIso (HomologicalComplex.doubleXIso₀
          (ModuleCat.ofHom P'.toExtension.cotangentComplex) hrel)).inv ≫
        R.map ((HomologicalComplex.doubleXIso₀
            (ModuleCat.ofHom P'.toExtension.cotangentComplex) hrel).hom ≫
          ModuleCat.ofHom P'.toExtension.cotangentComplex ≫
          (HomologicalComplex.doubleXIso₁
            (ModuleCat.ofHom P'.toExtension.cotangentComplex) hrel hne).inv) =
        R.map (ModuleCat.ofHom P'.toExtension.cotangentComplex) ≫
          R.map (HomologicalComplex.doubleXIso₁
            (ModuleCat.ofHom P'.toExtension.cotangentComplex) hrel hne).inv := by
      rw [Functor.mapIso_inv, ← R.map_comp, ← R.map_comp, Iso.inv_hom_id_assoc, R.map_comp]
    rw [Functor.mapHomologicalComplex_obj_d, HomologicalComplex.double_d _ _ hne,
      Category.assoc, hinv, ← Category.assoc, hmap, Category.assoc, Functor.mapIso_inv]
  · intro k hk
    rw [Functor.mapHomologicalComplex_obj_d,
      HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by omega), R.map_zero, Limits.comp_zero]

/-- Functoriality of the naive cotangent complex in its first variable, in the derived
category: the morphism `NL_{A/Λ} ⟶ NL_{C/Λ}` of `D(A)` attached to a ring map `A ⟶ C` of
`Λ`-algebras. The target is a complex of `C`-modules, so it is viewed in `D(A)` by
restriction of scalars. -/
public def naiveCotangentSourceMap :
    derivedNaiveCotangentComplex Λ A ⟶
      (ModuleCat.restrictScalars.{u} (algebraMap A C)).mapDerivedCategory.obj
        (derivedNaiveCotangentComplex Λ C) :=
  DerivedCategory.Q.map (naiveCotangentSourceChainMap Λ A C) ≫
    (ModuleCat.restrictScalars.{u}
      (algebraMap A C)).mapDerivedCategoryFactors.inv.app (naiveCotangentDouble Λ C)

/-- The chain map underlying `Deformation.Artin.naiveCotangentToDifferentials`: the
projection of the two-term complex of the canonical presentation onto its degree-zero
cohomology, given in degree `0` by `Algebra.Extension.toKaehler`. -/
public def naiveCotangentToDifferentialsChainMap (Λ A : Type u) [CommRing Λ] [CommRing A]
    [Algebra Λ A] :
    twoTermComplex (NaiveCotangent.nlRestrict A (Algebra.Generators.self Λ A)) ⟶
      (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
        (differentialsModule Λ A) :=
  let P := Algebra.Generators.self Λ A
  HomologicalComplex.mkHomFromDouble upIntRelNegOneZero (show (-1 : ℤ) ≠ 0 by omega) 0
    (ModuleCat.ofHom P.toExtension.toKaehler ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (differentialsModule Λ A)).inv)
    (by
      have h0 : ModuleCat.ofHom (NaiveCotangent.nlRestrict A P).d ≫
          ModuleCat.ofHom P.toExtension.toKaehler = 0 :=
        ModuleCat.hom_ext (LinearMap.ext fun z =>
          P.toExtension.exact_cotangentComplex_toKaehler.apply_apply_eq_zero z)
      rw [Limits.zero_comp, ← Category.assoc, h0, Limits.zero_comp])
    (fun k _ => by rw [HomologicalComplex.single_obj_d, Limits.comp_zero])

/-- The canonical morphism `NL_{A/Λ} ⟶ Ω_{A/Λ}[0]` of `D(A)`: the projection of the naive
cotangent complex onto its degree-zero cohomology, given in degree `0` by
`Algebra.Extension.toKaehler`. -/
public def naiveCotangentToDifferentials (Λ A : Type u) [CommRing Λ] [CommRing A]
    [Algebra Λ A] :
    derivedNaiveCotangentComplex Λ A ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (differentialsModule Λ A) :=
  DerivedCategory.Q.map (naiveCotangentToDifferentialsChainMap Λ A)

end NaiveCotangent

/-! ### Ext groups along a map of coefficients and a change of rings -/

section Ext

variable {A C : Type u} [CommRing A] [CommRing C]

/-- The pushforward of an `Ext` class along a map of coefficient modules. -/
public def extPushforward (E : DerivedCategory (ModuleCat.{u} A)) {M N : ModuleCat.{u} A}
    (f : M ⟶ N) (i : ℤ)
    (α : DerivedCategory.Ext E
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) i) :
    DerivedCategory.Ext E ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) i :=
  α ≫ ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f)⟦i⟧'

/-- The pullback of an `Ext` class over a change of rings: a morphism `E ⟶ Res_f F` of `D(A)`
carries `Ext^i_C(F, N)` to `Ext^i_A(E, Res_f N)`. -/
public def extRestrictScalars (f : A →+* C)
    (E : DerivedCategory (ModuleCat.{u} A)) (F : DerivedCategory (ModuleCat.{u} C))
    (c : E ⟶ (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj F)
    (N : ModuleCat.{u} C) (i : ℤ)
    (β : DerivedCategory.Ext F
      ((DerivedCategory.singleFunctor (ModuleCat.{u} C) 0).obj N) i) :
    DerivedCategory.Ext E ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      ((ModuleCat.restrictScalars.{u} f).obj N)) i :=
  c ≫ (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.map β ≫
    (((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.commShiftIso i).app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} C) 0).obj N)).hom ≫
    ((((ModuleCat.restrictScalars.{u} f).mapDerivedCategorySingleFunctor 0).app N).hom)⟦i⟧'

end Ext

/-! ### Objects over an affine chart of the base -/

/-- An affine open `Spec Λ ⊆ S` of the base, as in clause (1) of the source: a ring `Λ`
together with an open immersion `Spec Λ ⟶ S`. -/
public structure AffineChart (S : Scheme.{u}) where
  /-- The ring `Λ` of functions on the chart. -/
  ring : Type u
  [commRing : CommRing ring]
  /-- The morphism `Spec Λ ⟶ S`. -/
  immersion : Spec (.of ring) ⟶ S
  /-- It is an open immersion, so `Spec Λ` is an affine open subscheme of `S`. -/
  isOpenImmersion : IsOpenImmersion immersion

attribute [instance] AffineChart.commRing AffineChart.isOpenImmersion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)

/-- The index of clause (1) of the source: an object `x` of the fibred category over the
spectrum of an `S`-algebra `A`, together with the factorization of `Spec A → S` through a
fixed affine chart `Spec Λ ⊆ S` which makes `A` a `Λ`-algebra and hence makes `NL_{A/Λ}`
available. -/
public structure ChartedObject (c : AffineChart S) where
  /-- The object `x` of the fibred category over the spectrum of an `S`-algebra `A`. -/
  obj : AffineObject B S hS p
  /-- `A` is an algebra over the ring of functions on the chart. -/
  [algebra : Algebra c.ring obj.alg.carrier]
  /-- The structure morphism `Spec A ⟶ S` factors through the chart by that algebra
  structure. -/
  factorization :
    Spec.map (CommRingCat.ofHom (algebraMap c.ring obj.alg.carrier)) ≫ c.immersion =
      obj.alg.toScheme

attribute [instance] ChartedObject.algebra

namespace ChartedObject

variable {B S hS p} {c : AffineChart S}

/-- The `S`-algebra `A` underlying a charted object. -/
public abbrev ring (P : ChartedObject B S hS p c) : Type u := P.obj.alg.carrier

/-- The object `x` of the fibred category, as an object of the ambient category. -/
public abbrev point (P : ChartedObject B S hS p c) : X := P.obj.obj.1

/-- The naive cotangent complex `NL_{A/Λ}` of a charted object, in `D(A)`. -/
public abbrev naiveCotangent (P : ChartedObject B S hS p c) :
    DerivedCategory (ModuleCat.{u} P.ring) :=
  derivedNaiveCotangentComplex c.ring P.ring

/-- The tangent functor `T_x` of a charted object. -/
public abbrev tangent (P : ChartedObject B S hS p c) (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp) :
    TangentFunctorData P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem p P.point P.obj.obj.2 :=
  tangentFunctor P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem p P.point P.obj.obj.2 hp hRS

/-- The functor `Inf_x` of infinitesimal automorphisms of a charted object. -/
public abbrev infAut (P : ChartedObject B S hS p c) (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp) :
    InfinitesimalAutomorphismFunctorData P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem p
      P.point P.obj.obj.2 hp :=
  infinitesimalAutomorphismFunctor P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem p P.point
    P.obj.obj.2 hp hRS

/-- The isomorphism classes of lifts of `x` over the trivial square-zero extension `A[M]`,
which are the values of the tangent functor. -/
public abbrev liftClasses (P : ChartedObject B S hS p c) (M : SiteModule P.ring B) : Type _ :=
  squareZeroLiftClasses P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem p P.point
    P.obj.obj.2 M

/-- A lift of `x` over the trivial square-zero extension `A[M]`. -/
public abbrev liftOver (P : ChartedObject B S hS p c) (M : SiteModule P.ring B) : Type _ :=
  (Under.post p).Fiber (Under.mk (eqToHom P.obj.obj.2 ≫
    squareZeroArrow P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem M))

/-- The trivial lift of `x` over `A[M]`, whose automorphisms are the values of `Inf_x`. -/
public abbrev trivialLift (P : ChartedObject B S hS p c) (hp : p.IsFiberedInGroupoids)
    (M : SiteModule P.ring B) : P.liftOver M :=
  trivialDeformation P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem p P.point P.obj.obj.2 hp M

/-- `Spec A[M]`, as an object over `S` in the site. -/
public abbrev squareZeroBase (P : ChartedObject B S hS p c) (M : SiteModule P.ring B) :
    BigFppfOver B S hS :=
  squareZeroOver P.ring B S hS P.obj.alg.toScheme M

end ChartedObject

/-! ### The transitions of Stacks 07YA across a ring map -/

section BaseChange

variable {B S hS p} {c : AffineChart S}

/-- The ring map `A[M] ⟶ C[N]` of trivial square-zero extensions determined by a ring map
`f : A ⟶ C` and an `f`-semilinear map `M ⟶ N` of coefficients, together with the morphism of
spectra over `S` it induces: the base of the transition maps of Stacks 07YA. -/
public def IsSquareZeroBaseMap {P Q : ChartedObject B S hS p c} (f : P.ring →+* Q.ring)
    {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (g : Q.squareZeroBase N ⟶ P.squareZeroBase M) : Prop :=
  ∃ e : TrivSqZeroExt P.ring M.obj →+* TrivSqZeroExt Q.ring N.obj,
    (∀ z : TrivSqZeroExt P.ring M.obj, e z = (f z.fst, ψ z.snd)) ∧
      (BigFppfOver.toScheme B S hS).map g = Spec.map (CommRingCat.ofHom e)

/-- The transition of Stacks 07YA on lifts across a ring map: the class `b` of lifts of `y`
over `C[N]` is the pullback of the class `a` of lifts of `x` over `A[M]` along the morphism
`Spec C[N] ⟶ Spec A[M]` induced by `A ⟶ C` and `M ⟶ N`, compatibly with `y ⟶ x`. -/
public def IsSquareZeroLiftBaseChange {P Q : ChartedObject B S hS p c}
    (h : AffineObject.Hom P.obj Q.obj) (f : P.ring →+* Q.ring)
    {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (a : P.liftClasses M) (b : Q.liftClasses N) : Prop :=
  ∃ (a' : P.liftOver M) (b' : Q.liftOver N),
    Quotient.mk _ a' = a ∧ Quotient.mk _ b' = b ∧
      ∃ g : Q.squareZeroBase N ⟶ P.squareZeroBase M,
        IsSquareZeroBaseMap f ψ g ∧
          ∃ φ : b'.1.right ⟶ a'.1.right,
            p.IsStronglyCartesian g φ ∧ b'.1.hom ≫ φ = h.objMap ≫ a'.1.hom

/-- The transition of Stacks 07YA on infinitesimal automorphisms across a ring map: a
cartesian arrow exhibiting the trivial lift of `y` over `C[N]` as the pullback of the trivial
lift of `x` over `A[M]` conjugates the automorphism `θ'` into `θ`. -/
public def IsInfinitesimalAutomorphismBaseChange {P Q : ChartedObject B S hS p c}
    (hp : p.IsFiberedInGroupoids) (h : AffineObject.Hom P.obj Q.obj) (f : P.ring →+* Q.ring)
    {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (θ : P.trivialLift hp M ⟶ P.trivialLift hp M)
    (θ' : Q.trivialLift hp N ⟶ Q.trivialLift hp N) : Prop :=
  ∃ g : Q.squareZeroBase N ⟶ P.squareZeroBase M,
    IsSquareZeroBaseMap f ψ g ∧
      ∃ ρ : (Q.trivialLift hp N).1.right ⟶ (P.trivialLift hp M).1.right,
        p.IsStronglyCartesian g ρ ∧
          (Q.trivialLift hp N).1.hom ≫ ρ = h.objMap ≫ (P.trivialLift hp M).1.hom ∧
            θ'.1.right ≫ ρ = ρ ≫ θ.1.right

end BaseChange

/-! ### Naive obstruction theories -/

/-- **Stacks 07YP.** A naive obstruction theory for a category fibred in groupoids `𝒳` over
the big fppf site of `S` satisfying (RS*), relative to a fixed affine chart `Spec Λ ⊆ S`: a
complex `E_x ∈ D⁻(A)` with a map `ξ_x : E_x ⟶ NL_{A/Λ}` for every object `x` of `𝒳` over
`Spec A`, identifications of `Inf_x` and `T_x` with `Ext^{-1}_A(E_x, −)` and
`Ext^0_A(E_x, −)`, and a functoriality map `E_x ⟶ E_y` for every ring map `A ⟶ B`, subject to
the five conditions of the source. -/
@[stacks 07YP]
public structure NaiveObstructionTheory (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp) (c : AffineChart S) where
  /-- Clause (1): the object `E_x` of `D⁻(A)` attached to an object `x` of the fibred category
  over the spectrum of an `S`-algebra `A` mapping into the chart. -/
  complex : ∀ P : ChartedObject B S hS p c, DerivedCategory.Minus (ModuleCat.{u} P.ring)
  /-- Clause (1): the map `ξ_x : E_x ⟶ NL_{A/Λ}` in `D(A)`. -/
  xi : ∀ P : ChartedObject B S hS p c, (complex P).obj ⟶ P.naiveCotangent
  /-- Clause (2): the transformation `Inf_x(M) ⟶ Ext^{-1}_A(E_x, M)`, at a module `M` whose
  trivial square-zero extension occurs in the site. -/
  infMap : ∀ (P : ChartedObject B S hS p c) (M : SiteModule P.ring B),
    ((P.infAut hp hRS).functor.obj M : Type w) →
      DerivedCategory.Ext (complex P).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} P.ring) 0).obj M.obj) (-1)
  /-- Clause (2): the transformation on infinitesimal automorphisms is additive. -/
  infMap_add : ∀ (P : ChartedObject B S hS p c) (M : SiteModule P.ring B)
      (θ θ' : ((P.infAut hp hRS).functor.obj M : Type w)),
    infMap P M (θ + θ') = infMap P M θ + infMap P M θ'
  /-- Clause (2): the transformation on infinitesimal automorphisms is natural in the
  coefficient module. -/
  infMap_natural : ∀ (P : ChartedObject B S hS p c) (M N : SiteModule P.ring B) (f : M ⟶ N)
      (θ : ((P.infAut hp hRS).functor.obj M : Type w)),
    infMap P N ((P.infAut hp hRS).functor.map f θ) =
      extPushforward (complex P).obj f.hom (-1) (infMap P M θ)
  /-- Clause (2): the transformation `T_x(M) ⟶ Ext^0_A(E_x, M)`. -/
  tangentMap : ∀ (P : ChartedObject B S hS p c) (M : SiteModule P.ring B),
    ((P.tangent hp hRS).functor.obj M : Type (max (u + 1) v w)) →
      DerivedCategory.Ext (complex P).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} P.ring) 0).obj M.obj) 0
  /-- Clause (2): the transformation on tangent modules is additive. -/
  tangentMap_add : ∀ (P : ChartedObject B S hS p c) (M : SiteModule P.ring B)
      (a a' : ((P.tangent hp hRS).functor.obj M : Type (max (u + 1) v w))),
    tangentMap P M (a + a') = tangentMap P M a + tangentMap P M a'
  /-- Clause (2): the transformation on tangent modules is natural in the coefficient
  module. -/
  tangentMap_natural : ∀ (P : ChartedObject B S hS p c) (M N : SiteModule P.ring B)
      (f : M ⟶ N) (a : ((P.tangent hp hRS).functor.obj M : Type (max (u + 1) v w))),
    tangentMap P N ((P.tangent hp hRS).functor.map f a) =
      extPushforward (complex P).obj f.hom 0 (tangentMap P M a)
  /-- Clause (3): the functoriality map `E_x ⟶ E_y` in `D(A)` attached to a ring map `A ⟶ C`
  of `Λ`-algebras in the site and the restriction `y = x|_{Spec C}`. The target is a complex
  of `C`-modules, viewed in `D(A)` by restriction of scalars. -/
  functoriality : ∀ (P Q : ChartedObject B S hS p c) (h : AffineObject.Hom P.obj Q.obj)
      [Algebra P.ring Q.ring] [IsScalarTower c.ring P.ring Q.ring]
      (_halg : algebraMap P.ring Q.ring = h.alg.ringMap),
    (complex P).obj ⟶
      (ModuleCat.restrictScalars.{u} (algebraMap P.ring Q.ring)).mapDerivedCategory.obj
        (complex Q).obj
  /-- Condition (i): the square formed by `ξ_x`, `ξ_y`, the functoriality map `E_x ⟶ E_y` and
  the base-change map `NL_{A/Λ} ⟶ NL_{C/Λ}` commutes in `D(A)`. -/
  xi_functoriality : ∀ (P Q : ChartedObject B S hS p c) (h : AffineObject.Hom P.obj Q.obj)
      [Algebra P.ring Q.ring] [IsScalarTower c.ring P.ring Q.ring]
      (halg : algebraMap P.ring Q.ring = h.alg.ringMap),
    functoriality P Q h halg ≫
        (ModuleCat.restrictScalars.{u} (algebraMap P.ring Q.ring)).mapDerivedCategory.map
          (xi Q) =
      xi P ≫ naiveCotangentSourceMap c.ring P.ring Q.ring
  /-- Condition (ii): for `A ⟶ C ⟶ D` the composite of the functoriality maps `E_x ⟶ E_y` and
  `E_y ⟶ E_z` is the functoriality map `E_x ⟶ E_z`. -/
  functoriality_comp : ∀ (P Q R : ChartedObject B S hS p c)
      (h : AffineObject.Hom P.obj Q.obj) (k : AffineObject.Hom Q.obj R.obj)
      [Algebra P.ring Q.ring] [Algebra Q.ring R.ring] [Algebra P.ring R.ring]
      [IsScalarTower P.ring Q.ring R.ring] [IsScalarTower c.ring P.ring Q.ring]
      [IsScalarTower c.ring Q.ring R.ring] [IsScalarTower c.ring P.ring R.ring]
      (halg : algebraMap P.ring Q.ring = h.alg.ringMap)
      (kalg : algebraMap Q.ring R.ring = k.alg.ringMap)
      (hcomp : algebraMap P.ring R.ring = (h.comp k).alg.ringMap),
    functoriality P R (h.comp k) hcomp =
      functoriality P Q h halg ≫
        (ModuleCat.restrictScalars.{u} (algebraMap P.ring Q.ring)).mapDerivedCategory.map
          (functoriality Q R k kalg) ≫
        (derivedRestrictScalarsCompOfEq (algebraMap P.ring Q.ring) (algebraMap Q.ring R.ring)
          (algebraMap P.ring R.ring)
          (IsScalarTower.algebraMap_eq P.ring Q.ring R.ring)).hom.app (complex R).obj
  /-- Condition (iii): the transformation `Inf_x(−) ⟶ Ext^{-1}_A(E_x, −)` is an
  isomorphism. -/
  infMap_bijective : ∀ (P : ChartedObject B S hS p c) (M : SiteModule P.ring B),
    Function.Bijective (infMap P M)
  /-- Condition (iii): the transformation `T_x(−) ⟶ Ext^0_A(E_x, −)` is an isomorphism. -/
  tangentMap_bijective : ∀ (P : ChartedObject B S hS p c) (M : SiteModule P.ring B),
    Function.Bijective (tangentMap P M)
  /-- Condition (iii): the transformation on infinitesimal automorphisms is compatible with
  the functoriality maps and with the transition maps of Stacks 07YA. -/
  infMap_functoriality : ∀ (P Q : ChartedObject B S hS p c)
      (h : AffineObject.Hom P.obj Q.obj) [Algebra P.ring Q.ring]
      [IsScalarTower c.ring P.ring Q.ring] (halg : algebraMap P.ring Q.ring = h.alg.ringMap)
      (M : SiteModule P.ring B) (N : SiteModule Q.ring B)
      (ψ : M.obj ⟶
        (ModuleCat.restrictScalars (algebraMap P.ring Q.ring)).obj N.obj),
    ∃ σ : ((P.infAut hp hRS).functor.obj M : Type w) →
        ((Q.infAut hp hRS).functor.obj N : Type w),
      (∀ θ, IsInfinitesimalAutomorphismBaseChange hp h (algebraMap P.ring Q.ring) ψ
        ((P.infAut hp hRS).autEquiv M θ) ((Q.infAut hp hRS).autEquiv N (σ θ))) ∧
        ∀ θ, extPushforward (complex P).obj ψ (-1) (infMap P M θ) =
          extRestrictScalars (algebraMap P.ring Q.ring) (complex P).obj (complex Q).obj
            (functoriality P Q h halg) N.obj (-1) (infMap Q N (σ θ))
  /-- Condition (iii): the transformation on tangent modules is compatible with the
  functoriality maps and with the transition maps of Stacks 07YA. -/
  tangentMap_functoriality : ∀ (P Q : ChartedObject B S hS p c)
      (h : AffineObject.Hom P.obj Q.obj) [Algebra P.ring Q.ring]
      [IsScalarTower c.ring P.ring Q.ring] (halg : algebraMap P.ring Q.ring = h.alg.ringMap)
      (M : SiteModule P.ring B) (N : SiteModule Q.ring B)
      (ψ : M.obj ⟶
        (ModuleCat.restrictScalars (algebraMap P.ring Q.ring)).obj N.obj),
    ∃ τ : ((P.tangent hp hRS).functor.obj M : Type (max (u + 1) v w)) →
        ((Q.tangent hp hRS).functor.obj N : Type (max (u + 1) v w)),
      (∀ a, IsSquareZeroLiftBaseChange h (algebraMap P.ring Q.ring) ψ
        ((P.tangent hp hRS).liftEquiv M a) ((Q.tangent hp hRS).liftEquiv N (τ a))) ∧
        ∀ a, extPushforward (complex P).obj ψ 0 (tangentMap P M a) =
          extRestrictScalars (algebraMap P.ring Q.ring) (complex P).obj (complex Q).obj
            (functoriality P Q h halg) N.obj 0 (tangentMap Q N (τ a))
  /-- Condition (iv): the composition `E_x ⟶ NL_{A/Λ} ⟶ Ω_{A/Λ}` is the image under the
  transformation of clause (2) of the canonical element of `T_x(Ω_{A/Λ})`. -/
  tangentMap_canonicalElement : ∀ (P : ChartedObject B S hS p c)
      (hΩ : B.Contains (Spec (squareZeroRing P.ring
        (differentialsModule c.ring P.ring)))),
    tangentMap P (differentialsSiteModule c.ring P.ring B hΩ)
        (canonicalDeformationElement c.ring P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem
          p P.point P.obj.obj.2 hp hRS hΩ c.immersion P.factorization).element =
      ShiftedHom.mk₀ (0 : ℤ) rfl
        (xi P ≫ naiveCotangentToDifferentials c.ring P.ring)
  /-- Condition (v): for a deformation situation `(x, A' ⟶ A)` the object `x` lifts over
  `Spec A'` exactly when the composition `E_x ⟶ NL_{A/Λ} ⟶ NL_{A/A'}` vanishes. -/
  hasLift_iff_xi_comp_eq_zero : ∀ (P : ChartedObject B S hS p c)
      (t : DeformationSituation B S hS P.obj.alg)
      [Algebra t.top.carrier P.ring] [Algebra c.ring t.top.carrier]
      [IsScalarTower c.ring t.top.carrier P.ring]
      (_hmap : algebraMap t.top.carrier P.ring = t.hom.ringMap)
      (_hchart : Spec.map (CommRingCat.ofHom (algebraMap c.ring t.top.carrier)) ≫ c.immersion =
        t.top.toScheme),
    AffineObject.HasLift hp P.obj t ↔
      xi P ≫ naiveCotangentBaseMap c.ring t.top.carrier P.ring = 0

end Deformation.Artin
