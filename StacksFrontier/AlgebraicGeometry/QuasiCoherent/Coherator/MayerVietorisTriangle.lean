module

public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictAdjunction
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.DerivedPushforwardCommutation
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardAnyModel
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.UnboundedMayerVietorisTriangle

/-!
# The Mayer--Vietoris triangle of the coherator

Let `X` be a quasi-compact and quasi-separated scheme covered by two quasi-compact opens,
`X = U ∪ V`, and write `DQ_Z : D(𝒪_Z) ⥤ D_QCoh(𝒪_Z)` for a right adjoint of the inclusion
`D_QCoh(𝒪_Z) ⥤ D(𝒪_Z)` — the *coherator* of `Z`. For every `K` in `D(𝒪_X)` there is a canonical
distinguished triangle in `D_QCoh(𝒪_X)`

`DQ_X(K) ⟶ Rj_{U,*}DQ_U(K|_U) ⊕ Rj_{V,*}DQ_V(K|_V) ⟶ Rj_{U ∩ V,*}DQ_{U ∩ V}(K|_{U ∩ V}) ⟶`

## Main definitions

* `Stacks.Duality.Coherator.quasiCoherentι`: the inclusion `D_QCoh(𝒪_Z) ⥤ D(𝒪_Z)`.
* `Stacks.Duality.Coherator.restrictPushforward`: the object `Rj_{W,*}(K|_W)` of `D(𝒪_X)`.
* `Stacks.Duality.Coherator.restrictPushforwardUnit`: the unit `K ⟶ Rj_{W,*}(K|_W)` of
  `j_W^* ⊣ Rj_{W,*}`.
* `Stacks.Duality.Coherator.restrictCoheratorPushforward`: the object `Rj_{W,*}DQ_W(K|_W)` of
  `D_QCoh(𝒪_X)`.
* `Stacks.Duality.Coherator.coheratorPushforwardOpens`: the object `Rj_{W,*}DQ_W(K|_W)` for a
  quasi-compact open `W` of a quasi-compact quasi-separated scheme.
* `Stacks.Duality.Coherator.mayerVietorisMiddleIso`: the isomorphism
  `DQ_X(Rj_{U,*}(K|_U) ⊕ Rj_{V,*}(K|_V)) ≅ Rj_{U,*}DQ_U(K|_U) ⊕ Rj_{V,*}DQ_V(K|_V)`.
* `Stacks.Duality.Coherator.mayerVietorisThirdIso`: the isomorphism
  `DQ_X(Rj_{U ∩ V,*}(K|_{U ∩ V})) ≅ Rj_{U ∩ V,*}DQ_{U ∩ V}(K|_{U ∩ V})`.
* `Stacks.Duality.Coherator.mayerVietorisTriangle`: the canonical triangle above, as data.

## Main results

* `Stacks.Duality.Coherator.mayerVietorisTriangle_distinguished`: a distinguished triangle on the
  three terms above exists.

## Implementation notes

The derived categories are at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, with no `[HasDerivedCategory.{w}]` binder.

Everything is written with `AlgebraicGeometry.Scheme.Modules`, never with the definitionally equal
`SheafOfModules.{u} X.ringCatSheaf`: `Scheme.Modules` is not reducible, so mixing the two spellings
in one statement produces two `HasShift` instances on `D_QCoh(𝒪_X)` and two types
`DQ_X.CommShift ℤ` which print identically and do not unify.

## References

* [Stacks Project, Tag 0CR2](https://stacks.math.columbia.edu/tag/0CR2)
* [Stacks Project, Tag 0CR1](https://stacks.math.columbia.edu/tag/0CR1)
* [Stacks Project, Tag 0CR0](https://stacks.math.columbia.edu/tag/0CR0)
* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe u

namespace Stacks.Duality.Coherator

variable {X : Scheme.{u}}

/-! ### The terms of the two triangles -/

/-- The inclusion `D_QCoh(𝒪_Z) ⥤ D(𝒪_Z)` of the complexes of `𝒪_Z`-modules with quasi-coherent
cohomology into the unbounded derived category. A *coherator* of `Z` is a right adjoint of it. -/
abbrev quasiCoherentι (Z : Scheme.{u}) :
    quasiCoherentDerivedCategory Z ⥤ DerivedCategory Z.Modules :=
  (DerivedCategoryB.derivedCategoryB (A := Z.Modules)
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf)).ι

/-- The term `Rj_{W,*}(K|_W)` of `D(𝒪_X)` attached to an open `W` of a scheme `X` and an object
`K` of `D(𝒪_X)`: restrict `K` to the open subscheme `W`, then take the unbounded derived direct
image along the open immersion `j_W : W → X`. -/
abbrev restrictPushforward (W : X.Opens) (K : DerivedCategory X.Modules) :
    DerivedCategory X.Modules :=
  (derivedPushforward W.ι).obj ((OpenImmersion.derivedRestrict W.ι).obj K)

/-- The canonical map `K ⟶ Rj_{W,*}(K|_W)`, namely the unit of the adjunction `j_W^* ⊣ Rj_{W,*}` of
[Stacks, Tag 079W] for the open immersion `j_W : W → X`. -/
abbrev restrictPushforwardUnit (W : X.Opens) (K : DerivedCategory X.Modules) :
    K ⟶ restrictPushforward W K :=
  (OpenImmersion.derivedRestrictPushforwardAdjunction W.ι).unit.app K

/-- The term `Rj_{W,*}DQ_W(K|_W)` of `D_QCoh(𝒪_X)`: restrict `K` to the open subscheme `W`, apply
the coherator `DQ_W` of `W`, then take the restriction to `D_QCoh` of the unbounded derived direct
image along `j_W : W → X`, which preserves quasi-coherence of cohomology by `hpushW`. -/
abbrev restrictCoheratorPushforward (W : X.Opens)
    (hpushW : ∀ (L : quasiCoherentDerivedCategory W.toScheme) (i : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules i).obj
        ((derivedPushforward W.ι).obj L.obj)).IsQuasicoherent)
    (DQW : DerivedCategory W.toScheme.Modules ⥤ quasiCoherentDerivedCategory W.toScheme)
    (K : DerivedCategory X.Modules) : quasiCoherentDerivedCategory X :=
  (quasiCoherentDerivedPushforward W.ι hpushW).obj
    (DQW.obj ((OpenImmersion.derivedRestrict W.ι).obj K))

/-! ### The three uses of Tag 0CR1 -/

section

variable (U V : X.Opens)
  (DQX : DerivedCategory X.Modules ⥤ quasiCoherentDerivedCategory X)
  (DQU : DerivedCategory U.toScheme.Modules ⥤ quasiCoherentDerivedCategory U.toScheme)
  (DQV : DerivedCategory V.toScheme.Modules ⥤ quasiCoherentDerivedCategory V.toScheme)
  (DQUV : DerivedCategory (U ⊓ V).toScheme.Modules ⥤
    quasiCoherentDerivedCategory (U ⊓ V).toScheme)
  (adjX : quasiCoherentι X ⊣ DQX)
  (adjU : quasiCoherentι U.toScheme ⊣ DQU)
  (adjV : quasiCoherentι V.toScheme ⊣ DQV)
  (adjUV : quasiCoherentι (U ⊓ V).toScheme ⊣ DQUV)
  (hpushU : ∀ (L : quasiCoherentDerivedCategory U.toScheme) (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPushforward U.ι).obj L.obj)).IsQuasicoherent)
  (hpushV : ∀ (L : quasiCoherentDerivedCategory V.toScheme) (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPushforward V.ι).obj L.obj)).IsQuasicoherent)
  (hpushUV : ∀ (L : quasiCoherentDerivedCategory (U ⊓ V).toScheme) (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPushforward (U ⊓ V).ι).obj L.obj)).IsQuasicoherent)
  (K : DerivedCategory X.Modules)

/-- The coherator `DQ_X` of the second term of the Mayer--Vietoris triangle is the direct sum of
the second terms of the triangle of [Stacks, Tag 0CR2]:

`DQ_X(Rj_{U,*}(K|_U) ⊕ Rj_{V,*}(K|_V)) ≅ Rj_{U,*}DQ_U(K|_U) ⊕ Rj_{V,*}DQ_V(K|_V)`.

It is the biproduct comparison of `DQ_X` followed by the isomorphisms
`Stacks.Duality.coheratorDerivedPushforwardIso` of [Stacks, Tag 0CR1] at `K|_U` and at `K|_V`. -/
def mayerVietorisMiddleIso :
    DQX.obj (restrictPushforward U K ⊞ restrictPushforward V K) ≅
      restrictCoheratorPushforward U hpushU DQU K ⊞
        restrictCoheratorPushforward V hpushV DQV K :=
  letI : DQX.IsRightAdjoint := adjX.isRightAdjoint
  letI : DQX.Additive := adjX.right_adjoint_additive
  letI : PreservesBinaryBiproducts DQX :=
    preservesBinaryBiproducts_of_preservesBinaryProducts DQX
  DQX.mapBiprod _ _ ≪≫
    biprod.mapIso
      ((coheratorDerivedPushforwardIso U.ι hpushU DQU DQX adjU adjX).app
        ((OpenImmersion.derivedRestrict U.ι).obj K)).symm
      ((coheratorDerivedPushforwardIso V.ι hpushV DQV DQX adjV adjX).app
        ((OpenImmersion.derivedRestrict V.ι).obj K)).symm

/-- The coherator `DQ_X` of the third term of the Mayer--Vietoris triangle is the third term of the
triangle of [Stacks, Tag 0CR2]:

`DQ_X(Rj_{U ∩ V,*}(K|_{U ∩ V})) ≅ Rj_{U ∩ V,*}DQ_{U ∩ V}(K|_{U ∩ V})`.

It is the inverse of the isomorphism `Stacks.Duality.coheratorDerivedPushforwardIso` of
[Stacks, Tag 0CR1] along `j_{U ∩ V}`, at the object `K|_{U ∩ V}` of `D(𝒪_{U ∩ V})`. -/
def mayerVietorisThirdIso :
    DQX.obj (restrictPushforward (U ⊓ V) K) ≅
      restrictCoheratorPushforward (U ⊓ V) hpushUV DQUV K :=
  ((coheratorDerivedPushforwardIso (U ⊓ V).ι hpushUV DQUV DQX adjUV adjX).app
    ((OpenImmersion.derivedRestrict (U ⊓ V).ι).obj K)).symm

/-! ### The triangle -/

/-- The canonical triangle

`DQ_X(K) ⟶ Rj_{U,*}DQ_U(K|_U) ⊕ Rj_{V,*}DQ_V(K|_V) ⟶ Rj_{U ∩ V,*}DQ_{U ∩ V}(K|_{U ∩ V}) ⟶`

attached to a scheme `X`, two opens `U`, `V` of `X`, coherators `DQ_X`, `DQ_U`, `DQ_V`,
`DQ_{U ∩ V}` with `DQ_X` commuting with the shift, an object `K` of `D(𝒪_X)`, and the last two maps
`mor₂`, `mor₃` of the Mayer--Vietoris triangle of [Stacks, Tag 08BV] for the cover `X = U ∪ V`.

It is the image under `DQ_X` of that Mayer--Vietoris triangle, conjugated by
`Stacks.Duality.Coherator.mayerVietorisMiddleIso` and
`Stacks.Duality.Coherator.mayerVietorisThirdIso`: the first map is `DQ_X` of the canonical
`biprod.lift` of the two units of `j_W^* ⊣ Rj_{W,*}` followed by the middle identification, the
second is `DQ_X(mor₂)` read through both identifications, and the third is `DQ_X(mor₃)` read
through the third identification and the commutation of `DQ_X` with the shift. -/
@[stacks 0CR2 "the canonical triangle, as data"]
def mayerVietorisTriangle [DQX.CommShift ℤ]
    (mor₂ : restrictPushforward U K ⊞ restrictPushforward V K ⟶ restrictPushforward (U ⊓ V) K)
    (mor₃ : restrictPushforward (U ⊓ V) K ⟶ K⟦(1 : ℤ)⟧) :
    Triangle (quasiCoherentDerivedCategory X) :=
  Triangle.mk
    (DQX.map (biprod.lift (restrictPushforwardUnit U K) (restrictPushforwardUnit V K)) ≫
      (mayerVietorisMiddleIso U V DQX DQU DQV adjX adjU adjV hpushU hpushV K).hom)
    ((mayerVietorisMiddleIso U V DQX DQU DQV adjX adjU adjV hpushU hpushV K).inv ≫
      DQX.map mor₂ ≫ (mayerVietorisThirdIso U V DQX DQUV adjX adjUV hpushUV K).hom)
    ((mayerVietorisThirdIso U V DQX DQUV adjX adjUV hpushUV K).inv ≫
      DQX.map mor₃ ≫ (DQX.commShiftIso (1 : ℤ)).hom.app K)

end

/-! ### The triangle of the tag is distinguished -/

/- The intersection of two quasi-compact opens of a quasi-separated scheme is quasi-compact. -/
attribute [local instance] AlgebraicGeometry.Scheme.Opens.compactSpace_inf

/-- The term `Rj_{W,*}DQ_W(K|_W)` of `D_QCoh(𝒪_X)` attached to a quasi-compact open `W` of a
quasi-compact quasi-separated scheme `X`, a coherator `DQ_W` of `W` and an object `K` of
`D(𝒪_X)`: `Stacks.Duality.Coherator.restrictCoheratorPushforward`, with the preservation of
quasi-coherence by `Rj_{W,*}` given by
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_opens`. -/
abbrev coheratorPushforwardOpens [CompactSpace X] [QuasiSeparatedSpace X] (W : X.Opens)
    [CompactSpace W.toScheme]
    (DQW : DerivedCategory W.toScheme.Modules ⥤ quasiCoherentDerivedCategory W.toScheme)
    (K : DerivedCategory X.Modules) : quasiCoherentDerivedCategory X :=
  restrictCoheratorPushforward W (isQuasicoherent_homology_derivedPushforward_opens W) DQW K

section

variable [CompactSpace X] [QuasiSeparatedSpace X] (U V : X.Opens)
  [CompactSpace U.toScheme] [CompactSpace V.toScheme]
  (DQX : DerivedCategory X.Modules ⥤ quasiCoherentDerivedCategory X)
  (DQU : DerivedCategory U.toScheme.Modules ⥤ quasiCoherentDerivedCategory U.toScheme)
  (DQV : DerivedCategory V.toScheme.Modules ⥤ quasiCoherentDerivedCategory V.toScheme)
  (DQUV : DerivedCategory (U ⊓ V).toScheme.Modules ⥤
    quasiCoherentDerivedCategory (U ⊓ V).toScheme)
  (adjX : quasiCoherentι X ⊣ DQX)
  (adjU : quasiCoherentι U.toScheme ⊣ DQU)
  (adjV : quasiCoherentι V.toScheme ⊣ DQV)
  (adjUV : quasiCoherentι (U ⊓ V).toScheme ⊣ DQUV)
  (K : DerivedCategory X.Modules)

include adjX adjU adjV adjUV

/-- Let `X` be a quasi-compact and quasi-separated scheme, let `X = U ∪ V` with `U` and `V`
quasi-compact open, and let `DQ_X`, `DQ_U`, `DQ_V`, `DQ_{U ∩ V}` be coherators — right adjoints of
the inclusions `D_QCoh ⥤ D`. Then for every object `K` of `D(𝒪_X)` there is a distinguished
triangle

`DQ_X(K) ⟶ Rj_{U,*}DQ_U(K|_U) ⊕ Rj_{V,*}DQ_V(K|_V) ⟶ Rj_{U ∩ V,*}DQ_{U ∩ V}(K|_{U ∩ V}) ⟶`

in `D_QCoh(𝒪_X)`. -/
@[stacks 0CR2 "the distinguished triangle of the tag, over arbitrary coherators"]
theorem mayerVietorisTriangle_distinguished (hUV : U ⊔ V = ⊤) :
    ∃ (f : DQX.obj K ⟶
          coheratorPushforwardOpens U DQU K ⊞ coheratorPushforwardOpens V DQV K)
      (g : coheratorPushforwardOpens U DQU K ⊞ coheratorPushforwardOpens V DQV K ⟶
          coheratorPushforwardOpens (U ⊓ V) DQUV K)
      (h : coheratorPushforwardOpens (U ⊓ V) DQUV K ⟶ (DQX.obj K)⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (quasiCoherentDerivedCategory X) := by
  let : DQX.CommShift ℤ := adjX.rightAdjointCommShift ℤ
  let : adjX.CommShift ℤ := adjX.commShift_of_leftAdjoint ℤ
  let : adjX.IsTriangulated := Adjunction.IsTriangulated.mk' adjX
  obtain ⟨f, g, δ, hT⟩ := exists_distTriang_self U V hUV K
  let eM := mayerVietorisMiddleIso U V DQX DQU DQV adjX adjU adjV
    (isQuasicoherent_homology_derivedPushforward_opens U)
    (isQuasicoherent_homology_derivedPushforward_opens V) K
  let eT := mayerVietorisThirdIso U V DQX DQUV adjX adjUV
    (isQuasicoherent_homology_derivedPushforward_opens (U ⊓ V)) K
  refine ⟨DQX.map f ≫ eM.hom, eM.inv ≫ DQX.map g ≫ eT.hom,
    eT.inv ≫ DQX.map δ ≫ (DQX.commShiftIso (1 : ℤ)).hom.app K, ?_⟩
  refine isomorphic_distinguished _ (DQX.map_distinguished _ hT) _ (Iso.symm ?_)
  exact Triangle.isoMk _ _ (Iso.refl _) eM eT
    (by simp [Functor.mapTriangle]) (by simp [Functor.mapTriangle])
    (by simp [Functor.mapTriangle])

end

end Stacks.Duality.Coherator

end
