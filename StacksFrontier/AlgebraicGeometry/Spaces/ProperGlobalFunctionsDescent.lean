module

public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.RingTheory.Finiteness.Small
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.Connected
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricComponentCount
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalFunctionsSpecMap
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsSeparable
public import StacksFrontier.RingTheory.TensorProduct.SeparableSelfConnected

/-!
# Separable descent for the global functions of a geometrically connected algebraic space

Let `k` be a field and let `X` be an algebraic space over `k` with
`A = H⁰(X, 𝒪_X) = AlgebraicGeometry.Space.globalFunctions`.  This file proves the descent step
behind parts (5) to (8) of Tag 0DMY, and the content of parts (7) and (8):  if `X` is proper,
geometrically reduced and geometrically connected, with finite dimensional global functions,
then `A = k`.  The registered statements, which discharge finiteness from properness, are in
`StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsGeometric`.

## Main definitions

* `AlgebraicGeometry.Space.siteToBase` is the structure morphism of an object of the big fppf
  site over `Spec k` to the terminal object of the slice.
* `AlgebraicGeometry.Space.pointsPullbackSpecHomeomorph` identifies the point space of
  `Spec A' ×_{Spec k} Spec k'` with the spectrum of `A' ⊗_k k'`.

## Main results

* `AlgebraicGeometry.Space.connectedSpace_points_of_isGeometricallyConnected`: the point space of
  a geometrically connected algebraic space is connected.
* `AlgebraicGeometry.Space.connectedSpace_primeSpectrum_tensorProduct_of_isGeometricallyConnected`:
  the descent step.  For a geometrically connected `X` whose global functions are presented by a
  `k`-algebra `A'` with a one-point spectrum in the universe of the site, the spectrum of
  `A' ⊗_k k'` is connected for every field extension `k'/k` in the site.
* `AlgebraicGeometry.Space.bijective_baseToGlobalFunctions_of_finite`: for a proper
  geometrically reduced and geometrically connected `X` with finite dimensional global
  functions, the canonical map `k ⟶ H⁰(X, 𝒪_X)` is bijective.
* `Space.isGeometricallyReduced_and_isGeometricallyConnected_of_isGeometricallyIntegral`: a
  geometrically integral algebraic space is geometrically reduced and geometrically connected.

## Implementation notes

**The route taken.**  Tag 0DMY argues through Tag 073K, the comparison
`H⁰(X, 𝒪_X) ⊗_k K = H⁰(X_K, 𝒪_{X_K})` for a field extension `K/k`.  What is used instead is
*separable descent* along the canonical morphism to the spectrum of the global functions, which
needs no cohomology.  Writing `A'` for a presentation of `A` by a `k`-algebra in the universe of
the site — one exists because `A` is finite over `k`, so `Module.Finite.small` applies — the
three steps are:

1. The presentation `A' ≃ₐ[k] A` gives a morphism of algebraic spaces `p : X ⟶ Spec A'` over
   `Spec k`, `AlgebraicGeometry.Space.toSpecOfAlgHom`.  When `|Spec A'|` is a single point and
   `|X|` is nonempty, `p` is surjective on points.
2. Base change along `Spec k' ⟶ Spec k` preserves surjectivity on points, which is Tag 03MH
   (`AlgebraicGeometry.Space.surjective_pointsMap_of_isPullback`) applied to the cartesian
   naturality square of the counit of the relocalization adjunction
   (`CategoryTheory.OverShriek.isPullback_map_relocalizeRestrictCounit`).  The source of that
   base change is `X_{k'}` read over `Spec k`, whose point space is `|X_{k'}|` and so is
   connected by geometric connectedness; the target is `Spec (A' ⊗_k k')`, because the counit
   exhibits the base change of a representable as the fibre product of the two site objects and
   both `yoneda` and `BigFppfOver.toScheme` preserve fibre products.  Hence
   `|Spec (A' ⊗_k k')|` is connected, being the image of a connected space under a continuous
   surjection.
3. For parts (7) and (8), taking `k' := A'` and feeding
   `Stacks.SeparableSelfTensor.bijective_algebraMap_of_connectedSpace` — a finite separable
   extension whose tensor square has connected spectrum is trivial — gives `A' = k`, the
   separability being part (4).  For parts (5) and (6) the descent step is taken at an
   algebraic closure of `k`, in
   `StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsIrreducible`;  that is why it asks
   only for a one-point spectrum of `A'`, rather than for a field.

## References

* [Stacks Project, Tag 0DMY](https://stacks.math.columbia.edu/tag/0DMY)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
* [Stacks Project, Tag 0DMX](https://stacks.math.columbia.edu/tag/0DMX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

section Descent

attribute [local instance] pointTopology

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hS X)
    (A' : Type u) [CommRing A'] [Algebra k A'] (hA' : B.Contains (Spec (.of A')))

variable {k B hS}

/-- The structure morphism of an object of the big fppf site over `Spec k` to the terminal object
of the slice, which is the base read as an object over itself. -/
def siteToBase (U : BigFppfOver B (Spec (.of k)) hS) : U ⟶ Over.mk (𝟙 (B.obj hS)) :=
  Over.homMk U.hom (by simp)

/-- The structure morphism of a representable presheaf to the representable presheaf of the
terminal object of the slice is the Yoneda image of `AlgebraicGeometry.Space.siteToBase`:  there
is only one morphism to that presheaf. -/
theorem toYonedaMkId_yoneda_obj (U : BigFppfOver B (Spec (.of k)) hS) :
    OverShriek.toYonedaMkId (yoneda.obj U) = yoneda.map (siteToBase U) := by
  ext W x
  exact (OverShriek.subsingleton_yoneda_obj_mkId W).elim _ _

variable (k B hS)

/-- **The point space of the fibre product of `Spec A'` with `Spec k'` over `Spec k` is the
spectrum of `A' ⊗_k k'`.**  Both `yoneda` and `AlgebraicGeometry.BigFppfOver.toScheme` preserve
fibre products, so the presheaf fibre product is represented by the fibre product of the two
site objects, whose underlying scheme is `Spec A' ×_{Spec k} Spec k'`;  that is
`Spec (A' ⊗_k k')` by `AlgebraicGeometry.pullbackSpecIso`. -/
def pointsPullbackSpecHomeomorph (k' : Type u) [Field k'] [Algebra k k']
    (hk' : B.Contains (Spec (.of k'))) :
    points B (Spec (.of k)) hS
        (pullback (yoneda.map (siteToBase (specSiteObject k B hS A' hA')))
          (yoneda.map (siteToBase (Over.mk (specMapOfExtension B k hS k' hk'))))) ≃ₜ
      PrimeSpectrum (A' ⊗[k] k') :=
  have := preservesLimitsOfShape_walkingCospan_toScheme B (Spec (.of k)) hS
  (pointsHomeomorphOfIso B (Spec (.of k)) hS
      (PreservesPullback.iso (yoneda (C := BigFppfOver B (Spec (.of k)) hS))
        (siteToBase (specSiteObject k B hS A' hA'))
        (siteToBase (Over.mk (specMapOfExtension B k hS k' hk')))).symm).trans
    ((schemePointsHomeomorph B (Spec (.of k)) hS _).trans
      ((Scheme.homeoOfIso (PreservesPullback.iso (BigFppfOver.toScheme B (Spec (.of k)) hS)
          (siteToBase (specSiteObject k B hS A' hA'))
          (siteToBase (Over.mk (specMapOfExtension B k hS k' hk'))))).trans
        (Scheme.homeoOfIso (pullbackSpecIso k A' k'))))

include hX

omit hX in
/-- **The point space of a geometrically connected algebraic space is connected.**  This is the
definition of geometric connectedness at the trivial extension `k/k`, whose site morphism is the
identity and whose base change is therefore `X` itself. -/
theorem connectedSpace_points_of_isGeometricallyConnected
    (hconn : IsGeometricallyConnected B k hS X) :
    ConnectedSpace (points B (Spec (.of k)) hS X) := by
  have hid : fieldExtensionMap B k k hS hS = 𝟙 (B.obj hS) := by
    apply B.inclusion.map_injective
    rw [map_fieldExtensionMap, CategoryTheory.Functor.map_id]
    change Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _
    simp
  have h := hconn k hS
  rw [hid] at h
  exact connectedSpace_points_of_iso B (Spec (.of k)) hS
    (((Functor.whiskeringLeft (Over (B.obj hS))ᵒᵖ (Over (B.obj hS))ᵒᵖ (Type u)).mapIso
      (NatIso.op (Over.mapId (B.obj hS)).symm)).app X) h

include hA'

/-- **The descent step.**  Let `X` be a geometrically connected algebraic space over `k` whose
global functions are presented by a `k`-algebra `A'` in the universe of the site with a
one-point spectrum — a field, or an Artinian local ring.  Then `|Spec (A' ⊗_k k')|` is connected
for every field extension `k'/k` whose spectrum lies in the site.

The presentation gives a morphism `p : X ⟶ Spec A'` over `Spec k`,
`AlgebraicGeometry.Space.toSpecOfAlgHom`;  it is surjective on
points because `|X|` is nonempty and `|Spec A'|` is a single point.  The naturality square of the
counit of the relocalization adjunction along `Spec k' ⟶ Spec k` is cartesian, so Tag 03MH makes
the base change of `p` surjective on points too.  Its source has the point space of `X_{k'}`,
which is connected, and its target is `Spec (A' ⊗_k k')` by
`AlgebraicGeometry.Space.pointsPullbackSpecHomeomorph`. -/
theorem connectedSpace_primeSpectrum_tensorProduct_of_isGeometricallyConnected
    [Subsingleton (PrimeSpectrum A')]
    (hconn : IsGeometricallyConnected B k hS X)
    (e : globalFunctions B (Spec (.of k)) hS X ≃ₐ[k] A')
    (k' : Type u) [Field k'] [Algebra k k'] (hk' : B.Contains (Spec (.of k'))) :
    ConnectedSpace (PrimeSpectrum (A' ⊗[k] k')) := by
  set T := specSiteObject k B hS A' hA' with hT
  set a := specMapOfExtension B k hS k' hk' with ha
  set p : X ⟶ yoneda.obj T :=
    toSpecOfAlgHom k B hS ⟨X, hX⟩ A' hA' e.symm.toAlgHom with hp
  -- the point space of the base change of `X` to `k'`, read over `Spec k`, is connected
  have hXk' : ConnectedSpace (points B (Spec (.of k')) hk'
      ((OverShriek.relocalizeRestrict a).obj X)) := by
    rw [ha, specMapOfExtension_eq_fieldExtensionMap B k hS k' hk']
    exact hconn k' hk'
  have hRX : IsAlgebraicSpace B (Spec (.of k')) hk' ((OverShriek.relocalizeRestrict a).obj X) :=
    isAlgebraicSpace_relocalizeRestrict B (Spec (.of k')) (Spec (.of k)) hk' hS a X hX
  have hhX := relocalizedPointsHomeo B (Spec (.of k')) (Spec (.of k)) hk' hS a
    ((OverShriek.relocalizeRestrict a).obj X) hRX
  have hΛX : ConnectedSpace (points B (Spec (.of k)) hS
      ((OverShriek.relocalizePresheafFunctor a).obj
        ((OverShriek.relocalizeRestrict a).obj X))) :=
    hhX.surjective.connectedSpace hhX.continuous
  -- `|X|` is nonempty, and `|Spec A'|` is a single point, so `p` is surjective on points
  have hne : Nonempty (points B (Spec (.of k)) hS X) :=
    ⟨pointsMap B (Spec (.of k)) hS _ (OverShriek.relocalizeRestrictCounit a X)
      (Classical.choice hΛX.toNonempty)⟩
  have hTsub : Subsingleton (points B (Spec (.of k)) hS (yoneda.obj T)) :=
    have : Subsingleton ((BigFppfOver.toScheme B (Spec (.of k)) hS).obj T) :=
      ⟨fun x y => Subsingleton.elim (α := PrimeSpectrum A') x y⟩
    (schemePointsHomeomorph B (Spec (.of k)) hS T).injective.subsingleton
  have hpsurj : Function.Surjective (pointsMap B (Spec (.of k)) hS X p) :=
    fun _ => ⟨Classical.choice hne, Subsingleton.elim _ _⟩
  -- Tag 03MH: the base change of `p` along `Spec k' ⟶ Spec k` is surjective on points
  have husurj := surjective_pointsMap_of_isPullback B (Spec (.of k)) hS
    (OverShriek.isPullback_map_relocalizeRestrictCounit a p) hpsurj
  have hΛY : ConnectedSpace (points B (Spec (.of k)) hS
      ((OverShriek.relocalizePresheafFunctor a).obj
        ((OverShriek.relocalizeRestrict a).obj (yoneda.obj T)))) :=
    husurj.connectedSpace (continuous_pointsMap B (Spec (.of k)) hS _)
  -- and its target is the spectrum of `A' ⊗_k k'`
  have hc := OverShriek.isPullback_relocalizeRestrictCounit a (yoneda.obj T)
    OverShriek.subsingleton_yoneda_obj_mkId (OverShriek.toYonedaMkId (yoneda.obj T))
    (OverShriek.toYonedaMkId (yoneda.obj (Over.mk a)))
  rw [toYonedaMkId_yoneda_obj T, toYonedaMkId_yoneda_obj (Over.mk a)] at hc
  have hfin := (pointsHomeomorphOfIso B (Spec (.of k)) hS hc.isoPullback).trans
    (pointsPullbackSpecHomeomorph k B hS A' hA' k' hk')
  exact hfin.surjective.connectedSpace hfin.continuous

end Descent

section Tag0DMY

attribute [local instance] pointTopology

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hS X)
    (f : X ⟶ yoneda.obj (baseObject k B hS))

include hX

/-- **The global functions of a proper geometrically reduced and geometrically connected
algebraic space with finite dimensional global functions are the constants.**

`|X|` is connected by
`AlgebraicGeometry.Space.connectedSpace_points_of_isGeometricallyConnected`, so a componentwise
factorization of the global functions has a single factor and identifies the global functions
with it;  that factor is a field finite and separable over `k` by
`AlgebraicGeometry.Space.isSeparable_componentFunctions_of_finite`.  Transporting it to a
`k`-algebra `A'` in the universe of the site — possible because it is finite over `k` — the
descent step
`AlgebraicGeometry.Space.connectedSpace_primeSpectrum_tensorProduct_of_isGeometricallyConnected`
applied to the extension `A'/k` itself makes `|Spec (A' ⊗_k A')|` connected, and a finite
separable extension whose tensor square has connected spectrum is trivial
(`Stacks.SeparableSelfTensor.bijective_algebraMap_of_connectedSpace`). -/
theorem bijective_baseToGlobalFunctions_of_finite (hf : IsProper B (Spec (.of k)) hS f)
    (hfin : Module.Finite k (globalFunctions B (Spec (.of k)) hS X))
    (hgr : IsGeometricallyReduced k B hS X hX)
    (hconn : IsGeometricallyConnected B k hS X) :
    Function.Bijective (baseToGlobalFunctions k B hS X) := by
  classical
  obtain ⟨fac⟩ := nonempty_componentwiseArtinianFactorization_of_isProper_of_field k B hS X hX f hf
  -- the single connected component, and the identification of the global functions with it
  have hXconn : ConnectedSpace (points B (Spec (.of k)) hS X) :=
    connectedSpace_points_of_isGeometricallyConnected k B hS X hconn
  let _ : Unique (ConnectedComponents (points B (Spec (.of k)) hS X)) :=
    uniqueOfSubsingleton (Classical.arbitrary _)
  let (c : ConnectedComponents (points B (Spec (.of k)) hS X)) :
      Algebra k (componentFunctions B (Spec (.of k)) hS X c) := fac.factorAlgebra c
  let e₀ : globalFunctions B (Spec (.of k)) hS X ≃ₐ[k]
      componentFunctions B (Spec (.of k)) hS X default :=
    fac.equivalence.trans (AlgEquiv.ofRingEquiv
      (f := RingEquiv.piUnique fun c => componentFunctions B (Spec (.of k)) hS X c)
      (fun _ => rfl))
  -- the factor is a finite separable field extension, and so are the global functions
  obtain ⟨hfield, -, hsep⟩ :=
    isSeparable_componentFunctions_of_finite k B hS X hX hfin hgr fac default
  let _ : Field (componentFunctions B (Spec (.of k)) hS X default) := hfield.toField
  let _ : Field (globalFunctions B (Spec (.of k)) hS X) :=
    (e₀.toRingEquiv.toMulEquiv.isField hfield).toField
  have : Algebra.IsSeparable k (globalFunctions B (Spec (.of k)) hS X) :=
    AlgEquiv.Algebra.isSeparable e₀.symm
  -- a model of the global functions in the universe of the site
  have : Small.{u} (globalFunctions B (Spec (.of k)) hS X) :=
    Module.Finite.small (R := k) (M := globalFunctions B (Spec (.of k)) hS X)
  let eA : Shrink.{u} (globalFunctions B (Spec (.of k)) hS X) ≃ₐ[k]
      globalFunctions B (Spec (.of k)) hS X :=
    Shrink.algEquiv k (globalFunctions B (Spec (.of k)) hS X)
  have := Module.Finite.equiv (R := k) eA.symm.toLinearEquiv
  have : Algebra.IsSeparable k (Shrink.{u} (globalFunctions B (Spec (.of k)) hS X)) :=
    AlgEquiv.Algebra.isSeparable eA.symm
  have hA' : B.Contains (Spec (.of (Shrink.{u} (globalFunctions B (Spec (.of k)) hS X)))) :=
    Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit k _ hS
  -- the descent step at the extension `A'/k` itself
  have hconnSq := connectedSpace_primeSpectrum_tensorProduct_of_isGeometricallyConnected k B hS
    X hX (Shrink.{u} (globalFunctions B (Spec (.of k)) hS X)) hA' hconn eA.symm _ hA'
  have hbij : Function.Bijective
      (algebraMap k (Shrink.{u} (globalFunctions B (Spec (.of k)) hS X))) :=
    Stacks.SeparableSelfTensor.bijective_algebraMap_of_connectedSpace k _ hconnSq
  -- transport back along the model
  have hcomp : (baseToGlobalFunctions k B hS X : k → globalFunctions B (Spec (.of k)) hS X) =
      eA ∘ algebraMap k (Shrink.{u} (globalFunctions B (Spec (.of k)) hS X)) := by
    rw [← algebraMap_globalFunctions k B hS X]
    funext x
    exact (eA.commutes x).symm
  rw [show (baseToGlobalFunctions k B hS X : k → globalFunctions B (Spec (.of k)) hS X) =
    _ from hcomp]
  exact eA.bijective.comp hbij

omit hX in
/-- **A geometrically integral algebraic space is geometrically reduced and geometrically
connected.**  It is geometrically irreducible
(`AlgebraicGeometry.Space.IsGeometricallyIntegral.isGeometricallyIrreducible`), hence
geometrically connected, every base change having an irreducible and so connected point space;
and it is geometrically reduced, by the argument of Tag 0DMX — the base change to an algebraic
closure of `k` is reduced, and reducedness there is geometric reducedness over `k`. -/
theorem isGeometricallyReduced_and_isGeometricallyConnected_of_isGeometricallyIntegral
    (hX : IsAlgebraicSpace B (Spec (.of k)) hS X) (hint : IsGeometricallyIntegral B k hS X) :
    IsGeometricallyReduced k B hS X hX ∧ IsGeometricallyConnected B k hS X := by
  refine ⟨?_, ?_⟩
  · have hK := contains_specAlgebraicClosure B k hS
    refine (isGeometricallyReduced_fieldBaseChange_iff B k hS X (AlgebraicClosure k) hK hX).mpr ?_
    exact isGeometricallyReduced_of_isReduced (AlgebraicClosure k) B hK _
      (isAlgebraicSpace_fieldBaseChange B k hS X hX (AlgebraicClosure k) hK)
      (hint (AlgebraicClosure k) hK).1
  · intro K _ _ hK
    rw [← specMapOfExtension_eq_fieldExtensionMap B k hS K hK]
    exact (hint.isGeometricallyIrreducible K hK).connectedSpace

end Tag0DMY

end AlgebraicGeometry.Space

end
