module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethDeRhamScalars
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethDeRhamIso
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethTensorScalars
public import StacksFrontier.AlgebraicGeometry.Varieties.KunnethUnconditional

/-!
# Axiom (A5) for de Rham cohomology: the Künneth formula in cup-product form

Let `k` be a field and let `X`, `Y` be smooth proper schemes over `k`, with fibre product
`X ×_k Y` and projections `p`, `q`. Axiom (A5) of Weil cohomology theories
([Stacks, Section 0FID]), for de Rham cohomology ([Stacks, Section 0FWC]), asks that

`⨁_{i + j = n} H^i_{dR}(X/k) ⊗_k H^j_{dR}(Y/k) ⟶ H^n_{dR}(X ×_k Y/k)`,  `x ⊗ y ↦ p^*x ∪ q^*y`

be an isomorphism. The source deduces it from the Künneth formula of [Stacks, Tag 0FMB],
observing that the derived tensor product over the field `k` is harmless. This file proves it.

## Main definitions

* `Stacks.WeilDeRham.deRhamScalars`: the ring map `k = Γ(Spec k, 𝒪) ⟶ Γ(X, s^{-1}𝒪)` through
  which relative de Rham cohomology is a `k`-module.
* `Stacks.WeilDeRham.deRhamModule`: `H^n_{dR}(X/k)` as a `k`-module.
* `Stacks.WeilDeRham.deRhamPullLinear`: the pullback `f^*` of [Stacks, Section 0FL6] as a
  `k`-linear map, for a morphism over `k`.
* `Stacks.WeilDeRham.deRhamCupLinear`: the cup product as a `k`-bilinear map.
* `Stacks.WeilDeRham.kunnethCupMap`: the map `x ⊗ y ↦ p^*x ∪ q^*y`.

## Main results

* `Stacks.WeilDeRham.bijective_kunnethCupMap`: **axiom (A5), the Künneth formula: the map
  `⨁_{i + j = n} H^i_{dR}(X/k) ⊗_k H^j_{dR}(Y/k) ⟶ H^n_{dR}(X ×_k Y/k)`, `x ⊗ y ↦ p^*x ∪ q^*y`,
  is bijective.**

## The argument

The de Rham Künneth map of [Stacks, Tag 0FMB], formed with the global cup product of
[Stacks, Section 0FKU] on the base, is an isomorphism in `D(Γ(Spec k, 𝒪))`
(`Stacks.WeilDeRham.isIso_deRhamGlobalKunnethMap_cupProductOnSpace`). Over the field
`Γ(Spec k, 𝒪) ≅ k` the sum of the cohomology products is bijective
(`Stacks.WeilDeRham.bijective_kunnethSum_of_isField`). On cohomology the Künneth map carries the
cohomology product of two classes to the cup product of their pullbacks
(`Stacks.WeilDeRham.deRhamGlobalKunnethMap_crossProduct`). The tensor products over
`Γ(Spec k, 𝒪)` and over `k` are compared along the ring isomorphism
(`Stacks.WeilDeRham.bijective_tensorMapOfSemilinear`).

## References

* [Stacks Project, Section 0FWC](https://stacks.math.columbia.edu/tag/0FWC)
* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0FMB](https://stacks.math.columbia.edu/tag/0FMB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.BoxKunneth
open Stacks.Cohomology.DerivedGlobalCupProduct Stacks.Cohomology.LerayCupPairing
open scoped TensorProduct DirectSum

universe u


namespace Stacks.WeilDeRham

variable {k : Type u} [Field k]

section Modules

variable {V : Scheme.{u}} (c : V ⟶ Spec (.of k))

/-- **The ring map `k ⟶ Γ(V, c^{-1}𝒪)`**: the inverse of `Γ(Spec k, 𝒪) ≅ k`, followed by the unit
of the inverse-image adjunction on global sections
(`AlgebraicGeometry.Scheme.Hom.inverseImageGlobalSections`). -/
def deRhamScalars : k →+* (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{u} c.base).obj (Spec (.of k)).sheaf)).obj.obj (op ⊤) :=
  (Scheme.Hom.inverseImageGlobalSections c).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

/-- **Relative de Rham cohomology `H^n_{dR}(V/k)` as a `k`-module**, through `deRhamScalars`. -/
abbrev deRhamModule (n : ℤ) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (deRhamScalars c)).obj
    (AlgebraicGeometry.SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras c)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras c)) n)

/-- `H^n_{dR}(V/k)` read in another, equal, degree. -/
def deRhamCastLinear {m n : ℤ} (h : m = n) : deRhamModule c m →ₗ[k] deRhamModule c n := by
  subst h
  exact LinearMap.id

/-- **The cup product as a `k`-bilinear map**
`H^i_{dR}(V/k) × H^j_{dR}(V/k) ⟶ H^{i + j}_{dR}(V/k)`: it is bilinear over `Γ(V, c^{-1}𝒪)`, hence
over `k`. -/
def deRhamCupLinear (i j : ℤ) :
    deRhamModule c i →ₗ[k] deRhamModule c j →ₗ[k] deRhamModule c (i + j) :=
  LinearMap.mk₂ k
    (fun x y => AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup (Scheme.Hom.deRhamAlgebras c)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras c)) i j x y)
    (fun x x' y => AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup_add_left _ _ i j x x' y)
    (fun r x y => AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup_smul_left _ _ i j
      (deRhamScalars c r) x y)
    (fun x y y' => AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup_add_right _ _ i j x y y')
    (fun r x y => AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup_smul_right _ _ i j
      (deRhamScalars c r) x y)

end Modules

section Pull

variable {X X' : Scheme.{u}} (g' : X' ⟶ X) (c : X ⟶ Spec (.of k)) (c' : X' ⟶ Spec (.of k))
  (w : g' ≫ c = c' ≫ 𝟙 (Spec (.of k)))

/-- **The pullback `g'^* : H^n_{dR}(X/k) ⟶ H^n_{dR}(X'/k)` along a morphism over `k` is
`k`-linear.** The pullback of [Stacks, Section 0FL6], read in the realization in which the cup
product lives, is semilinear along `Γ(X, c^{-1}𝒪) ⟶ Γ(X', c'^{-1}𝒪)`, which is compatible with
the two maps from `k`. -/
def deRhamPullLinear (n : ℤ) : deRhamModule c n →ₗ[k] deRhamModule c' n where
  toFun x := deRhamPull g' c c' (𝟙 _) w n x
  map_add' x y := deRhamPull_add g' c c' (𝟙 _) w n x y
  map_smul' r x := by
    refine (deRhamPull_smul g' c c' (𝟙 _) w n (deRhamScalars c r) x).trans ?_
    exact congrArg (· • deRhamPull g' c c' (𝟙 _) w n x)
      (congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of k)).inv.hom r))
        (globalRingHom_inverseImageBaseMap_comp g' c c' w))

/-- `deRhamPullLinear g' c c' w n` sends a class `x` to its pullback
`deRhamPull g' c c' (𝟙 _) w n x`. -/
theorem deRhamPullLinear_apply (n : ℤ) (x : deRhamModule c n) :
    deRhamPullLinear g' c c' w n x = deRhamPull g' c c' (𝟙 _) w n x :=
  rfl

end Pull

section Kunneth

variable {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))

/-- **The Künneth map in cup-product form**
`⨁_{i + j = n} H^i_{dR}(X/k) ⊗_k H^j_{dR}(Y/k) ⟶ H^n_{dR}(X ×_k Y/k)`, `x ⊗ y ↦ p^*x ∪ q^*y`,
with `p` and `q` the two projections of the fibre product. -/
def kunnethCupMap (n : ℤ) :
    (⨁ ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n},
        deRhamModule sX ij.1.1 ⊗[k] deRhamModule sY ij.1.2) →ₗ[k]
      deRhamModule (pullback.fst sX sY ≫ sX) n :=
  DirectSum.toModule k _ _ fun ij =>
    deRhamCastLinear (pullback.fst sX sY ≫ sX) ij.2 ∘ₗ
      TensorProduct.lift ((deRhamCupLinear (pullback.fst sX sY ≫ sX) ij.1.1 ij.1.2).compl₁₂
        (deRhamPullLinear (pullback.fst sX sY) sX (pullback.fst sX sY ≫ sX) (fst_comp_eq sX sY)
          ij.1.1)
        (deRhamPullLinear (pullback.snd sX sY) sY (pullback.fst sX sY ≫ sX) (snd_comp_eq sX sY)
          ij.1.2))

/-- The Künneth map on a summand, on a pure tensor. -/
theorem kunnethCupMap_lof_tmul (n : ℤ) (ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n})
    (x : deRhamModule sX ij.1.1) (y : deRhamModule sY ij.1.2) :
    kunnethCupMap sX sY n (DirectSum.lof k _ _ ij (x ⊗ₜ y)) =
      deRhamCastLinear (pullback.fst sX sY ≫ sX) ij.2
        (deRhamCupLinear (pullback.fst sX sY ≫ sX) ij.1.1 ij.1.2
          (deRhamPullLinear (pullback.fst sX sY) sX (pullback.fst sX sY ≫ sX) (fst_comp_eq sX sY)
            ij.1.1 x)
          (deRhamPullLinear (pullback.snd sX sY) sY (pullback.fst sX sY ≫ sX) (snd_comp_eq sX sY)
            ij.1.2 y)) := by
  rw [kunnethCupMap, DirectSum.toModule_lof, LinearMap.comp_apply, TensorProduct.lift.tmul]
  rfl

end Kunneth

section Main

variable {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))

/-- `Γ(Spec k, 𝒪)` is a field, being isomorphic to `k`. -/
theorem isField_gammaSpec : IsField (baseRing (Spec (.of k)).toRingedSpace) :=
  (AlgebraicGeometry.gammaSectionsRingEquiv k).toMulEquiv.isField (Field.toIsField k)

/-- The identification of the cohomology of `RΓ(V, Ω^•_{V/k})` over `Γ(Spec k, 𝒪)` with
`H^n_{dR}(V/k)`, as an additive bijection onto the `k`-module. -/
def deRhamClassAddEquiv {V : Scheme.{u}} (c : V ⟶ Spec (.of k)) (n : ℤ) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) n).obj
        ((sectionsOverBase (inverseImageBaseProjection c)).obj
          (DerivedCategory.Q.obj (leftComplex c (Scheme.Hom.deRhamDiffOpCochainComplex c)))) ≃+
      deRhamModule c n :=
  letI := @HasDerivedCategory.standard.{u, u + 1}
  (deRhamClassIso c n).toLinearEquiv.toAddEquiv

/-- The identification is semilinear along `k ≅ Γ(Spec k, 𝒪)`. -/
theorem deRhamClassAddEquiv_smul {V : Scheme.{u}} (c : V ⟶ Spec (.of k)) (n : ℤ) (r : k)
    (m : letI := @HasDerivedCategory.standard.{u, u + 1};
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace))
      n).obj ((sectionsOverBase (inverseImageBaseProjection c)).obj
        (DerivedCategory.Q.obj (leftComplex c (Scheme.Hom.deRhamDiffOpCochainComplex c))))) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    deRhamClassAddEquiv c n ((AlgebraicGeometry.gammaSectionsRingEquiv k).symm r • m) =
      r • deRhamClassAddEquiv c n m :=
  let := @HasDerivedCategory.standard.{u, u + 1}
  (deRhamClassIso c n).hom.hom.map_smul _ m

/-- `deRhamGlobalKunnethMap_crossProduct` in a degree `n` with `i + j = n`. -/
theorem deRhamGlobalKunnethMap_crossProductCast (i j n : ℤ) (h : i + j = n)
    (x : deRhamModule sX i) (y : deRhamModule sY j) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (deRhamClassIso (pullback.fst sX sY ≫ sX) n).hom
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace))
          n).map
            (deRhamGlobalKunnethMap sX sY (cupProductOnSpace (Spec (.of k)).toRingedSpace))).hom
        ((crossProductCast _ _ i j n h).hom
          ((deRhamClassIso sX i).inv x ⊗ₜ (deRhamClassIso sY j).inv y))) =
      deRhamCastLinear (pullback.fst sX sY ≫ sX) h
        (deRhamCupLinear (pullback.fst sX sY ≫ sX) i j
          (deRhamPullLinear (pullback.fst sX sY) sX (pullback.fst sX sY ≫ sX) (fst_comp_eq sX sY)
            i x)
          (deRhamPullLinear (pullback.snd sX sY) sY (pullback.fst sX sY ≫ sX) (snd_comp_eq sX sY)
            j y)) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  subst h
  exact deRhamGlobalKunnethMap_crossProduct sX sY isField_gammaSpec i j x y

/-- The de Rham Künneth map of [Stacks, Tag 0FMB] on cohomology, preceded by the sum of the
cohomology products over `Γ(Spec k, 𝒪)` and followed by the identification with `H^n_{dR}`. -/
def deRhamKunnethAddHom (n : ℤ) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (⨁ ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n},
        TensorProduct (baseRing (Spec (.of k)).toRingedSpace)
          ((DerivedCategory.homologyFunctor
            (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) ij.1.1).obj
            ((sectionsOverBase (inverseImageBaseProjection sX)).obj
              (DerivedCategory.Q.obj (leftComplex sX (Scheme.Hom.deRhamDiffOpCochainComplex sX)))))
          ((DerivedCategory.homologyFunctor
            (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) ij.1.2).obj
            ((sectionsOverBase (inverseImageBaseProjection sY)).obj
              (DerivedCategory.Q.obj
                (leftComplex sY (Scheme.Hom.deRhamDiffOpCochainComplex sY)))))) →+
      deRhamModule (pullback.fst sX sY ≫ sX) n :=
  letI := @HasDerivedCategory.standard.{u, u + 1}
  ((deRhamClassIso (pullback.fst sX sY ≫ sX) n).hom.hom.toAddMonoidHom.comp
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) n).map
          (deRhamGlobalKunnethMap sX sY
            (cupProductOnSpace (Spec (.of k)).toRingedSpace))).hom.toAddMonoidHom).comp
    (kunnethSum _ _ n).toAddMonoidHom

/-- **The de Rham Künneth map on cohomology is bijective** for `X`, `Y` smooth and proper over a
field: the sum of the cohomology products over the field `Γ(Spec k, 𝒪)` is bijective, and so is
the Künneth map of [Stacks, Tag 0FMB]. -/
theorem bijective_deRhamKunnethAddHom [AlgebraicGeometry.Smooth sX] [AlgebraicGeometry.Smooth sY]
    [IsProper sX] [IsProper sY] (n : ℤ) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    Function.Bijective (deRhamKunnethAddHom sX sY n) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  have := isIso_deRhamGlobalKunnethMap_cupProductOnSpace sX sY
  have hΨ := bijective_kunnethSum_of_isField isField_gammaSpec
    ((sectionsOverBase (inverseImageBaseProjection sX)).obj
      (DerivedCategory.Q.obj (leftComplex sX (Scheme.Hom.deRhamDiffOpCochainComplex sX))))
    ((sectionsOverBase (inverseImageBaseProjection sY)).obj
      (DerivedCategory.Q.obj (leftComplex sY (Scheme.Hom.deRhamDiffOpCochainComplex sY)))) n
  have hD : Function.Bijective ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) n).map
        (deRhamGlobalKunnethMap sX sY (cupProductOnSpace (Spec (.of k)).toRingedSpace))).hom :=
    ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) n).mapIso
        (asIso (deRhamGlobalKunnethMap sX sY
          (cupProductOnSpace (Spec (.of k)).toRingedSpace)))).toLinearEquiv.bijective
  have hE : Function.Bijective (deRhamClassIso (pullback.fst sX sY ≫ sX) n).hom :=
    (deRhamClassIso (pullback.fst sX sY ≫ sX) n).toLinearEquiv.bijective
  exact hE.comp (hD.comp hΨ)

/-- The Künneth map in cup-product form on a pure tensor in a summand is `deRhamKunnethAddHom` on
the corresponding pure tensor of cohomology classes of `RΓ(X, Ω^•_{X/k})` and
`RΓ(Y, Ω^•_{Y/k})`. -/
theorem kunnethCupMap_of_tmul (n : ℤ) (ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n})
    (x : deRhamModule sX ij.1.1) (y : deRhamModule sY ij.1.2) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    kunnethCupMap sX sY n (DirectSum.of _ ij (x ⊗ₜ y)) =
      deRhamKunnethAddHom sX sY n (DirectSum.of _ ij
        ((deRhamClassAddEquiv sX ij.1.1).symm x ⊗ₜ (deRhamClassAddEquiv sY ij.1.2).symm y)) :=
  let := @HasDerivedCategory.standard.{u, u + 1}
  (kunnethCupMap_lof_tmul sX sY n ij x y).trans
    ((deRhamGlobalKunnethMap_crossProductCast sX sY ij.1.1 ij.1.2 n ij.2 x y).symm.trans
      (congrArg (fun z => (deRhamClassIso (pullback.fst sX sY ≫ sX) n).hom
        (((DerivedCategory.homologyFunctor
          (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) n).map
            (deRhamGlobalKunnethMap sX sY (cupProductOnSpace (Spec (.of k)).toRingedSpace))).hom z))
        (kunnethSum_of _ _ n ij _).symm))

/-- **Axiom (A5) for de Rham cohomology, the Künneth formula** ([Stacks, Section 0FWC], axiom (A5)
of [Stacks, Section 0FID]). Let `k` be a field and `X`, `Y` smooth proper schemes over `k`, with
projections `p`, `q` of the fibre product `X ×_k Y`. For every `n : ℤ` the `k`-linear map

`⨁_{i + j = n} H^i_{dR}(X/k) ⊗_k H^j_{dR}(Y/k) ⟶ H^n_{dR}(X ×_k Y/k)`,  `x ⊗ y ↦ p^*x ∪ q^*y`

is bijective. -/
theorem bijective_kunnethCupMap [AlgebraicGeometry.Smooth sX] [AlgebraicGeometry.Smooth sY]
    [IsProper sX] [IsProper sY] (n : ℤ) :
    Function.Bijective (kunnethCupMap sX sY n) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  rw [← LinearMap.toAddMonoidHom_coe]
  exact bijective_of_directSum_tensorMapOfSemilinear
    (AlgebraicGeometry.gammaSectionsRingEquiv k).symm
    (ι := {ij : ℤ × ℤ // ij.1 + ij.2 = n})
    (M := fun ij => (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) ij.1.1).obj
        ((sectionsOverBase (inverseImageBaseProjection sX)).obj
          (DerivedCategory.Q.obj (leftComplex sX (Scheme.Hom.deRhamDiffOpCochainComplex sX)))))
    (N := fun ij => (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) ij.1.2).obj
        ((sectionsOverBase (inverseImageBaseProjection sY)).obj
          (DerivedCategory.Q.obj (leftComplex sY (Scheme.Hom.deRhamDiffOpCochainComplex sY)))))
    (M' := fun ij => deRhamModule sX ij.1.1) (N' := fun ij => deRhamModule sY ij.1.2)
    (fun ij => deRhamClassAddEquiv sX ij.1.1) (fun ij => deRhamClassAddEquiv_smul sX ij.1.1)
    (fun ij => deRhamClassAddEquiv sY ij.1.2) (fun ij => deRhamClassAddEquiv_smul sY ij.1.2)
    (deRhamKunnethAddHom sX sY n) (bijective_deRhamKunnethAddHom sX sY n)
    (kunnethCupMap sX sY n).toAddMonoidHom (kunnethCupMap_of_tmul sX sY n)

end Main

end Stacks.WeilDeRham

end
