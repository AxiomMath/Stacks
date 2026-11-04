module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjShiftedSectionScalar
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison

/-!
# Shifted global sections pulled back along a morphism into `Proj`, and their linearity

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a nonnegatively graded ring, `M = ⨁_{i ∈ ℤ} 𝒨 i` a graded
`S`-module, and `h : Y ⟶ Proj 𝒮` a morphism of schemes. A homogeneous element `m` of degree `n`
names a global section `Stacks.AlgebraicGeometry.ProjShiftedSections.degreeNToGlobalSections` of
`M(n)~` on `Proj 𝒮`, and the unit of the adjunction `h^* ⊣ h_*` carries it to a global section
of `h^*(M(n)~)` on `Y`. This file forms that composite and proves it linear over the ring of
functions on an **affine** scheme `Z` equipped with a ring map `c : Γ(Z, 𝒪_Z) ⟶ 𝒮_0`, the
scalars acting on the target through

`f = h ≫ (Proj 𝒮 ⟶ Spec 𝒮_0 ⟶ Spec Γ(Z, 𝒪_Z) ≅ Z)`.

That linearity is what `Stacks.AlgebraicGeometry.AffineHomRecovery.homEquiv` asks for in order to
recover a morphism `f^*ℳ_n ⟶ h^*(M(n)~)` of `𝒪_Y`-modules from its effect on global sections;
additivity is not enough.

## The four steps of the linearity

The scalar travels along four identifications, and three of them were already in the tree:

1. the `Γ(Z, 𝒪_Z)`-action on homogeneous sections is the degree-zero action of the graded ring of
   sections (`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.strHom_smul_of`);
2. a degree-zero scalar acts on shifted global sections by multiplication by the function
   `π^♯(a)`, `π : Proj 𝒮 ⟶ Spec 𝒮_0` the structure morphism
   (`Stacks.AlgebraicGeometry.ProjShiftedSections.degreeNToGlobalSections_smul`);
3. the pullback unit is semilinear along `h^♯`
   (`Stacks.RingedSpace.pullbackUnit_smul`);
4. `h^♯(π^♯(c r)) = f^♯ r`, which is `appTop_structureComposite` below.

Step 4 is pure `Scheme.Hom.appTop` bookkeeping: `appTop` is contravariantly functorial, the
`appTop` of `Z.isoSpec.inv` is the inverse of the `Γ`-`Spec` unit at `Γ(Z, 𝒪_Z)`
(`isoSpec_inv_appTop`), and `Scheme.ΓSpecIso_inv_naturality` moves `c` across `Spec.map c`. No
geometry enters; the geometric content of the composite — that `f` is the morphism a triple
recovers from its degree-zero part — is
`Stacks.AlgebraicGeometry.ProjTripleStructureMorphism.toProj_comp_toSpecZero_over_affine`, and
nothing of it is needed here.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjShiftedSections.degreeZeroPullbackHom`: the ring map
  `𝒮_0 ⟶ Γ(Proj 𝒮, 𝒪)` of the structure morphism, bundled.
* `Stacks.AlgebraicGeometry.ProjShiftedSections.pullbackDegreeN`: **the global section of
  `h^*(M(n)~)` attached to a homogeneous element of degree `n`.**
* `Stacks.AlgebraicGeometry.ProjShiftedSections.structureCompositeSharp`: the function `f^♯ r`,
  named at the type the scalars of the pullback module take.

## Main results

* `Stacks.AlgebraicGeometry.ProjShiftedSections.appTop_structureComposite`: **step 4**, the
  factorisation `f^♯ = c ≫ π^♯ ≫ h^♯` of the global sections of the structure composite.
* `Stacks.AlgebraicGeometry.ProjShiftedSections.pullbackDegreeN_add` and
  `pullbackDegreeN_smul`: additivity, and semilinearity along `h^♯ ∘ π^♯` in a degree-zero
  scalar.
* `Stacks.AlgebraicGeometry.ProjShiftedSections.pullbackDegreeN_smul_appTop`: **the four steps
  composed** — the section attached to `(c r) · m` is `f^♯ r` times the section attached to `m`.

## Implementation notes

`pullbackDegreeN` lands in the sections over `h^{-1}⊤` rather than over `⊤`: that is the open at
which `Stacks.RingedSpace.pullbackUnit` produces its value, and it is `⊤` definitionally, so no
transport along an equality of opens appears anywhere below. It is also the open at which
`Stacks.AlgebraicGeometry.AffineHomRecovery.pushforward_sectionsTop_eq` reads the sections of
`f_*h^*(M(n)~)` over `⊤`, which is why the composite can be handed to `homEquiv` directly.

`structureCompositeSharp` is a named `def` with a declared type, not a type ascription on
`f.appTop r`: the scalar type `Γ(Y, h^{-1}⊤)` has to be presented as
`(structureRingSheaf Y).obj.obj (h^{-1}⊤)` for the `HSMul` instance of the sections of a sheaf of
modules to be found, and `inferType` on an ascribed term keeps the term's own type. This is the
cure recorded for `pullbackDegreeZero` in
`StacksFrontier.AlgebraicGeometry.Constructions.ProjShiftedSectionScalar`.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01O6](https://stacks.math.columbia.edu/tag/01O6)
* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheaf)
open Stacks.GradedModule (shiftedGrading)
open RingedSpaceModuleAdjunction (opensMap)
open scoped Stacks.GradedLocalization

universe u w t

namespace Stacks.AlgebraicGeometry.ProjShiftedSections

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **The ring map `𝒮_0 ⟶ Γ(Proj 𝒮, 𝒪)` of the structure morphism**, bundled as a morphism of
`CommRingCat`: the inverse of the `Γ`-`Spec` unit at `𝒮_0` followed by the global sections of
`π : Proj 𝒮 ⟶ Spec 𝒮_0`. Its value on a degree-zero element is the function
`Stacks.AlgebraicGeometry.ProjShiftedSections.pullbackDegreeZero`, whose value at every point of
`Proj 𝒮` is the fraction `a / 1`. -/
def degreeZeroPullbackHom :
    CommRingCat.of (𝒮 0) ⟶ Γ(AlgebraicGeometry.Proj 𝒮, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (𝒮 0))).inv ≫ (AlgebraicGeometry.Proj.toSpecZero 𝒮).appTop

/-- The bundled ring map and the function of `pullbackDegreeZero` agree; the two differ only in
the spelling of the global functions on `Proj 𝒮`, which is `Γ(Proj 𝒮, ⊤)` for `Scheme.Hom.appTop`
and the structure sheaf of the projective spectrum for the sections of an associated module
sheaf. -/
theorem degreeZeroPullbackHom_apply (a : 𝒮 0) :
    degreeZeroPullbackHom 𝒮 a = pullbackDegreeZero 𝒮 a := rfl

variable {Y Z : Scheme.{u}} [IsAffine Z] (c : Γ(Z, ⊤) ⟶ CommRingCat.of (𝒮 0))

/-- **The global sections of the inverse of `Z ≅ Spec Γ(Z, 𝒪_Z)`** are the inverse of the
`Γ`-`Spec` unit at `Γ(Z, 𝒪_Z)`. Mathlib has this for an affine *open*
(`AlgebraicGeometry.IsAffineOpen.isoSpec_inv_appTop`) but not for an affine scheme; it follows
from `AlgebraicGeometry.Scheme.toSpecΓ_appTop` by cancelling the forward map. -/
theorem isoSpec_inv_appTop : Z.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Z, ⊤)).inv := by
  rw [← cancel_mono (Scheme.ΓSpecIso Γ(Z, ⊤)).hom, Iso.inv_hom_id]
  have h : Z.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(Z, ⊤)).hom := by
    rw [Scheme.isoSpec, asIso_hom, Scheme.toSpecΓ_appTop]
  rw [← h, ← Scheme.Hom.comp_appTop, Z.isoSpec.hom_inv_id, Scheme.Hom.id_appTop]

/-- **Step 4 of the linearity: the global sections of the structure composite.** For a morphism
`h : Y ⟶ Proj 𝒮`, an affine scheme `Z` and a ring map `c : Γ(Z, 𝒪_Z) ⟶ 𝒮_0`, the morphism

`f = h ≫ π ≫ Spec.map c ≫ (Spec Γ(Z, 𝒪_Z) ≅ Z)`

induces on global sections the composite `c` followed by the structure map `𝒮_0 ⟶ Γ(Proj 𝒮, 𝒪)`
followed by `h^♯`. Elementwise this is `f^♯ r = h^♯(π^♯(c r))`, the last of the four steps the
linearity of the canonical map `f^*ℳ_n ⟶ h^*(M(n)~)` on global sections is made of.

It is `Scheme.Hom.appTop` functoriality and `AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality`;
no property of `Proj 𝒮` is used, so `h` and `c` are arbitrary. -/
theorem appTop_structureComposite (h : Y ⟶ AlgebraicGeometry.Proj 𝒮) :
    (h ≫ AlgebraicGeometry.Proj.toSpecZero 𝒮 ≫ Spec.map c ≫ Z.isoSpec.inv).appTop
      = c ≫ degreeZeroPullbackHom 𝒮 ≫ h.appTop := by
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
    isoSpec_inv_appTop, degreeZeroPullbackHom, Category.assoc, Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality_assoc, Category.assoc]

section Composite

variable {M : Type u} {τ : Type t} [AddCommGroup M] [Module S M]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-- **The global section of `h^*(M(n)~)` on `Y` attached to a homogeneous element of degree
`n`.** The element names a global section of `M(n)~` on `Proj 𝒮` by
`Stacks.AlgebraicGeometry.ProjShiftedSections.degreeNToGlobalSections`, and the unit of the
adjunction `h^* ⊣ h_*` carries that to a section of the pullback over `h^{-1}⊤`.

This is the map that, prescribed in every degree, recovers the canonical morphism
`f^*ℳ_n ⟶ h^*(M(n)~)` of property (1) of [Stacks, Tag 01O7] over an affine base. -/
def pullbackDegreeN (h : Y ⟶ AlgebraicGeometry.Proj 𝒮) (n : ℤ) (m : 𝒨 n) :
    ((Stacks.RingedSpace.pullbackFunctor h.toLRSHom.toShHom).obj
        (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 n))).val.obj
      ((opensMap h.toLRSHom.toShHom).op.obj (op ⊤)) :=
  Stacks.RingedSpace.pullbackUnit h.toLRSHom.toShHom
    (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 n)) (op ⊤)
    (degreeNToGlobalSections 𝒮 𝒨 n m)

omit [Decomposition 𝒨] in
/-- **The attached section is additive in the homogeneous element.** -/
theorem pullbackDegreeN_add (h : Y ⟶ AlgebraicGeometry.Proj 𝒮) (n : ℤ) (m m' : 𝒨 n) :
    pullbackDegreeN 𝒮 𝒨 h n (m + m')
      = pullbackDegreeN 𝒮 𝒨 h n m + pullbackDegreeN 𝒮 𝒨 h n m' := by
  unfold pullbackDegreeN
  rw [map_add]
  exact Stacks.RingedSpace.pullbackUnit_add _ _ _ _ _

omit [Decomposition 𝒨] in
/-- **Steps 2 and 3 composed: a degree-zero scalar acts through `h^♯ ∘ π^♯`.** For `a` of degree
zero and `m` of degree `n`, the section attached to `a · m` is the function `h^♯(π^♯(a))` times
the section attached to `m`.

The product `a · m` is passed as a separate homogeneous element of degree `n` together with the
equation naming it, for the reason recorded for
`Stacks.AlgebraicGeometry.ProjShiftedSections.degreeNToGlobalSections_smul`: the graded scalar
multiplication lands in degree `((0 : ℕ) : ℤ) + n`, not in `n`. -/
theorem pullbackDegreeN_smul (h : Y ⟶ AlgebraicGeometry.Proj 𝒮) (n : ℤ) (a : 𝒮 0)
    (m am : 𝒨 n) (ham : (am : M) = (a : S) • (m : M)) :
    pullbackDegreeN 𝒮 𝒨 h n am
      = Stacks.RingedSpace.sharp h.toLRSHom.toShHom (op ⊤) (degreeZeroPullbackHom 𝒮 a)
          • pullbackDegreeN 𝒮 𝒨 h n m := by
  unfold pullbackDegreeN
  rw [degreeNToGlobalSections_smul 𝒮 𝒨 n a m am ham]
  exact Stacks.RingedSpace.pullbackUnit_smul _ _ _ _ _

/-- The image of a global function under the structure map of the ringed-space morphism
underlying `h` is its image under `Scheme.Hom.appTop`, on the nose. -/
theorem sharp_eq_appTop (h : Y ⟶ AlgebraicGeometry.Proj 𝒮) (x : Γ(AlgebraicGeometry.Proj 𝒮, ⊤)) :
    Stacks.RingedSpace.sharp h.toLRSHom.toShHom (op ⊤) x = h.appTop x := rfl

/-- **The function `f^♯ r` on `Y`**, for `f` the structure composite
`h ≫ π ≫ Spec.map c ≫ (Spec Γ(Z, 𝒪_Z) ≅ Z)`, named at the type the scalars of the sections of a
pullback module take. It is `(f.appTop) r` and nothing else; what the named `def` supplies is the
declared type, which a type ascription does not. -/
def structureCompositeSharp (h : Y ⟶ AlgebraicGeometry.Proj 𝒮) (r : Γ(Z, ⊤)) :
    (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj.obj
      ((opensMap h.toLRSHom.toShHom).op.obj (op ⊤)) :=
  (h ≫ AlgebraicGeometry.Proj.toSpecZero 𝒮 ≫ Spec.map c ≫ Z.isoSpec.inv).appTop r

/-- **Step 4, elementwise**: the function `h^♯(π^♯(c r))` is `f^♯ r`. -/
theorem sharp_degreeZeroPullbackHom (h : Y ⟶ AlgebraicGeometry.Proj 𝒮) (r : Γ(Z, ⊤)) :
    Stacks.RingedSpace.sharp h.toLRSHom.toShHom (op ⊤) (degreeZeroPullbackHom 𝒮 (c r))
      = structureCompositeSharp 𝒮 c h r := by
  rw [sharp_eq_appTop, structureCompositeSharp, appTop_structureComposite 𝒮 c h]
  rfl

omit [Decomposition 𝒨] in
/-- **The four steps composed: the linearity the affine recovery asks for.** For `r` a global
function on the affine scheme `Z` and `m` a homogeneous element of degree `n`, the global section
of `h^*(M(n)~)` attached to `(c r) · m` is the function `f^♯ r` times the one attached to `m`,
where `f = h ≫ π ≫ Spec.map c ≫ (Spec Γ(Z, 𝒪_Z) ≅ Z)`.

This is the `Γ(Z, 𝒪_Z)`-linearity of `pullbackDegreeN` that
`Stacks.AlgebraicGeometry.AffineHomRecovery.homEquiv` consumes. -/
theorem pullbackDegreeN_smul_appTop (h : Y ⟶ AlgebraicGeometry.Proj 𝒮) (n : ℤ) (r : Γ(Z, ⊤))
    (m am : 𝒨 n) (ham : (am : M) = ((c r : 𝒮 0) : S) • (m : M)) :
    pullbackDegreeN 𝒮 𝒨 h n am
      = structureCompositeSharp 𝒮 c h r • pullbackDegreeN 𝒮 𝒨 h n m := by
  rw [pullbackDegreeN_smul 𝒮 𝒨 h n (c r) m am ham, sharp_degreeZeroPullbackHom]

end Composite

end Stacks.AlgebraicGeometry.ProjShiftedSections

end
