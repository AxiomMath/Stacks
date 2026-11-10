module

public import StacksFrontier.AlgebraicGeometry.Crystalline.UniversalThickeningScheme

/-!
# The structure sheaf of the first-order universal thickening splits

Let `(T, J, δ)` be a divided power scheme over a scheme `Y` and let `T'` be the first-order
universal thickening of [Stacks, Tag 07J2]: the space of `T` carrying the square-zero extension
`𝒪_{T'} = 𝒪_T ⊕ Ω_{T/Y,δ}`.  The morphism `p₀ : T' ⟶ T` is the inclusion `g ↦ (g, 0)` on
sections and `i : T ⟶ T'` is the projection `(g, ω) ↦ g`; both are the identity on the space.

Reading `𝒪_{T'}` through `p₀` makes it a sheaf of `𝒪_T`-modules, and as such it is the direct sum

`p₀_* 𝒪_{T'} ≅ Ω_{T/Y,δ} ⊞ 𝒪_T`,

the first summand being the ideal of the diagonal, that is, the kernel of the comorphism of `i`.
The splitting is `p₀` itself and the retraction onto the first summand is the second coordinate
of the square-zero extension.

## Main definitions

* `Crystalline.firstOrderThickeningUnitRestriction`: `𝒪_{T'}` read as a sheaf of
  `𝒪_T`-modules, through the comorphism of `p₀`.
* `Crystalline.firstOrderThickeningInrSheaf`: the ideal of the diagonal as a sheaf of
  `𝒪_T`-modules, the inclusion `Ω_{T/Y,δ} ⟶ p₀_* 𝒪_{T'}`, `ω ↦ (0, ω)`.
* `Crystalline.firstOrderThickeningSndSheaf`: its retraction `(g, ω) ↦ ω`.
* `Crystalline.firstOrderThickeningProjSheaf` and `Crystalline.firstOrderThickeningInlSheaf`:
  the comorphisms of `i` and of `p₀`, as morphisms of sheaves of `𝒪_T`-modules.
* `Crystalline.firstOrderThickeningStructureSplitting`: the splitting of the short complex
  `0 ⟶ Ω_{T/Y,δ} ⟶ p₀_* 𝒪_{T'} ⟶ 𝒪_T ⟶ 0`.
* `Crystalline.firstOrderThickeningStructureBiprodIso`: `p₀_* 𝒪_{T'} ≅ Ω_{T/Y,δ} ⊞ 𝒪_T`.

## Main results

* `Crystalline.exact_firstOrderThickeningStructureShortComplex`: the short complex is exact.

## References

* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open PresheafOfModules

universe u

noncomputable section

namespace Crystalline

/-- The structure sheaf of a scheme as an object of `AlgebraicGeometry.Scheme.Modules`. -/
abbrev schemeUnitModule (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)

/-- `𝒪_{T'}` as a sheaf of `𝒪_T`-modules, the scalars being read through the comorphism
`g ↦ (g, 0)` of `p₀ : T' ⟶ T`. -/
abbrev firstOrderThickeningUnitRestriction : T.scheme.Modules :=
  (Scheme.Modules.pushforward (firstOrderThickeningProjHom T Y f)).obj
    (SheafOfModules.unit (firstOrderThickeningScheme T Y f).ringCatSheaf)

/-! ### The two coordinates of a product with a section pulled back along `p₀` -/

/-- The second coordinate of `(a, 0) · x` is `a · ω`, where `x = (g, ω)`. -/
theorem sqZeroExtSnd_firstOrderThickeningP₀_mul (W : (Opens ↑T.scheme)ᵒᵖ)
    (a : T.scheme.sheaf.obj.obj W) (x : (firstOrderThickeningPresheaf T Y f).obj W) :
    sqZeroExtSnd (M := dpDifferentialsModules T Y f)
        (((firstOrderThickeningP₀ T Y f).app W).hom a * x) =
      a • sqZeroExtSnd (M := dpDifferentialsModules T Y f) x := by
  change a • sqZeroExtSnd (M := dpDifferentialsModules T Y f) x +
      sqZeroExtFst (M := dpDifferentialsModules T Y f) x •
        (0 : (dpDifferentialsModules T Y f).obj W) =
    a • sqZeroExtSnd (M := dpDifferentialsModules T Y f) x
  rw [smul_zero, add_zero]

/-- The first coordinate of `(a, 0) · x` is `a · g`, where `x = (g, ω)`. -/
theorem sqZeroExtFst_firstOrderThickeningP₀_mul (W : (Opens ↑T.scheme)ᵒᵖ)
    (a : T.scheme.sheaf.obj.obj W) (x : (firstOrderThickeningPresheaf T Y f).obj W) :
    sqZeroExtFst (M := dpDifferentialsModules T Y f)
        (((firstOrderThickeningP₀ T Y f).app W).hom a * x) =
      a * sqZeroExtFst (M := dpDifferentialsModules T Y f) x := rfl

/-! ### The ideal of the diagonal and its retraction -/

/-- The inclusion `ω ↦ (0, ω)` of the square-zero summand, as a morphism of the underlying
presheaves of abelian groups. -/
def firstOrderThickeningInrPresheaf :
    (dpDifferentialsSheaf T Y f).val.presheaf ⟶
      (firstOrderThickeningUnitRestriction T Y f).val.presheaf where
  app W := AddCommGrpCat.ofHom (firstOrderThickeningInr T Y f W)
  naturality _ _ _ := by
    ext ω
    exact sqZeroExt_ext (map_zero _).symm rfl

/-- The ideal of the diagonal as a sheaf of `𝒪_T`-modules: the inclusion
`Ω_{T/Y,δ} ⟶ p₀_* 𝒪_{T'}`, `ω ↦ (0, ω)`. -/
def firstOrderThickeningInrSheaf :
    dpDifferentialsSheaf T Y f ⟶ firstOrderThickeningUnitRestriction T Y f :=
  ⟨PresheafOfModules.homMk (firstOrderThickeningInrPresheaf T Y f) fun W a ω ↦
    (mul_firstOrderThickeningInr T Y f W (((firstOrderThickeningP₀ T Y f).app W).hom a) ω).symm⟩

/-- The inclusion `firstOrderThickeningInrSheaf` is `ω ↦ (0, ω)` on sections. -/
@[simp]
theorem firstOrderThickeningInrSheaf_val_app (W : (Opens ↑T.scheme)ᵒᵖ)
    (ω : (dpDifferentialsSheaf T Y f).val.obj W) :
    (firstOrderThickeningInrSheaf T Y f).val.app W ω = firstOrderThickeningInr T Y f W ω := rfl

/-- The second coordinate `(g, ω) ↦ ω` of the square-zero extension, as a morphism of the
underlying presheaves of abelian groups. -/
def firstOrderThickeningSndPresheaf :
    (firstOrderThickeningUnitRestriction T Y f).val.presheaf ⟶
      (dpDifferentialsSheaf T Y f).val.presheaf where
  app _ := AddCommGrpCat.ofHom
    { toFun x := sqZeroExtSnd (M := dpDifferentialsModules T Y f) x
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ _ := rfl

/-- The retraction `(g, ω) ↦ ω` of the ideal of the diagonal, as a morphism of sheaves of
`𝒪_T`-modules. -/
def firstOrderThickeningSndSheaf :
    firstOrderThickeningUnitRestriction T Y f ⟶ dpDifferentialsSheaf T Y f :=
  ⟨PresheafOfModules.homMk (firstOrderThickeningSndPresheaf T Y f)
    (sqZeroExtSnd_firstOrderThickeningP₀_mul T Y f)⟩

/-! ### The comorphisms of `i` and of `p₀` as morphisms of modules -/

/-- The comorphism `(g, ω) ↦ g` of the diagonal `i : T ⟶ T'`, as a morphism of sheaves of
`𝒪_T`-modules `p₀_* 𝒪_{T'} ⟶ 𝒪_T`. -/
def firstOrderThickeningProjSheaf :
    firstOrderThickeningUnitRestriction T Y f ⟶
      schemeUnitModule T.scheme :=
  ⟨PresheafOfModules.homMk
    { app _ := AddCommGrpCat.ofHom
        { toFun x := sqZeroExtFst (M := dpDifferentialsModules T Y f) x
          map_zero' := rfl
          map_add' _ _ := rfl }
      naturality _ _ _ := rfl }
    (sqZeroExtFst_firstOrderThickeningP₀_mul T Y f)⟩

/-- The comorphism `g ↦ (g, 0)` of `p₀ : T' ⟶ T`, as a morphism of sheaves of
`𝒪_T`-modules `𝒪_T ⟶ p₀_* 𝒪_{T'}`. -/
def firstOrderThickeningInlSheaf :
    schemeUnitModule T.scheme ⟶
      firstOrderThickeningUnitRestriction T Y f :=
  ⟨PresheafOfModules.homMk
    { app W := AddCommGrpCat.ofHom ((firstOrderThickeningP₀ T Y f).app W).hom.toAddMonoidHom
      naturality _ _ i := by
        ext a
        exact congrArg (fun k ↦ (CommRingCat.Hom.hom k) a)
          ((firstOrderThickeningP₀ T Y f).naturality i) }
    (fun W a x ↦ map_mul ((firstOrderThickeningP₀ T Y f).app W).hom a x)⟩

/-! ### The splitting -/

/-- The short complex `0 ⟶ Ω_{T/Y,δ} ⟶ p₀_* 𝒪_{T'} ⟶ 𝒪_T ⟶ 0` of sheaves of
`𝒪_T`-modules. -/
def firstOrderThickeningStructureShortComplex : ShortComplex T.scheme.Modules :=
  ShortComplex.mk (firstOrderThickeningInrSheaf T Y f) (firstOrderThickeningProjSheaf T Y f) (by
    ext W x
    rfl)

/-- The splitting of the short complex of the square-zero extension, with retraction the second
coordinate and section the comorphism of `p₀`. -/
def firstOrderThickeningStructureSplitting :
    (firstOrderThickeningStructureShortComplex T Y f).Splitting where
  r := firstOrderThickeningSndSheaf T Y f
  s := firstOrderThickeningInlSheaf T Y f
  f_r := by
    ext W x
    rfl
  s_g := by
    ext W x
    rfl
  id := by
    ext W x
    exact sqZeroExt_ext (zero_add _) (add_zero _)

/-- The isomorphism `p₀_* 𝒪_{T'} ≅ Ω_{T/Y,δ} ⊞ 𝒪_T` of sheaves of `𝒪_T`-modules. -/
def firstOrderThickeningStructureBiprodIso :
    firstOrderThickeningUnitRestriction T Y f ≅
      dpDifferentialsSheaf T Y f ⊞
        schemeUnitModule T.scheme :=
  (firstOrderThickeningStructureSplitting T Y f).isoBinaryBiproduct

/-- The short complex `0 ⟶ Ω_{T/Y,δ} ⟶ p₀_* 𝒪_{T'} ⟶ 𝒪_T ⟶ 0` is exact. -/
theorem exact_firstOrderThickeningStructureShortComplex :
    (firstOrderThickeningStructureShortComplex T Y f).Exact :=
  (firstOrderThickeningStructureSplitting T Y f).exact

/-- The inclusion of `Ω_{T/Y,δ}` is a kernel of the comorphism of the diagonal `i : T ⟶ T'`, as
sheaves of `𝒪_T`-modules. -/
def isLimitKernelFork_firstOrderThickeningInrSheaf :
    IsLimit (KernelFork.ofι (firstOrderThickeningInrSheaf T Y f)
      (firstOrderThickeningStructureShortComplex T Y f).zero) :=
  (firstOrderThickeningStructureSplitting T Y f).fIsKernel

end Crystalline

end

end
