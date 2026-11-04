module

public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.FlagBundleUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.Hyperplane
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ModuleFacts

/-!
# The projective completion of a vector bundle

Let `X` be a scheme and `𝒞` a finite locally free `𝒪_X`-module of rank `r`. The projective
completion of the vector bundle of `𝒞` is

  `E = Proj_X(Sym^*(𝒞)[T]) = Proj_X(Sym^*(𝒞 ⊕ 𝒪_X))`,

the projective bundle of `𝒞 ⊕ 𝒪_X`, the variable `T` of degree one being the summand `𝒪_X`. This
file names `E`, its projection `π : E ⟶ X`, its twist `𝒪_E(1)`, the tautological surjection
`u : π^*(𝒞 ⊕ 𝒪_X) ⟶ 𝒪_E(1)` and the global section `T ∈ Γ(E, 𝒪_E(1))`, the image of the unit of
the summand `𝒪_X`, as well as the module

  `𝒦 = Ker(u)`,

finite locally free of rank `r`, with the map `φ : 𝒦 ⟶ π^*𝒪_X = 𝒪_E` given by the summand
`𝒪_X`. The Koszul complex of `φ` resolves the structure sheaf of the zero section of `E`.

## Main definitions

* `Stacks.Chow.ProjectiveCompletion.module`: `𝒞 ⊕ 𝒪_X`.
* `Stacks.Chow.ProjectiveCompletion.space`, `Stacks.Chow.ProjectiveCompletion.proj`: `E` and `π`.
* `Stacks.Chow.ProjectiveCompletion.twist`, `Stacks.Chow.ProjectiveCompletion.taut`: `𝒪_E(1)`
  and `u`.
* `Stacks.Chow.ProjectiveCompletion.coordT`: the section `T` of `𝒪_E(1)`.
* `Stacks.Chow.ProjectiveCompletion.kernelModule`, `Stacks.Chow.ProjectiveCompletion.koszulMap`:
  `𝒦 = Ker(u)` and `φ : 𝒦 ⟶ 𝒪_E`.

## References

* [Stacks Project, Tag 0FEF](https://stacks.math.columbia.edu/tag/0FEF)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.ProjectiveCompletion

variable {X : Scheme.{u}} (𝒞 : X.Modules)

/-- The biproduct of a module with the structure sheaf exists. -/
instance hasBinaryBiproduct_unit : HasBinaryBiproduct 𝒞 (SheafOfModules.unit X.ringCatSheaf) :=
  HasBinaryBiproducts.has_binary_biproduct _ _

/-- **The module `𝒞 ⊕ 𝒪_X`**, whose symmetric algebra is `Sym^*(𝒞)[T]`. -/
def module : X.Modules :=
  𝒞 ⊞ SheafOfModules.unit X.ringCatSheaf

/-- The inclusion `𝒞 ⟶ 𝒞 ⊕ 𝒪_X`. -/
def inl : 𝒞 ⟶ module 𝒞 := biprod.inl

/-- The inclusion `𝒪_X ⟶ 𝒞 ⊕ 𝒪_X` of the summand of the variable `T`. -/
def inr : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ module 𝒞 := biprod.inr

/-- The projection `𝒞 ⊕ 𝒪_X ⟶ 𝒪_X`. -/
def snd : module 𝒞 ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf) := biprod.snd

/-- The composite `𝒞 ⟶ 𝒞 ⊕ 𝒪_X ⟶ 𝒪_X` is zero. -/
theorem inl_snd : inl 𝒞 ≫ snd 𝒞 = 0 := biprod.inl_snd

/-- The split short exact sequence `0 ⟶ 𝒞 ⟶ 𝒞 ⊕ 𝒪_X ⟶ 𝒪_X ⟶ 0`. -/
theorem shortExact_inl_snd :
    (ShortComplex.mk (C := X.Modules) (inl 𝒞) (snd 𝒞) (inl_snd 𝒞)).ShortExact :=
  (ShortComplex.Splitting.ofHasBinaryBiproduct 𝒞 (SheafOfModules.unit X.ringCatSheaf)).shortExact

/-- The structure sheaf is finite locally free of rank one. -/
theorem isFiniteLocallyFreeOfRank_unit :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (SheafOfModules.unit X.ringCatSheaf) 1 :=
  (Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_iff
    (SheafOfModules.unit X.ringCatSheaf) 1).mpr inferInstance

/-- **`𝒞 ⊕ 𝒪_X` has rank `r + 1`** when `𝒞` has rank `r`. -/
theorem isFiniteLocallyFreeOfRank_module (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (module 𝒞) (r + 1) :=
  GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact _ (shortExact_inl_snd 𝒞) r 1
    inferInstance (isFiniteLocallyFreeOfRank_unit (X := X))

variable [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]

/-- `𝒞 ⊕ 𝒪_X` is finite locally free. -/
instance isFiniteLocallyFree_module :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (module 𝒞) :=
  haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (SheafOfModules.unit X.ringCatSheaf) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
      (hM := isFiniteLocallyFreeOfRank_unit (X := X))
  AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_biprod _ _

/-- **The projective completion `E = Proj_X(Sym^*(𝒞)[T])`** of the vector bundle of `𝒞`. -/
def space : Scheme.{u} := bundle (module 𝒞)

/-- **The projection `π : E ⟶ X`.** -/
def proj : space 𝒞 ⟶ X := bundleProj (module 𝒞)

/-- **The twist `𝒪_E(1)`.** -/
def twist : (space 𝒞).Modules := bundleTwist (module 𝒞)

/-- **The tautological surjection `u : π^*(𝒞 ⊕ 𝒪_X) ⟶ 𝒪_E(1)`.** -/
def taut : (Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞) ⟶ twist 𝒞 :=
  bundleTautological (module 𝒞)

/-- The tautological map `u : π^*(𝒞 ⊕ 𝒪_X) ⟶ 𝒪_E(1)` is an epimorphism. -/
instance epi_taut : Epi (taut 𝒞) := epi_bundleTautological (module 𝒞)

/-- The twist `𝒪_E(1)` is an invertible module. -/
instance isInvertible_twist :
    AlgebraicGeometry.SheafOfModules.IsInvertible (space 𝒞).sheaf.obj
      (space 𝒞).ringCatSheaf.property (twist 𝒞) :=
  isInvertible_bundleTwist (module 𝒞)

/-- The projection `π : E ⟶ X` is proper. -/
instance isProper_proj : IsProper (proj 𝒞) := isProper_bundleProj (module 𝒞)

/-- **The kernel `𝒦 = Ker(u)`.** -/
def kernelModule : (space 𝒞).Modules := kernel (taut 𝒞)

/-- **`𝒦` is finite locally free of rank `r`** when `𝒞` has rank `r`. -/
theorem isFiniteLocallyFreeOfRank_kernelModule (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (kernelModule 𝒞) r :=
  isFiniteLocallyFreeOfRank_kernel_bundleTautological (module 𝒞) r
    (isFiniteLocallyFreeOfRank_module 𝒞 r)

/-- The tautological sequence `0 ⟶ 𝒦 ⟶ π^*(𝒞 ⊕ 𝒪_X) ⟶ 𝒪_E(1) ⟶ 0` is short exact. -/
theorem shortExact_taut :
    (ShortComplex.mk (kernel.ι (taut 𝒞)) (taut 𝒞) (kernel.condition _)).ShortExact :=
  shortExact_bundleTautological (module 𝒞)

/-- **The map `φ : 𝒦 ⟶ 𝒪_E`**: the inclusion into `π^*(𝒞 ⊕ 𝒪_X)` followed by the projection to
`π^*𝒪_X = 𝒪_E`. Its Koszul complex resolves the structure sheaf of the zero section. -/
def koszulMap :
    kernelModule 𝒞 ⟶ (show (space 𝒞).Modules from SheafOfModules.unit (space 𝒞).ringCatSheaf) :=
  kernel.ι (taut 𝒞) ≫ (Scheme.Modules.pullback (proj 𝒞)).map (snd 𝒞) ≫
    (Scheme.Modules.pullbackUnitIso (proj 𝒞)).hom

end Stacks.Chow.ProjectiveCompletion
