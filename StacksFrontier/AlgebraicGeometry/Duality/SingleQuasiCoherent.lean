module

public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentPushforwardAdjoint

/-!
# A quasi-coherent module in a single degree, as an object of `D_QCoh`

For a scheme `X` and a quasi-coherent `𝒪_X`-module `F`, the complex `F[-n]` (the module placed in
cohomological degree `n`) has quasi-coherent cohomology sheaves: `F` in degree `n` and zero in
every other degree. So it is an object of `D_QCoh(𝒪_X)`.

## Main definitions

* `Stacks.Duality.singleQuasiCoherent`: `F` placed in degree `n`, as an object of
  `Stacks.Duality.quasiCoherentDerivedCategory X`, at any model of `D(𝒪_X)`.
-/

@[expose] public noncomputable section

universe w u

open CategoryTheory AlgebraicGeometry

namespace Stacks.Duality

variable {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]

/-- **A quasi-coherent `𝒪_X`-module placed in degree `n`, as an object of `D_QCoh(𝒪_X)`**: its
cohomology sheaf is the module in degree `n` and a zero object in every other degree. -/
def singleQuasiCoherent (F : X.Modules) (hF : F.IsQuasicoherent) (n : ℤ) :
    quasiCoherentDerivedCategory X :=
  ⟨(DerivedCategory.singleFunctor X.Modules n).obj F, fun i => by
    have := containsZero_isQuasicoherent X
    rcases lt_trichotomy i n with h | rfl | h
    · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isZero
        (DerivedCategory.isZero_of_isGE ((DerivedCategory.singleFunctor X.Modules n).obj F) n i h)
    · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules i).app F).symm hF
    · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isZero
        (DerivedCategory.isZero_of_isLE ((DerivedCategory.singleFunctor X.Modules n).obj F) n i h)⟩

/-- The underlying object of `D(𝒪_X)` of `singleQuasiCoherent F hF n` is `F` placed in degree
`n`. -/
@[simp]
theorem singleQuasiCoherent_obj (F : X.Modules) (hF : F.IsQuasicoherent) (n : ℤ) :
    (singleQuasiCoherent F hF n).obj = (DerivedCategory.singleFunctor X.Modules n).obj F :=
  rfl

end Stacks.Duality
