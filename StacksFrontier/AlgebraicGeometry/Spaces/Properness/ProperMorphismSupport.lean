module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceHypotheses
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion

/-!
# Supports along a proper morphism of algebraic spaces

Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over a scheme `S`. Every closed
subspace `Z ⊆ X` is then proper over `Y`, and every closed subset of `|X|` is proper over `Y` in
the sense of Stacks 0CZD. Hence every finite type `𝒪_X`-module has support proper over `Y`, and
the scheme-theoretic support of a finite type quasi-coherent `𝒪_X`-module (Stacks 07U0, 07U1) is
proper over `Y`.

## Main results

* `AlgebraicGeometry.Space.isProper_ι_comp_of_isProper`: a closed subspace of `X` is proper
  over `Y` when `f` is proper.
* `AlgebraicGeometry.Space.hasProperSupport_of_isProper`: an abelian sheaf on the small étale
  site of `X` with closed support has support proper over `Y` when `f` is proper.
* `AlgebraicGeometry.Space.hasProperSupport_toSheaf_of_isProper`: a finite type `𝒪_X`-module
  has support proper over `Y` when `f` is proper.
* `AlgebraicGeometry.Space.isProper_schemeTheoreticSupport_of_isProper`: the scheme-theoretic
  support of a finite type quasi-coherent `𝒪_X`-module is proper over `Y` when `f` is proper.

## References

* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 07U0](https://stacks.math.columbia.edu/tag/07U0)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 0CZI](https://stacks.math.columbia.edu/tag/0CZI)
* [Stacks Project, Tag 04XZ](https://stacks.math.columbia.edu/tag/04XZ)
* [Stacks Project, Tag 04XY](https://stacks.math.columbia.edu/tag/04XY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v m

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Presheaves

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- If `f : X ⟶ Y` is proper, then every closed subspace of `X` is proper over `Y`. -/
theorem isProper_ι_comp_of_isProper (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hproper : IsProper B S hS f)
    (Z : Subfunctor X) (hZ : IsClosedSubspace B S hS Z) :
    IsProper B S hS (Z.ι ≫ f) :=
  isProper_comp' B S hS Z.ι f hX hY (isProper_of_isClosedImmersion B S hS hZ.1 hX Z.ι hZ.2)
    hproper

/-- If `f : X ⟶ Y` is proper, then an abelian sheaf on the small étale site of `X` with closed
support has support proper over `Y`. -/
theorem hasProperSupport_of_isProper (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (hproper : IsProper B S hS f)
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (hF : IsClosed (supportOfSheaf B S hS X F)) :
    HasProperSupport B S hS hX hY f hf F :=
  ⟨hF, isProperOver_of_isProper B S hS hX hY f hf hproper _ hF⟩

/-- If `f : X ⟶ Y` is proper, then a finite type `𝒪_X`-module has support proper over `Y`. -/
theorem hasProperSupport_toSheaf_of_isProper (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (hproper : IsProper B S hS f) (F : Modules.{u, m} B S hS X hX)
    [SheafOfModules.IsFiniteTypeOnSite F] :
    HasProperSupport B S hS hX hY f hf ((SheafOfModules.toSheaf _).obj F) :=
  hasProperSupport_of_isProper B S hS hX hY f hf hproper _
    (isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X hX F)

end Presheaves

/-- If `f : X ⟶ Y` is proper, then the scheme-theoretic support of a finite type
quasi-coherent `𝒪_X`-module `F` is proper over `Y`. -/
theorem isProper_schemeTheoreticSupport_of_isProper (X Y : AlgebraicSpaces B S hS)
    (f : X.1 ⟶ Y.1) (hproper : IsProper B S hS f) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (hFft : SheafOfModules.IsFiniteTypeOnSite F) :
    IsProper B S hS ((schemeTheoreticSupport B S hS X F).ι ≫ f) :=
  isProper_ι_comp_of_isProper B S hS X.2 Y.2 f hproper _
    (exists_isClosedSubspace_schemeTheoreticSupport B S hS X F hF
      (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite F hFft)).1

end AlgebraicGeometry.Space

end
