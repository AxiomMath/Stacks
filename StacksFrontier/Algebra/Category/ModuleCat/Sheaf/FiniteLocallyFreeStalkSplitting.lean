module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExactIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerFunctorialStalk
public import StacksFrontier.LinearAlgebra.SymmetricPower.SquareFiltration

/-!
# Free stalks of a finite locally free sheaf, and the stalkwise splitting of a short exact
sequence

Let `X` be a topological space, `O♯` a sheaf of commutative rings on it and
`E' --f--> E --g--> E''` a short exact sequence of sheaves of `O♯`-modules with `E''` finite
locally free. Every stalk of `E''` is free of finite rank over the corresponding stalk of `O♯`,
`f` is a split injection on every stalk, and consequently `Symⁿ f` is a monomorphism.

## Main results

* `Stacks.SheafOfModules.TopWedge.free_stalk` and
  `Stacks.SheafOfModules.TopWedge.finite_stalk`: every stalk of a finite locally free sheaf of
  modules is a free module of finite rank over the corresponding stalk of the sheaf of rings.
* `Stacks.SheafOfModules.TopWedge.exists_stalkMapL_leftInverse_of_shortExact`: the inclusion of
  a short exact sequence of sheaves of modules whose quotient is finite locally free has a left
  inverse on every stalk.
* `SheafOfModules.GradedAlgebra.IsSymmetricAlgebra.mono_pieceMap_of_shortExact` and
  `SheafOfModules.TensorExteriorSymmetricAlgebras.mono_symmetricSquareMap_of_shortExact`:
  `Symⁿ f` and `Sym² f` are monomorphisms along such a sequence.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules.TopWedge

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}

/-! ### The stalks of a finite locally free sheaf of modules are free of finite rank -/

/-- Every stalk of a finite locally free sheaf of modules is a free module over the
corresponding stalk of the sheaf of rings. -/
theorem free_stalk
    (F : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] (x : ↥X) :
    Module.Free ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk F.val.presheaf x) := by
  obtain ⟨r, ⟨e⟩⟩ := exists_nonempty_stalkLinearEquiv_finsupp F x
  exact Module.Free.of_equiv e.symm

/-- Every stalk of a finite locally free sheaf of modules is a finite module over the
corresponding stalk of the sheaf of rings. -/
theorem finite_stalk
    (F : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] (x : ↥X) :
    Module.Finite ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk F.val.presheaf x) := by
  obtain ⟨r, ⟨e⟩⟩ := exists_nonempty_stalkLinearEquiv_finsupp F x
  exact Module.Finite.equiv e.symm

/-! ### The stalkwise splitting -/

section Splitting

variable {E' E E'' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- The inclusion of a short exact sequence of sheaves of modules whose quotient is finite
locally free admits a left inverse on every stalk. -/
theorem exists_stalkMapL_leftInverse_of_shortExact (f : E' ⟶ E) (g : E ⟶ E'')
    (hfg : f ≫ g = 0) (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] (x : ↥X) :
    ∃ ρ : ↑(TopCat.Presheaf.stalk E.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
        ↑(TopCat.Presheaf.stalk E'.val.presheaf x),
      ρ.comp (PresheafOfModules.stalkMapL x f.val) = LinearMap.id := by
  have := free_stalk E'' x
  obtain ⟨hinj, hsurj, hex⟩ := stalkMapL_shortExact f g hfg hS x
  exact SymPow.exists_leftInverse_of_shortExact _ _ hinj hsurj hex

end Splitting

end Stacks.SheafOfModules.TopWedge

/-! ### Monomorphy of the symmetric powers along such a sequence -/

namespace SheafOfModules

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {E' E E'' : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

namespace GradedAlgebra.IsSymmetricAlgebra

/-- `Symⁿ f` is a monomorphism along a short exact sequence `E' --f--> E --g--> E''` of sheaves
of modules whose quotient `E''` is finite locally free. -/
theorem mono_pieceMap_of_shortExact
    {A B : GradedAlgebra.{u, u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (gen : E' ⟶ A.piece 1) (gen' : E ⟶ B.piece 1)
    (hA : GradedAlgebra.IsSymmetricAlgebra A gen)
    (hB : GradedAlgebra.IsSymmetricAlgebra B gen')
    (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] (n : ℕ) :
    Mono (hA.pieceMap hB f (n : ℤ)) :=
  mono_pieceMap_of_stalkwise_leftInverse gen gen' hA hB f n fun x =>
    Stacks.SheafOfModules.TopWedge.exists_stalkMapL_leftInverse_of_shortExact f g hfg hS x

end GradedAlgebra.IsSymmetricAlgebra

namespace TensorExteriorSymmetricAlgebras

/-- `Sym²E' ⟶ Sym²E` is a monomorphism along a short exact sequence `E' --f--> E --g--> E''` of
sheaves of modules whose quotient `E''` is finite locally free. -/
theorem mono_symmetricSquareMap_of_shortExact
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) E')
    (A' : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) E)
    (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] :
    Mono (A.symmetricSquareMap A' f) :=
  mono_symmetricSquareMap_of_stalkwise_leftInverse A A' f fun x =>
    Stacks.SheafOfModules.TopWedge.exists_stalkMapL_leftInverse_of_shortExact f g hfg hS x

end TensorExteriorSymmetricAlgebras

end SheafOfModules

end
