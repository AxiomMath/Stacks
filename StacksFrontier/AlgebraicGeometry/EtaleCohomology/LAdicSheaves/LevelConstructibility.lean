module

public import Mathlib.CategoryTheory.Subobject.Lattice
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShrinkCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RawKernel

/-!
# The finite levels of an ℓ-adic sheaf are Noetherian objects

The finite levels of an ℓ-adic sheaf are sheaves of `ℤ/ℓⁿ⁺¹ℤ`-modules in `ModuleCat.{u + 1}`. A
subsheaf or a quotient of a constructible finite-level sheaf is constructible, and a constructible
finite-level sheaf is a Noetherian object, so an ascending chain of subobjects of it stabilises.

## Main results

* `Stacks.EtaleCohomology.FiniteLevelSheaf.isConstructible_of_mono` and
  `.isConstructible_subobject`: a subsheaf of a constructible finite-level sheaf is
  constructible.
* `Stacks.EtaleCohomology.FiniteLevelSheaf.isConstructible_of_epi`: so is a quotient of one.
* `Stacks.EtaleCohomology.FiniteLevelSheaf.isNoetherianObject`: a constructible finite-level
  sheaf is a Noetherian object.
* `Stacks.EtaleCohomology.LAdicSheaf.isConstructible_subobject` and
  `.isNoetherianObject_level`: the same two statements at a level of an ℓ-adic sheaf.
* `Stacks.EtaleCohomology.LAdicSheaf.isConstructible_kernel_app`: the levelwise kernel of a
  morphism of ℓ-adic sheaves is constructible.

## References

* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
* [Stacks Project, Tag 09YV](https://stacks.math.columbia.edu/tag/09YV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

namespace FiniteLevelSheaf

omit [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- A subsheaf of a constructible finite-level sheaf is constructible. -/
@[stacks 09BH "part (3), subsheaf, at the coefficients Z/l^{n+1}Z of a finite level of an \
l-adic sheaf"]
public theorem isConstructible_of_mono (n : ℕ)
    {G F : FiniteLevelSheaf.{u, u + 1} B X ℓ n} (i : G ⟶ F) [Mono i]
    (hF : IsConstructibleModuleSheaf B X (ZMod (ℓ ^ (n + 1))) F) :
    IsConstructibleModuleSheaf B X (ZMod (ℓ ^ (n + 1))) G :=
  isConstructibleModuleSheaf_of_mono' B (ZMod (ℓ ^ (n + 1))) X i hF

omit [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- A quotient of a constructible finite-level sheaf is constructible. -/
@[stacks 09BH "part (3), quotient sheaf, at the coefficients Z/l^{n+1}Z of a finite level of an \
l-adic sheaf"]
public theorem isConstructible_of_epi (n : ℕ)
    {G Q : FiniteLevelSheaf.{u, u + 1} B X ℓ n} (p : G ⟶ Q) [Epi p]
    (hG : IsConstructibleModuleSheaf B X (ZMod (ℓ ^ (n + 1))) G) :
    IsConstructibleModuleSheaf B X (ZMod (ℓ ^ (n + 1))) Q :=
  isConstructibleModuleSheaf_of_epi' B (ZMod (ℓ ^ (n + 1))) X p hG

omit [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- Every subobject of a constructible finite-level sheaf is constructible. -/
public theorem isConstructible_subobject (n : ℕ)
    {F : FiniteLevelSheaf.{u, u + 1} B X ℓ n}
    (hF : IsConstructibleModuleSheaf B X (ZMod (ℓ ^ (n + 1))) F) (S : Subobject F) :
    IsConstructibleModuleSheaf B X (ZMod (ℓ ^ (n + 1))) ((Subobject.underlying).obj S) :=
  isConstructible_of_mono B X ℓ n S.arrow hF

omit [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- A constructible finite-level sheaf is a Noetherian object: every ascending chain of subsheaves
of it stabilises. -/
@[stacks 09YV "sheaves of modules, at the coefficients Z/l^{n+1}Z of a finite level of an \
l-adic sheaf"]
public theorem isNoetherianObject (n : ℕ) (F : FiniteLevelSheaf.{u, u + 1} B X ℓ n)
    (hF : IsConstructibleModuleSheaf B X (ZMod (ℓ ^ (n + 1))) F) :
    IsNoetherianObject F := by
  let _ := SmallEtale.hasSheafify_moduleCat.{u, 0, u + 1} B X (ZMod (ℓ ^ (n + 1)))
  exact isNoetherianObject_of_isConstructibleModuleSheaf' B (ZMod (ℓ ^ (n + 1))) X F hF

end FiniteLevelSheaf

namespace LAdicSheaf

variable {B X ℓ}

/-- Every subobject of a finite level of an ℓ-adic sheaf is a constructible sheaf. -/
public theorem isConstructible_subobject (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ)
    (S : Subobject (F.level n)) :
    IsConstructibleModuleSheaf B X (ZMod (ℓ ^ (n + 1))) ((Subobject.underlying).obj S) :=
  FiniteLevelSheaf.isConstructible_subobject B X ℓ n (F.constructible n) S

/-- A finite level of an ℓ-adic sheaf is a Noetherian object. -/
public theorem isNoetherianObject_level (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    IsNoetherianObject (F.level n) :=
  FiniteLevelSheaf.isNoetherianObject B X ℓ n _ (F.constructible n)

/-- The levelwise kernel of a morphism of ℓ-adic sheaves is a constructible sheaf. -/
public theorem isConstructible_kernel_app {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    (n : ℕ) :
    IsConstructibleModuleSheaf B X (ZMod (ℓ ^ (n + 1))) (kernel (f.app n)) :=
  FiniteLevelSheaf.isConstructible_of_mono B X ℓ n (kernel.ι (f.app n)) (F.constructible n)

end LAdicSheaf

end Stacks.EtaleCohomology

end
