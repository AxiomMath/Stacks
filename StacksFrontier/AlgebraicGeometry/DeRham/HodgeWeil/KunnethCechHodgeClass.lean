module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.KunnethCechClass
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Data
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.DeRhamComplexSections

/-!
# Hodge cohomology classes of Čech cocycles of differential forms

Let `f : X ⟶ S` be a morphism of schemes. The Hodge cohomology groups `H^q(X, Ω^p_{X/S})` are the
cohomology of the derived global sections of `Ω^p_{X/S}`, a sheaf of modules over the base ring
sheaf `f⁻¹𝒪_S`. This file records the sections of `Ω^p_{X/S}` as a presheaf of modules over a
ring `k` mapping to `Γ(X, f⁻¹𝒪_S)`, whose Čech complexes are those of [Stacks, Tag 01ED], and the
class in `H^q(X, Ω^p_{X/S})` of a Čech `q`-cocycle of `Ω^p_{X/S}` on an open covering of `X`.

## Main definitions

* `Stacks.HodgeWeil.hodgeSectionsK`: the sections of `Ω^p_{X/S}` as a presheaf of `k`-modules.
* `Stacks.HodgeWeil.hodgeCechClass`: the class in `H^q(X, Ω^p_{X/S})` of a Čech `q`-cocycle.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.CechSheaf (abSections)
open AlgebraicGeometry.SheafOfModules (hodgeCohomologyComponent deRhamTerm baseRingedSpace)

universe u

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The sections of `Ω^p_{X/S}` as a presheaf of `k`-modules**, for a ring map
`φ : k ⟶ Γ(X, f⁻¹𝒪_S)`: `V ↦ Γ(V, Ω^p_{X/S})`, with `k` acting through `φ` and restriction to
`V`. -/
def hodgeSectionsK {k : Type u} [CommRing k] (φ : k →+* hodgeBaseRing f) (p : ℕ) :
    X.Opensᵒᵖ ⥤ ModuleCat.{u} k :=
  (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) (Limits.isTerminalTop).op).obj
      (deRhamTerm (formsAlgebras f) p).val ⋙
    ModuleCat.restrictScalars φ

variable {I : Type u} (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)

/-- **The class in `H^q(X, Ω^p_{X/S})` of a Čech `q`-cocycle** `c` of `Ω^p_{X/S}` on an open
covering `𝒰` of `X`: the class `cechSheafClass` of `c` for the ringed space `(X, f⁻¹𝒪_S)`. -/
def hodgeCechClass (p : ℕ) {q : ℕ}
    (c : CechCochains.Cochain U (abSections (deRhamTerm (formsAlgebras f) p)) q)
    (hc : CechCochains.cechD U (abSections (deRhamTerm (formsAlgebras f) p)) q c = 0) :
    hodgeCohomologyComponent (formsAlgebras f) p (q : ℤ) :=
  cechSheafClass (baseRingedSpace (f.inverseImageRingSheaf)) U hU
    (deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p) c hc

end Stacks.HodgeWeil

end
