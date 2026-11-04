module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Support
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections

/-!
# Support of a quasi-coherent module on an affine open

For a quasi-coherent module sheaf on a scheme, a point of an affine open lies in the support of
the sheaf exactly when the corresponding prime lies in the support of the module of sections
over that open.

Both sides are read off a single stalk: the stalk of the sheaf at the point is the localization
of the module of sections at the prime, so one is nontrivial exactly when the other is.

## Main results

* `AlgebraicGeometry.Scheme.Modules.mem_support_sections_iff_mem_supp`: support on an affine
  open is detected by its module of sections.

## Implementation notes

The affine open is represented by `X.affineOpens`; its ring of functions is `Γ(X, U.1)` and the
corresponding prime is `U.2.primeIdealOf ⟨x, hx⟩`. The support of the sheaf is
`SheafOfModules.supp`, read off the stalks of the underlying sheaf of abelian groups; that is
the same set as the support of the sheaf viewed as a module sheaf on the underlying ringed
space, and it is available for a scheme in an arbitrary universe.

## References

* [Stacks Project, Tag 056I](https://stacks.math.columbia.edu/tag/056I)
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.tilde CategoryTheory CategoryTheory.Limits
  TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- On an affine open, support of the sections module agrees with support of the
quasi-coherent sheaf. -/
@[stacks 056I]
public lemma mem_support_sections_iff_mem_supp {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (U : X.affineOpens) (x : X) (hx : x ∈ U.1) :
    U.2.primeIdealOf ⟨x, hx⟩ ∈ Module.support Γ(X, U.1) Γ(F, U.1) ↔
      x ∈ SheafOfModules.supp F := by
  let A := Γ(X, U.1)
  let f := U.2.fromSpec
  let : IsOpenImmersion f := U.2.isOpenImmersion_fromSpec
  let y := U.2.primeIdealOf ⟨x, hx⟩
  let G := F.restrict f
  let M := ModuleCat.of A Γ(G, ⊤)
  let e := affineSectionsLinearEquiv F U.2
  let t := ModuleCat.Hom.hom (AlgebraicGeometry.tilde.toStalk M y)
  let : IsLocalizedModule y.asIdeal.primeCompl t :=
    instIsLocalizedModuleCarrierCarrierOfCarrierStalkAbPresheafPrimeComplAsIdealHomToStalk M y
  let : IsLocalizedModule y.asIdeal.primeCompl (t ∘ₗ e.symm.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right y.asIdeal.primeCompl t e.symm
  let localIso := IsLocalizedModule.iso y.asIdeal.primeCompl
    (t ∘ₗ e.symm.toLinearMap)
  let : G.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor f F
  let : IsIso G.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent G
  let quasiIso :=
    ((Scheme.Modules.toPresheaf (Spec A) ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y).mapIso
      (asIso G.fromTildeΓ))
  have hxy : f y = x := U.2.fromSpec_primeIdealOf ⟨x, hx⟩
  have hstalk :
      (TopCat.Presheaf.stalkFunctor Ab.{u} (f y)).obj
          ((Scheme.Modules.toPresheaf X).obj F) =
        (TopCat.Presheaf.stalkFunctor Ab.{u} x).obj
          ((Scheme.Modules.toPresheaf X).obj F) :=
    congrArg (fun z : X =>
      (TopCat.Presheaf.stalkFunctor Ab.{u} z).obj ((Scheme.Modules.toPresheaf X).obj F)) hxy
  let castIso := eqToIso hstalk
  let restrictionIso := (Scheme.Modules.restrictStalkNatIso f y).app F
  let stalkEquiv := quasiIso.addCommGroupIsoToAddEquiv.trans
    (restrictionIso.addCommGroupIsoToAddEquiv.trans castIso.addCommGroupIsoToAddEquiv)
  rw [Module.mem_support_iff]
  refine Iff.trans ?_ (SheafOfModules.mem_supp_iff_nontrivial_stalk F x).symm
  exact (localIso.toAddEquiv.trans stalkEquiv).toEquiv.nontrivial_congr

end AlgebraicGeometry.Scheme.Modules
