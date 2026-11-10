module

public import StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceHodgeEveryDimension
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Kunneth
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.DegreeZero
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.KunnethCechCup
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.KunnethCechModel
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.RestrictScalarsCechComputes
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCechTransfer
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyGlobalScalars
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyAbelianDegreeOneNaturality
public import
  StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologySinglePairingAtCompat
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCupNaturality
public import StacksFrontier.Algebra.Module.RankOneGenerator

/-!
# The Hodge cohomology of projective space in the realization of the Weil data

Let `f : X ⟶ S` be a morphism of schemes and let `H^q(X, Ωᵖ_{X/S})` be the Hodge cohomology groups
of the Weil data of Remark 0FWE: the cohomology of the derived global sections of `Ωᵖ_{X/S}`, read
as a sheaf of modules over `f⁻¹𝒪_S`, with the cup product and the Hodge first Chern class
`c₁^{Hodge}(L)` of that realization. This file proves [Stacks, Tag 0FMI] over a field in this
realization: for `k` a field and `π : ℙʳ_k ⟶ Spec k`,

* `H^q(ℙʳ_k, Ωᵖ) = 0` unless `p = q ≤ r`;
* for `p ≤ r` the `k`-vector space `Hᵖ(ℙʳ_k, Ωᵖ)` has dimension one, with basis the cup power
  `c₁^{Hodge}(𝒪(1))ᵖ`.

The groups are first identified with the Čech hypercohomology of `Ωᵖ_{X/S}` as an `𝒪_X`-module,
for `X` with affine diagonal: the derived global sections over `f⁻¹𝒪_S` are those over `𝒪_X`
(both compute sheaf cohomology), and Čech cohomology for affine open coverings computes both
([Stacks, Tag 01XD]). This comparison is semilinear along `Γ(S, 𝒪_S) ⟶ Γ(X, 𝒪_X)`, sends the class
of a Čech cocycle to its class, and carries the cup product of the Weil data to the Čech cup
product along the wedge product `Ωᵖ × Ω^{p'} ⟶ Ω^{p+p'}`, up to the Koszul sign `(-1)^{q p'}` on
`H^q × H^{q'}`. On `ℙʳ_k` the Čech hypercohomology is the one in which [Stacks, Tag 0FMI] is
proved for every `r ≥ 0`, so the vanishing and the dimension transfer directly. The powers are
nonzero, hence a basis: by induction on `p`, the comparison sends `c₁^{Hodge}(𝒪(1))ᵖ` to a nonzero
multiple of the power `c₁^{Hodge}(𝒪(1))ᵖ` of [Stacks, Tag 0FMI], both spaces having dimension one.

## Main definitions

* `Stacks.HodgeWeil.hodgeComponentCechEquiv`: `H^q(X, Ωᵖ_{X/S})` is the Čech hypercohomology of
  `Ωᵖ_{X/S}`, for `X` with affine diagonal.
* `Stacks.HodgeWeil.hodgeFirstChernClassPow`: the cup powers `c₁^{Hodge}(L)ᵖ ∈ Hᵖ(X, Ωᵖ_{X/S})`.
* `Stacks.HodgeWeil.projectiveHodgeComponentEquiv`: `H^q(ℙʳ_k, Ωᵖ)` of the Weil data is
  `H^q(ℙʳ_k, Ωᵖ)` computed by right derived functors, as `k`-vector spaces.

## Main results

* `Stacks.HodgeWeil.hodgeComponentCechEquiv_hodgeCohomologyCup`: the comparison with Čech
  hypercohomology carries cup products to cup products, up to the sign `(-1)^{q p'}`.
* `Stacks.HodgeWeil.isZero_hodgeCohomologyComponent_projectiveSpace`: [Stacks, Tag 0FMI], the
  vanishing, `H^q(ℙʳ_k, Ωᵖ) = 0` unless `p = q ≤ r`.
* `Stacks.HodgeWeil.exists_basis_hodgeFirstChernClassPow`: [Stacks, Tag 0FMI], the basis,
  `c₁^{Hodge}(𝒪(1))ᵖ` is a basis of `Hᵖ(ℙʳ_k, Ωᵖ)` for `p ≤ r`.

## Implementation notes

The `k`-module structure on `H^q(ℙʳ_k, Ωᵖ)` is the one of the Weil data, through
`Stacks.HodgeWeil.hodgeScalarsOverField`; in the comparison it becomes multiplication by the
constant global functions of `ℙʳ_k`. The Hodge first Chern class of the Weil data lies in
`H¹(ℙʳ_k, Ω¹)`, with `Ω¹ = ⋀¹Ω`, while the source's lies in `H¹(ℙʳ_k, Ω)`; the two are compared
through the generator `Ω ⟶ ⋀¹Ω`, and only up to a nonzero scalar, which suffices for the basis.

## References

* [Stacks Project, Tag 0FMI](https://stacks.math.columbia.edu/tag/0FMI)
* [Stacks Project, Tag 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Section 01FP](https://stacks.math.columbia.edu/tag/01FP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

section Groups

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom (pullback.diagonal (terminal.from X))]

/-- Čech cohomology computes the cohomology of `Ωᵖ_{X/S}` read over `f⁻¹𝒪_S`. -/
theorem cechComputes_deRhamTerm_formsAlgebras (p : ℕ) :
    Stacks.Cech.Hypercohomology.CechComputes
      (SheafOfModules.baseRingedSpace
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).sheaf
      (Stacks.Cech.Hypercohomology.singlePlus
        (SheafOfModules.baseRingedSpace
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).sheaf
        (SheafOfModules.deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p) 0) :=
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms f p
  Stacks.Cech.Hypercohomology.cechComputesSheaf_restrictScalars_of_isQuasicoherent X
    (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap f))
    (Scheme.Hom.relativeDifferentialForms f (p : ℤ))

/-- Čech cohomology computes the cohomology of `Ωᵖ_{X/S}` as an `𝒪_X`-module. -/
theorem cechComputesSheaf_relativeDifferentialForms (p : ℕ) :
    Stacks.Cech.Hypercohomology.CechComputesSheaf X.sheaf
      (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) :=
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms f p
  Stacks.Cech.Hypercohomology.cechComputesSheaf_of_isQuasicoherent X
    (Scheme.Hom.relativeDifferentialForms f (p : ℤ))

/-- **`H^q(X, Ω^p_{X/S})` in the module realization is the Čech hypercohomology of `Ω^p_{X/S}` as
an `𝒪_X`-module**: the two models of derived global sections over `f⁻¹𝒪_S`, followed by the
identification of Čech cocycles across restriction of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X`. -/
def hodgeComponentCechEquiv (p q : ℕ) :
    SheafOfModules.hodgeCohomologyComponent (formsAlgebras f) p (q : ℤ) ≃+
      Stacks.Cech.Hypercohomology.hypercohomology X.sheaf
        (Stacks.Cech.Hypercohomology.singlePlus X.sheaf
          (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) 0) q :=
  haveI := Scheme.Hom.isQuasicoherent_relativeDifferentialForms f p
  ((DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
    ((Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIsoBaseSections
      (SheafOfModules.baseRingedSpace
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))).app
      (Stacks.Cech.Hypercohomology.singlePlus
        (SheafOfModules.baseRingedSpace
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).sheaf
        (SheafOfModules.deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p)
          0))).symm.toLinearEquiv.toAddEquiv.trans
    (Stacks.Cech.Hypercohomology.restrictScalarsCechEquiv
      (SheafOfModules.underlyingRingHom (X := X.toRingedSpace) (φ := inverseImageStructureMap f))
      (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) 0
      (cechComputes_deRhamTerm_formsAlgebras f p)
      (Stacks.Cech.Hypercohomology.cechComputesSheaf_of_isQuasicoherent X
        (Scheme.Hom.relativeDifferentialForms f (p : ℤ))) q)

omit [IsAffineHom (pullback.diagonal (terminal.from X))] in
/-- **Multiplication by a global function of `f⁻¹𝒪_S`, read over `f⁻¹𝒪_S`**: restricting the
scalars of multiplication by the image of `s ∈ Γ(X, f⁻¹𝒪_S)` in `Γ(X, 𝒪_X)` gives multiplication
by `s`. -/
theorem restrictScalars_map_smulHom_underlyingRingHom
    (s : ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).obj.obj (op ⊤))
    (F : X.Modules) :
    (_root_.SheafOfModules.restrictScalars
        (SheafOfModules.underlyingRingHom (X := X.toRingedSpace)
          (φ := inverseImageStructureMap f))).map
        (Stacks.Cohomology.InvertibleDerived.smulHom (X := X.toRingedSpace)
          (((SheafOfModules.underlyingRingHom (X := X.toRingedSpace)
            (φ := inverseImageStructureMap f)).hom.app (op ⊤)).hom s) F) =
      Stacks.Cohomology.InvertibleDerived.smulHom (X := SheafOfModules.baseRingedSpace
          (X := X.toRingedSpace) ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)) s
        ((_root_.SheafOfModules.restrictScalars
          (SheafOfModules.underlyingRingHom (X := X.toRingedSpace)
            (φ := inverseImageStructureMap f))).obj F) := by
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun y => ?_))
  have h := ConcreteCategory.congr_hom
    ((SheafOfModules.underlyingRingHom (X := X.toRingedSpace)
      (φ := inverseImageStructureMap f)).hom.naturality (homOfLE (le_top : V.unop ≤ ⊤)).op) s
  exact (congrArg (fun r : (ringSheaf X.sheaf).obj.obj V =>
    (r • (show F.val.obj V from y) : F.val.obj V)) h).symm

/-- **The comparison `hodgeComponentCechEquiv` is semilinear** along the structure map
`Γ(X, f⁻¹𝒪_S) ⟶ Γ(X, 𝒪_X)`. -/
theorem hodgeComponentCechEquiv_smul (p q : ℕ) (s : hodgeBaseRing f)
    (x : SheafOfModules.hodgeCohomologyComponent (formsAlgebras f) p (q : ℤ)) :
    hodgeComponentCechEquiv f p q (s • x) =
      (show Stacks.Cohomology.CechSheaf.SectionRing (ringSheaf X.sheaf) ⊤ from
        ((SheafOfModules.underlyingRingHom (X := X.toRingedSpace)
          (φ := inverseImageStructureMap f)).hom.app (op ⊤)).hom s) •
        hodgeComponentCechEquiv f p q x := by
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms f p
  let e := ((DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
    ((Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIsoBaseSections
      (SheafOfModules.baseRingedSpace
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))).app
      (Stacks.Cech.Hypercohomology.singlePlus
        (SheafOfModules.baseRingedSpace
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).sheaf
        (SheafOfModules.deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p) 0))).symm
  have he : e.hom.hom (s • x) = (show Stacks.Cohomology.CechSheaf.SectionRing
      (structureSheafRing (SheafOfModules.baseRingedSpace
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))) ⊤ from s) • e.hom.hom x :=
    e.hom.hom.map_smul _ x
  have h1 := Stacks.Cech.Hypercohomology.restrictScalarsCechEquiv_hypercohomologyMap
    (SheafOfModules.underlyingRingHom (X := X.toRingedSpace) (φ := inverseImageStructureMap f))
    (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) 0
    (Stacks.Cohomology.InvertibleDerived.smulHom (X := X.toRingedSpace)
      (((SheafOfModules.underlyingRingHom (X := X.toRingedSpace)
        (φ := inverseImageStructureMap f)).hom.app (op ⊤)).hom s)
      (Scheme.Hom.relativeDifferentialForms f (p : ℤ)))
    (cechComputes_deRhamTerm_formsAlgebras f p)
    (Stacks.Cech.Hypercohomology.cechComputesSheaf_of_isQuasicoherent X
      (Scheme.Hom.relativeDifferentialForms f (p : ℤ)))
    (cechComputes_deRhamTerm_formsAlgebras f p)
    (Stacks.Cech.Hypercohomology.cechComputesSheaf_of_isQuasicoherent X
      (Scheme.Hom.relativeDifferentialForms f (p : ℤ))) q (e.hom.hom x)
  have h2 := Stacks.Cech.Hypercohomology.hypercohomologyMap_smulHom
    (X := SheafOfModules.baseRingedSpace (X := X.toRingedSpace)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)) s
    ((_root_.SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom (X := X.toRingedSpace)
      (φ := inverseImageStructureMap f))).obj (Scheme.Hom.relativeDifferentialForms f (p : ℤ))) 0
    (cechComputes_deRhamTerm_formsAlgebras f p) _ (e.hom.hom x)
  have h3 := Stacks.Cech.Hypercohomology.hypercohomologyMap_smulHom (X := X.toRingedSpace)
    (((SheafOfModules.underlyingRingHom (X := X.toRingedSpace)
      (φ := inverseImageStructureMap f)).hom.app (op ⊤)).hom s)
    (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) 0
    (Stacks.Cech.Hypercohomology.cechComputesSheaf_of_isQuasicoherent X
      (Scheme.Hom.relativeDifferentialForms f (p : ℤ))) q
    (hodgeComponentCechEquiv f p q x)
  have h4 := congrArg (fun g => Stacks.Cech.Hypercohomology.hypercohomologyMap
      (SheafOfModules.baseRingedSpace
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).sheaf
      (Stacks.Cech.Hypercohomology.singlePlusMapAt
        (SheafOfModules.baseRingedSpace
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).sheaf
        g 0) ((q : ℤ) + 0) (e.hom.hom x))
    (restrictScalars_map_smulHom_underlyingRingHom f s
      (Scheme.Hom.relativeDifferentialForms f (p : ℤ)))
  exact (congrArg (Stacks.Cech.Hypercohomology.restrictScalarsCechEquiv
        (SheafOfModules.underlyingRingHom (X := X.toRingedSpace) (φ := inverseImageStructureMap f))
        (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) 0
        (cechComputes_deRhamTerm_formsAlgebras f p)
        (Stacks.Cech.Hypercohomology.cechComputesSheaf_of_isQuasicoherent X
          (Scheme.Hom.relativeDifferentialForms f (p : ℤ))) q)
        ((he.trans h2.symm).trans h4.symm)).trans
    (h1.trans h3)

/-- **The comparison `hodgeComponentCechEquiv` on the class of a Čech cocycle** is the class of the
same cocycle in the Čech hypercohomology of `Ωᵖ_{X/S}` as an `𝒪_X`-module. -/
theorem hodgeComponentCechEquiv_hodgeCechClass (p : ℕ) {q : ℕ} {I : Type u} (U : I → X.Opens)
    (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (c : CechCochains.Cochain U (Stacks.Cohomology.CechSheaf.abSections
      (SheafOfModules.deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p)) q)
    (hc : CechCochains.cechD U (Stacks.Cohomology.CechSheaf.abSections
      (SheafOfModules.deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p)) q c = 0) :
    hodgeComponentCechEquiv f p q (hodgeCechClass f U hU p c hc) =
      Stacks.Cech.Hypercohomology.cechCocycleClass U hU
        (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) c hc := by
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms f p
  rw [hodgeCechClass_eq]
  exact (congrArg (Stacks.Cech.Hypercohomology.restrictScalarsCechEquiv
      (SheafOfModules.underlyingRingHom (X := X.toRingedSpace) (φ := inverseImageStructureMap f))
      (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) 0
      (cechComputes_deRhamTerm_formsAlgebras f p)
      (Stacks.Cech.Hypercohomology.cechComputesSheaf_of_isQuasicoherent X
        (Scheme.Hom.relativeDifferentialForms f (p : ℤ))) q)
    (Iso.hom_inv_id_apply ((DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
      ((Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIsoBaseSections
        (SheafOfModules.baseRingedSpace
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))).app
        (Stacks.Cech.Hypercohomology.singlePlus
          (SheafOfModules.baseRingedSpace
            ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).sheaf
          (SheafOfModules.deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p) 0))) _)).trans
    (Stacks.Cech.Hypercohomology.restrictScalarsCechEquiv_cechCocycleClassAt U hU
      (SheafOfModules.underlyingRingHom (X := X.toRingedSpace) (φ := inverseImageStructureMap f))
      (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) 0
      (cechComputes_deRhamTerm_formsAlgebras f p)
      (Stacks.Cech.Hypercohomology.cechComputesSheaf_of_isQuasicoherent X
        (Scheme.Hom.relativeDifferentialForms f (p : ℤ))) c hc)

/-- **Every class is the class of a Čech cocycle**, in `Hᵠ(X, Ωᵖ_{X/S})`: through
`hodgeComponentCechEquiv`, a class is the class of a Čech cocycle of `Ωᵖ_{X/S}` on some open
covering ([Stacks, Tag 01XD]). -/
theorem exists_hodgeCechClass_eq (p q : ℕ)
    (x : SheafOfModules.hodgeCohomologyComponent (formsAlgebras f) p (q : ℤ)) :
    ∃ (J : Type u) (V : J → X.Opens) (hV : (⊤ : X.Opens) = ⨆ j, V j)
      (c : CechCochains.Cochain V (Stacks.Cohomology.CechSheaf.abSections
        (SheafOfModules.deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p)) q)
      (hc : CechCochains.cechD V (Stacks.Cohomology.CechSheaf.abSections
        (SheafOfModules.deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p)) q c = 0),
      hodgeCechClass f V hV p c hc = x := by
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms f p
  obtain ⟨J, V, hV, c, hc, h⟩ := Stacks.Cech.Hypercohomology.exists_cechCocycleClassAt_eq
    (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) 0
    (Stacks.Cech.Hypercohomology.cechComputesSheaf_of_isQuasicoherent X
      (Scheme.Hom.relativeDifferentialForms f (p : ℤ))) q (hodgeComponentCechEquiv f p q x)
  exact ⟨J, V, hV, c, hc, (hodgeComponentCechEquiv f p q).injective
    ((hodgeComponentCechEquiv_hodgeCechClass f p V hV c hc).trans h)⟩

/-- **The class of a Čech cocycle is unchanged by refinement** ([Stacks, Tag 01FD]). -/
theorem hodgeCechClass_refinementMap (p : ℕ) {q : ℕ} {I J : Type u} (U : I → X.Opens)
    (hU : (⊤ : X.Opens) = ⨆ i, U i) (V : J → X.Opens) (hV : (⊤ : X.Opens) = ⨆ j, V j)
    (r : J → I) (hr : ∀ j, V j ≤ U (r j))
    (c : CechCochains.Cochain U (Stacks.Cohomology.CechSheaf.abSections
      (SheafOfModules.deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p)) q)
    (hc : CechCochains.cechD U (Stacks.Cohomology.CechSheaf.abSections
      (SheafOfModules.deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p)) q c = 0) :
    hodgeCechClass f V hV p (CechCochains.refinementMap U V r hr _ q c)
        (by rw [← CechCochains.refinementMap_cechD, hc, map_zero]) =
      hodgeCechClass f U hU p c hc :=
  (hodgeComponentCechEquiv f p q).injective
    ((hodgeComponentCechEquiv_hodgeCechClass f p V hV _ _).trans
      ((Stacks.Cech.Hypercohomology.cechCocycleClassAt_refinement U hU
        (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) 0 V hV r hr c hc).trans
        (hodgeComponentCechEquiv_hodgeCechClass f p U hU c hc).symm))

/-- **The comparison `hodgeComponentCechEquiv` carries the cup product of the Weil data to the Čech
cup product along the wedge product**, up to the Koszul sign `(-1)^{q p'}`:
`x ∪ y ↦ (-1)^{q p'} · (x ∪ y)` for `x ∈ H^q(X, Ωᵖ)` and `y ∈ H^{q'}(X, Ω^{p'})`. -/
theorem hodgeComponentCechEquiv_hodgeCohomologyCup (p p' q q' : ℕ)
    (x : SheafOfModules.hodgeCohomologyComponent (formsAlgebras f) p (q : ℤ))
    (y : SheafOfModules.hodgeCohomologyComponent (formsAlgebras f) p' (q' : ℤ)) :
    hodgeComponentCechEquiv f (p + p') (q + q')
        (SheafOfModules.reindexHodgeDeg (formsAlgebras f) (Nat.cast_add q q').symm
          (SheafOfModules.hodgeCohomologyCup (formsAlgebras f) p p' q q' x y)) =
      (((q : ℤ) * p').negOnePow : ℤ) •
        Stacks.Cech.Hypercohomology.cup X.sheaf (cechComputesSheaf_relativeDifferentialForms f p)
          (cechComputesSheaf_relativeDifferentialForms f p')
          (Stacks.Cech.Hypercohomology.singlePairing (Stacks.Cech.Hypercohomology.bilinearPairing
            ((Scheme.Hom.relativeDifferentialFormsAlgebra f).mul (p : ℤ) (p' : ℤ))))
          q q' ((q + q' : ℕ) : ℤ) (by push_cast; rfl) (hodgeComponentCechEquiv f p q x)
          (hodgeComponentCechEquiv f p' q' y) := by
  obtain ⟨J, V, hV, c, hc, rfl⟩ := exists_hodgeCechClass_eq f p q x
  obtain ⟨J', V', hV', e, he, rfl⟩ := exists_hodgeCechClass_eq f p' q' y
  have hW := Stacks.Cech.Hypercohomology.iSup_inf_eq_top V hV V' hV'
  rw [← hodgeCechClass_refinementMap f p V hV _ hW Prod.fst (fun _ => inf_le_left) c hc,
    ← hodgeCechClass_refinementMap f p' V' hV' _ hW Prod.snd (fun _ => inf_le_right) e he,
    hodgeCohomologyCup_hodgeCechClass, SheafOfModules.reindexHodgeDeg_zsmul]
  have hre : ∀ {a b : ℤ} (h : a = b)
      (z : SheafOfModules.hodgeCohomologyComponent (formsAlgebras f) (p + p') a),
      SheafOfModules.reindexHodgeDeg (formsAlgebras f) h.symm
        (SheafOfModules.reindexHodgeDeg (formsAlgebras f) h z) = z := by
    intro a b h z
    subst h
    rfl
  rw [hre, map_zsmul, hodgeComponentCechEquiv_hodgeCechClass,
    hodgeComponentCechEquiv_hodgeCechClass, hodgeComponentCechEquiv_hodgeCechClass]
  exact congrArg _ (Stacks.Cech.Hypercohomology.cup_cechCocycleClass _ hW
    (cechComputesSheaf_relativeDifferentialForms f p)
    (cechComputesSheaf_relativeDifferentialForms f p')
    ((Scheme.Hom.relativeDifferentialFormsAlgebra f).mul (p : ℤ) (p' : ℤ)) _ _ _ _).symm

end Groups

section Powers

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The cup powers `c₁^{Hodge}(L)ᵖ ∈ Hᵖ(X, Ωᵖ_{X/S})` of the Hodge first Chern class** of
`L ∈ Pic(X)`, for the cup product on Hodge cohomology: `c⁰ = 1` and `c^{p+1} = cᵖ ∪ c₁^{Hodge}(L)`,
read in bidegree `(p + 1, p + 1)`. -/
noncomputable def hodgeFirstChernClassPow (L : Stacks.Picard.ofScheme X) :
    (p : ℕ) → SheafOfModules.hodgeCohomologyComponent (formsAlgebras f) p (p : ℤ)
  | 0 => hodgeOne (formsAlgebras f)
  | p + 1 => SheafOfModules.reindexHodgeDeg (formsAlgebras f) (by push_cast; rfl)
      (SheafOfModules.hodgeCohomologyCup (formsAlgebras f) p 1 (p : ℤ) 1
        (hodgeFirstChernClassPow L p) (hodgeFirstChernClassModule f L))

/-- The zeroth cup power `c₁^{Hodge}(L)⁰` of the Hodge first Chern class is the unit class. -/
theorem hodgeFirstChernClassPow_zero (L : Stacks.Picard.ofScheme X) :
    hodgeFirstChernClassPow f L 0 = hodgeOne (formsAlgebras f) :=
  rfl

/-- The `(p + 1)`-st cup power of the Hodge first Chern class is `c₁^{Hodge}(L)ᵖ ∪ c₁^{Hodge}(L)`,
read in bidegree `(p + 1, p + 1)`. -/
theorem hodgeFirstChernClassPow_succ (L : Stacks.Picard.ofScheme X) (p : ℕ) :
    hodgeFirstChernClassPow f L (p + 1) =
      SheafOfModules.reindexHodgeDeg (formsAlgebras f) (by push_cast; rfl)
        (SheafOfModules.hodgeCohomologyCup (formsAlgebras f) p 1 (p : ℤ) 1
          (hodgeFirstChernClassPow f L p) (hodgeFirstChernClassModule f L)) :=
  rfl

/-- **`c₁^{Hodge}(L)¹ = c₁^{Hodge}(L)`**: the unit is a left unit for the cup product. -/
theorem hodgeFirstChernClassPow_one (L : Stacks.Picard.ofScheme X) :
    hodgeFirstChernClassPow f L 1 = hodgeFirstChernClassModule f L :=
  eq_of_heq ((SheafOfModules.reindexHodgeDeg_heq (formsAlgebras f) _ _).trans
    (hodgeOne_hodgeCohomologyCup_heq (formsAlgebras f) 1 1 (hodgeFirstChernClassModule f L)))

/-- The cup product of the zero class with any class is zero. -/
theorem hodgeCohomologyCup_zero_left (p p' : ℕ) (q q' : ℤ)
    (ζ : SheafOfModules.hodgeCohomologyComponent (formsAlgebras f) p' q') :
    SheafOfModules.hodgeCohomologyCup (formsAlgebras f) p p' q q' 0 ζ = 0 := by
  have h := SheafOfModules.hodgeCupProduct_add_left (formsAlgebras f) p p' q q' 0 0 ζ
  rw [add_zero] at h
  exact left_eq_add.mp h

/-- **The unit class is nonzero** as soon as `H⁰(X, Ω⁰_{X/S})` is: `1 ∪ x = x`. -/
theorem hodgeOne_ne_zero
    [Nontrivial (SheafOfModules.hodgeCohomologyComponent (formsAlgebras f) 0 0)] :
    hodgeOne (formsAlgebras f) ≠ 0 := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : SheafOfModules.hodgeCohomologyComponent (formsAlgebras f) 0 0)
  have e := hodgeOne_hodgeCohomologyCup (formsAlgebras f) 0 0 x
  rw [h, hodgeCohomologyCup_zero_left] at e
  exact hx (e.symm.trans (by simp))

end Powers

section ProjectiveSpace

open Stacks.AlgebraicGeometry.ProjectiveSpaceHodge
open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)
open Stacks.ProjectiveSpace.Cohomology (coeffScalar)

variable (k : Type u) [Field k] (r : ℕ)

/-- **The scalars of Hodge cohomology of `ℙʳ_k` over `k` are the coefficients**: `c ∈ k`, read in
`Γ(ℙʳ_k, π⁻¹𝒪_{Spec k})` and then in `Γ(ℙʳ_k, 𝒪)`, is the coefficient `c`. -/
theorem underlyingRingHom_app_top_hodgeScalarsOverField (c : k) :
    ((SheafOfModules.underlyingRingHom (X := (projectiveSpace k r).toRingedSpace)
        (φ := inverseImageStructureMap (projToSpecCoeff k r))).hom.app (op ⊤)).hom
        (hodgeScalarsOverField (projToSpecCoeff k r) c) =
      coeffScalar k r c :=
  congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))
    (Scheme.Hom.inverseImageGlobalSections_comp_inverseImageStructureMap_app (projToSpecCoeff k r))

/-- **`H^q(ℙʳ_k, Ωᵖ)` in the realization of the Weil data is `H^q(ℙʳ_k, Ωᵖ)` computed by right
derived functors of sheaves of `𝒪`-modules**, as `k`-vector spaces. -/
def projectiveHodgeComponentEquiv (p q : ℕ) :
    SheafOfModules.hodgeCohomologyComponent (formsAlgebras (projToSpecCoeff k r)) p (q : ℤ) ≃ₗ[k]
      projectiveHodgeCohomology k r p q where
  toFun x := (projectiveHodgeCohomologyIso k r p q).inv.hom
    (hodgeComponentCechEquiv (projToSpecCoeff k r) p q x)
  invFun y := (hodgeComponentCechEquiv (projToSpecCoeff k r) p q).symm
    ((projectiveHodgeCohomologyIso k r p q).hom.hom y)
  left_inv x := (congrArg (hodgeComponentCechEquiv (projToSpecCoeff k r) p q).symm
      (Iso.inv_hom_id_apply (projectiveHodgeCohomologyIso k r p q) _)).trans
    (AddEquiv.symm_apply_apply _ x)
  right_inv y := (congrArg (projectiveHodgeCohomologyIso k r p q).inv.hom
      (AddEquiv.apply_symm_apply _ _)).trans
    (Iso.hom_inv_id_apply (projectiveHodgeCohomologyIso k r p q) y)
  map_add' x y := (congrArg (projectiveHodgeCohomologyIso k r p q).inv.hom (map_add _ x y)).trans
    (map_add _ _ _)
  map_smul' c x := by
    simp only [RingHom.id_apply]
    rw [hodgeComponent_smul_def, hodgeComponentCechEquiv_smul,
      underlyingRingHom_app_top_hodgeScalarsOverField]
    exact (projectiveHodgeCohomologyIso k r p q).inv.hom.map_smul c _

/-- **[Stacks, Tag 0FMI], the vanishing, in the realization of the Weil data**:
`H^q(ℙʳ_k, Ωᵖ) = 0` unless `p = q ≤ r`. -/
theorem isZero_hodgeCohomologyComponent_projectiveSpace (p : ℕ) (q : ℤ)
    (h : (p : ℤ) ≠ q ∨ r < p) :
    IsZero (SheafOfModules.hodgeCohomologyComponent (formsAlgebras (projToSpecCoeff k r)) p q) := by
  rcases lt_or_ge q 0 with hq | hq
  · exact isZero_hodgeCohomologyComponent_of_neg (formsAlgebras (projToSpecCoeff k r)) p hq
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    have hN := isZero_projectiveHodgeCohomology k r p n (by
      rcases h with h | h
      · exact Or.inl (fun e => h (congrArg Nat.cast e))
      · exact Or.inr h)
    have := ModuleCat.subsingleton_of_isZero hN
    have := (projectiveHodgeComponentEquiv k r p n).toEquiv.subsingleton
    exact ModuleCat.isZero_of_subsingleton _

/-- **[Stacks, Tag 0FMI], the dimension, in the realization of the Weil data**: for `p ≤ r` the
`k`-vector space `Hᵖ(ℙʳ_k, Ωᵖ)` is free of rank one. -/
theorem nonempty_basis_hodgeCohomologyComponent_projectiveSpace (p : ℕ) (hp : p ≤ r) :
    Nonempty (Module.Basis (Fin 1) k
      (SheafOfModules.hodgeCohomologyComponent (formsAlgebras (projToSpecCoeff k r)) p
        (p : ℤ))) := by
  obtain ⟨b, -⟩ := exists_basis_projectiveHodgeChernPow k r p hp
  exact ⟨b.map (projectiveHodgeComponentEquiv k r p p).symm⟩

/-- The cup product of any class with the zero class is zero. -/
private theorem cup_zero_right {X : TopCat.{u}} (O : TopCat.Sheaf CommRingCat.{u} X)
    {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (hF : Stacks.Cech.Hypercohomology.CechComputes O F)
    (hG : Stacks.Cech.Hypercohomology.CechComputes O G)
    (γ : Stacks.Cech.Hypercohomology.Pairing O F G H) (p q t : ℤ) (ht : p + q = t)
    (a : Stacks.Cech.Hypercohomology.hypercohomology O F p) :
    Stacks.Cech.Hypercohomology.cup O hF hG γ p q t ht a 0 = 0 := by
  simpa using Stacks.Cech.Hypercohomology.cup_smul_right O hF hG γ p q t ht a 0 0

/-- The class `c₁^{Hodge}(𝒪(1))ᵖ` of [Stacks, Tag 0FMI] is nonzero for `p ≤ r`. -/
private theorem projectiveChernPowR2_ne_zero (p : ℕ) (hp : p ≤ r) :
    projectiveChernPowR2 k r p ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_basis_projectiveHodgeChernPow k r p hp
  exact fun h => b.ne_zero 0
    (hb.trans ((congrArg (projectiveHodgeCohomologyIso k r p p).inv.hom h).trans (map_zero _)))

/-- **The Hodge first Chern class of `𝒪(1)` on `ℙʳ_k` is nonzero** for `r ≥ 1`, in the realization
of the Weil data: its first power in the base realization is a basis vector of `H¹(ℙʳ_k, Ω¹)`. -/
theorem hodgeFirstChernClassModule_projectiveTwistingSheafOne_ne_zero (hr : 1 ≤ r) :
    hodgeFirstChernClassModule (projToSpecCoeff k r) (projectiveTwistingSheafOnePicardClass k r) ≠
      0 := by
  intro h
  have hc : Scheme.Hom.hodgeFirstChernClass (projToSpecCoeff k r)
      (projectiveTwistingSheafOnePicardClass k r) = 0 :=
    (hodgeCohomologyOneIsoComponent_inv_hodgeFirstChernClassModule (projToSpecCoeff k r)
      (projectiveTwistingSheafOnePicardClass k r)).symm.trans
      ((congrArg (hodgeCohomologyOneIsoComponent (projToSpecCoeff k r)).inv.hom h).trans
        (map_zero _))
  have e := Stacks.Cech.Hypercohomology.abelianToModuleH1_naturality
    (F := Stacks.AlgebraicGeometry.ProjEulerSequence.projDifferentials k r)
    (G := Stacks.AlgebraicGeometry.ProjEulerSequence.projDifferentials k r)
    (Stacks.Cohomology.InvertibleDerived.smulHom (X := (projectiveSpace k r).toRingedSpace) 0
      (Stacks.AlgebraicGeometry.ProjEulerSequence.projDifferentials k r)) 0
  have e2 := Stacks.Cech.Hypercohomology.hypercohomologyMap_smulHom
    (X := (projectiveSpace k r).toRingedSpace) 0
    (Stacks.AlgebraicGeometry.ProjEulerSequence.projDifferentials k r) 0
    (cechComputesSheaf_projDifferentials k r) 1
    (Stacks.Cech.Hypercohomology.abelianToModuleH1
      (Stacks.AlgebraicGeometry.ProjEulerSequence.projDifferentials k r) 0)
  have hz : Stacks.Cech.Hypercohomology.abelianToModuleH1
      (Stacks.AlgebraicGeometry.ProjEulerSequence.projDifferentials k r) 0 = 0 :=
    (congrArg (Stacks.Cech.Hypercohomology.abelianToModuleH1
      (Stacks.AlgebraicGeometry.ProjEulerSequence.projDifferentials k r)) (map_zero _).symm).trans
      (e.trans (e2.trans (zero_smul _ _)))
  have h0 : projectiveHodgeFirstChernClassModule k r = 0 := by
    change Stacks.Cech.Hypercohomology.abelianToModuleH1 _
      (Scheme.Hom.hodgeFirstChernClass (projToSpecCoeff k r)
        (projectiveTwistingSheafOnePicardClass k r)) = 0
    rw [hc]
    exact hz
  have h1 : projectiveChernPowR2 k r 1 = 0 := by
    change Stacks.Cech.Hypercohomology.cup (projectiveSpace k r).sheaf
      (cechComputesSheaf_projectiveForms k r 0) (cechComputesSheaf_projDifferentials k r)
      (projectiveWedgePairing k r 0) 0 1 ((0 + 1 : ℕ) : ℤ) _ (projectiveChernPowR2 k r 0)
      (projectiveHodgeFirstChernClassModule k r) = 0
    rw [h0]
    exact cup_zero_right _ _ _ _ _ _ _ _ _
  exact projectiveChernPowR2_ne_zero k r 1 hr h1

/-- **The cup product with a class of `Ω` is the cup product with its image in `Ω¹`**: the wedge
product `Ωᵖ × Ω ⟶ Ω^{p+1}` is the wedge product `Ωᵖ × Ω¹ ⟶ Ω^{p+1}` precomposed with the
degree-one generator `Ω ⟶ ⋀¹Ω`. -/
theorem cup_projectiveWedgePairing (p : ℕ)
    (x : Stacks.Cech.Hypercohomology.hypercohomology (projectiveSpace k r).sheaf
      (Stacks.Cech.Hypercohomology.singlePlus (projectiveSpace k r).sheaf (projectiveForms k r p) 0)
      (p : ℤ))
    (c : Stacks.Cech.Hypercohomology.hypercohomology (projectiveSpace k r).sheaf
      (Stacks.Cech.Hypercohomology.singlePlus (projectiveSpace k r).sheaf
        (Stacks.AlgebraicGeometry.ProjEulerSequence.projDifferentials k r) 0) 1) :
    Stacks.Cech.Hypercohomology.cup (projectiveSpace k r).sheaf
        (cechComputesSheaf_projectiveForms k r p) (cechComputesSheaf_projDifferentials k r)
        (projectiveWedgePairing k r p) p 1 ((p + 1 : ℕ) : ℤ) (by push_cast; ring) x c =
      Stacks.Cech.Hypercohomology.cup (projectiveSpace k r).sheaf
        (cechComputesSheaf_projectiveForms k r p) (cechComputesSheaf_projectiveForms k r 1)
        (Stacks.Cech.Hypercohomology.singlePairing (Stacks.Cech.Hypercohomology.bilinearPairing
          ((Scheme.Hom.relativeDifferentialFormsAlgebra (projToSpecCoeff k r)).mul (p : ℤ)
            ((1 : ℕ) : ℤ))))
        p ((1 : ℕ) : ℤ) ((p + 1 : ℕ) : ℤ) (by push_cast; rfl) x
        (Stacks.Cech.Hypercohomology.hypercohomologyMap (projectiveSpace k r).sheaf
          (Stacks.Cech.Hypercohomology.singlePlusMap (projectiveSpace k r).sheaf
            (Scheme.Modules.exteriorGenerator
              (Scheme.Hom.relativeDifferentials (projToSpecCoeff k r)))) 1 c) := by
  have hP := Stacks.Cech.Hypercohomology.pairingHom_singlePairing
    (O := (projectiveSpace k r).sheaf) (𝟙 (projectiveForms k r p))
    (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials (projToSpecCoeff k r)))
    (𝟙 (projectiveForms k r (p + 1))) (projectiveWedgeBilinear k r p)
    ((Scheme.Hom.relativeDifferentialFormsAlgebra (projToSpecCoeff k r)).mul (p : ℤ) ((1 : ℕ) : ℤ))
    (fun _ _ _ => rfl)
  have hid : ∀ (F : _root_.SheafOfModules.{u} (ringSheaf (projectiveSpace k r).sheaf)) (n : ℤ)
      (z : Stacks.Cech.Hypercohomology.hypercohomology (projectiveSpace k r).sheaf
        (Stacks.Cech.Hypercohomology.singlePlus (projectiveSpace k r).sheaf F 0) n),
      Stacks.Cech.Hypercohomology.hypercohomologyMap (projectiveSpace k r).sheaf
        (Stacks.Cech.Hypercohomology.singlePlusMap (projectiveSpace k r).sheaf (𝟙 F)) n z = z :=
    fun F n z => by
      have h1 : Stacks.Cech.Hypercohomology.singlePlusMap (projectiveSpace k r).sheaf (𝟙 F) = 𝟙 _ :=
        ObjectProperty.hom_ext _ ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map_id F)
      rw [h1, Stacks.Cech.Hypercohomology.hypercohomologyMap_id]
      rfl
  have h := Stacks.Cech.Hypercohomology.cup_natural (projectiveSpace k r).sheaf
    (cechComputesSheaf_projectiveForms k r p) (cechComputesSheaf_projDifferentials k r)
    (cechComputesSheaf_projectiveForms k r p) (cechComputesSheaf_projectiveForms k r 1) _ _ _ _ _ hP
    (p : ℤ) 1 ((p + 1 : ℕ) : ℤ) (by push_cast; ring) x c
  exact (hid (projectiveForms k r (p + 1)) _ _).symm.trans (h.trans
    (congrArg (fun z => Stacks.Cech.Hypercohomology.cup (projectiveSpace k r).sheaf
      (cechComputesSheaf_projectiveForms k r p) (cechComputesSheaf_projectiveForms k r 1)
      (Stacks.Cech.Hypercohomology.singlePairing (Stacks.Cech.Hypercohomology.bilinearPairing
        ((Scheme.Hom.relativeDifferentialFormsAlgebra (projToSpecCoeff k r)).mul (p : ℤ)
          ((1 : ℕ) : ℤ))))
      p ((1 : ℕ) : ℤ) ((p + 1 : ℕ) : ℤ) (by push_cast; rfl) z
      (Stacks.Cech.Hypercohomology.hypercohomologyMap (projectiveSpace k r).sheaf
        (Stacks.Cech.Hypercohomology.singlePlusMap (projectiveSpace k r).sheaf
          (Scheme.Modules.exteriorGenerator
            (Scheme.Hom.relativeDifferentials (projToSpecCoeff k r)))) 1 c))
      (hid (projectiveForms k r p) _ x)))

/-- **A nonzero class of `Hᵖ(ℙʳ_k, Ωᵖ)` is a nonzero multiple of `c₁^{Hodge}(𝒪(1))ᵖ`** in the base
realization, for `p ≤ r`: that vector space is free of rank one with this basis element. -/
theorem exists_ne_zero_smul_projectiveChernPowR2 (p : ℕ) (hp : p ≤ r)
    (v : Stacks.Cech.Hypercohomology.hypercohomology (projectiveSpace k r).sheaf
      (Stacks.Cech.Hypercohomology.singlePlus (projectiveSpace k r).sheaf (projectiveForms k r p) 0)
      (p : ℤ)) (hv : v ≠ 0) :
    ∃ t : k, t ≠ 0 ∧ v = (show Stacks.Cohomology.CechSheaf.SectionRing
      (ringSheaf (projectiveSpace k r).sheaf) ⊤ from coeffScalar k r t) •
        projectiveChernPowR2 k r p := by
  obtain ⟨b, hb⟩ := exists_basis_projectiveHodgeChernPow k r p hp
  let b' := b.map (projectiveHodgeCohomologyIso k r p p).toLinearEquiv
  have hb' : b' 0 = projectiveChernPowR2 k r p := by
    rw [Module.Basis.map_apply, hb]
    exact Iso.inv_hom_id_apply (projectiveHodgeCohomologyIso k r p p) _
  have hv' := b'.eq_repr_smul v
  refine ⟨b'.repr v 0, fun ht => hv ?_, ?_⟩
  · rw [hv', ht, zero_smul]
    rfl
  · rw [hb'] at hv'
    exact hv'

/-- **In the base realization, `c₁^{Hodge}(𝒪(1))` of the Weil data is a nonzero multiple of the
image in `H¹(ℙʳ_k, Ω¹)` of the Hodge first Chern class of `𝒪(1)` in `H¹(ℙʳ_k, Ω)`**, for
`r ≥ 1`: both are nonzero vectors of a vector space of dimension one. -/
theorem exists_ne_zero_smul_hodgeFirstChernClassModule (hr : 1 ≤ r) :
    ∃ t : k, t ≠ 0 ∧ hodgeComponentCechEquiv (projToSpecCoeff k r) 1 1
        (hodgeFirstChernClassModule (projToSpecCoeff k r)
          (projectiveTwistingSheafOnePicardClass k r)) =
      (show Stacks.Cohomology.CechSheaf.SectionRing (ringSheaf (projectiveSpace k r).sheaf) ⊤ from
        coeffScalar k r t) •
        Stacks.Cech.Hypercohomology.hypercohomologyMap (projectiveSpace k r).sheaf
          (Stacks.Cech.Hypercohomology.singlePlusMap (projectiveSpace k r).sheaf
            (Scheme.Modules.exteriorGenerator
              (Scheme.Hom.relativeDifferentials (projToSpecCoeff k r)))) 1
          (projectiveHodgeFirstChernClassModule k r) := by
  have hC : projectiveChernPowR2 k r 1 = Stacks.Cech.Hypercohomology.cup (projectiveSpace k r).sheaf
      (cechComputesSheaf_projectiveForms k r 0) (cechComputesSheaf_projectiveForms k r 1)
      (Stacks.Cech.Hypercohomology.singlePairing (Stacks.Cech.Hypercohomology.bilinearPairing
        ((Scheme.Hom.relativeDifferentialFormsAlgebra (projToSpecCoeff k r)).mul ((0 : ℕ) : ℤ)
          ((1 : ℕ) : ℤ))))
      ((0 : ℕ) : ℤ) ((1 : ℕ) : ℤ) ((0 + 1 : ℕ) : ℤ) (by norm_num) (projectiveChernPowR2 k r 0)
      (Stacks.Cech.Hypercohomology.hypercohomologyMap (projectiveSpace k r).sheaf
        (Stacks.Cech.Hypercohomology.singlePlusMap (projectiveSpace k r).sheaf
          (Scheme.Modules.exteriorGenerator
            (Scheme.Hom.relativeDifferentials (projToSpecCoeff k r)))) 1
        (projectiveHodgeFirstChernClassModule k r)) :=
    cup_projectiveWedgePairing k r 0 _ _
  have hC1 := projectiveChernPowR2_ne_zero k r 1 hr
  have hg : Stacks.Cech.Hypercohomology.hypercohomologyMap (projectiveSpace k r).sheaf
      (Stacks.Cech.Hypercohomology.singlePlusMap (projectiveSpace k r).sheaf
        (Scheme.Modules.exteriorGenerator
          (Scheme.Hom.relativeDifferentials (projToSpecCoeff k r)))) 1
      (projectiveHodgeFirstChernClassModule k r) ≠ 0 := by
    intro hg
    apply hC1
    rw [hC, hg]
    exact cup_zero_right _ _ _ _ _ _ _ _ _
  obtain ⟨s', hs', hgs⟩ := exists_ne_zero_smul_projectiveChernPowR2 k r 1 hr _ hg
  have hv : hodgeComponentCechEquiv (projToSpecCoeff k r) 1 1
      (hodgeFirstChernClassModule (projToSpecCoeff k r)
        (projectiveTwistingSheafOnePicardClass k r)) ≠
        0 := fun h => hodgeFirstChernClassModule_projectiveTwistingSheafOne_ne_zero k r hr
    ((hodgeComponentCechEquiv (projToSpecCoeff k r) 1 1).injective (h.trans (map_zero _).symm))
  obtain ⟨s, hs, hvs⟩ := exists_ne_zero_smul_projectiveChernPowR2 k r 1 hr _ hv
  refine ⟨s / s', div_ne_zero hs hs', ?_⟩
  rw [hgs]
  have hm : (show Stacks.Cohomology.CechSheaf.SectionRing (ringSheaf (projectiveSpace k r).sheaf) ⊤
      from coeffScalar k r s) =
      (show Stacks.Cohomology.CechSheaf.SectionRing (ringSheaf (projectiveSpace k r).sheaf) ⊤
        from coeffScalar k r (s / s')) *
      (show Stacks.Cohomology.CechSheaf.SectionRing (ringSheaf (projectiveSpace k r).sheaf) ⊤
        from coeffScalar k r s') :=
    (congrArg (coeffScalar k r) (div_mul_cancel₀ s hs')).symm.trans (map_mul _ _ _)
  exact hvs.trans ((congrArg (· • projectiveChernPowR2 k r 1) hm).trans (mul_smul _ _ _))

/-- **In the base realization, `c₁^{Hodge}(𝒪(1))ᵖ` of the Weil data is a nonzero multiple of
`c₁^{Hodge}(𝒪(1))ᵖ` of [Stacks, Tag 0FMI]**, for `p ≤ r`: by induction on `p`, using that the
comparison carries cup products to cup products up to sign. -/
theorem exists_ne_zero_smul_hodgeFirstChernClassPow : (p : ℕ) → p ≤ r →
    ∃ t : k, t ≠ 0 ∧ hodgeComponentCechEquiv (projToSpecCoeff k r) p p
        (hodgeFirstChernClassPow (projToSpecCoeff k r)
          (projectiveTwistingSheafOnePicardClass k r) p) =
      (show Stacks.Cohomology.CechSheaf.SectionRing (ringSheaf (projectiveSpace k r).sheaf) ⊤ from
        coeffScalar k r t) • projectiveChernPowR2 k r p
  | 0, _ => by
    obtain ⟨b⟩ := nonempty_basis_hodgeCohomologyComponent_projectiveSpace k r 0 (Nat.zero_le r)
    have : Nontrivial (SheafOfModules.hodgeCohomologyComponent
        (formsAlgebras (projToSpecCoeff k r)) 0 0) := ⟨⟨b 0, 0, b.ne_zero 0⟩⟩
    have hv : hodgeComponentCechEquiv (projToSpecCoeff k r) 0 0
        (hodgeFirstChernClassPow (projToSpecCoeff k r)
          (projectiveTwistingSheafOnePicardClass k r) 0) ≠
          0 := fun h => hodgeOne_ne_zero (projToSpecCoeff k r)
      ((hodgeComponentCechEquiv (projToSpecCoeff k r) 0 0).injective (h.trans (map_zero _).symm))
    exact exists_ne_zero_smul_projectiveChernPowR2 k r 0 (Nat.zero_le r) _ hv
  | p + 1, hp => by
    obtain ⟨t, ht, hpt⟩ := exists_ne_zero_smul_hodgeFirstChernClassPow p (Nat.le_of_succ_le hp)
    obtain ⟨t₁, ht₁, h₁⟩ := exists_ne_zero_smul_hodgeFirstChernClassModule k r
      ((Nat.le_add_left 1 p).trans hp)
    have hcup := hodgeComponentCechEquiv_hodgeCohomologyCup (projToSpecCoeff k r) p 1 p 1
      (hodgeFirstChernClassPow (projToSpecCoeff k r) (projectiveTwistingSheafOnePicardClass k r) p)
      (hodgeFirstChernClassModule (projToSpecCoeff k r) (projectiveTwistingSheafOnePicardClass k r))
    rw [hpt, h₁] at hcup
    have eL := Stacks.Cech.Hypercohomology.cup_smul_left (projectiveSpace k r).sheaf
      (cechComputesSheaf_projectiveForms k r p) (cechComputesSheaf_projectiveForms k r 1)
      (Stacks.Cech.Hypercohomology.singlePairing (Stacks.Cech.Hypercohomology.bilinearPairing
        ((Scheme.Hom.relativeDifferentialFormsAlgebra (projToSpecCoeff k r)).mul (p : ℤ)
          ((1 : ℕ) : ℤ))))
      p ((1 : ℕ) : ℤ) ((p + 1 : ℕ) : ℤ) (Nat.cast_add p 1).symm (projectiveChernPowR2 k r p)
      ((show Stacks.Cohomology.CechSheaf.SectionRing (ringSheaf (projectiveSpace k r).sheaf) ⊤
        from coeffScalar k r t₁) •
        Stacks.Cech.Hypercohomology.hypercohomologyMap (projectiveSpace k r).sheaf
          (Stacks.Cech.Hypercohomology.singlePlusMap (projectiveSpace k r).sheaf
            (Scheme.Modules.exteriorGenerator
              (Scheme.Hom.relativeDifferentials (projToSpecCoeff k r)))) 1
          (projectiveHodgeFirstChernClassModule k r))
      (show Stacks.Cohomology.CechSheaf.SectionRing (ringSheaf (projectiveSpace k r).sheaf) ⊤
        from coeffScalar k r t)
    have eR := Stacks.Cech.Hypercohomology.cup_smul_right (projectiveSpace k r).sheaf
      (cechComputesSheaf_projectiveForms k r p) (cechComputesSheaf_projectiveForms k r 1)
      (Stacks.Cech.Hypercohomology.singlePairing (Stacks.Cech.Hypercohomology.bilinearPairing
        ((Scheme.Hom.relativeDifferentialFormsAlgebra (projToSpecCoeff k r)).mul (p : ℤ)
          ((1 : ℕ) : ℤ))))
      p ((1 : ℕ) : ℤ) ((p + 1 : ℕ) : ℤ) (Nat.cast_add p 1).symm (projectiveChernPowR2 k r p)
      (Stacks.Cech.Hypercohomology.hypercohomologyMap (projectiveSpace k r).sheaf
          (Stacks.Cech.Hypercohomology.singlePlusMap (projectiveSpace k r).sheaf
            (Scheme.Modules.exteriorGenerator
              (Scheme.Hom.relativeDifferentials (projToSpecCoeff k r)))) 1
          (projectiveHodgeFirstChernClassModule k r))
      (show Stacks.Cohomology.CechSheaf.SectionRing (ringSheaf (projectiveSpace k r).sheaf) ⊤
        from coeffScalar k r t₁)
    have eW := (cup_projectiveWedgePairing k r p (projectiveChernPowR2 k r p)
      (projectiveHodgeFirstChernClassModule k r)).symm
    refine ⟨((((p : ℤ) * ((1 : ℕ) : ℤ)).negOnePow : ℤ) : k) * t * t₁,
      mul_ne_zero (mul_ne_zero ((Units.isUnit _).map (Int.castRingHom k)).ne_zero ht) ht₁,
      hcup.trans ((congrArg (fun z => (((p : ℤ) * ((1 : ℕ) : ℤ)).negOnePow : ℤ) • z)
        (eL.trans (congrArg (fun z => (show Stacks.Cohomology.CechSheaf.SectionRing
          (ringSheaf (projectiveSpace k r).sheaf) ⊤ from coeffScalar k r t) • z)
          (eR.trans (congrArg (fun z => (show Stacks.Cohomology.CechSheaf.SectionRing
            (ringSheaf (projectiveSpace k r).sheaf) ⊤ from coeffScalar k r t₁) • z)
          eW))))).trans ?_)⟩
    have hm : (show Stacks.Cohomology.CechSheaf.SectionRing (ringSheaf (projectiveSpace k r).sheaf)
        ⊤ from coeffScalar k r ((((p : ℤ) * ((1 : ℕ) : ℤ)).negOnePow : ℤ) * t * t₁)) =
        ((((p : ℤ) * ((1 : ℕ) : ℤ)).negOnePow : ℤ) :
          Stacks.Cohomology.CechSheaf.SectionRing (ringSheaf (projectiveSpace k r).sheaf) ⊤) *
        (show Stacks.Cohomology.CechSheaf.SectionRing (ringSheaf (projectiveSpace k r).sheaf) ⊤
          from coeffScalar k r t) *
        (show Stacks.Cohomology.CechSheaf.SectionRing (ringSheaf (projectiveSpace k r).sheaf) ⊤
          from coeffScalar k r t₁) :=
      (map_mul (coeffScalar k r) _ t₁).trans (congrArg (· * coeffScalar k r t₁)
        ((map_mul (coeffScalar k r) _ t).trans (congrArg (· * coeffScalar k r t)
          (map_intCast (coeffScalar k r) (((p : ℤ) * ((1 : ℕ) : ℤ)).negOnePow : ℤ)))))
    exact (((Int.cast_smul_eq_zsmul _ _ _).symm.trans (mul_smul _ _ _).symm).trans
      ((mul_smul _ _ _).symm)).trans (congrArg (· • projectiveChernPowR2 k r (p + 1)) hm.symm)

/-- **[Stacks, Tag 0FMI], in the realization of the Weil data**: for `p ≤ r` the Hodge cohomology
`Hᵖ(ℙʳ_k, Ωᵖ)` is a `k`-vector space of dimension one with basis `c₁^{Hodge}(𝒪(1))ᵖ`. -/
theorem exists_basis_hodgeFirstChernClassPow (p : ℕ) (hp : p ≤ r) :
    ∃ b : Module.Basis (Fin 1) k
      (SheafOfModules.hodgeCohomologyComponent (formsAlgebras (projToSpecCoeff k r)) p (p : ℤ)),
      b 0 = hodgeFirstChernClassPow (projToSpecCoeff k r)
        (projectiveTwistingSheafOnePicardClass k r) p := by
  obtain ⟨b⟩ := nonempty_basis_hodgeCohomologyComponent_projectiveSpace k r p hp
  have hf : Module.finrank k (SheafOfModules.hodgeCohomologyComponent
      (formsAlgebras (projToSpecCoeff k r)) p (p : ℤ)) = 1 := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hC := projectiveChernPowR2_ne_zero k r p hp
  obtain ⟨t, ht, hpt⟩ := exists_ne_zero_smul_hodgeFirstChernClassPow k r p hp
  have hne : hodgeFirstChernClassPow (projToSpecCoeff k r)
      (projectiveTwistingSheafOnePicardClass k r) p ≠ 0 := by
    intro h
    rw [h, map_zero] at hpt
    have hinv : (show Stacks.Cohomology.CechSheaf.SectionRing
        (ringSheaf (projectiveSpace k r).sheaf) ⊤
        from coeffScalar k r t⁻¹) *
        (show Stacks.Cohomology.CechSheaf.SectionRing (ringSheaf (projectiveSpace k r).sheaf) ⊤
          from coeffScalar k r t) = 1 :=
      (map_mul _ _ _).symm.trans ((congrArg _ (inv_mul_cancel₀ ht)).trans (map_one _))
    exact hC ((((one_smul _ _).symm.trans
      (congrArg (· • projectiveChernPowR2 k r p) hinv.symm)).trans
      (mul_smul _ _ _)).trans ((congrArg (_ • ·) hpt.symm).trans (smul_zero _)))
  exact ⟨FiniteDimensional.basisSingleton (Fin 1) hf _ hne,
    FiniteDimensional.basisSingleton_apply _ _ _ _ _⟩

end ProjectiveSpace

end Stacks.HodgeWeil

end
