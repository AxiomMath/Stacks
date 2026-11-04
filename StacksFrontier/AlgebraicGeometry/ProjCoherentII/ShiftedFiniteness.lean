module

public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.ShiftComposition
public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.TwistedFiniteness
public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.TwistedToShiftedScalar
public import StacksFrontier.AlgebraicGeometry.ProjCoherentModule.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two finiteness assertions of Tag 0B5R for the sections of a finite graded module

Let `S = ⨁_{i ≥ 0} 𝒮 i` be a Noetherian graded ring, `M = ⨁_{n ∈ ℤ} 𝒨 n` a finite graded
`S`-module, `X = Proj 𝒮` and `k ∈ ℤ`. [Stacks, Tag 0B5R] studies the two graded `S`-modules

`N = ⨁_{n ≥ k} H⁰(X, M̃(n))`   and   `N' = ⨁_{n ≥ k} H⁰(X, M(n)~)`,

the first built from the twists of the associated sheaf and the second from the associated
sheaves of the shifted modules. This file proves the two finiteness assertions of the tag:
part **(2)**, that `N` is a finite `S`-module, and part **(1)**, that `N'` is. No generation
hypothesis on `S` appears; in particular `S` is not assumed generated in degree one over `S₀`.

## The source's proof

Part (2) is immediate from what the library already has. `M` is a finite `S`-module and `S` is
Noetherian, so `M̃` is coherent
(`AlgebraicGeometry.ProjectiveSpectrum.Proj.isCoherent_associatedModuleSheaf`), and
`Stacks.AlgebraicGeometry.ProjCoherentII.moduleFinite_truncation_of_isCoherent` is exactly the
assertion for an arbitrary coherent sheaf.

Part (1) is the source's Veronese reduction, run on the shifted side. A degree `d` is chosen by
`Stacks.AlgebraicGeometry.ProjCoherentII.exists_reductionDegree`, the degrees are split into the
`d` residue classes `n = md + q`, and for each class the source writes

`M(md + q)~ = M(q)(md)~ ≅ (M(q)~)(md) ≅ i_*(M(q)~)(m)` on `X' = Proj S⁽ᵈ⁾`,

where the first identification is an identity of graded modules, the second is [Stacks, Tag
01MU] — bijective on global sections precisely because `d ∣ md`, which is part (6) of this tag —
and the third is [Stacks, Tag 0B5J]. On `X'` the graded ring is generated in degree one, so
assertion (4) of [Stacks, Tag 0AG6] applies to the coherent module `i_*(M(q)~)`; the `d`
resulting finite families are assembled over `S` by
`Stacks.AlgebraicGeometry.ProjTwistedSections.moduleFinite_gradedActionTruncation_of_residues`.

Two of those three identifications are already in the library, as
`Stacks.AlgebraicGeometry.ProjCoherentII.veroneseSectionsComparison` and
`Stacks.AlgebraicGeometry.ProjCoherentII.twistedToShiftedComponent`, and so is each one's
semilinearity over `S⁽ᵈ⁾ ⊆ S`. What this file adds is **the first identification as a semilinear
map**: the shift of a shift `M(q)(n) = M(n + q)` is an equality of gradings, hence an equality of
associated sheaves and an equality of their groups of global sections, and the content is that
the homogeneous scalar action of [Stacks, Tag 01MR] is carried across it.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjCoherentII.associatedSectionsCongrEquiv`: the transport of
  global sections along an equality of gradings.
* `Stacks.AlgebraicGeometry.ProjCoherentII.shiftedSectionsShiftEquiv`: the shift identification
  `H⁰(X, M(q)(n)~) ≃+ H⁰(X, M(n + q)~)`.
* `Stacks.AlgebraicGeometry.ProjCoherentII.shiftedSectionsCastEquiv`: the transport of a shifted
  global section along an equality of degrees.
* `Stacks.AlgebraicGeometry.ProjCoherentII.shiftedResidueComparison`: the comparison
  `Γ(X', ℱ'(m)) → H⁰(X, M(md + q)~)` of one residue class.

## Main results

* `Stacks.AlgebraicGeometry.ProjCoherentII`
  `.shiftedSectionsShiftEquiv_homogeneousScalarGlobalSections`: the shift identification carries
  the homogeneous scalar action of [Stacks, Tag 01MR] to itself.
* `Stacks.AlgebraicGeometry.ProjCoherentII`
  `.shiftedResidueComparison_homogeneousScalarGlobalSections` and
  `Stacks.AlgebraicGeometry.ProjCoherentII.surjective_shiftedResidueComparison`: the residue
  comparison is semilinear over `S⁽ᵈ⁾ ⊆ S`, and surjective.
* `Stacks.AlgebraicGeometry.ProjCoherentII.moduleFinite_twistedTruncation`: **part (2)**, `N` is
  a finite `S`-module.
* `Stacks.AlgebraicGeometry.ProjCoherentII.moduleFinite_shiftedTruncation`: **part (1)**, `N'` is
  a finite `S`-module.

## Implementation notes

**The shift identification is an equality of types, and the scalar action is carried across it
pointwise.** `AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf` takes no
decomposition datum and its only hypothesis on the grading is `Prop`-valued, so equal gradings
give *equal* sheaves
(`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf_congr`) and the transport is a
`cast`. The compatibility with the scalar action cannot be `rfl`: the two gradings
`i ↦ 𝒨 ((i + n) + q)` and `i ↦ 𝒨 (i + (n + q))` are equal only propositionally. It is proved in
the module fibres, where there is nothing to prove — a section of either sheaf is a dependent
function into the ambient fibres, the `cast` does not move it, and the action is multiplication by
the scalar on both sides. That is the same move as in
`Stacks.AlgebraicGeometry.ModuleTwistIso.moduleTwistMap_tmul_eq_homogeneousScalar`, and
`Stacks.AlgebraicGeometry.ProjShiftedSections.homogeneousScalarGlobalSections_apply` is the
pointwise formula it rests on.

**The degree equations are named theorems and never written inline.** Writing `by ring` inside a
`cast` makes the two sides of an `exact` elaborate two distinct proofs of the same arithmetic and
the unifier reduces them before proof irrelevance can be used. Only one equation is new here,
`shiftScalarDegree`; the others are reused from
`StacksFrontier/AlgebraicGeometry/ProjCoherentII/TwistedFiniteness.lean` and
`StacksFrontier/AlgebraicGeometry/ProjCoherentII/TwistIterateScalar.lean`.

**Why the twisted comparison enters where it does.** The residue comparison goes up through the
*twisted* sections of `M(q)~` and only then crosses to the shifted side, by
`Stacks.AlgebraicGeometry.ProjCoherentII.twistedToShiftedComponent` at the degree `md`. Crossing
at the degree `md + q` instead is not available: part (6) of the tag needs `d` to divide the
degree, and `d ∤ md + q` for `q ≠ 0`. Twisting the module by `q` first is what makes the degree
divisible, and it is the only place in part (1) where `d` is used for anything but the residue
bookkeeping.

The lower bound upstairs is `k' = ⌊(k - q - 1)/d⌋ + 1`, and
`Stacks.AlgebraicGeometry.ProjCoherentII.residueBoundIff` is the equivalence `k' ≤ m ↔ k ≤ md + q`
that the transport asks for.

## References

* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
* [Stacks Project, Tag 0AG6](https://stacks.math.columbia.edu/tag/0AG6)
* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
* [Stacks Project, Tag 01MQ](https://stacks.math.columbia.edu/tag/01MQ)
* [Stacks Project, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheaf
  associatedModuleSheafSectionsEquiv associatedModuleSheaf_congr
  isCoherent_associatedModuleSheaf)
open Stacks.AlgebraicGeometry.ModuleTwistIso (twistIterateScalarDegree)
open Stacks.AlgebraicGeometry.ProjShiftedSections (shiftedSectionsComponent
  shiftedModuleGlobalSections globalSectionsModuleMap homogeneousScalarGlobalSections
  homogeneousScalarGlobalSections_apply)
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistedSectionsComponent
  homogeneousScalarTwistedSections twistedGlobalSectionsModule residueScalarDegree
  exists_finite_span_residue moduleFinite_gradedActionTruncation_of_residues)
open Stacks.GradedModule (shiftedGrading shiftedGrading_shiftedGrading)
open Stacks.Veronese (veroneseGrading veroneseSubring veroneseGradingGradedRing
  veronesePushforward veronesePushforwardPullbackIso veroneseProjIso pullbackProjModule
  isNoetherianRing_veroneseGrading_zero isCoherent_veronesePushforward
  exists_finite_degreeOne_generators_veroneseSubring)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjCoherentII

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

/-! ### The degree bookkeeping -/

/-- **The degree bookkeeping of the shift identification.** A homogeneous scalar of degree `i`
carries the degree-`n` sections of `M(q)` to the degree-`i + n` ones, which the shift
identification reads in degree `(i + n) + q`; downstairs the same scalar carries degree `n + q` to
degree `i + (n + q)`. -/
public theorem shiftScalarDegree (i : ℕ) (n q : ℤ) : (i : ℤ) + (n + q) = ((i : ℤ) + n) + q :=
  (add_assoc (i : ℤ) n q).symm

variable {S M : Type u} {σ τ : Type u}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M]

/-! ### Transporting a global section along an equality of gradings -/

section Congr

variable {𝒩₁ 𝒩₂ : ℤ → τ} [SetLike.GradedSMul 𝒮 𝒩₁] [SetLike.GradedSMul 𝒮 𝒩₂]

/-- **Equal gradings have the same group of global sections.** The two associated sheaves are
equal, not merely isomorphic, by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf_congr`, so their groups of
sections over `⊤` are the same type. -/
public theorem associatedSections_congr (h : 𝒩₁ = 𝒩₂) :
    (↥((associatedModuleSheaf 𝒮 𝒩₁).val.obj (op ⊤)) : Type u) =
      ↥((associatedModuleSheaf 𝒮 𝒩₂).val.obj (op ⊤)) := by
  subst h
  rfl

/-- **The transport of a global section along an equality of gradings**, as an isomorphism of
additive groups. It is `cast` on the type of sections, which is the spelling the semilinearity
squares of the library are stated in. -/
public def associatedSectionsCongrEquiv (h : 𝒩₁ = 𝒩₂) :
    ↥((associatedModuleSheaf 𝒮 𝒩₁).val.obj (op ⊤)) ≃+
      ↥((associatedModuleSheaf 𝒮 𝒩₂).val.obj (op ⊤)) where
  toFun := cast (associatedSections_congr 𝒮 h)
  invFun := cast (associatedSections_congr 𝒮 h.symm)
  left_inv _ := by subst h; rfl
  right_inv _ := by subst h; rfl
  map_add' _ _ := by subst h; rfl

/-- **The transport along an equality of gradings does not move the section.** A section of
either associated sheaf is a dependent function into the ambient module fibres, which do not
mention the grading, and the transport leaves that function alone. -/
public theorem coe_associatedSectionsCongrEquiv [DirectSum.Decomposition 𝒩₁]
    [DirectSum.Decomposition 𝒩₂] (h : 𝒩₁ = 𝒩₂)
    (s : ↥((associatedModuleSheaf 𝒮 𝒩₁).val.obj (op ⊤)))
    (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) :
    ((associatedModuleSheafSectionsEquiv 𝒮 𝒩₂ ⊤).toFun
        (associatedSectionsCongrEquiv 𝒮 h s)).1 x =
      ((associatedModuleSheafSectionsEquiv 𝒮 𝒩₁ ⊤).toFun s).1 x := by
  subst h
  rfl

end Congr

variable (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨]

/-! ### The shift identification on global sections -/

/-- **The shift identification `H⁰(X, M(q)(n)~) ≃+ H⁰(X, M(n + q)~)`.** The gradings of `M(q)(n)`
and of `M(n + q)` are the same family of subobjects
(`Stacks.GradedModule.shiftedGrading_shiftedGrading`), so this is the transport of a global
section along an equality of gradings and not a comparison map. -/
public def shiftedSectionsShiftEquiv (q n : ℤ) :
    shiftedSectionsComponent 𝒮 (shiftedGrading 𝒨 q) n ≃+
      shiftedSectionsComponent 𝒮 𝒨 (n + q) :=
  associatedSectionsCongrEquiv 𝒮 (shiftedGrading_shiftedGrading 𝒨 q n)

/-- The shift identification does not move the section: at every point of `Proj 𝒮` the value is
unchanged. -/
public theorem coe_shiftedSectionsShiftEquiv (q n : ℤ)
    (s : shiftedSectionsComponent 𝒮 (shiftedGrading 𝒨 q) n)
    (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) :
    ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 (n + q)) ⊤).toFun
        (shiftedSectionsShiftEquiv 𝒮 𝒨 q n s)).1 x =
      ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading (shiftedGrading 𝒨 q) n) ⊤).toFun
        s).1 x :=
  coe_associatedSectionsCongrEquiv 𝒮 (shiftedGrading_shiftedGrading 𝒨 q n) s x

/-! ### Transporting a shifted global section along an equality of degrees -/

/-- **Transporting a shifted global section along an equality of degrees**, as an isomorphism of
additive groups `H⁰(X, M(a)~) ≃+ H⁰(X, M(b)~)` for `a = b`. -/
public def shiftedSectionsCastEquiv {a b : ℤ} (h : a = b) :
    shiftedSectionsComponent 𝒮 𝒨 a ≃+ shiftedSectionsComponent 𝒮 𝒨 b where
  toFun := cast (congrArg (shiftedSectionsComponent 𝒮 𝒨) h)
  invFun := cast (congrArg (shiftedSectionsComponent 𝒮 𝒨) h.symm)
  left_inv _ := by subst h; rfl
  right_inv _ := by subst h; rfl
  map_add' _ _ := by subst h; rfl

omit [DirectSum.Decomposition 𝒨] in
/-- A transport of degrees does not move the section. -/
public theorem coe_shiftedSectionsCastEquiv {a b : ℤ} (h : a = b)
    (s : shiftedSectionsComponent 𝒮 𝒨 a) (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) :
    ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 b) ⊤).toFun
        (shiftedSectionsCastEquiv 𝒮 𝒨 h s)).1 x =
      ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 a) ⊤).toFun s).1 x := by
  subst h
  rfl

omit [DirectSum.Decomposition 𝒨] in
/-- **The homogeneous scalar action of Equation 01MR commutes with a transport of degrees.** -/
public theorem homogeneousScalarGlobalSections_cast (i : ℕ) {a b : ℤ} (h : a = b) (c : 𝒮 i)
    (s : shiftedSectionsComponent 𝒮 𝒨 a) :
    homogeneousScalarGlobalSections 𝒮 𝒨 i b c
        (cast (congrArg (shiftedSectionsComponent 𝒮 𝒨) h) s) =
      cast (congrArg (fun n : ℤ => shiftedSectionsComponent 𝒮 𝒨 ((i : ℤ) + n)) h)
        (homogeneousScalarGlobalSections 𝒮 𝒨 i a c s) := by
  subst h
  rfl

omit [DirectSum.Decomposition 𝒨] in
/-- **The shift identification commutes with a transport of degrees.** -/
public theorem shiftedSectionsShiftEquiv_cast (q : ℤ) {a b : ℤ} (h : a = b)
    (s : shiftedSectionsComponent 𝒮 (shiftedGrading 𝒨 q) a) :
    shiftedSectionsShiftEquiv 𝒮 𝒨 q b
        (cast (congrArg (shiftedSectionsComponent 𝒮 (shiftedGrading 𝒨 q)) h) s) =
      cast (congrArg (fun n : ℤ => shiftedSectionsComponent 𝒮 𝒨 (n + q)) h)
        (shiftedSectionsShiftEquiv 𝒮 𝒨 q a s) := by
  subst h
  rfl

/-- **The degreewise comparison `N_n → N'_n` of part (3) commutes with a transport of
degrees.** -/
public theorem twistedToShiftedComponent_cast {a b : ℤ} (h : a = b)
    (s : twistedSectionsComponent 𝒮 (associatedModuleSheaf 𝒮 𝒨) a) :
    twistedToShiftedComponent 𝒮 𝒨 b
        (cast (congrArg (twistedSectionsComponent 𝒮 (associatedModuleSheaf 𝒮 𝒨)) h) s) =
      cast (congrArg (shiftedSectionsComponent 𝒮 𝒨) h)
        (twistedToShiftedComponent 𝒮 𝒨 a s) := by
  subst h
  rfl

/-! ### The shift identification is semilinear -/

/-- **The shift identification carries the homogeneous scalar action of Equation 01MR to
itself.** This is the one piece of the Veronese reduction of part (1) that the library did not
already contain: the source's `M(dn + q)~ = M(q)~(dn)` is used as an identification of *graded*
modules, and that is what this says.

Both sides are read in the module fibres. They have to be: the two gradings of `M(q)(i + n)` and
of `M((i + n) + q)` are equal only propositionally, so no identity of the operators themselves is
available, while a section of either associated sheaf is a dependent function into the ambient
module fibres, which do not mention the grading at all. There the transport does nothing
(`coe_shiftedSectionsShiftEquiv`) and both actions are multiplication by the scalar
(`Stacks.AlgebraicGeometry.ProjShiftedSections.homogeneousScalarGlobalSections_apply`). -/
public theorem shiftedSectionsShiftEquiv_homogeneousScalarGlobalSections (q : ℤ) (i : ℕ) (n : ℤ)
    (c : 𝒮 i) (s : shiftedSectionsComponent 𝒮 (shiftedGrading 𝒨 q) n) :
    shiftedSectionsShiftEquiv 𝒮 𝒨 q ((i : ℤ) + n)
        (homogeneousScalarGlobalSections 𝒮 (shiftedGrading 𝒨 q) i n c s) =
      cast (congrArg (shiftedSectionsComponent 𝒮 𝒨) (shiftScalarDegree i n q))
        (homogeneousScalarGlobalSections 𝒮 𝒨 i (n + q) c
          (shiftedSectionsShiftEquiv 𝒮 𝒨 q n s)) := by
  refine (associatedModuleSheafSectionsEquiv 𝒮
    (shiftedGrading 𝒨 (((i : ℤ) + n) + q)) ⊤).injective ?_
  refine Subtype.ext (funext fun x => ?_)
  have hL := coe_shiftedSectionsShiftEquiv 𝒮 𝒨 q ((i : ℤ) + n)
    (homogeneousScalarGlobalSections 𝒮 (shiftedGrading 𝒨 q) i n c s) x
  have hL2 := homogeneousScalarGlobalSections_apply 𝒮 (shiftedGrading 𝒨 q) i n c s x
  have hR := coe_shiftedSectionsCastEquiv 𝒮 𝒨 (shiftScalarDegree i n q)
    (homogeneousScalarGlobalSections 𝒮 𝒨 i (n + q) c (shiftedSectionsShiftEquiv 𝒮 𝒨 q n s)) x
  have hR2 := homogeneousScalarGlobalSections_apply 𝒮 𝒨 i (n + q) c
    (shiftedSectionsShiftEquiv 𝒮 𝒨 q n s) x
  have hR3 := coe_shiftedSectionsShiftEquiv 𝒮 𝒨 q n s x
  exact (hL.trans hL2).trans
    (hR.trans (hR2.trans (congrArg (fun z => (c : S) • z) hR3))).symm

/-! ### One residue class of the shifted global sections -/

section ShiftedResidueComparison

variable (d : ℕ) (hdpos : 0 < d)
  (G' : letI := veroneseGradingGradedRing 𝒮 d hdpos
    SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology
          (ProjectiveSpectrum.top (veroneseGrading 𝒮 d)))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf (veroneseGrading 𝒮 d))))
  (q : ℕ)
  (φ : letI := veroneseGradingGradedRing 𝒮 d hdpos
    pullbackProjModule 𝒮 (veroneseGrading 𝒮 d) (veroneseProjIso 𝒮 d hdpos).hom G' ≅
      associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 (q : ℤ)))

/-- **The comparison of one residue class on the shifted side**:
`Γ(X', ℱ'(m)) → H⁰(X, M(md + q)~)`, for an identification `φ : i^*ℱ' ≅ M(q)~`.

It is `Stacks.AlgebraicGeometry.ProjCoherentII.veroneseSectionsComparison` at `𝒢 = M(q)~`,
followed by the degreewise comparison of part (3) of the tag at the degree `dm` — bijective
there, by part (6), because `d ∣ dm` — followed by the shift identification
`H⁰(X, M(q)(dm)~) = H⁰(X, M(dm + q)~)` and the transport of the degree `dm + q` to `md + q`. -/
public def shiftedResidueComparison (m : ℤ) :
    letI := veroneseGradingGradedRing 𝒮 d hdpos
    twistedSectionsComponent (veroneseGrading 𝒮 d) G' m →+
      shiftedSectionsComponent 𝒮 𝒨 (m * (d : ℤ) + (q : ℤ)) :=
  letI := veroneseGradingGradedRing 𝒮 d hdpos
  (shiftedSectionsCastEquiv 𝒮 𝒨 (iterateResidueDegree d q m)).toAddMonoidHom.comp
    ((shiftedSectionsShiftEquiv 𝒮 𝒨 (q : ℤ) ((d : ℤ) * m)).toAddMonoidHom.comp
      ((twistedToShiftedComponent 𝒮 (shiftedGrading 𝒨 (q : ℤ)) ((d : ℤ) * m)).comp
        (veroneseSectionsComparison 𝒮 d hdpos G'
          (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 (q : ℤ))) φ m).toAddMonoidHom))

/-- **The residue comparison is surjective.** Three of its four factors are isomorphisms, and the
degreewise comparison of part (3) is bijective at the degree `dm` by part (6) of the tag, the
hypothesis `hdegopen` being the one property of `d` that part (6) uses. -/
public theorem surjective_shiftedResidueComparison
    (hdegopen : AlgebraicGeometry.Proj.degreeOpen 𝒮 d = ⊤) (m : ℤ) :
    letI := veroneseGradingGradedRing 𝒮 d hdpos
    Function.Surjective (shiftedResidueComparison 𝒮 𝒨 d hdpos G' q φ m) :=
  let := veroneseGradingGradedRing 𝒮 d hdpos
  (shiftedSectionsCastEquiv 𝒮 𝒨 (iterateResidueDegree d q m)).surjective.comp
    ((shiftedSectionsShiftEquiv 𝒮 𝒨 (q : ℤ) ((d : ℤ) * m)).surjective.comp
      ((bijective_twistedToShiftedComponent_shiftedGrading 𝒮 𝒨 hdegopen (q : ℤ)
          (⟨m, rfl⟩ : (d : ℤ) ∣ (d : ℤ) * m)).2.comp
        (veroneseSectionsComparison 𝒮 d hdpos G'
          (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 (q : ℤ))) φ m).surjective))

/-- **The residue comparison is semilinear over the inclusion of the Veronese subring.** This is
exactly the hypothesis `hθ` of
`Stacks.AlgebraicGeometry.ProjTwistedSections.exists_finite_span_residue`: the degrees are
identified by `Stacks.AlgebraicGeometry.ProjTwistedSections.residueScalarDegree`. -/
public theorem shiftedResidueComparison_homogeneousScalarGlobalSections (e : ℕ) (m : ℤ)
    (a : veroneseSubring 𝒮 d) (ha : (a : S) ∈ 𝒮 (e * d))
    (y : letI := veroneseGradingGradedRing 𝒮 d hdpos
      twistedSectionsComponent (veroneseGrading 𝒮 d) G' m) :
    letI := veroneseGradingGradedRing 𝒮 d hdpos
    shiftedResidueComparison 𝒮 𝒨 d hdpos G' q φ ((e : ℤ) + m)
        (homogeneousScalarTwistedSections (veroneseGrading 𝒮 d) G' e m ⟨a, ha⟩ y) =
      cast (congrArg (shiftedSectionsComponent 𝒮 𝒨) (residueScalarDegree e m d q))
        (homogeneousScalarGlobalSections 𝒮 𝒨 (e * d) (m * (d : ℤ) + (q : ℤ)) ⟨(a : S), ha⟩
          (shiftedResidueComparison 𝒮 𝒨 d hdpos G' q φ m y)) := by
  let := veroneseGradingGradedRing 𝒮 d hdpos
  have hdef : ∀ (n : ℤ) (z : twistedSectionsComponent (veroneseGrading 𝒮 d) G' n),
      shiftedResidueComparison 𝒮 𝒨 d hdpos G' q φ n z =
        cast (congrArg (shiftedSectionsComponent 𝒮 𝒨) (iterateResidueDegree d q n))
          (shiftedSectionsShiftEquiv 𝒮 𝒨 (q : ℤ) ((d : ℤ) * n)
            (twistedToShiftedComponent 𝒮 (shiftedGrading 𝒨 (q : ℤ)) ((d : ℤ) * n)
              (veroneseSectionsComparison 𝒮 d hdpos G'
                (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 (q : ℤ))) φ n z))) :=
    fun _ _ => rfl
  rw [hdef, hdef,
    veroneseSectionsComparison_homogeneousScalarTwistedSections 𝒮 d hdpos G'
      (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 (q : ℤ))) φ e m a ha y,
    twistedToShiftedComponent_cast 𝒮 (shiftedGrading 𝒨 (q : ℤ))
      (twistIterateScalarDegree d e m),
    twistedToShiftedComponent_homogeneousScalar 𝒮 (shiftedGrading 𝒨 (q : ℤ)) (e * d)
      ((d : ℤ) * m) ⟨(a : S), ha⟩,
    shiftedSectionsShiftEquiv_cast 𝒮 𝒨 (q : ℤ) (twistIterateScalarDegree d e m),
    shiftedSectionsShiftEquiv_homogeneousScalarGlobalSections 𝒮 𝒨 (q : ℤ) (e * d)
      ((d : ℤ) * m) ⟨(a : S), ha⟩,
    homogeneousScalarGlobalSections_cast 𝒮 𝒨 (e * d) (iterateResidueDegree d q m),
    cast_cast, cast_cast, cast_cast]

end ShiftedResidueComparison

/-! ### The two theorems -/

/-- **Part (2) of [Stacks, Tag 0B5R].** For `S` a Noetherian graded ring, `M` a finite graded
`S`-module, `X = Proj 𝒮` and `k ∈ ℤ`, the graded `S`-module

`N = ⨁_{n ≥ k} H⁰(X, M̃(n))`

is a finite `S`-module. `M̃` is coherent, because `M` is a finite module over a Noetherian ring,
and the assertion for an arbitrary coherent sheaf is
`Stacks.AlgebraicGeometry.ProjCoherentII.moduleFinite_truncation_of_isCoherent`. -/
public theorem moduleFinite_twistedTruncation [IsNoetherianRing S] [Module.Finite S M]
    (k : ℤ) :
    letI := (twistedGlobalSectionsModule 𝒮 (associatedModuleSheaf 𝒮 𝒨)).moduleInst
    Module.Finite S ((twistedGlobalSectionsModule 𝒮
      (associatedModuleSheaf 𝒮 𝒨)).truncation 𝒮 (associatedModuleSheaf 𝒮 𝒨) k) :=
  moduleFinite_truncation_of_isCoherent 𝒮 (associatedModuleSheaf 𝒮 𝒨)
    (isCoherent_associatedModuleSheaf 𝒮 𝒨) k

/-- **Part (1) of [Stacks, Tag 0B5R].** For `S` a Noetherian graded ring, `M` a finite graded
`S`-module, `X = Proj 𝒮` and `k ∈ ℤ`, the graded `S`-module

`N' = ⨁_{n ≥ k} H⁰(X, M(n)~)`

is a finite `S`-module.

No generation hypothesis on `S` is assumed. The proof is the source's Veronese reduction: a
degree `d` is chosen by
`Stacks.AlgebraicGeometry.ProjCoherentII.exists_reductionDegree`, the degrees are split into the
`d` residue classes `n = md + q`, each class is compared by
`Stacks.AlgebraicGeometry.ProjCoherentII.shiftedResidueComparison` with the twisted global
sections of the coherent sheaf `i_*(M(q)~)` on `X' = Proj S⁽ᵈ⁾` where [Stacks, Tag 0AG6] (4)
applies, and the `d` resulting finite families are assembled over `S` by
`Stacks.AlgebraicGeometry.ProjTwistedSections.moduleFinite_gradedActionTruncation_of_residues`. -/
@[sga "2 XII 5.3" "clause (a), special case"]
public theorem moduleFinite_shiftedTruncation [IsNoetherianRing S] [Module.Finite S M]
    (k : ℤ) :
    letI := (globalSectionsModuleMap 𝒮 𝒨).moduleInst
    Module.Finite S ((globalSectionsModuleMap 𝒮 𝒨).truncation 𝒮 𝒨 k) := by
  classical
  let := (globalSectionsModuleMap 𝒮 𝒨).moduleInst
  obtain ⟨r, f, deg, d, hdeg, hfdeg, hgen, hdpos, -, hVgen, hdegopen, -⟩ :=
    exists_reductionDegree 𝒮
  let : GradedRing (veroneseGrading 𝒮 d) := veroneseGradingGradedRing 𝒮 d hdpos
  have : IsNoetherianRing (𝒮 0) := isNoetherianRing_gradeZero 𝒮
  have : IsNoetherianRing ((veroneseGrading 𝒮 d) 0) :=
    isNoetherianRing_veroneseGrading_zero 𝒮 d
  obtain ⟨n₀, y₀, hy₀, hy₀gen⟩ :=
    exists_finite_degreeOne_generators_veroneseSubring 𝒮 d f deg hdeg hfdeg hgen hVgen
  obtain ⟨n₁, y₁, hy₁, hy₁gen⟩ :=
    Stacks.ProjCoherentDegreeOne.exists_two_le_generators (veroneseGrading 𝒮 d) y₀ hy₀ hy₀gen
  refine moduleFinite_gradedActionTruncation_of_residues 𝒮
    (homogeneousScalarGlobalSections 𝒮 𝒨)
    ((globalSectionsModuleMap 𝒮 𝒨).smul_of 𝒮 𝒨) hdpos k fun q _ => ?_
  -- the coherent sheaf upstairs, for the residue class of `q`
  have hGqcoh : _root_.SheafOfModules.IsCoherent
      (veronesePushforward 𝒮 d hdpos
        (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 (q : ℤ)))) :=
    isCoherent_veronesePushforward 𝒮 d hdpos
      (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 (q : ℤ)))
      (isCoherent_associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 (q : ℤ)))
  let := (twistedGlobalSectionsModule (veroneseGrading 𝒮 d)
    (veronesePushforward 𝒮 d hdpos
      (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 (q : ℤ))))).moduleInst
  refine exists_finite_span_residue 𝒮 (homogeneousScalarGlobalSections 𝒮 𝒨)
    ((globalSectionsModuleMap 𝒮 𝒨).smul_of 𝒮 𝒨) d
    (homogeneousScalarTwistedSections (veroneseGrading 𝒮 d)
      (veronesePushforward 𝒮 d hdpos
        (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 (q : ℤ)))))
    (twistedGlobalSectionsModule (veroneseGrading 𝒮 d)
      (veronesePushforward 𝒮 d hdpos
        (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 (q : ℤ))))).smul_homogeneous q
    (fun m => shiftedResidueComparison 𝒮 𝒨 d hdpos
      (veronesePushforward 𝒮 d hdpos
        (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 (q : ℤ)))) q
      (veronesePushforwardPullbackIso 𝒮 d hdpos
        (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 (q : ℤ)))) m)
    (fun e m b y => shiftedResidueComparison_homogeneousScalarGlobalSections 𝒮 𝒨 d hdpos
      (veronesePushforward 𝒮 d hdpos
        (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 (q : ℤ)))) q
      (veronesePushforwardPullbackIso 𝒮 d hdpos
        (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 (q : ℤ))))
      e m (b : veroneseSubring 𝒮 d) b.2 y)
    hdpos k ((k - (q : ℤ) - 1) / (d : ℤ) + 1) (fun m => residueBoundIff hdpos k q m)
    (fun m => surjective_shiftedResidueComparison 𝒮 𝒨 d hdpos
      (veronesePushforward 𝒮 d hdpos
        (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 (q : ℤ)))) q
      (veronesePushforwardPullbackIso 𝒮 d hdpos
        (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 (q : ℤ)))) hdegopen m) ?_
  exact Stacks.ProjCoherentDegreeOne.moduleFinite_truncation (veroneseGrading 𝒮 d)
    (veronesePushforward 𝒮 d hdpos
      (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 (q : ℤ)))) y₁ hy₁ hy₁gen hGqcoh
    (twistedGlobalSectionsModule (veroneseGrading 𝒮 d)
      (veronesePushforward 𝒮 d hdpos
        (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 (q : ℤ)))))
    ((k - (q : ℤ) - 1) / (d : ℤ) + 1)

end Stacks.AlgebraicGeometry.ProjCoherentII

end
