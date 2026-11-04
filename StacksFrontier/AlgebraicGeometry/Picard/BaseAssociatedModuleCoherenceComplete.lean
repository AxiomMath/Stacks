module

public import StacksFrontier.AlgebraicGeometry.Picard.BaseAssociatedModuleCoherenceAssociator
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseAssociatedModuleTensor

/-!
# The associativity coherence of the tensor comparison of the associated-module functor

`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'` is Stacks 03EL at the morphism of
ringed sites `((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)`, packaged as the object-level tensor comparison
`Stacks.SheafOfModules.Picard.TensorIso` of the associated-module functor `𝓕 ↦ 𝓕^a` of Stacks
03DU (4).  `Stacks.SheafOfModules.TensorPowerTransport.powerTransportIso_tensor` asks for four
coherences of that comparison; naturality is
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'_natural` and the symmetry coherence
is `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'_braiding`.  This file discharges
the **associativity** one.

## Main results

* `Stacks.SheafOfModules.Invertible.tensorProductAssociator_naturality`: **the associativity
  constraint of Tag 01CA is natural in its three arguments**, at the bifunctor spelling of the
  tensor product and over a presheaf of commutative rings together with a sheaf condition.  It is
  the companion of
  `Stacks.SheafOfModules.Invertible.tensorProductBraiding_naturality_bifunctorMap`.
* `AlgebraicGeometry.BigFppfOver.baseTensorComparison_associator`: the associativity coherence of
  Stacks 03EL at that morphism, read at the structure sheaf of the ringed site.
* `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'_associator`: **the object-level
  tensor comparison of `𝓕 ↦ 𝓕^a` is compatible with the associativity constraint of Tag 01CA**,
  at every one of the five topologies and with no hypothesis on `S`.

## Implementation notes

**Where the spellings cross, and why one `exact` will not do it.**  The coherence of Stacks 03EL
is proved over a ringed topos, where the sheaf condition of the structure sheaf is the term
`Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf` produces; the coherences of
Tag 01CA are consumed at a ringed *site*, where it is the second component of
`Stacks.SheafOfModules.Tensor.ringSheaf` of the site's own structure sheaf.  The two are
definitionally equal, and so are the three pairs
`AlgebraicGeometry.BigFppfOver.basePullbackModules` against
`Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules`,
`AlgebraicGeometry.BigFppfOver.baseTensorComparison` against
`Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison`, and
`AlgebraicGeometry.BigFppfOver.baseRingedSite` against its `toRingedTopos`.  A single `exact`
across the whole square has to discover all of them at once and exhausts the recursion limit.

Each of the six factors of the square crosses on its own by `rfl`, so the crossing is paid
factor by factor: six `rfl`s between the two spellings of one morphism, and then one `rw`, after
which the goal is the generalized coherence on the nose.  No limit is raised.
`Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison_associator` takes the two
sheaf conditions as explicit arguments for the same reason.

**Why the sheaf condition is a hypothesis and not a term.**  At the ringed site the sheaf
condition arrives as the projection
`(Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2`, and the associativity
square mentions it six times — once in each factor.  Written out in each place, the crossings
and the instantiation of the generalized coherence do not fit one heartbeat budget between them.
So both results are proved first with that sheaf condition as a *hypothesis*
(`AlgebraicGeometry.BigFppfOver.associatorOfSheafCondition` and
`AlgebraicGeometry.BigFppfOver.associatorIsoOfSheafCondition`), where every factor mentions the
one variable and the instantiation of
`Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison_associator` is syntactic
(`AlgebraicGeometry.BigFppfOver.crossedAssociator`); the two public statements are those at the
projection, each a single application.  Splitting the work over four declarations instead of one
is what keeps every step inside the default limit.

**Why the transport is fed constants.**  The categories
`Stacks.SheafOfModules.TransportCoherence.transported_associator'` is read in are fixed by
`AlgebraicGeometry.BigFppfOver.pullbackModulesIsoBaseAssociatedModule`, the modules over
`Stacks.SheafOfModules.Tensor.ringSheaf` of the two ringed topoi.  Passed a lambda written at the
sheaf-of-rings spelling of the tensor product, the kernel infers its type against those and the
inference alone exhausts the budget (about 14 s); the same operation as a constant with a
declared type is compared at once.  So every datum — the two tensor products, the action on
morphisms `AlgebraicGeometry.BigFppfOver.tensorMap`, the comparison, the functors and the
isomorphism between them — is a constant, the four hypotheses are stated in exactly those
constants, and the transport's instantiation is syntactic.  Its conclusion is matched against
`Stacks.SheafOfModules.TensorPowerTransport.TensorIsoAssociator` factor by factor.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf)
open Stacks.SheafOfModules.Invertible (tensorProductAssociator tensorProductBifunctor)
open Stacks.SheafOfModules.RingedToposPullback (pullbackTensorComparison)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe w v u

/-! ### Naturality of the associativity constraint of Tag 01CA -/

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The associativity constraint of Tag 01CA is natural in its three arguments**, at the
spelling in which the tensor product of two morphisms is the action of
`Stacks.SheafOfModules.Invertible.tensorProductBifunctor`.

This is `CategoryTheory.MonoidalCategory.associator_naturality` for
`Stacks.SheafOfModules.sheafTensorMonoidal`, whose associator is the fixed constraint of Tag 01CA
and whose tensor product of morphisms is the action of the bifunctor, both by `rfl`.  That
structure is switched on by `letI` and never as an instance: left in scope it wins instance
search over the localized structure of `Stacks.SheafOfModules.monoidalCategory`, and the lemmas
stated with the notation then mean something else.

It is the companion of
`Stacks.SheafOfModules.Invertible.tensorProductBraiding_naturality_bifunctorMap`, and it is stated
over a presheaf of commutative rings together with a sheaf condition rather than over a sheaf of
commutative rings on a site: at that index it applies to a ringed site's own structure sheaf and
sheaf condition without any crossing, which is what the transport of the coherence needs. -/
theorem tensorProductAssociator_naturality
    {A A' Bb Bb' D D' : SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
    (u : A ⟶ A') (v : Bb ⟶ Bb') (t : D ⟶ D') :
    (tensorProductBifunctor O hO).map
          (X := ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} ⟨O,
            Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj A).obj Bb),
            D)) (Y := ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} ⟨O,
            Presheaf.isSheaf_of_isSheaf_comp _ O
            (forget₂ CommRingCat RingCat) hO⟩).obj A').obj Bb'), D'))
          ((tensorProductBifunctor O hO).map (X := (A, Bb)) (Y := (A', Bb')) (u, v), t) ≫
        (tensorProductAssociator O hO A' Bb' D').hom =
      (tensorProductAssociator O hO A Bb D).hom ≫
        (tensorProductBifunctor O hO).map
          (X := (A, (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} ⟨O,
            Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj Bb).obj D)))
            (Y := (A', (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} ⟨O,
            Presheaf.isSheaf_of_isSheaf_comp _ O
            (forget₂ CommRingCat RingCat) hO⟩).obj Bb').obj D')))
          (u, (tensorProductBifunctor O hO).map (X := (Bb, D)) (Y := (Bb', D')) (v, t)) := by
  let := Stacks.SheafOfModules.sheafTensorMonoidal O hO
  exact MonoidalCategory.associator_naturality u v t

end Stacks.SheafOfModules.Invertible

/-! ### The associativity coherence at the base spelling -/

namespace AlgebraicGeometry.BigFppfOver

open AlgebraicGeometry.SmallEtale (zariskiStructureIsSheaf)

/-! The canonical tensor product of Tag 01CA is indexed by
`Stacks.SheafOfModules.Tensor.ringSheaf` while the constraints of Tag 01CA are indexed by
`Stacks.SheafOfModules.TensorSheafification.structureSheaf`; the two sheaves of rings are the
same, by proof irrelevance in the sheaf condition, but only at *default* transparency, so each
crossing below is a `whnf` of both.  Making the two reducible lets the crossings be made at
implicit transparency instead; `Stacks.SheafOfModules.TensorSheafification.structureSheaf`
carries the same attribute where it is defined. -/
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Each factor of the associativity square crosses between the ringed-site and the ringed-topos
spelling by `rfl`; crossing all six at once does not finish inside the recursion limit, so the
six are crossed separately. -/
private theorem c1 (τ : SiteKind) (M N P : S.Modules) :
    (basePullbackModules B S hS τ).map (tensorProductAssociator S.presheaf (zariskiStructureIsSheaf
      S) M N P).hom =
      (basePullbackModules B S hS τ).map (tensorProductAssociator
        S.zariskiRingedSite.toRingedTopos.O.obj (zariskiStructureIsSheaf S) M N P).hom := rfl

private theorem c2 (τ : SiteKind) (M N P : S.Modules) :
    baseTensorComparison B S hS τ M ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨S.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
      (zariskiStructureIsSheaf S)⟩).obj N).obj P)) =
      pullbackTensorComparison (baseRingedToposModulesHom B S hS τ) M
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨S.zariskiRingedSite.toRingedTopos.O.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ S.zariskiRingedSite.toRingedTopos.O.obj
        (forget₂ CommRingCat RingCat) (zariskiStructureIsSheaf S)⟩).obj N).obj P)) := rfl

private theorem c3 (τ : SiteKind)
    (hO : Presheaf.IsSheaf (baseRingedSite B S hS τ).J
      (structureRingPresheaf (baseRingedSite B S hS τ).O.obj))
    (M N P : S.Modules) :
    (tensorProductBifunctor (baseRingedSite B S hS τ).O.obj hO).map
      (X := ((basePullbackModules B S hS τ).obj M, (basePullbackModules B S hS τ).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨S.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
        (zariskiStructureIsSheaf S)⟩).obj N).obj P))))
      (Y := ((basePullbackModules B S hS τ).obj M,
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(baseRingedSite B S hS τ).O.obj, Presheaf.isSheaf_of_isSheaf_comp _
        (baseRingedSite B S hS τ).O.obj (forget₂ CommRingCat RingCat) hO⟩).obj
        ((basePullbackModules B S hS τ).obj N)).obj ((basePullbackModules B S hS τ).obj P))))
      (𝟙 ((basePullbackModules B S hS τ).obj M), baseTensorComparison B S hS τ N P) =
      (tensorProductBifunctor (baseRingedSite B S hS τ).toRingedTopos.O.obj hO).map
      (X := ((basePullbackModules B S hS τ).obj M, (basePullbackModules B S hS τ).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨S.zariskiRingedSite.toRingedTopos.O.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ S.zariskiRingedSite.toRingedTopos.O.obj
        (forget₂ CommRingCat RingCat) (zariskiStructureIsSheaf S)⟩).obj N).obj P))))
      (Y := ((basePullbackModules B S hS τ).obj M,
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(baseRingedSite B S hS τ).toRingedTopos.O.obj, Presheaf.isSheaf_of_isSheaf_comp _
        (baseRingedSite B S hS τ).toRingedTopos.O.obj (forget₂ CommRingCat RingCat) hO⟩).obj
        ((basePullbackModules B S hS τ).obj N)).obj ((basePullbackModules B S hS τ).obj P))))
      (𝟙 ((basePullbackModules B S hS τ).obj M), pullbackTensorComparison
        (baseRingedToposModulesHom B S hS τ) N P) := rfl

private theorem d1 (τ : SiteKind) (M N P : S.Modules) :
    baseTensorComparison B S hS τ ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨S.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
      (zariskiStructureIsSheaf S)⟩).obj M).obj N)) P =
      pullbackTensorComparison (baseRingedToposModulesHom B S hS τ)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨S.zariskiRingedSite.toRingedTopos.O.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ S.zariskiRingedSite.toRingedTopos.O.obj
        (forget₂ CommRingCat RingCat) (zariskiStructureIsSheaf S)⟩).obj M).obj N)) P := rfl

private theorem d2 (τ : SiteKind)
    (hO : Presheaf.IsSheaf (baseRingedSite B S hS τ).J
      (structureRingPresheaf (baseRingedSite B S hS τ).O.obj))
    (M N P : S.Modules) :
    (tensorProductBifunctor (baseRingedSite B S hS τ).O.obj hO).map
      (X := ((basePullbackModules B S hS τ).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨S.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
        (zariskiStructureIsSheaf S)⟩).obj M).obj N)), (basePullbackModules B S hS τ).obj P))
      (Y := ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(baseRingedSite B S hS τ).O.obj, Presheaf.isSheaf_of_isSheaf_comp _
        (baseRingedSite B S hS τ).O.obj (forget₂ CommRingCat RingCat) hO⟩).obj
        ((basePullbackModules B S hS τ).obj M)).obj ((basePullbackModules B S hS τ).obj N)),
        (basePullbackModules B S hS τ).obj P))
      (baseTensorComparison B S hS τ M N, 𝟙 ((basePullbackModules B S hS τ).obj P)) =
      (tensorProductBifunctor (baseRingedSite B S hS τ).toRingedTopos.O.obj hO).map
      (X := ((basePullbackModules B S hS τ).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨S.zariskiRingedSite.toRingedTopos.O.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ S.zariskiRingedSite.toRingedTopos.O.obj
        (forget₂ CommRingCat RingCat) (zariskiStructureIsSheaf S)⟩).obj M).obj N)),
        (basePullbackModules B S hS τ).obj P))
      (Y := ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(baseRingedSite B S hS τ).toRingedTopos.O.obj, Presheaf.isSheaf_of_isSheaf_comp _
        (baseRingedSite B S hS τ).toRingedTopos.O.obj (forget₂ CommRingCat RingCat) hO⟩).obj
        ((basePullbackModules B S hS τ).obj M)).obj ((basePullbackModules B S hS τ).obj N)),
        (basePullbackModules B S hS τ).obj P))
      (pullbackTensorComparison (baseRingedToposModulesHom B S hS τ) M N, 𝟙
        ((basePullbackModules B S hS τ).obj P)) := rfl

private theorem d3 (τ : SiteKind)
    (hO : Presheaf.IsSheaf (baseRingedSite B S hS τ).J
      (structureRingPresheaf (baseRingedSite B S hS τ).O.obj))
    (M N P : S.Modules) :
    (tensorProductAssociator (baseRingedSite B S hS τ).O.obj hO
      ((basePullbackModules B S hS τ).obj M) ((basePullbackModules B S hS τ).obj
        N) ((basePullbackModules B S hS τ).obj P)).hom =
      (tensorProductAssociator (baseRingedSite B S hS τ).toRingedTopos.O.obj hO
        ((basePullbackModules B S hS τ).obj M) ((basePullbackModules B S hS
          τ).obj N) ((basePullbackModules B S hS τ).obj P)).hom := rfl

/-- The associativity coherence of Stacks 03EL at the morphism, in the ringed-topos spelling
that `Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison_associator` states it
in and with the sheaf condition of the structure sheaf carried as a hypothesis.  Keeping it a
hypothesis is what makes the instantiation syntactic: every factor of the square mentions the
one variable `hO` instead of a copy of the term that
`Stacks.SheafOfModules.Tensor.ringSheaf` of the site's structure sheaf projects out of. -/
private theorem crossedAssociator (τ : SiteKind)
    (hO : Presheaf.IsSheaf (baseRingedSite B S hS τ).J
      (structureRingPresheaf (baseRingedSite B S hS τ).O.obj))
    (M N P : S.Modules) :
    (basePullbackModules B S hS τ).map (tensorProductAssociator
        S.zariskiRingedSite.toRingedTopos.O.obj (zariskiStructureIsSheaf S) M N P).hom ≫
      pullbackTensorComparison (baseRingedToposModulesHom B S hS τ) M
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨S.zariskiRingedSite.toRingedTopos.O.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ S.zariskiRingedSite.toRingedTopos.O.obj
        (forget₂ CommRingCat RingCat) (zariskiStructureIsSheaf S)⟩).obj N).obj P)) ≫
      (tensorProductBifunctor (baseRingedSite B S hS τ).toRingedTopos.O.obj hO).map
      (X := ((basePullbackModules B S hS τ).obj M, (basePullbackModules B S hS τ).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨S.zariskiRingedSite.toRingedTopos.O.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ S.zariskiRingedSite.toRingedTopos.O.obj
        (forget₂ CommRingCat RingCat) (zariskiStructureIsSheaf S)⟩).obj N).obj P))))
      (Y := ((basePullbackModules B S hS τ).obj M,
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(baseRingedSite B S hS τ).toRingedTopos.O.obj, Presheaf.isSheaf_of_isSheaf_comp _
        (baseRingedSite B S hS τ).toRingedTopos.O.obj (forget₂ CommRingCat RingCat) hO⟩).obj
        ((basePullbackModules B S hS τ).obj N)).obj ((basePullbackModules B S hS τ).obj P))))
      (𝟙 ((basePullbackModules B S hS τ).obj M), pullbackTensorComparison
        (baseRingedToposModulesHom B S hS τ) N P) =
      pullbackTensorComparison (baseRingedToposModulesHom B S hS τ)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨S.zariskiRingedSite.toRingedTopos.O.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ S.zariskiRingedSite.toRingedTopos.O.obj
        (forget₂ CommRingCat RingCat) (zariskiStructureIsSheaf S)⟩).obj M).obj N)) P ≫
      (tensorProductBifunctor (baseRingedSite B S hS τ).toRingedTopos.O.obj hO).map
      (X := ((basePullbackModules B S hS τ).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨S.zariskiRingedSite.toRingedTopos.O.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ S.zariskiRingedSite.toRingedTopos.O.obj
        (forget₂ CommRingCat RingCat) (zariskiStructureIsSheaf S)⟩).obj M).obj N)),
        (basePullbackModules B S hS τ).obj P))
      (Y := ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(baseRingedSite B S hS τ).toRingedTopos.O.obj, Presheaf.isSheaf_of_isSheaf_comp _
        (baseRingedSite B S hS τ).toRingedTopos.O.obj (forget₂ CommRingCat RingCat) hO⟩).obj
        ((basePullbackModules B S hS τ).obj M)).obj ((basePullbackModules B S hS τ).obj N)),
        (basePullbackModules B S hS τ).obj P))
      (pullbackTensorComparison (baseRingedToposModulesHom B S hS τ) M N, 𝟙
        ((basePullbackModules B S hS τ).obj P)) ≫
      (tensorProductAssociator (baseRingedSite B S hS τ).toRingedTopos.O.obj hO
        ((basePullbackModules B S hS τ).obj M) ((basePullbackModules B S hS
          τ).obj N) ((basePullbackModules B S hS τ).obj P)).hom :=
  Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison_associator
    (baseRingedToposModulesHom B S hS τ) hO (zariskiStructureIsSheaf S) M N P

/-- `AlgebraicGeometry.BigFppfOver.baseTensorComparison_associator` with the sheaf condition of
the structure sheaf of the ringed site carried as a hypothesis.  The six crossings are made one
factor at a time, and the crossed square is
`AlgebraicGeometry.BigFppfOver.crossedAssociator`; both for the reason recorded in the
implementation notes at the head of this file. -/
private theorem associatorOfSheafCondition (τ : SiteKind)
    (hO : Presheaf.IsSheaf (baseRingedSite B S hS τ).J
      (structureRingPresheaf (baseRingedSite B S hS τ).O.obj))
    (M N P : S.Modules) :
    (basePullbackModules B S hS τ).map (tensorProductAssociator S.presheaf (zariskiStructureIsSheaf
      S) M N P).hom ≫
        baseTensorComparison B S hS τ M ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨S.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
          (zariskiStructureIsSheaf S)⟩).obj N).obj P)) ≫
        (tensorProductBifunctor (baseRingedSite B S hS τ).O.obj hO).map
        (X := ((basePullbackModules B S hS τ).obj M, (basePullbackModules B S hS τ).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨S.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
          (zariskiStructureIsSheaf S)⟩).obj N).obj P))))
        (Y := ((basePullbackModules B S hS τ).obj M,
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          ⟨(baseRingedSite B S hS τ).O.obj, Presheaf.isSheaf_of_isSheaf_comp _
          (baseRingedSite B S hS τ).O.obj (forget₂ CommRingCat RingCat) hO⟩).obj
          ((basePullbackModules B S hS τ).obj N)).obj ((basePullbackModules B S hS τ).obj P))))
        (𝟙 ((basePullbackModules B S hS τ).obj M), baseTensorComparison B S hS τ N P) =
      baseTensorComparison B S hS τ ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨S.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
        (zariskiStructureIsSheaf S)⟩).obj M).obj N)) P ≫
        (tensorProductBifunctor (baseRingedSite B S hS τ).O.obj hO).map
        (X := ((basePullbackModules B S hS τ).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨S.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
          (zariskiStructureIsSheaf S)⟩).obj M).obj N)), (basePullbackModules B S hS τ).obj P))
        (Y := ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          ⟨(baseRingedSite B S hS τ).O.obj, Presheaf.isSheaf_of_isSheaf_comp _
          (baseRingedSite B S hS τ).O.obj (forget₂ CommRingCat RingCat) hO⟩).obj
          ((basePullbackModules B S hS τ).obj M)).obj ((basePullbackModules B S hS τ).obj N)),
          (basePullbackModules B S hS τ).obj P))
        (baseTensorComparison B S hS τ M N, 𝟙 ((basePullbackModules B S hS τ).obj P)) ≫
        (tensorProductAssociator (baseRingedSite B S hS τ).O.obj hO
          ((basePullbackModules B S hS τ).obj M) ((basePullbackModules B S hS
            τ).obj N) ((basePullbackModules B S hS τ).obj P)).hom := by
  rw [c1 B S hS τ M N P, c2 B S hS τ M N P, c3 B S hS τ hO M N P, d1 B S hS τ M N P,
    d2 B S hS τ hO M N P, d3 B S hS τ hO M N P]
  exact crossedAssociator B S hS τ hO M N P

/-! ### The data of the transport, as constants with declared types

`Stacks.SheafOfModules.TransportCoherence.transported_associator'` is instantiated below with every
operation passed as a constant whose type is declared, never as a lambda.  The categories the
transport is read in are fixed by `pullbackModulesIsoBaseAssociatedModule`, whose source and target
are the modules over `Stacks.SheafOfModules.Tensor.ringSheaf` of the two ringed topoi; a lambda
written at the sheaf-of-rings spelling of the tensor product has its type inferred by the kernel
against those, and that inference alone exhausts the budget, while the same operation as a constant
with a declared type is compared at once.  The hypotheses of the transport are then stated in
exactly these constants, so that the instantiation is syntactic. -/

/-- The tensor product of two modules on the small Zariski site, as a binary operation with a
declared type. -/
private abbrev zariskiTensor (M N : SheafOfModules.{u}
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf
    (zariskiStructureIsSheaf S))) :
    SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf
      (zariskiStructureIsSheaf S)) := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨S.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
      (zariskiStructureIsSheaf S)⟩).obj M).obj N

/-- The tensor product of two modules on the big site, as a binary operation with a declared
type. -/
private abbrev bigTensor (τ : SiteKind)
    (hO : Presheaf.IsSheaf (baseRingedSite B S hS τ).J
      (structureRingPresheaf (baseRingedSite B S hS τ).O.obj))
    (M N : SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (baseRingedSite B S hS τ).O.obj hO)) : SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (baseRingedSite B S hS τ).O.obj hO) :=
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          ⟨(baseRingedSite B S hS τ).O.obj, Presheaf.isSheaf_of_isSheaf_comp _
          (baseRingedSite B S hS τ).O.obj (forget₂ CommRingCat RingCat) hO⟩).obj M).obj N

/-- `AlgebraicGeometry.BigFppfOver.basePullbackModules` with its source and target written at
the indices `Stacks.SheafOfModules.TensorPowerTransport.TensorIsoAssociator` reads them at. -/
private abbrev pullbackAt (τ : SiteKind)
    (hO : Presheaf.IsSheaf (baseRingedSite B S hS τ).J
      (structureRingPresheaf (baseRingedSite B S hS τ).O.obj)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf
      (zariskiStructureIsSheaf S)) ⥤ SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (baseRingedSite B S hS τ).O.obj hO) := basePullbackModules B S hS τ

/-- `AlgebraicGeometry.BigFppfOver.baseAssociatedModule` at the same indices. -/
private abbrev associatedAt (τ : SiteKind)
    (hO : Presheaf.IsSheaf (baseRingedSite B S hS τ).J
      (structureRingPresheaf (baseRingedSite B S hS τ).O.obj)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf
      (zariskiStructureIsSheaf S)) ⥤ SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (baseRingedSite B S hS τ).O.obj hO) := baseAssociatedModule B S hS τ

/-- `AlgebraicGeometry.BigFppfOver.pullbackModulesIsoBaseAssociatedModule` at the same indices. -/
private def pullbackToBaseAt (τ : SiteKind)
    (hO : Presheaf.IsSheaf (baseRingedSite B S hS τ).J
      (structureRingPresheaf (baseRingedSite B S hS τ).O.obj)) :
    pullbackAt B S hS τ hO ≅ associatedAt B S hS τ hO := pullbackModulesIsoBaseAssociatedModule B S
      hS τ

/-- The tensor product of two morphisms of Tag 0GMW, the action of
`Stacks.SheafOfModules.Invertible.tensorProductBifunctor` on the pair, with its four objects
explicit and its source and target written with `AlgebraicGeometry.BigFppfOver.bigTensor`.  The
crossing between `(tensorProductBifunctor O hO).obj (X, Y)` and the `sheafTensor` spelling is
paid here, once, at four free objects. -/
private def tensorMap (τ : SiteKind)
    (hO : Presheaf.IsSheaf (baseRingedSite B S hS τ).J
      (structureRingPresheaf (baseRingedSite B S hS τ).O.obj))
    (X X' Y Y' : SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (baseRingedSite B S hS τ).O.obj hO)) (f : X ⟶ X') (g : Y ⟶ Y') :
    bigTensor B S hS τ hO X Y ⟶ bigTensor B S hS τ hO X' Y' :=
  (tensorProductBifunctor (baseRingedSite B S hS τ).O.obj hO).map (X := (X, Y)) (Y := (X', Y'))
    (f, g)

/-- The tensor comparison of `𝓕 ↦ 𝓕^a` as a family of morphisms with a declared type. -/
private abbrev tensorComparisonMap (τ : SiteKind)
    (hO : Presheaf.IsSheaf (baseRingedSite B S hS τ).J
      (structureRingPresheaf (baseRingedSite B S hS τ).O.obj))
    (M N : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf
      (zariskiStructureIsSheaf S))) :
    (associatedAt B S hS τ hO).obj (zariskiTensor S M N) ⟶ bigTensor B S hS τ hO
      ((associatedAt B S hS τ hO).obj M) ((associatedAt B S hS τ hO).obj N) :=
  (baseAssociatedModuleTensorIso' B S hS τ M N).hom

/-- `AlgebraicGeometry.BigFppfOver.tensorMap` preserves composition: the functoriality of
`Stacks.SheafOfModules.Invertible.tensorProductBifunctor` read on the pair. -/
private theorem tensorMap_comp (τ : SiteKind)
    (hO : Presheaf.IsSheaf (baseRingedSite B S hS τ).J
      (structureRingPresheaf (baseRingedSite B S hS τ).O.obj))
    (X X' X'' Y Y' Y'' : SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (baseRingedSite B S hS τ).O.obj hO))
    (u : X ⟶ X') (u' : X' ⟶ X'') (v : Y ⟶ Y') (v' : Y' ⟶ Y'') :
    tensorMap B S hS τ hO X X' Y Y' u v ≫ tensorMap B S hS τ hO X' X'' Y' Y'' u' v'
      = tensorMap B S hS τ hO X X'' Y Y'' (u ≫ u') (v ≫ v') :=
  ((tensorProductBifunctor (baseRingedSite B S hS τ).O.obj hO).map_comp (X := (X, Y))
    (Y := (X', Y')) (Z := (X'', Y'')) (u, v) (u', v')).symm

/-- The associativity constraint of Tag 01CA is natural for
`AlgebraicGeometry.BigFppfOver.tensorMap`: this is
`Stacks.SheafOfModules.Invertible.tensorProductAssociator_naturality`. -/
private theorem tensorMap_assoc (τ : SiteKind)
    (hO : Presheaf.IsSheaf (baseRingedSite B S hS τ).J
      (structureRingPresheaf (baseRingedSite B S hS τ).O.obj))
    (X X' Y Y' W W' : SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (baseRingedSite B S hS τ).O.obj hO))
    (u : X ⟶ X') (v : Y ⟶ Y') (t : W ⟶ W') :
    tensorMap B S hS τ hO (bigTensor B S hS τ hO X Y) (bigTensor B S hS τ hO X' Y') W W'
      (tensorMap B S hS τ hO X X' Y Y' u v) t ≫
        (tensorProductAssociator (baseRingedSite B S hS τ).O.obj hO X' Y' W').hom =
      (tensorProductAssociator (baseRingedSite B S hS τ).O.obj hO X Y W).hom ≫
        tensorMap B S hS τ hO X X' (bigTensor B S hS τ hO Y W) (bigTensor B S hS τ hO Y' W') u
          (tensorMap B S hS τ hO Y Y' W W' v t) :=
  Stacks.SheafOfModules.Invertible.tensorProductAssociator_naturality
    (baseRingedSite B S hS τ).O.obj hO u v t

/-- `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'_hom'` in the constants of the
transport. -/
private theorem tensorIsoHom (τ : SiteKind)
    (hO : Presheaf.IsSheaf (baseRingedSite B S hS τ).J
      (structureRingPresheaf (baseRingedSite B S hS τ).O.obj))
    (M N : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf
      (zariskiStructureIsSheaf S))) :
    tensorComparisonMap B S hS τ hO M N =
      (pullbackToBaseAt B S hS τ hO).inv.app (zariskiTensor S M N)
        ≫ baseTensorComparison B S hS τ M N ≫
        tensorMap B S hS τ hO ((pullbackAt B S hS τ hO).obj M) ((associatedAt B S hS τ hO).obj M)
          ((pullbackAt B S hS τ hO).obj N) ((associatedAt B S hS τ hO).obj N)
          ((pullbackToBaseAt B S hS τ hO).hom.app M) ((pullbackToBaseAt B S hS τ hO).hom.app N) :=
  baseAssociatedModuleTensorIso'_hom' B S hS τ M N

/-- `AlgebraicGeometry.BigFppfOver.associatorOfSheafCondition` in the constants of the
transport. -/
private theorem associatorOfSheafCondition' (τ : SiteKind)
    (hO : Presheaf.IsSheaf (baseRingedSite B S hS τ).J
      (structureRingPresheaf (baseRingedSite B S hS τ).O.obj))
    (M N P : SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf
      (zariskiStructureIsSheaf S))) :
    (pullbackAt B S hS τ hO).map (tensorProductAssociator S.presheaf
      (zariskiStructureIsSheaf S) M N P).hom ≫
        baseTensorComparison B S hS τ M (zariskiTensor S N P) ≫
        tensorMap B S hS τ hO ((pullbackAt B S hS τ hO).obj M) ((pullbackAt B S hS τ hO).obj M)
          ((pullbackAt B S hS τ hO).obj (zariskiTensor S N P))
          (bigTensor B S hS τ hO ((pullbackAt B S hS τ hO).obj N) ((pullbackAt B S hS τ hO).obj P))
            (𝟙 ((pullbackAt B S hS τ hO).obj M)) (baseTensorComparison B S hS τ N P) =
      baseTensorComparison B S hS τ (zariskiTensor S M N) P ≫
        tensorMap B S hS τ hO ((pullbackAt B S hS τ hO).obj (zariskiTensor S M N))
          (bigTensor B S hS τ hO ((pullbackAt B S hS τ hO).obj M) ((pullbackAt B S hS τ hO).obj N))
          ((pullbackAt B S hS τ hO).obj P) ((pullbackAt B S hS τ hO).obj P)
          (baseTensorComparison B S hS τ M N) (𝟙 ((pullbackAt B S hS τ hO).obj P)) ≫
        (tensorProductAssociator (baseRingedSite B S hS τ).O.obj hO ((pullbackAt B S hS τ hO).obj M)
          ((pullbackAt B S hS τ hO).obj N) ((pullbackAt B S hS τ hO).obj P)).hom :=
  associatorOfSheafCondition B S hS τ hO M N P

/-- The associativity coherence of `𝓕 ↦ 𝓕^a` at one triple of arguments, exactly as
`Stacks.SheafOfModules.TransportCoherence.transported_associator'` produces it from the constants
above. -/
private theorem transportedAssociatorAt (τ : SiteKind)
    (hO : Presheaf.IsSheaf (baseRingedSite B S hS τ).J
      (structureRingPresheaf (baseRingedSite B S hS τ).O.obj))
    (A D E : SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf
      (zariskiStructureIsSheaf S))) :
    (associatedAt B S hS τ hO).map (tensorProductAssociator S.presheaf
      (zariskiStructureIsSheaf S) A D E).hom ≫
        tensorComparisonMap B S hS τ hO A (zariskiTensor S D E) ≫
        tensorMap B S hS τ hO ((associatedAt B S hS τ hO).obj A) ((associatedAt B S hS τ hO).obj A)
          ((associatedAt B S hS τ hO).obj (zariskiTensor S D E)) (bigTensor B S hS τ hO
          ((associatedAt B S hS τ hO).obj D) ((associatedAt B S hS τ hO).obj E))
          (𝟙 ((associatedAt B S hS τ hO).obj A)) (tensorComparisonMap B S hS τ hO D E) =
      tensorComparisonMap B S hS τ hO (zariskiTensor S A D) E ≫
        tensorMap B S hS τ hO ((associatedAt B S hS τ hO).obj (zariskiTensor S A D))
          (bigTensor B S hS τ hO ((associatedAt B S hS τ hO).obj A)
          ((associatedAt B S hS τ hO).obj D)) ((associatedAt B S hS τ hO).obj E)
          ((associatedAt B S hS τ hO).obj E)
          (tensorComparisonMap B S hS τ hO A D) (𝟙 ((associatedAt B S hS τ hO).obj E)) ≫
        (tensorProductAssociator (baseRingedSite B S hS τ).O.obj hO
          ((associatedAt B S hS τ hO).obj A) ((associatedAt B S hS τ hO).obj D)
          ((associatedAt B S hS τ hO).obj E)).hom :=
  Stacks.SheafOfModules.TransportCoherence.transported_associator'
    (pullbackToBaseAt B S hS τ hO) (zariskiTensor S) (bigTensor B S hS τ hO) (tensorMap B S hS τ hO)
    (tensorProductAssociator S.presheaf (zariskiStructureIsSheaf S))
    (tensorProductAssociator (baseRingedSite B S hS τ).O.obj hO)
    (baseTensorComparison B S hS τ) (tensorComparisonMap B S hS τ hO)
    (tensorIsoHom B S hS τ hO) (tensorMap_comp B S hS τ hO) (tensorMap_assoc B S hS τ hO)
    (associatorOfSheafCondition' B S hS τ hO) A D E

/-- The tensor product sheaf of the identity and an isomorphism is
`AlgebraicGeometry.BigFppfOver.tensorMap` of the pair, by `rfl`. -/
private theorem tensorIsoWhiskerLeft (τ : SiteKind)
    (hO : Presheaf.IsSheaf (baseRingedSite B S hS τ).J
      (structureRingPresheaf (baseRingedSite B S hS τ).O.obj))
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (baseRingedSite B S hS τ).O.obj hO)) {N N' : SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (baseRingedSite B S hS τ).O.obj hO)} (f : N ≅ N') :
    (Stacks.SheafOfModules.Invertible.tensorProductIso (baseRingedSite B S hS τ).O.obj hO
        (Iso.refl M) f).hom = tensorMap B S hS τ hO M M N N' (𝟙 M) f.hom := rfl

/-- The companion of `AlgebraicGeometry.BigFppfOver.tensorIsoWhiskerLeft` on the right. -/
private theorem tensorIsoWhiskerRight (τ : SiteKind)
    (hO : Presheaf.IsSheaf (baseRingedSite B S hS τ).J
      (structureRingPresheaf (baseRingedSite B S hS τ).O.obj))
    {M M' : SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (baseRingedSite B S hS τ).O.obj hO)} (N : SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (baseRingedSite B S hS τ).O.obj hO)) (e : M ≅ M') :
    (Stacks.SheafOfModules.Invertible.tensorProductIso (baseRingedSite B S hS τ).O.obj hO
        e (Iso.refl N)).hom = tensorMap B S hS τ hO M M' N N e.hom (𝟙 N) := rfl

/-- `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'_associator` with the sheaf
condition of the structure sheaf of the ringed site carried as a hypothesis, so that each factor
of the square mentions the one variable `hO` rather than a copy of the projection out of
`Stacks.SheafOfModules.Tensor.ringSheaf`. -/
private theorem associatorIsoOfSheafCondition (τ : SiteKind)
    (hO : Presheaf.IsSheaf (baseRingedSite B S hS τ).J
      (structureRingPresheaf (baseRingedSite B S hS τ).O.obj)) :
    Stacks.SheafOfModules.TensorPowerTransport.TensorIsoAssociator S.presheaf
      (zariskiStructureIsSheaf S) (baseRingedSite B S hS τ).O.obj
      hO (baseAssociatedModule B S hS τ)
      (baseAssociatedModuleTensorIso' B S hS τ) := by
  intro A D E
  rw [tensorIsoWhiskerLeft B S hS τ hO, tensorIsoWhiskerRight B S hS τ hO]
  -- The two sides are compared one factor at a time: as a single unification problem the
  -- comparison of the transport's statement with the goal does not fit the budget.
  refine Eq.trans ?_ ((transportedAssociatorAt B S hS τ hO A D E).trans ?_) <;> congr 1

/-- **The object-level tensor comparison of `𝓕 ↦ 𝓕^a` is compatible with the associativity
constraint of Tag 01CA**, at every one of the five topologies and with no hypothesis on `S`.
This is the second of the four data
`Stacks.SheafOfModules.TensorPowerTransport.powerTransportIso_tensor` asks for.

It is `AlgebraicGeometry.BigFppfOver.baseTensorComparison_associator`, the coherence for the
pullback of modules, transported along
`AlgebraicGeometry.BigFppfOver.pullbackModulesIsoBaseAssociatedModule` by
`Stacks.SheafOfModules.TransportCoherence.transported_associator'`.  The transport is
`AlgebraicGeometry.BigFppfOver.associatorIsoOfSheafCondition`, where the sheaf condition of the
structure sheaf is still a hypothesis; as for the symmetry coherence, every argument is supplied
already crossed into one spelling, because a term that leaves two of them to be matched there
exhausts the heartbeat budget at `whnf` while each crossing on its own is cheap.  The
functoriality of the tensor action is the functoriality of
`Stacks.SheafOfModules.Invertible.tensorProductBifunctor`, read at the pair shape. -/
public theorem baseAssociatedModuleTensorIso'_associator (τ : SiteKind) :
    Stacks.SheafOfModules.TensorPowerTransport.TensorIsoAssociator S.presheaf
      (zariskiStructureIsSheaf S) (baseRingedSite B S hS τ).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2
        (baseAssociatedModule B S hS τ)
      (baseAssociatedModuleTensorIso' B S hS τ) :=
  associatorIsoOfSheafCondition B S hS τ
    (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2

end AlgebraicGeometry.BigFppfOver

end
