module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.BaseSites
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.PairTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.TrivializationTorsorIso

/-!
# Transporting an isomorphism of pairs to the big `τ`-site

A pair `(ℒ, α)` of Tag 040Q on a scheme `S` is carried to a pair on the big `τ`-site of `S` by
the associated-module functor `𝓕 ↦ 𝓕^a` of Descent, Proposition 03DX; this is
`AlgebraicGeometry.basePairSheaf` and `AlgebraicGeometry.basePairTriv`.  This file shows that the
transport is compatible with isomorphisms of pairs: an isomorphism `e : ℒ ≅ ℳ` carrying `α` to
`β` has `e^a` carrying the transported trivialization `α^a` to `β^a`.

The point is the naturality in `ℒ` of the comparison `(ℒ^a)^{⊗ n} ≅ (ℒ^{⊗ n})^a` of Tag 01CU,
`Stacks.SheafOfModules.TensorPowerTransport.powerTransportIso_naturality`, whose extra datum —
the naturality of the object-level tensor comparison — is discharged for `𝓕 ↦ 𝓕^a` by
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'_natural`.

## Main results

* `Stacks.SheafOfModules.TensorPowerTransport.transportTriv_congr`: **the transported
  trivializations of two isomorphic pairs are intertwined by the transported isomorphism**, over
  an arbitrary functor with the object-level unit and tensor comparisons and the naturality of
  the latter.
* `AlgebraicGeometry.basePairTriv_congr`: **the same statement for `𝓕 ↦ 𝓕^a` on the big
  `τ`-site of a scheme**, written with the tensor power of an isomorphism of the ringed-site API.
* `AlgebraicGeometry.basePairClass_eq_of_pairIso`: **isomorphic pairs on `S` give the same
  isomorphism class of torsors of trivializations on the big `τ`-site**, hence the same class in
  `H¹((Sch/S)_τ, μ_n)`.

## Implementation notes

Three recursions compute the `n`-th tensor power of an isomorphism of invertible modules, and the
statement above has to pass between them:
`Stacks.SheafOfModules.TensorPowerTransport.powerMapOf` over an arbitrary sheaf of commutative
rings, `AlgebraicGeometry.tensorPowerMap` for a scheme, and
`Stacks.Cohomology.Torsors.Generators.powerMap` for a ringed site.  They agree, but not by
`rfl` at a variable exponent: each is defined by recursion on the exponent, so the identification
is an induction.  `Stacks.Cohomology.Torsors.Generators.powerMap_eq_powerMapOf` is an induction
whose step is a single `congrArg`, the two recursions being syntactically the same; for
`AlgebraicGeometry.tensorPowerMap_eq_powerMapOf` the step also has to move one
`CategoryTheory.Iso.trans_assoc`, the scheme-level recursion associating its triple composite to
the right and the generic one to the left.

The content is proved in
`Stacks.SheafOfModules.TensorPowerTransport.transportTriv_congr`, over an arbitrary functor and
with no site of schemes in sight.  That keeps the whole computation inside the single spelling
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` of the coefficient sheaf: a composite
of isomorphisms mixing that spelling with the ringed site's
`(Stacks.SheafOfModules.Tensor.ringSheaf X.O)` is type-correct only at default transparency, so
`rw` and `simp` refuse on it, reporting a missing pattern.  For the same reason the proof is
assembled from `Eq.trans`, `congrArg`, `CategoryTheory.Category.assoc` and the cancellation lemmas
`CategoryTheory.Iso.eq_inv_comp` and `CategoryTheory.Iso.comp_inv_eq` as terms, at the level of
the `hom` components, with `CategoryTheory.Iso.ext` at the very end.

Three retyping instances are declared `local`, each stating an instance already available at
another, definitionally equal, spelling.  Instance search will not cross any of the three, the
definitions involved being plain definitions rather than reducible abbreviations:
`AlgebraicGeometry.basePairSheaf` is the value of the associated-module functor, which is how the
tensor power of a transported isomorphism presents its module; and
`AlgebraicGeometry.schemeFunctionsRingedSite` is
`AlgebraicGeometry.BigFppfOver.baseRingedSite` by `AlgebraicGeometry.baseRingedSite_eq`, but the
sheafification instances of the big `τ`-site are stated for
`AlgebraicGeometry.BigFppfOver.baseOverTopology` and not for the projection
`(schemeFunctionsRingedSite _ _ _).J` that `AlgebraicGeometry.trivializationTorsor` asks for.

The corollary carries the hypothesis that units have local `n`-th roots on the site as an
explicit argument: it is a property of the site and of `n`, proved unconditionally by
`AlgebraicGeometry.localRoots_baseRingedSite_fppf` and its companions, and no part of Tag 040Q.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.Cohomology.Torsors (torsorSetoid)
open Stacks.SheafOfModules (IsInvertible)
open Stacks.SheafOfModules.Invertible (tensorPower tensorPowerSuccIso tensorProductIso)
open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf structureSheaf)

universe w u₁ v₁ u₂ v₂ u

namespace Stacks.SheafOfModules.TensorPowerTransport

variable {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
  (O₁ : C₁ᵒᵖ ⥤ CommRingCat.{w}) (hO₁ : Presheaf.IsSheaf J₁ (structureRingPresheaf O₁))
  [J₁.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J₁ AddCommGrpCat.{w}]
  {C₂ : Type u₂} [Category.{v₂} C₂] {J₂ : GrothendieckTopology C₂}
  (O₂ : C₂ᵒᵖ ⥤ CommRingCat.{w}) (hO₂ : Presheaf.IsSheaf J₂ (structureRingPresheaf O₂))
  [J₂.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J₂ AddCommGrpCat.{w}]
  (F : SheafOfModules.{w} (structureSheaf O₁ hO₁) ⥤ SheafOfModules.{w} (structureSheaf O₂ hO₂))

/-- **The transported trivializations of two isomorphic pairs are intertwined by the transported
isomorphism.**  Let `F` carry the structure sheaf to the structure sheaf and tensor products to
tensor products on objects, let the tensor comparison be natural, and let `e : L ≅ M` carry the
trivialization `bl` of `M^{⊗ n}` to the trivialization `al` of `L^{⊗ n}`.  Then `F.mapIso e`
carries the transported trivialization of `(M, bl)` to the transported trivialization of
`(L, al)`, the transport being
`Stacks.SheafOfModules.TensorPowerTransport.powerTransportIso` followed by `F` of the
trivialization and the unit comparison. -/
theorem transportTriv_congr (hunit : Picard.UnitIso O₁ hO₁ O₂ hO₂ F)
    (hten : Picard.TensorIso O₁ hO₁ O₂ hO₂ F) (hnat : TensorIsoNatural O₁ hO₁ O₂ hO₂ F hten)
    {L M : SheafOfModules.{w} (structureSheaf O₁ hO₁)}
    [IsInvertible O₁ hO₁ L] [IsInvertible O₁ hO₁ M] (n : ℕ)
    (al : tensorPower O₁ hO₁ L (n : ℤ) ≅ SheafOfModules.unit (structureSheaf O₁ hO₁))
    (bl : tensorPower O₁ hO₁ M (n : ℤ) ≅ SheafOfModules.unit (structureSheaf O₁ hO₁))
    (e : L ≅ M) (hcompat : powerMapOf O₁ hO₁ e n ≪≫ bl = al) :
    letI := isInvertible_obj O₁ hO₁ O₂ hO₂ F hunit hten L
    letI := isInvertible_obj O₁ hO₁ O₂ hO₂ F hunit hten M
    powerMapOf O₂ hO₂ (F.mapIso e) n ≪≫
          (((powerTransportIso O₁ hO₁ O₂ hO₂ F hunit hten M n).symm ≪≫ F.mapIso bl) ≪≫ hunit) =
        ((powerTransportIso O₁ hO₁ O₂ hO₂ F hunit hten L n).symm ≪≫ F.mapIso al) ≪≫ hunit := by
  let := isInvertible_obj O₁ hO₁ O₂ hO₂ F hunit hten L
  let := isInvertible_obj O₁ hO₁ O₂ hO₂ F hunit hten M
  have hnatur : F.map (powerMapOf O₁ hO₁ e n).hom ≫
      (powerTransportIso O₁ hO₁ O₂ hO₂ F hunit hten M n).hom =
      (powerTransportIso O₁ hO₁ O₂ hO₂ F hunit hten L n).hom ≫
        (powerMapOf O₂ hO₂ (F.mapIso e) n).hom :=
    powerTransportIso_naturality O₁ hO₁ O₂ hO₂ F hunit hten hnat e n
  have hcancel : (powerMapOf O₂ hO₂ (F.mapIso e) n).hom ≫
      (powerTransportIso O₁ hO₁ O₂ hO₂ F hunit hten M n).inv =
      (powerTransportIso O₁ hO₁ O₂ hO₂ F hunit hten L n).inv ≫
        F.map (powerMapOf O₁ hO₁ e n).hom :=
    (Iso.comp_inv_eq (powerTransportIso O₁ hO₁ O₂ hO₂ F hunit hten M n)).2
      (((Iso.eq_inv_comp (powerTransportIso O₁ hO₁ O₂ hO₂ F hunit hten L n)).2
        hnatur.symm).trans (Category.assoc _ _ _).symm)
  have hmap : F.map (powerMapOf O₁ hO₁ e n).hom ≫ F.map bl.hom = F.map al.hom :=
    (F.map_comp _ _).symm.trans (congrArg F.map (congrArg Iso.hom hcompat))
  have key : (powerMapOf O₂ hO₂ (F.mapIso e) n).hom ≫
      ((powerTransportIso O₁ hO₁ O₂ hO₂ F hunit hten M n).inv ≫ F.map bl.hom) =
      (powerTransportIso O₁ hO₁ O₂ hO₂ F hunit hten L n).inv ≫ F.map al.hom :=
    ((Category.assoc _ _ _).symm.trans (eq_whisker hcancel _)).trans
      ((Category.assoc _ _ _).trans (whisker_eq _ hmap))
  exact Iso.ext ((Category.assoc _ _ _).symm.trans (eq_whisker key _))

end Stacks.SheafOfModules.TensorPowerTransport

namespace Stacks.Cohomology.Torsors.Generators

open Stacks.SheafOfModules.TensorPowerTransport (powerMapOf)

/-- **The tensor power of an isomorphism on a ringed site is the generic one.**  The recursion of
`Stacks.Cohomology.Torsors.Generators.powerMap` and that of
`Stacks.SheafOfModules.TensorPowerTransport.powerMapOf` are the same, so the induction step is a
single `congrArg`; the two are not `rfl` at a variable exponent only because each is defined by
recursion on it. -/
theorem powerMap_eq_powerMapOf (X : RingedSite.{u₁, v₁, w})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]
    {L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M] (e : L ≅ M) :
    (k : ℕ) → powerMap X e k = powerMapOf X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 e k
  | 0 => rfl
  | k + 1 =>
      congrArg
        (fun z : tpow X L k ≅ tpow X M k =>
          ((tpowSuccIso X L k).symm ≪≫
              tensorProductIso X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 z e) ≪≫
            tpowSuccIso X M k)
        (powerMap_eq_powerMapOf X e k)

end Stacks.Cohomology.Torsors.Generators

namespace AlgebraicGeometry

open Stacks.SheafOfModules.TensorPowerTransport
  (isInvertible_obj powerMapOf powerTransportIso transportTriv_congr)
open Stacks.Cohomology.Torsors.Generators (tpow powerMap powerMap_eq_powerMapOf LocalRoots)

/-- **The tensor power of an isomorphism of invertible sheaves on a scheme is the generic one.**
The induction step moves one `CategoryTheory.Iso.trans_assoc`: the scheme-level recursion
associates its triple composite to the right and
`Stacks.SheafOfModules.TensorPowerTransport.powerMapOf` to the left. -/
theorem tensorPowerMap_eq_powerMapOf (S : Scheme.{u}) {L M : SheafOfModules.{u} (ringSheaf S)}
    [IsInvertible S.presheaf (ringSheafCond S) L]
    [IsInvertible S.presheaf (ringSheafCond S) M] (e : L ≅ M) :
    (n : ℕ) → tensorPowerMap S e n = powerMapOf S.presheaf (ringSheafCond S) e n
  | 0 => rfl
  | n + 1 =>
      (congrArg
          (fun z : tensorPower S.presheaf (ringSheafCond S) L (n : ℤ) ≅
              tensorPower S.presheaf (ringSheafCond S) M (n : ℤ) =>
            (tensorPowerSuccIso S.presheaf (ringSheafCond S) L (n : ℤ)).symm ≪≫
              tensorProductIso S.presheaf (ringSheafCond S) z e ≪≫
                tensorPowerSuccIso S.presheaf (ringSheafCond S) M (n : ℤ))
          (tensorPowerMap_eq_powerMapOf S e n)).trans
        (Iso.trans_assoc _ _ _).symm

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (τ : SiteKind) (n : ℕ)

/-- The invertibility of the associated module of the invertible sheaf of a pair, at the spelling
instance search meets it in: the module written as the value of the associated-module functor,
which is how the tensor power of `AlgebraicGeometry.BigFppfOver.baseAssociatedModule.mapIso`
presents it, rather than as `AlgebraicGeometry.basePairSheaf`.  The two are the same sheaf of
modules, but `AlgebraicGeometry.basePairSheaf` does not unfold at instance transparency, so
`AlgebraicGeometry.basePairSheaf_isInvertible` alone is not found. -/
local instance basePairSheafObj_isInvertible (P : TrivializedPower S n) :
    IsInvertible (BigFppfOver.baseRingedSite B S hS τ).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).2
      ((BigFppfOver.baseAssociatedModule B S hS τ).obj P.sheaf) :=
  basePairSheaf_isInvertible B S hS τ n P

/-- Sheafification of abelian presheaves on the big `τ`-site of `S`, at the spelling instance
search meets it in inside `AlgebraicGeometry.trivializationTorsor`: the topology written as the
projection `(schemeFunctionsRingedSite _ _ _).J` of the ringed site built from the site, the
functor to schemes and the sheaf condition of the global functions.  That ringed site is
`AlgebraicGeometry.BigFppfOver.baseRingedSite` by `AlgebraicGeometry.baseRingedSite_eq`, but the
projection does not unfold at instance transparency: the sheaf condition carried by
`AlgebraicGeometry.FibredSite.baseStructureSheaf` is stated for a presheaf that is the composite
`_.op ⋙ Scheme.Γ` only after unfolding. -/
local instance baseSchemeFunctions_hasWeakSheafify :
    HasWeakSheafify (schemeFunctionsRingedSite (BigFppfOver.baseOverTopology B S hS τ)
      (BigFppfOver.toScheme B S hS)
      (BigFppfOver.baseRingedSite B S hS τ).O.property).J AddCommGrpCat.{u} :=
  inferInstanceAs (HasWeakSheafify (BigFppfOver.baseOverTopology B S hS τ) AddCommGrpCat.{u})

/-- Weak equivalences of abelian presheaves on the big `τ`-site of `S` are the locally bijective
maps, at the same spelling. -/
local instance baseSchemeFunctions_wEqualsLocallyBijective :
    (schemeFunctionsRingedSite (BigFppfOver.baseOverTopology B S hS τ)
        (BigFppfOver.toScheme B S hS)
        (BigFppfOver.baseRingedSite B S hS τ).O.property).J.WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  inferInstanceAs ((BigFppfOver.baseOverTopology B S hS τ).WEqualsLocallyBijective
    AddCommGrpCat.{u})

/-- An isomorphism of pairs on `S`, read through the generic tensor power of an isomorphism: the
compatibility of `AlgebraicGeometry.PairIso` with
`Stacks.SheafOfModules.TensorPowerTransport.powerMapOf` in place of
`AlgebraicGeometry.tensorPowerMap`. -/
theorem pairIso_compatible' (P Q : TrivializedPower S n) (φ : PairIso P Q) :
    letI := P.invertible
    letI := Q.invertible
    powerMapOf S.presheaf (ringSheafCond S) φ.sheafIso n ≪≫ Q.trivialization =
      P.trivialization :=
  let := P.invertible
  let := Q.invertible
  (congrArg (· ≪≫ Q.trivialization) (tensorPowerMap_eq_powerMapOf S φ.sheafIso n).symm).trans
    φ.compatible

/-- **An isomorphism of pairs on `S` carries the transported trivialization of one pair to the
transported trivialization of the other**, on the big `τ`-site of `S`.  This is part (1) of the
second construction of Tag 040Q for a pair read on the big site: it is
`Stacks.SheafOfModules.TensorPowerTransport.transportTriv_congr` at the associated-module functor
of Descent, Proposition 03DX, whose tensor comparison is natural by
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'_natural`. -/
theorem basePairTriv_congr (P Q : TrivializedPower S n) (φ : PairIso P Q) :
    letI := basePairSheaf_isInvertible B S hS τ n P
    letI := basePairSheaf_isInvertible B S hS τ n Q
    powerMap (BigFppfOver.baseRingedSite B S hS τ)
          ((BigFppfOver.baseAssociatedModule B S hS τ).mapIso φ.sheafIso) n ≪≫
        basePairTriv B S hS τ n Q =
      basePairTriv B S hS τ n P :=
  let := basePairSheaf_isInvertible B S hS τ n P
  let := basePairSheaf_isInvertible B S hS τ n Q
  let := P.invertible
  let := Q.invertible
  Iso.ext
    ((eq_whisker (congrArg Iso.hom
        (powerMap_eq_powerMapOf (BigFppfOver.baseRingedSite B S hS τ)
          ((BigFppfOver.baseAssociatedModule B S hS τ).mapIso φ.sheafIso) n)) _).trans
      (congrArg Iso.hom
        (transportTriv_congr S.presheaf (ringSheafCond S)
          (BigFppfOver.baseRingedSite B S hS τ).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).2
          (BigFppfOver.baseAssociatedModule B S hS τ)
          (BigFppfOver.baseAssociatedModulePicardUnitIso B S hS τ)
          (BigFppfOver.baseAssociatedModuleTensorIso' B S hS τ)
          (BigFppfOver.baseAssociatedModuleTensorIso'_natural B S hS τ) n
          P.trivialization Q.trivialization φ.sheafIso
          (pairIso_compatible' S n P Q φ))))

/-- **Isomorphic pairs on `S` have the same isomorphism class of torsors of trivializations on
the big `τ`-site of `S`**, hence the same class in `H¹((Sch/S)_τ, μ_n)`.  This is part (2) of the
second construction of Tag 040Q for a pair read on the big site: it is
`AlgebraicGeometry.trivializationTorsor_class_eq_of_iso'` fed the transported isomorphism and
`AlgebraicGeometry.basePairTriv_congr`.  The hypothesis that units have local `n`-th roots is
carried as an argument; it is proved unconditionally by
`AlgebraicGeometry.localRoots_baseRingedSite_fppf` and its companions. -/
theorem basePairClass_eq_of_pairIso (hroot : LocalRoots (BigFppfOver.baseRingedSite B S hS τ) n)
    (P Q : TrivializedPower S n) (φ : PairIso P Q) :
    Quotient.mk
          (torsorSetoid (rootsOfUnitySheaf (BigFppfOver.baseOverTopology B S hS τ)
            (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS τ) n))
          (trivializationTorsor (BigFppfOver.baseOverTopology B S hS τ)
            (BigFppfOver.toScheme B S hS) (BigFppfOver.baseRingedSite B S hS τ).O.property
            (unitsPresheaf_isSheaf_base B S hS τ) n
            (baseRingedSite_isLocallyRinged B S hS τ) hroot (basePairSheaf B S hS τ n P)
            (basePairSheaf_isInvertible B S hS τ n P) (basePairTriv B S hS τ n P)) =
      Quotient.mk
        (torsorSetoid (rootsOfUnitySheaf (BigFppfOver.baseOverTopology B S hS τ)
          (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS τ) n))
        (trivializationTorsor (BigFppfOver.baseOverTopology B S hS τ)
          (BigFppfOver.toScheme B S hS) (BigFppfOver.baseRingedSite B S hS τ).O.property
          (unitsPresheaf_isSheaf_base B S hS τ) n
          (baseRingedSite_isLocallyRinged B S hS τ) hroot (basePairSheaf B S hS τ n Q)
          (basePairSheaf_isInvertible B S hS τ n Q) (basePairTriv B S hS τ n Q)) :=
  trivializationTorsor_class_eq_of_iso' (BigFppfOver.baseOverTopology B S hS τ)
    (BigFppfOver.toScheme B S hS) (BigFppfOver.baseRingedSite B S hS τ).O.property
    (unitsPresheaf_isSheaf_base B S hS τ) n (baseRingedSite_isLocallyRinged B S hS τ) hroot
    (basePairSheaf B S hS τ n P) (basePairSheaf B S hS τ n Q)
    (basePairSheaf_isInvertible B S hS τ n P) (basePairSheaf_isInvertible B S hS τ n Q)
    (basePairTriv B S hS τ n P) (basePairTriv B S hS τ n Q)
    ((BigFppfOver.baseAssociatedModule B S hS τ).mapIso φ.sheafIso)
    (basePairTriv_congr B S hS τ n P Q φ)

end AlgebraicGeometry

end
