module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.Deformation.Artin.FormalObject
public import StacksFrontier.Deformation.Artin.FormalObject.Predeformation
public import StacksFrontier.Deformation.Artin.FormalObject.Versal
public import StacksFrontier.Deformation.Artin.LimitPreservingPresheafStack
public import StacksFrontier.Deformation.Predeformation.PointsFromBase
public import StacksFrontier.RingTheory.AdicCompletion.KerTruncation
public import StacksFrontier.RingTheory.AdicCompletion.QuotientCompletionMap

/-!
# The functor, stack and formal object of the Stacks 07XI counterexample

Let `Λ` be a Noetherian ring with maximal ideal `𝔪`, and let `C` be a `Λ`-algebra of finite
type equipped with a `Λ`-algebra map to a chosen ring `R` (in the Example, `R = Λ_𝔪^∧`, but
that specialization is not needed for the constructions of `F` and `𝒳`). Set `S = Spec(Λ)`,
let `U = S ∖ {𝔪}` be the open complement of the point of `𝔪`, and `S' = U ⨿ Spec(C)`.

This file constructs, for a chosen big fppf site `B` containing `S`: the scheme `S'` and the
canonical morphism `g : S' ⟶ S`; the size bound placing `S'` inside `B`; and the set-valued
presheaf `F` on the big fppf site of `S` sending an object `T` to a one-point set when its
structure morphism factors through `g`, and to the empty set otherwise. The associated
category fibred in groupoids `𝒳 = 𝒮_F` is then obtained from `F` for free, via
`AlgebraicGeometry.Stack.fibredCategory`.

It then constructs the Example's formal object `ξ` over `R = Λ_𝔪^∧`: the complete local base
`R` with its structure morphism to `S`, and the levels of `ξ`, which exist because
`Λ → C → R → R/𝔪_R^{n+1}` makes every infinitesimal neighbourhood of the closed point of
`Spec(R)` factor through `Spec(C) ⊆ S'`, hence lie in `F`.

Finally, `𝒳 → (Sch/S)_{fppf}` is limit preserving on objects: `g : S' ⟶ S` is locally of
finite presentation, so `F` descends along inverse limits of affine objects.

## Main definitions

* `Deformation.Artin.GRingCounterexample.openComplement`: the open subscheme `U = S ∖ {𝔪}`.
* `Deformation.Artin.GRingCounterexample.auxScheme`: the scheme `S' = U ⨿ Spec(C)`.
* `Deformation.Artin.GRingCounterexample.auxMap`: the morphism `g : S' ⟶ S`.
* `Deformation.Artin.GRingCounterexample.functor`: the presheaf `F`.
* `Deformation.Artin.GRingCounterexample.stack`: the category `𝒳 = 𝒮_F` fibred in sets.
* `Deformation.Artin.GRingCounterexample.completion`: the ring `R = Λ_𝔪^∧`.
* `Deformation.Artin.GRingCounterexample.completionBase`: `R` as a complete local base
  over `S`.
* `Deformation.Artin.GRingCounterexample.formalObject`: the formal object `ξ` over `R`.

## Main results

* `Deformation.Artin.GRingCounterexample.contains_auxScheme`: the size bound `B.Contains S'`.
* `Deformation.Artin.GRingCounterexample.locallyOfFinitePresentation_auxMap`: `g : S' ⟶ S` is
  locally of finite presentation.
* `Deformation.Artin.GRingCounterexample.descendsOnAffineLimits_functor`: `F` descends along
  inverse limits of affine objects of the site.
* `Deformation.Artin.GRingCounterexample.isLimitPreservingOnObjects_stack`: `𝒳 = 𝒮_F` is limit
  preserving on objects.

## References

* [Stacks Project, Tag 07XI](https://stacks.math.columbia.edu/tag/07XI)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 07X4](https://stacks.math.columbia.edu/tag/07X4)
-/


@[expose] public noncomputable section

namespace Deformation.Artin.GRingCounterexample

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v w

variable {Λ : Type u} [CommRing Λ] (m : Ideal Λ) [hm : m.IsMaximal]
variable (C : Type u) [CommRing C] (φ : Λ →+* C)

/-- The point of `Spec(Λ)` corresponding to the maximal ideal `𝔪`. -/
public abbrev point : (Spec (.of Λ) : Scheme) := ⟨m, hm.isPrime⟩

/-- **The open complement `U = S ∖ {𝔪}`.** Removing a single point cut out by a maximal
ideal leaves an open subscheme, since `{𝔪}` is closed. -/
public def openComplement : (Spec (.of Λ)).Opens :=
  ⟨{point m}ᶜ, (PrimeSpectrum.isClosed_singleton_iff_isMaximal (point m)).mpr hm |>.isOpen_compl⟩

/-- **The auxiliary scheme `S' = U ⨿ Spec(C)`.** -/
public def auxScheme : Scheme.{u} := (openComplement m).toScheme ⨿ Spec (.of C)

/-- **The canonical morphism `g : S' ⟶ S`**, glued from the open immersion `U ↪ S` and the
morphism `Spec(C) ⟶ Spec(Λ)` dual to the structure map `φ : Λ →+* C`. -/
public def auxMap : auxScheme m C ⟶ Spec (.of Λ) :=
  coprod.desc (openComplement m).ι (Spec.map (CommRingCat.ofHom φ))

/-- **The inclusion `U ↪ S'`** of the first summand. -/
public def auxInl : (openComplement m).toScheme ⟶ auxScheme m C := Limits.coprod.inl

/-- **The inclusion `Spec(C) ↪ S'`** of the second summand. -/
public def auxInr : Spec (.of C) ⟶ auxScheme m C := Limits.coprod.inr

/-- The first summand of `S' = U ⨿ Spec(C)` maps to `S` by the open immersion of `U`. -/
public theorem auxInl_auxMap :
    auxInl m C ≫ auxMap m C φ = (openComplement m).ι :=
  Limits.coprod.inl_desc _ _

/-- The second summand of `S' = U ⨿ Spec(C)` maps to `S` by `Spec` of the structure map
`φ : Λ → C`. -/
public theorem auxInr_auxMap :
    auxInr m C ≫ auxMap m C φ = Spec.map (CommRingCat.ofHom φ) :=
  Limits.coprod.inr_desc _ _

/-- The open complement has size at most that of the ambient scheme. -/
private theorem size_openComplement_le :
    (openComplement m : Scheme.{u}).size ≤ (Spec (.of Λ) : Scheme.{u}).size :=
  Scheme.size_coe_opens_le (Spec (.of Λ)) (openComplement m)

/-- **The auxiliary scheme is inside the site, provided `Spec(Λ)` and `Spec(C)` are.** -/
public theorem contains_auxScheme (B : AlgebraicGeometry.BigFppfSite.{u})
    (hS : (Spec (.of Λ) : Scheme.{u}).size < B.cutoff)
    (hC : (Spec (.of C) : Scheme.{u}).size < B.cutoff) :
    (auxScheme m C : Scheme.{u}).size < B.cutoff := by
  let A : ULift.{u} WalkingPair → Scheme.{u} :=
    fun i => i.down.casesOn (openComplement m).toScheme (Spec (.of C))
  let Wsum : Scheme.{u} := ∐ A
  have hWsum : Wsum.size < B.cutoff := by
    apply Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof
      (ι := ULift.{u} WalkingPair) (Y := A) (by simp)
    intro b
    rcases b with ⟨b⟩
    cases b with
    | left => simpa [A] using (size_openComplement_le m).trans_lt hS
    | right => simpa [A] using hC
  change ((openComplement m).toScheme ⨿ Spec (.of C)).size < B.cutoff
  rw [Scheme.size_congr (coprodIsoSigma (openComplement m).toScheme (Spec (.of C)))]
  exact hWsum

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (hS : B.Contains (Spec (.of Λ)))

/-- **The structure morphism to `S` of an object `T` of the big fppf category over `S`.** -/
public def structureMap (T : BigFppfOver B (Spec (.of Λ)) hS) :
    (BigFppfOver.toScheme B (Spec (.of Λ)) hS).obj T ⟶ Spec (.of Λ) :=
  B.inclusion.map T.hom

/-- Restriction along a morphism of the site commutes with taking the structure map to `S`:
both compute the image, in `B.Schemes`, of the underlying triangle identity of the slice
category `Over (B.obj hS)`. -/
public theorem toScheme_map_comp_structureMap
    {T T' : BigFppfOver B (Spec (.of Λ)) hS} (α : T' ⟶ T) :
    (BigFppfOver.toScheme B (Spec (.of Λ)) hS).map α ≫ structureMap B hS T =
      structureMap B hS T' := by
  change B.inclusion.map ((BigFppfOver.forget B (Spec (.of Λ)) hS).map α) ≫
      B.inclusion.map T.hom = B.inclusion.map T'.hom
  rw [← B.inclusion.map_comp]
  exact congrArg B.inclusion.map (Over.w α)

/-- **The proposition that the structure morphism of `T` factors through `g : S' ⟶ S`.** -/
public def Factors (m : Ideal Λ) [m.IsMaximal] (C : Type u) [CommRing C] (φ : Λ →+* C)
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hS : B.Contains (Spec (.of Λ)))
    (T : BigFppfOver B (Spec (.of Λ)) hS) : Prop :=
  ∃ h : (BigFppfOver.toScheme B (Spec (.of Λ)) hS).obj T ⟶ auxScheme m C,
    h ≫ auxMap m C φ = structureMap B hS T

/-- Transporting a factorization through the big fppf site along a restriction map. -/
public theorem factors_map (m : Ideal Λ) [m.IsMaximal] (C : Type u) [CommRing C] (φ : Λ →+* C)
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hS : B.Contains (Spec (.of Λ)))
    {T T' : BigFppfOver B (Spec (.of Λ)) hS} (α : T' ⟶ T) (h : Factors m C φ B hS T) :
    Factors m C φ B hS T' :=
  ⟨(BigFppfOver.toScheme B (Spec (.of Λ)) hS).map α ≫ h.choose,
    by rw [Category.assoc, h.choose_spec, toScheme_map_comp_structureMap]⟩

/-- Restriction of a one-point witness of `Factors` along a morphism of the big fppf category
over `S`, as a morphism of `Type u`. -/
public def restrictFactors (m : Ideal Λ) [m.IsMaximal] (C : Type u) [CommRing C] (φ : Λ →+* C)
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hS : B.Contains (Spec (.of Λ)))
    {T T' : (BigFppfOver B (Spec (.of Λ)) hS)ᵒᵖ} (α : T ⟶ T') :
    ULift.{u} (PLift (Factors m C φ B hS T.unop)) ⟶
      ULift.{u} (PLift (Factors m C φ B hS T'.unop)) :=
  ↾ fun x => ULift.up (PLift.up (factors_map m C φ B hS α.unop x.down.down))

/-- **The functor `F` of the counterexample.** It sends an object `T` of the big fppf
category over `S` to a one-point set when the structure morphism of `T` factors through
`g : S' ⟶ S`, and to the empty set otherwise; functoriality is transport of the chosen
factorization along the restriction map. Since the value at each object is a (univalent)
proposition wrapped in `PLift`, it is a subsingleton, and the functor laws hold by proof
irrelevance. -/
public def functor (m : Ideal Λ) [m.IsMaximal] (C : Type u) [CommRing C] (φ : Λ →+* C)
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hS : B.Contains (Spec (.of Λ))) :
    (BigFppfOver B (Spec (.of Λ)) hS)ᵒᵖ ⥤ Type u where
  obj T := ULift.{u} (PLift (Factors m C φ B hS T.unop))
  map {T T'} α := restrictFactors m C φ B hS α
  map_id T := by ext x; exact Subsingleton.elim _ _
  map_comp f g := by ext x; exact Subsingleton.elim _ _

/-- **The category `𝒳 = 𝒮_F` fibred in groupoids over the big fppf site of `S`,** built from
the functor `F` via the Grothendieck construction of **Stacks 0458**. -/
@[stacks 07XI "the Example's construction: the functor `F` on the big fppf site of \
`S = Spec(Λ)`, which is a one-point set on a `T` whose structure morphism factors through \
`S' = (S ∖ {𝔪}) ⨿ Spec(C)` and empty otherwise, and the category `𝒳 = 𝒮_F` fibred in sets \
that it defines. The source's three assertions about them are \
`Deformation.Artin.GRingCounterexample.isLimitPreservingOnObjects_stack`, \
`Deformation.Artin.GRingCounterexample.isEffective_formalObject` and \
`Deformation.Artin.GRingCounterexample.isVersal_formalObject`, about the formal object \
`Deformation.Artin.GRingCounterexample.formalObject`; the Example whole -- those assertions \
together with the Example's conditional conclusion, which assumes the conclusion of Stacks \
07XH for these `𝒳` rather than any G-ring property -- is \
`Deformation.Artin.GRingCounterexample.exists_algHom_henselian`."]
public def stack (m : Ideal Λ) [m.IsMaximal] (C : Type u) [CommRing C] (φ : Λ →+* C)
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hS : B.Contains (Spec (.of Λ))) :
    CategoryTheory.CatFiberedInGroupoids (BigFppfOver B (Spec (.of Λ)) hS) :=
  AlgebraicGeometry.Stack.fibredCategory B (Spec (.of Λ)) hS (functor m C φ B hS)

/-- The values of `F` are subsingletons: each is a proposition wrapped in `PLift` and
`ULift`. -/
public instance subsingleton_functor_obj
    (T : (BigFppfOver B (Spec (.of Λ)) hS)ᵒᵖ) :
    Subsingleton ((functor m C φ B hS).obj T) :=
  inferInstanceAs (Subsingleton (ULift.{u} (PLift (Factors m C φ B hS T.unop))))

/-- **Morphisms of `𝒳 = 𝒮_F` are determined by their base component.** The fibres of `𝒮_F` are
discrete and `F` takes only subsingleton values, so the fibre component of a morphism carries no
information beyond the morphism of the site it lies over. -/
public theorem stack_hom_ext {z w : (stack m C φ B hS).val.obj} (u v : z ⟶ w)
    (h : u.base = v.base) : u = v := by
  refine CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.ext _ _ h ?_
  apply Discrete.hom_eq

/-- **Any two objects of `𝒳 = 𝒮_F` over the same object of the site are joined by a morphism
over the identity.** The fibres of `𝒮_F` are discrete and `F` is subsingleton-valued, so the
only datum a morphism needs is its base component, which here is the given equality. -/
public def verticalHom {z w : (stack m C φ B hS).val.obj}
    (h : (stack m C φ B hS).val.p.obj z = (stack m C φ B hS).val.p.obj w) : z ⟶ w where
  base := eqToHom h
  fiber := Discrete.eqToHom (Subsingleton.elim _ _)

/-- The base component of `verticalHom` is the transport along the given equality. -/
public theorem verticalHom_base {z w : (stack m C φ B hS).val.obj}
    (h : (stack m C φ B hS).val.p.obj z = (stack m C φ B hS).val.p.obj w) :
    (verticalHom m C φ B hS h).base = eqToHom h :=
  rfl

/-! ### The formal object over `R = Λ_𝔪^∧` -/

open IsLocalRing in
/-- **The ring `R = Λ_𝔪^∧`** of the Example: the completion of the local ring of `Λ` at `𝔪`
in its maximal-ideal-adic topology. -/
public abbrev completion : Type u :=
  AdicCompletion (maximalIdeal (Localization.AtPrime m)) (Localization.AtPrime m)

open IsLocalRing in
/-- `Λ → R/𝔪_R` is surjective: the residue field of `R = Λ_𝔪^∧` is that of `Λ_𝔪`, which is
`κ(𝔪) = Λ/𝔪` because `𝔪` is maximal. -/
private theorem surjective_residue_comp_algebraMap [IsNoetherianRing Λ] :
    Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal (completion m) ^ (0 + 1))).comp
        (algebraMap Λ (completion m))) := by
  have hloc : Function.Surjective
      (algebraMap Λ (ResidueField (Localization.AtPrime m))) := by
    intro y
    obtain ⟨x, hx⟩ := (Ideal.bijective_algebraMap_quotient_residueField m).2 y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨a, by rw [← hx, Ideal.algebraMap_quotient_residueField_mk]⟩
  have hcompl := AdicCompletion.residueField_map_bijective (Localization.AtPrime m)
  rw [pow_one]
  intro y
  obtain ⟨z, hz⟩ := hcompl.2 y
  obtain ⟨a, ha⟩ := hloc z
  refine ⟨a, ?_⟩
  change Ideal.Quotient.mk (maximalIdeal (completion m)) (algebraMap Λ (completion m) a) = y
  rw [← hz, ← ha,
    show algebraMap Λ (ResidueField (Localization.AtPrime m)) a =
      residue (Localization.AtPrime m) (algebraMap Λ (Localization.AtPrime m) a) from rfl,
    ResidueField.map_residue]
  change _ = residue (completion m) (algebraMap (Localization.AtPrime m) (completion m)
    (algebraMap Λ (Localization.AtPrime m) a))
  rw [← IsScalarTower.algebraMap_apply]
  rfl

open IsLocalRing in
/-- **`R = Λ_𝔪^∧` as a complete local base over `S = Spec(Λ)`.** It is Noetherian and
`𝔪_R`-adically complete because `Λ` is Noetherian, and its residue field is of finite type
over `S` because `Λ → R/𝔪_R` is surjective, so that `Spec(R/𝔪_R) → S` is a closed
immersion. -/
public def completionBase [IsNoetherianRing Λ] :
    Deformation.Artin.FormalBase (Spec (.of Λ)) where
  R := completion m
  noetherian := inferInstance
  complete := inferInstance
  toS := Spec.map (CommRingCat.ofHom (algebraMap Λ (completion m)))
  residueLocallyFiniteType := by
    rw [AlgebraicGeometry.adicThickeningι, ← Spec.map_comp]
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (maximalIdeal (completion m) ^ (0 + 1))).comp
          (algebraMap Λ (completion m))))) :=
      IsClosedImmersion.spec_of_surjective _ (surjective_residue_comp_algebraMap m)
    infer_instance
  residueQuasiCompact := by
    rw [AlgebraicGeometry.adicThickeningι, ← Spec.map_comp]
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (maximalIdeal (completion m) ^ (0 + 1))).comp
          (algebraMap Λ (completion m))))) :=
      IsClosedImmersion.spec_of_surjective _ (surjective_residue_comp_algebraMap m)
    infer_instance

section FormalObject

open IsLocalRing

variable [IsNoetherianRing Λ]

/-- The truncation `Spec(R/𝔪_R^{n+1})` of `R = Λ_𝔪^∧` mapped to `Spec(C)` through the
Example's factorization `Λ → C → R`. -/
public def truncationToSpecC (ψ : C →+* completion m) (n : ℕ) :
    (completionBase m).truncation n ⟶ Spec (.of C) :=
  Spec.map (CommRingCat.ofHom
    ((Ideal.Quotient.mk (maximalIdeal (completion m) ^ (n + 1))).comp ψ))

/-- Each infinitesimal thickening of `Spec(R)` lies in the chosen big fppf site as soon as
`Spec(R)` does, by **Stacks 07X4**'s size bound on quotients. -/
public theorem completionContains (hR : B.Contains (Spec (.of (completion m)))) (k : ℕ) :
    B.Contains ((completionBase m).truncation k) :=
  Deformation.Artin.truncationContains B (Spec (.of Λ)) (completionBase m) hR k

/-- Every infinitesimal neighbourhood of the closed point of `Spec(R)` lies in `F`: its
structure morphism to `S` factors through `Spec(C)`, hence through `g : S' ⟶ S`, because the
Example's factorization `Λ → C → R` composes with `R → R/𝔪_R^{n+1}`. -/
public theorem factors_truncationOver (ψ : C →+* completion m)
    (hψ : ψ.comp φ = algebraMap Λ (completion m))
    (hR : B.Contains (Spec (.of (completion m)))) (n : ℕ) :
    Factors m C φ B hS (Deformation.Artin.truncationOver B (Spec (.of Λ)) hS
      (completionBase m) (completionContains m B hR) n) := by
  have hbase : (completionBase m).truncationToS n =
      Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk
        (maximalIdeal (completion m) ^ (n + 1))).comp (algebraMap Λ (completion m)))) := by
    change AlgebraicGeometry.adicThickeningι (completion m) (maximalIdeal (completion m)) n ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ (completion m))) = _
    rw [AlgebraicGeometry.adicThickeningι, ← Spec.map_comp]
    rfl
  have key : (truncationToSpecC m C ψ n ≫ auxInr m C) ≫ auxMap m C φ =
      (completionBase m).truncationToS n := by
    rw [Category.assoc, auxInr_auxMap, hbase, truncationToSpecC, ← Spec.map_comp]
    refine congrArg Spec.map (CommRingCat.hom_ext ?_)
    change ((Ideal.Quotient.mk (maximalIdeal (completion m) ^ (n + 1))).comp ψ).comp φ =
      (Ideal.Quotient.mk (maximalIdeal (completion m) ^ (n + 1))).comp
        (algebraMap Λ (completion m))
    rw [RingHom.comp_assoc, hψ]
  exact ⟨truncationToSpecC m C ψ n ≫ auxInr m C, key⟩

/-- **The formal object `ξ` over `R = Λ_𝔪^∧`** of the Example. Each level is the unique point
of `F(Spec(R/𝔪_R^{n+1}))`, which is nonempty because the Example's factorization
`Λ → C → R` makes every infinitesimal neighbourhood of the closed point map to `Spec(C)`, and
the transitions are the unique morphisms of `𝒳 = 𝒮_F` lying over the closed immersions
`Spec(R/𝔪_R^{n+1}) ↪ Spec(R/𝔪_R^{n+2})`, the fibres of `𝒮_F` being discrete and `F` taking
only subsingleton values. -/
@[stacks 07XI "the formal object `ξ` over `R = Λ_𝔪^∧` whose existence the Example asserts: \
the complete local base `R` over `S = Spec(Λ)`, the level of `ξ` at each infinitesimal \
neighbourhood of the closed point of `Spec(R)`, and the transitions. That `ξ` is effective \
(`Deformation.Artin.FormalObject.IsEffective`, Stacks 07X7) is \
`Deformation.Artin.GRingCounterexample.isEffective_formalObject`, and that it is versal \
(`Deformation.Artin.FormalObject.IsVersal`, Stacks 0CXJ) is \
`Deformation.Artin.GRingCounterexample.isVersal_formalObject`. The Example whole -- the \
three assertions together with the Example's conditional conclusion, which assumes the \
conclusion of Stacks 07XH for these `𝒳` rather than any G-ring property -- is \
`Deformation.Artin.GRingCounterexample.exists_algHom_henselian`."]
public def formalObject (ψ : C →+* completion m)
    (hψ : ψ.comp φ = algebraMap Λ (completion m))
    (hR : B.Contains (Spec (.of (completion m)))) :
    Deformation.Artin.FormalObject B (Spec (.of Λ)) hS (stack m C φ B hS).val.p where
  base := completionBase m
  contains := completionContains m B hR
  level n := ⟨Deformation.Artin.truncationOver B (Spec (.of Λ)) hS (completionBase m)
      (completionContains m B hR) n,
    Discrete.mk (ULift.up (PLift.up (factors_truncationOver m C φ B hS ψ hψ hR n)))⟩
  level_eq _ := rfl
  transition n :=
    { base := Deformation.Artin.truncationOverSucc B (Spec (.of Λ)) hS (completionBase m)
        (completionContains m B hR) n
      fiber := Discrete.eqToHom (Subsingleton.elim _ _) }
  transition_lift _ :=
    CategoryTheory.IsHomLift.of_fac _ _ _ rfl rfl rfl

end FormalObject

/-! ### Limit preservation on objects -/

section LimitPreserving

/-- **`g : S' ⟶ S` is locally of finite presentation.** The first summand `U ↪ S` is an open
immersion; the second is `Spec` of `φ : Λ → C`, of finite presentation because `C` is of
finite type over the Noetherian ring `Λ`; and `LocallyOfFinitePresentation` is Zariski local
on the source, for which `inl` and `inr` are a cover of `S'`. -/
public theorem locallyOfFinitePresentation_auxMap [IsNoetherianRing Λ]
    (hφ : RingHom.FiniteType φ) : LocallyOfFinitePresentation (auxMap m C φ) := by
  have _ : IsZariskiLocalAtSource
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
  have hC : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom φ)) :=
    (LocallyOfFinitePresentation.SpecMap_iff (CommRingCat.ofHom φ)).mpr
      (RingHom.FinitePresentation.of_finiteType.mp hφ)
  refine IsZariskiLocalAtSource.of_openCover
    (coprodOpenCover.{u, 0} (openComplement m).toScheme (Spec (.of C))) ?_
  rintro (_ | _)
  · change LocallyOfFinitePresentation (auxInl m C ≫ auxMap m C φ)
    rw [auxInl_auxMap]
    infer_instance
  · change LocallyOfFinitePresentation (auxInr m C ≫ auxMap m C φ)
    rw [auxInr_auxMap]
    exact hC

/-- **The functor `F` descends along inverse limits of affine schemes.** An element of
`F(T)` for `T = lim Tᵢ` is a factorization of `T → S` through `g : S' ⟶ S`; since `g` is
locally of finite presentation and the `Tᵢ` are affine with affine transition maps, that
factorization is defined at some stage (**Stacks 01ZC**, the surjective half of (1) ⇒ (3),
`AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`). The stage it
produces is pushed below a prescribed index by cofilteredness, restricting the factorization
along the transition map, and the compatibility equation is automatic because `F` takes only
subsingleton values. -/
public theorem descendsOnAffineLimits_functor [IsNoetherianRing Λ]
    (hφ : RingHom.FiniteType φ) :
    AlgebraicGeometry.Stack.DescendsOnAffineLimits.{u, u, u} B (Spec (.of Λ)) hS
      (functor m C φ B hS) := by
  intro I _ _ D c hc i t
  have := locallyOfFinitePresentation_auxMap m C φ hφ
  obtain ⟨a, ha⟩ := t.down.down
  have hcomp : ∀ {T T' : AlgebraicGeometry.BigAffineFppf B (Spec (.of Λ)) hS} (α : T' ⟶ T),
      (AlgebraicGeometry.BigAffineFppf.toScheme B (Spec (.of Λ)) hS).map α ≫
        structureMap B hS
          ((AlgebraicGeometry.BigAffineFppf.inclusion B (Spec (.of Λ)) hS).obj T) =
      structureMap B hS
        ((AlgebraicGeometry.BigAffineFppf.inclusion B (Spec (.of Λ)) hS).obj T') :=
    fun α => toScheme_map_comp_structureMap B hS
      ((AlgebraicGeometry.BigAffineFppf.inclusion B (Spec (.of Λ)) hS).map α)
  let τ : (D ⋙ AlgebraicGeometry.BigAffineFppf.toScheme B (Spec (.of Λ)) hS) ⟶
      (CategoryTheory.Functor.const I).obj (Spec (.of Λ)) :=
    { app := fun k => structureMap B hS
        ((AlgebraicGeometry.BigAffineFppf.inclusion B (Spec (.of Λ)) hS).obj (D.obj k))
      naturality := fun k l f => by simpa using hcomp (D.map f) }
  have hπ : ∀ k : I,
      (AlgebraicGeometry.BigAffineFppf.toScheme B (Spec (.of Λ)) hS).map (c.π.app k) ≫
        τ.app k =
      structureMap B hS
        ((AlgebraicGeometry.BigAffineFppf.inclusion B (Spec (.of Λ)) hS).obj c.pt) :=
    fun k => hcomp (c.π.app k)
  have hAff : ∀ k : I,
      IsAffine ((D ⋙ AlgebraicGeometry.BigAffineFppf.toScheme B (Spec (.of Λ)) hS).obj k) :=
    fun k => inferInstanceAs (IsAffine
      ((AlgebraicGeometry.BigAffineFppf.toScheme B (Spec (.of Λ)) hS).obj (D.obj k)))
  have : ∀ {k l : I} (f : k ⟶ l),
      IsAffineHom ((D ⋙ AlgebraicGeometry.BigAffineFppf.toScheme B (Spec (.of Λ)) hS).map f) :=
    fun _ => isAffineHom_of_isAffine _
  obtain ⟨k, g, -, hg⟩ :=
    AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (D := D ⋙ AlgebraicGeometry.BigAffineFppf.toScheme B (Spec (.of Λ)) hS) τ
      (auxMap m C φ)
      ((AlgebraicGeometry.BigAffineFppf.toScheme B (Spec (.of Λ)) hS).mapCone c) hc a
      (by
        refine CategoryTheory.NatTrans.ext (funext fun k => ?_)
        change (AlgebraicGeometry.BigAffineFppf.toScheme B (Spec (.of Λ)) hS).map
            (c.π.app k) ≫ τ.app k = a ≫ auxMap m C φ
        rw [hπ k, ha])
  have hfactors : Factors m C φ B hS
      ((AlgebraicGeometry.BigAffineFppf.inclusion B (Spec (.of Λ)) hS).obj (D.obj k)) :=
    ⟨g, hg⟩
  refine ⟨CategoryTheory.IsCofiltered.min i k, CategoryTheory.IsCofiltered.minToLeft i k,
    ULift.up (PLift.up (factors_map m C φ B hS
      ((AlgebraicGeometry.BigAffineFppf.inclusion B (Spec (.of Λ)) hS).map
        (D.map (CategoryTheory.IsCofiltered.minToRight i k))) hfactors)),
    Subsingleton.elim _ _⟩

/-- **`𝒳 = 𝒮_F` is limit preserving on objects**, the first of the Example's three assertions
about `𝒳`. -/
@[stacks 07XI "the Example's assertion that `𝒳 = 𝒮_F ⟶ (Sch/S)_{fppf}` is limit preserving \
on objects. The construction of `F` and `𝒳` is \
`Deformation.Artin.GRingCounterexample.stack`, and the other two assertions, about the \
formal object `ξ` over `R = Λ_𝔪^∧`, are \
`Deformation.Artin.GRingCounterexample.isEffective_formalObject` and \
`Deformation.Artin.GRingCounterexample.isVersal_formalObject`. The Example whole is \
`Deformation.Artin.GRingCounterexample.exists_algHom_henselian`."]
public theorem isLimitPreservingOnObjects_stack [IsNoetherianRing Λ]
    (hφ : RingHom.FiniteType φ) :
    AlgebraicGeometry.BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1}
      B (Spec (.of Λ)) hS (stack m C φ B hS)
      (Deformation.Artin.Approximation.baseFiberedCategory B (Spec (.of Λ)) hS)
      (Deformation.Artin.Approximation.structureMorphism B (Spec (.of Λ)) hS
        (stack m C φ B hS)) :=
  AlgebraicGeometry.Stack.isLimitPreservingOnObjects_fibredCategory B (Spec (.of Λ)) hS
    (functor m C φ B hS)
    (descendsOnAffineLimits_functor m C φ B hS hφ)

end LimitPreserving

/-! ### Points of `R = Λ_𝔪^∧` at Artinian local `Λ_𝔪`-algebras -/

section Points

open IsLocalRing

variable [IsNoetherianRing Λ]

/-- **`R = Λ_𝔪^∧` as an object of the category of Noetherian complete local
`Λ_𝔪`-algebras**, with its own residue field as the chosen identification. It is
`(formalObject …).completeLocalBase (Localization.AtPrime m)` (`completeLocalBase_eq`). -/
public def completeBase : Deformation.CompleteLocalAlgCat.{u, u, u}
    (Localization.AtPrime m) (ResidueField (completion m)) where
  carrier := completion m
  completeLocal := ⟨inferInstance, inferInstance, inferInstance⟩
  residueEquiv := AlgEquiv.refl

/-- **The `Λ_𝔪`-algebra structure on the base ring of the Example's formal object.** -/
public instance algebra_formalObject_base (ψ : C →+* completion m)
    (hψ : ψ.comp φ = algebraMap Λ (completion m))
    (hR : B.Contains (Spec (.of (completion m)))) :
    Algebra (Localization.AtPrime m) (formalObject m C φ B hS ψ hψ hR).base.R :=
  inferInstanceAs (Algebra (Localization.AtPrime m) (completion m))

/-- The complete local base of the Example's formal object, relative to `Λ_𝔪`, is
`completeBase`. -/
public theorem completeLocalBase_eq (ψ : C →+* completion m)
    (hψ : ψ.comp φ = algebraMap Λ (completion m))
    (hR : B.Contains (Spec (.of (completion m)))) :
    (formalObject m C φ B hS ψ hψ hR).completeLocalBase (Localization.AtPrime m) =
      completeBase m :=
  rfl

/-- The structure morphism of `R = Λ_𝔪^∧` over `Λ_𝔪` is a local homomorphism. -/
public instance isLocalHom_algebraMap_completion :
    IsLocalHom (algebraMap (Localization.AtPrime m) (completion m)) :=
  AdicCompletion.algebraMap_isLocalHom_of_fg
    (maximalIdeal (Localization.AtPrime m)).fg_of_isNoetherianRing

/-- The structure morphism `Algebra.ofId` of `R = Λ_𝔪^∧` over `Λ_𝔪` is a local homomorphism. -/
public instance isLocalHom_ofId_completion :
    IsLocalHom (Algebra.ofId (Localization.AtPrime m) (completion m)) :=
  ⟨fun a ha => (isLocalHom_algebraMap_completion m).map_nonunit a ha⟩

/-- **The residue field of `Λ_𝔪` is that of `R = Λ_𝔪^∧`.** -/
public def residueFieldEquivCompletion :
    ResidueField (Localization.AtPrime m) ≃ₐ[Localization.AtPrime m]
      ResidueField (completion m) :=
  AlgEquiv.ofBijective
    (ResidueField.mapAlgHom
      (Algebra.ofId (Localization.AtPrime m) (completion m)))
    (AdicCompletion.residueField_map_bijective (Localization.AtPrime m))

/-- **`R = Λ_𝔪^∧` has the same adic truncations as `Λ_𝔪`.** -/
public theorem hasBaseTruncations_completeBase :
    Deformation.HasBaseTruncations (completeBase m) :=
  fun n => AdicCompletion.bijective_quotientMapOfPow
    (maximalIdeal (Localization.AtPrime m)) n
    (maximalIdeal (Localization.AtPrime m)).fg_of_isNoetherianRing

/-- **Every Artinian local `Λ_𝔪`-algebra carries exactly one point of `R = Λ_𝔪^∧`.** -/
public theorem nonempty_subsingleton_hom_completeBase
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} (Localization.AtPrime m)
      (ResidueField (completion m))) :
    Nonempty (completeBase m ⟶ Deformation.artinianToComplete.obj A) ∧
      Subsingleton (completeBase m ⟶ Deformation.artinianToComplete.obj A) :=
  Deformation.nonempty_subsingleton_hom_of_hasBaseTruncations
    (residueFieldEquivCompletion m) (completeBase m) (hasBaseTruncations_completeBase m) A

end Points

/-! ### Versality of the formal object -/

section Versal

open IsLocalRing

variable [IsNoetherianRing Λ] (ψ : C →+* completion m)
  (hψ : ψ.comp φ = algebraMap Λ (completion m))
  (hR : B.Contains (Spec (.of (completion m))))

/-- **The canonical morphism `Spec(Λ_𝔪) ⟶ S`**, the deformation base of the Example read as a
chart of `S = Spec(Λ)`. -/
public def localChart : Spec (.of (Localization.AtPrime m)) ⟶ Spec (.of Λ) :=
  Spec.map (CommRingCat.ofHom (algebraMap Λ (Localization.AtPrime m)))

/-- The structure morphism of `R = Λ_𝔪^∧` factors through the chart `Spec(Λ_𝔪) ⟶ S`. -/
public theorem base_toS_eq :
    Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime m)
        (formalObject m C φ B hS ψ hψ hR).base.R)) ≫ localChart m =
      (formalObject m C φ B hS ψ hψ hR).base.toS := by
  change Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime m) (completion m))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ (Localization.AtPrime m))) =
    Spec.map (CommRingCat.ofHom (algebraMap Λ (completion m)))
  rw [← Spec.map_comp]
  refine congrArg Spec.map (CommRingCat.hom_ext ?_)
  change (algebraMap (Localization.AtPrime m) (completion m)).comp
      (algebraMap Λ (Localization.AtPrime m)) = algebraMap Λ (completion m)
  exact (IsScalarTower.algebraMap_eq Λ (Localization.AtPrime m) (completion m)).symm

/-- **The projection of the predeformation category of the Example's closed fibre.** -/
public abbrev predefProjection :
    (Deformation.Artin.predeformationCategory (localChart m)
      ((stack m C φ B hS).val.p ⋙ CategoryTheory.Over.post B.inclusion)
      ((formalObject m C φ B hS ψ hψ hR).level 0)
      ((formalObject m C φ B hS ψ hψ hR).basePoint (Localization.AtPrime m)
        (localChart m) (base_toS_eq m C φ B hS ψ hψ hR))).carrier ⥤
      Deformation.ArtinianLocalAlgCat.{u, u, u} (Localization.AtPrime m)
        (ResidueField (formalObject m C φ B hS ψ hψ hR).base.R) :=
  (Deformation.Artin.predeformationCategory (localChart m)
    ((stack m C φ B hS).val.p ⋙ CategoryTheory.Over.post B.inclusion)
    ((formalObject m C φ B hS ψ hψ hR).level 0)
    ((formalObject m C φ B hS ψ hψ hR).basePoint (Localization.AtPrime m)
      (localChart m) (base_toS_eq m C φ B hS ψ hψ hR))).projection

/-- **The predeformation projection in the shape `IsVersal` presents it**: the projection
`(BasedCategory.ofFunctor predefProjection).p`. -/
public abbrev predefBasedProjection :=
  (CategoryTheory.BasedCategory.ofFunctor (predefProjection m C φ B hS ψ hψ hR)).p

/-- **The complete local base of the predeformation formal object.** It is `completeBase` by
`predefBase_eq`. -/
public abbrev predefBase :=
  ((formalObject m C φ B hS ψ hψ hR).predeformationFormalObject (Localization.AtPrime m)
    (localChart m) (base_toS_eq m C φ B hS ψ hψ hR)).base

/-- The base of the predeformation formal object is `completeBase`. -/
public theorem predefBase_eq :
    predefBase m C φ B hS ψ hψ hR = completeBase m :=
  rfl

/-- **Exactly one point of the predeformation base at every Artinian local `Λ_𝔪`-algebra.** -/
public theorem nonempty_subsingleton_hom_predefBase
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} (Localization.AtPrime m)
      (ResidueField (completion m))) :
    Nonempty (predefBase m C φ B hS ψ hψ hR ⟶ Deformation.artinianToComplete.obj A) ∧
      Subsingleton (predefBase m C φ B hS ψ hψ hR ⟶
        Deformation.artinianToComplete.obj A) :=
  nonempty_subsingleton_hom_completeBase m A

end Versal

end Deformation.Artin.GRingCounterexample


