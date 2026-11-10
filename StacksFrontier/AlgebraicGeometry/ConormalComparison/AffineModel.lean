module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Cotangent
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.Defs
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafAffine
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde

/-!
# The conormal module of a closed immersion of affine schemes is `I / I²`

Let `R` be a commutative ring and `I` an ideal of `R`, and let `k : Spec (R ⧸ I) ⟶ Spec R` be
the induced closed immersion. Its ideal sheaf is `I^~`, by the affine content of
[Stacks, Tag 01IN], and this file computes the global sections of the module pullback of that
ideal sheaf along `k`:

`Γ(Spec R, k_* (k^* I(k))) ≅ I.Cotangent`,

as `R`-modules, **together with the formula on generators**: the section obtained from `a ∈ I`
by the unit of the pullback-pushforward adjunction goes to `Ideal.toCotangent a`. Since
`Ideal.toCotangent` is surjective, that formula determines the isomorphism.

This is the affine model of the part (2) assertions of
[Stacks, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3): the conormal module of a
closed immersion of affine schemes is `I / I²`, normalized on generators. The passage from an
arbitrary immersion of schemes and an arbitrary affine open to this model is *not* carried out
here; see the "What is not done" section.

## Main definitions

* `Stacks.Conormal.AffineModel.extendScalarsIsoCotangent`: the module-theoretic heart,
  `(R ⧸ I) ⊗_R I ≅ I.Cotangent` as `R`-modules. This is Mathlib's
  `TensorProduct.quotTensorEquivQuotSMul`, read at the module `I` and at the `R`-module
  structure that `ModuleCat.extendScalars` produces.
* `Stacks.Conormal.AffineModel.idealTildeΓIsoCotangent`: the computation for the sheaf `I^~`
  presented as `AlgebraicGeometry.tilde` of the module `I`.

## Main results

* `Stacks.Conormal.AffineModel.idealTildeΓIsoCotangent_unit_toOpen`: the generator formula
  for `idealTildeΓIsoCotangent`.
* `Stacks.Conormal.AffineModel.exists_idealSheafΓIsoCotangent`: **the affine model**, stated
  for the ideal sheaf itself — `Stacks.ClosedImmersion.idealSheaf` of `k`, in the vocabulary
  of [Stacks, Tag 01R3] — rather than for `I^~`, together with its generator formula.

## Route

Three inputs, all already in the library, and one module-theoretic computation.

* `Stacks.ClosedImmersion.IdealSheafAffine.exists_tilde_iso_kernel_quotUnitHom`: the affine
  content of [Stacks, Tag 01IN]. The ideal sheaf of `k` is `I^~`, compatibly with the two
  inclusions into the structure sheaf. That compatibility is what lets a section of the ideal
  sheaf be named by an element of `I`.
* `AlgebraicGeometry.pullbackTildeIso`: [Stacks, Tag 01I9]. The module pullback along `k` of
  `M^~` is `((R ⧸ I) ⊗_R M)^~`. Its generator formula
  `AlgebraicGeometry.pullbackTildeIso_hom_app_unit_toOpen` is exactly the elementwise
  description needed: it computes the adjunction *unit* on global sections, which is what the
  quotient map of [Stacks, Tag 01R3] is built from.
* `AlgebraicGeometry.pushforwardΓIso` together with
  `AlgebraicGeometry.tilde.toTildeΓNatIso`: the global sections of the pushforward along `k`
  of `N^~` are `N` with its scalars restricted along `R ⟶ R ⧸ I`. Both comparisons are the
  identity on the underlying sets.
* `TensorProduct.quotTensorEquivQuotSMul`: `(R ⧸ I) ⊗_R M ≅ M / I·M`, which at `M = I` is
  `Ideal.Cotangent`, with `TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul` sending `1 ⊗ a`
  to the class of `a`.

Passing from `I^~` to the ideal sheaf is then transport along the isomorphism of the first
input. The section `x` of the ideal sheaf is named by `a ∈ I` through the *inclusion into the
structure sheaf*, as [Stacks, Tag 01R3] names it, and not through that isomorphism; the step
that reconciles the two is the inverse image of `x` under the isomorphism, which is a section
of `I^~` and hence `a` itself, because `AlgebraicGeometry.tilde.toOpen` at `⊤` is invertible
and the inclusions agree.

## Vocabulary

Four identifications hold by `rfl` and are used to state the result in the vocabulary of the
Stacks statements rather than in Mathlib's `AlgebraicGeometry.Scheme.Modules` vocabulary. They are
recorded as the statements of `idealSheaf_eq_kernel_quotUnitHom` and
`toOpen_top_eq_ΓSpecIso_inv` below, and as the two `rfl` coercions inside
`exists_idealSheafΓIsoCotangent`:

Tag 01C2's `idealSheaf` is `Stacks.ClosedImmersion.idealSheaf`, whose
instance at `k` is `CategoryTheory.Limits.kernel` of
`Stacks.ClosedImmersion.IdealSheafAffine.quotUnitHom`.

`RingedSpaceModuleAdjunction.modulePullback` is
`AlgebraicGeometry.Scheme.Modules.pullback`, and likewise for `modulePushforward` and for
`modulePullbackPushforwardAdjunction`.

The two spellings are *not* interchangeable at the elaborator's implicit transparency, both
being plain definitions, so every intermediate statement below is written in the
`AlgebraicGeometry.Scheme.Modules` spelling and only the final one is restated in the Stacks
statements' spelling.

No hypothesis beyond a commutative ring and an ideal is used: nothing is Noetherian, nothing
is finitely generated, and `I` is an arbitrary ideal.

## Universe situation

A single universe `u`, forced by `AlgebraicGeometry.tilde.functor`, which takes a
`ModuleCat.{u} R` for `R : CommRingCat.{u}`.

## Transparency gotchas

Two rewrites in `exists_idealSheafΓIsoCotangent` fail with a spurious "did not find an
occurrence" error, because the motive mentions
`CategoryTheory.SheafOfModules.unit` of `AlgebraicGeometry.Scheme.ringCatSheaf` under a
functor out of `AlgebraicGeometry.Scheme.Modules` and is not type-correct at implicit
transparency. Both are done by `congrArg` and `Eq.trans` instead:
`CategoryTheory.Functor.map_id` at `AlgebraicGeometry.tildeSelf` is supplied as a *term*,
whose type is checked at default transparency, and the final assembly is a `congrArg` chain.

## What is not done

* **No labelled assertion of [Stacks, Tag 01R3] is discharged, and no tag is attached.** Its
  part (2) is about an arbitrary immersion of schemes and an arbitrary affine open of
  the ambient scheme; this file is the model case `Spec (R ⧸ I) ⟶ Spec R` with the affine open
  the whole of `Spec R`. Three further steps separate them, named in the next two items.
* **No locality, and no transport along an isomorphism of schemes, *here*.** There is no
  statement in this file that the conormal sheaf of an immersion restricted to the preimage of
  an affine open is the conormal sheaf of the restricted closed immersion, nor any passage
  from an affine open `V` with `AlgebraicGeometry.IsAffineOpen.isoSpec` and a quotient
  presentation of the fibre to the model `Spec (R ⧸ I) ⟶ Spec R`.

  Both exist downstream: that is
  `Stacks.Conormal.AffineShape.conormalSheafRestrictIsoAffineModel`
  (`StacksFrontier.AlgebraicGeometry.ConormalAffineShape.Shape`), with
  `Stacks.Conormal.AffineShape.conormalRestrictTopSectionsIso` evaluating it at `⊤`, which is
  where this file's `exists_idealSheafΓIsoCotangent` applies.

  What is still missing is narrower than "no locality". That comparison is a five-fold composite of
  isomorphisms, and **not one of
  the five has an elementwise formula**, so a named section cannot be carried across it; and
  the comparison of the two scalar actions, over `Γ((i ⁻¹ᵁ V).toScheme, ⊤)` on one side and
  over `Γ(X, V)` on the other, is recorded as not supplied by
  `conormalRestrictTopSectionsIso`'s own docstring. Moreover,
  `Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictIso` is the comparison for the
  pullback alone and has no characterizing lemma, so it cannot carry the generator formula;
  and `Stacks.IdealSheafRestrict.pullbackIdealSheafIso` restricts the target only, leaving the
  source whole.
* **Nothing about the kernel of the quotient map.** The clause recorded as
  `conormalQuotientMap_kernel` of [Stacks, Tag 01R3] asks for the kernel on an affine open to
  be the square of the ideal. The forward implication is `Ideal.toCotangent_eq_zero` once the
  identification above is available over that open, which it is not.
* **No surjectivity.** The quotient map is not shown to be an epimorphism; that is a separate
  multi-file job recorded in the module docstring of
  `StacksFrontier.AlgebraicGeometry.ConormalComparison.Normalization`.
* **Sections over a general open are untouched.** Everything here is at `⊤`; the pullback has
  no elementwise description over a smaller open.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01IN](https://stacks.math.columbia.edu/tag/01IN)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.ClosedImmersion.IdealSheafAffine
open scoped ChangeOfRings

universe u

namespace Stacks.Conormal.AffineModel

variable (R : CommRingCat.{u}) (I : Ideal R)

/-! ### The module-theoretic heart -/

/-- `(R ⧸ I) ⊗_R I` is `I.Cotangent`, as `R`-modules.

This is Mathlib's `TensorProduct.quotTensorEquivQuotSMul` at the module `I`, where
`I ⧸ I·I` is `Ideal.Cotangent` by definition. The `R`-module structure that
`ModuleCat.extendScalars` puts on the tensor product agrees with the one Mathlib's
equivalence is stated for; that agreement is definitional. -/
def extendScalarsIsoCotangent :
    (ModuleCat.restrictScalars (quotHom I).hom).obj
        ((ModuleCat.extendScalars (quotHom I).hom).obj (ModuleCat.of R I)) ≅
      ModuleCat.of R I.Cotangent :=
  (TensorProduct.quotTensorEquivQuotSMul (ModuleCat.of R I) I).toModuleIso

/-- `extendScalarsIsoCotangent` sends `1 ⊗ a` to the class of `a`. -/
theorem extendScalarsIsoCotangent_one_tmul (a : I) :
    (extendScalarsIsoCotangent R I).hom.hom ((1 : quotRing I) ⊗ₜ[R, (quotHom I).hom] a) =
      I.toCotangent a :=
  TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul (M := ModuleCat.of R I) I a

/-! ### The computation for `I^~` -/

/-- The global sections of the pushforward along `k` of the module pullback along `k` of
`M^~`, compared with the global sections of the pushforward of `((R ⧸ I) ⊗_R M)^~`. This is
`AlgebraicGeometry.pullbackTildeIso` read under `k_*` and global sections, at `M = I`. -/
def pullbackTildeΓComparison :
    (moduleSpecΓFunctor (R := R)).obj
        ((Scheme.Modules.pushforward (Spec.map (quotHom I))).obj
          ((Scheme.Modules.pullback (Spec.map (quotHom I))).obj
            (tilde (ModuleCat.of R I)))) ≅
      (moduleSpecΓFunctor (R := R)).obj
        ((Scheme.Modules.pushforward (Spec.map (quotHom I))).obj
          (tilde ((ModuleCat.extendScalars (quotHom I).hom).obj (ModuleCat.of R I)))) :=
  (Scheme.Modules.pushforward (Spec.map (quotHom I)) ⋙ moduleSpecΓFunctor).mapIso
    ((pullbackTildeIso R (quotRing I) (quotHom I)).app (ModuleCat.of R I))

/-- The global sections over `Spec R` of the pushforward along `k` of `N^~`, for an
`R ⧸ I`-module `N`, are `N` with its scalars restricted along `R ⟶ R ⧸ I`. Both steps are the
identity on underlying sets: `AlgebraicGeometry.pushforwardΓIso` because a pushforward along
`k` does not change the sections over `⊤`, and `AlgebraicGeometry.tilde.toTildeΓNatIso`
because the global sections of `N^~` are `N`. -/
def tildeΓIsoExtendScalars :
    (moduleSpecΓFunctor (R := R)).obj
        ((Scheme.Modules.pushforward (Spec.map (quotHom I))).obj
          (tilde ((ModuleCat.extendScalars (quotHom I).hom).obj (ModuleCat.of R I)))) ≅
      (ModuleCat.restrictScalars (quotHom I).hom).obj
        ((ModuleCat.extendScalars (quotHom I).hom).obj (ModuleCat.of R I)) :=
  (pushforwardΓIso R (quotRing I) (quotHom I)).app _ ≪≫
    (ModuleCat.restrictScalars (quotHom I).hom).mapIso
      (tilde.toTildeΓNatIso.app
        ((ModuleCat.extendScalars (quotHom I).hom).obj (ModuleCat.of R I))).symm

/-- `tildeΓIsoExtendScalars` undoes `AlgebraicGeometry.tilde.toOpen` at `⊤`. -/
theorem tildeΓIsoExtendScalars_toOpen
    (z : (ModuleCat.extendScalars (quotHom I).hom).obj (ModuleCat.of R I)) :
    (tildeΓIsoExtendScalars R I).hom.hom
        (tilde.toOpen ((ModuleCat.extendScalars (quotHom I).hom).obj (ModuleCat.of R I)) ⊤ z) =
      z :=
  (tilde.toTildeΓNatIso.app
    ((ModuleCat.extendScalars (quotHom I).hom).obj (ModuleCat.of R I))).hom_inv_id_apply z

/-- `tildeΓIsoExtendScalars` followed by `extendScalarsIsoCotangent`. -/
def pullbackTildeΓIsoCotangent :
    (moduleSpecΓFunctor (R := R)).obj
        ((Scheme.Modules.pushforward (Spec.map (quotHom I))).obj
          (tilde ((ModuleCat.extendScalars (quotHom I).hom).obj (ModuleCat.of R I)))) ≅
      ModuleCat.of R I.Cotangent :=
  tildeΓIsoExtendScalars R I ≪≫ extendScalarsIsoCotangent R I

/-- `pullbackTildeΓIsoCotangent` sends the global section represented by `1 ⊗ a` to the class
of `a`. -/
theorem pullbackTildeΓIsoCotangent_toOpen (a : I) :
    (pullbackTildeΓIsoCotangent R I).hom.hom
        (tilde.toOpen ((ModuleCat.extendScalars (quotHom I).hom).obj (ModuleCat.of R I)) ⊤
          ((1 : quotRing I) ⊗ₜ[R, (quotHom I).hom] a)) =
      I.toCotangent a :=
  (congrArg (extendScalarsIsoCotangent R I).hom.hom
    (tildeΓIsoExtendScalars_toOpen R I _)).trans (extendScalarsIsoCotangent_one_tmul R I a)

/-- **The computation for `I^~`.** The global sections over `Spec R` of the pushforward along
`k : Spec (R ⧸ I) ⟶ Spec R` of the module pullback along `k` of `I^~` are `I.Cotangent`. -/
def idealTildeΓIsoCotangent :
    (moduleSpecΓFunctor (R := R)).obj
        ((Scheme.Modules.pushforward (Spec.map (quotHom I))).obj
          ((Scheme.Modules.pullback (Spec.map (quotHom I))).obj
            (tilde (ModuleCat.of R I)))) ≅
      ModuleCat.of R I.Cotangent :=
  pullbackTildeΓComparison R I ≪≫ pullbackTildeΓIsoCotangent R I

/-- **The generator formula for `idealTildeΓIsoCotangent`.** The global section of `I^~`
represented by `a ∈ I`, pushed through the unit of the pullback-pushforward adjunction, goes
to the class of `a` in `I.Cotangent`.

This is `AlgebraicGeometry.pullbackTildeIso_hom_app_unit_toOpen` followed by
`pullbackTildeΓIsoCotangent_toOpen`. -/
theorem idealTildeΓIsoCotangent_unit_toOpen (a : I) :
    (idealTildeΓIsoCotangent R I).hom.hom
        (((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (quotHom I))).unit.app
          (tilde (ModuleCat.of R I))).val.app (.op ⊤)
            (tilde.toOpen (ModuleCat.of R I) ⊤ a)) =
      I.toCotangent a :=
  (congrArg (pullbackTildeΓIsoCotangent R I).hom.hom
    (pullbackTildeIso_hom_app_unit_toOpen R (quotRing I) (quotHom I) (ModuleCat.of R I) a)).trans
    (pullbackTildeΓIsoCotangent_toOpen R I a)

/-! ### Passing from `I^~` to the ideal sheaf -/

/-- The ideal sheaf of `k : Spec (R ⧸ I) ⟶ Spec R` in the vocabulary of
[Stacks, Tag 01R3] is the kernel of
`Stacks.ClosedImmersion.IdealSheafAffine.quotUnitHom`. Both sides are the kernel of the same
morphism. -/
theorem idealSheaf_eq_kernel_quotUnitHom :
    Stacks.ClosedImmersion.idealSheaf (Spec.map (quotHom I)).toLRSHom.toShHom =
      kernel (quotUnitHom I) :=
  rfl

/-- `AlgebraicGeometry.tilde.toOpen` at `⊤` on the module `R` is the canonical identification
of `R` with the global sections of its structure sheaf. -/
theorem toOpen_top_eq_ΓSpecIso_inv (x : R) :
    (tilde.toOpen (ModuleCat.of R R) ⊤).hom x = (Scheme.ΓSpecIso R).inv x :=
  rfl

/-- Cancelling an isomorphism of modules against the unit of the pullback-pushforward
adjunction: the unit at the target, followed by the functor applied to the inverse, is the
inverse followed by the unit at the source. This is naturality of the unit, with the two
images of the isomorphism cancelled. -/
theorem unit_app_comp_map_inv {M N : (Spec R).Modules} (e : M ≅ N) :
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (quotHom I))).unit.app N ≫
        (Scheme.Modules.pullback (Spec.map (quotHom I)) ⋙
          Scheme.Modules.pushforward (Spec.map (quotHom I))).map e.inv =
      e.inv ≫ (Scheme.Modules.pullbackPushforwardAdjunction
        (Spec.map (quotHom I))).unit.app M := by
  rw [← (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (quotHom I))).unit.naturality
    e.inv]
  rfl

/-- **The affine model of [Stacks, Tag 01R3], part (2).** For an ideal `I` of a commutative
ring `R` and the induced closed immersion `k : Spec (R ⧸ I) ⟶ Spec R`, the global sections
over `Spec R` of the pushforward along `k` of the module pullback along `k` of the ideal sheaf
of `k` are `I.Cotangent`, and the isomorphism is normalized on generators: a section `x` of
the ideal sheaf whose image in the structure sheaf is `a ∈ I` is sent by the canonical
quotient map to the class of `a`.

The generator formula determines the isomorphism, `Ideal.toCotangent` being surjective
(`Ideal.toCotangent_surjective`) and every section of the ideal sheaf over `⊤` arising from
some `a` (the ideal sheaf is `I^~`, whose global sections are `I`). -/
theorem exists_idealSheafΓIsoCotangent :
    ∃ c : (moduleSpecΓFunctor (R := R)).obj
          ((Scheme.Modules.pushforward (Spec.map (quotHom I))).obj
            ((Scheme.Modules.pullback (Spec.map (quotHom I))).obj
              (Stacks.ClosedImmersion.idealSheaf
                (Spec.map (quotHom I)).toLRSHom.toShHom))) ≅ ModuleCat.of R I.Cotangent,
      ∀ (a : I) (x : (Stacks.ClosedImmersion.idealSheaf
          (Spec.map (quotHom I)).toLRSHom.toShHom).val.obj (.op ⊤)),
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom (Spec.map (quotHom I)).toLRSHom.toShHom))).val.app (.op ⊤) x =
            (Scheme.ΓSpecIso R).inv (a : R) →
          c.hom.hom (((modulePullbackPushforwardAdjunction
              (Spec.map (quotHom I)).toLRSHom.toShHom).unit.app
                (Stacks.ClosedImmersion.idealSheaf
                  (Spec.map (quotHom I)).toLRSHom.toShHom)).val.app (.op ⊤) x) =
            I.toCotangent a := by
  obtain ⟨e, he⟩ := exists_tilde_iso_kernel_quotUnitHom I
  refine ⟨(moduleSpecΓFunctor (R := R)).mapIso
    ((Scheme.Modules.pullback (Spec.map (quotHom I)) ⋙
      Scheme.Modules.pushforward (Spec.map (quotHom I))).mapIso e.symm) ≪≫
      idealTildeΓIsoCotangent R I, ?_⟩
  intro a x hx
  -- The section of `I^~` that `x` comes from.
  obtain ⟨b, hb⟩ := (ConcreteCategory.bijective_of_isIso
    (tilde.toOpen (ModuleCat.of R I) ⊤)).2 ((moduleSpecΓFunctor.map e.inv).hom x)
  have hbx : (moduleSpecΓFunctor.map e.hom).hom
      ((tilde.toOpen (ModuleCat.of R I) ⊤).hom b) = x := by
    rw [hb]
    exact (moduleSpecΓFunctor.mapIso e).inv_hom_id_apply x
  -- Its image in the structure sheaf is `b`, so `b = a`.
  have he₂ := (moduleSpecΓFunctor.map_comp e.hom (kernel.ι (quotUnitHom I))).symm.trans
    ((moduleSpecΓFunctor.congr_map he).trans
      (moduleSpecΓFunctor.map_comp (tilde.map (ModuleCat.ofHom (Submodule.subtype I)))
        tildeSelf.hom))
  have hι : (moduleSpecΓFunctor.map (kernel.ι (quotUnitHom I))).hom
        ((moduleSpecΓFunctor.map e.hom).hom ((tilde.toOpen (ModuleCat.of R I) ⊤).hom b)) =
      (moduleSpecΓFunctor.map tildeSelf.hom).hom
        ((moduleSpecΓFunctor.map (tilde.map (ModuleCat.ofHom (Submodule.subtype I)))).hom
          ((tilde.toOpen (ModuleCat.of R I) ⊤).hom b)) :=
    congr($(he₂).hom ((tilde.toOpen (ModuleCat.of R I) ⊤).hom b))
  have hsub : (moduleSpecΓFunctor.map
        (tilde.map (ModuleCat.ofHom (Submodule.subtype I)))).hom
        ((tilde.toOpen (ModuleCat.of R I) ⊤).hom b) =
      (tilde.toOpen (ModuleCat.of R R) ⊤).hom (b : R) :=
    congr($(tilde.toOpen_map_app (ModuleCat.ofHom (Submodule.subtype I)) ⊤).hom b)
  have htSmap : moduleSpecΓFunctor.map (tildeSelf (R := R)).hom = 𝟙 _ :=
    moduleSpecΓFunctor.map_id (tilde (ModuleCat.of R R))
  have htS : ∀ z, (moduleSpecΓFunctor.map (tildeSelf (R := R)).hom).hom z = z := fun z =>
    congr($(htSmap).hom z)
  have hchain : (moduleSpecΓFunctor.map (tildeSelf (R := R)).hom).hom
        ((tilde.toOpen (ModuleCat.of R R) ⊤).hom (b : R)) =
      (moduleSpecΓFunctor.map (kernel.ι (quotUnitHom I))).hom x :=
    (congrArg (moduleSpecΓFunctor.map (tildeSelf (R := R)).hom).hom hsub.symm).trans
      (hι.symm.trans
        (congrArg (moduleSpecΓFunctor.map (kernel.ι (quotUnitHom I))).hom hbx))
  have hba : b = a :=
    Subtype.ext ((ConcreteCategory.bijective_of_isIso
      (tilde.toOpen (ModuleCat.of R R) ⊤)).1
        (((htS _).symm.trans hchain).trans hx))
  -- The computation, through the model for `I^~`.
  have hkey : moduleSpecΓFunctor.map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (quotHom I))).unit.app
          (kernel (quotUnitHom I))) ≫
        (moduleSpecΓFunctor.mapIso
          ((Scheme.Modules.pullback (Spec.map (quotHom I)) ⋙
            Scheme.Modules.pushforward (Spec.map (quotHom I))).mapIso e.symm) ≪≫
          idealTildeΓIsoCotangent R I).hom =
      moduleSpecΓFunctor.map e.inv ≫ moduleSpecΓFunctor.map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (quotHom I))).unit.app
          (tilde (ModuleCat.of R I))) ≫ (idealTildeΓIsoCotangent R I).hom := by
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [← Category.assoc, ← Functor.map_comp, unit_app_comp_map_inv, Functor.map_comp,
      Category.assoc]
  have hfin : (moduleSpecΓFunctor.map e.inv).hom x =
      (tilde.toOpen (ModuleCat.of R I) ⊤).hom a := by rw [← hb, hba]
  refine Eq.trans (congr($(hkey).hom x)) ?_
  exact Eq.trans (congrArg (fun y => (idealTildeΓIsoCotangent R I).hom.hom
      ((moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction
        (Spec.map (quotHom I))).unit.app (tilde (ModuleCat.of R I)))).hom y)) hfin)
    (idealTildeΓIsoCotangent_unit_toOpen R I a)

end Stacks.Conormal.AffineModel

end
