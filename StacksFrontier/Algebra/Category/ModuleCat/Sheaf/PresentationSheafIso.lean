module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Module.Presentation.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos
public import StacksCore.Tactic.StacksAttribute

/-!
# Construction (2) of Stacks 01BH: the cokernel of a presentation matrix

Let `(X, 𝒪_X)` be a ringed space, let `α : R → Γ(X, 𝒪_X)` be a ring homomorphism, let `M` be an
`R`-module and let `P` be a presentation of `M` by generators `P.G` and relations `P.R`. Stacks
01BH compares three constructions of the associated sheaf of `𝒪_X`-modules; construction (2) is
the cokernel of the relation matrix `⊕_{P.R} 𝒪_X → ⊕_{P.G} 𝒪_X` whose `j`-th column is
`(α(r_{ij}))_i`. This file builds construction (2) and proves that it agrees with construction
(3), the sheafification of `U ↦ 𝒪_X(U) ⊗_R M`, together with the equation that pins the
comparison down. Construction (3), the comparison of (1) with (3) and the universe-lifting
machinery for sheaves of modules are in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos`.

## Main definitions

* `Stacks.AssociatedSheaf.structureSheafULift`: the structure sheaf of `X`, regarded as a sheaf
  of modules whose sections live in a larger universe. Mathlib's `SheafOfModules.unit` exists
  only at the universe of the sheaf of rings, which is why the universe lift is needed.
* `Stacks.AssociatedSheaf.structureSheafULiftMk`, `globalEval` and `globalEvalHom`: the
  universe-lifted analogue of Mathlib's `SheafOfModules.unitHomEquiv`. A morphism out of
  `structureSheafULift X` is the same thing as a global section of the target, recovered by
  `globalEval`; `structureSheafULift_hom_eq_mk` and `structureSheafULift_hom_ext` are the
  resulting ext principles. The analogue of `SheafOfModules.freeHomEquiv` is `freeSheafULift`
  together with `freeSheafULiftι`, `freeSheafULift_hom_ext` and `Sigma.ι_desc`.
* `Stacks.AssociatedSheaf.structureSection` and `structureSheafULiftScalar`: the restriction of
  a global section of the structure sheaf to an open set, and multiplication by a global section
  on `structureSheafULift X`; `structureSheafULiftScalar_app_apply` is its formula on sections.
* `Stacks.AssociatedSheaf.freeSheafULift`: the coproduct of copies of `structureSheafULift X`
  indexed by a type of an arbitrary universe, i.e. the free sheaf of modules on that type.
* `Stacks.AssociatedSheaf.presentationSheafMap`, `presentationSheaf` and
  `presentationGenerator`: **construction (2)**, namely the relation matrix of `P` read over
  `𝒪_X`, its cokernel, and the morphism from the `i`-th summand into the cokernel.
* `Stacks.AssociatedSheaf.restrictTop`: the restriction of a global section of a presheaf of
  `𝒪_X`-modules to an open set.
* `Stacks.AssociatedSheaf.moduleULift`, `moduleULift2`, `moduleULift2Up` and `moduleULift2Down`:
  the universe lifts of an `R`-module used to move between the module universe of `M` and the
  one in which construction (3) is left adjoint to global sections.
* `Stacks.AssociatedSheaf.presentationToAssociated` and `associatedToPresentation`: the two
  comparison morphisms between constructions (2) and (3).

## Main results

* `Stacks.AssociatedSheaf.map_tensorUnitSection`: the section `1 ⊗ m` of construction (3) is
  compatible with restriction, so it is the restriction of a global section.
* `Stacks.AssociatedSheaf.globalSections_smul`: the `R`-action on global sections of a sheaf of
  `𝒪_X`-modules is multiplication by `α r`.
* `Stacks.AssociatedSheaf.associatedSheafULiftIso_hom_app_tensorUnitSection`: the comparison
  `associatedSheafULiftIso` of `AssociatedSheafIsos` carries the lift of `1 ⊗ m` to `1 ⊗ (lift
  of m)`, which is what makes the universe lift invisible on sections.
* `Stacks.AssociatedSheaf.associatedSheaf_hom_ext`: a morphism out of construction (3) is
  determined by its effect on the sections `1 ⊗ m` on the whole space. This is clause (4) of
  Stacks 01BH transported to an arbitrary module universe.
* `Stacks.AssociatedSheaf.globalEval_relation_comp`: composing the `j`-th relation of the
  presentation matrix with a morphism out of the free sheaf on the generators evaluates to the
  corresponding `α`-twisted linear combination of the images of the generators. This is the one
  computation that both comparison morphisms need.
* `Stacks.AssociatedSheaf.presentationSheafIso` (**Stacks 01BH, (2) = (3)**): construction (2)
  is construction (3), with the sections of the latter lifted to the common universe of the
  module, the generators and the relations; and
  `presentationSheafIso_hom_app_apply`, which pins it down by sending the image of the `i`-th
  generator on an open `U` to the image of `1 ⊗ P.toSolution.π (single i 1)`.

## Implementation notes

The module universe `v` of `M` and the universes `w` and `z` of the generators and the relations
are independent of the common universe `u` of the ringed space and of `R`. Construction (2) has
sections in `max u v w z`, while construction (3) on `M` has sections in `max u v`, and that is
why the statement of `presentationSheafIso` lifts the latter by `max w z`: nothing is narrowed.
Three universes of sections occur in the proof and each is forced. Construction (2) lives at
`max u v w z`. Construction (3) is left adjoint to global sections only at module universes
already containing `u`, because extension of scalars raises the module universe to the ring's
(see the implementation notes of `AssociatedSheafComparison`), so the comparison is made at
`moduleULift2 M`, i.e. `ULift.{u} (ULift.{max w z} M)`, and transported to `M` along
`uliftAssociatedSheafIso` and `associatedSheafULiftIso`.

Morphisms out of the free sheaf are handled through `globalEval` rather than through
`PresheafOfModules.sections`: on the open-cover site the whole space is an initial object of
`(Opens X)ᵒᵖ`, so a compatible family of sections is the same thing as a single global section,
and `restrictTop` recovers the rest of the family. This keeps the ULifted analogue of
`SheafOfModules.freeHomEquiv` to the few lemmas listed above.

The vanishing of the relation matrix on the generators of construction (3) is not computed by
hand: `presentationTensorSolution` is `P.toSolution.postcomp (tensorUnitGlobalMap X α M)`, so it
is a solution of the relations because the image of a solution under a linear map is one. The
corresponding statement for construction (2) is `presentationGeneratorSection_relation`, which
comes from `cokernel.condition`.

**Where the identification `RingedSpace.{u, u}` comes from, and that it is ours rather than
Mathlib's.** Note first that in `RingedSpace.{A, B}` the *first* parameter is the universe of the
structure sheaf's sections and the *second* is the universe of the underlying space, so
`RingedSpace.{u, u}` identifies those two. Here that identification is inherited from
`structureSheafRing`, which is itself stated only for `RingedSpace.{u, u}`,
and it is *not* the Mathlib pullback pin: the comparison proved in this file uses no pullback at
all — the constant closure of `presentationSheafIso` contains neither `SheafOfModules.pullback`
nor `PresheafOfModules.pullback`. That is the difference from the `(1) = (3)` comparison in
`AssociatedSheafIsos`, which does use the pullback and is therefore genuinely pinned by Mathlib's
`PresheafOfModules` pullback-existence instance, stated for two `SmallCategory` sites
`C D : Type u` over `RingCat.{u}` and so identifying the site, ring and module universes.

The identification here is consequently removable, and the two constraints that block removal
have been discharged by direct elaboration. `structureSheafRing` generalizes to
`(X : RingedSpace.{u, t})` with the space universe `t` independent of the ring universe `u` as
soon as it takes `[UnivLE.{t, u}]`, which is what `HasSheafCompose` for
`forget₂ CommRingCat RingCat` needs; and the sheafification instances generalize as soon as the
sections universe is a *single independent* universe variable carrying
`[EssentiallySmall.{s} (Opens X.carrier)]`, rather than a `max` expression — in the `max` form
the universe unifier gets stuck on `max t ?m =?= max t u v`, the same incompleteness recorded
for 03EM. What remains is re-deriving the explicit universe annotations along the chain
`AssociatedSheafComparison → Tag03CU → AssociatedSheafIsos →` this file, and the signature
change to `structureSheafRing`, which is mentioned in 270 files of this tree. None of the statements of Tag 01BH
ask for the separation: each states `RingedSpace.{u, u}` itself.

No backward-compatibility elaboration option, linter exemption or rewrite-by-defeq
tactic is used.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped TensorProduct

universe u t v w z

namespace Stacks.AssociatedSheaf

section FreeSheaf

variable (X : RingedSpace.{u, u})

/-- The structure sheaf of `X`, regarded as a sheaf of modules with sections in a larger
universe. -/
abbrev structureSheafULift :
    SheafOfModules.{max u t} (structureSheafRing X) :=
  SheafOfModules.uliftObj.{_, _, _, _, t}
    (SheafOfModules.unit (structureSheafRing X))

variable {X}

/-- The restriction of a global section of a presheaf of `𝒪_X`-modules to an open set. -/
def restrictTop {T : PresheafOfModules.{z} (structureSheafRing X).obj}
    (x : T.obj (op ⊤)) (U : (Opens X.carrier)ᵒᵖ) : T.obj U :=
  T.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op x

@[simp]
lemma restrictTop_top {T : PresheafOfModules.{z} (structureSheafRing X).obj}
    (x : T.obj (op ⊤)) : restrictTop x (op ⊤) = x := by
  rw [restrictTop, T.congr_map_apply (Subsingleton.elim _ (𝟙 (op (⊤ : Opens X.carrier)))),
    T.map_id]
  rfl

lemma map_restrictTop {T : PresheafOfModules.{z} (structureSheafRing X).obj}
    (x : T.obj (op ⊤)) {U V : (Opens X.carrier)ᵒᵖ} (f : U ⟶ V) :
    T.map f (restrictTop x U) = restrictTop x V := by
  rw [restrictTop, restrictTop, ← T.map_comp_apply]
  exact T.congr_map_apply (Subsingleton.elim _ _) x

/-- Evaluation of a morphism out of the universe-lifted structure sheaf on the unit global
section. -/
def globalEval {T : SheafOfModules.{max u t} (structureSheafRing X)}
    (φ : structureSheafULift.{u, t} X ⟶ T) : T.val.obj (op ⊤) :=
  PresheafOfModules.Hom.app φ.val (op ⊤)
    (ULift.up (1 : (structureSheafRing X).obj.obj (op ⊤)))

/-- The morphism out of the universe-lifted structure sheaf determined by a global section:
on an open `U` it sends `r` to `r` times the restriction of the given section. -/
def structureSheafULiftMk
    {T : SheafOfModules.{max u t} (structureSheafRing X)}
    (x : T.val.obj (op ⊤)) : structureSheafULift.{u, t} X ⟶ T where
  val.app U := ModuleCat.ofHom
    { toFun := fun r ↦
        (show (structureSheafRing X).obj.obj U from r.down) • restrictTop x U
      map_add' := fun a b ↦ add_smul _ _ _
      map_smul' := fun s a ↦ mul_smul _ _ _ }
  val.naturality {U V} f := by
    ext r
    refine Eq.symm (Eq.trans (T.val.map_smul f _ (restrictTop x U)) ?_)
    exact congrArg _ (map_restrictTop x f)

@[simp]
lemma globalEval_structureSheafULiftMk
    {T : SheafOfModules.{max u t} (structureSheafRing X)}
    (x : T.val.obj (op ⊤)) : globalEval (structureSheafULiftMk.{u, t} x) = x := by
  show (1 : (structureSheafRing X).obj.obj (op ⊤)) •
    restrictTop x (op ⊤) = x
  rw [restrictTop_top, one_smul]

lemma structureSheafULiftMk_app_apply
    {T : SheafOfModules.{max u t} (structureSheafRing X)}
    (x : T.val.obj (op ⊤)) (U : (Opens X.carrier)ᵒᵖ)
    (r : (structureSheafULift.{u, t} X).val.obj U) :
    PresheafOfModules.Hom.app (structureSheafULiftMk.{u, t} x).val U r =
      (show (structureSheafRing X).obj.obj U from r.down) •
        restrictTop x U := rfl

/-- On an open `U`, a morphism out of the universe-lifted structure sheaf carries the unit
section to the restriction of its value on the whole space. -/
lemma app_one_eq_restrictTop
    {T : SheafOfModules.{max u t} (structureSheafRing X)}
    (φ : structureSheafULift.{u, t} X ⟶ T) (U : (Opens X.carrier)ᵒᵖ) :
    PresheafOfModules.Hom.app φ.val U
        (ULift.up (1 : (structureSheafRing X).obj.obj U)) =
      restrictTop (globalEval φ) U := by
  have hmap : (structureSheafULift.{u, t} X).val.map
        (homOfLE (show U.unop ≤ ⊤ from le_top)).op
        (ULift.up (1 : (structureSheafRing X).obj.obj (op ⊤))) =
      ULift.up (1 : (structureSheafRing X).obj.obj U) :=
    congrArg ULift.up (PresheafOfModules.unit_map_one _ _)
  have hunit := PresheafOfModules.naturality_apply φ.val
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op
    (ULift.up (1 : (structureSheafRing X).obj.obj (op ⊤)))
  rw [hmap] at hunit
  exact hunit

/-- A morphism out of the universe-lifted structure sheaf is linear over the scalars. -/
private lemma app_up_eq_smul_one
    {T : SheafOfModules.{max u t} (structureSheafRing X)}
    (φ : structureSheafULift.{u, t} X ⟶ T) (U : (Opens X.carrier)ᵒᵖ)
    (r : (structureSheafRing X).obj.obj U) :
    PresheafOfModules.Hom.app φ.val U (ULift.up r) =
      r • PresheafOfModules.Hom.app φ.val U (ULift.up (1 : (structureSheafRing X).obj.obj U)) :=
  (congrArg (PresheafOfModules.Hom.app φ.val U) (congrArg ULift.up (mul_one r)).symm).trans
    ((PresheafOfModules.Hom.app φ.val U).hom.map_smul _ _)

/-- A morphism out of the universe-lifted structure sheaf is determined by its value on the
unit global section. -/
lemma structureSheafULift_hom_eq_mk
    {T : SheafOfModules.{max u t} (structureSheafRing X)}
    (φ : structureSheafULift.{u, t} X ⟶ T) :
    φ = structureSheafULiftMk.{u, t} (globalEval φ) := by
  refine SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun U ↦ ModuleCat.hom_ext
    (LinearMap.ext fun r ↦ ?_))
  exact (app_up_eq_smul_one φ U r.down).trans (congrArg _ (app_one_eq_restrictTop φ U))

lemma structureSheafULift_hom_ext
    {T : SheafOfModules.{max u t} (structureSheafRing X)}
    {φ ψ : structureSheafULift.{u, t} X ⟶ T} (h : globalEval φ = globalEval ψ) : φ = ψ := by
  rw [structureSheafULift_hom_eq_mk φ, structureSheafULift_hom_eq_mk ψ, h]

lemma globalEval_comp
    {T T' : SheafOfModules.{max u t} (structureSheafRing X)}
    (φ : structureSheafULift.{u, t} X ⟶ T) (ψ : T ⟶ T') :
    globalEval (φ ≫ ψ) = PresheafOfModules.Hom.app ψ.val (op ⊤) (globalEval φ) := rfl

lemma globalEval_add
    {T : SheafOfModules.{max u t} (structureSheafRing X)}
    (φ ψ : structureSheafULift.{u, t} X ⟶ T) :
    globalEval (φ + ψ) = globalEval φ + globalEval ψ := rfl

lemma globalEval_zero
    (T : SheafOfModules.{max u t} (structureSheafRing X)) :
    globalEval (0 : structureSheafULift.{u, t} X ⟶ T) = 0 := rfl

variable (X) in
/-- Evaluation on the unit global section, as an additive map. -/
def globalEvalHom (T : SheafOfModules.{max u t} (structureSheafRing X)) :
    (structureSheafULift.{u, t} X ⟶ T) →+ T.val.obj (op ⊤) where
  toFun := globalEval
  map_zero' := globalEval_zero T
  map_add' := globalEval_add

variable (X) in
@[simp]
lemma globalEvalHom_apply
    (T : SheafOfModules.{max u t} (structureSheafRing X))
    (φ : structureSheafULift.{u, t} X ⟶ T) : globalEvalHom X T φ = globalEval φ := rfl

variable (X)

/-- The restriction to an open set of a global section of the structure sheaf. -/
abbrev structureSection (r : X.presheaf.obj (op ⊤)) (U : (Opens X.carrier)ᵒᵖ) :
    X.presheaf.obj U :=
  X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r

/-- Multiplication by a global section of the structure sheaf, on the universe-lifted
structure sheaf: the morphism attached to that global section. -/
def structureSheafULiftScalar (r : X.presheaf.obj (op ⊤)) :
    structureSheafULift.{u, t} X ⟶ structureSheafULift.{u, t} X :=
  structureSheafULiftMk.{u, t}
    (ULift.up (show (structureSheafRing X).obj.obj (op ⊤) from r))

/-- On an open `U`, multiplication by a global section `r` multiplies by the restriction of `r`
to `U`. -/
lemma structureSheafULiftScalar_app_apply (r : X.presheaf.obj (op ⊤))
    (U : (Opens X.carrier)ᵒᵖ) (m : (structureSheafULift.{u, t} X).val.obj U) :
    PresheafOfModules.Hom.app (structureSheafULiftScalar.{u, t} X r).val U m =
      ULift.up (structureSection X r U * (show X.presheaf.obj U from m.down)) :=
  congrArg ULift.up (mul_comm (show X.presheaf.obj U from m.down) (structureSection X r U))

@[simp]
lemma globalEval_structureSheafULiftScalar_comp (r : X.presheaf.obj (op ⊤))
    {T : SheafOfModules.{max u t} (structureSheafRing X)}
    (ψ : structureSheafULift.{u, t} X ⟶ T) :
    globalEval (structureSheafULiftScalar.{u, t} X r ≫ ψ) =
      (show (structureSheafRing X).obj.obj (op ⊤) from r) • globalEval ψ := by
  exact (congrArg (PresheafOfModules.Hom.app ψ.val (op ⊤))
    (globalEval_structureSheafULiftMk _)).trans (app_up_eq_smul_one ψ (op ⊤) r)

/-- The coproduct of copies of the universe-lifted structure sheaf indexed by a type: the free
sheaf of modules on a type of an arbitrary universe. -/
abbrev freeSheafULift (I : Type w) :
    SheafOfModules.{max u t w} (structureSheafRing X) := by
  letI := hasModuleSheafify.{u, max t w} X
  letI := moduleSheafifyWEqualsLocallyBijective.{u, max t w} X
  exact ∐ fun (_ : I) ↦ structureSheafULift.{u, max t w} X

/-- The inclusion of the summand indexed by `i` in the free sheaf of modules. -/
def freeSheafULiftι {I : Type w} (i : I) :
    structureSheafULift.{u, max t w} X ⟶ freeSheafULift.{u, t, w} X I := by
  letI := hasModuleSheafify.{u, max t w} X
  letI := moduleSheafifyWEqualsLocallyBijective.{u, max t w} X
  exact Sigma.ι (fun (_ : I) ↦ structureSheafULift.{u, max t w} X) i

/-- A morphism out of the free sheaf of modules is determined by its restrictions to the
summands. -/
lemma freeSheafULift_hom_ext {I : Type w}
    {T : SheafOfModules.{max u t w} (structureSheafRing X)}
    {φ ψ : freeSheafULift.{u, t, w} X I ⟶ T}
    (h : ∀ i : I, freeSheafULiftι.{u, t, w} X i ≫ φ =
      freeSheafULiftι.{u, t, w} X i ≫ ψ) : φ = ψ := by
  let := hasModuleSheafify.{u, max t w} X
  let := moduleSheafifyWEqualsLocallyBijective.{u, max t w} X
  exact Sigma.hom_ext _ _ h

end FreeSheaf

section Presentation

variable (X : RingedSpace.{u, u}) {R : Type u} [CommRing R] (α : R →+* X.presheaf.obj (op ⊤))

/-- The relation matrix of a module presentation, read over the structure sheaf: the `j`-th
summand goes to `∑ᵢ α(rᵢⱼ) · eᵢ`. -/
def presentationSheafMap {M : ModuleCat.{v} R} (P : Module.Presentation.{w, z} R M) :
    freeSheafULift.{u, max v w z, z} X P.R ⟶ freeSheafULift.{u, max v w z, w} X P.G := by
  letI := hasModuleSheafify.{u, max v w z} X
  letI := moduleSheafifyWEqualsLocallyBijective.{u, max v w z} X
  exact Sigma.desc fun j ↦ (P.relation j).sum fun i r ↦
    structureSheafULiftScalar.{u, max v w z} X (α r) ≫ freeSheafULiftι.{u, max v w z, w} X i

/-- **Stacks 01BH, construction (2).** The cokernel of the relation matrix of a presentation
of `M`, taken over the structure sheaf of `X`. -/
abbrev presentationSheaf {M : ModuleCat.{v} R} (P : Module.Presentation.{w, z} R M) :
    SheafOfModules.{max u v w z} (structureSheafRing X) := by
  letI := hasModuleSheafify.{u, max v w z} X
  letI := moduleSheafifyWEqualsLocallyBijective.{u, max v w z} X
  exact cokernel (presentationSheafMap X α P)

/-- The morphism from the summand indexed by `i` into construction (2). -/
def presentationGenerator {M : ModuleCat.{v} R} (P : Module.Presentation.{w, z} R M) (i : P.G) :
    structureSheafULift.{u, max v w z} X ⟶ presentationSheaf X α P := by
  letI := hasModuleSheafify.{u, max v w z} X
  letI := moduleSheafifyWEqualsLocallyBijective.{u, max v w z} X
  exact freeSheafULiftι.{u, max v w z, w} X i ≫ cokernel.π (presentationSheafMap X α P)

end Presentation

section TensorUnit

variable (X : RingedSpace.{u, u}) {R : Type u} [CommRing R] (α : R →+* X.presheaf.obj (op ⊤))

/-- The section `1 ⊗ m` of construction (3) is compatible with restriction. -/
lemma map_tensorUnitSection (M : ModuleCat.{v} R) {U V : (Opens X.carrier)ᵒᵖ} (f : U ⟶ V)
    (m : M) :
    (associatedSheaf X α M).val.map f (tensorUnitSection X α M U m) =
      tensorUnitSection X α M V m := by
  let := hasModuleSheafify.{u, v} X
  let := moduleSheafifyWEqualsLocallyBijective.{u, v} X
  let : Algebra R (X.presheaf.obj U) := ((globalSectionsMap X α).app U).hom.toAlgebra
  let : Algebra R (X.presheaf.obj V) := ((globalSectionsMap X α).app V).hom.toAlgebra
  have hmap : (associatedPresheaf X α M).map f ((1 : X.presheaf.obj U) ⊗ₜ[R] m) =
      (1 : X.presheaf.obj V) ⊗ₜ[R] m := by
    refine Eq.trans (Stacks.PresheafOfModules.ChangeOfRings.cofMap_tmul (globalSectionsMap X α)
      ((constantModuleFunctor.{u, v} X).obj M) f (1 : X.presheaf.obj U) m) ?_
    rw [map_one]
    rfl
  exact (PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction.{max u v}
      (R := structureSheafRing X)
      (𝟙 (structureSheafRing X).obj)).unit.app
        (associatedPresheaf X α M)) f ((1 : X.presheaf.obj U) ⊗ₜ[R] m)).symm.trans
    (congrArg _ hmap)

lemma restrictTop_tensorUnitSection (M : ModuleCat.{v} R) (U : (Opens X.carrier)ᵒᵖ) (m : M) :
    restrictTop (tensorUnitSection X α M (op ⊤) m) U = tensorUnitSection X α M U m :=
  map_tensorUnitSection X α M _ m

/-- The `R`-action on the global sections of a sheaf of modules, read through `α`. -/
lemma globalSections_smul
    (T : SheafOfModules.{max u v} (structureSheafRing X)) (r : R)
    (y : (globalSectionsFunctor.{u, v} X α).obj T) :
    r • y = (show (structureSheafRing X).obj.obj (op ⊤) from α r) •
      (show T.val.obj (op ⊤) from y) := by
  show (show (structureSheafRing X).obj.obj (op ⊤) from
      ((globalSectionsMap X α).app (op ⊤)).hom r) • (show T.val.obj (op ⊤) from y) = _
  rw [globalSectionsMap_app_top_apply]

/-- **The universe lift of construction (3), on the sections `1 ⊗ m`.** -/
lemma associatedSheafULiftIso_hom_app_tensorUnitSection (M : ModuleCat.{v} R)
    (U : (Opens X.carrier)ᵒᵖ) (m : M) :
    PresheafOfModules.Hom.app (associatedSheafULiftIso.{t, u, v} X α M).hom.val U
        (ULift.up (tensorUnitSection X α M U m)) =
      tensorUnitSection X α (ModuleCat.of R (ULift.{t} M.carrier)) U (ULift.up m) := by
  let := hasModuleSheafify.{u, v} X
  let := moduleSheafifyWEqualsLocallyBijective.{u, v} X
  let := hasModuleSheafify.{u, max v t} X
  let := moduleSheafifyWEqualsLocallyBijective.{u, max v t} X
  let : Algebra R (X.presheaf.obj U) := ((globalSectionsMap X α).app U).hom.toAlgebra
  let tm : Stacks.PresheafOfModules.ChangeOfRings.cofObj (globalSectionsMap X α)
      ((constantModuleFunctor.{u, v} X).obj M) U := (1 : X.presheaf.obj U) ⊗ₜ[R] m
  have h1 := PresheafOfModules.sheafifyULiftHom_unit_apply.{_, _, _, _, t}
    (𝟙 (structureSheafRing X).obj)
    ((associatedPresheafFunctor.{u, v} X α).obj M) U tm
  have h2 : PresheafOfModules.Hom.app
        (asIso (PresheafOfModules.sheafifyULiftHom.{_, _, _, _, t}
          (𝟙 (structureSheafRing X).obj)
          ((associatedPresheafFunctor.{u, v} X α).obj M))).inv.val U
        (ULift.up (tensorUnitSection X α M U m)) =
      PresheafOfModules.Hom.app
        ((PresheafOfModules.sheafificationAdjunction.{max u v t}
          (R := structureSheafRing X)
          (𝟙 (structureSheafRing X).obj)).unit.app
            (PresheafOfModules.uliftObj.{_, _, _, _, t}
              ((associatedPresheafFunctor.{u, v} X α).obj M))) U (ULift.up tm) := by
    exact (congrArg (fun y ↦ PresheafOfModules.Hom.app
        (asIso (PresheafOfModules.sheafifyULiftHom.{_, _, _, _, t}
          (𝟙 (structureSheafRing X).obj)
          ((associatedPresheafFunctor.{u, v} X α).obj M))).inv.val U y) h1.symm).trans
      (sheafIso_inv_app_hom_app.{u, max v t} X _ U _)
  have h3 := PresheafOfModules.unit_naturality_apply
    (α := 𝟙 (structureSheafRing X).obj)
    (uliftAssociatedPresheafULiftIso.{t, u, v} X α M).hom U (ULift.up tm)
  exact ((congrArg (fun y ↦ PresheafOfModules.Hom.app
    ((moduleSheafification.{u, max v t} X).map
      (uliftAssociatedPresheafULiftIso.{t, u, v} X α M).hom).val U y) h2).trans h3)

lemma associatedSheafULiftIso_inv_app_tensorUnitSection' (M : ModuleCat.{v} R)
    (U : (Opens X.carrier)ᵒᵖ) (m : M) :
    PresheafOfModules.Hom.app (associatedSheafULiftIso.{t, u, v} X α M).inv.val U
        (tensorUnitSection X α (ModuleCat.of R (ULift.{t} M.carrier)) U (ULift.up m)) =
      ULift.up (tensorUnitSection X α M U m) := by
  conv_lhs => rw [← associatedSheafULiftIso_hom_app_tensorUnitSection X α M U m]
  exact congrArg (fun φ : SheafOfModules.uliftObj.{_, _, _, _, t} (associatedSheaf X α M) ⟶ _ ↦
      PresheafOfModules.Hom.app φ.val U (ULift.up (tensorUnitSection X α M U m)))
    (associatedSheafULiftIso.{t, u, v} X α M).hom_inv_id

/-- A morphism out of construction (3) is determined by its effect on the sections `1 ⊗ m` on
the whole space. This is the universal property of construction (3), i.e. clause (4) of Stacks
01BH, transported to an arbitrary module universe along `uliftAssociatedSheafIso`. -/
lemma associatedSheaf_hom_ext (M : ModuleCat.{v} R)
    {T : SheafOfModules.{max u v} (structureSheafRing X)}
    {φ ψ : associatedSheaf X α M ⟶ T}
    (h : ∀ m : M, PresheafOfModules.Hom.app φ.val (op ⊤) (tensorUnitSection X α M (op ⊤) m) =
      PresheafOfModules.Hom.app ψ.val (op ⊤) (tensorUnitSection X α M (op ⊤) m)) :
    φ = ψ := by
  have key : ∀ (χ : associatedSheaf X α M ⟶ T) (y : (ModuleCat.uliftFunctor.{u} R).obj M),
      ModuleCat.Hom.hom ((associatedSheafAdjunction.{u, v} X α).homEquiv _ T
          (((uliftAssociatedSheafIso.{u, v} X α).app M).hom ≫ χ)) y =
        PresheafOfModules.Hom.app χ.val (op ⊤) (tensorUnitSection X α M (op ⊤) y.down) := by
    intro χ y
    rw [Adjunction.homEquiv_unit]
    show PresheafOfModules.Hom.app
        (((uliftAssociatedSheafIso.{u, v} X α).app M).hom ≫ χ).val (op ⊤)
      (ModuleCat.Hom.hom ((associatedSheafAdjunction.{u, v} X α).unit.app
        ((ModuleCat.uliftFunctor.{u} R).obj M)) y) = _
    rw [associatedSheafAdjunction_unit_app_tensorUnitSection]
    exact congrArg _ (uliftAssociatedSheafIso_hom_app_tensorUnitSection X α M (op ⊤) y.down)
  refine (Iso.cancel_iso_hom_left ((uliftAssociatedSheafIso.{u, v} X α).app M) φ ψ).mp ?_
  refine ((associatedSheafAdjunction.{u, v} X α).homEquiv _ T).injective
    (ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_))
  rw [key φ y, key ψ y, h y.down]

end TensorUnit

section Comparison

variable (X : RingedSpace.{u, u}) {R : Type u} [CommRing R] (α : R →+* X.presheaf.obj (op ⊤))
  {M : ModuleCat.{v} R}

/-- Composing the `j`-th relation of the presentation matrix with a morphism out of the free
sheaf on the generators evaluates to the corresponding linear combination of the images of the
generators. -/
lemma globalEval_relation_comp (P : Module.Presentation.{w, z} R M)
    {T : SheafOfModules.{max u v w z} (structureSheafRing X)}
    (ψ : freeSheafULift.{u, max v w z, w} X P.G ⟶ T) (j : P.R) :
    globalEval (freeSheafULiftι.{u, max v w z, z} X j ≫ presentationSheafMap X α P ≫ ψ) =
      (P.relation j).sum fun i r ↦
        (show (structureSheafRing X).obj.obj (op ⊤) from α r) •
          globalEval (freeSheafULiftι.{u, max v w z, w} X i ≫ ψ) := by
  let := hasModuleSheafify.{u, max v w z} X
  let := moduleSheafifyWEqualsLocallyBijective.{u, max v w z} X
  have h0 : freeSheafULiftι.{u, max v w z, z} X j ≫ presentationSheafMap X α P =
      (P.relation j).sum fun i r ↦ structureSheafULiftScalar.{u, max v w z} X (α r) ≫
        freeSheafULiftι.{u, max v w z, w} X i :=
    Sigma.ι_desc _ j
  rw [← Category.assoc, h0]
  simp only [Finsupp.sum]
  rw [Preadditive.sum_comp]
  simp only [Category.assoc]
  refine Eq.trans (map_sum (globalEvalHom X T) _ _) ?_
  simp only [globalEvalHom_apply]
  exact Finset.sum_congr rfl fun i _ ↦ globalEval_structureSheafULiftScalar_comp X _ _

/-- The universe lift of an `R`-module. -/
abbrev moduleULift (N : ModuleCat.{v} R) : ModuleCat.{max v t} R :=
  ModuleCat.of R (ULift.{t} N.carrier)

/-- The universe lift of an `R`-module, lifted once more so that the result contains the
universe of `R`. This is where construction (3) is left adjoint to global sections. -/
abbrev moduleULift2 (N : ModuleCat.{v} R) : ModuleCat.{max u v t} R :=
  (ModuleCat.uliftFunctor.{u} R).obj (moduleULift.{u, t, v} N)

/-- The `R`-linear lift of a module into its doubly lifted copy. -/
def moduleULift2Up (N : ModuleCat.{v} R) : N →ₗ[R] moduleULift2.{u, t, v} N :=
  ULift.moduleEquiv.symm.toLinearMap.comp ULift.moduleEquiv.symm.toLinearMap

/-- The `R`-linear projection of the doubly lifted copy of a module back onto it. -/
def moduleULift2Down (N : ModuleCat.{v} R) : moduleULift2.{u, t, v} N →ₗ[R] N :=
  ULift.moduleEquiv.toLinearMap.comp ULift.moduleEquiv.toLinearMap

@[simp]
lemma moduleULift2Down_up (N : ModuleCat.{v} R) (x : N) :
    moduleULift2Down.{u, t, v} N (moduleULift2Up.{u, t, v} N x) = x := rfl

@[simp]
lemma moduleULift2Up_down (N : ModuleCat.{v} R) (y : moduleULift2.{u, t, v} N) :
    moduleULift2Up.{u, t, v} N (moduleULift2Down.{u, t, v} N y) = y := rfl

/-- `m ↦ 1 ⊗ m`, as an `R`-linear map from a module into the global sections of construction
(3) on its doubly lifted copy. -/
def tensorUnitGlobalMap (N : ModuleCat.{v} R) :
    N →ₗ[R] (globalSectionsFunctor.{u, max v t} X α).obj
      ((associatedSheafFunctor.{u, max u v t} X α).obj (moduleULift2.{u, t, v} N)) :=
  (ModuleCat.Hom.hom ((associatedSheafAdjunction.{u, max v t} X α).unit.app
    (moduleULift2.{u, t, v} N))).comp (moduleULift2Up.{u, t, v} N)

/-- The solution of the presentation's relations in construction (3) given by `m ↦ 1 ⊗ m`. -/
abbrev presentationTensorSolution (P : Module.Presentation.{w, z} R M) :
    P.toRelations.Solution ((globalSectionsFunctor.{u, max v w z} X α).obj
      ((associatedSheafFunctor.{u, max u v w z} X α).obj
        (moduleULift2.{u, max w z, v} M))) :=
  P.toSolution.postcomp (tensorUnitGlobalMap.{u, max w z, v} X α M)

/-- The global section `1 ⊗ (generator i)` of construction (3). -/
def presentationTensorSection (P : Module.Presentation.{w, z} R M) (i : P.G) :
    ((associatedSheafFunctor.{u, max u v w z} X α).obj
      (moduleULift2.{u, max w z, v} M)).val.obj (op ⊤) :=
  (presentationTensorSolution X α P).var i

/-- The morphism from the free sheaf on the generators to construction (3) that sends the `i`-th
basis section to `1 ⊗ (generator i)`. -/
def presentationFreeMap (P : Module.Presentation.{w, z} R M) :
    freeSheafULift.{u, max v w z, w} X P.G ⟶
      (associatedSheafFunctor.{u, max u v w z} X α).obj (moduleULift2.{u, max w z, v} M) := by
  letI := hasModuleSheafify.{u, max v w z} X
  letI := moduleSheafifyWEqualsLocallyBijective.{u, max v w z} X
  exact Sigma.desc fun i ↦ structureSheafULiftMk.{u, max v w z}
    (presentationTensorSection X α P i)

@[simp]
lemma globalEval_presentationFreeMap (P : Module.Presentation.{w, z} R M) (i : P.G) :
    globalEval (freeSheafULiftι.{u, max v w z, w} X i ≫ presentationFreeMap X α P) =
      presentationTensorSection X α P i := by
  let := hasModuleSheafify.{u, max v w z} X
  let := moduleSheafifyWEqualsLocallyBijective.{u, max v w z} X
  have h : freeSheafULiftι.{u, max v w z, w} X i ≫ presentationFreeMap X α P =
      structureSheafULiftMk.{u, max v w z} (presentationTensorSection X α P i) :=
    Sigma.ι_desc _ i
  rw [h, globalEval_structureSheafULiftMk]

lemma presentationSheafMap_comp_presentationFreeMap (P : Module.Presentation.{w, z} R M) :
    presentationSheafMap X α P ≫ presentationFreeMap X α P = 0 := by
  refine freeSheafULift_hom_ext X fun j ↦ ?_
  rw [Limits.comp_zero, ← Category.assoc, Category.assoc]
  refine structureSheafULift_hom_ext (Eq.trans ?_ (globalEval_zero _).symm)
  have h1 := (presentationTensorSolution X α P).linearCombination_var_relation j
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at h1
  refine Eq.trans (globalEval_relation_comp X α P (presentationFreeMap X α P) j) ?_
  rw [Finsupp.sum]
  refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) h1
  exact (congrArg (fun y ↦ (show (structureSheafRing X).obj.obj (op ⊤) from
      α ((P.relation j) i)) • y) (globalEval_presentationFreeMap X α P i)).trans
    (globalSections_smul.{u, max v w z} X α
      ((associatedSheafFunctor.{u, max u v w z} X α).obj (moduleULift2.{u, max w z, v} M))
      ((P.relation j) i) (presentationTensorSection X α P i)).symm

/-- The images of the generators in construction (2), as global sections. -/
def presentationGeneratorSection (P : Module.Presentation.{w, z} R M) (i : P.G) :
    (globalSectionsFunctor.{u, max v w z} X α).obj (presentationSheaf X α P) :=
  globalEval (presentationGenerator X α P i)

/-- The images of the generators in construction (2) solve the presentation's relations. -/
lemma presentationGeneratorSection_relation (P : Module.Presentation.{w, z} R M) (j : P.R) :
    Finsupp.linearCombination R (presentationGeneratorSection X α P) (P.relation j) = 0 := by
  let := hasModuleSheafify.{u, max v w z} X
  let := moduleSheafifyWEqualsLocallyBijective.{u, max v w z} X
  have h0 : freeSheafULiftι.{u, max v w z, z} X j ≫ presentationSheafMap X α P ≫
      cokernel.π (presentationSheafMap X α P) = 0 := by
    rw [cokernel.condition, Limits.comp_zero]
  have h1 := globalEval_relation_comp X α P (cokernel.π (presentationSheafMap X α P)) j
  rw [h0, globalEval_zero, Finsupp.sum] at h1
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) h1.symm
  exact globalSections_smul.{u, max v w z} X α (presentationSheaf X α P) ((P.relation j) i)
    (presentationGeneratorSection X α P i)

/-- The solution of the presentation's relations given by the generators of construction (2). -/
def presentationCokernelSolution (P : Module.Presentation.{w, z} R M) :
    P.toRelations.Solution ((globalSectionsFunctor.{u, max v w z} X α).obj
      (presentationSheaf X α P)) where
  var := presentationGeneratorSection X α P
  linearCombination_var_relation := presentationGeneratorSection_relation X α P

/-- **Construction (2) maps to construction (3).** -/
def presentationToAssociated (P : Module.Presentation.{w, z} R M) :
    presentationSheaf X α P ⟶
      (associatedSheafFunctor.{u, max u v w z} X α).obj (moduleULift2.{u, max w z, v} M) := by
  letI := hasModuleSheafify.{u, max v w z} X
  letI := moduleSheafifyWEqualsLocallyBijective.{u, max v w z} X
  exact cokernel.desc _ (presentationFreeMap X α P)
    (presentationSheafMap_comp_presentationFreeMap X α P)

/-- The `R`-linear map `M → Γ(X, construction (2))` given by the universal property of the
presentation and the generators of construction (2). -/
def presentationDesc (P : Module.Presentation.{w, z} R M) :
    moduleULift2.{u, max w z, v} M ⟶
      (globalSectionsFunctor.{u, max v w z} X α).obj (presentationSheaf X α P) :=
  ModuleCat.ofHom
    (X := moduleULift2.{u, max w z, v} M)
    (Y := (globalSectionsFunctor.{u, max v w z} X α).obj (presentationSheaf X α P))
    ((P.toIsPresentation.desc (presentationCokernelSolution X α P)).comp
      (moduleULift2Down.{u, max w z, v} M))

/-- **Construction (3) maps to construction (2)**, by the universal property of construction
(3) applied to `presentationDesc`. -/
def associatedToPresentation (P : Module.Presentation.{w, z} R M) :
    (associatedSheafFunctor.{u, max u v w z} X α).obj (moduleULift2.{u, max w z, v} M) ⟶
      presentationSheaf X α P :=
  ((associatedSheafAdjunction.{u, max v w z} X α).homEquiv _ (presentationSheaf X α P)).symm
    (presentationDesc X α P)

lemma associatedToPresentation_apply (P : Module.Presentation.{w, z} R M)
    (y : moduleULift2.{u, max w z, v} M) :
    PresheafOfModules.Hom.app (associatedToPresentation X α P).val (op ⊤)
        (tensorUnitSection X α (moduleULift2.{u, max w z, v} M) (op ⊤) y) =
      ModuleCat.Hom.hom (presentationDesc X α P) y := by
  have h := ((associatedSheafAdjunction.{u, max v w z} X α).homEquiv
      (moduleULift2.{u, max w z, v} M) (presentationSheaf X α P)).apply_symm_apply
    (presentationDesc X α P)
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun φ ↦ ModuleCat.Hom.hom φ y) h

lemma presentationGenerator_comp_presentationToAssociated
    (P : Module.Presentation.{w, z} R M) (i : P.G) :
    presentationGenerator X α P i ≫ presentationToAssociated X α P =
      freeSheafULiftι.{u, max v w z, w} X i ≫ presentationFreeMap X α P := by
  let := hasModuleSheafify.{u, max v w z} X
  let := moduleSheafifyWEqualsLocallyBijective.{u, max v w z} X
  rw [presentationGenerator, Category.assoc, presentationToAssociated, cokernel.π_desc]

/-- Composing the universal property of the presentation with the comparison from construction
(2) to construction (3) gives `m ↦ 1 ⊗ m`. This is the equation that makes the two comparison
morphisms mutually inverse. -/
lemma desc_comp_presentationToAssociated (P : Module.Presentation.{w, z} R M) :
    (ModuleCat.Hom.hom ((globalSectionsFunctor.{u, max v w z} X α).map
          (presentationToAssociated X α P))).comp
        (P.toIsPresentation.desc (presentationCokernelSolution X α P)) =
      tensorUnitGlobalMap.{u, max w z, v} X α M := by
  refine P.toIsPresentation.postcomp_injective
    (Module.Relations.Solution.ext (funext fun i ↦ ?_))
  show ModuleCat.Hom.hom ((globalSectionsFunctor.{u, max v w z} X α).map
      (presentationToAssociated X α P))
    (P.toIsPresentation.desc (presentationCokernelSolution X α P) (P.var i)) =
      tensorUnitGlobalMap.{u, max w z, v} X α M (P.var i)
  rw [Module.Relations.Solution.IsPresentation.desc_var]
  show PresheafOfModules.Hom.app (presentationToAssociated X α P).val (op ⊤)
    (globalEval (presentationGenerator X α P i)) = _
  rw [← globalEval_comp, presentationGenerator_comp_presentationToAssociated,
    globalEval_presentationFreeMap]
  rfl

/-- **Construction (2) is construction (3) applied to the doubly lifted module.** -/
def presentationAssociatedIso (P : Module.Presentation.{w, z} R M) :
    presentationSheaf X α P ≅
      (associatedSheafFunctor.{u, max u v w z} X α).obj (moduleULift2.{u, max w z, v} M) where
  hom := presentationToAssociated X α P
  inv := associatedToPresentation X α P
  hom_inv_id := by
    let := hasModuleSheafify.{u, max v w z} X
    let := moduleSheafifyWEqualsLocallyBijective.{u, max v w z} X
    refine (cancel_epi (cokernel.π (presentationSheafMap X α P))).mp ?_
    rw [Category.comp_id, ← Category.assoc, presentationToAssociated, cokernel.π_desc]
    refine freeSheafULift_hom_ext X fun i ↦ ?_
    refine structureSheafULift_hom_ext ?_
    rw [← Category.assoc, globalEval_comp, globalEval_presentationFreeMap]
    refine Eq.trans (associatedToPresentation_apply X α P
      (moduleULift2Up.{u, max w z, v} M (P.var i))) ?_
    change P.toIsPresentation.desc (presentationCokernelSolution X α P)
      (moduleULift2Down.{u, max w z, v} M
        (moduleULift2Up.{u, max w z, v} M (P.var i))) = _
    rw [moduleULift2Down_up, Module.Relations.Solution.IsPresentation.desc_var]
    rfl
  inv_hom_id := by
    refine associatedSheaf_hom_ext X α (moduleULift2.{u, max w z, v} M) fun y ↦ ?_
    refine Eq.trans (congrArg (fun x ↦ PresheafOfModules.Hom.app
      (presentationToAssociated X α P).val (op ⊤) x)
      (associatedToPresentation_apply X α P y)) ?_
    exact congrArg (fun f : M →ₗ[R] (globalSectionsFunctor.{u, max v w z} X α).obj
        ((associatedSheafFunctor.{u, max u v w z} X α).obj
          (moduleULift2.{u, max w z, v} M)) ↦
        f (moduleULift2Down.{u, max w z, v} M y))
      (desc_comp_presentationToAssociated X α P)

end Comparison

section Statement

variable (X : RingedSpace.{u, u}) {R : Type u} [CommRing R] (α : R →+* X.presheaf.obj (op ⊤))
  (M : ModuleCat.{v} R) (P : Module.Presentation.{w, z} R M)

/-- **Stacks 01BH, (2) = (3).** The cokernel of the relation matrix of a presentation of `M`
over the structure sheaf of `X` is the sheafification of `U ↦ 𝒪_X(U) ⊗_R M`, with the sections
lifted to the common universe of the module, the generators and the relations. -/
@[stacks 01BH "comparison_of_three_constructions"]
def presentationSheafIso :
    presentationSheaf X α P ≅
      SheafOfModules.uliftObj.{_, _, _, _, max w z} (associatedSheaf X α M) :=
  presentationAssociatedIso X α P ≪≫
    (uliftAssociatedSheafIso.{u, max v w z} X α).app (moduleULift.{u, max w z, v} M) ≪≫
    (associatedSheafULiftIso.{max w z, u, v} X α M).symm

lemma globalEval_presentationGenerator_comp_presentationSheafIso (i : P.G) :
    globalEval (presentationGenerator X α P i ≫ (presentationSheafIso X α M P).hom) =
      ULift.up (tensorUnitSection X α M (op ⊤) (P.var i)) := by
  have h1 : globalEval (presentationGenerator X α P i ≫ presentationToAssociated X α P) =
      presentationTensorSection X α P i := by
    rw [presentationGenerator_comp_presentationToAssociated, globalEval_presentationFreeMap]
  have h2 := uliftAssociatedSheafIso_hom_app_tensorUnitSection X α
    (moduleULift.{u, max w z, v} M) (op ⊤) (ULift.up (P.var i))
  have h3 := associatedSheafULiftIso_inv_app_tensorUnitSection' X α M (op ⊤) (P.var i)
  show PresheafOfModules.Hom.app
      (associatedSheafULiftIso.{max w z, u, v} X α M).inv.val (op ⊤)
    (PresheafOfModules.Hom.app ((uliftAssociatedSheafIso.{u, max v w z} X α).hom.app
      (moduleULift.{u, max w z, v} M)).val (op ⊤)
      (globalEval (presentationGenerator X α P i ≫ presentationToAssociated X α P))) = _
  rw [h1]
  exact Eq.trans (congrArg (fun x ↦ PresheafOfModules.Hom.app
    (associatedSheafULiftIso.{max w z, u, v} X α M).inv.val (op ⊤) x) h2) h3

/-- **Stacks 01BH, the comparison of (2) and (3) is pinned down.** On every open it carries the
image of the `i`-th generator to the image of `1 ⊗ (generator i)`. -/
@[stacks 01BH "comparison_of_three_constructions"]
lemma presentationSheafIso_hom_app_apply (i : P.G) (U : Opens X.carrier) :
    PresheafOfModules.Hom.app (presentationSheafIso X α M P).hom.val (op U)
        (PresheafOfModules.Hom.app (presentationGenerator X α P i).val (op U)
          (ULift.up (1 : X.presheaf.obj (op U)))) =
      ULift.up (tensorUnitSection X α M (op U)
        (P.toSolution.π (Finsupp.single i 1))) := by
  rw [Module.Relations.Solution.π_single]
  show PresheafOfModules.Hom.app
      (presentationGenerator X α P i ≫ (presentationSheafIso X α M P).hom).val (op U)
    (ULift.up (1 : (structureSheafRing X).obj.obj (op U))) = _
  rw [app_one_eq_restrictTop, globalEval_presentationGenerator_comp_presentationSheafIso]
  exact congrArg ULift.up (restrictTop_tensorUnitSection X α M (op U) (P.var i))

end Statement

end Stacks.AssociatedSheaf

end
