module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.TwistShiftIdeal
public import StacksCore.Tactic.StacksAttribute

/-!
# Towards `𝒪_X(q+1) ⟶ 𝒪_X(q)` as multiplication by an element of `I`, on sections

The containment of
`StacksFrontier/AlgebraicGeometry/LocalCohomology/BitUniformityIII/TwistShiftIdeal.lean` — the image
of `𝒪_X(t+1) ⟶ 𝒪_X(t)` lies in `I·𝒪_X(t)` at every point of the blowup — is there read in the
degree-zero localization, and the *stalk* bridge carrying it to the morphism is proved there too.
What a section-level argument needs instead is: every section of `𝒪_X(t+1)` is carried by
`Stacks.Blowup.twistShiftMap` to a section which, on a neighbourhood of any given point, is
`b ·` a section of `𝒪_X(t)` for some `b ∈ I`.

**That statement is `Stacks.Blowup.exists_restrict_appTwistShift_eq_smul`**, together with its
ingredients — the fraction identity at a point, the section the factorisation produces, and the
passage from a pointwise identity to an identity of restricted sections — and the four abstract
lemmas about the sheafified tensor product that turn it into the complex condition `amb_comp` of
`Stacks.LocalCohomology.UniformityIII.GeometricInput`.

## Main definitions

* `Stacks.Blowup.appTwistShift`: the image of a section under `Stacks.Blowup.twistShiftMap`, as a
  named function. It is `irreducible`, for the reason recorded below.
* `Stacks.Blowup.shiftFractionSection`: the section `m / (b⁽¹⁾·σ)` of `𝒪_X(t)` which the
  factorisation produces.

## Main results

* `Stacks.SheafOfModules.OnSpace.tensorObjTmul_smul_right`: a scalar moves across a local pure
  tensor.
* `Stacks.SheafOfModules.OnSpace.tensorObjTmul_zero_left`: a pure tensor with a zero factor is
  zero.
* `Stacks.SheafOfModules.OnSpace.tensorObjTmul_eq_zero_of_locally`: **a local pure tensor that
  vanishes near every point of its open vanishes**, the sheaf property of the sheafified tensor
  product.
* `Stacks.SheafOfModules.smul_app_one`: a morphism out of the free sheaf of rank one is
  determined on a section `r` by its value at `1`, since `r • 1 = r`.
* `Stacks.SheafOfModules.OnSpace.tensorObjTmul_app_one_smul_eq_zero`: **a pure tensor whose left
  factor is the image of `1` and whose right factor carries a scalar killed by the same map is
  zero** — the shape in which the two halves of the comparison meet.
* `Stacks.Blowup.exists_forall_appTwistShift_val`: the image of a section is pointwise the
  localization of `divX` applied to the values of some section of the truncation sheaf.
* `Stacks.Blowup.map_reesShift_eq_val_smul`: the fraction identity of
  `Stacks.Blowup.map_reesShift_mk` with the scalar read as a degree-zero fraction of the
  structure sheaf.
* `Stacks.Blowup.eq_smul_of_pointwise`, `Stacks.Blowup.map_eq_smul_of_pointwise`: two sections
  of a twisting sheaf related pointwise by a scalar are related by it, the second with the
  left-hand section restricted to a smaller open.
* `Stacks.Blowup.exists_restrict_appTwistShift_eq_smul`: **the local factorisation**. Near any
  point at which `b⁽¹⁾` is invertible, the image of a section of `𝒪_X(t+1)` under
  `Stacks.Blowup.twistShiftMap` restricts to `b ·` a section of `𝒪_X(t)`.

## Implementation notes

The route is on *sections* rather than on stalks, so no stalk functor and no germ appears here: a
section of the associated sheaf is a dependent function into the degree-zero localizations
satisfying the local-fraction condition, so near any point it is a single fraction `m / σ` — that
is the definition of the condition — and `Stacks.Blowup.map_reesShift_mk` rewrites the image of
that fraction as `b · (m / (b⁽¹⁾·σ))`. The second fraction *is* a section of `𝒪_X(t)` over the
intersection of the given neighbourhood with `D₊(b⁽¹⁾)`, with the same numerator and denominator
at every point, so the local-fraction condition for it is immediate
(`Stacks.Blowup.shiftFractionSection`).

The scalar is taken as a *parameter* constrained only by its values, rather than constructed: the
section of `𝒪_X` a consumer has is the pullback of `b` along the blowup morphism, and what is
known about it is exactly its value at each point
(`Stacks.LocalCohomology.UniformityIII.val_appTop_toSpec`). Two sections of the structure sheaf
with equal values are equal, so nothing is lost.

### What spends the budget

Four ways of exceeding the 200 000-heartbeat budget arise in the declarations above, and each is
worked around here rather than suppressed — raising the limit is not available.

* **the inverse of the comparison isomorphism must never be forced into weak head normal form.**
  `Stacks.Blowup.reesTruncationComparison` is an `asIso`, so `.inv` drags in the whole
  eventual-bijectivity instance; `set s' := (reesTruncationComparison I t).inv.val.app _ s`
  followed by `s'.2` dies at `whnf`. `exists_forall_appTwistShift_val` names it once, as the
  witness of an `∃`, and nothing looks at it again;
* **an equation naming `associatedModuleSheafMap` must not be the body of an `∃`.** A version
  of `exists_forall_appTwistShift_val` going through an intermediate
  `∃ s', appTwistShift … = (associatedModuleSheafMap …).val.app _ s'` dies at `isDefEq` on its own
  anonymous constructor: unifying the two spellings of the induced map forces its implicit
  `Decomposition` and `SetLike.GradedSMul` instances for the truncation to be compared. The
  comparison is affordable against a *hypothesis*, which is why `appTwistShift_val_of_eq` takes
  the equation as one;
* **the image of a section is a named `irreducible` definition**, `appTwistShift`, so that a
  statement mentions `twistShiftMap` inside a `.val.app` no times rather than twice — the wall
  `TwistShiftIdeal.lean`'s notes record for `Stacks.Blowup.stalkShift`;
* **nothing may be destructured by `rcases`, `obtain` or `rintro` while the goal is the
  factorisation statement.** This is where the whole budget of
  `exists_restrict_appTwistShift_eq_smul` goes. With that statement as the goal, the single
  tactic `obtain ⟨s', hs'⟩ := exists_forall_appTwistShift_val I t U s` exhausts the 200 000
  heartbeats at `isDefEq` by itself, and so does any truncation of the proof that begins with
  it; the same destructuring written in term mode,
  `(exists_forall_appTwistShift_val I t U s).elim fun s' hs' => _`, costs nothing measurable.
  `rcases` abstracts the goal into the motive of a `casesOn`, and this goal mentions
  `appTwistShift I t (op U) s`, against which the motive has to be matched. The proof therefore
  takes apart the local-fraction condition — three nested existentials over an
  `IsModuleFraction`, itself three more — entirely through `Exists.elim` and `And` projections,
  and then the declaration checks in a few seconds.

In particular the cost is in the proof and not in elaborating the *statement*: the statement of
`exists_restrict_appTwistShift_eq_smul` costs no measurable time, as the conclusion of a
declaration and not merely as a hypothesis — a file holding it with the proof replaced by a
single cheap tactic checks as fast as an empty one. Neither of the following is a difficulty. `PresheafOfModules.map` has its target
wrapped in `ModuleCat.restrictScalars`, so `map_eq_smul_of_pointwise` does compare an element of
that wrapper with a plain section, and a single `Subtype.ext` discharges it; `M.val.presheaf.map`
is not needed anywhere. The subtype constructor `⟨y.1, hVU y.2⟩` under an existentially bound
proof is not a difficulty either — it appears in both the statement and the proof above.

Every equality of morphisms is transported onto an element by an explicit `congrArg` whose
function carries the type of the morphism, never by `rw`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0GA7](https://stacks.math.columbia.edu/tag/0GA7)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace Polynomial
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf twistGrading associatedModuleSheaf
  ModuleFiber structureSheaf)
open Stacks.GradedModule
open Stacks.SheafOfModules.TensorStalkRingedSpace (sheafifyUnit)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality (associatedModuleSheafMap)
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections (associatedModuleSheafMap_app_apply)
open scoped TensorProduct

universe u v

namespace Stacks.SheafOfModules

/-! ### A morphism out of the free sheaf of rank one -/

/-- **A morphism out of the free sheaf of rank one is multiplication of its value at `1`.** On a
section `r` of the sheaf of rings it is `r` times the value at the section `1`, because
`r • 1 = r` there. -/
theorem smul_app_one {C : Type*} [Category.{v} C] {J : GrothendieckTopology C}
    {R : CategoryTheory.Sheaf J RingCat.{u}} {M : _root_.SheafOfModules.{u} R}
    (φ : _root_.SheafOfModules.unit R ⟶ M) (U : Cᵒᵖ) (r : R.obj.obj U) :
    r • (φ.val.app U).hom (1 : R.obj.obj U) = (φ.val.app U).hom r :=
  ((φ.val.app U).hom.map_smul r (1 : R.obj.obj U)).symm.trans
    (congrArg (φ.val.app U).hom (mul_one r))

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules.OnSpace

attribute [local instance] monoidal

section Tensor

variable (X : AlgebraicGeometry.RingedSpace.{u, u})
  (A B : _root_.SheafOfModules.{u} (structureSheafRing X))

/-- **A scalar moves across a local pure tensor.** -/
theorem tensorObjTmul_smul_right (U : (Opens X.carrier)ᵒᵖ) (r : X.presheaf.obj U)
    (a : A.val.obj U) (b : B.val.obj U) :
    tensorObjTmul X A B U a (r • b) = tensorObjTmul X A B U (r • a) b :=
  congrArg (tensorObjSection X A B U)
    ((TensorProduct.tmul_smul r a b).trans (TensorProduct.smul_tmul' r a b).symm)

/-- **A local pure tensor with a zero factor is zero.** -/
theorem tensorObjTmul_zero_left (U : (Opens X.carrier)ᵒᵖ) (b : B.val.obj U) :
    tensorObjTmul X A B U (0 : A.val.obj U) b = 0 :=
  (congrArg (tensorObjSection X A B U) (TensorProduct.zero_tmul _ b)).trans
    (map_zero ((sheafifyUnit X
      ((PresheafOfModules.tensorObj (O := (X).presheaf) (A.val) (B.val)))).app U).hom)

/-- **A pure tensor whose left factor is the image of `1` and whose right factor carries a
scalar killed by the same map is zero.** This is the shape in which the two halves of the
comparison meet: the scalar moves across the tensor onto the left factor, where it is the image
of itself by `Stacks.SheafOfModules.smul_app_one`.

Stated with `X` abstract on purpose. The scalar is written at the spelling `X.presheaf.obj U`
that the tensor product's sections use, while `Stacks.SheafOfModules.smul_app_one` writes it at
`(structureSheafRing X).obj.obj U`; the two are definitionally equal but not equal at `implicit`
transparency, so a consumer rewriting with both in a concrete goal gets no match. Here the
passage is a single application, where defeq is checked once and there is nothing to unfold. -/
theorem tensorObjTmul_app_one_smul_eq_zero
    {M : _root_.SheafOfModules.{u} (structureSheafRing X)}
    (φ : _root_.SheafOfModules.unit (structureSheafRing X) ⟶ M)
    (U : (Opens X.carrier)ᵒᵖ) (r : X.presheaf.obj U) (c : B.val.obj U)
    (hr : (φ.val.app U).hom r = 0) :
    tensorObjTmul X M B U
        ((φ.val.app U).hom (1 : (structureSheafRing X).obj.obj U)) (r • c) = 0 :=
  (tensorObjTmul_smul_right X M B U r _ c).trans
    ((congrArg (fun z : M.val.obj U => tensorObjTmul X M B U z c)
        ((Stacks.SheafOfModules.smul_app_one φ U r).trans hr)).trans
      (tensorObjTmul_zero_left X M B U c))

/-- **A local pure tensor which vanishes near every point of its open vanishes.** The sections of
the sheafified tensor product form a sheaf, so this is separatedness; it is what makes the
*local* containment of [Stacks, Tag 02OS] part (3) enough to kill a pure tensor. -/
theorem tensorObjTmul_eq_zero_of_locally (U : Opens X.carrier)
    (a : A.val.obj (op U)) (b : B.val.obj (op U))
    (h : ∀ x ∈ U, ∃ (V : Opens X.carrier) (hV : V ≤ U), x ∈ V ∧
      tensorObjTmul X A B (op V) ((A.val.map (homOfLE hV).op).hom a)
        ((B.val.map (homOfLE hV).op).hom b) = 0) :
    tensorObjTmul X A B (op U) a b = 0 := by
  refine TopCat.Presheaf.IsSheaf.section_ext (F := (A ⊗ B).val.presheaf) (A ⊗ B).isSheaf ?_
  intro x hx
  obtain ⟨V, hV, hxV, hzero⟩ := h x hx
  refine ⟨V, hV, hxV, ?_⟩
  refine (tensorSection_restrict X A B (homOfLE hV) a b).trans ?_
  exact hzero.trans (map_zero ((A ⊗ B).val.presheaf.map (homOfLE hV).op).hom).symm

end Tensor

end Stacks.SheafOfModules.OnSpace

namespace Stacks.Blowup

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- **The image of a section of `𝒪_X(t+1)` under `Stacks.Blowup.twistShiftMap`**, as a named
function.

A named definition rather than the composite written out: a goal mentioning `twistShiftMap`
inside a `.val.app` is where the heartbeat budget goes, and the budget is per declaration, so a
statement writing it out twice leaves nothing for its proof. `appTwistShift_eq` is the way
in. -/
def appTwistShift (t : ℤ) (U : (Opens (ProjectiveSpectrum.top (reesGrading I)))ᵒᵖ)
    (s : (twistingSheaf (reesGrading I) (t + 1)).val.obj U) :
    (twistingSheaf (reesGrading I) t).val.obj U :=
  (twistShiftMap I t).val.app U s

/-- The defining equation of `appTwistShift`. -/
theorem appTwistShift_eq (t : ℤ) (U : (Opens (ProjectiveSpectrum.top (reesGrading I)))ᵒᵖ)
    (s : (twistingSheaf (reesGrading I) (t + 1)).val.obj U) :
    appTwistShift I t U s = (twistShiftMap I t).val.app U s := rfl

attribute [irreducible] appTwistShift

/-- The section of `𝒪_X(t)` on the intersection of an open with `D₊(b⁽¹⁾)` given by the single
fraction `m / (b⁽¹⁾·σ)`: the second factor of the local factorisation below. -/
def shiftFractionSection (t : ℤ) {b : A} (hb : b ∈ I) {d : ℕ} (hd : -t ≤ (d : ℤ))
    (m : reesTruncation I t) (hm : m ∈ reesTruncationGrading I t (d : ℤ))
    (σ : reesAlgebra I) (hσ : σ ∈ reesGrading I d)
    (V : Opens (ProjectiveSpectrum.top (reesGrading I)))
    (hV : ∀ y : V, (σ : reesAlgebra I) ∈ y.1.asHomogeneousIdeal.toIdeal.primeCompl)
    (hVb : ∀ y : V,
      (reesDegOne I hb : reesAlgebra I) ∈ y.1.asHomogeneousIdeal.toIdeal.primeCompl) :
    (twistingSheaf (reesGrading I) t).val.obj (op V) :=
  ⟨fun y => LocalizedModule.mk ((m : reesAlgebra I))
      ⟨(reesDegOne I hb : reesAlgebra I) * (σ : reesAlgebra I),
        y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hVb y) (hV y)⟩,
    fun y => ⟨V, y.2, 𝟙 _, 1 + d, (m : reesAlgebra I),
      (reesDegOne I hb : reesAlgebra I) * (σ : reesAlgebra I),
      mem_twistGrading_succ_of_mem_reesTruncationGrading I t hd m hm,
      SetLike.mul_mem_graded (reesDegOne_mem_reesGrading I hb) hσ,
      fun z => z.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hVb z) (hV z),
      fun _ => rfl⟩⟩

/-- `appTwistShift` at a point, for a section of the truncation sheaf representing it: the
localization of `divX` applied to the value there. -/
theorem appTwistShift_val_of_eq (t : ℤ)
    (U : Opens (ProjectiveSpectrum.top (reesGrading I)))
    (s : (twistingSheaf (reesGrading I) (t + 1)).val.obj (op U))
    (s' : (associatedModuleSheaf (reesGrading I) (reesTruncationGrading I t)).val.obj (op U))
    (hs' : appTwistShift I t (op U) s =
      (associatedModuleSheafMap (reesGrading I) (reesTruncationGrading I t)
        (twistGrading (S := reesAlgebra I) (reesGrading I) t) (reesShift I t)
        (reesShift_mem_twistGrading I t)).val.app (op U) s') (y : U) :
    (appTwistShift I t (op U) s).1 y =
      LocalizedModule.map y.1.asHomogeneousIdeal.toIdeal.primeCompl (reesShift I t) (s'.1 y) :=
  (congrArg (fun z : (twistingSheaf (reesGrading I) t).val.obj (op U) => z.1 y) hs').trans
    (associatedModuleSheafMap_app_apply (reesGrading I) (reesTruncationGrading I t)
      (twistGrading (S := reesAlgebra I) (reesGrading I) t) (reesShift I t)
      (reesShift_mem_twistGrading I t) U s' y)

/-- **`appTwistShift` is pointwise the localization of `divX`** applied to the values of some
section of the truncation sheaf. This is the only form in which the comparison isomorphism and
the induced map of associated sheaves are used below.

The comparison isomorphism is inverted here and nowhere else, and the equation naming the
induced map of associated sheaves is never made the body of an `∃`: that version — one further
declaration, holding `∃ s', appTwistShift … = (associatedModuleSheafMap …).val.app _ s'` —
exhausts the budget at `isDefEq` on its own anonymous constructor, because unifying the two
spellings of the induced map forces its implicit `Decomposition` and `SetLike.GradedSMul`
instances for the truncation to be compared. Here that comparison happens against a
*hypothesis* of `appTwistShift_val_of_eq` instead, where there is nothing to unify. -/
theorem exists_forall_appTwistShift_val (t : ℤ)
    (U : Opens (ProjectiveSpectrum.top (reesGrading I)))
    (s : (twistingSheaf (reesGrading I) (t + 1)).val.obj (op U)) :
    ∃ s' : (associatedModuleSheaf (reesGrading I) (reesTruncationGrading I t)).val.obj (op U),
      ∀ y : U, (appTwistShift I t (op U) s).1 y =
        LocalizedModule.map y.1.asHomogeneousIdeal.toIdeal.primeCompl (reesShift I t)
          (s'.1 y) :=
  ⟨(reesTruncationComparison I t).inv.val.app (op U) s,
    fun y => appTwistShift_val_of_eq I t U s _
      ((appTwistShift_eq I t (op U) s).trans (app_twistShiftMap I t (op U) s)) y⟩

/-- **Below the cut the numerator vanishes**, so the image of the fraction is zero — and so is
any scalar multiple of zero. An element-level statement with its own heartbeat budget. -/
theorem map_reesShift_eq_zero (t : ℤ) (y : ProjectiveSpectrum.top (reesGrading I))
    {m : reesTruncation I t} (hm0 : m = 0)
    (σ : y.asHomogeneousIdeal.toIdeal.primeCompl)
    (r : Localization y.asHomogeneousIdeal.toIdeal.primeCompl) :
    LocalizedModule.map y.asHomogeneousIdeal.toIdeal.primeCompl (reesShift I t)
        (LocalizedModule.mk m σ) =
      r • (0 : ModuleFiber (M := reesAlgebra I) (reesGrading I) y) := by
  rw [hm0, LocalizedModule.zero_mk, map_zero, smul_zero]

/-- **The fraction identity with the scalar read as a degree-zero fraction of the structure
sheaf.** This is `Stacks.Blowup.map_reesShift_mk` with `b` replaced by any element of the
structure-sheaf fibre whose value is the constant fraction `b/1`; the passage between the two
scalar actions is `algebraMap_smul`. An element-level statement with its own heartbeat
budget. -/
theorem map_reesShift_eq_val_smul (t : ℤ) {b : A} (hb : b ∈ I)
    (y : ProjectiveSpectrum.top (reesGrading I))
    (hby : (reesDegOne I hb : reesAlgebra I) ∈ y.asHomogeneousIdeal.toIdeal.primeCompl)
    (m : reesTruncation I t) (σ : y.asHomogeneousIdeal.toIdeal.primeCompl)
    (r : HomogeneousLocalization.AtPrime (reesGrading I) y.asHomogeneousIdeal.toIdeal)
    (hr : HomogeneousLocalization.val r =
      algebraMap (reesAlgebra I) (Localization y.asHomogeneousIdeal.toIdeal.primeCompl)
        ((reesConst I b : reesAlgebra I))) :
    LocalizedModule.map y.asHomogeneousIdeal.toIdeal.primeCompl (reesShift I t)
        (LocalizedModule.mk m σ) =
      HomogeneousLocalization.val r •
        LocalizedModule.mk ((m : reesAlgebra I))
          ⟨(reesDegOne I hb : reesAlgebra I) * (σ : reesAlgebra I),
            y.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hby σ.2⟩ := by
  rw [hr, algebraMap_smul]
  exact map_reesShift_mk I t y hb hby m σ

/-- **A section of a twisting sheaf is a scalar multiple of another**, from the same relation
between their values: a section is a dependent function into the degree-zero localizations, and
the scalar action is pointwise. -/
theorem eq_smul_of_pointwise (t : ℤ) (V : Opens (ProjectiveSpectrum.top (reesGrading I)))
    (ρ : (structureSheaf (reesGrading I)).obj.obj (op V))
    (z c : (twistingSheaf (reesGrading I) t).val.obj (op V))
    (h : ∀ y : V, z.1 y = HomogeneousLocalization.val (ρ.1 y) • c.1 y) :
    z = ρ • c :=
  Subtype.ext (funext h)

/-- **A section restricted to a smaller open is a scalar multiple of another**, from the
relation between their values. This is `Stacks.Blowup.eq_smul_of_pointwise` with the left-hand
section restricted: restriction in a twisting sheaf is restriction of a dependent function, and
so is restriction in the structure sheaf, so the hypothesis is literally the two sides compared
at each point of the smaller open.

The restriction of a section is written `(…).val.map i` whose target is wrapped in
`ModuleCat.restrictScalars`, so the equation compares an element of that wrapper with a plain
section. That costs nothing here: the carriers are the same type and the proof is a single
`Subtype.ext`. -/
theorem map_eq_smul_of_pointwise (t : ℤ)
    {U V : Opens (ProjectiveSpectrum.top (reesGrading I))} (hVU : V ≤ U)
    (z : (twistingSheaf (reesGrading I) t).val.obj (op U))
    (ρ : (structureSheaf (reesGrading I)).obj.obj (op U))
    (c : (twistingSheaf (reesGrading I) t).val.obj (op V))
    (h : ∀ y : V, z.1 ⟨y.1, hVU y.2⟩ =
      HomogeneousLocalization.val (ρ.1 ⟨y.1, hVU y.2⟩) • c.1 y) :
    ((twistingSheaf (reesGrading I) t).val.map (homOfLE hVU).op).hom z =
      ((structureSheaf (reesGrading I)).obj.map (homOfLE hVU).op ρ) • c :=
  Subtype.ext (funext h)

/-- **The local factorisation of `Stacks.Blowup.twistShiftMap` on sections.** Near any point of
an open `U` at which the degree-one element `b⁽¹⁾` attached to `b ∈ I` is invertible, the image
of a section of `𝒪_X(t+1)` is `b` times a section of `𝒪_X(t)`: there is a neighbourhood `V ⊆ U`
of the point and a section `c` of `𝒪_X(t)` over `V` with
`(appTwistShift I t s)|_V = ρ|_V · c`, where `ρ` is any section of `𝒪_X` whose value at every
point of `U` is the constant fraction `b/1`.

This is [Stacks, Tag 02OS] part (3) in the form a *section-level* argument uses it, and it is
the last ingredient of the complex condition `amb_comp` of
`Stacks.LocalCohomology.UniformityIII.GeometricInput`: a pure tensor whose right factor is
`ρ|_V · c` moves the scalar onto its left factor, where `ρ|_V` is killed by `𝒪_X ⟶ 𝒪_{Y₁}`.

The scalar is a *parameter* constrained only by its values rather than constructed, because the
section a consumer has is the pullback of `b` along the blowup morphism and what is known about
it is exactly its value at each point
(`Stacks.LocalCohomology.UniformityIII.val_appTop_toSpec`).

No stalk functor and no germ appears. A section of the associated sheaf is a dependent function
into the degree-zero localizations satisfying the local-fraction condition, so near the given
point it is a single fraction `m / σ`, and `Stacks.Blowup.map_reesShift_mk` — through
`Stacks.Blowup.map_reesShift_eq_val_smul` — rewrites the image of that fraction as
`b · (m / (b⁽¹⁾·σ))`, which is the section `Stacks.Blowup.shiftFractionSection`. The
neighbourhood is the one the local-fraction condition supplies, cut down to the standard open
`D₊(b⁽¹⁾)` so that the new denominator is invertible throughout. Below the cut `-t` the
truncation has no elements, so there the numerator vanishes and the factorisation holds with
`c = 0` (`Stacks.Blowup.map_reesShift_eq_zero`). -/
theorem exists_restrict_appTwistShift_eq_smul (t : ℤ)
    (U : Opens (ProjectiveSpectrum.top (reesGrading I)))
    (s : (twistingSheaf (reesGrading I) (t + 1)).val.obj (op U))
    (x : ProjectiveSpectrum.top (reesGrading I)) (hx : x ∈ U)
    {b : A} (hb : b ∈ I)
    (hbx : (reesDegOne I hb : reesAlgebra I) ∈ x.asHomogeneousIdeal.toIdeal.primeCompl)
    (ρ : (structureSheaf (reesGrading I)).obj.obj (op U))
    (hρ : ∀ y : U, HomogeneousLocalization.val (ρ.1 y) =
      algebraMap (reesAlgebra I) (Localization y.1.asHomogeneousIdeal.toIdeal.primeCompl)
        ((reesConst I b : reesAlgebra I))) :
    ∃ (V : Opens (ProjectiveSpectrum.top (reesGrading I))) (hVU : V ≤ U), x ∈ V ∧
      ∃ c : (twistingSheaf (reesGrading I) t).val.obj (op V),
        ((twistingSheaf (reesGrading I) t).val.map (homOfLE hVU).op).hom
            (appTwistShift I t (op U) s) =
          ((structureSheaf (reesGrading I)).obj.map (homOfLE hVU).op ρ) • c := by
  refine (exists_forall_appTwistShift_val I t U s).elim fun s' hs' => ?_
  refine (s'.2 ⟨x, hx⟩).elim fun V h => h.elim fun hxV h => h.elim fun iV h =>
    h.elim fun d h => h.elim fun m h => h.elim fun σ h => h.2.2.elim fun hnz hfrac => ?_
  refine ⟨V ⊓ ProjectiveSpectrum.basicOpen (reesGrading I) (reesDegOne I hb),
    fun y hy => leOfHom iV hy.1,
    ⟨hxV, (ProjectiveSpectrum.mem_basicOpen (reesGrading I) _ x).mpr hbx⟩, ?_⟩
  have hWσ : ∀ y : (V ⊓ ProjectiveSpectrum.basicOpen (reesGrading I) (reesDegOne I hb) :
      Opens (ProjectiveSpectrum.top (reesGrading I))),
      (σ : reesAlgebra I) ∈ y.1.asHomogeneousIdeal.toIdeal.primeCompl :=
    fun y => hnz ⟨y.1, y.2.1⟩
  have hWb : ∀ y : (V ⊓ ProjectiveSpectrum.basicOpen (reesGrading I) (reesDegOne I hb) :
      Opens (ProjectiveSpectrum.top (reesGrading I))),
      (reesDegOne I hb : reesAlgebra I) ∈ y.1.asHomogeneousIdeal.toIdeal.primeCompl :=
    fun y => (ProjectiveSpectrum.mem_basicOpen (reesGrading I) _ y.1).mp y.2.2
  have hkey : ∀ y : V, (appTwistShift I t (op U) s).1 ⟨y.1, leOfHom iV y.2⟩ =
      LocalizedModule.map y.1.asHomogeneousIdeal.toIdeal.primeCompl (reesShift I t)
        (LocalizedModule.mk m ⟨σ, hnz y⟩) :=
    fun y => (hs' _).trans (congrArg _ (hfrac y))
  refine (le_or_gt (-t) (d : ℤ)).elim (fun hd => ?_) (fun hd => ?_)
  · refine ⟨shiftFractionSection I t hb hd m h.1 σ h.2.1 _ hWσ hWb,
      map_eq_smul_of_pointwise I t _ _ ρ _ fun y => ?_⟩
    exact (hkey ⟨y.1, y.2.1⟩).trans (map_reesShift_eq_val_smul I t hb y.1 (hWb y) m
      ⟨σ, hWσ y⟩ (ρ.1 ⟨y.1, leOfHom iV y.2.1⟩) (hρ _))
  · refine ⟨0, map_eq_smul_of_pointwise I t _ _ ρ _ fun y => ?_⟩
    have hm0 : m = 0 := AddSubgroup.mem_bot.mp
      (truncationAboveGrading_eq_bot (reesGrading I)
        (twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1)) (-t) hd ▸ h.1)
    exact (hkey ⟨y.1, y.2.1⟩).trans (map_reesShift_eq_zero I t y.1 hm0 ⟨σ, hWσ y⟩
      (HomogeneousLocalization.val (ρ.1 ⟨y.1, leOfHom iV y.2.1⟩)))

end Stacks.Blowup

end
