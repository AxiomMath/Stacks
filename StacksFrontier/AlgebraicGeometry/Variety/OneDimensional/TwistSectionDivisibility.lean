module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafTensor
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.VanishingIdealStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafSections
public import StacksFrontier.AlgebraicGeometry.Divisors.TwistSectionMinimality

/-!
# The divisibility step of [Stacks, Tag 0A27]

Let `Y` be a scheme, `y` a point at which the reduced point `D = y` is an effective Cartier
divisor cutting out the maximal ideal of `𝒪_{Y,y}`, and `p` a natural number. This file proves
that a global section of `𝒪_Y((p+1)y)` whose germ at `y` does **not** generate the stalk is the
image of a global section of `𝒪_Y(p·y)` under the inclusion `𝒪_Y(p·y) ⊂ 𝒪_Y((p+1)y)`.

That is the source's *"otherwise it would define a section of `𝒪_X((n-1)x) ⊂ 𝒪_X(n·x)`"* in the
proof of [Stacks, Tag 0A27], and it is the hypothesis `hlocal` of
`Stacks.Divisors.isAffineOpen_compl_singleton_of_mem_range_of_finrank`, which asks it at every
`p` because the minimal `p` is found by a search.

The proof is local-to-global, in three pieces.

*The local computation.* `𝒪_Y(D) = SheafHom(ℐ_D, 𝒪_Y)` is the dual of the ideal sheaf, with no
sheafification, so a section of it over `U` **is** a morphism `ℐ_D|_U ⟶ 𝒪_Y|_U` and the
inclusion `Stacks.Divisors.invertibleSheafMap` is precomposition with
`Stacks.Divisors.negativeTwistMap`. On an affine open `U` where the ideal of `D` is generated
by a nonzerodivisor `f` — which is the forward half of [Stacks, Tag 01WS],
`Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor` — the ideal
sheaf of `n·D` is free of rank one on a section `eₙ` with underlying function `fⁿ`
(`Stacks.Divisors.bijective_smulSectionMap_resSection`), and the induced morphism carries
`e_{p+1}` to `f · e_p`. So precomposition is injective there, because `f` is a nonzerodivisor,
and a functional `σ` on `ℐ_{(p+1)D}` is in its image exactly when `f` divides `σ(e_{p+1})`.

*The divisibility.* Off the support of `D` the ideal is the unit ideal and the generator may be
taken to be `1`. At `y` the hypothesis `y ∉ X_t` says, through
`Stacks.SheafOfModules.mem_nonvanishingLocus_iff` and the evaluation pairing, that no
neighbourhood carries a section of `ℐ_{(p+1)D}` on which `t` takes the value `1`; so the germ of
`t(e_{p+1})` is not a unit, hence lies in the maximal ideal, which is the stalk of `ℐ_D` there.
A generator of that stalk is the germ of `f`, so `f` divides `t(e_{p+1})` in the local ring and
therefore on a smaller affine neighbourhood.

*The gluing.* The local preimages agree because the inclusion is a monomorphism, so they glue:
the sections lying locally in the range of a monomorphism form a subsheaf,
`Stacks.IdealTorsion.Eta.monoRange`, whose sheaf condition is exactly that statement.

## Main results

* `Stacks.Divisors.dualAppLE`: the component at an open subset `A ≤ U` of a section of
  `𝒪_X(D)` over `U`, with the ambient open and the spelling of the structure sheaf pinned
  down; `Stacks.Divisors.eq_zero_of_dualAppLE` and
  `Stacks.Divisors.eq_of_dualAppLE_self_eq` are its two extensionality principles.
* `Stacks.Divisors.mono_invertibleSheafMap_negativeTwistMap`: **the inclusion
  `𝒪_X(p·D) ⟶ 𝒪_X((p+1)D)` is a monomorphism**, for any effective Cartier divisor `D`.
* `Stacks.Divisors.mem_range_app_of_dvd`: **the local surjectivity** — over an affine open
  with a nonzerodivisor generator `f`, a section of `𝒪_X((p+1)D)` is in the range exactly when
  `f` divides its value on the local basis of `ℐ_{(p+1)D}`.
* `Stacks.Divisors.mem_range_sectionsMap_invertibleSheafMap_of_notMem_nonvanishingLocus`: the
  divisibility step for an effective Cartier divisor supported at one point whose ideal sheaf
  cuts out the maximal ideal there.
* `AlgebraicGeometry.mem_range_invertibleSheafMap_of_notMem_nonvanishingChart`: **the
  minimality step of [Stacks, Tag 0A27]**, in the shape its consumer takes it.

## Implementation notes

**Two spellings of everything, and how they are kept apart.** A section of the structure sheaf
appears both as `Γ(X, U)` and as `(TensorSheafification.structureSheaf X.sheaf.obj _).obj.obj
(op U)`; the slice object `A ⟶ U` of `Opens X / U` appears both as an abstract `V : (Over U)ᵒᵖ`
with `V.unop.left` for its underlying open and as `op (Over.mk (homOfLE hAU))` with `A`. The
two members of each pair are equal by `rfl` but not syntactically, so a `rw` whose pattern
mentions one fails against the other. `Stacks.Divisors.idealRes` and
`Stacks.Divisors.dualAppLE` fix one spelling of each once and for all — the open is `A`, the
coefficients are `Γ(X, A)` — and every lemma below is stated at that spelling, which is what
makes the rewrites fire. The crossings happen only in those definitions' own lemmas, in term
position, where the elaborator's defeq check at default transparency settles them.

**Proof irrelevance does the work of the slice site.** The morphisms of `TopologicalSpace.Opens`
are proofs, so two objects of `Opens X / U` with the same underlying open are definitionally
equal; that is why `Stacks.Divisors.dualAppLE_sections_eval` is a `rfl` and why
`Stacks.Divisors.eq_zero_of_dualAppLE` can quantify over `A ≤ U` instead of over slice objects.

**No `@[stacks]` attribute is attached to anything here.** Tag 0A27 is the
affine-or-H-projective dichotomy for an arbitrary curve, and this file proves one hypothesis of
its inner claim; Tag 01WS is already tagged at
`Stacks.Divisors.isEffectiveCartierDivisor_of_forall_mem_support` and is used, not proved;
Tag 01WX names `𝒪_S(D)`, is tagged in
`StacksFrontier/AlgebraicGeometry/Divisors/InvertibleSheaf.lean`, and says nothing about the
inclusion `𝒪_X(p·D) ⊂ 𝒪_X((p+1)D)`. Withholding is the covering-set rule applied.

## References

* [Stacks Project, Tag 0A27](https://stacks.math.columbia.edu/tag/0A27)
* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.ProjectiveSpaceSections

universe v u

namespace Stacks.SheafOfModules

section Generic

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}}
  {h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪)}
  {L L' : SheafOfModules.{max u v}
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}

/-- **A section of the dual `L^∨` over `U` is determined by its value on a rank-one basis.**
Every section of `L` over an object of the slice site `C/U` is a multiple of the restricted
basis section, so the components of a section of the dual are all computed from its value on
the basis. This is `Stacks.SheafOfModules.DualBasisOne.eq_zero_of_eval_e` in the form of an
extensionality principle, with no subtraction of internal-hom sections involved. -/
theorem eq_of_dualEval_eq {U : C} (b : DualBasisOne 𝒪 h𝒪 L U)
    {σ τ : (dualSheaf 𝒪 h𝒪 L).val.obj (op U)} (h : dualEval σ b.e = dualEval τ b.e) : σ = τ := by
  refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  change dualApp σ V x = dualApp τ V x
  rw [← b.span V x, dualApp_smul, dualApp_smul, dualApp_resSection, dualApp_resSection, h]

/-- **Scaling a section of the dual scales its values.** -/
theorem dualEval_smul {U : C} (r : (TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U))
    (lam : (dualSheaf 𝒪 h𝒪 L).val.obj (op U)) (x : L.val.obj (op U)) :
    dualEval (r • lam) x = r * dualEval lam x :=
  evalSection_smul_left 𝒪 L.val
    (SheafOfModules.unit (TensorSheafification.structureSheaf 𝒪 h𝒪)).val (op U) r lam x

end Generic

section Gluing

variable {T : TopCat.{u}}
  {R : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
  {M N : _root_.SheafOfModules.{u} R}

/-- **A section lying locally in the range of a monomorphism lies in its range.** The sections
of the target which lie locally in the range of a morphism of sheaves of modules form a
subsheaf of the target — `Stacks.IdealTorsion.Eta.monoRange` — whose sheaf condition is
exactly this statement. -/
theorem mem_range_app_of_locally (phi : M ⟶ N) [Mono phi] {W : Opens T}
    (s : N.val.obj (op W))
    (h : ∀ z ∈ W, ∃ (A : Opens T) (hAW : A ≤ W), z ∈ A ∧
      N.val.map (homOfLE hAW).op s ∈ LinearMap.range (phi.val.app (op A)).hom) :
    s ∈ LinearMap.range (phi.val.app (op W)).hom := by
  refine (Stacks.IdealTorsion.Eta.monoRange phi).isSheaf s fun z hz => ?_
  obtain ⟨A, hAW, hzA, hmem⟩ := h z hz
  exact ⟨A, homOfLE hAW, hmem, hzA⟩

/-- **A global section whose value over `⊤` is in the range is in the range on global
sections.** The open `⊤` is terminal, so a single element over `⊤` extends uniquely to a
compatible family. -/
theorem mem_range_sectionsMap_of_mem_range_app_top (phi : M ⟶ N) (t : N.sections)
    (h : t.eval (op ⊤) ∈ LinearMap.range (phi.val.app (op ⊤)).hom) :
    t ∈ Set.range (_root_.SheafOfModules.sectionsMap phi) := by
  obtain ⟨u, hu⟩ := h
  refine ⟨sectionsOfTopOfRingSheaf M u, sections_ext_of_eval_top N ?_⟩
  have h1 : (_root_.SheafOfModules.sectionsMap phi (sectionsOfTopOfRingSheaf M u)).eval (op ⊤)
      = phi.val.app (op ⊤) ((sectionsOfTopOfRingSheaf M u).eval (op ⊤)) := rfl
  rw [h1, sectionsOfTopOfRingSheaf_eval_top]
  exact hu

end Gluing

end Stacks.SheafOfModules

namespace Stacks.Divisors

variable {X : Scheme.{u}}

section Monotone

variable {I J : X.IdealSheafData}

/-- **The monotone inclusion `𝒪_X(J) ⟶ 𝒪_X(I)` is precomposition with `g`, read on
components.** A section of `𝒪_X(J) = SheafHom(ℐ_J, 𝒪_X)` over `U` is a morphism on the slice
site over `U`, and `Stacks.Divisors.invertibleSheafMap` precomposes it with `g`; there is no
sheafification in the way, so the identity is definitional. -/
theorem dualApp_invertibleSheafMap (g : negativeTwist J ⟶ negativeTwist I) {U : X.Opens}
    (lam : (invertibleSheaf I).val.obj (op U)) (V : (Over U)ᵒᵖ)
    (b : (negativeTwist J).val.obj (op V.unop.left)) :
    Stacks.SheafOfModules.dualApp ((invertibleSheafMap g).val.app (op U) lam) V b
      = Stacks.SheafOfModules.dualApp lam V ((g.val.app (op V.unop.left)).hom b) := rfl

/-- **The monotone inclusion on values over the base open.** This is
`Stacks.Divisors.dualApp_invertibleSheafMap` at the terminal object of the slice site. -/
theorem dualEval_invertibleSheafMap (g : negativeTwist J ⟶ negativeTwist I) {U : X.Opens}
    (lam : (invertibleSheaf I).val.obj (op U)) (b : (negativeTwist J).val.obj (op U)) :
    Stacks.SheafOfModules.dualEval ((invertibleSheafMap g).val.app (op U) lam) b
      = Stacks.SheafOfModules.dualEval lam ((g.val.app (op U)).hom b) := rfl

/-- **The induced morphism of ideal sheaves does not change the underlying section of
`𝒪_X`.** Both ideal sheaves sit inside `𝒪_X` and `Stacks.Divisors.negativeTwistMap` lies over
the two inclusions, which is `Stacks.Divisors.negativeTwistMap_idealInclusion`. -/
theorem idealSheafSection_negativeTwistMap (h : I ≤ J) {U : X.Opens}
    (b : (negativeTwist I).val.obj (op U)) :
    idealSheafSection J (((negativeTwistMap h).val.app (op U)).hom b) = idealSheafSection I b :=
  congrArg
    (fun φ : negativeTwist I ⟶ SheafOfModules.unit (structureSheafRing X.toRingedSpace) =>
      (φ.val.app (op U)).hom b)
    (negativeTwistMap_idealInclusion h)

end Monotone

section DualAppLE

variable (I : X.IdealSheafData)

/-- **The restriction of a section of the ideal sheaf to an open subset.** This is
`Stacks.SheafOfModules.resSection` at the object `A ⟶ U` of the slice site over `U`, with the
ambient open `A` and the two spellings of the structure sheaf pinned down in the result type.
Without the pinning the open is spelled `(Over.mk (homOfLE hAU)).left`, which is `A` only
after a projection is unfolded, so nothing downstream matches. -/
noncomputable def idealRes {U A : X.Opens} (hAU : A ≤ U)
    (e : (negativeTwist I).val.obj (op U)) : (negativeTwist I).val.obj (op A) :=
  Stacks.SheafOfModules.resSection (𝒪 := X.sheaf.obj)
    (h𝒪 := (structureSheafRing X.toRingedSpace).property) (op (Over.mk (homOfLE hAU))) e

/-- **Restriction commutes with the inclusion of the ideal sheaf into `𝒪_X`.** -/
theorem idealSheafSection_idealRes {U A : X.Opens} (hAU : A ≤ U)
    (e : (negativeTwist I).val.obj (op U)) :
    idealSheafSection I (idealRes I hAU e)
      = X.presheaf.map (homOfLE hAU).op (idealSheafSection I e) :=
  idealSheafSection_resSection I (op (Over.mk (homOfLE hAU))) e

/-- **The component of a section of `𝒪_X(D)` at an open subset of its domain.** A section of
`𝒪_X(D) = SheafHom(ℐ_D, 𝒪_X)` over `U` is a morphism of presheaves of modules on the slice
site over `U`; its component at the object `A ⟶ U` is a map `ℐ_D(A) ⟶ 𝒪_X(A)`, and this is
that map. Pinning the ambient open `A` and the `Γ(X, -)` spelling of the structure sheaf in
the result type is what makes the equations below available to `rw`. -/
noncomputable def dualAppLE {U : X.Opens} (lam : (invertibleSheaf I).val.obj (op U))
    {A : X.Opens} (hAU : A ≤ U) (x : (negativeTwist I).val.obj (op A)) : Γ(X, A) :=
  Stacks.SheafOfModules.dualApp lam (op (Over.mk (homOfLE hAU))) x

/-- **The components of a section of `𝒪_X(D)` are `𝒪_X`-linear.** -/
theorem dualAppLE_smulSectionMap {U : X.Opens} (lam : (invertibleSheaf I).val.obj (op U))
    {A : X.Opens} (hAU : A ≤ U) (c : Γ(X, A)) (x : (negativeTwist I).val.obj (op A)) :
    dualAppLE I lam hAU (Stacks.SheafOfModules.smulSectionMap (𝒪 := X.sheaf.obj)
        (h𝒪 := (structureSheafRing X.toRingedSpace).property) x c)
      = c * dualAppLE I lam hAU x :=
  Stacks.SheafOfModules.dualApp_smul lam (op (Over.mk (homOfLE hAU))) c x

/-- **The components of a section of `𝒪_X(D)` commute with restriction.** This is the
naturality of `lam` inside the slice site over `U`. -/
theorem dualAppLE_idealRes {U : X.Opens} (lam : (invertibleSheaf I).val.obj (op U))
    {A B : X.Opens} (hAU : A ≤ U) (hBA : B ≤ A) (x : (negativeTwist I).val.obj (op A)) :
    dualAppLE I lam (hBA.trans hAU) (idealRes I hBA x)
      = X.presheaf.map (homOfLE hBA).op (dualAppLE I lam hAU x) :=
  PresheafOfModules.naturality_apply lam
    (Opposite.op (Over.homMk (homOfLE hBA) (Subsingleton.elim _ _) :
      Over.mk (homOfLE (hBA.trans hAU)) ⟶ Over.mk (homOfLE hAU))) x

/-- **A section of `𝒪_X(D)` all of whose components vanish is zero.** -/
theorem eq_zero_of_dualAppLE {U : X.Opens} (lam : (invertibleSheaf I).val.obj (op U))
    (h : ∀ (A : X.Opens) (hAU : A ≤ U) (x : (negativeTwist I).val.obj (op A)),
      dualAppLE I lam hAU x = 0) :
    lam = 0 :=
  Stacks.SheafOfModules.eq_zero_of_dualApp lam fun V x => h V.unop.left V.unop.hom.le x

/-- **The component at the whole domain is the value of the section.** -/
theorem dualAppLE_self {U : X.Opens} (lam : (invertibleSheaf I).val.obj (op U))
    (x : (negativeTwist I).val.obj (op U)) :
    dualAppLE I lam le_rfl x = Stacks.SheafOfModules.dualEval lam x := rfl

/-- **The value of a section of `𝒪_X(D)` is zero in the only possible sense.** -/
theorem dualAppLE_zero {U : X.Opens} {A : X.Opens} (hAU : A ≤ U)
    (x : (negativeTwist I).val.obj (op A)) :
    dualAppLE I (0 : (invertibleSheaf I).val.obj (op U)) hAU x = 0 := rfl

/-- **The value of a global section of `𝒪_X(D)` over a smaller open is its component
there.** The two sides differ only by which slice object the component is read at, and the two
slice objects over `U` with underlying open `A` are definitionally equal because the homs of
`TopologicalSpace.Opens` are proofs. -/
theorem dualAppLE_sections_eval (t : (invertibleSheaf I).sections) {U A : X.Opens}
    (hAU : A ≤ U) (x : (negativeTwist I).val.obj (op A)) :
    dualAppLE I (t.eval (op A)) le_rfl x = dualAppLE I (t.eval (op U)) hAU x := by
  have hres : (invertibleSheaf I).val.map (homOfLE hAU).op (t.eval (op U)) = t.eval (op A) :=
    PresheafOfModules.sections_property t (homOfLE hAU).op
  rw [← hres]
  rfl

/-- The component of `t` at `A` on a restricted section is the restriction of its value at `U`. -/
private theorem dualAppLE_sections_eval_idealRes (t : (invertibleSheaf I).sections) {U A : X.Opens}
    (hAU : A ≤ U) (b : (negativeTwist I).val.obj (op U)) :
    dualAppLE I (t.eval (op A)) le_rfl (idealRes I hAU b)
      = X.presheaf.map (homOfLE hAU).op (dualAppLE I (t.eval (op U)) le_rfl b) :=
  (dualAppLE_sections_eval I t hAU _).trans (dualAppLE_idealRes I (t.eval (op U)) le_rfl hAU b)

/-- Restricting a section of the ideal sheaf with underlying section `f ^ n` restricts `f`. -/
private theorem idealSheafSection_idealRes_of_eq_pow {U A : X.Opens} (hAU : A ≤ U) {f : Γ(X, U)}
    {n : ℕ} {e : (negativeTwist I).val.obj (op U)} (he : idealSheafSection I e = f ^ n) :
    idealSheafSection I (idealRes I hAU e) = X.presheaf.map (homOfLE hAU).op f ^ n := by
  rw [idealSheafSection_idealRes, he, map_pow]

/-- **Scaling a section of `𝒪_X(D)` scales its value.** -/
theorem dualAppLE_self_smulSectionMap {U : X.Opens}
    (lam : (invertibleSheaf I).val.obj (op U)) (r : Γ(X, U))
    (x : (negativeTwist I).val.obj (op U)) :
    dualAppLE I (Stacks.SheafOfModules.smulSectionMap (𝒪 := X.sheaf.obj)
        (h𝒪 := (structureSheafRing X.toRingedSpace).property) lam r) le_rfl x
      = r * dualAppLE I lam le_rfl x :=
  Stacks.SheafOfModules.dualEval_smul r lam x

/-- **The dual coordinate of a rank-one basis takes the value `1` on the basis section.** -/
theorem dualAppLE_lam_e {U : X.Opens}
    (b : Stacks.SheafOfModules.DualBasisOne X.sheaf.obj
      (structureSheafRing X.toRingedSpace).property (negativeTwist I) U) :
    dualAppLE I b.lam le_rfl b.e = 1 :=
  b.eval_self

/-- **A section of `𝒪_X(D)` over `U` is determined by its value on a rank-one basis of the
ideal sheaf.** -/
theorem eq_of_dualAppLE_self_eq {U : X.Opens}
    (b : Stacks.SheafOfModules.DualBasisOne X.sheaf.obj
      (structureSheafRing X.toRingedSpace).property (negativeTwist I) U)
    {sigma tau : (invertibleSheaf I).val.obj (op U)}
    (h : dualAppLE I sigma le_rfl b.e = dualAppLE I tau le_rfl b.e) : sigma = tau :=
  Stacks.SheafOfModules.eq_of_dualEval_eq b h

/-- **The monotone inclusion `𝒪_X(J) ⟶ 𝒪_X(I)` is precomposition with `g`, read on the
components of `Stacks.Divisors.dualAppLE`.** -/
theorem dualAppLE_invertibleSheafMap {J : X.IdealSheafData}
    (g : negativeTwist J ⟶ negativeTwist I) {U : X.Opens}
    (lam : (invertibleSheaf I).val.obj (op U)) {A : X.Opens} (hAU : A ≤ U)
    (b : (negativeTwist J).val.obj (op A)) :
    dualAppLE J ((invertibleSheafMap g).val.app (op U) lam) hAU b
      = dualAppLE I lam hAU ((g.val.app (op A)).hom b) := rfl

end DualAppLE

section LocalBasis

variable (D : X.IdealSheafData)

/-- **The ideal of `n·D` on an affine open where `D` is generated by `f` is generated by
`f ^ n`.** Mathlib's power of an `AlgebraicGeometry.Scheme.IdealSheafData` is the pointwise
power of its ideals, so this is `Ideal.span_singleton_pow`. -/
theorem ideal_pow_eq_span (U : X.affineOpens) {f : Γ(X, (U : X.Opens))}
    (hf : D.ideal U = Ideal.span {f}) (n : ℕ) :
    (D ^ n).ideal U = Ideal.span {f ^ n} := by
  have h : (D ^ n).ideal U = (D.ideal U) ^ n := rfl
  rw [h, hf, Ideal.span_singleton_pow]

/-- **A generator of the ideal on an affine open comes from a section of the ideal sheaf.**
This is the bridge `Stacks.Divisors.mem_ideal_iff_exists_idealSheafSection` at the generator
itself. -/
theorem exists_idealSheafSection_eq (U : X.affineOpens) {f : Γ(X, (U : X.Opens))}
    (hf : D.ideal U = Ideal.span {f}) : ∃ e, idealSheafSection D e = f :=
  (mem_ideal_iff_exists_idealSheafSection D U f).1
    (hf ▸ Ideal.mem_span_singleton_self f)

/-- **The rank-one dual basis of a principal ideal sheaf, at a prescribed basis section.**
This is `Stacks.Divisors.dualBasisOneOfPrincipal` with the basis section supplied rather than
chosen, so that its underlying section of `𝒪_X` is known. -/
noncomputable def dualBasisOneOfSection (U : X.affineOpens) {f : Γ(X, (U : X.Opens))}
    (hf : D.ideal U = Ideal.span {f}) (hfnzd : f ∈ nonZeroDivisors Γ(X, (U : X.Opens)))
    {e : (negativeTwist D).val.obj (op (U : X.Opens))} (he : idealSheafSection D e = f) :
    Stacks.SheafOfModules.DualBasisOne X.sheaf.obj
      (structureSheafRing X.toRingedSpace).property (negativeTwist D) (U : X.Opens) :=
  Stacks.SheafOfModules.DualBasisOne.ofSmulBijective _ e
    (bijective_smulSectionMap_resSection D U hf hfnzd he)

/-- The basis section of `Stacks.Divisors.dualBasisOneOfSection` is the one supplied. -/
@[simp]
theorem dualBasisOneOfSection_e (U : X.affineOpens) {f : Γ(X, (U : X.Opens))}
    (hf : D.ideal U = Ideal.span {f}) (hfnzd : f ∈ nonZeroDivisors Γ(X, (U : X.Opens)))
    {e : (negativeTwist D).val.obj (op (U : X.Opens))} (he : idealSheafSection D e = f) :
    (dualBasisOneOfSection D U hf hfnzd he).e = e := rfl

/-- **The dual coordinate of `Stacks.Divisors.dualBasisOneOfSection` takes the value `1` on
the basis section it was built from.** -/
theorem dualAppLE_lam_dualBasisOneOfSection (U : X.affineOpens) {f : Γ(X, (U : X.Opens))}
    (hf : D.ideal U = Ideal.span {f}) (hfnzd : f ∈ nonZeroDivisors Γ(X, (U : X.Opens)))
    {e : (negativeTwist D).val.obj (op (U : X.Opens))} (he : idealSheafSection D e = f) :
    dualAppLE D (dualBasisOneOfSection D U hf hfnzd he).lam le_rfl e = 1 :=
  (dualBasisOneOfSection D U hf hfnzd he).eval_self

/-- **The induced morphism carries the local basis of `ℐ_{(p+1)D}` to `f` times the local
basis of `ℐ_{p·D}`.** Both sides have `f ^ (p + 1)` for their underlying section of `𝒪_X`, and
the inclusion of the ideal sheaf is injective on sections. -/
theorem negativeTwistMap_eq_smul_of_idealSheafSection {U : X.Opens} {f : Γ(X, U)} {p : ℕ}
    {ep : (negativeTwist (D ^ p)).val.obj (op U)}
    {ep1 : (negativeTwist (D ^ (p + 1))).val.obj (op U)}
    (hep : idealSheafSection (D ^ p) ep = f ^ p)
    (hep1 : idealSheafSection (D ^ (p + 1)) ep1 = f ^ (p + 1)) :
    ((negativeTwistMap (pow_succ_le_pow D p)).val.app (op U)).hom ep1 =
      Stacks.SheafOfModules.smulSectionMap (𝒪 := X.sheaf.obj)
        (h𝒪 := (structureSheafRing X.toRingedSpace).property) ep f := by
  refine idealSheafSection_injective (D ^ p) ?_
  rw [idealSheafSection_negativeTwistMap, idealSheafSection_smulSectionMap, hep, hep1, pow_succ,
    mul_comm]

/-- **Every section of the ideal sheaf over an open subset of the affine open is a multiple
of the restricted generator.** This is the surjectivity half of
`Stacks.Divisors.bijective_smulSectionMap_resSection`, with the open and the spelling of the
coefficient pinned down. -/
theorem exists_smulSectionMap_idealRes_eq (U : X.affineOpens) {f : Γ(X, (U : X.Opens))}
    (hf : D.ideal U = Ideal.span {f}) (hfnzd : f ∈ nonZeroDivisors Γ(X, (U : X.Opens)))
    {e : (negativeTwist D).val.obj (op (U : X.Opens))} (he : idealSheafSection D e = f)
    {A : X.Opens} (hAU : A ≤ (U : X.Opens)) (x : (negativeTwist D).val.obj (op A)) :
    ∃ c : Γ(X, A), Stacks.SheafOfModules.smulSectionMap (𝒪 := X.sheaf.obj)
      (h𝒪 := (structureSheafRing X.toRingedSpace).property) (idealRes D hAU e) c = x :=
  (bijective_smulSectionMap_resSection D U hf hfnzd he (op (Over.mk (homOfLE hAU)))).2 x

end LocalBasis

section LocalInjectivity

variable (D : X.IdealSheafData) (p : ℕ)

/-- **The local injectivity of the inclusion `𝒪_X(p·D) ⟶ 𝒪_X((p+1)D)`.** Over an affine open
`U` on which the ideal of `D` is generated by a nonzerodivisor `f`, the ideal sheaf of `p·D`
is free of rank one on a section `e_p` whose underlying function is `f ^ p`, and the induced
morphism of ideal sheaves carries the corresponding basis of `ℐ_{(p+1)D}` to `f · e_p`. So a
functional killing the image of that morphism kills `f · e_p`, hence kills `e_p` because `f`
is a nonzerodivisor, hence kills every section of `ℐ_{p·D}` over every open subset of `U`.

This is the whole local content; no covering argument appears here. -/
theorem dualAppLE_eq_zero_of_forall_dualAppLE_negativeTwistMap_eq_zero {W : X.Opens}
    (mu : (invertibleSheaf (D ^ p)).val.obj (op W))
    (hmu : ∀ (A : X.Opens) (hAW : A ≤ W) (b : (negativeTwist (D ^ (p + 1))).val.obj (op A)),
      dualAppLE (D ^ p) mu hAW
        (((negativeTwistMap (pow_succ_le_pow D p)).val.app (op A)).hom b) = 0)
    (U : X.affineOpens) {f : Γ(X, (U : X.Opens))} (hf : D.ideal U = Ideal.span {f})
    (hfnzd : f ∈ nonZeroDivisors Γ(X, (U : X.Opens)))
    {A : X.Opens} (hAW : A ≤ W) (hAU : A ≤ (U : X.Opens))
    (x : (negativeTwist (D ^ p)).val.obj (op A)) :
    dualAppLE (D ^ p) mu hAW x = 0 := by
  obtain ⟨ep, hep⟩ := exists_idealSheafSection_eq (D ^ p) U (ideal_pow_eq_span D U hf p)
  obtain ⟨ep1, hep1⟩ :=
    exists_idealSheafSection_eq (D ^ (p + 1)) U (ideal_pow_eq_span D U hf (p + 1))
  have hfA : X.presheaf.map (homOfLE hAU).op f ∈ nonZeroDivisors Γ(X, A) :=
    mem_nonZeroDivisors_res U.2 hfnzd hAU
  have hkey : dualAppLE (D ^ p) mu hAW (idealRes (D ^ p) hAU ep) = 0 := by
    have h0 := hmu A hAW (idealRes (D ^ (p + 1)) hAU ep1)
    rw [negativeTwistMap_eq_smul_of_idealSheafSection D
      (idealSheafSection_idealRes_of_eq_pow _ hAU hep)
      (idealSheafSection_idealRes_of_eq_pow _ hAU hep1),
      dualAppLE_smulSectionMap] at h0
    exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hfA).1 h0
  obtain ⟨c, hc⟩ := exists_smulSectionMap_idealRes_eq (D ^ p) U
    (ideal_pow_eq_span D U hf p) (pow_mem hfnzd p) hep hAU x
  have h2 : dualAppLE (D ^ p) mu hAW x
      = c * dualAppLE (D ^ p) mu hAW (idealRes (D ^ p) hAU ep) := by
    rw [← hc]
    exact dualAppLE_smulSectionMap (D ^ p) mu hAW c _
  rw [h2, hkey, mul_zero]

/-- **The inclusion `𝒪_X(p·D) ⟶ 𝒪_X((p+1)D)` is a monomorphism.** A section of `𝒪_X(p·D)`
killed by the inclusion has all of its components killed, by
`Stacks.Divisors.dualAppLE_eq_zero_of_forall_dualAppLE_negativeTwistMap_eq_zero` on an affine
cover adapted to the divisor, and the value of a component is determined locally because
`𝒪_X` is a sheaf. So the inclusion is injective on sections over every open, which for
sheaves of modules is exactly `Mono`. -/
theorem mono_invertibleSheafMap_negativeTwistMap (hD : IsEffectiveCartierDivisor D) :
    Mono (invertibleSheafMap (negativeTwistMap (pow_succ_le_pow D p))) := by
  classical
  have hinj : ∀ W : X.Opens, Function.Injective
      ((invertibleSheafMap (negativeTwistMap (pow_succ_le_pow D p))).val.app (op W)) := by
    intro W mu nu hmn
    rw [← sub_eq_zero]
    have hzero : (invertibleSheafMap (negativeTwistMap (pow_succ_le_pow D p))).val.app (op W)
        (mu - nu) = 0 := by
      rw [map_sub, hmn, sub_self]
    have hsub : ∀ (A : X.Opens) (hAW : A ≤ W)
        (b : (negativeTwist (D ^ (p + 1))).val.obj (op A)),
        dualAppLE (D ^ p) (mu - nu) hAW
          (((negativeTwistMap (pow_succ_le_pow D p)).val.app (op A)).hom b) = 0 := by
      intro A hAW b
      rw [← dualAppLE_invertibleSheafMap, hzero, dualAppLE_zero]
    refine eq_zero_of_dualAppLE (D ^ p) _ fun A hAW x => ?_
    choose U hU hzU f hfreg hfspan using fun z : A =>
      exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor D hD (z : X)
    refine eq_of_locally_eq (fun z : A => A ⊓ U z) A (fun z => homOfLE inf_le_left)
      (fun w hw => Opens.mem_iSup.2 ⟨⟨w, hw⟩, ⟨hw, hzU ⟨w, hw⟩⟩⟩) _ 0 fun z => ?_
    rw [map_zero, ← dualAppLE_idealRes]
    exact dualAppLE_eq_zero_of_forall_dualAppLE_negativeTwistMap_eq_zero D p (mu - nu) hsub
      ⟨U z, hU z⟩ (hfspan z) (isRegular_iff_mem_nonZeroDivisors.1 (hfreg z)) _ inf_le_right _
  exact (SheafOfModules.forget (structureSheafRing X.toRingedSpace)).mono_of_mono_map
    (PresheafOfModules.mono_of_injective
      (f := (invertibleSheafMap (negativeTwistMap (pow_succ_le_pow D p))).val)
      fun {Wop} => hinj Wop.unop)

end LocalInjectivity

section LocalSurjectivity

variable (D : X.IdealSheafData) (p : ℕ)

/-- **The local surjectivity of the inclusion `𝒪_X(p·D) ⟶ 𝒪_X((p+1)D)`.** Over an affine open
`U` on which the ideal of `D` is generated by a nonzerodivisor `f`, both ideal sheaves are
free of rank one, on sections `e_p` and `e_{p+1}` with underlying functions `f ^ p` and
`f ^ (p+1)`, and the induced morphism of ideal sheaves carries `e_{p+1}` to `f · e_p`. So a
functional `σ` on `ℐ_{(p+1)D}` is the image of a functional on `ℐ_{p·D}` exactly when `f`
divides its value on `e_{p+1}`: the preimage is `(σ(e_{p+1}) / f) · λ_p`.

This is the whole of the source's *"otherwise it would define a section of `𝒪_X((n-1)x)`"*,
in its local form. -/
theorem mem_range_app_of_dvd (U : X.affineOpens) {f : Γ(X, (U : X.Opens))}
    (hf : D.ideal U = Ideal.span {f}) (hfnzd : f ∈ nonZeroDivisors Γ(X, (U : X.Opens)))
    {ep : (negativeTwist (D ^ p)).val.obj (op (U : X.Opens))}
    {ep1 : (negativeTwist (D ^ (p + 1))).val.obj (op (U : X.Opens))}
    (hep : idealSheafSection (D ^ p) ep = f ^ p)
    (hep1 : idealSheafSection (D ^ (p + 1)) ep1 = f ^ (p + 1))
    (sigma : (invertibleSheaf (D ^ (p + 1))).val.obj (op (U : X.Opens)))
    (hdvd : f ∣ dualAppLE (D ^ (p + 1)) sigma le_rfl ep1) :
    sigma ∈ LinearMap.range ((invertibleSheafMap
      (negativeTwistMap (pow_succ_le_pow D p))).val.app (op (U : X.Opens))).hom := by
  obtain ⟨r, hr⟩ := hdvd
  have hkey : ∀ lam : (invertibleSheaf (D ^ p)).val.obj (op (U : X.Opens)),
      dualAppLE (D ^ (p + 1)) ((invertibleSheafMap
          (negativeTwistMap (pow_succ_le_pow D p))).val.app (op (U : X.Opens)) lam) le_rfl ep1
        = f * dualAppLE (D ^ p) lam le_rfl ep := by
    intro lam
    rw [dualAppLE_invertibleSheafMap, negativeTwistMap_eq_smul_of_idealSheafSection D hep hep1,
      dualAppLE_smulSectionMap]
  refine ⟨Stacks.SheafOfModules.smulSectionMap (𝒪 := X.sheaf.obj)
      (h𝒪 := (structureSheafRing X.toRingedSpace).property)
      (dualBasisOneOfSection (D ^ p) U (ideal_pow_eq_span D U hf p) (pow_mem hfnzd p) hep).lam r,
    eq_of_dualAppLE_self_eq (D ^ (p + 1))
      (dualBasisOneOfSection (D ^ (p + 1)) U (ideal_pow_eq_span D U hf (p + 1))
        (pow_mem hfnzd (p + 1)) hep1) (Eq.trans (hkey _) ?_)⟩
  rw [dualAppLE_self_smulSectionMap, dualAppLE_lam_dualBasisOneOfSection, mul_one]
  exact hr.symm

end LocalSurjectivity

section Nonvanishing

variable (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

/-- **The local criterion for the nonvanishing locus of a section of `𝒪_X(D)`.** A point lies
in `X_t` exactly when some neighbourhood carries a section of `ℐ_D` on which `t` takes the
value `1`. This is `Stacks.SheafOfModules.mem_nonvanishingLocus_iff` at the evaluation
pairing, with the pairing computed by
`Stacks.SheafOfModules.tensorPairing_evaluationIso`; it is the statement
`Stacks.Divisors.mem_nonvanishingLocus_canonicalSections_iff` makes for the canonical section,
for an arbitrary section instead. -/
theorem mem_nonvanishingLocus_iff_exists_dualAppLE (t : (invertibleSheaf D).sections) (x : X) :
    x ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) (invertibleSheaf D) t ↔
      ∃ (W : X.Opens) (_ : x ∈ W) (b : (negativeTwist D).val.obj (op W)),
        dualAppLE D (t.eval (op W)) le_rfl b = 1 := by
  have := stacksIsInvertible_negativeTwist D
  have h := Stacks.SheafOfModules.mem_nonvanishingLocus_iff
    (X := X.toRingedSpace) (L := invertibleSheaf D) (N := negativeTwist D)
    (Stacks.SheafOfModules.Scheme.evaluationIso X (negativeTwist D)) t x
  exact h.trans (exists_congr fun W => exists_congr fun _ => exists_congr fun b =>
    Eq.congr_left (Stacks.SheafOfModules.tensorPairing_evaluationIso (negativeTwist D) W
      (t.eval (op W)) b))

/-- **Outside the nonvanishing locus every value of the section has a non-unit germ.** If some
value had a unit germ at `x` then it would be invertible on a neighbourhood, and rescaling the
section of the ideal sheaf by that inverse would make the value `1` there, putting `x` in the
nonvanishing locus. -/
theorem not_isUnit_germ_dualAppLE (t : (invertibleSheaf D).sections) {y : X}
    (ht : y ∉ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace)
      (invertibleSheaf D) t)
    {U : X.Opens} (hyU : y ∈ U) (b : (negativeTwist D).val.obj (op U)) :
    ¬ IsUnit (X.presheaf.germ U y hyU (dualAppLE D (t.eval (op U)) le_rfl b)) := by
  intro hunit
  refine ht ((mem_nonvanishingLocus_iff_exists_dualAppLE D t y).2 ?_)
  have hyb : y ∈ X.basicOpen (dualAppLE D (t.eval (op U)) le_rfl b) :=
    (X.mem_basicOpen _ y hyU).2 hunit
  have hWU : X.basicOpen (dualAppLE D (t.eval (op U)) le_rfl b) ≤ U := X.basicOpen_le _
  have hres : IsUnit (X.presheaf.map (homOfLE hWU).op (dualAppLE D (t.eval (op U)) le_rfl b)) :=
    X.toRingedSpace.isUnit_res_basicOpen _
  obtain ⟨v, hv⟩ := hres.exists_left_inv
  refine ⟨_, hyb, Stacks.SheafOfModules.smulSectionMap (𝒪 := X.sheaf.obj)
    (h𝒪 := (structureSheafRing X.toRingedSpace).property) (idealRes D hWU b) v, ?_⟩
  rw [dualAppLE_smulSectionMap, dualAppLE_sections_eval_idealRes]
  exact hv

end Nonvanishing

section Divisibility

variable (D : X.IdealSheafData) (p : ℕ) (t : (invertibleSheaf (D ^ (p + 1))).sections)

/-- **The restriction of `t` to `U` is in the range, given the divisibility.** This is
`Stacks.Divisors.mem_range_app_of_dvd` with the basis of `ℐ_{p·D}` produced internally. -/
theorem mem_range_app_of_dvd_eval (U : X.affineOpens) {f : Γ(X, (U : X.Opens))}
    (hf : D.ideal U = Ideal.span {f}) (hfnzd : f ∈ nonZeroDivisors Γ(X, (U : X.Opens)))
    {ep1 : (negativeTwist (D ^ (p + 1))).val.obj (op (U : X.Opens))}
    (hep1 : idealSheafSection (D ^ (p + 1)) ep1 = f ^ (p + 1))
    (hdvd : f ∣ dualAppLE (D ^ (p + 1)) (t.eval (op (U : X.Opens))) le_rfl ep1) :
    t.eval (op (U : X.Opens)) ∈ LinearMap.range ((invertibleSheafMap
      (negativeTwistMap (pow_succ_le_pow D p))).val.app (op (U : X.Opens))).hom :=
  have hep := exists_idealSheafSection_eq (D ^ p) U (ideal_pow_eq_span D U hf p)
  mem_range_app_of_dvd D p U hf hfnzd hep.choose_spec hep1 _ hdvd

/-- **Away from the support of `D` the restriction of `t` is in the range.** There the ideal of
`D` is the unit ideal, generated by the nonzerodivisor `1`, which divides everything. -/
theorem exists_affineOpen_mem_range_app_of_notMem_support {z : X} (hz : z ∉ D.support) :
    ∃ U : X.affineOpens, z ∈ (U : Set X) ∧
      t.eval (op (U : X.Opens)) ∈ LinearMap.range ((invertibleSheafMap
        (negativeTwistMap (pow_succ_le_pow D p))).val.app (op (U : X.Opens))).hom := by
  obtain ⟨U, hzU, htop⟩ := exists_affineOpens_ideal_eq_top D hz
  have hf : D.ideal U = Ideal.span {(1 : Γ(X, (U : X.Opens)))} := by
    rw [htop, Ideal.span_singleton_one]
  obtain ⟨ep1, hep1⟩ :=
    exists_idealSheafSection_eq (D ^ (p + 1)) U (ideal_pow_eq_span D U hf (p + 1))
  exact ⟨U, hzU, mem_range_app_of_dvd_eval D p t U hf (Submonoid.one_mem _) hep1 (one_dvd _)⟩

/-- **At a point whose ideal sheaf stalk is the maximal ideal, the non-generating hypothesis
gives the divisibility.** The germ of the value of `t` on the local basis of `ℐ_{(p+1)D}` is
not a unit, so it lies in the maximal ideal, which is generated by the germ of the local
equation `f` of `D`; so `f` divides that value in the local ring, hence on a smaller affine
neighbourhood, where `Stacks.Divisors.mem_range_app_of_dvd_eval` applies. -/
theorem exists_affineOpen_mem_range_app_of_stalk_eq_maximalIdeal
    (hD : IsEffectiveCartierDivisor D) {y : X}
    (hstalk : AlgebraicGeometry.IdealSheafData.stalk D y
      = IsLocalRing.maximalIdeal (X.presheaf.stalk y))
    (ht : y ∉ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace)
      (invertibleSheaf (D ^ (p + 1))) t) :
    ∃ U : X.affineOpens, y ∈ (U : Set X) ∧
      t.eval (op (U : X.Opens)) ∈ LinearMap.range ((invertibleSheafMap
        (negativeTwistMap (pow_succ_le_pow D p))).val.app (op (U : X.Opens))).hom := by
  have : IsEffectiveCartierDivisor (D ^ (p + 1)) := isEffectiveCartierDivisor_pow hD (p + 1)
  obtain ⟨U₀, hU₀, hyU₀, f₀, hreg₀, hspan₀⟩ :=
    exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor D hD y
  have hf₀ : f₀ ∈ nonZeroDivisors Γ(X, U₀) := isRegular_iff_mem_nonZeroDivisors.1 hreg₀
  obtain ⟨ep1, hep1⟩ := exists_idealSheafSection_eq (D ^ (p + 1)) ⟨U₀, hU₀⟩
    (ideal_pow_eq_span D ⟨U₀, hU₀⟩ hspan₀ (p + 1))
  have hspanStalk : AlgebraicGeometry.IdealSheafData.stalk D y
      = Ideal.span {X.presheaf.germ U₀ y hyU₀ f₀} := by
    rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ D y ⟨U₀, hU₀⟩ hyU₀, hspan₀,
      Ideal.map_span, Set.image_singleton]
  have hdvdgerm : X.presheaf.germ U₀ y hyU₀
        (dualAppLE (D ^ (p + 1)) (t.eval (op U₀)) le_rfl ep1)
      ∈ Ideal.span {X.presheaf.germ U₀ y hyU₀ f₀} := by
    rw [← hspanStalk, hstalk, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact not_isUnit_germ_dualAppLE (D ^ (p + 1)) t ht hyU₀ ep1
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hdvdgerm
  obtain ⟨V, hVU₀, hyV, r, hr⟩ := X.presheaf.exists_le_germ_eq c hyU₀
  have hgerm : X.presheaf.germ V y hyV (X.presheaf.map (homOfLE hVU₀).op
        (dualAppLE (D ^ (p + 1)) (t.eval (op U₀)) le_rfl ep1))
      = X.presheaf.germ V y hyV (r * X.presheaf.map (homOfLE hVU₀).op f₀) := by
    rw [X.presheaf.germ_res_apply, map_mul, hr, X.presheaf.germ_res_apply, hc]
  obtain ⟨W, hyW, iW, jW, hW⟩ := TopCat.Presheaf.germ_eq X.presheaf y hyV hyV _ _ hgerm
  have hWV : W ≤ V := iW.le
  have hWpinned : X.presheaf.map (homOfLE hWV).op (X.presheaf.map (homOfLE hVU₀).op
        (dualAppLE (D ^ (p + 1)) (t.eval (op U₀)) le_rfl ep1))
      = X.presheaf.map (homOfLE hWV).op (r * X.presheaf.map (homOfLE hVU₀).op f₀) := hW
  rw [map_mul, res_res, res_res] at hWpinned
  obtain ⟨g, hgW, hyg⟩ := hU₀.exists_basicOpen_le (V := W) ⟨y, hyW⟩ hyU₀
  have hU₁U₀ : ((X.affineBasicOpen (U := ⟨U₀, hU₀⟩) g : X.affineOpens) : X.Opens) ≤ U₀ :=
    X.basicOpen_le g
  have hU₁W : ((X.affineBasicOpen (U := ⟨U₀, hU₀⟩) g : X.affineOpens) : X.Opens) ≤ W := hgW
  refine ⟨X.affineBasicOpen (U := ⟨U₀, hU₀⟩) g, hyg, ?_⟩
  have hspan₁ : D.ideal (X.affineBasicOpen (U := ⟨U₀, hU₀⟩) g)
      = Ideal.span {X.presheaf.map (homOfLE hU₁U₀).op f₀} := by
    rw [← D.map_ideal (U := X.affineBasicOpen (U := ⟨U₀, hU₀⟩) g) (V := ⟨U₀, hU₀⟩) hU₁U₀,
      hspan₀, Ideal.map_span, Set.image_singleton]
    rfl
  have hf₁ : X.presheaf.map (homOfLE hU₁U₀).op f₀
      ∈ nonZeroDivisors Γ(X, ((X.affineBasicOpen (U := ⟨U₀, hU₀⟩) g : X.affineOpens) :
        X.Opens)) :=
    mem_nonZeroDivisors_res hU₀ hf₀ hU₁U₀
  refine mem_range_app_of_dvd_eval D p t _ hspan₁ hf₁
    (idealSheafSection_idealRes_of_eq_pow _ hU₁U₀ hep1) ?_
  rw [dualAppLE_sections_eval_idealRes]
  refine ⟨X.presheaf.map (homOfLE (hU₁W.trans hWV)).op r, ?_⟩
  have h2 := congrArg (fun z : Γ(X, W) => X.presheaf.map (homOfLE hU₁W).op z) hWpinned
  simp only [map_mul, res_res] at h2
  exact h2.trans (mul_comm _ _)

end Divisibility

section Main

/-- **The divisibility step, for a divisor supported at a single point whose ideal sheaf cuts
out the maximal ideal there.** Let `D` be an effective Cartier divisor on a scheme `X` whose
support is the single point `y` and whose ideal sheaf induces the maximal ideal of
`𝒪_{X,y}`. A global section of `𝒪_X((p+1)D)` whose germ at `y` does not generate the stalk is
the image of a global section of `𝒪_X(p·D)`.

The proof is local-to-global. Away from `y` the ideal of `D` is the unit ideal, so the
inclusion is locally an isomorphism; at `y` the non-generating hypothesis says exactly that
the value of the section on the local basis of `ℐ_{(p+1)D}` lies in the maximal ideal, which
is generated by the local equation of `D`, so that value is divisible by it and the section
extends. Those local preimages agree, because the inclusion is a monomorphism
(`Stacks.Divisors.mono_invertibleSheafMap_negativeTwistMap`), and therefore glue. -/
theorem mem_range_sectionsMap_invertibleSheafMap_of_notMem_nonvanishingLocus
    (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D) (p : ℕ)
    (t : (invertibleSheaf (D ^ (p + 1))).sections) {y : X} (hsupp : D.supportSet = {y})
    (hstalk : AlgebraicGeometry.IdealSheafData.stalk D y
      = IsLocalRing.maximalIdeal (X.presheaf.stalk y))
    (ht : y ∉ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace)
      (invertibleSheaf (D ^ (p + 1))) t) :
    t ∈ Set.range (SheafOfModules.sectionsMap (invertibleSheafMap
      (negativeTwistMap (pow_succ_le_pow D p)))) := by
  classical
  have := mono_invertibleSheafMap_negativeTwistMap D p hD
  refine Stacks.SheafOfModules.mem_range_sectionsMap_of_mem_range_app_top _ t
    (Stacks.SheafOfModules.mem_range_app_of_locally _ _ fun z _ => ?_)
  obtain ⟨U, hzU, hmem⟩ : ∃ U : X.affineOpens, z ∈ (U : Set X) ∧
      t.eval (op (U : X.Opens)) ∈ LinearMap.range ((invertibleSheafMap
        (negativeTwistMap (pow_succ_le_pow D p))).val.app (op (U : X.Opens))).hom := by
    by_cases hzy : z = y
    · subst hzy
      exact exists_affineOpen_mem_range_app_of_stalk_eq_maximalIdeal D p t hD hstalk ht
    · refine exists_affineOpen_mem_range_app_of_notMem_support D p t fun hz => ?_
      have h1 : z ∈ D.supportSet := Scheme.IdealSheafData.mem_supportSet_iff_mem_support.2 hz
      rw [hsupp] at h1
      exact hzy h1
  refine ⟨(U : X.Opens), le_top, hzU, ?_⟩
  rwa [PresheafOfModules.sections_property t (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op]

end Main

end Stacks.Divisors

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **The minimality step of the proof of [Stacks, Tag 0A27].** For `Y` a proper curve over a
field `k` and `y` a closed point at which `𝒪_{Y,y}` is a discrete valuation ring, a global
section of `𝒪_Y((p+1)y)` whose germ at `y` does not generate the stalk — equivalently, which
lies outside the nonvanishing locus at `y` — is the image of a global section of `𝒪_Y(p·y)`
under the inclusion `𝒪_Y(p·y) ⊂ 𝒪_Y((p+1)y)`.

This is the source's *"otherwise it would define a section of `𝒪_X((n-1)x) ⊂ 𝒪_X(n·x)`"*, and
it is the hypothesis `hlocal` of
`Stacks.Divisors.isAffineOpen_compl_singleton_of_mem_range_of_finrank`, which asks it at every
`p` because the minimal `p` is produced by a search.

Properness and the curve structure are not used: the statement is
`Stacks.Divisors.mem_range_sectionsMap_invertibleSheafMap_of_notMem_nonvanishingLocus` for the
divisor `y`, which is effective Cartier by items (4) and (5) of [Stacks, Tag 0B8Y], whose
support is `{y}` and whose ideal sheaf induces the maximal ideal of `𝒪_{Y,y}`. They are kept so
that the statement is the one the inner claim of Tag 0A27 consumes.

## References

* [Stacks Project, Tag 0A27](https://stacks.math.columbia.edu/tag/0A27)
-/
theorem mem_range_invertibleSheafMap_of_notMem_nonvanishingChart
    {k : Type u} [Field k] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of k))
    [IsLocallyNoetherian Y] [IsIntegral Y] (_hq : IsProper q) (_hc : IsCurve k q)
    {y : Y} (hy : IsClosed ({y} : Set Y))
    [IsDiscreteValuationRing (Y.presheaf.stalk y)] (p : ℕ)
    (t : (Stacks.Divisors.invertibleSheaf
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨{y}, hy⟩ : TopologicalSpace.Closeds Y) ^ (p + 1))).sections)
    (ht : y ∉ Stacks.ProjectiveSpaceSections.nonvanishingChart
      (Stacks.Divisors.invertibleSheaf (Scheme.IdealSheafData.vanishingIdeal
        (⟨{y}, hy⟩ : TopologicalSpace.Closeds Y) ^ (p + 1))) t) :
    t ∈ Set.range (SheafOfModules.sectionsMap (Stacks.Divisors.invertibleSheafMap
      (Stacks.Divisors.negativeTwistMap (Stacks.Divisors.pow_succ_le_pow
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨{y}, hy⟩ : TopologicalSpace.Closeds Y)) p)))) :=
  Stacks.Divisors.mem_range_sectionsMap_invertibleSheafMap_of_notMem_nonvanishingLocus _
    (isEffectiveCartierDivisor_vanishingIdeal_of_isDiscreteValuationRing hy) p t
    (Scheme.IdealSheafData.coe_support_vanishingIdeal (⟨{y}, hy⟩ : TopologicalSpace.Closeds Y))
    (Stacks.Divisors.stalk_vanishingIdeal_singleton_of_isClosed y hy) ht

end AlgebraicGeometry


end
