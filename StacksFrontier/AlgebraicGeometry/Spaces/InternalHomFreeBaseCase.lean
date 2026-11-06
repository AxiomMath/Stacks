module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentInternalHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The internal Hom out of a finite free `𝒪_F`-module on an algebraic space

Clause (6) of Stacks 03M1 asserts that the internal Hom `𝓗om_{𝒪_F}(G, G')` of two quasi-coherent
`𝒪_F`-modules on an algebraic space `F` is quasi-coherent when `G` is of finite presentation.
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentInternalHom` supplies the **inductive step** of
the source proof: the base change criterion of Descent, Proposition 03DX(2) for `𝓗om_{𝒪_F}(G, G')`
follows, unconditionally, from the criterion for the internal Homs out of the two modules of a
presentation `Q ⟶ P ⟶ G ⟶ 0`.

This file supplies the **base case**, which is what that reduction leaves open: the internal Hom
out of a *finite* coproduct of copies of the structure sheaf is cartesian on affine charts as
soon as the second variable is.  The proof is the composite of three steps:

* `𝓗om_{𝒪_F}(𝒪_F, N) ≅ N` — the internal Hom out of one copy of the structure sheaf is the module
  itself (`AlgebraicGeometry.Space.smallEtaleUnitCoevalIso`);
* `𝓗om_{𝒪_F}(∐_{i ∈ Fin n} 𝒪_F, N)` is a product of `n` copies of `𝓗om_{𝒪_F}(𝒪_F, N)` on the
  sections over every étale chart
  (`AlgebraicGeometry.Space.bijective_smallEtaleInternalHomMapLeft_pi_app`), because restriction to
  a slice of the small étale site preserves the coproduct (Stacks 03EJ);
* a module which is, on sections over every chart, a *finite* product of copies of a module
  cartesian on affine charts is itself cartesian on affine charts
  (`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_bijective_pi`).

**Where the finite-presentation hypothesis of the source enters, and it enters only here:** base
change along a flat ring map commutes with a *finite* product unconditionally, by Mathlib's
`TensorProduct.piRight`, but with an infinite one only under further hypotheses.  The third step
above is false for an arbitrary index type and is stated for finite index types only.

## Main definitions

* `Stacks.SheafOfModules.sectionsOverEquivFreeUniverse`: the global sections of the restriction of
  a sheaf of modules to a slice of the site are its sections over the object restricted to, at a
  free module universe.
* `Stacks.SheafOfModules.uliftUnitHomEquiv`: morphisms out of the universe lift of the free module
  of rank one are the global sections, `(uliftForPresentation (unit R) ⟶ M) ≃ M.sections`, at an
  arbitrary site and any module universe containing that of the coefficient rings.
* `Stacks.SheafOfModules.uliftUnitOverHomEquiv`: the same over a slice of the site, where the
  global sections of the restriction are the sections over the object restricted to.
* `AlgebraicGeometry.Space.smallEtaleUliftUnit`: the structure sheaf of an algebraic space as an
  `𝒪_F`-module in the module universe in which presentations are taken.
* `AlgebraicGeometry.Space.smallEtaleUnitCoeval`: the comparison `N ⟶ 𝓗om_{𝒪_F}(𝒪_F, N)` sending a
  section to multiplication by it, and
  `AlgebraicGeometry.Space.smallEtaleUnitCoevalIso`, the isomorphism it is.

## Main results

* `CategoryTheory.Limits.bijective_cofanInj_comp`: the universal property of a coproduct as a
  bijection of hom sets.
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_bijective_pi`: **being cartesian on affine
  charts passes to a finite product.**  Stated for an arbitrary finite index type and an
  arbitrary module universe, for a not-necessarily-constant family.  This is what the cartesian
  toolkit of this tree was missing: it
  already has the kernel, cokernel, short-exact and isomorphism transfer lemmas, and the
  *coproduct* of copies of the structure sheaf
  (`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isColimit_cofan` of
  `StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleCartesian`), but not the product.
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_smallEtaleInternalHom_unit`: the clause for
  the internal Hom out of one copy of the structure sheaf.
* `AlgebraicGeometry.Space.bijective_smallEtaleInternalHomMapLeft_pi_app`: over every étale chart,
  the sections of the internal Hom out of a finite coproduct of copies of the structure sheaf are
  the product of the sections of the internal Homs out of the summands.
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_smallEtaleInternalHom_free`: **the base case
  of Stacks 03M1(6), unconditionally.**

## Implementation notes

**No `@[stacks 03M1]` attribute is carried, and clause (6) is not closed by this file even
together with the inductive step.**  Stacks 03M1 has six parts and none of them is proved in
either tree; what is now available for clause (6) is the implication "`N` cartesian on affine
charts ⟹ `𝓗om_{𝒪_F}(G, N)` cartesian on affine charts for `G` with a *global* presentation by
finite free modules", whereas the finite-presentation hypothesis of the source is *local*.
Closing the gap needs the whole reduction transplanted to the slice sites, and quasi-coherence
itself needs Descent, Proposition 03DX(2), which is carried as the hypothesis `h03DX` in
`AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom_of_isCartesian`.  The same
convention — a reduction carries no tag — is used by
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentInternalHom`.

Two facts about module universes.

* `Stacks.SheafOfModules.sectionsOverEquivFreeUniverse` and
  `AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_bijective_pi` are at a **free** module
  universe, and the latter at a free index universe too; nothing in them needs sheafification, a
  colimit or a limit.  `Stacks.SheafOfModules.uliftUnitHomEquiv` and
  `Stacks.SheafOfModules.uliftUnitOverHomEquiv` are at `max t r`, that is at any module universe
  containing the universe of the coefficient rings, which is forced by the universe lift itself
  and is not an artifact.
* The statements about the internal Hom are at the module universe `max (u + 1) m`, as in
  `StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentInternalHom`.  For
  `AlgebraicGeometry.Space.bijective_smallEtaleInternalHomMapLeft_pi_app` the binding declaration
  is again `Stacks.SheafOfModules.overFunctor_preservesColimits` (Stacks 03EJ), which is stated
  only at module universes of the shape `max u v w t`, that is `max (u + 1) t` at the small étale
  ringed site; relaxing that one universe would move those statements to a free `m` too.  For
  `AlgebraicGeometry.Space.smallEtaleUnitCoeval` the pin is **intrinsic and not an artifact**: the
  universe lift `SheafOfModules.uliftForPresentation` to `t` of the free module of rank one lands
  in module universe `max t u`, while the internal Hom out of it lands in `max (u + 1) t`, so the
  two are the same module category only when `t` already contains `u + 1`.

`Stacks.SheafOfModules.uliftUnitOverHomEquiv` is built from
`Stacks.SheafOfModules.uliftUnitHomEquiv` at the slice site together with
`Stacks.SheafOfModules.sectionsOverEquivFreeUniverse`, a copy of
`Stacks.SheafOfModules.FiniteTypeKernel.sectionsOverEquiv` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel`, whose statement and proof are
universe-free but whose binder pins the module universe to the universe of the coefficient rings.
The copy carries a different name in a different namespace, so the two cannot clash, and it
should be deleted as soon as that universe is relaxed in place.

The three section-level computations are driven by
`Stacks.SheafOfModules.uliftUnitOverHomEquiv_symm_app`, which holds by `rfl`: the morphism
attached to a section `x` sends a local section `y` of the structure sheaf to `y · x`.  Scalar
multiplication on the internal Hom is postcomposition with multiplication on the target
(Stacks 03EM), so linearity of that assignment is the commutativity of the structure sheaf,
`Stacks.PresheafOfModules.InternalHom.multEndo_smul_comm`, and naturality is the restriction law
of `N` — `CategoryTheory.Over.map` does not move the left leg of a slice object, which is why no
transport appears.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0GMY](https://stacks.math.columbia.edu/tag/0GMY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.PresheafOfModules.InternalHom

universe w u v r t m

namespace CategoryTheory.Limits

/-- **The universal property of a coproduct as a bijection of hom sets.**  If a cofan
`ιs : ∀ i, E i ⟶ Pt` is colimiting, then precomposition with its injections is a bijection
from the morphisms out of `Pt` to the families of morphisms out of the `E i`.

Injectivity is `CategoryTheory.Limits.Cofan.IsColimit.hom_ext` and surjectivity is
`CategoryTheory.Limits.Cofan.IsColimit.desc`; Mathlib states both but not the bijection. -/
@[sga "4 Vbis 1.2.10.1" "special case"]
theorem bijective_cofanInj_comp {D : Type u} [Category.{v} D] {I : Type w} {E : I → D} {Pt : D}
    (ιs : ∀ i, E i ⟶ Pt) (hPt : IsColimit (Cofan.mk Pt ιs)) (W : D) :
    Function.Bijective (fun α : Pt ⟶ W => fun i => ιs i ≫ α) :=
  ⟨fun _ _ h => Cofan.IsColimit.hom_ext hPt _ _ (fun i => congrFun h i),
    fun φ => ⟨Cofan.IsColimit.desc hPt φ, funext fun i => Cofan.IsColimit.fac hPt φ i⟩⟩

end CategoryTheory.Limits

namespace Stacks.SheafOfModules

open _root_.SheafOfModules

section UliftUnit

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- Global sections of the restriction of `M` to the slice site over `V` are the sections of `M`
over `V`.

This is `Stacks.SheafOfModules.FiniteTypeKernel.sectionsOverEquiv` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel`, whose statement and proof are
the same token for token, with the module universe of its binder — which is pinned there to the
universe of the coefficient rings — left free.  It carries a different name in a different
namespace, so the two cannot clash, and it should be deleted as soon as that universe is relaxed
in place.  It is not `private`, although nothing outside this file uses it, because the module
system forbids an exposed definition from mentioning a private one. -/
noncomputable def sectionsOverEquivFreeUniverse (M : _root_.SheafOfModules.{m} R)
    (V : C) : (M.over V).sections ≃ M.val.obj (op V) where
  toFun s := s.val (op (Over.mk (𝟙 V)))
  invFun x := PresheafOfModules.sectionsMk (M := (M.over V).val)
    (fun Z => M.val.map (Z.unop.hom.op) x) fun {Z Z'} g => by
      change M.val.map (g.unop.left.op) (M.val.map (Z.unop.hom.op) x) = _
      rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w]
  left_inv s := by
    ext Z
    change M.val.map (Z.unop.hom.op) (s.val (op (Over.mk (𝟙 V)))) = _
    exact s.property ((Over.homMk Z.unop.hom (by simp) : Z.unop ⟶ Over.mk (𝟙 V))).op
  right_inv x := by
    change M.val.map ((𝟙 V).op) x = x
    rw [op_id, M.val.map_id]
    rfl

/-- **Morphisms out of the universe lift of the free module of rank one are the global
sections.**  For a sheaf of rings `R` on a site and a sheaf of `R`-modules `M` whose module
universe is a universe lift of that of `R`,

`(SheafOfModules.uliftForPresentation (SheafOfModules.unit R) ⟶ M) ≃ M.sections`.

A morphism out of the lift is determined by the image of the lift of `1`, because the sections
of the lift over an object `X` are the free `R(X)`-module on the lift of `1`, and the
compatibility of that image with restriction is exactly the condition for a global section.

This is `SheafOfModules.unitHomEquiv` of Mathlib with the universe lift inserted.  That
declaration cannot be used where a presentation is taken: it pins the module universe of `M` to
the universe of the coefficient rings, whereas `SheafOfModules.HasGlobalPresentation` lifts the
free modules into the common universe `max u v r m` first.  The equivalence is stated for
morphisms of the underlying *presheaves* of modules, which is the form in which the sections of
the internal Hom presheaf of Stacks 03EM appear; no sheaf condition is used. -/
noncomputable def uliftUnitHomEquiv (M : _root_.SheafOfModules.{max t r} R) :
    ((uliftForPresentation.{u, v, r, r, t} (unit R)).val ⟶ M.val) ≃ M.sections where
  toFun φ := PresheafOfModules.sectionsMk
    (fun X => φ.app X (ULift.up (1 : (R.obj.obj X : Type r))))
    (fun {X Y} f => by
      rw [← PresheafOfModules.naturality_apply φ f
        (ULift.up (1 : (R.obj.obj X : Type r)))]
      congr 1
      exact ULift.ext ((R.obj.map f).hom.map_one))
  invFun s := PresheafOfModules.Hom.mk
    (fun X => ModuleCat.ofHom
      { toFun := fun y => (ULift.down y : (R.obj.obj X : Type r)) • s.eval X
        map_add' := fun y y' => add_smul (ULift.down y : (R.obj.obj X : Type r))
          (ULift.down y' : (R.obj.obj X : Type r)) (s.eval X)
        map_smul' := fun a y => mul_smul a (ULift.down y : (R.obj.obj X : Type r)) (s.eval X) })
    (fun {X Y} f => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      change ((R.obj.map f).hom (ULift.down y : (R.obj.obj X : Type r))) • s.eval Y =
        M.val.map f ((ULift.down y : (R.obj.obj X : Type r)) • s.eval X)
      rw [PresheafOfModules.map_smul, PresheafOfModules.sections_property]
      rfl)
  left_inv φ := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    change (ULift.down y : (R.obj.obj X : Type r)) •
        φ.app X (ULift.up (1 : (R.obj.obj X : Type r))) = φ.app X y
    have hy : (ULift.down y : (R.obj.obj X : Type r)) •
        (ULift.up (1 : (R.obj.obj X : Type r)) :
          ((uliftForPresentation.{u, v, r, r, t} (unit R)).val.obj X : Type (max t r))) = y :=
      ULift.ext (mul_one (ULift.down y : (R.obj.obj X : Type r)))
    exact (((φ.app X).hom.map_smul _ _).symm).trans (congrArg (fun z => φ.app X z) hy)
  right_inv s := by
    apply PresheafOfModules.sections_ext
    intro X
    change (1 : (R.obj.obj X : Type r)) • s.eval X = s.eval X
    exact one_smul _ _

/-- **Morphisms out of the universe lift of the free module of rank one, over a slice of the
site, are the sections over the object restricted to.**  For an object `V` of the site,

`(SheafOfModules.uliftForPresentation (SheafOfModules.unit R)|_V ⟶ N|_V) ≃ N(V)`.

This is `Stacks.SheafOfModules.uliftUnitHomEquiv` applied at the slice site over `V`, composed
with the identification of the global sections of a restriction with the sections over `V`.  The
restriction of the lift of the free module of rank one is the lift of the free module of rank
one over the restricted ring sheaf, on the nose. -/
noncomputable def uliftUnitOverHomEquiv (N : _root_.SheafOfModules.{max t r} R) (V : C) :
    ((((uliftForPresentation.{u, v, r, r, t} (unit R)).over V).val) ⟶ (N.over V).val) ≃
      N.val.obj (op V) :=
  (uliftUnitHomEquiv.{max u v, v, r, t} (N.over V)).trans (sectionsOverEquivFreeUniverse N V)

/-- The morphism attached to a section `x` of `N` over `V` by
`Stacks.SheafOfModules.uliftUnitOverHomEquiv` sends a local section `y` of the structure sheaf
over `W ⟶ V` to `y` times the restriction of `x` to `W`.  This pins the equivalence down, and it
is what drives every computation with it below. -/
theorem uliftUnitOverHomEquiv_symm_app (N : _root_.SheafOfModules.{max t r} R) (V : C)
    (x : N.val.obj (op V)) (Z : (Over V)ᵒᵖ)
    (y : (((uliftForPresentation.{u, v, r, r, t} (unit R)).over V).val.obj Z :
      Type (max t r))) :
    ((uliftUnitOverHomEquiv N V).symm x).app Z y =
      (ULift.down y : (R.obj.obj (op Z.unop.left) : Type r)) •
        N.val.map (Z.unop.hom.op) x := rfl

end UliftUnit

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

section Product

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **Being cartesian on affine charts passes to a finite product.**  Let `G : I → Modules` be a
family of `𝒪_F`-modules on an algebraic space, indexed by a *finite* type, let `H` be an
`𝒪_F`-module and let `π : ∀ i, H ⟶ G i` be a family of morphisms exhibiting `H` as the product
of the `G i` on the sections over every *affine* étale chart.  If every `G i` is cartesian on
affine charts then so is `H`.

The hypothesis is asked only of affine charts, which is where it is available and where it is
used, as in `AlgebraicGeometry.Space.isCartesianOnAffineCharts_cokernel`.

**The finiteness of `I` is load-bearing and the statement is false without it:** the comparison
`𝒪_F(V) ⊗_{𝒪_F(U)} ∏_{i ∈ I} G(U) ⟶ ∏_{i ∈ I} (𝒪_F(V) ⊗_{𝒪_F(U)} G(U))` of Mathlib's
`TensorProduct.piRight` is an isomorphism exactly because `I` is finite.

The product is given by a family of morphisms rather than by a limit cone, so that no limits in
the category of `𝒪_F`-modules need to exist; linearity of the comparison over `𝒪_F(U)` and its
compatibility with restriction are then free, being part of the `π i` being morphisms.  The
module universe and the universe of the index type are both free.

What this adds to the existing toolkit for
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts` is the **product**.  That toolkit already
has the transfer lemmas for an isomorphism
(`AlgebraicGeometry.Space.IsCartesianOnAffineCharts.of_iso`), for a kernel
(`AlgebraicGeometry.Space.isCartesianOnAffineCharts_kernel` and
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isLimit`, which is the kernel case and not
a general limit), for a cokernel, for the three terms of a short exact sequence, and for a
*coproduct of copies of the structure sheaf*
(`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isColimit_cofan` and
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_free` of
`StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleCartesian`, both at the module universe `u`,
where Mathlib's `SheafOfModules.free` lives, and both for an *arbitrary* index type — the
coproduct of copies of `𝒪_F` needs no finiteness, it is the Hom *out of* one that does).  A
finite direct sum is a finite product, so the lemma below also covers the finite case of
clause (1) of Stacks 03M1: the family `G` is not required to be constant. -/
theorem isCartesianOnAffineCharts_of_bijective_pi {I : Type w} [Finite I]
    {G : I → Modules.{u, m} B S hS F hF} {H : Modules.{u, m} B S hS F hF} (π : ∀ i, H ⟶ G i)
    (hπ : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        Function.Bijective
          (fun x : H.val.obj (op U) => fun i => (π i).val.app (op U) x))
    (hG : ∀ i, IsCartesianOnAffineCharts (G i)) :
    IsCartesianOnAffineCharts H := by
  classical
  intro U V hU hV f
  let _ := Fintype.ofFinite I
  let _ := chartAlgebra (hF := hF) f
  let θ : (H.val.obj (op U) : Type m) →ₗ[chartRing B S hS F hF U]
      (∀ i, (G i).val.obj (op U)) :=
    LinearMap.pi fun i => ((π i).val.app (op U)).hom
  have hpi : Function.Bijective (fun (ww : ∀ i, TensorProduct (chartRing B S hS F hF U)
      (chartRing B S hS F hF V) ((G i).val.obj (op U))) =>
      fun i => sectionsBaseChange (G i) f (ww i)) :=
    (Equiv.piCongrRight fun i : I => Equiv.ofBijective _ (hG i U V hU hV f)).bijective
  have hlt : Function.Bijective (LinearMap.lTensor (chartRing B S hS F hF V) θ) :=
    bijective_lTensor_of_bijective _ θ (hπ U hU)
  have hpr : Function.Bijective (TensorProduct.piRight (chartRing B S hS F hF U)
      (chartRing B S hS F hF V) (chartRing B S hS F hF V)
      (fun i : I => ((G i).val.obj (op U) : Type m))) :=
    (TensorProduct.piRight _ _ _ _).toEquiv.bijective
  have key : ∀ z : TensorProduct (chartRing B S hS F hF U) (chartRing B S hS F hF V)
      (H.val.obj (op U)),
      (fun i => (π i).val.app (op V) (sectionsBaseChange H f z)) =
        (fun i => sectionsBaseChange (G i) f
          (TensorProduct.piRight (chartRing B S hS F hF U) (chartRing B S hS F hF V)
            (chartRing B S hS F hF V) (fun i : I => ((G i).val.obj (op U) : Type m))
            (LinearMap.lTensor (chartRing B S hS F hF V) θ z) i)) := by
    intro z
    funext i
    rw [app_sectionsBaseChange (π i) f z]
    congr 1
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b x => rfl
    | add z z' hz hz' => rw [map_add, map_add, map_add, Pi.add_apply, hz, hz']
  refine ((hπ V hV).of_comp_iff' (sectionsBaseChange H f)).1 ?_
  convert hpi.comp (hpr.comp hlt) using 1
  exact funext key

end Product

section FreeBaseCase

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The structure sheaf of an algebraic space as an `𝒪_F`-module in the module universe in
which presentations are taken.**  A global presentation in the sense of
`SheafOfModules.HasGlobalPresentation` is a cokernel of a map between coproducts of copies of
this module, and `Stacks.SheafOfModules.uliftForPresentation` is what puts the module and its
ring sheaf in the common universe; at the small étale ringed site of an algebraic space over
`Scheme.{u}` that universe is `max (u + 1) m`.

It is an `abbrev`, hence reducible, deliberately: the statements below must be interchangeable
with the spelled-out `SheafOfModules.uliftForPresentation (SheafOfModules.unit …)` that
`SheafOfModules.HasGlobalPresentation` uses, and the `rfl` of
`Stacks.SheafOfModules.uliftUnitOverHomEquiv_symm_app` is checked through it. -/
noncomputable abbrev smallEtaleUliftUnit : Modules.{u, max (u + 1) m} B S hS F hF :=
  SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) m}
    (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))

variable {B S hS F hF}

/-- **The comparison `N ⟶ 𝓗om_{𝒪_F}(𝒪_F, N)`**, sending a section of `N` over an étale chart `U`
to the morphism `𝒪_F|_U ⟶ N|_U` which multiplies a local function by (the restriction of) that
section.

Its component over `U` is the inverse of
`Stacks.SheafOfModules.uliftUnitOverHomEquiv`, so it is bijective on sections over every chart by
construction; it is given in this direction because this is the direction in which it is a
morphism for easy reasons.  Linearity over `𝒪_F(U)` is the commutativity of the structure sheaf,
since scalar multiplication on the internal Hom is postcomposition with multiplication on the
target (Stacks 03EM).  Naturality is the restriction law of `N`, and no transport appears because
`CategoryTheory.Over.map` leaves the left leg of a slice object unchanged. -/
noncomputable def smallEtaleUnitCoeval (N : Modules.{u, max (u + 1) m} B S hS F hF) :
    N ⟶ smallEtaleInternalHom B S hS F hF (smallEtaleUliftUnit.{u, m} B S hS F hF) N where
  val := PresheafOfModules.Hom.mk
    (fun X => ConcreteCategory.ofHom (C := ModuleCat
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj.obj X))
      { toFun := fun x =>
          (Stacks.SheafOfModules.uliftUnitOverHomEquiv.{u + 1, u, u, max (u + 1) m}
            N X.unop).symm x
        map_add' := by
          intro x x'
          refine PresheafOfModules.hom_ext fun Z => ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
          rw [Stacks.SheafOfModules.uliftUnitOverHomEquiv_symm_app, map_add, smul_add]
          rfl
        map_smul' := by
          intro a x
          refine PresheafOfModules.hom_ext fun Z => ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
          rw [Stacks.SheafOfModules.uliftUnitOverHomEquiv_symm_app,
            PresheafOfModules.map_smul]
          exact (multEndo_smul_comm (smallEtaleRingedSite B S hS F hF).O.obj N.val X.unop a Z
            (ULift.down y) (N.val.map Z.unop.hom.op x)).symm })
    (by
      intro X Y g
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (Stacks.SheafOfModules.uliftUnitOverHomEquiv.{u + 1, u, u, max (u + 1) m}
          N Y.unop).symm (N.val.map g x) =
        (smallEtaleInternalHom B S hS F hF (smallEtaleUliftUnit.{u, m} B S hS F hF) N).val.map g
          ((Stacks.SheafOfModules.uliftUnitOverHomEquiv.{u + 1, u, u, max (u + 1) m}
            N X.unop).symm x)
      apply PresheafOfModules.hom_ext
      intro Z
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      have H : N.val.map Z.unop.hom.op (N.val.map g x) =
          N.val.map ((Z.unop.hom ≫ g.unop).op) x := by
        rw [← PresheafOfModules.map_comp_apply]
        exact PresheafOfModules.congr_map_apply N.val
          (show g ≫ Z.unop.hom.op = (Z.unop.hom ≫ g.unop).op by
            rw [op_comp]
            rfl) x
      exact (Stacks.SheafOfModules.uliftUnitOverHomEquiv_symm_app N Y.unop
          (N.val.map g x) Z y).trans
        ((congrArg (fun z : (N.val.obj (op Z.unop.left) : Type (max (u + 1) m)) =>
            (ULift.down y :
              ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj.obj
                (op Z.unop.left) : Type u)) • z) H).trans
          (Stacks.SheafOfModules.uliftUnitOverHomEquiv_symm_app N X.unop x
            ((Over.map g.unop).op.obj Z) y).symm))

/-- `AlgebraicGeometry.Space.smallEtaleUnitCoeval` is an isomorphism on the sections over every
étale chart, being the inverse of `Stacks.SheafOfModules.uliftUnitOverHomEquiv` there. -/
theorem isIso_smallEtaleUnitCoeval_val_app (N : Modules.{u, max (u + 1) m} B S hS F hF)
    (X : (smallEtaleRingedSite B S hS F hF).Cᵒᵖ) :
    IsIso ((smallEtaleUnitCoeval N).val.app X) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (Stacks.SheafOfModules.uliftUnitOverHomEquiv.{u + 1, u, u, max (u + 1) m}
    N X.unop).symm.bijective

/-- **`𝓗om_{𝒪_F}(𝒪_F, N) ≅ N`.**  The internal Hom out of one copy of the structure sheaf of an
algebraic space is the module itself, by
`AlgebraicGeometry.Space.smallEtaleUnitCoeval`, which is an isomorphism because it is one on the
sections over every étale chart and the forgetful functor to presheaves of modules is fully
faithful. -/
noncomputable def smallEtaleUnitCoevalIso (N : Modules.{u, max (u + 1) m} B S hS F hF) :
    N ≅ smallEtaleInternalHom B S hS F hF (smallEtaleUliftUnit.{u, m} B S hS F hF) N :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun X => @asIso _ _ _ _ ((smallEtaleUnitCoeval N).val.app X)
        (isIso_smallEtaleUnitCoeval_val_app N X))
      (fun {_X _Y} g => (smallEtaleUnitCoeval N).val.naturality g))

/-- **The base case of Stacks 03M1(6) for one copy of the structure sheaf.**  If an `𝒪_F`-module
`N` is cartesian on affine charts then so is `𝓗om_{𝒪_F}(𝒪_F, N)`, the two being isomorphic by
`AlgebraicGeometry.Space.smallEtaleUnitCoevalIso`. -/
theorem isCartesianOnAffineCharts_smallEtaleInternalHom_unit
    (N : Modules.{u, max (u + 1) m} B S hS F hF) (hN : IsCartesianOnAffineCharts N) :
    IsCartesianOnAffineCharts
      (smallEtaleInternalHom B S hS F hF (smallEtaleUliftUnit.{u, m} B S hS F hF) N) :=
  IsCartesianOnAffineCharts.of_iso (smallEtaleUnitCoevalIso N) hN

/-- **Over every étale chart, the sections of the internal Hom out of a coproduct of copies of
the structure sheaf are the product of the sections of the internal Homs out of the summands.**
The comparison is the family of first-variable precomposition maps
`AlgebraicGeometry.Space.smallEtaleInternalHomMapLeft` along the injections of the coproduct.

This is the half of Stacks 0GMY(1) — internal Hom turns colimits in the first variable into
limits — that the quasi-coherence clause needs, for a coproduct instead of a presentation.  The
input is `Stacks.SheafOfModules.overFunctor_preservesColimits`, Stacks 03EJ: restriction to the
slice at `U` carries the coproduct to a coproduct, and the sections of the internal Hom over `U`
are by construction the morphisms of the restrictions, so the statement is the universal property
of that coproduct, `CategoryTheory.Limits.bijective_cofanInj_comp`.  Finiteness of the index is
*not* used here; it is used only in
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_bijective_pi`.  The index is nevertheless
written `Fin n` rather than an arbitrary type, because the colimit has to be preserved at the
*shape* universe of `Discrete (Fin n)`, which is where
`CategoryTheory.Limits.preservesColimitsOfSize_shrink` applies below. -/
@[sga "4 IV 12.2" "Hom_A(−, special case"]
theorem bijective_smallEtaleInternalHomMapLeft_pi_app {n : ℕ}
    {P : Modules.{u, max (u + 1) m} B S hS F hF}
    (ι : ∀ _ : Fin n, smallEtaleUliftUnit.{u, m} B S hS F hF ⟶ P)
    (hP : IsColimit (Cofan.mk P ι)) (N : Modules.{u, max (u + 1) m} B S hS F hF)
    (U : (smallEtaleRingedSite B S hS F hF).C) :
    Function.Bijective (fun α : (smallEtaleInternalHom B S hS F hF P N).val.obj (op U) =>
      fun i => (smallEtaleInternalHomMapLeft B S hS F hF (ι i) N).val.app (op U) α) := by
  have hpc : PreservesColimitsOfSize.{max (u + 1) m, max (u + 1) m}
      (SheafOfModules.overFunctor.{max (u + 1) m}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U) :=
    Stacks.SheafOfModules.overFunctor_preservesColimits _ U
  have _ : PreservesColimitsOfSize.{0, 0}
      (SheafOfModules.overFunctor.{max (u + 1) m}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U) :=
    preservesColimitsOfSize_shrink _
  have hcol : IsColimit (Cofan.mk ((SheafOfModules.overFunctor.{max (u + 1) m}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U).obj P)
      (fun i => (SheafOfModules.overFunctor.{max (u + 1) m}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
        U).map (ι i))) :=
    Cofan.isColimitMapCoconeEquiv _ _ (Cofan.mk P ι) (isColimitOfPreserves _ hP)
  have hcofan := bijective_cofanInj_comp
    (fun i => (SheafOfModules.overFunctor.{max (u + 1) m}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U).map (ι i))
    hcol (N.over U)
  have hv : ∀ A : Modules.{u, max (u + 1) m} B S hS F hF,
      Function.Bijective (fun β : A.over U ⟶ N.over U => β.val) := fun _ =>
    ⟨fun _ _ h => SheafOfModules.Hom.ext h, fun γ => ⟨⟨γ⟩, rfl⟩⟩
  exact (Function.Bijective.of_comp_iff _ (hv P)).1
    ((Equiv.piCongrRight fun _ : Fin n => Equiv.ofBijective _ (hv _)).bijective.comp hcofan)

/-- **The base case of Stacks 03M1(6), unconditionally.**  Let `P` be a *finite* coproduct of
copies of the structure sheaf of an algebraic space `F` — in this module universe, of
`AlgebraicGeometry.Space.smallEtaleUliftUnit` — and let `N` be an `𝒪_F`-module cartesian on
affine charts.  Then `𝓗om_{𝒪_F}(P, N)` is cartesian on affine charts.

Together with the inductive step
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_smallEtaleInternalHom` this gives the base
change criterion of Descent, Proposition 03DX(2) for the internal Hom out of any `𝒪_F`-module
admitting a global presentation by finite free modules, and with
`AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom_of_isCartesian` the
quasi-coherence of that internal Hom, conditional on 03DX(2) itself and on nothing else.

This is where the finite-presentation hypothesis of Stacks 03M1(6) enters, and it enters only
here: the index `Fin n` is finite, and
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_bijective_pi` is false for an infinite
index type. -/
theorem isCartesianOnAffineCharts_smallEtaleInternalHom_free {n : ℕ}
    {P N : Modules.{u, max (u + 1) m} B S hS F hF}
    (ι : ∀ _ : Fin n, smallEtaleUliftUnit.{u, m} B S hS F hF ⟶ P)
    (hP : IsColimit (Cofan.mk P ι)) (hN : IsCartesianOnAffineCharts N) :
    IsCartesianOnAffineCharts (smallEtaleInternalHom B S hS F hF P N) :=
  isCartesianOnAffineCharts_of_bijective_pi
    (fun i => smallEtaleInternalHomMapLeft B S hS F hF (ι i) N)
    (fun U _ => bijective_smallEtaleInternalHomMapLeft_pi_app ι hP N U)
    (fun _ => isCartesianOnAffineCharts_smallEtaleInternalHom_unit N hN)

end FreeBaseCase

end AlgebraicGeometry.Space

end
