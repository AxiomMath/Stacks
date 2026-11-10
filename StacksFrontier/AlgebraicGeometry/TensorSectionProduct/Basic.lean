module

public import StacksFrontier.AlgebraicGeometry.SectionTensorFormula.Scheme
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Stalk
public import StacksFrontier.AlgebraicGeometry.TensorSectionNonvanishing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `X_{m ⊗ n} = X_m ∩ X_n` for `Stacks.SectionTensorFormula.tensorSection`

`StacksFrontier/AlgebraicGeometry/TensorSectionNonvanishing/Basic.lean` proves the [Stacks, Tag
01CY] remark `X_{e ⊗ f} = X_e ∩ X_f` for two invertible `𝒪_X`-modules, with the product of two
global sections spelled as the composite `Stacks.TensorSectionNonvanishing.unitMul`. Its "What is
not done" names the one thing a consumer wants and it did not have:

> **The product is not related to `Stacks.SectionTensorFormula.tensorSection`.** That is the one
> thing a consumer might expect and it is genuinely absent […] Consequently the module-valued form
> of [Stacks, Tag 01PW] […] whose conclusion is stated with `tensorSection`, **cannot yet be
> composed with the results below**.

This file proves the product formula **for `tensorSection` itself**, over an arbitrary open and
with no bridge to `unitMul`, so that the conclusion of the module-valued Tag 01PW can be used to
compute a nonvanishing locus. The route named as missing there — a formula for the monoidality
isomorphism of sheafification on sections, and the right unitor of the sheafified product — is
**not** taken and is not needed; see the implementation notes.

## Main results

* `Stacks.TensorSectionProduct.surjective_pstalkHom_toTensorSection`: the comparison
  `Stacks.SectionTensorFormula.toTensorSection` is **surjective on stalks**. It is the
  sheafification unit followed by an isomorphism, and
  `Stacks.SectionProduct.pstalkHom_toSheafify_bijective` says the unit is a stalkwise bijection.
* `Stacks.TensorSectionProduct.exists_smul_germ_tensorSection`: **local generation.** If `eF` and
  `eG` generate `F` and `G` over `W` sectionwise, the germ of `tensorSection F G eF eG` generates
  the stalk of `F ⊗ G` at every point of `W`.
* `Stacks.TensorSectionProduct.germ_tensorSection_notMem_maximalSmul_iff`: **the product formula,
  over an arbitrary open.** For `F` and `G` invertible and `m : Γ(F, U)`, `n : Γ(G, U)`, the
  product `tensorSection F G m n` fails to vanish at a point of `U` exactly where both factors do.
* `Stacks.TensorSectionProduct.nonvanishingLocus_tensorSection`: the global case,
  `X_{m ⊗ n} = X_m ∩ X_n`, as an equality of subsets of `X`.
* `Stacks.TensorSectionProduct.mem_nonvanishingLocus_iff_of_resTop_eq`: **the consumer form.** If a
  *global* section `τ` of `F ⊗ G` restricts on `U` to `tensorSection F G m n`, then on `U` the
  nonvanishing locus of `τ` is where `m` and `n` both fail to vanish. This is the shape in which
  the conclusion of [Stacks, Tag 01PW] — an equation `τ|_{X_σ} = m ⊗ σ|_{X_σ}` — is consumed.

## Implementation notes

**Why no monoidality formula is needed.** The missing statements named in
`TensorSectionNonvanishing/Basic.lean` are *equations* between `tensorSection` and a whiskering of
the unit. Nothing below compares the two: the only thing used about
`Stacks.SectionTensorFormula.toTensorSection` is that it is surjective on stalks, which follows
from its definition as `Stacks.SheafOfModules.TensorSheafification.toSheafify` composed with
`Stacks.SectionTensorFormula.tensorSheafIsoTensorObj` and from
`Stacks.SectionProduct.pstalkHom_toSheafify_bijective`. Surjectivity plus
`TensorProduct.induction_on` is enough, because every element of the sectionwise tensor product is
a finite sum of elementary tensors and each elementary tensor is, over a trivializing open, a
scalar multiple of the product of the two basis sections
(`Stacks.SectionProduct.eq_triv_smul_res_basis`, and the bilinearity lemmas
`Stacks.SectionTensorFormula.tensorSection_smul_left` / `_smul_right`).

**Two spellings of the underlying presheaf, and why several statements are restated.**
`AlgebraicGeometry.Scheme.Modules.presheaf` is a `def`, so `M.presheaf` and `M.val.presheaf` are
definitionally equal but not reducibly so; `Stacks.Ample.nonvanishingLocus` and
`Stacks.ModuleStalk.maximalSmul` are keyed on the former while `Stacks.SectionProduct.pgerm` and
`pstalkHom` are keyed on the latter, and instance search for the stalk module structure crosses
neither. `Stacks.TensorSectionProduct.pgerm_eq_germ`, `pstalkHom_germ` and `exists_pstalkHom_eq`
are the three bridges, each `rfl` or a term-mode application; this is the `def`-vs-`abbrev`
mismatch in
its stalk incarnation. For the same reason the presheaf-level `F.val ⊗ G.val` is never written in
a type ascription — its monoidal structure is keyed on
  `(Stacks.SheafOfModules.TensorSheafification.structureSheaf _ _).obj` and is
not found at the `X.ringCatSheaf.obj` spelling.

## What is not done, and no tag is attached

**No `@[stacks]` attribute is attached.** The displayed equality is a *remark* of [Stacks, Tag
01CY], carries no label of its own in the tagged statement, and neither of that tag's two assertions
(the openness of `X_s` and the trivialization of the module on it) is proved here. Tag 01CU is the
construction of the integer tensor powers and is formalized elsewhere.

**Nothing here is proved about `Stacks.TensorSectionNonvanishing.unitMul`.** The two product
formulas are now both available and are still not identified with each other; that identification
remains exactly as open as that file records, and is not needed by anything below.

**Only the invertible case is treated.** The `⊆` half holds for arbitrary modules — that is
`Stacks.TensorSectionNonvanishing.nonvanishingLocus_unitMul_subset_left` in the other spelling —
but nothing here states it without invertibility, since both the generation step and the unit
criterion use a trivialization.

**This does not close part (1) of [Stacks, Tag 0892].** It removes one of that label's named
obstructions; see the report accompanying this file for the two that remain (the nonvanishing locus
of a section over an open subscheme obtained from a global section of the restriction, and
quasi-separatedness of the source of a relatively ample module).

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] TopCat.Presheaf.IsSheaf

open CategoryTheory Category AlgebraicGeometry Opposite MonoidalCategory TopologicalSpace
open Stacks.Ample Stacks.ModuleStalk Stacks.SectionProduct
open Stacks.SheafOfModules.TensorSheafification
open Stacks.SectionTensorFormula

universe u

namespace Stacks.TensorSectionProduct

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {X : Scheme.{u}}

/-- Restriction along a composite of inclusions of opens. -/
theorem map_map {M : X.Modules} {A B C : X.Opens} (i : A ⟶ B) (j : B ⟶ C) (u : Γ(M, C)) :
    M.presheaf.map i.op (M.presheaf.map j.op u) = M.presheaf.map (i ≫ j).op u := by
  rw [op_comp, Functor.map_comp]
  rfl

section Surjective

variable (F G : X.Modules)

/-- `Stacks.SectionTensorFormula.tensorSheafIsoTensorObj` at a scheme. -/
abbrev tensorIsoObj :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
          (schemeSheafCondition X)⟩).obj F).obj G ≅
      @MonoidalCategoryStruct.tensorObj X.Modules _
        (Stacks.SheafInternalHom.schemeMonoidalCategory X).toMonoidalCategoryStruct F G :=
  Stacks.SectionTensorFormula.tensorSheafIsoTensorObj X.presheaf (schemeSheafCondition X) F G

/-- `Stacks.SectionTensorFormula.toTensorSection` at a scheme. -/
abbrev toTensorSectionX :=
  Stacks.SectionTensorFormula.toTensorSection X.presheaf (schemeSheafCondition X) F G

/-- The underlying presheaf morphisms of the inverse and of the forward map of `tensorIsoObj F G`
compose to the identity of `(F ⊗ G).val`. -/
theorem inv_val_hom_val : (tensorIsoObj F G).inv.val ≫ (tensorIsoObj F G).hom.val =
    𝟙 ((F ⊗ G : X.Modules).val) :=
  congrArg (fun φ : (F ⊗ G : X.Modules) ⟶ F ⊗ G => φ.val) (tensorIsoObj F G).inv_hom_id

/-- **The section-level product is surjective on stalks.** The comparison
`Stacks.SectionTensorFormula.toTensorSection` is the sheafification unit followed by an
isomorphism, and the unit is a stalkwise bijection
(`Stacks.SectionProduct.pstalkHom_toSheafify_bijective`). -/
theorem surjective_pstalkHom_toTensorSection (x : X) :
    Function.Surjective (pstalkHom (toTensorSectionX F G) x) := by
  intro z
  have hw : pstalkHom (tensorIsoObj F G).hom.val x
      (pstalkHom (tensorIsoObj F G).inv.val x z) = z :=
    ((pstalkHom_comp (tensorIsoObj F G).inv.val (tensorIsoObj F G).hom.val x z).symm.trans
      (congrArg (fun φ : (F ⊗ G : X.Modules).val ⟶ (F ⊗ G : X.Modules).val =>
        pstalkHom φ x z) (inv_val_hom_val F G))).trans (pstalkHom_id _ x z)
  obtain ⟨v, hv⟩ := (pstalkHom_toSheafify_bijective (F.val ⊗ G.val) x).2
    (pstalkHom (tensorIsoObj F G).inv.val x z)
  exact ⟨v, (pstalkHom_comp _ _ x v).trans
    ((congrArg (pstalkHom (tensorIsoObj F G).hom.val x) hv).trans hw)⟩

end Surjective

section Generation

variable {F G : X.Modules}

/-- `Stacks.SectionProduct.pgerm` at a module on a scheme is the germ map. -/
theorem pgerm_eq_germ (M : X.Modules) (U : X.Opens) (x : X) (hx : x ∈ U) (t : Γ(M, U)) :
    pgerm M.val U x hx t = (M.presheaf.germ U x hx).hom t := rfl

/-- `Stacks.SectionProduct.pstalkHom_pgerm` for the comparison, in the
`AlgebraicGeometry.Scheme.Modules.presheaf` spelling that `Stacks.Ample.nonvanishingLocus` and
`Stacks.ModuleStalk.maximalSmul` are written over. -/
theorem pstalkHom_germ {P : PresheafOfModulesOfCommRing.{u} X.presheaf} {M : X.Modules}
    (φ : P ⟶ M.val) (U : X.Opens) (x : X) (hx : x ∈ U) (t : P.obj (op U)) :
    pstalkHom φ x (pgerm P U x hx t) =
      (M.presheaf.germ U x hx).hom (φ.app (op U) t) :=
  pstalkHom_pgerm φ x U hx t

/-- Surjectivity on stalks, in the `AlgebraicGeometry.Scheme.Modules.presheaf` spelling. -/
theorem exists_pstalkHom_eq (x : X)
    (w : TopCat.Presheaf.stalk (C := Ab.{u}) (F ⊗ G : X.Modules).presheaf x) :
    ∃ v, pstalkHom (toTensorSectionX F G) x v = w :=
  surjective_pstalkHom_toTensorSection F G x w

/-- **Local generation of the product of two sections.** Suppose `eF : Γ(F, W)` and `eG : Γ(G, W)`
locally generate, in the sense that every section of `F` (resp. of `G`) over an open inside `W` is
a multiple of the restriction of `eF` (resp. of `eG`). Then the germ at any point of `W` of
`Stacks.SectionTensorFormula.tensorSection F G eF eG` generates the stalk of `F ⊗ G` there.

The sheafification-unit stalk bijection
(`Stacks.SectionProduct.pstalkHom_toSheafify_bijective`) reduces the stalk of `F ⊗ G` to germs of
elements of the *sectionwise* tensor product, each of which is a finite sum of elementary tensors,
and the hypotheses then rewrite every elementary tensor as a multiple of `eF ⊗ eG`. No formula for
the monoidality isomorphism of sheafification is needed. -/
theorem exists_smul_germ_tensorSection {W : X.Opens} (eF : Γ(F, W)) (eG : Γ(G, W))
    (hF : ∀ (U : X.Opens) (i : U ⟶ W) (u : Γ(F, U)),
      ∃ r : Γ(X, U), u = r • F.presheaf.map i.op eF)
    (hG : ∀ (U : X.Opens) (i : U ⟶ W) (u : Γ(G, U)),
      ∃ r : Γ(X, U), u = r • G.presheaf.map i.op eG)
    {x : X} (hx : x ∈ W)
    (w : TopCat.Presheaf.stalk (C := Ab.{u}) (F ⊗ G : X.Modules).presheaf x) :
    ∃ r : X.presheaf.stalk x, w = r •
      (((F ⊗ G : X.Modules).presheaf.germ W x hx).hom
        (Stacks.SectionTensorFormula.tensorSection F G eF eG)) := by
  have main : ∀ (U : X.Opens) (hxU : x ∈ U) ξ,
      ∃ r : X.presheaf.stalk x,
        ((F ⊗ G : X.Modules).presheaf.germ U x hxU).hom
            ((toTensorSectionX F G).app (op U) ξ) =
          r • ((F ⊗ G : X.Modules).presheaf.germ W x hx).hom
            (Stacks.SectionTensorFormula.tensorSection F G eF eG) := by
    intro U hxU ξ
    induction ξ using TensorProduct.inductionOn with
    | add a b ha hb =>
      obtain ⟨r, hr⟩ := ha
      obtain ⟨r', hr'⟩ := hb
      refine ⟨r + r', ?_⟩
      rw [add_smul, ← hr, ← hr']
      exact (congrArg ((F ⊗ G : X.Modules).presheaf.germ U x hxU).hom
          (map_add (ConcreteCategory.hom ((toTensorSectionX F G).app (op U))) a b)).trans
        (map_add ((F ⊗ G : X.Modules).presheaf.germ U x hxU).hom _ _)
    | tmul m n =>
      have hxU' : x ∈ W ⊓ U := ⟨hx, hxU⟩
      obtain ⟨r, hr⟩ := hF (W ⊓ U) (homOfLE inf_le_left)
        (F.presheaf.map (homOfLE (inf_le_right : W ⊓ U ≤ U)).op m)
      obtain ⟨r', hr'⟩ := hG (W ⊓ U) (homOfLE inf_le_left)
        (G.presheaf.map (homOfLE (inf_le_right : W ⊓ U ≤ U)).op n)
      have hgoal : ((F ⊗ G : X.Modules).presheaf.germ U x hxU).hom
            (Stacks.SectionTensorFormula.tensorSection F G m n) =
          (X.presheaf.germ (W ⊓ U) x hxU').hom (r * r') •
            ((F ⊗ G : X.Modules).presheaf.germ W x hx).hom
              (Stacks.SectionTensorFormula.tensorSection F G eF eG) := by
        rw [← TopCat.Presheaf.germ_res_apply (C := Ab.{u}) (F ⊗ G : X.Modules).presheaf
            (homOfLE (inf_le_right : W ⊓ U ≤ U)) x hxU',
          Stacks.SectionTensorFormula.map_tensorSection F G
            (homOfLE (inf_le_right : W ⊓ U ≤ U)) m n,
          hr, hr', Stacks.SectionTensorFormula.tensorSection_smul_left,
          Stacks.SectionTensorFormula.tensorSection_smul_right, smul_smul,
          ← Stacks.SectionTensorFormula.map_tensorSection F G
            (homOfLE (inf_le_left : W ⊓ U ≤ W)) eF eG,
          Stacks.ModuleStalk.germ_smul,
          TopCat.Presheaf.germ_res_apply (C := Ab.{u}) (F ⊗ G : X.Modules).presheaf
            (homOfLE (inf_le_left : W ⊓ U ≤ W)) x hxU']
      exact ⟨_, hgoal⟩
  obtain ⟨v, hv⟩ := exists_pstalkHom_eq (F := F) (G := G) x w
  obtain ⟨U, hxU, ξ, rfl⟩ := exists_pgerm_eq _ v
  obtain ⟨r, hr⟩ := main U hxU ξ
  exact ⟨r, hv.symm.trans ((pstalkHom_germ (toTensorSectionX F G) U x hxU ξ).trans hr)⟩

end Generation

section Product

variable {F G : X.Modules}

/-- **A trivialization supplies the local-generation hypothesis** of
`Stacks.TensorSectionProduct.exists_smul_germ_tensorSection`: over any open inside the trivializing
open, every section is a multiple of the restricted basis section. -/
theorem exists_smul_res_basis {M : X.Modules} {V W : X.Opens}
    (t : Stacks.SheafDescent.Trivialization X.presheaf M.val V) (h : W ⟶ V)
    (U : X.Opens) (i : U ⟶ W) (u : Γ(M, U)) :
    ∃ r : Γ(X, U), u = r •
      M.presheaf.map i.op (M.presheaf.map h.op (Stacks.NonvanishingOpen.basis t)) := by
  refine ⟨Stacks.NonvanishingOpen.triv t (i ≫ h) u, ?_⟩
  rw [map_map]
  exact eq_triv_smul_res_basis t (i ≫ h) u

/-- `a • z` avoids `𝔪_x · M_x` exactly when `a` is a unit, provided `z` does. -/
theorem smul_notMem_maximalSmul_iff {M : X.Modules} {x : X} (a : X.presheaf.stalk x)
    {z : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x} (hz : z ∉ maximalSmul M x) :
    a • z ∉ maximalSmul M x ↔ IsUnit a := by
  rw [smul_mem_maximalSmul_iff a z]
  tauto

/-- The germ of the restricted basis section of a trivialization is nonvanishing. -/
private theorem germ_res_basis_notMem_maximalSmul {M : X.Modules} {V W : X.Opens}
    (t : Stacks.SheafDescent.Trivialization X.presheaf M.val V) (i : W ⟶ V) {x : X}
    (hxW : x ∈ W) :
    (M.presheaf.germ W x hxW).hom (M.presheaf.map i.op (Stacks.NonvanishingOpen.basis t)) ∉
      maximalSmul M x := by
  rw [TopCat.Presheaf.germ_res_apply (C := Ab.{u}) M.presheaf i x hxW]
  exact Stacks.NonvanishingOpen.notMem_maximalSmul_germ_basis t (leOfHom i hxW)

/-- **The product formula for nonvanishing, on a common trivializing open.** -/
theorem germ_tensorSection_notMem_maximalSmul_iff_of_triv [IsInvertibleModule X F]
    [IsInvertibleModule X G] {V₁ V₂ W : X.Opens}
    (tF : Stacks.SheafDescent.Trivialization X.presheaf F.val V₁)
    (tG : Stacks.SheafDescent.Trivialization X.presheaf G.val V₂)
    (i₁ : W ⟶ V₁) (i₂ : W ⟶ V₂) {x : X} (hxW : x ∈ W) (m : Γ(F, W)) (n : Γ(G, W)) :
    ((F ⊗ G : X.Modules).presheaf.germ W x hxW).hom
          (Stacks.SectionTensorFormula.tensorSection F G m n) ∉
        maximalSmul (F ⊗ G : X.Modules) x ↔
      ((F.presheaf.germ W x hxW).hom m ∉ maximalSmul F x ∧
        (G.presheaf.germ W x hxW).hom n ∉ maximalSmul G x) := by
  have : IsInvertibleModule X (F ⊗ G : X.Modules) :=
    AlgebraicGeometry.SheafOfModules.isInvertible_tensor X.presheaf (schemeSheafCondition X) F G
  have hz : ((F ⊗ G : X.Modules).presheaf.germ W x hxW).hom
      (Stacks.SectionTensorFormula.tensorSection F G
        (F.presheaf.map i₁.op (Stacks.NonvanishingOpen.basis tF))
        (G.presheaf.map i₂.op (Stacks.NonvanishingOpen.basis tG))) ∉
      maximalSmul (F ⊗ G : X.Modules) x :=
    notMem_maximalSmul_of_generates (F ⊗ G : X.Modules) x
      (fun w => exists_smul_germ_tensorSection _ _ (exists_smul_res_basis tF i₁)
        (exists_smul_res_basis tG i₂) hxW w)
  rw [eq_triv_smul_res_basis tF i₁ m, eq_triv_smul_res_basis tG i₂ n,
    Stacks.SectionTensorFormula.tensorSection_smul_left,
    Stacks.SectionTensorFormula.tensorSection_smul_right, smul_smul,
    Stacks.ModuleStalk.germ_smul, Stacks.ModuleStalk.germ_smul, Stacks.ModuleStalk.germ_smul,
    smul_notMem_maximalSmul_iff _ hz,
    smul_notMem_maximalSmul_iff _ (germ_res_basis_notMem_maximalSmul tF i₁ hxW),
    smul_notMem_maximalSmul_iff _ (germ_res_basis_notMem_maximalSmul tG i₂ hxW), map_mul]
  exact (Commute.all _ _).isUnit_mul_iff

/-- **The Stacks Tag 01CY remark `X_{m ⊗ n} = X_m ∩ X_n`, at the section-level product and over an
arbitrary open.** For `F` and `G` invertible and `m`, `n` sections of them over `U`, the product
`Stacks.SectionTensorFormula.tensorSection F G m n` fails to vanish at a point of `U` exactly where
both factors do. -/
theorem germ_tensorSection_notMem_maximalSmul_iff [IsInvertibleModule X F]
    [IsInvertibleModule X G] {U : X.Opens} (m : Γ(F, U)) (n : Γ(G, U)) {x : X} (hx : x ∈ U) :
    ((F ⊗ G : X.Modules).presheaf.germ U x hx).hom
          (Stacks.SectionTensorFormula.tensorSection F G m n) ∉
        maximalSmul (F ⊗ G : X.Modules) x ↔
      ((F.presheaf.germ U x hx).hom m ∉ maximalSmul F x ∧
        (G.presheaf.germ U x hx).hom n ∉ maximalSmul G x) := by
  obtain ⟨V₁, hxV₁, ⟨tF⟩⟩ := exists_trivialization_at F x
  obtain ⟨V₂, hxV₂, ⟨tG⟩⟩ := exists_trivialization_at G x
  have hxW : x ∈ U ⊓ (V₁ ⊓ V₂) := ⟨hx, hxV₁, hxV₂⟩
  have key := germ_tensorSection_notMem_maximalSmul_iff_of_triv tF tG
    (homOfLE (le_trans (inf_le_right : U ⊓ (V₁ ⊓ V₂) ≤ V₁ ⊓ V₂) inf_le_left))
    (homOfLE (le_trans (inf_le_right : U ⊓ (V₁ ⊓ V₂) ≤ V₁ ⊓ V₂) inf_le_right))
    hxW (F.presheaf.map (homOfLE (inf_le_left : U ⊓ (V₁ ⊓ V₂) ≤ U)).op m)
    (G.presheaf.map (homOfLE (inf_le_left : U ⊓ (V₁ ⊓ V₂) ≤ U)).op n)
  rwa [← Stacks.SectionTensorFormula.map_tensorSection,
    TopCat.Presheaf.germ_res_apply (C := Ab.{u}) (F ⊗ G : X.Modules).presheaf
      (homOfLE (inf_le_left : U ⊓ (V₁ ⊓ V₂) ≤ U)) x hxW,
    TopCat.Presheaf.germ_res_apply (C := Ab.{u}) F.presheaf
      (homOfLE (inf_le_left : U ⊓ (V₁ ⊓ V₂) ≤ U)) x hxW,
    TopCat.Presheaf.germ_res_apply (C := Ab.{u}) G.presheaf
      (homOfLE (inf_le_left : U ⊓ (V₁ ⊓ V₂) ≤ U)) x hxW] at key

/-- **`X_{m ⊗ n} = X_m ∩ X_n` for global sections**, at
`Stacks.SectionTensorFormula.tensorSection`. -/
@[ega "II 4.6.13.1" "(ii)"]
theorem nonvanishingLocus_tensorSection [IsInvertibleModule X F] [IsInvertibleModule X G]
    (m : Γ(F, ⊤)) (n : Γ(G, ⊤)) :
    nonvanishingLocus (F ⊗ G : X.Modules)
        (Stacks.SectionTensorFormula.tensorSection F G m n) =
      nonvanishingLocus F m ∩ nonvanishingLocus G n := by
  ext x
  exact germ_tensorSection_notMem_maximalSmul_iff m n (TopologicalSpace.Opens.mem_top x)

/-- **The consumer form.** If a global section `τ` of `F ⊗ G` restricts on `U` to the product of
`m : Γ(F, U)` and `n : Γ(G, U)`, then on `U` the nonvanishing locus of `τ` is cut out by the
nonvanishing of `m` and of `n`. This is the shape in which the output of [Stacks, Tag 01PW] — whose
conclusion is an equation `τ|_{X_σ} = m ⊗ σ|_{X_σ}` — is consumed. -/
theorem mem_nonvanishingLocus_iff_of_resTop_eq [IsInvertibleModule X F]
    [IsInvertibleModule X G] {U : X.Opens} (τ : Γ((F ⊗ G : X.Modules), ⊤))
    (m : Γ(F, U)) (n : Γ(G, U))
    (h : (F ⊗ G : X.Modules).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op τ =
      Stacks.SectionTensorFormula.tensorSection F G m n)
    {x : X} (hx : x ∈ U) :
    x ∈ nonvanishingLocus (F ⊗ G : X.Modules) τ ↔
      ((F.presheaf.germ U x hx).hom m ∉ maximalSmul F x ∧
        (G.presheaf.germ U x hx).hom n ∉ maximalSmul G x) := by
  rw [mem_nonvanishingLocus_iff,
    ← TopCat.Presheaf.Γgerm_res_apply (C := Ab.{u}) (i := homOfLE (le_top : U ≤ ⊤))
      (F ⊗ G : X.Modules).presheaf x hx τ, h]
  exact germ_tensorSection_notMem_maximalSmul_iff m n hx

end Product

end Stacks.TensorSectionProduct

end
