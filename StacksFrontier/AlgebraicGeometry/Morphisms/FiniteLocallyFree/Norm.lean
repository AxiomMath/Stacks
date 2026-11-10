module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.RingTheory.Norm.Projective
import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankSections
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic

/-!
# The norm of a finite locally free morphism

Following Stacks Section 0BCX, a *norm of degree `d`* for a finite morphism `π : X ⟶ Y` is a
multiplicative map of sheaves `Norm_π : π_* 𝒪_X ⟶ 𝒪_Y` such that the composite with `π^♯` is
`g ↦ g ^ d`, and such that the norm of a section vanishing at a point of `X` vanishes at its
image in `Y`.

Stacks Tag 0BD2 constructs such a norm for every finite locally free morphism of degree
`d ≥ 1`: on an affine open `V` of `Y` over which `π_* 𝒪_X` is free, a section `f` of `𝒪_X` over
`π ⁻¹ V` gives an endomorphism of that free module by multiplication, and `Norm_π(f)` is its
determinant. Because the pushforward is only *locally* free, the construction here uses the
determinant of a finite projective module, `Algebra.projectiveNorm`, which needs no basis
and therefore glues directly.

## Main definitions

* `Stacks.Norm.MorphismNormMap` is a multiplicative map of sheaves preserving pointwise
  vanishing, i.e. the unnamed notion of Stacks Section 0BCX without the degree condition.
* `Stacks.Norm.MorphismNorm` is a norm of a specified degree for a morphism of schemes, and
  `Stacks.Norm.HasNormOfDegree` asserts that one exists.
* `Stacks.Norm.IsDeterminantNorm` says that a norm map is given by the determinant of
  multiplication on every affine open trivialising the algebra, and
  `Stacks.Norm.DeterminantNorm` bundles that with the degree condition at every constant rank.
* `Stacks.Norm.affineLocalNorm` is the norm on an affine open, and `Stacks.Norm.normApp` is its
  extension to all opens.

## Main results

* `Stacks.Norm.finiteLocallyFreeNorm` is the canonical determinant norm of a finite locally free
  morphism, of arbitrary — possibly varying, possibly zero — rank.
* `Stacks.Norm.finiteLocallyFreeNormOfRank` specialises it to a norm of degree `d` for a
  morphism of positive constant rank `d`, which is Stacks Tag 0BD2.
* `Stacks.Norm.finiteLocallyFreeNorm_baseChange` and
  `Stacks.Norm.finiteLocallyFreeNormOfRank_baseChange`: the construction commutes with arbitrary
  base change.
* `Stacks.Norm.module_finite_and_projective_sections` and
  `Stacks.Norm.rankAtStalk_sections`: the sections of `𝒪_X` over `π ⁻¹ V`, for `V` an affine
  open of `Y`, are a finite projective `Γ(Y, V)`-algebra, of rank the degree of `π`.

## Implementation notes

The norm is built on affine opens and extended by
`TopCat.Sheaf.restrictHomEquivHom` along the basis of affine opens, since the target of the
norm is a sheaf of commutative monoids. Multiplicativity is therefore automatic, and the
extension is characterised on affine opens by `Stacks.Norm.normApp_affine`; every statement
about `normApp` on a general open is reduced to affine opens by
`Stacks.Norm.section_eq_of_affine_restrictions`.

Compatibility with base change is proved first on a pair of affine opens, where the relevant
square of rings is a pushout — Mathlib's `AlgebraicGeometry.isIso_pushoutSection_of_isAffineOpen`
— so that the algebraic base-change formula `Algebra.projectiveNorm_baseChange` applies.
The functoriality in the two opens is written with `AlgebraicGeometry.Scheme.Hom.appLE`, because
the two inverse-image opens are only propositionally equal.

Restriction compatibility of `affineLocalNorm` is the base-change statement for the identity
square, which avoids a second gluing argument.

## References

* [Stacks Project, Section 0BCX](https://stacks.math.columbia.edu/tag/0BCX)
* [Stacks Project, Tag 0BD2](https://stacks.math.columbia.edu/tag/0BD2)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.Norm

/-! ### The free sheaf of modules over a restriction -/

/-- The free sheaf of modules on `I` over an open subscheme is the image, under the equivalence
between its sheaves of modules and those over the restriction of the structure sheaf, of the
free sheaf of modules on `I` over that restriction. -/
noncomputable def finiteFreeOverEquivIsoX
    (X : Scheme.{u}) (U : X.Opens) (I : Type u) :
    SheafOfModules.free (R := ((U : Scheme).ringCatSheaf) ) I ≅
      (Scheme.Modules.overEquiv U).functor.obj
        (SheafOfModules.free (R := X.ringCatSheaf.over U) I) := by
  let F := (Scheme.Modules.overEquiv U).functor
  have : Limits.PreservesColimitsOfShape.{u, u} (Discrete I) F :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1} F
  exact @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F I this (Iso.refl _)


/-! ### Norms of a morphism of schemes, after Stacks Section 0BCX -/

/-- A multiplicative map from the direct image of the source's structure sheaf to the target's
structure sheaf, compatible with restriction and preserving vanishing in residue fields. No
degree is specified, which allows determinant norms of varying or zero rank. -/
structure MorphismNormMap {X Y : Scheme.{u}} (f : X ⟶ Y) where
  /-- The norm on sections over an open subset of the target. -/
  app (U : Y.Opens) : Γ(X, f ⁻¹ᵁ U) →* Γ(Y, U)
  /-- Norms commute with restriction to smaller open subsets. -/
  naturality {U V : Y.Opens} (i : V ⟶ U) (s : Γ(X, f ⁻¹ᵁ U)) :
    app V (X.presheaf.map ((Opens.map f.base).map i).op s) =
      Y.presheaf.map i.op (app U s)
  /-- If a section vanishes at a point, its norm vanishes at the image point. -/
  app_eq_zero_at_image {U : Y.Opens} (s : Γ(X, f ⁻¹ᵁ U)) (x : X)
      (hx : f x ∈ U) (hs : X.evaluation (f ⁻¹ᵁ U) x hx s = 0) :
    Y.evaluation U (f x) hx (app U s) = 0

/-- **Stacks Project, Section 0BCX.** A norm of degree `d` for a morphism of schemes: a
multiplicative map of sheaves preserving pointwise vanishing whose value on a function pulled
back from the target is its `d`-th power. -/
@[stacks 0BCX "norm of degree d"]
structure MorphismNorm {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) extends MorphismNormMap f where
  /-- The norm of a function pulled back from the target is its `d`-th power. -/
  app_pullback (U : Y.Opens) (g : Γ(Y, U)) : app U (f.app U g) = g ^ d

/-- A morphism admits a norm of degree `d`. -/
abbrev HasNormOfDegree {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) : Prop :=
  Nonempty (MorphismNorm f d)

/-! ### Sections of the structure sheaf over an affine open of the target -/

/-- For a finite locally free morphism `f : X ⟶ Y` and an affine open `U` of `Y`, the sections
of `𝒪_X` over `f ⁻¹ᵁ U` form a finite projective module over `Γ(Y, U)`. -/
theorem module_finite_and_projective_sections {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Stacks.Morphisms.IsFiniteLocallyFree f] (U : Y.affineOpens) :
    letI := (f.app U.1).hom.toAlgebra
    Module.Finite Γ(Y, U.1) Γ(X, f ⁻¹ᵁ (U : Y.Opens)) ∧
      Module.Projective Γ(Y, U.1) Γ(X, f ⁻¹ᵁ (U : Y.Opens)) := by
  let := (f.app U.1).hom.toAlgebra
  let : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  let : (Stacks.Morphisms.pushforwardStructureSheaf f).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom f _
  have h := AlgebraicGeometry.SheafOfModules.module_finite_and_projective_sections
    (Stacks.Morphisms.pushforwardStructureSheaf f) U
  exact ⟨h.1, h.2⟩

/-- For a finite locally free morphism `f : X ⟶ Y` of rank `d` and an affine open `U` of `Y`,
the sections of `𝒪_X` over `f ⁻¹ᵁ U` form a `Γ(Y, U)`-module of rank `d` at every prime. -/
theorem rankAtStalk_sections {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d] (U : Y.affineOpens) :
    letI := (f.app U.1).hom.toAlgebra
    ∀ p : PrimeSpectrum Γ(Y, U.1),
      Module.rankAtStalk Γ(X, f ⁻¹ᵁ (U : Y.Opens)) p = d := by
  let := (f.app U.1).hom.toAlgebra
  let : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  let : IsAffineHom f := inferInstance
  let : (Stacks.Morphisms.pushforwardStructureSheaf f).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom f _
  exact AlgebraicGeometry.SheafOfModules.rankAtStalk_sections
    (Stacks.Morphisms.pushforwardStructureSheaf f) d U

/-! ### The norm on an affine open -/

/-- The norm of a finite locally free morphism on an affine open of the target: the determinant
of multiplication on the finite projective algebra of sections. -/
@[ega "II 6.5.5" "special case", sga "3 V 4.1.1" "more general"]
def affineLocalNorm {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Stacks.Morphisms.IsFiniteLocallyFree f] (U : Y.affineOpens) :
    Γ(X, f ⁻¹ᵁ (U : Y.Opens)) →* Γ(Y, U.1) := by
  let := (f.app U.1).hom.toAlgebra
  let := (module_finite_and_projective_sections f U).1
  let := (module_finite_and_projective_sections f U).2
  exact Algebra.projectiveNorm Γ(Y, U.1)

/-- On an affine open over which the algebra of sections is free, the norm is the determinant of
multiplication in Mathlib's sense, `Algebra.norm`. -/
theorem affineLocalNorm_eq_norm_of_free {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Stacks.Morphisms.IsFiniteLocallyFree f] (U : Y.affineOpens) :
    letI := (f.app U.1).hom.toAlgebra
    ∀ (_ : Module.Free Γ(Y, U.1) Γ(X, f ⁻¹ᵁ (U : Y.Opens)))
      (_ : Module.Finite Γ(Y, U.1) Γ(X, f ⁻¹ᵁ (U : Y.Opens)))
      (s : Γ(X, f ⁻¹ᵁ (U : Y.Opens))),
      affineLocalNorm f U s = Algebra.norm Γ(Y, U.1) s := by
  let := (f.app U.1).hom.toAlgebra
  let := (module_finite_and_projective_sections f U).1
  let := (module_finite_and_projective_sections f U).2
  intro _ _ s
  change Algebra.projectiveNorm Γ(Y, U.1) s = _
  exact Algebra.projectiveNorm_eq_norm_of_free _ s

/-- The norm on affine opens is compatible with an arbitrary base change. -/
theorem affineLocalNorm_baseChange {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (g : Y' ⟶ Y)
    [Stacks.Morphisms.IsFiniteLocallyFree f] [Stacks.Morphisms.IsFiniteLocallyFree f']
    (sq : IsPullback g' f' f g) (U : Y.affineOpens) (V : Y'.affineOpens)
    (hV : V.1 ≤ g ⁻¹ᵁ U.1) (s : Γ(X, f ⁻¹ᵁ U.1)) :
    affineLocalNorm f' V (g'.appLE (f ⁻¹ᵁ U.1) (f' ⁻¹ᵁ V.1) (by
      intro x hx
      change f (g' x) ∈ U.1
      rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
      exact hV hx) s) = g.appLE U.1 V.1 hV (affineLocalNorm f U s) := by
  have heq : f' ⁻¹ᵁ V.1 = g' ⁻¹ᵁ (f ⁻¹ᵁ U.1) ⊓ f' ⁻¹ᵁ V.1 := by
    refine (inf_eq_right.mpr ?_).symm
    intro x hx
    change f (g' x) ∈ U.1
    rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
    exact hV hx
  have hpush := (isIso_pushoutSection_iff sq hV le_rfl heq).mp
    (isIso_pushoutSection_of_isAffineOpen sq hV le_rfl heq U.2 V.2 (U.2.preimage f))
  simp only [Scheme.Hom.appLE_eq_app] at hpush
  let := (f.app U.1).hom.toAlgebra
  let := (f'.app V.1).hom.toAlgebra
  let := (module_finite_and_projective_sections f U).1
  let := (module_finite_and_projective_sections f U).2
  let := (module_finite_and_projective_sections f' V).1
  let := (module_finite_and_projective_sections f' V).2
  exact Algebra.projectiveNorm_pushout _ _ _ _ hpush s

/-- The norm on affine opens commutes with restriction. -/
theorem affineLocalNorm_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Stacks.Morphisms.IsFiniteLocallyFree f]
    (U V : Y.affineOpens) (i : V.1 ⟶ U.1) (s : Γ(X, f ⁻¹ᵁ U.1)) :
    affineLocalNorm f V (X.presheaf.map ((Opens.map f.base).map i).op s) =
      Y.presheaf.map i.op (affineLocalNorm f U s) := by
  have sq : IsPullback (𝟙 X) f f (𝟙 Y) := .of_horiz_isIso ⟨by simp⟩
  have h := affineLocalNorm_baseChange f f (𝟙 X) (𝟙 Y) sq U V i.le s
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app] at h
  convert h using 1 <;> congr 2

/-! ### Extension to all opens -/

/-- The norm as a map of sheaves of commutative monoids, obtained by extending
`Stacks.Norm.affineLocalNorm` along the basis of affine opens. -/
def normPresheafMap {X Y : Scheme.{u}} (f : X ⟶ Y) [Stacks.Morphisms.IsFiniteLocallyFree f] :
    (Opens.map f.base).op ⋙ X.presheaf ⋙ forget₂ CommRingCat CommMonCat ⟶
      Y.presheaf ⋙ forget₂ CommRingCat CommMonCat := by
  let F := (Opens.map f.base).op ⋙ X.presheaf ⋙ forget₂ CommRingCat CommMonCat
  let G := (sheafCompose _ (forget₂ CommRingCat CommMonCat)).obj Y.sheaf
  let B : Y.affineOpens → Y.Opens := Subtype.val
  let α : (inducedFunctor B).op ⋙ F ⟶ (inducedFunctor B).op ⋙ G.obj :=
    { app U := CommMonCat.ofHom (affineLocalNorm f U.unop)
      naturality := by
        intro U V i
        ext s
        exact affineLocalNorm_naturality f U.unop V.unop i.unop.hom s }
  exact TopCat.Sheaf.restrictHomEquivHom F G
    (by simpa [B, Subtype.range_coe_subtype] using Y.isBasis_affineOpens) α

/-- On an affine open `U`, the component of `normPresheafMap f` at `U` is
`affineLocalNorm f U`. -/
theorem normPresheafMap_affine {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Stacks.Morphisms.IsFiniteLocallyFree f] (U : Y.affineOpens) :
    (normPresheafMap f).app (op U.1) = CommMonCat.ofHom (affineLocalNorm f U) := by
  apply TopCat.Sheaf.extend_hom_app

/-- The norm of a finite locally free morphism on an arbitrary open of the target. -/
def normApp {X Y : Scheme.{u}} (f : X ⟶ Y) [Stacks.Morphisms.IsFiniteLocallyFree f]
    (U : Y.Opens) : Γ(X, f ⁻¹ᵁ U) →* Γ(Y, U) :=
  ((normPresheafMap f).app (op U)).hom

/-- On an affine open `U`, `normApp f U` agrees with `affineLocalNorm f U`. -/
theorem normApp_affine {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Stacks.Morphisms.IsFiniteLocallyFree f] (U : Y.affineOpens)
    (s : Γ(X, f ⁻¹ᵁ U.1)) : normApp f U.1 s = affineLocalNorm f U s := by
  unfold normApp
  rw [normPresheafMap_affine]
  rfl

/-- The norm `normApp f` commutes with restriction along an inclusion of opens `V ⟶ U`. -/
theorem normApp_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Stacks.Morphisms.IsFiniteLocallyFree f] {U V : Y.Opens} (i : V ⟶ U)
    (s : Γ(X, f ⁻¹ᵁ U)) :
    normApp f V (X.presheaf.map ((Opens.map f.base).map i).op s) =
      Y.presheaf.map i.op (normApp f U s) :=
  congr($((normPresheafMap f).naturality i.op) s)

/-- Every point of an open lies in an affine open contained in it. -/
private theorem exists_affineOpen_mem_le {Y : Scheme.{u}} {U : Y.Opens} {y : Y} (hy : y ∈ U) :
    ∃ W : {W : Y.affineOpens // W.1 ≤ U}, y ∈ W.1.1 := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
  exact ⟨⟨⟨W, hW⟩, hWU⟩, hyW⟩

/-- Two sections of the structure sheaf agreeing on every affine open contained in their domain
are equal. -/
theorem section_eq_of_affine_restrictions {Y : Scheme.{u}} (U : Y.Opens) (s t : Γ(Y, U))
    (h : ∀ (V : Y.affineOpens) (i : V.1 ⟶ U),
      Y.presheaf.map i.op s = Y.presheaf.map i.op t) : s = t := by
  refine Y.sheaf.eq_of_locally_eq' (fun V : {V : Y.affineOpens // V.1 ≤ U} ↦ V.1.1) U
    (fun V ↦ homOfLE V.2) (fun x hx ↦ Opens.mem_iSup.mpr (exists_affineOpen_mem_le hx)) s t
    fun V ↦ h V.1 (homOfLE V.2)

/-! ### The three defining properties -/

/-- If a section `s` over `f ⁻¹ᵁ U` vanishes at a point `x`, then on an affine open `U` its norm
`affineLocalNorm f U s` vanishes at `f x`. -/
theorem affineLocalNorm_eq_zero_at_image {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Stacks.Morphisms.IsFiniteLocallyFree f] (U : Y.affineOpens)
    (s : Γ(X, f ⁻¹ᵁ U.1)) (x : X) (hx : f x ∈ U.1)
    (hs : X.evaluation (f ⁻¹ᵁ U.1) x hx s = 0) :
    Y.evaluation U.1 (f x) hx (affineLocalNorm f U s) = 0 := by
  let := (f.app U.1).hom.toAlgebra
  let := (module_finite_and_projective_sections f U).1
  let := (module_finite_and_projective_sections f U).2
  exact Algebra.projectiveNorm_eq_zero_of_field_hom _
    (Y.evaluation U.1 (f x) hx).hom (X.evaluation (f ⁻¹ᵁ U.1) x hx).hom
    (f.residueFieldMap x).hom
    (congrArg CommRingCat.Hom.hom (Scheme.evaluation_naturality f x hx).symm) s hs

/-- Evaluating the restriction of a section to `V` at a point of `V` equals evaluating the section
itself at that point. -/
theorem evaluation_restrict {X : Scheme.{u}} {U V : X.Opens}
    (i : V ⟶ U) (x : X) (hx : x ∈ V) (s : Γ(X, U)) :
    X.evaluation V x hx (X.presheaf.map i.op s) = X.evaluation U x (i.le hx) s := by
  change (X.presheaf.germ V x hx ≫ X.residue x) (X.presheaf.map i.op s) = _
  rw [← ConcreteCategory.comp_apply, ← Category.assoc, TopCat.Presheaf.germ_res]
  rfl

/-- If a section `s` over `f ⁻¹ᵁ U` vanishes at a point `x`, then its norm `normApp f U s` vanishes
at `f x`. -/
theorem normApp_eq_zero_at_image {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Stacks.Morphisms.IsFiniteLocallyFree f] {U : Y.Opens} (s : Γ(X, f ⁻¹ᵁ U)) (x : X)
    (hx : f x ∈ U) (hs : X.evaluation (f ⁻¹ᵁ U) x hx s = 0) :
    Y.evaluation U (f x) hx (normApp f U s) = 0 := by
  obtain ⟨⟨V, hVU⟩, hxV⟩ := exists_affineOpen_mem_le hx
  rw [← evaluation_restrict (homOfLE hVU) (f x) hxV, ← normApp_naturality, normApp_affine f V]
  exact affineLocalNorm_eq_zero_at_image f V _ x hxV
    ((evaluation_restrict ((Opens.map f.base).map (homOfLE hVU)) x hxV s).trans hs)

/-- For `f` finite locally free of constant rank `d` and an affine open `U`, the norm of the
pullback `f.app U s` of a section `s` is `s ^ d`. -/
theorem affineLocalNorm_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Stacks.Morphisms.IsFiniteLocallyFree f] (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d] (U : Y.affineOpens) (s : Γ(Y, U.1)) :
    affineLocalNorm f U (f.app U.1 s) = s ^ d := by
  let := (f.app U.1).hom.toAlgebra
  let := (module_finite_and_projective_sections f U).1
  let := (module_finite_and_projective_sections f U).2
  exact Algebra.projectiveNorm_algebraMap_of_rankAtStalk
    (R := Γ(Y, U.1)) (A := Γ(X, f ⁻¹ᵁ U.1)) (rankAtStalk_sections f d U) s

/-- For `f` finite locally free of constant rank `d`, the norm of the pullback `f.app U s` of a
section `s` over an open `U` is `s ^ d`. -/
theorem normApp_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Stacks.Morphisms.IsFiniteLocallyFree f] (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d] (U : Y.Opens) (s : Γ(Y, U)) :
    normApp f U (f.app U s) = s ^ d := by
  refine section_eq_of_affine_restrictions _ _ _ fun V i ↦ ?_
  rw [← normApp_naturality, normApp_affine f V, map_pow]
  have he := congr($(f.naturality i.op) s)
  simp only [ConcreteCategory.comp_apply] at he
  change f.app V.1 (Y.presheaf.map i.op s) =
    X.presheaf.map ((Opens.map f.base).map i).op (f.app U s) at he
  rw [← he, affineLocalNorm_pullback f d]

/-! ### Base change -/

/-- For a pullback square and an affine open `U` of `Y`, the norm of the base change `f'` over an
open `V ≤ g ⁻¹ᵁ U` of the pulled-back section equals the pullback along `g` of the norm over
`U`. -/
theorem normApp_baseChange_affine {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (g : Y' ⟶ Y)
    [Stacks.Morphisms.IsFiniteLocallyFree f] [Stacks.Morphisms.IsFiniteLocallyFree f']
    (sq : IsPullback g' f' f g) (U : Y.affineOpens) (V : Y'.Opens) (hV : V ≤ g ⁻¹ᵁ U.1)
    (s : Γ(X, f ⁻¹ᵁ U.1)) :
    normApp f' V (g'.appLE (f ⁻¹ᵁ U.1) (f' ⁻¹ᵁ V) (by
      intro x hx
      change f (g' x) ∈ U.1
      rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
      exact hV hx) s) = g.appLE U.1 V hV (normApp f U.1 s) := by
  refine section_eq_of_affine_restrictions _ _ _ fun W i ↦ ?_
  rw [← normApp_naturality, normApp_affine f' W, normApp_affine f U]
  simp only [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]
  exact affineLocalNorm_baseChange f f' g' g sq U W (i.le.trans hV) s

/-- For a pullback square, the norm of the base change `f'` over `g ⁻¹ᵁ U` of the pulled-back
section equals the pullback along `g` of the norm of `f` over `U`. -/
theorem normApp_baseChange {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (g : Y' ⟶ Y)
    [Stacks.Morphisms.IsFiniteLocallyFree f] [Stacks.Morphisms.IsFiniteLocallyFree f']
    (sq : IsPullback g' f' f g) (U : Y.Opens) (s : Γ(X, f ⁻¹ᵁ U)) :
    normApp f' (g ⁻¹ᵁ U) (g'.appLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ (g ⁻¹ᵁ U)) (by
      intro x hx
      change f (g' x) ∈ U
      rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
      exact hx) s) = g.app U (normApp f U s) := by
  refine Y'.sheaf.eq_of_locally_eq'
    (fun W : {W : Y.affineOpens // W.1 ≤ U} ↦ g ⁻¹ᵁ W.1.1) (g ⁻¹ᵁ U)
    (fun W ↦ (Opens.map g.base).map (homOfLE W.2)) ?_ _ _ ?_
  · intro y hy
    exact Opens.mem_iSup.mpr (exists_affineOpen_mem_le (y := g y) hy)
  intro W'
  have he := normApp_baseChange_affine f f' g' g sq W'.1 (g ⁻¹ᵁ W'.1.1) le_rfl
    (X.presheaf.map ((Opens.map f.base).map (homOfLE W'.2)).op s)
  rw [normApp_naturality, Scheme.Hom.appLE_eq_app] at he
  change Y'.presheaf.map ((Opens.map g.base).map (homOfLE W'.2)).op _ = Y'.presheaf.map _ _
  rw [← normApp_naturality, ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map,
    ← ConcreteCategory.comp_apply]
  have hg : g.app U ≫ Y'.presheaf.map ((Opens.map g.base).map (homOfLE W'.2)).op =
      Y.presheaf.map (homOfLE W'.2).op ≫ g.app W'.1.1 := (g.naturality _).symm
  rw [hg, ConcreteCategory.comp_apply]
  simpa only [← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE] using he

/-! ### Stacks Tag 0BD2 -/

/-- A norm map is the *determinant norm* if, on every affine open where the corresponding algebra
is finite free, its value is the determinant of multiplication. -/
def IsDeterminantNorm {X Y : Scheme.{u}} {f : X ⟶ Y} (N : MorphismNormMap f) : Prop :=
  ∀ (U : Y.Opens), IsAffineOpen U → IsAffineOpen (f ⁻¹ᵁ U) →
    letI := (f.app U).hom.toAlgebra
    ∀ (_ : Module.Free Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) (_ : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U))
      (s : Γ(X, f ⁻¹ᵁ U)), N.app U s = Algebra.norm Γ(Y, U) s

/-- A determinant norm, together with the degree condition at every constant rank the morphism
may have. The underlying map requires neither a constant nor a positive rank. -/
structure DeterminantNorm {X Y : Scheme.{u}} (f : X ⟶ Y) extends MorphismNormMap f where
  /-- On affine opens where the algebra is finite free, the norm is the determinant norm. -/
  isDeterminantNorm : IsDeterminantNorm toMorphismNormMap
  /-- At constant rank `d`, the norm of a pulled-back function is its `d`-th power. -/
  app_pullback (d : ℕ) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d]
    (U : Y.Opens) (g : Γ(Y, U)) : app U (f.app U g) = g ^ d

/-- A finite locally free morphism has a determinant norm which agrees with `affineLocalNorm f U`
on every affine open `U`. -/
theorem exists_determinantNorm {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Stacks.Morphisms.IsFiniteLocallyFree f] :
    ∃ N : DeterminantNorm f, ∀ (U : Y.affineOpens) (s : Γ(X, f ⁻¹ᵁ U.1)),
      N.app U.1 s = affineLocalNorm f U s := by
  refine ⟨{
    app := normApp f
    naturality := normApp_naturality f
    app_eq_zero_at_image := normApp_eq_zero_at_image f
    isDeterminantNorm := ?_
    app_pullback := normApp_pullback f }, fun U s ↦ normApp_affine f U s⟩
  intro U hU _ _ _ s
  rw [normApp_affine f ⟨U, hU⟩]
  exact affineLocalNorm_eq_norm_of_free f ⟨U, hU⟩ inferInstance inferInstance s

/-- **Stacks Project, Tag 0BD2.** The canonical determinant norm of a finite locally free
morphism, for an arbitrary — possibly varying, possibly zero — rank. -/
@[ega "II 6.5.1" "special case"]
def finiteLocallyFreeNorm {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Stacks.Morphisms.IsFiniteLocallyFree f] : DeterminantNorm f :=
  Classical.choose (exists_determinantNorm f)

/-- On an affine open `U`, `finiteLocallyFreeNorm f` agrees with `normApp f`. -/
theorem finiteLocallyFreeNorm_app_affine {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Stacks.Morphisms.IsFiniteLocallyFree f] (U : Y.affineOpens) (s : Γ(X, f ⁻¹ᵁ U.1)) :
    (finiteLocallyFreeNorm f).app U.1 s = normApp f U.1 s := by
  rw [normApp_affine]
  exact Classical.choose_spec (exists_determinantNorm f) U s

/-- On every open `U`, `finiteLocallyFreeNorm f` agrees with `normApp f`. -/
theorem finiteLocallyFreeNorm_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Stacks.Morphisms.IsFiniteLocallyFree f] (U : Y.Opens) (s : Γ(X, f ⁻¹ᵁ U)) :
    (finiteLocallyFreeNorm f).app U s = normApp f U s := by
  refine section_eq_of_affine_restrictions _ _ _ fun V i ↦ ?_
  rw [← (finiteLocallyFreeNorm f).naturality, ← normApp_naturality,
    finiteLocallyFreeNorm_app_affine]

/-- **Stacks Project, Tag 0BD2.** A finite locally free morphism of positive constant rank `d`
has a canonical norm of degree `d`, given on affine opens trivialising the algebra by the
determinant of multiplication. -/
@[sga "3 V 4.1.1" "more general"]
def finiteLocallyFreeNormOfRank {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d] (_hd : 0 < d) :
    {N : MorphismNorm f d // IsDeterminantNorm N.toMorphismNormMap} :=
  let := Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f d
  ⟨{ toMorphismNormMap := (finiteLocallyFreeNorm f).toMorphismNormMap
     app_pullback := (finiteLocallyFreeNorm f).app_pullback d },
    (finiteLocallyFreeNorm f).isDeterminantNorm⟩

/-- **Stacks Project, Tag 0BD2.** The canonical norm of a finite locally free morphism commutes
with arbitrary base change. -/
theorem finiteLocallyFreeNorm_baseChange {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (g : Y' ⟶ Y) [Stacks.Morphisms.IsFiniteLocallyFree f]
    (sq : IsPullback g' f' f g) :
    ∃ h' : Stacks.Morphisms.IsFiniteLocallyFree f',
      letI := h'
      ∀ (U : Y.Opens) (s : Γ(X, f ⁻¹ᵁ U)),
        (finiteLocallyFreeNorm f').app (g ⁻¹ᵁ U)
            (g'.appLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ (g ⁻¹ᵁ U)) (by
              intro x hx
              change f (g' x) ∈ U
              rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
              exact hx) s) = g.app U ((finiteLocallyFreeNorm f).app U s) := by
  let : Stacks.Morphisms.IsFiniteLocallyFree f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq inferInstance
  refine ⟨inferInstance, fun U s ↦ ?_⟩
  simpa only [finiteLocallyFreeNorm_app] using normApp_baseChange f f' g' g sq U s

/-- On every open `U`, the degree-`d` norm `finiteLocallyFreeNormOfRank f d hd` agrees with
`normApp f`. -/
theorem finiteLocallyFreeNormOfRank_app {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d] (hd : 0 < d) (U : Y.Opens)
    (s : Γ(X, f ⁻¹ᵁ U)) :
    (finiteLocallyFreeNormOfRank f d hd).1.app U s =
      letI := Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f d
      normApp f U s :=
  let := Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f d
  finiteLocallyFreeNorm_app f U s

/-- **Stacks Project, Tag 0BD2.** The degree-`d` norm of a finite locally free morphism of
positive constant rank `d` commutes with arbitrary base change: the canonical norm of the base
change agrees with the pullback of the degree-`d` norm. -/
theorem finiteLocallyFreeNormOfRank_baseChange {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y)
    (f' : X' ⟶ Y') (g' : X' ⟶ X) (g : Y' ⟶ Y) (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d] (hd : 0 < d)
    (sq : IsPullback g' f' f g) :
    ∃ h' : Stacks.Morphisms.IsFiniteLocallyFree f',
      letI := h'
      ∀ (U : Y.Opens) (s : Γ(X, f ⁻¹ᵁ U)),
        (finiteLocallyFreeNorm f').app (g ⁻¹ᵁ U)
            (g'.appLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ (g ⁻¹ᵁ U)) (by
              intro x hx
              change f (g' x) ∈ U
              rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
              exact hx) s) =
          g.app U ((finiteLocallyFreeNormOfRank f d hd).1.app U s) := by
  let : Stacks.Morphisms.IsFiniteLocallyFree f :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f d
  obtain ⟨h', hnorm⟩ := finiteLocallyFreeNorm_baseChange f f' g' g sq
  refine ⟨h', fun U s ↦ ?_⟩
  rw [finiteLocallyFreeNormOfRank_app f d hd U s, ← finiteLocallyFreeNorm_app f U s]
  exact hnorm U s

end Stacks.Norm

end
