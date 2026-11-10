module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackDescentAssembly
public import StacksFrontier.AlgebraicGeometry.Descent.InvariantQuasiAffineOpen
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineStableOpenSchematicLocus
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStack
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection
public import StacksFrontier.CategoryTheory.Sites.Localization.StacksOverSlice
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Polarized families form a stack (Stacks 0D40)

Let `D` be a descent datum of polarized families relative to a covering family `{V i ⟶ U}` of the
big fppf site. Forgetting the polarizations, `D` descends to a finitely presented, flat and proper
family `Y` of algebraic spaces over `U` (Stacks 0D1G). This file shows that the algebraic space of
`Y` is a scheme, so that `D` is effective
(`AlgebraicGeometry.PolarizedDescentScheme.isEffective`), and concludes both assertions of
Stacks 0D40.

The source deduces representability from the ampleness of the descended polarization (Stacks
0D3C, read through Stacks 0D32). Here the descended space is shown to be a scheme directly, point
by point, by exhibiting scheme charts: around a point of `Y`, take an affine open `W` of `U` and
an affine open `c` of some `V i` mapping flatly onto `W`. On the total space `X` of the member of
`D` over `c` the polarization `L` is ample (`c` is affine), and the gluing isomorphisms of `D`
give a descent datum of `L` along `c ⟶ W`. Every point of `X` lies in the nonvanishing locus of
an invariant section of a power of `L`
(`Stacks.Descent.InvariantSections.exists_isQuasiAffine_preimage_eq_preimage`), which is a
quasi-affine open of `X` stable for the datum. Its image in `Y` is then an open subspace which is a
scheme (`AlgebraicGeometry.Space.image_pointsMap_subset_schematicLocus_of_isQuasiAffine`, which
descends quasi-affine morphisms along the fpqc chart, Stacks 0247 and 0APL), so it lies in the
schematic locus of `Y` (Stacks 03JH), and an algebraic space whose schematic locus contains every
point is a scheme.

## Main results

* `AlgebraicGeometry.exists_isQuasiAffine_preimage_eq_of_descentDatum`: stable quasi-affine
  neighbourhoods on the total space of a member of a descent datum over an affine chart.
* `AlgebraicGeometry.mem_range_schematicLocus_of_descentDatum`: every point of the descended
  algebraic space lies in its schematic locus.
* `AlgebraicGeometry.SieveDescentDatum.isEffective_polarized`: descent data of polarized families
  relative to covering families are effective.
* `AlgebraicGeometry.polarizedProjection_isStack`: polarized families form a stack over the big
  fppf site.
* `AlgebraicGeometry.polarized_isStackInGroupoids`: **Stacks 0D40**, both assertions.
* `AlgebraicGeometry.polarizedStackUnconditional_isStack`: the stack condition for `𝒫olarized`
  read over the big fppf site of `Spec ℤ`.

## References

* [Stacks Project, Tag 0D40](https://stacks.math.columbia.edu/tag/0D40)
* [Stacks Project, Tag 0D1G](https://stacks.math.columbia.edu/tag/0D1G)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
* [Stacks Project, Tag 06NV](https://stacks.math.columbia.edu/tag/06NV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor (Fiber IsPreFibered pullbackFiber)
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat (pullHom)

universe w u

namespace CategoryTheory.Functor.SieveDescentDatum

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

variable {𝒞 : Type*} [Category 𝒞] {𝒳 : Type*} [Category 𝒳] {p : 𝒳 ⥤ 𝒞} [p.IsFibered]
  {U : 𝒞} {R : Sieve U} (D : SieveDescentDatum p R)

/-- The gluing morphism of a descent datum at one arrow `f` of the sieve and two morphisms
`ε ε' : Z ⟶ V` with `ε ≫ f = ε' ≫ f`: the gluing isomorphism followed by the chosen cartesian
lift of `ε'`. It lies over `ε'`. -/
abbrev glueHom ⦃V Z : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) (ε ε' : Z ⟶ V) (heq : ε ≫ f = ε' ≫ f) :
    (pullbackFiber p (D.obj f hf) ε).1 ⟶ (D.obj f hf).1 :=
  Fiber.fiberInclusion.map (D.iso hf hf ε ε' heq).hom ≫ IsPreFibered.pullbackMap (D.obj f hf).2 ε'

/-- The gluing morphism at `ε` and `ε'` lies over `ε'`. -/
instance ⦃V Z : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) (ε ε' : Z ⟶ V) (heq : ε ≫ f = ε' ≫ f) :
    p.IsHomLift ε' (D.glueHom hf ε ε' heq) := by
  have : p.IsHomLift (𝟙 Z) (Fiber.fiberInclusion.map (D.iso hf hf ε ε' heq).hom) :=
    (D.iso hf hf ε ε' heq).hom.2
  have h : p.IsHomLift (𝟙 Z ≫ ε') (D.glueHom hf ε ε' heq) := by
    unfold glueHom
    infer_instance
  rwa [Category.id_comp] at h

/-- At two equal morphisms the gluing morphism is the chosen cartesian lift. -/
theorem glueHom_of_eq ⦃V Z : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) (ε ε' : Z ⟶ V) (h : ε = ε')
    (heq : ε ≫ f = ε' ≫ f) :
    D.glueHom hf ε ε' heq = IsPreFibered.pullbackMap (D.obj f hf).2 ε := by
  subst h
  rw [glueHom, D.iso_self hf ε heq]
  exact Category.id_comp _

/-- The gluing morphism only depends on its second morphism up to equality. -/
theorem glueHom_congr ⦃V Z : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) (ε ε'₁ ε'₂ : Z ⟶ V) (h : ε'₁ = ε'₂)
    (heq₁ : ε ≫ f = ε'₁ ≫ f) (heq₂ : ε ≫ f = ε'₂ ≫ f) :
    D.glueHom hf ε ε'₁ heq₁ = D.glueHom hf ε ε'₂ heq₂ := by
  subst h
  rfl

/-- The gluing morphisms compose with the gluing isomorphisms (the cocycle condition). -/
theorem iso_hom_glueHom ⦃V Z : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) (ε ε' ε'' : Z ⟶ V)
    (h₁ : ε ≫ f = ε' ≫ f) (h₂ : ε' ≫ f = ε'' ≫ f) :
    Fiber.fiberInclusion.map (D.iso hf hf ε ε' h₁).hom ≫ D.glueHom hf ε' ε'' h₂ =
      D.glueHom hf ε ε'' (h₁.trans h₂) := by
  rw [glueHom, glueHom, ← Category.assoc, ← Functor.map_comp, D.cocycle]

/-- The restriction morphism `(γ ≫ ε)^* x ⟶ ε^* x` along `γ`, through the contraction of the
iterated chosen pullbacks. It lies over `γ`. -/
abbrev restrictHom ⦃V Z Z' : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) (ε : Z ⟶ V) (γ : Z' ⟶ Z) :
    (pullbackFiber p (D.obj f hf) (γ ≫ ε)).1 ⟶ (pullbackFiber p (D.obj f hf) ε).1 :=
  Fiber.fiberInclusion.map (pullbackFiberCompIso (D.obj f hf) ε γ).inv ≫
    IsPreFibered.pullbackMap (pullbackFiber p (D.obj f hf) ε).2 γ

/-- The restriction morphism along `γ` lies over `γ`. -/
instance ⦃V Z Z' : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) (ε : Z ⟶ V) (γ : Z' ⟶ Z) :
    p.IsHomLift γ (D.restrictHom hf ε γ) := by
  have : p.IsHomLift (𝟙 Z')
      (Fiber.fiberInclusion.map (pullbackFiberCompIso (D.obj f hf) ε γ).inv) :=
    (pullbackFiberCompIso (D.obj f hf) ε γ).inv.2
  have h : p.IsHomLift (𝟙 Z' ≫ γ) (D.restrictHom hf ε γ) := by
    unfold restrictHom
    infer_instance
  rwa [Category.id_comp] at h

/-- The restriction morphism along `γ` followed by the chosen cartesian lift of `ε` is the chosen
cartesian lift of `γ ≫ ε`. -/
theorem restrictHom_pullbackMap ⦃V Z Z' : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) (ε : Z ⟶ V)
    (γ : Z' ⟶ Z) :
    D.restrictHom hf ε γ ≫ IsPreFibered.pullbackMap (D.obj f hf).2 ε =
      IsPreFibered.pullbackMap (D.obj f hf).2 (γ ≫ ε) := by
  rw [restrictHom, Category.assoc]
  exact pullbackFiberCompIso_inv_fac (D.obj f hf) ε γ

/-- The restriction morphism along `γ` followed by the gluing morphism at `ε` and `ε'` is the
gluing morphism at `γ ≫ ε` and `γ ≫ ε'`. -/
theorem restrictHom_glueHom ⦃V Z Z' : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) (ε ε' : Z ⟶ V)
    (heq : ε ≫ f = ε' ≫ f) (γ : Z' ⟶ Z) :
    D.restrictHom hf ε γ ≫ D.glueHom hf ε ε' heq =
      D.glueHom hf (γ ≫ ε) (γ ≫ ε') (by rw [Category.assoc, Category.assoc, heq]) := by
  simp only [restrictHom, glueHom, Category.assoc]
  exact D.pullbackFiberCompIso_inv_glue hf hf ε ε' heq γ

/-- A gluing isomorphism followed by a restriction and a chosen cartesian lift is a gluing
morphism. -/
theorem iso_restrictHom_pullbackMap ⦃V Z Z' : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) (ε₀ : Z' ⟶ V)
    (ε : Z ⟶ V) (γ : Z' ⟶ Z) (h : ε₀ ≫ f = (γ ≫ ε) ≫ f) :
    Fiber.fiberInclusion.map (D.iso hf hf ε₀ (γ ≫ ε) h).hom ≫ D.restrictHom hf ε γ ≫
        IsPreFibered.pullbackMap (D.obj f hf).2 ε = D.glueHom hf ε₀ (γ ≫ ε) h := by
  rw [D.restrictHom_pullbackMap]

/-- A gluing isomorphism followed by a restriction and a gluing morphism is a gluing
morphism. -/
theorem iso_restrictHom_glueHom ⦃V Z Z' : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) (ε₀ : Z' ⟶ V)
    (ε ε' : Z ⟶ V) (heq : ε ≫ f = ε' ≫ f) (γ : Z' ⟶ Z) (h : ε₀ ≫ f = (γ ≫ ε) ≫ f) :
    Fiber.fiberInclusion.map (D.iso hf hf ε₀ (γ ≫ ε) h).hom ≫ D.restrictHom hf ε γ ≫
        D.glueHom hf ε ε' heq =
      D.glueHom hf ε₀ (γ ≫ ε') (h.trans (by rw [Category.assoc, Category.assoc, heq])) := by
  rw [D.restrictHom_glueHom, D.iso_hom_glueHom]

/-- A gluing isomorphism followed by a restriction along `γ` lies over `γ`. -/
theorem isHomLift_iso_restrictHom ⦃V Z Z' : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) (ε₀ : Z' ⟶ V)
    (ε : Z ⟶ V) (γ : Z' ⟶ Z) (h : ε₀ ≫ f = (γ ≫ ε) ≫ f) :
    p.IsHomLift γ (Fiber.fiberInclusion.map (D.iso hf hf ε₀ (γ ≫ ε) h).hom ≫
      D.restrictHom hf ε γ) := by
  have : p.IsHomLift (𝟙 Z') (Fiber.fiberInclusion.map (D.iso hf hf ε₀ (γ ≫ ε) h).hom) :=
    (D.iso hf hf ε₀ (γ ≫ ε) h).hom.2
  have h' : p.IsHomLift (𝟙 Z' ≫ γ)
      (Fiber.fiberInclusion.map (D.iso hf hf ε₀ (γ ≫ ε) h).hom ≫ D.restrictHom hf ε γ) :=
    inferInstance
  rwa [Category.id_comp] at h'

end CategoryTheory.Functor.SieveDescentDatum

namespace AlgebraicGeometry

open CategoryTheory.Functor.SieveDescentDatum

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

variable {B : BigFppfSite.{u}}

/-- `pullHom` of a transfer of polarizations along the morphism of total spaces of a morphism
`k` of polarized families, read at two composites. -/
theorem PolarizedFamily.pullHom_lineBundleTransfer_of_eq {w w' x y : PolarizedFamily B}
    (m : w ⟶ x) (n : w ⟶ y) (k : w' ⟶ w) (a : w' ⟶ x) (b : w' ⟶ y) (ha : k ≫ m = a)
    (hb : k ≫ n = b) (h₁ : k.totalMap ≫ m.totalMap = a.totalMap)
    (h₂ : k.totalMap ≫ n.totalMap = b.totalMap) :
    pullHom (F := modulePullbackPseudofunctor) (PolarizedFamily.lineBundleTransfer m n).hom
        k.totalMap a.totalMap b.totalMap h₁ h₂ =
      (PolarizedFamily.lineBundleTransfer a b).hom := by
  subst ha hb
  exact PolarizedFamily.pullHom_lineBundleTransfer m n k

/-- **The transfer of polarizations along two morphisms of polarized families is a cocycle.**
Restricted along three morphisms `k₁₂ k₂₃ k₁₃` into the common source, at composites `a`, `b`,
`d`, the transfers compose. -/
theorem PolarizedFamily.pullHom_lineBundleTransfer_cocycle {w w' x : PolarizedFamily B}
    (m n : w ⟶ x) (k₁₂ k₂₃ k₁₃ : w' ⟶ w) (a b d : w' ⟶ x) (h₁₂₁ : k₁₂ ≫ m = a)
    (h₁₂₂ : k₁₂ ≫ n = b) (h₂₃₁ : k₂₃ ≫ m = b) (h₂₃₂ : k₂₃ ≫ n = d) (h₁₃₁ : k₁₃ ≫ m = a)
    (h₁₃₂ : k₁₃ ≫ n = d) (e₁₂₁ : k₁₂.totalMap ≫ m.totalMap = a.totalMap)
    (e₁₂₂ : k₁₂.totalMap ≫ n.totalMap = b.totalMap) (e₂₃₁ : k₂₃.totalMap ≫ m.totalMap = b.totalMap)
    (e₂₃₂ : k₂₃.totalMap ≫ n.totalMap = d.totalMap) (e₁₃₁ : k₁₃.totalMap ≫ m.totalMap = a.totalMap)
    (e₁₃₂ : k₁₃.totalMap ≫ n.totalMap = d.totalMap) :
    pullHom (F := modulePullbackPseudofunctor) (PolarizedFamily.lineBundleTransfer m n).hom
        k₁₂.totalMap a.totalMap b.totalMap e₁₂₁ e₁₂₂ ≫
      pullHom (F := modulePullbackPseudofunctor) (PolarizedFamily.lineBundleTransfer m n).hom
        k₂₃.totalMap b.totalMap d.totalMap e₂₃₁ e₂₃₂ =
    pullHom (F := modulePullbackPseudofunctor) (PolarizedFamily.lineBundleTransfer m n).hom
      k₁₃.totalMap a.totalMap d.totalMap e₁₃₁ e₁₃₂ := by
  have key : ∀ (k : w' ⟶ w) (a b : w' ⟶ x) (ha : k ≫ m = a) (hb : k ≫ n = b)
      (e₁ : k.totalMap ≫ m.totalMap = a.totalMap) (e₂ : k.totalMap ≫ n.totalMap = b.totalMap),
      Scheme.Modules.pullHomIso (PolarizedFamily.lineBundleTransfer m n) k.totalMap a.totalMap
        b.totalMap e₁ e₂ = PolarizedFamily.lineBundleTransfer a b := fun k a b ha hb e₁ e₂ =>
    Iso.ext ((Scheme.Modules.pullHomIso_hom _ _ _ _ _ _).trans
      (PolarizedFamily.pullHom_lineBundleTransfer_of_eq m n k a b ha hb e₁ e₂))
  have h := congrArg Iso.hom
    (((congrArg₂ Iso.trans (key k₁₂ a b h₁₂₁ h₁₂₂ e₁₂₁ e₁₂₂)
        (key k₂₃ b d h₂₃₁ h₂₃₂ e₂₃₁ e₂₃₂)).trans
      (Iso.ext (PolarizedFamily.lineBundleTransfer_comp a b d))).trans
      (key k₁₃ a d h₁₃₁ h₁₃₂ e₁₃₁ e₁₃₂).symm)
  rwa [Iso.trans_hom, Scheme.Modules.pullHomIso_hom, Scheme.Modules.pullHomIso_hom,
    Scheme.Modules.pullHomIso_hom] at h

/-- **Invariant quasi-affine neighbourhoods for the transfer of polarizations.**
`Stacks.Descent.InvariantSections.exists_isQuasiAffine_preimage_eq_preimage` for the transfer of
polarizations through two morphisms `m n : w ⟶ x` of polarized families, whose cocycle condition
is read on three morphisms `s₁₂ s₂₃ s₁₃` into `w`. -/
theorem PolarizedFamily.exists_isQuasiAffine_preimage_eq_preimage {x w w₃ : PolarizedFamily B}
    (m n : w ⟶ x) (s₁₂ s₂₃ s₁₃ : w₃ ⟶ w) (T₁ T₂ T₃ : w₃ ⟶ x) (e₁ : s₁₂ ≫ m = T₁)
    (e₂ : s₁₂ ≫ n = T₂) (e₃ : s₂₃ ≫ m = T₂) (e₄ : s₂₃ ≫ n = T₃) (e₅ : s₁₃ ≫ m = T₁)
    (e₆ : s₁₃ ≫ n = T₃) {W V : Scheme.{u}} [IsAffine W] [IsAffine V] (q : V ⟶ W) [Flat q]
    (π : x.total ⟶ V) [QuasiSeparatedSpace x.total] [CompactSpace w.total]
    [QuasiSeparatedSpace w.total] [Stacks.Ample.IsInvertibleModule x.total x.lineBundle]
    (hL : Stacks.Ample.IsAmple x.total x.lineBundle) (k₁ : w.total ⟶ V)
    (sq₂ : IsPullback n.totalMap k₁ (π ≫ q) q)
    (hW : m.totalMap ≫ π ≫ q = n.totalMap ≫ π ≫ q) (Δ : x.total ⟶ w.total)
    (hΔ₁ : Δ ≫ m.totalMap = 𝟙 _) (hΔ₂ : Δ ≫ n.totalMap = 𝟙 _) (k₃ : w₃.total ⟶ V)
    (sq₃ : IsPullback s₂₃.totalMap k₃ (n.totalMap ≫ π ≫ q) q) (hk₁₂ : s₁₂.totalMap ≫ k₁ = k₃)
    (hk₁₃ : s₁₃.totalMap ≫ k₁ = k₃) (ξ : x.total) :
    ∃ T : x.total.Opens, ξ ∈ T ∧ (T : Scheme.{u}).IsQuasiAffine ∧
      m.totalMap ⁻¹ᵁ T = n.totalMap ⁻¹ᵁ T := by
  have tm : ∀ {a b d : PolarizedFamily B} {φ : a ⟶ b} {ψ : b ⟶ d} {χ : a ⟶ d},
      φ ≫ ψ = χ → φ.totalMap ≫ ψ.totalMap = χ.totalMap := fun h =>
    (PolarizedFamily.comp_totalMap _ _).symm.trans (congrArg PolarizedFamily.Hom.totalMap h)
  have hc := PolarizedFamily.pullHom_lineBundleTransfer_cocycle m n s₁₂ s₂₃ s₁₃ T₁ T₂ T₃ e₁ e₂ e₃
    e₄ e₅ e₆ (tm e₁) (tm e₂) (tm e₃) (tm e₄) (tm e₅) (tm e₆)
  refine Stacks.Descent.InvariantSections.exists_isQuasiAffine_preimage_eq_preimage q π
    x.lineBundle m.totalMap n.totalMap k₁ sq₂ hW (PolarizedFamily.lineBundleTransfer m n) hL Δ
    hΔ₁ hΔ₂ s₁₂.totalMap s₂₃.totalMap s₁₃.totalMap k₃ sq₃ T₁.totalMap T₂.totalMap T₃.totalMap
    (tm e₁) (tm e₂) (tm e₃) (tm e₄) (tm e₅) (tm e₆) hk₁₂ hk₁₃ ?_ ξ
  with_reducible exact hc

/-- A scheme of the site equal to one whose underlying scheme is affine has affine underlying
scheme. -/
theorem isAffine_inclusion_of_eq {b b' : B.Schemes} (h : b = b')
    [IsAffine (B.inclusion.obj b')] : IsAffine (B.inclusion.obj b) := by
  subst h
  assumption

/-- Around every point of the source of a flat morphism locally of finite presentation there is an
affine open whose image is an affine open of the target. -/
theorem exists_isAffineOpen_image_eq_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [LocallyOfFinitePresentation f] (x : X) :
    ∃ (V : X.Opens) (W : Y.Opens), IsAffineOpen V ∧ IsAffineOpen W ∧ x ∈ V ∧
      f '' (V : Set X) = (W : Set Y) := by
  obtain ⟨W₀, hW₀, hfx, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := f x) (U := ⊤) trivial
  obtain ⟨V₀, hV₀, hx, hV₀sub⟩ :=
    exists_isAffineOpen_mem_and_subset (x := x) (U := f ⁻¹ᵁ W₀) hfx
  let O : Y.Opens := ⟨f '' (V₀ : Set X), f.isOpenMap _ V₀.isOpen⟩
  obtain ⟨r, hle, hmem⟩ := hW₀.exists_basicOpen_le (V := O ⊓ W₀)
    ⟨f x, ⟨⟨x, hx, rfl⟩, hfx⟩⟩ hfx
  refine ⟨V₀ ⊓ f ⁻¹ᵁ Y.basicOpen r, Y.basicOpen r, ?_, hW₀.basicOpen r, ⟨hx, hmem⟩, ?_⟩
  · have hle' : V₀ ≤ f ⁻¹ᵁ W₀ := hV₀sub
    rw [Scheme.preimage_basicOpen, ← Scheme.basicOpen_res X _ (homOfLE hle').op]
    exact hV₀.basicOpen _
  · apply subset_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact hv.2
    · intro z hz
      obtain ⟨v, hv, rfl⟩ := (hle hz).1
      exact ⟨v, ⟨hv, hz⟩, rfl⟩

/-- The identification of two equal schemes of the site is an isomorphism of schemes. -/
theorem isIso_inclusion_map_eqToHom {b b' : B.Schemes} (h : b = b') :
    IsIso (B.inclusion.map (eqToHom h)) := by
  subst h
  rw [eqToHom_refl, CategoryTheory.Functor.map_id]
  infer_instance

/-- The identifications of two equal schemes of the site in the two directions are inverse on
points. -/
theorem inclusion_map_eqToHom_apply_symm {b b' : B.Schemes} (h : b = b')
    (z : B.inclusion.obj b') :
    (B.inclusion.map (eqToHom h)) ((B.inclusion.map (eqToHom h.symm)) z) = z := by
  subst h
  simp

/-- A morphism whose composite with a monomorphism has a property stable under base change has
the property. -/
@[ega "I 5.5.12" "special case"]
theorem _root_.CategoryTheory.MorphismProperty.of_comp_mono {C : Type*} [Category C]
    (P : MorphismProperty C) [P.IsStableUnderBaseChange] {X W U : C} (q : X ⟶ W) (w : W ⟶ U)
    [Mono w] (h : P (q ≫ w)) : P q := by
  have hsq : IsPullback (𝟙 X) q (q ≫ w) w := by
    simpa using isPullback_comp_mono (IsPullback.id_horiz q) w
  exact MorphismProperty.of_isPullback hsq h

/-- The morphism of bases of a morphism over `f` into a family of algebraic spaces, read as a
morphism of schemes, is `f` up to the identifications of the bases. -/
theorem toScheme_map_hom_right_of_isHomLift {V U : B.Schemes} {x : PolarizedFamily B}
    (hx : x.base = V) {Y : CartesianProperFlatSpaces B integerBase B.contains_integerBase}
    (hY : (polarizedFamiliesProperFlatProjection B).obj Y = U) (f : V ⟶ U)
    (ζ : (forgetPolarization B).obj x ⟶ Y)
    [(polarizedFamiliesProperFlatProjection B).IsHomLift f ζ] :
    (BigFppfOver.toScheme B integerBase B.contains_integerBase).map ζ.1.hom.right =
      B.inclusion.map (eqToHom hx) ≫ B.inclusion.map f ≫ B.inclusion.map (eqToHom hY.symm) := by
  change B.inclusion.map ((polarizedFamiliesProperFlatProjection B).map ζ) = _
  rw [IsHomLift.fac' (polarizedFamiliesProperFlatProjection B) f ζ, Functor.map_comp,
    Functor.map_comp]
  rfl

/-- The morphism of bases of a morphism over `f` into a family of algebraic spaces over the base
of `Y`, read as a morphism of schemes. -/
theorem toScheme_map_hom_right_of_isHomLift' {V : B.Schemes} {x : PolarizedFamily B}
    (hx : x.base = V) {Y : CartesianProperFlatSpaces B integerBase B.contains_integerBase}
    (f : V ⟶ (polarizedFamiliesProperFlatProjection B).obj Y)
    (ζ : (forgetPolarization B).obj x ⟶ Y)
    [(polarizedFamiliesProperFlatProjection B).IsHomLift f ζ] :
    (BigFppfOver.toScheme B integerBase B.contains_integerBase).map ζ.1.hom.right =
      B.inclusion.map (eqToHom hx) ≫ B.inclusion.map f := by
  rw [toScheme_map_hom_right_of_isHomLift hx rfl f ζ, eqToHom_refl,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- A cartesian square over a base square, read over one of its corners through an isomorphism. -/
theorem isPullback_comp_of_isPullback_base {X X₂ Vx Vc V₂ U : Scheme.{u}} (M G : X₂ ⟶ X)
    (tb : X ⟶ Vx) (e : Vx ≅ Vc) (k₂ : X₂ ⟶ V₂) (p₁ p₂ : V₂ ⟶ Vc) (gs : Vc ⟶ U)
    (r : Vx ⟶ U) (hr : r = e.hom ≫ gs) (hM : M ≫ tb ≫ e.hom = k₂ ≫ p₁)
    (hG : IsPullback G k₂ (tb ≫ e.hom) p₂) (hb : IsPullback p₁ p₂ gs gs) :
    IsPullback G (M ≫ tb) (tb ≫ r) r := by
  subst hr
  have h1 := hG.paste_vert hb.flip
  rw [← hM] at h1
  refine IsPullback.of_iso h1 (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_ ?_ <;>
    simp

/-- **The chart of the descended space over an affine open of the base.** For a morphism `ζ` over
`g` from the family underlying `x` to a family `Y`, and an affine open `W` of the base of `Y` onto
which `g` maps `c` flatly, the morphism of bases of `ζ` factors through the object of the site cut
out by `W`, by a surjective flat morphism of finite presentation of affines. -/
theorem exists_factor_hom_right_of_isHomLift {Y : CartesianProperFlatSpaces B integerBase
      B.contains_integerBase} {x : PolarizedFamily B} {c : B.Schemes} (hx : x.base = c)
    [IsAffine (B.inclusion.obj c)] {g : c ⟶ (polarizedFamiliesProperFlatProjection B).obj Y}
    (W : (B.inclusion.obj ((polarizedFamiliesProperFlatProjection B).obj Y)).Opens)
    [IsAffine W.toScheme] (hrangeg : Set.range (B.inclusion.map g) = (W : Set _))
    [Flat (B.inclusion.map g)] [LocallyOfFinitePresentation (B.inclusion.map g)]
    (ζ : (forgetPolarization B).obj x ⟶ Y)
    [(polarizedFamiliesProperFlatProjection B).IsHomLift g ζ] :
    ∃ (a' : BigFppfOver B integerBase B.contains_integerBase) (w' : a' ⟶ Y.obj.obj.right)
      (q' : ((forgetPolarization B).obj x).obj.obj.right ⟶ a'),
      _root_.AlgebraicGeometry.IsOpenImmersion
          ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map w') ∧
        IsAffine ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj a') ∧
        IsAffine ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj
          ((forgetPolarization B).obj x).obj.obj.right) ∧
        Flat ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map q') ∧
        Surjective ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map q') ∧
        LocallyOfFinitePresentation
          ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map q') ∧
        q' ≫ w' = ζ.1.hom.right := by
  have hmr := toScheme_map_hom_right_of_isHomLift' hx g ζ
  have := isIso_inclusion_map_eqToHom hx
  obtain ⟨a', w', hw'oi, hw'range, hw'univ⟩ := exists_restrict_bigFppfOver Y.obj.obj.right W
  have := hw'oi
  have hrange' : Set.range ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map
      ζ.1.hom.right) ⊆
        (W : Set (B.inclusion.obj ((polarizedFamiliesProperFlatProjection B).obj Y))) := by
    rw [hmr, ← hrangeg]
    rintro _ ⟨z, rfl⟩
    exact ⟨_, (Scheme.Hom.comp_apply _ _ z).symm⟩
  obtain ⟨q', hq'⟩ := hw'univ _ hrange'
  have hcomp : (BigFppfOver.toScheme B integerBase B.contains_integerBase).map q' ≫
      (BigFppfOver.toScheme B integerBase B.contains_integerBase).map w' =
      B.inclusion.map (eqToHom hx) ≫ B.inclusion.map g := by
    rw [← Functor.map_comp, hq', hmr]
  have hrw : Set.range ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map w') =
      Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    exact hw'range
  have : _root_.AlgebraicGeometry.IsOpenImmersion (show W.toScheme ⟶
      (BigFppfOver.toScheme B integerBase B.contains_integerBase).obj Y.obj.obj.right from W.ι) :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion W.ι)
  have h1 : IsAffine ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj a') :=
    IsAffine.of_isIso (IsOpenImmersion.isoOfRangeEq
      ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map w')
      (show W.toScheme ⟶ (BigFppfOver.toScheme B integerBase B.contains_integerBase).obj
        Y.obj.obj.right from W.ι) hrw).hom
  have hfl : Flat (B.inclusion.map (eqToHom hx) ≫ B.inclusion.map g) := inferInstance
  have hlfp : LocallyOfFinitePresentation (B.inclusion.map (eqToHom hx) ≫ B.inclusion.map g) :=
    inferInstance
  have h2 : Flat ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map q') :=
    MorphismProperty.of_comp_mono @Flat _
      ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map w') (hcomp ▸ hfl)
  have h3 : LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map q') :=
    MorphismProperty.of_comp_mono @LocallyOfFinitePresentation _
      ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map w') (hcomp ▸ hlfp)
  refine ⟨a', w', q', hw'oi, h1, isAffine_inclusion_of_eq hx, h2, ?_, h3, hq'⟩
  refine ⟨fun t => ?_⟩
  have ht : (BigFppfOver.toScheme B integerBase B.contains_integerBase).map w' t ∈
      Set.range (B.inclusion.map g) := by
    have h₀ : (BigFppfOver.toScheme B integerBase B.contains_integerBase).map w' t ∈
        Set.range ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map w') := ⟨t, rfl⟩
    rw [hw'range] at h₀
    have h₁ : (BigFppfOver.toScheme B integerBase B.contains_integerBase).map w' t ∈
        (W : Set (B.inclusion.obj ((polarizedFamiliesProperFlatProjection B).obj Y))) := h₀
    rw [← hrangeg] at h₁
    exact h₁
  obtain ⟨v₀, hv₀⟩ := ht
  refine ⟨(B.inclusion.map (eqToHom hx.symm)) v₀,
    ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map
      w').isOpenEmbedding.injective ?_⟩
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans
    ((congrArg (fun φ => φ ((B.inclusion.map (eqToHom hx.symm)) v₀)) hcomp).trans
      ((Scheme.Hom.comp_apply _ _ _).trans
        ((congrArg _ (inclusion_map_eqToHom_apply_symm _ _)).trans hv₀)))

/-- **The fibre product of a chart with itself.** For morphisms `m n : w ⟶ x` of polarized
families and a morphism `ζ` from the family underlying `x` to `Y` with
`forget n ≫ ζ = forget m ≫ ζ`, if the square of total spaces over the base of `Y` is cartesian
then `w` is, through `m` and `n`, the fibre product of the chart `ζ` with itself. -/
theorem isPullback_yoneda_totalMap_of_isPullback {x w : PolarizedFamily B} (m n : w ⟶ x)
    {Y : CartesianProperFlatSpaces B integerBase B.contains_integerBase}
    (ζ : (forgetPolarization B).obj x ⟶ Y)
    (hglue : (forgetPolarization B).map n ≫ ζ = (forgetPolarization B).map m ≫ ζ)
    (hsch : IsPullback n.totalMap (m.totalMap ≫ x.toBase)
      (x.toBase ≫ (BigFppfOver.toScheme B integerBase B.contains_integerBase).map ζ.1.hom.right)
      ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map ζ.1.hom.right)) :
    IsPullback (yoneda.map (PolarizedFamily.totalMapOverIntegers m))
      (yoneda.map (PolarizedFamily.totalMapOverIntegers n)) ζ.1.hom.left.hom
      ζ.1.hom.left.hom := by
  have sqg' := (isPullback_hom_of_isStronglyCartesian B integerBase B.contains_integerBase
    ζ.1.hom ζ.2).flip
  have hsite : IsPullback (PolarizedFamily.totalMapOverIntegers n)
      (PolarizedFamily.totalMapOverIntegers m ≫ x.structureMapOverIntegers)
      (x.structureMapOverIntegers ≫ ζ.1.hom.right) ζ.1.hom.right :=
    IsPullback.of_map_of_faithful (BigFppfOver.toScheme B integerBase B.contains_integerBase) hsch
  have hY₁ : IsPullback (yoneda.map (PolarizedFamily.totalMapOverIntegers n))
      (yoneda.map (PolarizedFamily.totalMapOverIntegers m) ≫
        yoneda.map x.structureMapOverIntegers)
      (ζ.1.hom.left.hom ≫ Y.obj.obj.hom) (yoneda.map ζ.1.hom.right) :=
    IsPullback.of_iso (hsite.map yoneda) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans ((Functor.map_comp _ _ _).trans (Category.id_comp _).symm))
      ((Category.comp_id _).trans ((Functor.map_comp _ _ _).trans
        (sqg'.w.symm.trans (Category.id_comp _).symm)))
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hcomm : yoneda.map (PolarizedFamily.totalMapOverIntegers m) ≫ ζ.1.hom.left.hom =
      yoneda.map (PolarizedFamily.totalMapOverIntegers n) ≫ ζ.1.hom.left.hom :=
    (congrArg (fun φ => φ.1.hom.left.hom) hglue).symm
  exact (IsPullback.of_bot hY₁ hcomm.symm sqg').flip

/-- **The points of the descended space coming from a chart lie in the schematic locus.** -/
theorem range_pointsMap_subset_schematicLocus_of_chart {x w : PolarizedFamily B} (m n : w ⟶ x)
    {c : B.Schemes} (hx : x.base = c) [IsAffine (B.inclusion.obj c)]
    {Y : CartesianProperFlatSpaces B integerBase B.contains_integerBase}
    {g : c ⟶ (polarizedFamiliesProperFlatProjection B).obj Y}
    (W : (B.inclusion.obj ((polarizedFamiliesProperFlatProjection B).obj Y)).Opens)
    [IsAffine W.toScheme] (hrangeg : Set.range (B.inclusion.map g) = (W : Set _))
    [Flat (B.inclusion.map g)] [LocallyOfFinitePresentation (B.inclusion.map g)]
    (ζ : (forgetPolarization B).obj x ⟶ Y)
    [(polarizedFamiliesProperFlatProjection B).IsHomLift g ζ]
    (hglue : (forgetPolarization B).map n ≫ ζ = (forgetPolarization B).map m ≫ ζ)
    (hsch : IsPullback n.totalMap (m.totalMap ≫ x.toBase)
      (x.toBase ≫ (BigFppfOver.toScheme B integerBase B.contains_integerBase).map ζ.1.hom.right)
      ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map ζ.1.hom.right))
    (hT : ∀ ξ : x.total, ∃ T : x.total.Opens, ξ ∈ T ∧ (T : Scheme.{u}).IsQuasiAffine ∧
      m.totalMap ⁻¹ᵁ T = n.totalMap ⁻¹ᵁ T) :
    Set.range (Space.pointsMap B integerBase B.contains_integerBase _ ζ.1.hom.left.hom) ⊆
      Set.range (Space.pointsMap B integerBase B.contains_integerBase
        (Space.schematicLocus B integerBase B.contains_integerBase Y.obj.obj.left.1).toFunctor
        (Space.schematicLocus B integerBase B.contains_integerBase Y.obj.obj.left.1).ι) := by
  obtain ⟨a', w', q', hw', ha', hc', hfl, hsu, hlfp, hq'⟩ :=
    exists_factor_hom_right_of_isHomLift hx W hrangeg ζ
  have := hw'
  have := ha'
  have := hc'
  have := hfl
  have := hsu
  have := hlfp
  have sq := isPullback_yoneda_totalMap_of_isPullback m n ζ hglue hsch
  have sqg : IsPullback ζ.1.hom.left.hom (yoneda.map x.structureMapOverIntegers) Y.obj.obj.hom
      (yoneda.map (q' ≫ w')) :=
    (congrArg (fun k => IsPullback ζ.1.hom.left.hom (yoneda.map x.structureMapOverIntegers)
      Y.obj.obj.hom (yoneda.map k)) hq').mpr
      (isPullback_hom_of_isStronglyCartesian B integerBase B.contains_integerBase
        ζ.1.hom ζ.2).flip
  rintro _ ⟨ξ', rfl⟩
  obtain ⟨T, hξT, hTqa, hT⟩ := hT (Space.pointsToScheme B integerBase B.contains_integerBase _ ξ')
  let T' : ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj
      ((schemeOverIntegers B).obj x.totalObj)).Opens := T
  have : (T' : Scheme.{u}).IsQuasiAffine := hTqa
  exact Space.image_pointsMap_subset_schematicLocus_of_isQuasiAffine B integerBase
    B.contains_integerBase Y.obj.obj.left.2 Y.obj.obj.hom w' q' ζ.1.hom.left.hom
    x.structureMapOverIntegers sqg (PolarizedFamily.totalMapOverIntegers m)
    (PolarizedFamily.totalMapOverIntegers n) sq T' hT ⟨ξ', hξT, rfl⟩

section Member

variable {U : B.Schemes} {R : Sieve U} (D : (polarizedProjection B).SieveDescentDatum R)
  {c : B.Schemes} {g : c ⟶ U} (hg : R g)

/-- The member of `D` over `g`, pulled back along the first projection of `c ×_U c`. -/
local notation "𝔀₂" => pullbackFiber (polarizedProjection B) (D.obj g hg) (pullback.fst g g)
/-- The chosen cartesian lift of the first projection. -/
local notation "𝓜" =>
  IsPreFibered.pullbackMap (Subtype.property (D.obj g hg)) (pullback.fst g g)
/-- The gluing morphism over the second projection. -/
local notation "𝓖" => D.glueHom hg (pullback.fst g g) (pullback.snd g g) pullback.condition
/-- The structure morphism of the member over `g`, read over `c`. -/
local notation "𝓹" => PolarizedFamily.toBase (Subtype.val (D.obj g hg)) ≫
  B.inclusion.map (eqToHom (Subtype.property (D.obj g hg)))
/-- The structure morphism of `𝔀₂` followed by the first projection. -/
local notation "𝓴₁" => (PolarizedFamily.toBase (Subtype.val (pullbackFiber
  (polarizedProjection B) (D.obj g hg) (pullback.fst g g))) ≫ B.inclusion.map (eqToHom
    (Subtype.property (pullbackFiber (polarizedProjection B) (D.obj g hg) (pullback.fst g g))))) ≫
  B.inclusion.map (pullback.fst g g)

/-- The fibre product of two arrows into `d` is cartesian over their factorisations through a
monomorphism `w`. -/
private theorem isPullback_inclusion_map_pullback_of_comp_mono {a b d : B.Schemes}
    {W : Scheme.{u}} (f : a ⟶ d) (f' : b ⟶ d) (qa : B.inclusion.obj a ⟶ W)
    (qb : B.inclusion.obj b ⟶ W) (w : W ⟶ B.inclusion.obj d) [Mono w]
    (ha : qa ≫ w = B.inclusion.map f) (hb : qb ≫ w = B.inclusion.map f') :
    IsPullback (B.inclusion.map (pullback.fst f f')) (B.inclusion.map (pullback.snd f f'))
      qa qb := by
  have : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
  exact isPullback_of_comp_mono w
    (by rw [ha, hb]; exact (IsPullback.of_hasPullback f f').map B.inclusion)

include hg in
/-- The two morphisms of total spaces over `c ×_U c`: the gluing morphism presents the total space
over `c ×_U c` as a base change of the total space over `c` along `q`, and the two morphisms agree
over `W`. -/
theorem isPullback_glueHom_totalMap {W : Scheme.{u}} (q : B.inclusion.obj c ⟶ W)
    (w : W ⟶ B.inclusion.obj U) [Mono w] (hqw : q ≫ w = B.inclusion.map g) :
    IsPullback (𝓖).totalMap (𝓴₁) ((𝓹) ≫ q) q ∧
      (𝓜).totalMap ≫ (𝓹) ≫ q = (𝓖).totalMap ≫ (𝓹) ≫ q := by
  have hM := PolarizedFamily.Hom.isPullback_of_isHomLift (𝔀₂).2 (D.obj g hg).2
    (pullback.fst g g) (𝓜)
  have hG := PolarizedFamily.Hom.isPullback_of_isHomLift (𝔀₂).2 (D.obj g hg).2
    (pullback.snd g g) (𝓖)
  have hbase := isPullback_inclusion_map_pullback_of_comp_mono g g q q w hqw hqw
  refine ⟨hG.paste_vert hbase.flip, ?_⟩
  rw [← Category.assoc, hM.w, ← Category.assoc _ _ q, hG.w, Category.assoc, Category.assoc,
    hbase.w]
  simp only [Category.assoc]

/-- **The diagonal.** The total space over `c` maps to the total space over `c ×_U c`, splitting
both morphisms to the total space over `c`. -/
theorem exists_diagonal_glueHom_totalMap :
    ∃ Δ : (D.obj g hg).1.total ⟶ (𝔀₂).1.total, Δ ≫ (𝓜).totalMap = 𝟙 _ ∧
      Δ ≫ (𝓖).totalMap = 𝟙 _ := by
  let δ : c ⟶ pullback g g := pullback.lift (𝟙 c) (𝟙 c) rfl
  have hδ₁ : δ ≫ pullback.fst g g = 𝟙 c := pullback.lift_fst _ _ _
  have hδ₂ : δ ≫ pullback.snd g g = 𝟙 c := pullback.lift_snd _ _ _
  have hM' := PolarizedFamily.Hom.isPullback_of_isHomLift
    (pullbackFiber (polarizedProjection B) (D.obj g hg) (δ ≫ pullback.fst g g)).2 (D.obj g hg).2
    (δ ≫ pullback.fst g g) (IsPreFibered.pullbackMap (D.obj g hg).2 (δ ≫ pullback.fst g g))
  have : IsIso (B.inclusion.map (δ ≫ pullback.fst g g)) := by
    rw [hδ₁, CategoryTheory.Functor.map_id]
    infer_instance
  have := hM'.isIso_fst_of_isIso
  refine ⟨inv (IsPreFibered.pullbackMap (D.obj g hg).2 (δ ≫ pullback.fst g g)).totalMap ≫
    (D.restrictHom hg (pullback.fst g g) δ).totalMap, ?_, ?_⟩
  · simp only [Category.assoc, ← PolarizedFamily.comp_totalMap, D.restrictHom_pullbackMap,
      IsIso.inv_hom_id]
  · simp only [Category.assoc, ← PolarizedFamily.comp_totalMap, D.restrictHom_glueHom]
    rw [D.glueHom_of_eq hg _ _ (hδ₁.trans hδ₂.symm)]
    exact IsIso.inv_hom_id _

/-- The three morphisms out of the member over `(c ×_U c) ×_U c`: the gluing isomorphism to the
member pulled back along a composite, followed by the restriction. -/
theorem iso_restrictHom_comp {Z : B.Schemes} (e₁ : Z ⟶ c) (π : Z ⟶ pullback g g)
    (h : e₁ ≫ g = (π ≫ pullback.fst g g) ≫ g) :
    (Fiber.fiberInclusion.map (D.iso hg hg e₁ (π ≫ pullback.fst g g) h).hom ≫
        D.restrictHom hg (pullback.fst g g) π) ≫ (𝓜) =
      D.glueHom hg e₁ (π ≫ pullback.fst g g) h ∧
    (Fiber.fiberInclusion.map (D.iso hg hg e₁ (π ≫ pullback.fst g g) h).hom ≫
        D.restrictHom hg (pullback.fst g g) π) ≫ (𝓖) =
      D.glueHom hg e₁ (π ≫ pullback.snd g g)
        (h.trans (by rw [Category.assoc, Category.assoc, pullback.condition])) :=
  ⟨(Category.assoc _ _ _).trans (D.iso_restrictHom_pullbackMap hg e₁ _ π h),
    (Category.assoc _ _ _).trans (D.iso_restrictHom_glueHom hg e₁ _ _ pullback.condition π h)⟩

include hg in
/-- **The triple overlap.** The data over `(c ×_U c) ×_U c` that the cocycle condition of the
transfer of polarizations is read on. -/
theorem exists_triple_glueHom {W : Scheme.{u}} (q : B.inclusion.obj c ⟶ W)
    (w : W ⟶ B.inclusion.obj U) [Mono w] (hqw : q ≫ w = B.inclusion.map g) :
    ∃ (w₃ : PolarizedFamily B) (s₁₂ s₂₃ s₁₃ : w₃ ⟶ (𝔀₂).1) (T₁ T₂ T₃ : w₃ ⟶ (D.obj g hg).1)
      (k₃ : w₃.total ⟶ B.inclusion.obj c),
      s₁₂ ≫ (𝓜) = T₁ ∧ s₁₂ ≫ (𝓖) = T₂ ∧ s₂₃ ≫ (𝓜) = T₂ ∧ s₂₃ ≫ (𝓖) = T₃ ∧
        s₁₃ ≫ (𝓜) = T₁ ∧ s₁₃ ≫ (𝓖) = T₃ ∧
        IsPullback s₂₃.totalMap k₃ ((𝓖).totalMap ≫ (𝓹) ≫ q) q ∧
        s₁₂.totalMap ≫ (𝓴₁) = k₃ ∧ s₁₃.totalMap ≫ (𝓴₁) = k₃ := by
  have : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
  have hcond : pullback.fst g g ≫ g = pullback.snd g g ≫ g := pullback.condition
  have hG := PolarizedFamily.Hom.isPullback_of_isHomLift (𝔀₂).2 (D.obj g hg).2
    (pullback.snd g g) (𝓖)
  let π₂₃ := pullback.fst (pullback.snd g g ≫ g) g
  let e₁ := pullback.snd (pullback.snd g g ≫ g) g
  have hc₃ : π₂₃ ≫ pullback.snd g g ≫ g = e₁ ≫ g := pullback.condition
  have he₁₂ : e₁ ≫ g = (π₂₃ ≫ pullback.fst g g) ≫ g := by
    rw [← hc₃, Category.assoc, hcond]
  have he₁₃ : e₁ ≫ g = (π₂₃ ≫ pullback.snd g g) ≫ g := by
    rw [← hc₃, Category.assoc]
  let π₁₂ : pullback (pullback.snd g g ≫ g) g ⟶ pullback g g :=
    pullback.lift e₁ (π₂₃ ≫ pullback.fst g g) he₁₂
  let π₁₃ : pullback (pullback.snd g g ≫ g) g ⟶ pullback g g :=
    pullback.lift e₁ (π₂₃ ≫ pullback.snd g g) he₁₃
  have h₁₂₁ : π₁₂ ≫ pullback.fst g g = e₁ := pullback.lift_fst _ _ _
  have h₁₂₂ : π₁₂ ≫ pullback.snd g g = π₂₃ ≫ pullback.fst g g := pullback.lift_snd _ _ _
  have h₁₃₁ : π₁₃ ≫ pullback.fst g g = e₁ := pullback.lift_fst _ _ _
  have h₁₃₂ : π₁₃ ≫ pullback.snd g g = π₂₃ ≫ pullback.snd g g := pullback.lift_snd _ _ _
  have he₁₂' : e₁ ≫ g = (π₁₂ ≫ pullback.fst g g) ≫ g := by rw [h₁₂₁]
  have he₁₃' : e₁ ≫ g = (π₁₃ ≫ pullback.fst g g) ≫ g := by rw [h₁₃₁]
  obtain ⟨hσ₁₂M, hσ₁₂G⟩ := iso_restrictHom_comp D hg e₁ π₁₂ he₁₂'
  obtain ⟨hσ₂₃M, hσ₂₃G⟩ := iso_restrictHom_comp D hg e₁ π₂₃ he₁₂
  obtain ⟨hσ₁₃M, hσ₁₃G⟩ := iso_restrictHom_comp D hg e₁ π₁₃ he₁₃'
  rw [D.glueHom_congr hg e₁ _ e₁ h₁₂₁ _ rfl] at hσ₁₂M
  rw [D.glueHom_congr hg e₁ _ _ h₁₂₂ _ he₁₂] at hσ₁₂G
  rw [D.glueHom_congr hg e₁ _ e₁ h₁₃₁ _ rfl] at hσ₁₃M
  rw [D.glueHom_congr hg e₁ _ _ h₁₃₂ _ he₁₃] at hσ₁₃G
  rw [D.glueHom_congr hg e₁ _ _ rfl _ he₁₃] at hσ₂₃G
  have hσ := fun (π : pullback (pullback.snd g g ≫ g) g ⟶ pullback g g)
      (h : e₁ ≫ g = (π ≫ pullback.fst g g) ≫ g) =>
    PolarizedFamily.Hom.isPullback_of_isHomLift
      (pullbackFiber (polarizedProjection B) (D.obj g hg) e₁).2 (𝔀₂).2 π
      (Fiber.fiberInclusion.map (D.iso hg hg e₁ (π ≫ pullback.fst g g) h).hom ≫
        D.restrictHom hg (pullback.fst g g) π)
      (hφ := D.isHomLift_iso_restrictHom hg e₁ (pullback.fst g g) π h)
  have hbase₃ := isPullback_inclusion_map_pullback_of_comp_mono (pullback.snd g g ≫ g) g
    (B.inclusion.map (pullback.snd g g) ≫ q) q w (by rw [Category.assoc, hqw, Functor.map_comp])
    hqw
  have sq₃ := (hσ π₂₃ he₁₂).paste_vert hbase₃
  rw [← Category.assoc _ (B.inclusion.map (pullback.snd g g)) q, ← hG.w, Category.assoc] at sq₃
  refine ⟨_, _, _, _, _, _, _, _, hσ₁₂M, hσ₁₂G, hσ₂₃M, hσ₂₃G, hσ₁₃M, hσ₁₃G, sq₃, ?_, ?_⟩
  · rw [← Category.assoc, (hσ π₁₂ he₁₂').w, Category.assoc, ← Functor.map_comp, h₁₂₁]
    exact Category.assoc _ _ _
  · rw [← Category.assoc, (hσ π₁₃ he₁₃').w, Category.assoc, ← Functor.map_comp, h₁₃₁]
    exact Category.assoc _ _ _

/-- **Stable quasi-affine neighbourhoods on the total space of a member of a descent datum.**
Let `D` be a descent datum of polarized families relative to a sieve `R` on `U`, let
`g : c ⟶ U` be an arrow of `R` with `c` affine, and suppose that `g` factors as a flat morphism
`q` to an affine scheme followed by a monomorphism `w`. Then every point of the total space of
the member of `D` over `g` has an open neighbourhood which is a quasi-affine scheme and whose two
preimages under the two morphisms from the total space over `c ×_U c` agree (the chosen
cartesian lift along the first projection, and the gluing morphism of `D`). -/
theorem exists_isQuasiAffine_preimage_eq_of_descentDatum [IsAffine (B.inclusion.obj c)]
    {W : Scheme.{u}} [IsAffine W] (q : B.inclusion.obj c ⟶ W) [Flat q]
    (w : W ⟶ B.inclusion.obj U) [Mono w] (hqw : q ≫ w = B.inclusion.map g)
    (ξ : (D.obj g hg).1.total) :
    ∃ T : (D.obj g hg).1.total.Opens, ξ ∈ T ∧ (T : Scheme.{u}).IsQuasiAffine ∧
      (𝓜).totalMap ⁻¹ᵁ T = (𝓖).totalMap ⁻¹ᵁ T := by
  classical
  obtain ⟨sq₂, hW⟩ := isPullback_glueHom_totalMap D hg q w hqw
  obtain ⟨Δ, hΔ₁, hΔ₂⟩ := exists_diagonal_glueHom_totalMap D hg
  obtain ⟨w₃, s₁₂, s₂₃, s₁₃, T₁, T₂, T₃, k₃, e₁, e₂, e₃, e₄, e₅, e₆, sq₃, hk₁₂, hk₁₃⟩ :=
    exists_triple_glueHom D hg q w hqw
  have : Stacks.Ample.IsInvertibleModule (D.obj g hg).1.total (D.obj g hg).1.lineBundle :=
    (D.obj g hg).1.invertible
  have : IsAffine (B.inclusion.obj (D.obj g hg).1.base) := isAffine_inclusion_of_eq (D.obj g hg).2
  have hL : Stacks.Ample.IsAmple (D.obj g hg).1.total (D.obj g hg).1.lineBundle :=
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple (D.obj g hg).1.toBase
      (D.obj g hg).1.lineBundle).1 (D.obj g hg).1.relativelyAmple
  have := (D.obj g hg).1.proper
  have : QuasiSeparatedSpace (D.obj g hg).1.total :=
    quasiSeparatedSpace_of_quasiSeparated (D.obj g hg).1.toBase
  have hbase := isPullback_inclusion_map_pullback_of_comp_mono g g q q w hqw hqw
  have : IsAffine (Limits.pullback q q) :=
    AlgebraicGeometry.Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine q q
  have : IsAffine (B.inclusion.obj (pullback g g)) := IsAffine.of_isIso hbase.isoPullback.hom
  have : IsAffine (B.inclusion.obj (𝔀₂).1.base) := isAffine_inclusion_of_eq (𝔀₂).2
  have := (𝔀₂).1.proper
  have : CompactSpace (𝔀₂).1.total := QuasiCompact.compactSpace_of_compactSpace (𝔀₂).1.toBase
  have : QuasiSeparatedSpace (𝔀₂).1.total :=
    quasiSeparatedSpace_of_quasiSeparated (𝔀₂).1.toBase
  exact PolarizedFamily.exists_isQuasiAffine_preimage_eq_preimage (w := (𝔀₂).1) (𝓜) (𝓖)
    s₁₂ s₂₃ s₁₃ T₁ T₂ T₃ e₁ e₂ e₃ e₄ e₅ e₆ q (𝓹) hL _ sq₂ hW Δ hΔ₁ hΔ₂ k₃ sq₃ hk₁₂ hk₁₃ ξ

end Member

/-- **Every point of the algebraic space descended from a descent datum of polarized families lies
in its schematic locus.** Let `D` be a descent datum of polarized families relative to a covering
family of the big fppf site, and let `Y` be a family of algebraic spaces over `U` with morphisms
`ζ f` over every arrow `f` of the sieve from the family underlying the member of `D` over `f`,
compatible with the gluing morphisms of `D`. Then every point of the algebraic space of `Y` lies
in its schematic locus. -/
theorem mem_range_schematicLocus_of_descentDatum {U : B.Schemes}
    (E : PreZeroHypercover.{u + 1} U) (hE : B.IsCovering ⟨U, E⟩)
    (D : (polarizedProjection B).SieveDescentDatum (Sieve.ofArrows E.X E.f))
    (Y : CartesianProperFlatSpaces B integerBase B.contains_integerBase)
    (hY : (polarizedFamiliesProperFlatProjection B).obj Y = U)
    (ζ : ∀ ⦃V : B.Schemes⦄ (f : V ⟶ U) (hf : Sieve.ofArrows E.X E.f f),
      (forgetPolarization B).obj (D.obj f hf).1 ⟶ Y)
    (hζ : ∀ ⦃V : B.Schemes⦄ (f : V ⟶ U) (hf : Sieve.ofArrows E.X E.f f),
      (polarizedFamiliesProperFlatProjection B).IsHomLift f (ζ f hf))
    (hglue : ∀ ⦃V Z : B.Schemes⦄ ⦃f : V ⟶ U⦄ (hf : Sieve.ofArrows E.X E.f f) (ε ε' : Z ⟶ V)
      (heq : ε ≫ f = ε' ≫ f),
      (forgetPolarization B).map (D.glueHom hf ε ε' heq) ≫ ζ f hf =
        (forgetPolarization B).map (IsPreFibered.pullbackMap (D.obj f hf).2 ε) ≫ ζ f hf)
    (pt : Space.points B integerBase B.contains_integerBase Y.obj.obj.left.1) :
    pt ∈ Set.range (Space.pointsMap B integerBase B.contains_integerBase
      (Space.schematicLocus B integerBase B.contains_integerBase Y.obj.obj.left.1).toFunctor
      (Space.schematicLocus B integerBase B.contains_integerBase Y.obj.obj.left.1).ι) := by
  classical
  subst hY
  obtain ⟨u₁, hu₁⟩ : ∃ u₁, u₁ = Space.pointsToScheme B integerBase B.contains_integerBase
      Y.obj.obj.right (Space.pointsMap B integerBase B.contains_integerBase _ Y.obj.obj.hom pt) :=
    ⟨_, rfl⟩
  have hfppf : Presieve.ofArrows (fun i => B.inclusion.obj (E.X i))
      (fun i => B.inclusion.map (E.f i)) ∈
        Scheme.fppfPrecoverage
          (B.inclusion.obj ((polarizedFamiliesProperFlatProjection B).obj Y)) := by
    have h : E.presieve₀.map B.inclusion ∈ Scheme.fppfPrecoverage
        (B.inclusion.obj ((polarizedFamiliesProperFlatProjection B).obj Y)) := hE.1
    rwa [PreZeroHypercover.presieve₀, Presieve.map_ofArrows] at h
  obtain ⟨hsurj, hfl⟩ :=
    (Scheme.ofArrows_mem_precoverage_iff (@Flat ⊓ @LocallyOfFinitePresentation)).1 hfppf
  obtain ⟨i, v, hv⟩ := hsurj u₁
  obtain ⟨hflat, hlfp⟩ := hfl i
  have := hflat
  have := hlfp
  obtain ⟨V, W, hV, hW, hvV, himg⟩ :=
    exists_isAffineOpen_image_eq_of_flat (B.inclusion.map (E.f i)) v
  let c : B.Schemes := B.obj (Scheme.size_lt_of_isOpenImmersion V.ι (E.X i).property)
  let ι : c ⟶ E.X i := ObjectProperty.homMk V.ι
  have hg : Sieve.ofArrows E.X E.f (ι ≫ E.f i) :=
    (Sieve.ofArrows E.X E.f).downward_closed (Sieve.ofArrows_mk E.X E.f i) ι
  have : IsAffine (B.inclusion.obj c) := hV
  have : IsAffine W.toScheme := hW
  have hincl : B.inclusion.map (ι ≫ E.f i) = V.ι ≫ B.inclusion.map (E.f i) :=
    CategoryTheory.Functor.map_comp _ _ _
  have hrangeg : Set.range (B.inclusion.map (ι ≫ E.f i)) = (W : Set _) := by
    rw [← himg, hincl]
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨V.ι a, by rw [← Scheme.Opens.range_ι V]; exact ⟨a, rfl⟩, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      rw [← Scheme.Opens.range_ι V] at hb
      obtain ⟨a, rfl⟩ := hb
      exact ⟨a, rfl⟩
  let q : B.inclusion.obj c ⟶ W.toScheme :=
    IsOpenImmersion.lift W.ι (B.inclusion.map (ι ≫ E.f i))
      (by rw [hrangeg, Scheme.Opens.range_ι])
  have hqw : q ≫ W.ι = B.inclusion.map (ι ≫ E.f i) := IsOpenImmersion.lift_fac _ _ _
  have : Flat q := MorphismProperty.of_comp_mono @Flat q W.ι (by rw [hqw, hincl]; infer_instance)
  have : Flat (B.inclusion.map (ι ≫ E.f i)) := by rw [hincl]; infer_instance
  have : LocallyOfFinitePresentation (B.inclusion.map (ι ≫ E.f i)) := by
    rw [hincl]; infer_instance
  have := hζ (ι ≫ E.f i) hg
  have hmr := toScheme_map_hom_right_of_isHomLift' (D.obj (ι ≫ E.f i) hg).2 (ι ≫ E.f i)
    (ζ (ι ≫ E.f i) hg)
  have hvV' : v ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hvV
  obtain ⟨v₀, rfl⟩ := hvV'
  obtain ⟨b, hb⟩ := Space.surjective_pointsToScheme B integerBase B.contains_integerBase
    ((forgetPolarization B).obj (D.obj (ι ≫ E.f i) hg).1).obj.obj.right
    ((B.inclusion.map (eqToHom (D.obj (ι ≫ E.f i) hg).2.symm)) v₀)
  have hab : Space.pointsMap B integerBase B.contains_integerBase _ Y.obj.obj.hom pt =
      Space.pointsMap B integerBase B.contains_integerBase _
        (yoneda.map (ζ (ι ≫ E.f i) hg).1.hom.right) b := by
    apply Space.injective_pointsToScheme B integerBase B.contains_integerBase
    refine hu₁.symm.trans (hv.symm.trans ?_)
    refine ((Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun φ => φ v₀) hincl.symm)).trans
      ?_
    refine ((congrArg (fun φ => φ ((B.inclusion.map
      (eqToHom (D.obj (ι ≫ E.f i) hg).2.symm)) v₀)) hmr).trans ((Scheme.Hom.comp_apply _ _ _).trans
        (congrArg _ (inclusion_map_eqToHom_apply_symm _ _)))).symm.trans ?_
    rw [← hb]
    exact (Space.pointsToScheme_pointsMap_yoneda B integerBase B.contains_integerBase _ _).symm
  obtain ⟨ξ', hξ', -⟩ := Space.exists_points_of_isPullback B integerBase B.contains_integerBase
    (isPullback_hom_of_isStronglyCartesian B integerBase B.contains_integerBase
      (ζ (ι ≫ E.f i) hg).1.hom (ζ (ι ≫ E.f i) hg).2).flip pt b hab
  have hM := PolarizedFamily.Hom.isPullback_of_isHomLift
    (pullbackFiber (polarizedProjection B) (D.obj (ι ≫ E.f i) hg)
      (pullback.fst (ι ≫ E.f i) (ι ≫ E.f i))).2 (D.obj (ι ≫ E.f i) hg).2
    (pullback.fst (ι ≫ E.f i) (ι ≫ E.f i))
    (IsPreFibered.pullbackMap (D.obj (ι ≫ E.f i) hg).2 (pullback.fst (ι ≫ E.f i) (ι ≫ E.f i)))
  have hG := PolarizedFamily.Hom.isPullback_of_isHomLift
    (pullbackFiber (polarizedProjection B) (D.obj (ι ≫ E.f i) hg)
      (pullback.fst (ι ≫ E.f i) (ι ≫ E.f i))).2 (D.obj (ι ≫ E.f i) hg).2
    (pullback.snd (ι ≫ E.f i) (ι ≫ E.f i))
    (D.glueHom hg (pullback.fst (ι ≫ E.f i) (ι ≫ E.f i)) (pullback.snd (ι ≫ E.f i) (ι ≫ E.f i))
      pullback.condition)
  have hsch := isPullback_comp_of_isPullback_base _ _ _
    (B.inclusion.mapIso (eqToIso (D.obj (ι ≫ E.f i) hg).2)) _ _ _ _ _ hmr hM.w hG
    ((IsPullback.of_hasPullback (ι ≫ E.f i) (ι ≫ E.f i)).map B.inclusion)
  exact range_pointsMap_subset_schematicLocus_of_chart _ _ (D.obj (ι ≫ E.f i) hg).2 W hrangeg
    (ζ (ι ≫ E.f i) hg) (hglue hg _ _ _) hsch
    (fun ξ => exists_isQuasiAffine_preimage_eq_of_descentDatum D hg q W.ι hqw ξ) ⟨ξ', hξ'⟩

/-- **Descent data of polarized families are effective.** Every descent datum of polarized
families relative to the sieve generated by a covering family of the big fppf site is effective:
the family of algebraic spaces underlying it descends (Stacks 0D1G); the descended algebraic space
is a scheme, its schematic locus containing every point
(`AlgebraicGeometry.mem_range_schematicLocus_of_descentDatum`); and the polarization descends
along the descended scheme (`AlgebraicGeometry.PolarizedDescentScheme.isEffective`). -/
theorem SieveDescentDatum.isEffective_polarized {U : B.Schemes}
    (E : PreZeroHypercover.{u + 1} U) (hE : B.IsCovering ⟨U, E⟩)
    (D : (polarizedProjection B).SieveDescentDatum (Sieve.ofArrows E.X E.f)) : D.IsEffective := by
  have := (polarizedFamiliesProperFlatProjection_isStack B).isFibered
  obtain ⟨y, ζ, hcart, hglue⟩ := isEffective_mapF_forgetPolarization B
    (Precoverage.generate_mem_toGrothendieck ⟨E, rfl, hE⟩) D
  have hζ : ∀ ⦃V : B.Schemes⦄ (f : V ⟶ U) (hf : Sieve.ofArrows E.X E.f f),
      (polarizedFamiliesProperFlatProjection B).IsHomLift f (ζ f hf) := fun _ f hf =>
    (hcart f hf).toIsHomLift
  have hglue' : ∀ ⦃V W Z : B.Schemes⦄ ⦃f : V ⟶ U⦄ (hf : Sieve.ofArrows E.X E.f f)
      ⦃g : W ⟶ U⦄ (hg : Sieve.ofArrows E.X E.f g) (b : Z ⟶ V) (b' : Z ⟶ W)
      (h : b ≫ f = b' ≫ g), (forgetPolarization B).map
        (Fiber.fiberInclusion.map (D.iso hf hg b b' h).hom ≫
          IsPreFibered.pullbackMap (D.obj g hg).2 b') ≫ ζ g hg =
      (forgetPolarization B).map (IsPreFibered.pullbackMap (D.obj f hf).2 b) ≫ ζ f hf :=
    fun _ _ _ _ hf _ hg b b' h =>
      Functor.SieveDescentDatum.map_comp_eq_of_mapF (forgetPolarization_isFibredOneMorphism B) D
        hf hg b b' h _ _ (hglue hf hg b b' h)
  have hrep : y.1.obj.obj.left.1.IsRepresentable :=
    Space.isRepresentable_of_surjective_pointsMap_schematicLocus B integerBase
      B.contains_integerBase y.1.obj.obj.left.2 fun pt =>
        mem_range_schematicLocus_of_descentDatum E hE D y.1 y.2 ζ hζ
          (fun _ _ _ hf ε ε' heq => hglue' hf hf ε ε' heq) pt
  have := hrep
  exact (PolarizedDescentScheme.ofRepresented y
    (fun i => ζ (E.f i) (Sieve.ofArrows_mk E.X E.f i)) (fun i => hζ _ _)
    (fun i j _ b b' h => hglue' (Sieve.ofArrows_mk E.X E.f i) (Sieve.ofArrows_mk E.X E.f j) b b' h)
    y.1.obj.obj.left.1.reprW).isEffective
    (BigFppfSite.ofArrows_inclusion_mem_fpqcPrecoverage hE)

variable (B)

/-- **Polarized families form a stack over the big fppf site.** -/
theorem polarizedProjection_isStack : (polarizedProjection B).IsStack B.topology :=
  polarizedProjection_isStack_of_isEffective B fun _ E hE D =>
    SieveDescentDatum.isEffective_polarized E hE D

/-- **Stacks 0D40, second assertion**: `𝒫olarized` is a stack in groupoids over the big fppf
site. -/
theorem polarizedProjection_isStackInGroupoids :
    (polarizedProjection B).IsStackInGroupoids.{w} B.topology :=
  (polarizedProjection_isStack B).isStackInGroupoids
    polarizedProjection_isFiberedInGroupoids_unconditional

/-- **Stacks 0D40, first assertion**: `𝒫olarized` is a stack in groupoids over
`Spaces'_{fp, flat, proper}`, with the topology inherited from the big fppf site (Stacks 06NV). -/
theorem polarizedSpacesForget_isStackInGroupoids :
    (polarizedSpacesForget B).IsStackInGroupoids.{w}
      ((polarizedFamiliesProperFlatProjection B).inheritedTopology B.topology) :=
  polarizedSpacesForget_isStackInGroupoids_of_isStack B (polarizedProjection_isStack B)

/-- **Stacks 0D40.** The category `𝒫olarized` of polarized families is a stack in groupoids over
`Spaces'_{fp, flat, proper}`, endowed with the topology inherited from the big fppf site
(Stacks 06NV), and it is a stack in groupoids over the big fppf site of schemes. -/
@[stacks 0D40]
theorem polarized_isStackInGroupoids :
    (polarizedSpacesForget B).IsStackInGroupoids.{w}
        ((polarizedFamiliesProperFlatProjection B).inheritedTopology B.topology) ∧
      (polarizedProjection B).IsStackInGroupoids.{w} B.topology :=
  ⟨polarizedSpacesForget_isStackInGroupoids B, polarizedProjection_isStackInGroupoids B⟩

/-- `𝒫olarized`, read over the big fppf site of the terminal scheme `Spec ℤ`, is a stack: this is
`AlgebraicGeometry.polarizedProjection_isStack` transported along the equivalence of the site with
its slice at the terminal object (Stacks 04WV). -/
theorem polarizedStackUnconditional_isStack
    (hZ : B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    (polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val.p.IsStack
      (BigFppfOver.topology B _ hZ) := by
  let _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  have hU : Presheaf.IsSheaf B.topology (yoneda.obj (B.obj hZ)) :=
    (CategoryTheory.isSheaf_iff_isSheaf_of_type (J := B.topology) _).2
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := B.topology) _)
  exact Over.isStack_of_comp_forget
    ((polarizedProjection B).sliceAtTerminal (isTerminal_obj_specULiftZ B hZ)) hU
    (polarizedProjection_isStack B)

end AlgebraicGeometry

end
