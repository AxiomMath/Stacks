module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.SiteBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedZariskiCanonical

/-!
# Comparisons of Zariski readings along composites of represented morphisms

This file is a piece of the bridge between the site Quot functor of `𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ` and the
scheme-level families on `ℙⁿ_T` (Stacks 0DPA).  Over objects `W₀`, `W`, `W'` of the big fppf site
with morphisms `W' ⟶ W ⟶ W₀` and `W' ⟶ W₀`, and algebraic spaces `X`, `X'` identified with the
represented `h_W`, `h_{W'}` and lying over `h_{W₀}`, it records how the Zariski reading of
modules (`AlgebraicGeometry.Space.representedZariskiModulePullbackIso`) interacts with the
comparisons of inverse images of Stacks 03LU:

* `AlgebraicGeometry.ProjectiveQuot.readingPullback_naturality`: the comparison of the readings
  along `W' ⟶ W`, through a square `φ' ≫ ρ = h_{W' ⟶ W} ≫ φ`, is natural in the module.
* `AlgebraicGeometry.ProjectiveQuot.readingSite_comp`: going round `W' ⟶ W ⟶ W₀` or straight down
  gives the same comparison of inverse images (two applications of
  `AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackTriangle_comp`).

Everything is stated over abstract objects of the site, with the represented algebraic spaces
written `⟨yoneda.obj W, _⟩` throughout: this keeps every inverse image in a single spelling, which
is what makes the elaborator and the kernel accept the pastings (see the implementation notes).
The generic pasting lemmas at the top are stated in arbitrary categories for the same reason.

## Implementation notes

Mixing `schemeSpace W` with `⟨yoneda.obj W, _⟩` inside one composite of morphisms of
modules, or `(F ⋙ G).map` with `G.map (F.map ·)` across differently spelled middle categories,
costs a deterministic timeout at `whnf` or in the kernel; stating each lemma in the spelling the
library lemmas it consumes produce, and feeding them to pasting lemmas proved in an arbitrary
category, costs a few seconds.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

namespace AlgebraicGeometry.ProjectiveQuot

universe u

variable {B : BigFppfSite.{u}} {n r : ℕ}

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- Pasting two commuting squares, bracketed as two composites of isomorphisms meet. -/
theorem comp_eq_comp_of_squares {C : Type*} [Category* C] {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C}
    {a : X₁ ⟶ X₂} {b : X₂ ⟶ Y₂} {c : Y₂ ⟶ Z₂} {d : X₁ ⟶ Y₁} {e : Y₁ ⟶ Y₂} {f : Y₁ ⟶ Z₁}
    {g : Z₁ ⟶ Z₂} (h₁ : a ≫ b = d ≫ e) (h₂ : e ≫ c = f ≫ g) : a ≫ (b ≫ c) = (d ≫ f) ≫ g := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- The naturality of an isomorphism `A ⋙ B ≅ A' ⋙ B'`, carried by two further functors and
written with every composite of functors applied. -/
theorem map_map_naturality {C D D' E F G : Type*} [Category* C] [Category* D] [Category* D']
    [Category* E] [Category* F] [Category* G] {A : C ⥤ D} {B : D ⥤ E} {A' : C ⥤ D'}
    {B' : D' ⥤ E} (α : A ⋙ B ≅ A' ⋙ B') (Z₁ : E ⥤ F) (Z₂ : F ⥤ G) {M M' : C} (f : M ⟶ M') :
    Z₂.map (Z₁.map (B.map (A.map f))) ≫ Z₂.map (Z₁.map (α.hom.app M')) =
      Z₂.map (Z₁.map (α.hom.app M)) ≫ Z₂.map (Z₁.map (B'.map (A'.map f))) := by
  simp only [← Functor.map_comp]
  exact congrArg (fun x => Z₂.map (Z₁.map x)) (α.hom.naturality f)

/-- The kernel of `ι ≫ R(A₀ ⟶ A₀/ker p)` is the kernel of `ι ≫ R p`, for `p` an epimorphism. -/
theorem kernelSubobject_comp_map_cokernel_π {𝒜 ℬ : Type*} [Category* 𝒜] [Category* ℬ]
    [Abelian 𝒜] [Abelian ℬ] (R : 𝒜 ⥤ ℬ) {A₀ Y : 𝒜} (p : A₀ ⟶ Y) [Epi p] {B₀ : ℬ}
    (ι : B₀ ⟶ R.obj A₀) :
    kernelSubobject (ι ≫ R.map (cokernel.π (kernelSubobject p).arrow)) =
      kernelSubobject (ι ≫ R.map p) := by
  rw [← Abelian.cokernelKernelSubobjectIso_inv_comp p, R.map_comp, ← Category.assoc]
  exact kernelSubobject_comp_mono _ _

/-- Kernels are unchanged by composing with an isomorphism. -/
theorem kernelSubobject_eq_of_comp_iso {ℬ : Type*} [Category* ℬ] [Abelian ℬ] {O Y Z : ℬ}
    (x : O ⟶ Y) (e : Y ≅ Z) (y : O ⟶ Z) (h : x ≫ e.hom = y) :
    kernelSubobject x = kernelSubobject y := by
  subst h
  exact (kernelSubobject_comp_mono x e.hom).symm

/-- The chase behind
`AlgebraicGeometry.ProjectiveQuot.schemeSubobject_quotientPullback_of_comp_eq`, in an arbitrary
category. -/
theorem comp_map_comp_comp_eq {C D : Type*} [Category* C] [Category* D] (P : C ⥤ D)
    {O' X₀ Y₂ : D} {O A₁ A₂ : C}
    (a : O' ⟶ P.obj O) (b : O ⟶ A₁) (c : A₁ ⟶ A₂) {X : D} (s : P.obj A₁ ⟶ X) (s' : P.obj A₂ ⟶ Y₂)
    (d : O' ⟶ X₀) (e : X₀ ⟶ X) (m : X ⟶ Y₂) (q : X₀ ⟶ Y₂)
    (hFC : a ≫ P.map b ≫ s = d ≫ e) (nat : P.map c ≫ s' = s ≫ m) (hq : e ≫ m = q) :
    (a ≫ P.map (b ≫ c)) ≫ s' = d ≫ q := by
  rw [P.map_comp, Category.assoc, Category.assoc, nat, ← Category.assoc (P.map b),
    ← Category.assoc a, hFC, Category.assoc, hq]

/-- The components of `α⁻¹ ≫ β` for two isomorphisms of functors. -/
theorem symm_trans_hom_app {C D : Type*} [Category* C] [Category* D] {F G H : C ⥤ D}
    (α : G ≅ F) (β : G ≅ H) (X : C) :
    (α.symm ≪≫ β).hom.app X = α.inv.app X ≫ β.hom.app X :=
  rfl

/-- The component at an object of an equation between two ways of contracting three functors. -/
theorem triangle_comp_app {𝒜 ℬ 𝒞 𝒟 : Type*} [Category* 𝒜] [Category* ℬ] [Category* 𝒞]
    [Category* 𝒟] {Fp : 𝒜 ⥤ ℬ} {Fg : ℬ ⥤ 𝒞} {Ff : 𝒞 ⥤ 𝒟} {Fk : ℬ ⥤ 𝒟} {Fq : 𝒜 ⥤ 𝒞}
    {Fr : 𝒜 ⥤ 𝒟} {tkr : Fr ≅ Fp ⋙ Fk} {tk : Fk ≅ Fg ⋙ Ff} {tr : Fr ≅ Fq ⋙ Ff}
    {tq : Fq ≅ Fp ⋙ Fg}
    (h : tkr ≪≫ Functor.isoWhiskerLeft Fp tk =
      tr ≪≫ Functor.isoWhiskerRight tq Ff ≪≫ Functor.associator Fp Fg Ff) (X : 𝒜) :
    tkr.hom.app X ≫ tk.hom.app (Fp.obj X) = tr.hom.app X ≫ Ff.map (tq.hom.app X) := by
  simpa using congrArg (fun e => e.hom.app X) h

/-- The chase behind `AlgebraicGeometry.ProjectiveQuot.readingSite_comp`, in an arbitrary
category. -/
theorem chase_site {C : Type*} [Category* C] {S₀ S₁ S₂ S₃ S₄ S₅ S₆ : C} (H : S₀ ≅ S₁)
    (K : S₀ ⟶ S₂) (R₁ : S₂ ≅ S₃) (M : S₁ ⟶ S₃) (R₂ : S₂ ⟶ S₄) (T' : S₀ ⟶ S₅) (N : S₅ ⟶ S₄)
    (g₁ : S₁ ⟶ S₆) (g₂ : S₆ ⟶ S₀) (s : S₃ ⟶ S₄)
    (c₁ : K ≫ R₁.hom = H.hom ≫ M) (c₂ : K ≫ R₂ = T' ≫ N) (hs : s = R₁.inv ≫ R₂)
    (hG : g₁ ≫ g₂ = H.inv) : M ≫ s = g₁ ≫ g₂ ≫ T' ≫ N := by
  have hM : M = H.inv ≫ K ≫ R₁.hom := by rw [c₁, Iso.inv_hom_id_assoc]
  rw [hs, hM, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, c₂, ← Category.assoc g₁, hG]

/-- Pasting the four comparisons of the reading of a module along `W' ⟶ W ⟶ W₀`, in an
arbitrary category. -/
theorem paste_readingComparisons {C : Type*} [Category* C] {A₀ A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ D₁ : C}
    {x₁ : A₀ ⟶ A₁} {x₂ : A₁ ⟶ A₂} {x₃ : A₂ ⟶ A₃} {x₄ : A₃ ⟶ A₄} {y₁ : A₁ ⟶ B₁} {y₂ : B₁ ⟶ A₃}
    {z₁ : B₁ ⟶ B₂} {z₂ : B₂ ⟶ B₃} {z₃ : B₃ ⟶ B₄} {z₄ : B₄ ⟶ A₄} {w₁ : A₀ ⟶ D₁} {w₂ : D₁ ⟶ B₂}
    (s₁ : x₂ ≫ x₃ = y₁ ≫ y₂) (s₄ : y₂ ≫ x₄ = z₁ ≫ z₂ ≫ z₃ ≫ z₄)
    (s₂ : x₁ ≫ y₁ ≫ z₁ = w₁ ≫ w₂) :
    (x₁ ≫ x₂) ≫ (x₃ ≫ x₄) = w₁ ≫ w₂ ≫ z₂ ≫ z₃ ≫ z₄ := by
  rw [Category.assoc, reassoc_of% s₁, s₄, reassoc_of% s₂]

/-- Two functors carry an equation `a ≫ b = c ≫ d ≫ e ≫ f` to the same equation.  The
equation comes first, so that its category is the one the functors are read on. -/
theorem map_map_comp_eq {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {X Y Y' Y₁ Y₂ Y₃ : C} {a : X ⟶ Y} {b : Y ⟶ Y'} {c : X ⟶ Y₁} {d : Y₁ ⟶ Y₂}
    {e : Y₂ ⟶ Y₃} {f : Y₃ ⟶ Y'} (h : a ≫ b = c ≫ d ≫ e ≫ f) (Z₁ : C ⥤ D) (Z₂ : D ⥤ E) :
    Z₂.map (Z₁.map a) ≫ Z₂.map (Z₁.map b) =
      Z₂.map (Z₁.map c) ≫ Z₂.map (Z₁.map d) ≫ Z₂.map (Z₁.map e) ≫ Z₂.map (Z₁.map f) := by
  simp only [← Functor.map_comp, h]

/-! ### The comparisons for a square of algebraic spaces over represented ones -/

section Abstract

variable {W₀ W W' : BigFppfOver B integerBase B.contains_integerBase}
  {X X' : AlgebraicSpaces B integerBase B.contains_integerBase}
  (pg : W' ⟶ W) (pa : W ⟶ W₀) (pa' : W' ⟶ W₀) (hp : pg ≫ pa = pa')
  (φ : (⟨yoneda.obj W, isAlgebraicSpace_yoneda B integerBase B.contains_integerBase W⟩ :
    AlgebraicSpaces B integerBase B.contains_integerBase) ≅ X)
  (φ' : (⟨yoneda.obj W', isAlgebraicSpace_yoneda B integerBase B.contains_integerBase W'⟩ :
    AlgebraicSpaces B integerBase B.contains_integerBase) ≅ X') (ρ : X' ⟶ X)
  (k : (⟨yoneda.obj W', isAlgebraicSpace_yoneda B integerBase B.contains_integerBase W'⟩ :
    AlgebraicSpaces B integerBase B.contains_integerBase) ⟶ X)
  (hk : (Space.representedSpaceMap B integerBase B.contains_integerBase pg) ≫ φ.hom = k)
  (hsq : φ'.hom ≫ ρ = k)
  (sp : X ⟶ (⟨yoneda.obj W₀, isAlgebraicSpace_yoneda B integerBase B.contains_integerBase W₀⟩ :
    AlgebraicSpaces B integerBase B.contains_integerBase))
  (sp' : X' ⟶ (⟨yoneda.obj W₀, isAlgebraicSpace_yoneda B integerBase B.contains_integerBase W₀⟩ :
    AlgebraicSpaces B integerBase B.contains_integerBase)) (hrel : ρ ≫ sp = sp')
  (hT : φ.hom ≫ sp = (Space.representedSpaceMap B integerBase B.contains_integerBase pa))
  (hT' : φ'.hom ≫ sp' = (Space.representedSpaceMap B integerBase B.contains_integerBase pa'))
  (F₀ : Space.Modules.{u, u} B integerBase B.contains_integerBase (yoneda.obj W₀)
    (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase W₀))
  (hF₀ : F₀.IsQuasicoherentOnSite)

/-- The contraction of the two inverse images along `W' ⟶ W ⟶ W₀`, followed by the transport to
`W' ⟶ W₀`, is the inverse of the comparison of Stacks 03LU at `h_{W' ⟶ W₀}`. -/
theorem readingSite_compIso
    (hab : (Space.representedSpaceMap B integerBase B.contains_integerBase pg) ≫
        (Space.representedSpaceMap B integerBase B.contains_integerBase pa) =
      (Space.representedSpaceMap B integerBase B.contains_integerBase pa')) :
    (Space.representedModulePullbackCompIso B integerBase B.contains_integerBase pg
        pa).hom.app F₀ ≫
      eqToHom (congrArg (fun m : W' ⟶ W₀ => (Space.modulePullback B integerBase
        B.contains_integerBase (Space.representedSpaceMap B integerBase
          B.contains_integerBase m)).obj F₀) hp) =
      (Space.modulePullbackTriangle B integerBase B.contains_integerBase hab).inv.app F₀ := by
  subst hp
  rw [eqToHom_refl, Category.comp_id]
  rfl

/-- **The site half of the compatibility of the readings of a module**: going round
`W' ⟶ W ⟶ W₀` or straight down `W' ⟶ W₀` gives the same comparison of inverse images.  Two
applications of the associativity coherence of Stacks 03LU
(`AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackTriangle_comp`). -/
theorem readingSite_comp :
    (Space.modulePullback B integerBase B.contains_integerBase
        (Space.representedSpaceMap B integerBase B.contains_integerBase pg)).map
        ((Space.modulePullbackTriangle B integerBase B.contains_integerBase hT).hom.app F₀) ≫
      ((Space.modulePullbackTriangle B integerBase B.contains_integerBase hk).symm ≪≫
      Space.modulePullbackTriangle B integerBase B.contains_integerBase hsq).hom.app
        ((Space.modulePullback B integerBase B.contains_integerBase sp).obj F₀) =
      (Space.representedModulePullbackCompIso B integerBase B.contains_integerBase pg pa).hom.app
          F₀ ≫
        eqToHom (congrArg (fun m : W' ⟶ W₀ => (Space.modulePullback B integerBase
          B.contains_integerBase (Space.representedSpaceMap B integerBase
            B.contains_integerBase m)).obj F₀) hp) ≫
        (Space.modulePullbackTriangle B integerBase B.contains_integerBase hT').hom.app F₀ ≫
        (Space.modulePullback B integerBase B.contains_integerBase φ'.hom).map
          ((Space.modulePullbackTriangle B integerBase B.contains_integerBase
            hrel).hom.app F₀) := by
  have hc := Space.modulePushforwardCoherence B integerBase B.contains_integerBase
  have hab : (Space.representedSpaceMap B integerBase B.contains_integerBase pg) ≫
      (Space.representedSpaceMap B integerBase B.contains_integerBase pa) =
      (Space.representedSpaceMap B integerBase B.contains_integerBase pa') :=
    (Space.representedSpaceMap_comp B integerBase B.contains_integerBase _ _).trans
      (congrArg _ hp)
  have hkr : k ≫ sp = (Space.representedSpaceMap B integerBase B.contains_integerBase pa') := by
    rw [← hk, Category.assoc, hT, hab]
  have c1F := triangle_comp_app (hc.modulePullbackTriangle_comp hk hT hab hkr) F₀
  have c2F := triangle_comp_app (hc.modulePullbackTriangle_comp hsq hrel hT' hkr) F₀
  have hs := symm_trans_hom_app
    (Space.modulePullbackTriangle B integerBase B.contains_integerBase hk)
    (Space.modulePullbackTriangle B integerBase B.contains_integerBase hsq)
    ((Space.modulePullback B integerBase B.contains_integerBase sp).obj F₀)
  have hG := readingSite_compIso pg pa pa' hp F₀ hab
  exact chase_site
    ((Space.modulePullbackTriangle B integerBase B.contains_integerBase hab).app F₀) _
    ((Space.modulePullbackTriangle B integerBase B.contains_integerBase hk).app
      ((Space.modulePullback B integerBase B.contains_integerBase sp).obj F₀))
    _ _ _ _ _ _ _ c1F c2F hs hG

/-- **The comparison of the readings along `W' ⟶ W` is natural in the module**: for the square
`φ' ≫ ρ = k = h_{W' ⟶ W} ≫ φ`, the Zariski reading of `M` on `W` pulled back to `W'` is compared
with the reading of `ρ^* M` on `W'` by
`AlgebraicGeometry.Space.representedZariskiModulePullbackIso` followed by the reading of the square
of inverse images, naturally in `M`. -/
theorem readingPullback_naturality
    {M M' : Space.Modules.{u, u} B integerBase B.contains_integerBase X.1 X.2}
    (hM : M.IsQuasicoherentOnSite) (hM' : M'.IsQuasicoherentOnSite) (f : M ⟶ M') :
    (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) pg.left)).map
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((𝒯).obj W) W.left.property).map
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      W).inverse.map ((Space.modulePullback B integerBase B.contains_integerBase φ.hom).map f))) ≫
        ((Space.representedZariskiModulePullbackIso B integerBase B.contains_integerBase pg
      (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase pg)
      ((Space.modulePullback B integerBase B.contains_integerBase φ.hom).obj M')
      (Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase
      B.contains_integerBase _ M' hM')).hom ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((𝒯).obj W') W'.left.property).map
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      W').inverse.map
        (((Space.modulePullbackTriangle B integerBase B.contains_integerBase hk).symm ≪≫
      Space.modulePullbackTriangle B integerBase B.contains_integerBase hsq).hom.app M'))) =
      ((Space.representedZariskiModulePullbackIso B integerBase B.contains_integerBase pg
      (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase pg)
      ((Space.modulePullback B integerBase B.contains_integerBase φ.hom).obj M)
      (Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase
      B.contains_integerBase _ M hM)).hom ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((𝒯).obj W') W'.left.property).map
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      W').inverse.map
        (((Space.modulePullbackTriangle B integerBase B.contains_integerBase hk).symm ≪≫
      Space.modulePullbackTriangle B integerBase B.contains_integerBase hsq).hom.app M))) ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((𝒯).obj W') W'.left.property).map
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      W').inverse.map ((Space.modulePullback B integerBase B.contains_integerBase φ'.hom).map
        ((Space.modulePullback B integerBase B.contains_integerBase ρ).map f))) := by
  have n1 := Space.representedZariskiModulePullbackIso_naturality B integerBase
    B.contains_integerBase pg
    (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase pg)
    (Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase
      B.contains_integerBase φ.hom M hM)
    (Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase
      B.contains_integerBase φ.hom M' hM')
    ((Space.modulePullback B integerBase B.contains_integerBase φ.hom).map f)
  have n2 := map_map_naturality
    ((Space.modulePullbackTriangle B integerBase B.contains_integerBase hk).symm ≪≫
      Space.modulePullbackTriangle B integerBase B.contains_integerBase hsq)
    (Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      W').inverse
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((𝒯).obj W') W'.left.property) f
  exact comp_eq_comp_of_squares n1 n2

/-- Pasting the three comparisons of `AlgebraicGeometry.ProjectiveQuot.readingFree_bracket`, in an
arbitrary category. -/
theorem paste_bracket {C : Type*} [Category* C] {A₀ A₁ A₂ A₃ A₄ B₁ B₂ B₄ D₁ : C}
    {x₁ : A₀ ⟶ A₁} {x₂ : A₁ ⟶ A₂} {x₃ : A₂ ⟶ A₃} {x₄ : A₃ ⟶ A₄} {y₁ : A₁ ⟶ B₁} {y₂ : B₁ ⟶ A₃}
    {z₁ : B₁ ⟶ B₂} {z₃ : B₂ ⟶ B₄} {z₄ : B₄ ⟶ A₄} {w₁ : A₀ ⟶ D₁} {w₂ : D₁ ⟶ B₂}
    (s₁ : x₂ ≫ x₃ = y₁ ≫ y₂) (s₄ : y₂ ≫ x₄ = z₁ ≫ z₃ ≫ z₄)
    (s₂ : x₁ ≫ y₁ ≫ z₁ = w₁ ≫ w₂) :
    (x₁ ≫ x₂) ≫ (x₃ ≫ x₄) = w₁ ≫ w₂ ≫ z₃ ≫ z₄ := by
  rw [Category.assoc, reassoc_of% s₁, s₄, reassoc_of% s₂]

/-- `AlgebraicGeometry.ProjectiveQuot.paste_bracket` with an identity morphism in the middle of the
second square. -/
theorem paste_bracket_of_eq_id {C : Type*} [Category* C] {A₀ A₁ A₂ A₃ A₄ B₁ B₂ B₄ D₁ : C}
    {x₁ : A₀ ⟶ A₁} {x₂ : A₁ ⟶ A₂} {x₃ : A₂ ⟶ A₃} {x₄ : A₃ ⟶ A₄} {y₁ : A₁ ⟶ B₁} {y₂ : B₁ ⟶ A₃}
    {z₁ : B₁ ⟶ B₂} {z₂ : B₂ ⟶ B₂} {z₃ : B₂ ⟶ B₄} {z₄ : B₄ ⟶ A₄} {w₁ : A₀ ⟶ D₁} {w₂ : D₁ ⟶ B₂}
    (s₁ : x₂ ≫ x₃ = y₁ ≫ y₂) (s₄ : y₂ ≫ x₄ = z₁ ≫ z₂ ≫ z₃ ≫ z₄) (hz : z₂ = 𝟙 _)
    (s₂ : x₁ ≫ y₁ ≫ z₁ = w₁ ≫ w₂) :
    (x₁ ≫ x₂) ≫ (x₃ ≫ x₄) = w₁ ≫ w₂ ≫ z₃ ≫ z₄ := by
  simpa [hz] using paste_readingComparisons s₁ s₄ s₂

/-- Two functors carry a transport along `X = X` to an identity. -/
theorem map_map_eqToHom_self {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (Z₁ : C ⥤ D) (Z₂ : D ⥤ E) {X : C} (h : X = X) : Z₂.map (Z₁.map (eqToHom h)) = 𝟙 _ := by
  simp

/-- **The comparisons of the readings of a module along `W' ⟶ W ⟶ W₀` paste to the comparison
along the composite `W' ⟶ W₀`**: pulling back along `W' ⟶ W` the comparison below `W ⟶ W₀`, then
comparing below `W' ⟶ W`, is contracting the two pullbacks of modules on the schemes and comparing
below the composite.  This is the naturality of the comparison below `W' ⟶ W`, its composition law
(`AlgebraicGeometry.Space.representedZariskiModulePullbackIso_comp`) and the site half
`AlgebraicGeometry.ProjectiveQuot.readingSite_comp`. -/
theorem readingFree_bracket
    (hTc : φ'.hom ≫ sp' = (Space.representedSpaceMap B integerBase B.contains_integerBase
      (pg ≫ pa))) :
    ((Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) pg.left)).map
      (Space.representedZariskiModulePullbackIso B integerBase B.contains_integerBase pa
      (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase pa)
      F₀ hF₀).hom ≫
        (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) pg.left)).map
          ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((𝒯).obj W) W.left.property).map
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      W).inverse.map
        ((Space.modulePullbackTriangle B integerBase B.contains_integerBase hT).hom.app F₀)))) ≫
      ((Space.representedZariskiModulePullbackIso B integerBase B.contains_integerBase pg
      (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase pg)
      ((Space.modulePullback B integerBase B.contains_integerBase φ.hom).obj
        ((Space.modulePullback B integerBase B.contains_integerBase sp).obj F₀))
      (Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase
      B.contains_integerBase φ.hom
        ((Space.modulePullback B integerBase B.contains_integerBase sp).obj F₀)
        (Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase
      B.contains_integerBase sp F₀ hF₀))).hom ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((𝒯).obj W') W'.left.property).map
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      W').inverse.map
        (((Space.modulePullbackTriangle B integerBase B.contains_integerBase hk).symm ≪≫
      Space.modulePullbackTriangle B integerBase B.contains_integerBase hsq).hom.app
        ((Space.modulePullback B integerBase B.contains_integerBase sp).obj F₀)))) =
      (Scheme.Modules.pullbackComp
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) pg.left)
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            pa.left)).hom.app
          (Space.representedZariskiModule B integerBase B.contains_integerBase W₀ F₀) ≫
        (Space.representedZariskiModulePullbackIso B integerBase B.contains_integerBase (pg ≫ pa)
      (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase (pg ≫ pa))
      F₀ hF₀).hom ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((𝒯).obj W') W'.left.property).map
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      W').inverse.map
        ((Space.modulePullbackTriangle B integerBase B.contains_integerBase hTc).hom.app F₀)) ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((𝒯).obj W') W'.left.property).map
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      W').inverse.map ((Space.modulePullback B integerBase B.contains_integerBase φ'.hom).map
        ((Space.modulePullbackTriangle B integerBase B.contains_integerBase hrel).hom.app
          F₀))) := by
  have s1 := Space.representedZariskiModulePullbackIso_naturality B integerBase
    B.contains_integerBase pg
    (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase pg)
    (Space.isQuasicoherentOnSite_modulePullback_representedSpaceMap B integerBase
      B.contains_integerBase pa
      (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase pa) F₀ hF₀)
    (Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase
      B.contains_integerBase φ.hom
        ((Space.modulePullback B integerBase B.contains_integerBase sp).obj F₀)
        (Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase
      B.contains_integerBase sp F₀ hF₀))
    ((Space.modulePullbackTriangle B integerBase B.contains_integerBase hT).hom.app F₀)
  have s2 := Space.representedZariskiModulePullbackIso_comp B integerBase B.contains_integerBase
    pg pa (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase pg)
    (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase pa)
    (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase (pg ≫ pa))
    F₀ hF₀
  have s4 := map_map_comp_eq
    (readingSite_comp pg pa (pg ≫ pa) rfl φ φ' ρ k hk hsq sp sp' hrel hT hTc F₀)
    (Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      W').inverse
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((𝒯).obj W') W'.left.property)
  exact paste_bracket_of_eq_id s1 s4 (map_map_eqToHom_self _ _ _) s2


end Abstract

end AlgebraicGeometry.ProjectiveQuot

end
