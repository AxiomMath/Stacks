module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackKernelNaturality
public import StacksFrontier.AlgebraicGeometry.Quot.QuotArtinAxioms
public import StacksFrontier.Deformation.Artin.Infinitesimal.DeformationSpaceComparison

/-!
# The split thickenings `X_{k[V]}` of `X_k` for the Quot functor

Let `D` be a situation of Stacks 09TR over a base `B` with a unique point over every scheme of
the site, `k` a field with `Spec k` in the site over `S` and `V` a finite-dimensional
`k`-vector space. The base change `X_{k[V]}` of the situation to `Spec k[V]` is a split
square-zero thickening of `X_k`, with retraction induced by `k ⟶ k[V]`, section induced by
`k[V] ⟶ k` and square-zero functions the pullbacks of the elements of `V ⊆ k[V]`; and a module
on `X_{k[V]}` flat over `k[V]` satisfies the flatness hypothesis of
`AlgebraicGeometry.Space.retractionCopowerExtension`. These are the split thickenings of
`AlgebraicGeometry.Space.CoherentSituation.isSplitThickeningBy`, for the situation of Stacks 08KB
on the morphism of `D`, at the test schemes `Spec k` and `Spec k[V]`.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.morphismCoherentSituation`: the situation of Stacks 08KB
  on the morphism of `D`.
* `AlgebraicGeometry.Space.sqRetraction`: the retraction `Spec k[V] ⟶ Spec k`.
* `AlgebraicGeometry.Space.QuotSituation.sqFunctions`: the square-zero functions `V ⟶ Γ(k[V])`.
* `AlgebraicGeometry.Space.QuotSituation.sqExtension`: the extension
  `0 ⟶ 𝒢₀ ⊗ V ⟶ r_*𝒢 ⟶ 𝒢₀ ⟶ 0` of a module `𝒢` on `X_{k[V]}` flat over `k[V]`.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.sq_isSplitThickeningBy`: `X_{k[V]}` is a split
  square-zero thickening of `X_k` by `V`.
* `AlgebraicGeometry.Space.QuotSituation.sq_transfer_functions`: the transfer along
  `Spec k[W] ⟶ Spec k[V]` carries the square-zero function of `v` to that of `f v`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation Deformation.Artin

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The spectra `Spec k[V]` as objects of the site -/

section Objects

variable (hS) {k : Type u} [Field k] (toS : Spec (.of k) ⟶ S) (hk : B.Contains (Spec (.of k)))

/-- `Spec k[V]`, as an object of the site over `S`. -/
abbrev sqObj (V : FGModuleCat.{u} k) : BigFppfOver B S hS :=
  squareZeroOver k B S hS toS ((fgSiteModule B hk).obj V)

/-- The section `Spec k ⟶ Spec k[V]` of `k[V] ⟶ k`. -/
abbrev sqArrow (V : FGModuleCat.{u} k) : algebraOver k B S hS toS hk ⟶ sqObj hS toS hk V :=
  squareZeroArrow k B S hS toS hk ((fgSiteModule B hk).obj V)

/-- The morphism `Spec k[W] ⟶ Spec k[V]` of `k[f] : k[V] ⟶ k[W]`. -/
abbrev sqMap {V W : FGModuleCat.{u} k} (f : V ⟶ W) : sqObj hS toS hk W ⟶ sqObj hS toS hk V :=
  squareZeroOverMap k B S hS toS ((fgSiteModule B hk).map f)

/-- The retraction `Spec k[V] ⟶ Spec k` of the inclusion `k ⟶ k[V]`. -/
def sqRetraction (V : FGModuleCat.{u} k) : sqObj hS toS hk V ⟶ algebraOver k B S hS toS hk :=
  Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom k ((fgSiteModule B hk).obj V).obj))) :
      B.obj ((fgSiteModule B hk).obj V).property ⟶ B.obj hk) (by
    apply ObjectProperty.hom_ext
    rfl)

/-- The section `Spec k ⟶ Spec k[V]` followed by the retraction is the identity. -/
theorem sqArrow_sqRetraction (V : FGModuleCat.{u} k) :
    sqArrow hS toS hk V ≫ sqRetraction hS toS hk V = 𝟙 _ := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k
      ((fgSiteModule B hk).obj V).obj).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom k ((fgSiteModule B hk).obj V).obj)) = 𝟙 _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (TrivSqZeroExt.inlHom k ((fgSiteModule B hk).obj V).obj) ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom k k ((fgSiteModule B hk).obj V).obj).toRingHom =
        𝟙 (CommRingCat.of k) := by
    apply CommRingCat.hom_ext
    ext a
    simp
  rw [h, Spec.map_id]

/-- The retractions commute with `Spec k[W] ⟶ Spec k[V]`. -/
theorem sqMap_sqRetraction {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    sqMap hS toS hk f ≫ sqRetraction hS toS hk V = sqRetraction hS toS hk W := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  show Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.map ((fgSiteModule B hk).map f).hom.hom).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom k ((fgSiteModule B hk).obj V).obj)) =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom k ((fgSiteModule B hk).obj W).obj))
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  · simp
  · show (TrivSqZeroExt.map ((fgSiteModule B hk).map f).hom.hom (TrivSqZeroExt.inl a)).snd =
      (TrivSqZeroExt.inl a : TrivSqZeroExt k ((fgSiteModule B hk).obj W).obj).snd
    rw [TrivSqZeroExt.map_inl]

/-- The sections commute with `Spec k[W] ⟶ Spec k[V]`. -/
theorem sqArrow_sqMap {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    sqArrow hS toS hk W ≫ sqMap hS toS hk f = sqArrow hS toS hk V :=
  squareZeroArrow_naturality k B S hS toS hk ((fgSiteModule B hk).map f)

end Objects

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-- The situation of Stacks 08KB on the morphism of `D`: its base changes, their projections and
the morphisms between them are those of `D`. -/
abbrev morphismCoherentSituation : CoherentSituation B S hS :=
  ⟨D.X, D.Y, D.f, D.finitePresentation⟩

variable (ι : ∀ T : BigFppfOver B S hS, (schemeSpaceFunctor B S hS).obj T ⟶ D.Y)
  [hY : ∀ T : BigFppfOver B S hS, Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y)]
  {k : Type u} [Field k] (toS : Spec (.of k) ⟶ S) (hk : B.Contains (Spec (.of k)))

/-! ### The global functions of `Spec k` and `Spec k[V]` -/

/-- The test scheme `Spec k`. -/
def sq₀ : SchemesOver D.Y := D.testOver ι (algebraOver k B S hS toS hk)

/-- The test scheme `Spec k[V]`. -/
def sqT (V : FGModuleCat.{u} k) : SchemesOver D.Y := D.testOver ι (sqObj hS toS hk V)

/-- The section `Spec k ⟶ Spec k[V]`, as a morphism of test schemes. -/
def sqβ (V : FGModuleCat.{u} k) : D.sq₀ ι toS hk ⟶ D.sqT ι toS hk V :=
  D.testHom ι (sqArrow hS toS hk V)

/-- The retraction `Spec k[V] ⟶ Spec k`, as a morphism of test schemes. -/
def sqπ (V : FGModuleCat.{u} k) : D.sqT ι toS hk V ⟶ D.sq₀ ι toS hk :=
  D.testHom ι (sqRetraction hS toS hk V)

/-- The morphism `Spec k[W] ⟶ Spec k[V]` of `k[f]`, as a morphism of test schemes. -/
def sqσ {V W : FGModuleCat.{u} k} (f : V ⟶ W) : D.sqT ι toS hk W ⟶ D.sqT ι toS hk V :=
  D.testHom ι (sqMap hS toS hk f)

omit hY in
/-- The scheme underlying the test scheme `Spec k` is `Spec k`. -/
theorem toScheme_sq₀ :
    (BigFppfOver.toScheme B S hS).obj (D.sq₀ ι toS hk).left = Spec (.of k) := rfl

omit hY in
/-- The scheme underlying the test scheme `Spec k[V]` is `Spec k[V]`. -/
theorem toScheme_sqT (V : FGModuleCat.{u} k) :
    (BigFppfOver.toScheme B S hS).obj (D.sqT ι toS hk V).left =
      Spec (squareZeroRing k ((fgSiteModule B hk).obj V).obj) := rfl

/-- The identification of `k` with the global functions of `Spec k`. -/
def sqRing₀ : k ≃+* D.morphismCoherentSituation.testRing (D.sq₀ ι toS hk) :=
  RingEquiv.ofBijective (D.morphismCoherentSituation.testRingOfSpec _ (D.toScheme_sq₀ ι toS hk)).hom
    (D.morphismCoherentSituation.bijective_testRingOfSpec _ (D.toScheme_sq₀ ι toS hk))

/-- The identification of `k[V]` with the global functions of `Spec k[V]`. -/
def sqRing (V : FGModuleCat.{u} k) :
    TrivSqZeroExt k ((fgSiteModule B hk).obj V).obj ≃+*
      D.morphismCoherentSituation.testRing (D.sqT ι toS hk V) :=
  RingEquiv.ofBijective
    (D.morphismCoherentSituation.testRingOfSpec _ (D.toScheme_sqT ι toS hk V)).hom
    (D.morphismCoherentSituation.bijective_testRingOfSpec _ (D.toScheme_sqT ι toS hk V))

/-- The scalars `k ⟶ Γ(Spec k)`. -/
abbrev sqScalars : k →+* D.morphismCoherentSituation.testRing (D.sq₀ ι toS hk) :=
  (D.sqRing₀ ι toS hk).toRingHom

/-- A vector of `V`, as a vector of the site module of `V`. -/
def sqVec (V : FGModuleCat.{u} k) : ↥V →ₗ[k] ((fgSiteModule B hk).obj V).obj :=
  LinearMap.id

/-- `sqVec` intertwines `f : V ⟶ W` with its image on site modules. -/
theorem sqVec_map {V W : FGModuleCat.{u} k} (f : V ⟶ W) (v : ↥V) :
    sqVec hk W (f.hom.hom v) = ((fgSiteModule B hk).map f).hom.hom (sqVec hk V v) := rfl

/-- The square-zero functions `V ⟶ Γ(Spec k[V])`. -/
def sqFunctions (V : FGModuleCat.{u} k) :
    ↥V →+ D.morphismCoherentSituation.testRing (D.sqT ι toS hk V) :=
  (D.sqRing ι toS hk V).toAddMonoidHom.comp
    ((TrivSqZeroExt.inrHom k ((fgSiteModule B hk).obj V).obj).toAddMonoidHom.comp
      (sqVec hk V).toAddMonoidHom)

omit hY in
/-- The square-zero function of `v` is the image of `(0, v) ∈ k[V]`. -/
theorem sqFunctions_apply (V : FGModuleCat.{u} k) (v : ↥V) :
    D.sqFunctions ι toS hk V v = D.sqRing ι toS hk V (TrivSqZeroExt.inr (sqVec hk V v)) := rfl

include hY in
/-- Pullback of functions along the section `Spec k ⟶ Spec k[V]` is the residue map. -/
theorem siteΓ_sqArrow (V : FGModuleCat.{u} k)
    (y : TrivSqZeroExt k ((fgSiteModule B hk).obj V).obj) :
    (CoherentSituation.siteΓ (D.sqβ ι toS hk V).left).hom (D.sqRing ι toS hk V y) =
      D.sqRing₀ ι toS hk y.fst := by
  have key := D.morphismCoherentSituation.siteΓ_testRingOfSpec (T₁ := D.sq₀ ι toS hk)
    (T₀ := D.sqT ι toS hk V) (D.sqβ ι toS hk V).left (D.toScheme_sqT ι toS hk V)
    (D.toScheme_sq₀ ι toS hk)
    (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k ((fgSiteModule B hk).obj V).obj).toRingHom)
    rfl
  exact congrArg (fun f => f.hom y) key

include hY in
/-- Pullback of functions along the retraction `Spec k[V] ⟶ Spec k` is the inclusion. -/
theorem siteΓ_sqRetraction (V : FGModuleCat.{u} k) (c : k) :
    (CoherentSituation.siteΓ (D.sqπ ι toS hk V).left).hom
        (D.sqRing₀ ι toS hk c) = D.sqRing ι toS hk V (TrivSqZeroExt.inl c) := by
  have key := D.morphismCoherentSituation.siteΓ_testRingOfSpec (T₁ := D.sqT ι toS hk V)
    (T₀ := D.sq₀ ι toS hk) (D.sqπ ι toS hk V).left (D.toScheme_sq₀ ι toS hk)
    (D.toScheme_sqT ι toS hk V)
    (CommRingCat.ofHom (TrivSqZeroExt.inlHom k ((fgSiteModule B hk).obj V).obj))
    rfl
  exact congrArg (fun f => f.hom c) key

include hY in
/-- Pullback of functions along `Spec k[W] ⟶ Spec k[V]` is `k[f]`. -/
theorem siteΓ_sqMap {V W : FGModuleCat.{u} k} (f : V ⟶ W)
    (y : TrivSqZeroExt k ((fgSiteModule B hk).obj V).obj) :
    (CoherentSituation.siteΓ (D.sqσ ι toS hk f).left).hom (D.sqRing ι toS hk V y) =
      D.sqRing ι toS hk W (TrivSqZeroExt.map ((fgSiteModule B hk).map f).hom.hom y) := by
  have key := D.morphismCoherentSituation.siteΓ_testRingOfSpec (T₁ := D.sqT ι toS hk W)
    (T₀ := D.sqT ι toS hk V) (D.sqσ ι toS hk f).left (D.toScheme_sqT ι toS hk V)
    (D.toScheme_sqT ι toS hk W) (squareZeroRingMap k B ((fgSiteModule B hk).map f))
    rfl
  exact congrArg (fun g => g.hom y) key

/-! ### The split thickening -/

include hY in
/-- The section `Spec k ⟶ Spec k[V]` followed by the retraction is the identity, as
morphisms of test schemes. -/
theorem sqβ_sqπ (V : FGModuleCat.{u} k) :
    D.sqβ ι toS hk V ≫ D.sqπ ι toS hk V = 𝟙 _ :=
  CostructuredArrow.hom_ext _ _ (sqArrow_sqRetraction hS toS hk V)

include hY in
/-- The retractions commute with `Spec k[W] ⟶ Spec k[V]`, as morphisms of test schemes. -/
theorem sqσ_sqπ {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    D.sqσ ι toS hk f ≫ D.sqπ ι toS hk V = D.sqπ ι toS hk W :=
  CostructuredArrow.hom_ext _ _ (sqMap_sqRetraction hS toS hk f)

include hY in
/-- The sections commute with `Spec k[W] ⟶ Spec k[V]`, as morphisms of test schemes. -/
theorem sqβ_sqσ {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    D.sqβ ι toS hk W ≫ D.sqσ ι toS hk f = D.sqβ ι toS hk V :=
  CostructuredArrow.hom_ext _ _ (sqArrow_sqMap hS toS hk f)

omit hY in
/-- The product of two square-zero functions is zero. -/
theorem sqFunctions_mul (V : FGModuleCat.{u} k) (v w : ↥V) :
    D.sqFunctions ι toS hk V v * D.sqFunctions ι toS hk V w = 0 := by
  rw [sqFunctions_apply, sqFunctions_apply, ← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]

omit hY in
/-- The square-zero functions `V ⟶ Γ(Spec k[V])` are injective. -/
theorem sqFunctions_injective (V : FGModuleCat.{u} k) :
    Function.Injective (D.sqFunctions ι toS hk V) :=
  (D.sqRing ι toS hk V).injective.comp (TrivSqZeroExt.inr_injective.comp (fun _ _ h => h))

include hY in
/-- The square-zero functions vanish along the section `Spec k ⟶ Spec k[V]`. -/
theorem siteΓ_sqArrow_sqFunctions (V : FGModuleCat.{u} k) (v : ↥V) :
    (CoherentSituation.siteΓ (D.sqβ ι toS hk V).left).hom
      (D.sqFunctions ι toS hk V v) = 0 := by
  rw [sqFunctions_apply, siteΓ_sqArrow, TrivSqZeroExt.fst_inr, map_zero]

include hY in
/-- The kernel of pullback of functions along the section `Spec k ⟶ Spec k[V]` is the ideal
generated by the square-zero functions. -/
theorem ker_siteΓ_sqArrow (V : FGModuleCat.{u} k) :
    RingHom.ker (CoherentSituation.siteΓ (D.sqβ ι toS hk V).left).hom =
      Ideal.span (Set.range (D.sqFunctions ι toS hk V)) := by
  apply le_antisymm
  · intro t ht
    obtain ⟨y, rfl⟩ := (D.sqRing ι toS hk V).surjective t
    have h0 : D.sqRing₀ ι toS hk y.fst = 0 := by
      rwa [← D.siteΓ_sqArrow ι toS hk V]
    have hfst : y.fst = 0 := by simpa using h0
    have hy : y = TrivSqZeroExt.inr y.snd := TrivSqZeroExt.ext (by simp [hfst]) (by simp)
    rw [hy]
    exact Ideal.subset_span ⟨y.snd, rfl⟩
  · rw [Ideal.span_le]
    rintro _ ⟨v, rfl⟩
    exact D.siteΓ_sqArrow_sqFunctions ι toS hk V v

include hY in
/-- The square-zero function of `c • v` is the pullback of `c` along the retraction times the
square-zero function of `v`. -/
theorem sqFunctions_smul (V : FGModuleCat.{u} k) (c : k) (v : ↥V) :
    D.sqFunctions ι toS hk V (c • v) =
      (CoherentSituation.siteΓ (D.sqπ ι toS hk V).left).hom
        (D.sqScalars ι toS hk c) * D.sqFunctions ι toS hk V v := by
  rw [sqFunctions_apply, sqFunctions_apply, map_smul]
  show _ = (CoherentSituation.siteΓ (D.sqπ ι toS hk V).left).hom
      (D.sqRing₀ ι toS hk c) * _
  rw [D.siteΓ_sqRetraction ι toS hk V, ← map_mul, TrivSqZeroExt.inl_mul_inr]

/-- The residue `Γ(Spec k[V]) ⟶ k`. -/
def sqResidue (V : FGModuleCat.{u} k) :
    D.morphismCoherentSituation.testRing (D.sqT ι toS hk V) →+* k :=
  (TrivSqZeroExt.fstHom k k ((fgSiteModule B hk).obj V).obj).toRingHom.comp
    (D.sqRing ι toS hk V).symm.toRingHom

omit hY in
/-- The square-zero function of `v` times a function `a` is the square-zero function of
`r(a) • v`, `r` the residue. -/
theorem sqFunctions_mul_eq (V : FGModuleCat.{u} k) (v : ↥V)
    (a : D.morphismCoherentSituation.testRing (D.sqT ι toS hk V)) :
    D.sqFunctions ι toS hk V v * a = D.sqFunctions ι toS hk V (D.sqResidue ι toS hk V a • v) := by
  obtain ⟨y, rfl⟩ := (D.sqRing ι toS hk V).surjective a
  rw [sqFunctions_apply, sqFunctions_apply, map_smul, ← map_mul]
  show _ = D.sqRing ι toS hk V (TrivSqZeroExt.inr ((TrivSqZeroExt.fstHom k k _)
      ((D.sqRing ι toS hk V).symm (D.sqRing ι toS hk V y)) • sqVec hk V v))
  rw [RingEquiv.symm_apply_apply, TrivSqZeroExt.inr_mul_eq]
  rfl

include hY in
/-- A function on `Spec k[V]` with zero residue vanishes along the section
`Spec k ⟶ Spec k[V]`. -/
theorem siteΓ_sqArrow_of_sqResidue_eq_zero (V : FGModuleCat.{u} k)
    (a : D.morphismCoherentSituation.testRing (D.sqT ι toS hk V))
    (ha : D.sqResidue ι toS hk V a = 0) :
    (CoherentSituation.siteΓ (D.sqβ ι toS hk V).left).hom a = 0 := by
  obtain ⟨y, rfl⟩ := (D.sqRing ι toS hk V).surjective a
  rw [D.siteΓ_sqArrow ι toS hk V]
  have : y.fst = 0 := by
    have h := ha
    simp only [sqResidue, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at h
    exact h
  rw [this, map_zero]

include hY in
/-- Pullback of functions along `Spec k[W] ⟶ Spec k[V]` carries the square-zero function of
`v` to that of `f v`. -/
theorem siteΓ_sqMap_sqFunctions {V W : FGModuleCat.{u} k} (f : V ⟶ W) (v : ↥V) :
    (CoherentSituation.siteΓ (D.sqσ ι toS hk f).left).hom
      (D.sqFunctions ι toS hk V v) = D.sqFunctions ι toS hk W (f.hom.hom v) := by
  rw [sqFunctions_apply, siteΓ_sqMap, sqFunctions_apply, sqVec_map]
  congr 1
  exact TrivSqZeroExt.ext (by simp) (by simp)

/-! ### The split thickening `X_{k[V]}` of `X_k` -/

/-- The representability of the retraction. -/
abbrev sqRep (V : FGModuleCat.{u} k) :
    yoneda.relativelyRepresentable (D.relativeMap (D.sqπ ι toS hk V)).hom :=
  D.morphismCoherentSituation.splitRep (D.sqπ ι toS hk V)

include hY in
/-- On the base changes of `D`, the section followed by the retraction is the identity. -/
theorem sqI_sqR (V : FGModuleCat.{u} k) :
    D.relativeMap (D.sqβ ι toS hk V) ≫ D.relativeMap (D.sqπ ι toS hk V) = 𝟙 _ :=
  D.morphismCoherentSituation.relativeMap_comp_relativeMap_eq_id _ _
    (D.sqβ_sqπ ι toS hk V)

include hY in
/-- On the base changes of `D`, the retractions commute with the map induced by
`Spec k[W] ⟶ Spec k[V]`. -/
theorem sqH_sqR {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    D.relativeMap (D.sqσ ι toS hk f) ≫ D.relativeMap (D.sqπ ι toS hk V) =
      D.relativeMap (D.sqπ ι toS hk W) := by
  rw [← baseChangeMap_comp, D.sqσ_sqπ ι toS hk f]

include hY in
/-- On the base changes of `D`, the sections commute with the map induced by
`Spec k[W] ⟶ Spec k[V]`. -/
theorem sqI_sqH {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    D.relativeMap (D.sqβ ι toS hk W) ≫ D.relativeMap (D.sqσ ι toS hk f) =
      D.relativeMap (D.sqβ ι toS hk V) := by
  rw [← baseChangeMap_comp, D.sqβ_sqσ ι toS hk f]

/-- The scalars `k ⟶ Γ(X_k, 𝒪)`. -/
abbrev sqScalars₀ : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
      (D.space (D.sq₀ ι toS hk)).1 (D.space (D.sq₀ ι toS hk)).2).O) :=
  D.morphismCoherentSituation.splitScalars₀ (D.sqScalars ι toS hk)

/-- The scalars `k ⟶ Γ(X_{k[V]}, 𝒪)`. -/
abbrev sqScalars₁ (V : FGModuleCat.{u} k) : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
      (D.space (D.sqT ι toS hk V)).1 (D.space (D.sqT ι toS hk V)).2).O) :=
  D.morphismCoherentSituation.splitScalars₁ (D.sqπ ι toS hk V) (D.sqScalars ι toS hk)

/-- The square-zero functions on `X_{k[V]}`. -/
abbrev sqSplitFunctions (V : FGModuleCat.{u} k) :
    ↥V →+ Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
      (D.space (D.sqT ι toS hk V)).1 (D.space (D.sqT ι toS hk V)).2).O) :=
  D.morphismCoherentSituation.splitFunctions V (D.sqFunctions ι toS hk V)

/-- The `k`-linear structure on the modules of `X_k`. -/
abbrev sqLinear : Linear k (Modules.{u, u} B S hS (D.space (D.sq₀ ι toS hk)).1
    (D.space (D.sq₀ ι toS hk)).2) :=
  retractionLinear B S hS (X₀ := D.space (D.sq₀ ι toS hk)) (D.sqScalars₀ ι toS hk)

/-- The scheme underlying the test scheme `Spec k` is affine. -/
instance isAffine_sq₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj (D.sq₀ ι toS hk).left) :=
  inferInstanceAs (IsAffine (Spec (.of k)))

/-- The scheme underlying the test scheme `Spec k[V]` is affine. -/
instance isAffine_sqT (V : FGModuleCat.{u} k) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (D.sqT ι toS hk V).left) :=
  inferInstanceAs (IsAffine (Spec _))

include hY in
/-- `X_{k[V]}` is a split square-zero thickening of `X_k` by `V`. -/
theorem sq_isSplitThickeningBy (V : FGModuleCat.{u} k) :
    IsSplitThickeningBy B S hS (D.relativeMap (D.sqπ ι toS hk V)) (D.sqRep ι toS hk V)
      (D.relativeMap (D.sqβ ι toS hk V))
      (D.sqI_sqR ι toS hk V) V (D.sqScalars₀ ι toS hk) (D.sqScalars₁ ι toS hk V)
      (D.sqSplitFunctions ι toS hk V) :=
  D.morphismCoherentSituation.isSplitThickeningBy _ _ (D.sqβ_sqπ ι toS hk V) V
    (D.sqScalars ι toS hk) (D.sqFunctions ι toS hk V) inferInstance inferInstance
    (D.siteΓ_sqArrow_sqFunctions ι toS hk V) (D.ker_siteΓ_sqArrow ι toS hk V)
    (D.sqFunctions_mul ι toS hk V) (D.sqFunctions_smul ι toS hk V)

/-- The extension `0 ⟶ 𝒢₀ ⊗ V ⟶ r_*𝒢 ⟶ 𝒢₀ ⟶ 0` of a module `𝒢` on `X_{k[V]}` flat over
`k[V]`, for an identification `ψ` of its restriction to `X_k` with `𝒢₀`. -/
def sqExtension (V : FGModuleCat.{u} k)
    (G : Modules.{u, u} B S hS (D.space (D.sqT ι toS hk V)).1 (D.space (D.sqT ι toS hk V)).2)
    (G₀ : Modules.{u, u} B S hS (D.space (D.sq₀ ι toS hk)).1 (D.space (D.sq₀ ι toS hk)).2)
    (ψ : (modulePullback B S hS (D.relativeMap (D.sqβ ι toS hk V))).obj G ≅ G₀)
    (hG : G.IsQuasicoherentOnSite)
    (hflat : IsFlatOver B S hS (D.space (D.sqT ι toS hk V)).2
      (D.projection (D.sqT ι toS hk V)).hom G) :
    letI := D.sqLinear ι toS hk
    ModuleDeformation.CopowerExtension G₀ V :=
  retractionCopowerExtension B S hS G G₀ ψ hG (D.sq_isSplitThickeningBy ι toS hk V)
    (fun U hU n hn j => D.morphismCoherentSituation.splitFlat_of_isFlatOver _ _
      (D.sqβ_sqπ ι toS hk V) V (D.sqFunctions ι toS hk V) inferInstance
      inferInstance (D.sqResidue ι toS hk V) (D.sqFunctions_injective ι toS hk V)
      (D.sqFunctions_mul_eq ι toS hk V) (D.siteΓ_sqArrow_of_sqResidue_eq_zero ι toS hk V) G hG hflat
      U hU n hn j)

/-- The projection of `sqExtension` is `AlgebraicGeometry.Space.retractionProjection`. -/
theorem sqExtension_p (V : FGModuleCat.{u} k)
    (G : Modules.{u, u} B S hS (D.space (D.sqT ι toS hk V)).1 (D.space (D.sqT ι toS hk V)).2)
    (G₀ : Modules.{u, u} B S hS (D.space (D.sq₀ ι toS hk)).1 (D.space (D.sq₀ ι toS hk)).2)
    (ψ : (modulePullback B S hS (D.relativeMap (D.sqβ ι toS hk V))).obj G ≅ G₀)
    (hG : G.IsQuasicoherentOnSite)
    (hflat : IsFlatOver B S hS (D.space (D.sqT ι toS hk V)).2
      (D.projection (D.sqT ι toS hk V)).hom G) :
    letI := D.sqLinear ι toS hk
    (D.sqExtension ι toS hk V G G₀ ψ hG hflat).p =
      retractionProjection B S hS (D.relativeMap (D.sqπ ι toS hk V)) (D.sqRep ι toS hk V)
        (D.relativeMap (D.sqβ ι toS hk V))
        (D.sqI_sqR ι toS hk V) G G₀ ψ := rfl

/-- The multiplications of `sqExtension` are
`AlgebraicGeometry.Space.retractionMultiplicationFactor`. -/
theorem sqExtension_μ (V : FGModuleCat.{u} k)
    (G : Modules.{u, u} B S hS (D.space (D.sqT ι toS hk V)).1 (D.space (D.sqT ι toS hk V)).2)
    (G₀ : Modules.{u, u} B S hS (D.space (D.sq₀ ι toS hk)).1 (D.space (D.sq₀ ι toS hk)).2)
    (ψ : (modulePullback B S hS (D.relativeMap (D.sqβ ι toS hk V))).obj G ≅ G₀)
    (hG : G.IsQuasicoherentOnSite)
    (hflat : IsFlatOver B S hS (D.space (D.sqT ι toS hk V)).2
      (D.projection (D.sqT ι toS hk V)).hom G)
    (v : ↥V) :
    letI := D.sqLinear ι toS hk
    (D.sqExtension ι toS hk V G G₀ ψ hG hflat).μ v =
      retractionMultiplicationFactor B S hS G G₀ ψ hG (D.sq_isSplitThickeningBy ι toS hk V) v :=
  rfl

/-! ### Transfer of the square-zero functions -/

omit hY in
/-- `AlgebraicGeometry.Space.CoherentSituation.chartDiagramRestrict_transferChartDiagram_siteΓ`
for a retraction of the source given as a morphism equal to the composite. -/
theorem chartDiagramRestrict_transferChartDiagram_siteΓ' {T₀ T₁ T₂ : SchemesOver D.Y}
    (π₁ : T₁ ⟶ T₀) (g : T₂ ⟶ T₁) (π₂ : T₂ ⟶ T₀) (hg : g ≫ π₁ = π₂)
    (hr : D.relativeMap g ≫ D.relativeMap π₁ = D.relativeMap π₂)
    (U : SmallEtale B S hS (D.space T₀).1) (t : D.morphismCoherentSituation.testRing T₁) :
    chartDiagramRestrict B S hS (D.relativeMap g)
        (transferChartDiagram B S hS (D.relativeMap π₁) (D.morphismCoherentSituation.splitRep π₁)
          (D.relativeMap π₂) (D.morphismCoherentSituation.splitRep π₂) (D.relativeMap g) hr U)
        ((CoherentSituation.siteΓ (D.morphismCoherentSituation.splitChartToTest π₁ U)).hom t) =
      (CoherentSituation.siteΓ (D.morphismCoherentSituation.splitChartToTest π₂ U)).hom
        ((CoherentSituation.siteΓ g.left).hom t) := by
  subst hg
  exact D.morphismCoherentSituation.chartDiagramRestrict_transferChartDiagram_siteΓ π₁ g U t

include hY in
/-- The transfer along `X_{k[W]} ⟶ X_{k[V]}` carries the square-zero function of `v` to that of
`f v`. -/
theorem sq_transfer_functions {V W : FGModuleCat.{u} k} (f : V ⟶ W)
    (U : SmallEtale B S hS (D.space (D.sq₀ ι toS hk)).1) (v : ↥V) :
    chartDiagramRestrict B S hS (D.relativeMap (D.sqσ ι toS hk f))
        (transferChartDiagram B S hS (D.relativeMap (D.sqπ ι toS hk V)) (D.sqRep ι toS hk V)
          (D.relativeMap (D.sqπ ι toS hk W))
          (D.sqRep ι toS hk W) (D.relativeMap (D.sqσ ι toS hk f)) (D.sqH_sqR ι toS hk f) U)
        ((D.sqSplitFunctions ι toS hk V v).1
          (op ((smallBaseChange B S hS (D.relativeMap (D.sqπ ι toS hk V))
            (D.sqRep ι toS hk V)).obj U))) =
      (D.sqSplitFunctions ι toS hk W (f.hom.hom v)).1
        (op ((smallBaseChange B S hS (D.relativeMap (D.sqπ ι toS hk W))
          (D.sqRep ι toS hk W)).obj U)) := by
  have h := D.chartDiagramRestrict_transferChartDiagram_siteΓ' _ _ _
    (D.sqσ_sqπ ι toS hk f) (D.sqH_sqR ι toS hk f) U
    (D.sqFunctions ι toS hk V v)
  rwa [D.siteΓ_sqMap_sqFunctions ι toS hk f v] at h

end QuotSituation

end AlgebraicGeometry.Space

end
