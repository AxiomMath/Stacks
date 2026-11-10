module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Sheafification of presheaves of modules is local for a cover-dense subcategory

Let `G : 𝒞 ⥤ 𝒟` be a functor which is cover-dense and locally full for a topology `K` on `𝒟` —
for instance the inclusion of the objects of a covering sieve into a slice site, which is
`CategoryTheory.Sieve.isCoverDense_ι_overObjects`. Let `R` be a sheaf of rings on `𝒟`. This file
proves that the sheafification of a presheaf of `R`-modules depends only on its restriction
along `G`:

**two presheaves of modules whose restrictions along `G` are isomorphic have isomorphic
sheafifications**, and the same for complexes of them.

The mechanism is a single Hom-bijection. If the underlying presheaf of abelian groups of a
presheaf of modules `N` is a sheaf, then restriction along `G` is bijective from maps `M ⟶ N` of
presheaves of modules onto maps of their restrictions: injectivity because the underlying
abelian-group statement is Mathlib's
`CategoryTheory.Functor.whiskerLeft_obj_map_bijective_of_isCoverDense`, and surjectivity because
the abelian-group map produced by that same bijection is automatically `R`-linear — linearity is
an equation between sections of a sheaf which holds after restriction along every arrow out of
the image of `G`, and those arrows cover.

Composing that bijection with the sheafification adjunction turns a map of the restrictions into
a map of the sheafifications, `PresheafOfModules.sheafifyLiftRes`, compatibly with composition
and identities. Hence an *isomorphism* of the restrictions gives an isomorphism of the
sheafifications, and a *morphism of complexes* of the restrictions which is degreewise
invertible gives an isomorphism of the degreewise sheafifications.

This is the step of [Stacks, Tag 099E] which the source states as "`K_{U,I}` and `K_{U,I'}` are
the same for any object lying over one of the `U_j`. The statement on sheafifications follows."

## Main definitions

* `PresheafOfModules.pushforwardHomEquiv`: **restriction along `G` is bijective on maps into a
  presheaf of modules whose underlying presheaf is a sheaf.**
* `PresheafOfModules.sheafifyLiftRes`: the map of sheafifications attached to a map of the
  restrictions.
* `PresheafOfModules.sheafifyIsoOfRes`: **the isomorphism of sheafifications attached to an
  isomorphism of the restrictions.**
* `PresheafOfModules.sheafifyComplexIsoOfRes`: the same for complexes, degreewise.

## Main results

* `PresheafOfModules.sheafifyLiftRes_comp`, `PresheafOfModules.sheafifyLiftRes_id`,
  `PresheafOfModules.sheafifyLiftRes_pushforward₀_map`: `sheafifyLiftRes` is compatible with
  composition, identities and the restrictions of actual maps of presheaves.
* `PresheafOfModules.sheafifyLiftRes_comp_sheafification_map`: **the induced map of
  sheafifications is compatible with augmentations** — with any pair of maps into a common
  presheaf of modules whose restrictions the given map of restrictions respects.

## Implementation notes

The scalars are not changed: everything is stated for `PresheafOfModules.sheafification
(𝟙 R.obj)`, the sheafification functor of presheaves of `R.obj`-modules, which is the one every
consumer in this library uses.

Restriction of presheaves of modules along `G` is Mathlib's `PresheafOfModules.pushforward₀ G`,
whose composite with the forgetful functor to presheaves of abelian groups is *definitionally*
precomposition with `G.op` — `PresheafOfModules.pushforward₀CompToPresheaf` is `Iso.refl` — so
the bridge lemmas below are `rfl`.

## References

* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace PresheafOfModules

universe w v₁ u₁ v₂ u₂

section CoverDense

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {K : GrothendieckTopology D} {G : C ⥤ D} [G.IsCoverDense K] [G.IsLocallyFull K]
  {R₀ : Dᵒᵖ ⥤ RingCat.{w}}

/-- Restriction of a presheaf of modules along `G` is, on underlying presheaves of abelian
groups, precomposition with `G.op`. -/
theorem presheaf_pushforward₀Obj (M : PresheafOfModules.{w} R₀) :
    ((pushforward₀ G R₀).obj M).presheaf = G.op ⋙ M.presheaf := rfl

/-- Restriction along `G` of a map of presheaves of modules is, on underlying presheaves of
abelian groups, the whiskering of the underlying map. -/
theorem toPresheaf_map_pushforward₀_map {M N : PresheafOfModules.{w} R₀} (φ : M ⟶ N) :
    (toPresheaf (G.op ⋙ R₀)).map ((pushforward₀ G R₀).map φ) =
      ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{w}).obj G.op).map
        ((toPresheaf R₀).map φ) := rfl

/-- Semilinearity of the restriction maps of a presheaf of modules, read on the underlying
presheaf of abelian groups. -/
theorem map_smul_presheaf (M : PresheafOfModules.{w} R₀) {X Y : Dᵒᵖ} (f : X ⟶ Y)
    (r : R₀.obj X) (m : M.presheaf.obj X) :
    M.presheaf.map f (r • m) = R₀.map f r • M.presheaf.map f m :=
  M.map_smul f r m

omit [G.IsLocallyFull K] in
/-- **Sections of a presheaf of modules whose underlying presheaf is a sheaf are determined by
their restrictions along the arrows out of the image of a cover-dense functor.** -/
theorem ext_of_isSheaf_presheaf {N : PresheafOfModules.{w} R₀}
    (hN : Presheaf.IsSheaf K N.presheaf) {X : Dᵒᵖ} (x y : N.presheaf.obj X)
    (h : ∀ (Z : C) (p : G.obj Z ⟶ X.unop),
      N.presheaf.map p.op x = N.presheaf.map p.op y) : x = y := by
  refine hN.isSeparated X.unop (Sieve.coverByImage G X.unop)
    (G.is_cover_of_isCoverDense K X.unop) x y ?_
  rintro Y p hp
  obtain ⟨Z, l, m, rfl⟩ := hp.some
  change N.presheaf.map (l ≫ m).op x = N.presheaf.map (l ≫ m).op y
  simp only [op_comp, CategoryTheory.Functor.map_comp, CategoryTheory.comp_apply, h Z m]

omit [G.IsLocallyFull K] in
/-- The abelian-group map produced by cover-density out of a map of restrictions is linear: the
two sides of the linearity equation are sections of a sheaf with the same restriction along every
arrow out of the image of `G`. -/
theorem app_smul_of_whiskerLeft_eq {M N : PresheafOfModules.{w} R₀}
    (hN : Presheaf.IsSheaf K N.presheaf) {δ : M.presheaf ⟶ N.presheaf}
    {u : (pushforward₀ G R₀).obj M ⟶ (pushforward₀ G R₀).obj N}
    (hδ : ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{w}).obj G.op).map δ =
      (toPresheaf (G.op ⋙ R₀)).map u)
    (X : Dᵒᵖ) (r : R₀.obj X) (m : M.presheaf.obj X) :
    δ.app X (r • m) = r • δ.app X m := by
  refine ext_of_isSheaf_presheaf (G := G) hN _ _ fun Z p ↦ ?_
  have hres : ∀ z : M.presheaf.obj (op (G.obj Z)),
      δ.app (op (G.obj Z)) z = u.app (op Z) z := fun z ↦
    ConcreteCategory.congr_hom (NatTrans.congr_app hδ (op Z)) z
  calc N.presheaf.map p.op (δ.app X (r • m))
      = δ.app (op (G.obj Z)) (M.presheaf.map p.op (r • m)) :=
        (NatTrans.naturality_apply δ p.op (r • m)).symm
    _ = δ.app (op (G.obj Z)) (R₀.map p.op r • M.presheaf.map p.op m) := by
        rw [map_smul_presheaf]
    _ = R₀.map p.op r • δ.app (op (G.obj Z)) (M.presheaf.map p.op m) := by
        rw [hres, hres]
        exact (u.app (op Z)).hom.map_smul _ _
    _ = R₀.map p.op r • N.presheaf.map p.op (δ.app X m) := by
        rw [NatTrans.naturality_apply]
    _ = N.presheaf.map p.op (r • δ.app X m) := (map_smul_presheaf N p.op r _).symm

/-- **Restriction along a cover-dense, locally full functor is bijective on maps of presheaves of
modules into one whose underlying presheaf is a sheaf.** -/
theorem bijective_pushforward₀_map {M N : PresheafOfModules.{w} R₀}
    (hN : Presheaf.IsSheaf K N.presheaf) :
    Function.Bijective (fun φ : M ⟶ N ↦ (pushforward₀ G R₀).map φ) := by
  have hbij := Functor.whiskerLeft_obj_map_bijective_of_isCoverDense
    (K := K) G (A := AddCommGrpCat.{w}) M.presheaf N.presheaf hN
  refine ⟨fun φ ψ h ↦ (toPresheaf R₀).map_injective (hbij.1 ?_), fun u ↦ ?_⟩
  · exact (toPresheaf_map_pushforward₀_map (G := G) φ).symm.trans
      ((congrArg (toPresheaf (G.op ⋙ R₀)).map h).trans
        (toPresheaf_map_pushforward₀_map (G := G) ψ))
  · obtain ⟨δ, hδ⟩ := hbij.2 ((toPresheaf (G.op ⋙ R₀)).map u)
    refine ⟨homMk δ (app_smul_of_whiskerLeft_eq hN hδ), ?_⟩
    refine (toPresheaf (G.op ⋙ R₀)).map_injective ?_
    rw [toPresheaf_map_pushforward₀_map]
    exact hδ

/-- **Restriction along a cover-dense, locally full functor is a bijection on maps of presheaves
of modules into one whose underlying presheaf is a sheaf.** -/
def pushforwardHomEquiv {M N : PresheafOfModules.{w} R₀} (hN : Presheaf.IsSheaf K N.presheaf) :
    (M ⟶ N) ≃ ((pushforward₀ G R₀).obj M ⟶ (pushforward₀ G R₀).obj N) :=
  Equiv.ofBijective _ (bijective_pushforward₀_map hN)

/-- `pushforwardHomEquiv` sends a map to its restriction along `G`. -/
@[simp]
theorem pushforwardHomEquiv_apply {M N : PresheafOfModules.{w} R₀}
    (hN : Presheaf.IsSheaf K N.presheaf) (φ : M ⟶ N) :
    pushforwardHomEquiv (G := G) hN φ = (pushforward₀ G R₀).map φ := rfl

end CoverDense

section Sheafify

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {K : GrothendieckTopology D} {G : C ⥤ D} [G.IsCoverDense K] [G.IsLocallyFull K]
  {R : Sheaf K RingCat.{w}} [HasWeakSheafify K AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [HasWeakSheafify K AddCommGrpCat] [K.WEqualsLocallyBijective AddCommGrpCat] in
/-- The underlying presheaf of the right adjoint of sheafification applied to a sheaf of modules
is a sheaf, since restriction of scalars does not change it. -/
theorem isSheaf_presheaf_forget (T : SheafOfModules.{w} R) :
    Presheaf.IsSheaf K
      ((SheafOfModules.forget R ⋙ restrictScalars (𝟙 R.obj)).obj T).presheaf :=
  T.isSheaf

/-- Two maps out of a sheafification into a sheaf of modules agree as soon as the corresponding
maps of presheaves agree after restriction along `G`. -/
theorem sheafification_hom_ext_of_pushforward₀ {M : PresheafOfModules.{w} R.obj}
    {T : SheafOfModules.{w} R}
    (a b : (sheafification (𝟙 R.obj)).obj M ⟶ T)
    (h : (pushforward₀ G R.obj).map ((sheafificationAdjunction (𝟙 R.obj)).homEquiv M T a) =
      (pushforward₀ G R.obj).map ((sheafificationAdjunction (𝟙 R.obj)).homEquiv M T b)) :
    a = b :=
  ((sheafificationAdjunction (𝟙 R.obj)).homEquiv M T).injective
    ((pushforwardHomEquiv (G := G) (isSheaf_presheaf_forget T)).injective h)

/-- **The map of sheafifications attached to a map of the restrictions along `G`.** -/
def sheafifyLiftRes {M N : PresheafOfModules.{w} R.obj}
    (u : (pushforward₀ G R.obj).obj M ⟶ (pushforward₀ G R.obj).obj N) :
    (sheafification (𝟙 R.obj)).obj M ⟶ (sheafification (𝟙 R.obj)).obj N :=
  ((sheafificationAdjunction (𝟙 R.obj)).homEquiv M _).symm
    ((pushforwardHomEquiv (G := G) (isSheaf_presheaf_forget _)).symm
      (u ≫ (pushforward₀ G R.obj).map
        ((sheafificationAdjunction (𝟙 R.obj)).unit.app N)))

/-- The characterising property of `PresheafOfModules.sheafifyLiftRes`. -/
theorem pushforward₀_map_homEquiv_sheafifyLiftRes {M N : PresheafOfModules.{w} R.obj}
    (u : (pushforward₀ G R.obj).obj M ⟶ (pushforward₀ G R.obj).obj N) :
    (pushforward₀ G R.obj).map ((sheafificationAdjunction (𝟙 R.obj)).homEquiv M _
        (sheafifyLiftRes (G := G) u)) =
      u ≫ (pushforward₀ G R.obj).map
        ((sheafificationAdjunction (𝟙 R.obj)).unit.app N) := by
  rw [sheafifyLiftRes, Equiv.apply_symm_apply]
  exact (pushforwardHomEquiv (G := G) (isSheaf_presheaf_forget _)).apply_symm_apply _

/-- `sheafifyLiftRes` of the restriction of an actual map of presheaves of modules is the
sheafification of that map. -/
theorem sheafifyLiftRes_pushforward₀_map {M N : PresheafOfModules.{w} R.obj} (φ : M ⟶ N) :
    sheafifyLiftRes (G := G) ((pushforward₀ G R.obj).map φ) =
      (sheafification (𝟙 R.obj)).map φ := by
  have hnat : (sheafificationAdjunction (𝟙 R.obj)).unit.app M ≫
      (SheafOfModules.forget R ⋙ restrictScalars (𝟙 R.obj)).map
        ((sheafification (𝟙 R.obj)).map φ) =
      φ ≫ (sheafificationAdjunction (𝟙 R.obj)).unit.app N :=
    ((sheafificationAdjunction (𝟙 R.obj)).unit.naturality φ).symm
  refine sheafification_hom_ext_of_pushforward₀ (G := G) _ _ ?_
  rw [pushforward₀_map_homEquiv_sheafifyLiftRes, Adjunction.homEquiv_unit, hnat,
    CategoryTheory.Functor.map_comp]

/-- `sheafifyLiftRes` preserves identities. -/
theorem sheafifyLiftRes_id (M : PresheafOfModules.{w} R.obj) :
    sheafifyLiftRes (G := G) (𝟙 ((pushforward₀ G R.obj).obj M)) = 𝟙 _ := by
  have h := sheafifyLiftRes_pushforward₀_map (G := G) (𝟙 M)
  rwa [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at h

/-- The unit of sheafification absorbs a `sheafifyLiftRes`, by its characterising property. -/
theorem pushforward₀_map_unit_comp {N P : PresheafOfModules.{w} R.obj}
    (v : (pushforward₀ G R.obj).obj N ⟶ (pushforward₀ G R.obj).obj P) :
    (pushforward₀ G R.obj).map ((sheafificationAdjunction (𝟙 R.obj)).unit.app N) ≫
        (pushforward₀ G R.obj).map
          ((SheafOfModules.forget R ⋙ restrictScalars (𝟙 R.obj)).map
            (sheafifyLiftRes (G := G) v)) =
      v ≫ (pushforward₀ G R.obj).map
        ((sheafificationAdjunction (𝟙 R.obj)).unit.app P) := by
  have h := pushforward₀_map_homEquiv_sheafifyLiftRes (G := G) v
  rwa [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp] at h

/-- `sheafifyLiftRes` preserves composition. -/
theorem sheafifyLiftRes_comp {M N P : PresheafOfModules.{w} R.obj}
    (u : (pushforward₀ G R.obj).obj M ⟶ (pushforward₀ G R.obj).obj N)
    (v : (pushforward₀ G R.obj).obj N ⟶ (pushforward₀ G R.obj).obj P) :
    sheafifyLiftRes (G := G) (u ≫ v) =
      sheafifyLiftRes (G := G) u ≫ sheafifyLiftRes (G := G) v := by
  refine sheafification_hom_ext_of_pushforward₀ (G := G) _ _ ?_
  rw [pushforward₀_map_homEquiv_sheafifyLiftRes, Adjunction.homEquiv_naturality_right,
    CategoryTheory.Functor.map_comp, pushforward₀_map_homEquiv_sheafifyLiftRes]
  simp only [Category.assoc, pushforward₀_map_unit_comp]

/-- The map of sheafifications induced by an isomorphism of restrictions is an isomorphism. -/
instance isIso_sheafifyLiftRes {M N : PresheafOfModules.{w} R.obj}
    (u : (pushforward₀ G R.obj).obj M ⟶ (pushforward₀ G R.obj).obj N) [IsIso u] :
    IsIso (sheafifyLiftRes (G := G) u) := by
  refine ⟨sheafifyLiftRes (G := G) (inv u), ?_, ?_⟩
  · rw [← sheafifyLiftRes_comp, IsIso.hom_inv_id, sheafifyLiftRes_id]
  · rw [← sheafifyLiftRes_comp, IsIso.inv_hom_id, sheafifyLiftRes_id]

/-- **The map of sheafifications is compatible with augmentations.** If a map of the restrictions
is compatible with the restrictions of two maps into a common presheaf of modules, then the
induced map of sheafifications is compatible with their sheafifications. This is the form of
compatibility [Stacks, Tag 099E] asks for, "compatible with maps to `𝒪_U`". -/
theorem sheafifyLiftRes_comp_sheafification_map {M N P : PresheafOfModules.{w} R.obj}
    (u : (pushforward₀ G R.obj).obj M ⟶ (pushforward₀ G R.obj).obj N)
    (a : M ⟶ P) (b : N ⟶ P)
    (h : u ≫ (pushforward₀ G R.obj).map b = (pushforward₀ G R.obj).map a) :
    sheafifyLiftRes (G := G) u ≫ (sheafification (𝟙 R.obj)).map b =
      (sheafification (𝟙 R.obj)).map a := by
  rw [← sheafifyLiftRes_pushforward₀_map (G := G) b, ← sheafifyLiftRes_comp, h,
    sheafifyLiftRes_pushforward₀_map]

/-- **Two presheaves of modules whose restrictions along a cover-dense, locally full functor are
isomorphic have isomorphic sheafifications.** -/
def sheafifyIsoOfRes {M N : PresheafOfModules.{w} R.obj}
    (e : (pushforward₀ G R.obj).obj M ≅ (pushforward₀ G R.obj).obj N) :
    (sheafification (𝟙 R.obj)).obj M ≅ (sheafification (𝟙 R.obj)).obj N where
  hom := sheafifyLiftRes (G := G) e.hom
  inv := sheafifyLiftRes (G := G) e.inv
  hom_inv_id := by rw [← sheafifyLiftRes_comp, e.hom_inv_id, sheafifyLiftRes_id]
  inv_hom_id := by rw [← sheafifyLiftRes_comp, e.inv_hom_id, sheafifyLiftRes_id]

/-- The forward map of `sheafifyIsoOfRes e` is `sheafifyLiftRes e.hom`. -/
@[simp]
theorem sheafifyIsoOfRes_hom {M N : PresheafOfModules.{w} R.obj}
    (e : (pushforward₀ G R.obj).obj M ≅ (pushforward₀ G R.obj).obj N) :
    (sheafifyIsoOfRes (G := G) e).hom = sheafifyLiftRes (G := G) e.hom := rfl

/-- The inverse map of `sheafifyIsoOfRes e` is `sheafifyLiftRes e.inv`. -/
@[simp]
theorem sheafifyIsoOfRes_inv {M N : PresheafOfModules.{w} R.obj}
    (e : (pushforward₀ G R.obj).obj M ≅ (pushforward₀ G R.obj).obj N) :
    (sheafifyIsoOfRes (G := G) e).inv = sheafifyLiftRes (G := G) e.inv := rfl

end Sheafify

section Complexes

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {K : GrothendieckTopology D} {G : C ⥤ D} [G.IsCoverDense K] [G.IsLocallyFull K]
  {R : Sheaf K RingCat.{w}} [HasWeakSheafify K AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}]

variable {ι : Type*} {c : ComplexShape ι}

/-- **A degreewise family of maps of the restrictions along `G`, commuting with the
differentials, induces a map of the degreewise sheafifications.** -/
def sheafifyComplexLiftRes
    {F F' : HomologicalComplex (PresheafOfModules.{w} R.obj) c}
    (u : ∀ n, (pushforward₀ G R.obj).obj (F.X n) ⟶ (pushforward₀ G R.obj).obj (F'.X n))
    (hu : ∀ n m, c.Rel n m →
      u n ≫ (pushforward₀ G R.obj).map (F'.d n m) =
        (pushforward₀ G R.obj).map (F.d n m) ≫ u m) :
    ((sheafification (𝟙 R.obj)).mapHomologicalComplex c).obj F ⟶
      ((sheafification (𝟙 R.obj)).mapHomologicalComplex c).obj F' where
  f n := sheafifyLiftRes (G := G) (u n)
  comm' n m h := by
    change sheafifyLiftRes (G := G) (u n) ≫ (sheafification (𝟙 R.obj)).map (F'.d n m) =
      (sheafification (𝟙 R.obj)).map (F.d n m) ≫ sheafifyLiftRes (G := G) (u m)
    rw [← sheafifyLiftRes_pushforward₀_map (G := G) (F'.d n m),
      ← sheafifyLiftRes_pushforward₀_map (G := G) (F.d n m), ← sheafifyLiftRes_comp,
      ← sheafifyLiftRes_comp, hu n m h]

/-- In degree `n`, `sheafifyComplexLiftRes u hu` is `sheafifyLiftRes (u n)`. -/
@[simp]
theorem sheafifyComplexLiftRes_f
    {F F' : HomologicalComplex (PresheafOfModules.{w} R.obj) c}
    (u : ∀ n, (pushforward₀ G R.obj).obj (F.X n) ⟶ (pushforward₀ G R.obj).obj (F'.X n))
    (hu : ∀ n m, c.Rel n m →
      u n ≫ (pushforward₀ G R.obj).map (F'.d n m) =
        (pushforward₀ G R.obj).map (F.d n m) ≫ u m) (n : ι) :
    (sheafifyComplexLiftRes (G := G) u hu).f n = sheafifyLiftRes (G := G) (u n) := rfl

/-- The map of degreewise sheafifications induced by a degreewise family of isomorphisms is an
isomorphism. -/
instance isIso_sheafifyComplexLiftRes
    {F F' : HomologicalComplex (PresheafOfModules.{w} R.obj) c}
    (u : ∀ n, (pushforward₀ G R.obj).obj (F.X n) ⟶ (pushforward₀ G R.obj).obj (F'.X n))
    (hu : ∀ n m, c.Rel n m →
      u n ≫ (pushforward₀ G R.obj).map (F'.d n m) =
        (pushforward₀ G R.obj).map (F.d n m) ≫ u m) [∀ n, IsIso (u n)] :
    IsIso (sheafifyComplexLiftRes (G := G) u hu) :=
  have : ∀ n, IsIso ((sheafifyComplexLiftRes (G := G) u hu).f n) := fun n ↦
    isIso_sheafifyLiftRes (G := G) (u n)
  HomologicalComplex.Hom.isIso_of_components _

/-- **Two complexes of presheaves of modules whose restrictions along a cover-dense, locally full
functor are isomorphic have isomorphic degreewise sheafifications.** -/
def sheafifyComplexIsoOfRes
    {F F' : HomologicalComplex (PresheafOfModules.{w} R.obj) c}
    (u : ∀ n, (pushforward₀ G R.obj).obj (F.X n) ⟶ (pushforward₀ G R.obj).obj (F'.X n))
    (hu : ∀ n m, c.Rel n m →
      u n ≫ (pushforward₀ G R.obj).map (F'.d n m) =
        (pushforward₀ G R.obj).map (F.d n m) ≫ u m) [∀ n, IsIso (u n)] :
    ((sheafification (𝟙 R.obj)).mapHomologicalComplex c).obj F ≅
      ((sheafification (𝟙 R.obj)).mapHomologicalComplex c).obj F' :=
  asIso (sheafifyComplexLiftRes (G := G) u hu)

end Complexes

end PresheafOfModules

end
