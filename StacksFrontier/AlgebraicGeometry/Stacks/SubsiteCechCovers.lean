module

public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategorySiteKind
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteLocalFactorizations
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePrimedConnectedFactorizations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CoverDescent.Cohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CoverDescent.ComponentPresheaf

/-! # Representable covers of the iterated 2-fibre products of a presentation

Let `𝒳` be an algebraic stack over `S` with its étale or fppf site, and let `𝒳' ⊆ 𝒳` be a full
subcategory satisfying the two hypotheses of Stacks 07AK: it is closed under the morphisms lying
over smooth (respectively flat and locally finitely presented) morphisms of schemes, and it
contains an object `x` over a scheme `U` whose 1-morphism `(Sch/U) ⟶ 𝒳` is smooth and
surjective.

The proof of Stacks 07AK runs along the covering `h_x ⟶ *` of the final sheaf and the fibre
powers `h_x ×_* ⋯ ×_* h_x`, which are the presheaves represented by the 2-fibre products
`U ×_𝒳 ⋯ ×_𝒳 U`. These are algebraic stacks smooth over `U`, so they are in turn covered by an
object of `𝒳'` — the image of the distinguished object of a smooth atlas, which lies over a smooth
morphism to `U` and therefore belongs to `𝒳'` — whose fibre powers are again the presheaves of
2-fibre products of algebraic stacks smooth over `U`. This file proves that the class of these
presheaves is closed under representable covers in the sense of
`Stacks.Sites.CoverDescent.IsClosedUnderRepresentableCovers`, which is the geometric input of
the comparison of cohomology along `𝒳' ⊆ 𝒳`.

The presheaf represented by a 1-morphism of categories fibred in groupoids `z : 𝒵 ⟶ 𝒳` is the
presheaf of components `Stacks.Sites.CoverDescent.componentPresheaf`; its fibre powers along a
second 1-morphism are computed by
`Stacks.Sites.CoverDescent.bijective_componentPresheafTwoFibreProductHom`.

## Main definitions

* `AlgebraicGeometry.Stack.cechTower`: the iterated 2-fibre products `𝒜 ×_𝒵 ⋯ ×_𝒵 𝒜` of a
  1-morphism `e : 𝒜 ⟶ 𝒵` of algebraic stacks, with their projections to `𝒵`.
* `AlgebraicGeometry.Stack.SmoothOverAtlas`: the presheaves on `𝒳` represented by an algebraic
  stack with faithful structure functor and a smooth 1-morphism to `U`.

## Main results

* `AlgebraicGeometry.Stack.exists_tuplePresheaf_iso_cechTower`: the fibre powers of the map of
  presheaves represented by `e` are the presheaves represented by the iterated 2-fibre products.
* `AlgebraicGeometry.Stack.isClosedUnderRepresentableCovers_smoothOverAtlas`: the class of the
  final presheaf and of the presheaves represented by algebraic stacks smooth over `U` is closed
  under representable covers by objects of `𝒳'`.

## References

* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 075W](https://stacks.math.columbia.edu/tag/075W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Sites.CoverDescent

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The iterated 2-fibre products of a 1-morphism -/

/-- **The iterated 2-fibre products of a 1-morphism of algebraic stacks.** For `e : 𝒜 ⟶ 𝒵`, the
term in degree `0` is `𝒜` over `𝒵` along `e`, and the term in degree `r + 1` is the 2-fibre product
`𝒜 ×_{e, 𝒵} T_r` of `e` with the term in degree `r`, mapping to `𝒵` through its first projection
and `e`. -/
def cechTower {𝒜 𝒵 : AlgebraicStacks.{u, w} B S hS} (e : 𝒜 ⟶ 𝒵) :
    ℕ → Σ 𝒯 : AlgebraicStacks.{u, w} B S hS, 𝒯 ⟶ 𝒵
  | 0 => ⟨𝒜, e⟩
  | r + 1 => ⟨(twoFibreProductSquareAlgebraicStacks B S hS e (cechTower e r).2).pt,
      (twoFibreProductSquareAlgebraicStacks B S hS e (cechTower e r).2).fst ≫ e⟩

variable {B S hS}

/-- The first projection of the 2-fibre product of `e` with a smooth `g` is smooth. -/
private theorem isSmooth_twoFibreProductSquare_fst {𝒜 𝒵 𝒯 : AlgebraicStacks.{u, w} B S hS}
    (e : 𝒜 ⟶ 𝒵) (g : 𝒯 ⟶ 𝒵) (hg : AlgebraicStacks.IsSmooth B S hS g) :
    AlgebraicStacks.IsSmooth B S hS (twoFibreProductSquareAlgebraicStacks B S hS e g).fst :=
  AlgebraicStacks.isSmooth_baseChange B S hS g e (twoFibreProductSquareAlgebraicStacks B S hS e g)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS e g) hg

/-- The projections of the iterated 2-fibre products of a smooth 1-morphism are smooth. -/
theorem isSmooth_cechTower {𝒜 𝒵 : AlgebraicStacks.{u, w} B S hS} (e : 𝒜 ⟶ 𝒵)
    (he : AlgebraicStacks.IsSmooth B S hS e) :
    ∀ r, AlgebraicStacks.IsSmooth B S hS (cechTower B S hS e r).2
  | 0 => he
  | r + 1 => AlgebraicStacks.isSmooth_comp B S hS _ e
      (isSmooth_twoFibreProductSquare_fst e _ (isSmooth_cechTower e he r)) he

/-- The first projection of the iterated 2-fibre product in degree `r + 1` is smooth when the
1-morphism is. -/
theorem isSmooth_cechTower_fst {𝒜 𝒵 : AlgebraicStacks.{u, w} B S hS} (e : 𝒜 ⟶ 𝒵)
    (he : AlgebraicStacks.IsSmooth B S hS e) (r : ℕ) :
    AlgebraicStacks.IsSmooth B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS e (cechTower B S hS e r).2).fst :=
  isSmooth_twoFibreProductSquare_fst e _ (isSmooth_cechTower e he r)

/-- Two morphisms lying over equal morphisms for a faithful functor are equal. -/
private theorem eq_of_isHomLift_of_eq {𝒳 𝒮 : Type*} [Category 𝒳] [Category 𝒮] {p : 𝒳 ⥤ 𝒮}
    [p.Faithful] {a b : 𝒳} {R T : 𝒮} {φ ψ : R ⟶ T} {f g : a ⟶ b} (hf : p.IsHomLift φ f)
    (hg : p.IsHomLift ψ g) (h : φ = ψ) : f = g := by
  apply p.map_injective
  rw [IsHomLift.fac' p φ f, IsHomLift.fac' p ψ g]
  subst h
  rfl

/-- The iterated 2-fibre products of a 1-morphism out of an algebraic stack with faithful
structure functor have faithful structure functors: a morphism of a 2-fibre product is
determined by its two components, which are determined by the common base morphism. -/
theorem faithful_cechTower {𝒜 𝒵 : AlgebraicStacks.{u, w} B S hS} (e : 𝒜 ⟶ 𝒵)
    [h𝒜 : 𝒜.val.val.p.Faithful] : ∀ r, (cechTower B S hS e r).1.val.val.p.Faithful
  | 0 => h𝒜
  | r + 1 => by
    have ih := faithful_cechTower e r
    refine ⟨fun {ξ ξ'} f g h => TwoFibreProductOver.Hom.ext' ?_ ?_⟩
    · exact eq_of_isHomLift_of_eq f.ha g.ha h
    · exact eq_of_isHomLift_of_eq f.hb g.hb h

/-! ### The fibre powers of the presheaf represented by a 1-morphism -/

section Tuple

variable {𝒳 𝒵 𝒜 : AlgebraicStacks.{u, w} B S hS} (z : 𝒵.val.val.obj ⥤ 𝒳.val.val.obj)
  (hz : z ⋙ 𝒳.val.val.p = 𝒵.val.val.p) [z.Faithful] (e : 𝒜 ⟶ 𝒵)

include hz in
/-- **The fibre powers of the presheaf represented by a 1-morphism are represented by its
iterated 2-fibre products.** Let `z : 𝒵 ⟶ 𝒳` be faithful over the base, and let `e : 𝒜 ⟶ 𝒵` be
a 1-morphism of algebraic stacks. The presheaf of `(r + 1)`-tuples of sections of `Ψ(z ∘ e)` with a
common image in `Ψ(z)` is `Ψ(z ∘ e_r)` for the projection `e_r` of the iterated 2-fibre product
`𝒜 ×_𝒵 ⋯ ×_𝒵 𝒜`, compatibly with the maps to `Ψ(z)`.

By induction on `r`: prepending an entry identifies the tuples of length `r + 2` with a fibre
product, over `Ψ(z)`, of `Ψ(z ∘ e)` and the tuples of length `r + 1`, and the presheaf of
components of the 2-fibre product `𝒜 ×_𝒵 T_r` is that fibre product. -/
theorem exists_tuplePresheaf_iso_cechTower (r : ℕ) :
    ∃ E : tuplePresheaf (componentPresheafMap z (CatFiberedInGroupoids.homFunctor e.hom)) r ≅
        componentPresheaf (CatFiberedInGroupoids.homFunctor (cechTower B S hS e r).2.hom ⋙ z),
      E.hom ≫
          componentPresheafMap z (CatFiberedInGroupoids.homFunctor (cechTower B S hS e r).2.hom) =
        tupleπ _ r 0 ≫ componentPresheafMap z (CatFiberedInGroupoids.homFunctor e.hom) := by
  induction r with
  | zero => exact ⟨tuplePresheafZeroIso _, rfl⟩
  | succ r ih =>
    obtain ⟨E, hE⟩ := ih
    have hp := 𝒳.val.isFiberedInGroupoids
    have hZ : (z ⋙ 𝒳.val.val.p).IsFiberedInGroupoids := hz ▸ 𝒵.val.isFiberedInGroupoids
    have hpA : CatFiberedInGroupoids.homFunctor e.hom ⋙ z ⋙ 𝒳.val.val.p = 𝒜.val.val.p :=
      hz ▸ e.hom.hom.w
    have hpB : CatFiberedInGroupoids.homFunctor (cechTower B S hS e r).2.hom ⋙ z ⋙
        𝒳.val.val.p = (cechTower B S hS e r).1.val.val.p :=
      hz ▸ (cechTower B S hS e r).2.hom.hom.w
    have hA : (CatFiberedInGroupoids.homFunctor e.hom ⋙ z ⋙ 𝒳.val.val.p).IsFiberedInGroupoids :=
      hpA ▸ 𝒜.val.isFiberedInGroupoids
    have hB : (CatFiberedInGroupoids.homFunctor (cechTower B S hS e r).2.hom ⋙ z ⋙
        𝒳.val.val.p).IsFiberedInGroupoids :=
      hpB ▸ (cechTower B S hS e r).1.val.isFiberedInGroupoids
    let FP := componentPresheafTwoFibreProductHom z 𝒜.val.val.p
      (cechTower B S hS e r).1.val.val.p 𝒵.val.val.p (CatFiberedInGroupoids.homFunctor e.hom)
      (CatFiberedInGroupoids.homFunctor (cechTower B S hS e r).2.hom)
    have : IsIso FP :=
      @NatIso.isIso_of_isIso_app _ _ _ _ _ _ FP fun y =>
        (isIso_iff_bijective _).2 (bijective_componentPresheafTwoFibreProductHom 𝒳.val.val.p z
          _ _ _ _ _ hp hZ hA hB hpA hpB hz y)
    refine ⟨tuplePresheafSuccIso _ r ≪≫ fibreProductPresheafIsoOfIso _ _ _ E hE ≪≫
      (asIso FP).symm, ?_⟩
    refine natTrans_ext fun y a => ?_
    let fst := TwoFibreProductOver.fst 𝒜.val.val.p (cechTower B S hS e r).1.val.val.p
      𝒵.val.val.p (CatFiberedInGroupoids.homFunctor e.hom)
      (CatFiberedInGroupoids.homFunctor (cechTower B S hS e r).2.hom)
    let x := (tuplePresheafSuccIso _ r ≪≫ fibreProductPresheafIsoOfIso _ _ _ E hE).hom.app y a
    have hx : (FP.app y ((inv FP).app y x)) = x := by
      rw [← NatTrans.comp_app_apply, IsIso.inv_hom_id]
      rfl
    have hfst : (componentPresheafMap (CatFiberedInGroupoids.homFunctor e.hom ⋙ z) fst).app y
        ((inv FP).app y x) = a.1 0 :=
      congrArg (fun q => q.1.1) hx
    have hcomp := congrArg (fun φ => φ.app y ((inv FP).app y x))
      (componentPresheafMap_comp z fst (CatFiberedInGroupoids.homFunctor e.hom))
    simp only [NatTrans.comp_app_apply] at hcomp
    change (componentPresheafMap z (fst ⋙ CatFiberedInGroupoids.homFunctor e.hom)).app y
      ((inv FP).app y x) = _
    rw [hcomp, hfst]
    rfl

end Tuple

/-! ### Local surjectivity along a smooth surjective atlas -/

section Cover

variable {𝒳 𝒯 : AlgebraicStacks.{u, w} B S hS} (τ : SiteKind)
  (hgen : ∀ {U : BigFppfOver B S hS} {W : B.Schemes} (m : W ⟶ U.left),
    Smooth (B.inclusion.map m) → Surjective (B.inclusion.map m) →
      Sieve.generate (Presieve.singleton
          (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U))
        ∈ BigFppfOver.baseOverTopology B S hS τ U)
  (z : 𝒯.val.val.obj ⥤ 𝒳.val.val.obj) (hz : z ⋙ 𝒳.val.val.p = 𝒯.val.val.p)

include hgen hz in
/-- **The presheaf represented by a smooth surjective atlas covers the presheaf represented by
its target.** For `z : 𝒯 ⟶ 𝒳` over the base and a smooth surjective 1-morphism
`e : (Sch/D) ⟶ 𝒯`, the map `Ψ(z ∘ e) ⟶ Ψ(z)` of presheaves on the site of `𝒳` is locally
surjective: an arrow `y ⟶ z(ζ)` lifts along `e` after a covering of the scheme `ζ` lies over, by
**Stacks 06XH**, and the corresponding covering sieve of `y` is the one the site of `𝒳` inherits
from the base. -/
theorem isLocallySurjective_componentPresheafMap_atlas {D : BigFppfOver B S hS}
    (e : schemeStack.{u, w} B S hS D ⟶ 𝒯) (hesm : AlgebraicStacks.IsSmooth B S hS e)
    (hesurj : IsSurjective B S hS e) :
    Presheaf.IsLocallySurjective (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
      (componentPresheafMap z (CatFiberedInGroupoids.homFunctor e.hom)) := by
  have hp := 𝒳.val.isFiberedInGroupoids
  have : 𝒳.val.val.p.IsFibered := hp.isFibered
  refine isLocallySurjective_componentPresheafMap z 𝒳.val.val.p _ _ hp fun y ζ φ => ?_
  obtain ⟨R, hR, hlift⟩ := exists_covering_fibre_lift B S hS τ hgen e hesurj hesm
    (𝒯.val.val.p.obj ζ) ζ rfl
  have hζ : 𝒳.val.val.p.obj (z.obj ζ) = 𝒯.val.val.p.obj ζ := Functor.congr_obj hz ζ
  refine ⟨Sieve.functorPullback 𝒳.val.val.p
      (Sieve.pullback (𝒳.val.val.p.map φ ≫ eqToHom hζ) R),
    Functor.functorPullback_mem_inheritedTopology 𝒳.val.val.p _ y
      ((BigFppfOver.baseOverTopology B S hS τ).pullback_stable _ hR), ?_⟩
  intro y' g hg
  obtain ⟨x', α, hα⟩ := hlift hg
  refine ⟨x', α, ?_⟩
  have h₁ : 𝒳.val.val.p.IsHomLift ((𝒳.val.val.p.map g ≫ 𝒳.val.val.p.map φ) ≫ eqToHom hζ)
      (z.map α) := PresheafOfCategories.isHomLift_map_of_comp hz _ α hα
  rw [Functor.map_comp]
  exact (IsHomLift.lift_comp_eqToHom_iff 𝒳.val.val.p _ (z.map α) hζ).1
    (by simpa using h₁)

end Cover

/-! ### The class of presheaves represented by algebraic stacks smooth over the atlas -/

section Class

variable (𝒳 : AlgebraicStacks.{u, w} B S hS) {U₀ : BigFppfOver B S hS}
  (a : schemeStack.{u, w} B S hS U₀ ⟶ 𝒳)

/-- **The presheaves represented by algebraic stacks smooth over a presentation.** The class of
presheaves of sets on `𝒳` consisting of the final presheaf `Ψ(𝟭)` together with the presheaves
`Ψ(a ∘ q)` represented by `a ∘ q` for an algebraic stack `𝒯` with faithful structure functor and a
smooth 1-morphism `q : 𝒯 ⟶ (Sch/U₀)`. -/
def SmoothOverAtlas (F : 𝒳.val.val.objᵒᵖ ⥤ Type (u + 1)) : Prop :=
  F = componentPresheaf (𝟭 𝒳.val.val.obj) ∨
    ∃ (𝒯 : AlgebraicStacks.{u, w} B S hS) (q : 𝒯 ⟶ schemeStack.{u, w} B S hS U₀),
      𝒯.val.val.p.Faithful ∧ AlgebraicStacks.IsSmooth B S hS q ∧
        F = componentPresheaf (CatFiberedInGroupoids.homFunctor (q ≫ a).hom)

variable {𝒳 a}

/-- The image under `a` of the morphism to the terminal object of a slice lies over the structure
morphism of its source. -/
lemma isHomLift_map_toUnit (z₀ : Over U₀) :
    𝒳.val.val.p.IsHomLift z₀.hom
      ((CatFiberedInGroupoids.homFunctor a.hom).map (Over.homMk z₀.hom (Category.comp_id _) :
        z₀ ⟶ Over.mk (𝟙 U₀))) :=
  PresheafOfCategories.isHomLift_map_of_comp (q := Over.forget U₀) a.hom.hom.w z₀.hom _
    (IsHomLift.of_fac' (Over.forget U₀) z₀.hom _ rfl rfl (by simp))

variable (τ : SiteKind) (P : ObjectProperty 𝒳.val.val.obj)
  (hcl : IsClosedUnderSitePullback B S hS 𝒳.val.val.p P τ)

include hcl in
/-- **The distinguished object of a smooth 1-morphism through the presentation is in the
subcategory.** If `q ∘ e : (Sch/D) ⟶ (Sch/U₀)` is smooth and the distinguished object `x` of the
presentation `a` belongs to the subcategory, so does the image under `a ∘ q ∘ e` of the identity
of `D`: it maps to `x` over the morphism `D ⟶ U₀` underlying `q ∘ e`, which is smooth because the
identity of `D` is a smooth object of `(Sch/D)` and smooth 1-morphisms preserve smooth objects. -/
lemma prop_atlasObj_of_isSmooth {D : BigFppfOver B S hS}
    (g : schemeStack.{u, w} B S hS D ⟶ schemeStack.{u, w} B S hS U₀)
    (hg : AlgebraicStacks.IsSmooth B S hS g)
    (hx : P ((CatFiberedInGroupoids.homFunctor a.hom).obj (Over.mk (𝟙 U₀)))) :
    P ((CatFiberedInGroupoids.homFunctor a.hom).obj
      ((CatFiberedInGroupoids.homFunctor g.hom).obj (Over.mk (𝟙 D)))) := by
  set z₀ : Over U₀ := (CatFiberedInGroupoids.homFunctor g.hom).obj (Over.mk (𝟙 D))
  have hsm : smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS U₀) z₀ :=
    LisseEtale.smoothObject_map.{u, w} B S hS g hg
      ⟨Over.mk (𝟙 D), smoothObject_schemeStack_id.{u, w} B S hS D⟩
  replace hsm : Smooth ((BigFppfOver.toScheme B S hS).map (z₀ : Over U₀).hom) :=
    (smoothObject_schemeStack_iff.{u, w} B S hS U₀ z₀).1 hsm
  have hl := isHomLift_map_toUnit (a := a) z₀
  have hsmooth : Smooth (B.inclusion.map (𝒳.val.val.p.map
      ((CatFiberedInGroupoids.homFunctor a.hom).map (Over.homMk z₀.hom (Category.comp_id _) :
        z₀ ⟶ Over.mk (𝟙 U₀)))).left) := by
    have h := IsHomLift.fac' 𝒳.val.val.p z₀.hom
      ((CatFiberedInGroupoids.homFunctor a.hom).map (Over.homMk z₀.hom (Category.comp_id _) :
        z₀ ⟶ Over.mk (𝟙 U₀)))
    have := hsm
    change Smooth ((BigFppfOver.toScheme B S hS).map _)
    rw [h]
    simp only [Functor.map_comp]
    infer_instance
  rcases hcl with ⟨-, h⟩ | ⟨-, h⟩
  · exact h _ hsmooth hx
  · have := hsmooth
    exact h ((CatFiberedInGroupoids.homFunctor a.hom).map (Over.homMk z₀.hom
      (Category.comp_id _) : z₀ ⟶ Over.mk (𝟙 U₀))) inferInstance inferInstance hx

end Class

/-! ### Closure under representable covers -/

section Closure

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {U₀ : BigFppfOver B S hS}
  (a : schemeStack.{u, w} B S hS U₀ ⟶ 𝒳) (τ : SiteKind) (P : ObjectProperty 𝒳.val.val.obj)
  (hcl : IsClosedUnderSitePullback B S hS 𝒳.val.val.p P τ)

/-- A smooth surjective morphism of objects of the site generates a covering sieve of either of
the two topologies admitted by Stacks 07AK. -/
lemma generatesCovering_of_isClosedUnderSitePullback
    (hcl : IsClosedUnderSitePullback B S hS 𝒳.val.val.p P τ) {U : BigFppfOver B S hS}
    {W : B.Schemes} (m : W ⟶ U.left) (hsm : Smooth (B.inclusion.map m))
    (hsurj : Surjective (B.inclusion.map m)) :
    Sieve.generate (Presieve.singleton
        (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U))
      ∈ BigFppfOver.baseOverTopology B S hS τ U := by
  rcases hcl with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact generate_singleton_mem_baseOverTopology_etale B S hS m hsm hsurj
  · exact generate_singleton_mem_baseOverTopology_fppf B S hS m hsm hsurj

include hcl in
/-- **The presheaves represented by algebraic stacks smooth over a presentation are closed under
representable covers.** Let `a : (Sch/U₀) ⟶ 𝒳` be smooth and surjective with distinguished object
in the subcategory `𝒳'`. Every member of `AlgebraicGeometry.Stack.SmoothOverAtlas` receives a
locally surjective map from the representable presheaf of an object of `𝒳'`, locally surjective
also after restriction to `𝒳'`, whose fibre powers are again members:

* the final presheaf is covered by the distinguished object `x` of `a`, and its fibre powers are
  represented by the iterated 2-fibre products `U₀ ×_𝒳 ⋯ ×_𝒳 U₀`, smooth over `U₀` through their
  first projection (**Stacks 075W**);
* the presheaf represented by `a ∘ q` for `q : 𝒯 ⟶ (Sch/U₀)` smooth is covered by the image `y`
  of the distinguished object of a smooth surjective atlas `e : (Sch/D) ⟶ 𝒯`, which lies in `𝒳'`
  because it maps to `x` over the smooth morphism `D ⟶ U₀` underlying `q ∘ e`; its fibre powers
  are represented by the iterated 2-fibre products `D ×_𝒯 ⋯ ×_𝒯 D`, smooth over `U₀` through
  their projections to `𝒯` followed by `q`.

The local surjectivity is **Stacks 06XH** for the atlas, in the form
`AlgebraicGeometry.Stack.isLocallySurjective_componentPresheafMap_atlas`, and after restriction it
follows from cocontinuity of the inclusion of `𝒳'`. -/
theorem isClosedUnderRepresentableCovers_smoothOverAtlas
    (hasm : AlgebraicStacks.IsSmooth B S hS a) (hasurj : IsSurjective B S hS a)
    (hx : P ((CatFiberedInGroupoids.homFunctor a.hom).obj (Over.mk (𝟙 U₀)))) :
    haveI := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
      𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl
    IsClosedUnderRepresentableCovers.{u + 1}
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
      (P.ι.inheritedTopology (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)) P.ι
      (SmoothOverAtlas 𝒳 a) := by
  have := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl
  have := isCocontinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl
  have hgen := @generatesCovering_of_isClosedUnderSitePullback B S hS 𝒳 τ P hcl
  -- the cover of the presheaf represented by `z` given by an atlas of the source of `z`
  have key : ∀ {𝒯 : AlgebraicStacks.{u, w} B S hS} (z : 𝒯.val.val.obj ⥤ 𝒳.val.val.obj)
      (hz : z ⋙ 𝒳.val.val.p = 𝒯.val.val.p) [z.Faithful] {D : BigFppfOver B S hS}
      (e : schemeStack.{u, w} B S hS D ⟶ 𝒯), AlgebraicStacks.IsSmooth B S hS e →
      IsSurjective B S hS e →
      ∀ (hy : P ((CatFiberedInGroupoids.homFunctor e.hom ⋙ z).obj (Over.mk (𝟙 D)))),
      ∃ t : uliftYoneda.{u + 1}.obj (P.ι.obj ⟨_, hy⟩) ⟶ componentPresheaf z,
        Presheaf.IsLocallySurjective (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) t ∧
        Presheaf.IsLocallySurjective
          (P.ι.inheritedTopology (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ))
          (Functor.whiskerLeft P.ι.op t) ∧
        ∀ r : ℕ, Nonempty (tuplePresheaf t (r + 1) ≅ componentPresheaf
          (CatFiberedInGroupoids.homFunctor (cechTower B S hS e (r + 1)).2.hom ⋙ z)) := by
    intro 𝒯 z hz _ D e hesm hesurj hy
    let E₀ := componentPresheafIsoOfIsTerminal (CatFiberedInGroupoids.homFunctor e.hom ⋙ z)
      (Over.mkIdTerminal (X := D))
    have := isLocallySurjective_componentPresheafMap_atlas τ hgen z hz e hesm hesurj
    let t := E₀.inv ≫ componentPresheafMap z (CatFiberedInGroupoids.homFunctor e.hom) ≫
      (Iso.refl _).hom
    have ht : Presheaf.IsLocallySurjective
        (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) t := inferInstance
    refine ⟨t, ht, Presheaf.isLocallySurjective_whisker
      (P.ι.inheritedTopology (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ))
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) P.ι t, fun r => ?_⟩
    obtain ⟨E, -⟩ := exists_tuplePresheaf_iso_cechTower z hz e (r + 1)
    exact ⟨tuplePresheafCompIso E₀.symm _ (Iso.refl _) (r + 1) ≪≫ E⟩
  have hfaithD : ∀ D : BigFppfOver B S hS, (schemeStack.{u, w} B S hS D).val.val.p.Faithful :=
    fun D => inferInstanceAs (Over.forget D).Faithful
  rintro F (rfl | ⟨𝒯, q, hfaith, hq, rfl⟩)
  · -- the final presheaf, covered by the distinguished object of the presentation
    have := hfaithD U₀
    obtain ⟨t, ht, htK, htup⟩ := key (𝟭 _) (Functor.id_comp _) a hasm hasurj hx
    exact ⟨⟨_, hx⟩, t, ht, htK, fun r => ⟨_, Or.inr ⟨(cechTower B S hS a (r + 1)).1,
      (twoFibreProductSquareAlgebraicStacks B S hS a (cechTower B S hS a r).2).fst,
      faithful_cechTower a (r + 1), isSmooth_cechTower_fst a hasm r, rfl⟩, htup r⟩⟩
  · -- the presheaf represented by `a ∘ q`, covered by the image of an atlas of `𝒯`
    have hz : CatFiberedInGroupoids.homFunctor (q ≫ a).hom ⋙ 𝒳.val.val.p = 𝒯.val.val.p :=
      (q ≫ a).hom.hom.w
    have : (CatFiberedInGroupoids.homFunctor (q ≫ a).hom).Faithful :=
      Functor.Faithful.of_comp_eq hz
    obtain ⟨D, e, hesm, hesurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒯
    have := hfaithD D
    have hy := prop_atlasObj_of_isSmooth (a := a) τ P hcl (e ≫ q)
      (AlgebraicStacks.isSmooth_comp B S hS e q hesm hq) hx
    obtain ⟨t, ht, htK, htup⟩ := key _ hz e hesm hesurj hy
    exact ⟨⟨_, hy⟩, t, ht, htK, fun r => ⟨_, Or.inr ⟨(cechTower B S hS e (r + 1)).1,
      (cechTower B S hS e (r + 1)).2 ≫ q, faithful_cechTower e (r + 1),
      AlgebraicStacks.isSmooth_comp B S hS _ q (isSmooth_cechTower e hesm (r + 1)) hq, rfl⟩,
      htup r⟩⟩

end Closure

end AlgebraicGeometry.Stack

end
