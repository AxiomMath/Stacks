module

public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermExact

/-!
# Linearity of the boundary map of the six-term sequence of a 2-fibre product

Let `f : ℋ → ℱ` and `g : 𝒢 → ℱ` be `1`-morphisms of deformation categories over `𝒞_Λ` and let
`𝒲 = ℋ ×_ℱ 𝒢`. The boundary map `δ : Inf(ℱ) → T𝒲` of the six-term sequence is `k`-linear.

`Deformation.boundaryFun` is a map of sets: it sends an automorphism `α` of the chosen
pushforward `x'₀` of `x₀ = f(y₀)` to the class of the quadruple `(k[M], y'₀, z'₀, c' ∘ α ∘ b')`.
This file reads it as a map between the values of two canonical `k`-linear lifts — the lift
`Deformation.infinitesimalAutomorphismLinearLift` of the infinitesimal automorphisms of `x₀` and
the lift `Deformation.associatedTangentSpaceModuleStructure` of the associated square-zero
functor of `𝒲` — and proves it linear.

## Main definitions

* `Deformation.boundaryLiftFun`: the boundary map read on the values of the two linear lifts.
* `Deformation.boundaryLinearMap`: **part (2) of Tag 06L5, the boundary map** — the same map as
  a `k`-linear map `Inf(ℱ) → T𝒲`, at an arbitrary coordinate module.

## Main results

* `Deformation.boundaryObjectHom`: the canonical arrow `δ(α) ⟶ δ(α')` over a linear map `M → N`
  of coordinate modules, where `α'` is the transport of `α`. Its two components are the
  canonical arrows between the chosen pushforwards of `y₀` and of `z₀`.
* `Deformation.boundaryFun_naturality`: the boundary map is natural in the coordinate module.
* `Deformation.isLinearMap_boundaryLiftFun`: the boundary map is `k`-linear at every coordinate
  module.

## Implementation notes

Linearity is obtained from naturality, through `Deformation.isLinearMap_of_natural_at`: a
natural family of maps between the values of two linear functors on finitely generated modules
is linear at every module. That is the only available route, since neither the addition nor the
scalar action of the two lifts is given by a formula — both are produced by the product
conditions of Tag 06I6 — while naturality in the coordinate module is a diagram chase.

The chase is the one the comparison isomorphisms `b'` and `c'` make possible. All three arrows
out of `x₀` whose codomains the boundary map compares are strongly cocartesian over the
structure arrow of the re-based square-zero extension, so each comparison is pinned by its
composite with the chosen inclusion (`Deformation.comp_cocartesianCompare_hom`), and the
canonical arrow between two chosen pushforwards is pinned the same way
(`Deformation.ChosenPushforwardsAt.inclusion_map`). Naturality of `b'` and of `c'` is then the
uniqueness half of the universal property, applied to two arrows that agree after
precomposition with that inclusion.

The source of the boundary map is an automorphism group of a pushforward to the *re-based*
square-zero extension `Deformation.squareZeroCrossUnder`, while the linear lift of the
infinitesimal automorphisms is indexed by the square-zero extension
`Deformation.squareZeroUnder` read as an algebra under the base. The two are compared by
`Deformation.squareZeroCrossUnderIso`, which is the identity on carriers, and the comparison is
natural in the coordinate module; transport along it is what turns a value of the lift into an
argument of the boundary map.

## References

* [Stacks Project, Tag 06L5](https://stacks.math.columbia.edu/tag/06L5)
* [Stacks Project, Tag 06L6](https://stacks.math.columbia.edu/tag/06L6)
-/

@[expose] public section

namespace Deformation

/-! ### Naturality of the comparison of the two square-zero normalizations -/

section Cross
open CategoryTheory
universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The underlying arrow of `𝒞_Λ` of a coordinate map read between the re-based square-zero
extensions is the one of `Deformation.squareZeroExtensionArtinian`, with no transport. -/
public theorem squareZeroCrossUnderMap_right (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    {M N : FGModuleCat.{max v w} k} (h : M ⟶ N) :
    (squareZeroCrossUnderMap.{u, v, w} A h).right =
      (squareZeroExtensionArtinian.{u, w, max v w} Λ k).map h := rfl

/-- The comparison between the square-zero extension read as an algebra under `A` and the one
read in `𝒞_Λ` is natural in the coordinate module. -/
public theorem squareZeroAlgFunctor_map_comp_squareZeroCrossUnderIso
    (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) {M N : FGModuleCat.{max v w} k} (h : M ⟶ N) :
    (squareZeroAlgFunctor.{u, v, w} A).map h ≫ (squareZeroCrossUnderIso.{u, v, w} A N).hom =
      (squareZeroCrossUnderIso.{u, v, w} A M).hom ≫ squareZeroCrossUnderMap.{u, v, w} A h :=
  StructuredArrow.hom_ext _ _ (squareZeroCross_naturality.{u, v, w} A h)

end Cross

/-! ### Naturality of the two comparison isomorphisms of the boundary map -/

section Compare
open CategoryTheory CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G] {F : Type u₃} [Category.{v₃} F]

attribute [local implicit_reducible] squareZeroCrossUnder

/-- The comparison `b'` is pinned by its composite with the chosen inclusion of `x₀`: that
composite is the image under `f` of the chosen inclusion of `y₀`. -/
public theorem inclusion_comp_boundaryCompareFst_hom
    {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : H ⥤ F) {y₀ : H}
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PF : ChosenPushforwardsAt pF (f.obj y₀))
    (hcofF : IsCofiberedInGroupoids pF) (M : FGModuleCat.{max v w} k) :
    PF.inclusion (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M) ≫
        (boundaryCompareFst.{u, v, w} f PH PF hcofF M).hom =
      f.map (PH.inclusion (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M)) := by
  let _ := PF.inclusion_cocartesian (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M)
  let _ := isStronglyCocartesian_boundaryFst.{u, v, w} f PH hcofF M
  exact comp_cocartesianCompare_hom pF
    (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M).hom
    (PF.inclusion (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M))
    (f.map (PH.inclusion (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M)))

/-- The comparison `c'` is pinned by its composite with the chosen inclusion of `x₀`: that
composite is the comparison isomorphism of `w₀` followed by the image under `g` of the chosen
inclusion of `z₀`. -/
public theorem inclusion_comp_boundaryCompareSnd_hom
    {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : H ⥤ F) (g : G ⥤ F)
    {y₀ : H} {z₀ : G} (hzy : (g ⋙ pF).obj z₀ = (f ⋙ pF).obj y₀)
    {cmp : f.obj y₀ ≅ g.obj z₀}
    (hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom)
    (PG : ChosenPushforwardsAt (g ⋙ pF) z₀) (PF : ChosenPushforwardsAt pF (f.obj y₀))
    (hcofF : IsCofiberedInGroupoids pF) (M : FGModuleCat.{max v w} k) :
    PF.inclusion (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M) ≫
        (boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF hcofF M).hom =
      cmp.hom ≫
        g.map (PG.inclusion (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj z₀) M)) := by
  let _ := isStronglyCocartesian_of_isCofiberedInGroupoids hcofF
    (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M).hom
    (cmp.hom ≫ g.map (PG.inclusion (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj z₀) M)))
    (isHomLift_boundarySnd.{u, v, w} f g hzy hcmp PG M)
  let _ := PF.inclusion_cocartesian (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M)
  exact comp_cocartesianCompare_hom pF
    (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M).hom
    (PF.inclusion (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M))
    (cmp.hom ≫ g.map (PG.inclusion (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj z₀) M)))

/-- Two arrows out of the chosen pushforward of `x` that agree after precomposition with the
inclusion satisfy a naturality square along `PF.map ψ`, if they are compatible with the lifts. -/
private theorem map_comp_eq_of_inclusion_comp {C : Type*} [Category C] {p : F ⥤ C} {x : F}
    (P : ChosenPushforwardsAt p x) {A B : Under (p.obj x)} (ψ : A ⟶ B) {YA YB : F}
    (cA : (P.obj A).1 ⟶ YA) (cB : (P.obj B).1 ⟶ YB) (u : YA ⟶ YB) (eA : x ⟶ YA) (eB : x ⟶ YB)
    [p.IsHomLift (𝟙 A.right) cA] [p.IsHomLift (𝟙 B.right) cB] [p.IsHomLift ψ.right u]
    (hA : P.inclusion A ≫ cA = eA) (hB : P.inclusion B ≫ cB = eB) (hu : eA ≫ u = eB) :
    P.map ψ ≫ cB = cA ≫ u := by
  let _ := P.inclusion_cocartesian A
  have _hl := IsHomLift.comp_lift_id_right' p ψ.right (P.map ψ) B.right cB
  have _hr := IsHomLift.comp_lift_id_left' p A.right cA ψ.right u
  refine IsStronglyCocartesian.ext p A.hom (P.inclusion A) ψ.right ?_
  rw [← Category.assoc, P.inclusion_map ψ, hB, ← Category.assoc, hA, hu]

/-- The comparison `b'` is natural in the coordinate module: the canonical arrow between the
chosen pushforwards of `x₀ = f(y₀)` carries `b'` at `M` to `b'` at `N`.

Both sides lie over the coordinate map read in `𝒞_Λ`, and the chosen inclusion of `x₀` into its
pushforward is strongly cocartesian over the structure arrow of the re-based square-zero
extension, so it is enough that the two agree after precomposition with that inclusion — where
both become the image under `f` of the chosen inclusion of `y₀` at `N`. -/
public theorem map_comp_boundaryCompareFst_hom
    {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : H ⥤ F) {y₀ : H}
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PF : ChosenPushforwardsAt pF (f.obj y₀))
    (hcofF : IsCofiberedInGroupoids pF) {M N : FGModuleCat.{max v w} k} (φ : M ⟶ N) :
    PF.map (squareZeroCrossUnderMap.{u, v, w} ((f ⋙ pF).obj y₀) φ) ≫
        (boundaryCompareFst.{u, v, w} f PH PF hcofF N).hom =
      (boundaryCompareFst.{u, v, w} f PH PF hcofF M).hom ≫
        f.map (PH.map (squareZeroCrossUnderMap.{u, v, w} ((f ⋙ pF).obj y₀) φ)) := by
  have _ : pF.IsHomLift (𝟙 (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M).right)
      (boundaryCompareFst.{u, v, w} f PH PF hcofF M).hom :=
    (isHomLift_boundaryCompareFst.{u, v, w} f PH PF hcofF M).1
  have _ : pF.IsHomLift (𝟙 (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) N).right)
      (boundaryCompareFst.{u, v, w} f PH PF hcofF N).hom :=
    (isHomLift_boundaryCompareFst.{u, v, w} f PH PF hcofF N).1
  let _ := isHomLift_map_of_comp_eq (rfl : f ⋙ pF = f ⋙ pF)
    (squareZeroCrossUnderMap.{u, v, w} ((f ⋙ pF).obj y₀) φ).right
    (PH.map (squareZeroCrossUnderMap.{u, v, w} ((f ⋙ pF).obj y₀) φ))
  refine map_comp_eq_of_inclusion_comp PF _ _ _ _ _ _
    (inclusion_comp_boundaryCompareFst_hom.{u, v, w} f PH PF hcofF M)
    (inclusion_comp_boundaryCompareFst_hom.{u, v, w} f PH PF hcofF N) ?_
  rw [← f.map_comp, PH.inclusion_map (squareZeroCrossUnderMap.{u, v, w} ((f ⋙ pF).obj y₀) φ)]

/-- The comparison `c'` is natural in the coordinate module, by the same argument: after
precomposition with the chosen inclusion of `x₀` both sides become the comparison isomorphism of
`w₀` followed by the image under `g` of the chosen inclusion of `z₀` at `N`. -/
public theorem map_comp_boundaryCompareSnd_hom
    {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : H ⥤ F) (g : G ⥤ F)
    {y₀ : H} {z₀ : G} (hzy : (g ⋙ pF).obj z₀ = (f ⋙ pF).obj y₀)
    {cmp : f.obj y₀ ≅ g.obj z₀}
    (hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom)
    (PG : ChosenPushforwardsAt (g ⋙ pF) z₀) (PF : ChosenPushforwardsAt pF (f.obj y₀))
    (hcofF : IsCofiberedInGroupoids pF) {M N : FGModuleCat.{max v w} k} (φ : M ⟶ N) :
    PF.map (squareZeroCrossUnderMap.{u, v, w} ((f ⋙ pF).obj y₀) φ) ≫
        (boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF hcofF N).hom =
      (boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF hcofF M).hom ≫
        g.map (PG.map (squareZeroCrossUnderMap.{u, v, w} ((g ⋙ pF).obj z₀) φ)) := by
  have _ : pF.IsHomLift (𝟙 (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M).right)
      (boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF hcofF M).hom :=
    (isHomLift_boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF hcofF M).1
  have _ : pF.IsHomLift (𝟙 (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) N).right)
      (boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF hcofF N).hom :=
    (isHomLift_boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF hcofF N).1
  have _hg : pF.IsHomLift (squareZeroCrossUnderMap.{u, v, w} ((f ⋙ pF).obj y₀) φ).right
      (g.map (PG.map (squareZeroCrossUnderMap.{u, v, w} ((g ⋙ pF).obj z₀) φ))) :=
    isHomLift_map_of_comp_eq (rfl : g ⋙ pF = g ⋙ pF)
      (squareZeroCrossUnderMap.{u, v, w} ((g ⋙ pF).obj z₀) φ).right
      (PG.map (squareZeroCrossUnderMap.{u, v, w} ((g ⋙ pF).obj z₀) φ))
  refine map_comp_eq_of_inclusion_comp PF _ _ _ _ _ _
    (inclusion_comp_boundaryCompareSnd_hom.{u, v, w} f g hzy hcmp PG PF hcofF M)
    (inclusion_comp_boundaryCompareSnd_hom.{u, v, w} f g hzy hcmp PG PF hcofF N) ?_
  rw [Category.assoc, ← g.map_comp,
    PG.inclusion_map (squareZeroCrossUnderMap.{u, v, w} ((g ⋙ pF).obj z₀) φ)]

end Compare

/-! ### The boundary map is natural in the coordinate module -/

section Naturality
open CategoryTheory CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G] {F : Type u₃} [Category.{v₃} F]

attribute [local implicit_reducible] squareZeroCrossUnder

/-- **The arrow between the two objects the boundary map produces.** For a linear map `φ` of
coordinate modules, the quadruple `δ(α)` over `k[M]` maps to the quadruple `δ(α')` over `k[N]`,
where `α'` is the transport of `α` along `φ`. The two components are the canonical arrows
between the chosen pushforwards of `y₀` and of `z₀`, and the comparison square commutes because
the canonical arrow between the chosen pushforwards of `x₀` intertwines `α` with `α'` and
carries both `b'` and `c'` at `M` to their counterparts at `N`. -/
public noncomputable def boundaryObjectHom
    {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : H ⥤ F) (g : G ⥤ F)
    {y₀ : H} {z₀ : G} (hzy : (g ⋙ pF).obj z₀ = (f ⋙ pF).obj y₀)
    {cmp : f.obj y₀ ≅ g.obj z₀}
    (hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom)
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PG : ChosenPushforwardsAt (g ⋙ pF) z₀)
    (PF : ChosenPushforwardsAt pF (f.obj y₀)) (hcofF : IsCofiberedInGroupoids pF)
    {M N : FGModuleCat.{max v w} k} (φ : M ⟶ N)
    (α : Aut (PF.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M))) :
    boundaryObject.{u, v, w} f g hzy hcmp PH PG PF hcofF M α ⟶
      boundaryObject.{u, v, w} f g hzy hcmp PH PG PF hcofF N
        (PF.transportAut (squareZeroCrossUnderMap.{u, v, w} ((f ⋙ pF).obj y₀) φ) α) where
  hbase := (squareZeroExtensionArtinian.{u, w, max v w} Λ k).map φ
  a := PH.map (squareZeroCrossUnderMap.{u, v, w} ((f ⋙ pF).obj y₀) φ)
  b := PG.map (squareZeroCrossUnderMap.{u, v, w} ((g ⋙ pF).obj z₀) φ)
  ha := PH.map_isHomLift (squareZeroCrossUnderMap.{u, v, w} ((f ⋙ pF).obj y₀) φ)
  hb := PG.map_isHomLift (squareZeroCrossUnderMap.{u, v, w} ((g ⋙ pF).obj z₀) φ)
  w := by
    let ψ : squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M ⟶
        squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) N :=
      squareZeroCrossUnderMap.{u, v, w} ((f ⋙ pF).obj y₀) φ
    let ρ : squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj z₀) M ⟶
        squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj z₀) N :=
      squareZeroCrossUnderMap.{u, v, w} ((g ⋙ pF).obj z₀) φ
    let bM := boundaryCompareFst.{u, v, w} f PH PF hcofF M
    let bN := boundaryCompareFst.{u, v, w} f PH PF hcofF N
    let cM := boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF hcofF M
    let cN := boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF hcofF N
    have hb : PF.map ψ ≫ bN.hom = bM.hom ≫ f.map (PH.map ψ) :=
      map_comp_boundaryCompareFst_hom.{u, v, w} f PH PF hcofF φ
    have hc : PF.map ψ ≫ cN.hom = cM.hom ≫ g.map (PG.map ρ) :=
      map_comp_boundaryCompareSnd_hom.{u, v, w} f g hzy hcmp PG PF hcofF φ
    have hα : PF.map ψ ≫ (PF.transportAut ψ α).hom.val = α.hom.val ≫ PF.map ψ :=
      PF.map_transportHom ψ α
    have hbinv : f.map (PH.map ψ) ≫ bN.inv = bM.inv ≫ PF.map ψ := by
      rw [Iso.comp_inv_eq, Category.assoc, hb, Iso.inv_hom_id_assoc]
    change f.map (PH.map ψ) ≫ bN.inv ≫ (PF.transportAut ψ α).hom.val ≫ cN.hom =
      (bM.inv ≫ α.hom.val ≫ cM.hom) ≫ g.map (PG.map ρ)
    simp only [Category.assoc]
    rw [reassoc_of% hbinv, reassoc_of% hα, hc]

/-- The class of the object the boundary map produces is natural in the coordinate module. -/
public theorem boundaryClass_naturality
    {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : H ⥤ F) (g : G ⥤ F)
    {y₀ : H} {z₀ : G} (hzy : (g ⋙ pF).obj z₀ = (f ⋙ pF).obj y₀)
    {cmp : f.obj y₀ ≅ g.obj z₀}
    (hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom)
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PG : ChosenPushforwardsAt (g ⋙ pF) z₀)
    (PF : ChosenPushforwardsAt pF (f.obj y₀)) (hcofF : IsCofiberedInGroupoids pF)
    (hcofW : IsCofiberedInGroupoids
      (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g))
    {M N : FGModuleCat.{max v w} k} (φ : M ⟶ N)
    (α : Aut (PF.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M))) :
    (isomorphismClasses (BasedCategory.ofFunctor
          (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g)) hcofW).map
        ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).map φ)
        (boundaryClass.{u, v, w} f g hzy hcmp PH PG PF hcofF hcofW M α) =
      boundaryClass.{u, v, w} f g hzy hcmp PH PG PF hcofF hcofW N
        (PF.transportAut (squareZeroCrossUnderMap.{u, v, w} ((f ⋙ pF).obj y₀) φ) α) := by
  have _hl : (BasedCategory.ofFunctor
        (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g)).p.IsHomLift
      ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).map φ)
      (boundaryObjectHom.{u, v, w} f g hzy hcmp PH PG PF hcofF φ α) :=
    TwoFibreProductOver.structureFunctor_isHomLift
      (boundaryObjectHom.{u, v, w} f g hzy hcmp PH PG PF hcofF φ α)
      ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).map φ)
      (PH.map_isHomLift (squareZeroCrossUnderMap.{u, v, w} ((f ⋙ pF).obj y₀) φ))
  exact map_classOf (BasedCategory.ofFunctor
      (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g)) hcofW
    ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).map φ) _ _
    (boundaryObjectHom.{u, v, w} f g hzy hcmp PH PG PF hcofF φ α)

/-- **The boundary map is natural in the coordinate module.** Read in the value of the canonical
linear lift of the associated square-zero functor of `𝒲`, the boundary map commutes with the
action of a linear map of coordinate modules. -/
public theorem boundaryFun_naturality
    {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : H ⥤ F) (g : G ⥤ F)
    {y₀ : H} {z₀ : G} (hzy : (g ⋙ pF).obj z₀ = (f ⋙ pF).obj y₀)
    {cmp : f.obj y₀ ≅ g.obj z₀}
    (hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom)
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PG : ChosenPushforwardsAt (g ⋙ pF) z₀)
    (PF : ChosenPushforwardsAt pF (f.obj y₀)) (hcofF : IsCofiberedInGroupoids pF)
    (hpreW : IsPredeformationCategory.{u, v, w}
      (BasedCategory.ofFunctor
        (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g)).p)
    (hS2W : SchlessingerConditionS2 (CategoryOfElements.π (isomorphismClasses
      (BasedCategory.ofFunctor
        (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g)) hpreW.cofibered)))
    {M N : FGModuleCat.{max v w} k} (φ : M ⟶ N)
    (α : Aut (PF.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M))) :
    boundaryFun.{u, v, w} f g hzy hcmp PH PG PF hcofF hpreW hS2W N
        (PF.transportAut (squareZeroCrossUnderMap.{u, v, w} ((f ⋙ pF).obj y₀) φ) α) =
      ((associatedTangentSpaceModuleStructure.{u, v, w} (BasedCategory.ofFunctor
          (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g))
          hpreW hS2W).functor.map φ)
        (boundaryFun.{u, v, w} f g hzy hcmp PH PG PF hcofF hpreW hS2W M α) := by
  set 𝒲 := BasedCategory.ofFunctor
    (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g)
  have hcast := moduleFunctor_map_cast k
    (associatedTangentSpaceModuleStructure.{u, v, w} 𝒲 hpreW hS2W).functor
    (squareZeroExtensionArtinian.{u, w, max v w} Λ k ⋙ isomorphismClasses 𝒲 hpreW.cofibered)
    (associatedTangentSpaceModuleStructure.{u, v, w} 𝒲 hpreW hS2W).forget_comp φ
    (boundaryFun.{u, v, w} f g hzy hcmp PH PG PF hcofF hpreW hS2W M α)
  refine (Equiv.cast (associatedTangentLift_carrier.{u, v, w} 𝒲 hpreW hS2W N)).injective ?_
  show cast (associatedTangentLift_carrier.{u, v, w} 𝒲 hpreW hS2W N) _ =
    cast (associatedTangentLift_carrier.{u, v, w} 𝒲 hpreW hS2W N) _
  rw [hcast]
  show cast (associatedTangentLift_carrier.{u, v, w} 𝒲 hpreW hS2W N)
      (cast (associatedTangentLift_carrier.{u, v, w} 𝒲 hpreW hS2W N).symm _) =
    (isomorphismClasses 𝒲 hpreW.cofibered).map
      ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).map φ)
      (cast (associatedTangentLift_carrier.{u, v, w} 𝒲 hpreW hS2W M)
        (cast (associatedTangentLift_carrier.{u, v, w} 𝒲 hpreW hS2W M).symm _))
  rw [cast_symm_cancel, cast_symm_cancel]
  exact (boundaryClass_naturality.{u, v, w} f g hzy hcmp PH PG PF hcofF hpreW.cofibered
    φ α).symm

end Naturality

/-! ### The boundary map as a linear map -/

section Linear
open CategoryTheory CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G] {F : Type u₃} [Category.{v₃} F]

attribute [local implicit_reducible] squareZeroCrossUnder

/-- The automorphism of the pushforward of `x₀` to the re-based square-zero extension that an
infinitesimal automorphism of `x₀` over the square-zero extension read as an algebra under the
base of `x₀` determines: transport along the comparison of the two normalizations. -/
public noncomputable def crossInfinitesimalAut
    {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : H ⥤ F) {y₀ : H}
    (PF : ChosenPushforwardsAt pF (f.obj y₀)) (M : FGModuleCat.{max v w} k)
    (a : infinitesimalAutomorphismKernel PF (squareZeroUnderRed pF (f.obj y₀) M)) :
    Aut (PF.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M)) :=
  PF.transportAut (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj y₀) M).hom a.1

/-- Transport to the re-based normalization is compatible with a coordinate map, because the
comparison of the two normalizations is natural in the coordinate module. -/
public theorem crossInfinitesimalAut_map
    {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : H ⥤ F) {y₀ : H}
    (PF : ChosenPushforwardsAt pF (f.obj y₀)) {M N : FGModuleCat.{max v w} k} (φ : M ⟶ N)
    (a : infinitesimalAutomorphismKernel PF (squareZeroUnderRed pF (f.obj y₀) M)) :
    crossInfinitesimalAut.{u, v, w} f PF N
        ((infinitesimalAutomorphismModuleFunctor PF).map φ a) =
      PF.transportAut (squareZeroCrossUnderMap.{u, v, w} ((f ⋙ pF).obj y₀) φ)
        (crossInfinitesimalAut.{u, v, w} f PF M a) :=
  (PF.transportAut_comp (squareZeroUnderMap pF (f.obj y₀) φ)
      (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj y₀) N).hom a.1).symm.trans
    ((congrArg (fun ξ => PF.transportAut ξ a.1)
        (squareZeroAlgFunctor_map_comp_squareZeroCrossUnderIso.{u, v, w}
          ((f ⋙ pF).obj y₀) φ)).trans
      (PF.transportAut_comp (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj y₀) M).hom
        (squareZeroCrossUnderMap.{u, v, w} ((f ⋙ pF).obj y₀) φ) a.1))

/-- The canonical `k`-linear lift of the associated square-zero functor of the `2`-fibre product
`𝒲 = ℋ ×_ℱ 𝒢`: the functor `M ↦ T𝒲(M)` of the coordinate module. -/
public noncomputable abbrev productTangentLift
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : H ⥤ F) (g : G ⥤ F)
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF) :=
  (associatedTangentSpaceModuleStructure.{u, v, w} (productBased.{u, v, w} pF f g)
    (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).predeformation
    (tangentConditionS2.{u, v, w}
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF))).functor

/-- **The boundary map read on the values of the two linear lifts.** The underlying map of
`δ : Inf(ℱ) → T𝒲` at a coordinate module: read the value of the linear lift of the infinitesimal
automorphisms as an automorphism of the pushforward of `x₀` to the re-based square-zero
extension, and apply the boundary map. -/
public noncomputable def boundaryLiftFun
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : H ⥤ F) (g : G ⥤ F)
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF)
    {y₀ : H} {z₀ : G} (hzy : (g ⋙ pF).obj z₀ = (f ⋙ pF).obj y₀)
    {cmp : f.obj y₀ ≅ g.obj z₀}
    (hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom)
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PG : ChosenPushforwardsAt (g ⋙ pF) z₀)
    (PF : ChosenPushforwardsAt pF (f.obj y₀)) (M : FGModuleCat.{max v w} k) :
    ↥((infinitesimalAutomorphismLinearLift PF hF.satisfiesRS).functor.obj M) →
      ↥((productTangentLift.{u, v, w} pF f g hH hG hF).obj M) :=
  fun y =>
    boundaryFun.{u, v, w} f g hzy hcmp PH PG PF hF.predeformation.cofibered
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).predeformation
      (tangentConditionS2.{u, v, w}
        (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF)) M
      (crossInfinitesimalAut.{u, v, w} f PF M
        (cast (infinitesimalAutomorphismLinearLift_carrier PF hF.satisfiesRS M) y))

/-- The boundary map, read on the values of the two linear lifts, is natural in the coordinate
module. -/
public theorem boundaryLiftFun_naturality
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : H ⥤ F) (g : G ⥤ F)
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF)
    {y₀ : H} {z₀ : G} (hzy : (g ⋙ pF).obj z₀ = (f ⋙ pF).obj y₀)
    {cmp : f.obj y₀ ≅ g.obj z₀}
    (hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom)
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PG : ChosenPushforwardsAt (g ⋙ pF) z₀)
    (PF : ChosenPushforwardsAt pF (f.obj y₀)) {M N : FGModuleCat.{max v w} k} (φ : M ⟶ N)
    (y : ↥((infinitesimalAutomorphismLinearLift PF hF.satisfiesRS).functor.obj M)) :
    boundaryLiftFun.{u, v, w} pF f g hH hG hF hzy hcmp PH PG PF N
        (((infinitesimalAutomorphismLinearLift PF hF.satisfiesRS).functor.map φ) y) =
      ((productTangentLift.{u, v, w} pF f g hH hG hF).map φ)
        (boundaryLiftFun.{u, v, w} pF f g hH hG hF hzy hcmp PH PG PF M y) := by
  have h1 : crossInfinitesimalAut.{u, v, w} f PF N
        (cast (infinitesimalAutomorphismLinearLift_carrier PF hF.satisfiesRS N)
          (((infinitesimalAutomorphismLinearLift PF hF.satisfiesRS).functor.map φ) y)) =
      PF.transportAut (squareZeroCrossUnderMap.{u, v, w} ((f ⋙ pF).obj y₀) φ)
        (crossInfinitesimalAut.{u, v, w} f PF M
          (cast (infinitesimalAutomorphismLinearLift_carrier PF hF.satisfiesRS M) y)) := by
    rw [cast_lift_map PF hF.satisfiesRS φ y]
    exact crossInfinitesimalAut_map.{u, v, w} f PF φ _
  exact (congrArg (boundaryFun.{u, v, w} f g hzy hcmp PH PG PF
    hF.predeformation.cofibered
    (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).predeformation
    (tangentConditionS2.{u, v, w}
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF)) N) h1).trans <|
    boundaryFun_naturality.{u, v, w} f g hzy hcmp PH PG PF hF.predeformation.cofibered
    (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).predeformation
    (tangentConditionS2.{u, v, w}
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF)) φ _

/-- **The boundary map of the six-term sequence is `k`-linear.** A natural family of maps between
the values of two linear functors on finitely generated modules is linear at every module, and
the boundary map is such a family. -/
public theorem isLinearMap_boundaryLiftFun
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : H ⥤ F) (g : G ⥤ F)
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF)
    {y₀ : H} {z₀ : G} (hzy : (g ⋙ pF).obj z₀ = (f ⋙ pF).obj y₀)
    {cmp : f.obj y₀ ≅ g.obj z₀}
    (hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom)
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PG : ChosenPushforwardsAt (g ⋙ pF) z₀)
    (PF : ChosenPushforwardsAt pF (f.obj y₀)) (M : FGModuleCat.{max v w} k) :
    IsLinearMap k
      (boundaryLiftFun.{u, v, w} pF f g hH hG hF hzy hcmp PH PG PF M) :=
  isLinearMap_of_natural_at k
    (infinitesimalAutomorphismLinearLift PF hF.satisfiesRS).functor
    (productTangentLift.{u, v, w} pF f g hH hG hF)
    (boundaryLiftFun.{u, v, w} pF f g hH hG hF hzy hcmp PH PG PF)
    (fun φ y => boundaryLiftFun_naturality.{u, v, w} pF f g hH hG hF hzy hcmp PH PG PF φ y) M

/-- **Stacks Project, Tag 06L5, part (2): the boundary map `δ : Inf(ℱ) → T𝒲` of the six-term
sequence, as a `k`-linear map**, at an arbitrary coordinate module. At the rank-one module this
is the third map of the six-term exact sequence of the `2`-fibre product.

This is the form of `δ` that the sequence of `k`-vector spaces asks for;
`Deformation.boundaryFun`, of which it is the linear reading, is a map of sets. -/
@[stacks 06L5 "part (2), the boundary map `Inf(ℱ) → T𝒲` of the six-term exact sequence, as a \
`k`-linear map of the vector spaces of Tag 06IH"]
public noncomputable def boundaryLinearMap
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : H ⥤ F) (g : G ⥤ F)
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF)
    {y₀ : H} {z₀ : G} (hzy : (g ⋙ pF).obj z₀ = (f ⋙ pF).obj y₀)
    {cmp : f.obj y₀ ≅ g.obj z₀}
    (hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom)
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PG : ChosenPushforwardsAt (g ⋙ pF) z₀)
    (PF : ChosenPushforwardsAt pF (f.obj y₀)) (M : FGModuleCat.{max v w} k) :
    ↥((infinitesimalAutomorphismLinearLift PF hF.satisfiesRS).functor.obj M) →ₗ[k]
      ↥((productTangentLift.{u, v, w} pF f g hH hG hF).obj M) :=
  (isLinearMap_boundaryLiftFun.{u, v, w} pF f g hH hG hF hzy hcmp PH PG PF M).mk'
    (boundaryLiftFun.{u, v, w} pF f g hH hG hF hzy hcmp PH PG PF M)

/-- The linear boundary map is the boundary map on representatives. -/
public theorem boundaryLinearMap_apply
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : H ⥤ F) (g : G ⥤ F)
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF)
    {y₀ : H} {z₀ : G} (hzy : (g ⋙ pF).obj z₀ = (f ⋙ pF).obj y₀)
    {cmp : f.obj y₀ ≅ g.obj z₀}
    (hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom)
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PG : ChosenPushforwardsAt (g ⋙ pF) z₀)
    (PF : ChosenPushforwardsAt pF (f.obj y₀)) (M : FGModuleCat.{max v w} k)
    (y : ↥((infinitesimalAutomorphismLinearLift PF hF.satisfiesRS).functor.obj M)) :
    boundaryLinearMap.{u, v, w} pF f g hH hG hF hzy hcmp PH PG PF M y =
      boundaryFun.{u, v, w} f g hzy hcmp PH PG PF hF.predeformation.cofibered
        (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).predeformation
        (tangentConditionS2.{u, v, w}
          (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF)) M
        (crossInfinitesimalAut.{u, v, w} f PF M
          (cast (infinitesimalAutomorphismLinearLift_carrier PF hF.satisfiesRS M) y)) := rfl

end Linear

end Deformation

end
