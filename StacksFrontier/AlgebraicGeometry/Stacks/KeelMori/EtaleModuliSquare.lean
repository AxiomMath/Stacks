module

public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSeparatedModuliSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineUniformModuliSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.ModuliSpaceBasics
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.DiscreteTwoFibreProduct

/-!
# The cartesian square of Stacks 0DUS over a prescribed moduli space

Stacks 0DUS produces, for an étale, separated, stabilizer-preserving 1-morphism `h : 𝒳' ⟶ 𝒳`
with `𝒳` well-nigh affine, a cartesian square over *some* moduli space `𝒳 ⟶ M` of Stacks 0DUP.
In the proof of the Keel–Mori theorem (Stacks 0DUT) the moduli space of `𝒳` is fixed once and
for all, and the square has to sit over it. Any two categorical moduli spaces of `𝒳` are
isomorphic compatibly with the 1-morphisms, so the square of Stacks 0DUS can be moved onto any
prescribed categorical moduli space `f : 𝒳 ⟶ M` with `M` an object of the site.

## Main results

* `AlgebraicGeometry.Stack.cancel_associatedMap_of_iso`: the 1-morphism attached to an
  isomorphism of presheaves can be cancelled on the right.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_congr_of_discrete`: a 2-fibre product over the
  category attached to a presheaf may be read over equal legs and with any filler.
* `AlgebraicGeometry.Stack.exists_moduliSquare_of_isEtale_of_isSeparated`: Stacks 0DUS over a
  prescribed categorical moduli space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The 1-morphism attached to an isomorphism of presheaves can be cancelled on the right.** -/
theorem cancel_associatedMap_of_iso {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ F')
    {W : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (x y : W ⟶ fibredCategory B S hS F)
    (h : x ≫ (associatedMap B S hS e.hom).1 = y ≫ (associatedMap B S hS e.hom).1) : x = y := by
  have key (z : W ⟶ fibredCategory B S hS F) :
      (z ≫ (associatedMap B S hS e.hom).1) ≫ (associatedMap B S hS e.inv).1 = z := by
    refine (hom_eq_of_hom₂ B S hS (Bicategory.associator _ _ _).hom).trans ?_
    rw [← associatedMap_comp, e.hom_inv_id, associatedMap_id_eq]
    exact hom_eq_of_hom₂ B S hS (Bicategory.rightUnitor z).hom
  rw [← key x, h, key y]

/-- **A 2-fibre product over the category attached to a presheaf may be read over equal legs and
with any filler.** -/
noncomputable def isTwoFibreProduct_congr_of_discrete
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a a' : 𝒴 ⟶ fibredCategory B S hS F} {f f' : 𝒳 ⟶ fibredCategory B S hS F}
    (ha : a = a') (hf : f = f')
    (P : Bicategory.TwoCommSq a f) (hP : Bicategory.IsTwoFibreProduct P)
    (φ : P.fst ≫ a' ≅ P.snd ≫ f') :
    Bicategory.IsTwoFibreProduct (⟨P.pt, P.fst, P.snd, φ⟩ : Bicategory.TwoCommSq a' f') := by
  subst ha hf
  exact isTwoFibreProduct_of_eq_of_discrete B S hS P hP φ

/-- **Stacks 0DUS over a prescribed categorical moduli space.** Let `h : 𝒳' ⟶ 𝒳` be étale,
separated and inducing isomorphisms on automorphism groups, with `𝒳` well-nigh affine, and let
`f : 𝒳 ⟶ M` be any categorical moduli space with `M` an object of the site. Then there is a
2-cartesian square
```
𝒳' ⟶ 𝒳
↓     ↓ f
M' ⟶ M
```
with `M' ⟶ M` a separated étale morphism of schemes. -/
theorem exists_moduliSquare_of_isEtale_of_isSeparated
    {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (h : 𝒳' ⟶ 𝒳)
    (h𝒳 : IsWellNighAffine.{u, w} B S hS 𝒳)
    (he : IsEtale B S hS h) (hsep : AlgebraicStacks.IsSeparated B S hS h)
    (hauto : ∀ q : points B S hS 𝒳'.val.val 𝒳'.val.isFiberedInGroupoids,
      InducesIsomorphismAt B S hS h q)
    (M : BigFppfOver B S hS)
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS (yoneda.obj M) (isAlgebraicSpace_yoneda B S hS M))
    (hf : IsCategoricalModuliSpace B S hS ⟨yoneda.obj M, isAlgebraicSpace_yoneda B S hS M⟩
      f.hom) :
    ∃ (M' : BigFppfOver B S hS)
      (f' : 𝒳' ⟶
        algebraicSpaceStack.{u, w} B S hS (yoneda.obj M') (isAlgebraicSpace_yoneda B S hS M'))
      (g : M' ⟶ M) (hcomm : f'.hom ≫ (associatedMap B S hS (yoneda.map g)).1 = h.hom ≫ f.hom),
      Etale ((BigFppfOver.toScheme B S hS).map g) ∧
      _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map g) ∧
      Nonempty (Bicategory.IsTwoFibreProduct
        (ChartBaseChange.moduliSquare h g f.hom f'.hom hcomm)) := by
  obtain ⟨M₀, M', F, F', g, hcomm, het, hgsep, ⟨hP⟩, hF, -, -, -⟩ :=
    exists_isTwoFibreProduct_moduliSpace_of_isEtale_of_isSeparated B S hS h h𝒳 he hsep hauto
  obtain ⟨e, heF⟩ := exists_iso_of_isCategoricalModuliSpace B S hS
    (isCategoricalModuliSpace_of_isUniformCategoricalModuliSpace B S hS
      (isUniformCategoricalModuliSpace_of_isUniformCategoricalModuliSpaceIn B S hS 𝒳 h𝒳 _ _ hF)) hf
  -- the isomorphism of presheaves underlying `e`, and the isomorphism of the site it comes from
  let eP : yoneda.obj M₀ ≅ yoneda.obj M := (ObjectProperty.ι _).mapIso e
  let e' : M₀ ≅ M := Yoneda.fullyFaithful.preimageIso eP
  have he' : yoneda.map e'.hom = e.hom.hom := Yoneda.fullyFaithful.map_preimage _
  have hleg : (associatedMap B S hS (yoneda.map g)).1 ≫ (associatedMap B S hS eP.hom).1 =
      (associatedMap B S hS (yoneda.map (g ≫ e'.hom))).1 := by
    rw [Functor.map_comp, he', associatedMap_comp]
    rfl
  have hcomm' : F'.hom ≫ (associatedMap B S hS (yoneda.map (g ≫ e'.hom))).1 = h.hom ≫ f.hom := by
    rw [← hleg, ← heF]
    refine (hom_eq_of_hom₂ B S hS (Bicategory.associator _ _ _).inv).trans ?_
    show (F'.hom ≫ (associatedMap B S hS (yoneda.map g)).1) ≫ _ = _
    rw [hcomm]
    exact hom_eq_of_hom₂ B S hS (Bicategory.associator _ _ _).hom
  refine ⟨M', F', g ≫ e'.hom, hcomm', ?_, ?_, ⟨?_⟩⟩
  · rw [Functor.map_comp]
    infer_instance
  · rw [Functor.map_comp]
    infer_instance
  · let P := ChartBaseChange.moduliSquare h g F.hom F'.hom hcomm
    exact isTwoFibreProduct_congr_of_discrete B S hS hleg heF _
      (isTwoFibreProduct_postcompose_of_cancel B S hS (associatedMap B S hS eP.hom).1
        (cancel_associatedMap_of_iso B S hS eP) P hP
        ((Bicategory.associator _ _ _).symm ≪≫
          Bicategory.whiskerRightIso P.iso (associatedMap B S hS eP.hom).1 ≪≫
          Bicategory.associator _ _ _)) _

end AlgebraicGeometry.Stack

end
