module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowSectionLocalIso
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeReducedFactorization
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyLiftingSubstack

/-!
# Gerbes over an open, through base changes and closed substacks

Let `f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an algebraic space which is a gerbe
over an open `V ⊆ Y`. This file records two ways the gerbe condition passes to a modification of
`f`, as in the proof of [Stacks, Tag 0CQ7]:

* along any 2-fibre product of `f` with a 1-morphism factoring through `V`
  (`AlgebraicGeometry.Stack.AlgebraicStacks.isGerbeOver_snd_of_isTwoFibreProduct`);
* to a full substack containing every object over an open `W`: the 2-fibre product of `W` with
  the substack is the 2-fibre product of `W` with the ambient stack
  (`AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_substackSquare`).

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
* [Stacks Project, Tag 06QE](https://stacks.math.columbia.edu/tag/06QE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Gerbe

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
  {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)

/-- **The gerbe condition over `V` passes to every 2-fibre product with a 1-morphism through
`V`.** If `𝒳_V ⟶ V` is a gerbe, `G : 𝒰 ⟶ Y` is 2-isomorphic to `c ≫ (V ⟶ Y)` and `N` is a
2-fibre product of `f` and `G`, then its projection to `𝒰` is a gerbe. -/
theorem isGerbeOver_snd_of_isTwoFibreProduct (V : Subfunctor Y)
    (hV : Space.IsOpenSubspace B S hS V)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst)
    {𝒰 : AlgebraicStacks.{u, w} B S hS} (G : 𝒰 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (c : 𝒰 ⟶ algebraicSpaceStack.{u, w} B S hS V.toFunctor hV.1)
    (θ : c ≫ algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι ≅ G) (N : TwoCommSq f G)
    (hN : IsTwoFibreProduct N) : IsGerbeOver B S hS N.snd := by
  let Q := twoFibreProductSquareAlgebraicStacks B S hS
    (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f
  have hQ : IsTwoFibreProduct Q := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ f
  have hQ' := isTwoFibreProduct_swap hQ
  exact isGerbeOver_of_isEquivalence_comp B S hS (𝟙 _) N.snd
    (innerSquareOfOuter B S hS Q.swap hQ' θ N).snd (inferInstanceAs (𝟭 _).IsEquivalence)
    (λ_ _ ≪≫ innerSquareOfOuter_snd_iso B S hS Q.swap hQ' θ N)
    (isGerbeOver_of_isTwoFibreProduct B S hS _
      (isTwoFibreProduct_innerSquareOfOuter B S hS Q.swap hQ' θ N hN) hG)

end Gerbe

section Substack

/-- The 2-fibre product of `h` with the inclusion `i` of a full substack followed by `g`, read as
a 2-commutative square over `(h, g)`: its second leg is the projection to the substack followed by
`i`. -/
def substackSquare {𝒳 𝒲 𝒵 : AlgebraicStacks.{u, w} B S hS} (h : 𝒲 ⟶ 𝒵) (g : 𝒳 ⟶ 𝒵)
    (P : ObjectProperty 𝒳.val.val.obj)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P)) : TwoCommSq h g where
  pt := (twoFibreProductSquareAlgebraicStacks B S hS h (fullSubcategoryInclusion 𝒳 P hP ≫ g)).pt
  fst := (twoFibreProductSquareAlgebraicStacks B S hS h (fullSubcategoryInclusion 𝒳 P hP ≫ g)).fst
  snd := (twoFibreProductSquareAlgebraicStacks B S hS h
    (fullSubcategoryInclusion 𝒳 P hP ≫ g)).snd ≫ fullSubcategoryInclusion 𝒳 P hP
  iso := (twoFibreProductSquareAlgebraicStacks B S hS h
    (fullSubcategoryInclusion 𝒳 P hP ≫ g)).iso ≪≫ (α_ _ _ _).symm

/-- A square of identities through two parallel morphisms commutes when they agree. -/
theorem map_id_comp_eq_comp_map_id {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ E) (G : D ⥤ E) {x : C} {y : D} {i j : F.obj x ⟶ G.obj y} (e : i = j) :
    F.map (𝟙 x) ≫ j = i ≫ G.map (𝟙 y) := by
  simp [e]

/-- **A full substack containing every object of the 2-fibre product has the same 2-fibre
product.** Let `i : 𝒳_P ⟶ 𝒳` be the inclusion of a full substack and let every object of the
2-fibre product of `h` and `g` have its `𝒳`-component in `𝒳_P`. Then the 2-fibre product of `h`
and `i ≫ g` is a 2-fibre product of `h` and `g`. -/
def isTwoFibreProduct_substackSquare {𝒳 𝒲 𝒵 : AlgebraicStacks.{u, w} B S hS} (h : 𝒲 ⟶ 𝒵)
    (g : 𝒳 ⟶ 𝒵) (P : ObjectProperty 𝒳.val.val.obj)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (hmem : ∀ s : (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      h.hom g.hom).pt.val.obj, P s.y) :
    IsTwoFibreProduct (substackSquare h g P hP) := by
  refine isTwoFibreProduct_of_underlying (isTwoFibreProduct_of_isEquivalence_to
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      h.hom g.hom)
    (CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u, u + 1, u + 1} h.hom g.hom
      (substackSquare h g P hP).underlying) ?_)
  set L := (CatFiberedInGroupoids.liftTwoFibreProductSquare.{u, u, u + 1, u + 1} h.hom g.hom
    (substackSquare h g P hP).underlying).hom.toFunctor
  have hiso : ∀ t, (L.obj t).iso.hom = t.iso.hom := fun t => Category.comp_id _
  have hfaith : L.Faithful := by
    refine ⟨fun {t t'} m m' e => ?_⟩
    have ha := congrArg TwoFibreProductOver.Hom.a e
    have hb := congrArg TwoFibreProductOver.Hom.b e
    exact TwoFibreProductOver.Hom.ext' ha (ObjectProperty.hom_ext _ hb)
  have hfull : L.Full := by
    refine ⟨fun {t t'} Φ => ?_⟩
    refine ⟨⟨Φ.hbase, Φ.a, ObjectProperty.homMk Φ.b, Φ.ha, isHomLift_restrict _ _ Φ.hb, ?_⟩,
      TwoFibreProductOver.Hom.ext' rfl rfl⟩
    have hw := Φ.w
    rwa [hiso t, hiso t'] at hw
  have hess : L.EssSurj := by
    refine ⟨fun s => ?_⟩
    let t : (substackSquare h g P hP).pt.val.val.obj :=
      { base := s.base, x := s.x, y := ⟨s.y, hmem s⟩, hx := s.hx, hy := s.hy,
        iso := s.iso, vertical := s.vertical }
    have hts : (L.obj t).iso.hom = s.iso.hom := hiso t
    let u : L.obj t ⟶ s := ⟨𝟙 s.base, 𝟙 s.x, 𝟙 s.y, IsHomLift.id s.hx, IsHomLift.id s.hy,
      map_id_comp_eq_comp_map_id _ _ hts⟩
    let v : s ⟶ L.obj t := ⟨𝟙 s.base, 𝟙 s.x, 𝟙 s.y, IsHomLift.id s.hx, IsHomLift.id s.hy,
      map_id_comp_eq_comp_map_id _ _ hts.symm⟩
    exact ⟨t, ⟨⟨u, v, TwoFibreProductOver.Hom.ext' (Category.id_comp _) (Category.id_comp _),
      TwoFibreProductOver.Hom.ext' (Category.id_comp _) (Category.id_comp _)⟩⟩⟩
  have hLe : L.IsEquivalence := Functor.IsEquivalence.mk
  exact hLe

end Substack

end AlgebraicGeometry.Stack.AlgebraicStacks

end
