module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupBaseChange
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.CategoryTheory.FiberedCategory.Strictification
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Fibres

/-!
# Field-valued points of a base change (Stacks 0DUC)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks, let `g : 𝒴' ⟶ 𝒴` be arbitrary, and let
`𝒳'` be the apex of a 2-cartesian square with projections `f' : 𝒳' ⟶ 𝒴'` and `𝒳' ⟶ 𝒳`. If `f`
induces an isomorphism between automorphism groups at points (Stacks 0DTW,
`AlgebraicGeometry.Stack.InducesIsomorphismAt`), then for every field `k` the map
`Mor(Spec k, 𝒳') → Mor(Spec k, 𝒴') × Mor(Spec k, 𝒳)` is injective on isomorphism classes.

By the 2-Yoneda lemma a 1-morphism `Spec k ⟶ 𝒳` is an object of the fibre category of `𝒳` over
the field spectrum, and two such are 2-isomorphic exactly when those objects are isomorphic in
that fibre; so `Mor(Spec k, -)` is read here as `CategoryTheory.Functor.Fiber` at an object `U`
of the big fppf site whose underlying scheme is `Spec k`, and the isomorphism class of a
1-morphism is `CategoryTheory.Functor.isoClassMk`, the library's `Ob(𝒳_U)/≅`.

The square is an arbitrary 2-cartesian square (`CategoryTheory.Bicategory.TwoCommSq` together
with `CategoryTheory.Bicategory.IsTwoFibreProduct`), so no chosen 2-fibre product is forced on
the caller. Over the concrete 2-fibre product of Stacks 0040 the statement is the computation
below: an object of the fibre is a triple `(y', x, φ : g y' ≅ f x)`, and two triples with
isomorphic components differ only by an automorphism of `f x` over `k`, which the hypothesis on
`f` lifts to an automorphism of `x`.

## Main results

* `CategoryTheory.TwoFibreProductOver.nonempty_iso_of_iso_components`: two objects of a fibre
  of the concrete 2-fibre product with isomorphic components are isomorphic, provided the second
  1-morphism of the cospan is surjective on the vertical automorphisms of the second component.
  This replaces the thinness hypothesis under which the same conclusion is
  `CategoryTheory.Functor.exists_iso_of_twoFibreProduct_components`, the injectivity half of
  Stacks 04SD.
* `AlgebraicGeometry.Stack.isoClassMk_eq_of_isoClassMk_eq_components`: **Stacks 0DUC**.

## Implementation notes

The hypothesis of Stacks 0DUC is the one of Stacks 0DTW at every point of `|𝒳|`, and only its
instance at the point represented by the second component enters the proof; it is used through
`AlgebraicGeometry.Stack.inducesIsomorphismAt_iff_forall_representatives`, which turns it into
bijectivity of `AlgebraicGeometry.Stack.automorphismGroupMap` at that component, and only
surjectivity is needed.

The comparison of the arbitrary square with the concrete 2-fibre product is
`AlgebraicGeometry.Stack.isEquivalence_lift_of_isTwoFibreProduct`, as for Stacks 0DUB; the
resulting equivalence is a 1-morphism over the big site, so it is fully faithful and reflects
verticality (`CategoryTheory.Functor.isHomLift_of_isHomLift_map`), which is what transports an
isomorphism of fibre objects back to the apex.

## References

* [Stacks Project, Tag 0DUC](https://stacks.math.columbia.edu/tag/0DUC)
* [Stacks Project, Tag 0DTW](https://stacks.math.columbia.edu/tag/0DTW)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/- `CategoryTheory.Functor.Fiber` is a semireducible definition, so a projection out of a fibre
object is not type-correct at `implicit` transparency and instance search declines to look at
it; this makes the fibre transparent for the proofs below. -/
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber

/-- The comparison isomorphism of an object of the fibre of the 2-fibre product over `U` is
vertical over `U`. -/
private lemma isHomLift_iso_fiber {U : 𝒞}
    (A : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) : p𝒮.IsHomLift (𝟙 U) A.1.iso.hom := by
  obtain ⟨A, hA⟩ := A
  subst hA
  exact A.vertical

/-- For vertical isomorphisms `a`, `b` between the components of two objects of a fibre of the
2-fibre product, the automorphism of `G B.y` by which the comparison square fails to commute is
vertical. -/
theorem isHomLift_discrepancy_hom (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) {U : 𝒞}
    {A B : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U}
    (a : A.1.x ≅ B.1.x) (b : A.1.y ≅ B.1.y)
    (ha : p𝒳.IsHomLift (𝟙 U) a.inv) (hb : p𝒴.IsHomLift (𝟙 U) b.hom) :
    p𝒮.IsHomLift (𝟙 U) ((F.mapIso a ≪≫ B.1.iso).symm ≪≫ (A.1.iso ≪≫ G.mapIso b)).hom := by
  have h₁ : p𝒮.IsHomLift (𝟙 U) B.1.iso.hom := isHomLift_iso_fiber B
  have h₂ : p𝒮.IsHomLift (𝟙 U) A.1.iso.hom := isHomLift_iso_fiber A
  have h₃ : p𝒮.IsHomLift (𝟙 U) (F.map a.inv) :=
    Functor.isHomLift_map_of_comp p𝒮 F a.inv (by rw [hF]; exact ha)
  have h₄ : p𝒮.IsHomLift (𝟙 U) (G.map b.hom) :=
    Functor.isHomLift_map_of_comp p𝒮 G b.hom (by rw [hG]; exact hb)
  show p𝒮.IsHomLift (𝟙 U) ((B.1.iso.inv ≫ F.map a.inv) ≫ A.1.iso.hom ≫ G.map b.hom)
  infer_instance

/-- Two objects of a fibre of the 2-fibre product are isomorphic as soon as there are vertical
isomorphisms between their components making the comparison square commute. -/
theorem nonempty_iso_of_isHomLift_of_comm {U : 𝒞}
    {A B : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U}
    (a : A.1.x ≅ B.1.x) (b : A.1.y ≅ B.1.y)
    (ha : p𝒳.IsHomLift (𝟙 U) a.hom) (hb : p𝒴.IsHomLift (𝟙 U) b.hom)
    (hw : F.map a.hom ≫ B.1.iso.hom = A.1.iso.hom ≫ G.map b.hom) :
    Nonempty (A ≅ B) := by
  have hAB : A.1.base = B.1.base :=
    (show A.1.base = U from A.2).trans (show B.1.base = U from B.2).symm
  have hx := Functor.eqToHom_comp_map_comp_eqToHom p𝒳 a.hom ha A.1.hx B.1.hx hAB
  have hbase : eqToHom A.1.hy.symm ≫ p𝒴.map b.hom ≫ eqToHom B.1.hy
      = eqToHom A.1.hx.symm ≫ p𝒳.map a.hom ≫ eqToHom B.1.hx :=
    (Functor.eqToHom_comp_map_comp_eqToHom p𝒴 b.hom hb A.1.hy B.1.hy hAB).trans hx.symm
  let φ : A.1 ⟶ B.1 := Hom.mk' a.hom b.hom hbase hw
  have hφlift : (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsHomLift (𝟙 U) φ := by
    refine IsHomLift.of_fac' (structureFunctor p𝒳 p𝒴 p𝒮 F G) (𝟙 U) φ A.2 B.2 ?_
    show eqToHom A.1.hx.symm ≫ p𝒳.map a.hom ≫ eqToHom B.1.hx
      = eqToHom A.2 ≫ 𝟙 U ≫ eqToHom B.2.symm
    refine hx.trans ?_
    simp only [Category.id_comp, eqToHom_trans]
    rfl
  have : IsIso φ :=
    isIso_of_isIso_components p𝒳 p𝒴 p𝒮 F G φ
      (by rw [show φ.a = a.hom from rfl]; exact Iso.isIso_hom a)
      (by rw [show φ.b = b.hom from rfl]; exact Iso.isIso_hom b)
  exact ⟨Functor.fiberIsoOfLift (structureFunctor p𝒳 p𝒴 p𝒮 F G) (asIso φ) hφlift⟩

/-- Two objects `A`, `B` of a fibre of the 2-fibre product `𝒳 ×_𝒮 𝒴` of categories over `𝒞`
whose `𝒳`-components and whose `𝒴`-components are isomorphic in the respective fibres are
themselves isomorphic, provided `G` is surjective on the automorphisms of `B`'s `𝒴`-component
lying over an identity.

A pair of component isomorphisms need not make the comparison square of a morphism of the
2-fibre product commute; the two sides differ by an automorphism of `G B.y` over the base, and
the hypothesis replaces the `𝒴`-component by one for which they agree. Under thinness of the
fibres of `p𝒮` the square commutes for free and no correction is needed, which is
`CategoryTheory.Functor.exists_iso_of_twoFibreProduct_components`. -/
theorem nonempty_iso_of_iso_components (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) {U : 𝒞}
    {A B : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U}
    (hsurj : Function.Surjective (Functor.verticalAutMap G hG B.1.y))
    (α : (Functor.fiberMap (structureFunctor p𝒳 p𝒴 p𝒮 F G) p𝒳
        (fst p𝒳 p𝒴 p𝒮 F G) fst_comp_eq U).obj A ≅
      (Functor.fiberMap (structureFunctor p𝒳 p𝒴 p𝒮 F G) p𝒳
        (fst p𝒳 p𝒴 p𝒮 F G) fst_comp_eq U).obj B)
    (β : (Functor.fiberMap (structureFunctor p𝒳 p𝒴 p𝒮 F G) p𝒴
        (snd p𝒳 p𝒴 p𝒮 F G) snd_comp_eq U).obj A ≅
      (Functor.fiberMap (structureFunctor p𝒳 p𝒴 p𝒮 F G) p𝒴
        (snd p𝒳 p𝒴 p𝒮 F G) snd_comp_eq U).obj B) :
    Nonempty (A ≅ B) := by
  let a : A.1.x ≅ B.1.x := Functor.Fiber.fiberInclusion.mapIso α
  let b : A.1.y ≅ B.1.y := Functor.Fiber.fiberInclusion.mapIso β
  have hahom : p𝒳.IsHomLift (𝟙 U) a.hom := α.hom.2
  have hbhom : p𝒴.IsHomLift (𝟙 U) b.hom := β.hom.2
  have hBy : p𝒴.obj B.1.y = U := B.1.hy.trans B.2
  -- The discrepancy between the two sides of the comparison square.
  set ε : G.obj B.1.y ≅ G.obj B.1.y :=
    (F.mapIso a ≪≫ B.1.iso).symm ≪≫ (A.1.iso ≪≫ G.mapIso b) with hεdef
  have hεlift : p𝒮.IsHomLift (𝟙 U) ε.hom := isHomLift_discrepancy_hom hF hG a b α.inv.2 hbhom
  have hεmem : ε ∈ p𝒮.verticalAut (G.obj B.1.y) := by
    refine (Functor.mem_verticalAut_iff p𝒮 ε).mpr ?_
    rw [IsHomLift.fac' p𝒮 (𝟙 U) ε.hom]
    simp
  obtain ⟨γ, hγ⟩ := hsurj ⟨ε, hεmem⟩
  -- The lifted automorphism, read as an isomorphism, and the corrected `𝒴`-component.
  let γ' : B.1.y ≅ B.1.y := γ.1
  let b' : A.1.y ≅ B.1.y := b ≪≫ γ'.symm
  have hγhom : G.map γ'.hom = ε.hom := by
    simpa using congrArg
      (fun z : p𝒮.verticalAut (G.obj B.1.y) => (z : Aut (G.obj B.1.y)).hom) hγ
  have hγinv : G.map γ'.inv = ε.inv := (Iso.inv_eq_inv (G.mapIso γ') ε).2 hγhom
  have hγlift : p𝒴.IsHomLift (𝟙 U) γ'.hom := by
    refine IsHomLift.of_fac' p𝒴 (𝟙 U) γ'.hom hBy hBy ?_
    rw [show p𝒴.map γ'.hom = 𝟙 (p𝒴.obj B.1.y) from Functor.verticalAut.cond γ]
    simp
  have hγinvlift : p𝒴.IsHomLift (𝟙 U) γ'.inv := IsHomLift.lift_id_inv p𝒴 U γ'
  have hb'lift : p𝒴.IsHomLift (𝟙 U) b'.hom := IsHomLift.comp_of_lift_id p𝒴 U b.hom γ'.inv
  have hw : F.map a.hom ≫ B.1.iso.hom = A.1.iso.hom ≫ G.map b'.hom := by
    rw [show b'.hom = b.hom ≫ γ'.inv from rfl, G.map_comp, hγinv, hεdef]
    simp
  exact nonempty_iso_of_isHomLift_of_comm a b' hahom hb'lift hw

end CategoryTheory.TwoFibreProductOver

namespace AlgebraicGeometry.Stack

open CategoryTheory CategoryTheory.Bicategory

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 0DUC.** Let `𝒳'` be the apex of a 2-cartesian square of algebraic stacks with
`f' : 𝒳' ⟶ 𝒴'` its first projection, over `f : 𝒳 ⟶ 𝒴` and `g : 𝒴' ⟶ 𝒴`, and suppose `f`
induces an isomorphism between automorphism groups at every point of `|𝒳|` (Stacks 0DTW). Then
for every field `k` the map `Mor(Spec k, 𝒳') → Mor(Spec k, 𝒴') × Mor(Spec k, 𝒳)` is injective
on isomorphism classes.

A 1-morphism `Spec k ⟶ 𝒳'` is, by 2-Yoneda, an object of the fibre of `𝒳'` over an object `U`
of the big site with underlying scheme `Spec k`, and its isomorphism class is
`CategoryTheory.Functor.isoClassMk`; so this says that two such 1-morphisms with the same pair
of classes in `𝒴'` and in `𝒳` have the same class in `𝒳'`. -/
@[stacks 0DUC "field-valued points of a base change, injective on isomorphism classes"]
theorem isoClassMk_eq_of_isoClassMk_eq_components (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hf : ∀ q : points B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids,
      InducesIsomorphismAt B S hS f q)
    (k : Type u) [Field k] (U : BigFppfOver B S hS)
    (hU : (BigFppfOver.toScheme B S hS).obj U ≅ Spec (.of k))
    (a b : P.pt.val.val.p.Fiber U)
    (hfst : Functor.isoClassMk 𝒴'.val.val.p
        ((Functor.fiberMap P.pt.val.val.p 𝒴'.val.val.p
          (CatFiberedInGroupoids.homFunctor P.fst.hom)
          (CatFiberedInGroupoids.homFunctor_comp_p P.fst.hom) U).obj a)
      = Functor.isoClassMk 𝒴'.val.val.p
        ((Functor.fiberMap P.pt.val.val.p 𝒴'.val.val.p
          (CatFiberedInGroupoids.homFunctor P.fst.hom)
          (CatFiberedInGroupoids.homFunctor_comp_p P.fst.hom) U).obj b))
    (hsnd : Functor.isoClassMk 𝒳.val.val.p
        ((Functor.fiberMap P.pt.val.val.p 𝒳.val.val.p
          (CatFiberedInGroupoids.homFunctor P.snd.hom)
          (CatFiberedInGroupoids.homFunctor_comp_p P.snd.hom) U).obj a)
      = Functor.isoClassMk 𝒳.val.val.p
        ((Functor.fiberMap P.pt.val.val.p 𝒳.val.val.p
          (CatFiberedInGroupoids.homFunctor P.snd.hom)
          (CatFiberedInGroupoids.homFunctor_comp_p P.snd.hom) U).obj b)) :
    Functor.isoClassMk P.pt.val.val.p a = Functor.isoClassMk P.pt.val.val.p b := by
  obtain ⟨α⟩ := Functor.exists_iso_of_isoClassMk_eq hfst
  obtain ⟨β⟩ := Functor.exists_iso_of_isoClassMk_eq hsnd
  -- The second component of `b`, as a field-valued point of `𝒳`.
  let q : FieldValuedPoint B S hS 𝒳.val.val :=
    { carrier := k
      base := U
      isSpec := hU
      obj := (CatFiberedInGroupoids.homFunctor P.snd.hom).obj b.1
      «over» := (Functor.congr_obj
        (CatFiberedInGroupoids.homFunctor_comp_p P.snd.hom) b.1).trans b.2 }
  have hbij : Function.Bijective (automorphismGroupMap B S hS f q.obj) :=
    (inducesIsomorphismAt_iff_forall_representatives B S hS f
      (pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids q)).1
      (hf _) q rfl q.obj (𝟙 q.obj)
  -- Compare the apex with the concrete 2-fibre product of Stacks 0040.
  set L := TwoFibreProductOver.lift 𝒴'.val.val.p 𝒳.val.val.p 𝒴.val.val.p
    (CatFiberedInGroupoids.homFunctor g.hom) (CatFiberedInGroupoids.homFunctor f.hom)
    P.pt.val.val.p (CatFiberedInGroupoids.homFunctor P.fst.hom)
    (CatFiberedInGroupoids.homFunctor P.snd.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p P.fst.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p P.snd.hom)
    (squareFiller B S hS P) (squareFiller_hom_app_isHomLift B S hS P)
  have hLp : L ⋙ TwoFibreProductOver.structureFunctor 𝒴'.val.val.p 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor g.hom) (CatFiberedInGroupoids.homFunctor f.hom)
      = P.pt.val.val.p := TwoFibreProductOver.lift_comp_structureFunctor ..
  have : L.IsEquivalence := isEquivalence_lift_of_isTwoFibreProduct B S hS f g P hP
  obtain ⟨e⟩ := TwoFibreProductOver.nonempty_iso_of_iso_components
    (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    (A := ⟨L.obj a.1, a.2⟩) (B := ⟨L.obj b.1, b.2⟩) hbij.2 α β
  -- Transport the isomorphism back along the equivalence.
  let e₀ : L.obj a.1 ≅ L.obj b.1 := Functor.Fiber.fiberInclusion.mapIso e
  let e₁ : a.1 ≅ b.1 := L.preimageIso e₀
  have hlift : P.pt.val.val.p.IsHomLift (𝟙 U) e₁.hom := by
    have h : (TwoFibreProductOver.structureFunctor 𝒴'.val.val.p 𝒳.val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor g.hom)
        (CatFiberedInGroupoids.homFunctor f.hom)).IsHomLift (𝟙 U) (L.map e₁.hom) := by
      rw [show e₁.hom = L.preimage e₀.hom from rfl, L.map_preimage]
      exact e.hom.2
    exact Functor.isHomLift_of_isHomLift_map hLp (𝟙 U) e₁.hom
  exact Functor.isoClassMk_eq_of_iso
    (Functor.fiberIsoOfLift P.pt.val.val.p e₁ hlift)

end AlgebraicGeometry.Stack

end
