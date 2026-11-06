module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase

/-!
# Automorphism groups at a point under base change (Stacks 0DUB)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks and let `f' : 𝒳' ⟶ 𝒴'` be its base change
along `g : 𝒴' ⟶ 𝒴`, so that `𝒳'` is the apex of a 2-cartesian square with `f'` its first
projection. Part (1) of Stacks 0DUB says that the property of *inducing an isomorphism between
automorphism groups at a point* (Stacks 0DTW,
`AlgebraicGeometry.Stack.InducesIsomorphismAt`) passes from `f` at a point `x` of `|𝒳|` to `f'`
at any point `x'` of `|𝒳'|` above `x`. Nothing global is assumed: the hypothesis is the
isomorphism at the single point `x`, and the conclusion is the isomorphism at the single point
`x'`.

The automorphism group of a point is read, as in
`StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupAtPoint`, on the sections of the
automorphism group algebraic space: these are the automorphisms of the objects of the stack
lying over a representative which lie over an identity of the site
(`CategoryTheory.Functor.verticalAut`), and `f` acts on them by
`CategoryTheory.Functor.verticalAutMap`. So all that has to be proved is that the vertical
automorphisms of an object of the 2-fibre product are computed by its two components, which is
`CategoryTheory.TwoFibreProductOver.bijective_verticalAutMap_fst`: a vertical automorphism of
`(U, x, y, φ)` is a pair of vertical automorphisms `α` of `x` and `β` of `y` with
`F α ≫ φ = φ ≫ G β`, so `α` determines `G β`, and bijectivity at `y` then determines `β`.

## Main results

* `CategoryTheory.TwoFibreProductOver.bijective_verticalAutMap_fst`: the first projection of a
  2-fibre product of categories over a base induces an isomorphism between the automorphism
  groups at an object as soon as the opposite side of the square does at the object's second
  component.
* `AlgebraicGeometry.Stack.inducesIsomorphismAt_baseChange`: **Stacks 0DUB, part (1)**.

Part (2), that a stabilizer-preserving 1-morphism stays stabilizer preserving after base change,
is `AlgebraicGeometry.Stack.nonempty_inertiaPullbackComparison_isEquivalenceOver_baseChange` in
`StacksFrontier.AlgebraicGeometry.Stacks.StabilizerPreserving`.

## Implementation notes

The hypothesis of part (1) is pointwise, so it cannot be routed through the *global*
`CategoryTheory.Functor.bijective_verticalAutMap`, which assumes that the inertia comparison of
Stacks 06R5 is full and essentially surjective — that assumption is the content of part (2), and
using it here would prove a corollary of part (2) rather than part (1).

An arbitrary 2-cartesian square is compared with the concrete 2-fibre product of Stacks 0040 by
`AlgebraicGeometry.Stack.isEquivalence_lift_of_isTwoFibreProduct`, whose proof is the one
already used for part (2); vertical automorphism groups are then transported along the resulting
equivalence by `CategoryTheory.Functor.bijective_verticalAutMap_of_fullyFaithful`.

`CategoryTheory.Functor.verticalAut` is a subgroup of the automorphism group rather than a
subtype of the endomorphisms lying over an identity, so the pair `(α, β)` produced for
surjectivity has to be shown invertible; that is
`CategoryTheory.TwoFibreProductOver.isIso_of_isIso_components`. For the same reason verticality
is spelled both as `CategoryTheory.Functor.mem_verticalAut_iff` and as an `IsHomLift` over an
identity, and `CategoryTheory.Functor.mem_verticalAut_of_map_mem` moves it across a 1-morphism
over the base.

## References

* [Stacks Project, Tag 0DUB](https://stacks.math.columbia.edu/tag/0DUB)
* [Stacks Project, Tag 0DTW](https://stacks.math.columbia.edu/tag/0DTW)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

universe uC vC uX vX uY vY uZ vZ

variable {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
  {Y : Type uY} [Category.{vY} Y] {Z : Type uZ} [Category.{vZ} Z]
  {pX : X ⥤ C} {pY : Y ⥤ C} {pZ : Z ⥤ C}

/-- A 1-morphism over the base *reflects* verticality: an automorphism whose image lies over an
identity lies over an identity itself, because the structure functors determine each other. -/
lemma mem_verticalAut_of_map_mem (F : X ⥤ Y) (hF : F ⋙ pY = pX) {a : X} (α : Aut a)
    (h : pY.map (F.map α.asIso.hom) = 𝟙 (pY.obj (F.obj a))) : α ∈ pX.verticalAut a := by
  have hc : pY.map (F.map α.asIso.hom) = eqToHom (Functor.congr_obj hF a) ≫ pX.map α.asIso.hom ≫
      eqToHom (Functor.congr_obj hF a).symm := by simpa using Functor.congr_hom hF α.asIso.hom
  have hm : eqToHom (Functor.congr_obj hF a).symm ≫ pY.map (F.map α.asIso.hom) ≫
      eqToHom (Functor.congr_obj hF a) = pX.map α.asIso.hom := by simp [hc]
  rw [mem_verticalAut_iff, ← hm, h]
  simp

/-- A fully faithful 1-morphism over the base induces isomorphisms between all automorphism
groups: it is bijective on automorphisms, and verticality is reflected. -/
theorem bijective_verticalAutMap_of_fullyFaithful (F : X ⥤ Y) (hF : F ⋙ pY = pX)
    (h : F.FullyFaithful) (a : X) : Function.Bijective (verticalAutMap F hF a) := by
  refine ⟨fun α β hab => Subtype.ext (Aut.ext (Iso.ext (h.map_injective (congrArg (fun z => z.1.asIso.hom) hab)))),
    fun β => ?_⟩
  have hpre : F.map (h.preimageIso β.1.asIso).hom = β.1.asIso.hom := h.map_preimage _
  refine ⟨⟨.of (h.preimageIso β.1.asIso), mem_verticalAut_of_map_mem F hF _ ?_⟩,
    Subtype.ext (Aut.ext (Iso.ext hpre))⟩
  rw [hpre]
  exact verticalAut.cond β

/-- The homomorphism of automorphism groups induced by a composite of 1-morphisms over the base
is the composite of the two induced homomorphisms. -/
lemma verticalAutMap_comp (F : X ⥤ Y) (G : Y ⥤ Z) (hF : F ⋙ pY = pX) (hG : G ⋙ pZ = pY)
    (hFG : (F ⋙ G) ⋙ pZ = pX) (a : X) :
    verticalAutMap (F ⋙ G) hFG a =
      (verticalAutMap G hG (F.obj a)).comp (verticalAutMap F hF a) :=
  MonoidHom.ext fun _ => Subtype.ext (Aut.ext rfl)

/-- A composite of 1-morphisms over the base induces an isomorphism between the automorphism
groups at an object as soon as both factors do. -/
theorem bijective_verticalAutMap_comp (F : X ⥤ Y) (G : Y ⥤ Z) (hF : F ⋙ pY = pX)
    (hG : G ⋙ pZ = pY) (hFG : (F ⋙ G) ⋙ pZ = pX) (a : X)
    (hf : Function.Bijective (verticalAutMap F hF a))
    (hg : Function.Bijective (verticalAutMap G hG (F.obj a))) :
    Function.Bijective (verticalAutMap (F ⋙ G) hFG a) := by
  rw [verticalAutMap_comp F G hF hG hFG a, MonoidHom.coe_comp]
  exact hg.comp hf

end CategoryTheory.Functor

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-- The surjectivity half of
`CategoryTheory.TwoFibreProductOver.bijective_verticalAutMap_fst`: a vertical automorphism `α`
of `P.x` is the first component of a vertical automorphism of `P`, as soon as the conjugate
`φ⁻¹ ≫ F α ≫ φ` of `α` is in the image of `G`. -/
private theorem exists_aut_fst_eq (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴)
    (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G)
    (h : Function.Surjective (Functor.verticalAutMap G hG P.y))
    (α : Aut P.x) (hα : α ∈ p𝒳.verticalAut P.x) :
    ∃ Φ : Aut P, Φ ∈ (structureFunctor p𝒳 p𝒴 p𝒮 F G).verticalAut P ∧
      (fst p𝒳 p𝒴 p𝒮 F G).map Φ.asIso.hom = α.asIso.hom := by
  have hαc : p𝒳.map α.asIso.hom = 𝟙 (p𝒳.obj P.x) := (Functor.mem_verticalAut_iff p𝒳 α).mp hα
  have hFα : p𝒮.map (F.map α.asIso.hom) = 𝟙 (p𝒮.obj (F.obj P.x)) :=
    Functor.verticalAut.cond (Functor.verticalAutMap F hF P.x ⟨α, hα⟩)
  have hγ : (Aut.of (P.iso.symm ≪≫ F.mapIso α.asIso ≪≫ P.iso) : Aut (G.obj P.y)) ∈
      p𝒮.verticalAut (G.obj P.y) :=
    (Functor.mem_verticalAut_iff p𝒮 _).mpr (by
      show p𝒮.map (P.iso.inv ≫ F.map α.asIso.hom ≫ P.iso.hom) = _
      rw [p𝒮.map_comp, p𝒮.map_comp, hFα, Category.id_comp]
      exact (p𝒮.mapIso P.iso).inv_hom_id)
  obtain ⟨⟨β, hβmem⟩, hβ⟩ := h ⟨_, hγ⟩
  have hβ' : G.map β.asIso.hom = P.iso.inv ≫ F.map α.asIso.hom ≫ P.iso.hom :=
    congrArg (fun z => z.1.asIso.hom) hβ
  have hbase : eqToHom P.hy.symm ≫ p𝒴.map β.asIso.hom ≫ eqToHom P.hy =
      eqToHom P.hx.symm ≫ p𝒳.map α.asIso.hom ≫ eqToHom P.hx := by
    rw [hαc, (Functor.mem_verticalAut_iff p𝒴 β).mp hβmem]
    simp
  have hw : F.map α.asIso.hom ≫ P.iso.hom = P.iso.hom ≫ G.map β.asIso.hom := by
    rw [hβ', Iso.hom_inv_id_assoc]
  have hiso : @IsIso _ _ P P (Hom.mk' α.asIso.hom β.asIso.hom hbase hw) := by
    refine isIso_of_isIso_components p𝒳 p𝒴 p𝒮 F G
      (Hom.mk' α.asIso.hom β.asIso.hom hbase hw) ?_ ?_
    · rw [Hom.mk'_a]
      exact Iso.isIso_hom α.asIso
    · rw [Hom.mk'_b]
      exact Iso.isIso_hom β.asIso
  refine ⟨.of (@asIso _ _ P P (Hom.mk' α.asIso.hom β.asIso.hom hbase hw) hiso), ?_, rfl⟩
  refine (Functor.mem_verticalAut_iff _ _).mpr ?_
  show (Hom.mk' α.asIso.hom β.asIso.hom hbase hw).hbase = 𝟙 P.base
  rw [Hom.mk'_hbase, hαc]
  simp

/-- The automorphism groups of the 2-fibre product `𝒳 ×_𝒮 𝒴` of categories over `𝒞` are
computed by those of the two factors: if `G` induces an isomorphism between the automorphism
groups at `P.y`, then the first projection induces one at `P`.

A vertical automorphism of `P = (U, x, y, φ)` is a pair of vertical automorphisms `α` of `x` and
`β` of `y` with `F α ≫ φ = φ ≫ G β`, so `α` determines `G β` and hence, by the hypothesis, `β`
itself. This is the whole content of part (1) of Stacks 0DUB. -/
theorem bijective_verticalAutMap_fst (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴)
    (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G)
    (h : Function.Bijective (Functor.verticalAutMap G hG P.y)) :
    Function.Bijective (Functor.verticalAutMap (fst p𝒳 p𝒴 p𝒮 F G) fst_comp_eq P) := by
  constructor
  · rintro ⟨Φ, hΦ⟩ ⟨Ψ, hΨ⟩ hΦΨ
    have ha : Φ.asIso.hom.a = Ψ.asIso.hom.a := congrArg (fun z => z.1.asIso.hom) hΦΨ
    have hGb : G.map Φ.asIso.hom.b = G.map Ψ.asIso.hom.b := by
      refine (cancel_epi P.iso.hom).1 ?_
      rw [← Φ.asIso.hom.w, ← Ψ.asIso.hom.w, ha]
    have key : Functor.verticalAutMap G hG P.y
          (Functor.verticalAutMap (snd p𝒳 p𝒴 p𝒮 F G) snd_comp_eq P ⟨Φ, hΦ⟩) =
        Functor.verticalAutMap G hG P.y
          (Functor.verticalAutMap (snd p𝒳 p𝒴 p𝒮 F G) snd_comp_eq P ⟨Ψ, hΨ⟩) :=
      Subtype.ext (Aut.ext (Iso.ext hGb))
    exact Subtype.ext (Aut.ext (Iso.ext (Hom.ext' ha (congrArg (fun z => z.1.asIso.hom) (h.1 key)))))
  · intro α
    obtain ⟨Φ, hΦmem, hΦa⟩ := exists_aut_fst_eq hF hG P h.2 α.1 α.2
    exact ⟨⟨Φ, hΦmem⟩, Subtype.ext (Aut.ext (Iso.ext hΦa))⟩

end CategoryTheory.TwoFibreProductOver

namespace AlgebraicGeometry.Stack

open CategoryTheory CategoryTheory.Bicategory

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}

/-- The 2-cell filling a 2-commutative square of algebraic stacks, read as an isomorphism of the
underlying functors of the two composites. -/
def squareFiller {f : 𝒳 ⟶ 𝒴} {g : 𝒴' ⟶ 𝒴} (P : Bicategory.TwoCommSq g f) :
    (CatFiberedInGroupoids.homFunctor P.fst.hom ⋙ CatFiberedInGroupoids.homFunctor g.hom) ≅
      (CatFiberedInGroupoids.homFunctor P.snd.hom ⋙
        CatFiberedInGroupoids.homFunctor f.hom) where
  hom := P.iso.hom.hom.hom.toNatTrans
  inv := P.iso.inv.hom.hom.toNatTrans
  hom_inv_id := congrArg (fun m => m.hom.hom.toNatTrans) P.iso.hom_inv_id
  inv_hom_id := congrArg (fun m => m.hom.hom.toNatTrans) P.iso.inv_hom_id

/-- Every component of the 2-cell filling a 2-commutative square of algebraic stacks is vertical:
it lies over an identity of the big site. -/
lemma squareFiller_hom_app_isHomLift {f : 𝒳 ⟶ 𝒴} {g : 𝒴' ⟶ 𝒴}
    (P : Bicategory.TwoCommSq g f) (a : P.pt.val.val.obj) :
    𝒴.val.val.p.IsHomLift (𝟙 (P.pt.val.val.p.obj a)) ((squareFiller B S hS P).hom.app a) :=
  P.iso.hom.hom.hom.isHomLift' a

/-- The comparison functor from the apex of a 2-commutative square of algebraic stacks to the
concrete 2-fibre product of the underlying categories. -/
private abbrev squareLift (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴) (P : Bicategory.TwoCommSq g f) :=
    TwoFibreProductOver.lift 𝒴'.val.val.p 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor g.hom) (CatFiberedInGroupoids.homFunctor f.hom)
      P.pt.val.val.p (CatFiberedInGroupoids.homFunctor P.fst.hom)
      (CatFiberedInGroupoids.homFunctor P.snd.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p P.fst.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p P.snd.hom)
      (squareFiller B S hS P) (squareFiller_hom_app_isHomLift B S hS P)

/-- The comparison 1-morphism from the apex of a 2-cartesian square of algebraic stacks to the
concrete 2-fibre product of Stacks 0040 of the underlying categories over the big site is an
equivalence.

A 2-fibre product of algebraic stacks is also one of categories fibred in groupoids
(`AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids`), the
concrete 2-fibre product carries the canonical such square
(`CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare`), and the
comparison between two 2-fibre products of one cospan is an equivalence. -/
theorem isEquivalence_lift_of_isTwoFibreProduct (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P) :
    (TwoFibreProductOver.lift 𝒴'.val.val.p 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor g.hom) (CatFiberedInGroupoids.homFunctor f.hom)
      P.pt.val.val.p (CatFiberedInGroupoids.homFunctor P.fst.hom)
      (CatFiberedInGroupoids.homFunctor P.snd.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p P.fst.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p P.snd.hom)
      (squareFiller B S hS P)
      (squareFiller_hom_app_isHomLift B S hS P)).IsEquivalence := by
  refine Bicategory.isEquivalence_of_isTwoFibreProduct
    (AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids B S hS P hP)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      g.hom f.hom)
    { hom := Bicategory.InducedBicategory.mkHom
        { toFunctor := squareLift B S hS f g P
          w := TwoFibreProductOver.lift_comp_structureFunctor .. }
      isoFst := Iso.refl _
      isoSnd := Iso.refl _
      compat := ?_ }
  refine Bicategory.InducedBicategory.hom₂_ext (BasedNatTrans.ext _ _ (NatTrans.ext ?_))
  funext a
  exact CatFiberedInGroupoids.map_id_comp_id_eq
    (CatFiberedInGroupoids.homFunctor g.hom) (CatFiberedInGroupoids.homFunctor f.hom)
    (P.iso.hom.hom.hom.toNatTrans.app a)

/-- The base change of `f : 𝒳 ⟶ 𝒴` along `g : 𝒴' ⟶ 𝒴` induces an isomorphism between the
automorphism groups at an object `a` of the apex as soon as `f` does at the image of `a` in `𝒳`.

The apex is compared with the concrete 2-fibre product, where the computation of the vertical
automorphisms is `CategoryTheory.TwoFibreProductOver.bijective_verticalAutMap_fst`. -/
theorem bijective_automorphismGroupMap_fst (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (a : P.pt.val.val.obj)
    (ha : Function.Bijective (automorphismGroupMap B S hS f
      ((CatFiberedInGroupoids.homFunctor P.snd.hom).obj a))) :
    Function.Bijective (automorphismGroupMap B S hS P.fst a) := by
  have := isEquivalence_lift_of_isTwoFibreProduct B S hS f g P hP
  exact Functor.bijective_verticalAutMap_comp
    (squareLift B S hS f g P)
    (TwoFibreProductOver.fst 𝒴'.val.val.p 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor g.hom) (CatFiberedInGroupoids.homFunctor f.hom))
    (TwoFibreProductOver.lift_comp_structureFunctor ..) TwoFibreProductOver.fst_comp_eq
    (CatFiberedInGroupoids.homFunctor_comp_p P.fst.hom) a
    (Functor.bijective_verticalAutMap_of_fullyFaithful _ _
      (Functor.FullyFaithful.ofFullyFaithful _) a)
    (TwoFibreProductOver.bijective_verticalAutMap_fst
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom) _ ha)

/-- **Stacks 0DUB, part (1).** In a 2-cartesian square of algebraic stacks with apex `𝒳'`,
first projection `f' : 𝒳' ⟶ 𝒴'` and second projection `𝒳' ⟶ 𝒳`, if `f` induces an isomorphism
between automorphism groups at the image `x` of a point `x'` of `|𝒳'|`, then `f'` induces an
isomorphism between automorphism groups at `x'`.

The hypothesis is the isomorphism at the single point `x` and nothing else; in particular `f` is
not assumed stabilizer preserving, which is the hypothesis of part (2). -/
@[stacks 0DUB "the automorphism groups at a point of a base change"]
theorem inducesIsomorphismAt_baseChange (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (x' : points B S hS P.pt.val.val P.pt.val.isFiberedInGroupoids)
    (hx : InducesIsomorphismAt B S hS f
      (pointsMap B S hS P.pt.val.val P.pt.val.isFiberedInGroupoids
        𝒳.val.isFiberedInGroupoids P.snd.hom.hom x')) :
    InducesIsomorphismAt B S hS P.fst x' := by
  refine (inducesIsomorphismAt_iff_forall_representatives B S hS P.fst x').2 fun p hp a m => ?_
  exact bijective_automorphismGroupMap_fst B S hS f g P hP a
    ((inducesIsomorphismAt_iff_forall_representatives B S hS f _).1 hx
      (fieldValuedPointMap B S hS P.pt.val.val P.snd.hom.hom p) (by rw [← hp]; rfl)
      ((CatFiberedInGroupoids.homFunctor P.snd.hom).obj a)
      ((CatFiberedInGroupoids.homFunctor P.snd.hom).map m))

end AlgebraicGeometry.Stack

end
