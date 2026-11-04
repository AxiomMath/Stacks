module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverMapPentagonTransport

/-!
# The functoriality of restriction to an object satisfies the cocycle condition

The transition isomorphisms of Stacks 03DX (1),
`AlgebraicGeometry.BigFppfOver.transitionIso`, satisfy the identity law, the composition law and
compatibility with pullback unconditionally, and
`AlgebraicGeometry.BigFppfOver.pullHom_transitionIso_of_comparison_comp` reduces the remaining
field of a descent datum to one equation: that the comparison isomorphism of Stacks 03DV,
`AlgebraicGeometry.BigFppfOver.localAssociatedModuleComparison`, is compatible with composition
in the big fppf site.  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/ComparisonCoherence.lean` split that
equation into two independent coherences: a square relating
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` at a morphism, at a second
morphism and at their composite, and a cocycle condition among the three instances of
`AlgebraicGeometry.BigFppfOver.objRestrictComp`.

**This file proves the second of the two, unconditionally.**  With the coherence pentagon for
restriction of sheaves of modules, `Stacks.SheafOfModules.overMapCompIso_assoc`, available with
no hypothesis, the cocycle becomes a statement about restriction along single arrows of an
arbitrary site — `Stacks.SheafOfModules.overMapCompIso_cocycle` — and that statement transports
to the big fppf site along the two spellings of restriction,
`AlgebraicGeometry.BigFppfOver.objRestrict_eq_overMap`.  The transport is
`Stacks.whiskerCocycle_of_heq`: a cocycle of comparison isomorphisms is carried along equalities
of the six functors it compares, and the four comparisons of the two spellings are related by
`AlgebraicGeometry.BigFppfOver.objRestrictComp_heq` only heterogeneously, which is exactly what
that lemma consumes.

## Main results

* `Stacks.whiskerCocycle_of_heq`: **a cocycle of comparison isomorphisms transports along
  equalities of the functors it compares**, the four comparisons being related only by `HEq`.
* `Stacks.SheafOfModules.overMapCongrIso_refl`,
  `Stacks.SheafOfModules.overMapCongrIso_trans`,
  `Stacks.SheafOfModules.overMapCompIso_whiskerRight_congrIso` and
  `Stacks.SheafOfModules.overMapCompIso_whiskerLeft_congrIso`: the congruence isomorphisms of
  restriction are reflexive, composable, and may be moved past the composition comparison on
  either side.
* `Stacks.SheafOfModules.overMapCompIso_cocycle`: **the cocycle condition for the functoriality
  of restriction along arrows of a site**, with the three composites pinned by arbitrary
  equalities of arrows rather than being the composites themselves.  Unconditional.
* `AlgebraicGeometry.BigFppfOver.objRestrictComp_cocycle`: **the functoriality of restriction to
  an object of the big fppf site satisfies the cocycle condition.**  Unconditional.  This is the
  coherence that the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/RestrictCompCoherence.lean` name as
  still missing.
* `AlgebraicGeometry.BigFppfOver.transitionIso_hom_comp_hom_symm`: the two transition morphisms
  of a descent datum are mutually inverse.

## Implementation notes

Nothing here carries a `stacks` attribute: Stacks 03DX (1) is still a hypothesis, and a
hypothesis is part of a citation.

Pinning the three composites of `Stacks.SheafOfModules.overMapCompIso_cocycle` by hypotheses is
what makes it the cocycle the big fppf site needs: there the three composites are pinned by
`CategoryTheory.Over.w`, not by the composites of the arrows.  The associativity congruence that
the pentagon ends with is then absorbed for free, since both routes compare restriction along
`h ≫ g ≫ f` with restriction along the pinned arrow by *some* equality of arrows, and any two
proofs of one equality agree.

**What remains, and exactly where it stops.**  The other half of the residue — the square for
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso`, whose constituents are
assembled from `CategoryTheory.Adjunction.leftAdjointUniq` — is not proved here and is proved
nowhere in the library.  Nor is the cocycle above available at a *module*: evaluating
`AlgebraicGeometry.BigFppfOver.objRestrictComp_cocycle` at `𝒢` requires identifying the two
spellings of the outermost restriction, `objRestrict` at the scheme of `Z` with `objRestrict` at
the scheme of the slice object `Over.mk g₁.left`, as a comparison of *morphisms* rather than of
functor types; `objRestrict` is reducible, so that identification unfolds to the concrete
structure sheaf of the big fppf site and exhausts the heartbeat budget, which is the same wall
that forces `AlgebraicGeometry.BigFppfOver.objRestrict_eq_overMap` to be proved by citing a
general lemma instead of by `rfl`.  The functor-level statement proved here is unaffected,
because there the identification is performed once, inside a type.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace Stacks

/-- **A cocycle of comparison isomorphisms transports along equalities of the functors it
compares.**  Suppose `P`, `Q` and `L` are composable functors, `A` contracts `P ⋙ Q`, `C`
contracts `Q ⋙ L` and `D` contracts all three, and the four comparison isomorphisms
`α : P ⋙ Q ≅ A`, `β : A ⋙ L ≅ D`, `γ : Q ⋙ L ≅ C`, `δ : P ⋙ C ≅ D` satisfy the cocycle
identity — contracting the inner pair and then the outer agrees with contracting the outer pair
and then the inner.  If every one of the six functors is *equal* to another one and every one of
the four isomorphisms is heterogeneously equal to the corresponding isomorphism for those, then
the cocycle identity holds for the second system too.

This is how a cocycle proved for restriction along single arrows of a site is transported to
restriction to objects of the big fppf site: the two spellings of restriction are equal functors,
`AlgebraicGeometry.BigFppfOver.objRestrict_eq_overMap`, and the comparison isomorphisms are
transports along those equalities, so they are only *heterogeneously* equal to the comparison
isomorphisms of the other spelling —
`AlgebraicGeometry.BigFppfOver.objRestrictComp_heq`.  Substituting the six equalities makes the
four `HEq`s into equalities, after which there is nothing left to prove. -/
public theorem whiskerCocycle_of_heq {𝒜 : Type u₁} [Category.{v₁} 𝒜] {ℬ : Type u₂}
    [Category.{v₂} ℬ] {𝒞 : Type u₃} [Category.{v₃} 𝒞] {𝒟 : Type u₄} [Category.{v₄} 𝒟]
    {P P' : 𝒜 ⥤ ℬ} {Q Q' : ℬ ⥤ 𝒞} {L L' : 𝒞 ⥤ 𝒟} {A A' : 𝒜 ⥤ 𝒞} {C C' : ℬ ⥤ 𝒟}
    {D D' : 𝒜 ⥤ 𝒟} (hP : P = P') (hQ : Q = Q') (hL : L = L') (hA : A = A') (hC : C = C')
    (hD : D = D') {α : P ⋙ Q ≅ A} {α' : P' ⋙ Q' ≅ A'} {β : A ⋙ L ≅ D} {β' : A' ⋙ L' ≅ D'}
    {γ : Q ⋙ L ≅ C} {γ' : Q' ⋙ L' ≅ C'} {δ : P ⋙ C ≅ D} {δ' : P' ⋙ C' ≅ D'}
    (hα : HEq α α') (hβ : HEq β β') (hγ : HEq γ γ') (hδ : HEq δ δ')
    (h : (Functor.associator P' Q' L').symm ≪≫ Functor.isoWhiskerRight α' L' ≪≫ β' =
      Functor.isoWhiskerLeft P' γ' ≪≫ δ') :
    (Functor.associator P Q L).symm ≪≫ Functor.isoWhiskerRight α L ≪≫ β =
      Functor.isoWhiskerLeft P γ ≪≫ δ := by
  subst hP
  subst hQ
  subst hL
  subst hA
  subst hC
  subst hD
  obtain rfl : α = α' := eq_of_heq hα
  obtain rfl : β = β' := eq_of_heq hβ
  obtain rfl : γ = γ' := eq_of_heq hγ
  obtain rfl : δ = δ' := eq_of_heq hδ
  exact h

end Stacks

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
variable {U V W X : C}

/-! ### The congruence isomorphisms of restriction -/

/-- **Restriction along an arrow is compared with itself by the identity.**  The congruence
isomorphism `Stacks.SheafOfModules.overMapCongrIso` of a reflexive equality of arrows is the
identity isomorphism of the restriction functor, because it is the transport along a reflexive
equality of functors. -/
public theorem overMapCongrIso_refl {Y Z : C} (a : Y ⟶ Z) :
    overMapCongrIso R (rfl : a = a) = Iso.refl (SheafOfModules.overMap.{w} R a) := by
  rw [← overMap_eqToIso]
  exact eqToIso_refl _

/-- **The congruence isomorphisms of restriction compose.**  For `a = b` and `b = c` arrows of
the site, comparing restriction along `a` with restriction along `b` and then with restriction
along `c` is comparing it along `a` with it along `c`.  Both are the transport along the
corresponding equality of functors, and the two equalities of functors coincide. -/
public theorem overMapCongrIso_trans {Y Z : C} {a b c : Y ⟶ Z} (e : a = b) (e' : b = c) :
    overMapCongrIso R e ≪≫ overMapCongrIso R e' = overMapCongrIso R (e.trans e') := by
  rw [← overMap_eqToIso, ← overMap_eqToIso, ← overMap_eqToIso, eqToIso_trans]

/-- **The congruence isomorphism of restriction is compatible with precomposition.**  For
`a = b` arrows `V ⟶ U` and `h : W ⟶ V`, comparing the restrictions along `a` and along `b` and
then restricting further along `h` is restricting along `h` first and then comparing the
restrictions along the composites `h ≫ a` and `h ≫ b`.  Both are the identity on sections; this
is the step that moves a congruence past the composition comparison on the inner side. -/
public theorem overMapCompIso_whiskerRight_congrIso {a b : V ⟶ U} (e : a = b) (h : W ⟶ V) :
    Functor.isoWhiskerRight (overMapCongrIso R e) (SheafOfModules.overMap.{w} R h) ≪≫
        overMapCompIso R b h =
      overMapCompIso R a h ≪≫ overMapCongrIso R (congrArg (fun k : V ⟶ U => h ≫ k) e) := by
  subst e
  rw [overMapCongrIso_refl, overMapCongrIso_refl, Functor.isoWhiskerRight_refl,
    Iso.refl_trans, Iso.trans_refl]

/-- **The congruence isomorphism of restriction is compatible with postcomposition.**  For
`a = b` arrows `W ⟶ V` and `f : V ⟶ U`, restricting along `f` and then comparing the
restrictions along `a` and along `b` is comparing the restrictions along the composites `a ≫ f`
and `b ≫ f` after the composition comparison.  This is the step that moves a congruence past the
composition comparison on the outer side. -/
public theorem overMapCompIso_whiskerLeft_congrIso (f : V ⟶ U) {a b : W ⟶ V} (e : a = b) :
    Functor.isoWhiskerLeft (SheafOfModules.overMap.{w} R f) (overMapCongrIso R e) ≪≫
        overMapCompIso R f b =
      overMapCompIso R f a ≪≫ overMapCongrIso R (congrArg (fun k : W ⟶ V => k ≫ f) e) := by
  subst e
  rw [overMapCongrIso_refl, overMapCongrIso_refl, Functor.isoWhiskerLeft_refl,
    Iso.refl_trans, Iso.trans_refl]

/-! ### The cocycle condition for the functoriality of restriction -/

/-- **The cocycle condition for the functoriality of restriction along arrows of a site, with the
composites pinned by arbitrary equalities.**  Let `f : V ⟶ U`, `g : W ⟶ V` and `h : X ⟶ W`, and
let `a`, `b` and `c` be arrows with `g ≫ f = a`, `h ≫ a = b`, `h ≫ g = c` and `c ≫ f = b`.
Threefold restriction along `f`, `g` and `h` is identified with restriction along `b` in two
ways: contracting the inner pair `(f, g)` to `a` and then the pair `(a, h)`, or contracting the
outer pair `(g, h)` to `c` and then the pair `(f, c)`.  The two agree.

This is the coherence pentagon `Stacks.SheafOfModules.overMapCompIso_assoc` with the three
congruence isomorphisms moved past the composition comparisons by
`Stacks.SheafOfModules.overMapCompIso_whiskerRight_congrIso` and
`Stacks.SheafOfModules.overMapCompIso_whiskerLeft_congrIso`; the associativity congruence that
the pentagon ends with is absorbed, because the two routes then compare restriction along
`h ≫ g ≫ f` with restriction along `b` by equalities of arrows, and any two proofs of one such
equality agree.

Pinning the composites by hypotheses rather than taking them to be the composites themselves is
what makes this the cocycle that the functoriality of restriction to an object of the big fppf
site satisfies: there the three composites are pinned by `CategoryTheory.Over.w`. -/
public theorem overMapCompIso_cocycle (f : V ⟶ U) (g : W ⟶ V) (h : X ⟶ W)
    {a : W ⟶ U} (ea : g ≫ f = a) {b : X ⟶ U} (eb : h ≫ a = b)
    {c : X ⟶ V} (ec : h ≫ g = c) (ecf : c ≫ f = b) :
    (Functor.associator (SheafOfModules.overMap.{w} R f) (SheafOfModules.overMap.{w} R g)
            (SheafOfModules.overMap.{w} R h)).symm ≪≫
        Functor.isoWhiskerRight (overMapCompIso R f g ≪≫ overMapCongrIso R ea)
            (SheafOfModules.overMap.{w} R h) ≪≫
          overMapCompIso R a h ≪≫ overMapCongrIso R eb =
      Functor.isoWhiskerLeft (SheafOfModules.overMap.{w} R f)
          (overMapCompIso R g h ≪≫ overMapCongrIso R ec) ≪≫
        overMapCompIso R f c ≪≫ overMapCongrIso R ecf := by
  subst ea
  subst eb
  subst ec
  rw [overMapCongrIso_refl, overMapCongrIso_refl, overMapCongrIso_refl]
  simp only [Iso.trans_refl]
  exact (overMapCompIso_assoc R f g h).symm

end Stacks.SheafOfModules

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The cocycle for the functoriality of restriction to an object -/

/-- **The functoriality of restriction to an object of the big fppf site satisfies the cocycle
condition.**  Let `g₁ : Z ⟶ T₁` and `g : Z' ⟶ Z` be morphisms of `(Sch/S)_fppf`.  Restricting a
module on `(Sch/S)_fppf` to the big fppf site of the scheme of `T₁`, then to that of `Z`, then to
that of `Z'` is identified with restricting it to the site of the scheme of `Z'` in two ways:
contracting the first two steps by `AlgebraicGeometry.BigFppfOver.objRestrictComp` at `g₁` and
then contracting with the third by `objRestrictComp` at `g`, or contracting the last two steps by
`objRestrictComp` at the morphism `g` read over the scheme of `T₁` and then contracting with the
first by `objRestrictComp` at `g ≫ g₁`.  The two agree.

This is one of the two halves of the residue of
`CategoryTheory.Pseudofunctor.DescentData.pullHom_hom` for the transition isomorphisms of
Stacks 03DX (1), described in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/ComparisonCoherence.lean` and of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/RestrictCompCoherence.lean`.  It is
`Stacks.SheafOfModules.overMapCompIso_cocycle` — the coherence pentagon for restriction along a
single arrow of a site, with the three composites pinned by `CategoryTheory.Over.w` — transported
along `AlgebraicGeometry.BigFppfOver.objRestrict_eq_overMap` by
`Stacks.whiskerCocycle_of_heq`, the `HEq` characterisation
`AlgebraicGeometry.BigFppfOver.objRestrictComp_heq` supplying the four comparisons. -/
public theorem objRestrictComp_cocycle {T₁ Z Z' : BigFppfOver B S hS}
    (g₁ : Z ⟶ T₁) (g : Z' ⟶ Z) :
    (Functor.associator (objRestrict B S hS T₁)
            (objRestrict B (objScheme B S hS T₁) (contains_objScheme B S hS T₁)
              (Over.mk g₁.left))
            (objRestrict B (objScheme B S hS Z) (contains_objScheme B S hS Z)
              (Over.mk g.left))).symm ≪≫
        Functor.isoWhiskerRight (objRestrictComp B S hS g₁)
            (objRestrict B (objScheme B S hS Z) (contains_objScheme B S hS Z)
              (Over.mk g.left)) ≪≫
          objRestrictComp B S hS g =
      Functor.isoWhiskerLeft (objRestrict B S hS T₁)
          (objRestrictComp B (objScheme B S hS T₁) (contains_objScheme B S hS T₁)
            (Over.homMk (U := Over.mk (g ≫ g₁).left) (V := Over.mk g₁.left) g.left rfl)) ≪≫
        objRestrictComp B S hS (g ≫ g₁) := by
  refine Stacks.whiskerCocycle_of_heq
    (objRestrict_eq_overMap B S hS T₁)
    (objRestrict_eq_overMap B (objScheme B S hS T₁) (contains_objScheme B S hS T₁)
      (Over.mk g₁.left))
    (objRestrict_eq_overMap B (objScheme B S hS Z) (contains_objScheme B S hS Z)
      (Over.mk g.left))
    (objRestrict_eq_overMap B S hS Z)
    (objRestrict_eq_overMap B (objScheme B S hS T₁) (contains_objScheme B S hS T₁)
      (Over.mk (g ≫ g₁).left))
    (objRestrict_eq_overMap B S hS Z')
    (objRestrictComp_heq B S hS g₁) (objRestrictComp_heq B S hS g)
    (objRestrictComp_heq B (objScheme B S hS T₁) (contains_objScheme B S hS T₁) _)
    (objRestrictComp_heq B S hS (g ≫ g₁)) ?_
  exact Stacks.SheafOfModules.overMapCompIso_cocycle B.structureSheaf T₁.hom g₁.left g.left
    (Over.w g₁) (Over.w g) rfl (Over.w (g ≫ g₁))

/-- **The two transition morphisms of a descent datum are mutually inverse.**  Over an object
`Z` mapping into two members `T₁` and `T₂` of the family, the transition from the first local
datum to the second followed by the transition from the second to the first is the identity:
`AlgebraicGeometry.BigFppfOver.transitionIso_symm` identifies the second with the inverse of the
first. -/
public theorem transitionIso_hom_comp_hom_symm
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {T₁ T₂ Z : BigFppfOver B S hS}
    (g₁ : Z ⟶ T₁) (g₂ : Z ⟶ T₂)
    {F₁ : (objScheme B S hS T₁).Modules} (hF₁ : F₁.IsQuasicoherent)
    (e₁ : (associatedModule B (objScheme B S hS T₁) (contains_objScheme B S hS T₁)).obj F₁ ≅
      (objRestrict B S hS T₁).obj G)
    {F₂ : (objScheme B S hS T₂).Modules} (hF₂ : F₂.IsQuasicoherent)
    (e₂ : (associatedModule B (objScheme B S hS T₂) (contains_objScheme B S hS T₂)).obj F₂ ≅
      (objRestrict B S hS T₂).obj G) :
    (transitionIso B S hS G g₁ g₂ hF₁ e₁ hF₂ e₂).hom ≫
        (transitionIso B S hS G g₂ g₁ hF₂ e₂ hF₁ e₁).hom = 𝟙 _ := by
  rw [← transitionIso_symm, Iso.inv_hom_id]

end AlgebraicGeometry.BigFppfOver

end
