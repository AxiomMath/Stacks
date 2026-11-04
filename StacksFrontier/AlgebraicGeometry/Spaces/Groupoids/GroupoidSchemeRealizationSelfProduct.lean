module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeRealizationHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.OpenSubgroupoidQuotientSelfProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingOfCompactFibre

/-!
# Self 2-fibre products at a point over the quotient stack of an open subgroupoid scheme

Let `φ : (U, P, …) ⟶ (U, R, …)` be an open subgroupoid of a groupoid scheme — a morphism of
groupoid schemes which is an open immersion on arrows and the equality on objects — and let `u` be
a point of `U` such that `P` contains every arrow of `R` with source and target `u`, as a strong
splitting over `u` does (Stacks 04RK, part (1)). Realize both as groupoids in algebraic spaces and
let `[φ] : [U/P] ⟶ [U/R]` be the induced 1-morphism of quotient stacks. This file proves the step
of **Stacks 0DU5** "since `P ⊂ R` is open and contains `{r ∈ R : s(r) = u, t(r) = u}` we see that
`u ×_𝒰 u ⟶ u ×_𝒳 u` is an isomorphism", in the form: for every 1-morphism `q : 𝒯 ⟶ [U/P]`
whose objects are all presented by generalized points of `U` lying over `u`, the comparison
`𝒯 ×_{[U/P]} 𝒯 ⟶ 𝒯 ×_{[U/R]} 𝒯` is an equivalence.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.Hom.IsOverPoint`: a generalized point of the object scheme lies
  over a point when it takes only that value.

## Main results

* `Stacks.Groupoids.GroupoidScheme.Hom.mono_realization_mapArrows`: the realization of a
  monomorphism on arrows is a monomorphism on arrow spaces.
* `Stacks.Groupoids.GroupoidScheme.Hom.realization_arrow_lift`: an arrow of the realization of
  `R` between the images of two generalized points of `U` over `u` comes from an arrow of the
  realization of `P` between them.
* `Stacks.Groupoids.GroupoidScheme.Hom.isEquivalence_mapBase_quotientStackMap_realization`: the
  comparison of self 2-fibre products.

## References

* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 0DU5](https://stacks.math.columbia.edu/tag/0DU5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Space Opposite

universe u vT uT

namespace Stacks.Groupoids.GroupoidScheme.Hom

variable {S : Scheme.{u}} (C : BigFppfSite.{u}) (hS : C.Contains S)
  {G H : GroupoidScheme S} (φ : Hom G H)
  (hGU : C.Contains G.objects.left) (hGR : C.Contains G.arrows.left)
  (hGP : C.Contains (pullback G.source G.target).left)
  (hHU : C.Contains H.objects.left) (hHR : C.Contains H.arrows.left)
  (hHP : C.Contains (pullback H.source H.target).left)

/-- A generalized point of the object scheme of `G` over a test object lies *over* a point `u`
of the object scheme when every point of the test object is sent to `u`. -/
def IsOverPoint (u : G.objects.left) (T : BigFppfOver C S hS)
    (x : (G.realization C hS hGU hGR hGP).objects.obj.obj (op T)) : Prop :=
  ∀ τ : ((siteToOver C hS).obj T).left, (yonedaSchemePointEquiv C hS hGU (op T) x).left τ = u

/-- Lying over a point is stable under pullback of generalized points. -/
theorem isOverPoint_map (u : G.objects.left) {T T' : BigFppfOver C S hS} (g : T ⟶ T')
    (y : (G.realization C hS hGU hGR hGP).objects.obj.obj (op T'))
    (hy : IsOverPoint C hS hGU hGR hGP u T' y) :
    IsOverPoint C hS hGU hGR hGP u T ((G.realization C hS hGU hGR hGP).objects.obj.map g.op y) := by
  intro τ
  have h : yonedaSchemePointEquiv C hS hGU (op T)
      ((G.realization C hS hGU hGR hGP).objects.obj.map g.op y) =
        (siteToOver C hS).map g ≫ yonedaSchemePointEquiv C hS hGU (op T') y :=
    (siteToOver C hS).map_comp (Z := schemeSiteObject C hS hGU) g y
  rw [h, Over.comp_left, Scheme.Hom.comp_apply]
  exact hy _

/-- **Arrows over a point lift to an open subgroupoid containing every arrow over it.** Let
`φ : G ⟶ H` be a morphism of groupoid schemes which is an open immersion on arrows and an
equality on objects, and let `u` be a point of the object scheme of `H` such that every arrow of
`H` with source and target `u` lies in the image of `φ`. Then an arrow of the realization of `H`
over a test object between the images of two generalized points of `G` lying over the
corresponding point of `G` is the image of an arrow of the realization of `G` between them. -/
theorem realization_arrow_lift [IsOpenImmersion φ.mapArrows.left]
    (e : G.objects = H.objects) (hφ : φ.mapObjects = eqToHom e) (u : H.objects.left)
    (hstab : ∀ r : H.arrows.left, H.source.left.base r = u → H.target.left.base r = u →
      ∃ p : G.arrows.left, φ.mapArrows.left.base p = r)
    (T : BigFppfOver C S hS) (x y : (G.realization C hS hGU hGR hGP).objects.obj.obj (op T))
    (hx : IsOverPoint C hS hGU hGR hGP ((eqToHom e.symm).left.base u) T x)
    (hy : IsOverPoint C hS hGU hGR hGP ((eqToHom e.symm).left.base u) T y)
    (b : (H.realization C hS hHU hHR hHP).arrows.obj.obj (op T))
    (hbs : (H.realization C hS hHU hHR hHP).toGroupoidInFunctors.source.app (op T) b =
      (realization C hS φ hGU hGR hGP hHU hHR hHP).toGroupoidHom.mapObjects.app (op T) x)
    (hbt : (H.realization C hS hHU hHR hHP).toGroupoidInFunctors.target.app (op T) b =
      (realization C hS φ hGU hGR hGP hHU hHR hHP).toGroupoidHom.mapObjects.app (op T) y) :
    ∃ a : (G.realization C hS hGU hGR hGP).arrows.obj.obj (op T),
      (G.realization C hS hGU hGR hGP).toGroupoidInFunctors.source.app (op T) a = x ∧
      (G.realization C hS hGU hGR hGP).toGroupoidInFunctors.target.app (op T) a = y ∧
      (realization C hS φ hGU hGR hGP hHU hHR hHP).toGroupoidHom.mapArrows.app (op T) a = b := by
  set eHU := yonedaSchemePointEquiv C hS hHU (op T)
  set eHR := yonedaSchemePointEquiv C hS hHR (op T)
  set eGU := yonedaSchemePointEquiv C hS hGU (op T)
  set eGR := yonedaSchemePointEquiv C hS hGR (op T)
  have hs : eHR b ≫ H.source = eGU x ≫ φ.mapObjects :=
    (yonedaSchemePointEquiv_map C hS hHR hHU H.source (op T) b).symm.trans ((congrArg eHU hbs).trans
      (yonedaSchemePointEquiv_realization_mapObjects C hS φ hGU hGR hGP hHU hHR hHP (op T) x))
  have ht : eHR b ≫ H.target = eGU y ≫ φ.mapObjects :=
    (yonedaSchemePointEquiv_map C hS hHR hHU H.target (op T) b).symm.trans ((congrArg eHU hbt).trans
      (yonedaSchemePointEquiv_realization_mapObjects C hS φ hGU hGR hGP hHU hHR hHP (op T) y))
  have hpt : ∀ (z : (G.realization C hS hGU hGR hGP).objects.obj.obj (op T)),
      IsOverPoint C hS hGU hGR hGP ((eqToHom e.symm).left.base u) T z →
      ∀ τ, (eGU z ≫ φ.mapObjects).left τ = u := by
    intro z hz τ
    rw [hφ, Over.comp_left, Scheme.Hom.comp_apply]
    rw [hz τ]
    exact over_eqToHom_apply_symm e u
  obtain ⟨a', ha'⟩ := exists_comp_mapArrows_eq_of_forall_eq φ u
    hstab (eHR b)
    (fun τ => by simpa only [Over.comp_left, Scheme.Hom.comp_apply] using
      (congrArg (fun k => k.left τ) hs).trans (hpt x hx τ))
    (fun τ => by simpa only [Over.comp_left, Scheme.Hom.comp_apply] using
      (congrArg (fun k => k.left τ) ht).trans (hpt y hy τ))
  have : IsIso φ.mapObjects := by
    rw [hφ]
    infer_instance
  have key : ∀ (f : G.arrows ⟶ G.objects) (g : H.arrows ⟶ H.objects),
      f ≫ φ.mapObjects = φ.mapArrows ≫ g → ∀ z, eHR b ≫ g = eGU z ≫ φ.mapObjects →
        a' ≫ f = eGU z := fun f g w z hz => by
    rw [← cancel_mono φ.mapObjects, Category.assoc, w, ← Category.assoc, ha', hz]
  refine ⟨eGR.symm a', ?_, ?_, ?_⟩
  · apply eGU.injective
    refine (yonedaSchemePointEquiv_map C hS hGR hGU G.source (op T) _).trans ?_
    rw [Equiv.apply_symm_apply]
    exact key _ _ φ.map_source.symm x hs
  · apply eGU.injective
    refine (yonedaSchemePointEquiv_map C hS hGR hGU G.target (op T) _).trans ?_
    rw [Equiv.apply_symm_apply]
    exact key _ _ φ.map_target.symm y ht
  · apply eHR.injective
    refine (yonedaSchemePointEquiv_realization_mapArrows C hS φ hGU hGR hGP hHU hHR hHP (op T)
      _).trans ?_
    rw [Equiv.apply_symm_apply, ha']

/-- The arrow map of the realization of a morphism of groupoid schemes whose arrow map is a
monomorphism is a monomorphism: on generalized points it is composition with a monomorphism. -/
theorem mono_realization_mapArrows [Mono φ.mapArrows] :
    Mono (realization C hS φ hGU hGR hGP hHU hHR hHP).toGroupoidHom.mapArrows := by
  have happ : ∀ T, Mono
      ((realization C hS φ hGU hGR hGP hHU hHR hHP).toGroupoidHom.mapArrows.app T) := by
    intro T
    rw [mono_iff_injective]
    intro a a' h
    apply (yonedaSchemePointEquiv C hS hGR T).injective
    have h' := (yonedaSchemePointEquiv_realization_mapArrows C hS φ hGU hGR hGP hHU hHR hHP T
      a).symm.trans ((congrArg (yonedaSchemePointEquiv C hS hHR T) h).trans
        (yonedaSchemePointEquiv_realization_mapArrows C hS φ hGU hGR hGP hHU hHR hHP T a'))
    exact (cancel_mono φ.mapArrows).1 h'
  exact NatTrans.mono_of_mono_app _

/-- **The self 2-fibre product comparison at a point over the quotient stack of an open
subgroupoid scheme.** Let `φ : G ⟶ H` be a morphism of groupoid schemes which is an open
immersion on arrows and an equality on objects, and let `u` be a point of the object scheme of
`H` such that every arrow of `H` with source and target `u` lies in the image of `φ`. Let
`q : 𝒯 ⥤ [U/G]` be a functor every object of which is isomorphic to the object presented by a
generalized point of `U` lying over `u`. Then postcomposing both legs of `𝒯 ×_{[U/G]} 𝒯` with the
1-morphism `[φ] : [U/G] ⟶ [U/H]` of the realization of `φ` is an equivalence onto
`𝒯 ×_{[U/H]} 𝒯`.

This is the step "`u ×_𝒰 u ⟶ u ×_𝒳 u` is an isomorphism" of the proof of Stacks 0DU5, before
composing with the étale 1-morphism `[U/H] ⟶ 𝒳`. -/
theorem isEquivalence_mapBase_quotientStackMap_realization [IsOpenImmersion φ.mapArrows.left]
    (e : G.objects = H.objects) (hφ : φ.mapObjects = eqToHom e) (u : H.objects.left)
    (hstab : ∀ r : H.arrows.left, H.source.left.base r = u → H.target.left.base r = u →
      ∃ p : G.arrows.left, φ.mapArrows.left.base p = r)
    {𝒯 : Type uT} [Category.{vT} 𝒯] {pT : 𝒯 ⥤ BigFppfOver C S hS}
    (q : 𝒯 ⥤ (Stack.quotientStack (G.realization C hS hGU hGR hGP)).obj)
    (hq : ∀ a : 𝒯, ∃ X : (presheafOfGroupoids (Stack.evaluationGroupoidFunctor
        (G.realization C hS hGU hGR hGP).toGroupoidInFunctors)).obj,
      IsOverPoint C hS hGU hGR hGP ((eqToHom e.symm).left.base u) X.base X.fiber ∧
        Nonempty (q.obj a ≅ (Stack.pointwiseToQuotientStack _).obj X)) :
    (TwoFibreProductOver.mapBase (pT := pT) (p𝒜 := pT) q q
      (Stack.quotientStackMap (realization C hS φ hGU hGR hGP hHU hHR hHP)).toFunctor
      (Stack.quotientStackMap (realization C hS φ hGU hGR hGP hHU hHR hHP)).w).IsEquivalence := by
  have : Mono φ.mapArrows.left := inferInstance
  have : Mono φ.mapArrows := (Over.forget S).mono_of_mono_map ‹_›
  exact Stack.isEquivalence_mapBase_quotientStackMap _
    (mono_realization_mapArrows C hS φ hGU hGR hGP hHU hHR hHP)
    (IsOverPoint C hS hGU hGR hGP ((eqToHom e.symm).left.base u))
    (fun g y hy => isOverPoint_map C hS hGU hGR hGP _ g y hy)
    (realization_arrow_lift C hS φ hGU hGR hGP hHU hHR hHP e hφ u hstab)
    q hq

end Stacks.Groupoids.GroupoidScheme.Hom

end
