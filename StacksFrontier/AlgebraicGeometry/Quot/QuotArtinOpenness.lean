module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotArtinAxioms
public import StacksFrontier.Deformation.Artin.FormalObject.SquareZeroTowerObstruction
public import StacksFrontier.Deformation.Artin.Versality.OpennessObstruction
public import StacksFrontier.Deformation.Artin.Obstruction.LiftSituationPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentable
public import StacksFrontier.Deformation.Artin.Versality.OpennessOfVersality
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackSquareZeroEffective
public import StacksFrontier.Deformation.Artin.FormalObject.Realization

/-!
# Towers of square-zero thickenings for a category fibred in sets

Openness of versality (axiom [5]) for `Quot_{F/X/S}` is obtained from Stacks 0CXU, through
`Deformation.Artin.isOpenVersality_of_isSquareZeroTowerEffectiveOnClasses`, whose condition (4)
is the effectivity of towers of square-zero thickenings on lift classes. For the category fibred
in sets `𝒮_F` of a presheaf `F` the lift classes of an object `x` along `Spec A ⟶ Spec C` are the
elements of `F(Spec C)` restricting to the element of `x`; this file proves that identification
and reads the effectivity condition on elements.

## Main definitions

* `AlgebraicGeometry.Space.liftElem`: the element of `F` named by a lift class.

## Main results

* `AlgebraicGeometry.Space.liftElem_injective`, `AlgebraicGeometry.Space.exists_liftElem_eq` and
  `AlgebraicGeometry.Space.liftElem_map`: lift classes of `𝒮_F` are elements of `F`, compatibly
  with pullback.
* `AlgebraicGeometry.Space.isSquareZeroTowerEffectiveOnClasses_fibredCategory`: effectivity of
  square-zero towers on lift classes for `𝒮_F`, from effectivity on elements.

## References

* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
* [Stacks Project, Tag 0CZW](https://stacks.math.columbia.edu/tag/0CZW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Functor

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Lift classes of a category fibred in sets -/

section LiftClasses

open Deformation.Artin

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {A : Type u} [CommRing A]
  {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  (x : (Stack.fibredCategory B S hS F).val.obj)
  (hx : (Stack.fibredCategory B S hS F).val.p.obj x = algebraOver A B S hS toS hA)

/-- The element of `F` named by a lift of `x` along `Spec A ⟶ Spec C`. -/
def liftElemOfFiber (D : AugmentedSiteRing A B S hS toS hA)
    (d : (Under.post (Stack.fibredCategory B S hS F).val.p).Fiber
      (Under.mk (eqToHom hx ≫ D.arrow))) :
    F.obj (op D.siteOver) :=
  Stack.presheafFiberElement B S hS F
    ⟨d.1.right, underFiber_right_obj (Stack.fibredCategory B S hS F).val.p hx D.arrow d⟩

/-- Isomorphic lifts name the same element. -/
theorem liftElemOfFiber_eq_of_iso (D : AugmentedSiteRing A B S hS toS hA)
    {d e : (Under.post (Stack.fibredCategory B S hS F).val.p).Fiber
      (Under.mk (eqToHom hx ≫ D.arrow))} (i : d ≅ e) :
    liftElemOfFiber x hx D d = liftElemOfFiber x hx D e := by
  have hl := underPost_isHomLift_right (Stack.fibredCategory B S hS F).val.p
    (𝟙 (Under.mk (eqToHom hx ≫ D.arrow))) (Fiber.fiberInclusion.map i.hom) inferInstance
  have hl' : (Stack.fibredCategory B S hS F).val.p.IsHomLift (𝟙 D.siteOver)
      (Fiber.fiberInclusion.map i.hom).right := hl
  have h := Stack.presheafFiberElement_map B S hS F (𝟙 D.siteOver)
    ⟨d.1.right, underFiber_right_obj (Stack.fibredCategory B S hS F).val.p hx D.arrow d⟩
    ⟨e.1.right, underFiber_right_obj (Stack.fibredCategory B S hS F).val.p hx D.arrow e⟩
    (Fiber.fiberInclusion.map i.hom).right hl'
  simpa [liftElemOfFiber] using h.symm

/-- The element of `F` named by a lift class of `x`. -/
def liftElem (D : AugmentedSiteRing A B S hS toS hA)
    (z : AugmentedSiteRing.classes (Stack.fibredCategory B S hS F).val.p x hx D) :
    F.obj (op D.siteOver) :=
  @Quotient.lift _ _ (isIsomorphicSetoid _) (liftElemOfFiber x hx D)
    (fun _ _ (h : IsIsomorphic _ _) => liftElemOfFiber_eq_of_iso x hx D h.some) z

/-- The element named by the class of a lift `d` is the element named by `d`. -/
theorem liftElem_mk (D : AugmentedSiteRing A B S hS toS hA)
    (d : (Under.post (Stack.fibredCategory B S hS F).val.p).Fiber
      (Under.mk (eqToHom hx ≫ D.arrow))) :
    liftElem x hx D (Quotient.mk _ d) = liftElemOfFiber x hx D d := rfl

/-- The element named by a lift class restricts to the element named by `x`. -/
theorem map_arrow_liftElem (D : AugmentedSiteRing A B S hS toS hA)
    (z : AugmentedSiteRing.classes (Stack.fibredCategory B S hS F).val.p x hx D) :
    F.map D.arrow.op (liftElem x hx D z) = Stack.presheafFiberElement B S hS F ⟨x, hx⟩ := by
  induction z using Quotient.inductionOn with
  | h d =>
    exact Stack.presheafFiberElement_map B S hS F D.arrow ⟨x, hx⟩
      ⟨d.1.right, underFiber_right_obj (Stack.fibredCategory B S hS F).val.p hx D.arrow d⟩ d.1.hom
      (underFiber_isHomLift _ hx D.arrow d)

/-- **Pullback of lift classes is restriction of elements.** -/
theorem liftElem_map {D E : AugmentedSiteRing A B S hS toS hA} (f : AugmentedSiteRing.Hom D E)
    (z : AugmentedSiteRing.classes (Stack.fibredCategory B S hS F).val.p x hx D) :
    liftElem x hx E (AugmentedSiteRing.map _ x hx
        (Stack.fibredCategory B S hS F).isFiberedInGroupoids f z) =
      F.map f.right.op (liftElem x hx D z) := by
  induction z using Quotient.inductionOn with
  | h d =>
    obtain ⟨e, φ, hφ, -, hmap⟩ := AugmentedSiteRing.representative_map _ x hx
      (Stack.fibredCategory B S hS F).isFiberedInGroupoids f d
    rw [hmap]
    exact (Stack.presheafFiberElement_map B S hS F f.right
      ⟨e.1.right, underFiber_right_obj (Stack.fibredCategory B S hS F).val.p hx E.arrow e⟩
      ⟨d.1.right, underFiber_right_obj (Stack.fibredCategory B S hS F).val.p hx D.arrow d⟩ φ
      hφ.toIsHomLift).symm

/-- Two objects of a fibre of `𝒮_F` naming the same element are equal. -/
theorem fiber_eq_of_presheafFiberElement_eq {V : BigFppfOver B S hS}
    (a b : (Stack.fibredCategory B S hS F).val.p.Fiber V)
    (h : Stack.presheafFiberElement B S hS F a = Stack.presheafFiberElement B S hS F b) :
    a = b := by
  obtain ⟨s, rfl⟩ := Deformation.Artin.exists_eq_fibredCategoryFiberMk a
  obtain ⟨t, rfl⟩ := Deformation.Artin.exists_eq_fibredCategoryFiberMk b
  obtain rfl : s = t := h
  rfl

/-- **A lift class is determined by the element it names.** -/
theorem liftElem_injective (D : AugmentedSiteRing A B S hS toS hA) :
    Function.Injective (liftElem x hx D) := by
  intro z w
  induction z, w using Quotient.inductionOn₂ with
  | h d e =>
    intro h
    apply Quotient.sound
    let p := (Stack.fibredCategory B S hS F).val.p
    have hd := underFiber_right_obj p hx D.arrow d
    have he := underFiber_right_obj p hx D.arrow e
    have hde : d.1.right = e.1.right :=
      congrArg Subtype.val (fiber_eq_of_presheafFiberElement_eq ⟨d.1.right, hd⟩ ⟨e.1.right, he⟩ h)
    have hsub : ∀ (a b : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ D.arrow))),
        Subsingleton (a ⟶ b) := fun a b => ⟨fun φ ψ => by
      apply Subtype.ext
      apply Under.UnderMorphism.ext
      have hφ := underPost_isHomLift_right p (𝟙 (Under.mk (eqToHom hx ≫ D.arrow)))
        (Fiber.fiberInclusion.map φ) inferInstance
      have hψ := underPost_isHomLift_right p (𝟙 (Under.mk (eqToHom hx ≫ D.arrow)))
        (Fiber.fiberInclusion.map ψ) inferInstance
      exact @Stack.hom_eq_of_isHomLift_fibredCategory B S hS F _ _ _ _ (𝟙 D.siteOver) _ _ hφ hψ⟩
    have mk : ∀ (a b : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ D.arrow))),
        a.1.right = b.1.right → (a ⟶ b) := fun a b hab => by
      have ha := underFiber_right_obj p hx D.arrow a
      have hb := underFiber_right_obj p hx D.arrow b
      have hχ : p.IsHomLift (𝟙 D.siteOver) (eqToHom hab) :=
        IsHomLift.of_fac p _ _ ha hb (by simp [eqToHom_map])
      have hla := underFiber_isHomLift p hx D.arrow a
      have hlb := underFiber_isHomLift p hx D.arrow b
      refine underFiberHomMk p hx D.arrow (eqToHom hab) hχ ?_
      have : p.IsHomLift (D.arrow ≫ 𝟙 D.siteOver) (a.1.hom ≫ eqToHom hab) := inferInstance
      rw [Category.comp_id] at this
      exact Stack.hom_eq_of_isHomLift_fibredCategory B S hS D.arrow _ _
    exact ⟨⟨mk d e hde, mk e d hde.symm, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

omit x hx in
/-- **Every element restricting to the element of `x` is named by a lift class**, for `x` given
by an element over `Spec A`. -/
theorem exists_liftElem_eq (s : F.obj (op (algebraOver A B S hS toS hA)))
    (D : AugmentedSiteRing A B S hS toS hA) (t : F.obj (op D.siteOver))
    (ht : F.map D.arrow.op t = s) :
    ∃ z : AugmentedSiteRing.classes (Stack.fibredCategory B S hS F).val.p
        (⟨algebraOver A B S hS toS hA, Discrete.mk s⟩ : (Stack.fibredCategory B S hS F).val.obj)
        rfl D,
      liftElem _ rfl D z = t := by
  let m := Stack.fibredCategoryHomMk B S hS D.arrow ht.symm
  refine ⟨Quotient.mk _ (Deformation.Artin.underFiberObjMk (Stack.fibredCategory B S hS F).val.p rfl
    D.arrow m (Stack.isHomLift_fibredCategoryHomMk B S hS D.arrow ht.symm)), ?_⟩
  exact Stack.presheafFiberElement_eq_of_heq B S hS F
    ⟨⟨D.siteOver, Discrete.mk t⟩, IsHomLift.codomain_eq _ D.arrow m⟩ t HEq.rfl

end LiftClasses

/-! ### Effectivity of square-zero towers for a category fibred in sets -/

section Towers

open Deformation.Artin

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Effectivity of square-zero towers on lift classes, for `𝒮_F`, from the elements of `F`.**
If every compatible family of elements of `F` over the levels `Rₙ` of a square-zero tower comes
from one element over `lim Rₙ`, then the category fibred in sets `𝒮_F` has the effectivity on lift
classes of condition (4) of Stacks 0CXU. -/
theorem isSquareZeroTowerEffectiveOnClasses_fibredCategory
    (h : ∀ (R : ℕ → Type u) [∀ n, CommRing (R n)] (f : ∀ n, R (n + 1) →+* R n)
      (_ : ∀ n, Function.Surjective (f n))
      (_ : ∀ n, RingHom.ker (SquareZeroTower.toBase f n) ^ 2 = ⊥)
      (toS : Spec (.of (R 0)) ⟶ S) (hA : B.Contains (Spec (.of (R 0))))
      (Λ : AugmentedSiteRing (R 0) B S hS toS hA) (β : ∀ n, Λ.ring →+* R n)
      (hβ : ∀ n, (f n).comp (β (n + 1)) = β n) (hβ0 : β 0 = Λ.aug)
      (hR : ∀ n, B.Contains (Spec (.of (R n)))),
      MapsIntoAffineOpen S toS →
      ∀ t : ∀ n, F.obj (op (SquareZeroTower.level f Λ β hβ hβ0 hR n).siteOver),
        (∀ n, F.map (SquareZeroTower.transition f Λ β hβ hβ0 hR n).toHom.right.op (t (n + 1)) =
          t n) →
        ∃ ξ : F.obj (op (SquareZeroTower.limitRing f Λ β hβ hβ0 hR).siteOver),
          ∀ n, F.map (SquareZeroTower.limitProj f Λ β hβ hβ0 hR n).toHom.right.op ξ = t n) :
    IsSquareZeroTowerEffectiveOnClasses B S hS (Stack.fibredCategory B S hS F).val.p
      (Stack.fibredCategory B S hS F).isFiberedInGroupoids := by
  intro R _ f hf hsq toS hA Λ β hβ hβ0 hR hU x hx b hb
  obtain ⟨xb, ⟨s⟩⟩ := x
  change xb = _ at hx
  subst hx
  let t : ∀ n, F.obj (op (SquareZeroTower.level f Λ β hβ hβ0 hR n).siteOver) := fun n =>
    liftElem _ rfl (SquareZeroTower.level f Λ β hβ hβ0 hR n).toAffine (b n)
  have ht : ∀ n, F.map (SquareZeroTower.transition f Λ β hβ hβ0 hR n).toHom.right.op
      (t (n + 1)) = t n := fun n => by
    have e := liftElem_map (⟨algebraOver (R 0) B S hS toS hA, Discrete.mk s⟩ :
      (Stack.fibredCategory B S hS F).val.obj) rfl
      (SquareZeroTower.transition f Λ β hβ hβ0 hR n).toHom (b (n + 1))
    exact e.symm.trans (congrArg _ (hb n))
  obtain ⟨ξ, hξ⟩ := h R f hf hsq toS hA Λ β hβ hβ0 hR hU t ht
  have hξ0 : F.map (SquareZeroTower.limitRing f Λ β hβ hβ0 hR).arrow.op ξ = s := by
    have hw := Under.w (SquareZeroTower.limitProj f Λ β hβ hβ0 hR 0).toHom
    change (SquareZeroTower.level f Λ β hβ hβ0 hR 0).arrow ≫
      (SquareZeroTower.limitProj f Λ β hβ hβ0 hR 0).toHom.right =
        (SquareZeroTower.limitRing f Λ β hβ hβ0 hR).arrow at hw
    rw [← hw, op_comp, Functor.map_comp_apply, hξ 0]
    exact map_arrow_liftElem (⟨algebraOver (R 0) B S hS toS hA, Discrete.mk s⟩ :
      (Stack.fibredCategory B S hS F).val.obj) rfl _ (b 0)
  obtain ⟨z, hz⟩ := exists_liftElem_eq s _ ξ hξ0
  refine ⟨z, fun n => liftElem_injective _ rfl _ ?_⟩
  have e := liftElem_map (⟨algebraOver (R 0) B S hS toS hA, Discrete.mk s⟩ :
    (Stack.fibredCategory B S hS F).val.obj) rfl
    (SquareZeroTower.limitProj f Λ β hβ hβ0 hR n).toHom z
  rwa [hz, hξ n] at e

end Towers

/-! ### Towers of quotients -/

section QuotTowers

open Deformation.Artin

/-- Restriction in a model of the Quot presheaf, over a base with a unique point over every scheme
of the site, is pullback of quotients along the induced morphism of test schemes. -/
theorem QuotSitePresheafModel.map_eq_iff {D : QuotSituation B S hS} (M : QuotSitePresheafModel D)
    (ι : ∀ T : BigFppfOver B S hS, (schemeSpaceFunctor B S hS).obj T ⟶ D.Y)
    [∀ T : BigFppfOver B S hS, Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y)]
    {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (x : M.presheaf.obj (op T))
    (y : M.presheaf.obj (op T')) (K : D.properlySupportedQuotients (D.testOver ι T))
    (K' : D.properlySupportedQuotients (D.testOver ι T'))
    (hx : M.iso.hom.app (op T) (ULift.up x) = D.ofQuot ι T K)
    (hy : M.iso.hom.app (op T') (ULift.up y) = D.ofQuot ι T' K') :
    M.presheaf.map g.op x = y ↔ D.quotientPullback (D.testHom ι g) K.1 = K'.1 := by
  rw [← (M.iso_hom_app_injective (op T')).eq_iff, M.iso_hom_app_map, hx, hy]
  change (D.ofQuot ι T K).baseChange g = _ ↔ _
  rw [D.baseChange_ofQuot]
  exact ⟨fun h => congrArg Subtype.val (D.ofQuot_injective ι T' h),
    fun h => congrArg (D.ofQuot ι T') (Subtype.ext h)⟩

/-- Every section of a model of the Quot presheaf, over a base with a unique point over every
scheme of the site, is a quotient over the test scheme. -/
theorem QuotSitePresheafModel.exists_ofQuot {D : QuotSituation B S hS}
    (M : QuotSitePresheafModel D)
    (ι : ∀ T : BigFppfOver B S hS, (schemeSpaceFunctor B S hS).obj T ⟶ D.Y)
    [∀ T : BigFppfOver B S hS, Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y)]
    {T : BigFppfOver B S hS} (x : M.presheaf.obj (op T)) :
    ∃ K : D.properlySupportedQuotients (D.testOver ι T),
      M.iso.hom.app (op T) (ULift.up x) = D.ofQuot ι T K :=
  (D.ofQuot_surjective ι T _).imp fun _ h => h.symm

/-- Every quotient over the test scheme is a section of a model of the Quot presheaf. -/
theorem QuotSitePresheafModel.exists_of_ofQuot {D : QuotSituation B S hS}
    (M : QuotSitePresheafModel D)
    (ι : ∀ T : BigFppfOver B S hS, (schemeSpaceFunctor B S hS).obj T ⟶ D.Y)
    {T : BigFppfOver B S hS} (K : D.properlySupportedQuotients (D.testOver ι T)) :
    ∃ x : M.presheaf.obj (op T), M.iso.hom.app (op T) (ULift.up x) = D.ofQuot ι T K :=
  ⟨(M.iso.inv.app (op T) (D.ofQuot ι T K)).down, by
    change (M.iso.inv ≫ M.iso.hom).app (op T) _ = _
    rw [Iso.inv_hom_id]
    rfl⟩

/-- **Effectivity of towers for a model of the Quot presheaf, from towers of quotients.** Over a
base with a unique point over every scheme of the site, if every compatible family of quotients
over the levels `Spec Rₙ` of a square-zero tower is the family of pullbacks of one quotient over
`Spec (lim Rₙ)`, then compatible families of sections of the model over the levels come from one
section over the limit: the element-level effectivity consumed by
`AlgebraicGeometry.Space.isSquareZeroTowerEffectiveOnClasses_fibredCategory`. -/
theorem QuotSitePresheafModel.towerEffective_of_quotients {D : QuotSituation B S hS}
    (M : QuotSitePresheafModel D)
    (ι : ∀ T : BigFppfOver B S hS, (schemeSpaceFunctor B S hS).obj T ⟶ D.Y)
    [∀ T : BigFppfOver B S hS, Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y)]
    {R : ℕ → Type u} [∀ n, CommRing (R n)] {f : ∀ n, R (n + 1) →+* R n}
    {toS : Spec (.of (R 0)) ⟶ S} {hA : B.Contains (Spec (.of (R 0)))}
    {Λ : AugmentedSiteRing (R 0) B S hS toS hA} {β : ∀ n, Λ.ring →+* R n}
    {hβ : ∀ n, (f n).comp (β (n + 1)) = β n} {hβ0 : β 0 = Λ.aug}
    {hR : ∀ n, B.Contains (Spec (.of (R n)))}
    (hquot : ∀ K : ∀ n, D.properlySupportedQuotients
        (D.testOver ι (SquareZeroTower.level f Λ β hβ hβ0 hR n).siteOver),
      (∀ n, D.quotientPullback
          (D.testHom ι (SquareZeroTower.transition f Λ β hβ hβ0 hR n).toHom.right)
          (K (n + 1)).1 = (K n).1) →
        ∃ Kl : D.properlySupportedQuotients
            (D.testOver ι (SquareZeroTower.limitRing f Λ β hβ hβ0 hR).siteOver),
          ∀ n, D.quotientPullback
            (D.testHom ι (SquareZeroTower.limitProj f Λ β hβ hβ0 hR n).toHom.right) Kl.1 = (K n).1)
    (t : ∀ n, M.presheaf.obj (op (SquareZeroTower.level f Λ β hβ hβ0 hR n).siteOver))
    (ht : ∀ n, M.presheaf.map (SquareZeroTower.transition f Λ β hβ hβ0 hR n).toHom.right.op
      (t (n + 1)) = t n) :
    ∃ ξ : M.presheaf.obj (op (SquareZeroTower.limitRing f Λ β hβ hβ0 hR).siteOver),
      ∀ n, M.presheaf.map (SquareZeroTower.limitProj f Λ β hβ hβ0 hR n).toHom.right.op ξ = t n := by
  choose K hK using fun n => M.exists_ofQuot ι (t n)
  obtain ⟨Kl, hKl⟩ := hquot K fun n => (M.map_eq_iff ι _ _ _ _ _ (hK (n + 1)) (hK n)).1 (ht n)
  obtain ⟨ξ, hξ⟩ := M.exists_of_ofQuot ι Kl
  exact ⟨ξ, fun n => (M.map_eq_iff ι _ _ _ _ _ hξ (hK n)).2 (hKl n)⟩

end QuotTowers

/-! ### Limit preservation from its surjectivity half -/

/-- **A model of the Quot presheaf is limit preserving as soon as sections over a limit come from
a stage** (axiom [1]), for `F` of finite type and a base with at most one point over every scheme
of the site: the injectivity half is
`AlgebraicGeometry.Space.QuotSitePresheafModel.exists_stage_eq`. -/
theorem QuotSitePresheafModel.limitPreserving_of_exists_stage {D : QuotSituation B S hS}
    (M : QuotSitePresheafModel D)
    (hY : ∀ a : BigFppfOver B S hS, Subsingleton (D.Y.1.obj (op a)))
    (hFt : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hsurj : ∀ (I : Type u) [Category.{u} I] [IsCofiltered I] (E : I ⥤ BigFppfOver B S hS)
      (c : Cone E), IsLimit ((BigFppfOver.toScheme B S hS).mapCone c) →
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i))) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) →
      ∀ x : M.presheaf.obj (op c.pt), ∃ (i : I) (y : M.presheaf.obj (op (E.obj i))),
        M.presheaf.map (c.π.app i).op y = x) :
    AlgebraicGeometry.LimitPreserving.{u, u, u, u} (BigFppfOver.toScheme B S hS) M.presheaf := by
  intro I _ _ E c hc haff hpt
  refine ⟨Types.FilteredColimit.isColimitOf' _ _ (fun x => ?_) (fun i y z h => ?_)⟩
  · obtain ⟨i, y, hy⟩ := hsurj I E c hc haff hpt x
    exact ⟨op i, y, hy.symm⟩
  · obtain ⟨j, g, hg⟩ := M.exists_stage_eq hY hFt E c hc haff i.unop y z h
    exact ⟨op j, g.op, hg⟩

/-! ### Sections of an affine scheme over the limit of a tower -/

section AffineTower

open Deformation.Artin

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] {f : ∀ n, R (n + 1) →+* R n}
  {toS : Spec (.of (R 0)) ⟶ S} {hA : B.Contains (Spec (.of (R 0)))}
  {Λ : AugmentedSiteRing (R 0) B S hS toS hA} {β : ∀ n, Λ.ring →+* R n}
  {hβ : ∀ n, (f n).comp (β (n + 1)) = β n} {hβ0 : β 0 = Λ.aug}
  {hR : ∀ n, B.Contains (Spec (.of (R n)))}

/-- The projections of the limit of a tower are compatible with its transitions, as morphisms of
the site. -/
theorem transition_right_comp_limitProj_right (n : ℕ) :
    (SquareZeroTower.transition f Λ β hβ hβ0 hR n).toHom.right ≫
        (SquareZeroTower.limitProj f Λ β hβ hβ0 hR (n + 1)).toHom.right =
      (SquareZeroTower.limitProj f Λ β hβ hβ0 hR n).toHom.right := by
  have h : (SquareZeroTower.transition f Λ β hβ hβ0 hR n).comp
      (SquareZeroTower.limitProj f Λ β hβ hβ0 hR (n + 1)) =
        SquareZeroTower.limitProj f Λ β hβ hβ0 hR n :=
    BasedSiteRing.RingMap.ext (RingHom.ext fun r => r.2 n)
  rw [← h, BasedSiteRing.RingMap.toHom_comp (SquareZeroTower.transition f Λ β hβ hβ0 hR n)
    (SquareZeroTower.limitProj f Λ β hβ hβ0 hR (n + 1))]
  rfl

/-- A section of the schemes underlying `p : V ⟶ P` lifts to a section of `p` in the site. -/
private theorem exists_hom_of_scheme_section {V P : BigFppfOver B S hS} (p : V ⟶ P)
    (s' : (BigFppfOver.toScheme B S hS).obj P ⟶ (BigFppfOver.toScheme B S hS).obj V)
    (hs' : s' ≫ (BigFppfOver.toScheme B S hS).map p = 𝟙 _) :
    ∃ s : P ⟶ V, s ≫ p = 𝟙 _ ∧ (BigFppfOver.toScheme B S hS).map s = s' := by
  let sB : P.left ⟶ V.left := ObjectProperty.homMk s'
  have hw : sB ≫ V.hom = P.hom := by
    apply ObjectProperty.hom_ext
    change s' ≫ B.inclusion.map V.hom = _
    rw [← Over.w p, Functor.map_comp, ← Category.assoc]
    change (s' ≫ (BigFppfOver.toScheme B S hS).map p) ≫ _ = _
    rw [hs']
    exact Category.id_comp _
  refine ⟨Over.homMk sB hw, ?_, rfl⟩
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact hs'

/-- The point of a presheaf affine over `yoneda P` given by compatible points over a family
`T n` of objects over `P`, provided affine objects over `P` admit the corresponding sections. The
compatibilities are indexed by the edges `tr e : T (src e) ⟶ T (tgt e)`. -/
private theorem exists_point_of_exists_section {ε : Type} {src tgt : ε → ℕ}
    {T : ℕ → BigFppfOver B S hS} {P : BigFppfOver B S hS}
    (hP : IsAffine ((BigFppfOver.toScheme B S hS).obj P))
    (l : ∀ n, T n ⟶ P) (tr : ∀ e, T (src e) ⟶ T (tgt e))
    (hlc : ∀ e, tr e ≫ l (tgt e) = l (src e))
    (hsec : ∀ (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
      (q : V ⟶ P) (g : ∀ n, T n ⟶ V), (∀ n, g n ≫ q = l n) →
      (∀ e, tr e ≫ g (tgt e) = g (src e)) → ∃ s : P ⟶ V, s ≫ q = 𝟙 _ ∧ ∀ n, l n ≫ s = g n)
    {H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : H ⟶ yoneda.obj P) (hp : IsAffineHom B S hS p)
    (x : ∀ n, yoneda.obj (T n) ⟶ H) (hx : ∀ n, x n ≫ p = yoneda.map (l n))
    (hc : ∀ e, yoneda.map (tr e) ≫ x (tgt e) = x (src e)) :
    ∃ y : yoneda.obj P ⟶ H, y ≫ p = 𝟙 _ ∧ ∀ n, yoneda.map (l n) ≫ y = x n := by
  obtain ⟨W, pW, q, hpb⟩ := hp ⟨P, hP⟩ (𝟙 _)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj W)) :=
    W.property
  let g : ∀ n, T n ⟶ (BigAffineFppf.inclusion B S hS).obj W := fun n =>
    yoneda.preimage (hpb.lift (x n) (yoneda.map (l n)) (by rw [hx n, Category.comp_id]))
  have hg₁ : ∀ n, yoneda.map (g n) ≫ pW = x n := fun n => by
    simp only [g, Functor.map_preimage, IsPullback.lift_fst]
  have hg₂ : ∀ n, g n ≫ q = l n := fun n => by
    apply yoneda.map_injective
    simp only [g, Functor.map_comp, Functor.map_preimage, IsPullback.lift_snd]
  have hgc : ∀ e, tr e ≫ g (tgt e) = g (src e) := fun e => by
    apply yoneda.map_injective
    apply hpb.hom_ext
    · rw [Functor.map_comp, Category.assoc, hg₁, hg₁, hc]
    · rw [Functor.map_comp, Category.assoc, ← Functor.map_comp, hg₂, ← Functor.map_comp,
        ← Functor.map_comp, hg₂, hlc]
  obtain ⟨sec, hsec, hsecn⟩ := hsec _ q g hg₂ hgc
  refine ⟨yoneda.map sec ≫ pW, ?_, fun n => ?_⟩
  · rw [Category.assoc, hpb.w, Category.comp_id, ← Functor.map_comp, hsec,
      CategoryTheory.Functor.map_id]
  · rw [← Category.assoc, ← Functor.map_comp, hsecn, hg₁]

/-- A morphism of the site compatible with the structure maps to `P`, as a morphism of test
schemes over `P`. -/
private def testHomMk {X Y P : BigFppfOver B S hS} (f : X ⟶ Y) (a : X ⟶ P) (b : Y ⟶ P)
    (h : f ≫ b = a) : CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map a) ⟶
      CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map b) :=
  CostructuredArrow.homMk f (by
    change (schemeSpaceFunctor B S hS).map _ ≫ (schemeSpaceFunctor B S hS).map _ = _
    rw [← Functor.map_comp, h]
    rfl)

/-- A functor on the test schemes over `P` which is an algebraic space affine over it takes the
family `T n` to a limit, provided affine objects over `P` admit the sections of
`AlgebraicGeometry.Space.exists_point_of_exists_section`. -/
private theorem exists_eq_of_exists_section {ε : Type} {src tgt : ε → ℕ}
    {T : ℕ → BigFppfOver B S hS} {P : BigFppfOver B S hS}
    (hP : IsAffine ((BigFppfOver.toScheme B S hS).obj P))
    (l : ∀ n, T n ⟶ P) (tr : ∀ e, T (src e) ⟶ T (tgt e))
    (hlc : ∀ e, tr e ≫ l (tgt e) = l (src e))
    (hsec : ∀ (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
      (q : V ⟶ P) (g : ∀ n, T n ⟶ V), (∀ n, g n ≫ q = l n) →
      (∀ e, tr e ≫ g (tgt e) = g (src e)) → ∃ s : P ⟶ V, s ≫ q = 𝟙 _ ∧ ∀ n, l n ≫ s = g n)
    {Rf : (SchemesOver (schemeSpace P))ᵒᵖ ⥤ Type (u + 1)}
    (hRf : IsAffineAlgebraicSpaceOver _ Rf)
    (a : ∀ n, Rf.obj (op (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map (l n)))))
    (ha : ∀ e, Rf.map (testHomMk (tr e) (l (src e)) (l (tgt e)) (hlc e)).op (a (tgt e)) =
      a (src e)) :
    ∃ v : Rf.obj (op (CostructuredArrow.mk (𝟙 (schemeSpace P)))),
      ∀ n, Rf.map (CostructuredArrow.homMk (l n) (Category.comp_id _)).op v = a n := by
  obtain ⟨H, p, hp, ⟨c⟩⟩ := hRf
  let y : ∀ n, spacePointsOverObj p
      (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map (l n))) :=
    fun n => (c.inv.app _ (a n)).down
  have hcu : ∀ n, c.hom.app _ (ULift.up (y n)) = a n := fun n => by
    change (c.inv ≫ c.hom).app _ (a n) = a n
    rw [Iso.inv_hom_id]
    rfl
  let x : ∀ n, yoneda.obj (T n) ⟶ H.1 := fun n => yonedaEquiv.symm (y n).1
  have hx : ∀ n, x n ≫ p.hom = yoneda.map (l n) := fun n => by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact (y n).2
  have hnat : ∀ {U W} (g : U ⟶ W) (z : spacePointsOverObj p W),
      Rf.map g.op (c.hom.app _ (ULift.up z)) =
        c.hom.app _ (ULift.up ((spacePointsOver p).map g.op z)) := fun g z =>
    (types_congr_hom (c.hom.naturality g.op) (ULift.up z)).symm
  have hxc : ∀ e, yoneda.map (tr e) ≫ x (tgt e) = x (src e) := fun e => by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact congrArg Subtype.val (congrArg ULift.down ((c.app _).toEquiv.injective
      ((hnat (testHomMk (tr e) (l (src e)) (l (tgt e)) (hlc e)) (y (tgt e))).symm.trans
        ((congrArg (Rf.map (testHomMk (tr e) (l (src e)) (l (tgt e)) (hlc e)).op)
          (hcu (tgt e))).trans ((ha e).trans (hcu (src e)).symm)))))
  obtain ⟨w, hw, hwn⟩ := exists_point_of_exists_section hP l tr hlc hsec p.hom hp x hx hxc
  let z : spacePointsOverObj p (CostructuredArrow.mk (𝟙 (schemeSpace P))) :=
    ⟨yonedaEquiv w, by
      rw [← yonedaEquiv_comp]
      exact congrArg yonedaEquiv hw⟩
  refine ⟨c.hom.app _ (ULift.up z), fun n => ?_⟩
  refine (hnat (U := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map (l n)))
    (W := CostructuredArrow.mk (𝟙 (schemeSpace P)))
    (CostructuredArrow.homMk (l n) (Category.comp_id _)) z).trans ?_
  refine Eq.trans ?_ (hcu n)
  congr 2
  apply Subtype.ext
  change H.1.map _ (yonedaEquiv w) = (y n).1
  rw [yonedaEquiv_naturality]
  change yonedaEquiv (yoneda.map (l n) ≫ w) = _
  rw [hwn]
  exact Equiv.apply_symm_apply _ _

/-- **A compatible family of points of an affine scheme over the levels of a tower comes from a
section over the limit.** Let `p : V ⟶ Spec (lim Rₙ)` be a morphism of the site with `V` affine,
and let `gₙ : Spec Rₙ ⟶ V` be compatible with the transitions and lie over the projections
`Spec Rₙ ⟶ Spec (lim Rₙ)`. Then there is a section `s` of `p` with `gₙ` the composite of the
projection and `s`: maps into an affine scheme are ring maps out of its ring of functions, and
compatible ring maps into the `Rₙ` are a ring map into `lim Rₙ`. -/
theorem exists_section_of_compatible {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (p : V ⟶ (SquareZeroTower.limitRing f Λ β hβ hβ0 hR).siteOver)
    (g : ∀ n, (SquareZeroTower.level f Λ β hβ hβ0 hR n).siteOver ⟶ V)
    (hg : ∀ n, g n ≫ p = (SquareZeroTower.limitProj f Λ β hβ hβ0 hR n).toHom.right)
    (hc : ∀ n, (SquareZeroTower.transition f Λ β hβ hβ0 hR n).toHom.right ≫ g (n + 1) = g n) :
    ∃ s : (SquareZeroTower.limitRing f Λ β hβ hβ0 hR).siteOver ⟶ V, s ≫ p = 𝟙 _ ∧
      ∀ n, (SquareZeroTower.limitProj f Λ β hβ hβ0 hR n).toHom.right ≫ s = g n := by
  let V' := (BigFppfOver.toScheme B S hS).obj V
  let tg : ∀ n, Spec (.of (R n)) ⟶ V' := fun n => (BigFppfOver.toScheme B S hS).map (g n)
  let ψ : ∀ n, Γ(V', ⊤) ⟶ CommRingCat.of (R n) := fun n =>
    Spec.preimage (tg n ≫ V'.isoSpec.hom)
  have hψ : ∀ n, Spec.map (ψ n) = tg n ≫ V'.isoSpec.hom := fun n => Spec.map_preimage _
  have hcancel : ∀ {Y : Scheme.{u}} (a : Y ⟶ V'), (a ≫ V'.isoSpec.hom) ≫ V'.isoSpec.inv = a :=
    fun a => by simp
  have hcancel2 : ∀ {Y Z : Scheme.{u}} (a : Y ⟶ V') (m : V' ⟶ Z),
      (a ≫ V'.isoSpec.hom) ≫ V'.isoSpec.inv ≫ m = a ≫ m := fun a m => by simp
  have htr : ∀ n, Spec.map (CommRingCat.ofHom (f n)) ≫ tg (n + 1) = tg n := fun n =>
    (Functor.map_comp _ _ _).symm.trans (congrArg (BigFppfOver.toScheme B S hS).map (hc n))
  have hcomp : ∀ n, ψ (n + 1) ≫ CommRingCat.ofHom (f n) = ψ n := fun n => by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, hψ, ← Category.assoc, htr]
  let Ψ : Γ(V', ⊤) →+* SquareZeroTower.limit f :=
    (RingHom.pi fun n => (ψ n).hom).codRestrict (SquareZeroTower.limit f) fun x n =>
      congrArg (fun φ => φ.hom x) (hcomp n)
  let s' : Spec (.of (SquareZeroTower.limit f)) ⟶ V' :=
    Spec.map (CommRingCat.ofHom Ψ) ≫ V'.isoSpec.inv
  have hproj : ∀ n, Spec.map (CommRingCat.ofHom
      (SquareZeroTower.limitProj f Λ β hβ hβ0 hR n).hom) ≫ s' = tg n := fun n => by
    have e : CommRingCat.ofHom Ψ ≫ CommRingCat.ofHom
        (SquareZeroTower.limitProj f Λ β hβ hβ0 hR n).hom = ψ n := by
      ext x
      rfl
    have h1 := Spec.map_comp (CommRingCat.ofHom Ψ) (CommRingCat.ofHom
      (SquareZeroTower.limitProj f Λ β hβ hβ0 hR n).hom)
    rw [e] at h1
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ V'.isoSpec.inv) (h1.symm.trans (hψ n)))).trans (hcancel (tg n))
  let π : CommRingCat.of (SquareZeroTower.limit f) ⟶ Γ(V', ⊤) :=
    Spec.preimage (V'.isoSpec.inv ≫ (BigFppfOver.toScheme B S hS).map p)
  have hπ : Spec.map π = V'.isoSpec.inv ≫ (BigFppfOver.toScheme B S hS).map p :=
    Spec.map_preimage _
  have hπψ : ∀ n, π ≫ ψ n = CommRingCat.ofHom (SquareZeroTower.limitProj f Λ β hβ hβ0 hR n).hom :=
    fun n => by
      apply Spec.map_injective
      rw [Spec.map_comp, hψ, hπ]
      exact (hcancel2 (tg n) _).trans ((Functor.map_comp _ _ _).symm.trans
        (congrArg (BigFppfOver.toScheme B S hS).map (hg n)))
  have hπΨ : π ≫ CommRingCat.ofHom Ψ = 𝟙 _ := by
    ext x n
    exact congrArg (fun φ => φ.hom x) (hπψ n)
  have hsec' : s' ≫ (BigFppfOver.toScheme B S hS).map p = 𝟙 _ :=
    (Category.assoc _ _ _).trans ((congrArg (Spec.map (CommRingCat.ofHom Ψ) ≫ ·) hπ.symm).trans
      ((Spec.map_comp _ _).symm.trans ((congrArg Spec.map hπΨ).trans (Spec.map_id _))))
  obtain ⟨s, hsp, hs⟩ := exists_hom_of_scheme_section p s' hsec'
  exact ⟨s, hsp, fun n => (BigFppfOver.toScheme B S hS).map_injective
    (by rw [Functor.map_comp, hs]; exact hproj n)⟩

/-- **A compatible family of points over the levels of a tower of a presheaf affine over the
limit comes from a section over the limit.** Let `p : H ⟶ h_{Spec (lim Rₙ)}` be affine (Stacks
03WF) and `xₙ : h_{Spec Rₙ} ⟶ H` compatible with the transitions and lying over the projections.
Then there is a section `y` of `p` restricting to every `xₙ`: the base change of `p` to the affine
scheme `Spec (lim Rₙ)` itself is an affine scheme `W`, and
`AlgebraicGeometry.Space.exists_section_of_compatible` applies to `W`. -/
theorem exists_point_of_compatible {H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : H ⟶ yoneda.obj (SquareZeroTower.limitRing f Λ β hβ hβ0 hR).siteOver)
    (hp : IsAffineHom B S hS p)
    (x : ∀ n, yoneda.obj (SquareZeroTower.level f Λ β hβ hβ0 hR n).siteOver ⟶ H)
    (hx : ∀ n, x n ≫ p = yoneda.map (SquareZeroTower.limitProj f Λ β hβ hβ0 hR n).toHom.right)
    (hc : ∀ n, yoneda.map (SquareZeroTower.transition f Λ β hβ hβ0 hR n).toHom.right ≫ x (n + 1) =
      x n) :
    ∃ y : yoneda.obj (SquareZeroTower.limitRing f Λ β hβ hβ0 hR).siteOver ⟶ H, y ≫ p = 𝟙 _ ∧
      ∀ n, yoneda.map (SquareZeroTower.limitProj f Λ β hβ hβ0 hR n).toHom.right ≫ y = x n := by
  exact exists_point_of_exists_section
    (T := fun n => (SquareZeroTower.level f Λ β hβ hβ0 hR n).siteOver)
    (l := fun n => (SquareZeroTower.limitProj f Λ β hβ hβ0 hR n).toHom.right)
    (src := id) (tgt := (· + 1)) (inferInstanceAs (IsAffine (Spec _)))
    (tr := fun n => (SquareZeroTower.transition f Λ β hβ hβ0 hR n).toHom.right)
    transition_right_comp_limitProj_right
    (fun V _ q g hg hgc => exists_section_of_compatible q g hg hgc) p hp x hx hc

/-- The level `Spec Rₙ` of a tower as a test scheme over the limit `Spec (lim Rₙ)`. -/
abbrev levelOverLimit (n : ℕ) :
    SchemesOver (schemeSpace (SquareZeroTower.limitRing f Λ β hβ hβ0 hR).siteOver) :=
  CostructuredArrow.mk
    ((schemeSpaceFunctor B S hS).map (SquareZeroTower.limitProj f Λ β hβ hβ0 hR n).toHom.right)

/-- The limit `Spec (lim Rₙ)` as a test scheme over itself. -/
abbrev limitOverLimit :
    SchemesOver (schemeSpace (SquareZeroTower.limitRing f Λ β hβ hβ0 hR).siteOver) :=
  CostructuredArrow.mk (𝟙 _)

/-- The transition `Spec Rₙ ⟶ Spec Rₙ₊₁` as a morphism of test schemes over the limit. -/
def levelOverLimitTransition (n : ℕ) :
    levelOverLimit (f := f) (Λ := Λ) (hβ := hβ) (hβ0 := hβ0) (hR := hR) n ⟶
      levelOverLimit (f := f) (Λ := Λ) (hβ := hβ) (hβ0 := hβ0) (hR := hR) (n + 1) :=
  CostructuredArrow.homMk (SquareZeroTower.transition f Λ β hβ hβ0 hR n).toHom.right (by
    change (schemeSpaceFunctor B S hS).map _ ≫ (schemeSpaceFunctor B S hS).map _ = _
    rw [← Functor.map_comp, transition_right_comp_limitProj_right]
    rfl)

/-- The projection `Spec Rₙ ⟶ Spec (lim Rₙ)` as a morphism of test schemes over the limit. -/
def levelOverLimitProj (n : ℕ) :
    levelOverLimit (f := f) (Λ := Λ) (hβ := hβ) (hβ0 := hβ0) (hR := hR) n ⟶
      limitOverLimit (f := f) (Λ := Λ) (hβ := hβ) (hβ0 := hβ0) (hR := hR) :=
  CostructuredArrow.homMk (SquareZeroTower.limitProj f Λ β hβ hβ0 hR n).toHom.right
    (Category.comp_id _)

/-- **A functor on the test schemes over the limit of a tower which is an algebraic space affine
over it takes the limit to a limit.** If `R` is the universe lift of the points of an algebraic
space affine over `Spec (lim Rₙ)`, a compatible family of elements of `R` over the levels comes
from an element over the limit. -/
theorem exists_eq_of_isAffineAlgebraicSpaceOver
    {Rf : (SchemesOver (schemeSpace (SquareZeroTower.limitRing f Λ β hβ hβ0 hR).siteOver))ᵒᵖ ⥤
      Type (u + 1)}
    (hRf : IsAffineAlgebraicSpaceOver _ Rf)
    (u : ∀ n, Rf.obj (op (levelOverLimit (f := f) (Λ := Λ) (hβ := hβ) (hβ0 := hβ0) (hR := hR) n)))
    (hu : ∀ n, Rf.map (levelOverLimitTransition n).op (u (n + 1)) = u n) :
    ∃ v : Rf.obj (op (limitOverLimit (f := f) (Λ := Λ) (hβ := hβ) (hβ0 := hβ0) (hR := hR))),
      ∀ n, Rf.map (levelOverLimitProj n).op v = u n := by
  exact exists_eq_of_exists_section
    (T := fun n => (SquareZeroTower.level f Λ β hβ hβ0 hR n).siteOver)
    (l := fun n => (SquareZeroTower.limitProj f Λ β hβ hβ0 hR n).toHom.right)
    (src := id) (tgt := (· + 1)) (inferInstanceAs (IsAffine (Spec _)))
    (tr := fun n => (SquareZeroTower.transition f Λ β hβ hβ0 hR n).toHom.right)
    transition_right_comp_limitProj_right
    (fun V _ q g hg hgc => exists_section_of_compatible q g hg hgc) hRf u hu

end AffineTower

/-! ### Effective systems of a category fibred in sets -/

section EffectiveSystems

open Deformation.Artin

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A system of objects of `𝒮_F` over a cocone is effective as soon as its elements come from one
element over the vertex.** -/
theorem isEffectiveSystem_fibredCategory {J : Type*} [Category J]
    (ξ : J ⥤ (Stack.fibredCategory B S hS F).val.obj)
    (c : Cocone (ξ ⋙ (Stack.fibredCategory B S hS F).val.p))
    (t : F.obj (op c.pt))
    (ht : ∀ j, F.map (c.ι.app j).op t = Stack.presheafFiberElement B S hS F ⟨ξ.obj j, rfl⟩) :
    IsEffectiveSystem (Stack.fibredCategory B S hS F).val.p ξ c := by
  let ι : ∀ j, ξ.obj j ⟶ (⟨c.pt, Discrete.mk t⟩ : (Stack.fibredCategory B S hS F).val.obj) :=
    fun j => Stack.fibredCategoryHomMk B S hS (V := (ξ.obj j).base) (c.ι.app j) (ht j).symm
  refine ⟨⟨⟨c.pt, Discrete.mk t⟩, { app := ι, naturality := fun j j' g => ?_ }⟩, ?_⟩
  · refine Deformation.Artin.fibredCategory_hom_ext _ _ ?_
    change (ξ.map g).base ≫ c.ι.app j' = c.ι.app j ≫ 𝟙 _
    rw [Category.comp_id]
    exact c.w g
  · obtain ⟨pt, cι⟩ := c
    rfl

/-- **Effectivity of square-zero towers for `𝒮_F`, from the elements of `F`.** If, for every
tower of square-zero thickenings of affine schemes with its limit cocone as in
`Deformation.Artin.IsSquareZeroEffective`, compatible elements of `F` over the members come from
one element over the vertex, then `𝒮_F` satisfies `Deformation.Artin.IsSquareZeroEffective`. -/
theorem isSquareZeroEffective_fibredCategory
    (h : ∀ (Λ : Type u) [CommRing Λ] (chart : Spec (.of Λ) ⟶ S)
      [AlgebraicGeometry.IsOpenImmersion chart]
      (R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ) (cR : Cone R) (_ : IsLimit cR)
      (_ : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
      (_ : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), (RingHom.ker (R.map f).hom.toRingHom) ^ 2 = ⊥)
      (T : ℕ ⥤ BigFppfOver B S hS) (c : Cocone T)
      (e : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).obj (T.obj n) ≅ Spec (.of (R.obj (.op n))))
      (eLimit : (BigFppfOver.toScheme B S hS).obj c.pt ≅ Spec (.of cR.pt)),
      (∀ {i j : ℕ} (f : i ⟶ j),
        (BigFppfOver.toScheme B S hS).map (T.map f) ≫ (e j).hom =
          (e i).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (R.map f.op).hom.toRingHom).op) →
      (∀ n : ℕ, (BigFppfOver.toScheme B S hS).map (c.ι.app n) ≫ eLimit.hom =
        (e n).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op) →
      (eLimit.inv ≫ B.inclusion.map c.pt.hom =
        Scheme.Spec.map (CommRingCat.ofHom (algebraMap Λ cR.pt)).op ≫ chart) →
      ∀ t : ∀ n, F.obj (op (T.obj n)),
        (∀ n, F.map (T.map (homOfLE (n.le_add_right 1))).op (t (n + 1)) = t n) →
        ∃ τ : F.obj (op c.pt), ∀ n, F.map (c.ι.app n).op τ = t n) :
    IsSquareZeroEffective B S hS (Stack.fibredCategory B S hS F).val.p
      (Stack.fibredCategory B S hS F).isFiberedInGroupoids := by
  intro Λ _ chart _ R cR hcR hsurj hsq ξ c e eLimit he heL hch
  let t : ∀ n, F.obj (op ((ξ ⋙ (Stack.fibredCategory B S hS F).val.p).obj n)) := fun n =>
    Stack.presheafFiberElement B S hS F ⟨ξ.obj n, rfl⟩
  have ht : ∀ n, F.map ((ξ ⋙ (Stack.fibredCategory B S hS F).val.p).map
      (homOfLE (n.le_add_right 1))).op (t (n + 1)) = t n := fun n =>
    Stack.presheafFiberElement_map B S hS F _ ⟨ξ.obj n, rfl⟩ ⟨ξ.obj (n + 1), rfl⟩
      (ξ.map (homOfLE (n.le_add_right 1))) (IsHomLift.map _ _)
  obtain ⟨τ, hτ⟩ := h Λ chart R cR hcR hsurj hsq _ c e eLimit he heL hch t ht
  exact isEffectiveSystem_fibredCategory ξ c τ hτ

end EffectiveSystems

/-! ### Maps from the spectrum of a limit into an affine scheme -/

section SpecLimit

/-- **Compatible maps from the spectra of an inverse system of rings into an affine scheme are
induced by exactly one map from the spectrum of the limit.** -/
theorem existsUnique_spec_limit_hom_of_isAffine {A : ℕᵒᵖ ⥤ CommRingCat.{u}} {cA : Cone A}
    (hcA : IsLimit cA) {V : Scheme.{u}} [IsAffine V] (t : ∀ n, Spec (A.obj (op n)) ⟶ V)
    (ht : ∀ {i j : ℕ} (f : i ⟶ j), Spec.map (A.map f.op) ≫ t j = t i) :
    ∃! τ : Spec cA.pt ⟶ V, ∀ n, Spec.map (cA.π.app (op n)) ≫ τ = t n := by
  let ψ : ∀ n, Γ(V, ⊤) ⟶ A.obj (op n) := fun n => Spec.preimage (t n ≫ V.isoSpec.hom)
  have hψ : ∀ n, Spec.map (ψ n) = t n ≫ V.isoSpec.hom := fun n => Spec.map_preimage _
  let cV : Cone A :=
    { pt := Γ(V, ⊤)
      π := { app := fun n => ψ n.unop
             naturality := fun i j f => by
               apply Spec.map_injective
               simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
                 Spec.map_comp, hψ]
               rw [← Category.assoc]
               exact congrArg (· ≫ V.isoSpec.hom) (ht f.unop).symm } }
  refine ⟨Spec.map (hcA.lift cV) ≫ V.isoSpec.inv, fun n => ?_, fun τ hτ => ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, hcA.fac cV (op n)]
    change Spec.map (ψ n) ≫ _ = _
    rw [hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · have hΦ := Spec.map_preimage (τ ≫ V.isoSpec.hom)
    have heq : Spec.preimage (τ ≫ V.isoSpec.hom) = hcA.lift cV := by
      refine hcA.hom_ext fun n => ?_
      rw [hcA.fac cV n]
      apply Spec.map_injective
      rw [Spec.map_comp, hΦ, hψ, ← Category.assoc, hτ n.unop]
    rw [← heq, hΦ, Category.assoc, Iso.hom_inv_id, Category.comp_id]


variable {Λ : Type u} [CommRing Λ] {R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ} {cR : Cone R}
  (hcR : IsLimit cR) {T : ℕ ⥤ BigFppfOver B S hS} {c : Cocone T}
  {e : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).obj (T.obj n) ≅ Spec (.of (R.obj (.op n)))}
  {eLimit : (BigFppfOver.toScheme B S hS).obj c.pt ≅ Spec (.of cR.pt)}
  (he : ∀ {i j : ℕ} (f : i ⟶ j),
    (BigFppfOver.toScheme B S hS).map (T.map f) ≫ (e j).hom =
      (e i).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (R.map f.op).hom.toRingHom).op)
  (heL : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).map (c.ι.app n) ≫ eLimit.hom =
    (e n).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op)

include hcR he heL in
/-- **A compatible family of points of an affine scheme over the members of a tower of spectra
comes from a section over its limit.** Let `c` be a cocone over a tower `Tₙ` of schemes of the
site, identified with `Spec Rₙ` and its vertex with `Spec (lim Rₙ)`; let `p : V ⟶ c.pt` with `V`
affine and `gₙ : Tₙ ⟶ V` compatible maps over the legs of `c`. Then `p` has a section restricting
to every `gₙ`. -/
theorem exists_section_of_cocone {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (p : V ⟶ c.pt) (g : ∀ n, T.obj n ⟶ V)
    (hg : ∀ n, g n ≫ p = c.ι.app n) (hc : ∀ {i j : ℕ} (f : i ⟶ j), T.map f ≫ g j = g i) :
    ∃ s : c.pt ⟶ V, s ≫ p = 𝟙 _ ∧ ∀ n, c.ι.app n ≫ s = g n := by
  let Φ := BigFppfOver.toScheme B S hS
  let A : ℕᵒᵖ ⥤ CommRingCat.{u} := R ⋙ forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}
  have hA := CommAlgCat.isLimitForget₂CommRingCat hcR
  let t : ∀ n, Spec (A.obj (op n)) ⟶ Φ.obj V := fun n => (e n).inv ≫ Φ.map (g n)
  have he' : ∀ {i j : ℕ} (f : i ⟶ j), Spec.map (A.map f.op) =
      (e i).inv ≫ Φ.map (T.map f) ≫ (e j).hom := fun f =>
    (Iso.eq_inv_comp _).2 (he f).symm
  have ht : ∀ {i j : ℕ} (f : i ⟶ j), Spec.map (A.map f.op) ≫ t j = t i := fun f => by
    change Spec.map (A.map f.op) ≫ (e _).inv ≫ Φ.map (g _) = (e _).inv ≫ Φ.map (g _)
    rw [he' f, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hc f]
  have heL' : ∀ n, Spec.map ((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).mapCone cR |>.π.app
      (op n)) = (e n).inv ≫ Φ.map (c.ι.app n) ≫ eLimit.hom := fun n =>
    (Iso.eq_inv_comp _).2 (heL n).symm
  obtain ⟨τ, hτ, -⟩ := existsUnique_spec_limit_hom_of_isAffine hA t ht
  have hπ : ∀ {i j : ℕ} (f : i ⟶ j),
      Spec.map (A.map f.op) ≫ Spec.map (((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).mapCone
        cR).π.app (op j)) =
      Spec.map (((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).mapCone cR).π.app (op i)) :=
    fun f => by
      rw [← Spec.map_comp]
      congr 1
      exact ((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).mapCone cR).w f.op
  obtain ⟨τ₀, -, huniq⟩ := existsUnique_spec_limit_hom_of_isAffine hA
    (fun n => Spec.map (((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).mapCone cR).π.app (op n)))
    hπ
  have hsec : τ ≫ Φ.map p ≫ eLimit.hom = 𝟙 _ := by
    have h1 := huniq (τ ≫ Φ.map p ≫ eLimit.hom) (fun n => by
      rw [← Category.assoc, hτ n, heL' n]
      change ((e n).inv ≫ Φ.map (g n)) ≫ Φ.map p ≫ eLimit.hom = _
      rw [Category.assoc, ← Category.assoc (Φ.map (g n)), ← Functor.map_comp, hg n])
    exact h1.trans (huniq (𝟙 _) fun n => Category.comp_id _).symm
  let s' : Φ.obj c.pt ⟶ Φ.obj V := eLimit.hom ≫ τ
  have hs' : s' ≫ Φ.map p = 𝟙 _ := by
    have : s' ≫ Φ.map p = eLimit.hom ≫ (τ ≫ Φ.map p ≫ eLimit.hom) ≫ eLimit.inv := by
      simp [s']
    rw [this, hsec]
    exact (congrArg (eLimit.hom ≫ ·) (Category.id_comp _)).trans eLimit.hom_inv_id
  have hs'n : ∀ n, Φ.map (c.ι.app n) ≫ s' = Φ.map (g n) := fun n => by
    change Φ.map (c.ι.app n) ≫ eLimit.hom ≫ τ = _
    rw [← Category.assoc, heL n, Category.assoc]
    exact (congrArg ((e n).hom ≫ ·) (hτ n)).trans (Iso.hom_inv_id_assoc _ _)
  obtain ⟨s, hsp, hs⟩ := exists_hom_of_scheme_section p s' hs'
  exact ⟨s, hsp, fun n => Φ.map_injective (by rw [Functor.map_comp, hs]; exact hs'n n)⟩

include hcR he heL in
/-- **A compatible family of points over the members of a tower of a presheaf affine over the
vertex comes from a section over the vertex** (Stacks 03WF): the base change of the presheaf to the
affine vertex is an affine scheme, to which
`AlgebraicGeometry.Space.exists_section_of_cocone` applies. -/
theorem exists_point_of_cocone {H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : H ⟶ yoneda.obj c.pt) (hp : IsAffineHom B S hS p) (x : ∀ n, yoneda.obj (T.obj n) ⟶ H)
    (hx : ∀ n, x n ≫ p = yoneda.map (c.ι.app n))
    (hc : ∀ {i j : ℕ} (f : i ⟶ j), yoneda.map (T.map f) ≫ x j = x i) :
    ∃ y : yoneda.obj c.pt ⟶ H, y ≫ p = 𝟙 _ ∧ ∀ n, yoneda.map (c.ι.app n) ≫ y = x n := by
  exact exists_point_of_exists_section (T := T.obj) (l := c.ι.app)
    (src := fun e : Arrow ℕ => e.left) (tgt := fun e => e.right) (tr := fun e => T.map e.hom)
    (IsAffine.of_isIso eLimit.hom) (fun e => c.w e.hom)
    (fun V _ q g hg hgc => exists_section_of_cocone hcR he heL q g hg fun f => hgc (Arrow.mk f))
    p hp x hx fun e => hc e.hom

variable (c) in
/-- A member of the tower as a test scheme over the vertex of the cocone. -/
abbrev legOver (n : ℕ) : SchemesOver (schemeSpace c.pt) :=
  CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map (c.ι.app n))

variable (c) in
/-- The vertex of the cocone as a test scheme over itself. -/
abbrev vertexOver : SchemesOver (schemeSpace c.pt) := CostructuredArrow.mk (𝟙 _)

variable (c) in
/-- A transition of the tower as a morphism of test schemes over the vertex. -/
def legOverMap {i j : ℕ} (f : i ⟶ j) : legOver c i ⟶ legOver c j :=
  CostructuredArrow.homMk (T.map f) (by
    change (schemeSpaceFunctor B S hS).map _ ≫ (schemeSpaceFunctor B S hS).map _ = _
    rw [← Functor.map_comp, c.w]
    rfl)

variable (c) in
/-- A leg of the cocone as a morphism of test schemes over the vertex. -/
def legOverProj (n : ℕ) : legOver c n ⟶ vertexOver c :=
  CostructuredArrow.homMk (c.ι.app n) (Category.comp_id _)

include hcR he heL in
/-- **A functor on the test schemes over the vertex of a tower cocone which is an algebraic space
affine over it takes the tower to a limit.** -/
theorem exists_eq_of_isAffineAlgebraicSpaceOver_cocone
    {Rf : (SchemesOver (schemeSpace c.pt))ᵒᵖ ⥤ Type (u + 1)}
    (hRf : IsAffineAlgebraicSpaceOver _ Rf) (u : ∀ n, Rf.obj (op (legOver c n)))
    (hu : ∀ {i j : ℕ} (f : i ⟶ j), Rf.map (legOverMap c f).op (u j) = u i) :
    ∃ v : Rf.obj (op (vertexOver c)), ∀ n, Rf.map (legOverProj c n).op v = u n := by
  exact exists_eq_of_exists_section (T := T.obj) (l := c.ι.app) (src := fun e : Arrow ℕ => e.left)
    (tgt := fun e => e.right) (tr := fun e => T.map e.hom) (IsAffine.of_isIso eLimit.hom)
    (fun e => c.w e.hom)
    (fun V _ q g hg hgc => exists_section_of_cocone hcR he heL q g hg fun f => hgc (Arrow.mk f))
    hRf u fun e => hu e.hom

end SpecLimit

/-! ### Effectivity of formal objects of a category fibred in sets -/

section FormalObjects

open Deformation.Artin

variable {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Formal objects of `𝒮_G` are effective as soon as compatible elements of `G` over the
truncations of a complete local base come from an element over the base.** -/
theorem isEffective_fibredCategory_of_exists_eq
    (h : ∀ (A : FormalBase S) (hA : ∀ n, B.Contains (A.truncation n))
      (ξ : ∀ n, G.obj (op (truncationOver B S hS A hA n))),
      (∀ n, G.map (truncationOverSucc B S hS A hA n).op (ξ (n + 1)) = ξ n) →
      ∃ x : G.obj (op (baseOver B S hS A (A.contains_spec_of_contains_truncation hA))),
        ∀ n, G.map (restrictionToBase B S hS A (A.contains_spec_of_contains_truncation hA) hA n).op
          x = ξ n)
    (ξ : FormalObject B S hS (Stack.fibredCategory B S hS G).val.p) :
    FormalObject.IsEffective B S hS (Stack.fibredCategory B S hS G).val.p
      (Stack.fibredCategory B S hS G).property ξ := by
  let p := (Stack.fibredCategory B S hS G).val.p
  have hA := ξ.base.contains_spec_of_contains_truncation ξ.contains
  let s : ∀ n, G.obj (op (truncationOver B S hS ξ.base ξ.contains n)) := fun n =>
    G.map (eqToHom (ξ.level_eq n).symm).op (ξ.level n).fiber.as
  have L₁ : ∀ {a b : BigFppfOver B S hS} (h : a = b) (y : G.obj (op a)),
      G.map (eqToHom h).op (G.map (eqToHom h.symm).op y) = y := by
    intro a b h y
    subst h
    simp
  have L₂ : ∀ {a a' b b' : BigFppfOver B S hS} (h : a = a') (h' : b = b') (f : a' ⟶ b')
      (y : G.obj (op b)), G.map f.op (G.map (eqToHom h'.symm).op y) =
        G.map (eqToHom h.symm).op (G.map (eqToHom h ≫ f ≫ eqToHom h'.symm).op y) := by
    intro a a' b b' h h' f y
    subst h h'
    simp
  have hs : ∀ n, (ξ.level n).fiber.as = G.map (eqToHom (ξ.level_eq n)).op (s n) :=
    fun n => (L₁ (ξ.level_eq n) _).symm
  have hcompat : ∀ n, G.map (truncationOverSucc B S hS ξ.base ξ.contains n).op (s (n + 1)) =
      s n := fun n => by
    have h₁ := fiber_as_eq_of_hom (ξ.transition n)
    have h₃ : (ξ.transition n).base = eqToHom (ξ.level_eq n) ≫
        truncationOverSucc B S hS ξ.base ξ.contains n ≫ eqToHom (ξ.level_eq (n + 1)).symm :=
      FormalObject.map_transition ξ n
    exact (L₂ (ξ.level_eq n) (ξ.level_eq (n + 1)) _ _).trans
      (congrArg (G.map (eqToHom (ξ.level_eq n).symm).op)
        ((congrArg (fun k => G.map k.op (ξ.level (n + 1)).fiber.as) h₃).symm.trans h₁.symm))
  obtain ⟨x, hx⟩ := h ξ.base ξ.contains s hcompat
  let X : (Stack.fibredCategory B S hS G).val.obj := ⟨baseOver B S hS ξ.base hA, Discrete.mk x⟩
  let r : ∀ n, ξ.level n ⟶ X := fun n =>
    ⟨eqToHom (ξ.level_eq n) ≫ restrictionToBase B S hS ξ.base hA ξ.contains n,
      Discrete.eqToHom (by
        change (ξ.level n).fiber.as =
          G.map (eqToHom (ξ.level_eq n) ≫ restrictionToBase B S hS ξ.base hA ξ.contains n).op x
        rw [hs n, op_comp, Functor.map_comp_apply, hx n])⟩
  refine FormalObject.isEffective_of_realization (Stack.fibredCategory B S hS G).property
    (hx := (rfl : p.obj X = baseOver B S hS ξ.base hA))
    (R :=
      { r := r
        comp_transition := fun n => fibredCategory_hom_ext _ _ ?_
        map_eq := fun n => congrArg (eqToHom (ξ.level_eq n) ≫ ·)
          (Category.comp_id (restrictionToBase B S hS ξ.base hA ξ.contains n)).symm })
  have L₃ : ∀ {a a' b b' : BigFppfOver B S hS} (h : a = a') (h' : b = b') (f : a' ⟶ b')
      {c : BigFppfOver B S hS} (r₁ : b' ⟶ c) (r₀ : a' ⟶ c), f ≫ r₁ = r₀ →
      (eqToHom h ≫ f ≫ eqToHom h'.symm) ≫ eqToHom h' ≫ r₁ = eqToHom h ≫ r₀ := by
    intro a a' b b' h h' f c r₁ r₀ hf
    subst h h'
    simpa using hf
  exact (congrArg (· ≫ eqToHom (ξ.level_eq (n + 1)) ≫
    restrictionToBase B S hS ξ.base hA ξ.contains (n + 1)) (FormalObject.map_transition ξ n)).trans
    (L₃ (ξ.level_eq n) (ξ.level_eq (n + 1)) _ _ _ (restrictionToBase_succ B S hS ξ.base hA
      ξ.contains n))

end FormalObjects

end AlgebraicGeometry.Space
