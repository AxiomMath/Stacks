module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackCorner
public import StacksFrontier.CategoryTheory.Sites.Descent.CoGrothendieckPullbackComp
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedFunctor
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CategoricalPullbackSquareDiagonal

/-!
# The comparison functor of Stacks 0EX9 for a Grothendieck construction

Conditions (2) and (3) of Stacks 0EX9 are stated, in
`AlgebraicGeometry.BigHOver.twoFibreProductComparison`, for an arbitrary fibred category
`p : 𝒳 ⥤ (Sch/S)_h`: its fibres are `CategoryTheory.Functor.Fiber`, its transition functors are
the chosen cartesian pullbacks `CategoryTheory.Functor.IsFibered.fiberPullback`, and the
structural isomorphism of the comparison functor is the comparison
`CategoryTheory.Functor.IsFibered.CartStruct.cmpIso` of two cartesian structures.  When `p` is the
Grothendieck construction of a pseudofunctor `F`, as is the category fibred in groupoids of Stacks
Tag 0EXE, the categories, the transition functors and the comparison isomorphism one actually
computes with are those of `F`: the values `F U`, the functors `F f` and the composite of the two
composition constraints of `F` around the square.

This file proves that the two comparison functors are equivalences together.

## Main definitions

* `AlgebraicGeometry.BigHOver.pseudofunctorSquareIso`: for a commutative square of the site, the
  isomorphism `F z ⋙ F e ≅ F b ⋙ F d` given by the two composition constraints of `F`.
* `AlgebraicGeometry.BigHOver.pseudofunctorSquareComparison`: the functor
  `F X ⥤ F Z ×_{F E} F X'` it determines.

## Main results

* `AlgebraicGeometry.BigHOver.cartesianLift_eq_vertHom_mapComp'`: the tautological cartesian lift
  of the Grothendieck construction along a composite, for a composite given as a variable.
* `AlgebraicGeometry.BigHOver.pseudofunctorSquareComparisonIso`: the pseudofunctor comparison
  followed by the identification of the fibres is the fibration comparison preceded by it.
* `AlgebraicGeometry.BigHOver.isEquivalence_twoFibreProductComparison_forget_iff`: **the
  comparison functor of Stacks 0EX9 for the Grothendieck construction of `F` is an equivalence
  exactly when the comparison functor of `F` is.**

## Implementation notes

The transfer between the two two-fibre products is
`CategoryTheory.Limits.CategoricalPullback.map` on the identifications
`CategoryTheory.Pseudofunctor.CoGrothendieck.fiberFunctor` of the three lower corners, with the
comparisons `CategoryTheory.Pseudofunctor.CoGrothendieck.pullbackCmpIso` of the transition
functors as its two fillers; it is an equivalence by Stacks 02XB.  The one identity to be proved
is the compatibility of the two structural isomorphisms, and it is proved after composing with
the strongly cartesian projection of the chosen pullback along `d` then `b`: every term then
telescopes to a composite of tautological cartesian lifts of the Grothendieck construction, which
compose by `CategoryTheory.Pseudofunctor.CoGrothendieck.cartesianLift_of_comp`.

## References

* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
* [Stacks Project, Tag 003S](https://stacks.math.columbia.edu/tag/003S)
* [Stacks Project, Tag 02XB](https://stacks.math.columbia.edu/tag/02XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.IsFibered CategoryTheory.Functor.IsFibered.CartStruct
open CategoryTheory.Pseudofunctor CategoryTheory.Functor

universe v₂ u₂ u

-- Load-bearing, for the reasons set out in the implementation notes of
-- `StacksFrontier/CategoryTheory/Sites/Descent/CoGrothendieckStack.lean`: the underlying object of a
-- fibre element is spelled both through `Fiber.fiberInclusion` and as a `Subtype.val`.
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.mk CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.IsFibered.fiberPullback

namespace AlgebraicGeometry

namespace BigHOver

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable (F : Pseudofunctor (LocallyDiscrete (BigHOver B S hS)ᵒᵖ) Cat.{v₂, u₂})

/-! ### The tautological cartesian lifts along a composite and along equal morphisms -/

/-- **The tautological cartesian lift of the Grothendieck construction along a composite**, the
composite being a variable `n` subject to `g ≫ f = n`: it is the lift along `g` after the lift
along `f`, corrected by the vertical morphism the composition constraint `mapComp'` of `F`
attaches to the object. -/
theorem cartesianLift_eq_vertHom_mapComp' {U V W : BigHOver B S hS} (f : V ⟶ U) (g : W ⟶ V)
    (n : W ⟶ U) (hn : g ≫ f = n) (M : F.obj ⟨op U⟩) :
    CoGrothendieck.cartesianLift M n =
      CoGrothendieck.vertHom F W
          ((F.mapComp' f.op.toLoc g.op.toLoc n.op.toLoc
            (by rw [← hn]; rfl)).hom.toNatTrans.app M) ≫
        CoGrothendieck.cartesianLift ((F.map f.op.toLoc).toFunctor.obj M) g ≫
          CoGrothendieck.cartesianLift M f := by
  subst hn
  exact CoGrothendieck.cartesianLift_of_comp F f g M _
    (congrArg (fun i => i.hom.toNatTrans.app M) (F.mapComp'_eq_mapComp f.op.toLoc g.op.toLoc))

/-! ### The comparison functor of a pseudofunctor -/

variable {X X' Z E : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z)

/-- **The comparison of the two composite transition functors of a pseudofunctor around a
commutative square**: the inverse of the composition constraint of `F` along `z` then `e`,
followed by the composition constraint along `b` then `d`, read at the composite `e ≫ z`. -/
def pseudofunctorSquareIso (hw : e ≫ z = d ≫ b) :
    (F.map z.op.toLoc).toFunctor ⋙ (F.map e.op.toLoc).toFunctor ≅
      (F.map b.op.toLoc).toFunctor ⋙ (F.map d.op.toLoc).toFunctor :=
  (Cat.Hom.toNatIso (F.mapComp z.op.toLoc e.op.toLoc)).symm ≪≫
    Cat.Hom.toNatIso (F.mapComp' b.op.toLoc d.op.toLoc (e ≫ z).op.toLoc
      (by rw [hw]; rfl))

/-- **The functor `F X ⥤ F Z ×_{F E} F X'` of a commutative square**, for a pseudofunctor `F` on
the big h category over `S`. -/
def pseudofunctorSquareComparison (hw : e ≫ z = d ≫ b) :
    F.obj ⟨op X⟩ ⥤ CategoricalPullback (F.map e.op.toLoc).toFunctor (F.map d.op.toLoc).toFunctor :=
  CategoricalPullback.squareComparison (F.map z.op.toLoc).toFunctor (F.map b.op.toLoc).toFunctor
    (F.map e.op.toLoc).toFunctor (F.map d.op.toLoc).toFunctor
    (pseudofunctorSquareIso F b z d e hw)

/-! ### The comparison with the fibration -/

variable (hsq : IsPullback e d z b)

/-- The transfer functor from the two-fibre product of the transition functors of `F` to that of
the chosen pullback functors of its Grothendieck construction: Stacks 02XA on the identifications
of the fibres, with the comparisons of the transition functors as fillers. -/
def pseudofunctorTwoFibreProductTransfer :
    CategoricalPullback (F.map e.op.toLoc).toFunctor (F.map d.op.toLoc).toFunctor ⥤
      CategoricalPullback
        (Functor.IsFibered.fiberPullback (p := CoGrothendieck.forget F) e)
        (Functor.IsFibered.fiberPullback (p := CoGrothendieck.forget F) d) :=
  CategoricalPullback.map (F.map e.op.toLoc).toFunctor (F.map d.op.toLoc).toFunctor
    (CoGrothendieck.fiberFunctor F Z) (CoGrothendieck.fiberFunctor F X')
    (CoGrothendieck.fiberFunctor F E)
    (Functor.IsFibered.fiberPullback (p := CoGrothendieck.forget F) e)
    (Functor.IsFibered.fiberPullback (p := CoGrothendieck.forget F) d)
    (CoGrothendieck.pullbackCmpIso F d.op.toLoc).symm
    (CoGrothendieck.pullbackCmpIso F e.op.toLoc)

/-- The transfer functor `pseudofunctorTwoFibreProductTransfer F d e` is an equivalence of
categories. -/
instance : (pseudofunctorTwoFibreProductTransfer F d e).IsEquivalence :=
  induced_isEquivalence_of_isEquivalence _ _ _ _ _

/-- A morphism of fibres that composes with the chosen cartesian lift along `u` to `L` still does
so after the chosen pullback along `v`, up to the lift along `v`. -/
private theorem fiberPullback_map_comp_proj {A A' A'' : BigHOver B S hS} (u : A' ⟶ A)
    (v : A'' ⟶ A') (N : (CoGrothendieck.forget F).Fiber A) {Y : (CoGrothendieck.forget F).Fiber A'}
    (c : Y ⟶ (fiberPullback (p := CoGrothendieck.forget F) u).obj N)
    {L : Fiber.fiberInclusion.obj Y ⟶ Fiber.fiberInclusion.obj N}
    (hc : Fiber.fiberInclusion.map c ≫ IsPreFibered.pullbackMap N.2 u = L) :
    Fiber.fiberInclusion.map ((fiberPullback (p := CoGrothendieck.forget F) v).map c) ≫
        (cartComp (p := CoGrothendieck.forget F) u v).proj N =
      IsPreFibered.pullbackMap Y.2 v ≫ L := by
  subst hc
  change Fiber.fiberInclusion.map (fiberPullbackMap v c) ≫
    IsPreFibered.pullbackMap ((fiberPullback (p := CoGrothendieck.forget F) u).obj N).2 v ≫
      IsPreFibered.pullbackMap N.2 u = _
  rw [← Category.assoc, fiberPullbackMap_comm (p := CoGrothendieck.forget F) v c, Category.assoc]

/-- **The compatibility of the two structural isomorphisms, for abstract comparisons.**  The four
comparisons of the transition functors of `F` with the chosen pullbacks and the vertical morphism
`θ` are arguments, characterised by their defining triangles; this keeps every object in one
spelling, which the comparisons themselves, typed through `LocallyDiscrete`, do not. -/
theorem squareIso_compat_of_fac (M : F.obj ⟨op X⟩)
    (cz : (CoGrothendieck.fiberFunctor F Z).obj ((F.map z.op.toLoc).toFunctor.obj M) ≅
      (fiberPullback (p := CoGrothendieck.forget F) z).obj
        ((CoGrothendieck.fiberFunctor F X).obj M))
    (hcz : Fiber.fiberInclusion.map cz.hom ≫
        IsPreFibered.pullbackMap ((CoGrothendieck.fiberFunctor F X).obj M).2 z =
      CoGrothendieck.cartesianLift M z)
    (cb : (CoGrothendieck.fiberFunctor F X').obj ((F.map b.op.toLoc).toFunctor.obj M) ≅
      (fiberPullback (p := CoGrothendieck.forget F) b).obj
        ((CoGrothendieck.fiberFunctor F X).obj M))
    (hcb : Fiber.fiberInclusion.map cb.hom ≫
        IsPreFibered.pullbackMap ((CoGrothendieck.fiberFunctor F X).obj M).2 b =
      CoGrothendieck.cartesianLift M b)
    (ce : (CoGrothendieck.fiberFunctor F E).obj
        ((F.map e.op.toLoc).toFunctor.obj ((F.map z.op.toLoc).toFunctor.obj M)) ≅
      (fiberPullback (p := CoGrothendieck.forget F) e).obj
        ((CoGrothendieck.fiberFunctor F Z).obj ((F.map z.op.toLoc).toFunctor.obj M)))
    (hce : Fiber.fiberInclusion.map ce.hom ≫
        IsPreFibered.pullbackMap
          ((CoGrothendieck.fiberFunctor F Z).obj ((F.map z.op.toLoc).toFunctor.obj M)).2 e =
      CoGrothendieck.cartesianLift ((F.map z.op.toLoc).toFunctor.obj M) e)
    (cd : (CoGrothendieck.fiberFunctor F E).obj
        ((F.map d.op.toLoc).toFunctor.obj ((F.map b.op.toLoc).toFunctor.obj M)) ≅
      (fiberPullback (p := CoGrothendieck.forget F) d).obj
        ((CoGrothendieck.fiberFunctor F X').obj ((F.map b.op.toLoc).toFunctor.obj M)))
    (hcd : Fiber.fiberInclusion.map cd.hom ≫
        IsPreFibered.pullbackMap
          ((CoGrothendieck.fiberFunctor F X').obj ((F.map b.op.toLoc).toFunctor.obj M)).2 d =
      CoGrothendieck.cartesianLift ((F.map b.op.toLoc).toFunctor.obj M) d)
    (θ : (F.map e.op.toLoc).toFunctor.obj ((F.map z.op.toLoc).toFunctor.obj M) ⟶
      (F.map d.op.toLoc).toFunctor.obj ((F.map b.op.toLoc).toFunctor.obj M))
    (hθ : CoGrothendieck.vertHom F E θ ≫
        CoGrothendieck.cartesianLift ((F.map b.op.toLoc).toFunctor.obj M) d ≫
          CoGrothendieck.cartesianLift M b =
      CoGrothendieck.cartesianLift ((F.map z.op.toLoc).toFunctor.obj M) e ≫
        CoGrothendieck.cartesianLift M z) :
    (fiberPullback (p := CoGrothendieck.forget F) e).map cz.hom ≫
        (cmpIso (cartComp z e) (cartCompOfSquare b d hsq)).hom.app
          ((CoGrothendieck.fiberFunctor F X).obj M) =
      (ce.inv ≫ (CoGrothendieck.fiberFunctor F E).map θ ≫ cd.hom) ≫
        (fiberPullback (p := CoGrothendieck.forget F) d).map cb.hom := by
  have := (cartComp (p := CoGrothendieck.forget F) b d).isCart
    ((CoGrothendieck.fiberFunctor F X).obj M)
  refine (cancel_epi ce.hom).1 ?_
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  refine Functor.fiber_hom_ext_of_cartesian (d ≫ b)
    ((cartComp (p := CoGrothendieck.forget F) b d).proj
      ((CoGrothendieck.fiberFunctor F X).obj M))
    (Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian _ _ _) _ _ ?_
  have pL4 : Fiber.fiberInclusion.map
        ((cmpIso (cartComp z e) (cartCompOfSquare b d hsq)).hom.app
          ((CoGrothendieck.fiberFunctor F X).obj M)) ≫
        (cartComp (p := CoGrothendieck.forget F) b d).proj
          ((CoGrothendieck.fiberFunctor F X).obj M) =
      (cartComp (p := CoGrothendieck.forget F) z e).proj
        ((CoGrothendieck.fiberFunctor F X).obj M) := by
    rw [cmpIso_hom_app_incl,
      (proj_cast hsq.w (cartComp b d) ((CoGrothendieck.fiberFunctor F X).obj M)).symm]
    exact cmpUnderlying_fac _ _ _
  simp only [Functor.map_comp, Category.assoc]
  rw [pL4, fiberPullback_map_comp_proj F z e _ cz.hom hcz,
    fiberPullback_map_comp_proj F b d _ cb.hom hcb, ]
  refine ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ CoGrothendieck.cartesianLift M z) hce)).trans (hθ.symm.trans ?_)
  exact congrArg (CoGrothendieck.vertHom F E θ ≫ ·)
    ((congrArg (· ≫ CoGrothendieck.cartesianLift M b) hcd.symm).trans (Category.assoc _ _ _))

/-- **The compatibility of the two structural isomorphisms**, which is the one identity behind
`AlgebraicGeometry.BigHOver.pseudofunctorSquareComparisonIso`. -/
theorem pseudofunctorSquareIso_compat (M : F.obj ⟨op X⟩) :
    (Functor.IsFibered.fiberPullback (p := CoGrothendieck.forget F) e).map
          ((CoGrothendieck.pullbackCmpIso F z.op.toLoc).hom.app M) ≫
        (cmpIso (cartComp z e) (cartCompOfSquare b d hsq)).hom.app
          ((CoGrothendieck.fiberFunctor F X).obj M) =
      ((CoGrothendieck.pullbackCmpIso F e.op.toLoc).inv.app
            ((F.map z.op.toLoc).toFunctor.obj M) ≫
          (CoGrothendieck.fiberFunctor F E).map
            ((pseudofunctorSquareIso F b z d e hsq.w).hom.app M) ≫
          (CoGrothendieck.pullbackCmpIso F d.op.toLoc).hom.app
            ((F.map b.op.toLoc).toFunctor.obj M)) ≫
        (Functor.IsFibered.fiberPullback (p := CoGrothendieck.forget F) d).map
          ((CoGrothendieck.pullbackCmpIso F b.op.toLoc).hom.app M) := by
  refine squareIso_compat_of_fac F b z d e hsq M
    ((CoGrothendieck.pullbackCmpIso F z.op.toLoc).app M)
    (CoGrothendieck.pullbackCmp_hom_fac F z.op.toLoc M)
    ((CoGrothendieck.pullbackCmpIso F b.op.toLoc).app M)
    (CoGrothendieck.pullbackCmp_hom_fac F b.op.toLoc M)
    ((CoGrothendieck.pullbackCmpIso F e.op.toLoc).app ((F.map z.op.toLoc).toFunctor.obj M))
    (CoGrothendieck.pullbackCmp_hom_fac F e.op.toLoc _)
    ((CoGrothendieck.pullbackCmpIso F d.op.toLoc).app ((F.map b.op.toLoc).toFunctor.obj M))
    (CoGrothendieck.pullbackCmp_hom_fac F d.op.toLoc _)
    ((pseudofunctorSquareIso F b z d e hsq.w).hom.app M) ?_
  have h₁ := CoGrothendieck.cartesianLift_of_comp F z e M _ rfl
  have h₂ := cartesianLift_eq_vertHom_mapComp' F b d (e ≫ z) hsq.w.symm M
  have hσ : CoGrothendieck.vertHom F E ((pseudofunctorSquareIso F b z d e hsq.w).hom.app M) =
      CoGrothendieck.vertHom F E ((F.mapComp z.op.toLoc e.op.toLoc).inv.toNatTrans.app M) ≫
        CoGrothendieck.vertHom F E ((F.mapComp' b.op.toLoc d.op.toLoc (e ≫ z).op.toLoc
          (by rw [hsq.w]; rfl)).hom.toNatTrans.app M) :=
    (CoGrothendieck.ι F E).map_comp _ _
  have hinv : CoGrothendieck.vertHom F E ((F.mapComp z.op.toLoc e.op.toLoc).inv.toNatTrans.app M) ≫
      CoGrothendieck.vertHom F E ((F.mapComp z.op.toLoc e.op.toLoc).hom.toNatTrans.app M) = 𝟙 _ :=
    ((CoGrothendieck.ι F E).map_comp _ _).symm.trans
      ((congrArg (CoGrothendieck.ι F E).map
        (Cat.Hom.inv_hom_id_toNatTrans_app (F.mapComp z.op.toLoc e.op.toLoc) M)).trans
        ((CoGrothendieck.ι F E).map_id _))
  calc CoGrothendieck.vertHom F E ((pseudofunctorSquareIso F b z d e hsq.w).hom.app M) ≫
        CoGrothendieck.cartesianLift ((F.map b.op.toLoc).toFunctor.obj M) d ≫
          CoGrothendieck.cartesianLift M b
      = CoGrothendieck.vertHom F E ((F.mapComp z.op.toLoc e.op.toLoc).inv.toNatTrans.app M) ≫
          CoGrothendieck.cartesianLift M (e ≫ z) :=
        (congrArg (· ≫ _) hσ).trans ((Category.assoc _ _ _).trans (congrArg _ h₂.symm))
    _ = CoGrothendieck.vertHom F E ((F.mapComp z.op.toLoc e.op.toLoc).inv.toNatTrans.app M) ≫
          CoGrothendieck.vertHom F E ((F.mapComp z.op.toLoc e.op.toLoc).hom.toNatTrans.app M) ≫
            CoGrothendieck.cartesianLift ((F.map z.op.toLoc).toFunctor.obj M) e ≫
              CoGrothendieck.cartesianLift M z := congrArg _ h₁
    _ = CoGrothendieck.cartesianLift ((F.map z.op.toLoc).toFunctor.obj M) e ≫
          CoGrothendieck.cartesianLift M z :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hinv).trans (Category.id_comp _))

/-- **The pseudofunctor comparison, followed by the transfer to the fibration, is the fibration
comparison preceded by the identification of the fibre over the base.** -/
def pseudofunctorSquareComparisonIso :
    pseudofunctorSquareComparison F b z d e hsq.w ⋙ pseudofunctorTwoFibreProductTransfer F d e ≅
      CoGrothendieck.fiberFunctor F X ⋙
        twoFibreProductComparison B S hS (CoGrothendieck.forget F) b z d e hsq :=
  NatIso.ofComponents
    (fun M => CategoricalPullback.mkIso ((CoGrothendieck.pullbackCmpIso F z.op.toLoc).app M)
      ((CoGrothendieck.pullbackCmpIso F b.op.toLoc).app M)
      (pseudofunctorSquareIso_compat F b z d e hsq M))
    (fun {M N} g => by
      refine CategoricalPullback.hom_ext ?_ ?_
      · exact (CoGrothendieck.pullbackCmpIso F z.op.toLoc).hom.naturality g
      · exact (CoGrothendieck.pullbackCmpIso F b.op.toLoc).hom.naturality g)

/-- **The comparison functor of Stacks 0EX9 for the Grothendieck construction of a pseudofunctor
`F` is an equivalence exactly when the comparison functor of `F` itself is.** -/
theorem isEquivalence_twoFibreProductComparison_forget_iff :
    (twoFibreProductComparison B S hS (CoGrothendieck.forget F) b z d e hsq).IsEquivalence ↔
      (pseudofunctorSquareComparison F b z d e hsq.w).IsEquivalence := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · have : (pseudofunctorSquareComparison F b z d e hsq.w ⋙
        pseudofunctorTwoFibreProductTransfer F d e).IsEquivalence :=
      Functor.isEquivalence_of_iso (pseudofunctorSquareComparisonIso F b z d e hsq).symm
    exact Functor.isEquivalence_of_comp_right _ (pseudofunctorTwoFibreProductTransfer F d e)
  · have : (CoGrothendieck.fiberFunctor F X ⋙
        twoFibreProductComparison B S hS (CoGrothendieck.forget F) b z d e hsq).IsEquivalence :=
      Functor.isEquivalence_of_iso (pseudofunctorSquareComparisonIso F b z d e hsq)
    exact Functor.isEquivalence_of_comp_left (CoGrothendieck.fiberFunctor F X) _

end BigHOver

end AlgebraicGeometry

end
