module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesFamilyDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesCoproductLift

/-!
# Descent of smooth lifts along a family of representables with coproducts (Stacks 0CJU)

Let `D` be a descent datum for the smooth lifts of Stacks 0CJP relative to the sieve generated
by a jointly surjective family `{f l : N l ⟶ U}` whose members are represented by objects
`nN l` of the big fppf site having a coproduct there, and whose attached smooth lifts have
ambient spaces represented by objects `nA l` having a coproduct too. Then `D` is effective:
the smooth lifts glue to one over the coproduct of the `N l`
(`AlgebraicGeometry.Stack.EtaleSmoothLift.exists_sigma_lift`), whose summand inclusions are
monomorphisms, pairwise disjoint and jointly surjective on points, so that
`AlgebraicGeometry.Stack.EtaleSmoothLift.isEffective_of_family` applies.

## Main results

* `AlgebraicGeometry.Stack.EtaleSmoothLift.isEffective_of_sigma`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u w

namespace AlgebraicGeometry.Space.SpacesEtale

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {W : AlgebraicSpaces B S hS}
  {L : Type u} (N : L → SpacesEtale B S hS W) (nN : L → BigFppfOver B S hS)
  (iN : ∀ l, yoneda.obj (nN l) ≅ (N l).obj.left.obj) {V : BigFppfOver B S hS}
  (c : ∀ l, nN l ⟶ V) (hV : IsColimit (Cofan.mk V c))

include hV

/-- The summand inclusions of the coproduct object are jointly surjective on points. -/
theorem exists_pointsMap_sigmaRepι (q : points B S hS (sigmaRep N nN iN c hV).obj.left.obj) :
    ∃ (l : L) (y : points B S hS (N l).obj.left.obj),
      pointsMap B S hS _ (sigmaRepι N nN iN c hV l).hom.left.hom y = q := by
  have hq : q ∈ ⋃ l, Set.range (pointsMap B S hS _ (yoneda.map (c l))) := by
    rw [(isEtaleCovering_yoneda_map nN c hV).jointly_surjective]
    trivial
  obtain ⟨l, y, hy⟩ := Set.mem_iUnion.1 hq
  refine ⟨l, pointsMap B S hS _ (iN l).hom y, ?_⟩
  have h₁ := congrFun (pointsMap_comp B S hS _ (iN l).inv (yoneda.map (c l)))
    (pointsMap B S hS _ (iN l).hom y)
  have h₂ := congrFun (pointsMap_comp B S hS _ (iN l).hom (iN l).inv) y
  rw [Iso.hom_inv_id, pointsMap_id] at h₂
  exact h₁.trans ((congrArg (pointsMap B S hS _ (yoneda.map (c l))) h₂.symm).trans hy)

/-- The summand inclusions of the coproduct object are monomorphisms. -/
theorem sigmaRepι_cancel (l : L) {Z : SpacesEtale B S hS W} (u u' : Z ⟶ N l)
    (h : u ≫ sigmaRepι N nN iN c hV l = u' ≫ sigmaRepι N nN iN c hV l) : u = u' := by
  have := mono_cofan_inj nN c hV l
  have h' : u.hom.left.hom ≫ ((iN l).inv ≫ yoneda.map (c l)) =
      u'.hom.left.hom ≫ ((iN l).inv ≫ yoneda.map (c l)) :=
    congrArg (fun g => g.hom.left.hom) h
  have hm : Mono ((iN l).inv ≫ yoneda.map (c l)) :=
    @mono_comp _ _ _ _ _ _ (IsIso.mono_of_iso _) _ (Functor.map_mono yoneda _)
  exact ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _
    (hm.right_cancellation _ _ h')))

/-- **The summands of the coproduct object are disjoint**: an object mapping to two distinct
summands compatibly has no points. -/
theorem isEmpty_points_of_comp_sigmaRepι_eq {k l : L} (hkl : k ≠ l) {Z : SpacesEtale B S hS W}
    (u : Z ⟶ N k) (u' : Z ⟶ N l)
    (h : u ≫ sigmaRepι N nN iN c hV k = u' ≫ sigmaRepι N nN iN c hV l) :
    IsEmpty (points B S hS Z.obj.left.obj) := by
  refine ⟨fun q => ?_⟩
  induction q using Quot.ind with
  | mk x =>
    have hT := congrArg (fun g => g.hom.left.hom.app _ x.value) h
    have hE := isEmpty_of_comp_eq_cofan nN c hV hkl
      ((iN k).inv.app _ (u.hom.left.hom.app _ x.value))
      ((iN l).inv.app _ (u'.hom.left.hom.app _ x.value)) hT
    exact hE.false (Classical.choice (inferInstance : Nonempty (Spec (.of x.carrier))))

omit hV in
/-- The coproduct object is representable. -/
theorem isRepresentable_sigmaRep (hV : IsColimit (Cofan.mk V c)) :
    (sigmaRep N nN iN c hV).obj.left.obj.IsRepresentable := by
  show (yoneda.obj V).IsRepresentable
  infer_instance

end AlgebraicGeometry.Space.SpacesEtale

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

namespace EtaleSmoothLift

attribute [local instance] isFibered_proj

/-- `AlgebraicGeometry.Stack.EtaleSmoothLift.exists_sigma_lift` for a family of smooth lifts
whose bases are given objects `N l` of the spaces-étale site. -/
theorem exists_sigma_lift_of_base_eq {L : Type u} (ξ : L → EtaleSmoothLift B S hS ι hι W x hx)
    (N : L → Space.SpacesEtale B S hS W) (hN : ∀ l, (ξ l).base = N l)
    (nN nA : L → BigFppfOver B S hS) (iN : ∀ l, yoneda.obj (nN l) ≅ (N l).obj.left.obj)
    (iA : ∀ l, yoneda.obj (nA l) ≅ (ξ l).ambient.obj) {VN VA : BigFppfOver B S hS}
    (cN : ∀ l, nN l ⟶ VN) (cA : ∀ l, nA l ⟶ VA) (hVN : IsColimit (Cofan.mk VN cN))
    (hVA : IsColimit (Cofan.mk VA cA)) :
    ∃ (ζ : EtaleSmoothLift B S hS ι hι W x hx)
      (hζ : ζ.base = Space.SpacesEtale.sigmaRep N nN iN cN hVN) (m : ∀ l, ξ l ⟶ ζ),
      ∀ l, (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift
        (Space.SpacesEtale.sigmaRepι N nN iN cN hVN l ≫ eqToHom hζ.symm) (m l) := by
  obtain rfl : (fun l => (ξ l).base) = N := funext hN
  obtain ⟨⟨ζ, hζ⟩, m, hm⟩ := exists_sigma_lift ξ nN nA iN iA cN cA hVN hVA
  refine ⟨ζ, hζ, m, fun l => ?_⟩
  have := hm l
  infer_instance

variable {U : Space.SpacesEtale B S hS W} {L : Type u} {N : L → Space.SpacesEtale B S hS W}
  {f : ∀ l, N l ⟶ U}
  (D : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).SieveDescentDatum (Sieve.ofArrows N f))

/-- `AlgebraicGeometry.Stack.EtaleSmoothLift.isEffective_of_family` with the base of the smooth
lift identified with a given object. -/
theorem isEffective_of_family_of_eq (X : Space.SpacesEtale B S hS W) (ιX : ∀ l, N l ⟶ X)
    (hcov : ∀ q : Space.points B S hS X.obj.left.obj, ∃ (l : L)
      (y : Space.points B S hS (N l).obj.left.obj),
        Space.pointsMap B S hS _ (ιX l).hom.left.hom y = q)
    (hinj : ∀ (l : L) {Z : Space.SpacesEtale B S hS W} (u u' : Z ⟶ N l),
      u ≫ ιX l = u' ≫ ιX l → u = u')
    (hdisj : ∀ (k l : L), k ≠ l → ∀ {Z : Space.SpacesEtale B S hS W} (u : Z ⟶ N k)
      (u' : Z ⟶ N l), u ≫ ιX k = u' ≫ ιX l → IsEmpty (Space.points B S hS Z.obj.left.obj))
    (ε : X ⟶ U) (hε : ∀ l, ιX l ≫ ε = f l) (hsurj : Space.IsSurjective B S hS ε.hom.left.hom)
    (hrep : X.obj.left.obj.IsRepresentable) (ζ : EtaleSmoothLift B S hS ι hι W x hx)
    (hζ : ζ.base = X) (m : ∀ l, (famObj D l).1 ⟶ ζ)
    (hm : ∀ l, (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift
      (ιX l ≫ eqToHom hζ.symm) (m l)) :
    D.IsEffective := by
  subst hζ
  exact isEffective_of_family D ζ hrep ιX hcov hinj hdisj ε hε hsurj m
    (fun l => by simpa using hm l)

/-- **Effectivity along a jointly surjective family of representables with coproducts.** If the
members `N l` of the family and the ambient spaces of the smooth lifts of `D` over them are
represented by objects of the big fppf site having coproducts there, `D` is effective. -/
theorem isEffective_of_sigma (nN : L → BigFppfOver B S hS)
    (iN : ∀ l, yoneda.obj (nN l) ≅ (N l).obj.left.obj) {VN : BigFppfOver B S hS}
    (cN : ∀ l, nN l ⟶ VN) (hVN : IsColimit (Cofan.mk VN cN))
    (hf : ∀ p : Space.points B S hS U.obj.left.obj, ∃ (l : L)
      (q : Space.points B S hS (N l).obj.left.obj),
        Space.pointsMap B S hS _ (f l).hom.left.hom q = p)
    (nA : L → BigFppfOver B S hS) (iA : ∀ l, yoneda.obj (nA l) ≅ (famObj D l).1.ambient.obj)
    {VA : BigFppfOver B S hS} (cA : ∀ l, nA l ⟶ VA) (hVA : IsColimit (Cofan.mk VA cA)) :
    D.IsEffective := by
  obtain ⟨ζ, hζ, m, hm⟩ := exists_sigma_lift_of_base_eq (fun l => (famObj D l).1) N
    (fun l => (famObj D l).2) nN nA iN iA cN cA hVN hVA
  obtain ⟨d, hd⟩ := Space.SpacesEtale.exists_sigmaRep_desc N nN iN cN hVN U f
  refine isEffective_of_family_of_eq D _ _
    (Space.SpacesEtale.exists_pointsMap_sigmaRepι N nN iN cN hVN)
    (fun l _ u u' h => Space.SpacesEtale.sigmaRepι_cancel N nN iN cN hVN l u u' h)
    (fun _ _ hkl _ u u' h =>
      Space.SpacesEtale.isEmpty_points_of_comp_sigmaRepι_eq N nN iN cN hVN hkl u u' h)
    d hd (fun p => ?_) (Space.SpacesEtale.isRepresentable_sigmaRep N nN iN cN hVN) ζ hζ m hm
  obtain ⟨l, q, hq⟩ := hf p
  refine ⟨Space.pointsMap B S hS _ (Space.SpacesEtale.sigmaRepι N nN iN cN hVN l).hom.left.hom q,
    ?_⟩
  rw [← Space.pointsMap_comp_apply]
  show Space.pointsMap B S hS _
    (Space.SpacesEtale.sigmaRepι N nN iN cN hVN l ≫ d).hom.left.hom q = p
  rw [hd l]
  exact hq

end EtaleSmoothLift

end AlgebraicGeometry.Stack
