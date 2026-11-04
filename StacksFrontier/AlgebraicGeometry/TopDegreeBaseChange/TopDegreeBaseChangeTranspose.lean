module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite

/-!
# The transpose of the derived base change map under the horizontal adjunction (draft)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedPullback.Composition

universe u

namespace Stacks.Cohomology.DerivedBaseChange

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-- Transposition under the derived adjunction along a morphism, transported along an equality
of morphisms. -/
theorem derivedAdjunction_homEquiv_eqToHom {X Y : RingedSpace.{u, u}} {q₁ q₂ : X ⟶ Y}
    (e : q₁ = q₂) (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (e₁ : (derivedPullback q₁).obj M = (derivedPullback q₂).obj M)
    (e₂ : (derivedPushforward q₂).obj N = (derivedPushforward q₁).obj N)
    (ψ : (derivedPullback q₂).obj M ⟶ N) :
    (derivedAdjunction q₁).homEquiv M N (eqToHom e₁ ≫ ψ) =
      (derivedAdjunction q₂).homEquiv M N ψ ≫ eqToHom e₂ := by
  subst e
  simp

namespace TransposeMate

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  {Lh : A ⥤ B} {Rh : B ⥤ A} {Lf' : A ⥤ C} {Rf' : C ⥤ A} {Lf'' : B ⥤ D} {Rf'' : D ⥤ B}
  {Lh' : C ⥤ D} {Rh' : D ⥤ C} {Lc : A ⥤ D} {Rc : D ⥤ A}
  (adjh : Lh ⊣ Rh) (adjf' : Lf' ⊣ Rf') (adjf'' : Lf'' ⊣ Rf'') (adjh' : Lh' ⊣ Rh')
  (adjc : Lc ⊣ Rc) (e₁ : Lh ⋙ Lf'' ≅ Lc) (e₂ : Lf' ⋙ Lh' ≅ Lc)
  (p₁ : ∀ N, Rh.obj (Rf''.obj N) ⟶ Rc.obj N) (p₂ : ∀ N, Rf'.obj (Rh'.obj N) ⟶ Rc.obj N)

/-- **The transpose of a mate under the other pair of adjunctions**, with every functor a
variable. If both composite adjunctions agree with `adjc` along the comparisons, then the mate of
`e₁.hom ≫ e₂.inv`, transposed under `adjh`, is `Rf'` of the unit of `adjh'`. -/
theorem homEquiv_derivedBaseChangeMap
    (h₁ : ∀ M N (φ : Lc.obj M ⟶ N),
      adjh.homEquiv _ _ (adjf''.homEquiv _ _ (e₁.hom.app M ≫ φ)) ≫ p₁ N =
        adjc.homEquiv M N φ)
    (h₂ : ∀ M N (φ : Lc.obj M ⟶ N),
      adjf'.homEquiv _ _ (adjh'.homEquiv _ _ (e₂.hom.app M ≫ φ)) ≫ p₂ N =
        adjc.homEquiv M N φ)
    (K : C) (bc : Lh.obj (Rf'.obj K) ⟶ Rf''.obj (Lh'.obj K))
    (hbc : bc = adjf''.homEquiv _ _ (e₁.hom.app (Rf'.obj K) ≫ e₂.inv.app (Rf'.obj K) ≫
      Lh'.map (adjf'.counit.app K))) :
    adjh.homEquiv _ _ bc ≫ p₁ (Lh'.obj K) =
      Rf'.map (adjh'.unit.app K) ≫ p₂ (Lh'.obj K) := by
  subst hbc
  refine (h₁ (Rf'.obj K) (Lh'.obj K)
    (e₂.inv.app (Rf'.obj K) ≫ Lh'.map (adjf'.counit.app K))).trans ?_
  rw [← h₂, Iso.hom_inv_id_app_assoc]
  congr 1
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hn : adjh'.unit.app (Lf'.obj (Rf'.obj K)) ≫ Rh'.map (Lh'.map (adjf'.counit.app K)) =
      adjf'.counit.app K ≫ adjh'.unit.app K := (adjh'.unit.naturality _).symm
  rw [hn, Functor.map_comp, ← Category.assoc, adjf'.right_triangle_components, Category.id_comp]

end TransposeMate

variable {X'' X' Y'' Y' : RingedSpace.{u, u}} (h' : X'' ⟶ X') (f'' : X'' ⟶ Y'')
  (f' : X' ⟶ Y') (h : Y'' ⟶ Y') (sq : h' ≫ f' = f'' ≫ h)

include sq in
/-- The two derived pushforwards along the diagonal of a commutative square agree. -/
theorem derivedPushforward_diagonal_eq :
    derivedPushforward (f'' ≫ h) = derivedPushforward (h' ≫ f') :=
  congrArg (fun q : X'' ⟶ Y' => derivedPushforward q) sq.symm

/-- A transport of functors read at an object is a transport of objects. -/
theorem eqToHom_app_eq {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (e : F = G) (Y : C)
    (e' : F.obj Y = G.obj Y) : (eqToHom e : F ⟶ G).app Y = eqToHom e' := by
  subst e
  simp

/-- Derived pushforwards along equal morphisms agree on objects. -/
theorem derivedPushforward_obj_eq {X Y : RingedSpace.{u, u}} {q₁ q₂ : X ⟶ Y} (e : q₁ = q₂)
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedPushforward q₁).obj N = (derivedPushforward q₂).obj N := by
  subst e; rfl

/-- Derived pullbacks along equal morphisms agree on objects. -/
theorem derivedPullback_obj_eq {X Y : RingedSpace.{u, u}} {q₁ q₂ : X ⟶ Y} (e : q₁ = q₂)
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (derivedPullback q₁).obj N = (derivedPullback q₂).obj N := by
  subst e; rfl

/-- The composition isomorphism for `f'' ≫ h` at an object, followed by the transport along
the commutativity of the square. -/
def pushforwardCompTransport (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing X''))) :
    (derivedPushforward h).obj ((derivedPushforward f'').obj N) ⟶
      (derivedPushforward (h' ≫ f')).obj N :=
  (derivedPushforwardCompIso f'' h).hom.app N ≫
    eqToHom (derivedPushforward_obj_eq sq.symm N)

/-- **The derived base change map, transposed under `Lh^* ⊣ Rh_*`.** For a commutative square
`h' ≫ f' = f'' ≫ h` of ringed spaces, the transpose of the derived base change map
`Lh^* Rf'_* K ⟶ Rf''_* Lh'^* K` under the derived adjunction along `h`, read through the
composition isomorphism for `f'' ≫ h`, is `Rf'_*` of the derived unit along `h'`, read through
the composition isomorphism for `h' ≫ f'`. -/
theorem derivedAdjunction_homEquiv_derivedBaseChangeMap
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))) :
    (derivedAdjunction h).homEquiv _ _ (derivedBaseChangeMap h' f'' f' h sq K) ≫
        pushforwardCompTransport h' f'' f' h sq ((derivedPullback h').obj K) =
      (derivedPushforward f').map ((derivedAdjunction h').unit.app K) ≫
        (derivedPushforwardCompIso h' f').hom.app ((derivedPullback h').obj K) := by
  refine TransposeMate.homEquiv_derivedBaseChangeMap (derivedAdjunction h)
    (derivedAdjunction f') (derivedAdjunction f'') (derivedAdjunction h')
    (derivedAdjunction (h' ≫ f'))
    (derivedPullbackCompIsoLeft h' f'' f' h sq) (derivedPullbackCompIsoCanonical h' f')
    (pushforwardCompTransport h' f'' f' h sq)
    (fun N => (derivedPushforwardCompIso h' f').hom.app N) ?_
    (fun M N φ => derivedAdjunction_comp_homEquiv h' f' M N φ) K _
    (derivedBaseChangeMap_eq h' f'' f' h sq K)
  intro M N φ
  have eM := derivedPullback_obj_eq sq.symm M
  have eN := derivedPushforward_obj_eq sq.symm N
  have hL : (derivedPullbackCompIsoLeft h' f'' f' h sq).hom.app M ≫ φ =
      (derivedPullbackCompIsoCanonical f'' h).hom.app M ≫ (eqToHom eM ≫ φ) := by
    rw [derivedPullbackCompIsoLeft_hom_app_eqToHom h' f'' f' h sq M eM, Category.assoc]
  have h1 := derivedAdjunction_comp_homEquiv f'' h M N (eqToHom eM ≫ φ)
  have h2 := derivedAdjunction_homEquiv_eqToHom sq.symm M N eM eN.symm φ
  have h3 : (derivedAdjunction (h' ≫ f')).homEquiv M N φ ≫ eqToHom eN.symm ≫ eqToHom eN =
      (derivedAdjunction (h' ≫ f')).homEquiv M N φ := by
    rw [eqToHom_trans, eqToHom_refl, Category.comp_id]
  refine (congrArg (fun x => (derivedAdjunction h).homEquiv _ _
    ((derivedAdjunction f'').homEquiv _ _ x) ≫ pushforwardCompTransport h' f'' f' h sq N) hL).trans
    ?_
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ eqToHom eN) h1)).trans ?_
  refine (congrArg (· ≫ eqToHom eN) h2).trans ?_
  exact (Category.assoc _ _ _).trans h3

end

end Stacks.Cohomology.DerivedBaseChange
