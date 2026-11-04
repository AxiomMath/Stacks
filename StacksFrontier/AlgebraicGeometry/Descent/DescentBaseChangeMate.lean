module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMateComp
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.DescentData
public import StacksFrontier.CategoryTheory.Sites.Descent.SingletonCoalgebra

/-!
# The two base-change morphisms of a self-pullback square agree

Let `f : X ⟶ S` be a morphism of schemes and let `sq` be a chosen pullback of `f` with itself,
with projections `p₁, p₂`. There are two morphisms of functors on sheaves of modules
`f^* f_* ⟶ (p₁)_* (p₂)^*`, built from 2-cells in conjugate orientations:

* `CategoryTheory.Pseudofunctor.descentBaseChange` is the forward mate, under the adjunctions
  `f^* ⊣ f_*` and `(p₁)^* ⊣ (p₁)_*`, of the comparison `(p₁)^* f^* ≅ (p₂)^* f^*` of two
  composites of inverse image functors;
* `Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` is the backward mate, under
  `(p₂)^* ⊣ (p₂)_*` and `f^* ⊣ f_*`, of the comparison `f_* (p₂)_* ≅ f_* (p₁)_*` of two
  composites of direct image functors.

This file proves that they are equal, and deduces that `descentBaseChange` is an isomorphism at
a quasi-coherent module over the spectrum of a pushout square of commutative rings.

## Main results

* `Stacks.AlgebraicGeometry.ModuleDescentBaseChange.descentBaseChange_eq_baseChangeNatTrans`:
  the two base-change morphisms of a chosen pullback of `f` with itself agree.
* `Stacks.AlgebraicGeometry.ModuleDescentBaseChange.conjugateEquiv_descentSquare`: the
  conjugate of the inverse-image comparison is the direct-image comparison.
* `Stacks.AlgebraicGeometry.ModuleDescentBaseChange.isIso_descentBaseChange_specMap` and
  `Stacks.AlgebraicGeometry.ModuleDescentBaseChange.mono_descentBaseChange_specMap`: for a
  pushout square of commutative rings, `descentBaseChange` is an isomorphism, hence a
  monomorphism, at a quasi-coherent module.

## Implementation notes

The two sides of `descentSquare_eq` have definitionally but not syntactically equal types,
`(modulePullbackPseudofunctor.map f.op.toLoc).toFunctor` against
`AlgebraicGeometry.Scheme.Modules.pullback f`. A `rw` inside the composite re-elaborates the
rewritten subterm at `implicit` transparency, where it is no longer type-correct, so its last
step is an explicit `congrArg`.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ModuleDescentBaseChange

variable {X Y Z S : Scheme.{u}}

/-- The functor a prelax functor induces on a hom-category acts on objects as the prelax
functor does on 1-morphisms. -/
lemma mapFunctor_obj {B : Type*} [Bicategory B] {C : Type*} [Bicategory C]
    (F : PrelaxFunctor B C) {a b : B} (x : a ⟶ b) :
    (F.mapFunctor a b).obj x = F.map x := rfl

/-- The compositor of the inverse-image pseudofunctor is the inverse of
`AlgebraicGeometry.Scheme.Modules.pullbackComp`. -/
lemma mapComp_hom_toNatTrans (a : Z ⟶ Y) (b : Y ⟶ X) :
    (modulePullbackPseudofunctor.mapComp b.op.toLoc a.op.toLoc).hom.toNatTrans =
      (Scheme.Modules.pullbackComp a b).inv := rfl

/-- The inverse of the compositor of the inverse-image pseudofunctor is
`AlgebraicGeometry.Scheme.Modules.pullbackComp`. -/
lemma mapComp_inv_toNatTrans (a : Z ⟶ Y) (b : Y ⟶ X) :
    (modulePullbackPseudofunctor.mapComp b.op.toLoc a.op.toLoc).inv.toNatTrans =
      (Scheme.Modules.pullbackComp a b).hom := rfl

/-- The inverse-image pseudofunctor sends the 2-cell of an equality of morphisms of schemes to
the transport along the corresponding equality of inverse-image functors. -/
lemma map₂_eqToIso_hom_toNatTrans {a b : LocallyDiscrete Scheme.{u}ᵒᵖ} {x y : a ⟶ b}
    (h : x = y) :
    (modulePullbackPseudofunctor.map₂ (eqToIso h).hom).toNatTrans = eqToHom (by rw [h]) := by
  rw [eqToIso.hom, PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.eqToHom_toNatTrans]

variable {f : X ⟶ S}

/-- Over a chosen pullback of `f` with itself, the canonical comparison
`(p₁)^* f^* ≅ (p₂)^* f^*` is the composite of the two instances of
`AlgebraicGeometry.Scheme.Modules.pullbackComp` with the transport along the equality
`p₁ ≫ f = p₂ ≫ f`. -/
lemma descentSquare_eq (sq : ChosenPullback f f) :
    Pseudofunctor.descentSquare (F := modulePullbackPseudofunctor) sq =
      (Scheme.Modules.pullbackComp sq.p₁ f).hom ≫
        eqToHom (by rw [sq.hp₁, sq.hp₂]) ≫ (Scheme.Modules.pullbackComp sq.p₂ f).inv := by
  obtain ⟨P, p₁, p₂, cond, isLim, p, hp₁⟩ := sq
  subst hp₁
  simp only [Pseudofunctor.descentSquare, op_comp, Quiver.Hom.comp_toLoc,
    Cat.Hom.comp_toFunctor, Pseudofunctor.descentPullbackIso₁, Pseudofunctor.mapComp',
    Cat.Hom.toNatIso_inv, Iso.trans_inv, Functor.mapIso_inv, Discrete.functor_map_id,
    mapFunctor_obj, Category.comp_id, mapComp_inv_toNatTrans,
    Pseudofunctor.descentPullbackIso₂, Cat.Hom.toNatIso_hom, Iso.trans_hom,
    Functor.mapIso_hom, PrelaxFunctor.mapFunctor_map, Cat.Hom.toNatTrans_comp,
    mapComp_hom_toNatTrans]
  exact congrArg (fun z => (Scheme.Modules.pullbackComp p₁ f).hom ≫ z ≫
    (Scheme.Modules.pullbackComp p₂ f).inv) (map₂_eqToIso_hom_toNatTrans _)

/-- Direct images along a morphism and along itself are compared by the identity. -/
lemma pushforwardCongr_rfl_hom (g : X ⟶ Y) :
    (Scheme.Modules.pushforwardCongr (rfl : g = g)).hom = 𝟙 _ := by
  ext M U
  simp

/-- The conjugate of the transport between inverse images along equal morphisms is the
comparison of the direct images along them. -/
lemma conjugateEquiv_eqToHom {g₁ g₂ : X ⟶ Y} (h : g₁ = g₂) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction g₁)
        (Scheme.Modules.pullbackPushforwardAdjunction g₂) (eqToHom (by rw [h])) =
      (Scheme.Modules.pushforwardCongr h).hom := by
  subst h
  rw [eqToHom_refl, CategoryTheory.conjugateEquiv_id, pushforwardCongr_rfl_hom]

/-- The conjugate, under the two composite pullback–pushforward adjunctions, of the comparison
`(p₁)^* f^* ≅ (p₂)^* f^*` of inverse images over a chosen pullback of `f` with itself is the
comparison `f_* (p₂)_* ≅ f_* (p₁)_*` of the corresponding direct images. -/
lemma conjugateEquiv_descentSquare (sq : ChosenPullback f f) :
    conjugateEquiv
        ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
          (Scheme.Modules.pullbackPushforwardAdjunction sq.p₂))
        ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
          (Scheme.Modules.pullbackPushforwardAdjunction sq.p₁))
        (Pseudofunctor.descentSquare (F := modulePullbackPseudofunctor) sq) =
      (AffinePushforward.pushforwardSquareIso (g' := sq.p₂) (f := f) (f' := sq.p₁) (g := f)
        (sq.hp₂.trans sq.hp₁.symm)).hom := by
  refine Eq.trans (congrArg (fun z => conjugateEquiv _ _ z) (descentSquare_eq sq)) ?_
  rw [← Category.assoc,
    ← conjugateEquiv_comp _ (Scheme.Modules.pullbackPushforwardAdjunction (sq.p₂ ≫ f)) _,
    ← conjugateEquiv_comp _ (Scheme.Modules.pullbackPushforwardAdjunction (sq.p₁ ≫ f)) _,
    Scheme.Modules.conjugateEquiv_pullbackComp_inv,
    conjugateEquiv_eqToHom (sq.hp₂.trans sq.hp₁.symm),
    Stacks.ModuleSkyscraper.conjugateEquiv_pullbackComp_hom]
  rfl

/-- For a chosen pullback of `f` with itself, the forward mate of the comparison of inverse
images, which is the base-change morphism attached to the descent datum of a one-element family,
is the backward mate of the comparison of direct images, which is the base-change morphism of the
commutative square. -/
theorem descentBaseChange_eq_baseChangeNatTrans (sq : ChosenPullback f f) :
    Pseudofunctor.descentBaseChange (F := modulePullbackPseudofunctor) sq
        (Scheme.Modules.pullbackPushforwardAdjunction f)
        (Scheme.Modules.pullbackPushforwardAdjunction sq.p₁) =
      AffinePushforward.baseChangeNatTrans (g' := sq.p₂) (f := f) (f' := sq.p₁) (g := f)
        (sq.hp₂.trans sq.hp₁.symm) := by
  rw [AffinePushforward.baseChangeNatTrans_eq, ← conjugateEquiv_descentSquare sq,
    ← iterated_mateEquiv_conjugateEquiv
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction sq.p₁)
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction sq.p₂)
      (Pseudofunctor.descentSquare (F := modulePullbackPseudofunctor) sq)]
  exact (Equiv.symm_apply_apply _ _).symm

section Affine

variable {A B P : CommRingCat.{u}} {φ : A ⟶ B} {ψ₁ ψ₂ : B ⟶ P}

/-- The chosen pullback of `Spec φ` with itself provided by a pushout square of commutative
rings. -/
noncomputable def specChosenPullback (hpc : IsPushout φ φ ψ₁ ψ₂) :
    ChosenPullback (Spec.map φ) (Spec.map φ) where
  pullback := Spec P
  p₁ := Spec.map ψ₁
  p₂ := Spec.map ψ₂
  condition := by rw [← Spec.map_comp, ← Spec.map_comp, hpc.w]
  isLimit := (isPullback_SpecMap_of_isPushout φ φ ψ₁ ψ₂ hpc).isLimit

/-- For a pushout square of commutative rings and a quasi-coherent module `M` on `Spec B`, the
base-change morphism `f^* f_* M ⟶ (p₁)_* (p₂)^* M` of `Spec φ` and its chosen self-pullback
`Spec P` is an isomorphism. -/
theorem isIso_descentBaseChange_specMap (hpc : IsPushout φ φ ψ₁ ψ₂)
    (hp : MilnorPatching.IsPushoutSquare φ.hom φ.hom ψ₂.hom ψ₁.hom
      (by rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hpc.w]))
    (M : (Spec B).Modules) [M.IsQuasicoherent] :
    IsIso ((Pseudofunctor.descentBaseChange (F := modulePullbackPseudofunctor)
      (specChosenPullback hpc)
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))
      (Scheme.Modules.pullbackPushforwardAdjunction (specChosenPullback hpc).p₁)).app M) := by
  rw [descentBaseChange_eq_baseChangeNatTrans]
  exact ModuleBaseChange.isIso_baseChangeNatTrans_specMap hpc.w.symm hp M

/-- For a pushout square of commutative rings and a quasi-coherent module `N` on `Spec A`, the
base-change morphism of `Spec φ` and its chosen self-pullback `Spec P` is a monomorphism at the
inverse image of `N` along `Spec φ`. -/
theorem mono_descentBaseChange_specMap (hpc : IsPushout φ φ ψ₁ ψ₂)
    (hp : MilnorPatching.IsPushoutSquare φ.hom φ.hom ψ₂.hom ψ₁.hom
      (by rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hpc.w]))
    (N : (Spec A).Modules) [N.IsQuasicoherent] :
    Mono ((Pseudofunctor.descentBaseChange (F := modulePullbackPseudofunctor)
      (specChosenPullback hpc)
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))
      (Scheme.Modules.pullbackPushforwardAdjunction (specChosenPullback hpc).p₁)).app
        ((Scheme.Modules.pullback (Spec.map φ)).obj N)) := by
  have := Stacks.Descent.isQuasicoherent_pullback_specMap φ N
  have := isIso_descentBaseChange_specMap hpc hp ((Scheme.Modules.pullback (Spec.map φ)).obj N)
  infer_instance

end Affine

end Stacks.AlgebraicGeometry.ModuleDescentBaseChange

end
