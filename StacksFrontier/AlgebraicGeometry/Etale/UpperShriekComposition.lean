module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompIso
public import StacksFrontier.AlgebraicGeometry.Etale.UpperShriekQuasiFinite
public import StacksFrontier.CategoryTheory.Comma.Over.PullbackCoherence

import StacksCore.Tactic.StacksAttribute

/-!
# Composition of upper shriek for locally quasi-finite morphisms

For composable locally quasi-finite morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of a big étale site,
the upper shriek functors `f^!` on abelian étale sheaves are the right adjoints of the direct
images with compact support `f_!` (Stacks 0F59). The canonical isomorphism
`(g ∘ f)_! ≅ g_! ∘ f_!` of Stacks 0F6T therefore has a conjugate isomorphism
`(g ∘ f)^! ≅ f^! ∘ g^!` between the right adjoints, and the associativity of the former,
property (4) of Stacks 0F6T, passes to the latter. This is Stacks 0F5B.

## Main definitions

* `AlgebraicGeometry.SmallEtale.upperShriekCompIso` — the isomorphism `(g ∘ f)^! ≅ f^! ∘ g^!`.

## Main results

* `AlgebraicGeometry.SmallEtale.upperShriekCompIso_assoc` — the associativity square for three
  locally quasi-finite morphisms.

## Implementation notes

The source states the existence of the isomorphism for separated morphisms `f` and `g`. The
isomorphism of Stacks 0F6T it is conjugate to exists for all locally quasi-finite morphisms, and
so does the one here; separatedness is not assumed. (It could not be, for the étale case of
Stacks 0F5C, where the morphisms are only étale.) In the separated case the isomorphism of
Stacks 0F6T agrees with the one of Stacks 0F50, by part (1) of Stacks 0F6T.

A locally quasi-finite morphism in the sense of the Stacks project is locally of finite type,
whereas Mathlib's `AlgebraicGeometry.LocallyQuasiFinite` does not include finite type; both
instances are assumed, as for `AlgebraicGeometry.SmallEtale.fUpperShriekFunctor`.

The composites `(f ≫ g) ≫ h` and `f ≫ g ≫ h` are equal but not syntactically so, and the
associativity square carries one `eqToHom` between their upper shriek functors, exactly as
property (4) of Stacks 0F6T carries one between their direct images with compact support.

## References

* [Stacks Project, Tag 0F5B](https://stacks.math.columbia.edu/tag/0F5B)
* [Stacks Project, Tag 0F6T](https://stacks.math.columbia.edu/tag/0F6T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

universe u v

namespace AlgebraicGeometry.SmallEtale

section Congr

variable (B : BigEtaleSite.{u}) {X T : B.Scheme} {k₁ k₂ : X ⟶ T}
  [LocallyOfFiniteType (B.inclusion.map k₁)] [LocallyQuasiFinite (B.inclusion.map k₁)]
  [LocallyOfFiniteType (B.inclusion.map k₂)] [LocallyQuasiFinite (B.inclusion.map k₂)]

/-- Equal morphisms have equal upper shriek functors. -/
public theorem fUpperShriekFunctor_congr (h : k₁ = k₂) :
    fUpperShriekFunctor.{u, v} B k₁ = fUpperShriekFunctor.{u, v} B k₂ := by
  subst h
  rfl

/-- The identification of the upper shriek functors of equal morphisms is conjugate to the
identification of their direct images with compact support. -/
public theorem conjugateEquiv_eqToHom_fShriekFunctor (h : k₁ = k₂) :
    conjugateEquiv (fShriekAdjunction.{u, v} B k₁) (fShriekAdjunction.{u, v} B k₂)
        (eqToHom (fShriekFunctor_congr.{u, v} B h.symm)) =
      eqToHom (fUpperShriekFunctor_congr.{u, v} B h) := by
  subst h
  exact conjugateEquiv_id _

end Congr

section Comp

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]

/-- **Stacks 0F5B, the canonical isomorphism.** For composable locally quasi-finite morphisms
`f : X ⟶ Y` and `g : Y ⟶ Z` there is a canonical isomorphism `(g ∘ f)^! ≅ f^! ∘ g^!` of upper
shriek functors on abelian étale sheaves: the conjugate, under the adjunctions
`(g ∘ f)_! ⊣ (g ∘ f)^!` and `g_! ∘ f_! ⊣ f^! ∘ g^!`, of the canonical isomorphism
`(g ∘ f)_! ≅ g_! ∘ f_!` of Stacks 0F6T. The source assumes `f` and `g` separated; that
hypothesis is not needed. -/
@[stacks 0F5B "the canonical isomorphism (g ∘ f)^! ≅ f^! ∘ g^!"]
public def upperShriekCompIso :
    fUpperShriekFunctor.{u, v} B (f ≫ g) ≅
      fUpperShriekFunctor.{u, v} B g ⋙ fUpperShriekFunctor.{u, v} B f :=
  conjugateIsoEquiv (fShriekAdjunction.{u, v} B (f ≫ g))
    ((fShriekAdjunction.{u, v} B f).comp (fShriekAdjunction.{u, v} B g))
    (fShriekCompIso.{u, v} B f g).symm

/-- The isomorphism `(g ∘ f)^! ≅ f^! ∘ g^!` is the mate of the inverse of the isomorphism
`(g ∘ f)_! ≅ g_! ∘ f_!` of Stacks 0F6T. -/
public theorem upperShriekCompIso_hom :
    (upperShriekCompIso.{u, v} B f g).hom =
      Adjunction.rightAdjointCompNatTrans (fShriekAdjunction.{u, v} B f)
        (fShriekAdjunction.{u, v} B g) (fShriekAdjunction.{u, v} B (f ≫ g))
        (fShriekCompIso.{u, v} B f g).inv :=
  rfl

end Comp

section Assoc

variable (B : BigEtaleSite.{u}) {X Y Z T : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
  [LocallyOfFiniteType (B.inclusion.map h)] [LocallyQuasiFinite (B.inclusion.map h)]

/-- Property (4) of Stacks 0F6T, for the inverses of the composition isomorphisms and in the
shape of a cocycle law for compositors `L₀₁ ⋙ L₁₂ ⟶ L₀₂`. -/
theorem fShriekCompIso_inv_assoc :
    whiskerRight (fShriekCompIso.{u, v} B f g).inv (fShriekFunctor.{u, v} B h) ≫
        (fShriekCompIso.{u, v} B (f ≫ g) h).inv ≫
          eqToHom (fShriekFunctor_congr.{u, v} B (Category.assoc f g h)) =
      (associator (fShriekFunctor.{u, v} B f) (fShriekFunctor.{u, v} B g)
          (fShriekFunctor.{u, v} B h)).hom ≫
        whiskerLeft (fShriekFunctor.{u, v} B f) (fShriekCompIso.{u, v} B g h).inv ≫
          (fShriekCompIso.{u, v} B f (g ≫ h)).inv := by
  have e : (eqToIso (fShriekFunctor_congr.{u, v} B (Category.assoc f g h)) ≪≫
        fShriekCompIso.{u, v} B f (g ≫ h) ≪≫
          isoWhiskerLeft (fShriekFunctor.{u, v} B f) (fShriekCompIso.{u, v} B g h)).inv =
      (fShriekCompIso.{u, v} B (f ≫ g) h ≪≫
        isoWhiskerRight (fShriekCompIso.{u, v} B f g) (fShriekFunctor.{u, v} B h)).inv :=
    congrArg Iso.inv (Iso.ext (fShriekCompIso_assoc.{u, v} B f g h))
  ext F : 2
  have eF := NatTrans.congr_app e F
  simp only [Iso.trans_inv, eqToIso.inv, isoWhiskerLeft_inv, isoWhiskerRight_inv,
    NatTrans.comp_app, eqToHom_app] at eF
  simp only [NatTrans.comp_app, associator_hom_app, Category.id_comp, ← Category.assoc, ← eF]
  simp

/-- **Stacks 0F5B, the associativity square.** For locally quasi-finite morphisms
`f : X ⟶ Y`, `g : Y ⟶ Z` and `h : Z ⟶ T` the two isomorphisms
`(h ∘ g ∘ f)^! ≅ f^! ∘ g^! ∘ h^!` built from the composition isomorphisms of upper shriek agree:
`(h ∘ g ∘ f)^! → f^! ∘ (h ∘ g)^! → f^! ∘ g^! ∘ h^!` equals
`(h ∘ g ∘ f)^! → (g ∘ f)^! ∘ h^! → f^! ∘ g^! ∘ h^!`. The identification
`(h ∘ (g ∘ f))^! = ((h ∘ g) ∘ f)^!` along the associativity of composition, and the
associator of composition of functors, are written out. The source assumes `f` and `g`
separated; that hypothesis is not needed. -/
@[stacks 0F5B "the associativity square"]
public theorem upperShriekCompIso_assoc :
    eqToHom (fUpperShriekFunctor_congr.{u, v} B (Category.assoc f g h).symm) ≫
        (upperShriekCompIso.{u, v} B (f ≫ g) h).hom ≫
          whiskerLeft (fUpperShriekFunctor.{u, v} B h) (upperShriekCompIso.{u, v} B f g).hom =
      (upperShriekCompIso.{u, v} B f (g ≫ h)).hom ≫
        whiskerRight (upperShriekCompIso.{u, v} B g h).hom (fUpperShriekFunctor.{u, v} B f) ≫
          (associator (fUpperShriekFunctor.{u, v} B h) (fUpperShriekFunctor.{u, v} B g)
            (fUpperShriekFunctor.{u, v} B f)).hom := by
  have key := Adjunction.rightAdjointCompNatTrans_assoc (fShriekAdjunction.{u, v} B f)
    (fShriekAdjunction.{u, v} B g) (fShriekAdjunction.{u, v} B h)
    (fShriekAdjunction.{u, v} B (f ≫ g)) (fShriekAdjunction.{u, v} B (g ≫ h))
    (fShriekAdjunction.{u, v} B (f ≫ g ≫ h))
    (fShriekCompIso.{u, v} B f g).inv (fShriekCompIso.{u, v} B g h).inv
    (fShriekCompIso.{u, v} B f (g ≫ h)).inv
    ((fShriekCompIso.{u, v} B (f ≫ g) h).inv ≫
      eqToHom (fShriekFunctor_congr.{u, v} B (Category.assoc f g h)))
    (fShriekCompIso_inv_assoc.{u, v} B f g h)
  refine Eq.trans ?_ key
  rw [Adjunction.rightAdjointCompNatTrans, ← conjugateEquiv_comp _
    (fShriekAdjunction.{u, v} B ((f ≫ g) ≫ h)),
    conjugateEquiv_eqToHom_fShriekFunctor.{u, v} B (Category.assoc f g h).symm]
  rfl

end Assoc

end AlgebraicGeometry.SmallEtale

end
