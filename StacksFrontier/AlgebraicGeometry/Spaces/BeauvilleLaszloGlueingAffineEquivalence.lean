module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffineEssSurj

/-!
# Fullness of the Beauville--Laszlo glueing functor on affines (Stacks 0F9Q)

Fix a Beauville--Laszlo glueing pair `(R → R', f)`, write `X = Spec R`, `U = Spec R_f`,
`X' = Spec R'` and `U' = Spec R'_f`, and let `G` be a glueing functor of Stacks 0F9N for the
resulting square. Stacks 0F9Q asserts that `G` restricts to an *equivalence* between the affine
algebraic spaces over `X` which are glueable for the pair and the cartesian glueing triples with
affine components. Faithfulness is Stacks 0F9S
(`BeauvilleLaszlo.Space.faithful_comp_glueingFunctor`) and essential surjectivity is
`BeauvilleLaszlo.Space.essSurj_affineGlueableRestriction`; this module proves the remaining
half, fullness, for a glueable affine source.

## Main results

* `BeauvilleLaszlo.Space.functor_map_route_eq`: the two routes of the square agree on a morphism
  of glueing triples.
* `BeauvilleLaszlo.Space.twoStepBaseChangeIso_inv_comp_kappa` and
  `BeauvilleLaszlo.Space.twoStepBaseChangeIso_inv_section_eq`: the comparison of the two
  presentations of the base change of `Spec A` to `U'` is the cast between the two routes.
* `BeauvilleLaszlo.Space.algHom_comp_eq_of_route`: the compatibility over `R'_f` of the two
  component algebra maps of a morphism of triples.
* `BeauvilleLaszlo.Space.exists_algHom_of_route`: the algebra map glued out of those two
  components.
* `BeauvilleLaszlo.Space.surjective_functor_map_specSpace`: **fullness for representable
  sources.** Every morphism between the triples of two affine algebraic spaces over `Spec R`,
  the source glueable, comes from a morphism of the spaces.

## Implementation notes

The cast between the two iterated base changes is kept an *opaque* morphism in every statement
which mentions it, exactly as in
`StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffineGluedTriple`: instantiating it
with `eqToHom` of a named equality asks the kernel for the weak head normal form of an `Eq.rec`
whose two sides are not definitionally equal, and that reduction does not terminate. The cast
enters only through `BeauvilleLaszlo.Space.exists_cast_of_square`, which supplies it by
`obtain`.

For the same reason the passage from an equality of tautological points to an equality of
morphisms goes through `BeauvilleLaszlo.Space.hom_ext_of_section_comp_right`, whose three
morphisms are abstract.

The second base-change square of a tensor product is obtained from the two first-step squares by
pasting (`CategoryTheory.IsPushout.of_left`), and the two canonical maps of the
Beauville--Laszlo sequence are identified with the corresponding tensor maps by
`BeauvilleLaszlo.Space.tensorMap_eq_baseChangeToAway` and
`tensorMap_eq_localizedBaseChangeToAway`.

## References

* [Stacks Project, Tag 0BP2](https://stacks.math.columbia.edu/tag/0BP2)
* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
* [Stacks Project, Tag 0F9S](https://stacks.math.columbia.edu/tag/0F9S)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

universe u

namespace BeauvilleLaszlo.Space

section Squares

/-- Conjugating a morphism `m` by the maps `eY`, `eZ` (the first having a left inverse `eY'`)
and applying `K` carries a square for `K.map m` to the corresponding square for the conjugate. -/
private theorem map_hom_comp_map_conj_eq {C D : Type*} [Category C] [Category D] (K : C ⥤ D)
    {P Q : D} {Y Y' Z Z' : C} {eY : Y ⟶ Y'} {eY' : Y' ⟶ Y} (eZ : Z ⟶ Z') (hY : eY ≫ eY' = 𝟙 Y)
    {s : P ⟶ K.obj Y} {m : Y ⟶ Z} {t : Q ⟶ K.obj Z} {α : P ⟶ Q}
    (hw : s ≫ K.map m = α ≫ t) :
    (s ≫ K.map eY) ≫ K.map (eY' ≫ m ≫ eZ) = α ≫ t ≫ K.map eZ := by
  rw [Category.assoc, ← K.map_comp, ← Category.assoc eY, hY, Category.id_comp, K.map_comp,
    ← Category.assoc, hw, Category.assoc]

variable (B : BigFppfSite.{u}) (U' U X' X : Scheme.{u}) (hU' : B.Contains U')
  (hU : B.Contains U) (hX' : B.Contains X') (hX : B.Contains X)
  (gU : B.obj hU' ⟶ B.obj hU) (gX' : B.obj hU' ⟶ B.obj hX')
  (jU : B.obj hU ⟶ B.obj hX) (jX' : B.obj hX' ⟶ B.obj hX)
  {hcomm : gU ≫ jU = gX' ≫ jX'}
  (G : GlueingFunctorSpec B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm)

/-- **The two routes of the Beauville--Laszlo square agree on a morphism of glueing triples.**
For a morphism `β` of the triples of two algebraic spaces over `X`, the base change to `U'` of
its `U`-component, read through the identification of that component with the base change along
`U → X`, is carried by the canonical cast to the base change of its `X'`-component. The middle
component of `β` is eliminated between the two squares it satisfies, which is what
`BeauvilleLaszlo.Space.functor_obj_toU_comp_eq_toX'_comp` puts in cancellable form. -/
theorem functor_map_route_eq (Y Z : AlgebraicSpaces B X hX)
    (β : G.functor.obj Y ⟶ G.functor.obj Z) :
    (baseChange B U' U hU' hU gU).map
          (G.overUIso.inv.app Y ≫ β.hom.left.right ≫ G.overUIso.hom.app Z) ≫
        eqToHom (baseChange_square_obj_eq B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm Z) =
      eqToHom (baseChange_square_obj_eq B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm Y) ≫
        (baseChange B U' X' hU' hX' gX').map
          (G.overX'Iso.inv.app Y ≫ β.hom.right ≫ G.overX'Iso.hom.app Z) := by
  have : IsIso (G.functor.obj Y).1.left.hom := (G.functor.obj Y).2.1
  have hw1 : (G.functor.obj Y).1.left.hom ≫
      (baseChange B U' U hU' hU gU).map β.hom.left.right =
      β.hom.left.left ≫ (G.functor.obj Z).1.left.hom := β.hom.left.w.symm
  have hw2 : (G.functor.obj Y).1.hom ≫
      (baseChange B U' X' hU' hX' gX').map β.hom.right =
      β.hom.left.left ≫ (G.functor.obj Z).1.hom := β.hom.w.symm
  have hL := map_hom_comp_map_conj_eq (baseChange B U' U hU' hU gU)
    (G.overUIso.hom.app Z) (G.overUIso.hom_inv_id_app Y) hw1
  have hR := map_hom_comp_map_conj_eq (baseChange B U' X' hU' hX' gX')
    (G.overX'Iso.hom.app Z) (G.overX'Iso.hom_inv_id_app Y) hw2
  refine (cancel_epi ((G.functor.obj Y).1.left.hom ≫
    (baseChange B U' U hU' hU gU).map (G.overUIso.hom.app Y))).mp ?_
  rw [← Category.assoc, hL, Category.assoc, Category.assoc,
    functor_obj_toU_comp_eq_toX'_comp B U' U X' X hU' hU hX' hX gU gX' jU jX' G Z, ← hR,
    ← functor_obj_toU_comp_eq_toX'_comp B U' U X' X hU' hU hX' hX gU gX' jU jX' G Y]
  simp only [Category.assoc]

end Squares


section Abstract

/-- **A composite out of a representable algebraic space agrees with a morphism as soon as their
tautological points do.** This is `BeauvilleLaszlo.Space.hom_ext_of_section_comp` for a
composite against a single morphism. All three morphisms and both objects are abstract, which is
what makes it usable: identifying the tautological point of a composite of a pair of
presentations of an iterated base change definitionally asks the kernel to reduce the
base-change functors of the site, and that reduction costs eleven times the heartbeat budget. -/
theorem hom_ext_of_section_comp_right (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (V : BigFppfOver B S hS) {F H : AlgebraicSpaces B S hS}
    (a : schemeSpace V ⟶ F) (b : F ⟶ H) (c : schemeSpace V ⟶ H)
    (h : b.hom.app (Opposite.op V) (schemeSpacePointEquiv V F a) =
      schemeSpacePointEquiv V H c) :
    a ≫ b = c :=
  schemeSpace_point_ext ((schemeSpacePointEquiv_comp a b).trans h)

end Abstract

section Cast

variable {R S₁ S₂ T A A₁ A' D : Type u} [CommRing R] [CommRing S₁] [CommRing S₂] [CommRing T]
  [Algebra R S₁] [Algebra R S₂] [Algebra S₁ T] [Algebra S₂ T]
  [CommRing A] [CommRing A₁] [CommRing A'] [CommRing D]
  [Algebra R A] [Algebra S₁ A₁] [Algebra S₂ A'] [Algebra T D]
  (B : BigFppfSite.{u}) (hX : B.Contains (Spec (.of R)))
  (hU : B.Contains (Spec (.of S₁))) (hX' : B.Contains (Spec (.of S₂)))
  (hU' : B.Contains (Spec (.of T)))
  (hA : B.Contains (Spec (.of A))) (hA₁ : B.Contains (Spec (.of A₁)))
  (hA' : B.Contains (Spec (.of A'))) (hD : B.Contains (Spec (.of D)))

/-- **The cast between the two routes of the square carries the tautological point of one
presentation of the base change of `Spec A` to `Spec T` to that of the other.** Both sections
project to `Spec` of the common composite structure map `A → D`, by
`BeauvilleLaszlo.Space.twoStepBaseChangeIso_inv_app_id_left` on either side, and the cast does
not move the underlying morphism of schemes. -/
theorem twoStepBaseChangeIso_inv_section_eq
    (u₁ : A →+* A₁) (u₂ : A₁ →+* D) (v₁ : A →+* A') (v₂ : A' →+* D)
    (hp₁ : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R S₁)) (CommRingCat.ofHom u₁)
      (CommRingCat.ofHom (algebraMap S₁ A₁)))
    (hp₂ : IsPushout (CommRingCat.ofHom (algebraMap S₁ A₁))
      (CommRingCat.ofHom (algebraMap S₁ T)) (CommRingCat.ofHom u₂)
      (CommRingCat.ofHom (algebraMap T D)))
    (hp₃ : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R S₂)) (CommRingCat.ofHom v₁)
      (CommRingCat.ofHom (algebraMap S₂ A')))
    (hp₄ : IsPushout (CommRingCat.ofHom (algebraMap S₂ A'))
      (CommRingCat.ofHom (algebraMap S₂ T)) (CommRingCat.ofHom v₂)
      (CommRingCat.ofHom (algebraMap T D)))
    (hcomm : (AlgebraicGeometry.Space.specSite B hU hU').hom ≫
          (AlgebraicGeometry.Space.specSite B hX hU).hom =
        (AlgebraicGeometry.Space.specSite B hX' hU').hom ≫
          (AlgebraicGeometry.Space.specSite B hX hX').hom)
    (huv : u₂.comp u₁ = v₂.comp v₁)
    (p : (baseChange B (Spec (.of T)) (Spec (.of S₁)) hU' hU
          (AlgebraicGeometry.Space.specSite B hU hU').hom).obj
        ((baseChange B (Spec (.of S₁)) (Spec (.of R)) hU hX
          (AlgebraicGeometry.Space.specSite B hX hU).hom).obj (specSpace B hX hA)) =
      (baseChange B (Spec (.of T)) (Spec (.of S₂)) hU' hX'
          (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj
        ((baseChange B (Spec (.of S₂)) (Spec (.of R)) hX' hX
          (AlgebraicGeometry.Space.specSite B hX hX').hom).obj (specSpace B hX hA))) :
    (eqToHom p).hom.app (Opposite.op (AlgebraicGeometry.Space.specSite B hU' hD))
        (schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hU' hD) _
          (twoStepBaseChangeIso B hX hU hU' hA hA₁ hD u₁ u₂ hp₁ hp₂).inv) =
      schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hU' hD) _
          (twoStepBaseChangeIso B hX hX' hU' hA hA' hD v₁ v₂ hp₃ hp₄).inv := by
  refine ((schemeSpaceIso (AlgebraicGeometry.Space.specSite B hX hA)).app
      (Opposite.op ((CategoryTheory.Over.map
        (AlgebraicGeometry.Space.specSite B hX hX').hom).obj
        ((CategoryTheory.Over.map (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj
          (AlgebraicGeometry.Space.specSite B hU' hD))))).toEquiv.injective
    (Over.OverMorphism.ext
    (((eqToHom_baseChange_two_specSpace_app_left B (Spec (.of S₁)) (Spec (.of S₂))
        (Spec (.of T)) hX hU hX' hU' hA _ _ _ _ hcomm
        (AlgebraicGeometry.Space.specSite B hU' hD) p _).trans
      (twoStepBaseChangeIso_inv_app_id_left B hX hU hU' hA hA₁ hD u₁ u₂ hp₁ hp₂)).trans ?_))
  exact (congrArg (fun w ↦ (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom w)) :
      B.obj hD ⟶ B.obj hA)) huv).trans
    (twoStepBaseChangeIso_inv_app_id_left B hX hX' hU' hA hA' hD v₁ v₂ hp₃ hp₄).symm

/-- **The comparison of the two presentations of the base change of `Spec A` to `Spec T` is the
cast between the two routes.** The comparison `kappa` is abstract and its action on the
tautological point is the hypothesis: instantiating it with the cast itself is what the
kernel cannot reduce. -/
theorem twoStepBaseChangeIso_inv_comp_kappa
    (u₁ : A →+* A₁) (u₂ : A₁ →+* D) (v₁ : A →+* A') (v₂ : A' →+* D)
    (hp₁ : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R S₁)) (CommRingCat.ofHom u₁)
      (CommRingCat.ofHom (algebraMap S₁ A₁)))
    (hp₂ : IsPushout (CommRingCat.ofHom (algebraMap S₁ A₁))
      (CommRingCat.ofHom (algebraMap S₁ T)) (CommRingCat.ofHom u₂)
      (CommRingCat.ofHom (algebraMap T D)))
    (hp₃ : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R S₂)) (CommRingCat.ofHom v₁)
      (CommRingCat.ofHom (algebraMap S₂ A')))
    (hp₄ : IsPushout (CommRingCat.ofHom (algebraMap S₂ A'))
      (CommRingCat.ofHom (algebraMap S₂ T)) (CommRingCat.ofHom v₂)
      (CommRingCat.ofHom (algebraMap T D)))
    (kappa : (baseChange B (Spec (.of T)) (Spec (.of S₁)) hU' hU
          (AlgebraicGeometry.Space.specSite B hU hU').hom).obj
        ((baseChange B (Spec (.of S₁)) (Spec (.of R)) hU hX
          (AlgebraicGeometry.Space.specSite B hX hU).hom).obj (specSpace B hX hA)) ⟶
      (baseChange B (Spec (.of T)) (Spec (.of S₂)) hU' hX'
          (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj
        ((baseChange B (Spec (.of S₂)) (Spec (.of R)) hX' hX
          (AlgebraicGeometry.Space.specSite B hX hX').hom).obj (specSpace B hX hA)))
    (hsec : kappa.hom.app (Opposite.op (AlgebraicGeometry.Space.specSite B hU' hD))
          (schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hU' hD) _
          (twoStepBaseChangeIso B hX hU hU' hA hA₁ hD u₁ u₂ hp₁ hp₂).inv) =
        schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hU' hD) _
          (twoStepBaseChangeIso B hX hX' hU' hA hA' hD v₁ v₂ hp₃ hp₄).inv) :
    (twoStepBaseChangeIso B hX hU hU' hA hA₁ hD u₁ u₂ hp₁ hp₂).inv ≫ kappa =
      (twoStepBaseChangeIso B hX hX' hU' hA hA' hD v₁ v₂ hp₃ hp₄).inv :=
  hom_ext_of_section_comp_right B (Spec (.of T)) hU'
    (AlgebraicGeometry.Space.specSite B hU' hD)
    (twoStepBaseChangeIso B hX hU hU' hA hA₁ hD u₁ u₂ hp₁ hp₂).inv kappa
    (twoStepBaseChangeIso B hX hX' hU' hA hA' hD v₁ v₂ hp₃ hp₄).inv hsec

end Cast


section Compare

variable {R S₁ S₂ T A A₁ A' D C C₁ C' E : Type u} [CommRing R] [CommRing S₁] [CommRing S₂]
  [CommRing T] [Algebra R S₁] [Algebra R S₂] [Algebra S₁ T] [Algebra S₂ T]
  [CommRing A] [CommRing A₁] [CommRing A'] [CommRing D]
  [Algebra R A] [Algebra S₁ A₁] [Algebra S₂ A'] [Algebra T D]
  [CommRing C] [CommRing C₁] [CommRing C'] [CommRing E]
  [Algebra R C] [Algebra S₁ C₁] [Algebra S₂ C'] [Algebra T E]
  (B : BigFppfSite.{u}) (hX : B.Contains (Spec (.of R)))
  (hU : B.Contains (Spec (.of S₁))) (hX' : B.Contains (Spec (.of S₂)))
  (hU' : B.Contains (Spec (.of T)))
  (hA : B.Contains (Spec (.of A))) (hA₁ : B.Contains (Spec (.of A₁)))
  (hA' : B.Contains (Spec (.of A'))) (hD : B.Contains (Spec (.of D)))
  (hC : B.Contains (Spec (.of C))) (hC₁ : B.Contains (Spec (.of C₁)))
  (hC' : B.Contains (Spec (.of C'))) (hE : B.Contains (Spec (.of E)))

/-- **The two outer components of a morphism of triples induce the same morphism of the base
changes to `Spec T`**, once each is read through its own presentation. This is the route
equation `hroute` with the two casts replaced by the two presentations. -/
theorem twoStep_conj_eq_of_route
    (u₁ : A →+* A₁) (u₂ : A₁ →+* D) (v₁ : A →+* A') (v₂ : A' →+* D)
    (hp₁ : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R S₁)) (CommRingCat.ofHom u₁)
      (CommRingCat.ofHom (algebraMap S₁ A₁)))
    (hp₂ : IsPushout (CommRingCat.ofHom (algebraMap S₁ A₁))
      (CommRingCat.ofHom (algebraMap S₁ T)) (CommRingCat.ofHom u₂)
      (CommRingCat.ofHom (algebraMap T D)))
    (hp₃ : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R S₂)) (CommRingCat.ofHom v₁)
      (CommRingCat.ofHom (algebraMap S₂ A')))
    (hp₄ : IsPushout (CommRingCat.ofHom (algebraMap S₂ A'))
      (CommRingCat.ofHom (algebraMap S₂ T)) (CommRingCat.ofHom v₂)
      (CommRingCat.ofHom (algebraMap T D)))
    (w₁ : C →+* C₁) (w₂ : C₁ →+* E) (x₁ : C →+* C') (x₂ : C' →+* E)
    (hq₁ : IsPushout (CommRingCat.ofHom (algebraMap R C))
      (CommRingCat.ofHom (algebraMap R S₁)) (CommRingCat.ofHom w₁)
      (CommRingCat.ofHom (algebraMap S₁ C₁)))
    (hq₂ : IsPushout (CommRingCat.ofHom (algebraMap S₁ C₁))
      (CommRingCat.ofHom (algebraMap S₁ T)) (CommRingCat.ofHom w₂)
      (CommRingCat.ofHom (algebraMap T E)))
    (hq₃ : IsPushout (CommRingCat.ofHom (algebraMap R C))
      (CommRingCat.ofHom (algebraMap R S₂)) (CommRingCat.ofHom x₁)
      (CommRingCat.ofHom (algebraMap S₂ C')))
    (hq₄ : IsPushout (CommRingCat.ofHom (algebraMap S₂ C'))
      (CommRingCat.ofHom (algebraMap S₂ T)) (CommRingCat.ofHom x₂)
      (CommRingCat.ofHom (algebraMap T E)))
    (kappaA : (baseChange B (Spec (.of T)) (Spec (.of S₁)) hU' hU
          (AlgebraicGeometry.Space.specSite B hU hU').hom).obj
        ((baseChange B (Spec (.of S₁)) (Spec (.of R)) hU hX
          (AlgebraicGeometry.Space.specSite B hX hU).hom).obj (specSpace B hX hA)) ⟶
      (baseChange B (Spec (.of T)) (Spec (.of S₂)) hU' hX'
          (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj
        ((baseChange B (Spec (.of S₂)) (Spec (.of R)) hX' hX
          (AlgebraicGeometry.Space.specSite B hX hX').hom).obj (specSpace B hX hA)))
    (kappaC : (baseChange B (Spec (.of T)) (Spec (.of S₁)) hU' hU
          (AlgebraicGeometry.Space.specSite B hU hU').hom).obj
        ((baseChange B (Spec (.of S₁)) (Spec (.of R)) hU hX
          (AlgebraicGeometry.Space.specSite B hX hU).hom).obj (specSpace B hX hC)) ⟶
      (baseChange B (Spec (.of T)) (Spec (.of S₂)) hU' hX'
          (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj
        ((baseChange B (Spec (.of S₂)) (Spec (.of R)) hX' hX
          (AlgebraicGeometry.Space.specSite B hX hX').hom).obj (specSpace B hX hC)))
    (hsecA : kappaA.hom.app (Opposite.op (AlgebraicGeometry.Space.specSite B hU' hD))
          (schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hU' hD) _
          (twoStepBaseChangeIso B hX hU hU' hA hA₁ hD u₁ u₂ hp₁ hp₂).inv) =
        schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hU' hD) _
          (twoStepBaseChangeIso B hX hX' hU' hA hA' hD v₁ v₂ hp₃ hp₄).inv)
    (hsecC : kappaC.hom.app (Opposite.op (AlgebraicGeometry.Space.specSite B hU' hE))
          (schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hU' hE) _
          (twoStepBaseChangeIso B hX hU hU' hC hC₁ hE w₁ w₂ hq₁ hq₂).inv) =
        schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hU' hE) _
          (twoStepBaseChangeIso B hX hX' hU' hC hC' hE x₁ x₂ hq₃ hq₄).inv)
    (mU : (baseChange B (Spec (.of S₁)) (Spec (.of R)) hU hX
          (AlgebraicGeometry.Space.specSite B hX hU).hom).obj (specSpace B hX hA) ⟶
      (baseChange B (Spec (.of S₁)) (Spec (.of R)) hU hX
          (AlgebraicGeometry.Space.specSite B hX hU).hom).obj (specSpace B hX hC))
    (mX' : (baseChange B (Spec (.of S₂)) (Spec (.of R)) hX' hX
          (AlgebraicGeometry.Space.specSite B hX hX').hom).obj (specSpace B hX hA) ⟶
      (baseChange B (Spec (.of S₂)) (Spec (.of R)) hX' hX
          (AlgebraicGeometry.Space.specSite B hX hX').hom).obj (specSpace B hX hC))
    (hroute : (baseChange B (Spec (.of T)) (Spec (.of S₁)) hU' hU
          (AlgebraicGeometry.Space.specSite B hU hU').hom).map mU ≫ kappaC =
        kappaA ≫ (baseChange B (Spec (.of T)) (Spec (.of S₂)) hU' hX'
          (AlgebraicGeometry.Space.specSite B hX' hU').hom).map mX') :
    (twoStepBaseChangeIso B hX hU hU' hA hA₁ hD u₁ u₂ hp₁ hp₂).inv ≫
        (baseChange B (Spec (.of T)) (Spec (.of S₁)) hU' hU
          (AlgebraicGeometry.Space.specSite B hU hU').hom).map mU ≫
          (twoStepBaseChangeIso B hX hU hU' hC hC₁ hE w₁ w₂ hq₁ hq₂).hom =
      (twoStepBaseChangeIso B hX hX' hU' hA hA' hD v₁ v₂ hp₃ hp₄).inv ≫
        (baseChange B (Spec (.of T)) (Spec (.of S₂)) hU' hX'
          (AlgebraicGeometry.Space.specSite B hX' hU').hom).map mX' ≫
          (twoStepBaseChangeIso B hX hX' hU' hC hC' hE x₁ x₂ hq₃ hq₄).hom := by
  have hA2 := twoStepBaseChangeIso_inv_comp_kappa B hX hU hX' hU' hA hA₁ hA' hD
    u₁ u₂ v₁ v₂ hp₁ hp₂ hp₃ hp₄ kappaA hsecA
  have hC2 := twoStepBaseChangeIso_inv_comp_kappa B hX hU hX' hU' hC hC₁ hC' hE
    w₁ w₂ x₁ x₂ hq₁ hq₂ hq₃ hq₄ kappaC hsecC
  have hC4 : kappaC = (twoStepBaseChangeIso B hX hU hU' hC hC₁ hE w₁ w₂ hq₁ hq₂).hom ≫
      (twoStepBaseChangeIso B hX hX' hU' hC hC' hE x₁ x₂ hq₃ hq₄).inv := by
    rw [← hC2, Iso.hom_inv_id_assoc]
  have hC3 : kappaC ≫ (twoStepBaseChangeIso B hX hX' hU' hC hC' hE x₁ x₂ hq₃ hq₄).hom =
      (twoStepBaseChangeIso B hX hU hU' hC hC₁ hE w₁ w₂ hq₁ hq₂).hom := by
    rw [hC4, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hroute' := congrArg
    (fun t ↦ t ≫ (twoStepBaseChangeIso B hX hX' hU' hC hC' hE x₁ x₂ hq₃ hq₄).hom) hroute
  simp only [Category.assoc] at hroute'
  have hA2' := congrArg
    (fun t ↦ t ≫ (baseChange B (Spec (.of T)) (Spec (.of S₂)) hU' hX'
        (AlgebraicGeometry.Space.specSite B hX' hU').hom).map mX' ≫
      (twoStepBaseChangeIso B hX hX' hU' hC hC' hE x₁ x₂ hq₃ hq₄).hom) hA2
  simp only [Category.assoc] at hA2'
  rw [← hC3, hroute']
  exact hA2'


/-- **The base-change dictionary in two steps.** The algebra map attached to the base change of a
morphism of representable affine spaces to `Spec T`, read through the two-step identification,
is determined by the algebra map of its one-step conjugate through the second structure map. -/
theorem specSpaceAlgHomEquiv_twoStep_conj
    (u₁ : A →+* A₁) (u₂ : A₁ →+* D) (w₁ : C →+* C₁) (w₂ : C₁ →+* E)
    (hp₁ : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R S₁)) (CommRingCat.ofHom u₁)
      (CommRingCat.ofHom (algebraMap S₁ A₁)))
    (hp₂ : IsPushout (CommRingCat.ofHom (algebraMap S₁ A₁))
      (CommRingCat.ofHom (algebraMap S₁ T)) (CommRingCat.ofHom u₂)
      (CommRingCat.ofHom (algebraMap T D)))
    (hq₁ : IsPushout (CommRingCat.ofHom (algebraMap R C))
      (CommRingCat.ofHom (algebraMap R S₁)) (CommRingCat.ofHom w₁)
      (CommRingCat.ofHom (algebraMap S₁ C₁)))
    (hq₂ : IsPushout (CommRingCat.ofHom (algebraMap S₁ C₁))
      (CommRingCat.ofHom (algebraMap S₁ T)) (CommRingCat.ofHom w₂)
      (CommRingCat.ofHom (algebraMap T E)))
    (mU : (baseChange B (Spec (.of S₁)) (Spec (.of R)) hU hX
          (AlgebraicGeometry.Space.specSite B hX hU).hom).obj (specSpace B hX hA) ⟶
      (baseChange B (Spec (.of S₁)) (Spec (.of R)) hU hX
          (AlgebraicGeometry.Space.specSite B hX hU).hom).obj (specSpace B hX hC))
    (c : C₁) :
    specSpaceAlgHomEquiv B hU' hD hE
        ((twoStepBaseChangeIso B hX hU hU' hA hA₁ hD u₁ u₂ hp₁ hp₂).inv ≫
          (baseChange B (Spec (.of T)) (Spec (.of S₁)) hU' hU
            (AlgebraicGeometry.Space.specSite B hU hU').hom).map mU ≫
          (twoStepBaseChangeIso B hX hU hU' hC hC₁ hE w₁ w₂ hq₁ hq₂).hom) (w₂ c) =
      u₂ (specSpaceAlgHomEquiv B hU hA₁ hC₁
        ((specSpaceBaseChangeIso B hX hU u₁ hp₁ hA hA₁).inv ≫ mU ≫
          (specSpaceBaseChangeIso B hX hU w₁ hq₁ hC hC₁).hom) c) := by
  obtain ⟨k, hk⟩ : ∃ k, (specSpaceBaseChangeIso B hX hU u₁ hp₁ hA hA₁).inv ≫ mU ≫
      (specSpaceBaseChangeIso B hX hU w₁ hq₁ hC hC₁).hom =
      yonedaSpaceHom B (Spec (.of S₁)) hU k :=
    ⟨_, ((yonedaSpaceHomEquiv B (Spec (.of S₁)) hU
      (AlgebraicGeometry.Space.specSite B hU hA₁)
      (AlgebraicGeometry.Space.specSite B hU hC₁)).symm_apply_apply _).symm⟩
  have hm : mU = (specSpaceBaseChangeIso B hX hU u₁ hp₁ hA hA₁).hom ≫
      yonedaSpaceHom B (Spec (.of S₁)) hU k ≫
      (specSpaceBaseChangeIso B hX hU w₁ hq₁ hC hC₁).inv := by
    rw [← hk]
    simp
  have heq : (twoStepBaseChangeIso B hX hU hU' hA hA₁ hD u₁ u₂ hp₁ hp₂).inv ≫
        (baseChange B (Spec (.of T)) (Spec (.of S₁)) hU' hU
          (AlgebraicGeometry.Space.specSite B hU hU').hom).map mU ≫
        (twoStepBaseChangeIso B hX hU hU' hC hC₁ hE w₁ w₂ hq₁ hq₂).hom =
      (specSpaceBaseChangeIso B hU hU' u₂ hp₂ hA₁ hD).inv ≫
        (baseChange B (Spec (.of T)) (Spec (.of S₁)) hU' hU
          (AlgebraicGeometry.Space.specSite B hU hU').hom).map
          (yonedaSpaceHom B (Spec (.of S₁)) hU k) ≫
        (specSpaceBaseChangeIso B hU hU' w₂ hq₂ hC₁ hE).hom := by
    rw [hm, Functor.map_comp, Functor.map_comp]
    simp only [twoStepBaseChangeIso, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv,
      Functor.mapIso_hom, Category.assoc]
    simp
  rw [heq, hk]
  exact specSpaceAlgHomEquiv_baseChange B hU hU' u₂ w₂ hp₂ hq₂ hA₁ hD hC₁ hE k c

/-- **The compatibility of the two component algebra maps over `R'_f`.** The two outer components
of a morphism of triples give algebra maps `C₁ → A₁` and `C' → A'`, and their images in `D` of
an element of `C` agree. This is the hypothesis the Beauville--Laszlo theorem for algebras asks
for. -/
theorem algHom_comp_eq_of_route
    (u₁ : A →+* A₁) (u₂ : A₁ →+* D) (v₁ : A →+* A') (v₂ : A' →+* D)
    (hp₁ : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R S₁)) (CommRingCat.ofHom u₁)
      (CommRingCat.ofHom (algebraMap S₁ A₁)))
    (hp₂ : IsPushout (CommRingCat.ofHom (algebraMap S₁ A₁))
      (CommRingCat.ofHom (algebraMap S₁ T)) (CommRingCat.ofHom u₂)
      (CommRingCat.ofHom (algebraMap T D)))
    (hp₃ : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R S₂)) (CommRingCat.ofHom v₁)
      (CommRingCat.ofHom (algebraMap S₂ A')))
    (hp₄ : IsPushout (CommRingCat.ofHom (algebraMap S₂ A'))
      (CommRingCat.ofHom (algebraMap S₂ T)) (CommRingCat.ofHom v₂)
      (CommRingCat.ofHom (algebraMap T D)))
    (w₁ : C →+* C₁) (w₂ : C₁ →+* E) (x₁ : C →+* C') (x₂ : C' →+* E)
    (hq₁ : IsPushout (CommRingCat.ofHom (algebraMap R C))
      (CommRingCat.ofHom (algebraMap R S₁)) (CommRingCat.ofHom w₁)
      (CommRingCat.ofHom (algebraMap S₁ C₁)))
    (hq₂ : IsPushout (CommRingCat.ofHom (algebraMap S₁ C₁))
      (CommRingCat.ofHom (algebraMap S₁ T)) (CommRingCat.ofHom w₂)
      (CommRingCat.ofHom (algebraMap T E)))
    (hq₃ : IsPushout (CommRingCat.ofHom (algebraMap R C))
      (CommRingCat.ofHom (algebraMap R S₂)) (CommRingCat.ofHom x₁)
      (CommRingCat.ofHom (algebraMap S₂ C')))
    (hq₄ : IsPushout (CommRingCat.ofHom (algebraMap S₂ C'))
      (CommRingCat.ofHom (algebraMap S₂ T)) (CommRingCat.ofHom x₂)
      (CommRingCat.ofHom (algebraMap T E)))
    (kappaA : (baseChange B (Spec (.of T)) (Spec (.of S₁)) hU' hU
          (AlgebraicGeometry.Space.specSite B hU hU').hom).obj
        ((baseChange B (Spec (.of S₁)) (Spec (.of R)) hU hX
          (AlgebraicGeometry.Space.specSite B hX hU).hom).obj (specSpace B hX hA)) ⟶
      (baseChange B (Spec (.of T)) (Spec (.of S₂)) hU' hX'
          (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj
        ((baseChange B (Spec (.of S₂)) (Spec (.of R)) hX' hX
          (AlgebraicGeometry.Space.specSite B hX hX').hom).obj (specSpace B hX hA)))
    (kappaC : (baseChange B (Spec (.of T)) (Spec (.of S₁)) hU' hU
          (AlgebraicGeometry.Space.specSite B hU hU').hom).obj
        ((baseChange B (Spec (.of S₁)) (Spec (.of R)) hU hX
          (AlgebraicGeometry.Space.specSite B hX hU).hom).obj (specSpace B hX hC)) ⟶
      (baseChange B (Spec (.of T)) (Spec (.of S₂)) hU' hX'
          (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj
        ((baseChange B (Spec (.of S₂)) (Spec (.of R)) hX' hX
          (AlgebraicGeometry.Space.specSite B hX hX').hom).obj (specSpace B hX hC)))
    (hsecA : kappaA.hom.app (Opposite.op (AlgebraicGeometry.Space.specSite B hU' hD))
          (schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hU' hD) _
          (twoStepBaseChangeIso B hX hU hU' hA hA₁ hD u₁ u₂ hp₁ hp₂).inv) =
        schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hU' hD) _
          (twoStepBaseChangeIso B hX hX' hU' hA hA' hD v₁ v₂ hp₃ hp₄).inv)
    (hsecC : kappaC.hom.app (Opposite.op (AlgebraicGeometry.Space.specSite B hU' hE))
          (schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hU' hE) _
          (twoStepBaseChangeIso B hX hU hU' hC hC₁ hE w₁ w₂ hq₁ hq₂).inv) =
        schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hU' hE) _
          (twoStepBaseChangeIso B hX hX' hU' hC hC' hE x₁ x₂ hq₃ hq₄).inv)
    (mU : (baseChange B (Spec (.of S₁)) (Spec (.of R)) hU hX
          (AlgebraicGeometry.Space.specSite B hX hU).hom).obj (specSpace B hX hA) ⟶
      (baseChange B (Spec (.of S₁)) (Spec (.of R)) hU hX
          (AlgebraicGeometry.Space.specSite B hX hU).hom).obj (specSpace B hX hC))
    (mX' : (baseChange B (Spec (.of S₂)) (Spec (.of R)) hX' hX
          (AlgebraicGeometry.Space.specSite B hX hX').hom).obj (specSpace B hX hA) ⟶
      (baseChange B (Spec (.of S₂)) (Spec (.of R)) hX' hX
          (AlgebraicGeometry.Space.specSite B hX hX').hom).obj (specSpace B hX hC))
    (hroute : (baseChange B (Spec (.of T)) (Spec (.of S₁)) hU' hU
          (AlgebraicGeometry.Space.specSite B hU hU').hom).map mU ≫ kappaC =
        kappaA ≫ (baseChange B (Spec (.of T)) (Spec (.of S₂)) hU' hX'
          (AlgebraicGeometry.Space.specSite B hX' hU').hom).map mX')
    (hwx : w₂.comp w₁ = x₂.comp x₁) (c : C) :
    u₂ (specSpaceAlgHomEquiv B hU hA₁ hC₁
        ((specSpaceBaseChangeIso B hX hU u₁ hp₁ hA hA₁).inv ≫ mU ≫
          (specSpaceBaseChangeIso B hX hU w₁ hq₁ hC hC₁).hom) (w₁ c)) =
      v₂ (specSpaceAlgHomEquiv B hX' hA' hC'
        ((specSpaceBaseChangeIso B hX hX' v₁ hp₃ hA hA').inv ≫ mX' ≫
          (specSpaceBaseChangeIso B hX hX' x₁ hq₃ hC hC').hom) (x₁ c)) := by
  have hcomp := twoStep_conj_eq_of_route B hX hU hX' hU' hA hA₁ hA' hD hC hC₁ hC' hE
    u₁ u₂ v₁ v₂ hp₁ hp₂ hp₃ hp₄ w₁ w₂ x₁ x₂ hq₁ hq₂ hq₃ hq₄ kappaA kappaC hsecA hsecC
    mU mX' hroute
  have hdU := specSpaceAlgHomEquiv_twoStep_conj B hX hU hU' hA hA₁ hD hC hC₁ hE
    u₁ u₂ w₁ w₂ hp₁ hp₂ hq₁ hq₂ mU (w₁ c)
  have hdX' := specSpaceAlgHomEquiv_twoStep_conj B hX hX' hU' hA hA' hD hC hC' hE
    v₁ v₂ x₁ x₂ hp₃ hp₄ hq₃ hq₄ mX' (x₁ c)
  rw [← hdU, ← hdX', hcomp]
  congr 1
  exact DFunLike.congr_fun hwx c

end Compare



section TensorSquares

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **The second base-change square of a tensor product.** For a tower `R → S → T`, the algebra
`M ⊗[R] T` is the base change of `M ⊗[R] S` along `S → T`. Obtained by pasting the two
first-step squares, which is cheaper than the scalar-tower form. -/
theorem isPushout_tensor_second {R M S T : Type u} [CommRing R] [CommRing M] [CommRing S]
    [CommRing T] [Algebra R M] [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] :
    IsPushout (CommRingCat.ofHom (algebraMap S (M ⊗[R] S)))
      (CommRingCat.ofHom (algebraMap S T))
      (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R M)
        (IsScalarTower.toAlgHom R S T)).toRingHom)
      (CommRingCat.ofHom (algebraMap T (M ⊗[R] T))) := by
  have hleft : IsPushout (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (algebraMap R M))
      (CommRingCat.ofHom (algebraMap S (M ⊗[R] S)))
      (CommRingCat.ofHom (algebraMap M (M ⊗[R] S))) :=
    CommRingCat.isPushout_of_isPushout R S M (M ⊗[R] S)
  have htotal : IsPushout (CommRingCat.ofHom (algebraMap R T))
      (CommRingCat.ofHom (algebraMap R M))
      (CommRingCat.ofHom (algebraMap T (M ⊗[R] T)))
      (CommRingCat.ofHom (algebraMap M (M ⊗[R] T))) :=
    CommRingCat.isPushout_of_isPushout R T M (M ⊗[R] T)
  have hcompS : CommRingCat.ofHom (algebraMap R S) ≫ CommRingCat.ofHom (algebraMap S T) =
      CommRingCat.ofHom (algebraMap R T) := by
    ext r
    exact (IsScalarTower.algebraMap_apply R S T r).symm
  have hcompM : CommRingCat.ofHom (algebraMap M (M ⊗[R] S)) ≫
        CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R M)
          (IsScalarTower.toAlgHom R S T)).toRingHom =
      CommRingCat.ofHom (algebraMap M (M ⊗[R] T)) := by
    ext m
    simp
  rw [← hcompS, ← hcompM] at htotal
  refine IsPushout.flip (IsPushout.of_left htotal ?_ hleft)
  ext s
  simp [Algebra.TensorProduct.right_algebraMap_apply]

/-- The base-change map of a tensor product restricts to the structure map on the left factor. -/
theorem tensorMap_comp_algebraMap_left {R M S T : Type u} [CommRing R] [CommRing M]
    [CommRing S] [CommRing T] [Algebra R M] [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] :
    (Algebra.TensorProduct.map (AlgHom.id R M)
          (IsScalarTower.toAlgHom R S T)).toRingHom.comp (algebraMap M (M ⊗[R] S)) =
      algebraMap M (M ⊗[R] T) := by
  ext m
  simp

/-- The base-change map `M ⊗[R] R' → M ⊗[R] R'_f` of the tensor product is the canonical map
`BeauvilleLaszlo.baseChangeToAway` of the Beauville--Laszlo sequence. -/
theorem tensorMap_eq_baseChangeToAway {R R' M : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] [CommRing M] [Algebra R M] (f : R) (x : M ⊗[R] R') :
    (Algebra.TensorProduct.map (AlgHom.id R M)
        (IsScalarTower.toAlgHom R R' (Localization.Away ((algebraMap R R') f)))) x =
      _root_.BeauvilleLaszlo.baseChangeToAway (S := R') M f x := by
  induction x with
  | tmul m s => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The base-change map `M ⊗[R] R_f → M ⊗[R] R'_f` of the tensor product is the canonical map
`BeauvilleLaszlo.localizedBaseChangeToAway` of the Beauville--Laszlo sequence. -/
theorem tensorMap_eq_localizedBaseChangeToAway {R R' M : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] [CommRing M] [Algebra R M] (f : R) (x : M ⊗[R] Localization.Away f) :
    (Algebra.TensorProduct.map (AlgHom.id R M)
        (IsScalarTower.toAlgHom R (Localization.Away f)
          (Localization.Away ((algebraMap R R') f)))) x =
      _root_.BeauvilleLaszlo.localizedBaseChangeToAway (S := R') M f x := by
  induction x with
  | tmul m s =>
      rw [Algebra.TensorProduct.map_tmul,
        _root_.BeauvilleLaszlo.localizedBaseChangeToAway_tmul]
      congr 1
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end TensorSquares



section Descend

variable {R S₁ A A₁ C C₁ : Type u} [CommRing R] [CommRing S₁] [Algebra R S₁]
  [CommRing A] [CommRing A₁] [Algebra R A] [Algebra S₁ A₁]
  [CommRing C] [CommRing C₁] [Algebra R C] [Algebra S₁ C₁]
  (B : BigFppfSite.{u}) (hX : B.Contains (Spec (.of R)))
  (hU : B.Contains (Spec (.of S₁)))
  (hA : B.Contains (Spec (.of A))) (hA₁ : B.Contains (Spec (.of A₁)))
  (hC : B.Contains (Spec (.of C))) (hC₁ : B.Contains (Spec (.of C₁)))

/-- **A morphism of base changes which agrees with an algebra map on the source algebra is the
base change of that algebra map.** Two algebra maps out of the base change `C₁` which agree on
`C` and on `S₁` are equal, because `C₁` is the pushout. -/
theorem baseChange_map_symm_eq
    (u₁ : A →+* A₁) (w₁ : C →+* C₁)
    (hp₁ : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R S₁)) (CommRingCat.ofHom u₁)
      (CommRingCat.ofHom (algebraMap S₁ A₁)))
    (hq₁ : IsPushout (CommRingCat.ofHom (algebraMap R C))
      (CommRingCat.ofHom (algebraMap R S₁)) (CommRingCat.ofHom w₁)
      (CommRingCat.ofHom (algebraMap S₁ C₁)))
    (θ : C →ₐ[R] A)
    (mU : (baseChange B (Spec (.of S₁)) (Spec (.of R)) hU hX
          (AlgebraicGeometry.Space.specSite B hX hU).hom).obj (specSpace B hX hA) ⟶
      (baseChange B (Spec (.of S₁)) (Spec (.of R)) hU hX
          (AlgebraicGeometry.Space.specSite B hX hU).hom).obj (specSpace B hX hC))
    (h : ∀ c : C, specSpaceAlgHomEquiv B hU hA₁ hC₁
        ((specSpaceBaseChangeIso B hX hU u₁ hp₁ hA hA₁).inv ≫ mU ≫
          (specSpaceBaseChangeIso B hX hU w₁ hq₁ hC hC₁).hom) (w₁ c) = u₁ (θ c)) :
    (baseChange B (Spec (.of S₁)) (Spec (.of R)) hU hX
          (AlgebraicGeometry.Space.specSite B hX hU).hom).map
        ((specSpaceAlgHomEquiv B hX hA hC).symm θ) = mU := by
  have hform : (specSpaceAlgHomEquiv B hX hA hC).symm θ =
      yonedaSpaceHom B (Spec (.of R)) hX
        ((AlgebraicGeometry.Space.specSiteHomEquiv B hX hA hC).symm θ) := rfl
  have hdict := specSpaceAlgHomEquiv_baseChange B hX hU u₁ w₁ hp₁ hq₁ hA hA₁ hC hC₁
    ((AlgebraicGeometry.Space.specSiteHomEquiv B hX hA hC).symm θ)
  have hθ : specSpaceAlgHomEquiv B hX hA hC (yonedaSpaceHom B (Spec (.of R)) hX
      ((AlgebraicGeometry.Space.specSiteHomEquiv B hX hA hC).symm θ)) = θ := by
    rw [← hform]
    exact (specSpaceAlgHomEquiv B hX hA hC).apply_symm_apply θ
  have hpt : ∀ c : C, specSpaceAlgHomEquiv B hU hA₁ hC₁
      ((specSpaceBaseChangeIso B hX hU u₁ hp₁ hA hA₁).inv ≫
        (baseChange B (Spec (.of S₁)) (Spec (.of R)) hU hX
          (AlgebraicGeometry.Space.specSite B hX hU).hom).map
          ((specSpaceAlgHomEquiv B hX hA hC).symm θ) ≫
        (specSpaceBaseChangeIso B hX hU w₁ hq₁ hC hC₁).hom) (w₁ c) =
      specSpaceAlgHomEquiv B hU hA₁ hC₁
        ((specSpaceBaseChangeIso B hX hU u₁ hp₁ hA hA₁).inv ≫ mU ≫
          (specSpaceBaseChangeIso B hX hU w₁ hq₁ hC hC₁).hom) (w₁ c) := by
    intro c
    rw [hform, hdict c, hθ, h c]
  have key : CommRingCat.ofHom
        (specSpaceAlgHomEquiv B hU hA₁ hC₁
          ((specSpaceBaseChangeIso B hX hU u₁ hp₁ hA hA₁).inv ≫
            (baseChange B (Spec (.of S₁)) (Spec (.of R)) hU hX
              (AlgebraicGeometry.Space.specSite B hX hU).hom).map
              ((specSpaceAlgHomEquiv B hX hA hC).symm θ) ≫
            (specSpaceBaseChangeIso B hX hU w₁ hq₁ hC hC₁).hom)).toRingHom =
      CommRingCat.ofHom (specSpaceAlgHomEquiv B hU hA₁ hC₁
          ((specSpaceBaseChangeIso B hX hU u₁ hp₁ hA hA₁).inv ≫ mU ≫
            (specSpaceBaseChangeIso B hX hU w₁ hq₁ hC hC₁).hom)).toRingHom := by
    refine hq₁.hom_ext ?_ ?_
    · ext c
      simpa using hpt c
    · ext t
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [AlgHom.commutes, AlgHom.commutes]
  have key2 : (specSpaceBaseChangeIso B hX hU u₁ hp₁ hA hA₁).inv ≫
        (baseChange B (Spec (.of S₁)) (Spec (.of R)) hU hX
          (AlgebraicGeometry.Space.specSite B hX hU).hom).map
          ((specSpaceAlgHomEquiv B hX hA hC).symm θ) ≫
        (specSpaceBaseChangeIso B hX hU w₁ hq₁ hC hC₁).hom =
      (specSpaceBaseChangeIso B hX hU u₁ hp₁ hA hA₁).inv ≫ mU ≫
        (specSpaceBaseChangeIso B hX hU w₁ hq₁ hC hC₁).hom := by
    refine (specSpaceAlgHomEquiv B hU hA₁ hC₁).injective (AlgHom.ext fun x ↦ ?_)
    have key' := congrArg CommRingCat.Hom.hom key
    simp only [CommRingCat.hom_ofHom] at key'
    exact DFunLike.congr_fun key' x
  have hcancel := congrArg (fun t ↦ (specSpaceBaseChangeIso B hX hU u₁ hp₁ hA hA₁).hom ≫ t ≫
    (specSpaceBaseChangeIso B hX hU w₁ hq₁ hC hC₁).inv) key2
  simpa using hcancel

end Descend



section AbstractNat

variable {C₀ D₀ E₀ : Type*} [Category C₀] [Category D₀] [Category E₀]

/-- A natural isomorphism identifies the morphisms a composite functor induces: if the
isomorphism carries the image of `φ` to a morphism `b`, conjugated, then the composite functor
sends `φ` to `b`. -/
theorem comp_map_eq_of_natIso (F : C₀ ⥤ D₀) (K : D₀ ⥤ E₀) (L : C₀ ⥤ E₀) (e : F ⋙ K ≅ L)
    {Y Z : C₀} (φ : Y ⟶ Z) (b : (F ⋙ K).obj Y ⟶ (F ⋙ K).obj Z)
    (h : L.map φ = e.inv.app Y ≫ b ≫ e.hom.app Z) : (F ⋙ K).map φ = b := by
  refine (cancel_mono (e.hom.app Z)).mp ?_
  rw [e.hom.naturality φ, h, ← Category.assoc, ← Category.assoc, Iso.hom_inv_id_app,
    Category.id_comp]

end AbstractNat

section Core

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

/-- An `S`-algebra map between base changes to `S` sends the image of `algebraMap R M r` to the
image of `algebraMap R N r`. -/
private theorem algHom_algebraMap_algebraMap_eq {R S M N : Type u} [CommRing R] [CommRing S]
    [CommRing M] [CommRing N] [Algebra R S] [Algebra R M] [Algebra R N]
    (g : M ⊗[R] S →ₐ[S] N ⊗[R] S) (r : R) :
    g (algebraMap M (M ⊗[R] S) (algebraMap R M r)) = algebraMap R N r ⊗ₜ[R] 1 := by
  rw [show algebraMap M (M ⊗[R] S) (algebraMap R M r) = algebraMap S (M ⊗[R] S) (algebraMap R S r)
    by rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply],
    AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  simp

/-- **The algebra map glued out of the two components of a morphism of triples.** The
compatibility of the two components over `R'_f` is
`BeauvilleLaszlo.Space.algHom_comp_eq_of_route`, and
`BeauvilleLaszlo.Space.exists_algHom_of_baseChanges_compatible` — the Beauville--Laszlo theorem
for a glueable algebra — produces the map, whose two base changes are the two components. -/
theorem exists_algHom_of_route (f : R)
    (B : BigFppfSite.{u}) (hX : B.Contains (Spec (.of R)))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R')))
    (hU' : B.Contains (Spec (.of (Localization.Away ((algebraMap R R') f)))))
    (hcomm : (AlgebraicGeometry.Space.specSite B hU hU').hom ≫
          (AlgebraicGeometry.Space.specSite B hX hU).hom =
        (AlgebraicGeometry.Space.specSite B hX' hU').hom ≫
          (AlgebraicGeometry.Space.specSite B hX hX').hom)
    {A C : Type u} [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
    (hA : B.Contains (Spec (.of A))) (hC : B.Contains (Spec (.of C)))
    (hA₁ : B.Contains (Spec (.of (A ⊗[R] Localization.Away f))))
    (hA' : B.Contains (Spec (.of (A ⊗[R] R'))))
    (hD : B.Contains (Spec (.of (A ⊗[R] Localization.Away ((algebraMap R R') f)))))
    (hC₁ : B.Contains (Spec (.of (C ⊗[R] Localization.Away f))))
    (hC' : B.Contains (Spec (.of (C ⊗[R] R'))))
    (hE : B.Contains (Spec (.of (C ⊗[R] Localization.Away ((algebraMap R R') f)))))
    (hp₁ : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R (Localization.Away f)))
      (CommRingCat.ofHom (algebraMap A (A ⊗[R] Localization.Away f)))
      (CommRingCat.ofHom (algebraMap (Localization.Away f) (A ⊗[R] Localization.Away f))))
    (hp₃ : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R R'))
      (CommRingCat.ofHom (algebraMap A (A ⊗[R] R')))
      (CommRingCat.ofHom (algebraMap R' (A ⊗[R] R'))))
    (hq₁ : IsPushout (CommRingCat.ofHom (algebraMap R C))
      (CommRingCat.ofHom (algebraMap R (Localization.Away f)))
      (CommRingCat.ofHom (algebraMap C (C ⊗[R] Localization.Away f)))
      (CommRingCat.ofHom (algebraMap (Localization.Away f) (C ⊗[R] Localization.Away f))))
    (hq₃ : IsPushout (CommRingCat.ofHom (algebraMap R C))
      (CommRingCat.ofHom (algebraMap R R'))
      (CommRingCat.ofHom (algebraMap C (C ⊗[R] R')))
      (CommRingCat.ofHom (algebraMap R' (C ⊗[R] R'))))
    (hAglue : _root_.BeauvilleLaszlo.IsGlueableFor (S := R') A f)
    (pA : (baseChange B (Spec (.of (Localization.Away ((algebraMap R R') f))))
          (Spec (.of (Localization.Away f))) hU' hU
          (AlgebraicGeometry.Space.specSite B hU hU').hom).obj
        ((baseChange B (Spec (.of (Localization.Away f))) (Spec (.of R)) hU hX
          (AlgebraicGeometry.Space.specSite B hX hU).hom).obj (specSpace B hX hA)) =
      (baseChange B (Spec (.of (Localization.Away ((algebraMap R R') f)))) (Spec (.of R'))
          hU' hX' (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj
        ((baseChange B (Spec (.of R')) (Spec (.of R)) hX' hX
          (AlgebraicGeometry.Space.specSite B hX hX').hom).obj (specSpace B hX hA)))
    (pC : (baseChange B (Spec (.of (Localization.Away ((algebraMap R R') f))))
          (Spec (.of (Localization.Away f))) hU' hU
          (AlgebraicGeometry.Space.specSite B hU hU').hom).obj
        ((baseChange B (Spec (.of (Localization.Away f))) (Spec (.of R)) hU hX
          (AlgebraicGeometry.Space.specSite B hX hU).hom).obj (specSpace B hX hC)) =
      (baseChange B (Spec (.of (Localization.Away ((algebraMap R R') f)))) (Spec (.of R'))
          hU' hX' (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj
        ((baseChange B (Spec (.of R')) (Spec (.of R)) hX' hX
          (AlgebraicGeometry.Space.specSite B hX hX').hom).obj (specSpace B hX hC)))
    (mU : (baseChange B (Spec (.of (Localization.Away f))) (Spec (.of R)) hU hX
          (AlgebraicGeometry.Space.specSite B hX hU).hom).obj (specSpace B hX hA) ⟶
      (baseChange B (Spec (.of (Localization.Away f))) (Spec (.of R)) hU hX
          (AlgebraicGeometry.Space.specSite B hX hU).hom).obj (specSpace B hX hC))
    (mX' : (baseChange B (Spec (.of R')) (Spec (.of R)) hX' hX
          (AlgebraicGeometry.Space.specSite B hX hX').hom).obj (specSpace B hX hA) ⟶
      (baseChange B (Spec (.of R')) (Spec (.of R)) hX' hX
          (AlgebraicGeometry.Space.specSite B hX hX').hom).obj (specSpace B hX hC))
    (hroute : (baseChange B (Spec (.of (Localization.Away ((algebraMap R R') f))))
            (Spec (.of (Localization.Away f))) hU' hU
            (AlgebraicGeometry.Space.specSite B hU hU').hom).map mU ≫ eqToHom pC =
        eqToHom pA ≫ (baseChange B (Spec (.of (Localization.Away ((algebraMap R R') f))))
            (Spec (.of R')) hU' hX'
            (AlgebraicGeometry.Space.specSite B hX' hU').hom).map mX') :
    ∃ θ : C →ₐ[R] A,
      (∀ c : C, specSpaceAlgHomEquiv B hX' hA' hC'
          ((specSpaceBaseChangeIso B hX hX' (algebraMap A (A ⊗[R] R')) hp₃ hA hA').inv ≫
            mX' ≫ (specSpaceBaseChangeIso B hX hX' (algebraMap C (C ⊗[R] R')) hq₃ hC hC').hom)
          (algebraMap C (C ⊗[R] R') c) = algebraMap A (A ⊗[R] R') (θ c)) ∧
      (∀ c : C, specSpaceAlgHomEquiv B hU hA₁ hC₁
          ((specSpaceBaseChangeIso B hX hU (algebraMap A (A ⊗[R] Localization.Away f))
              hp₁ hA hA₁).inv ≫ mU ≫
            (specSpaceBaseChangeIso B hX hU (algebraMap C (C ⊗[R] Localization.Away f))
              hq₁ hC hC₁).hom)
          (algebraMap C (C ⊗[R] Localization.Away f) c) =
        algebraMap A (A ⊗[R] Localization.Away f) (θ c)) := by
  have hp₂ := isPushout_tensor_second (R := R) (M := A) (S := Localization.Away f)
    (T := Localization.Away ((algebraMap R R') f))
  have hp₄ := isPushout_tensor_second (R := R) (M := A) (S := R')
    (T := Localization.Away ((algebraMap R R') f))
  have hq₂ := isPushout_tensor_second (R := R) (M := C) (S := Localization.Away f)
    (T := Localization.Away ((algebraMap R R') f))
  have hq₄ := isPushout_tensor_second (R := R) (M := C) (S := R')
    (T := Localization.Away ((algebraMap R R') f))
  have huv : ∀ (M : Type u) [CommRing M] [Algebra R M],
      (Algebra.TensorProduct.map (AlgHom.id R M)
          (IsScalarTower.toAlgHom R (Localization.Away f)
            (Localization.Away ((algebraMap R R') f)))).toRingHom.comp
        (algebraMap M (M ⊗[R] Localization.Away f)) =
      (Algebra.TensorProduct.map (AlgHom.id R M)
          (IsScalarTower.toAlgHom R R'
            (Localization.Away ((algebraMap R R') f)))).toRingHom.comp
        (algebraMap M (M ⊗[R] R')) := fun M _ _ ↦ by
    rw [tensorMap_comp_algebraMap_left, tensorMap_comp_algebraMap_left]
  have hsecA := twoStepBaseChangeIso_inv_section_eq B hX hU hX' hU' hA hA₁ hA' hD
    _ _ _ _ hp₁ hp₂ hp₃ hp₄ hcomm (huv A) pA
  have hsecC := twoStepBaseChangeIso_inv_section_eq B hX hU hX' hU' hC hC₁ hC' hE
    _ _ _ _ hq₁ hq₂ hq₃ hq₄ hcomm (huv C) pC
  have hcompat := fun c ↦ algHom_comp_eq_of_route B hX hU hX' hU' hA hA₁ hA' hD hC hC₁ hC' hE
    _ _ _ _ hp₁ hp₂ hp₃ hp₄ _ _ _ _ hq₁ hq₂ hq₃ hq₄ (eqToHom pA) (eqToHom pC) hsecA hsecC
    mU mX' hroute (huv C) c
  obtain ⟨θ, hθ', hθ₁⟩ := exists_algHom_of_baseChanges_compatible
    (A := A) (C := C) f hAglue
    ((specSpaceAlgHomEquiv B hX' hA' hC'
      ((specSpaceBaseChangeIso B hX hX' (algebraMap A (A ⊗[R] R')) hp₃ hA hA').inv ≫
        mX' ≫
        (specSpaceBaseChangeIso B hX hX' (algebraMap C (C ⊗[R] R'))
          hq₃ hC hC').hom)).toRingHom.comp (algebraMap C (C ⊗[R] R')))
    ((specSpaceAlgHomEquiv B hU hA₁ hC₁
      ((specSpaceBaseChangeIso B hX hU (algebraMap A (A ⊗[R] Localization.Away f))
          hp₁ hA hA₁).inv ≫ mU ≫
        (specSpaceBaseChangeIso B hX hU (algebraMap C (C ⊗[R] Localization.Away f))
          hq₁ hC hC₁).hom)).toRingHom.comp (algebraMap C (C ⊗[R] Localization.Away f)))
    (fun c ↦ by
      rw [← tensorMap_eq_baseChangeToAway, ← tensorMap_eq_localizedBaseChangeToAway]
      exact (hcompat c).symm)
    (fun r ↦ algHom_algebraMap_algebraMap_eq _ r)
    (fun r ↦ algHom_algebraMap_algebraMap_eq _ r)
  exact ⟨θ, fun c ↦ by simpa using (hθ' c).symm, fun c ↦ by simpa using (hθ₁ c).symm⟩

/-- **Fullness of the glueing functor on representable affine spaces, the source glueable.**
Every morphism between the triples of `Spec A` and `Spec C` is the triple of a morphism
`Spec A → Spec C` over `Spec R`. The two outer components give algebra maps on the two base
changes, the Beauville--Laszlo theorem glues them to `θ : C → A`, and
`BeauvilleLaszlo.Space.hom_ext_of_overU_of_overX` reduces the comparison of the triple of `Spec θ`
with the given morphism to its two outer components. -/
theorem surjective_functor_map_specSpace (f : R)
    (B : BigFppfSite.{u}) (hX : B.Contains (Spec (.of R)))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R')))
    (hU' : B.Contains (Spec (.of (Localization.Away ((algebraMap R R') f)))))
    (hcomm : (AlgebraicGeometry.Space.specSite B hU hU').hom ≫
          (AlgebraicGeometry.Space.specSite B hX hU).hom =
        (AlgebraicGeometry.Space.specSite B hX' hU').hom ≫
          (AlgebraicGeometry.Space.specSite B hX hX').hom)
    (G : GlueingFunctorSpec B (Spec (.of (Localization.Away ((algebraMap R R') f))))
      (Spec (.of (Localization.Away f))) (Spec (.of R')) (Spec (.of R)) hU' hU hX' hX
      (AlgebraicGeometry.Space.specSite B hU hU').hom
      (AlgebraicGeometry.Space.specSite B hX' hU').hom
      (AlgebraicGeometry.Space.specSite B hX hU).hom
      (AlgebraicGeometry.Space.specSite B hX hX').hom hcomm)
    {A C : Type u} [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
    (hA : B.Contains (Spec (.of A))) (hC : B.Contains (Spec (.of C)))
    (hAglue : _root_.BeauvilleLaszlo.IsGlueableFor (S := R') A f) :
    Function.Surjective
      (fun φ : specSpace B hX hA ⟶ specSpace B hX hC ↦ G.functor.map φ) := by
  intro β
  have hA₁ : B.Contains (Spec (.of (A ⊗[R] Localization.Away f))) :=
    contains_spec_tensorProduct B hA hU
  have hA' : B.Contains (Spec (.of (A ⊗[R] R'))) := contains_spec_tensorProduct B hA hX'
  have hD : B.Contains (Spec (.of (A ⊗[R] Localization.Away ((algebraMap R R') f)))) :=
    contains_spec_tensorProduct B hA hU'
  have hC₁ : B.Contains (Spec (.of (C ⊗[R] Localization.Away f))) :=
    contains_spec_tensorProduct B hC hU
  have hC' : B.Contains (Spec (.of (C ⊗[R] R'))) := contains_spec_tensorProduct B hC hX'
  have hE : B.Contains (Spec (.of (C ⊗[R] Localization.Away ((algebraMap R R') f)))) :=
    contains_spec_tensorProduct B hC hU'
  have hp₁ := CommRingCat.isPushout_of_isPushout R A (Localization.Away f)
    (A ⊗[R] Localization.Away f)
  have hp₃ := CommRingCat.isPushout_of_isPushout R A R' (A ⊗[R] R')
  have hq₁ := CommRingCat.isPushout_of_isPushout R C (Localization.Away f)
    (C ⊗[R] Localization.Away f)
  have hq₃ := CommRingCat.isPushout_of_isPushout R C R' (C ⊗[R] R')
  obtain ⟨pA, -⟩ := exists_cast_of_square B hX hU hX' hU' hA hcomm G
  obtain ⟨pC, -⟩ := exists_cast_of_square B hX hU hX' hU' hC hcomm G
  have hroute := functor_map_route_eq B (Spec (.of (Localization.Away ((algebraMap R R') f))))
    (Spec (.of (Localization.Away f))) (Spec (.of R')) (Spec (.of R)) hU' hU hX' hX
    _ _ _ _ G (specSpace B hX hA) (specSpace B hX hC) β
  obtain ⟨θ, hX'prop, hUprop⟩ := exists_algHom_of_route f B hX hU hX' hU' hcomm hA hC
    hA₁ hA' hD hC₁ hC' hE hp₁ hp₃ hq₁ hq₃ hAglue pA pC
    (G.overUIso.inv.app (specSpace B hX hA) ≫ β.hom.left.right ≫
      G.overUIso.hom.app (specSpace B hX hC))
    (G.overX'Iso.inv.app (specSpace B hX hA) ≫ β.hom.right ≫
      G.overX'Iso.hom.app (specSpace B hX hC)) hroute
  refine ⟨(specSpaceAlgHomEquiv B hX hA hC).symm θ, ?_⟩
  refine hom_ext_of_overU_of_overX B (Spec (.of (Localization.Away ((algebraMap R R') f))))
    (Spec (.of (Localization.Away f))) (Spec (.of R')) hU' hU hX' _ _ ?_ ?_
  · have hbc := baseChange_map_symm_eq B hX hU hA hA₁ hC hC₁
      (algebraMap A (A ⊗[R] Localization.Away f))
      (algebraMap C (C ⊗[R] Localization.Away f)) hp₁ hq₁ θ
      (G.overUIso.inv.app (specSpace B hX hA) ≫ β.hom.left.right ≫
        G.overUIso.hom.app (specSpace B hX hC)) hUprop
    exact comp_map_eq_of_natIso G.functor
      (overU B (Spec (.of (Localization.Away ((algebraMap R R') f))))
        (Spec (.of (Localization.Away f))) (Spec (.of R')) hU' hU hX' _ _)
      (baseChange B (Spec (.of (Localization.Away f))) (Spec (.of R)) hU hX
        (AlgebraicGeometry.Space.specSite B hX hU).hom)
      G.overUIso ((specSpaceAlgHomEquiv B hX hA hC).symm θ) β.hom.left.right hbc
  · have hbc := baseChange_map_symm_eq B hX hX' hA hA' hC hC'
      (algebraMap A (A ⊗[R] R')) (algebraMap C (C ⊗[R] R')) hp₃ hq₃ θ
      (G.overX'Iso.inv.app (specSpace B hX hA) ≫ β.hom.right ≫
        G.overX'Iso.hom.app (specSpace B hX hC)) hX'prop
    exact comp_map_eq_of_natIso G.functor
      (overX' B (Spec (.of (Localization.Away ((algebraMap R R') f))))
        (Spec (.of (Localization.Away f))) (Spec (.of R')) hU' hU hX' _ _)
      (baseChange B (Spec (.of R')) (Spec (.of R)) hX' hX
        (AlgebraicGeometry.Space.specSite B hX hX').hom)
      G.overX'Iso ((specSpaceAlgHomEquiv B hX hA hC).symm θ) β.hom.right hbc

end Core


section Subcategory

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

/-- Glueability of a module does not depend on which of two `Algebra R S` structures with the
same structure map is used; this is the direction opposite to
`BeauvilleLaszlo.Space.isGlueableFor_toAlgebra`. -/
theorem isGlueableFor_of_toAlgebra {S M : Type u} [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (f : R)
    (h : @_root_.BeauvilleLaszlo.IsGlueableFor R S _ _ (algebraMap R S).toAlgebra M _ _ f) :
    _root_.BeauvilleLaszlo.IsGlueableFor (S := S) M f := by
  have hinst : (algebraMap R S).toAlgebra = (inferInstance : Algebra R S) :=
    Algebra.algebra_ext _ _ fun _ ↦ rfl
  rwa [hinst] at h

/-- **Glueability of an algebraic space only depends on its isomorphism class.** An affine
scheme étale over one of two isomorphic spaces is étale over the other, by composing with the
isomorphism. -/
theorem isGlueableAlgebraicSpace_of_iso (f : R) (B : BigFppfSite.{u})
    (hX : B.Contains (Spec (.of R))) {Y Z : AlgebraicSpaces B (Spec (.of R)) hX} (e : Y ≅ Z)
    (h : AlgebraicGeometry.Space.IsGlueableAlgebraicSpace (algebraMap R R') f B hX Y) :
    AlgebraicGeometry.Space.IsGlueableAlgebraicSpace (algebraMap R R') f B hX Z := by
  intro W p hWaff hWet
  have : IsIso e.inv.hom :=
    ((ObjectProperty.ι (IsAlgebraicSpace B (Spec (.of R)) hX)).mapIso e.symm).isIso_hom
  exact h W (p ≫ e.inv.hom) hWaff (AlgebraicGeometry.Space.isEtale_comp B (Spec (.of R)) hX
    hWet (AlgebraicGeometry.Space.isEtale_of_isIso B (Spec (.of R)) hX e.inv.hom))

/-- **Stacks 0F9Q, fullness.** The glueing functor of Stacks 0F9N is full on the affine
algebraic spaces over `Spec R` which are glueable for the pair: the presentation theorem writes
the source and the target as `Spec A` and `Spec C`, glueability of the source passes to the
algebra `A`, and `BeauvilleLaszlo.Space.surjective_functor_map_specSpace` descends the
morphism. -/
theorem full_comp_glueingFunctor (f : R)
    (B : BigFppfSite.{u}) (hX : B.Contains (Spec (.of R)))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R')))
    (hU' : B.Contains (Spec (.of (Localization.Away ((algebraMap R R') f)))))
    (hcomm : (AlgebraicGeometry.Space.specSite B hU hU').hom ≫
          (AlgebraicGeometry.Space.specSite B hX hU).hom =
        (AlgebraicGeometry.Space.specSite B hX' hU').hom ≫
          (AlgebraicGeometry.Space.specSite B hX hX').hom)
    (G : GlueingFunctorSpec B (Spec (.of (Localization.Away ((algebraMap R R') f))))
      (Spec (.of (Localization.Away f))) (Spec (.of R')) (Spec (.of R)) hU' hU hX' hX
      (AlgebraicGeometry.Space.specSite B hU hU').hom
      (AlgebraicGeometry.Space.specSite B hX' hU').hom
      (AlgebraicGeometry.Space.specSite B hX hU).hom
      (AlgebraicGeometry.Space.specSite B hX hX').hom hcomm) :
    (ObjectProperty.ι (affineGlueableSpaces (algebraMap R R') f B hX) ⋙ G.functor).Full := by
  constructor
  intro Y Z β
  obtain ⟨A, _, _, hA, ⟨eA⟩⟩ :=
    AlgebraicGeometry.Space.exists_specSite_iso_of_isAffineSpace B hX Y.1.1 Y.property.1
  obtain ⟨C, _, _, hC, ⟨eC⟩⟩ :=
    AlgebraicGeometry.Space.exists_specSite_iso_of_isAffineSpace B hX Z.1.1 Z.property.1
  have iA : Y.1 ≅ specSpace B hX hA := ObjectProperty.isoMk _ (eA ≪≫ (schemeSpaceIso _).symm)
  have iC : Z.1 ≅ specSpace B hX hC := ObjectProperty.isoMk _ (eC ≪≫ (schemeSpaceIso _).symm)
  have hAg : _root_.BeauvilleLaszlo.IsGlueableFor (S := R') A f :=
    isGlueableFor_of_toAlgebra f (isGlueableFor_of_isGlueableAlgebraicSpace
      (algebraMap R R') f B hX hA
      (isGlueableAlgebraicSpace_of_iso (R' := R') f B hX iA Y.property.2))
  obtain ⟨φ, hφ⟩ := surjective_map_of_iso G.functor iA iC
    (surjective_functor_map_specSpace f B hX hU hX' hU' hcomm G hA hC hAg) β
  exact ⟨ObjectProperty.homMk φ, hφ⟩

end Subcategory

section Assembly

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

/-- The Beauville--Laszlo square of `(R → R', f)` commutes: both composites `U' → X` are the
structure morphism of `Spec R'_f` over `Spec R`. -/
theorem specSite_square_comm (f : R) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away ((algebraMap R R') f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R))) :
    (AlgebraicGeometry.Space.specSite B hU hU').hom ≫
        (AlgebraicGeometry.Space.specSite B hX hU).hom =
      (AlgebraicGeometry.Space.specSite B hX' hU').hom ≫
        (AlgebraicGeometry.Space.specSite B hX hX').hom :=
  (pairGU_comp_pairJU_eq_specSite_hom f B hU' hU hX).trans
    (pairGX'_comp_pairJX'_eq_specSite_hom f B hU' hX' hX).symm

/-- **Stacks 0F9Q.** The glueing functor of Stacks 0F9N restricts to an equivalence between the
affine algebraic spaces over `X = Spec R` which are glueable for the pair `(R → R', f)` and the
cartesian glueing triples `(V, V', Y')` over `U ← U' → X'` whose three components are affine —
together with the identification of the forward functor of that equivalence with the restriction
of the glueing functor itself, which is what the statement of the tag asserts.

Faithfulness is Stacks 0F9S, fullness is
`BeauvilleLaszlo.Space.full_comp_glueingFunctor` and essential surjectivity is
`BeauvilleLaszlo.Space.essSurj_affineGlueableRestriction`; the equivalence is the one Mathlib
builds out of the three, so its forward functor *is* the restricted glueing functor and the
identification is `BeauvilleLaszlo.Space.affineGlueableRestrictionCompIso`. -/
@[stacks 0F9Q]
noncomputable def beauvilleLaszloAffineEquivalence (f : R)
    (hpair : _root_.BeauvilleLaszlo.IsGlueingPair (algebraMap R R') f)
    (B : BigFppfSite.{u}) (hX : B.Contains (Spec (.of R)))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R')))
    (hU' : B.Contains (Spec (.of (Localization.Away ((algebraMap R R') f))))) :
    AffineGlueingEquivalenceSpec (algebraMap R R') f B
      (Spec (.of (Localization.Away ((algebraMap R R') f))))
      (Spec (.of (Localization.Away f))) (Spec (.of R')) hU' hU hX' hX
      (AlgebraicGeometry.Space.specSite B hU hU').hom
      (AlgebraicGeometry.Space.specSite B hX' hU').hom
      (beauvilleLaszloGlueingSpaces B (Spec (.of (Localization.Away ((algebraMap R R') f))))
        (Spec (.of (Localization.Away f))) (Spec (.of R')) (Spec (.of R)) hU' hU hX' hX
        (AlgebraicGeometry.Space.specSite B hU hU').hom
        (AlgebraicGeometry.Space.specSite B hX' hU').hom
        (AlgebraicGeometry.Space.specSite B hX hU).hom
        (AlgebraicGeometry.Space.specSite B hX hX').hom
        (specSite_square_comm f B hU' hU hX' hX)).functor := by
  haveI hfull := full_comp_glueingFunctor f B hX hU hX' hU'
    (specSite_square_comm f B hU' hU hX' hX)
    (beauvilleLaszloGlueingSpaces B _ _ _ _ hU' hU hX' hX _ _ _ _
      (specSite_square_comm f B hU' hU hX' hX))
  haveI hfaith := faithful_comp_glueingFunctor
    (beauvilleLaszloGlueingSpaces B _ _ _ _ hU' hU hX' hX _ _ _ _
      (specSite_square_comm f B hU' hU hX' hX))
    (fun Y Z hY hZ ↦ beauvilleLaszloGlueingSpaces_map_injective_of_isGlueable R R'
      (algebraMap R R') f hpair B hU' hU hX' hX
      (specSite_square_comm f B hU' hU hX' hX) Y Z hY hZ)
  haveI : (affineGlueableRestriction (g := algebraMap R R') (f := f)
      (beauvilleLaszloGlueingSpaces B _ _ _ _ hU' hU hX' hX _ _ _ _
        (specSite_square_comm f B hU' hU hX' hX)) ⋙ ObjectProperty.ι _).Full :=
    Functor.Full.of_iso (affineGlueableRestrictionCompIso _).symm
  haveI : (affineGlueableRestriction (g := algebraMap R R') (f := f)
      (beauvilleLaszloGlueingSpaces B _ _ _ _ hU' hU hX' hX _ _ _ _
        (specSite_square_comm f B hU' hU hX' hX)) ⋙ ObjectProperty.ι _).Faithful :=
    Functor.Faithful.of_iso (affineGlueableRestrictionCompIso _).symm
  haveI : (affineGlueableRestriction (g := algebraMap R R') (f := f)
      (beauvilleLaszloGlueingSpaces B _ _ _ _ hU' hU hX' hX _ _ _ _
        (specSite_square_comm f B hU' hU hX' hX))).Full :=
    Functor.Full.of_comp_faithful _ (ObjectProperty.ι _)
  haveI : (affineGlueableRestriction (g := algebraMap R R') (f := f)
      (beauvilleLaszloGlueingSpaces B _ _ _ _ hU' hU hX' hX _ _ _ _
        (specSite_square_comm f B hU' hU hX' hX))).Faithful :=
    Functor.Faithful.of_comp _ (ObjectProperty.ι _)
  haveI : (affineGlueableRestriction (g := algebraMap R R') (f := f)
      (beauvilleLaszloGlueingSpaces B _ _ _ _ hU' hU hX' hX _ _ _ _
        (specSite_square_comm f B hU' hU hX' hX))).EssSurj :=
    essSurj_affineGlueableRestriction f hpair B hX hU hX' hU'
      (specSite_square_comm f B hU' hU hX' hX) _
  haveI : (affineGlueableRestriction (g := algebraMap R R') (f := f)
      (beauvilleLaszloGlueingSpaces B _ _ _ _ hU' hU hX' hX _ _ _ _
        (specSite_square_comm f B hU' hU hX' hX))).IsEquivalence :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  exact { equivalence := (affineGlueableRestriction (g := algebraMap R R') (f := f)
            (beauvilleLaszloGlueingSpaces B _ _ _ _ hU' hU hX' hX _ _ _ _
              (specSite_square_comm f B hU' hU hX' hX))).asEquivalence
          functorIso := affineGlueableRestrictionCompIso _ }

end Assembly

end BeauvilleLaszlo.Space


end
