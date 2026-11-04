module

public import StacksFrontier.Homology.DerivedIndexing.CompositeCommShift
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeEdge
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeShift

/-!
# The degree shift of the pullback attached to a complex concentrated in one degree

Let `P : 𝒜 ⥤ ℬ` and `Q : ℬ ⥤ 𝒞` be additive functors between abelian categories, with `𝒜` and
`ℬ` having enough injectives and `P` preserving injective objects.
`Stacks.DerivedIndexing.singleDerivedPullback` attaches to every `q : ℤ` the pullback

`RQ((Pℱ)[-q]) ⟶ R(Q ∘ P)(ℱ[-q])`

in `D⁺(𝒞)`. This file moves a statement about its degree-`p` homology at `q = 0` to the
degree-`p + q` homology at `q`, through the isomorphism
`DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso` which compares the two.

That is the last step of [Stacks, Tag 0FMD]: the identification `Pic(X) = H¹(X, 𝒪_X^*)` of
[Stacks, Tag 09NU] is natural for the pullback of *first* cohomology classes, which by
`Stacks.DerivedIndexing.rightDerivedPlusEdge_app_eq` is the degree-one homology of the
degree-zero pullback, while the de Rham first Chern class of [Stacks, Tag 0FLE] lives in the
degree-two hypercohomology of the sheaf of units placed in degree one, which is the degree-two
homology of the degree-one pullback.

## Main results

* `Stacks.DerivedIndexing.singleFunctorCompHomologyFunctorShiftIso_inv_app`: the components of
  the comparison of the two degrees, written out.
* `Stacks.DerivedIndexing.singleDerivedPullback_comm`: **the degree-`q` pullback is the
  degree-zero one, shifted by `-q`.**
* `Stacks.DerivedIndexing.homologyFunctor_map_singleDerivedPullback_comm`: **the degree-`p`
  homology of the degree-zero pullback and the degree-`p + q` homology of the degree-`q`
  pullback agree**, through the comparison of the two degrees.

## Implementation notes

The pullback is `RQ` applied to the degree-`q` derived-functor unit followed by the inverse of
the composition isomorphism `R(Q ∘ P) ≅ RQ ∘ RP` of [Stacks, Tag 015M], and both factors are
compatible with the shift: the first by
`Stacks.DerivedIndexing.singleDerivedUnit_comm`, the second by
`Stacks.DerivedIndexing.natTransCommShift_rightDerivedPlusCompTrans`. The shift compatibility of
the composition transformation is supplied as a local hypothesis rather than left to instance
search, which exhausts its budget on it.

As in `StacksFrontier.Homology.DerivedIndexing.SingleDegreeShift`, the junction objects of the
composites involved carry two spellings which are only definitionally equal — a complex
concentrated in degree `q`, read as a bounded-below complex and then localized, is the value of
`DerivedCategory.Plus.singleFunctor` only definitionally — so the category algebra is done by
`exact` against abstract lemmas stated on variables.

## References

* [Stacks Project, Tag 0FMD](https://stacks.math.columbia.edu/tag/0FMD)
* [Stacks Project, Tag 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe w w'' v v' v'' u u' u''

namespace Stacks.DerivedIndexing

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] commShiftRightDerivedFunctorPlus
  natTransCommShiftRightDerivedFunctorPlusUnit

/-! ### Algebraic helpers -/

section Helpers

variable {V : Type u} [Category.{v} V]

/-- Five-fold composites with the commuting squares the degree shift of the pullback is
assembled from as hypotheses. Stated on variables because several of the junction objects carry
two spellings which are only definitionally equal. -/
private theorem star2_algebra {X Y Z₀ W₁ W₂ W₃ W₄ W₅ T : V}
    {g : X ⟶ Z₀} {gw : X ⟶ Y} {gt : Y ⟶ Z₀} {Ai : Z₀ ⟶ W₁} {m : W₁ ⟶ W₃}
    {Bi : Y ⟶ W₂} {ti : W₂ ⟶ W₁} {nm : W₂ ⟶ W₄} {tq : W₄ ⟶ W₃}
    {iA : Y ⟶ W₅} {r : W₅ ⟶ W₂} {iB : X ⟶ T} {c : T ⟶ W₅} {e : T ⟶ W₄} {f : T ⟶ W₃}
    (hg : g = gw ≫ gt) (h2 : gt ≫ Ai = Bi ≫ ti) (h3 : nm ≫ tq = ti ≫ m)
    (h4 : Bi = iA ≫ r) (h5 : gw ≫ iA = iB ≫ c) (h6 : c ≫ r ≫ nm = e) (h7 : f = e ≫ tq) :
    g ≫ Ai ≫ m = iB ≫ f := by
  subst hg; subst h4; subst h6; subst h7
  simp only [Category.assoc] at h2 h3 h5 ⊢
  rw [reassoc_of% h2, ← h3, reassoc_of% h5]

/-- Transporting the leading factor of a composite across a naturality square. -/
private theorem comp_eq_of_nat {M M' N₁ N₂ N₃ Pt : V}
    {f : M ⟶ M'} {i' : M' ⟶ N₁} {r₁ : N₁ ⟶ N₂} {i : M ⟶ Pt} {g : Pt ⟶ N₁} {s : Pt ⟶ N₃}
    {d : N₃ ⟶ N₂} (hnat : f ≫ i' = i ≫ g) (hr : g ≫ r₁ = s ≫ d) :
    f ≫ i' ≫ r₁ = (i ≫ s) ≫ d := by
  rw [← Category.assoc, hnat, Category.assoc, hr, Category.assoc]

end Helpers

/-- **The comparison of the degree-`q` and degree-zero readings, written out.** The three
factors are the shift sequence of the homology functor, the commutation of `Φ` with the shift,
and `Φ` applied to the comparison of the single functors with the shift. -/
theorem singleFunctorCompHomologyFunctorShiftIso_inv_app
    {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w''} B]
    (Φ : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B) [Φ.CommShift ℤ] (p q : ℤ) (Z : A) :
    ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso Φ p q).app Z).inv =
      ((DerivedCategory.Plus.homologyFunctor B 0).shiftIso (-q) (p + q) p (by omega)).inv.app
          (Φ.obj ((DerivedCategory.Plus.singleFunctor A 0).obj Z)) ≫
        (DerivedCategory.Plus.homologyFunctor B (p + q)).map
            ((Φ.commShiftIso (-q)).inv.app
              ((DerivedCategory.Plus.singleFunctor A 0).obj Z)) ≫
          (DerivedCategory.Plus.homologyFunctor B (p + q)).map (Φ.map
            (((DerivedCategory.Plus.singleFunctors A).shiftIso (-q) q 0
              (by omega)).hom.app Z)) := by
  have h1 : (Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor A 0)
        (Functor.isoWhiskerLeft Φ
          ((DerivedCategory.Plus.homologyFunctor B 0).shiftIso (-q) (p + q) p
            (by omega)))).inv.app Z =
      ((DerivedCategory.Plus.homologyFunctor B 0).shiftIso (-q) (p + q) p (by omega)).inv.app
        (Φ.obj ((DerivedCategory.Plus.singleFunctor A 0).obj Z)) := rfl
  simp only [Functor.comp_obj, DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso,
    DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIsoOfEq,
    NatIso.trans_app, Iso.trans_inv, Iso.app_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_inv,
    Functor.comp_map, assoc]
  exact h1 =≫ _

variable {C : Type u} {D : Type u'} {E : Type u''}
  [Category.{v} C] [Category.{v'} D] [Category.{v''} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D] [HasDerivedCategory.{w''} E]
  [EnoughInjectives C] [EnoughInjectives D]
  (P : C ⥤ D) (Q : D ⥤ E) [P.Additive] [Q.Additive] [P.PreservesInjectiveObjects]

/-- **The pullback attached to a complex concentrated in degree `q` is the one attached to a
complex concentrated in degree zero, shifted by `-q`.** The pullback is `RQ` applied to the
degree-`q` derived-functor unit followed by the inverse of the composition isomorphism of
[Stacks, Tag 015M], and both factors are compatible with the shift. -/
theorem singleDerivedPullback_comm (q : ℤ) (Z : C) :
    (shiftFunctor (DerivedCategory.Plus E) (-q)).map (singleDerivedPullback P Q 0 Z) ≫
        ((P ⋙ Q).rightDerivedFunctorPlus.commShiftIso (-q)).inv.app
          ((DerivedCategory.Plus.singleFunctor C 0).obj Z) ≫
        (P ⋙ Q).rightDerivedFunctorPlus.map
          (((DerivedCategory.Plus.singleFunctors C).shiftIso (-q) q 0 (by omega)).hom.app Z) =
      (Q.rightDerivedFunctorPlus.commShiftIso (-q)).inv.app
          ((DerivedCategory.Plus.singleFunctor D 0).obj (P.obj Z)) ≫
        Q.rightDerivedFunctorPlus.map
          (((DerivedCategory.Plus.singleFunctors D).shiftIso (-q) q 0 (by omega)).hom.app
            (P.obj Z)) ≫
          singleDerivedPullback P Q q Z := by
  have htrans : NatTrans.CommShift (rightDerivedPlusCompTrans P Q) ℤ :=
    natTransCommShift_rightDerivedPlusCompTrans P Q
  have ht : NatTrans.CommShift (rightDerivedPlusCompIso P Q).hom ℤ :=
    NatTrans.commShift_of_eq (θ := rightDerivedPlusCompTrans P Q) rfl
  have h2 : (shiftFunctor (DerivedCategory.Plus E) (-q)).map
          ((rightDerivedPlusCompIso P Q).inv.app
            ((DerivedCategory.Plus.singleFunctor C 0).obj Z)) ≫
        ((P ⋙ Q).rightDerivedFunctorPlus.commShiftIso (-q)).inv.app
          ((DerivedCategory.Plus.singleFunctor C 0).obj Z) =
      ((P.rightDerivedFunctorPlus ⋙ Q.rightDerivedFunctorPlus).commShiftIso (-q)).inv.app
          ((DerivedCategory.Plus.singleFunctor C 0).obj Z) ≫
        (rightDerivedPlusCompIso P Q).inv.app
          ((shiftFunctor (DerivedCategory.Plus C) (-q)).obj
            ((DerivedCategory.Plus.singleFunctor C 0).obj Z)) := by
    rw [NatTrans.app_shift, Iso.inv_hom_id_app_assoc]
  have h6 : Q.rightDerivedFunctorPlus.map
          ((shiftFunctor (DerivedCategory.Plus D) (-q)).map (singleDerivedUnit P 0 Z)) ≫
        Q.rightDerivedFunctorPlus.map
            ((P.rightDerivedFunctorPlus.commShiftIso (-q)).inv.app
              ((DerivedCategory.Plus.singleFunctor C 0).obj Z)) ≫
          Q.rightDerivedFunctorPlus.map (P.rightDerivedFunctorPlus.map
            (((DerivedCategory.Plus.singleFunctors C).shiftIso (-q) q 0
              (by omega)).hom.app Z)) =
      Q.rightDerivedFunctorPlus.map
          (((DerivedCategory.Plus.singleFunctors D).shiftIso (-q) q 0 (by omega)).hom.app
            (P.obj Z)) ≫
        Q.rightDerivedFunctorPlus.map (singleDerivedUnit P q Z) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp, ← singleDerivedUnit_comm P (-q) q 0 (by omega) Z]
  exact star2_algebra
    ((shiftFunctor (DerivedCategory.Plus E) (-q)).map_comp _ _)
    h2
    ((rightDerivedPlusCompIso P Q).inv.naturality
      (((DerivedCategory.Plus.singleFunctors C).shiftIso (-q) q 0 (by omega)).hom.app Z))
    (Functor.commShiftIso_comp_inv_app P.rightDerivedFunctorPlus Q.rightDerivedFunctorPlus (-q)
      ((DerivedCategory.Plus.singleFunctor C 0).obj Z))
    (Functor.commShiftIso_inv_naturality Q.rightDerivedFunctorPlus
      (singleDerivedUnit P 0 Z) (-q))
    h6
    (Category.assoc _ _ _).symm

/-- **The degree-`p` homology of the degree-zero pullback is the degree-`p + q` homology of the
degree-`q` pullback**, through the comparison
`DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso` of the two degrees.

This is the square left open by [Stacks, Tag 0FMD] after the two pullbacks have been put in the
same language: the degree-zero instance is the degreewise comparison of a composite of right
derived functors, which the identification of the Picard group with first cohomology is natural
for, and the degree-one instance is the pullback on the hypercohomology the de Rham first Chern
class lives in. -/
theorem homologyFunctor_map_singleDerivedPullback_comm (p q : ℤ) (Z : C) :
    (DerivedCategory.Plus.homologyFunctor E p).map (singleDerivedPullback P Q 0 Z) ≫
        ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso
          (P ⋙ Q).rightDerivedFunctorPlus p q).app Z).inv =
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso
          Q.rightDerivedFunctorPlus p q).app (P.obj Z)).inv ≫
        (DerivedCategory.Plus.homologyFunctor E (p + q)).map
          (singleDerivedPullback P Q q Z) := by
  have hnat : (DerivedCategory.Plus.homologyFunctor E p).map (singleDerivedPullback P Q 0 Z) ≫
        ((DerivedCategory.Plus.homologyFunctor E 0).shiftIso (-q) (p + q) p (by omega)).inv.app
          ((P ⋙ Q).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor C 0).obj Z)) =
      ((DerivedCategory.Plus.homologyFunctor E 0).shiftIso (-q) (p + q) p (by omega)).inv.app
          (Q.rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor D 0).obj (P.obj Z))) ≫
        (DerivedCategory.Plus.homologyFunctor E (p + q)).map
          ((shiftFunctor (DerivedCategory.Plus E) (-q)).map
            (singleDerivedPullback P Q 0 Z)) :=
    ((DerivedCategory.Plus.homologyFunctor E 0).shiftIso (-q) (p + q) p
      (by omega)).inv.naturality _
  rw [singleFunctorCompHomologyFunctorShiftIso_inv_app,
    singleFunctorCompHomologyFunctorShiftIso_inv_app]
  refine comp_eq_of_nat hnat ?_
  have := congrArg (DerivedCategory.Plus.homologyFunctor E (p + q)).map
    (singleDerivedPullback_comm P Q q Z)
  simp only [Functor.map_comp] at this
  exact this.trans (assoc _ _ _).symm

end Stacks.DerivedIndexing

end
