module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# Base change of an abelian direct image along a finite morphism, at the canonical comparison

Let
```
Y' --π'--> Y
|e'        |e
v          v
T' --π---> T
```
be a cartesian square of schemes with `π` finite. This file proves that the canonical comparison
`e⁻¹ π_* ⟶ π'_* (e')⁻¹` of `Stacks.EtaleCohomology.smallEtaleBaseChangeAb` is an isomorphism.

The statement itself is [Stacks, Tag 0959] for abelian sheaves, and the abelian case is already
available in this library as
`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite`. What is *not* available is the
statement at the comparison `Stacks.EtaleCohomology.smallEtaleBaseChangeAb`, which is the
comparison the higher-direct-image development of [Stacks, Tag 0F02] is written with, and the two
comparisons are different terms:

* `Stacks.EtaleCohomology.etaleAbelianBaseChange` is a mate along the adjunctions
  `Stacks.EtaleCohomology.etaleAbelianInverseImageDirectImageAdj`, whose left adjoint is the
  inverse image built as a left Kan extension followed by sheafification, Mathlib's
  `CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback`;
* `Stacks.EtaleCohomology.smallEtaleBaseChangeAb` is a mate along the adjunctions
  `Stacks.EtaleCohomology.smallEtaleAdjunctionAb`, whose left adjoint is the *abstract* left
  adjoint `CategoryTheory.Functor.sheafPullback` of the direct image, a chosen one with no
  construction attached.

The two left adjoints are isomorphic and not equal, so no amount of rewriting inside one
comparison produces the other. The bridge proved here is a general fact about mates:

**a mate taken along two adjunctions transports along a change of the two left adjoints with the
same right adjoints** (`Stacks.CategoryTheory.mateEquiv_symm_eq_leftAdjointUniq`), the transport
being whiskering with `CategoryTheory.Adjunction.leftAdjointUniq`. Invertibility therefore passes
between the two comparisons in both directions.

## Main results

* `Stacks.CategoryTheory.mateEquiv_symm_eq_leftAdjointUniq` and
  `Stacks.CategoryTheory.isIso_mateEquiv_symm_of_leftAdjointUniq` — the mate of a 2-cell between
  composites of right adjoints, taken along two different choices of the two left adjoints, is the
  same up to whiskering with the canonical comparisons of left adjoints; invertibility transfers.
* `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite_of_isPullback` — the abelian
  comparison of the proper base change development is invertible for a cartesian square of
  *arbitrary* schemes with `f` finite, with no big étale site in the hypotheses.
* `Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_isIso_etaleAbelianBaseChange` — the
  bridge: invertibility of `etaleAbelianBaseChange` gives invertibility of
  `smallEtaleBaseChangeAb`.
* `Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_isFinite` — **the conclusion**:
  `smallEtaleBaseChangeAb` is invertible for a cartesian square with `π` finite.
* `Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_isIso_smallEtaleBaseChangeNatTrans` and
  `Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_isIso_sets` — **the reduction to set
  coefficients**, with no condition on the morphism: `smallEtaleBaseChangeAb` is invertible as
  soon as `AlgebraicGeometry.smallEtaleBaseChangeNatTrans` is. This is what makes
  [Stacks, Tag 0EYP] — the set-valued statement for an *integral* morphism — give the abelian
  statement for an integral morphism, which is
  `Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_isIntegralHom`.

## Implementation notes

**The big étale site is eliminated, not assumed.**
`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite` carries the four schemes of the
square as objects of a big étale site, its module docstring recording that nothing constructs such
a site around given schemes. That is no longer so:
`AlgebraicGeometry.BigEtaleSite.exists_contains_of_small` produces a big étale site containing any
small set of schemes, and a morphism of a full subcategory is its underlying morphism, so the
containment is discharged here for an arbitrary square.

**Why the comparison of the two direct-image 2-cells is cheap.** Both comparisons are mates of a
2-cell between composites of *direct* images, and direct image is restriction of sections along a
functor of sites; the two 2-cells are the same composite of
`CategoryTheory.Functor.sheafPushforwardContinuousComp'`, one written with the composite
`e ≫ π` named and the other with it written out, so they differ by the transport
`Stacks.EtaleCohomology.etaleAbelianDirectImageCompIso'_rfl` already in the library.

## References

* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
* [Stacks Project, Tag 0EYP](https://stacks.math.columbia.edu/tag/0EYP)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.TwoSquare CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.CategoryTheory

/-! ### A mate under a change of the two left adjoints -/

section Mates

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ L₁' : C ⥤ D} {R₁ : D ⥤ C} {L₂ L₂' : E ⥤ F} {R₂ : F ⥤ E}

/-- The component of the mate of a 2-cell between composites of right adjoints: the inverse
image of the unit, the 2-cell, and the counit. -/
private lemma mateEquiv_symm_natTrans_app (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (β : TwoSquare R₁ H G R₂) (c : C) :
    ((mateEquiv adj₁ adj₂).symm β).app c =
      L₂.map (G.map (adj₁.unit.app c)) ≫ L₂.map (β.app (L₁.obj c)) ≫
        adj₂.counit.app (H.obj (L₁.obj c)) := by
  simp [mateEquiv]

/-- **Two choices of a left adjoint are interchangeable in a counit composite.** A morphism into
the right adjoint, followed by the counit, is the comparison of the two left adjoints followed by
the same composite for the other adjunction. -/
private lemma counit_comp_leftAdjointUniq (adj₂ : L₂ ⊣ R₂) (adj₂' : L₂' ⊣ R₂) {Z : E} {W : F}
    (k : Z ⟶ R₂.obj W) :
    L₂.map k ≫ adj₂.counit.app W =
      (Adjunction.leftAdjointUniq adj₂ adj₂').hom.app Z ≫ L₂'.map k ≫ adj₂'.counit.app W := by
  rw [← Adjunction.leftAdjointUniq_hom_app_counit adj₂ adj₂' W, ← Category.assoc,
    NatTrans.naturality]
  simp

/-- The componentwise form of `Stacks.CategoryTheory.mateEquiv_symm_eq_leftAdjointUniq`. -/
private lemma mateEquiv_symm_natTrans_app_eq (adj₁ : L₁ ⊣ R₁) (adj₁' : L₁' ⊣ R₁)
    (adj₂ : L₂ ⊣ R₂) (adj₂' : L₂' ⊣ R₂) (β : TwoSquare R₁ H G R₂) (c : C) :
    L₂.map (G.map (adj₁.unit.app c)) ≫ L₂.map (β.app (L₁.obj c)) ≫
        adj₂.counit.app (H.obj (L₁.obj c)) =
      (Adjunction.leftAdjointUniq adj₂ adj₂').hom.app (G.obj c) ≫
        (L₂'.map (G.map (adj₁'.unit.app c)) ≫ L₂'.map (β.app (L₁'.obj c)) ≫
          adj₂'.counit.app (H.obj (L₁'.obj c))) ≫
        H.map ((Adjunction.leftAdjointUniq adj₁ adj₁').inv.app c) := by
  have hu : adj₁'.unit.app c ≫ R₁.map ((Adjunction.leftAdjointUniq adj₁ adj₁').inv.app c) =
      adj₁.unit.app c := by
    rw [Adjunction.leftAdjointUniq_inv_app]
    exact Adjunction.unit_leftAdjointUniq_hom_app adj₁' adj₁ c
  have hβ := β.naturality ((Adjunction.leftAdjointUniq adj₁ adj₁').inv.app c)
  simp only [Functor.comp_map] at hβ
  have hinner : G.map (adj₁.unit.app c) ≫ β.app (L₁.obj c) =
      G.map (adj₁'.unit.app c) ≫ β.app (L₁'.obj c) ≫
        R₂.map (H.map ((Adjunction.leftAdjointUniq adj₁ adj₁').inv.app c)) := by
    rw [← hβ, ← hu, G.map_comp, Category.assoc]
  have hcn := adj₂.counit.naturality
    (H.map ((Adjunction.leftAdjointUniq adj₁ adj₁').inv.app c))
  simp only [Functor.comp_map, Functor.id_map] at hcn
  have h₁ : L₂.map (G.map (adj₁.unit.app c)) ≫ L₂.map (β.app (L₁.obj c)) ≫
        adj₂.counit.app (H.obj (L₁.obj c)) =
      L₂.map ((G.map (adj₁'.unit.app c) ≫ β.app (L₁'.obj c)) ≫
        R₂.map (H.map ((Adjunction.leftAdjointUniq adj₁ adj₁').inv.app c))) ≫
        adj₂.counit.app (H.obj (L₁.obj c)) := by
    rw [← Functor.map_comp_assoc, hinner, Category.assoc]
  have h₂ : L₂.map ((G.map (adj₁'.unit.app c) ≫ β.app (L₁'.obj c)) ≫
        R₂.map (H.map ((Adjunction.leftAdjointUniq adj₁ adj₁').inv.app c))) ≫
        adj₂.counit.app (H.obj (L₁.obj c)) =
      (Adjunction.leftAdjointUniq adj₂ adj₂').hom.app (G.obj c) ≫
        (L₂'.map (G.map (adj₁'.unit.app c)) ≫ L₂'.map (β.app (L₁'.obj c)) ≫
          adj₂'.counit.app (H.obj (L₁'.obj c))) ≫
        H.map ((Adjunction.leftAdjointUniq adj₁ adj₁').inv.app c) := by
    rw [Functor.map_comp, Category.assoc, hcn, ← Category.assoc,
      counit_comp_leftAdjointUniq adj₂ adj₂'
        (G.map (adj₁'.unit.app c) ≫ β.app (L₁'.obj c))]
    simp only [Functor.map_comp, Category.assoc, Functor.id_obj]
  exact h₁.trans h₂

/-- **A mate transports along a change of the two left adjoints.** For a 2-cell `β` between the
composites of the right adjoints of a square of adjunctions, the mate of `β` taken along
`adj₁`, `adj₂` and the mate taken along two other adjunctions `adj₁'`, `adj₂'` with the *same*
right adjoints differ only by whiskering with the canonical comparisons
`CategoryTheory.Adjunction.leftAdjointUniq` of the left adjoints.

Unlike a change of the 2-cell, a change of the chosen left adjoints is therefore harmless: the
two mates are invertible together. -/
public theorem mateEquiv_symm_eq_leftAdjointUniq
    (adj₁ : L₁ ⊣ R₁) (adj₁' : L₁' ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₂' : L₂' ⊣ R₂)
    (β : TwoSquare R₁ H G R₂) :
    ((mateEquiv adj₁ adj₂).symm β) =
      (Functor.isoWhiskerLeft G (Adjunction.leftAdjointUniq adj₂ adj₂')).hom ≫
        ((mateEquiv adj₁' adj₂').symm β) ≫
        (Functor.isoWhiskerRight (Adjunction.leftAdjointUniq adj₁ adj₁').symm H).hom := by
  refine NatTrans.ext (funext fun c => ?_)
  simp only [NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
    mateEquiv_symm_natTrans_app]
  exact mateEquiv_symm_natTrans_app_eq adj₁ adj₁' adj₂ adj₂' β c

/-- **Invertibility of a mate transports along a change of the two left adjoints.** -/
public theorem isIso_mateEquiv_symm_of_leftAdjointUniq
    (adj₁ : L₁ ⊣ R₁) (adj₁' : L₁' ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₂' : L₂' ⊣ R₂)
    (β : TwoSquare R₁ H G R₂)
    (h : IsIso ((mateEquiv adj₁' adj₂').symm β)) :
    IsIso ((mateEquiv adj₁ adj₂).symm β) := by
  rw [mateEquiv_symm_eq_leftAdjointUniq adj₁ adj₁' adj₂ adj₂' β]
  infer_instance

end Mates

end Stacks.CategoryTheory

namespace Stacks.EtaleCohomology

/-! ### The abelian comparison of the proper base change development, without a big étale site -/

/-- **The abelian base change comparison of a cartesian square with finite `f` is invertible**,
for a square of arbitrary schemes. This is
`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite` with its hypothesis that the
four schemes lie in a big étale site discharged: a big étale site containing any small set of
schemes exists, by `AlgebraicGeometry.BigEtaleSite.exists_contains_of_small`, and a morphism of
the full subcategory it cuts out is its own underlying morphism of schemes. -/
public alias isIso_etaleAbelianBaseChange_of_isFinite_of_isPullback :=
    Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isPullback_of_isFinite

/-! ### The two comparisons agree -/

section Bridge

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)

/-- The composition comparison for direct images with the composite named is the one with the
composite written out, up to the transport along the naming. -/
private lemma etaleAbelianDirectImageCompIso'_inv {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (ab : X ⟶ Z) (hab : ab = a ≫ b) :
    (etaleAbelianDirectImageCompIso'.{u, 0} a b ab hab).inv =
      eqToHom (congrArg (fun m : X ⟶ Z => etaleAbelianDirectImage.{u, 0} m) hab) ≫
        (etaleAbelianDirectImageCompIso.{u, 0} a b).inv := by
  subst hab
  rw [etaleAbelianDirectImageCompIso'_rfl]
  simp

/-- **The 2-cell that `smallEtaleBaseChangeAb` is the mate of is the one that
`etaleAbelianBaseChange` is the mate of.** Both identify the two composite direct images around
the square; one writes the diagonal `e ≫ g` out and transports along the commutativity, the other
carries the diagonal as a named morphism. -/
private lemma pushforwardCell_eq (w : h ≫ f' = e ≫ g) :
    ((smallEtalePushforwardAbCompIso e g).trans
        ((eqToIso (congrArg smallEtalePushforwardAb w.symm)).trans
          (smallEtalePushforwardAbCompIso h f').symm)).hom =
      (etaleAbelianDirectImageCompIso'.{u, 0} e g (e ≫ g) rfl).hom ≫
        (etaleAbelianDirectImageCompIso'.{u, 0} h f' (e ≫ g) w.symm).inv := by
  rw [etaleAbelianDirectImageCompIso'_rfl, etaleAbelianDirectImageCompIso'_inv]
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
  rfl

/-- `Stacks.EtaleCohomology.smallEtaleBaseChangeAb` is Mathlib's mate of the comparison of the
two composite direct images around the square. -/
private lemma smallEtaleBaseChangeAb_eq_mateEquiv_symm (w : h ≫ f' = e ≫ g) :
    smallEtaleBaseChangeAb f' g h e w =
      ((mateEquiv (smallEtaleAdjunctionAb e) (smallEtaleAdjunctionAb f')).symm
        (TwoSquare.mk _ _ _ _
          ((smallEtalePushforwardAbCompIso e g).trans
            ((eqToIso (congrArg smallEtalePushforwardAb w.symm)).trans
              (smallEtalePushforwardAbCompIso h f').symm)).hom)) :=
  Stacks.Cohomology.BaseChange.mate_eq_mateEquiv_symm _ _ _ _ _

/-- **The bridge between the two abelian base change comparisons.** The comparison
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb` of the higher-direct-image development and the
comparison `Stacks.EtaleCohomology.etaleAbelianBaseChange` of the proper base change development
are mates of the same 2-cell between composite direct images, taken along two different choices of
the inverse image: the abstract left adjoint of the direct image in the first case, the left Kan
extension followed by sheafification in the second. They are therefore invertible together, by
`Stacks.CategoryTheory.isIso_mateEquiv_symm_of_leftAdjointUniq`. -/
public theorem isIso_smallEtaleBaseChangeAb_of_isIso_etaleAbelianBaseChange
    (w : h ≫ f' = e ≫ g)
    (hiso : IsIso (etaleAbelianBaseChange.{u, 0} g f' e h w.symm)) :
    IsIso (smallEtaleBaseChangeAb f' g h e w) := by
  rw [smallEtaleBaseChangeAb_eq_mateEquiv_symm f' g h e w]
  refine Stacks.CategoryTheory.isIso_mateEquiv_symm_of_leftAdjointUniq
    (smallEtaleAdjunctionAb e) (etaleAbelianInverseImageDirectImageAdj.{u, 0} e)
    (smallEtaleAdjunctionAb f') (etaleAbelianInverseImageDirectImageAdj.{u, 0} f') _ ?_
  rw [etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso.{u, 0} g f' e h w.symm
    (e ≫ g) rfl w.symm] at hiso
  rwa [pushforwardCell_eq f' g h e w]

end Bridge

/-! ### Stacks 0959 for abelian sheaves, at the comparison `smallEtaleBaseChangeAb` -/

/-- **Base change of an abelian direct image along a finite morphism, at the comparison
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb`.** For a cartesian square
```
Y' --π'--> Y
|e'        |e
v          v
T' --π---> T
```
of schemes with `π` finite, the canonical comparison `e⁻¹ π_* ⟶ π'_* (e')⁻¹` of abelian sheaves on
the small étale sites is an isomorphism.

This is [Stacks, Tag 0959] for abelian coefficients, stated at the comparison which the
higher-direct-image development of [Stacks, Tag 0F02] uses. The abelian statement at the
comparison of the proper base change development is
`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite`; the passage between the two
comparisons is
`Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_isIso_etaleAbelianBaseChange`, and no big
étale site occurs in the hypotheses.

[Stacks, Tag 0EYP] is this statement with `π` merely *integral*. It does not follow from this one:
the source's passage from a finite morphism to an integral one presents the comparison as a
colimit of the comparisons for the finite stages of the integral morphism, and that presentation
is not available in this library for abelian coefficients. -/
@[stacks 0959 "for abelian sheaves, at the comparison `smallEtaleBaseChangeAb` of \
[Stacks, Tag 0F02]; the morphism is finite, not merely integral, so this is 0959 and not 0EYP"]
public theorem isIso_smallEtaleBaseChangeAb_of_isFinite {Y Y' T T' : Scheme.{u}} (e : Y ⟶ T)
    (π : T' ⟶ T) (π' : Y' ⟶ Y) (e' : Y' ⟶ T') (sq : IsPullback π' e' e π) [IsFinite π] :
    IsIso (smallEtaleBaseChangeAb e π π' e' sq.w) :=
  isIso_smallEtaleBaseChangeAb_of_isIso_etaleAbelianBaseChange e π π' e' sq.w
    (isIso_etaleAbelianBaseChange_of_isFinite_of_isPullback π e e' π' sq.flip)

/-! ### The abelian comparison from the comparison at set coefficients

What the finite hypothesis is used for, and only for, is the invertibility of the comparison at
**set** coefficients on the size-bounded small étale site,
`AlgebraicGeometry.smallEtaleBaseChangeNatTrans`. The two statements below record that: the
abelian comparison `smallEtaleBaseChangeAb` is invertible as soon as that one is, with no
condition on the morphism at all. [Stacks, Tag 0EYP] — the set-valued comparison for an
*integral* morphism — therefore gives the abelian statement for an integral morphism,
`Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_isIntegralHom`. -/

/-- **The abelian comparison `smallEtaleBaseChangeAb` is invertible as soon as the comparison at
set coefficients is**, for a commutative square of the underlying category of a big étale site.
No condition is placed on the morphisms: finiteness, integrality and even cartesianness enter
only through the hypothesis `hsets`, which is the invertibility of
`AlgebraicGeometry.smallEtaleBaseChangeNatTrans`.

Composed with [Stacks, Tag 0959] this is
`Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_isFinite`; composed with
[Stacks, Tag 0EYP] it is the same statement for an integral morphism. -/
public theorem isIso_smallEtaleBaseChangeAb_of_isIso_smallEtaleBaseChangeNatTrans
    (B : BigEtaleSite.{u}) {X X' Y Y' : B.Scheme} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (f' : X' ⟶ Y') (hcomm : g' ≫ f = f' ≫ g)
    (hsets : ∀ F, IsIso ((AlgebraicGeometry.smallEtaleBaseChangeNatTrans B g' f' f g hcomm).app F))
    (w : B.inclusion.map f' ≫ B.inclusion.map g =
      B.inclusion.map g' ≫ B.inclusion.map f) :
    IsIso (smallEtaleBaseChangeAb (B.inclusion.map g) (B.inclusion.map f)
      (B.inclusion.map f') (B.inclusion.map g') w) :=
  isIso_smallEtaleBaseChangeAb_of_isIso_etaleAbelianBaseChange _ _ _ _ w
    (isIso_etaleAbelianBaseChange_of_isIso_smallEtaleBaseChangeNatTrans B f g g' f' hcomm hsets
      w.symm)

/-- **The abelian comparison `smallEtaleBaseChangeAb` of a cartesian square of arbitrary schemes
is invertible as soon as the comparison at set coefficients is.** The big étale site of the
set-valued statement is quantified over rather than fixed, which is how the set-valued statement
is proved in this library; a big étale site containing the four schemes exists, so the hypothesis
is used at one of them and the conclusion mentions none.

With `π` integral, `hsets` is [Stacks, Tag 0EYP] at set coefficients, and this is how
`Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_isIntegralHom` is proved. -/
public theorem isIso_smallEtaleBaseChangeAb_of_isIso_sets {Y Y' T T' : Scheme.{u}} (e : Y ⟶ T)
    (π : T' ⟶ T) (π' : Y' ⟶ Y) (e' : Y' ⟶ T') (sq : IsPullback π' e' e π)
    (hsets : ∀ (B : BigEtaleSite.{u}) (hT' : B.Contains T') (hT : B.Contains T)
        (hY : B.Contains Y) (hY' : B.Contains Y')
        (hw : ObjectProperty.homMk (X := B.obj Y' hY') (Y := B.obj T' hT') e' ≫
            ObjectProperty.homMk (X := B.obj T' hT') (Y := B.obj T hT) π =
          ObjectProperty.homMk (X := B.obj Y' hY') (Y := B.obj Y hY) π' ≫
            ObjectProperty.homMk (X := B.obj Y hY) (Y := B.obj T hT) e)
        (F : Sheaf (SmallEtale.topology B T' hT') (Type (u + 1))),
      IsIso ((AlgebraicGeometry.smallEtaleBaseChangeNatTrans B _ _ _ _ hw).app F)) :
    IsIso (smallEtaleBaseChangeAb e π π' e' sq.w) := by
  have : Small.{u} ({Y'} : Set Scheme.{u}) := small_single.{u} Y'
  obtain ⟨B, hB⟩ :=
    BigEtaleSite.exists_contains_of_small ({T', T, Y, Y'} : Set Scheme.{u})
  have hT' : B.Contains T' := hB T' (by simp)
  have hT : B.Contains T := hB T (by simp)
  have hY : B.Contains Y := hB Y (by simp)
  have hY' : B.Contains Y' := hB Y' (by simp)
  have hw : ObjectProperty.homMk (X := B.obj Y' hY') (Y := B.obj T' hT') e' ≫
        ObjectProperty.homMk (X := B.obj T' hT') (Y := B.obj T hT) π =
      ObjectProperty.homMk (X := B.obj Y' hY') (Y := B.obj Y hY) π' ≫
        ObjectProperty.homMk (X := B.obj Y hY) (Y := B.obj T hT) e :=
    ObjectProperty.hom_ext _ sq.w.symm
  exact isIso_smallEtaleBaseChangeAb_of_isIso_smallEtaleBaseChangeNatTrans B _ _ _ _ hw
    (hsets B hT' hT hY hY' hw) sq.w

end Stacks.EtaleCohomology

end
