module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedHomChainIdentification
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.LinkApplyLemmas

/-!
# The chain of Tag 09LK carries a morphism to its differential graded Yoneda image

The four links of [Stacks, Tag 09LK] are bijections, and
`StacksFrontier/CategoryTheory/DifferentialGraded/RightModule/LinkApplyLemmas.lean` computes each of
them as a closed formula. A closed formula is not yet a *compatibility*: what the assembly of the
proof has to know is that the chain carries a distinguished *element* to a distinguished element,
namely that the fourth link

`Hom_{DA}(q x, (q y)⟦n⟧) ≃ Hom_{K(Mod^dg(C))/N}(Q h_x, (Q h_y)⟦n⟧)`

takes the image `q(f)` of a morphism `f : x ⟶ y⟦n⟧` of `K(C)` under the localization `q` to the
image `Q(h_f)` of its differential graded Yoneda image. No lemma of that shape existed: the value
lemmas express the link through its two engines and say nothing about a functor applied to a
morphism.

## The one computation that does it

Both engines of the fourth link are *conjugations by the characteristic isomorphism of a lift*:

* `CategoryTheory.homShiftEquivOfIsLocalization` conjugates by
  `CategoryTheory.Localization.compUniqFunctor`, and
* `CategoryTheory.ObjectProperty.homEquivVerdierEmbeddingShift` conjugates by
  `CategoryTheory.ObjectProperty.verdierEmbeddingCompIso`,

and in both cases that isomorphism is a `CategoryTheory.Localization.Lifting.iso`, hence compatible
with the shift by Mathlib's `CategoryTheory.NatTrans.commShift_iso_hom_of_localization`. So both
reduce to one lemma, `CategoryTheory.conj_map_comp_commShiftIso`: conjugating `F(q₁ f)` by a
shift-compatible `e : q₁ ⋙ F ≅ q₂` gives `q₂ f`, the shift commutations being absorbed by
naturality of `e` and by its shift compatibility.

## What this buys for the identification `(*)`

`CochainComplex.derivedHomLiftIdentificationOfNaturality` reduces `(*)` to its `unit_app_id`
clause: that the chain, at the `β`-image of a cohomology class, is `Q` of the morphism that the
class is by [Tag 09LC]. With the fourth link's compatibility available, that clause is no longer a
statement about four opaque bijections. Two further results here say exactly what is left:

* `CategoryTheory.ObjectProperty.homEquivReflectorShift_apply_unit` does the same job for the
  *second* link: on a morphism of the form `η⟦n⟧ ∘ u` the link is `Q(u)` followed by the shift
  commutation, the unit having cancelled against the unit isomorphism of the quotient. This is the
  left fraction of `CategoryTheory.ObjectProperty.homEquivReflectorShift_apply_inv` evaluated where
  the fraction is trivial.
* `DGCategory.RightModule.chainEquivReflectorEvaluation_apply_yonedaOnK` composes the two: the
  chain `H^n(ev_x(L h_y)) ≃ Hom_{DA}(q x, (q y)⟦n⟧)` carries the class that the first link assigns
  to `η⟦n⟧ ∘ h_f` to `q(f)`, unconditionally.

So what `unit_app_id` still owes is an identification of elements inside the *first* link alone:
that the class `β` produces out of a degree-`n` cohomology class of `Hom^•(K, Y)` is the class the
first link assigns to `η⟦n⟧ ∘ h_f`, with `f` the morphism of the homotopy category that the class
is by [Tag 09LC]. Nothing about links 2, 3 or 4 remains, and the first link computes
(`DGCategory.RightModule.homShiftEquivGradedCohomology_mk`). That last identification is not proved
here, and neither is the comparison of `K(C)` with `K(A)` that reading `DA` as a derived category
needs.

## Main results

* `CategoryTheory.conj_map_comp_commShiftIso`: the shared computation.
* `CategoryTheory.homShiftEquivOfIsLocalization_map` and
  `CategoryTheory.ObjectProperty.homEquivVerdierEmbeddingShift_map`: the two engines on the image
  of a morphism.
* `CategoryTheory.ObjectProperty.homEquivReflectorShift_apply_unit`: the second link on the image
  of a morphism composed with the unit.
* `DGCategory.RightModule.homEquivDerivedYonedaOnK_map` and
  `DGCategory.RightModule.homEquivDerivedYonedaOnK'_map`: **the fourth link is compatible with the
  differential graded Yoneda functor.**
* `DGCategory.RightModule.chainEquivReflectorEvaluation_eq_iff` and
  `DGCategory.RightModule.chainEquivReflectorEvaluation_apply_yonedaOnK`: the chain at a value.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK);
  [Tag 09LC](https://stacks.math.columbia.edu/tag/09LC), the identification of a degree-`n`
  cohomology class of a Hom complex with a morphism into an `n`-fold shift.
-/

@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃ v u v' u' r

namespace CategoryTheory

open Category Limits Pretriangulated

section Conj

variable {S : Type u} [Category.{v} S] [HasShift S ℤ]
  {D₁ : Type u₁} [Category.{v₁} D₁] [HasShift D₁ ℤ]
  {D₂ : Type u₂} [Category.{v₂} D₂] [HasShift D₂ ℤ]
  (q₁ : S ⥤ D₁) [q₁.CommShift ℤ] (q₂ : S ⥤ D₂) [q₂.CommShift ℤ]
  (F : D₁ ⥤ D₂) [F.CommShift ℤ] (e : q₁ ⋙ F ≅ q₂) [NatTrans.CommShift e.hom ℤ]

/-- **Conjugating the image of a morphism by a shift-compatible isomorphism of functors.** Let
`q₁ : S ⥤ D₁` and `q₂ : S ⥤ D₂` commute with the shift, let `F : D₁ ⥤ D₂` commute with it, and let
`e : q₁ ⋙ F ≅ q₂` be compatible with it. Then conjugating the `F`-image of `q₁(f)` — for `f` a
morphism `x ⟶ y⟦n⟧` of `S`, with the shift moved out of the argument on the target as in
`CategoryTheory.uniqFunctorShiftIso` — gives `q₂(f)`.

This is the computation both engines of the fourth link of [Stacks, Tag 09LK] reduce to. The proof
is naturality of `e` at `f` on the source and the shift compatibility of `e` at `y` on the target;
nothing about localization enters. -/
theorem conj_map_comp_commShiftIso (x y : S) (n : ℤ) (f : x ⟶ y⟦n⟧) :
    e.inv.app x ≫ F.map (q₁.map f ≫ (q₁.commShiftIso n).hom.app y) ≫
        (F.commShiftIso n).hom.app (q₁.obj y) ≫
          (shiftFunctor D₂ n).map (e.hom.app y) =
      q₂.map f ≫ (q₂.commShiftIso n).hom.app y := by
  have hcs : F.map ((q₁.commShiftIso n).hom.app y) ≫
      (F.commShiftIso n).hom.app (q₁.obj y) ≫ (shiftFunctor D₂ n).map (e.hom.app y) =
        e.hom.app (y⟦n⟧) ≫ (q₂.commShiftIso n).hom.app y := by
    have h := NatTrans.shift_app_comm e.hom n y
    rw [Functor.commShiftIso_comp_hom_app, assoc] at h
    exact h
  have hn : F.map (q₁.map f) ≫ e.hom.app (y⟦n⟧) = e.hom.app x ≫ q₂.map f :=
    e.hom.naturality f
  rw [F.map_comp, assoc, hcs, reassoc_of% hn, Iso.inv_hom_id_app_assoc]

/-- **The image of a morphism under a composite of two functors commuting with the shift.** For
`f : x ⟶ y⟦n⟧` the morphism `(Φ ⋙ Q)(f)` followed by the shift commutation of the composite is
`Q` of `Φ(f)` followed by the shift commutation of `Φ`, followed by that of `Q`. Bookkeeping, but
it is what lets a statement about `Φ ⋙ Q` be compared with one about `Q` alone. -/
theorem comp_map_comp_commShiftIso {T : Type u₃} [Category.{v₃} T] [HasShift T ℤ]
    (Φ : S ⥤ T) [Φ.CommShift ℤ] (Q : T ⥤ D₂) [Q.CommShift ℤ] (x y : S) (n : ℤ)
    (f : x ⟶ y⟦n⟧) :
    (Φ ⋙ Q).map f ≫ ((Φ ⋙ Q).commShiftIso n).hom.app y =
      Q.map (Φ.map f ≫ (Φ.commShiftIso n).hom.app y) ≫
        (Q.commShiftIso n).hom.app (Φ.obj y) := by
  simp [Functor.commShiftIso_comp_hom_app]

end Conj

section Engine1

variable {S : Type u} [Category.{v} S] [HasShift S ℤ]
  {D₁ : Type u₁} [Category.{v₁} D₁] [HasShift D₁ ℤ]
  {D₂ : Type u₂} [Category.{v₂} D₂] [HasShift D₂ ℤ]
  (W : MorphismProperty S)
  (q₁ : S ⥤ D₁) [q₁.IsLocalization W] [q₁.CommShift ℤ]
  (q₂ : S ⥤ D₂) [q₂.IsLocalization W] [q₂.CommShift ℤ]

/-- **The first engine of the fourth link on the image of a morphism.** For two localizations
`q₁`, `q₂` of `S` at the same class of morphisms, both commuting with the shift, the comparison
bijection `CategoryTheory.homShiftEquivOfIsLocalization` carries `q₁(f)` to `q₂(f)`.

The comparison equivalence `CategoryTheory.Localization.uniq` has
`CategoryTheory.Localization.compUniqFunctor` as the characteristic isomorphism of its lifting,
which is shift-compatible by `CategoryTheory.NatTrans.commShift_iso_hom_of_localization`; so this
is `CategoryTheory.conj_map_comp_commShiftIso`. -/
theorem homShiftEquivOfIsLocalization_map (x y : S) (n : ℤ) (f : x ⟶ y⟦n⟧) :
    homShiftEquivOfIsLocalization W q₁ q₂ x y n
        (q₁.map f ≫ (q₁.commShiftIso n).hom.app y) =
      q₂.map f ≫ (q₂.commShiftIso n).hom.app y := by
  let := commShiftUniqFunctor W q₁ q₂
  have : NatTrans.CommShift (Localization.compUniqFunctor q₁ q₂ W).hom ℤ :=
    NatTrans.commShift_iso_hom_of_localization q₁ W ℤ q₂ (Localization.uniq q₁ q₂ W).functor
  rw [homShiftEquivOfIsLocalization_apply, uniqFunctorShiftIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv]
  exact conj_map_comp_commShiftIso q₁ q₂ (Localization.uniq q₁ q₂ W).functor
    (Localization.compUniqFunctor q₁ q₂ W) x y n f

end Engine1

namespace ObjectProperty

section Engine2

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (A N : ObjectProperty C) [A.IsClosedUnderIsomorphisms] [A.IsTriangulated]
  [N.IsClosedUnderIsomorphisms] [N.IsTriangulated]
  {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  (L : A.FullSubcategory ⥤ D) [L.IsLocalization (N.inverseImage A.ι).trW] [L.CommShift ℤ]
  [L.IsTriangulated]

omit [A.IsClosedUnderIsomorphisms] [HasZeroObject D] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D] [L.IsTriangulated] in
/-- **The second engine of the fourth link on the image of a morphism.** The bijection
`CategoryTheory.ObjectProperty.homEquivVerdierEmbeddingShift` carries the image of `f` under the
quotient `L` of the subcategory to its image under `A.ι ⋙ Q`, the inclusion followed by the Verdier
quotient of the ambient category.

The embedding `CategoryTheory.ObjectProperty.verdierEmbedding` is a descent along `L`, so
`CategoryTheory.ObjectProperty.verdierEmbeddingCompIso` is the characteristic isomorphism of a
lifting and is shift-compatible; this is again
`CategoryTheory.conj_map_comp_commShiftIso`. -/
theorem homEquivVerdierEmbeddingShift_map [A.IsVerdierLeftLocalizing N]
    (x y : A.FullSubcategory) (n : ℤ) (f : x ⟶ y⟦n⟧) :
    homEquivVerdierEmbeddingShift A N L x y n (L.map f ≫ (L.commShiftIso n).hom.app y) =
      (A.ι ⋙ N.trW.Q).map f ≫ ((A.ι ⋙ N.trW.Q).commShiftIso n).hom.app y := by
  let := A.verdierEmbeddingCommShift N L
  have : NatTrans.CommShift (verdierEmbeddingCompIso A N L).hom ℤ :=
    NatTrans.commShift_iso_hom_of_localization L (N.inverseImage A.ι).trW ℤ
      (A.ι ⋙ N.trW.Q) (A.verdierEmbedding N L)
  rw [homEquivVerdierEmbeddingShift_apply, verdierEmbeddingShiftIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv]
  exact conj_map_comp_commShiftIso L (A.ι ⋙ N.trW.Q) (A.verdierEmbedding N L)
    (verdierEmbeddingCompIso A N L) x y n f

end Engine2

section Reflector

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)
  {D : Type u'} [Category.{v'} D] (Q : C ⥤ D)
  [Q.IsLocalization P.localizingClosure.{w}.trW] [HasShift D ℤ] [IsTriangulated C]
  [Q.CommShift ℤ] {L : C ⥤ C} {η : 𝟭 C ⟶ L}

/-- **The second link of [Stacks, Tag 09LK] on a morphism factoring through the unit.** On a
morphism of the shape `u ≫ (η X)⟦n⟧`, with `u : A ⟶ X⟦n⟧` not involving the reflector, the
bijection `CategoryTheory.ObjectProperty.homEquivReflectorShift` is `Q(u)` followed by the
commutation of `Q` with the shift — the inverse of the shifted unit isomorphism that
`CategoryTheory.ObjectProperty.homEquivReflectorShift_apply_inv` exhibits has cancelled against the
unit.

So the left fraction `Q(η)⟦n⟧⁻¹ ∘ Q(f)` is trivial exactly on the morphisms that come from the
ambient category, which is where the compatibility of the chain is evaluated. -/
theorem homEquivReflectorShift_apply_unit
    (hL : ∀ X, P.localizingClosure.{w}.rightOrthogonal (L.obj X))
    (hη : ∀ (X Z : C) (f : Z ⟶ X) (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk f (η.app X) g ∈ distTriang C → P.localizingClosure.{w} Z)
    (A X : C) (n : ℤ) (u : A ⟶ X⟦n⟧) :
    P.homEquivReflectorShift Q hL hη A X n (u ≫ (shiftFunctor C n).map (η.app X)) =
      Q.map u ≫ (Q.commShiftIso n).hom.app X := by
  rw [homEquivReflectorShift_apply]
  simp only [Iso.app_hom]
  rw [Q.map_comp, assoc, Q.commShiftIso_hom_naturality_assoc (η.app X) n, ← Functor.map_comp,
    ← P.localizingClosureUnitIso_hom Q hη X, Iso.hom_inv_id, Functor.map_id, comp_id]
  rfl

end Reflector

end ObjectProperty

end CategoryTheory

namespace DGCategory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.ObjectProperty

namespace RightModule

section Link4

variable {R : Type r} [CommRing R] (C : DGCategory.{v, u} R) {ι : Type*} (G : ι → C.Obj)

attribute [local implicit_reducible] DGCategory.K

variable [Preadditive C.K] [HasZeroObject C.K] [HasShift C.K ℤ]
  [∀ n : ℤ, (shiftFunctor C.K n).Additive] [Pretriangulated C.K]
  [((yonedaDGFunctor C).onK).CommShift ℤ] [((yonedaDGFunctor C).onK).IsTriangulated]

attribute [local instance] isLocalization_yonedaLift_comp

/-- **The third link over the essential image on the image of a morphism.** This is the second
engine, `CategoryTheory.ObjectProperty.homEquivVerdierEmbeddingShift_map`, at the essential image
of the differential graded Yoneda functor; nothing is reproved. -/
theorem homEquivYonedaImageVerdier_map (x y : (yonedaImage C).FullSubcategory) (n : ℤ)
    (f : x ⟶ y⟦n⟧) :
    homEquivYonedaImageVerdier C G x y n
        ((yonedaImageQ C G).map f ≫ (((yonedaImageQ C G)).commShiftIso n).hom.app y) =
      ((yonedaImage C).ι ⋙ (yonedaLocalizing C G).trW.Q).map f ≫
        (((yonedaImage C).ι ⋙ (yonedaLocalizing C G).trW.Q).commShiftIso n).hom.app y := by
  have := isVerdierLeftLocalizing_yonedaImage C G
  exact homEquivVerdierEmbeddingShift_map (yonedaImage C) (yonedaLocalizing C G)
    (yonedaImageQ C G) x y n f

/-- **The shift commutation of the lift `Φ'`, read inside `K(Mod^dg(C))`.** Pushing the shift
commutation of `Φ' : K(C) ⥤ A₀` into the ambient category along the inclusion of `A₀` and
following it with the shift commutation of the inclusion gives the shift commutation of `Φ`
itself.

This is the shift compatibility of the characteristic isomorphism `Φ' ⋙ ι ≅ Φ`,
`DGCategory.RightModule.natTransCommShift_liftCompιIso_yonedaLift`, together with the fact that
`CategoryTheory.ObjectProperty.liftCompιIso` is the identity isomorphism. -/
theorem commShiftIso_hom_app_ι_yonedaLift (y : C.K) (n : ℤ) :
    (yonedaImage C).ι.map (((yonedaLift C).commShiftIso n).hom.app y) ≫
        ((yonedaImage C).ι.commShiftIso n).hom.app ((yonedaLift C).obj y) =
      (((yonedaDGFunctor C).onK).commShiftIso n).hom.app y := by
  have h := NatTrans.shift_app_comm
    ((yonedaImage C).liftCompιIso ((yonedaDGFunctor C).onK)
      (fun X ↦ ⟨X, ⟨Iso.refl _⟩⟩)).hom n y
  rw [Functor.commShiftIso_comp_hom_app] at h
  simpa [ObjectProperty.liftCompιIso] using h

/-- **The fourth link of [Stacks, Tag 09LK] is compatible with the differential graded Yoneda
functor.** Let `q : K(C) ⥤ DA` be a localization of `K(C)` at the morphisms whose cone lies in
`Z = Φ⁻¹ N`, commuting with the shift. Then for every morphism `f : x ⟶ y⟦n⟧` of `K(C)` the
bijection `DGCategory.RightModule.homEquivDerivedYonedaOnK` carries the image of `f` under `q` to
the image of `f` under `Φ` followed by the Verdier quotient `Q` of `K(Mod^dg(C))` by `N`; that is,
it carries `q(f)` to `Q(h_f)`.

This is the statement the assembly of the replacement proof of [Stacks, Tag 09LK] needs and which
no value lemma supplies: the two engines are compatible with the images of morphisms
(`CategoryTheory.homShiftEquivOfIsLocalization_map` and
`DGCategory.RightModule.homEquivYonedaImageVerdier_map`), and the passage from the lift `Φ'` back
to `Φ` is `DGCategory.RightModule.commShiftIso_hom_app_ι_yonedaLift`. -/
theorem homEquivDerivedYonedaOnK_map {DA : Type u'} [Category.{v'} DA] [HasShift DA ℤ]
    (q : C.K ⥤ DA) [q.IsLocalization (yonedaInverseImage C G).trW] [q.CommShift ℤ]
    (x y : C.K) (n : ℤ) (f : x ⟶ y⟦n⟧) :
    homEquivDerivedYonedaOnK C G q x y n (q.map f ≫ (q.commShiftIso n).hom.app y) =
      (((yonedaDGFunctor C).onK ⋙ (yonedaLocalizing C G).trW.Q).map f) ≫
        (((yonedaDGFunctor C).onK ⋙
          (yonedaLocalizing C G).trW.Q).commShiftIso n).hom.app y := by
  rw [show homEquivDerivedYonedaOnK C G q x y n (q.map f ≫ (q.commShiftIso n).hom.app y) =
        homEquivYonedaImageVerdier C G ((yonedaLift C).obj x) ((yonedaLift C).obj y) n
          (homShiftEquivOfIsLocalization (yonedaInverseImage C G).trW q
            (yonedaLift C ⋙ yonedaImageQ C G) x y n
              (q.map f ≫ (q.commShiftIso n).hom.app y)) from rfl,
    homShiftEquivOfIsLocalization_map,
    CategoryTheory.comp_map_comp_commShiftIso (yonedaLift C) (yonedaImageQ C G) x y n f,
    homEquivYonedaImageVerdier_map]
  have hι : (yonedaImage C).ι.map ((yonedaLift C).map f ≫
          ((yonedaLift C).commShiftIso n).hom.app y) ≫
        ((yonedaImage C).ι.commShiftIso n).hom.app ((yonedaLift C).obj y) =
      ((yonedaDGFunctor C).onK).map f ≫
        (((yonedaDGFunctor C).onK).commShiftIso n).hom.app y := by
    rw [Functor.map_comp, Category.assoc, commShiftIso_hom_app_ι_yonedaLift]
    rfl
  simp only [Functor.comp_map, Functor.commShiftIso_comp_hom_app]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, hι]
  rfl

/-- **The fourth link is compatible with the Yoneda functor, with `N` written out as a localizing
closure.** The same statement as `DGCategory.RightModule.homEquivDerivedYonedaOnK_map` for the
spelling of the link that composes with the second one, in which
`DGCategory.RightModule.yonedaLocalizing` is unfolded. -/
theorem homEquivDerivedYonedaOnK'_map {DA : Type u'} [Category.{v'} DA] [HasShift DA ℤ]
    (q : C.K ⥤ DA) [q.IsLocalization (yonedaInverseImage C G).trW] [q.CommShift ℤ]
    (x y : C.K) (n : ℤ) (f : x ⟶ y⟦n⟧) :
    homEquivDerivedYonedaOnK' C G q x y n (q.map f ≫ (q.commShiftIso n).hom.app y) =
      (((yonedaDGFunctor C).onK ⋙
          (ofObj fun i ↦ yonedaObjK (G i)).localizingClosure.{v}.trW.Q).map f) ≫
        (((yonedaDGFunctor C).onK ⋙ (ofObj fun i ↦
          yonedaObjK (G i)).localizingClosure.{v}.trW.Q).commShiftIso n).hom.app y :=
  homEquivDerivedYonedaOnK_map C G q x y n f

end Link4

section Chain

variable {R : Type r} [CommRing R]
  (C : DGCategory.{v, v} R) [Preadditive C.K] [HasZeroObject C.K] [HasShift C.K ℤ]
  [∀ n : ℤ, (shiftFunctor C.K n).Additive] [Pretriangulated C.K]
  [((yonedaDGFunctor C).onK).CommShift ℤ] [((yonedaDGFunctor C).onK).IsTriangulated]
  {ι : Type v} (G : ι → C.Obj)

attribute [local implicit_reducible] DGCategory.K

/-- **The compatibility of the whole chain, reduced to its first two links.** The chain
`DGCategory.RightModule.chainEquivReflectorEvaluation` sends a class `c` to the image `q(f)` of a
morphism `f : x ⟶ y⟦n⟧` exactly when the first two links send `c` to `Q(h_f)`.

The chain ends with the inverse of the fourth link, which is pinned down by the forward direction
(`DGCategory.RightModule.homEquivDerivedYonedaOnK'_symm_eq_iff`); the forward direction at `q(f)`
is `Q(h_f)` by `DGCategory.RightModule.homEquivDerivedYonedaOnK'_map`. Nothing about the third
or fourth link survives on the right-hand side. -/
theorem chainEquivReflectorEvaluation_eq_iff
    {L : (rightModuleCategory.{v} C).K ⥤ (rightModuleCategory.{v} C).K} [L.CommShift ℤ]
    {η : 𝟭 (rightModuleCategory.{v} C).K ⟶ L}
    (hL : ∀ X, (yonedaLocalizing C G).rightOrthogonal (L.obj X))
    (hη : ∀ (X Z : (rightModuleCategory.{v} C).K) (f : Z ⟶ X) (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk f (η.app X) g ∈ distTriang (rightModuleCategory.{v} C).K →
        yonedaLocalizing C G Z)
    {DA : Type u'} [Category.{v'} DA] [HasShift DA ℤ] (q : C.K ⥤ DA)
    [q.IsLocalization (yonedaInverseImage C G).trW] [q.CommShift ℤ]
    (x y : C.K) (e : (endDGCategory C (x : C.Obj)).Obj) (n : ℤ)
    (c : gradedCohomology ((evaluationDGFunctor.{v} C (x : C.Obj)).obj
      (L.obj (yonedaObjK (y : C.Obj)))) e n) (f : x ⟶ y⟦n⟧) :
    chainEquivReflectorEvaluation C G hL hη q x y e n c =
        q.map f ≫ (q.commShiftIso n).hom.app y ↔
      (ofObj fun i ↦ yonedaObjK (G i)).homEquivReflectorShift
          (ofObj fun i ↦ yonedaObjK (G i)).localizingClosure.{v}.trW.Q hL hη
          (yonedaObjK (x : C.Obj)) (yonedaObjK (y : C.Obj)) n
          ((homShiftEquivEvaluationGradedCohomology (L.obj (yonedaObjK (y : C.Obj)))
            (x : C.Obj) e n).symm c) =
        (((yonedaDGFunctor C).onK ⋙
            (ofObj fun i ↦ yonedaObjK (G i)).localizingClosure.{v}.trW.Q).map f) ≫
          (((yonedaDGFunctor C).onK ⋙ (ofObj fun i ↦
            yonedaObjK (G i)).localizingClosure.{v}.trW.Q).commShiftIso n).hom.app y := by
  rw [show chainEquivReflectorEvaluation C G hL hη q x y e n c =
        (homEquivDerivedYonedaOnK' C G q x y n).symm
          ((ofObj fun i ↦ yonedaObjK (G i)).homEquivReflectorShift
            (ofObj fun i ↦ yonedaObjK (G i)).localizingClosure.{v}.trW.Q hL hη
            (yonedaObjK (x : C.Obj)) (yonedaObjK (y : C.Obj)) n
            ((homShiftEquivEvaluationGradedCohomology (L.obj (yonedaObjK (y : C.Obj)))
              (x : C.Obj) e n).symm c)) from rfl,
    homEquivDerivedYonedaOnK'_symm_eq_iff, homEquivDerivedYonedaOnK'_map]
  exact eq_comm

/-- **The chain is compatible with the Yoneda functor as soon as the first link is.** If the first
link assigns to the morphism `η⟦n⟧ ∘ h_f` — the differential graded Yoneda image of `f`, pushed
into the reflector along its unit — the class `c`, then the chain carries `c` to `q(f)`.

The second link is discharged by
`CategoryTheory.ObjectProperty.homEquivReflectorShift_apply_unit`, which applies because the
morphism is `h_f` composed with the unit, and the third and fourth by
`DGCategory.RightModule.chainEquivReflectorEvaluation_eq_iff`. -/
theorem chainEquivReflectorEvaluation_eq_of_link1
    {L : (rightModuleCategory.{v} C).K ⥤ (rightModuleCategory.{v} C).K} [L.CommShift ℤ]
    {η : 𝟭 (rightModuleCategory.{v} C).K ⟶ L}
    (hL : ∀ X, (yonedaLocalizing C G).rightOrthogonal (L.obj X))
    (hη : ∀ (X Z : (rightModuleCategory.{v} C).K) (f : Z ⟶ X) (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk f (η.app X) g ∈ distTriang (rightModuleCategory.{v} C).K →
        yonedaLocalizing C G Z)
    {DA : Type u'} [Category.{v'} DA] [HasShift DA ℤ] (q : C.K ⥤ DA)
    [q.IsLocalization (yonedaInverseImage C G).trW] [q.CommShift ℤ]
    (x y : C.K) (e : (endDGCategory C (x : C.Obj)).Obj) (n : ℤ)
    (c : gradedCohomology ((evaluationDGFunctor.{v} C (x : C.Obj)).obj
      (L.obj (yonedaObjK (y : C.Obj)))) e n) (f : x ⟶ y⟦n⟧)
    (hc : homShiftEquivEvaluationGradedCohomology (L.obj (yonedaObjK (y : C.Obj)))
        (x : C.Obj) e n
        ((((yonedaDGFunctor C).onK).map f ≫
            (((yonedaDGFunctor C).onK).commShiftIso n).hom.app y) ≫
          (shiftFunctor (rightModuleCategory.{v} C).K n).map
            (η.app (yonedaObjK (y : C.Obj)))) = c) :
    chainEquivReflectorEvaluation C G hL hη q x y e n c =
      q.map f ≫ (q.commShiftIso n).hom.app y := by
  rw [chainEquivReflectorEvaluation_eq_iff C G hL hη q x y e n c f, ← hc,
    Equiv.symm_apply_apply]
  exact (homEquivReflectorShift_apply_unit _ _ hL hη _ _ n _).trans
    (CategoryTheory.comp_map_comp_commShiftIso ((yonedaDGFunctor C).onK)
      (ofObj fun i ↦ yonedaObjK (G i)).localizingClosure.{v}.trW.Q x y n f).symm

/-- **The chain of [Stacks, Tag 09LK] carries the Yoneda image of a morphism to its localized
class.** For every morphism `f : x ⟶ y⟦n⟧` of `K(C)`, the chain
`DGCategory.RightModule.chainEquivReflectorEvaluation` takes the degree-`n` cohomology class that
the first link assigns to the differential graded Yoneda image of `f`, pushed along the unit of the
reflector, to the image `q(f)` of `f` in the localization.

This is `DGCategory.RightModule.chainEquivReflectorEvaluation_eq_of_link1` at the class the first
link produces, so the hypothesis there is an identity. It is the compatibility of the chain with
the differential graded Yoneda functor, unconditionally; what the `unit_app_id` clause of
`CochainComplex.derivedHomLiftIdentificationOfNaturality` still needs beyond it is the
identification of the class `β` produces with the class occurring here, which is a statement about
the first link and [Tag 09LC] alone. -/
theorem chainEquivReflectorEvaluation_apply_yonedaOnK
    {L : (rightModuleCategory.{v} C).K ⥤ (rightModuleCategory.{v} C).K} [L.CommShift ℤ]
    {η : 𝟭 (rightModuleCategory.{v} C).K ⟶ L}
    (hL : ∀ X, (yonedaLocalizing C G).rightOrthogonal (L.obj X))
    (hη : ∀ (X Z : (rightModuleCategory.{v} C).K) (f : Z ⟶ X) (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk f (η.app X) g ∈ distTriang (rightModuleCategory.{v} C).K →
        yonedaLocalizing C G Z)
    {DA : Type u'} [Category.{v'} DA] [HasShift DA ℤ] (q : C.K ⥤ DA)
    [q.IsLocalization (yonedaInverseImage C G).trW] [q.CommShift ℤ]
    (x y : C.K) (e : (endDGCategory C (x : C.Obj)).Obj) (n : ℤ) (f : x ⟶ y⟦n⟧) :
    chainEquivReflectorEvaluation C G hL hη q x y e n
        (homShiftEquivEvaluationGradedCohomology (L.obj (yonedaObjK (y : C.Obj)))
          (x : C.Obj) e n
          ((((yonedaDGFunctor C).onK).map f ≫
              (((yonedaDGFunctor C).onK).commShiftIso n).hom.app y) ≫
            (shiftFunctor (rightModuleCategory.{v} C).K n).map
              (η.app (yonedaObjK (y : C.Obj))))) =
      q.map f ≫ (q.commShiftIso n).hom.app y :=
  chainEquivReflectorEvaluation_eq_of_link1 C G hL hη q x y e n _ f rfl

end Chain

end RightModule

end DGCategory

end
