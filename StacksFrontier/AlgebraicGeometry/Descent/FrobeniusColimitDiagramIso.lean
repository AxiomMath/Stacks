module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitPresheafSquare

/-!
# The diagram of Stacks Tag 0EXB is the sheafification of the objectwise one

Let `p` be a prime, let `X` be a scheme in characteristic `p` and write `φ` for the `p`-th power
endomorphism of `𝒪_X`. The diagram `j ↦ (U_φ)^{∘j}((S_φ)^{∘j}𝒢)` of
`AlgebraicGeometry.frobeniusRestrictExtendDiagram` becomes, on the underlying abelian sheaves,
the abelian sheafification of the objectwise diagram `j ↦ 𝒪_X ⊗_{φ^j, 𝒪_X} 𝒢` of
`AlgebraicGeometry.frobeniusPresheafDiagram`. This file builds that isomorphism of diagrams.

At each stage the comparison is
`Stacks.SheafOfModules.pullbackObjToSheafIso` preceded by the identification of the `j`-fold
iterate of extension of scalars with extension of scalars along `φ^j`; the naturality is
`AlgebraicGeometry.pullbackCompToSheafIso_frobeniusIterTransitionHom`, the base-change square at
the transition morphism, together with the identification of that transition morphism with the
Frobenius unit.

## Main definitions

* `AlgebraicGeometry.frobeniusRestrictExtendToSheafIso`: the comparison at one stage, and
  `AlgebraicGeometry.frobeniusRestrictExtendDiagramToSheafIso` **the isomorphism of diagrams.**

## Main results

* `AlgebraicGeometry.frobeniusIterTransitionHom_eq`: **the transition morphism of the diagram,
  read through the comparison with the powers of Frobenius, is the Frobenius unit.**
* `AlgebraicGeometry.toSheaf_map_frobeniusRestrictExtendDiagram_map_succ`: **the naturality.**

## Implementation notes

Three things here are kernel budget rather than mathematics, and each is recorded where it
bites. The transport algebra of the naturality is stated over a *variable* category
(`CategoryTheory.comp_eqToHom_comp_eq_of_transport` and its neighbours), because at the sheaves
of modules in play two spellings of one object agree only after a functor is unfolded and
neither `rw` nor `simp` fires. Every statement mentioning the objectwise base change spells its
source and target `Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj` and nothing else, for
the reason given at `AlgebraicGeometry.frobeniusPresheafDiagram_map_succ'`. And the naturality is
assembled from four separate declarations rather than one, so that each definitional equality
gets its own budget.

## References

* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius TopologicalSpace

universe u

namespace CategoryTheory

universe v₂ u₂ v₃ u₃ v₄ u₄

variable {D : Type u₂} [Category.{v₂} D]

/-- **A transport of functors commutes with the image of a morphism**, with the image on the
left written as the image under the composite's two factors rather than under the composite.
This is `CategoryTheory.Functor.eqToHom_comp_map` in the spelling a consumer needs: the two
sides of `CategoryTheory.Functor.comp_map` are definitionally equal, but identifying them where
the functors are pullbacks of sheaves of modules is not something the kernel should be asked to
do. -/
lemma eqToHom_comp_map_comp {D' : Type u₄} [Category.{v₄} D'] {E : Type u₃} [Category.{v₃} E]
    {Φ : D' ⥤ D} {T : D ⥤ E} {T' : D' ⥤ E} (h : Φ ⋙ T = T') {A B : D'} (f : A ⟶ B) :
    eqToHom (Functor.congr_obj h A) ≫ T'.map f =
      T.map (Φ.map f) ≫ eqToHom (Functor.congr_obj h B) :=
  Functor.eqToHom_comp_map h f

/-- **The image of a morphism followed by a transport is the image followed by a transport.** -/
lemma map_comp_eqToHom {E : Type u₃} [Category.{v₃} E] (T : D ⥤ E) {A B C : D} (f : A ⟶ B)
    (h : B = C) :
    T.map (f ≫ eqToHom h) = T.map f ≫ eqToHom (congrArg T.obj h) := by
  rw [CategoryTheory.Functor.map_comp, eqToHom_map]

/-- **A commuting square whose two edges have been rewritten.** It exists so that the square
is assembled where the composites are generic, rather than at objects which two different
functors spell two different ways. -/
lemma comp_eq_comp_of_eq_of_eq {W₀ W₁ V₀ V₁ : D} {L L' : W₀ ⟶ W₁} {a : W₁ ⟶ V₁} {b : W₀ ⟶ V₀}
    {R R' : V₀ ⟶ V₁} (hL : L = L') (hR : R = R') (h : L' ≫ a = b ≫ R') : L ≫ a = b ≫ R := by
  rw [hL, hR, h]

/-- **A transport moved across an identity from both sides.** -/
lemma eqToHom_symm_comp_of_comp_eqToHom {A B W V : D}
    (h : A = B) (h₂ : W = V) {f : A ⟶ W} {g : B ⟶ V} (hfg : f ≫ eqToHom h₂ = eqToHom h ≫ g) :
    eqToHom h.symm ≫ f = g ≫ eqToHom h₂.symm := by
  subst h
  subst h₂
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp] at hfg
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp, hfg]

/-- **A composite which is a morphism followed by a transport absorbs a further transport.** -/
lemma comp_eqToHom_eq_of_eq {W A B Q : D} {f : W ⟶ A} {t : W ⟶ Q} {e : Q = A} (e₂ : A = B)
    (h : f = t ≫ eqToHom e) :
    f ≫ eqToHom e₂ = t ≫ eqToHom (e.trans e₂) := by
  rw [h, Category.assoc, eqToHom_trans]

/-- **The image of a two-step composite rewritten through three transported identities.** Let
`Φ` be a functor, let `u` and `m` be composable, and suppose that `x` followed by `Φ u` is `y`
up to the transport `d`, that `d` carries `Φ m` to `ψ` up to the transport `d₂`, and that `y`
followed by `ψ` is `t` up to the transport `c`. Then `x` followed by `Φ (u ≫ m)` is `t` up to
the composite transport.

This is the shape in which the transition morphism of the diagram of Stacks Tag 0EXB is
compared with the unit of the pullback adjunction along a power of Frobenius. It is stated over
a variable category because in the instance every object is a sheaf of modules built from
pullbacks, where the two spellings of one object agree only after a functor is unfolded. -/
lemma map_comp_eq_of_eqToHom {E : Type u₃} [Category.{v₃} E] (Φ : D ⥤ E) {A B C : D}
    (u : A ⟶ B) (m : B ⟶ C) {W P R Q : E} {x : W ⟶ Φ.obj A} {y : W ⟶ P} {t : W ⟶ Q}
    {ψ : P ⟶ R} (d : Φ.obj B = P) (d₂ : Φ.obj C = R) (c : R = Q)
    (h₂ : x ≫ Φ.map u = y ≫ eqToHom d.symm)
    (h₃ : eqToHom d.symm ≫ Φ.map m = ψ ≫ eqToHom d₂.symm)
    (h₇ : y ≫ ψ = t ≫ eqToHom c.symm) :
    x ≫ Φ.map (u ≫ m) = t ≫ eqToHom (c.symm.trans d₂.symm) := by
  rw [Φ.map_comp, ← Category.assoc, h₂, Category.assoc, h₃, ← Category.assoc, h₇,
    Category.assoc, eqToHom_trans]

/-- **A commuting square assembled from a square and a factorisation of its left edge**, with
the left edge read as three factors. This is how the naturality of a morphism of diagrams is
assembled from the base-change square at one object and the comparison of transition
morphisms. -/
lemma comp_comp_comp_eq_of_square {W₀ W₁ V₀ V₁ Z₀ Z₁ Y₀ Y₁ : D} {L : W₀ ⟶ W₁} {α₁ : W₁ ⟶ V₁}
    {k₁ : V₁ ⟶ Z₁} {π₁ : Z₁ ⟶ Y₁} {α₀ : W₀ ⟶ V₀} {k₀ : V₀ ⟶ Z₀} {π₀ : Z₀ ⟶ Y₀} {ρ : Y₀ ⟶ Y₁}
    {t : Z₀ ⟶ Z₁} (h₁ : t ≫ π₁ = π₀ ≫ ρ) (h₂ : L ≫ α₁ ≫ k₁ = α₀ ≫ k₀ ≫ t) :
    L ≫ α₁ ≫ k₁ ≫ π₁ = (α₀ ≫ k₀ ≫ π₀) ≫ ρ := by
  rw [reassoc_of% h₂, h₁, Category.assoc, Category.assoc]

/-- `CategoryTheory.comp_comp_comp_eq_of_square` with the left edge read as two factors. -/
lemma comp_comp_eq_of_square {W₀ W₁ V₀ Z₀ Z₁ Y₀ Y₁ : D} {L : W₀ ⟶ W₁} {α₁ : W₁ ⟶ Z₁}
    {π₁ : Z₁ ⟶ Y₁} {α₀ : W₀ ⟶ V₀} {k₀ : V₀ ⟶ Z₀} {π₀ : Z₀ ⟶ Y₀} {ρ : Y₀ ⟶ Y₁} {t : Z₀ ⟶ Z₁}
    (h₁ : t ≫ π₁ = π₀ ≫ ρ) (h₂ : L ≫ α₁ = α₀ ≫ k₀ ≫ t) :
    L ≫ α₁ ≫ π₁ = (α₀ ≫ k₀ ≫ π₀) ≫ ρ := by
  rw [reassoc_of% h₂, h₁, Category.assoc, Category.assoc]

/-- **A morphism which factors through an isomorphism is cancelled against it after a
functor.** -/
lemma map_comp_eq_map_comp_of_iso {E : Type u₃} [Category.{v₃} E] (T : D ⥤ E) {A B C₁ C₂ : D}
    (i : A ≅ B) (f : A ⟶ C₁) (g : C₁ ⟶ C₂) {t : B ⟶ C₂} (ht : t = i.inv ≫ f ≫ g) :
    T.map i.hom ≫ T.map t = T.map f ≫ T.map g := by
  rw [ht, ← CategoryTheory.Functor.map_comp, ← Category.assoc, Iso.hom_inv_id,
    Category.id_comp, CategoryTheory.Functor.map_comp]

/-- **A morphism which factors through an isomorphism is cancelled against it after a functor**,
with nothing following the isomorphism. -/
lemma map_comp_eq_map_of_iso {E : Type u₃} [Category.{v₃} E] (T : D ⥤ E) {A B C : D}
    (i : A ≅ B) (f : A ⟶ C) {t : B ⟶ C} (ht : t = i.inv ≫ f) :
    T.map i.hom ≫ T.map t = T.map f := by
  rw [ht, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_assoc]

/-- **The left edge of the naturality square of the transition morphisms, computed from the two
transport naturalities and the cancellation of the comparison isomorphism.** Every object here
is an abelian sheaf, and the two spellings of one of them agree only after a sheafification
functor is unfolded; keeping the statement over a variable category is what keeps the kernel
from being asked to identify them. -/
lemma comp_eqToHom_comp_eq_of_transport {M₀ M₁ N R₀ R₁ R₁' R₂ R₃ S : D} {L : M₀ ⟶ N}
    (m : M₀ ⟶ M₁) {hdT : M₁ = N} (a₁ : N = R₁') {aΦ : M₀ = R₀} {aΦ' : M₁ = R₁}
    {bΨ : R₁ = R₁'} {bΨ' : R₂ = R₃} {Tu : R₀ ⟶ R₁} {Tψ : R₁ ⟶ R₂} (Tκ : R₁' ⟶ R₃)
    {Ti : R₀ ⟶ S} {Tt : S ⟶ R₂} (hL : L = m ≫ eqToHom hdT)
    (hA : eqToHom aΦ ≫ Tu = m ≫ eqToHom aΦ') (hB : Tψ ≫ eqToHom bΨ' = eqToHom bΨ ≫ Tκ)
    (hC : Ti ≫ Tt = Tu ≫ Tψ) :
    L ≫ eqToHom a₁ ≫ Tκ = eqToHom aΦ ≫ Ti ≫ Tt ≫ eqToHom bΨ' := by
  rw [hL, ← Category.assoc Ti Tt (eqToHom bΨ'), hC, Category.assoc Tu Tψ (eqToHom bΨ'), hB,
    ← Category.assoc (eqToHom aΦ) Tu (eqToHom bΨ ≫ Tκ), hA]
  simp only [Category.assoc, eqToHom_trans_assoc]

/-- **The left edge of the naturality square of the legs**: the same as
`CategoryTheory.comp_eqToHom_comp_eq_of_transport` with no morphism after the transport on the
right, which is the shape the apex of the cocone of Stacks Tag 0EXB takes. -/
lemma comp_eqToHom_eq_of_transport {M₀ M₁ N R₀ R₁ R₂ S : D} {L : M₀ ⟶ N} (m : M₀ ⟶ M₁)
    {hdT : M₁ = N} (a₁ : N = R₂) {aΦ : M₀ = R₀} {aΦ' : M₁ = R₁} (b : R₁ = R₂)
    {Tw : R₀ ⟶ R₁} {Ti : R₀ ⟶ S} {Tt : S ⟶ R₁} (hL : L = m ≫ eqToHom hdT)
    (hA : eqToHom aΦ ≫ Tw = m ≫ eqToHom aΦ') (hC : Ti ≫ Tt = Tw) :
    L ≫ eqToHom a₁ = eqToHom aΦ ≫ Ti ≫ Tt ≫ eqToHom b := by
  rw [hL, ← Category.assoc Ti Tt (eqToHom b), hC,
    ← Category.assoc (eqToHom aΦ) Tw (eqToHom b), hA]
  simp only [Category.assoc, eqToHom_trans]

end CategoryTheory

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)
  (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens)

/-- **The unit of the `j`-fold iterated adjunction, followed by the `j`-fold iterate of
restriction of scalars applied to the comparison with extension of scalars along `φ^j`, is the
unit of the pullback adjunction along `φ^j`**, up to the transport
`AlgebraicGeometry.pushforward_frobeniusRingSheafIter`. This is
`AlgebraicGeometry.unit_comp_pushforward_map_frobeniusExtendScalarsIterIso_inv_app` with the
comparison read on the other side. -/
lemma unit_comp_endoIter_map_frobeniusExtendScalarsIterIso_hom_app (j : ℕ) :
    (frobeniusExtendScalarsAdjunctionIter X p hX j).unit.app G ≫
        ((frobeniusRestrictScalars X p hX).endoIter j).map
          ((frobeniusExtendScalarsIterIso X p hX j).hom.app G) =
      (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
          (frobeniusSelfIterStructureMap X p hX j)).unit.app G ≫
        eqToHom (Functor.congr_obj (pushforward_frobeniusRingSheafIter X p hX j)
          ((_root_.SheafOfModules.pullback.{u}
            (frobeniusSelfIterStructureMap X p hX j)).obj G)).symm := by
  refine CategoryTheory.eq_comp_eqToHom_symm
    (Functor.congr_obj (pushforward_frobeniusRingSheafIter X p hX j)
      ((_root_.SheafOfModules.pullback.{u}
        (frobeniusSelfIterStructureMap X p hX j)).obj G)) ?_
  rw [Category.assoc, ← Functor.eqToHom_comp_map
    (pushforward_frobeniusRingSheafIter X p hX j)
    ((frobeniusExtendScalarsIterIso X p hX j).hom.app G),
    ← reassoc_of% (unit_comp_pushforward_map_frobeniusExtendScalarsIterIso_inv_app X p hX j G),
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.comp_id]

/-- **The unit of the `j`-fold iterated adjunction, followed by the `j`-fold iterate of
restriction of scalars applied to the Frobenius unit and to the comparison at `j + 1`, is the
unit of the pullback adjunction along `φ^{j+1}`**, up to transports. This is the computation
which identifies the transition morphism of the diagram of Stacks Tag 0EXB. -/
lemma unit_comp_endoIter_map_unit_comp (j : ℕ) :
    (frobeniusExtendScalarsAdjunctionIter X p hX j).unit.app G ≫
        ((frobeniusRestrictScalars X p hX).endoIter j).map
          ((frobeniusExtendScalarsAdjunction X p hX).unit.app
              (((frobeniusExtendScalars X p hX).endoIter j).obj G) ≫
            (frobeniusRestrictScalars X p hX).map
              ((frobeniusExtendScalarsIterIso X p hX (j + 1)).hom.app G)) =
      (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
          (frobeniusSelfIterStructureMap X p hX (j + 1))).unit.app G ≫
        eqToHom ((Functor.congr_obj (pushforward_frobeniusRingSheafIter X p hX (j + 1))
            ((_root_.SheafOfModules.pullback.{u}
              (frobeniusSelfIterStructureMap X p hX (j + 1))).obj G)).symm.trans
          (Functor.endoIter_obj_obj (frobeniusRestrictScalars X p hX) j
            ((_root_.SheafOfModules.pullback.{u}
              (frobeniusSelfIterStructureMap X p hX (j + 1))).obj G)).symm) := by
  exact CategoryTheory.map_comp_eq_of_eqToHom ((frobeniusRestrictScalars X p hX).endoIter j)
    _ _ (Functor.endoIter_obj_obj _ j _) (Functor.endoIter_obj_obj _ j _)
    (Functor.congr_obj (pushforward_frobeniusRingSheafIter X p hX (j + 1))
      ((_root_.SheafOfModules.pullback.{u}
        (frobeniusSelfIterStructureMap X p hX (j + 1))).obj G))
    (CategoryTheory.eq_comp_eqToHom_symm _
      ((frobeniusExtendScalarsAdjunctionIter_unit_app_succ X p hX j G).trans
        (Category.assoc _ _ _).symm))
    (CategoryTheory.eqToHom_symm_comp_of_comp_eqToHom _ _
      (Functor.endoIter_map_comp_eqToHom (frobeniusRestrictScalars X p hX) j
        ((frobeniusExtendScalarsIterIso X p hX (j + 1)).hom.app G)))
    (unit_comp_endoIter_map_frobeniusExtendScalarsIterIso_hom_app X p hX G (j + 1))

/-- **The transition morphism of the diagram of Stacks Tag 0EXB, read through the comparison of
the iterates of extension of scalars with extension of scalars along the powers of Frobenius,
is the Frobenius unit.** Both sides are morphisms out of the extension of scalars along `φ^j`,
and the pullback adjunction along `φ^j` compares them with morphisms out of `𝒢`; there the
left-hand side is the unit of the `φ^{j+1}` adjunction by construction and the right-hand side
is the unit of the `j + 1`-fold iterated adjunction. -/
lemma frobeniusIterTransitionHom_eq (j : ℕ) :
    frobeniusIterTransitionHom X p hX j (j + 1) rfl G =
      (frobeniusExtendScalarsIterIso X p hX j).inv.app G ≫
        (frobeniusExtendScalarsAdjunction X p hX).unit.app
            (((frobeniusExtendScalars X p hX).endoIter j).obj G) ≫
          (frobeniusRestrictScalars X p hX).map
            ((frobeniusExtendScalarsIterIso X p hX (j + 1)).hom.app G) := by
  refine ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
    (frobeniusSelfIterStructureMap X p hX j)).homEquiv G _).injective ?_
  have hL : ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
          (frobeniusSelfIterStructureMap X p hX j)).homEquiv G _)
        (frobeniusIterTransitionHom X p hX j (j + 1) rfl G) =
      (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
          (frobeniusSelfIterStructureMap X p hX (j + 1))).unit.app G ≫
        eqToHom (Functor.congr_obj
          (pushforward_frobeniusSelf_comp_pushforward_frobeniusIter X p hX j (j + 1) rfl)
          ((_root_.SheafOfModules.pullback.{u}
            (frobeniusSelfIterStructureMap X p hX (j + 1))).obj G)).symm :=
    Equiv.apply_symm_apply _ _
  rw [hL, Adjunction.homEquiv_unit]
  symm
  rw [CategoryTheory.Functor.map_comp,
    reassoc_of% (unit_comp_pushforward_map_frobeniusExtendScalarsIterIso_inv_app X p hX j G),
    Functor.eqToHom_comp_map (pushforward_frobeniusRingSheafIter X p hX j)
      ((frobeniusExtendScalarsAdjunction X p hX).unit.app
          (((frobeniusExtendScalars X p hX).endoIter j).obj G) ≫
        (frobeniusRestrictScalars X p hX).map
          ((frobeniusExtendScalarsIterIso X p hX (j + 1)).hom.app G))]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  rw [unit_comp_endoIter_map_unit_comp X p hX G j, Category.assoc, eqToHom_trans]

/-- **The abelian sheaf underlying the `j`-th term of the diagram of Stacks Tag 0EXB** is the
sheafification of the objectwise base change `𝒪_X ⊗_{φ^j, 𝒪_X} 𝒢`. The `j`-fold restriction of
scalars disappears, the `j`-fold extension of scalars is extension of scalars along `φ^j` by
`AlgebraicGeometry.frobeniusExtendScalarsIterIso`, and the pullback is read through
`Stacks.SheafOfModules.pullbackObjToSheafIso`. -/
noncomputable def frobeniusRestrictExtendToSheafIso (j : ℕ) :
    (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).obj
        (frobeniusRestrictExtendIter X p hX j G) ≅
      (presheafToSheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u}).obj
        ((PresheafOfModules.toPresheaf X.ringSheafOnOpens.obj).obj
          (Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
            (frobeniusRingSheafIter X p hX j).hom G.val)) :=
  eqToIso (Functor.congr_obj (endoIter_frobeniusRestrictScalars_comp_toSheaf X p hX j)
      (((frobeniusExtendScalars X p hX).endoIter j).obj G)) ≪≫
    (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).mapIso
        ((frobeniusExtendScalarsIterIso X p hX j).app G) ≪≫
      Stacks.SheafOfModules.pullbackObjToSheafIso
        (frobeniusSelfIterStructureMap X p hX j) (𝟙 X.ringSheafOnOpens.obj)
        (frobeniusRingSheafIter X p hX j).hom
        (restrictScalars_frobeniusRingSheafIter_comp X p hX j) G

/-- The forward morphism of `AlgebraicGeometry.frobeniusRestrictExtendToSheafIso` as the composite
of its three pieces. -/
lemma frobeniusRestrictExtendToSheafIso_hom (j : ℕ) :
    (frobeniusRestrictExtendToSheafIso X p hX G j).hom =
      eqToHom (Functor.congr_obj (endoIter_frobeniusRestrictScalars_comp_toSheaf X p hX j)
          (((frobeniusExtendScalars X p hX).endoIter j).obj G)) ≫
        (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map
            ((frobeniusExtendScalarsIterIso X p hX j).hom.app G) ≫
          (Stacks.SheafOfModules.pullbackObjToSheafIso
            (frobeniusSelfIterStructureMap X p hX j) (𝟙 X.ringSheafOnOpens.obj)
            (frobeniusRingSheafIter X p hX j).hom
            (restrictScalars_frobeniusRingSheafIter_comp X p hX j) G).hom :=
  rfl

/-- The transition morphism of the objectwise diagram of Stacks Tag 0EXB, spelled as the base
change along one Frobenius with the arithmetic of the powers read in the form a variable upper
index takes. -/
lemma frobeniusPresheafExtendIterMap_eq (j : ℕ) :
    frobeniusPresheafExtendIterMap X p hX G.val j =
      Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo (frobeniusRingSheafIter X p hX j).hom
        (frobeniusRingSheafHom X p hX).hom G.val (frobeniusRingSheafIter X p hX (j + 1)).hom
        (frobeniusRingSheafIter_hom_comp_frobeniusRingSheafHom_hom' X p hX j (j + 1) rfl) :=
  rfl

/-- The transition morphism of `AlgebraicGeometry.frobeniusPresheafDiagram`, read as the base
change along one Frobenius, with its source and target spelled as
`Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj`.

That spelling is not cosmetic. The two sides of this identity are the image of one morphism
under `PresheafOfModules.toPresheaf` at two different spellings of its source, and the kernel
answers such a question by unfolding the morphism — here all the way through
`Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo` into an adjoint transpose, which exhausts
its budget. Every statement below therefore uses this one spelling of the two objects. -/
lemma frobeniusPresheafDiagram_map_succ' (j : ℕ) :
    ((frobeniusPresheafDiagram X p hX G.val).map (homOfLE j.le_succ) :
        Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
            (frobeniusRingSheafIter X p hX j).hom G.val ⟶
          Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
            (frobeniusRingSheafIter X p hX (j + 1)).hom G.val) =
      Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo (frobeniusRingSheafIter X p hX j).hom
        (frobeniusRingSheafHom X p hX).hom G.val (frobeniusRingSheafIter X p hX (j + 1)).hom
        (frobeniusRingSheafIter_hom_comp_frobeniusRingSheafHom_hom' X p hX j (j + 1) rfl) :=
  (frobeniusPresheafDiagram_map_succ X p hX G.val j).trans
    (frobeniusPresheafExtendIterMap_eq X p hX G j)

/-- `AlgebraicGeometry.frobeniusPresheafDiagram_map_succ'` after the underlying abelian presheaf
and its sheafification. -/
lemma presheafToSheaf_comp_frobeniusPresheafDiagram_map_succ (j : ℕ) :
    (frobeniusPresheafDiagram X p hX G.val ⋙
          PresheafOfModules.toPresheaf X.ringSheafOnOpens.obj ⋙
            presheafToSheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u}).map
        (homOfLE j.le_succ) =
      (presheafToSheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u}).map
        (@CategoryTheory.Functor.map _ _ _ _
          (PresheafOfModules.toPresheaf X.ringSheafOnOpens.obj)
          (Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
            (frobeniusRingSheafIter X p hX j).hom G.val)
          (Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
            (frobeniusRingSheafIter X p hX (j + 1)).hom G.val)
          (Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo
            (frobeniusRingSheafIter X p hX j).hom (frobeniusRingSheafHom X p hX).hom G.val
            (frobeniusRingSheafIter X p hX (j + 1)).hom
            (frobeniusRingSheafIter_hom_comp_frobeniusRingSheafHom_hom' X p hX j (j + 1)
              rfl))) :=
  congrArg
    (fun q ↦ (presheafToSheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u}).map
      (@CategoryTheory.Functor.map _ _ _ _
        (PresheafOfModules.toPresheaf X.ringSheafOnOpens.obj)
        (Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
          (frobeniusRingSheafIter X p hX j).hom G.val)
        (Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
          (frobeniusRingSheafIter X p hX (j + 1)).hom G.val) q))
    (frobeniusPresheafDiagram_map_succ' X p hX G j)

/-- `AlgebraicGeometry.pullbackCompToSheafIso_frobeniusIterTransitionHom` at `k = j + 1`, with
the objectwise base change read as the transition morphism of
`AlgebraicGeometry.frobeniusPresheafDiagram`. -/
theorem pullbackObjToSheafIso_frobeniusPresheafDiagram_map_succ (j : ℕ) :
    ((_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map
            (frobeniusIterTransitionHom X p hX j (j + 1) rfl G) ≫
          eqToHom (Functor.congr_obj (frobeniusRestrictScalars_comp_toSheaf X p hX)
            ((_root_.SheafOfModules.pullback.{u}
              (frobeniusSelfIterStructureMap X p hX (j + 1))).obj G))) ≫
        (Stacks.SheafOfModules.pullbackObjToSheafIso
          (frobeniusSelfIterStructureMap X p hX (j + 1)) (𝟙 X.ringSheafOnOpens.obj)
          (frobeniusRingSheafIter X p hX (j + 1)).hom
          (restrictScalars_frobeniusRingSheafIter_comp X p hX (j + 1)) G).hom =
      (Stacks.SheafOfModules.pullbackObjToSheafIso
          (frobeniusSelfIterStructureMap X p hX j) (𝟙 X.ringSheafOnOpens.obj)
          (frobeniusRingSheafIter X p hX j).hom
          (restrictScalars_frobeniusRingSheafIter_comp X p hX j) G).hom ≫
        (frobeniusPresheafDiagram X p hX G.val ⋙
          PresheafOfModules.toPresheaf X.ringSheafOnOpens.obj ⋙
            presheafToSheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u}).map
          (homOfLE j.le_succ) := by
  rw [presheafToSheaf_comp_frobeniusPresheafDiagram_map_succ]
  exact pullbackCompToSheafIso_frobeniusIterTransitionHom X p hX j (j + 1) rfl G


/-- The transition morphism of
`AlgebraicGeometry.frobeniusRestrictExtendDiagram`, read on the underlying abelian sheaves. -/
lemma toSheaf_comp_frobeniusRestrictExtendDiagram_map_succ (j : ℕ) :
    (frobeniusRestrictExtendDiagram X p hX G ⋙
          _root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map (homOfLE j.le_succ) =
      (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map
        (frobeniusRestrictExtendIterMap X p hX j G) :=
  congrArg (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map
    (frobeniusRestrictExtendDiagram_map_succ X p hX G j)

/-- **The left edge of the naturality square of the transition morphisms of Stacks Tag 0EXB**:
the transition morphism of the diagram, followed by the comparison of the `j + 1`-fold iterate
with extension of scalars along `φ^{j+1}`, is the comparison at `j` followed by the transition
morphism read as a morphism of pullbacks. Both sides are read on abelian sheaves, where the
`j`-fold restriction of scalars and the one along Frobenius both disappear; the transports are
exactly those disappearances. -/
theorem toSheaf_map_frobeniusRestrictExtendIterMap_comp (j : ℕ) :
    (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map
          (frobeniusRestrictExtendIterMap X p hX j G) ≫
        eqToHom (Functor.congr_obj
            (endoIter_frobeniusRestrictScalars_comp_toSheaf X p hX (j + 1))
            (((frobeniusExtendScalars X p hX).endoIter (j + 1)).obj G)) ≫
          (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map
            ((frobeniusExtendScalarsIterIso X p hX (j + 1)).hom.app G) =
      eqToHom (Functor.congr_obj (endoIter_frobeniusRestrictScalars_comp_toSheaf X p hX j)
          (((frobeniusExtendScalars X p hX).endoIter j).obj G)) ≫
        (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map
            ((frobeniusExtendScalarsIterIso X p hX j).hom.app G) ≫
          (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map
              (frobeniusIterTransitionHom X p hX j (j + 1) rfl G) ≫
            eqToHom (Functor.congr_obj (frobeniusRestrictScalars_comp_toSheaf X p hX)
              ((_root_.SheafOfModules.pullback.{u}
                (frobeniusSelfIterStructureMap X p hX (j + 1))).obj G)) := by
  have hL : (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map
        (frobeniusRestrictExtendIterMap X p hX j G) =
      (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map
          (((frobeniusRestrictScalars X p hX).endoIter j).map
            ((frobeniusExtendScalarsAdjunction X p hX).unit.app
              (((frobeniusExtendScalars X p hX).endoIter j).obj G))) ≫
        eqToHom (congrArg (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).obj
          (Functor.endoIter_obj_obj (frobeniusRestrictScalars X p hX) j
            (((frobeniusExtendScalars X p hX).endoIter (j + 1)).obj G))) :=
    CategoryTheory.map_comp_eqToHom _ _ _
  exact CategoryTheory.comp_eqToHom_comp_eq_of_transport _ _ _ hL
    (CategoryTheory.eqToHom_comp_map_comp
      (endoIter_frobeniusRestrictScalars_comp_toSheaf X p hX j)
      ((frobeniusExtendScalarsAdjunction X p hX).unit.app
        (((frobeniusExtendScalars X p hX).endoIter j).obj G)))
    (CategoryTheory.eqToHom_comp_map_comp (frobeniusRestrictScalars_comp_toSheaf X p hX)
      ((frobeniusExtendScalarsIterIso X p hX (j + 1)).hom.app G)).symm
    (CategoryTheory.map_comp_eq_map_comp_of_iso
      (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens)
      ((frobeniusExtendScalarsIterIso X p hX j).app G) _ _
      (frobeniusIterTransitionHom_eq X p hX G j))

/-- `AlgebraicGeometry.toSheaf_map_frobeniusRestrictExtendIterMap_comp` with the transition
morphism read as the image of `AlgebraicGeometry.frobeniusRestrictExtendDiagram`. -/
theorem toSheaf_map_frobeniusRestrictExtendDiagram_map_succ_comp (j : ℕ) :
    (frobeniusRestrictExtendDiagram X p hX G ⋙
          _root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map (homOfLE j.le_succ) ≫
        eqToHom (Functor.congr_obj
            (endoIter_frobeniusRestrictScalars_comp_toSheaf X p hX (j + 1))
            (((frobeniusExtendScalars X p hX).endoIter (j + 1)).obj G)) ≫
          (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map
            ((frobeniusExtendScalarsIterIso X p hX (j + 1)).hom.app G) =
      eqToHom (Functor.congr_obj (endoIter_frobeniusRestrictScalars_comp_toSheaf X p hX j)
          (((frobeniusExtendScalars X p hX).endoIter j).obj G)) ≫
        (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map
            ((frobeniusExtendScalarsIterIso X p hX j).hom.app G) ≫
          (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map
              (frobeniusIterTransitionHom X p hX j (j + 1) rfl G) ≫
            eqToHom (Functor.congr_obj (frobeniusRestrictScalars_comp_toSheaf X p hX)
              ((_root_.SheafOfModules.pullback.{u}
                (frobeniusSelfIterStructureMap X p hX (j + 1))).obj G)) := by
  rw [toSheaf_comp_frobeniusRestrictExtendDiagram_map_succ]
  exact toSheaf_map_frobeniusRestrictExtendIterMap_comp X p hX G j

/-- **The transition morphism of the diagram of Stacks Tag 0EXB becomes, on the underlying
abelian sheaves, the sheafification of the objectwise base change along one Frobenius.** This is
the naturality of `AlgebraicGeometry.frobeniusRestrictExtendToSheafIso`, in the shape
`CategoryTheory.NatTrans.ofSequence` asks for. -/
theorem toSheaf_map_frobeniusRestrictExtendDiagram_map_succ (j : ℕ) :
    (frobeniusRestrictExtendDiagram X p hX G ⋙
          _root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map (homOfLE j.le_succ) ≫
        (frobeniusRestrictExtendToSheafIso X p hX G (j + 1)).hom =
      (frobeniusRestrictExtendToSheafIso X p hX G j).hom ≫
        (frobeniusPresheafDiagram X p hX G.val ⋙
          PresheafOfModules.toPresheaf X.ringSheafOnOpens.obj ⋙
            presheafToSheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u}).map
          (homOfLE j.le_succ) := by
  rw [frobeniusRestrictExtendToSheafIso_hom, frobeniusRestrictExtendToSheafIso_hom]
  exact CategoryTheory.comp_comp_comp_eq_of_square
    (pullbackObjToSheafIso_frobeniusPresheafDiagram_map_succ X p hX G j)
    (toSheaf_map_frobeniusRestrictExtendDiagram_map_succ_comp X p hX G j)

/-- **The morphism of diagrams of Stacks Tag 0EXB**: at each stage the comparison
`AlgebraicGeometry.frobeniusRestrictExtendToSheafIso`, which is natural by
`AlgebraicGeometry.toSheaf_map_frobeniusRestrictExtendDiagram_map_succ`. -/
noncomputable def frobeniusRestrictExtendDiagramToSheafHom :
    frobeniusRestrictExtendDiagram X p hX G ⋙
        _root_.SheafOfModules.toSheaf X.ringSheafOnOpens ⟶
      frobeniusPresheafDiagram X p hX G.val ⋙
        PresheafOfModules.toPresheaf X.ringSheafOnOpens.obj ⋙
          presheafToSheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u} :=
  NatTrans.ofSequence (fun j ↦ (frobeniusRestrictExtendToSheafIso X p hX G j).hom)
    (fun j ↦ toSheaf_map_frobeniusRestrictExtendDiagram_map_succ X p hX G j)

/-- The component at `j` of `AlgebraicGeometry.frobeniusRestrictExtendDiagramToSheafHom` is the
comparison `AlgebraicGeometry.frobeniusRestrictExtendToSheafIso` at `j`. -/
@[simp]
lemma frobeniusRestrictExtendDiagramToSheafHom_app (j : ℕ) :
    (frobeniusRestrictExtendDiagramToSheafHom X p hX G).app j =
      (frobeniusRestrictExtendToSheafIso X p hX G j).hom :=
  NatTrans.ofSequence_app _ _ j

/-- Each component of `AlgebraicGeometry.frobeniusRestrictExtendDiagramToSheafHom` is an
isomorphism. -/
instance (j : ℕ) : IsIso ((frobeniusRestrictExtendDiagramToSheafHom X p hX G).app j) := by
  rw [frobeniusRestrictExtendDiagramToSheafHom_app]
  exact (frobeniusRestrictExtendToSheafIso X p hX G j).isIso_hom

/-- **The diagram of Stacks Tag 0EXB is, on the underlying abelian sheaves, the abelian
sheafification of the objectwise diagram `j ↦ 𝒪_X ⊗_{φ^j, 𝒪_X} 𝒢`.** -/
noncomputable def frobeniusRestrictExtendDiagramToSheafIso :
    frobeniusRestrictExtendDiagram X p hX G ⋙
        _root_.SheafOfModules.toSheaf X.ringSheafOnOpens ≅
      frobeniusPresheafDiagram X p hX G.val ⋙
        PresheafOfModules.toPresheaf X.ringSheafOnOpens.obj ⋙
          presheafToSheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u} :=
  have : IsIso (frobeniusRestrictExtendDiagramToSheafHom X p hX G) :=
    NatIso.isIso_of_isIso_app _
  asIso (frobeniusRestrictExtendDiagramToSheafHom X p hX G)

/-- The component at `j` of `AlgebraicGeometry.frobeniusRestrictExtendDiagramToSheafIso` is the
comparison `AlgebraicGeometry.frobeniusRestrictExtendToSheafIso` at `j`. -/
@[simp]
lemma frobeniusRestrictExtendDiagramToSheafIso_hom_app (j : ℕ) :
    (frobeniusRestrictExtendDiagramToSheafIso X p hX G).hom.app j =
      (frobeniusRestrictExtendToSheafIso X p hX G j).hom :=
  frobeniusRestrictExtendDiagramToSheafHom_app X p hX G j

end AlgebraicGeometry

end
